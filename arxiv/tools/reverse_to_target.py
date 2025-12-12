#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
reverse_by_row.py

Row-consistent reverse stepper for the unified p=0 table on the odd layer.
Given an odd child x' (≡1 or 5 mod 6), find all legal parents x with U(x')=x
by (i) matching the producing row x' = a*m + b, (ii) computing x = (3x'+1)/2^α,
and (iii) verifying row-consistency: s(x), j(x), m(x) match the row’s (s_in, j_in, m).

Also provides a small DFS to recover a path from a given x' back to a target y.
"""

from dataclasses import dataclass
from typing import List, Optional, Dict, Any, Tuple

# -------- helpers ------------------------------------------------------------

def family(x: int) -> str:
    r = x % 6
    if r == 1: return 'e'
    if r == 5: return 'o'
    raise ValueError(f"x={x} not in odd families (1 or 5 mod 6).")

def indices(x: int) -> Tuple[str, int, int]:
    """Return (s, j, m) for odd x."""
    s = family(x)
    m = x // 18
    j = (x // 6) % 3
    return s, j, m

# -------- unified p=0 rows (from your table) --------------------------------
# For each row: key, type, s_in, j_in, delta (output family offset),
# forward form x' = a*m + b, and forward power 2^alpha in 3x'+1 = 2^alpha x.

@dataclass(frozen=True)
class Row:
    key: str
    typ: str          # 'ee','eo','oe','oo'
    s_in: str         # 'e' or 'o' (input family)
    j_in: int         # 0,1,2
    delta: int        # 1 for *e, 5 for *o
    a: int
    b: int
    alpha: int

ROWS: List[Row] = [
    # ee (δ=1)
    Row("Psi_0", "ee", "e", 0, 1,  24,   1, 2),
    Row("Psi_1", "ee", "e", 1, 1,  96,  37, 4),
    Row("Psi_2", "ee", "e", 2, 1, 384, 277, 6),
    # oe (δ=1)
    Row("omega_0", "oe", "o", 0, 1,  48,  13, 3),
    Row("omega_1", "oe", "o", 1, 1,  12,   7, 1),
    Row("omega_2", "oe", "o", 2, 1, 192, 181, 5),
    # eo (δ=5)
    Row("psi_0", "eo", "e", 0, 5,  96,   5, 4),
    Row("psi_1", "eo", "e", 1, 5, 384, 149, 6),
    Row("psi_2", "eo", "e", 2, 5,  24,  17, 2),
    # oo (δ=5)
    Row("Omega_0", "oo", "o", 0, 5, 192,  53, 5),
    Row("Omega_1", "oo", "o", 1, 5,  48,  29, 3),
    Row("Omega_2", "oo", "o", 2, 5,  12,  11, 1),
]

# Candidate rows for a given child x' are those with delta == (x' mod 6).

def candidate_rows_for_child(x_child: int) -> List[Row]:
    delta = 1 if x_child % 6 == 1 else 5
    return [r for r in ROWS if r.delta == delta]

# -------- reverse one step ---------------------------------------------------

@dataclass
class ReverseOption:
    row: Row
    m: int
    x_parent: int
    s_parent: str
    j_parent: int
    m_parent: int
    consistent: bool  # True only if (s_parent, j_parent, m_parent) matches row.s_in/j_in/m

def reverse_step(x_child: int) -> List[ReverseOption]:
    """Return all row-consistent parents of x_child."""
    if x_child % 2 == 0:
        raise ValueError("x_child must be odd.")
    if x_child % 6 not in (1,5):
        raise ValueError("x_child must be 1 or 5 (mod 6).")

    out: List[ReverseOption] = []
    for r in candidate_rows_for_child(x_child):
        num = x_child - r.b
        if num % r.a != 0:
            continue
        m = num // r.a
        if m < 0:
            continue
        # parent via the forward identity 3x'+1 = 2^alpha x
        nump = 3 * x_child + 1
        if nump % (1 << r.alpha) != 0:
            continue
        x_parent = nump // (1 << r.alpha)
        if x_parent % 2 == 0:
            # parent must be odd on the odd layer
            continue

        s_p, j_p, m_p = indices(x_parent)
        ok = (s_p == r.s_in) and (j_p == r.j_in) and (m_p == m)
        out.append(ReverseOption(r, m, x_parent, s_p, j_p, m_p, ok))
    # Prefer consistent ones first, and smaller parents first as a heuristic.
    out.sort(key=lambda z: (not z.consistent, z.x_parent))
    return out

# -------- search for a specific ancestor ------------------------------------

@dataclass
class StepLog:
    x_child: int
    row_key: str
    m: int
    alpha: int
    x_parent: int
    consistent: bool

def reverse_to_target(x_start: int, x_target: int, max_depth: int = 200) -> Optional[List[StepLog]]:
    """
    DFS to find a row-consistent reverse path from x_start back to x_target.
    Returns the sequence of steps (child -> parent) if found, else None.
    """
    if x_start == x_target:
        return []

    # Stack entries: (current_x, depth, path_so_far)
    stack: List[Tuple[int, int, List[StepLog]]] = [(x_start, 0, [])]
    visited = set()

    while stack:
        x_cur, d, path = stack.pop()
        if d >= max_depth:
            continue
        if x_cur in visited:
            continue
        visited.add(x_cur)

        opts = reverse_step(x_cur)
        # Expand consistent, then others (though "others" should rarely pass checks)
        for opt in opts:
            log = StepLog(
                x_child=x_cur,
                row_key=opt.row.key,
                m=opt.m,
                alpha=opt.row.alpha,
                x_parent=opt.x_parent,
                consistent=opt.consistent,
            )
            new_path = path + [log]
            if opt.x_parent == x_target and opt.consistent:
                return new_path
            # heuristic: push smaller parents first
            stack.append((opt.x_parent, d + 1, new_path))

    return None

# -------- CLI demo -----------------------------------------------------------

def demo():
    # Example: reverse 43 back to 65 (the worked example)
    #path = reverse_to_target(43, 65, max_depth=10)
    path = reverse_to_target(7, 1, max_depth=10)
    if not path:
        print("No path found.")
        return
    print("Reverse path (child -> parent):")
    for i, step in enumerate(path, 1):
        print(f"[{i}] {step.x_child} --{step.row_key} (m={step.m}, α={step.alpha})--> {step.x_parent} "
              f"{'(consistent)' if step.consistent else '(inconsistent)'}")

if __name__ == "__main__":
    demo()
