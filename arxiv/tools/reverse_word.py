#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Row-consistent Collatz reverse stepper (odd layer, unified table, p=0 by default).

Given a child y (odd, ≡1 or 5 mod 6), we try rows whose output family matches y mod 6,
solve for m_prev, reconstruct x_prev = 18*m_prev + 6*j + p6, and verify U(y) == x_prev.
We can iterate to reach a target ancestor or stop at 1.

Author: you :)
"""

from dataclasses import dataclass, asdict
from typing import List, Optional, Dict, Any, Tuple

# ---------- utilities ----------

def v2(n: int) -> int:
    """2-adic valuation v2(n) for n>0."""
    if n <= 0:
        raise ValueError("v2 expects n>0.")
    c = 0
    while n & 1 == 0:
        n >>= 1
        c += 1
    return c

def U_odd(y: int) -> int:
    """Accelerated odd Collatz map U on odds."""
    s = v2(3*y + 1)
    return (3*y + 1) >> s

def family(x: int) -> str:
    r = x % 6
    if r == 1:
        return 'e'
    if r == 5:
        return 'o'
    raise ValueError(f"x={x} not in odd-layer families (1 or 5 mod 6)")

def indices(x: int) -> Tuple[str, int, int, int]:
    """Return (s, m, j, r) for odd x: s∈{e,o}, m=floor(x/18), j=floor(x/6) mod 3, r=floor(x/6)."""
    s = family(x)
    r = x // 6
    j = r % 3
    m = x // 18
    return s, m, j, r

# ---------- unified table rows (p=0 by default) ----------
# Each row encodes the parent lane (s,j) and child formula parameters (alpha,beta,c,delta).
# delta=1 means child family e; delta=5 means child family o.

ROWS: List[Dict[str, Any]] = [
    # (s='e') ee
    {"key":"Psi0", "s":"e", "j":0, "alpha":2, "beta":2,   "c":-2,  "delta":1, "type":"ee"},
    {"key":"Psi1", "s":"e", "j":1, "alpha":4, "beta":56,  "c":-2,  "delta":1, "type":"ee"},
    {"key":"Psi2", "s":"e", "j":2, "alpha":6, "beta":416, "c":-2,  "delta":1, "type":"ee"},

    # (s='o') oe
    {"key":"omega0", "s":"o", "j":0, "alpha":3, "beta":20,  "c":-2,  "delta":1, "type":"oe"},
    {"key":"omega1", "s":"o", "j":1, "alpha":1, "beta":11,  "c":-2,  "delta":1, "type":"oe"},
    {"key":"omega2", "s":"o", "j":2, "alpha":5, "beta":272, "c":-2,  "delta":1, "type":"oe"},

    # (s='e') eo
    {"key":"psi0", "s":"e", "j":0, "alpha":4, "beta":8,    "c":-8,  "delta":5, "type":"eo"},
    {"key":"psi1", "s":"e", "j":1, "alpha":6, "beta":224,  "c":-8,  "delta":5, "type":"eo"},
    {"key":"psi2", "s":"e", "j":2, "alpha":2, "beta":26,   "c":-8,  "delta":5, "type":"eo"},

    # (s='o') oo
    {"key":"Omega0", "s":"o", "j":0, "alpha":5, "beta":80,  "c":-8,  "delta":5, "type":"oo"},
    {"key":"Omega1", "s":"o", "j":1, "alpha":3, "beta":44,  "c":-8,  "delta":5, "type":"oo"},
    {"key":"Omega2", "s":"o", "j":2, "alpha":1, "beta":17,  "c":-8,  "delta":5, "type":"oo"},
]

@dataclass
class ReverseStep:
    i: int
    y_child: int
    row_key: str
    row_type: str  # ee/eo/oe/oo
    parent_s: str
    parent_j: int
    alpha: int
    beta: int
    c: int
    delta: int
    p: int
    k_p: int
    m_prev: int
    x_prev: int
    U_check: int
    indices_match: bool

class RowMismatch(Exception):
    pass

def reverse_step_from_row(y: int, row: Dict[str, Any], p: int = 0) -> Tuple[int, int, ReverseStep]:
    """
    Reverse one step given the child y and a candidate parent row (with parameter p >= 0).
    Returns (x_prev, m_prev, log). Raises RowMismatch if the row does not produce a valid parent.
    """
    s = row["s"]
    j = row["j"]
    alpha = row["alpha"]
    beta = row["beta"]
    c = row["c"]
    delta = row["delta"]
    key = row["key"]
    rtype = row["type"]

    # Filter by child's family via delta
    if y % 6 != delta:
        raise RowMismatch("Child family (mod 6) does not match row's delta.")

    # k_p = (beta * 64^p + c)/9 must be integer
    kp_num = beta * (64 ** p) + c
    if kp_num % 9 != 0:
        raise RowMismatch("Row params violate integrality for k_p.")
    k_p = kp_num // 9

    # Solve y = 6(2^{alpha+6p} * m_prev + k_p) + delta
    num = y - delta
    if num % 6 != 0:
        raise RowMismatch("y - delta not divisible by 6.")
    inner = num // 6
    slope = 1 << (alpha + 6 * p)
    rhs = inner - k_p
    if rhs % slope != 0:
        raise RowMismatch("No integer m_prev (divisibility by 2^{alpha+6p} fails).")
    m_prev = rhs // slope
    if m_prev < 0:
        raise RowMismatch("m_prev is negative.")

    # Reconstruct parent directly: x_prev = 18*m_prev + 6*j + p6
    p6 = 1 if s == 'e' else 5
    x_prev = 18 * m_prev + 6 * j + p6

    # Safety checks
    U_y = U_odd(y)
    if U_y != x_prev:
        raise RowMismatch("Forward check failed: U(y) != x_prev (row mismatch).")

    s_prev, m_chk, j_chk, _ = indices(x_prev)
    indices_ok = (s_prev == s and j_chk == j and m_chk == m_prev)

    log = ReverseStep(
        i=0,
        y_child=y,
        row_key=key,
        row_type=rtype,
        parent_s=s,
        parent_j=j,
        alpha=alpha,
        beta=beta,
        c=c,
        delta=delta,
        p=p,
        k_p=k_p,
        m_prev=m_prev,
        x_prev=x_prev,
        U_check=U_y,
        indices_match=indices_ok
    )
    return x_prev, m_prev, log

def reverse_step_auto(y: int, p: int = 0) -> ReverseStep:
    """
    Try all rows compatible with y%6 (via delta). Return the unique valid reverse step.
    Raises ValueError if none or multiple rows fit.
    """
    candidates: List[ReverseStep] = []
    for row in ROWS:
        try:
            x_prev, m_prev, log = reverse_step_from_row(y, row, p=p)
            candidates.append(log)
        except RowMismatch:
            continue

    if not candidates:
        raise ValueError(f"No valid parent row found for y={y} (p={p}).")
    if len(candidates) > 1:
        # It *should* be unique; if not, you can disambiguate by preferring indices_match True
        best = [c for c in candidates if c.indices_match]
        if len(best) == 1:
            return best[0]
        # As a fallback, raise with details
        rows = ", ".join(f"{c.row_key}" for c in candidates)
        raise ValueError(f"Ambiguous parent rows for y={y}: {rows}")
    return candidates[0]

def reverse_until(
    y_start: int,
    stop_at: Optional[int] = 1,
    max_steps: int = 1000,
    p: int = 0
) -> Dict[str, Any]:
    """
    Reverse from y_start up the inverse tree (one legal parent per step),
    until x_prev == stop_at (default 1) or max_steps reached.
    Returns a dict with the logs and final parent.
    """
    if y_start % 2 == 0:
        raise ValueError("y_start must be odd.")

    logs: List[ReverseStep] = []
    y = y_start

    for i in range(1, max_steps + 1):
        step = reverse_step_auto(y, p=p)
        step.i = i
        logs.append(step)
        x_prev = step.x_prev

        if stop_at is not None and x_prev == stop_at:
            break

        # Continue: next child is the current parent
        y = x_prev
    else:
        # did not break
        pass

    return {
        "start_child": y_start,
        "stop_at": stop_at,
        "steps": [asdict(s) for s in logs],
        "final_parent": logs[-1].x_prev if logs else None,
        "num_steps": len(logs),
    }

# ---------- CLI demo ----------
if __name__ == "__main__":
    # Example: reverse from y=43 up to 1 (p=0), logging each step.
    y0 = 43
    result = reverse_until(y0, stop_at=1, max_steps=100, p=0)
    print(f"Reversed from {y0} to {result['final_parent']} in {result['num_steps']} steps.")
    for s in result["steps"]:
        print(
            f"Step {s['i']}: y={s['y_child']} <-[{s['row_key']} ({s['row_type']}) "
            f"s={s['parent_s']}, j={s['parent_j']}, alpha={s['alpha']}]-- "
            f"x_prev={s['x_prev']} (m_prev={s['m_prev']}, U(y)={s['U_check']}, "
            f"indices_ok={s['indices_match']})"
        )
