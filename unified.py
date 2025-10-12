# unified.py
from __future__ import annotations
from dataclasses import dataclass, asdict
from typing import List, Dict, Any, Tuple, Optional
import math

# ---------- basic helpers ----------
def v2(n: int) -> int:
    """2-adic valuation v2(n) for n>0."""
    if n <= 0:
        raise ValueError("v2 defined for positive integers")
    c = 0
    while (n & 1) == 0:
        n >>= 1
        c += 1
    return c

def U_odd(y: int) -> int:
    """Accelerated odd Collatz map on odds."""
    s = v2(3*y + 1)
    return (3*y + 1) >> s

def family(x: int) -> str:
    r = x % 6
    if r == 1: return 'e'
    if r == 5: return 'o'
    raise ValueError(f"x={x} not in odd-layer families (1 or 5 mod 6).")

def indices(x: int) -> Tuple[str,int,int,int]:
    """Return (s, m, j, r) for current x."""
    s = family(x)
    r = x // 6
    j = r % 3
    m = x // 18
    return s, m, j, r

# ---------- unified p=0 formulas (Table: unified-F0-straight-xprime) ----------
# Each entry maps (block, j) -> lambda m: x'(m)
BLOCK_FORMULAS = {
    'ee': {
        0: lambda m: 24*m + 1,
        1: lambda m: 96*m + 37,
        2: lambda m: 384*m + 277,
    },
    'eo': {
        0: lambda m: 96*m + 5,
        1: lambda m: 384*m + 149,
        2: lambda m: 24*m + 17,
    },
    'oe': {
        0: lambda m: 48*m + 13,
        1: lambda m: 12*m + 7,
        2: lambda m: 192*m + 181,
    },
    'oo': {
        0: lambda m: 192*m + 53,
        1: lambda m: 48*m + 29,
        2: lambda m: 12*m + 11,
    },
}

TOKEN_BLOCK = {
    'Psi': 'ee',
    'psi': 'eo',
    'omega': 'oe',
    'Omega': 'oo',
}

@dataclass
class StepRecord:
    i: int
    token: str
    block: str
    x_before: int
    s_before: str
    m_before: int
    j_before: int
    x_after: int
    s_after: str
    m_after: int
    j_after: int
    U_of_after: int
    forward_ok: bool

class UnifiedEvaluator:
    """
    Evaluate words using the unified p=0 table.
    At each step: read (s,j,m) from the current x, then apply the block formula for the chosen token.
    """

    def __init__(self):
        pass

    @staticmethod
    def _block_for_token(token: str, s: str) -> str:
        if token not in TOKEN_BLOCK:
            raise ValueError(f"Unknown token '{token}'.")
        block = TOKEN_BLOCK[token]
        # admissibility check
        if (block in ('ee','eo')) and s != 'e':
            raise ValueError(f"Token {token} requires family e; current s={s}.")
        if (block in ('oe','oo')) and s != 'o':
            raise ValueError(f"Token {token} requires family o; current s={s}.")
        return block

    def step(self, x: int, token: str) -> Tuple[int, StepRecord]:
        s0, m0, j0, _ = indices(x)
        block = self._block_for_token(token, s0)
        f = BLOCK_FORMULAS[block][j0]
        y = f(m0)  # preimage (child)
        s1, m1, j1, _ = indices(y)
        u = U_odd(y)
        ok = (u == x)
        rec = StepRecord(
            i=0, token=token, block=block,
            x_before=x, s_before=s0, m_before=m0, j_before=j0,
            x_after=y, s_after=s1, m_after=m1, j_after=j1,
            U_of_after=u, forward_ok=ok
        )
        return y, rec

    def evaluate(self, word: List[str], x0: int = 1) -> Dict[str, Any]:
        x = int(x0)
        trace: List[StepRecord] = []
        for i, t in enumerate(word, 1):
            y, rec = self.step(x, t)
            rec.i = i
            trace.append(rec)
            x = y
        return {
            "x0": x0,
            "x_final": x,
            "length": len(word),
            "trace": [asdict(r) for r in trace],
        }

# ---------- tiny BFS for witnesses ----------
def admissible_tokens_for_x(x: int) -> List[str]:
    s, _, _, _ = indices(x)
    return ['Psi','psi'] if s == 'e' else ['omega','Omega']

def bfs_witnesses(modulus: int, max_depth: int = 6) -> Dict[int, Dict[str, Any]]:
    """
    From seed 1, breadth-first expand inverse steps up to max_depth.
    Returns first-found witness per odd residue class modulo 'modulus'.
    """
    assert modulus % 2 == 0 and modulus % 3 == 0, "Use M_K = 3*2^K style moduli"
    target_residues = [r for r in range(modulus) if r % 2 == 1 and r % 3 != 0]  # 1 or 5 mod 6
    got: Dict[int, Dict[str,Any]] = {}

    ev = UnifiedEvaluator()
    from collections import deque
    Q = deque()
    Q.append((1, []))  # (x, word)

    visited = set([1])

    while Q:
        x, w = Q.popleft()

        # record residue if new
        r = x % modulus
        if (r in target_residues) and (r not in got):
            got[r] = {"word": w[:], "x": x}
            if len(got) == len(target_residues):
                break

        if len(w) >= max_depth:
            continue

        for t in admissible_tokens_for_x(x):
            res = ev.evaluate([t], x0=x)
            y = res["x_final"]
            if y not in visited:
                visited.add(y)
                Q.append((y, w + [t]))

    return got
