# reverse_construct.py
# Row-consistent reversibility with unbounded p-search (finite per-row termination)
# Now with CSV output support.

from dataclasses import dataclass, asdict
from typing import Optional, List, Tuple
import argparse
import csv
import sys

# ---------- core odd-accelerated Collatz ----------
def v2(n: int) -> int:
    c = 0
    while n % 2 == 0:
        n //= 2
        c += 1
    return c

def U_odd(y: int) -> int:
    s = v2(3*y + 1)
    return (3*y + 1) >> s

def family(x: int) -> str:
    r = x % 6
    if r == 1: return 'e'
    if r == 5: return 'o'
    raise ValueError(f"x={x} not in odd layer families (1 or 5 mod 6)")

def indices(x: int) -> Tuple[str,int,int,int]:
    s = family(x)
    r = x // 6
    j = r % 3
    m = x // 18
    return s, m, j, r

# ---------- unified p=0 parameter table ----------
# Each entry: (key, s_parent, j_parent, alpha, beta, c, delta_child)
ROWS = [
    # ee rows (delta = 1)
    ("ee0", "e", 0, 2,   2,   -2, 1),
    ("ee1", "e", 1, 4,   56,  -2, 1),
    ("ee2", "e", 2, 6,   416, -2, 1),
    # oe rows (delta = 1)
    ("oe0", "o", 0, 3,   20,  -2, 1),
    ("oe1", "o", 1, 1,   11,  -2, 1),
    ("oe2", "o", 2, 5,   272, -2, 1),
    # eo rows (delta = 5)
    ("eo0", "e", 0, 4,   8,   -8, 5),
    ("eo1", "e", 1, 6,   224, -8, 5),
    ("eo2", "e", 2, 2,   26,  -8, 5),
    # oo rows (delta = 5)
    ("oo0", "o", 0, 5,   80,  -8, 5),
    ("oo1", "o", 1, 3,   44,  -8, 5),
    ("oo2", "o", 2, 1,   17,  -8, 5),
]

@dataclass
class ReverseStep:
    y: int
    x_prev: int
    key: str
    s: str
    j: int
    alpha: int
    beta: int
    c: int
    delta: int
    p: int
    m_prev: int
    k_p: int
    verified_U: bool
    verified_indices: bool
    detail: str

def reverse_one_step_unbounded_p(y: int) -> Optional[ReverseStep]:
    """
    Find a legal parent x_prev for an odd child y by scanning all rows and p >= 0.
    Per row, stop when ((y-delta)/6 - k_p) < 0 (k_p grows like 64^p).
    Returns None if no parent found.
    """
    if y % 2 == 0 or (y % 6) not in (1, 5):
        raise ValueError("y must be odd and ≡ 1 or 5 (mod 6).")

    # filter rows by child family (delta)
    candidates = [r for r in ROWS if r[6] == (1 if y % 6 == 1 else 5)]

    T = (y - (1 if y % 6 == 1 else 5)) // 6  # integral since y ≡ delta mod 6

    for key, s, j, alpha, beta, c, delta in candidates:
        p = 0
        while True:
            num = beta * pow(64, p) + c
            # early stop if num > 9T (then k_p > T, so no solutions for larger p either)
            if num > 9 * T:
                break

            if num % 9 == 0:
                k_p = num // 9
                t = T - k_p
                if t < 0:
                    break  # early stop for this row
                denom = 1 << (alpha + 6*p)
                if t % denom == 0:
                    m_prev = t // denom
                    if m_prev >= 0:
                        p6 = 1 if s == 'e' else 5
                        x_prev = 18*m_prev + 6*j + p6
                        ver_U = (U_odd(y) == x_prev)
                        s_prev, m_chk, j_chk, _ = indices(x_prev)
                        ver_idx = (s_prev == s and j_chk == j and m_chk == m_prev)
                        if ver_U and ver_idx:
                            return ReverseStep(
                                y=y, x_prev=x_prev, key=key, s=s, j=j, alpha=alpha,
                                beta=beta, c=c, delta=delta, p=p, m_prev=m_prev,
                                k_p=k_p, verified_U=ver_U, verified_indices=ver_idx,
                                detail=f"row={key} (s={s},j={j},alpha={alpha},beta={beta},c={c},delta={delta}), p={p}, k_p={k_p}"
                            )
            p += 1

    return None

def reverse_until(y0: int, stop: int = 1, max_steps: int = 10000) -> List[ReverseStep]:
    if y0 % 2 == 0:
        raise ValueError("y0 must be odd.")
    log: List[ReverseStep] = []
    y = y0
    steps = 0
    while y != stop:
        steps += 1
        if steps > max_steps:
            raise RuntimeError("Exceeded max_steps; possible bug or extremely long chain.")
        step = reverse_one_step_unbounded_p(y)
        if step is None:
            raise RuntimeError(f"No legal parent found for y={y}.")
        log.append(step)
        y = step.x_prev
    return log

# ---------- CSV helpers ----------
SINGLE_HEADERS = [
    "y", "x_prev", "row_key", "s_parent", "j_parent",
    "alpha", "beta", "c", "delta_child", "p", "m_prev", "k_p",
    "verified_U", "verified_indices", "detail"
]

def write_single_csv(path: str, step: ReverseStep) -> None:
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(SINGLE_HEADERS)
        w.writerow([
            step.y, step.x_prev, step.key, step.s, step.j,
            step.alpha, step.beta, step.c, step.delta, step.p,
            step.m_prev, step.k_p, step.verified_U, step.verified_indices, step.detail
        ])

CHAIN_HEADERS = [
    "i", "y_child", "x_prev", "row_key", "s_parent", "j_parent",
    "alpha", "beta", "c", "delta_child", "p", "m_prev", "k_p",
    "verified_U", "verified_indices", "detail"
]

def write_chain_csv(path: str, steps: List[ReverseStep]) -> None:
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(CHAIN_HEADERS)
        for i, s in enumerate(steps, start=1):
            w.writerow([
                i, s.y, s.x_prev, s.key, s.s, s.j,
                s.alpha, s.beta, s.c, s.delta, s.p, s.m_prev, s.k_p,
                s.verified_U, s.verified_indices, s.detail
            ])

# ---------- CLI ----------
def main():
    ap = argparse.ArgumentParser(
        description="Row-consistent reverse construction with unbounded p-search (writes CSV)."
    )
    ap.add_argument("--mode", choices=["one", "chain"], default="one",
                    help="one: single reverse step for --y; chain: reverse until --stop.")
    ap.add_argument("--y", type=int, default=None,
                    help="Child odd number y (for --mode one) or start y0 (for --mode chain).")
    ap.add_argument("--stop", type=int, default=1,
                    help="Target ancestor to stop at (used in --mode chain). Default: 1")
    ap.add_argument("--csv", type=str, default=None,
                    help="CSV output file (optional). If omitted, prints a text summary.")
    ap.add_argument("--max-steps", type=int, default=10000, help="Max steps for chain mode.")
    args = ap.parse_args()

    if args.y is None:
        print("Error: --y is required.", file=sys.stderr)
        sys.exit(2)

    if args.mode == "one":
        step = reverse_one_step_unbounded_p(args.y)
        if step is None:
            print(f"No legal parent found for y={args.y}.", file=sys.stderr)
            sys.exit(1)
        if args.csv:
            write_single_csv(args.csv, step)
            print(f"Wrote single-step CSV to {args.csv}")
        else:
            print(f"y={step.y} -> x_prev={step.x_prev}")
            print(step.detail)
            print(f"verified_U={step.verified_U}, verified_indices={step.verified_indices}")
    else:
        steps = reverse_until(args.y, stop=args.stop, max_steps=args.max_steps)
        if args.csv:
            write_chain_csv(args.csv, steps)
            print(f"Wrote chain CSV to {args.csv} ({len(steps)} steps).")
        else:
            print(f"Chain length: {len(steps)}")
            for s in steps:
                print(f"{s.y} <- {s.x_prev} | {s.detail}")

if __name__ == "__main__":
    main()
