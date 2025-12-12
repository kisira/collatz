#!/usr/bin/env python3
# tools/check_rows.py
from unified import indices, U_odd, BLOCK_FORMULAS, TOKEN_BLOCK, UnifiedEvaluator

def check_one_block(block: str, samples=200) -> int:
    """
    For each j in {0,1,2}, sample x of the right family/index j,
    apply the block formula and verify U(child) == parent.
    Returns number of failures.
    """
    failures = 0
    ev = UnifiedEvaluator()
    # families per block
    fam = 'e' if block in ('ee','eo') else 'o'

    # sample m and p6
    tried = 0
    for j in (0,1,2):
        f = BLOCK_FORMULAS[block][j]
        m = 0
        cnt = 0
        while cnt < samples:
            # build an x with desired (s=fam, j)
            # x = 18m + 6j + p6, pick p6 by family
            p6 = 1 if fam == 'e' else 5
            x = 18*m + 6*j + p6
            if x <= 0:
                m += 1; continue
            s, M, J, _ = indices(x)
            if s == fam and J == j:
                y = f(M)
                ok = (U_odd(y) == x)
                if not ok:
                    print(f"[FAIL] block={block}, j={j}, x={x}, child={y}, U(child)={U_odd(y)}")
                    failures += 1
                cnt += 1
            m += 1
            tried += 1
            if tried > 100000:
                break
    return failures

def main():
    total = 0
    for block in ('ee','eo','oe','oo'):
        fail = check_one_block(block)
        print(f"Block {block}: failures={fail}")
        total += fail
    if total == 0:
        print("All checks passed.")
    else:
        print(f"Total failures: {total}")

if __name__ == "__main__":
    main()
