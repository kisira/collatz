# tests_unified_rows.py
# Python 3.10+, stdlib only

from dataclasses import dataclass
from typing import Tuple, List

def v2(n: int) -> int:
    c = 0
    while n % 2 == 0:
        n //= 2
        c += 1
    return c

@dataclass
class Row:
    # fixed j and p6 are implied by this row’s design; we store them for checking
    alpha: int
    beta:  int
    c:     int
    delta: int    # 1 for *e, 5 for *o
    j:     int    # 0,1,2
    p6:    int    # 1 or 5
    # closed form at p=0:
    # x' = 6*(2^alpha * m + k) + delta,  where k = (beta + c)/9
    def xprime(self, m: int, p: int = 0) -> int:
        # lifted F(p,m)
        Fpm = ((9*m*(1<<self.alpha) + self.beta) * (1<<(6*p)) + self.c) // 9
        return 6*Fpm + self.delta

# --- your table (p=0 parameters) ---
# Fill with the 12 rows. Example: (alpha,beta,c,delta,j,p6)
ROWS: List[Row] = [
    Row(2,   2,  -2, 1, 0, 1),  # ee0  -> Psi_0
    Row(4,  56,  -2, 1, 1, 1),  # ee1  -> Psi_1
    Row(6, 416,  -2, 1, 2, 1),  # ee2  -> Psi_2
    Row(3,  20,  -2, 1, 0, 5),  # oe0  -> omega_0
    Row(1,  11,  -2, 1, 1, 5),  # oe1  -> omega_1
    Row(5, 272,  -2, 1, 2, 5),  # oe2  -> omega_2
    Row(4,   8,  -8, 5, 0, 1),  # eo0  -> psi_0
    Row(6, 224,  -8, 5, 1, 1),  # eo1  -> psi_1
    Row(2,  26,  -8, 5, 2, 1),  # eo2  -> psi_2
    Row(5,  80,  -8, 5, 0, 5),  # oo0  -> Omega_0
    Row(3,  44,  -8, 5, 1, 5),  # oo1  -> Omega_1
    Row(1,  17,  -8, 5, 2, 5),  # oo2  -> Omega_2
]

def test_row_identity():
    # For each row, sample m values and check 3x'+1 == 2^(alpha+6p) * x
    for row in ROWS:
        for p in (0, 1):          # check p-lift too
            for m in range(0, 7): # small grid is enough to catch mistakes
                x = 18*m + 6*row.j + row.p6
                xp = row.xprime(m, p=p)
                lhs = 3*xp + 1
                rhs = (1 << (row.alpha + 6*p)) * x
                assert lhs == rhs, f"Identity failed for row={row}, m={m}, p={p}"

def test_mod3_ee_reachability():
    # ee rows give B' = B or B+1 mod 3
    # From any B, we can reach any target in ≤2 steps.
    maps = []
    for row in ROWS:
        if row.delta == 1 and row.p6 == 1:  # ee family
            two_alpha_mod3 = pow(2, row.alpha, 3)
            k = (row.beta + row.c)//9
            maps.append((two_alpha_mod3 % 3, k % 3))
    def step(B: int, f: Tuple[int,int]) -> int:
        a, k = f
        return (a*B + k) % 3
    for B0 in range(3):
        reachable = {B0}
        for f in maps:
            reachable.add(step(B0,f))
        for f1 in maps:
            for f2 in maps:
                reachable.add(step(step(B0,f1), f2))
        assert reachable == {0,1,2}, f"EE mod3 reachability failed from B={B0}: got {reachable}"

def test_mod3_oo_reachability():
    # oo rows give B' = 2B + {1,2} mod 3; two steps suffice
    maps = []
    for row in ROWS:
        if row.delta == 5 and row.p6 == 5:  # oo family
            two_alpha_mod3 = pow(2, row.alpha, 3)
            k = (row.beta + row.c)//9
            maps.append((two_alpha_mod3 % 3, k % 3))
    def step(B: int, f: Tuple[int,int]) -> int:
        a, k = f
        return (a*B + k) % 3
    for B0 in range(3):
        reachable = {B0}
        for f1 in maps:
            for f2 in maps:
                reachable.add(step(step(B0,f1), f2))
        assert reachable == {0,1,2}, f"OO mod3 reachability failed from B={B0}: got {reachable}"

def test_parity_toggle_exists_oo_side():
    # Quick parity sanity: at p=0, k = (beta+c)/9; check at least one oo row has k odd
    ks = [ (row.beta + row.c)//9 for row in ROWS if row.delta==5 and row.p6==5 ]
    assert any(k % 2 == 1 for k in ks), f"No odd k among oo rows: {ks}"

if __name__ == "__main__":
    test_row_identity()
    test_mod3_ee_reachability()
    test_mod3_oo_reachability()
    test_parity_toggle_exists_oo_side()
    print("All tests passed.")
