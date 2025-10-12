from __future__ import annotations
from dataclasses import dataclass, asdict
from typing import List, Dict, Any, Tuple, Optional
import csv
import pandas as pd
import sys

# -------- helpers --------
def v2(n: int) -> int:
    """2-adic valuation ν2(n) for n>0."""
    c = 0
    while n & 1 == 0:
        n >>= 1
        c += 1
    return c

def U_odd(y: int) -> int:
    """Accelerated odd Collatz map U on odds."""
    s = v2(3*y + 1)
    return (3*y + 1) >> s

# -------- per-step record --------
@dataclass
class StepRowUT:
    i: int
    token: str
    block: str               # 'ee','eo','oe','oo'
    x_before: int
    s_before: str            # 'e' or 'o'
    m_before: int
    j_before: int
    r_before: int
    formula: str             # human-readable closed form
    x_after: int             # computed preimage (child)
    s_after: str
    m_after: int
    j_after: int
    r_after: int
    # unified-table annotation
    ut_row_found: bool
    ut_col_name: Optional[str]
    # forward consistency
    U_of_after: int
    idx_check_ok: bool       # (U(x_after) == x_before) and index advances

class UnifiedWordEvaluator:
    """
    Evaluate words using the unified p=0 table semantics.

    Token → type block:
      Psi  -> ee  (allowed only if current x ≡ 1 mod 6)
      psi  -> eo  (allowed only if current x ≡ 1 mod 6)
      omega-> oe  (allowed only if current x ≡ 5 mod 6)
      Omega-> oo  (allowed only if current x ≡ 5 mod 6)

    Row selection:
      s = 'e' if x % 6 == 1 else 'o'
      r = x // 6
      j = r % 3
      m = x // 18
      Then use the closed form x' listed for (block, s, j).

    Optional: pass a unified table DataFrame (with columns 'image','col0','col1',...)
    to annotate which column the computed child sits in.
    """

    def __init__(self, df_unified: Optional[pd.DataFrame] = None):
        self.set_table(df_unified)

    # ---------- unified table plumbing ----------
    def set_table(self, df: Optional[pd.DataFrame]) -> None:
        self.df = None
        self.preimage_cols: List[str] = []
        self.row_index: Dict[int, Dict[str,int]] = {}
        if df is None:
            return
        if "image" not in df.columns:
            raise ValueError("Unified table must contain an 'image' column.")
        pre_cols = [c for c in df.columns if str(c).startswith("col")]
        if not pre_cols:
            raise ValueError("Unified table requires preimage columns like 'col0','col1',....")
        self.df = df.copy()
        self.preimage_cols = pre_cols
        self.row_index = {}
        for _, row in self.df.iterrows():
            x = int(row["image"])
            cols = {}
            for c in self.preimage_cols:
                val = row[c]
                if pd.isna(val):
                    continue
                try:
                    cols[c] = int(val)
                except Exception:
                    continue
            self.row_index[x] = cols

    @classmethod
    def from_csv(cls, path: str) -> "UnifiedWordEvaluator":
        df = pd.read_csv(path)
        return cls(df)

    # ---------- indices ----------
    @staticmethod
    def family(x: int) -> str:
        r = x % 6
        if r == 1: return 'e'
        if r == 5: return 'o'
        raise ValueError(f"x={x} not in families (1 or 5 mod 6)")

    @staticmethod
    def indices(x: int) -> Tuple[str,int,int,int]:
        s = UnifiedWordEvaluator.family(x)
        r = x // 6
        j = r % 3
        m = x // 18
        return s, m, j, r

    # ---------- token → block and block formulas ----------
    @staticmethod
    def token_block(token: str, s: str) -> str:
        if token == 'Psi':
            if s != 'e': raise ValueError("Psi allowed only when x ≡ 1 (mod 6).")
            return 'ee'
        if token == 'psi':
            if s != 'e': raise ValueError("psi allowed only when x ≡ 1 (mod 6).")
            return 'eo'
        if token == 'omega':
            if s != 'o': raise ValueError("omega allowed only when x ≡ 5 (mod 6).")
            return 'oe'
        if token == 'Omega':
            if s != 'o': raise ValueError("Omega allowed only when x ≡ 5 (mod 6).")
            return 'oo'
        raise ValueError(f"Unknown token '{token}'")

    @staticmethod
    def next_from_block(block: str, s: str, j: int, m: int) -> Tuple[int,str]:
        """
        Return (x_after, formula_string) from the unified p=0 table.
        We inline the closed forms (no min/max semantics here).
        """
        if block == 'ee':  # Psi, s must be 'e'
            if s != 'e': raise RuntimeError("Block 'ee' requires s='e'.")
            if   j == 0: return 24*m + 1,   "x' = 24*m + 1"
            elif j == 1: return 96*m + 37,  "x' = 96*m + 37"
            elif j == 2: return 384*m + 277,"x' = 384*m + 277"
        elif block == 'eo':  # psi, s must be 'e'
            if s != 'e': raise RuntimeError("Block 'eo' requires s='e'.")
            if   j == 0: return 96*m + 5,   "x' = 96*m + 5"
            elif j == 1: return 384*m + 149,"x' = 384*m + 149"
            elif j == 2: return 24*m + 17,  "x' = 24*m + 17"
        elif block == 'oe':  # omega, s must be 'o'
            if s != 'o': raise RuntimeError("Block 'oe' requires s='o'.")
            if   j == 0: return 48*m + 13,  "x' = 48*m + 13"
            elif j == 1: return 12*m + 7,   "x' = 12*m + 7"
            elif j == 2: return 192*m + 181,"x' = 192*m + 181"
        elif block == 'oo':  # Omega, s must be 'o'
            if s != 'o': raise RuntimeError("Block 'oo' requires s='o'.")
            if   j == 0: return 192*m + 53, "x' = 192*m + 53"
            elif j == 1: return 48*m + 29,  "x' = 48*m + 29"
            elif j == 2: return 12*m + 11,  "x' = 12*m + 11"
        else:
            raise RuntimeError(f"Unknown block '{block}'")
        raise RuntimeError(f"Invalid j={j} (must be 0,1,2)")

    # ---------- evaluate ----------
    def evaluate(self, word: List[str], x0: int = 1) -> Dict[str, Any]:
        """
        Evaluate a word from x0 using the unified table rules.
        Returns a dict with x0, x_final, length, and a detailed per-step trace.
        """
        x = int(x0)
        rows: List[StepRowUT] = []

        for i, token in enumerate(word, start=1):
            s0, m0, j0, r0 = self.indices(x)
            block = self.token_block(token, s0)
            y, formula = self.next_from_block(block, s0, j0, m0)

            # unified table check for the row 'image == x'
            ut_row = self.row_index.get(x, None)
            ut_found = False
            ut_col = None
            if ut_row is not None:
                for col_name, val in ut_row.items():
                    if val == y:
                        ut_found = True
                        ut_col = col_name
                        break

            s1, m1, j1, r1 = self.indices(y)

            # forward consistency: U(y) should equal x, and indices advance (r,m) -> (3*r+j, 3*m+j)
            u = U_odd(y)
            idx_ok = (u == x)
            rows.append(StepRowUT(
                i=i, token=token, block=block,
                x_before=x, s_before=s0, m_before=m0, j_before=j0, r_before=r0,
                formula=formula,
                x_after=y,  s_after=s1,  m_after=m1,  j_after=j1,  r_after=r1,
                ut_row_found=(ut_row is not None), ut_col_name=ut_col,
                U_of_after=u, idx_check_ok=idx_ok
            ))
            x = y

        return {
            "x0": x0,
            "x_final": x,
            "length": len(word),
            "trace": [asdict(r) for r in rows]
        }

    @staticmethod
    def save_trace_csv(result: Dict[str, Any], path: str) -> None:
        rows = result["trace"]
        if not rows:
            with open(path, "w", newline="") as f:
                csv.writer(f).writerow(["empty_trace"])
            return
        with open(path, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
            w.writeheader()
            for r in rows:
                w.writerow(r)
def main():
    word = ['psi','Omega','Omega','Omega','omega','Psi','Psi','Psi',
            'psi','Omega','Omega','Omega','Omega','Omega','Omega','Omega','Omega',
            'omega','psi','omega','psi','Omega','Omega','omega','psi',
            'Omega','Omega','omega','psi','Omega','omega','psi','omega',
            'Psi','psi','Omega','Omega','Omega']

    # If you want CSV verification/annotation:
    # ev = UnifiedWordEvaluator.from_csv("your_unified_table.csv")

    ev = UnifiedWordEvaluator()  # without CSV
    #word = ['psi','omega','Psi']  # example tokens
    res = ev.evaluate(word, x0=1)
    print(res["x_final"])
    # Save detailed CSV:
    UnifiedWordEvaluator.save_trace_csv(res, "word_trace_from_1.csv")    
    res = ev.evaluate(word, x0=19)
    print(res["x_final"])
    # Save detailed CSV:
    UnifiedWordEvaluator.save_trace_csv(res, "word_trace_from_19.csv")
    res = ev.evaluate(word, x0=55)
    print(res["x_final"])
    # Save detailed CSV:
    UnifiedWordEvaluator.save_trace_csv(res, "word_trace_from_55.csv")

if __name__ == "__main__":
    sys.exit(main())