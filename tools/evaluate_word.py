#!/usr/bin/env python3
# tools/evaluate_word.py
import argparse, sys, csv
from unified import UnifiedEvaluator

def parse_word(s: str):
    # word like: psi,Omega,omega,psi
    parts = [p.strip() for p in s.split(',') if p.strip()]
    for p in parts:
        if p not in ("Psi","psi","omega","Omega"):
            raise SystemExit(f"Unknown token '{p}'. Allowed: Psi, psi, omega, Omega.")
    return parts

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--word", required=True, help="Comma-separated tokens, e.g. 'psi,Omega,omega'")
    ap.add_argument("--x0", type=int, default=1, help="Start odd (default 1)")
    ap.add_argument("--csv", default="", help="Optional CSV path for detailed trace")
    args = ap.parse_args()

    word = parse_word(args.word)
    ev = UnifiedEvaluator()
    res = ev.evaluate(word, x0=args.x0)

    print(f"x0={res['x0']}, x_final={res['x_final']}, length={res['length']}")
    for row in res["trace"]:
        print(f" {row['i']:>2d}. {row['token']:>6s} | x={row['x_before']:<8d}  "
              f"(s={row['s_before']}, j={row['j_before']}, m={row['m_before']})  "
              f"-> x'={row['x_after']}  "
              f"| U(x')={row['U_of_after']} {'OK' if row['forward_ok'] else 'FAIL'}")

    if args.csv:
        with open(args.csv, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(res["trace"][0].keys()))
            w.writeheader()
            for r in res["trace"]:
                w.writerow(r)
        print(f"Wrote trace CSV to {args.csv}")

if __name__ == "__main__":
    main()
