#!/usr/bin/env python3
# tools/replay_example.py
import argparse
from unified import UnifiedEvaluator

EXAMPLES = {
    # You can add more canned examples here
    "ex1": ["psi","Omega","omega","psi"],
    "ex2": ["psi","Omega","Omega","omega","psi"],
    "psiOnly": ["psi"],
}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--name", help="Example name (ex1, ex2, psiOnly)", default="ex1")
    ap.add_argument("--x0", type=int, default=1)
    args = ap.parse_args()

    if args.name not in EXAMPLES:
        raise SystemExit(f"Unknown example '{args.name}'. Available: {', '.join(EXAMPLES)}")

    word = EXAMPLES[args.name]
    ev = UnifiedEvaluator()
    res = ev.evaluate(word, x0=args.x0)

    print(f"[{args.name}] x0={res['x0']} -> x_final={res['x_final']} (len={len(word)})")
    for row in res["trace"]:
        print(f" {row['i']:>2d}. {row['token']:>6s} | x={row['x_before']:<8d}  "
              f"(s={row['s_before']}, j={row['j_before']}, m={row['m_before']})  "
              f"-> x'={row['x_after']}  | U(x')={row['U_of_after']} "
              f\"{'OK' if row['forward_ok'] else 'FAIL'}\")

if __name__ == "__main__":
    main()
