#!/usr/bin/env python3
# tools/make_witnesses.py
import argparse, csv
from unified import bfs_witnesses

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mod", type=int, required=True, help="Modulus, e.g. 24, 48, 96")
    ap.add_argument("--out", required=True, help="CSV output path")
    ap.add_argument("--max_depth", type=int, default=6, help="BFS depth (default 6)")
    args = ap.parse_args()

    got = bfs_witnesses(args.mod, max_depth=args.max_depth)
    rows = []
    for r in sorted(got.keys()):
        word = ",".join(got[r]["word"])
        x = got[r]["x"]
        rows.append({"residue": r, "word": word, "example_x": x})

    with open(args.out, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["residue","word","example_x"])
        w.writeheader()
        for row in rows:
            w.writerow(row)

    print(f"Wrote {len(rows)} witnesses to {args.out}")

if __name__ == "__main__":
    main()
