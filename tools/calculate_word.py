#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
calculate_word.py

Given a positive odd integer x0, compute its forward odd-accelerated Collatz
orbit to 1, then convert the reversed orbit into a legal inverse word
W ∈ {Psi, psi, omega, Omega}* that maps 1 -> x0. Optionally verifies each
step against the unified p=0 table formulas.

Usage:
  python calculate_word.py 497
  python calculate_word.py 497 --json-out 497_word.json
  python calculate_word.py 497 --no-verify
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import List, Tuple

# ---------- basic arithmetic ----------

def v2(n: int) -> int:
    """2-adic valuation v2(n) for n>0."""
    if n <= 0:
        raise ValueError("v2 expects a positive integer")
    c = 0
    while (n & 1) == 0:
        n >>= 1
        c += 1
    return c

def U_odd(y: int) -> int:
    """Accelerated odd Collatz map U on odds."""
    s = v2(3*y + 1)
    return (3*y + 1) >> s

def family(x: int) -> str:
    """Return 'e' if x ≡ 1 (mod 6), 'o' if x ≡ 5 (mod 6)."""
    r = x % 6
    if r == 1:
        return 'e'
    if r == 5:
        return 'o'
    raise ValueError(f"x={x} not in odd-layer families (1 or 5 mod 6)")

def indices(x: int) -> Tuple[str, int, int, int]:
    """Return (s, m, j, r) with s∈{'e','o'}, m=floor(x/18), j=floor(x/6) mod 3, r=floor(x/6)."""
    s = family(x)
    r = x // 6
    j = r % 3
    m = x // 18
    return s, m, j, r

# ---------- unified p=0 table: x' = 6F(0,m)+delta ----------

def preimage_from_row(x: int, token: str) -> int:
    """
    Given current x (odd, in {1,5} mod 6) and a token in {'Psi','psi','omega','Omega'},
    compute x' using the unified p=0 closed forms. This is the *inverse* step: U(x') = x.
    """
    s, m, j, _ = indices(x)

    if token == 'Psi':        # 'ee' : allowed only if s='e'
        if s != 'e': raise ValueError("Psi requires x ≡ 1 (mod 6)")
        if j == 0:  return 24*m + 1
        if j == 1:  return 96*m + 37
        if j == 2:  return 384*m + 277

    elif token == 'psi':      # 'eo' : allowed only if s='e'
        if s != 'e': raise ValueError("psi requires x ≡ 1 (mod 6)")
        if j == 0:  return 96*m + 5
        if j == 1:  return 384*m + 149
        if j == 2:  return 24*m + 17

    elif token == 'omega':    # 'oe' : allowed only if s='o'
        if s != 'o': raise ValueError("omega requires x ≡ 5 (mod 6)")
        if j == 0:  return 48*m + 13
        if j == 1:  return 12*m + 7
        if j == 2:  return 192*m + 181

    elif token == 'Omega':    # 'oo' : allowed only if s='o'
        if s != 'o': raise ValueError("Omega requires x ≡ 5 (mod 6)")
        if j == 0:  return 192*m + 53
        if j == 1:  return 48*m + 29
        if j == 2:  return 12*m + 11

    else:
        raise ValueError(f"Unknown token '{token}'")

    raise RuntimeError("Invalid j index")

def token_from_transition(s_from: str, s_to: str) -> str:
    """
    Map a *forward* family transition (s_from = family(y), s_to = family(x)) to its token.
    In forward time y -> x, in inverse time x --token--> y.
    """
    if   s_to == 'e' and s_from == 'e': return 'Psi'
    elif s_to == 'o' and s_from == 'e': return 'psi'
    elif s_to == 'e' and s_from == 'o': return 'omega'
    elif s_to == 'o' and s_from == 'o': return 'Omega'
    else:
        raise RuntimeError(f"Unexpected family transition {s_from}->{s_to}")

# ---------- main recovery ----------

@dataclass
class StepRecord:
    i: int
    y: int        # forward: y -> x
    x: int
    s_y: str
    s_x: str
    token: str
    xprime_from_table: int  # computed via row formulas
    verified: bool          # U(xprime) == x and xprime == y

def forward_odd_orbit(x0: int) -> List[int]:
    """Return [x0, x1, x2, ..., 1] under the odd-accelerated map U."""
    if x0 <= 0 or (x0 % 2 == 0):
        raise ValueError("x0 must be a positive odd integer")
    seq = [x0]
    x = x0
    while x != 1:
        x = U_odd(x)
        seq.append(x)
    return seq

def recover_word_from_forward_orbit(x0: int, verify: bool = True) -> Tuple[List[str], List[StepRecord]]:
    """
    Given an odd x0, compute its forward U-orbit to 1 and convert it into a legal inverse word.
    Returns (word_from_1_to_x0, per_step_records).

    word[0] takes 1 -> something, and the full word takes 1 -> x0.
    """
    seq = forward_odd_orbit(x0)       # [x0, x1, ..., 1]
    records: List[StepRecord] = []
    tokens_reversed: List[str] = []   # tokens from x0 down to 1 (inverse direction)

    for i in range(len(seq)-1):
        y = seq[i]       # current (forward)
        x = seq[i+1]     # next (forward)
        s_y = family(y)
        s_x = family(x)
        tok = token_from_transition(s_from=s_y, s_to=s_x)

        ok = True
        xprime = -1
        if verify:
            xprime = preimage_from_row(x, tok)
            ok = (U_odd(xprime) == x) and (xprime == y)

        records.append(StepRecord(
            i=i+1, y=y, x=x, s_y=s_y, s_x=s_x,
            token=tok, xprime_from_table=xprime, verified=ok
        ))
        tokens_reversed.append(tok)

    # We want the word that maps 1 -> x0, i.e. reverse the tokens:
    word = list(reversed(tokens_reversed))
    return word, records

# ---------- CLI ----------

if __name__ == "__main__":
    import argparse, json

    ap = argparse.ArgumentParser(description="Recover a legal inverse word from a forward odd U-orbit.")
    ap.add_argument("x0", type=int, help="positive odd integer")
    ap.add_argument("--no-verify", action="store_true", help="skip per-step row verification")
    ap.add_argument("--json-out", type=str, default="", help="optional path to save a JSON report")
    args = ap.parse_args()

    word, recs = recover_word_from_forward_orbit(args.x0, verify=(not args.no_verify))

    print(f"# x0 = {args.x0}")
    print(f"# Word length = {len(word)}")
    print("Word (from 1 to x0):")
    print(" ".join(word))

    all_ok = all(r.verified for r in recs)
    print(f"\nAll steps verified via unified p=0 rows: {all_ok}")

    if args.json_out:
        payload = {
            "x0": args.x0,
            "word": word,
            "verified_all": all_ok,
            "steps": [r.__dict__ for r in recs],
        }
        with open(args.json_out, "w") as f:
            json.dump(payload, f, indent=2)
        print(f"Wrote {args.json_out}")
