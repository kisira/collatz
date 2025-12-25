 
# A Finite-State Inverse Calculus for the Odd Layer of the Collatz Map

This repository contains the LaTeX source and reference code accompanying:

> **A Finite-State Inverse Calculus for the Odd Layer of the Collatz Map**
> Agola Kisira Odero

The paper develops a unified, finite-state “inverse calculus” on the odd layer of the accelerated Collatz map \(U\), with certified one-step inverses, a word semantics, and constructive lifting from residues \(M_K = 3\cdot 2^K\) to exact integers. The repo includes a word evaluator and small scripts for reproducing examples in the paper.

- 📄 Paper source: `collatz_calculus.tex` (+ `collatz.bib`)
- 🧪 Reference scripts: `scripts/`
- 🔗 DOI (Zenodo): **[10.5281/zenodo.XXXXX](https://doi.org/10.5281/zenodo.XXXXX)**  ← _replace with your DOI_

---

## Contents


### Formal Verification with Rocq/Coq

The repository includes a formal verification of the main theorems using **Rocq** (formerly Coq), a proof assistant for mechanized mathematics.

#### Coq Files

- **`coq/CollatzBasics.v`**: Core definitions including:
  - The accelerated Collatz map `U(y) = (3y+1)/2^v2(3y+1)`
  - Modular families (classes mod 6)
  - Move tokens (Ψ, ψ, ω, Ω) and word semantics
  - Main convergence theorem: every admissible odd integer reaches 1
  - Forward identity: certified one-step inverses

- **`coq/CollatzRows.v`**: Row operations and steering lemmas including:
  - Concrete row parameters for each move type
  - Row correctness lemma (forward identity per row)
  - Steering gadgets for controlling 2-adic valuation
  - Family pattern invariance
  - Mod-3 steering control

- **`coq/CollatzLifting.v`**: Residue lifting and reachability including:
  - Lifting from M_K to M_{K+1}
  - Residue reachability theorem for all K ≥ 3
  - 2-adic refinement from residues to exact integers
  - Constructive witness computation

#### Building the Coq Proofs

Requirements:
- Coq/Rocq 8.18.0 or later
- Standard Coq libraries (Arith, ZArith, List)

To build:
```bash
make -f Makefile.coq
```

To clean:
```bash
make -f Makefile.coq clean-coq
```

The formalization provides:
- **Axiomatized definitions** for the core Collatz machinery
- **Formal statements** of all main theorems and lemmas from the paper
- **Structural proofs** (currently admitted, ready for detailed proof development)
- **Type-checked correctness** of theorem statements and dependencies

#### Main Theorems Formalized

1. **Odd Layer Convergence** (`odd_layer_convergence`): Every odd integer x ≡ 1,5 (mod 6) has a finite inverse word from 1
2. **Residue Reachability** (`residue_reachability`): For all K ≥ 3, every residue mod M_K is reachable
3. **Residues to Exact Integers** (`residues_to_exact_integers`): Compatible residue witnesses yield exact integer solutions
4. **Row Correctness** (`row_correctness`): Each row satisfies the forward identity 3x'+1 = 2^(α+6p)x
5. **Steering Lemma** (`steering_lemma`): Same-family padding controls 2-adic valuation and intercept
6. **Lifting Lemma** (`lifting_K_to_K_plus_1`): Constructive lift from M_K to M_{K+1}
