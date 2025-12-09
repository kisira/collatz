In this folder are Rocq/Coq proofs of the paper constituting its formalisation. This formalisation was done in Rocq version 9.1.0.

In the sections folder the proofs are broken out by the sections in the the paper.  The other unclassified proofs in this folder are general and/or interesting proofs regardless of section.

Every Teorem, lemma and corollary had been fully proven, in a few cases an axiom may be stated in place of a proof that can be found elswhere among these files. In every case where an axiom is stated in palce of a proof, a comment above the axiom points out where that proof may be found.

Every .v file has been made stand-alone to the extent possible and there may be facts that are proven more than once throughout the different sections.

Below is an overview of the fomalisation:

================================================================================
INDEX OF ROCQ/COQ FORMALIZATION
"An Inverse Calculus for the Odd Layer of the Collatz Map"
================================================================================

This index maps the verified Coq files (.v) to the corresponding Lemmas,
Theorems, and Sections in the paper.

--------------------------------------------------------------------------------
PART I: ALGEBRAIC FOUNDATIONS
(Establishing the Unified Table, Row Identities, and Completeness)
--------------------------------------------------------------------------------

File: Sec02_notation_indices_and_moves.v
- Paper Result: Corollary 2.3 (Family and indices from the tag)
- Coq Proof:    cor_tag_indices_plain
- Logic:        Verifies the bijection between the CRT tag t = (x-1)/2 and
                the tuple (family, router, m).

File: Sec4_Drift.v
- Paper Result: Proposition 4.2 & Corollary 4.3 (Drift Equation)
- Coq Proof:    diff_equation_correct
- Logic:        Rigorously proves ΔV = rK + Δ_ε. Uses `pow64_decomp` to
                handle p-lift arithmetic modulo 9.

File: Sec08_row_correctness_family_pattern_and_word_semantics.v
- Paper Result: Lemma 7.1 (Row Correctness) & Lemma 7.3 (Monotonicity)
- Coq Proof:    lem_row_correctness, forward_monotonicity_by_row_and_lift
- Logic:        Explicitly proves 3x' + 1 = 2^(α+6p)x for any row and
                formally verifies forward contraction/expansion conditions.

File: Sec09_algebraic_completeness_of_rows_and_texorpdfstringp.v
- Paper Result: Proposition 9.1 (Row/Lift Completeness)
- Coq Proof:    rows_and_lifts_are_complete_odd
- Logic:        Proves that *every* valid odd step 3y+1 = 2^e x corresponds
                to a specific row r and lift p in the unified table.

File: Sec11_row_level_invariance_and_many_realizations.v
- Paper Result: Lemma 11.2 & Lemma 11.5 (Invariance)
- Coq Proof:    uniqueness_across_all_realizations
- Logic:        Proves that different (row, p) pairs realizing the same
                arithmetic step produce identical output values y.

File: Sec12_row_design_and_the_forward_identity.v
- Paper Result: Lemma 12.1 (Forward identity for a lifted row)
- Coq Proof:    forward_identity_via_rows
- Logic:        Mathematical justification that the "Unified Table" works
                correctly for all column lifts p >= 0.

File: Sec13_super_families_via_pdfmathp.v
- Paper Result: Section 13 (Super-families)
- Coq Proof:    super_family_completeness
- Logic:        Formalizes the splitting of exponents into (a = e mod 6)
                and (p = e/6), linking the table to all possible exponents.

File: Sec42_appendix_e_derivation_of_the_identity_texorpdfstring3x_p12alpha6p.v
- Paper Result: Theorem E.1 (Appendix E: Algebraic Derivation)
- Coq Proof:    Forward_identity_for_a_lifted_row
- Logic:        The "Engine Room": rigorous Z-arithmetic proof of the
                forward identity from abstract parameter constraints.

--------------------------------------------------------------------------------
PART II: DYNAMICAL MECHANICS
(Word Semantics, Affine Composition, and Expansion)
--------------------------------------------------------------------------------

File: Sec15_evolution_of_the_index_m_along_inverse_words.v
- Paper Result: Proposition 15.1 (m_n closed form) & Lemma 15.3
- Coq Proof:    inv_word_affine, m_after_inverse_word
- Logic:        Proves by induction that inverse words act as linear maps
                m -> Am + B and validates composition laws for A and B.

File: Sec28_DriftAndGeometry.v
- Paper Result: Section 28 (Drift/Geometry), Section 17 (Operator Projection)
- Coq Proof:    gain_expansive_except_singularities
- Logic:        Defines rational operators (A, B). Proves that for all
                non-singular tokens (and all p >= 1), slope A > 1 (Expansion).

File: Sec29_DynamicalImplication.v
- Paper Result: Theorem 29.1 (The Semantic Link)
- Coq Proof:    thm_dynamical_implication
- Logic:        Proves that if x_W(m) = x, then applying the forward Collatz
                map U exactly |W| times to x yields 1.

File: Sec17_geometric_series_simplifications_for_texorpdfstringm_n.v
- Paper Result: Corollary 17.2 (x_n from m_n)
- Coq Proof:    cor_xn_from_mn
- Logic:        Verifies the translation between internal index m and global x.

--------------------------------------------------------------------------------
PART III: ALGORITHMIC CORE (LIFTING & STEERING)
(Constructive existence of witnesses)
--------------------------------------------------------------------------------

File: Sec18_residue_targeting_via_a_last_row_congruence.v
- Paper Result: Lemma 18.1 (Last-row congruence), Corollary 18.2 (Pinning)
- Coq Proof:    lem_last_row_p, cor_pinning
- Logic:        Uses Bezout's identity to prove the linear congruence
                a^(p)m = r (mod M_K) is solvable iff the GCD condition holds.

File: Sec24_linear_2_adic_lifting_from_congruences_to_equality.v
- Paper Result: Lemma 24.1 (Linear 2-adic lifting)
- Coq Proof:    lem_linear_hensel, linear_2adic_class
- Logic:        Proves that divisibility (2^s | b) implies the existence of
                an exact integer m, bridging modular residues to Z.

File: Sec14_samefamily_padding_as_emphsteering.v
- Paper Result: Lemma 14.2 (Monotone Lifting)
- Coq Proof:    pad_reaches_any_target
- Logic:        Proves that appending same-family tokens can strictly
                increase v_2(A) to exceed any target K ("Bit Pump").

File: Sec19_same_family_steering_menu_and_monotone_padding_p0.v
- Paper Result: Lemma 19.3 (Finite Menu Monotone Padding)
- Coq Proof:    lem_monotone_padding
- Logic:        Proves that a finite menu of gadgets is sufficient to
                reach any K while preserving family.

File: Sec34_mod_3_steering_in_the_same_family.v
- Paper Result: Lemma 14.1 / Appendix A (Mod-3 Steering)
- Coq Proof:    lem_mod3_steer
- Logic:        Proves that for any odd x (not div by 3), there exists a
                token in the current family valid modulo 3 ("Liveness").

File: Sec38_appendix_a_mod_three_steering.v
- Paper Result: Appendix A (Concrete Steering Gadgets)
- Coq Proof:    lem_mod3_steering
- Logic:        Explicitly constructs gadgets to reach any target B mod 3.

--------------------------------------------------------------------------------
PART IV: ROUTING & STABILITY
(Ensuring prefixes remain valid under padding)
--------------------------------------------------------------------------------

File: Sec21_same_family_steering_menu_and_monotone_padding_across_columns.v
- Paper Result: Lemma 21.1 (One-step composition with floor)
- Coq Proof:    lem_one_step_floor
- Logic:        Algebraic update rule for (A, B) when composing with floor,
                proving noise accumulates linearly.

File: Sec22_routing_compatibility_no_branch_flips.v
- Paper Result: Lemma 22.1 (Routing compatibility)
- Coq Proof:    lem_TD2_routing, cor_stable_padding
- Logic:        Proves that fixing m mod 2^S freezes the router path,
                ensuring no branch flips occur during lifting.

File: Sec20_routing_compatibility_of_a_fixed_prefix_under_tail_padding.v
- Logic:        Interface definitions connecting concrete algebra (Sec 21)
                to abstract routing stability (Sec 22).

--------------------------------------------------------------------------------
PART V: HIGH-LEVEL ASSEMBLY
(The Final Proof)
--------------------------------------------------------------------------------

File: Sec25_steering_gadget_menu_explicit_algebra_and_finite_padding_controls.v
- Paper Result: Theorem 25.1 (Base Coverage at 24)
- Coq Proof:    thm_base_coverage_24
- Logic:        Exhaustively verifies base witnesses for residues mod 24.

File: Sec32_rowconsistent_reversibility_with_optional_texorpdfstringp.v
- Paper Result: Algorithm 4 (Reverse Search) & Corollary 18.2
- Coq Proof:    cor_alg_complete_reverse
- Logic:        Proves that the reverse search algorithm is complete (will
                find a parent if one exists).

File: Sec27_and_31_assembly_into_the_main_theorem_mocked.v
- Paper Result: Theorem 16.1 (Global odd-layer realization)
- Coq Proof:    thm_odd_layer_global_0, Algorithmic_construction_and_termination
- Logic:        The "Roof": Composes Base Coverage, Steering, and Lifting
                to prove a witness exists for *every* odd x.

File: Sec33_from_residues_to_exact_integers.v
File: Sec35_synthesis_how_the_pieces_yield_convergence_on_the_odd_layer.v
- Paper Result: Corollary 35.2 (Finite convergence)
- Coq Proof:    thm_odd_layer_convergence
- Logic:        Final synthesis: Witness existence => Collatz Truth.
