/-
Mechanized-honesty audit (P4). `#print axioms` for every theorem in the genuine-proof layer.

A theorem proved with `sorry` shows `sorryAx`; one proved with `native_decide` shows
`Lean.ofReduceBool`; a stray `axiom` shows its own name. So this single pass is the authoritative
check that the proof layer is genuine. `scripts/honesty_audit.sh` runs this and fails CI if any
output mentions `sorryAx` / `ofReduceBool` / `trustCompiler`, or any axiom outside the standard
trio `{propext, Classical.choice, Quot.sound}`.

This file is NOT part of the `F1Square` library target; it is run directly via `lake env lean`.
-/

import F1Square

open UOR.Bridge.F1Square

-- Mechanism (the function-field Hasse mechanism; tropical positivity).
#print axioms Mechanism.hodgeType_iff
#print axioms Mechanism.hasse_q25_a10
#print axioms Mechanism.hasse_q25_a12
#print axioms Mechanism.hasse_q4_a4
#print axioms Mechanism.hasse_q4_a5
#print axioms Mechanism.hasse_q9_a6
#print axioms Mechanism.hasse_q9_a7
#print axioms Mechanism.tropMult_nonneg
#print axioms Mechanism.bezout_line_line
#print axioms Mechanism.bezout_line_conic

-- Template (the product-of-curves Hodge-index template).
#print axioms Template.pair_symm
#print axioms Template.sq_nonneg
#print axioms Template.E1_dot_E2
#print axioms Template.E3_sq
#print axioms Template.H_sq
#print axioms Template.H_sq_pos
#print axioms Template.f1_perp
#print axioms Template.f2_perp
#print axioms Template.Hperp_gram_11
#print axioms Template.Hperp_gram_12
#print axioms Template.Hperp_gram_22
#print axioms Template.Hperp_value
#print axioms Template.Hperp_neg_semidef
#print axioms Template.int_sq_eq_zero
#print axioms Template.Hperp_definite

-- CharOne (the characteristic-1 / max-plus base; R1, R12).
#print axioms CharOne.tAdd_idem
#print axioms CharOne.tAdd_comm
#print axioms CharOne.tAdd_none_left
#print axioms CharOne.tAdd_none_right
#print axioms CharOne.tMul_comm
#print axioms CharOne.tMul_none_left
#print axioms CharOne.tMul_one_left
#print axioms CharOne.csum_append
#print axioms CharOne.csum_reverse
#print axioms CharOne.cycle_reversal_invariant

-- Bridge (the mechanism bridge; the §2.3 control).
#print axioms Bridge.hodge_implies_spectral_bound
#print axioms Bridge.control_psd

-- CycleCounts (R6, exact Bowen–Lanford trace identity).
#print axioms CycleCounts.N1
#print axioms CycleCounts.N2
#print axioms CycleCounts.N3
#print axioms CycleCounts.N4
#print axioms CycleCounts.N5
#print axioms CycleCounts.N6
#print axioms CycleCounts.N7
#print axioms CycleCounts.N8

-- Crux (the property; proved on the Template, OPEN on the square).
#print axioms Crux.template_hodgeIndex

-- v0.2.0 — Tropical closure / κ / spectrum (R2, R3, R4, R9, R10, R11).
#print axioms Tropical.star_matches
#print axioms Tropical.R2_kleene_idempotent
#print axioms Tropical.R3_kappa_perm_invariant
#print axioms Tropical.R4_cycle_spectrum
#print axioms Tropical.R9_same_kappa
#print axioms Tropical.R10_diff_spectrum
#print axioms Tropical.R11_kappa_fiber

-- v0.2.0 — sibling carriers (R14, R15, R16).
#print axioms Tropical.R14_kappaBool_perm_invariant
#print axioms Tropical.R15_faceted_address
#print axioms Tropical.R16_boolean_facet_degenerate

-- v0.2.0 — tropical Hodge-index signatures (§2.3, Babaee–Huh).
#print axioms Tropical.Signature.parallel_pencil
#print axioms Tropical.Signature.delta_gamma_zero
#print axioms Tropical.Signature.fan_degenerate
#print axioms Tropical.Signature.fan_kernel
#print axioms Tropical.Signature.fan_basis_nonpos
#print axioms Tropical.Signature.bh_two_positive_dirs

-- v0.2.0 — exact ℚ analysis brick.
#print axioms Analysis.Qeq_refl
#print axioms Analysis.reduce_6_8
#print axioms Analysis.reduce_idem
#print axioms Analysis.reduce_idem_neg
#print axioms Analysis.reduce_preserves_value
#print axioms Analysis.same_address_iff_eq
#print axioms Analysis.add_sample
#print axioms Analysis.mul_sample
#print axioms Analysis.Qle_sample

-- v0.3.0 — the ℤ ring normalizer (reflective canonical polynomial form) and its soundness.
#print axioms Analysis.RingNF.minsert_sound
#print axioms Analysis.RingNF.mmul_sound
#print axioms Analysis.RingNF.pinsert_sound
#print axioms Analysis.RingNF.padd_sound
#print axioms Analysis.RingNF.pscaleMono_sound
#print axioms Analysis.RingNF.pmul_sound
#print axioms Analysis.RingNF.pneg_sound
#print axioms Analysis.RingNF.norm_sound
#print axioms Analysis.RingNF.nf_eq
#print axioms Analysis.RingNF.sq_add
#print axioms Analysis.RingNF.mul_diff
#print axioms Analysis.RingNF.sq_add3
#print axioms Analysis.RingNF.distrib_comm

-- v0.3.0 — general ℚ field laws (via the normalizer).
#print axioms Analysis.add_comm
#print axioms Analysis.mul_comm
#print axioms Analysis.mul_assoc
#print axioms Analysis.add_assoc
#print axioms Analysis.mul_add
#print axioms Analysis.mul_one
#print axioms Analysis.add_zero
#print axioms Analysis.add_neg

-- v0.3.0 — constructive ℝ (Bishop regular sequences over ℚ).
#print axioms Analysis.Qsub_self_num
#print axioms Analysis.Qsub_swap_num
#print axioms Analysis.Qsub_swap_den
#print axioms Analysis.const_regular
#print axioms Analysis.Req_refl
#print axioms Analysis.Req_symm
#print axioms Analysis.ofQ_respects
#print axioms Analysis.Pos_half

-- v0.4.0 — the from-scratch `ring_uor` tactic (sample theorems it discharges, axiom-clean).
#print axioms Analysis.RingNF.ring_uor_sq
#print axioms Analysis.RingNF.ring_uor_cube
#print axioms Analysis.RingNF.ring_uor_telescope

-- v0.4.0 — ℚ as a verified ordered field.
#print axioms Analysis.Qle_refl
#print axioms Analysis.Qeq_le
#print axioms Analysis.Qle_trans
#print axioms Analysis.Qabs_Qeq
#print axioms Analysis.Qle_congr_left
#print axioms Analysis.Qle_congr_right
#print axioms Analysis.Qadd_le_add
#print axioms Analysis.Qabs_add_le
#print axioms Analysis.Qabs_sub_add4

-- v0.4.0 — denominator-positivity helpers.
#print axioms Analysis.add_den_pos
#print axioms Analysis.Qsub_den_pos
#print axioms Analysis.Qabs_den_pos

-- v0.4.0 — ℝ arithmetic (negation + Bishop addition, regularity proved).
#print axioms Analysis.Qbound_den_pos
#print axioms Analysis.Qabs_Qsub_neg
#print axioms Analysis.Rneg
#print axioms Analysis.Radd
#print axioms Analysis.Rneg_Rneg_seq
