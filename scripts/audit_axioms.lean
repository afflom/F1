/-
Mechanized-honesty audit (P4). `#print axioms` for every theorem in the genuine-proof layer.

A theorem proved with `sorry` shows `sorryAx`; one proved with `native_decide` shows
`Lean.ofReduceBool`; a stray `axiom` shows its own name. So this single pass is the authoritative
check that the proof layer is genuine. `scripts/honesty_audit.sh` runs this and fails CI if any
output mentions `sorryAx` / `ofReduceBool` / `trustCompiler`, or any axiom outside the minimal,
choice-free pair `{propext, Quot.sound}` (both forced by `omega`/`simp`/`Int` core internals).

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

-- v0.5.0 — ℚ Archimedean + strict order (for ≈-transitivity).
#print axioms Analysis.Qle_or_Qlt
#print axioms Analysis.Qabs_sub_triangle
#print axioms Analysis.Qarch

-- v0.5.0 — ℚ multiplication and order (consumed by ℝ multiplication).
#print axioms Analysis.Qabs_mul
#print axioms Analysis.Qmul_le_mul_left
#print axioms Analysis.Qmul_le_mul_right
#print axioms Analysis.Qmul_le_mul
#print axioms Analysis.Qabs_mul_diff
#print axioms Analysis.Qabs_le_add
#print axioms Analysis.Qmul_den_pos
#print axioms Analysis.Qabs_num_nonneg

-- v0.5.0 — ℝ: ≈ is an equivalence; ℝ multiplication with regularity.
#print axioms Analysis.Req_of_seq_Qeq
#print axioms Analysis.Req_trans
#print axioms Analysis.Radd_comm
#print axioms Analysis.Radd_neg
#print axioms Analysis.canon_bound
#print axioms Analysis.Ridx_succ
#print axioms Analysis.Rmul
#print axioms Analysis.Rmul_comm

-- v0.5.0 — operation-congruence over ≈ (well-definedness on the setoid).
#print axioms Analysis.Rneg_congr
#print axioms Analysis.Radd_congr
#print axioms Analysis.Rsub_congr

-- v0.5.0 — ℂ = ℝ×ℝ with all four operations and commutative multiplication.
#print axioms Analysis.Ceq_refl
#print axioms Analysis.Ceq_symm
#print axioms Analysis.Ceq_trans
#print axioms Analysis.Cadd_comm
#print axioms Analysis.Cadd_neg
#print axioms Analysis.Cmul_re
#print axioms Analysis.Cmul_im
#print axioms Analysis.Cmul_comm

-- v0.6.0 — the well-definedness engine (generalized Archimedean lemma + linear-bound criterion).
#print axioms Analysis.Qscale_le
#print axioms Analysis.Qarch_gen
#print axioms Analysis.Ridx_ge
#print axioms Analysis.Qconst_le
#print axioms Analysis.Rgap_le
#print axioms Analysis.Rcross_le
#print axioms Analysis.Req_of_lin_bound
#print axioms Analysis.Rmul_gap
#print axioms Analysis.Qabs_two_diff_gen
#print axioms Analysis.canon_bound_mul
#print axioms Analysis.canon_bound_le

-- v0.6.0 — ℝ as a commutative ring up to ≈ (multiplication well-defined on the setoid).
#print axioms Analysis.Rmul_congr
#print axioms Analysis.Rmul_one
#print axioms Analysis.Radd_assoc
#print axioms Analysis.Rmul_distrib
#print axioms Analysis.Rmul_assoc
#print axioms Analysis.Rmul_zero
#print axioms Analysis.Radd_zero
#print axioms Analysis.Rsub_zero
#print axioms Analysis.Rmul_distrib_right
#print axioms Analysis.Rsub_Radd_Radd
#print axioms Analysis.Radd_swap
#print axioms Analysis.Rmul_neg_left
#print axioms Analysis.Rmul_neg_right
#print axioms Analysis.Rmul_sub_distrib
#print axioms Analysis.Rmul_sub_distrib_right
#print axioms Analysis.Rreassoc_sub
#print axioms Analysis.Rreassoc_add

-- v0.6.0 — ℂ as a commutative ring up to ≈.
#print axioms Analysis.Cadd_assoc
#print axioms Analysis.Cmul_one
#print axioms Analysis.Cmul_distrib
#print axioms Analysis.Cmul_assoc

-- v0.7.0 — Cauchy completeness of ℝ (every regular sequence of reals converges).
#print axioms Analysis.Qfrac_le
#print axioms Analysis.Qcollapse_le
#print axioms Analysis.RlimSeq_regular
#print axioms Analysis.Rlim
#print axioms Analysis.Rlim_seq
#print axioms Analysis.Rlim_tendsTo
#print axioms Analysis.Qabs_Qsub_comm
#print axioms Analysis.RTendsTo_unique

-- v0.8.0 — the first transcendental: Euler's number e via the exponential series.
#print axioms Analysis.fct_pos
#print axioms Analysis.self_le_fct
#print axioms Analysis.two_mul_fct_le
#print axioms Analysis.eSum_den_pos
#print axioms Analysis.eSum_le
#print axioms Analysis.efac_step
#print axioms Analysis.eU_step
#print axioms Analysis.eU_le
#print axioms Analysis.ediff_bound
#print axioms Analysis.eabs_bound
#print axioms Analysis.efct_reindex
#print axioms Analysis.eSeq_regular
#print axioms Analysis.e
#print axioms Analysis.e_pos

-- v0.9.0 — the general exponential exp(q) on the rational interval [0,1].
#print axioms Analysis.qpow_den_pos
#print axioms Analysis.qpow_nonneg
#print axioms Analysis.qpow_le_one
#print axioms Analysis.expTerm_le
#print axioms Analysis.expSum_den_pos
#print axioms Analysis.expSum_le
#print axioms Analysis.Qsub_add_right
#print axioms Analysis.expdiff_dom
#print axioms Analysis.expdiff_bound
#print axioms Analysis.expabs_bound
#print axioms Analysis.expSeq_regular
#print axioms Analysis.Rexp
#print axioms Analysis.Qeq_trans
#print axioms Analysis.expSum_zero_eq
#print axioms Analysis.Rexp_zero
#print axioms Analysis.Rexp_one_pos
#print axioms Analysis.Qadd_congr
#print axioms Analysis.qpow_one_eq
#print axioms Analysis.expSum_one_eq
#print axioms Analysis.Rexp_one_eq_e

-- Coverage completion: leaf and helper lemmas that are transitively reached by the audited
-- theorems above, audited here EXPLICITLY so `honesty_audit.sh`'s coverage check can mechanically
-- enforce that EVERY non-private proof-layer theorem/lemma is `#print axioms`-checked (no drift).
#print axioms Analysis.RingNF.mul4
#print axioms Analysis.I_im
#print axioms Analysis.ofReal_im
#print axioms Analysis.Qeq_symm
#print axioms Analysis.neg_den_pos
#print axioms Analysis.fct_succ
#print axioms Analysis.eSum_step
#print axioms Analysis.eU_den_pos
#print axioms Analysis.e_seq
#print axioms Analysis.one_seq
#print axioms Analysis.zero_seq
#print axioms Analysis.Ridx_comm
#print axioms Analysis.RmulK_comm
#print axioms Analysis.RmulK_pos
#print axioms Analysis.xBound_pos
#print axioms Analysis.Qabs_le_of_nonneg
#print axioms Analysis.Qsub_le_sub
#print axioms Analysis.Qsub_add_cancel
#print axioms Analysis.Qle_self_add
#print axioms Analysis.Qle_add_self
#print axioms Analysis.qpow_succ
#print axioms Analysis.qpow_zero_succ_num
#print axioms Analysis.expSum_step
#print axioms Analysis.expTerm_den_pos
#print axioms Analysis.expTerm_num_nonneg
#print axioms Analysis.expTerm_one_eq
#print axioms Analysis.expTerm_zero_succ_num
#print axioms Analysis.Qeq_add_zero_num
#print axioms Analysis.Qle_Qabs_Qsub_of_Qeq
#print axioms Analysis.Rexp_seq

-- v0.11.0 — the order ≤ on ℝ (foundation for the transcendentals).
#print axioms Analysis.Qle_self_Qabs
#print axioms Analysis.Qabs_le_of_both
#print axioms Analysis.Qle_add_of_Qabs_sub
#print axioms Analysis.Qsub_le_of_le_add
#print axioms Analysis.Rnonneg_zero
#print axioms Analysis.Rnonneg_one
#print axioms Analysis.Rnonneg_Radd
#print axioms Analysis.Rle_refl
#print axioms Analysis.Rle_of_Req
#print axioms Analysis.Rle_antisymm
#print axioms Analysis.Rle_trans
#print axioms Analysis.Rle_zero_of_Rnonneg

-- v0.12.0 (in progress) — the multiplicative substrate: real powers + the reciprocal.
#print axioms Analysis.Rpow_zero
#print axioms Analysis.Rpow_succ
#print axioms Analysis.Rpow_one
#print axioms Analysis.Rpow_congr
#print axioms Analysis.Qmul_congr
#print axioms Analysis.Qinv_den_pos
#print axioms Analysis.Qinv_num_pos
#print axioms Analysis.Qmul_Qinv
#print axioms Analysis.Qinv_antitone
#print axioms Analysis.Qinv_sub_eq
#print axioms Analysis.Rdelta_num_pos
#print axioms Analysis.Rdelta_den_pos
#print axioms Analysis.RL_num_pos
#print axioms Analysis.RL_den_pos
#print axioms Analysis.Rinv_lb
#print axioms Analysis.Qabs_Qinv
#print axioms Analysis.Rinv_num_pos
#print axioms Analysis.RinvR_ge
#print axioms Analysis.Rinv_perterm
#print axioms Analysis.Qmul_add_right
#print axioms Analysis.Qabs_Qsub_swap
#print axioms Analysis.RinvSeq_regular
#print axioms Analysis.Rinv
#print axioms Analysis.qpow_abs
#print axioms Analysis.qpow_base_mono
#print axioms Analysis.expSumM_den_pos
#print axioms Analysis.expSumM_step
#print axioms Analysis.expSumM_le
#print axioms Analysis.expM_step_le
#print axioms Analysis.expM_U_den_pos
#print axioms Analysis.expM_U_step
#print axioms Analysis.expM_U_le
#print axioms Analysis.expM_diff_bound
#print axioms Analysis.qpow_nat_base
#print axioms Analysis.expTerm_abs_le_M
#print axioms Analysis.expSum_abs_diff_le_M
#print axioms Analysis.expSum_trunc_bound
#print axioms Analysis.qpow_abs_le
#print axioms Analysis.qpow_diff_bound
#print axioms Analysis.expTerm_diff_bound
#print axioms Analysis.LipS_den_pos
#print axioms Analysis.expSum_Lip_le
#print axioms Analysis.Pbound_closed
#print axioms Analysis.expSumM_le_U
#print axioms Analysis.LipS_shift
#print axioms Analysis.LipS_le_U
#print axioms Analysis.two_pow_ge
#print axioms Analysis.fct_ge_geom
#print axioms Analysis.trunc_reindex
#print axioms Analysis.expSumM_num_nonneg
#print axioms Analysis.expM_U_num_nonneg
#print axioms Analysis.Qle_toNat
#print axioms Analysis.RexpReal_diag_le
#print axioms Analysis.RexpReal_regular
#print axioms Analysis.RexpReal
#print axioms Analysis.Qabs_neg
#print axioms Analysis.fct_mono
#print axioms Analysis.qsq_abs_le
#print axioms Analysis.altTerm_den_pos
#print axioms Analysis.altSum_den_pos
#print axioms Analysis.altTerm_abs_le
#print axioms Analysis.altSum_abs_diff_le
#print axioms Analysis.altSum_trunc_bound
#print axioms Analysis.altTerm_diff_bound
#print axioms Analysis.altSum_Lip_le
#print axioms Analysis.qsq_diff_le
#print axioms Analysis.RaltReal_diag_le
#print axioms Analysis.RaltReal_regular
#print axioms Analysis.RaltReal
#print axioms Analysis.Rcos
#print axioms Analysis.Rsin
#print axioms Analysis.geoSum_den_pos
#print axioms Analysis.geoU_eq
#print axioms Analysis.geo_diff_eq
#print axioms Analysis.Qsub_le_self
#print axioms Analysis.geo_diff_bound
#print axioms Analysis.artTerm_den_pos
#print axioms Analysis.artSum_den_pos
#print axioms Analysis.artTerm_abs_le
#print axioms Analysis.artSum_abs_diff_le
#print axioms Analysis.artSum_trunc
#print axioms Analysis.qpow_abs_le_rat
#print axioms Analysis.Pcoef_den_pos
#print axioms Analysis.Pcoef_num_nonneg
#print axioms Analysis.qpow_diff_bound_rat
#print axioms Analysis.geoEvenSum_den_pos
#print axioms Analysis.geoEven_eq
#print axioms Analysis.geoEven_bound
#print axioms Analysis.Pcoef_closed
#print axioms Analysis.artTerm_diff_bound
#print axioms Analysis.artSum_Lip_le
#print axioms Analysis.qpow_half_value
#print axioms Analysis.qpow_half_le
#print axioms Analysis.qpow_geom_bound
#print axioms Analysis.Qmul_le_cancel_right
#print axioms Analysis.Qone_mul
#print axioms Analysis.Qmul_swap_right
#print axioms Analysis.artanh_reindex
#print axioms Analysis.Rartanh_diag_le
#print axioms Analysis.Rartanh_regular
#print axioms Analysis.Rartanh
#print axioms Analysis.Qmul_rearrange4
#print axioms Analysis.Qmul_rearrange4b
#print axioms Analysis.Qmul_sub_right
#print axioms Analysis.Qneg_congr
#print axioms Analysis.Qsub_congr
#print axioms Analysis.Qinv_mul
#print axioms Analysis.tmap_ring
#print axioms Analysis.tmap_diff_cleared
#print axioms Analysis.Qabs_of_nonneg
#print axioms Analysis.tmap_lipschitz
#print axioms Analysis.tmap_cross_le
#print axioms Analysis.tmap_cross_ge
#print axioms Analysis.Qmul_neg_left
#print axioms Analysis.tmap_abs_le
#print axioms Analysis.Rlog_regular
#print axioms Analysis.tmap_M_eq
#print axioms Analysis.Rlog
#print axioms Analysis.Rlog_two_ok
#print axioms Analysis.Qle_add_right_nonneg
#print axioms Analysis.Qle_add_left_nonneg
#print axioms Analysis.Qbound_anti
#print axioms Analysis.reindex_regular
#print axioms Analysis.RlogPosR_tail
#print axioms Analysis.RlogPosR_self
#print axioms Analysis.Rlog_ub
#print axioms Analysis.RlogPos
#print axioms Analysis.qpow_one
#print axioms Analysis.arctanTerm_den_pos
#print axioms Analysis.arctanSum_den_pos
#print axioms Analysis.arctanTerm_abs_le
#print axioms Analysis.arctanSum_abs_diff_le
#print axioms Analysis.arctanSum_trunc
#print axioms Analysis.Rarctan_diag_le
#print axioms Analysis.Rarctan_regular
#print axioms Analysis.Rarctan
#print axioms Analysis.Qle_of_Qsub_le_Qsub_left
#print axioms Analysis.Qle_of_Qsub_le_Qsub_right
#print axioms Analysis.Rlt_Qbound_of_Rle_ofQ
#print axioms Analysis.Pos_of_Rle_ofQ
#print axioms Analysis.Rpi_lower
#print axioms Analysis.Rle_Rneg
#print axioms Analysis.Radd_le_add
#print axioms Analysis.Rsub_le_sub
#print axioms Analysis.arctanSum_diag_ge
#print axioms Analysis.arctanSum_diag_le
#print axioms Analysis.Rarctan_ge
#print axioms Analysis.Rarctan_le
#print axioms Analysis.Qmul_sub_left
#print axioms Analysis.Qabs_mul_const_sub
#print axioms Analysis.Qneg_le_neg
#print axioms Analysis.Qsub_le_2
#print axioms Analysis.Qabs_Qsub_neg_neg
#print axioms Analysis.Rpi_seq_den_pos
#print axioms Analysis.Rpi_regular
#print axioms Analysis.Rpi_pos

-- v0.14.0 (wip) — γ₀ (Euler–Mascheroni) via the alternating ζ-series.
#print axioms Analysis.AltSum_succ
#print axioms Analysis.Qsub_nonneg_of_le
#print axioms Analysis.Qzero_le
#print axioms Analysis.num_nonneg_of_Qzero_le
#print axioms Analysis.Qsub_zero_eq
#print axioms Analysis.AltSum_den_pos
#print axioms Analysis.altSum_bracket
#print axioms Analysis.altSum_gap
#print axioms Analysis.zetaSum_s_anti_step
#print axioms Analysis.zetaSum_num_nonneg
#print axioms Analysis.zetaSum_le_two
#print axioms Analysis.altSum_diff_le
#print axioms Analysis.bterm_den_pos
#print axioms Analysis.bterm_num_nonneg
#print axioms Analysis.bterm_anti
#print axioms Analysis.bterm_le
#print axioms Analysis.bterm_depth_diff
#print axioms Analysis.gammaSeq_den_pos
#print axioms Analysis.gammaSeq_reg_le
#print axioms Analysis.gammaSeq_regular

-- v0.14.0 (wip) — accelerated γ (harmonic/telescoping): the artanh rational bounds.
#print axioms Analysis.artTerm_num_nonneg
#print axioms Analysis.artSum_step
#print axioms Analysis.artSum_mono
#print axioms Analysis.artSum_zero_eq
#print axioms Analysis.artSum_ge_arg
#print axioms Analysis.artTerm_le_geoTerm
#print axioms Analysis.artSum_le_geoSum
#print axioms Analysis.geoSum_cleared_le
#print axioms Analysis.artSum_le_geo
#print axioms Analysis.two_artSum_ge
#print axioms Analysis.two_artSum_le
#print axioms Analysis.cApprox_den_pos
#print axioms Analysis.cApprox_num_nonneg
#print axioms Analysis.cApprox_ub
#print axioms Analysis.Ssum_den_pos
#print axioms Analysis.Ssum_tail_le
#print axioms Analysis.npow_base_mono
#print axioms Analysis.npow_add
#print axioms Analysis.qpow_one_den
#print axioms Analysis.cApprox_depth_diff
#print axioms Analysis.Ssum_depth_diff
#print axioms Analysis.Ssum_le
#print axioms Analysis.pow_dom
#print axioms Analysis.gammaHseq_den_pos
#print axioms Analysis.gammaHseq_reg_le
#print axioms Analysis.gammaHseq_regular
#print axioms Analysis.Qabs_lower
#print axioms Analysis.clow_le_cApprox
#print axioms Analysis.Ssum_le_of_le
#print axioms Analysis.clow_den_pos
#print axioms Analysis.gammaHseq_ge_clow
#print axioms Analysis.gammaHseq_nonneg
#print axioms Analysis.Rgamma_h_lower

-- v0.10.0 — the λₙ / RH proof boundary (analytic face), locked faithfully.
#print axioms Li.Pos_one
#print axioms Li.template_liPositive
#print axioms Li.template_liNonneg
#print axioms Li.template_liPositiveUpTo
#print axioms Li.liPositive_iff_all_upTo
#print axioms Li.liDecomposition_genuine
#print axioms Li.explicitFormulaTrace_genuine
#print axioms Li.liAgreesWith_genuine

-- v0.10.0 — ExactBoundedReal enclosure interface + ζ(s) as an exact-bounded object.
#print axioms Analysis.enclosure_width
#print axioms Analysis.lowerB_le_upperB
#print axioms Analysis.certificate
#print axioms Analysis.npow_succ
#print axioms Analysis.npow_pos
#print axioms Analysis.npow_two
#print axioms Analysis.npow_one
#print axioms Analysis.npow_mono
#print axioms Analysis.zetaSum_den_pos
#print axioms Analysis.zetaSum_step
#print axioms Analysis.zetaSum_le
#print axioms Analysis.zeta_step_le
#print axioms Analysis.zetaU_den_pos
#print axioms Analysis.zetaU_step
#print axioms Analysis.zetaU_le
#print axioms Analysis.zetadiff_bound
#print axioms Analysis.zetaabs_bound
#print axioms Analysis.zetaSeq_regular
#print axioms Analysis.zeta_seq
#print axioms Analysis.zeta_pos
