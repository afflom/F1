/-
F1 square — Track 1, item 3/6: **the general-σ theta–Mellin integrand** `t^{σ−1}·ψ(t)` and its
integral `∫₁^∞ t^{σ−1}ψ(t) dt` (`ThetaMellinPow.lean`).

`thetaMellin1` (`ThetaMellin.lean`) is the `σ = 1` case `∫₁^∞ ψ`. The general exponent `e = σ−1 ≤ 0`
multiplies in the power factor `gPowClamp e` (`RpowClampLip.lean`). Both factors are total, bounded by `1`,
and Lipschitz, so the product is Lipschitz (`Rmul_lipschitz`) and bounded; the per-interval decay reuses
`integralTerm_thetaClamp_le` (the product `≤ ψ` there, since `0 ≤ t^e ≤ 1`). This assembles the σ-general
real Mellin object the roadmap's item-3 bridge `ThetaModular ⟹ CompletedZetaFE` consumes.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.RpowClampLip
import F1Square.Analysis.ThetaMellin
import F1Square.Analysis.RmulLipschitz

namespace UOR.Bridge.F1Square.Analysis

/-- `gPowClamp e t ≥ 0` (it is an `exp`). -/
theorem gPowClamp_nonneg (e t : Real) : Rnonneg (gPowClamp e t) := by
  unfold gPowClamp; exact RexpReal_nonneg _

/-- `gPowClamp e t ≤ 1` for `e ≤ 0` (since `max(t,1) ≥ 1`). -/
theorem gPowClamp_le_one (e : Real) (he : Rle e zero) (t : Real) : Rle (gPowClamp e t) one := by
  unfold gPowClamp
  exact RrpowPos_le_one_of_nonpos (qClampOne t) 1 (ge1_pos_witness (qClampOne t) (qClampOne_ge1 t 1))
    (Rle_one_of_seq_ge1 (qClampOne_ge1 t)) e he

/-- `|gPowClamp e t| ≤ 1` for `e ≤ 0` — the integral-interface bound (`ofQ 1`-valued, `one = ofQ ⟨1,1⟩`). -/
theorem gPowClamp_abs_le_one (e : Real) (he : Rle e zero) (t : Real) :
    Rle (Rabs (gPowClamp e t)) (ofQ (⟨1, 1⟩ : Q) (by decide)) :=
  Rle_trans (Rle_of_Req (Rabs_of_nonneg (gPowClamp_nonneg e t))) (gPowClamp_le_one e he t)

/-- `|thetaClamp t| ≤ 1` — the integral-interface bound for the ψ factor. -/
theorem thetaClamp_abs_le_one (t : Real) :
    Rle (Rabs (thetaClamp t)) (ofQ (⟨1, 1⟩ : Q) (by decide)) :=
  Rle_trans (Rle_of_Req (Rabs_of_nonneg (thetaClamp_nonneg t)))
    (thetaFn_le_one (clampOne t) (clampOne_ge_one t))

end UOR.Bridge.F1Square.Analysis
