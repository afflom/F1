/-
F1 square — v0.22.0 crux frontier: **the LOOSE UPPER bracket on the second Stieltjes constant `γ₂`**
(`γ₂ ≤ 1/20`), the last constant input to `Pos Rlambda4` (the n=4 prime–archimedean coupling).

`λ₄`'s arithmetic side carries `−2γγ₂` through `η₃`; with `γ > 0` a LOOSE UPPER bound `γ₂ ≤ ε`
(`ε` modest, here `1/20`) suffices to control it (the `Pos λ₄` margin is `≈ +0.054` once `γ₁ ≤ −0.0677`
and `γ₃ ≤ 1/8` are in place). This file builds that upper bracket by the SAME DISCRETE Euler–Maclaurin
acceleration as `GammaTwoBracket` (the `γ₂` LOWER bound) — but in the UPPER direction, mirroring the
`γ₃`/`γ₁` upper pipelines.

The per-step trapezoidal residual `sStep ≈ decompForm = b²·C2 + b·R1 + R0` (`b = ln p`, `δ = a−b`,
`u0 = 1/p`, `u1 = 1/(p+1)`):
  b²·C2 ≤ 1/(p(p+1))   (C2 = ½(u0+u1)−δ ≤ 1/(2p(p+1)(2p+1)) (`C2_le`), b² ≤ 4p (`logSq_le_self4`))
  b·R1  ≤ 0            (R1 = δ(u1−δ),  u1 ≤ δ)
  R0    ≤ 1/(p(p+1))   (R0 = ½δ²u1 − ⅓δ³ ≤ ½δ²u1, δ² ≤ 1/p²)
so `sStep ≤ 2/(p(p+1))`, telescoping to `γ₂ ≤ hSeq(N) + 2/(N+1) + corr + 1/(j+1)`.

The only new ingredient is `(ln p)² ≤ 4p` (`logSq_le_self4`): with `M = L/2`, `exp(M) ≥ 1+M ≥ M`, so
`exp(L) = exp(M)² ≥ M²`, i.e. `4·exp(L) ≥ L²`; `exp(ln p) = p`.  No `RrpowPos`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.GammaThreeBracket

namespace UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 4000000

-- `logN` opaque downstream: prevents exponential `whnf`/`isDefEq` blowup on the nested `δ = ln(p+1)−ln p`.
attribute [local irreducible] logN

-- ===========================================================================
-- (S1) The square-root cap `(ln p)² ≤ 4p`.
-- ===========================================================================

/-- **Square monotonicity** `0 ≤ A ≤ B ⟹ A² ≤ B²`. -/
theorem sq_le_sq {A B : Real} (hA : Rnonneg A) (hB : Rnonneg B) (hAB : Rle A B) :
    Rle (Rmul A A) (Rmul B B) :=
  Rle_trans (Rmul_le_Rmul_right hA hAB) (Rmul_le_Rmul_left hB hAB)

/-- **`L² ≤ 4·exp(L)`** for `L ≥ 0`.  With `M = L/2`: `exp(M) ≥ 1+M ≥ M ≥ 0`, so
    `exp(L) = exp(M+M) = exp(M)² ≥ M²`, and `4·M² = L²`. -/
theorem sq_le_4_exp (L : Real) (hL : Rnonneg L) :
    Rle (Rmul L L) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (RexpReal L)) := by
  have hMnn : Rnonneg (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L) :=
    Rnonneg_Rmul (Rnonneg_ofQ (by decide) (by decide)) hL
  have hEnn : Rnonneg (RexpReal (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L)) := RexpReal_nonneg _
  have hMleE : Rle (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L)
      (RexpReal (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L)) :=
    Rle_trans (Rle_self_Radd_left Rnonneg_one) (RexpReal_ge_one_add_nonneg hMnn)
  have hsq := sq_le_sq hMnn hEnn hMleE
  -- M+M ≈ L
  have hcoef : Req (Radd (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L) (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L)) L := by
    refine Req_trans (Req_symm (Rmul_distrib_right _ _ L)) ?_
    refine Req_trans (Rmul_congr ?_ (Req_refl L)) (Rone_mul L)
    exact Req_trans (Radd_ofQ_ofQ (by decide) (by decide)) (ofQ_congr (by decide) (by decide) (by decide))
  -- E² ≈ exp(L)
  have hE2 : Req (Rmul (RexpReal (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L))
        (RexpReal (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L))) (RexpReal L) :=
    Req_trans (Req_symm (RexpReal_add _ _)) (RexpReal_congr hcoef)
  -- L² ≈ 4·M²
  have hconst : Req (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide))
      (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (ofQ (⟨1, 2⟩ : Q) (by decide)))) one := by
    refine Req_trans (Rmul_congr (Req_refl _) (Rmul_ofQ_ofQ (by decide) (by decide))) ?_
    exact Req_trans (Rmul_ofQ_ofQ (by decide) (by decide)) (ofQ_congr (by decide) (by decide) (by decide))
  have hL2 : Req (Rmul L L)
      (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide))
        (Rmul (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L) (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L))) := by
    refine Req_symm ?_
    refine Req_trans (Rmul_congr (Req_refl _) (prod_sq_reassoc (ofQ (⟨1, 2⟩ : Q) (by decide)) L)) ?_
    refine Req_trans (Req_symm (Rmul_assoc (ofQ (⟨4, 1⟩ : Q) (by decide))
        (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (ofQ (⟨1, 2⟩ : Q) (by decide))) (Rmul L L))) ?_
    exact Req_trans (Rmul_congr hconst (Req_refl _)) (Rone_mul _)
  refine Rle_trans (Rle_of_Req hL2) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) hsq) ?_
  exact Rle_of_Req (Rmul_congr (Req_refl _) hE2)

/-- **`(ln p)² ≤ 4·p`** — the square-root cap. -/
theorem logSq_le_self4 (p : Nat) (hp : 1 ≤ p) :
    Rle (Rmul (logN p hp) (logN p hp)) (ofQ (⟨4 * (p : Int), 1⟩ : Q) Nat.one_pos) := by
  refine Rle_trans (sq_le_4_exp (logN p hp) (Rnonneg_logN p hp)) ?_
  refine Rle_trans (Rle_of_Req (Rmul_congr (Req_refl _) (Rexp_logN p hp))) ?_
  exact Rle_of_Req (Req_trans (Rmul_ofQ_ofQ (by decide) Nat.one_pos)
    (ofQ_congr (Qmul_den_pos (by decide) Nat.one_pos) Nat.one_pos
      (by show Qeq (mul (⟨4, 1⟩ : Q) (⟨(p : Int), 1⟩ : Q)) (⟨4 * (p : Int), 1⟩ : Q)
          simp only [Qeq, mul])))

end UOR.Bridge.F1Square.Analysis
