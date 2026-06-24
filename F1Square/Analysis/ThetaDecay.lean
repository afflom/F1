/-
F1 square — Track 1, item 3: the **theta decay bound** `ψ(t) ≤ 2·e^{−πt}` for `t ≥ 1`. The terms
`e^{−(m+1)²πt}` are geometrically dominated — consecutive ratio `≤ ½` (since the exponent jumps by
`(2m+3)πt ≥ 1`, via `Rexp_neg_le_ratio`) — so `ψ(t) = Σ ≤ e^{−πt}·Σ2^{−m} ≤ 2·e^{−πt}`
(`genSum_geom_le`). This is the decay the Mellin improper integral `∫₁^∞ t^{s−1}ψ(t)dt` needs.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.GenSumGeom
import F1Square.Analysis.ThetaFunction

namespace UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 1000000 in
/-- The theta exponent increment: `(m+2)²·πt = (m+1)²·πt + (2m+3)·πt`. (Kept `thetaArg` folded via
    `Req_refl` to dodge the `Rpi`-whnf barrier.) -/
theorem thetaArg_succ (t : Real) (m : Nat) :
    Req (thetaArg t (m + 1))
      (Radd (thetaArg t m) (Rmul (RofNat (2 * m + 3)) (Rmul Rpi t))) := by
  have hnat : (m + 1 + 1) * (m + 1 + 1) = (m + 1) * (m + 1) + (2 * m + 3) := by
    have h : (((m + 1 + 1) * (m + 1 + 1) : Nat) : Int)
        = ((m + 1) * (m + 1) + (2 * m + 3) : Nat) := by push_cast; ring_uor
    exact_mod_cast h
  have e1 : Req (thetaArg t (m + 1)) (Rmul (RofNat ((m + 1 + 1) * (m + 1 + 1))) (Rmul Rpi t)) :=
    Req_refl _
  have e2 : Req (thetaArg t m) (Rmul (RofNat ((m + 1) * (m + 1))) (Rmul Rpi t)) := Req_refl _
  refine Req_trans e1 (Req_trans ?_ (Radd_congr (Req_symm e2) (Req_refl _)))
  rw [hnat]
  refine Req_trans (Rmul_congr ?_ (Req_refl _)) (Rmul_distrib_right _ _ _)
  refine Req_trans ?_ (Req_symm (Radd_ofQ_ofQ Nat.one_pos Nat.one_pos))
  exact ofQ_congr Nat.one_pos (add_den_pos Nat.one_pos Nat.one_pos)
    (by simp only [Qeq, add]; push_cast; ring_uor)

set_option maxHeartbeats 1000000 in
/-- **The consecutive ratio bound** `e^{−(m+2)²πt} ≤ ½·e^{−(m+1)²πt}` for `t ≥ 1`. -/
theorem thetaTerm_ratio (t : Real) (ht : Rle one t) (m : Nat) :
    Rle (thetaTerm t (m + 1)) (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (thetaTerm t m)) := by
  have hsplit : Req (thetaTerm t (m + 1))
      (Rmul (thetaTerm t m) (RexpReal (Rneg (Rmul (RofNat (2 * m + 3)) (Rmul Rpi t))))) := by
    show Req (RexpReal (Rneg (thetaArg t (m + 1))))
      (Rmul (RexpReal (Rneg (thetaArg t m)))
        (RexpReal (Rneg (Rmul (RofNat (2 * m + 3)) (Rmul Rpi t)))))
    refine Req_trans (RexpReal_congr (Rneg_congr (thetaArg_succ t m))) ?_
    refine Req_trans (RexpReal_congr (Rneg_Radd _ _)) ?_
    exact RexpReal_add (Rneg (thetaArg t m)) (Rneg (Rmul (RofNat (2 * m + 3)) (Rmul Rpi t)))
  have hpit : Rle one (Rmul Rpi t) := one_le_pi_mul t ht
  have hpit0 : Rnonneg (Rmul Rpi t) :=
    Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg (Rnonneg_ofQ (by decide) (by decide))) hpit)
  have hk1 : Rle one (RofNat (2 * m + 3)) :=
    Rle_ofQ_ofQ (by decide) Nat.one_pos (by simp only [Qle]; push_cast; omega)
  have hcomm : Req (Rmul one (Rmul Rpi t)) (Rmul Rpi t) :=
    Req_trans (Rmul_comm one (Rmul Rpi t)) (Rmul_one (Rmul Rpi t))
  have hinc : Rle (ofQ (⟨1, 1⟩ : Q) (by decide)) (Rmul (RofNat (2 * m + 3)) (Rmul Rpi t)) :=
    Rle_trans hpit (Rle_trans (Rle_of_Req (Req_symm hcomm)) (Rmul_le_Rmul_right hpit0 hk1))
  have hexp : Rle (RexpReal (Rneg (Rmul (RofNat (2 * m + 3)) (Rmul Rpi t)))) (ofQ (⟨1, 2⟩ : Q) (by decide)) :=
    Rle_trans (Rexp_neg_le_ratio (by decide) (by decide) hinc)
      (Rle_of_Req (ofQ_congr (by decide) (by decide) (by decide)))
  refine Rle_trans (Rle_of_Req hsplit) ?_
  refine Rle_trans (Rmul_le_Rmul_left (RexpReal_nonneg _) hexp) ?_
  exact Rle_of_Req (Rmul_comm (thetaTerm t m) (ofQ (⟨1, 2⟩ : Q) (by decide)))

end UOR.Bridge.F1Square.Analysis
