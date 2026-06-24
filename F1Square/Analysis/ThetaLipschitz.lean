/-
F1 square — Track 1, item 3 substrate: the **Jacobi-theta Lipschitz bound** on `[1, ∞)`, the modulus
of continuity the Mellin integrand `t^{σ−1}·ψ(t)` needs to enter the certified-integration framework.

The per-term step `|e^{−aₘs} − e^{−aₘt}| ≤ rₘ·|s−t|` would normally need a case split on `s ≤ t` vs
`t ≤ s` (which constructively is undecidable). The **RmaxZero trick** removes it: the order-free bound

  `1 − e^{−z} ≤ 4·max(z, 0)`  for ALL real `z`

(here, via `1 − e^{−z} ≤ 1 − e^{−max(z,0)} ≤ 4·max(z,0)`, monotone in the exponent + the global
`RexpReal_one_sub_neg_le_global` on the nonneg argument `max(z,0)`) is symmetric enough that the signed
per-term difference factors through `max` with no dichotomy.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.ThetaValueDecay
import F1Square.Analysis.ExpVarGlobal
import F1Square.Analysis.ClampOne

namespace UOR.Bridge.F1Square.Analysis

/-- `z ≤ max(z, 0)` (the tent dominates its argument). -/
theorem Rle_RmaxZero_self (z : Real) : Rle z (RmaxZero z) := by
  show Rle z (Rhalf (Radd z (Rabs z)))
  exact Rle_trans (Rle_of_Req (Req_symm (Rhalf_add_self z)))
    (Rhalf_le_Rhalf (Radd_le_add (Rle_refl z) (Rle_Rabs_self z)))

/-- `max(z, 0) ≤ |z|` (the tent is dominated by the absolute value). -/
theorem RmaxZero_le_Rabs (z : Real) : Rle (RmaxZero z) (Rabs z) := by
  show Rle (Rhalf (Radd z (Rabs z))) (Rabs z)
  exact Rle_trans (Rhalf_le_Rhalf (Radd_le_add (Rle_Rabs_self z) (Rle_refl (Rabs z))))
    (Rle_of_Req (Rhalf_add_self (Rabs z)))

/-- **Order-free global exp variation** `1 − e^{−z} ≤ 4·max(z, 0)` for EVERY real `z` (no `z ≥ 0`).
    `1 − e^{−z} ≤ 1 − e^{−max(z,0)}` (since `max(z,0) ≥ z` ⟹ `e^{−max(z,0)} ≤ e^{−z}`), and the latter
    is `≤ 4·max(z,0)` by the nonneg-argument bound. The `max` makes the signed per-term theta difference
    boundable without a real case split. -/
theorem RexpReal_one_sub_neg_le_maxZero (z : Real) :
    Rle (Rsub one (RexpReal (Rneg z))) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (RmaxZero z)) := by
  have hexp : Rle (RexpReal (Rneg (RmaxZero z))) (RexpReal (Rneg z)) :=
    RexpReal_le_of_le (Rle_Rneg (Rle_RmaxZero_self z))
  have hsub : Rle (Rsub one (RexpReal (Rneg z))) (Rsub one (RexpReal (Rneg (RmaxZero z)))) :=
    Radd_le_add (Rle_refl one) (Rle_Rneg hexp)
  exact Rle_trans hsub (RexpReal_one_sub_neg_le_global (Rnonneg_RmaxZero z))

/-- The theta-term coefficient `aₘ = (m+1)²·π` (so `thetaArg t m ≈ aₘ·t`). -/
def thetaCoeff (m : Nat) : Real := Rmul (RofNat ((m + 1) * (m + 1))) Rpi

/-- `thetaArg t m ≈ aₘ·t` (associativity of `(m+1)²·π·t`). -/
theorem thetaArg_eq_coeff (t : Real) (m : Nat) :
    Req (thetaArg t m) (Rmul (thetaCoeff m) t) :=
  Req_symm (Rmul_assoc (RofNat ((m + 1) * (m + 1))) Rpi t)

private theorem Rpi_nn : Rnonneg Rpi :=
  Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg (Rnonneg_ofQ (by decide) (by decide)))
    Rpi_lower_three)

/-- `aₘ ≥ 0`. -/
theorem thetaCoeff_nonneg (m : Nat) : Rnonneg (thetaCoeff m) :=
  Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (Int.ofNat_nonneg _)) Rpi_nn

/-- `aₘ ≥ 3·(m+1)²` (since `π ≥ 3`). -/
theorem thetaCoeff_lower (m : Nat) :
    Rle (ofQ (⟨3 * (((m + 1) * (m + 1) : Nat) : Int), 1⟩ : Q) Nat.one_pos) (thetaCoeff m) := by
  refine Rle_trans (Rle_of_Req ?_)
    (Rmul_le_Rmul_left (Rnonneg_ofQ Nat.one_pos (Int.ofNat_nonneg _)) Rpi_lower_three)
  refine Req_symm (Req_trans (Rmul_ofQ_ofQ Nat.one_pos (by decide)) (ofQ_congr _ Nat.one_pos ?_))
  simp only [Qeq, mul]; push_cast; ring_uor

/-- **The summable per-term coefficient bound** `aₘ·e^{−aₘ} ≤ 4/(3(m+1)²)` (quadratic decay). Via the
    half-split `aₘ·e^{−aₘ} = (aₘ·e^{−aₘ/2})·e^{−aₘ/2} ≤ 2·e^{−aₘ/2}` (peak bound `X·e^{−X} ≤ 1` at
    `X = aₘ/2`) and `e^{−aₘ/2} ≤ 1/(1+3(m+1)²/2) ≤ 2/(3(m+1)²)` (`Rexp_neg_le_ratio`, `aₘ/2 ≥ 3(m+1)²/2`).
    No upper bound on `π` (the peak bound carries the real `aₘ`). -/
theorem thetaCoeff_exp_le (m : Nat) :
    Rle (Rmul (thetaCoeff m) (RexpReal (Rneg (thetaCoeff m))))
      (ofQ (⟨4, 3 * ((m + 1) * (m + 1))⟩ : Q)
        (Nat.mul_pos (by decide) (Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos m)))) := by
  have hMpos : 0 < (m + 1) * (m + 1) := Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos m)
  have h3Mpos : 0 < 3 * ((m + 1) * (m + 1)) := Nat.mul_pos (by decide) hMpos
  have hMI : (0 : Int) < (((m + 1) * (m + 1) : Nat) : Int) := by exact_mod_cast hMpos
  let e : Real := RexpReal (Rneg (Rhalf (thetaCoeff m)))
  have he_nn : Rnonneg e := RexpReal_nonneg _
  -- `aₘ/2 ≥ 3(m+1)²/2`
  have hhalf_lower : Rle (ofQ (⟨3 * (((m + 1) * (m + 1) : Nat) : Int), 2⟩ : Q)
        (by show (0 : Nat) < 2; decide))
      (Rhalf (thetaCoeff m)) :=
    Rle_trans (Rle_of_Req (Req_symm (Req_trans (Rhalf_ofQ _ Nat.one_pos)
      (ofQ_congr (Qmul_den_pos (by decide) Nat.one_pos) (by show (0 : Nat) < 2; decide) (by
        simp only [Qeq, mul]; push_cast; ring_uor))))) (Rhalf_le_Rhalf (thetaCoeff_lower m))
  have hhalf_nn : Rnonneg (Rhalf (thetaCoeff m)) := Rhalf_nonneg (thetaCoeff_nonneg m)
  -- `e^{−aₘ/2} ≤ 2/(3(m+1)²)`
  have hexp_half : Rle e (ofQ (⟨2, 3 * ((m + 1) * (m + 1))⟩ : Q) h3Mpos) := by
    refine Rle_trans (Rexp_neg_le_ratio (τ := (⟨3 * (((m + 1) * (m + 1) : Nat) : Int), 2⟩ : Q))
        (by show (0 : Int) < 3 * (((m + 1) * (m + 1) : Nat) : Int); omega)
        (by show (0 : Nat) < 2; decide) hhalf_lower) ?_
    refine Rle_ofQ_ofQ (Qinv_den_pos (by
        show (0 : Int) < (add (⟨1, 1⟩ : Q) (⟨3 * (((m + 1) * (m + 1) : Nat) : Int), 2⟩ : Q)).num
        simp only [add]; omega)) h3Mpos ?_
    simp only [Qle, Qinv, add]; omega
  -- `aₘ ≈ 2·(aₘ/2)`
  have hheq : Req (thetaCoeff m) (Radd (Rhalf (thetaCoeff m)) (Rhalf (thetaCoeff m))) :=
    Req_symm (Req_trans (Req_symm (Rhalf_Radd (thetaCoeff m) (thetaCoeff m)))
      (Rhalf_add_self (thetaCoeff m)))
  -- `aₘ·e^{−aₘ/2} ≤ 2`  (peak: `aₘ·e^{−aₘ/2} = (aₘ/2)·e + (aₘ/2)·e ≤ 1 + 1`)
  have hpeak : Rle (Rmul (Rhalf (thetaCoeff m)) e) one := Rmul_self_exp_neg_le_one hhalf_nn
  have ha_half_le : Rle (Rmul (thetaCoeff m) e) (ofQ (⟨2, 1⟩ : Q) (by decide)) := by
    refine Rle_trans (Rle_of_Req (Rmul_congr hheq (Req_refl e))) ?_
    refine Rle_trans (Rle_of_Req (Rmul_distrib_right (Rhalf (thetaCoeff m)) (Rhalf (thetaCoeff m)) e)) ?_
    refine Rle_trans (Radd_le_add hpeak hpeak) (Rle_of_Req ?_)
    exact Req_trans (Radd_ofQ_ofQ (by decide) (by decide))
      (ofQ_congr (add_den_pos (by decide) (by decide)) (by decide) (by decide))
  -- split `e^{−aₘ} ≈ e·e`
  have hsplit : Req (RexpReal (Rneg (thetaCoeff m))) (Rmul e e) :=
    Req_trans (RexpReal_congr (Req_trans (Rneg_congr hheq)
        (Rneg_Radd (Rhalf (thetaCoeff m)) (Rhalf (thetaCoeff m)))))
      (RexpReal_add (Rneg (Rhalf (thetaCoeff m))) (Rneg (Rhalf (thetaCoeff m))))
  -- assemble: `aₘ·e^{−aₘ} = aₘ·(e·e) = (aₘ·e)·e ≤ 2·e ≤ 2·(2/(3(m+1)²)) = 4/(3(m+1)²)`
  refine Rle_trans (Rle_of_Req (Rmul_congr (Req_refl _) hsplit)) ?_
  refine Rle_trans (Rle_of_Req (Req_symm (Rmul_assoc (thetaCoeff m) e e))) ?_
  refine Rle_trans (Rmul_le_Rmul_right he_nn ha_half_le) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) hexp_half) ?_
  refine Rle_of_Req (Req_trans (Rmul_ofQ_ofQ (by decide) h3Mpos)
    (ofQ_congr (Qmul_den_pos (by decide) h3Mpos) _ ?_))
  simp only [Qeq, mul]; push_cast; ring_uor

end UOR.Bridge.F1Square.Analysis
