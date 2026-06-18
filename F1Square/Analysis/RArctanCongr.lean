/-
F1 square — v0.22.0 Track 1: **`arctan` is continuous (respects `Req`)** — `RarctanR_congr`, the
real-argument analog of `Rartanh_congr` (`ExpLog.lean`).

This is the foundation for lifting rational arctan/log identities (the artanh addition law, hence log
multiplicativity) to general real arguments, and for the well-definedness of `arg(z)` under `Req`.
Mirrors `Rartanh_congr` exactly with `artSum → arctanSum`: the diagonal gap is bounded by the
Lipschitz estimate `geoEvenSum ρ · |t−t'|` (`arctanSum_Lip_le`, `RArctan.lean`), with `geoEvenSum ≤ 2`
(`geoEvenSum_le_two`, shared and sign-independent) and `|t−t'| ≤ 2/(R+1)` from `Req`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.RArctan
import F1Square.Analysis.ExpLog

namespace UOR.Bridge.F1Square.Analysis

/-- **`arctan` is continuous (respects `Req`)**: if `t ≈ t'` (both bounded by `ρ < 1`) then
    `RarctanR t ≈ RarctanR t'`. Mirrors `Rartanh_congr`. -/
theorem RarctanR_congr (t t' : Real) (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
    (hbt : ∀ n, Qle (Qabs (t.seq n)) ρ) (hbt' : ∀ n, Qle (Qabs (t'.seq n)) ρ) (heq : Req t t') :
    Req (RarctanR t ρ hρ0 hρd hlt hbt) (RarctanR t' ρ hρ0 hρd hlt hbt') := by
  refine Req_of_lin_bound (C := 4) ?_
  intro n
  show Qle (Qabs (Qsub (arctanSum (t.seq (Rartanh_R ρ n)) (Rartanh_R ρ n))
      (arctanSum (t'.seq (Rartanh_R ρ n)) (Rartanh_R ρ n)))) (⟨(4 : Int), n + 1⟩ : Q)
  have hdiffd : 0 < (Qsub (t.seq (Rartanh_R ρ n)) (t'.seq (Rartanh_R ρ n))).den :=
    Qsub_den_pos (t.den_pos _) (t'.den_pos _)
  refine Qle_trans (Qmul_den_pos (geoEvenSum_den_pos hρd _) (Qabs_den_pos hdiffd))
    (arctanSum_Lip_le (t.den_pos _) (t'.den_pos _) hρd (hbt _) (hbt' _) (Rartanh_R ρ n)) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos hdiffd))
    (Qmul_le_mul_right (Qabs_num_nonneg _) (geoEvenSum_le_two hρ0 hρd hρ2 (Rartanh_R ρ n))) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos _))
    (Qmul_le_mul_left (by decide) (heq (Rartanh_R ρ n))) ?_
  have hRge : n ≤ Rartanh_R ρ n := by
    unfold Rartanh_R
    have hk : 1 ≤ ρ.den * ρ.den + 4 * ρ.den :=
      Nat.le_trans (by omega : 1 ≤ 4 * ρ.den) (Nat.le_add_left _ _)
    calc n ≤ 1 * (n + 1) := by omega
      _ ≤ (ρ.den * ρ.den + 4 * ρ.den) * (n + 1) := Nat.mul_le_mul_right _ hk
  show (2 * 2 : Int) * ((n + 1 : Nat) : Int) ≤ (4 : Int) * ((1 * (Rartanh_R ρ n + 1) : Nat) : Int)
  push_cast; omega

end UOR.Bridge.F1Square.Analysis
