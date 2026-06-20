import F1Square.Analysis.RlogMulSigned

/-!
# General-radius (`ρ < 1`) artanh continuity — toward fully general `Rlog`/`Clog`

The bounded/symmetric-band discharges (`RlogMulPos`, `RlogMulSigned`) are gated by the small-radius
constraint `ρ² ≤ 1/2` in the artanh continuity lemmas (`Rartanh_congr`, `Rartanh_radius_indep`),
inherited from `geoEvenSum_le_two` (the even geometric sum `Σρ^{2k} ≤ 2`). For large moduli the
radius `ρ_B = (B−1)/(B+1)` approaches 1, so `ρ² ≤ 1/2` fails.

Key observation: `geoEvenSum ρ N ≤ 1/(1−ρ²) ≤ d²/(2d−1) ~ d/2` (`d = ρ.den`), while the artanh
reindex factor is `ρ.den²+4ρ.den ~ d²`. So the **existing reindex already absorbs** the general
`1/(1−ρ²)` bound — `ρ²≤1/2` is needed only for the clean constant `2`, not for convergence. This file
generalizes the continuity lemmas to any `ρ < 1` with an explicit absorbable bound `K`.
-/

namespace UOR.Bridge.F1Square.Analysis

/-- **General even-geometric-sum bound** `Σ_{k≤N} ρ^{2k} ≤ K` for any `K ≥ 1/(1−ρ²)` (`K·(1−ρ²) ≥ 1`).
    Generalizes `geoEvenSum_le_two` (`K = 2`, `ρ² ≤ 1/2`) to arbitrary `ρ < 1` via `mul_div_gen`. -/
theorem geoEvenSum_le_gen {ρ K : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hKF : Qle (⟨1, 1⟩ : Q) (mul K (Qsub ⟨1, 1⟩ (mul ρ ρ)))) (N : Nat) :
    Qle (geoEvenSum ρ N) K := by
  have hsd : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).den := Qsub_den_pos Nat.one_pos (Qmul_den_pos hρd hρd)
  have hab : Qle (mul (geoEvenSum ρ N) (Qsub ⟨1, 1⟩ (mul ρ ρ))) ⟨1, 1⟩ :=
    Qle_trans (add_den_pos (Qmul_den_pos (geoEvenSum_den_pos hρd N) hsd) (qpow_den_pos hρd _))
      (Qle_self_add (qpow_nonneg hρ0 (2 * N + 2)))
      (Qeq_le (geoEven_eq hρd N))
  exact Qle_trans (Qmul_den_pos hKd Nat.one_pos)
    (mul_div_gen (geoEvenSum_num_nonneg hρ0 N) (geoEvenSum_den_pos hρd N) hsd hKd hK0 hKF hab)
    (Qeq_le (mul_one K))

set_option maxHeartbeats 800000 in
/-- **General-radius `Rartanh` argument-congruence**: `Req t t' ⟹ Req (Rartanh t) (Rartanh t')` for any
    `ρ < 1` (no `ρ² ≤ 1/2`). The even-sum bound `geoEvenSum ≤ K` (`K·(1−ρ²) ≥ 1`, `K` a Nat) is absorbed
    by the artanh reindex provided `K ≤ 2(ρ.den²+4ρ.den)` (`hKr`) — which holds for every `ρ < 1`. The
    generalization of `Rartanh_congr` past the small-radius cap. -/
theorem Rartanh_congr_gen (t t' : Real) (ρ : Q) (K : Nat) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den)
    (hKF : Qle (⟨1, 1⟩ : Q) (mul (⟨(K : Int), 1⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ))))
    (hKr : K ≤ 2 * (ρ.den * ρ.den + 4 * ρ.den))
    (hbt : ∀ n, Qle (Qabs (t.seq n)) ρ) (hbt' : ∀ n, Qle (Qabs (t'.seq n)) ρ) (heq : Req t t') :
    Req (Rartanh t ρ hρ0 hρd hlt hbt) (Rartanh t' ρ hρ0 hρd hlt hbt') := by
  refine Req_of_lin_bound (C := 4) ?_
  intro n
  show Qle (Qabs (Qsub (artSum (t.seq (Rartanh_R ρ n)) (Rartanh_R ρ n))
      (artSum (t'.seq (Rartanh_R ρ n)) (Rartanh_R ρ n)))) (⟨(4 : Int), n + 1⟩ : Q)
  have hdiffd : 0 < (Qsub (t.seq (Rartanh_R ρ n)) (t'.seq (Rartanh_R ρ n))).den :=
    Qsub_den_pos (t.den_pos _) (t'.den_pos _)
  refine Qle_trans (Qmul_den_pos (geoEvenSum_den_pos hρd _) (Qabs_den_pos hdiffd))
    (artSum_Lip_le (t.den_pos _) (t'.den_pos _) hρd (hbt _) (hbt' _) (Rartanh_R ρ n)) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos hdiffd))
    (Qmul_le_mul_right (Qabs_num_nonneg _)
      (geoEvenSum_le_gen hρ0 hρd Nat.one_pos (by exact Int.ofNat_nonneg K) hKF (Rartanh_R ρ n))) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos _))
    (Qmul_le_mul_left (Int.ofNat_nonneg K) (heq (Rartanh_R ρ n))) ?_
  show ((K : Int) * 2) * ((n + 1 : Nat) : Int) ≤ (4 : Int) * ((1 * (Rartanh_R ρ n + 1) : Nat) : Int)
  unfold Rartanh_R
  push_cast
  have hk2 : (K : Int) * 2 ≤ 4 * ((ρ.den : Int) * ρ.den + 4 * ρ.den) := by
    have h := hKr; push_cast at h; omega
  have hmnn : (0 : Int) ≤ (n : Int) + 1 := by omega
  have hprod := Int.mul_le_mul_of_nonneg_right hk2 hmnn
  have e1 : (4 * ((ρ.den : Int) * ρ.den + 4 * ρ.den)) * ((n : Int) + 1)
      = 4 * (((ρ.den : Int) * ρ.den + 4 * ρ.den) * ((n : Int) + 1)) := by
    generalize ((ρ.den : Int) * ρ.den + 4 * ρ.den) = A; generalize ((n : Int) + 1) = m; ring_uor
  have e2 : (4 : Int) * (1 * (((ρ.den : Int) * ρ.den + 4 * ρ.den) * ((n : Int) + 1) + 1))
      = 4 * (((ρ.den : Int) * ρ.den + 4 * ρ.den) * ((n : Int) + 1)) + 4 := by
    generalize ((ρ.den : Int) * ρ.den + 4 * ρ.den) * ((n : Int) + 1) = P; ring_uor
  rw [e1] at hprod; rw [e2]; omega

end UOR.Bridge.F1Square.Analysis
