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

/-- **General-radius depth-Cauchy bound** for `artSum`: `|artSum u b − artSum u a| ≤ K·σ.den/(n+1)` for
    `a ≤ b`, `n+1 ≤ 2a+3`, any `σ < 1` with the even-sum bound `K` (`K·(1−σ²) ≥ 1`). Generalizes
    `artSum_depth_recip` (`K = 2`, `σ²≤1/2`) by swapping `mul_div2 → mul_div_gen`. -/
theorem artSum_depth_recip_gen (u σ : Q) (K : Nat) (hud : 0 < u.den) (hσ0 : 0 ≤ σ.num) (hσd : 0 < σ.den)
    (hu : Qle (Qabs u) σ) (hKF : Qle (⟨1, 1⟩ : Q) (mul (⟨(K : Int), 1⟩ : Q) (Qsub ⟨1, 1⟩ (mul σ σ))))
    (hσlt : σ.num.toNat < σ.den) {a b n : Nat} (hab : a ≤ b) (hn : n + 1 ≤ 2 * a + 3) :
    Qle (Qabs (Qsub (artSum u b) (artSum u a))) (⟨(K : Int) * (σ.den : Int), n + 1⟩ : Q) := by
  have hWd : 0 < (Qsub (⟨1, 1⟩ : Q) (mul σ σ)).den := Qsub_den_pos Nat.one_pos (Qmul_den_pos hσd hσd)
  have hW : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul σ σ)).num := by
    rcases Int.le_total 0 (Qsub (⟨1, 1⟩ : Q) (mul σ σ)).num with h | h
    · exact h
    · exfalso
      have hKnn : (0 : Int) ≤ (K : Int) := Int.ofNat_nonneg K
      have hkey : ((Qsub (⟨1, 1⟩ : Q) (mul σ σ)).den : Int)
          ≤ (K : Int) * (Qsub (⟨1, 1⟩ : Q) (mul σ σ)).num := by
        have hh := hKF; simp only [Qle, mul] at hh ⊢; push_cast at hh ⊢; omega
      have hmn : (K : Int) * (Qsub (⟨1, 1⟩ : Q) (mul σ σ)).num ≤ (K : Int) * 0 :=
        Int.mul_le_mul_of_nonneg_left h hKnn
      have hd1 : (1 : Int) ≤ ((Qsub (⟨1, 1⟩ : Q) (mul σ σ)).den : Int) := by exact_mod_cast hWd
      simp only [Int.mul_zero] at hmn; omega
  have htrunc := artSum_trunc hud hσ0 hσd hu hW hab
  have hd2 := mul_div_gen (Qabs_num_nonneg _)
    (Qabs_den_pos (Qsub_den_pos (artSum_den_pos hud b) (artSum_den_pos hud a)))
    (Qsub_den_pos Nat.one_pos (Qmul_den_pos hσd hσd)) Nat.one_pos (Int.ofNat_nonneg K) hKF htrunc
  refine Qle_trans (Qmul_den_pos Nat.one_pos (qpow_den_pos hσd _)) hd2 ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos n))
    (Qmul_le_mul_left (Int.ofNat_nonneg K) (qpow_le_recip hσ0 hσd hσlt hn)) ?_
  apply Qeq_le; simp only [Qeq, mul]; push_cast; ring_uor

set_option maxHeartbeats 1200000 in
/-- **General-radius `Rartanh` radius-independence**: `Rartanh t ρ ≈ Rartanh t ρ'` for any two radii
    `ρ, ρ'`, with `t` bounded by `τ < 1` carrying the even-sum bound `K` (`K·(1−τ²) ≥ 1`). The
    generalization of `Rartanh_radius_indep` past `τ²≤1/2`, via `artSum_depth_recip_gen` (`K·τ.den`
    legs) + `geoEvenSum_le_gen` (`2K` Lipschitz leg). Conclusion `Req` is `C`-agnostic. -/
theorem Rartanh_radius_indep_gen (t X X' : Real) (ρ ρ' τ : Q) (K : Nat) (hρd : 0 < ρ.den)
    (hρ'd : 0 < ρ'.den) (hτ0 : 0 ≤ τ.num) (hτd : 0 < τ.den) (hτlt : τ.num.toNat < τ.den)
    (hKF : Qle (⟨1, 1⟩ : Q) (mul (⟨(K : Int), 1⟩ : Q) (Qsub ⟨1, 1⟩ (mul τ τ))))
    (hbt : ∀ m, Qle (Qabs (t.seq m)) τ)
    (hXseq : ∀ j, X.seq j = artSum (t.seq (Rartanh_R ρ j)) (Rartanh_R ρ j))
    (hX'seq : ∀ j, X'.seq j = artSum (t.seq (Rartanh_R ρ' j)) (Rartanh_R ρ' j)) :
    Req X X' := by
  have htd : ∀ m, 0 < (t.seq m).den := fun m => t.den_pos m
  have hRge : ∀ (r : Q), 0 < r.den → ∀ j, j + 1 ≤ Rartanh_R r j := by
    intro r hrd j; unfold Rartanh_R
    have hk : 1 ≤ r.den * r.den + 4 * r.den := Nat.le_trans (by omega : 1 ≤ 4 * r.den) (Nat.le_add_left _ _)
    calc j + 1 = 1 * (j + 1) := by omega
      _ ≤ (r.den * r.den + 4 * r.den) * (j + 1) := Nat.mul_le_mul_right _ hk
  refine Req_of_lin_bound (C := 2 * K * τ.den + 2 * K) ?_
  intro n
  rw [hXseq, hX'seq]
  have hage := hRge ρ hρd n
  have hbge := hRge ρ' hρ'd n
  have haM : Rartanh_R ρ n ≤ max (Rartanh_R ρ n) (Rartanh_R ρ' n) := Nat.le_max_left _ _
  have hbM : Rartanh_R ρ' n ≤ max (Rartanh_R ρ n) (Rartanh_R ρ' n) := Nat.le_max_right _ _
  have hna : n + 1 ≤ 2 * Rartanh_R ρ n + 3 := by omega
  have hnb : n + 1 ≤ 2 * Rartanh_R ρ' n + 3 := by omega
  have hT1 : Qle (Qabs (Qsub (artSum (t.seq (Rartanh_R ρ n)) (Rartanh_R ρ n))
        (artSum (t.seq (Rartanh_R ρ n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n)))))
      (⟨(K : Int) * (τ.den : Int), n + 1⟩ : Q) := by
    rw [Qabs_Qsub_comm]
    exact artSum_depth_recip_gen (t.seq (Rartanh_R ρ n)) τ K (htd _) hτ0 hτd (hbt _) hKF hτlt haM hna
  have hT3 : Qle (Qabs (Qsub (artSum (t.seq (Rartanh_R ρ' n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n)))
        (artSum (t.seq (Rartanh_R ρ' n)) (Rartanh_R ρ' n)))) (⟨(K : Int) * (τ.den : Int), n + 1⟩ : Q) :=
    artSum_depth_recip_gen (t.seq (Rartanh_R ρ' n)) τ K (htd _) hτ0 hτd (hbt _) hKF hτlt hbM hnb
  have hT2 : Qle (Qabs (Qsub (artSum (t.seq (Rartanh_R ρ n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n)))
        (artSum (t.seq (Rartanh_R ρ' n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n)))))
      (⟨2 * (K : Int), n + 1⟩ : Q) := by
    refine Qle_trans (Qmul_den_pos (geoEvenSum_den_pos hτd _)
        (Qabs_den_pos (Qsub_den_pos (htd _) (htd _))))
      (artSum_Lip_le (htd _) (htd _) hτd (hbt _) (hbt _) _) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos (htd _) (htd _))))
      (Qmul_le_mul_right (Qabs_num_nonneg _)
        (geoEvenSum_le_gen hτ0 hτd Nat.one_pos (Int.ofNat_nonneg K) hKF _)) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)))
      (Qmul_le_mul_left (Int.ofNat_nonneg K) (t.reg (Rartanh_R ρ n) (Rartanh_R ρ' n))) ?_
    have hRa : Qle (Qbound (Rartanh_R ρ n)) (Qbound n) := by
      show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((Rartanh_R ρ n + 1 : Nat) : Int)
      rw [Int.one_mul, Int.one_mul]; exact_mod_cast (show n + 1 ≤ Rartanh_R ρ n + 1 by omega)
    have hRb : Qle (Qbound (Rartanh_R ρ' n)) (Qbound n) := by
      show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((Rartanh_R ρ' n + 1 : Nat) : Int)
      rw [Int.one_mul, Int.one_mul]; exact_mod_cast (show n + 1 ≤ Rartanh_R ρ' n + 1 by omega)
    refine Qle_trans (Qmul_den_pos Nat.one_pos (add_den_pos (Qbound_den_pos n) (Qbound_den_pos n)))
      (Qmul_le_mul_left (Int.ofNat_nonneg K) (Qadd_le_add hRa hRb)) ?_
    apply Qeq_le
    show Qeq (mul (⟨(K : Int), 1⟩ : Q) (add (Qbound n) (Qbound n))) (⟨2 * (K : Int), n + 1⟩ : Q)
    simp only [Qeq, mul, add, Qbound]; push_cast; ring_uor
  have hP0d : 0 < (artSum (t.seq (Rartanh_R ρ n)) (Rartanh_R ρ n)).den := artSum_den_pos (htd _) _
  have hP1d : 0 < (artSum (t.seq (Rartanh_R ρ n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n))).den :=
    artSum_den_pos (htd _) _
  have hP2d : 0 < (artSum (t.seq (Rartanh_R ρ' n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n))).den :=
    artSum_den_pos (htd _) _
  have hP3d : 0 < (artSum (t.seq (Rartanh_R ρ' n)) (Rartanh_R ρ' n)).den := artSum_den_pos (htd _) _
  have hpc : Qle (Qabs (Qsub (artSum (t.seq (Rartanh_R ρ n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n)))
        (artSum (t.seq (Rartanh_R ρ' n)) (Rartanh_R ρ' n))))
      (add (⟨2 * (K : Int), n + 1⟩ : Q) (⟨(K : Int) * (τ.den : Int), n + 1⟩ : Q)) :=
    Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hP1d hP2d))
        (Qabs_den_pos (Qsub_den_pos hP2d hP3d)))
      (Qabs_sub_triangle hP1d hP2d hP3d) (Qadd_le_add hT2 hT3)
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hP0d hP1d))
      (Qabs_den_pos (Qsub_den_pos hP1d hP3d)))
    (Qabs_sub_triangle hP0d hP1d hP3d) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos n) (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n)))
    (Qadd_le_add hT1 hpc) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n))
    (Qadd_le_add (Qle_refl _) (Qeq_le (Qadd_same_den_loc (2 * (K : Int)) ((K : Int) * (τ.den : Int)) (n + 1)))) ?_
  refine Qle_trans (Nat.succ_pos n)
    (Qeq_le (Qadd_same_den_loc ((K : Int) * (τ.den : Int)) (2 * (K : Int) + (K : Int) * (τ.den : Int)) (n + 1))) ?_
  apply Qeq_le; simp only [Qeq]; push_cast; ring_uor

end UOR.Bridge.F1Square.Analysis
