/-
F1 square — `log` on the positive reals (v0.13.0 transcendental).

`log(x) = 2·artanh(t)`, `t = (x−1)/(x+1)`, `artanh(t) = Σₙ t^{2n+1}/(2n+1)` for `|t| < 1`. Unlike the
exp/cos/sin series (factorial tails), the artanh series is **geometric**: for `|t| ≤ ρ < 1` the tail is
`Σ_{n>N} ρ^{2n+1}/(2n+1) ≤ ρ^{2N+3}/(1−ρ²)`, which → 0 geometrically; a Bernoulli estimate turns it into
a `1/(j+1)` reindex. This file builds that geometric machinery (the telescoping invariant, the tail
bound) — the foundation for `artanh` and hence `log`.

Pure Lean 4, no Mathlib, no `sorry`.
-/

import F1Square.Analysis.CosSin

namespace UOR.Bridge.F1Square.Analysis

/-- `ρ^{2n+1}`, the `n`-th geometric term. -/
def geoTerm (ρ : Q) (n : Nat) : Q := qpow ρ (2 * n + 1)

/-- `Σ_{n=0}^N ρ^{2n+1}`. -/
def geoSum (ρ : Q) : Nat → Q
  | 0 => geoTerm ρ 0
  | (n + 1) => add (geoSum ρ n) (geoTerm ρ (n + 1))

theorem geoSum_den_pos {ρ : Q} (hρd : 0 < ρ.den) : ∀ N, 0 < (geoSum ρ N).den
  | 0 => qpow_den_pos hρd _
  | (n + 1) => add_den_pos (geoSum_den_pos hρd n) (qpow_den_pos hρd _)

-- The telescoping ring identity `(G+P)(1−R²) + R²P ≈ G(1−R²) + P`.
private theorem geo_step_eq (G P R : Q) :
    Qeq (add (mul (add G P) (Qsub ⟨1, 1⟩ (mul R R))) (mul R (mul R P)))
      (add (mul G (Qsub ⟨1, 1⟩ (mul R R))) P) := by
  simp only [Qeq, add, mul, Qsub, neg]; push_cast; ring_uor

/-- **The geometric telescoping invariant**: `S_N·(1−ρ²) + ρ^{2N+3} = ρ` for every `N`. -/
theorem geoU_eq {ρ : Q} (hρd : 0 < ρ.den) : ∀ N,
    Qeq (add (mul (geoSum ρ N) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (qpow ρ (2 * N + 3))) ρ
  | 0 => by
      show Qeq (add (mul (geoTerm ρ 0) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (qpow ρ 3)) ρ
      simp only [geoTerm, qpow, Qeq, add, mul, Qsub, neg]; push_cast; ring_uor
  | (N + 1) => by
      refine Qeq_trans (add_den_pos (Qmul_den_pos (geoSum_den_pos hρd N)
          (Qsub_den_pos Nat.one_pos (Nat.mul_pos hρd hρd))) (qpow_den_pos hρd (2 * N + 3)))
        ?_ (geoU_eq hρd N)
      have hgs : geoSum ρ (N + 1) = add (geoSum ρ N) (qpow ρ (2 * N + 3)) := by
        show add (geoSum ρ N) (geoTerm ρ (N + 1)) = add (geoSum ρ N) (qpow ρ (2 * N + 3))
        unfold geoTerm; rw [show 2 * (N + 1) + 1 = 2 * N + 3 from by omega]
      have hpw : qpow ρ (2 * (N + 1) + 3) = mul ρ (mul ρ (qpow ρ (2 * N + 3))) := by
        rw [show 2 * (N + 1) + 3 = (2 * N + 3) + 1 + 1 from by omega, qpow_succ, qpow_succ]
      rw [hgs, hpw]
      exact geo_step_eq (geoSum ρ N) (qpow ρ (2 * N + 3)) ρ

-- `P·(1−R²) ≈ P − R²·P`  and the 3-point telescoping `(A−B)+(B−C) ≈ A−C` (abstract ring identities).
private theorem geo_term_id (P R : Q) :
    Qeq (mul P (Qsub ⟨1, 1⟩ (mul R R))) (Qsub P (mul R (mul R P))) := by
  simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor

private theorem Qsub_telescope (A B C : Q) :
    Qeq (add (Qsub A B) (Qsub B C)) (Qsub A C) := by
  simp only [Qeq, add, Qsub, neg]; push_cast; ring_uor

/-- **The exact geometric difference**: `(S_b − S_a)·(1−ρ²) = ρ^{2a+3} − ρ^{2b+3}` for `a ≤ b`. -/
theorem geo_diff_eq {ρ : Q} (hρd : 0 < ρ.den) (a : Nat) : ∀ {b}, a ≤ b →
    Qeq (mul (Qsub (geoSum ρ b) (geoSum ρ a)) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
      (Qsub (qpow ρ (2 * a + 3)) (qpow ρ (2 * b + 3))) := by
  have hW : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).den := Qsub_den_pos Nat.one_pos (Nat.mul_pos hρd hρd)
  intro b hab
  induction hab with
  | refl =>
      have h1 : (mul (Qsub (geoSum ρ a) (geoSum ρ a)) (Qsub ⟨1, 1⟩ (mul ρ ρ))).num = 0 := by
        show (Qsub (geoSum ρ a) (geoSum ρ a)).num * (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).num = 0
        rw [Qsub_self_num]; exact Int.zero_mul _
      have h2 : (Qsub (qpow ρ (2 * a + 3)) (qpow ρ (2 * a + 3))).num = 0 := Qsub_self_num _
      unfold Qeq; rw [h1, h2]; simp
  | @step k hk ih =>
      -- regroup S_{k+1} − S_a = (S_k − S_a) + ρ^{2k+3}
      have hgs : Qeq (Qsub (geoSum ρ (k + 1)) (geoSum ρ a))
          (add (Qsub (geoSum ρ k) (geoSum ρ a)) (qpow ρ (2 * k + 3))) := by
        have h := Qsub_add_right (geoSum ρ k) (geoTerm ρ (k + 1)) (geoSum ρ a)
        rw [show geoTerm ρ (k + 1) = qpow ρ (2 * k + 3) by
          unfold geoTerm; rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by omega]] at h
        exact h
      have hpw : qpow ρ (2 * (k + 1) + 3) = mul ρ (mul ρ (qpow ρ (2 * k + 3))) := by
        rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 1 + 1 from by omega, qpow_succ, qpow_succ]
      rw [hpw]
      have d1 := Qmul_den_pos (add_den_pos (Qsub_den_pos (geoSum_den_pos hρd k)
        (geoSum_den_pos hρd a)) (qpow_den_pos hρd (2 * k + 3))) hW
      have d2 := add_den_pos (Qmul_den_pos (Qsub_den_pos (geoSum_den_pos hρd k)
        (geoSum_den_pos hρd a)) hW) (Qmul_den_pos (qpow_den_pos hρd (2 * k + 3)) hW)
      have d3 := add_den_pos (Qsub_den_pos (qpow_den_pos hρd (2 * a + 3)) (qpow_den_pos hρd (2 * k + 3)))
        (Qsub_den_pos (qpow_den_pos hρd (2 * k + 3))
          (Qmul_den_pos hρd (Qmul_den_pos hρd (qpow_den_pos hρd (2 * k + 3)))))
      exact Qeq_trans d1 (Qmul_congr hgs (Qeq_refl _))
        (Qeq_trans d2 (Qmul_add_right (Qsub (geoSum ρ k) (geoSum ρ a)) (qpow ρ (2 * k + 3))
          (Qsub ⟨1, 1⟩ (mul ρ ρ)))
          (Qeq_trans d3 (Qadd_congr ih (geo_term_id (qpow ρ (2 * k + 3)) ρ))
            (Qsub_telescope (qpow ρ (2 * a + 3)) (qpow ρ (2 * k + 3))
              (mul ρ (mul ρ (qpow ρ (2 * k + 3)))))))

/-- `Qsub a b ≤ a` when `0 ≤ b.num`. -/
theorem Qsub_le_self {a b : Q} (hb : 0 ≤ b.num) : Qle (Qsub a b) a := by
  show (a.num * (b.den : Int) + (-b.num) * (a.den : Int)) * (a.den : Int)
      ≤ a.num * ((a.den : Int) * (b.den : Int))
  have hd : (0 : Int) ≤ (a.den : Int) * (a.den : Int) :=
    Int.mul_nonneg (Int.ofNat_nonneg _) (Int.ofNat_nonneg _)
  have hbn : 0 ≤ b.num * ((a.den : Int) * (a.den : Int)) := Int.mul_nonneg hb hd
  have e : a.num * ((a.den : Int) * (b.den : Int))
      - (a.num * (b.den : Int) + (-b.num) * (a.den : Int)) * (a.den : Int)
      = b.num * ((a.den : Int) * (a.den : Int)) := by ring_uor
  omega

/-- **The geometric tail bound**: `(S_b − S_a)·(1−ρ²) ≤ ρ^{2a+3}` for `a ≤ b`. -/
theorem geo_diff_bound {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) {a b : Nat} (hab : a ≤ b) :
    Qle (mul (Qsub (geoSum ρ b) (geoSum ρ a)) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (qpow ρ (2 * a + 3)) :=
  Qle_trans (Qsub_den_pos (qpow_den_pos hρd _) (qpow_den_pos hρd _))
    (Qeq_le (geo_diff_eq hρd a hab))
    (Qsub_le_self (qpow_nonneg hρ0 _))

-- ===========================================================================
-- The artanh series Σ t^{2n+1}/(2n+1), dominated by the geometric series.
-- ===========================================================================

/-- The `n`-th artanh term `t^{2n+1}/(2n+1)`. -/
def artTerm (t : Q) (n : Nat) : Q := mul (qpow t (2 * n + 1)) ⟨1, 2 * n + 1⟩

theorem artTerm_den_pos {t : Q} (htd : 0 < t.den) (n : Nat) : 0 < (artTerm t n).den :=
  Qmul_den_pos (qpow_den_pos htd _) (Nat.succ_pos _)

/-- The artanh partial sum `Σ_{n=0}^N t^{2n+1}/(2n+1)`. -/
def artSum (t : Q) : Nat → Q
  | 0 => artTerm t 0
  | (n + 1) => add (artSum t n) (artTerm t (n + 1))

theorem artSum_den_pos {t : Q} (htd : 0 < t.den) : ∀ N, 0 < (artSum t N).den
  | 0 => artTerm_den_pos htd 0
  | (n + 1) => add_den_pos (artSum_den_pos htd n) (artTerm_den_pos htd (n + 1))

/-- **Per-term domination**: `|t^{2n+1}/(2n+1)| ≤ ρ^{2n+1}` when `|t| ≤ ρ`. -/
theorem artTerm_abs_le {t ρ : Q} (htd : 0 < t.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (htρ : Qle (Qabs t) ρ) (n : Nat) : Qle (Qabs (artTerm t n)) (geoTerm ρ n) := by
  have hpw : Qle (Qabs (qpow t (2 * n + 1))) (qpow ρ (2 * n + 1)) :=
    Qle_trans (qpow_den_pos (Qabs_den_pos htd) _) (Qeq_le (qpow_abs t (2 * n + 1)))
      (qpow_base_mono (Qabs_den_pos htd) hρd (Qabs_num_nonneg t) htρ (2 * n + 1))
  have h1 : Qabs (artTerm t n) = mul (Qabs (qpow t (2 * n + 1))) ⟨1, 2 * n + 1⟩ := by
    unfold artTerm; rw [Qabs_mul]; rfl
  rw [h1]
  refine Qle_trans (Qmul_den_pos (qpow_den_pos hρd _) (Nat.succ_pos _))
    (Qmul_le_mul_right (by show (0 : Int) ≤ 1; decide) hpw) ?_
  -- mul (qpow ρ (2n+1)) ⟨1,2n+1⟩ ≤ qpow ρ (2n+1) = geoTerm ρ n
  refine Qle_trans (Qmul_den_pos (qpow_den_pos hρd _) (Nat.succ_pos _))
    (Qmul_le_mul_left (qpow_nonneg hρ0 _) (show Qle (⟨1, 2 * n + 1⟩ : Q) ⟨1, 1⟩ by
      show (1 : Int) * 1 ≤ 1 * ((2 * n + 1 : Nat) : Int); push_cast; omega))
    (Qeq_le (mul_one (qpow ρ (2 * n + 1))))

/-- **Truncation domination**: `|artSum gap| ≤ S_b − S_a` (geometric). -/
theorem artSum_abs_diff_le {t ρ : Q} (htd : 0 < t.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (htρ : Qle (Qabs t) ρ) {a b : Nat} (hab : a ≤ b) :
    Qle (Qabs (Qsub (artSum t b) (artSum t a))) (Qsub (geoSum ρ b) (geoSum ρ a)) := by
  induction hab with
  | refl =>
      have h := Qsub_self_num (artSum t a)
      have h' := Qsub_self_num (geoSum ρ a)
      unfold Qle Qabs; rw [h, h']; simp
  | @step k _ ih =>
      have hstep : Qle (Qabs (Qsub (artSum t (k + 1)) (artSum t a)))
          (add (Qabs (Qsub (artSum t k) (artSum t a))) (Qabs (artTerm t (k + 1)))) := by
        have heqabs := Qabs_Qeq (Qsub_add_right (artSum t k) (artTerm t (k + 1)) (artSum t a))
        refine Qle_congr_left (Qabs_den_pos (add_den_pos (Qsub_den_pos (artSum_den_pos htd k)
          (artSum_den_pos htd a)) (artTerm_den_pos htd (k + 1)))) (Qeq_symm heqabs) (Qabs_add_le _ _)
      have hbound : Qle (add (Qabs (Qsub (artSum t k) (artSum t a))) (Qabs (artTerm t (k + 1))))
          (add (Qsub (geoSum ρ k) (geoSum ρ a)) (geoTerm ρ (k + 1))) :=
        Qadd_le_add ih (artTerm_abs_le htd hρ0 hρd htρ (k + 1))
      have hregroup : Qeq (add (Qsub (geoSum ρ k) (geoSum ρ a)) (geoTerm ρ (k + 1)))
          (Qsub (geoSum ρ (k + 1)) (geoSum ρ a)) :=
        Qeq_symm (Qsub_add_right (geoSum ρ k) (geoTerm ρ (k + 1)) (geoSum ρ a))
      refine Qle_trans
        (add_den_pos (Qabs_den_pos (Qsub_den_pos (artSum_den_pos htd k) (artSum_den_pos htd a)))
          (Qabs_den_pos (artTerm_den_pos htd (k + 1))))
        hstep
        (Qle_trans (add_den_pos (Qsub_den_pos (geoSum_den_pos hρd k) (geoSum_den_pos hρd a))
          (qpow_den_pos hρd _)) hbound (Qeq_le hregroup))

/-- **The artanh truncation tail**: `|artSum gap|·(1−ρ²) ≤ ρ^{2a+3}` for `|t| ≤ ρ`, `a ≤ b`. -/
theorem artSum_trunc {t ρ : Q} (htd : 0 < t.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (htρ : Qle (Qabs t) ρ) (hW : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).num) {a b : Nat} (hab : a ≤ b) :
    Qle (mul (Qabs (Qsub (artSum t b) (artSum t a))) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
      (qpow ρ (2 * a + 3)) :=
  Qle_trans (Qmul_den_pos (Qsub_den_pos (geoSum_den_pos hρd b) (geoSum_den_pos hρd a))
      (Qsub_den_pos Nat.one_pos (Nat.mul_pos hρd hρd)))
    (Qmul_le_mul_right hW (artSum_abs_diff_le htd hρ0 hρd htρ hab))
    (geo_diff_bound hρ0 hρd hab)

end UOR.Bridge.F1Square.Analysis
