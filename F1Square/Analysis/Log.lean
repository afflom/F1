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
import F1Square.Analysis.Inv

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

-- ===========================================================================
-- The rational-base per-power difference bound (the ρ^{2n} decay the artanh Lipschitz needs).
-- ===========================================================================

/-- `|tⁱ| ≤ ρⁱ` when `|t| ≤ ρ` (rational base). -/
theorem qpow_abs_le_rat {t ρ : Q} (htd : 0 < t.den) (hρd : 0 < ρ.den) (htρ : Qle (Qabs t) ρ)
    (i : Nat) : Qle (Qabs (qpow t i)) (qpow ρ i) :=
  Qle_trans (qpow_den_pos (Qabs_den_pos htd) i) (Qeq_le (qpow_abs t i))
    (qpow_base_mono (Qabs_den_pos htd) hρd (Qabs_num_nonneg t) htρ i)

/-- The rational Lipschitz coefficient `i·ρ^{i-1}` (recursively, `P(0)=0`, `P(i+1)=ρ·P(i)+ρⁱ`). -/
def Pcoef (ρ : Q) : Nat → Q
  | 0 => ⟨0, 1⟩
  | (i + 1) => add (mul ρ (Pcoef ρ i)) (qpow ρ i)

theorem Pcoef_den_pos {ρ : Q} (hρd : 0 < ρ.den) : ∀ i, 0 < (Pcoef ρ i).den
  | 0 => Nat.one_pos
  | (i + 1) => add_den_pos (Qmul_den_pos hρd (Pcoef_den_pos hρd i)) (qpow_den_pos hρd i)

theorem Pcoef_num_nonneg {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) : ∀ i, 0 ≤ (Pcoef ρ i).num
  | 0 => by show (0 : Int) ≤ 0; decide
  | (i + 1) => by
      show 0 ≤ (add (mul ρ (Pcoef ρ i)) (qpow ρ i)).num
      show (0 : Int) ≤ ρ.num * (Pcoef ρ i).num * ((qpow ρ i).den : Int)
        + (qpow ρ i).num * ((ρ.den : Int) * (Pcoef ρ i).den)
      exact Int.add_nonneg
        (Int.mul_nonneg (Int.mul_nonneg hρ0 (Pcoef_num_nonneg hρ0 hρd i)) (Int.ofNat_nonneg _))
        (Int.mul_nonneg (qpow_nonneg hρ0 i) (Int.mul_nonneg (Int.ofNat_nonneg _) (Int.ofNat_nonneg _)))

-- `ρ·(C·D) + D·P ≈ (ρ·C + P)·D` (abstract).
private theorem pcoef_factor (R C D P : Q) :
    Qeq (add (mul R (mul C D)) (mul D P)) (mul (add (mul R C) P) D) := by
  simp only [Qeq, add, mul]; push_cast; ring_uor

/-- **Rational per-power difference bound**: `|tⁱ − t'ⁱ| ≤ (i·ρ^{i-1})·|t − t'|` for `|t|,|t'| ≤ ρ`. -/
theorem qpow_diff_bound_rat {t t' ρ : Q} (htd : 0 < t.den) (ht'd : 0 < t'.den) (hρd : 0 < ρ.den)
    (htρ : Qle (Qabs t) ρ) (ht'ρ : Qle (Qabs t') ρ) :
    ∀ i, Qle (Qabs (Qsub (qpow t i) (qpow t' i))) (mul (Pcoef ρ i) (Qabs (Qsub t t')))
  | 0 => by
      show Qle (Qabs (Qsub (qpow t 0) (qpow t' 0))) (mul (⟨0, 1⟩ : Q) (Qabs (Qsub t t')))
      have h0 : (Qsub (qpow t 0) (qpow t' 0)).num = 0 := rfl
      unfold Qle Qabs mul
      rw [h0]; simp
  | (i + 1) => by
      have ihh := qpow_diff_bound_rat htd ht'd hρd htρ ht'ρ i
      have hqpid : 0 < (qpow t i).den := qpow_den_pos htd i
      have hqp'id : 0 < (qpow t' i).den := qpow_den_pos ht'd i
      have hid : Qeq (Qsub (qpow t (i + 1)) (qpow t' (i + 1)))
          (add (mul t (Qsub (qpow t i) (qpow t' i))) (mul (Qsub t t') (qpow t' i))) := by
        show Qeq (Qsub (mul t (qpow t i)) (mul t' (qpow t' i)))
          (add (mul t (Qsub (qpow t i) (qpow t' i))) (mul (Qsub t t') (qpow t' i)))
        simp only [Qeq, Qsub, mul, add, neg]; push_cast; ring_uor
      have htri : Qle (Qabs (Qsub (qpow t (i + 1)) (qpow t' (i + 1))))
          (add (Qabs (mul t (Qsub (qpow t i) (qpow t' i)))) (Qabs (mul (Qsub t t') (qpow t' i)))) :=
        Qle_congr_left (Qabs_den_pos (add_den_pos (Qmul_den_pos htd (Qsub_den_pos hqpid hqp'id))
          (Qmul_den_pos (Qsub_den_pos htd ht'd) hqp'id))) (Qeq_symm (Qabs_Qeq hid)) (Qabs_add_le _ _)
      have hP1 : Qle (Qabs (mul t (Qsub (qpow t i) (qpow t' i))))
          (mul ρ (mul (Pcoef ρ i) (Qabs (Qsub t t')))) := by
        rw [Qabs_mul]
        exact Qmul_le_mul (Qabs_den_pos htd) hρd (Qabs_den_pos (Qsub_den_pos hqpid hqp'id))
          (Qabs_num_nonneg t) (Qabs_num_nonneg _) htρ ihh
      have hP2 : Qle (Qabs (mul (Qsub t t') (qpow t' i)))
          (mul (Qabs (Qsub t t')) (qpow ρ i)) := by
        rw [Qabs_mul]
        exact Qmul_le_mul_left (Qabs_num_nonneg _) (qpow_abs_le_rat ht'd hρd ht'ρ i)
      have hsum := Qadd_le_add hP1 hP2
      have hfactor : Qeq (add (mul ρ (mul (Pcoef ρ i) (Qabs (Qsub t t'))))
            (mul (Qabs (Qsub t t')) (qpow ρ i)))
          (mul (Pcoef ρ (i + 1)) (Qabs (Qsub t t'))) :=
        pcoef_factor ρ (Pcoef ρ i) (Qabs (Qsub t t')) (qpow ρ i)
      refine Qle_trans ?_ htri (Qle_trans ?_ hsum (Qeq_le hfactor))
      · exact add_den_pos (Qabs_den_pos (Qmul_den_pos htd (Qsub_den_pos hqpid hqp'id)))
          (Qabs_den_pos (Qmul_den_pos (Qsub_den_pos htd ht'd) hqp'id))
      · exact add_den_pos (Qmul_den_pos hρd (Qmul_den_pos (Pcoef_den_pos hρd i)
          (Qabs_den_pos (Qsub_den_pos htd ht'd))))
          (Qmul_den_pos (Qabs_den_pos (Qsub_den_pos htd ht'd)) (qpow_den_pos hρd i))

-- ===========================================================================
-- The artanh Lipschitz bound (geometric, with the 1/(2n+1) weight cancelled).
-- ===========================================================================

/-- `Σ_{n=0}^N ρ^{2n}` (even powers). -/
def geoEvenSum (ρ : Q) : Nat → Q
  | 0 => qpow ρ 0
  | (n + 1) => add (geoEvenSum ρ n) (qpow ρ (2 * (n + 1)))

theorem geoEvenSum_den_pos {ρ : Q} (hρd : 0 < ρ.den) : ∀ N, 0 < (geoEvenSum ρ N).den
  | 0 => qpow_den_pos hρd 0
  | (n + 1) => add_den_pos (geoEvenSum_den_pos hρd n) (qpow_den_pos hρd _)

/-- Even telescoping invariant: `E_N·(1−ρ²) + ρ^{2N+2} = 1`. -/
theorem geoEven_eq {ρ : Q} (hρd : 0 < ρ.den) : ∀ N,
    Qeq (add (mul (geoEvenSum ρ N) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (qpow ρ (2 * N + 2))) ⟨1, 1⟩
  | 0 => by
      show Qeq (add (mul (qpow ρ 0) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (qpow ρ 2)) ⟨1, 1⟩
      simp only [qpow, Qeq, add, mul, Qsub, neg]; push_cast; ring_uor
  | (N + 1) => by
      refine Qeq_trans (add_den_pos (Qmul_den_pos (geoEvenSum_den_pos hρd N)
          (Qsub_den_pos Nat.one_pos (Nat.mul_pos hρd hρd))) (qpow_den_pos hρd (2 * N + 2)))
        ?_ (geoEven_eq hρd N)
      have hgs : geoEvenSum ρ (N + 1) = add (geoEvenSum ρ N) (qpow ρ (2 * N + 2)) := by
        show add (geoEvenSum ρ N) (qpow ρ (2 * (N + 1))) = add (geoEvenSum ρ N) (qpow ρ (2 * N + 2))
        rw [show 2 * (N + 1) = 2 * N + 2 from by omega]
      have hpw : qpow ρ (2 * (N + 1) + 2) = mul ρ (mul ρ (qpow ρ (2 * N + 2))) := by
        rw [show 2 * (N + 1) + 2 = (2 * N + 2) + 1 + 1 from by omega, qpow_succ, qpow_succ]
      rw [hgs, hpw]
      exact geo_step_eq (geoEvenSum ρ N) (qpow ρ (2 * N + 2)) ρ

/-- `E_N·(1−ρ²) ≤ 1`. -/
theorem geoEven_bound {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (N : Nat) :
    Qle (mul (geoEvenSum ρ N) (Qsub ⟨1, 1⟩ (mul ρ ρ))) ⟨1, 1⟩ :=
  Qle_trans (add_den_pos (Qmul_den_pos (geoEvenSum_den_pos hρd N)
      (Qsub_den_pos Nat.one_pos (Nat.mul_pos hρd hρd))) (qpow_den_pos hρd _))
    (Qle_self_add (qpow_nonneg hρ0 _)) (Qeq_le (geoEven_eq hρd N))

-- `(k·P)·... ` cancellation:  `((k·P)·D)·(1/k) ≈ P·D`.
private theorem cancel_k (k : Nat) (P D : Q) :
    Qeq (mul (mul (mul ⟨(k : Int), 1⟩ P) D) ⟨1, k⟩) (mul P D) := by
  simp only [Qeq, mul]; push_cast; ring_uor

-- `ρ·(k·Pi) + ρ·Pi ≈ (k+1)·(ρ·Pi)` (abstract).
private theorem pcoef_step_eq (R Pi : Q) (k : Nat) :
    Qeq (add (mul R (mul ⟨(k : Int), 1⟩ Pi)) (mul R Pi))
      (mul ⟨((k + 1 : Nat) : Int), 1⟩ (mul R Pi)) := by
  simp only [Qeq, add, mul]; push_cast; ring_uor

/-- Closed form `Pcoef ρ (i+1) = (i+1)·ρⁱ`. -/
theorem Pcoef_closed {ρ : Q} (hρd : 0 < ρ.den) : ∀ i,
    Qeq (Pcoef ρ (i + 1)) (mul ⟨((i + 1 : Nat) : Int), 1⟩ (qpow ρ i))
  | 0 => by
      show Qeq (add (mul ρ ⟨0, 1⟩) (qpow ρ 0)) (mul ⟨1, 1⟩ (qpow ρ 0))
      simp only [qpow, Qeq, add, mul]; push_cast; ring_uor
  | (i + 1) => by
      show Qeq (add (mul ρ (Pcoef ρ (i + 1))) (qpow ρ (i + 1)))
        (mul ⟨((i + 1 + 1 : Nat) : Int), 1⟩ (qpow ρ (i + 1)))
      have ih := Pcoef_closed hρd i
      rw [qpow_succ ρ i]
      refine Qeq_trans
        (add_den_pos (Qmul_den_pos hρd (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd i)))
          (Qmul_den_pos hρd (qpow_den_pos hρd i)))
        (Qadd_congr (Qmul_congr (Qeq_refl ρ) ih) (Qeq_refl (mul ρ (qpow ρ i))))
        (pcoef_step_eq ρ (qpow ρ i) (i + 1))

/-- **Per-term artanh Lipschitz**: `|t^{2n+1}/(2n+1) − t'^{2n+1}/(2n+1)| ≤ ρ^{2n}·|t − t'|`
    (the `(2n+1)` coefficient cancels the `1/(2n+1)` weight). -/
theorem artTerm_diff_bound {t t' ρ : Q} (htd : 0 < t.den) (ht'd : 0 < t'.den) (hρd : 0 < ρ.den)
    (htρ : Qle (Qabs t) ρ) (ht'ρ : Qle (Qabs t') ρ) (n : Nat) :
    Qle (Qabs (Qsub (artTerm t n) (artTerm t' n))) (mul (qpow ρ (2 * n)) (Qabs (Qsub t t'))) := by
  have hfac : Qeq (Qsub (artTerm t n) (artTerm t' n))
      (mul (Qsub (qpow t (2 * n + 1)) (qpow t' (2 * n + 1))) ⟨1, 2 * n + 1⟩) := by
    show Qeq (Qsub (mul (qpow t (2 * n + 1)) ⟨1, 2 * n + 1⟩)
        (mul (qpow t' (2 * n + 1)) ⟨1, 2 * n + 1⟩))
      (mul (Qsub (qpow t (2 * n + 1)) (qpow t' (2 * n + 1))) ⟨1, 2 * n + 1⟩)
    simp only [Qeq, Qsub, mul, add, neg]; push_cast; ring_uor
  have heq1 : Qeq (Qabs (Qsub (artTerm t n) (artTerm t' n)))
      (mul (Qabs (Qsub (qpow t (2 * n + 1)) (qpow t' (2 * n + 1)))) ⟨1, 2 * n + 1⟩) := by
    have h := Qabs_Qeq hfac
    rw [Qabs_mul, show Qabs (⟨1, 2 * n + 1⟩ : Q) = ⟨1, 2 * n + 1⟩ from rfl] at h; exact h
  have hb1 := Qmul_le_mul_right (a := Qabs (Qsub (qpow t (2 * n + 1)) (qpow t' (2 * n + 1))))
    (b := mul (Pcoef ρ (2 * n + 1)) (Qabs (Qsub t t'))) (c := ⟨1, 2 * n + 1⟩)
    (by show (0 : Int) ≤ 1; decide) (qpow_diff_bound_rat htd ht'd hρd htρ ht'ρ (2 * n + 1))
  have hmid : Qeq (mul (mul (Pcoef ρ (2 * n + 1)) (Qabs (Qsub t t'))) ⟨1, 2 * n + 1⟩)
      (mul (mul (mul ⟨((2 * n + 1 : Nat) : Int), 1⟩ (qpow ρ (2 * n))) (Qabs (Qsub t t')))
        ⟨1, 2 * n + 1⟩) :=
    Qmul_congr (Qmul_congr (Pcoef_closed hρd (2 * n)) (Qeq_refl _)) (Qeq_refl _)
  exact Qle_trans
    (Qmul_den_pos (Qabs_den_pos (Qsub_den_pos (qpow_den_pos htd _) (qpow_den_pos ht'd _)))
      (Nat.succ_pos _))
    (Qeq_le heq1)
    (Qle_trans (Qmul_den_pos (Qmul_den_pos (Pcoef_den_pos hρd _)
        (Qabs_den_pos (Qsub_den_pos htd ht'd))) (Nat.succ_pos _)) hb1
      (Qle_trans (Qmul_den_pos (Qmul_den_pos (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd _))
          (Qabs_den_pos (Qsub_den_pos htd ht'd))) (Nat.succ_pos _))
        (Qeq_le hmid) (Qeq_le (cancel_k (2 * n + 1) (qpow ρ (2 * n)) (Qabs (Qsub t t'))))))

/-- **The artanh Lipschitz sum bound**: `|artSum_t(N) − artSum_{t'}(N)| ≤ E_N·|t − t'|`. -/
theorem artSum_Lip_le {t t' ρ : Q} (htd : 0 < t.den) (ht'd : 0 < t'.den) (hρd : 0 < ρ.den)
    (htρ : Qle (Qabs t) ρ) (ht'ρ : Qle (Qabs t') ρ) :
    ∀ N, Qle (Qabs (Qsub (artSum t N) (artSum t' N))) (mul (geoEvenSum ρ N) (Qabs (Qsub t t')))
  | 0 => artTerm_diff_bound htd ht'd hρd htρ ht'ρ 0
  | (N + 1) => by
      have ih := artSum_Lip_le htd ht'd hρd htρ ht'ρ N
      have hAd : 0 < (artSum t N).den := artSum_den_pos htd N
      have hCd : 0 < (artSum t' N).den := artSum_den_pos ht'd N
      have hBd : 0 < (artTerm t (N + 1)).den := artTerm_den_pos htd (N + 1)
      have hDd : 0 < (artTerm t' (N + 1)).den := artTerm_den_pos ht'd (N + 1)
      refine Qle_trans
        (add_den_pos (Qabs_den_pos (Qsub_den_pos hAd hCd)) (Qabs_den_pos (Qsub_den_pos hBd hDd)))
        (Qabs_sub_add4 hAd hBd hCd hDd)
        (Qle_trans
          (add_den_pos (Qmul_den_pos (geoEvenSum_den_pos hρd N)
            (Qabs_den_pos (Qsub_den_pos htd ht'd)))
            (Qmul_den_pos (qpow_den_pos hρd _) (Qabs_den_pos (Qsub_den_pos htd ht'd))))
          (Qadd_le_add ih (artTerm_diff_bound htd ht'd hρd htρ ht'ρ (N + 1)))
          (Qeq_le (Qeq_symm (Qmul_add_right (geoEvenSum ρ N) (qpow ρ (2 * (N + 1)))
            (Qabs (Qsub t t'))))))

-- ===========================================================================
-- The geometric reindex for ρ ≤ 1/2:  ρᵐ ≤ 1/(m+1).
-- ===========================================================================

/-- `(1/2)ᵐ = 1/2ᵐ`. -/
theorem qpow_half_value : ∀ m, qpow (⟨1, 2⟩ : Q) m = ⟨1, npow 2 m⟩
  | 0 => rfl
  | (m + 1) => by
      show mul (⟨1, 2⟩ : Q) (qpow (⟨1, 2⟩ : Q) m) = ⟨1, npow 2 (m + 1)⟩
      rw [qpow_half_value m]; rfl

/-- For `0 ≤ ρ ≤ 1/2`: `ρᵐ ≤ 1/(m+1)`. -/
theorem qpow_half_le {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρ12 : Qle ρ ⟨1, 2⟩) (m : Nat) :
    Qle (qpow ρ m) ⟨1, m + 1⟩ := by
  have h1 : Qle (qpow ρ m) (qpow (⟨1, 2⟩ : Q) m) :=
    qpow_base_mono hρd (by decide) hρ0 hρ12 m
  rw [qpow_half_value m] at h1
  refine Qle_trans (npow_pos (by decide) m) h1 ?_
  show (1 : Int) * ((m + 1 : Nat) : Int) ≤ 1 * ((npow 2 m : Nat) : Int)
  rw [Int.one_mul, Int.one_mul]; exact_mod_cast two_pow_ge m

/-- **The general Bernoulli bound**: for `0 ≤ ρ < 1` (i.e. `p = ρ.num.toNat ≤ q = ρ.den`),
    `ρᵐ ≤ q/(q + m(q−p))` — a `1/(linear)` decay, the engine of the geometric reindex. -/
theorem qpow_geom_bound {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hple : ρ.num.toNat ≤ ρ.den) :
    ∀ m, Qle (qpow ρ m) ⟨(ρ.den : Int), ρ.den + m * (ρ.den - ρ.num.toNat)⟩
  | 0 => by
      show (1 : Int) * ((ρ.den + 0 * (ρ.den - ρ.num.toNat) : Nat) : Int) ≤ (ρ.den : Int) * 1
      omega
  | (m + 1) => by
      have ih := qpow_geom_bound hρ0 hρd hple m
      have hsc : ρ.num.toNat + (ρ.den - ρ.num.toNat) = ρ.den := Nat.add_sub_cancel' hple
      have h2 : (ρ.num.toNat : Int) + ((ρ.den - ρ.num.toNat : Nat) : Int) = (ρ.den : Int) := by
        exact_mod_cast hsc
      have hcs : ((ρ.den - ρ.num.toNat : Nat) : Int) = (ρ.den : Int) - (ρ.num.toNat : Int) := by
        rw [← h2]; ring_uor
      have hp : ((ρ.num.toNat : Nat) : Int) = ρ.num := Int.toNat_of_nonneg hρ0
      have hqp : (0 : Int) ≤ (ρ.den : Int) - ρ.num := by
        have h1 : (ρ.num.toNat : Int) ≤ (ρ.den : Int) := by exact_mod_cast hple
        omega
      have hstep : Qle (mul ρ ⟨(ρ.den : Int), ρ.den + m * (ρ.den - ρ.num.toNat)⟩)
          ⟨(ρ.den : Int), ρ.den + (m + 1) * (ρ.den - ρ.num.toNat)⟩ := by
        show (ρ.num * (ρ.den : Int)) * ((ρ.den + (m + 1) * (ρ.den - ρ.num.toNat) : Nat) : Int)
            ≤ (ρ.den : Int) * ((ρ.den * (ρ.den + m * (ρ.den - ρ.num.toNat)) : Nat) : Int)
        have hdiff : (ρ.den : Int)
              * ((ρ.den * (ρ.den + m * (ρ.den - ρ.num.toNat)) : Nat) : Int)
            - (ρ.num * (ρ.den : Int))
              * ((ρ.den + (m + 1) * (ρ.den - ρ.num.toNat) : Nat) : Int)
            = (ρ.den : Int) * (((ρ.den : Int) - ρ.num)
              * ((ρ.den : Int) - ρ.num) * ((m : Int) + 1)) := by
          push_cast [hcs, hp]; ring_uor
        have hnn : (0 : Int) ≤ (ρ.den : Int) * (((ρ.den : Int) - ρ.num)
            * ((ρ.den : Int) - ρ.num) * ((m : Int) + 1)) :=
          Int.mul_nonneg (Int.ofNat_nonneg _)
            (Int.mul_nonneg (Int.mul_nonneg hqp hqp) (by omega))
        omega
      exact Qle_trans (Qmul_den_pos hρd (Nat.lt_of_lt_of_le hρd (Nat.le_add_right _ _)))
        (Qmul_le_mul_left hρ0 ih) hstep

/-- Right cancellation for `≤` by a strictly positive rational: `a·c ≤ b·c ⟹ a ≤ b`. -/
theorem Qmul_le_cancel_right {a b c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (h : Qle (mul a c) (mul b c)) : Qle a b := by
  have hc : (0 : Int) < c.num * (c.den : Int) := Int.mul_pos hcn (by exact_mod_cast hcd)
  have h' : (a.num * (b.den : Int)) * (c.num * (c.den : Int))
      ≤ (b.num * (a.den : Int)) * (c.num * (c.den : Int)) := by
    have e1 : a.num * c.num * ((b.den : Int) * (c.den : Int))
        = (a.num * (b.den : Int)) * (c.num * (c.den : Int)) := by ring_uor
    have e2 : b.num * c.num * ((a.den : Int) * (c.den : Int))
        = (b.num * (a.den : Int)) * (c.num * (c.den : Int)) := by ring_uor
    have hh : a.num * c.num * ((b.den : Int) * (c.den : Int))
        ≤ b.num * c.num * ((a.den : Int) * (c.den : Int)) := by
      simpa only [mul, Qle] using h
    rw [e1, e2] at hh; exact hh
  exact Int.le_of_mul_le_mul_right h' hc

/-- `1·a ≈ a`. -/
theorem Qone_mul (a : Q) : Qeq (mul ⟨1, 1⟩ a) a := by simp only [Qeq, mul]; push_cast; ring_uor

/-- `(a·b)·c ≈ (a·c)·b`. -/
theorem Qmul_swap_right (a b c : Q) : Qeq (mul (mul a b) c) (mul (mul a c) b) := by
  simp only [Qeq, mul]; push_cast; ring_uor

-- ===========================================================================
-- The artanh diagonal: artanh(t) for a real t with |t.seq n| ≤ ρ < 1.
-- ===========================================================================

/-- The artanh diagonal reindex: `(q² + 4q)·(j+1)` with `q = ρ.den` (≥ 4q and ≥ q², so both the
    Lipschitz and the geometric truncation shrink fast enough). -/
def Rartanh_R (ρ : Q) (j : Nat) : Nat := (ρ.den * ρ.den + 4 * ρ.den) * (j + 1)

/-- The `j`-th artanh diagonal approximant. -/
def Rartanh_seq (t : Real) (ρ : Q) (j : Nat) : Q := artSum (t.seq (Rartanh_R ρ j)) (Rartanh_R ρ j)

/-- **The artanh reindex inequality**: the truncation `1/(q+(2Rⱼ+3)(q−p))`-bound plus the
    argument-gap `2/(Rⱼ+1)` is `≤ (1/(j+1))·(1−ρ²)`, so the diagonal gap is `≤ 1/(j+1)`. -/
theorem artanh_reindex {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hlt : ρ.num.toNat < ρ.den)
    (j : Nat) :
    Qle (add (⟨2, Rartanh_R ρ j + 1⟩ : Q)
        ⟨(ρ.den : Int), ρ.den + (2 * Rartanh_R ρ j + 3) * (ρ.den - ρ.num.toNat)⟩)
      (mul (⟨1, j + 1⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ))) := by
  -- abbreviations: q = ρ.den, p = ρ.num.toNat, C = q²+4q, Rⱼ = C(j+1)
  -- casts: q − p as ℤ, p = ρ.num, and the positivity facts
  have hsc : ρ.num.toNat + (ρ.den - ρ.num.toNat) = ρ.den := Nat.add_sub_cancel' (Nat.le_of_lt hlt)
  have h2 : (ρ.num.toNat : Int) + ((ρ.den - ρ.num.toNat : Nat) : Int) = (ρ.den : Int) := by
    exact_mod_cast hsc
  have hp : ((ρ.num.toNat : Nat) : Int) = ρ.num := Int.toNat_of_nonneg hρ0
  have hcs : ((ρ.den - ρ.num.toNat : Nat) : Int) = (ρ.den : Int) - ρ.num := by rw [← hp] at h2 ⊢; omega
  have hqp1I : (1 : Int) ≤ (ρ.den : Int) - ρ.num := by
    have : (ρ.num.toNat : Int) < (ρ.den : Int) := by exact_mod_cast hlt
    omega
  have hdenpos : (0 : Int) ≤ (ρ.den : Int) := Int.ofNat_nonneg _
  have hjpos : (0 : Int) ≤ (j : Int) + 1 := by omega
  -- half1: 2/(Rⱼ+1) ≤ 1/(2q(j+1))
  have half1 : Qle (⟨2, Rartanh_R ρ j + 1⟩ : Q) ⟨1, 2 * ρ.den * (j + 1)⟩ := by
    show (2 : Int) * ((2 * ρ.den * (j + 1) : Nat) : Int) ≤ 1 * ((Rartanh_R ρ j + 1 : Nat) : Int)
    unfold Rartanh_R
    have hdiff : (1 : Int) * (((ρ.den * ρ.den + 4 * ρ.den) * (j + 1) + 1 : Nat) : Int)
        - 2 * ((2 * ρ.den * (j + 1) : Nat) : Int)
        = (ρ.den : Int) * (ρ.den : Int) * ((j : Int) + 1) + 1 := by push_cast; ring_uor
    have hnn : (0 : Int) ≤ (ρ.den : Int) * (ρ.den : Int) * ((j : Int) + 1) + 1 :=
      Int.add_nonneg (Int.mul_nonneg (Int.mul_nonneg hdenpos hdenpos) hjpos) (by decide)
    omega
  -- half2: 1/(q+(2Rⱼ+3)(q−p)) ≤ 1/(2q(j+1))
  have half2 : Qle (⟨(ρ.den : Int), ρ.den + (2 * Rartanh_R ρ j + 3) * (ρ.den - ρ.num.toNat)⟩ : Q)
      ⟨1, 2 * ρ.den * (j + 1)⟩ := by
    show (ρ.den : Int) * ((2 * ρ.den * (j + 1) : Nat) : Int)
        ≤ 1 * ((ρ.den + (2 * Rartanh_R ρ j + 3) * (ρ.den - ρ.num.toNat) : Nat) : Int)
    unfold Rartanh_R
    have hdiff : (1 : Int)
          * ((ρ.den + (2 * ((ρ.den * ρ.den + 4 * ρ.den) * (j + 1)) + 3) * (ρ.den - ρ.num.toNat) : Nat) : Int)
        - (ρ.den : Int) * ((2 * ρ.den * (j + 1) : Nat) : Int)
        = (ρ.den : Int) + 3 * ((ρ.den : Int) - ρ.num)
          + 8 * (ρ.den : Int) * ((j : Int) + 1) * ((ρ.den : Int) - ρ.num)
          + 2 * (ρ.den : Int) * (ρ.den : Int) * ((j : Int) + 1) * (((ρ.den : Int) - ρ.num) - 1) := by
      push_cast [hcs]; ring_uor
    have hnn : (0 : Int) ≤ (ρ.den : Int) + 3 * ((ρ.den : Int) - ρ.num)
        + 8 * (ρ.den : Int) * ((j : Int) + 1) * ((ρ.den : Int) - ρ.num)
        + 2 * (ρ.den : Int) * (ρ.den : Int) * ((j : Int) + 1) * (((ρ.den : Int) - ρ.num) - 1) := by
      have hs0 : (0 : Int) ≤ (ρ.den : Int) - ρ.num := by omega
      have hs1 : (0 : Int) ≤ ((ρ.den : Int) - ρ.num) - 1 := by omega
      have t1 : (0 : Int) ≤ 3 * ((ρ.den : Int) - ρ.num) := Int.mul_nonneg (by decide) hs0
      have t2 : (0 : Int) ≤ 8 * (ρ.den : Int) * ((j : Int) + 1) * ((ρ.den : Int) - ρ.num) :=
        Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (by decide) hdenpos) hjpos) hs0
      have t3 : (0 : Int) ≤ 2 * (ρ.den : Int) * (ρ.den : Int) * ((j : Int) + 1)
          * (((ρ.den : Int) - ρ.num) - 1) :=
        Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (by decide) hdenpos)
          hdenpos) hjpos) hs1
      omega
    omega
  -- 1/(2q(j+1)) + 1/(2q(j+1)) = 1/(q(j+1))
  have hsum : Qeq (add (⟨1, 2 * ρ.den * (j + 1)⟩ : Q) ⟨1, 2 * ρ.den * (j + 1)⟩)
      ⟨1, ρ.den * (j + 1)⟩ := by simp only [Qeq, add]; push_cast; ring_uor
  -- 1/(q(j+1)) ≤ (1/(j+1))·(1−ρ²)   (uses q(q−1) ≥ p², i.e. p < q)
  have hlast : Qle (⟨1, ρ.den * (j + 1)⟩ : Q) (mul (⟨1, j + 1⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ))) := by
    have hltI : ρ.num < (ρ.den : Int) := by rw [← hp]; exact_mod_cast hlt
    simp only [Qle, mul, Qsub, add, neg]
    push_cast
    have hdiff : 1 * (1 * ((ρ.den : Int) * (ρ.den : Int)) + -(ρ.num * ρ.num) * 1)
          * ((ρ.den : Int) * ((j : Int) + 1))
        - ((j : Int) + 1) * (1 * ((ρ.den : Int) * (ρ.den : Int)))
        = ((j : Int) + 1) * (ρ.den : Int)
          * ((ρ.den : Int) * (ρ.den : Int) - (ρ.den : Int) - ρ.num * ρ.num) := by ring_uor
    have hnn : (0 : Int) ≤ ((j : Int) + 1) * (ρ.den : Int)
        * ((ρ.den : Int) * (ρ.den : Int) - (ρ.den : Int) - ρ.num * ρ.num) := by
      have hp2 : ρ.num * ρ.num ≤ ((ρ.den : Int) - 1) * ((ρ.den : Int) - 1) :=
        Int.mul_le_mul (by omega) (by omega) hρ0 (by omega)
      have he2 : ((ρ.den : Int) - 1) * ((ρ.den : Int) - 1)
          = (ρ.den : Int) * (ρ.den : Int) - 2 * (ρ.den : Int) + 1 := by ring_uor
      have hkey : (0 : Int) ≤ (ρ.den : Int) * (ρ.den : Int) - (ρ.den : Int) - ρ.num * ρ.num := by
        omega
      exact Int.mul_nonneg (Int.mul_nonneg hjpos hdenpos) hkey
    omega
  refine Qle_trans (add_den_pos (Nat.mul_pos (Nat.mul_pos (by decide) hρd) (Nat.succ_pos j))
      (Nat.mul_pos (Nat.mul_pos (by decide) hρd) (Nat.succ_pos j))) (Qadd_le_add half1 half2) ?_
  exact Qle_trans (Nat.mul_pos hρd (Nat.succ_pos j)) (Qeq_le hsum) hlast

set_option maxHeartbeats 1000000 in
/-- **The artanh diagonal regularity (one side)**: for `j ≤ k`, the gap is `≤ 1/(j+1)`. -/
theorem Rartanh_diag_le (t : Real) {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (hb : ∀ n, Qle (Qabs (t.seq n)) ρ) {j k : Nat} (hjk : j ≤ k) :
    Qle (Qabs (Qsub (Rartanh_seq t ρ j) (Rartanh_seq t ρ k))) (Qbound j) := by
  have hltI : ρ.num < (ρ.den : Int) := by rw [← Int.toNat_of_nonneg hρ0]; exact_mod_cast hlt
  have hd1 : (1 : Int) ≤ (ρ.den : Int) := by exact_mod_cast hρd
  -- W = 1 − ρ²,  positive
  have hWd : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).den :=
    Qsub_den_pos Nat.one_pos (Nat.mul_pos hρd hρd)
  have hWn : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).num := by
    show 0 < 1 * ((ρ.den * ρ.den : Nat) : Int) + -(ρ.num * ρ.num) * ((1 : Nat) : Int)
    have hp2 : ρ.num * ρ.num ≤ ((ρ.den : Int) - 1) * ((ρ.den : Int) - 1) :=
      Int.mul_le_mul (by omega) (by omega) hρ0 (by omega)
    have he2 : ((ρ.den : Int) - 1) * ((ρ.den : Int) - 1)
        = (ρ.den : Int) * (ρ.den : Int) - 2 * (ρ.den : Int) + 1 := by ring_uor
    push_cast; omega
  have hWnn : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).num := Int.le_of_lt hWn
  -- reindex monotone, and the argument-gap bound
  have hRle : Rartanh_R ρ j ≤ Rartanh_R ρ k := by
    unfold Rartanh_R; exact Nat.mul_le_mul (Nat.le_refl _) (Nat.succ_le_succ hjk)
  have hDbound : Qle (Qabs (Qsub (t.seq (Rartanh_R ρ j)) (t.seq (Rartanh_R ρ k))))
      ⟨2, Rartanh_R ρ j + 1⟩ := by
    have hanti : Qle (Qbound (Rartanh_R ρ k)) (Qbound (Rartanh_R ρ j)) := by
      show (1 : Int) * ((Rartanh_R ρ j + 1 : Nat) : Int) ≤ 1 * ((Rartanh_R ρ k + 1 : Nat) : Int)
      rw [Int.one_mul, Int.one_mul]; exact_mod_cast (show Rartanh_R ρ j + 1 ≤ Rartanh_R ρ k + 1 by omega)
    have hsum : Qeq (add (Qbound (Rartanh_R ρ j)) (Qbound (Rartanh_R ρ j))) ⟨2, Rartanh_R ρ j + 1⟩ := by
      simp only [Qeq, add, Qbound]; push_cast; ring_uor
    exact Qle_trans (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)) (t.reg _ _)
      (Qle_trans (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))
        (Qadd_le_add (Qle_refl _) hanti) (Qeq_le hsum))
  -- triangle through the midpoint S_{t_{Rk}}(Rj)
  have htri := Qabs_sub_triangle (a := Rartanh_seq t ρ j)
    (b := artSum (t.seq (Rartanh_R ρ k)) (Rartanh_R ρ j)) (c := Rartanh_seq t ρ k)
    (artSum_den_pos (t.den_pos _) _) (artSum_den_pos (t.den_pos _) _) (artSum_den_pos (t.den_pos _) _)
  -- Lipschitz part:  Lip · W ≤ |t_j − t_k|
  have hLipW : Qle (mul (Qabs (Qsub (Rartanh_seq t ρ j)
        (artSum (t.seq (Rartanh_R ρ k)) (Rartanh_R ρ j)))) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
      (Qabs (Qsub (t.seq (Rartanh_R ρ j)) (t.seq (Rartanh_R ρ k)))) := by
    have hLS := artSum_Lip_le (t.den_pos (Rartanh_R ρ j)) (t.den_pos (Rartanh_R ρ k))
      hρd (hb _) (hb _) (Rartanh_R ρ j)
    refine Qle_trans (Qmul_den_pos (Qmul_den_pos (geoEvenSum_den_pos hρd _)
        (Qabs_den_pos (Qsub_den_pos (t.den_pos _) (t.den_pos _)))) hWd)
      (Qmul_le_mul_right hWnn hLS) ?_
    refine Qle_trans (Qmul_den_pos (Qmul_den_pos (geoEvenSum_den_pos hρd _) hWd)
        (Qabs_den_pos (Qsub_den_pos (t.den_pos _) (t.den_pos _))))
      (Qeq_le (Qmul_swap_right _ _ _)) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos (t.den_pos _) (t.den_pos _))))
      (Qmul_le_mul_right (Qabs_num_nonneg _) (geoEven_bound hρ0 hρd _)) (Qeq_le (Qone_mul _))
  -- truncation part:  trunc · W ≤ ρ^{2Rⱼ+3}
  have hTrW : Qle (mul (Qabs (Qsub (artSum (t.seq (Rartanh_R ρ k)) (Rartanh_R ρ j))
        (Rartanh_seq t ρ k))) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (qpow ρ (2 * Rartanh_R ρ j + 3)) := by
    have hTB := artSum_trunc (t.den_pos (Rartanh_R ρ k)) hρ0 hρd (hb _) hWnn
      (a := Rartanh_R ρ j) hRle
    rw [Qabs_Qsub_comm]; exact hTB
  -- combine and cancel W
  refine Qmul_le_cancel_right hWn hWd ?_
  refine Qle_trans (Qmul_den_pos (add_den_pos (Qabs_den_pos (Qsub_den_pos
      (artSum_den_pos (t.den_pos _) _) (artSum_den_pos (t.den_pos _) _)))
      (Qabs_den_pos (Qsub_den_pos (artSum_den_pos (t.den_pos _) _)
        (artSum_den_pos (t.den_pos _) _)))) hWd)
    (Qmul_le_mul_right hWnn htri) ?_
  refine Qle_trans (add_den_pos (Qmul_den_pos (Qabs_den_pos (Qsub_den_pos
      (artSum_den_pos (t.den_pos _) _) (artSum_den_pos (t.den_pos _) _))) hWd)
      (Qmul_den_pos (Qabs_den_pos (Qsub_den_pos (artSum_den_pos (t.den_pos _) _)
        (artSum_den_pos (t.den_pos _) _))) hWd))
    (Qeq_le (Qmul_add_right _ _ _))
    (Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (t.den_pos _) (t.den_pos _)))
      (qpow_den_pos hρd _)) (Qadd_le_add hLipW hTrW)
      (Qle_trans (add_den_pos (Nat.succ_pos _)
          (Nat.lt_of_lt_of_le hρd (Nat.le_add_right _ _)))
        (Qadd_le_add hDbound (qpow_geom_bound hρ0 hρd (Nat.le_of_lt hlt) _))
        (artanh_reindex hρ0 hρd hlt j)))

/-- The artanh diagonal is Bishop-regular. -/
theorem Rartanh_regular (t : Real) {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (hb : ∀ n, Qle (Qabs (t.seq n)) ρ) : IsRegular (Rartanh_seq t ρ) := by
  intro j k
  rcases Nat.le_total j k with h | h
  · exact Qle_trans (Qbound_den_pos j) (Rartanh_diag_le t hρ0 hρd hlt hb h)
      (Qle_self_add (by show (0 : Int) ≤ 1; decide))
  · have hswap := Rartanh_diag_le t hρ0 hρd hlt hb h
    rw [Qabs_Qsub_comm] at hswap
    exact Qle_trans (Qbound_den_pos k) hswap (Qle_add_self (by show (0 : Int) ≤ 1; decide))

/-- **`artanh` on `[−ρ, ρ]`** (`ρ < 1`): the diagonal of the artanh series. -/
def Rartanh (t : Real) (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs (t.seq n)) ρ) : Real :=
  ⟨Rartanh_seq t ρ, Rartanh_regular t hρ0 hρd hlt hb,
    fun j => artSum_den_pos (t.den_pos _) (Rartanh_R ρ j)⟩

-- ===========================================================================
-- The t-map  q ↦ (q−1)/(q+1)  and its cleared difference identity.
-- ===========================================================================

/-- `(x·y)·(z·w) ≈ (x·w)·(y·z)` (abstract). -/
theorem Qmul_rearrange4 (x y z w : Q) :
    Qeq (mul (mul x y) (mul z w)) (mul (mul x w) (mul y z)) := by
  simp only [Qeq, mul]; push_cast; ring_uor

/-- `(x·y)·(z·w) ≈ (x·z)·(y·w)` (abstract). -/
theorem Qmul_rearrange4b (x y z w : Q) :
    Qeq (mul (mul x y) (mul z w)) (mul (mul x z) (mul y w)) := by
  simp only [Qeq, mul]; push_cast; ring_uor

/-- Right distributivity over subtraction: `(p−q)·r ≈ p·r − q·r`. -/
theorem Qmul_sub_right (p q r : Q) : Qeq (mul (Qsub p q) r) (Qsub (mul p r) (mul q r)) := by
  simp only [Qeq, Qsub, mul, add, neg]; push_cast; ring_uor

/-- `−` respects `≈`. -/
theorem Qneg_congr {q q' : Q} (h : Qeq q q') : Qeq (neg q) (neg q') := by
  unfold Qeq neg
  have e1 : (-q.num) * (q'.den : Int) = -(q.num * (q'.den : Int)) := by ring_uor
  have e2 : (-q'.num) * (q.den : Int) = -(q'.num * (q.den : Int)) := by ring_uor
  rw [e1, e2, h]

/-- `Qsub` respects `≈`. -/
theorem Qsub_congr {p p' q q' : Q} (hp : Qeq p p') (hq : Qeq q q') :
    Qeq (Qsub p q) (Qsub p' q') := Qadd_congr hp (Qneg_congr hq)

/-- `(1/a)·a ≈ 1` for `0 < a.num`, `0 < a.den`. -/
theorem Qinv_mul {a : Q} (had : 0 < a.den) (ha : 0 < a.num) : Qeq (mul (Qinv a) a) ⟨1, 1⟩ :=
  Qeq_trans (Qmul_den_pos had (Qinv_den_pos ha)) (mul_comm (Qinv a) a) (Qmul_Qinv ha)

/-- The t-map `q ↦ (q−1)/(q+1)`. -/
def tmap (q : Q) : Q := mul (Qsub q ⟨1, 1⟩) (Qinv (add q ⟨1, 1⟩))

/-- The final ring identity `(a−1)(b+1) − (b−1)(a+1) = 2(a−b)` (abstract). -/
theorem tmap_ring (a b : Q) :
    Qeq (Qsub (mul (Qsub a ⟨1, 1⟩) (add b ⟨1, 1⟩)) (mul (Qsub b ⟨1, 1⟩) (add a ⟨1, 1⟩)))
      (mul ⟨2, 1⟩ (Qsub a b)) := by
  simp only [Qeq, Qsub, mul, add, neg]; push_cast; ring_uor

/-- **The cleared t-map difference**: `(tmap a − tmap b)·(a+1)(b+1) = 2(a−b)`,
    for `a+1, b+1 > 0`. -/
theorem tmap_diff_cleared {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den)
    (ha : 0 < (add a ⟨1, 1⟩).num) (hb : 0 < (add b ⟨1, 1⟩).num) :
    Qeq (mul (Qsub (tmap a) (tmap b)) (mul (add a ⟨1, 1⟩) (add b ⟨1, 1⟩)))
      (mul ⟨2, 1⟩ (Qsub a b)) := by
  have hcad : 0 < (add a ⟨1, 1⟩).den := add_den_pos had Nat.one_pos
  have hcbd : 0 < (add b ⟨1, 1⟩).den := add_den_pos hbd Nat.one_pos
  have hsad : 0 < (Qsub a ⟨1, 1⟩).den := Qsub_den_pos had Nat.one_pos
  have hsbd : 0 < (Qsub b ⟨1, 1⟩).den := Qsub_den_pos hbd Nat.one_pos
  -- tmap a · (a+1)(b+1) ≈ (a−1)(b+1)
  have hA : Qeq (mul (tmap a) (mul (add a ⟨1, 1⟩) (add b ⟨1, 1⟩)))
      (mul (Qsub a ⟨1, 1⟩) (add b ⟨1, 1⟩)) := by
    show Qeq (mul (mul (Qsub a ⟨1, 1⟩) (Qinv (add a ⟨1, 1⟩)))
        (mul (add a ⟨1, 1⟩) (add b ⟨1, 1⟩))) (mul (Qsub a ⟨1, 1⟩) (add b ⟨1, 1⟩))
    refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hsad hcbd) (Qmul_den_pos (Qinv_den_pos ha) hcad))
      (Qmul_rearrange4 _ _ _ _)
      (Qeq_trans (Qmul_den_pos (Qmul_den_pos hsad hcbd) Nat.one_pos)
        (Qmul_congr (Qeq_refl _) (Qinv_mul hcad ha)) (mul_one _))
  have hB : Qeq (mul (tmap b) (mul (add a ⟨1, 1⟩) (add b ⟨1, 1⟩)))
      (mul (Qsub b ⟨1, 1⟩) (add a ⟨1, 1⟩)) := by
    show Qeq (mul (mul (Qsub b ⟨1, 1⟩) (Qinv (add b ⟨1, 1⟩)))
        (mul (add a ⟨1, 1⟩) (add b ⟨1, 1⟩))) (mul (Qsub b ⟨1, 1⟩) (add a ⟨1, 1⟩))
    -- rearrange so 1/(b+1) meets (b+1)
    refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hsbd hcad) (Qmul_den_pos (Qinv_den_pos hb) hcbd))
      (Qmul_rearrange4b _ _ _ _)
      (Qeq_trans (Qmul_den_pos (Qmul_den_pos hsbd hcad) Nat.one_pos)
        (Qmul_congr (Qeq_refl _) (Qinv_mul hcbd hb)) (mul_one _))
  -- combine
  refine Qeq_trans (Qsub_den_pos
      (Qmul_den_pos (Qmul_den_pos hsad (Qinv_den_pos ha)) (Qmul_den_pos hcad hcbd))
      (Qmul_den_pos (Qmul_den_pos hsbd (Qinv_den_pos hb)) (Qmul_den_pos hcad hcbd)))
    (Qmul_sub_right (tmap a) (tmap b) (mul (add a ⟨1, 1⟩) (add b ⟨1, 1⟩))) ?_
  exact Qeq_trans (Qsub_den_pos (Qmul_den_pos hsad hcbd) (Qmul_den_pos hsbd hcad))
    (Qsub_congr hA hB) (tmap_ring a b)

/-- `|a| ≈ a` when `0 ≤ a.num`. -/
theorem Qabs_of_nonneg {a : Q} (h : 0 ≤ a.num) : Qeq (Qabs a) a := by
  unfold Qabs Qeq; rw [Int.natAbs_of_nonneg h]

/-- **The t-map Lipschitz bound**: `|tmap a − tmap b| ≤ (2/(L+1)²)·|a − b|` for `a+1, b+1 ≥ L+1 > 0`. -/
theorem tmap_lipschitz {a b L : Q} (had : 0 < a.den) (hbd : 0 < b.den)
    (ha : 0 < (add a ⟨1, 1⟩).num) (hb : 0 < (add b ⟨1, 1⟩).num) (hLpos : 0 < (add L ⟨1, 1⟩).num)
    (hLad : 0 < (add L ⟨1, 1⟩).den) (hLa : Qle (add L ⟨1, 1⟩) (add a ⟨1, 1⟩))
    (hLb : Qle (add L ⟨1, 1⟩) (add b ⟨1, 1⟩)) :
    Qle (Qabs (Qsub (tmap a) (tmap b)))
      (mul (mul ⟨2, 1⟩ (Qinv (mul (add L ⟨1, 1⟩) (add L ⟨1, 1⟩)))) (Qabs (Qsub a b))) := by
  have hcad : 0 < (add a ⟨1, 1⟩).den := add_den_pos had Nat.one_pos
  have hcbd : 0 < (add b ⟨1, 1⟩).den := add_den_pos hbd Nat.one_pos
  have hPd : 0 < (Qsub (tmap a) (tmap b)).den := Qsub_den_pos
    (Qmul_den_pos (Qsub_den_pos had Nat.one_pos) (Qinv_den_pos ha))
    (Qmul_den_pos (Qsub_den_pos hbd Nat.one_pos) (Qinv_den_pos hb))
  have hcabd : 0 < (mul (add a ⟨1, 1⟩) (add b ⟨1, 1⟩)).den := Qmul_den_pos hcad hcbd
  have hcLLd : 0 < (mul (add L ⟨1, 1⟩) (add L ⟨1, 1⟩)).den := Qmul_den_pos hLad hLad
  have hcabn : 0 < (mul (add a ⟨1, 1⟩) (add b ⟨1, 1⟩)).num := by
    show 0 < (add a ⟨1, 1⟩).num * (add b ⟨1, 1⟩).num; exact Int.mul_pos ha hb
  have hcLLn : 0 < (mul (add L ⟨1, 1⟩) (add L ⟨1, 1⟩)).num := by
    show 0 < (add L ⟨1, 1⟩).num * (add L ⟨1, 1⟩).num; exact Int.mul_pos hLpos hLpos
  -- |P| · (a+1)(b+1) ≈ 2·|a−b|
  have h1 : Qeq (mul (Qabs (Qsub (tmap a) (tmap b))) (mul (add a ⟨1, 1⟩) (add b ⟨1, 1⟩)))
      (mul ⟨2, 1⟩ (Qabs (Qsub a b))) := by
    have hq := Qabs_Qeq (tmap_diff_cleared had hbd ha hb)
    rw [Qabs_mul, Qabs_mul, Qabs_mul] at hq
    -- hq : mul (Qabs P) (mul (Qabs (a+1)) (Qabs (b+1))) ≈ mul (Qabs ⟨2,1⟩) (Qabs (Qsub a b))
    exact Qeq_trans (Qmul_den_pos (Qabs_den_pos hPd) (Qmul_den_pos (Qabs_den_pos hcad)
        (Qabs_den_pos hcbd)))
      (Qmul_congr (Qeq_refl _) (Qmul_congr (Qeq_symm (Qabs_of_nonneg (Int.le_of_lt ha)))
        (Qeq_symm (Qabs_of_nonneg (Int.le_of_lt hb)))))
      (Qeq_trans (Qmul_den_pos (Qabs_den_pos Nat.one_pos) (Qabs_den_pos (Qsub_den_pos had hbd)))
        hq (Qmul_congr (Qabs_of_nonneg (by decide)) (Qeq_refl _)))
  -- |P| · (L+1)² ≤ 2·|a−b|
  have hLL_le : Qle (mul (add L ⟨1, 1⟩) (add L ⟨1, 1⟩)) (mul (add a ⟨1, 1⟩) (add b ⟨1, 1⟩)) :=
    Qmul_le_mul hLad hcad hLad (Int.le_of_lt hLpos) (Int.le_of_lt hLpos) hLa hLb
  have h2 : Qle (mul (Qabs (Qsub (tmap a) (tmap b))) (mul (add L ⟨1, 1⟩) (add L ⟨1, 1⟩)))
      (mul ⟨2, 1⟩ (Qabs (Qsub a b))) :=
    Qle_trans (Qmul_den_pos (Qabs_den_pos hPd) hcabd)
      (Qmul_le_mul_left (Qabs_num_nonneg _) hLL_le) (Qeq_le h1)
  -- cancel (L+1)² to the right via its inverse
  have hcancel : Qeq (Qabs (Qsub (tmap a) (tmap b)))
      (mul (mul (Qabs (Qsub (tmap a) (tmap b))) (mul (add L ⟨1, 1⟩) (add L ⟨1, 1⟩)))
        (Qinv (mul (add L ⟨1, 1⟩) (add L ⟨1, 1⟩)))) := by
    refine Qeq_trans (Qmul_den_pos (Qabs_den_pos hPd) Nat.one_pos) (mul_one _).symm ?_
    refine Qeq_trans (Qmul_den_pos (Qabs_den_pos hPd) (Qmul_den_pos hcLLd (Qinv_den_pos hcLLn)))
      (Qmul_congr (Qeq_refl _) (Qmul_Qinv hcLLn).symm) ?_
    exact (mul_assoc _ _ _).symm
  refine Qle_trans (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hPd) hcLLd) (Qinv_den_pos hcLLn))
    (Qeq_le hcancel)
    (Qle_trans (Qmul_den_pos (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos had hbd)))
      (Qinv_den_pos hcLLn)) (Qmul_le_mul_right (Int.le_of_lt (Qinv_num_pos hcLLd)) h2) (Qeq_le ?_))
  -- (2|a−b|)·(1/(L+1)²) ≈ (2·(1/(L+1)²))·|a−b|
  exact Qmul_swap_right ⟨2, 1⟩ (Qabs (Qsub a b)) (Qinv (mul (add L ⟨1, 1⟩) (add L ⟨1, 1⟩)))

/-- `(q−1)(M+1) ≤ (M−1)(q+1)` when `q ≤ M`. -/
theorem tmap_cross_le {q M : Q} (h : Qle q M) :
    Qle (mul (Qsub q ⟨1, 1⟩) (add M ⟨1, 1⟩)) (mul (Qsub M ⟨1, 1⟩) (add q ⟨1, 1⟩)) := by
  have h' : q.num * (M.den : Int) ≤ M.num * (q.den : Int) := h
  simp only [Qle, mul, Qsub, add, neg]
  push_cast
  have hd : (M.num * 1 + -1 * (M.den : Int)) * (q.num * 1 + 1 * (q.den : Int))
        * ((q.den : Int) * 1 * ((M.den : Int) * 1))
      - (q.num * 1 + -1 * (q.den : Int)) * (M.num * 1 + 1 * (M.den : Int))
        * ((M.den : Int) * 1 * ((q.den : Int) * 1))
      = 2 * (M.num * (q.den : Int) - q.num * (M.den : Int)) * ((q.den : Int) * (M.den : Int)) := by
    ring_uor
  have hnn : 0 ≤ 2 * (M.num * (q.den : Int) - q.num * (M.den : Int)) * ((q.den : Int) * (M.den : Int)) :=
    Int.mul_nonneg (Int.mul_nonneg (by decide) (by omega))
      (Int.mul_nonneg (Int.ofNat_nonneg _) (Int.ofNat_nonneg _))
  omega

/-- `−(q−1)(M+1) ≤ (M−1)(q+1)` when `1 ≤ q·M`. -/
theorem tmap_cross_ge {q M : Q} (h : Qle ⟨1, 1⟩ (mul q M)) :
    Qle (neg (mul (Qsub q ⟨1, 1⟩) (add M ⟨1, 1⟩))) (mul (Qsub M ⟨1, 1⟩) (add q ⟨1, 1⟩)) := by
  have h' : (1 : Int) * (q.den * M.den : Nat) ≤ q.num * M.num * 1 := h
  simp only [Qle, mul, Qsub, add, neg]
  push_cast
  push_cast at h'
  have hd : (M.num * 1 + -1 * (M.den : Int)) * (q.num * 1 + 1 * (q.den : Int))
        * ((q.den : Int) * 1 * ((M.den : Int) * 1))
      - -((q.num * 1 + -1 * (q.den : Int)) * (M.num * 1 + 1 * (M.den : Int)))
        * ((M.den : Int) * 1 * ((q.den : Int) * 1))
      = 2 * (q.num * M.num - (q.den : Int) * (M.den : Int)) * ((q.den : Int) * (M.den : Int)) := by
    ring_uor
  have hnn : 0 ≤ 2 * (q.num * M.num - (q.den : Int) * (M.den : Int)) * ((q.den : Int) * (M.den : Int)) :=
    Int.mul_nonneg (Int.mul_nonneg (by decide) (by omega))
      (Int.mul_nonneg (Int.ofNat_nonneg _) (Int.ofNat_nonneg _))
  omega

/-- `(−a)·b ≈ −(a·b)`. -/
theorem Qmul_neg_left (a b : Q) : Qeq (mul (neg a) b) (neg (mul a b)) := by
  simp only [Qeq, mul, neg]; push_cast; ring_uor

/-- **The t-map range bound**: `|tmap q| ≤ tmap M` for `q ≤ M` and `1 ≤ q·M`
    (i.e. `q ∈ [1/M, M]`), with `q+1, M+1 > 0`. -/
theorem tmap_abs_le {q M : Q} (hqd : 0 < q.den) (hMd : 0 < M.den)
    (hq1 : 0 < (add q ⟨1, 1⟩).num) (hM1 : 0 < (add M ⟨1, 1⟩).num)
    (hqM : Qle q M) (hqMge : Qle ⟨1, 1⟩ (mul q M)) : Qle (Qabs (tmap q)) (tmap M) := by
  have hsqd : 0 < (Qsub q ⟨1, 1⟩).den := Qsub_den_pos hqd Nat.one_pos
  have hsMd : 0 < (Qsub M ⟨1, 1⟩).den := Qsub_den_pos hMd Nat.one_pos
  have hcqd : 0 < (add q ⟨1, 1⟩).den := add_den_pos hqd Nat.one_pos
  have hcMd : 0 < (add M ⟨1, 1⟩).den := add_den_pos hMd Nat.one_pos
  have hDn : 0 < (mul (add q ⟨1, 1⟩) (add M ⟨1, 1⟩)).num := Int.mul_pos hq1 hM1
  have hDd : 0 < (mul (add q ⟨1, 1⟩) (add M ⟨1, 1⟩)).den := Qmul_den_pos hcqd hcMd
  have hL_qM : 0 < (mul (Qsub q ⟨1, 1⟩) (add M ⟨1, 1⟩)).den := Qmul_den_pos hsqd hcMd
  have hL_Mq : 0 < (mul (Qsub M ⟨1, 1⟩) (add q ⟨1, 1⟩)).den := Qmul_den_pos hsMd hcqd
  -- tmap q · (q+1)(M+1) ≈ (q−1)(M+1)
  have hrq : Qeq (mul (tmap q) (mul (add q ⟨1, 1⟩) (add M ⟨1, 1⟩)))
      (mul (Qsub q ⟨1, 1⟩) (add M ⟨1, 1⟩)) := by
    show Qeq (mul (mul (Qsub q ⟨1, 1⟩) (Qinv (add q ⟨1, 1⟩))) (mul (add q ⟨1, 1⟩) (add M ⟨1, 1⟩)))
      (mul (Qsub q ⟨1, 1⟩) (add M ⟨1, 1⟩))
    exact Qeq_trans (Qmul_den_pos hL_qM (Qmul_den_pos (Qinv_den_pos hq1) hcqd))
      (Qmul_rearrange4 _ _ _ _)
      (Qeq_trans (Qmul_den_pos hL_qM Nat.one_pos)
        (Qmul_congr (Qeq_refl _) (Qinv_mul hcqd hq1)) (mul_one _))
  -- tmap M · (q+1)(M+1) ≈ (M−1)(q+1)
  have hrM : Qeq (mul (tmap M) (mul (add q ⟨1, 1⟩) (add M ⟨1, 1⟩)))
      (mul (Qsub M ⟨1, 1⟩) (add q ⟨1, 1⟩)) := by
    show Qeq (mul (mul (Qsub M ⟨1, 1⟩) (Qinv (add M ⟨1, 1⟩))) (mul (add q ⟨1, 1⟩) (add M ⟨1, 1⟩)))
      (mul (Qsub M ⟨1, 1⟩) (add q ⟨1, 1⟩))
    exact Qeq_trans (Qmul_den_pos hL_Mq (Qmul_den_pos (Qinv_den_pos hM1) hcMd))
      (Qmul_rearrange4b _ _ _ _)
      (Qeq_trans (Qmul_den_pos hL_Mq Nat.one_pos)
        (Qmul_congr (Qeq_refl _) (Qinv_mul hcMd hM1)) (mul_one _))
  refine Qabs_le_of_both ?_ ?_
  · exact Qmul_le_cancel_right hDn hDd (Qle_trans hL_qM (Qeq_le hrq)
      (Qle_trans hL_Mq (tmap_cross_le hqM) (Qeq_le (Qeq_symm hrM))))
  · have hrnq : Qeq (mul (neg (tmap q)) (mul (add q ⟨1, 1⟩) (add M ⟨1, 1⟩)))
        (neg (mul (Qsub q ⟨1, 1⟩) (add M ⟨1, 1⟩))) :=
      Qeq_trans (show 0 < (neg (mul (tmap q) (mul (add q ⟨1, 1⟩) (add M ⟨1, 1⟩)))).den from
          Qmul_den_pos (Qmul_den_pos hsqd (Qinv_den_pos hq1)) hDd)
        (Qmul_neg_left (tmap q) (mul (add q ⟨1, 1⟩) (add M ⟨1, 1⟩))) (Qneg_congr hrq)
    exact Qmul_le_cancel_right hDn hDd
      (Qle_trans (show 0 < (neg (mul (Qsub q ⟨1, 1⟩) (add M ⟨1, 1⟩))).den from hL_qM)
        (Qeq_le hrnq)
        (Qle_trans hL_Mq (tmap_cross_ge hqMge) (Qeq_le (Qeq_symm hrM))))

-- ===========================================================================
-- Rlog:  log x = 2·artanh((x−1)/(x+1)) on a positive, [1/M, M]-bounded real.
-- ===========================================================================

/-- The log reindex `g(n) = 2(n+1)`: absorbs the t-map Lipschitz constant `2`. -/
def Rlog_R (n : Nat) : Nat := 2 * (n + 1)

/-- The `n`-th log diagonal approximant: `tmap` of the reindexed `x`-approximant. -/
def Rlog_seq (x : Real) (n : Nat) : Q := tmap (x.seq (Rlog_R n))

/-- The log diagonal is Bishop-regular (the t-map is 2-Lipschitz on `x ≥ 0`). -/
theorem Rlog_regular (x : Real) (hxpos : ∀ n, 0 < (x.seq n).num) : IsRegular (Rlog_seq x) := by
  intro j k
  have had : 0 < (x.seq (Rlog_R j)).den := x.den_pos _
  have hbd : 0 < (x.seq (Rlog_R k)).den := x.den_pos _
  have ha0 : 0 < (x.seq (Rlog_R j)).num := hxpos _
  have hb0 : 0 < (x.seq (Rlog_R k)).num := hxpos _
  have hca : 0 < (add (x.seq (Rlog_R j)) ⟨1, 1⟩).num := by
    have h := Int.ofNat_nonneg (x.seq (Rlog_R j)).den
    show 0 < (x.seq (Rlog_R j)).num * 1 + 1 * ((x.seq (Rlog_R j)).den : Int); omega
  have hcb : 0 < (add (x.seq (Rlog_R k)) ⟨1, 1⟩).num := by
    have h := Int.ofNat_nonneg (x.seq (Rlog_R k)).den
    show 0 < (x.seq (Rlog_R k)).num * 1 + 1 * ((x.seq (Rlog_R k)).den : Int); omega
  have hLa : Qle (add (⟨0, 1⟩ : Q) ⟨1, 1⟩) (add (x.seq (Rlog_R j)) ⟨1, 1⟩) := by
    simp only [Qle, add]; push_cast; omega
  have hLb : Qle (add (⟨0, 1⟩ : Q) ⟨1, 1⟩) (add (x.seq (Rlog_R k)) ⟨1, 1⟩) := by
    simp only [Qle, add]; push_cast; omega
  -- per-leg reindex: 2/(g m + 1) ≤ 1/(m+1)
  have hleg : ∀ m : Nat, Qle (mul (Qbound (Rlog_R m))
      (mul (⟨2, 1⟩ : Q) (Qinv (mul (add (⟨0, 1⟩ : Q) ⟨1, 1⟩) (add (⟨0, 1⟩ : Q) ⟨1, 1⟩)))))
      (Qbound m) := by
    intro m
    show ((1 : Int) * 2) * ((m + 1 : Nat) : Int) ≤ 1 * (((Rlog_R m + 1) * 1 : Nat) : Int)
    unfold Rlog_R; push_cast; omega
  refine Qle_trans (Qmul_den_pos (Qmul_den_pos (by decide)
        (Qinv_den_pos (by decide)))
      (Qabs_den_pos (Qsub_den_pos had hbd)))
    (tmap_lipschitz had hbd hca hcb (by decide) (by decide) hLa hLb)
    (Qle_trans (Qmul_den_pos (Qmul_den_pos (by decide) (Qinv_den_pos (by decide)))
        (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)))
      (Qmul_le_mul_left (by decide) (x.reg (Rlog_R j) (Rlog_R k)))
      (Qle_trans (add_den_pos (Qmul_den_pos (Qbound_den_pos _)
          (Qmul_den_pos (by decide) (Qinv_den_pos (by decide))))
        (Qmul_den_pos (Qbound_den_pos _)
          (Qmul_den_pos (by decide) (Qinv_den_pos (by decide)))))
        (Qeq_le (Qeq_trans (Qmul_den_pos (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))
            (Qmul_den_pos (by decide) (Qinv_den_pos (by decide))))
          (mul_comm _ _) (Qmul_add_right _ _ _)))
        (Qadd_le_add (hleg j) (hleg k))))

/-- `tmap M = (M.num − M.den)/(M.num + M.den)` in lowest-ish terms (the artanh radius `ρ`). -/
theorem tmap_M_eq {M : Q} (hMd : 0 < M.den) (hMn : 0 ≤ M.num) :
    Qeq (tmap M) ⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ := by
  show (tmap M).num * ((M.num.toNat + M.den : Nat) : Int)
      = (M.num - (M.den : Int)) * ((tmap M).den : Int)
  unfold tmap Qinv Qsub
  simp only [Qeq, mul, add, neg]
  push_cast
  rw [Int.toNat_of_nonneg hMn,
    Int.toNat_of_nonneg (show (0 : Int) ≤ M.num * 1 + 1 * (M.den : Int) by omega)]
  ring_uor

/-- **`log` on a positive, `[1/M, M]`-bounded real**: `Rlog x = 2·artanh((x−1)/(x+1))`. -/
def Rlog (x : Real) (M : Q) (hMd : 0 < M.den) (hMge : Qle (⟨1, 1⟩ : Q) M)
    (hxpos : ∀ n, 0 < (x.seq n).num) (hhi : ∀ n, Qle (x.seq n) M)
    (hlo : ∀ n, Qle (⟨1, 1⟩ : Q) (mul (x.seq n) M)) : Real := by
  have hMge' : (1 : Int) * (M.den : Int) ≤ M.num * 1 := hMge
  have hMn : 0 ≤ M.num := by omega
  have hM1 : 0 < (add M ⟨1, 1⟩).num := by
    show 0 < M.num * 1 + 1 * (M.den : Int); omega
  -- the artanh radius ρ = (M−1)/(M+1), in clean form
  have hρ0 : 0 ≤ (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q).num := by
    show 0 ≤ M.num - (M.den : Int); omega
  have hρd : 0 < (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q).den := by
    show 0 < M.num.toNat + M.den; omega
  have hlt : (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q).num.toNat
      < (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q).den := by
    show (M.num - (M.den : Int)).toNat < M.num.toNat + M.den
    have h1 : ((M.num.toNat : Nat) : Int) = M.num := Int.toNat_of_nonneg hMn
    have h2 : ((M.num - (M.den : Int)).toNat : Int) = M.num - (M.den : Int) :=
      Int.toNat_of_nonneg (by omega)
    have : ((M.num - (M.den : Int)).toNat : Int) < ((M.num.toNat + M.den : Nat) : Int) := by
      push_cast [h1, h2]; omega
    exact_mod_cast this
  -- the custom regular sequence t = (x−1)/(x+1)
  have hden : ∀ n, 0 < (Rlog_seq x n).den := by
    intro n
    refine Qmul_den_pos (Qsub_den_pos (x.den_pos _) Nat.one_pos) (Qinv_den_pos ?_)
    have h := Int.ofNat_nonneg (x.seq (Rlog_R n)).den
    have h2 := hxpos (Rlog_R n)
    show 0 < (x.seq (Rlog_R n)).num * 1 + 1 * ((x.seq (Rlog_R n)).den : Int)
    omega
  -- the radius bound on every approximant
  have hb : ∀ n, Qle (Qabs ((⟨Rlog_seq x, Rlog_regular x hxpos, hden⟩ : Real).seq n))
      (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q) := by
    intro n
    have hca : 0 < (add (x.seq (Rlog_R n)) ⟨1, 1⟩).num := by
      have h := Int.ofNat_nonneg (x.seq (Rlog_R n)).den; have := hxpos (Rlog_R n)
      show 0 < (x.seq (Rlog_R n)).num * 1 + 1 * ((x.seq (Rlog_R n)).den : Int); omega
    exact Qle_trans (show 0 < (tmap M).den from
        Qmul_den_pos (Qsub_den_pos hMd Nat.one_pos) (Qinv_den_pos hM1))
      (tmap_abs_le (x.den_pos _) hMd hca hM1 (hhi (Rlog_R n)) (hlo (Rlog_R n)))
      (Qeq_le (tmap_M_eq hMd hMn))
  exact Rmul (ofQ ⟨2, 1⟩ (by decide))
    (Rartanh ⟨Rlog_seq x, Rlog_regular x hxpos, hden⟩ _ hρ0 hρd hlt hb)

end UOR.Bridge.F1Square.Analysis
