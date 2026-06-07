/-
F1 square — the **Euler–Mascheroni constant γ via the convergence-accelerated harmonic route**, whose
approximants have small denominators so that `Pos λ₁` is kernel-certifiable.

Standard definition, realized in *telescoped* form (so no log-additivity lemma is needed):

  γ = Σ_{i≥1} cᵢ,   cᵢ = 1/i − log((i+1)/i) = 1/i − 2·artanh(1/(2i+1)),   0 ≤ cᵢ ≤ 1/(i(i+1)).

Each consecutive-ratio log has a *small* artanh argument `1/(2i+1)` (fast geometric convergence),
unlike `log(n+1)` directly (argument `→ 1`). The series is built as a single rational diagonal (à la
`Rpi`, `gammaSeq`), reusing the artanh partial sum `artSum` (Log.lean); its termwise bracket
`0 ≤ cᵢ ≤ 1/(i(i+1))` rests on the two analytic facts `t ≤ artanh t ≤ t/(1−t²)`, mechanized here as
rational bounds on `artSum`.

This file builds the analytic foundation (the `artSum` bounds). The diagonal, its regularity, the
γ-lower bracket, and `Pos λ₁` follow. Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.Log
import F1Square.Analysis.Euler

namespace UOR.Bridge.F1Square.Analysis

/-! ### Rational lower bound: `artSum t N ≥ t` (the first series term, for `t ≥ 0`) -/

/-- Each artanh term is non-negative for a non-negative base. -/
theorem artTerm_num_nonneg {t : Q} (ht0 : 0 ≤ t.num) (n : Nat) : 0 ≤ (artTerm t n).num := by
  show 0 ≤ (mul (qpow t (2 * n + 1)) ⟨1, 2 * n + 1⟩).num
  simp only [mul]
  have := qpow_nonneg ht0 (2 * n + 1)
  omega

/-- The artanh partial sums are monotone (one step), for a non-negative base. -/
theorem artSum_step {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) (N : Nat) :
    Qle (artSum t N) (artSum t (N + 1)) := by
  show Qle (artSum t N) (add (artSum t N) (artTerm t (N + 1)))
  exact Qle_self_add (artTerm_num_nonneg ht0 (N + 1))

/-- The artanh partial sums are monotone, for a non-negative base. -/
theorem artSum_mono {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) {a b : Nat} (hab : a ≤ b) :
    Qle (artSum t a) (artSum t b) := by
  induction hab with
  | refl => exact Qle_refl _
  | step _ ih => exact Qle_trans (artSum_den_pos htd _) ih (artSum_step ht0 htd _)

/-- The first partial sum is the base: `artSum t 0 ≈ t`. -/
theorem artSum_zero_eq (t : Q) : Qeq (artSum t 0) t := by
  show Qeq (mul (qpow t (2 * 0 + 1)) ⟨1, 2 * 0 + 1⟩) t
  have hq : qpow t 1 = mul t (qpow t 0) := qpow_succ t 0
  show Qeq (mul (qpow t 1) ⟨1, 1⟩) t
  rw [hq]
  simp only [Qeq, mul, qpow]; push_cast; ring_uor

/-- **`artSum t N ≥ t`** for a non-negative base — the artanh lower bound at the rational level. -/
theorem artSum_ge_arg {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) (N : Nat) :
    Qle t (artSum t N) :=
  Qle_trans (artSum_den_pos htd 0) (Qeq_le (Qeq_symm (artSum_zero_eq t)))
    (artSum_mono ht0 htd (Nat.zero_le N))

/-! ### Rational geometric upper bound: `artSum t N · (1−t²) ≤ t` -/

/-- Each artanh term is `≤` the geometric term (since `1/(2n+1) ≤ 1`). -/
theorem artTerm_le_geoTerm {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) (n : Nat) :
    Qle (artTerm t n) (geoTerm t n) := by
  show Qle (mul (qpow t (2 * n + 1)) ⟨1, 2 * n + 1⟩) (qpow t (2 * n + 1))
  have h1 : Qle (⟨1, 2 * n + 1⟩ : Q) ⟨1, 1⟩ := by
    show (1 : Int) * ((1 : Nat) : Int) ≤ 1 * ((2 * n + 1 : Nat) : Int); push_cast; omega
  have h2 : Qle (mul (qpow t (2 * n + 1)) ⟨1, 2 * n + 1⟩) (mul (qpow t (2 * n + 1)) ⟨1, 1⟩) :=
    Qmul_le_mul_left (qpow_nonneg ht0 _) h1
  have h3 : Qeq (mul (qpow t (2 * n + 1)) ⟨1, 1⟩) (qpow t (2 * n + 1)) := by
    simp only [Qeq, mul]; push_cast; ring_uor
  exact Qle_trans (Qmul_den_pos (qpow_den_pos htd _) Nat.one_pos) h2 (Qeq_le h3)

/-- The artanh partial sum is `≤` the geometric partial sum. -/
theorem artSum_le_geoSum {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) :
    ∀ N, Qle (artSum t N) (geoSum t N)
  | 0 => artTerm_le_geoTerm ht0 htd 0
  | (N + 1) => by
      show Qle (add (artSum t N) (artTerm t (N + 1))) (add (geoSum t N) (geoTerm t (N + 1)))
      exact Qadd_le_add (artSum_le_geoSum ht0 htd N) (artTerm_le_geoTerm ht0 htd (N + 1))

/-- Cleared geometric closed bound: `geoSum t N · (1−t²) ≤ t` (drop the non-negative `t^{2N+3}`). -/
theorem geoSum_cleared_le {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) (N : Nat) :
    Qle (mul (geoSum t N) (Qsub ⟨1, 1⟩ (mul t t))) t := by
  have hU := geoU_eq htd N
  exact Qle_trans (add_den_pos (Qmul_den_pos (geoSum_den_pos htd N)
      (Qsub_den_pos Nat.one_pos (Nat.mul_pos htd htd))) (qpow_den_pos htd _))
    (Qle_self_add (qpow_nonneg ht0 _)) (Qeq_le hU)

/-- **The cleared artanh geometric upper bound**: `artSum t N · (1−t²) ≤ t`. -/
theorem artSum_le_geo {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den)
    (hWnn : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul t t)).num) (N : Nat) :
    Qle (mul (artSum t N) (Qsub ⟨1, 1⟩ (mul t t))) t := by
  have h1 : Qle (mul (artSum t N) (Qsub ⟨1, 1⟩ (mul t t)))
      (mul (geoSum t N) (Qsub ⟨1, 1⟩ (mul t t))) :=
    Qmul_le_mul_right hWnn (artSum_le_geoSum ht0 htd N)
  exact Qle_trans (Qmul_den_pos (geoSum_den_pos htd N)
    (Qsub_den_pos Nat.one_pos (Nat.mul_pos htd htd))) h1 (geoSum_cleared_le ht0 htd N)

/-! ### Step 2: the γ-term bracket `0 ≤ 1/(n+1) − 2·artSum(1/(2n+3),T) ≤ 1/((n+1)(n+2))` -/

/-- `2·artSum ≥ 1/(n+2)` (from `artSum ≥` its argument `1/(2n+3)`). -/
theorem two_artSum_ge (n T : Nat) :
    Qle (⟨1, n + 2⟩ : Q) (mul (⟨2, 1⟩ : Q) (artSum ⟨1, 2 * n + 3⟩ T)) := by
  have htd : 0 < (⟨1, 2 * n + 3⟩ : Q).den := by show 0 < 2 * n + 3; omega
  have ht0 : (0 : Int) ≤ (⟨1, 2 * n + 3⟩ : Q).num := by show (0 : Int) ≤ 1; decide
  have h1 : Qle (⟨1, 2 * n + 3⟩ : Q) (artSum ⟨1, 2 * n + 3⟩ T) := artSum_ge_arg ht0 htd T
  have h2 := Qmul_le_mul_left (show (0 : Int) ≤ (⟨2, 1⟩ : Q).num by decide) h1
  refine Qle_trans (Qmul_den_pos (by decide) htd) ?_ h2
  simp only [Qle, mul]; push_cast; omega

/-- `2·artSum ≤ 1/(n+1)` (from the geometric bound `artSum·(1−t²) ≤ t`, then cancel `1−t²`). -/
theorem two_artSum_le (n T : Nat) :
    Qle (mul (⟨2, 1⟩ : Q) (artSum ⟨1, 2 * n + 3⟩ T)) (⟨1, n + 1⟩ : Q) := by
  have htd : 0 < (⟨1, 2 * n + 3⟩ : Q).den := by show 0 < 2 * n + 3; omega
  have ht0 : (0 : Int) ≤ (⟨1, 2 * n + 3⟩ : Q).num := by show (0 : Int) ≤ 1; decide
  have hWn : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)).num := by
    show 0 < (add (⟨1, 1⟩ : Q) (neg (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩))).num
    simp only [add, neg, mul]
    have h9 : ((9 : Nat) : Int) ≤ (((2 * n + 3) * (2 * n + 3) : Nat) : Int) := by
      exact_mod_cast Nat.mul_le_mul (show 3 ≤ 2 * n + 3 by omega) (show 3 ≤ 2 * n + 3 by omega)
    push_cast at h9 ⊢; omega
  have hWd : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)).den :=
    Qsub_den_pos Nat.one_pos (Qmul_den_pos htd htd)
  refine Qmul_le_cancel_right hWn hWd ?_
  have hge := artSum_le_geo (t := ⟨1, 2 * n + 3⟩) ht0 htd (Int.le_of_lt hWn) T
  have hassoc : Qeq
      (mul (mul (⟨2, 1⟩ : Q) (artSum ⟨1, 2 * n + 3⟩ T))
        (Qsub ⟨1, 1⟩ (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)))
      (mul (⟨2, 1⟩ : Q)
        (mul (artSum ⟨1, 2 * n + 3⟩ T) (Qsub ⟨1, 1⟩ (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)))) := by
    simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor
  have hLHS : Qle
      (mul (mul (⟨2, 1⟩ : Q) (artSum ⟨1, 2 * n + 3⟩ T))
        (Qsub ⟨1, 1⟩ (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)))
      (mul (⟨2, 1⟩ : Q) ⟨1, 2 * n + 3⟩) :=
    Qle_trans (Qmul_den_pos (by decide) (Qmul_den_pos (artSum_den_pos htd T) hWd))
      (Qeq_le hassoc) (Qmul_le_mul_left (by decide) hge)
  refine Qle_trans (Qmul_den_pos (by decide) htd) hLHS ?_
  have hmono : (2 * (n : Int) + 3) ≤ 2 * (n + 2) := by omega
  have hnn : (0 : Int) ≤ 2 * ((n : Int) + 1) * (2 * n + 3) :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega)
  have hstep := Int.mul_le_mul_of_nonneg_left hmono hnn
  have hkey : (2 : Int) * ((n : Int) + 1) * ((2 * (n : Int) + 3) * (2 * (n : Int) + 3))
      ≤ ((2 * (n : Int) + 3) * (2 * (n : Int) + 3) - 1) * (2 * (n : Int) + 3) := by
    calc (2 : Int) * ((n : Int) + 1) * ((2 * (n : Int) + 3) * (2 * (n : Int) + 3))
        = (2 * ((n : Int) + 1) * (2 * (n : Int) + 3)) * (2 * (n : Int) + 3) := by ring_uor
      _ ≤ (2 * ((n : Int) + 1) * (2 * (n : Int) + 3)) * (2 * ((n : Int) + 2)) := hstep
      _ = ((2 * (n : Int) + 3) * (2 * (n : Int) + 3) - 1) * (2 * (n : Int) + 3) := by ring_uor
  have hcmp_int : 2 * (((n : Int) + 1) * ((2 * (n : Int) + 3) * (2 * (n : Int) + 3)))
      ≤ ((2 * (n : Int) + 3) * (2 * (n : Int) + 3) + -1) * (2 * (n : Int) + 3) := by
    have hid : ((2 * (n : Int) + 3) * (2 * (n : Int) + 3) + -1) * (2 * (n : Int) + 3)
        - 2 * (((n : Int) + 1) * ((2 * (n : Int) + 3) * (2 * (n : Int) + 3)))
        = 2 * ((n : Int) + 1) * (2 * (n : Int) + 3) := by ring_uor
    have hpos : (0 : Int) ≤ 2 * ((n : Int) + 1) * (2 * (n : Int) + 3) :=
      Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega)
    omega
  show Qle (mul (⟨2, 1⟩ : Q) ⟨1, 2 * n + 3⟩)
    (mul (⟨1, n + 1⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)))
  simp only [Qle, mul, Qsub, add, neg]
  push_cast
  simp only [Int.one_mul]
  exact hcmp_int

/-- The `n`-th γ-term approximant `cApprox(n,T) = 1/(n+1) − 2·artSum(1/(2n+3),T)` (harmonic index
    `i = n+1`). Bracketed in `[0, 1/((n+1)(n+2))]` **uniformly in the artanh depth `T`**. -/
def cApprox (n T : Nat) : Q := Qsub ⟨1, n + 1⟩ (mul ⟨2, 1⟩ (artSum ⟨1, 2 * n + 3⟩ T))

theorem cApprox_den_pos (n T : Nat) : 0 < (cApprox n T).den :=
  Qsub_den_pos (by show 0 < n + 1; omega)
    (Qmul_den_pos (by decide) (artSum_den_pos (by show 0 < 2 * n + 3; omega) T))

theorem cApprox_num_nonneg (n T : Nat) : 0 ≤ (cApprox n T).num :=
  num_nonneg_of_Qzero_le (Qsub_nonneg_of_le (two_artSum_le n T))

theorem cApprox_ub (n T : Nat) : Qle (cApprox n T) (⟨1, (n + 1) * (n + 2)⟩ : Q) := by
  have hneg : Qle (neg (mul (⟨2, 1⟩ : Q) (artSum ⟨1, 2 * n + 3⟩ T))) (neg ⟨1, n + 2⟩) :=
    Qneg_le_neg (two_artSum_ge n T)
  have hstep : Qle (cApprox n T) (Qsub (⟨1, n + 1⟩ : Q) ⟨1, n + 2⟩) := by
    show Qle (add (⟨1, n + 1⟩ : Q) (neg (mul ⟨2, 1⟩ (artSum ⟨1, 2 * n + 3⟩ T))))
      (add ⟨1, n + 1⟩ (neg ⟨1, n + 2⟩))
    exact Qadd_le_add (Qle_refl _) hneg
  have heq : Qeq (Qsub (⟨1, n + 1⟩ : Q) ⟨1, n + 2⟩) (⟨1, (n + 1) * (n + 2)⟩ : Q) := by
    simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
  exact Qle_trans (Qsub_den_pos (by show 0 < n + 1; omega) (by show 0 < n + 2; omega)) hstep
    (Qeq_le heq)

/-! ### Step 3a: the plain partial sum and its telescoping truncation tail -/

/-- The plain partial sum `Σ_{i=0}^{M-1} f i`. -/
def Ssum (f : Nat → Q) : Nat → Q
  | 0 => ⟨0, 1⟩
  | (M + 1) => add (Ssum f M) (f M)

theorem Ssum_den_pos {f : Nat → Q} (hf : ∀ i, 0 < (f i).den) : ∀ M, 0 < (Ssum f M).den
  | 0 => Nat.one_pos
  | (M + 1) => add_den_pos (Ssum_den_pos hf M) (hf M)

/-- **Telescoping truncation tail**: for `0 ≤ f i ≤ 1/((i+1)(i+2))`, the gap from `Mj` to `Mk`
    (`Mj ≤ Mk`) is `≤ 1/(Mj+1) − 1/(Mk+1)`. -/
theorem Ssum_tail_le {f : Nat → Q} (hf : ∀ i, 0 < (f i).den)
    (hfb : ∀ i, Qle (f i) (⟨1, (i + 1) * (i + 2)⟩ : Q)) (Mj : Nat) :
    ∀ {Mk}, Mj ≤ Mk →
      Qle (Qsub (Ssum f Mk) (Ssum f Mj)) (Qsub (⟨1, Mj + 1⟩ : Q) ⟨1, Mk + 1⟩) := by
  intro Mk hjk
  induction hjk with
  | refl =>
    have h0 : (Qsub (Ssum f Mj) (Ssum f Mj)).num = 0 := Qsub_self_num _
    have h1 : (Qsub (⟨1, Mj + 1⟩ : Q) ⟨1, Mj + 1⟩).num = 0 := Qsub_self_num _
    show Qle (Qsub (Ssum f Mj) (Ssum f Mj)) (Qsub (⟨1, Mj + 1⟩ : Q) ⟨1, Mj + 1⟩)
    unfold Qle; rw [h0, h1]; omega
  | @step K hK ih =>
    have hKpos : 0 < (K + 1) * (K + 2) := Nat.mul_pos (by omega) (by omega)
    have hrew : Qeq (Qsub (Ssum f (K + 1)) (Ssum f Mj))
        (add (Qsub (Ssum f K) (Ssum f Mj)) (f K)) :=
      Qsub_add_right (Ssum f K) (f K) (Ssum f Mj)
    have hstep : Qle (add (Qsub (Ssum f K) (Ssum f Mj)) (f K))
        (add (Qsub (⟨1, Mj + 1⟩ : Q) ⟨1, K + 1⟩) ⟨1, (K + 1) * (K + 2)⟩) :=
      Qadd_le_add ih (hfb K)
    have heq : Qeq (add (Qsub (⟨1, Mj + 1⟩ : Q) ⟨1, K + 1⟩) ⟨1, (K + 1) * (K + 2)⟩)
        (Qsub (⟨1, Mj + 1⟩ : Q) ⟨1, K + 2⟩) := by
      simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
    refine Qle_trans (add_den_pos (Qsub_den_pos (by show 0 < Mj + 1; omega) (by show 0 < K + 1; omega))
        hKpos)
      (Qle_congr_left (add_den_pos (Qsub_den_pos (Ssum_den_pos hf K) (Ssum_den_pos hf Mj)) (hf K))
        (Qeq_symm hrew) hstep) (Qeq_le heq)

/-! ### Step 3b: the per-term ζ-depth difference bound -/

/-- Powers are monotone in the base. -/
theorem npow_base_mono {a b : Nat} (h : a ≤ b) : ∀ m, npow a m ≤ npow b m
  | 0 => Nat.le_refl 1
  | (m + 1) => by
      show a * npow a m ≤ b * npow b m
      exact Nat.mul_le_mul h (npow_base_mono h m)

/-- `i^{a+b} = i^a · i^b`. -/
theorem npow_add (i a : Nat) : ∀ b, npow i (a + b) = npow i a * npow i b
  | 0 => by show npow i a = npow i a * 1; rw [Nat.mul_one]
  | (b + 1) => by
      show npow i (a + b + 1) = npow i a * npow i (b + 1)
      rw [npow_succ, npow_add i a b, npow_succ]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- `(1/d)^m = 1/dᵐ`. -/
theorem qpow_one_den (d : Nat) : ∀ m, qpow (⟨1, d⟩ : Q) m = ⟨1, npow d m⟩
  | 0 => rfl
  | (m + 1) => by rw [qpow_succ, qpow_one_den d m, npow_succ]; rfl

/-- **Per-term depth bound**: deepening the artanh approximant from `Tj` to `Tk` moves the γ-term by
    at most `1/3^{2Tj+1}` (uniformly in `n`). -/
theorem cApprox_depth_diff (n : Nat) {Tj Tk : Nat} (hT : Tj ≤ Tk) :
    Qle (Qabs (Qsub (cApprox n Tj) (cApprox n Tk))) (⟨1, npow 3 (2 * Tj + 1)⟩ : Q) := by
  have htd : 0 < (⟨1, 2 * n + 3⟩ : Q).den := by show 0 < 2 * n + 3; omega
  have ht0 : (0 : Int) ≤ (⟨1, 2 * n + 3⟩ : Q).num := by show (0 : Int) ≤ 1; decide
  have hWn : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)).num := by
    show 0 < (add (⟨1, 1⟩ : Q) (neg (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩))).num
    simp only [add, neg, mul]
    have h9 : ((9 : Nat) : Int) ≤ (((2 * n + 3) * (2 * n + 3) : Nat) : Int) := by
      exact_mod_cast Nat.mul_le_mul (show 3 ≤ 2 * n + 3 by omega) (show 3 ≤ 2 * n + 3 by omega)
    push_cast at h9 ⊢; omega
  have hWd : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)).den :=
    Qsub_den_pos Nat.one_pos (Qmul_den_pos htd htd)
  -- the ⟨1,n+1⟩ cancels: cApprox-diff = 2·(artSum Tk − artSum Tj)
  have heq : Qeq (Qsub (cApprox n Tj) (cApprox n Tk))
      (mul ⟨2, 1⟩ (Qsub (artSum ⟨1, 2 * n + 3⟩ Tk) (artSum ⟨1, 2 * n + 3⟩ Tj))) := by
    simp only [cApprox, Qeq, Qsub, mul, add, neg]; push_cast
    generalize (artSum ⟨1, 2 * n + 3⟩ Tj).num = aj; generalize ((artSum ⟨1, 2 * n + 3⟩ Tj).den : Int) = bj
    generalize (artSum ⟨1, 2 * n + 3⟩ Tk).num = ak; generalize ((artSum ⟨1, 2 * n + 3⟩ Tk).den : Int) = bk
    ring_uor
  have habs : Qeq (Qabs (Qsub (cApprox n Tj) (cApprox n Tk)))
      (mul ⟨2, 1⟩ (Qabs (Qsub (artSum ⟨1, 2 * n + 3⟩ Tk) (artSum ⟨1, 2 * n + 3⟩ Tj)))) := by
    have h := Qabs_Qeq heq; rw [Qabs_mul] at h; exact h
  refine Qle_congr_left (Qmul_den_pos (by decide) (Qabs_den_pos (Qsub_den_pos
      (artSum_den_pos htd Tk) (artSum_den_pos htd Tj)))) (Qeq_symm habs) ?_
  -- cancel W
  refine Qmul_le_cancel_right hWn hWd ?_
  have htrunc := artSum_trunc (t := ⟨1, 2 * n + 3⟩) (ρ := ⟨1, 2 * n + 3⟩) htd ht0 htd
    (Qle_refl _) (Int.le_of_lt hWn) hT
  -- htrunc : |artSum Tk − artSum Tj|·W ≤ qpow ⟨1,2n+3⟩ (2Tj+3)
  have hassoc : Qeq
      (mul (mul (⟨2, 1⟩ : Q) (Qabs (Qsub (artSum ⟨1, 2 * n + 3⟩ Tk) (artSum ⟨1, 2 * n + 3⟩ Tj))))
        (Qsub ⟨1, 1⟩ (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)))
      (mul (⟨2, 1⟩ : Q)
        (mul (Qabs (Qsub (artSum ⟨1, 2 * n + 3⟩ Tk) (artSum ⟨1, 2 * n + 3⟩ Tj)))
          (Qsub ⟨1, 1⟩ (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)))) := by
    simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor
  have hLHS : Qle
      (mul (mul (⟨2, 1⟩ : Q) (Qabs (Qsub (artSum ⟨1, 2 * n + 3⟩ Tk) (artSum ⟨1, 2 * n + 3⟩ Tj))))
        (Qsub ⟨1, 1⟩ (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)))
      (mul (⟨2, 1⟩ : Q) (qpow ⟨1, 2 * n + 3⟩ (2 * Tj + 3))) :=
    Qle_trans (Qmul_den_pos (by decide) (Qmul_den_pos (Qabs_den_pos (Qsub_den_pos
        (artSum_den_pos htd Tk) (artSum_den_pos htd Tj))) hWd)) (Qeq_le hassoc)
      (Qmul_le_mul_left (by decide) htrunc)
  refine Qle_trans (Qmul_den_pos (by decide) (qpow_den_pos htd (2 * Tj + 3))) hLHS ?_
  -- final power comparison: 2·(1/(2n+3)^{2Tj+3}) ≤ (1/3^{2Tj+1})·W
  rw [qpow_one_den, show 2 * Tj + 3 = (2 * Tj + 1) + 2 from by omega, npow_add, npow_two]
  show Qle (mul (⟨2, 1⟩ : Q) ⟨1, npow (2 * n + 3) (2 * Tj + 1) * ((2 * n + 3) * (2 * n + 3))⟩)
    (mul (⟨1, npow 3 (2 * Tj + 1)⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)))
  have hmonoI : ((npow 3 (2 * Tj + 1) : Nat) : Int) ≤ ((npow (2 * n + 3) (2 * Tj + 1) : Nat) : Int) := by
    exact_mod_cast npow_base_mono (show 3 ≤ 2 * n + 3 by omega) (2 * Tj + 1)
  have hAnn : (0 : Int) ≤ ((npow 3 (2 * Tj + 1) : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have hBnn : (0 : Int) ≤ ((npow (2 * n + 3) (2 * Tj + 1) : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have hm8 : (8 : Int) ≤ (2 * (n : Int) + 3) * (2 * (n : Int) + 3) + -1 := by
    have h := Int.mul_le_mul (show (3 : Int) ≤ 2 * (n : Int) + 3 by omega)
      (show (3 : Int) ≤ 2 * (n : Int) + 3 by omega) (by omega) (by omega)
    omega
  have hmm : (0 : Int) ≤ (2 * (n : Int) + 3) * (2 * (n : Int) + 3) :=
    Int.mul_nonneg (by omega) (by omega)
  have hge : 2 * ((npow 3 (2 * Tj + 1) : Nat) : Int)
      ≤ ((2 * (n : Int) + 3) * (2 * (n : Int) + 3) + -1) * ((npow (2 * n + 3) (2 * Tj + 1) : Nat) : Int) :=
    calc 2 * ((npow 3 (2 * Tj + 1) : Nat) : Int)
        ≤ 8 * ((npow 3 (2 * Tj + 1) : Nat) : Int) := Int.mul_le_mul_of_nonneg_right (by omega) hAnn
      _ ≤ 8 * ((npow (2 * n + 3) (2 * Tj + 1) : Nat) : Int) :=
          Int.mul_le_mul_of_nonneg_left hmonoI (by omega)
      _ ≤ ((2 * (n : Int) + 3) * (2 * (n : Int) + 3) + -1) * ((npow (2 * n + 3) (2 * Tj + 1) : Nat) : Int) :=
          Int.mul_le_mul_of_nonneg_right hm8 hBnn
  simp only [Qle, mul, Qsub, add, neg]
  push_cast
  simp only [Int.one_mul]
  calc 2 * (((npow 3 (2 * Tj + 1) : Nat) : Int)
          * ((2 * (n : Int) + 3) * (2 * (n : Int) + 3)))
      = (2 * ((npow 3 (2 * Tj + 1) : Nat) : Int))
          * ((2 * (n : Int) + 3) * (2 * (n : Int) + 3)) := by ring_uor
    _ ≤ (((2 * (n : Int) + 3) * (2 * (n : Int) + 3) + -1) * ((npow (2 * n + 3) (2 * Tj + 1) : Nat) : Int))
          * ((2 * (n : Int) + 3) * (2 * (n : Int) + 3)) := Int.mul_le_mul_of_nonneg_right hge hmm
    _ = ((2 * (n : Int) + 3) * (2 * (n : Int) + 3) + -1)
          * (((npow (2 * n + 3) (2 * Tj + 1) : Nat) : Int) * ((2 * (n : Int) + 3) * (2 * (n : Int) + 3))) := by
        ring_uor

/-! ### Step 3c: the γ diagonal and its regularity -/

/-- **Term-wise difference of two plain sums**: if each term differs by `≤ 1/e`, the length-`M` sums
    differ by `≤ M/e`. -/
theorem Ssum_depth_diff {f g : Nat → Q} (e : Nat) (he : 0 < e) (hfd : ∀ i, 0 < (f i).den)
    (hgd : ∀ i, 0 < (g i).den) (hdiff : ∀ i, Qle (Qabs (Qsub (f i) (g i))) (⟨1, e⟩ : Q)) :
    ∀ M, Qle (Qabs (Qsub (Ssum f M) (Ssum g M))) (⟨(M : Int), e⟩ : Q)
  | 0 => by
      show Qle (Qabs (Qsub (⟨0, 1⟩ : Q) ⟨0, 1⟩)) (⟨(0 : Int), e⟩ : Q)
      have hx : (Qabs (Qsub (⟨0, 1⟩ : Q) ⟨0, 1⟩)).num = 0 := by decide
      unfold Qle; rw [hx]; simp
  | (M + 1) => by
      show Qle (Qabs (Qsub (add (Ssum f M) (f M)) (add (Ssum g M) (g M))))
        (⟨((M + 1 : Nat) : Int), e⟩ : Q)
      have hreg : Qeq (Qsub (add (Ssum f M) (f M)) (add (Ssum g M) (g M)))
          (add (Qsub (Ssum f M) (Ssum g M)) (Qsub (f M) (g M))) := by
        simp only [Qeq, Qsub, add, neg]; push_cast
        generalize (Ssum f M).num = a1; generalize ((Ssum f M).den : Int) = b1
        generalize (f M).num = a2; generalize ((f M).den : Int) = b2
        generalize (Ssum g M).num = a3; generalize ((Ssum g M).den : Int) = b3
        generalize (g M).num = a4; generalize ((g M).den : Int) = b4
        ring_uor
      have hsum : Qeq (add (⟨(M : Int), e⟩ : Q) ⟨1, e⟩) (⟨((M + 1 : Nat) : Int), e⟩ : Q) := by
        simp only [Qeq, add]; push_cast
        generalize ((e : Nat) : Int) = E; generalize ((M : Nat) : Int) = Mc
        ring_uor
      have key : Qle (Qabs (Qsub (add (Ssum f M) (f M)) (add (Ssum g M) (g M))))
          (add (Qabs (Qsub (Ssum f M) (Ssum g M))) (Qabs (Qsub (f M) (g M)))) :=
        Qle_congr_left (Qabs_den_pos (add_den_pos
          (Qsub_den_pos (Ssum_den_pos hfd M) (Ssum_den_pos hgd M)) (Qsub_den_pos (hfd M) (hgd M))))
          (Qeq_symm (Qabs_Qeq hreg)) (Qabs_add_le _ _)
      refine Qle_trans (add_den_pos
          (Qabs_den_pos (Qsub_den_pos (Ssum_den_pos hfd M) (Ssum_den_pos hgd M)))
          (Qabs_den_pos (Qsub_den_pos (hfd M) (hgd M)))) key ?_
      exact Qle_trans (add_den_pos (show 0 < (⟨(M : Int), e⟩ : Q).den from he)
          (show 0 < (⟨1, e⟩ : Q).den from he))
        (Qadd_le_add (Ssum_depth_diff e he hfd hgd hdiff M) (hdiff M)) (Qeq_le hsum)

end UOR.Bridge.F1Square.Analysis
