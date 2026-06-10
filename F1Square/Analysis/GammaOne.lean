/-
F1 square — the **first Stieltjes constant `γ₁`** (the v0.16.0 ingredient that, with `γ`, `log 4π`,
and `ζ(2)`, gives the second Li coefficient `λ₂`).

`γ₁` is the limit of the **defining sequence**

    g(N) = S(N) − ½·(ln N)²,        S(N) = Σ_{k=1}^N (ln k)/k,

i.e. `γ₁ = lim_{N→∞} [ Σ_{k=1}^N (ln k)/k − ½(ln N)² ] ≈ −0.07282`. Telescoping `½(ln N)²` term by term,
`g(N) = Σ_{k=2}^N d_k` with `d_k = (ln k)/k − ½[(ln k)² − (ln(k−1))²] ≈ (1 − ln k)/(2k²)`.

This module builds the real substrate — the term `(ln k)/k`, the partial sum `S(N)`, and the sequence
`g(N)`. The two analytic theorems that complete `γ₁` are scoped on top of it:
  • **`g` is eventually decreasing** (`d_k ≤ 0` for `k ≥ 4`, from `(ln x)/x` decreasing on `x ≥ 3`),
    giving the **upper bound `γ₁ ≤ g(M)`** for any `M ≥ 4` — *no tail estimate needed* (the omitted
    `d_k` are `≤ 0`); this is the half that `Pos λ₂` consumes (`γ₁ ≤ −0.0445`).
  • **`g` is regular** (the tail `Σ_{k>M} |d_k| ≤ (ln M + 1)/M` via the integral-comparison telescoping
    of `(ln k)/k²`), so `γ₁ := Rlim g` is a genuine constructive real.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.RealPow

namespace UOR.Bridge.F1Square.Analysis

/-- The harmonic-logarithmic term `(ln k)/k` (for `k ≥ 1`), as a constructive real. -/
def lnOver (k : Nat) (hk : 1 ≤ k) : Real := Rmul (logN k hk) (ofQ ⟨1, k⟩ (by show 0 < k; omega))

/-- Each term `(ln k)/k ≥ 0` (`ln k ≥ 0` for `k ≥ 1`, and `1/k > 0`). -/
theorem lnOver_nonneg (k : Nat) (hk : 1 ≤ k) : Rnonneg (lnOver k hk) :=
  Rnonneg_Rmul (Rnonneg_logN k hk) (Rnonneg_ofQ (by show 0 < k; omega) (by show (0 : Int) ≤ 1; decide))

/-- The partial sum `S(N) = Σ_{k=1}^N (ln k)/k`. -/
def lnSum : Nat → Real
  | 0 => zero
  | (n + 1) => Radd (lnSum n) (lnOver (n + 1) (by omega))

/-- `S(n) ≤ S(n+1)` (the new term is `≥ 0`). -/
theorem lnSum_step (n : Nat) : Rle (lnSum n) (lnSum (n + 1)) :=
  Rle_self_Radd_right (lnOver_nonneg (n + 1) (by omega))

/-- `S` is monotone (non-decreasing). -/
theorem lnSum_mono {a b : Nat} (hab : a ≤ b) : Rle (lnSum a) (lnSum b) := by
  induction hab with
  | refl => exact Rle_refl _
  | step _ ih => exact Rle_trans ih (lnSum_step _)

/-- The **defining sequence** `g(j+1) = S(j+1) − ½·(ln (j+1))²` (indexed from `j = 0`, so no positivity
    hypothesis is needed). `γ₁ = Rlim gSeq`. -/
def gSeq (j : Nat) : Real :=
  Rsub (lnSum (j + 1)) (Rhalf (Rmul (logN (j + 1) (by omega)) (logN (j + 1) (by omega))))

-- ===========================================================================
-- `log k ≥ 1` for `k ≥ 4` — a prerequisite for the `g`-decreasing (upper-bound) half.
-- ===========================================================================

/-- **`log 4 ≥ 1`** — `log 4 = 2·log 2 ≥ 2·½ = 1` (`logN_pow_two` + `logN_2_ge_half`). -/
theorem logN_four_ge_one : Rle (ofQ (⟨1, 1⟩ : Q) (by decide)) (logN 4 (by omega)) := by
  have h4 : Req (logN 4 (by omega)) (Rnsmul 2 (logN 2 (by omega))) :=
    Req_trans (logN_eq_of_eq (show (4 : Nat) = 2 ^ 2 from rfl) (by omega) (by omega))
      (logN_pow_two 2)
  -- ofQ 1 ≈ (½ + (½ + 0)) ≤ (log 2 + (log 2 + 0)) = Rnsmul 2 (log 2)
  have hhalf := logN_2_ge_half
  have hmono : Rle (Radd (ofQ (⟨1, 2⟩ : Q) (by decide)) (Radd (ofQ (⟨1, 2⟩ : Q) (by decide)) zero))
      (Rnsmul 2 (logN 2 (by omega))) :=
    Radd_le_add hhalf (Radd_le_add hhalf (Rle_refl zero))
  have hsum : Req (Radd (ofQ (⟨1, 2⟩ : Q) (by decide)) (Radd (ofQ (⟨1, 2⟩ : Q) (by decide)) zero))
      (ofQ (⟨1, 1⟩ : Q) (by decide)) := by
    refine Req_trans (Radd_congr (Req_refl _) (Radd_zero _)) ?_
    apply Req_of_seq_Qeq; intro n; simp only [Qeq, Radd, ofQ, add]; decide
  exact Rle_trans (Rle_of_Req (Req_symm hsum)) (Rle_trans hmono (Rle_of_Req (Req_symm h4)))

/-- **`log k ≥ 1` for `k ≥ 4`** (`log 4 ≥ 1` and `log` monotone). -/
theorem logN_ge_one {k : Nat} (hk : 4 ≤ k) : Rle (ofQ (⟨1, 1⟩ : Q) (by decide)) (logN k (by omega)) :=
  Rle_trans logN_four_ge_one (logN_mono (by omega) hk)

-- ===========================================================================
-- The consecutive-log difference `δ = log(p+1) − log p` and its UPPER bound `δ ≤ 1/p`.
-- ===========================================================================

/-- **`log(p+1) − log p ≤ 1/p`** (`p ≥ 1`): since `exp(δ) = (p+1)/p ≤ 1 + 1/p ≤ exp(1/p)` and `exp`
    reflects `≤`. This is the `(m−1)·δ_m ≤ 1` fact in the `d_m ≤ 0` proof. -/
theorem deltaLog_upper (p : Nat) (hp : 1 ≤ p) :
    Rle (Rsub (logN (p + 1) (by omega)) (logN p hp)) (ofQ (⟨1, p⟩ : Q) hp) := by
  have hpp : 0 < p := hp
  -- exp(−log p) ≈ 1/p
  have hexpNeg : Req (RexpReal (Rneg (logN p hp))) (ofQ (⟨1, p⟩ : Q) hpp) :=
    RexpReal_neg_eq_recip p hpp (Rexp_logN p hp)
  -- exp(δ) = exp(log(p+1)) · exp(−log p) ≈ (p+1) · (1/p) ≈ (p+1)/p
  have hexpDelta : Req (RexpReal (Rsub (logN (p + 1) (by omega)) (logN p hp)))
      (ofQ (⟨((p : Int) + 1), p⟩ : Q) hpp) := by
    refine Req_trans (RexpReal_add (logN (p + 1) (by omega)) (Rneg (logN p hp))) ?_
    refine Req_trans (Rmul_congr (Rexp_logN (p + 1) (by omega)) hexpNeg) ?_
    refine Req_trans (Rmul_ofQ_ofQ Nat.one_pos hpp) ?_
    exact ofQ_respects (Qmul_den_pos Nat.one_pos hpp) hpp (by simp only [Qeq, mul]; push_cast; ring_uor)
  -- (p+1)/p ≈ 1 + 1/p ≤ exp(1/p)
  have h1add : Req (Radd one (ofQ (⟨1, p⟩ : Q) hpp)) (ofQ (⟨((p : Int) + 1), p⟩ : Q) hpp) := by
    apply Req_of_seq_Qeq; intro n; simp only [Qeq, Radd, one, ofQ, add]; push_cast; ring_uor
  have hge : Rle (ofQ (⟨((p : Int) + 1), p⟩ : Q) hpp) (RexpReal (ofQ (⟨1, p⟩ : Q) hpp)) :=
    Rle_trans (Rle_of_Req (Req_symm h1add))
      (RexpReal_ge_one_add_nonneg (Rnonneg_ofQ hpp (by show (0:Int) ≤ 1; decide)))
  -- exp(δ) ≤ exp(1/p), then reflect
  exact RexpReal_reflects_le (Rnonneg_ofQ hpp (by show (0:Int) ≤ 1; decide))
    (Rle_trans (Rle_of_Req hexpDelta) hge)

-- ===========================================================================
-- The consecutive-log difference LOWER bound `δ ≥ 1/(p+1)` (the sign + tail input for |d_k|).
-- ===========================================================================

/-- `exp(δ) = exp(log(p+1) − log p) ≈ (p+1)/p` (shared by the lower/upper δ bounds). -/
theorem expDelta_eq (p : Nat) (hp : 1 ≤ p) :
    Req (RexpReal (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp)))
      (ofQ (⟨(p : Int) + 1, p⟩ : Q) hp) := by
  have hpp : 0 < p := hp
  have hexpNeg : Req (RexpReal (Rneg (logN p hp))) (ofQ (⟨1, p⟩ : Q) hpp) :=
    RexpReal_neg_eq_recip p hpp (Rexp_logN p hp)
  refine Req_trans (RexpReal_add (logN (p + 1) (Nat.succ_pos p)) (Rneg (logN p hp))) ?_
  refine Req_trans (Rmul_congr (Rexp_logN (p + 1) (Nat.succ_pos p)) hexpNeg) ?_
  refine Req_trans (Rmul_ofQ_ofQ Nat.one_pos hpp) ?_
  exact ofQ_respects (Qmul_den_pos Nat.one_pos hpp) hpp (by simp only [Qeq, mul]; push_cast; ring_uor)

/-- **`expSum(1/(p+1), N) ≤ (p+1)/p`** — the geometric `exp(q) ≤ 1/(1−q)` at `q = 1/(p+1)`
    (`expSum_mul_one_sub_le` + cancel by `(1−q) = p/(p+1)`). -/
theorem expRecip_le (p : Nat) (hp : 1 ≤ p) (N : Nat) :
    Qle (expSum (⟨1, p + 1⟩ : Q) N) (⟨(p : Int) + 1, p⟩ : Q) := by
  have hpp : 0 < p := hp
  have hpInt : (0 : Int) < (p : Int) := by exact_mod_cast hpp
  have hq1 : Qle (⟨1, p + 1⟩ : Q) ⟨1, 1⟩ := by
    show (1 : Int) * 1 ≤ 1 * ((p + 1 : Nat) : Int); push_cast; omega
  have hbase := expSum_mul_one_sub_le (q := ⟨1, p + 1⟩) (by show (0:Int) ≤ 1; decide)
    (Nat.succ_pos p) hq1 N
  refine Qmul_le_cancel_right (c := ⟨(p : Int), p + 1⟩) hpInt (Nat.succ_pos p) ?_
  have hceq : Qeq (mul (⟨(p : Int) + 1, p⟩ : Q) ⟨(p : Int), p + 1⟩) (⟨1, 1⟩ : Q) := by
    simp only [Qeq, mul]; push_cast; ring_uor
  have hseq : Qeq (mul (expSum (⟨1, p + 1⟩ : Q) N) (⟨(p : Int), p + 1⟩ : Q))
      (mul (expSum (⟨1, p + 1⟩ : Q) N) (Qsub (⟨1, 1⟩ : Q) ⟨1, p + 1⟩)) := by
    apply Qmul_congr (Qeq_refl _); simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
  refine Qle_congr_left
    (Qmul_den_pos (expSum_den_pos (Nat.succ_pos p) N) (Qsub_den_pos (by decide) (Nat.succ_pos p)))
    (Qeq_symm hseq) ?_
  exact Qle_trans Nat.one_pos hbase (Qeq_le (Qeq_symm hceq))

/-- **`exp(1/(p+1)) ≤ (p+1)/p`** (the real geometric bound, the diagonal of `expRecip_le`). -/
theorem Rexp_recip_le (p : Nat) (hp : 1 ≤ p) :
    Rle (RexpReal (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p))) (ofQ (⟨(p : Int) + 1, p⟩ : Q) hp) := by
  have hpp : 0 < p := hp
  intro j
  show Qle (expSum (⟨1, p + 1⟩ : Q) (RexpReal_R (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p)) j))
    (add (⟨(p : Int) + 1, p⟩ : Q) ⟨2, j + 1⟩)
  exact Qle_trans hpp (expRecip_le p hp _) (Qle_self_add (by show (0 : Int) ≤ 2; decide))

/-- **`log(p+1) − log p ≥ 1/(p+1)`** (`p ≥ 1`): `exp(1/(p+1)) ≤ (p+1)/p = exp(δ)` + `exp` reflects `≤`.
    With `deltaLog_upper`, `δ ∈ [1/(p+1), 1/p]`. -/
theorem deltaLog_lower (p : Nat) (hp : 1 ≤ p) :
    Rle (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p)) (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp)) :=
  RexpReal_reflects_le (Rnonneg_Rsub_of_Rle (logN_mono hp (Nat.le_succ p)))
    (Rle_trans (Rexp_recip_le p hp) (Rle_of_Req (Req_symm (expDelta_eq p hp))))

-- ===========================================================================
-- Real-algebra helpers for the per-step bound on `d = (ln m)/m − ½((ln m)² − (ln(m−1))²)`.
-- ===========================================================================

/-- The linear identity `(a + b) + (a − b) ≈ a + a`. -/
theorem addsub_linear (a b : Real) : Req (Radd (Radd a b) (Rsub a b)) (Radd a a) :=
  Req_trans (Radd_swap a b a (Rneg b))
    (Req_trans (Radd_congr (Req_refl _) (Radd_neg b)) (Radd_zero _))

/-- The quadratic identity `(a² − b²) + (a − b)² ≈ (a − b)·(a + a)` ( = `2aδ`, `δ = a − b`). -/
theorem sq_diff_identity (a b : Real) :
    Req (Radd (Rsub (Rmul a a) (Rmul b b)) (Rmul (Rsub a b) (Rsub a b)))
        (Rmul (Rsub a b) (Radd a a)) := by
  refine Req_trans (Radd_congr (Req_symm (Rmul_sub_add_self a b)) (Req_refl _)) ?_
  refine Req_trans (Req_symm (Rmul_distrib (Rsub a b) (Radd a b) (Rsub a b))) ?_
  exact Rmul_congr (Req_refl _) (addsub_linear a b)

/-- `x − y ≤ z` from `x ≤ z + y`. -/
theorem Rsub_le_of_le_add {x y z : Real} (h : Rle x (Radd z y)) : Rle (Rsub x y) z :=
  Rle_trans (Rsub_le_sub h (Rle_refl y))
    (Rle_of_Req (Req_trans (Radd_assoc z y (Rneg y))
      (Req_trans (Radd_congr (Req_refl z) (Radd_neg y)) (Radd_zero z))))

/-- **`½a² − ½b² + ½(a−b)² ≈ a·(a−b)`** (`= aδ`). The combined `½`-identity. -/
theorem half_combine (a b : Real) :
    Req (Radd (Rsub (Rhalf (Rmul a a)) (Rhalf (Rmul b b))) (Rhalf (Rmul (Rsub a b) (Rsub a b))))
        (Rmul a (Rsub a b)) := by
  refine Req_trans (Radd_congr (Req_symm (Rhalf_Rsub (Rmul a a) (Rmul b b))) (Req_refl _)) ?_
  refine Req_trans
    (Req_symm (Rhalf_Radd (Rsub (Rmul a a) (Rmul b b)) (Rmul (Rsub a b) (Rsub a b)))) ?_
  refine Req_trans (Rhalf_congr (sq_diff_identity a b)) ?_
  refine Req_trans (Rhalf_congr (Rmul_distrib (Rsub a b) a a)) ?_
  refine Req_trans (Rhalf_Radd (Rmul (Rsub a b) a) (Rmul (Rsub a b) a)) ?_
  exact Req_trans (Rhalf_double (Rmul (Rsub a b) a)) (Rmul_comm (Rsub a b) a)

-- ===========================================================================
-- The per-step `d = g(p+1) − g(p) = (ln(p+1))/(p+1) − ½((ln(p+1))² − (ln p)²)` and its bounds.
-- ===========================================================================

/-- The per-step difference `d_{p+1} = g(p+1) − g(p)` (`p ≥ 1`). -/
def dStep (p : Nat) (hp : 1 ≤ p) : Real :=
  Rsub (lnOver (p + 1) (Nat.succ_pos p))
    (Rsub (Rhalf (Rmul (logN (p + 1) (Nat.succ_pos p)) (logN (p + 1) (Nat.succ_pos p))))
          (Rhalf (Rmul (logN p hp) (logN p hp))))

/-- **`d_{p+1} ≤ ½·δ²`** (`δ = log(p+1) − log p`): the half of the upper |d| bound (with `½δ² ≤
    1/(2p²)`). Since `d = lnOver(p+1) − (½L²−½L'²)` and `lnOver(p+1) = L·(1/(p+1)) ≤ L·δ`
    (`δ ≥ 1/(p+1)`), and `½L²−½L'²+½δ² = L·δ`. -/
theorem dStep_le_half_sq (p : Nat) (hp : 1 ≤ p) :
    Rle (dStep p hp)
      (Rhalf (Rmul (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))
                   (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp)))) := by
  have ha : Rnonneg (logN (p + 1) (Nat.succ_pos p)) := Rnonneg_logN (p + 1) (Nat.succ_pos p)
  -- lnOver(p+1) = L·(1/(p+1)) ≤ L·δ
  have hle : Rle (lnOver (p + 1) (Nat.succ_pos p))
      (Rmul (logN (p + 1) (Nat.succ_pos p))
        (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))) :=
    Rmul_le_Rmul_left ha (deltaLog_lower p hp)
  apply Rsub_le_of_le_add
  refine Rle_trans hle (Rle_of_Req ?_)
  refine Req_trans (Req_symm (half_combine (logN (p + 1) (Nat.succ_pos p)) (logN p hp))) ?_
  exact Radd_comm _ _

/-- **`d_{p+1} ≤ 1/(2p²)`** — the numeric upper bound (`½δ² ≤ ½(1/p)²`, `δ ≤ 1/p`). -/
theorem dStep_le (p : Nat) (hp : 1 ≤ p) :
    Rle (dStep p hp) (ofQ (⟨1, 2 * p * p⟩ : Q) (Nat.mul_pos (Nat.mul_pos (by decide) hp) hp)) := by
  have hδnn : Rnonneg (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp)) :=
    Rnonneg_Rsub_of_Rle (logN_mono hp (Nat.le_succ p))
  have hδle : Rle (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp)) (ofQ (⟨1, p⟩ : Q) hp) :=
    deltaLog_upper p hp
  have hpp : 0 < p := hp
  have hofqnn : Rnonneg (ofQ (⟨1, p⟩ : Q) hp) := Rnonneg_ofQ hpp (by show (0 : Int) ≤ 1; decide)
  have hsq : Rle (Rmul (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))
                       (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp)))
                 (Rmul (ofQ (⟨1, p⟩ : Q) hp) (ofQ (⟨1, p⟩ : Q) hp)) :=
    Rle_trans (Rmul_le_Rmul_left hδnn hδle) (Rmul_le_Rmul_right hofqnn hδle)
  refine Rle_trans (dStep_le_half_sq p hp) ?_
  refine Rle_trans (Rhalf_le_Rhalf hsq) (Rle_of_Req ?_)
  refine Req_trans (Rhalf_congr (Rmul_ofQ_ofQ hpp hpp)) ?_
  apply Req_of_seq_Qeq; intro n; simp only [Rhalf, ofQ, mul, Qeq]; push_cast; ring_uor

/-- **`d_{p+1} ≥ −log(p+1)/(p(p+1))`** — the numeric lower bound. Since `d = lnOver(p+1) −
    (½a²−½b²)` and `½a²−½b² ≤ a·δ` (the `½δ² ≥ 0` slack), `d ≥ lnOver(p+1) − a·δ = −a·(δ − 1/(p+1))`
    and `δ − 1/(p+1) ≤ 1/p − 1/(p+1) = 1/(p(p+1))`. -/
theorem dStep_ge (p : Nat) (hp : 1 ≤ p) :
    Rle (Rneg (Rmul (logN (p + 1) (Nat.succ_pos p)) (ofQ (⟨1, p * (p + 1)⟩ : Q)
        (Nat.mul_pos hp (Nat.succ_pos p)))))
      (dStep p hp) := by
  have hpp : 0 < p := hp
  have ha : Rnonneg (logN (p + 1) (Nat.succ_pos p)) := Rnonneg_logN (p + 1) (Nat.succ_pos p)
  -- abbreviations (defeq to the underlying log terms)
  let a := logN (p + 1) (Nat.succ_pos p)
  let b := logN p hp
  let δ := Rsub a b
  -- h1 : ½a² − ½b² ≤ a·δ  (slack ½δ² ≥ 0, via half_combine)
  have h1 : Rle (Rsub (Rhalf (Rmul a a)) (Rhalf (Rmul b b))) (Rmul a δ) :=
    Rle_trans (Rle_self_Radd_right (Rhalf_nonneg (Rnonneg_Rmul_self δ)))
      (Rle_of_Req (half_combine a b))
  -- step2 : lnOver(p+1) − a·δ ≤ dStep
  have hstep2 : Rle (Rsub (lnOver (p + 1) (Nat.succ_pos p)) (Rmul a δ)) (dStep p hp) :=
    Rsub_le_sub (Rle_refl _) h1
  -- heq3 : lnOver(p+1) − a·δ = −(a·(δ − 1/(p+1)))
  have heq3 : Req (Rsub (lnOver (p + 1) (Nat.succ_pos p)) (Rmul a δ))
      (Rneg (Rmul a (Rsub δ (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p))))) := by
    refine Req_trans (Req_symm (Rmul_sub_distrib a (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p)) δ)) ?_
    refine Req_trans (Rmul_congr (Req_refl a)
      (Req_symm (Rneg_Rsub δ (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p))))) ?_
    exact Rmul_neg_right a (Rsub δ (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p)))
  -- h4 : δ − 1/(p+1) ≤ 1/(p(p+1))
  have h4 : Rle (Rsub δ (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p)))
      (ofQ (⟨1, p * (p + 1)⟩ : Q) (Nat.mul_pos hp (Nat.succ_pos p))) := by
    refine Rle_trans (Rsub_le_sub (deltaLog_upper p hp) (Rle_refl _)) (Rle_of_Req ?_)
    apply Req_of_seq_Qeq; intro n; simp only [Rsub, Radd, Rneg, ofQ, add, neg, Qeq]; push_cast; ring_uor
  -- combine
  refine Rle_trans (Rle_Rneg (Rmul_le_Rmul_left ha h4)) ?_
  exact Rle_trans (Rle_of_Req (Req_symm heq3)) hstep2

-- ===========================================================================
-- The per-step gSeq identity and its two-sided bounds (the dyadic-tail input).
-- ===========================================================================

/-- `(−x) − (−y) ≈ −(x − y)`. -/
theorem Rsub_Rneg_Rneg (x y : Real) : Req (Rsub (Rneg x) (Rneg y)) (Rneg (Rsub x y)) := by
  apply Req_of_seq_Qeq; intro n; simp only [Qeq, Rsub, Radd, Rneg, neg, add]; push_cast; ring_uor

/-- **`gSeq(j+1) − gSeq j ≈ dStep(j+1)`** — the consecutive gSeq difference is the per-step `d`. -/
theorem gSeq_step_eq (j : Nat) :
    Req (Rsub (gSeq (j + 1)) (gSeq j)) (dStep (j + 1) (Nat.succ_pos j)) := by
  have hAC : Req (Rsub (lnSum (j + 2)) (lnSum (j + 1)))
      (lnOver (j + 2) (Nat.succ_pos (j + 1))) := by
    show Req (Rsub (Radd (lnSum (j + 1)) (lnOver (j + 2) (by omega))) (lnSum (j + 1)))
             (lnOver (j + 2) (Nat.succ_pos (j + 1)))
    refine Req_trans (Rsub_congr (Radd_comm (lnSum (j + 1)) (lnOver (j + 2) (by omega)))
      (Req_refl _)) ?_
    refine Req_trans (Radd_assoc (lnOver (j + 2) (by omega)) (lnSum (j + 1))
      (Rneg (lnSum (j + 1)))) ?_
    exact Req_trans (Radd_congr (Req_refl _) (Radd_neg (lnSum (j + 1)))) (Radd_zero _)
  unfold gSeq dStep
  refine Req_trans (Rsub_Radd_Radd (lnSum (j + 2))
    (Rneg (Rhalf (Rmul (logN (j + 2) (by omega)) (logN (j + 2) (by omega)))))
    (lnSum (j + 1))
    (Rneg (Rhalf (Rmul (logN (j + 1) (by omega)) (logN (j + 1) (by omega)))))) ?_
  -- Radd (Rsub A C) (Rsub (Rneg X) (Rneg Y)) ≈ Radd (lnOver(j+2)) (Rneg (Rsub X Y))
  --   = Rsub (lnOver(j+2)) (Rsub X Y)  (defeq)
  exact Radd_congr hAC (Rsub_Rneg_Rneg _ _)

/-- **`(a − b) + (b − c) ≈ a − c`** — the telescoping split for the gap induction. -/
theorem Rsub_split (a b c : Real) : Req (Radd (Rsub a b) (Rsub b c)) (Rsub a c) := by
  refine Req_trans (Req_symm (Radd_assoc (Rsub a b) b (Rneg c))) ?_
  refine Radd_congr ?_ (Req_refl _)
  refine Req_trans (Radd_assoc a (Rneg b) b) ?_
  exact Req_trans (Radd_congr (Req_refl a) (Req_trans (Radd_comm (Rneg b) b) (Radd_neg b)))
    (Radd_zero a)

/-- **Per-step gSeq upper bound** `gSeq(j+1) − gSeq j ≤ 1/(2(j+1)²)`. -/
theorem gSeq_step_le (j : Nat) :
    Rle (Rsub (gSeq (j + 1)) (gSeq j))
      (ofQ (⟨1, 2 * (j + 1) * (j + 1)⟩ : Q)
        (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos j)) (Nat.succ_pos j))) :=
  Rle_trans (Rle_of_Req (gSeq_step_eq j)) (dStep_le (j + 1) (Nat.succ_pos j))

/-- **Per-step gSeq lower bound** `gSeq(j+1) − gSeq j ≥ −log(j+2)/((j+1)(j+2))`. -/
theorem gSeq_step_ge (j : Nat) :
    Rle (Rneg (Rmul (logN (j + 2) (Nat.succ_pos (j + 1)))
        (ofQ (⟨1, (j + 1) * (j + 2)⟩ : Q) (Nat.mul_pos (Nat.succ_pos j) (Nat.succ_pos (j + 1))))))
      (Rsub (gSeq (j + 1)) (gSeq j)) :=
  Rle_trans (dStep_ge (j + 1) (Nat.succ_pos j)) (Rle_of_Req (Req_symm (gSeq_step_eq j)))

-- ===========================================================================
-- The UPPER gap bound `gSeq(N+d) − gSeq N ≤ 1/(2N)` (clean rational telescoping).
-- ===========================================================================

/-- Rational partial sum `Σ_{p≤j} 1/(2p²)` of the per-step upper bounds. -/
def Usum : Nat → Q
  | 0 => ⟨0, 1⟩
  | (j + 1) => add (Usum j) ⟨1, 2 * (j + 1) * (j + 1)⟩

theorem Usum_den_pos : ∀ j, 0 < (Usum j).den
  | 0 => by decide
  | (j + 1) => add_den_pos (Usum_den_pos j)
      (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos j)) (Nat.succ_pos j))

/-- `a + (x − y) ≈ (x + a) − y` on ℚ (general, so `ring_uor` sees only the three atoms). -/
theorem Qadd_Qsub_comm (a x y : Q) : Qeq (add a (Qsub x y)) (Qsub (add x a) y) := by
  simp only [Qsub, add, neg, Qeq]; push_cast; ring_uor

/-- **Upper gap bound, U-form** (`d`-induction): `gSeq(N+d) − gSeq N ≤ Usum(N+d) − Usum N`.
    Each step adds exactly the per-step bound `1/(2(N+d+1)²)` (`gSeq_step_le`); the `Rsub_split`
    telescopes and the combine is a pure rational rearrangement (`Radd_ofQ_ofQ` + `ofQ_congr`). -/
theorem gSeq_diff_le_U (N : Nat) (d : Nat) :
    Rle (Rsub (gSeq (N + d)) (gSeq N))
        (ofQ (Qsub (Usum (N + d)) (Usum N))
          (Qsub_den_pos (Usum_den_pos (N + d)) (Usum_den_pos N))) := by
  induction d with
  | zero =>
      simp only [Nat.add_zero]
      apply Rle_of_Req
      refine Req_trans (Radd_neg (gSeq N)) (Req_symm ?_)
      apply Req_of_seq_Qeq; intro n
      simp only [ofQ, zero, Qsub, add, neg, Qeq]; push_cast; ring_uor
  | succ d ih =>
      exact Rle_trans
        (Rle_of_Req (Req_symm (Rsub_split (gSeq (N + d + 1)) (gSeq (N + d)) (gSeq N))))
        (Rle_trans
          (Radd_le_add (gSeq_step_le (N + d)) ih)
          (Rle_of_Req (Req_trans
            (Radd_ofQ_ofQ _ _)
            (ofQ_congr _ _ (Qadd_Qsub_comm _ (Usum (N + d)) (Usum N))))))

/-- Telescoping sum on ℚ: `(p − q) + (r − p) ≈ r − q`. -/
theorem Qadd_Qsub_telescope (p q r : Q) : Qeq (add (Qsub p q) (Qsub r p)) (Qsub r q) := by
  simp only [Qsub, add, neg, Qeq]; push_cast; ring_uor

/-- **Per-step telescoping inequality** `1/(2(m+1)²) ≤ 1/(2m) − 1/(2(m+1))` (the difference is
    `4(m+1) ≥ 0`). -/
theorem Usum_step_ineq (m : Nat) :
    Qle (⟨1, 2 * (m + 1) * (m + 1)⟩ : Q) (Qsub (⟨1, 2 * m⟩ : Q) ⟨1, 2 * (m + 1)⟩) := by
  simp only [Qle, Qsub, add, neg]
  push_cast
  have key : (1 * (2 * ((m : Int) + 1)) + (-1) * (2 * (m : Int))) * (2 * ((m : Int) + 1) * ((m : Int) + 1))
      - 1 * (2 * (m : Int) * (2 * ((m : Int) + 1))) = 4 * (m : Int) + 4 := by ring_uor
  have hm : (0 : Int) ≤ (m : Int) := Int.ofNat_nonneg m
  omega

/-- **Rational telescoping tail bound** `Usum(N+d) − Usum N ≤ 1/(2N) − 1/(2(N+d))` (for `N ≥ 1`). -/
theorem Usum_tail_le (N : Nat) (hN : 1 ≤ N) (d : Nat) :
    Qle (Qsub (Usum (N + d)) (Usum N)) (Qsub (⟨1, 2 * N⟩ : Q) ⟨1, 2 * (N + d)⟩) := by
  induction d with
  | zero =>
      simp only [Nat.add_zero]
      apply Qeq_le
      simp only [Qsub, add, neg, Qeq]; push_cast; ring_uor
  | succ d ih =>
      -- den-positivity abbreviations
      have hA : 0 < (⟨1, 2 * ((N + d) + 1) * ((N + d) + 1)⟩ : Q).den :=
        Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos (N + d))) (Nat.succ_pos (N + d))
      have hC : 0 < (Qsub (⟨1, 2 * N⟩ : Q) ⟨1, 2 * (N + d)⟩).den :=
        Qsub_den_pos (Nat.mul_pos (by decide) hN) (Nat.mul_pos (by decide) (by omega))
      have hD : 0 < (Qsub (⟨1, 2 * (N + d)⟩ : Q) ⟨1, 2 * (N + d + 1)⟩).den :=
        Qsub_den_pos (Nat.mul_pos (by decide) (by omega)) (Nat.mul_pos (by decide) (by omega))
      have hB : 0 < (Qsub (Usum (N + d)) (Usum N)).den :=
        Qsub_den_pos (Usum_den_pos (N + d)) (Usum_den_pos N)
      -- step: A + (1/(2N) − 1/(2(N+d))) ≤ 1/(2N) − 1/(2(N+d+1))
      have hstep : Qle (add (⟨1, 2 * ((N + d) + 1) * ((N + d) + 1)⟩ : Q)
            (Qsub (⟨1, 2 * N⟩ : Q) ⟨1, 2 * (N + d)⟩))
          (Qsub (⟨1, 2 * N⟩ : Q) ⟨1, 2 * (N + d + 1)⟩) :=
        Qle_trans (add_den_pos hD hC)
          (Qadd_le_add (Usum_step_ineq (N + d)) (Qle_refl _))
          (Qeq_le (Qadd_Qsub_telescope _ _ _))
      -- assemble: LHS ≈ A + (Usum(N+d) − Usum N) ≤ A + (1/(2N) − 1/(2(N+d))) ≤ target
      exact Qle_trans (add_den_pos hA hB)
        (Qeq_le (Qeq_symm (Qadd_Qsub_comm _ (Usum (N + d)) (Usum N))))
        (Qle_trans (add_den_pos hA hC) (Qadd_le_add (Qle_refl _) ih) hstep)

/-- **The UPPER gap bound** `gSeq(N+d) − gSeq N ≤ 1/(2N) − 1/(2(N+d)) ≤ 1/(2N)` (for `N ≥ 1`). -/
theorem gSeq_diff_le (N : Nat) (hN : 1 ≤ N) (d : Nat) :
    Rle (Rsub (gSeq (N + d)) (gSeq N))
        (ofQ (Qsub (⟨1, 2 * N⟩ : Q) ⟨1, 2 * (N + d)⟩)
          (Qsub_den_pos (Nat.mul_pos (by decide) hN) (Nat.mul_pos (by decide) (by omega)))) :=
  Rle_trans (gSeq_diff_le_U N d) (Rle_ofQ_ofQ _ _ (Usum_tail_le N hN d))

end UOR.Bridge.F1Square.Analysis
