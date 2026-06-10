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

end UOR.Bridge.F1Square.Analysis
