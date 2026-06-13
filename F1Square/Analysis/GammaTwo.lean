/-
F1 square — the **second Stieltjes constant `γ₂`** (the v0.20.0 frontier ingredient that, with
`γ`, `γ₁`, `log 4π`, `ζ(2)`, `ζ(3)`, gives the third Li coefficient `λ₃`).

`γ₂` is the limit of the **defining sequence**

    g₂(N) = S₂(N) − ⅓·(ln N)³,        S₂(N) = Σ_{k=1}^N (ln k)²/k,

i.e. `γ₂ = lim_{N→∞} [ Σ_{k=1}^N (ln k)²/k − ⅓(ln N)³ ] ≈ −0.00969`. Telescoping the `⅓(ln N)³` term,
`g₂(N) = Σ_{k=2}^N e_k` with `e_k = (ln k)²/k − ⅓[(ln k)³ − (ln(k−1))³]`; the leading `(ln k)²/k`
terms cancel against the cubic-log difference, leaving `e_k = O((ln k)²/k²)`, a convergent tail —
so `γ₂ := Rlim g₂Seq` is a genuine constructive real (the regularity is the analytic content
scoped on top of this substrate, mirroring `GammaOne` for `γ₁`).

THIS FILE (brick 1 of γ₂): the real substrate — the term `(ln k)²/k`, the partial sum `S₂(N)`, the
cube `(ln N)³`, and the sequence `g₂(N)`. The monotonicity/regularity layers and the certified
bracket follow (the γ₂ analogue of `GammaOne`'s dyadic-tail stack).

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.GammaOne

namespace UOR.Bridge.F1Square.Analysis

/-- The squared-log harmonic term `(ln k)²/k` (for `k ≥ 1`), as a constructive real. -/
def lnSqOver (k : Nat) (hk : 1 ≤ k) : Real :=
  Rmul (Rmul (logN k hk) (logN k hk)) (ofQ ⟨1, k⟩ (by show 0 < k; omega))

/-- Each term `(ln k)²/k ≥ 0` (`(ln k)² ≥ 0` and `1/k > 0`). -/
theorem lnSqOver_nonneg (k : Nat) (hk : 1 ≤ k) : Rnonneg (lnSqOver k hk) :=
  Rnonneg_Rmul (Rnonneg_Rmul_self (logN k hk))
    (Rnonneg_ofQ (by show 0 < k; omega) (by show (0 : Int) ≤ 1; decide))

/-- The partial sum `S₂(N) = Σ_{k=1}^N (ln k)²/k`. -/
def lnSqSum : Nat → Real
  | 0 => zero
  | (n + 1) => Radd (lnSqSum n) (lnSqOver (n + 1) (by omega))

/-- `S₂(n) ≤ S₂(n+1)` (the new term is `≥ 0`). -/
theorem lnSqSum_step (n : Nat) : Rle (lnSqSum n) (lnSqSum (n + 1)) :=
  Rle_self_Radd_right (lnSqOver_nonneg (n + 1) (by omega))

/-- `S₂` is monotone (non-decreasing). -/
theorem lnSqSum_mono {a b : Nat} (hab : a ≤ b) : Rle (lnSqSum a) (lnSqSum b) := by
  induction hab with
  | refl => exact Rle_refl _
  | step _ ih => exact Rle_trans ih (lnSqSum_step _)

/-- The cube `(ln N)³` as a constructive real. -/
def logCube (N : Nat) (hN : 1 ≤ N) : Real :=
  Rmul (Rmul (logN N hN) (logN N hN)) (logN N hN)

/-- `(ln N)³ ≥ 0` for `N ≥ 1`. -/
theorem logCube_nonneg (N : Nat) (hN : 1 ≤ N) : Rnonneg (logCube N hN) :=
  Rnonneg_Rmul (Rnonneg_Rmul_self (logN N hN)) (Rnonneg_logN N hN)

/-- The **defining sequence** `g₂(j+1) = S₂(j+1) − ⅓·(ln (j+1))³` (indexed from `j = 0`).
    `γ₂ = Rlim g₂Seq`. -/
def g2Seq (j : Nat) : Real :=
  Rsub (lnSqSum (j + 1)) (Rmul (ofQ ⟨1, 3⟩ (by decide)) (logCube (j + 1) (by omega)))

end UOR.Bridge.F1Square.Analysis
