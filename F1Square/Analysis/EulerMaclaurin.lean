/-
F1 square — **Euler–Maclaurin continuation of `ζ` into the critical strip** (the v0.16.0 "(B) analytic
continuation" deliverable). The Dirichlet series `ζ(s) = Σ n⁻ˢ` converges only for `Re s > 1`
(`ComplexZeta.Czeta`); Euler–Maclaurin summation continues it to `Re s > 1 − 2K` for any fixed `K`:

    ζ(s) = Σ_{n=1}^{N−1} n⁻ˢ + N^{1−s}/(s−1) + ½·N⁻ˢ
            + Σ_{k=1}^{K} (B_{2k}/(2k)!)·(s)_{2k−1}·N^{−s−2k+1}  +  R_K(s, N),

with `(s)_m = s(s+1)…(s+m−1)` the rising factorial and `R_K` the periodic-Bernoulli remainder, which is
`O(N^{−Re s−2K+1}) → 0` as `N → ∞` (fixed `K`). This module builds the **deterministic correction-term
data**: the complex rising factorial `Cpoch` and the exact-rational coefficients `B_{2k}/(2k)!`. The
remainder bound and the `ExactBoundedReal` packaging (the analytic crux) build on top of these.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.Bernoulli
import F1Square.Analysis.ComplexPow

namespace UOR.Bridge.F1Square.Analysis

/-- The complex embedding of a natural number `n` (`= n + 0·i`). -/
def Cnat (n : Nat) : Complex := ⟨ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos, zero⟩

/-- **The complex rising factorial** (Pochhammer symbol) `(s)_m = s·(s+1)·⋯·(s+m−1)` — the polynomial
    factor of the `k`-th Euler–Maclaurin correction term (`m = 2k−1`). -/
def Cpoch (s : Complex) : Nat → Complex
  | 0 => Cone
  | (m + 1) => Cmul (Cpoch s m) (Cadd s (Cnat m))

/-- `(s)_0 = 1`. -/
theorem Cpoch_zero (s : Complex) : Cpoch s 0 = Cone := rfl

/-- `(s)_{m+1} = (s)_m · (s + m)`. -/
theorem Cpoch_succ (s : Complex) (m : Nat) : Cpoch s (m + 1) = Cmul (Cpoch s m) (Cadd s (Cnat m)) := rfl

-- ===========================================================================
-- The exact-rational Euler–Maclaurin coefficients `B_{2k}/(2k)!`.
-- ===========================================================================

/-- **The `k`-th Euler–Maclaurin coefficient** `B_{2k}/(2k)!` (exact rational) — the scalar factor of the
    `k`-th correction term `(B_{2k}/(2k)!)·(s)_{2k−1}·N^{−s−2k+1}`. -/
def emCoeff (k : Nat) : Q := mul (bernoulli (2 * k)) ⟨1, fct (2 * k)⟩

theorem emCoeff_den_pos (k : Nat) : 0 < (emCoeff k).den :=
  Qmul_den_pos (bernoulli_den_pos (2 * k)) (fct_pos (2 * k))

/-- `B₂/2! = 1/12`. -/
theorem emCoeff_one : Qeq (emCoeff 1) ⟨1, 12⟩ := by decide

/-- `B₄/4! = −1/720`. -/
theorem emCoeff_two : Qeq (emCoeff 2) ⟨-1, 720⟩ := by decide

/-- `B₆/6! = 1/30240`. -/
theorem emCoeff_three : Qeq (emCoeff 3) ⟨1, 30240⟩ := by decide

end UOR.Bridge.F1Square.Analysis
