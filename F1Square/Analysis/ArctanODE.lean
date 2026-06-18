/-
F1 square — v0.22.0 Track 1, brick (special-function substrate): **the formal arctan ODE**
`arctan′(t) = 1/(1+t²)` at the level of formal power-series coefficients.

This is the alternating sibling of `dgeom_ode` (ExpLog.lean), which proved that the `(1+w)/(1−w)`
coefficients satisfy `E′ = (2/(1−w²))·E` — the engine behind the *exact rational* artanh exp identity.

The arctan series `A(t) = Σ (−1)ⁿ t^{2n+1}/(2n+1)` has formal derivative `A′(t) = Σ (−1)ⁿ t^{2n} =
1/(1+t²)` (`arctan_fderiv`), and `(1+t²)·A′(t) = 1` (`onePlusSq_geomAlt`). Unlike the geometric
series, the arctan series is *not* rational-summable, so this formal identity does not collapse to an
exact rational value identity (as the artanh one did): the value-level inverse-function fact
`tan(arctan t) = t` — the remaining gap for the argument-addition `arg(zw) = arg z + arg w` (the
imaginary half of `Clog` additivity) — requires a formal-PS → value (fundamental-theorem-of-calculus)
bridge on top of this ODE. This brick is the constructive seed of that bridge.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.ExpLog

namespace UOR.Bridge.F1Square.Analysis

/-- The **arctan coefficient sequence**: coefficient of `tᵏ` in `Σ (−1)ⁿ t^{2n+1}/(2n+1)`. Nonzero only
    at odd degree `k = 2n+1`, where it is `(−1)ⁿ/(2n+1) = (−1)^{k/2}/k`. -/
def arctanCoeff (k : Nat) : Q :=
  if k % 2 = 1 then mul (qpow (⟨-1, 1⟩ : Q) (k / 2)) ⟨1, k⟩ else ⟨0, 1⟩

/-- The **`1/(1+t²)` coefficient sequence**: `Σ (−1)ⁿ t^{2n}`. Nonzero only at even degree `k = 2n`,
    where it is `(−1)ⁿ = (−1)^{k/2}`. -/
def geomAlt (k : Nat) : Q :=
  if k % 2 = 0 then qpow (⟨-1, 1⟩ : Q) (k / 2) else ⟨0, 1⟩

theorem arctanCoeff_den_pos (k : Nat) : 0 < (arctanCoeff k).den := by
  unfold arctanCoeff; split
  · rename_i h
    refine Qmul_den_pos (qpow_den_pos (by decide) (k / 2)) ?_
    show 0 < k; omega
  · exact Nat.one_pos

theorem geomAlt_den_pos (k : Nat) : 0 < (geomAlt k).den := by
  unfold geomAlt; split
  · exact qpow_den_pos (by decide) _
  · exact Nat.one_pos

/-- **The formal arctan ODE**: `fderiv arctanCoeff = geomAlt`, i.e. `A′(t) = 1/(1+t²)`. At even degree
    `k = 2n` the derivative `(k+1)·arctanCoeff(k+1) = (2n+1)·(−1)ⁿ/(2n+1) = (−1)ⁿ` matches `geomAlt(2n)`;
    at odd degree the next arctan coefficient vanishes, matching `geomAlt(odd) = 0`. -/
theorem arctan_fderiv (k : Nat) : Qeq (fderiv arctanCoeff k) (geomAlt k) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · -- k even: k = 2n; k+1 = 2n+1 odd, (2n+1)/2 = n, (2n)/2 = n
    obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    show Qeq (mul ⟨(2 * n + 1 : Int), 1⟩ (arctanCoeff (2 * n + 1))) (geomAlt (2 * n))
    unfold arctanCoeff geomAlt
    rw [if_pos (by omega : (2 * n + 1) % 2 = 1), if_pos (by omega : (2 * n) % 2 = 0),
      show (2 * n + 1) / 2 = n from by omega, show (2 * n) / 2 = n from by omega]
    -- (2n+1)·((−1)ⁿ·(1/(2n+1))) ≈ (−1)ⁿ
    simp only [Qeq, mul]; push_cast; ring_uor
  · -- k odd: k = 2n+1; k+1 = 2n+2 even, arctanCoeff(2n+2) = 0; geomAlt(2n+1) = 0
    obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    show Qeq (mul ⟨(2 * n + 1 + 1 : Int), 1⟩ (arctanCoeff (2 * n + 1 + 1))) (geomAlt (2 * n + 1))
    unfold arctanCoeff geomAlt
    rw [if_neg (by omega : ¬ (2 * n + 1 + 1) % 2 = 1), if_neg (by omega : ¬ (2 * n + 1) % 2 = 0)]
    -- (2n+2)·0 ≈ 0
    show Qeq (mul ⟨(2 * n + 1 + 1 : Int), 1⟩ ⟨0, 1⟩) ⟨0, 1⟩
    simp only [Qeq, mul]; omega

/-- **The `(1+t²)·A′ = 1` annihilation, homogeneous part**: the derivative coefficients `geomAlt`
    satisfy `geomAlt(k+2) + geomAlt(k) ≈ 0` — i.e. multiplication by `1+t²` kills every degree `≥ 2`.
    The parity recurrence `(−1)^{n+1} + (−1)ⁿ = 0` (`qpow_succ` of `⟨−1,1⟩`). -/
theorem geomAlt_recurrence (k : Nat) : Qeq (add (geomAlt (k + 2)) (geomAlt k)) ⟨0, 1⟩ := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    unfold geomAlt
    rw [if_pos (by omega : (2 * n + 2) % 2 = 0), if_pos (by omega : (2 * n) % 2 = 0),
      show (2 * n + 2) / 2 = n + 1 from by omega, show (2 * n) / 2 = n from by omega, qpow_succ]
    -- (−1)ⁿ·(−1) + (−1)ⁿ ≈ 0
    simp only [Qeq, add, mul]; push_cast; ring_uor
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    unfold geomAlt
    rw [if_neg (by omega : ¬ (2 * n + 1 + 2) % 2 = 0), if_neg (by omega : ¬ (2 * n + 1) % 2 = 0)]
    show Qeq (add (⟨0, 1⟩ : Q) ⟨0, 1⟩) ⟨0, 1⟩
    decide

/-- Boundary value: `A′(0) = 1` (`geomAlt 0 = 1`), the normalization `arctan′(0) = 1/(1+0²) = 1`. -/
theorem geomAlt_zero : geomAlt 0 = ⟨1, 1⟩ := by decide

/-- Boundary value: the degree-1 coefficient of `A′` vanishes (`geomAlt 1 = 0`). -/
theorem geomAlt_one : geomAlt 1 = ⟨0, 1⟩ := by decide

end UOR.Bridge.F1Square.Analysis
