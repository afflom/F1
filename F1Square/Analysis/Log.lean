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

end UOR.Bridge.F1Square.Analysis
