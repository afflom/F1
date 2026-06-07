/-
F1 square — the **complex exponential** `Cexp z = exp(re z)·(cos(im z) + i·sin(im z))`, the first
brick of the v0.15.0 complex analytic engine (roadmap stage A).

Built directly on the real transcendentals `RexpReal` (ExpReal), `Rcos`/`Rsin` (CosSin) and the
complex ring `ℂ = ℝ×ℝ` (Complex): each component of `Cexp z` is a genuine constructive real, so `Cexp`
is a clean composition — no new regularity obligation. The argument-0 anchor (`Cexp 0 ≈ 1`), the `nˢ`
map, and `Czeta` build on this in subsequent bricks.

Pure Lean 4, no Mathlib, no `sorry`, choice-free.
-/

import F1Square.Analysis.Complex
import F1Square.Analysis.CosSin
import F1Square.Analysis.ExpReal

namespace UOR.Bridge.F1Square.Analysis

/-- **The complex exponential** `e^z = e^{re z}·(cos(im z) + i·sin(im z))`. Each component is a genuine
    constructive real built from `RexpReal`, `Rcos`, `Rsin`, so this is a clean composition. -/
def Cexp (z : Complex) : Complex :=
  ⟨Rmul (RexpReal z.re) (Rcos z.im), Rmul (RexpReal z.re) (Rsin z.im)⟩

/-- `Re(e^z) = e^{re z}·cos(im z)`. -/
theorem Cexp_re (z : Complex) : (Cexp z).re = Rmul (RexpReal z.re) (Rcos z.im) := rfl

/-- `Im(e^z) = e^{re z}·sin(im z)`. -/
theorem Cexp_im (z : Complex) : (Cexp z).im = Rmul (RexpReal z.re) (Rsin z.im) := rfl

end UOR.Bridge.F1Square.Analysis
