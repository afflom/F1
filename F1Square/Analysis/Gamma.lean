/-
F1 square — **the Γ function via Spouge's approximation** (the archimedean `Γ′/Γ` place).

For the Li-coefficient / explicit-formula archimedean term we need `Γ` on the real line `z > 0`. Spouge's
approximation
  `Γ(z+1) = (z+a)^{z+½} · e^{−(z+a)} · (c₀ + Σ_{k=1}^{⌈a⌉−1} cₖ/(z+k) + ε_a(z))`,
  `c₀ = √(2π)`,  `cₖ = (−1)^{k−1}/(k−1)! · (a−k)^{k−½} · e^{a−k}`,
is built entirely from `exp` and `log` of POSITIVE reals — every power, including `√(2π) = exp(½·log 2π)`
and the half-integer `(a−k)^{k−½} = exp((k−½)·log(a−k))`, is `x^y := exp(y·log x)`. So NO dedicated
square-root primitive is required: the single real-power combinator `RrpowPos` is the whole foundation.

This file builds that combinator and its laws; Spouge's coefficients, the approximant, and the error
estimate follow.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.RealPow
import F1Square.Analysis.Log
import F1Square.Analysis.Pi

namespace UOR.Bridge.F1Square.Analysis

/-- **The real power `x^y := exp(y · log x)` for a positive base** `x` (positivity witnessed by `k, hk`).
    The single combinator behind every Spouge power: `√(2π) = RrpowPos 2π _ _ ½`,
    `(z+a)^{z+½} = RrpowPos (z+a) _ _ (z+½)`, `(a−k)^{k−½} = RrpowPos (a−k) _ _ (k−½)`. -/
def RrpowPos (x : Real) (k : Nat) (hk : Qlt (Qbound k) (x.seq k)) (y : Real) : Real :=
  RexpReal (Rmul y (RlogPos x k hk))

/-- **`x^y > 0` for a non-negative exponent** (`exp` of a non-negative real is `≥ 1 > 0`). The
    non-negative-exponent powers in Spouge — `√(2π) = exp(½·log 2π)` and `(z+a)^{z+½}` — are positive. -/
theorem Pos_RrpowPos_of_nonneg (x : Real) (k : Nat) (hk : Qlt (Qbound k) (x.seq k)) (y : Real)
    (hy : Rnonneg (Rmul y (RlogPos x k hk))) : Pos (RrpowPos x k hk y) :=
  Pos_RexpReal hy

/-- **The exponent law `x^{y+y'} = x^y · x^{y'}`**: powers add under multiplication, by `exp(a+b)=exp a·exp b`. -/
theorem RrpowPos_add (x : Real) (k : Nat) (hk : Qlt (Qbound k) (x.seq k)) (y y' : Real) :
    Req (RrpowPos x k hk (Radd y y')) (Rmul (RrpowPos x k hk y) (RrpowPos x k hk y')) := by
  show Req (RexpReal (Rmul (Radd y y') (RlogPos x k hk)))
        (Rmul (RexpReal (Rmul y (RlogPos x k hk))) (RexpReal (Rmul y' (RlogPos x k hk))))
  refine Req_trans (RexpReal_congr (Rmul_distrib_right y y' (RlogPos x k hk))) ?_
  exact RexpReal_add (Rmul y (RlogPos x k hk)) (Rmul y' (RlogPos x k hk))

end UOR.Bridge.F1Square.Analysis
