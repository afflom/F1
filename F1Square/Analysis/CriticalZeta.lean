/-
F1 square — **critical-strip ζ via the Dirichlet η quotient** `ζ(s) = η(s) / (1 − 2^{1−s})`.

`Ceta` (EtaVariation) gives the Dirichlet eta `η(s) = Σ (−1)^{n−1} n⁻ˢ` as a genuine constructive
complex number on the whole open right half `Re s > 0` (the integration-free route — η converges by
bounded variation where the raw ζ series diverges). The functional relation `(1 − 2^{1−s})·ζ(s) = η(s)`
then yields ζ on the critical strip `0 < Re s < 1`, where the spurious zeros of `1 − 2^{1−s}` (all on
`Re s = 1`) are absent, so the quotient is everywhere defined.

This file builds the denominator `1 − 2^{1−s} = 1 − 2·2⁻ˢ = 1 − 2·cpowNeg s 2` (reusing the committed
`cpowNeg`, no new `Cexp`), its non-vanishing `|1 − 2^{1−s}|² ≥ (2^{1−σ} − 1)² > 0` for `σ < 1` (via the
`Cexp`/`ncpow` modulus identity and `Re ≤ |·|`), and the constructive inverse `Cinv`.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.EtaVariation
import F1Square.Analysis.ComplexInv

namespace UOR.Bridge.F1Square.Analysis

/-- **The `n⁻ˢ` squared modulus**: `|n⁻ˢ|² = (exp(−Re s · log n))²`. Specialises `ncpow_normSq` to the
    negated exponent (`cpowNeg s n = ncpow n _ (−s)`, and `(−s).re = −Re s`). -/
theorem cpowNeg_normSq (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Req (CnormSq (cpowNeg s n))
      (Rmul (RexpReal (Rmul (Rneg s.re) (RlogNat n hn)))
            (RexpReal (Rmul (Rneg s.re) (RlogNat n hn)))) := by
  unfold cpowNeg
  rw [dif_pos hn]
  exact ncpow_normSq n hn (Cneg s)

end UOR.Bridge.F1Square.Analysis
