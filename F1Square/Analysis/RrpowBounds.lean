/-
F1 square — Track 1, item 0/3 substrate: **`RrpowPos` bounds from the convexity modulus**.

`RrpowPos x k hk y = exp(y · log x)` (`Gamma.lean`). With the now-general convexity bound
`RlogPos x ≤ x − 1` (`RartanhBounds.lean`, transported from the wall-break `Rlog_le_sub_one_real`),
the real power is bounded above by `exp(y·(x−1))` for a non-negative exponent — `Rmul`-monotone in the
exponent times `RexpReal`-monotone. This is the integrand bound the general `t^{σ−1}` Mellin step needs.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.Gamma
import F1Square.Analysis.RartanhBounds

namespace UOR.Bridge.F1Square.Analysis

/-- **`x^y ≤ exp(y·(x−1))`** for a non-negative exponent `y` and a base `x` presented in `[1,B]` at a
    small radius. Directly from `RlogPos_le_sub_one` (`log x ≤ x−1`): `y·log x ≤ y·(x−1)` (`Rmul`-monotone,
    `y ≥ 0`), then `exp`-monotone. The integrand upper bound for the general real Mellin transform. -/
theorem RrpowPos_le_exp_sub_one (x : Real) (k : Nat) (hk : Qlt (Qbound k) (x.seq k)) (y : Real)
    (hy : Rnonneg y)
    (B : Q) (hBd : 0 < B.den) (hBge : Qle (⟨1, 1⟩ : Q) B)
    (hxposB : ∀ n, 0 < (x.seq n).num) (hxhiB : ∀ n, Qle (x.seq n) B)
    (hxloB : ∀ n, Qle (⟨1, 1⟩ : Q) (mul (x.seq n) B))
    (hρB2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩
              ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩))) :
    Rle (RrpowPos x k hk y) (RexpReal (Rmul y (Rsub x one))) :=
  RexpReal_le_of_Rle (Rmul_le_Rmul_left hy
    (RlogPos_le_sub_one x k hk B hBd hBge hxposB hxhiB hxloB hρB2))

end UOR.Bridge.F1Square.Analysis
