/-
F1 square — **the Voros off-line branch: modulus growth, constructively** (track 2). The witness term
of an off-line zero has a squared modulus that STRICTLY GROWS with `n` — the constructive seed of
Voros's exponential regime. The step from this growth to a NEGATIVE Li coefficient is the classical
phase/saddle-point analysis, which is not formalized (and is honestly delimited here).

`offLine_left_not_inClosedDisk` (`Reflection.lean`) already proves a left-of-line zero leaves the
closed Cayley disk: its factor `w = 1−1/ρ` has `|w|² > 1`. THIS FILE pushes that one step further into
the dynamics: when `|w|² > 1`, the squared modulus of the witness term `wⁿ` is strictly increasing,
`|wⁿ⁺¹|² − |wⁿ|² = |wⁿ|²·(|w|²−1) > 0` (`offLine_term_grows`), via the Atlas composition norm power
law `cnormSq_npow`. So the off-line term's magnitude blows up monotonically.

WHAT THIS IS AND IS NOT. This is the term-level modulus growth (Voros's exponential seed), proven. It
is NOT the negativity of `λₙ`: that needs the PHASE of `wⁿ` (when `Re(wⁿ) > 1`) and the dominance of
the growing term over the SUM — Voros's saddle-point — which is the irreducible classical content
carried as the `LiBridge.dichotomy` interface (`BLPipeline.lean`). Crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.RHWitness
import F1Square.Analysis.Reflection
import F1Square.Li

namespace UOR.Bridge.F1Square.Analysis

open UOR.Bridge.F1Square.Li (Pos_one)

/-- Powers of a positive real are positive. -/
theorem Pos_Rnpow {x : Real} (hx : Pos x) : ∀ n, Pos (Rnpow x n)
  | 0 => Pos_one
  | (n + 1) => Pos_Rmul hx (Pos_Rnpow hx n)

/-- `x − 1 > 0 ⟹ x > 0` (a real exceeding `1` is positive). -/
theorem Pos_of_Pos_Rsub_one {x : Real} (h : Pos (Rsub x one)) : Pos x :=
  Pos_mono (Rle_of_Rnonneg_Rsub (Rnonneg_of_Pos h)) Pos_one

/-- `x·p − p ≈ p·(x − 1)` (factor a step of the power difference). -/
private theorem step_factor (x p : Real) :
    Req (Rsub (Rmul x p) p) (Rmul p (Rsub x one)) :=
  Req_trans (Rsub_congr (Rmul_comm x p) (Req_symm (Rmul_one p)))
    (Req_symm (Rmul_sub_distrib p x one))

/-- **OFF-LINE ⟹ THE WITNESS TERM'S SQUARED MODULUS STRICTLY GROWS**: if the Cayley factor `w` has
    `|w|² > 1` (its zero off the line, `offLine_left_not_inClosedDisk`), then `|wⁿ|²` is strictly
    increasing in `n` — `|wⁿ⁺¹|² − |wⁿ|² = |wⁿ|²·(|w|²−1) > 0`, via the composition-norm power law
    `cnormSq_npow`. The constructive modulus-growth seed of the Voros off-line branch; the step from
    growth to a negative coefficient (the phase/saddle-point) stays the classical interface. -/
theorem offLine_term_grows {w : Complex} (hw : Pos (Rsub (cnormSq w) one)) (n : Nat) :
    Pos (Rsub (cnormSq (Cnpow w (n + 1))) (cnormSq (Cnpow w n))) := by
  have key : Req (Rsub (cnormSq (Cnpow w (n + 1))) (cnormSq (Cnpow w n)))
      (Rmul (Rnpow (cnormSq w) n) (Rsub (cnormSq w) one)) :=
    Req_trans (Rsub_congr (cnormSq_npow w (n + 1)) (cnormSq_npow w n))
      (step_factor (cnormSq w) (Rnpow (cnormSq w) n))
  exact Pos_congr (Req_symm key)
    (Pos_Rmul (Pos_Rnpow (Pos_of_Pos_Rsub_one hw) n) hw)

end UOR.Bridge.F1Square.Analysis
