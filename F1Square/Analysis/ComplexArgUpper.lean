/-
F1 square — v0.22.0 Track 1, brick (argument axis): **the second-sector / upper-half argument**
`arg(z) = π/2 − arctan(Re z / Im z)` for `Im z > 0` and `|Re z / Im z| ≤ ρ < 1`.

The principal-sector `Carg` (`ComplexArg.lean`) covers `Re z > 0`, `|Im/Re| < 1` (i.e. `|arg| < π/4`).
Past that — toward the upper imaginary axis (`|arg| → π/2`) — the standard reciprocal reduction
`arctan t = π/2 − arctan(1/t)` applies: where `Im z` dominates (`|Re/Im| < 1`), the argument is
`π/2 − arctan(Re/Im)`. This file packages that as `CargUpper`, anchored by `arg(i) = π/2`
(`Carg_I`), using the constructive `π/2 = Rpi_half` (`TanPiQuarter.lean`, where `cos(π/2) = 0`,
`sin(π/2) = 1` are proved).

`CargUpper` is the second-sector value by definition (just as the principal `Carg` is `arctan(Im/Re)`
by definition); its agreement with the principal `Carg` in the overlap, and its additivity, are the
following bricks (they need the real-argument value identity `sin(RarctanR t) = t·cos(RarctanR t)`,
a continuity lift).

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/
import F1Square.Analysis.ComplexArg
import F1Square.Analysis.TanPiQuarter

namespace UOR.Bridge.F1Square.Analysis

/-- **The upper-half-plane argument**: `arg(z) = π/2 − arctan(Re z / Im z)` for `Im z > 0`
    (witness `k`) and `|Re z / Im z| ≤ ρ < 1`. The reciprocal-reduction value where `Im z`
    dominates `Re z` (`|arg| ∈ (π/4, π/2]`), complementing the principal `Carg`. -/
def CargUpper (z : Complex) (k : Nat) (hk : Qlt (Qbound k) (z.im.seq k))
    (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs ((Rdiv z.re z.im k hk).seq n)) ρ) : Real :=
  Rsub Rpi_half (RarctanR (Rdiv z.re z.im k hk) ρ hρ0 hρd hρlt hb)

/-- **`arg(i) = π/2`** — the imaginary unit has argument `π/2`. With `Im i = 1 > 0` and
    `Re i = 0`, the ratio `Re/Im = 0/1` has vanishing numerators, so `arctan(Re/Im) = 0`
    (`RarctanR_of_num_zero`) and `CargUpper i = π/2 − 0 = π/2`. The upper-sector anchor, the
    counterpart of `Carg_ofReal_pos` (`arg(x) = 0` on the positive real axis). -/
theorem Carg_I (k : Nat) (hk : Qlt (Qbound k) (I.im.seq k))
    (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs ((Rdiv I.re I.im k hk).seq n)) ρ) :
    Req (CargUpper I k hk ρ hρ0 hρd hρlt hb) Rpi_half := by
  unfold CargUpper
  have hz : Req (RarctanR (Rdiv I.re I.im k hk) ρ hρ0 hρd hρlt hb) zero := by
    refine RarctanR_of_num_zero (Rdiv I.re I.im k hk) ?_ ρ hρ0 hρd hρlt hb
    intro n
    show ((Rmul zero (Rinv I.im k hk)).seq n).num = 0
    show (mul (zero.seq (Ridx zero (Rinv I.im k hk) n))
        ((Rinv I.im k hk).seq (Ridx zero (Rinv I.im k hk) n))).num = 0
    rw [zero_seq]; simp [mul]
  exact Req_trans (Rsub_congr (Req_refl Rpi_half) hz) (Rsub_zero Rpi_half)

end UOR.Bridge.F1Square.Analysis
