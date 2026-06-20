/-
F1 square — v0.22.0 Track 1, brick (toward item 1, complex Γ): **the general complex power**
`Cpow z w = z^w := exp(w·log z)` (principal-sector base, via the complex logarithm `Clog`).

`ncpow` (`ComplexPow.lean`) gives `n^s` only for a NATURAL base `n ≥ 2` (the ζ Dirichlet terms).
The completed `ξ(s) = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)` and Spouge's `Γ` need a COMPLEX base raised to
a complex power — `(z+a)^{z+1/2}` — which is `exp((z+1/2)·log(z+a))`. This file defines that power on
the principal sector (where `Clog` is anchored) as `Cexp(w·Clog z)` and proves the exponent law
`z^{w₁+w₂} = z^{w₁}·z^{w₂}` (`Cpow_add_exp`, immediate from `Cexp_add` and distributivity). The
base law `(zz')^w = z^w·z'^w` will follow from `Clog` additivity (`Clog_add`/`ClogUpper_add`, item 0).

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/
import F1Square.Analysis.ComplexLog
import F1Square.Analysis.ComplexExpAdd

namespace UOR.Bridge.F1Square.Analysis

/-- `Cadd` respects `≈` (local helper). -/
theorem Cadd_congr_loc {z z' w w' : Complex} (hz : Ceq z z') (hw : Ceq w w') :
    Ceq (Cadd z w) (Cadd z' w') :=
  ⟨Radd_congr hz.1 hw.1, Radd_congr hz.2 hw.2⟩

/-- **The complex power** `z^w = exp(w·log z)` on the principal sector (`Re z > 0`, `|arg| < π/4`),
    via the complex logarithm `Clog`. Witnesses `kn` (for `|z|² > 0`), `kr` (for `Re z > 0`), and the
    `ρ`-bound for the argument ratio are exactly `Clog`'s. -/
def Cpow (z : Complex) (kn : Nat) (hkn : Qlt (Qbound kn) ((cnormSq z).seq kn))
    (kr : Nat) (hkr : Qlt (Qbound kr) (z.re.seq kr))
    (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs ((Rdiv z.im z.re kr hkr).seq n)) ρ) (w : Complex) : Complex :=
  Cexp (Cmul w (Clog z kn hkn kr hkr ρ hρ0 hρd hρlt hb))

/-- **`z^w` real part is `exp(Re(w·log z))·cos(Im(w·log z))`** (definitional, via `Cexp_re`). -/
theorem Cpow_re (z : Complex) (kn : Nat) (hkn : Qlt (Qbound kn) ((cnormSq z).seq kn))
    (kr : Nat) (hkr : Qlt (Qbound kr) (z.re.seq kr))
    (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs ((Rdiv z.im z.re kr hkr).seq n)) ρ) (w : Complex) :
    (Cpow z kn hkn kr hkr ρ hρ0 hρd hρlt hb w).re
      = Rmul (RexpReal (Cmul w (Clog z kn hkn kr hkr ρ hρ0 hρd hρlt hb)).re)
          (Rcos (Cmul w (Clog z kn hkn kr hkr ρ hρ0 hρd hρlt hb)).im) := rfl

/-- **★ exponent law** `z^{w₁+w₂} = z^{w₁}·z^{w₂}` (same principal-sector base). Immediate from
    `Cexp_add` and distributing `(w₁+w₂)·log z = w₁·log z + w₂·log z`. -/
theorem Cpow_add_exp (z : Complex) (kn : Nat) (hkn : Qlt (Qbound kn) ((cnormSq z).seq kn))
    (kr : Nat) (hkr : Qlt (Qbound kr) (z.re.seq kr))
    (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs ((Rdiv z.im z.re kr hkr).seq n)) ρ) (w₁ w₂ : Complex) :
    Ceq (Cpow z kn hkn kr hkr ρ hρ0 hρd hρlt hb (Cadd w₁ w₂))
      (Cmul (Cpow z kn hkn kr hkr ρ hρ0 hρd hρlt hb w₁)
        (Cpow z kn hkn kr hkr ρ hρ0 hρd hρlt hb w₂)) := by
  refine Ceq_trans (Cexp_congr ?_)
    (Cexp_add (Cmul w₁ (Clog z kn hkn kr hkr ρ hρ0 hρd hρlt hb))
      (Cmul w₂ (Clog z kn hkn kr hkr ρ hρ0 hρd hρlt hb)))
  exact Ceq_trans (Cmul_comm (Cadd w₁ w₂) (Clog z kn hkn kr hkr ρ hρ0 hρd hρlt hb))
    (Ceq_trans (Cmul_distrib (Clog z kn hkn kr hkr ρ hρ0 hρd hρlt hb) w₁ w₂)
      (Cadd_congr_loc (Cmul_comm (Clog z kn hkn kr hkr ρ hρ0 hρd hρlt hb) w₁)
        (Cmul_comm (Clog z kn hkn kr hkr ρ hρ0 hρd hρlt hb) w₂)))

end UOR.Bridge.F1Square.Analysis
