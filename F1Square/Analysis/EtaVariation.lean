/-
F1 square — the **`n⁻ˢ` multiplicative recurrence** `(n+1)⁻ˢ = n⁻ˢ · e^{−s·δ_n}` (`δ_n = log(n+1) − log n`),
the engine of the η-series **variation bound** `Σ |n⁻ˢ − (n+1)⁻ˢ| < ∞` (`Re s > 0`) — the integration-free
route to `ζ` on the critical strip. The recurrence is the direct consequence of the complex exponential
law `Cexp_add`: `n⁻ˢ = e^{−s·log n}` (`cpowNeg`), and `log(n+1) = log n + δ_n`, so
`e^{−s·log(n+1)} = e^{−s·log n}·e^{−s·δ_n}`.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.EulerMaclaurin
import F1Square.Analysis.ComplexExpAdd

namespace UOR.Bridge.F1Square.Analysis

/-- **The consecutive-log gap** `δ_n = log(n+1) − log n` (for `n ≥ 2`), as a constructive real. -/
def deltaLogNat (n : Nat) (hn : 2 ≤ n) : Real :=
  Rsub (RlogNat (n + 1) (by omega)) (RlogNat n hn)

/-- **The `n⁻ˢ` multiplicative recurrence** `(n+1)⁻ˢ ≈ n⁻ˢ · e^{−s·δ_n}` (for `n ≥ 2`). Both sides are
    `Cexp` of an argument; `log(n+1) = log n + δ_n` (`Radd_Rsub_self`) lifts through `Rmul_distrib` to the
    complex argument additivity, and `Cexp_add`/`Cexp_congr` close it. -/
theorem cpowNeg_succ (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Ceq (cpowNeg s (n + 1))
      (Cmul (cpowNeg s n)
        (Cexp ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩)) := by
  have h1 : 2 ≤ n + 1 := by omega
  unfold cpowNeg
  rw [dif_pos h1, dif_pos hn]
  -- both `ncpow` are `Cexp` of the argument `−s·log`; reduce to `Cexp_add` via argument additivity
  refine Ceq_trans (Cexp_congr (z := ⟨Rmul (Rneg s.re) (RlogNat (n + 1) h1), Rmul (Rneg s.im) (RlogNat (n + 1) h1)⟩)
      (w := Cadd ⟨Rmul (Rneg s.re) (RlogNat n hn), Rmul (Rneg s.im) (RlogNat n hn)⟩
        ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩) ?_)
    (Cexp_add ⟨Rmul (Rneg s.re) (RlogNat n hn), Rmul (Rneg s.im) (RlogNat n hn)⟩
      ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩)
  -- argument additivity: `−s·log(n+1) ≈ −s·log n + (−s)·δ_n`, componentwise
  have hlog : Req (RlogNat (n + 1) h1) (Radd (RlogNat n hn) (deltaLogNat n hn)) :=
    Req_symm (Radd_Rsub_self (RlogNat n hn) (RlogNat (n + 1) h1))
  exact ⟨Req_trans (Rmul_congr (Req_refl _) hlog)
      (Rmul_distrib (Rneg s.re) (RlogNat n hn) (deltaLogNat n hn)),
    Req_trans (Rmul_congr (Req_refl _) hlog)
      (Rmul_distrib (Rneg s.im) (RlogNat n hn) (deltaLogNat n hn))⟩

end UOR.Bridge.F1Square.Analysis
