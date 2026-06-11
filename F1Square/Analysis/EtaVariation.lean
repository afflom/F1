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
import F1Square.Analysis.ComplexZeta

namespace UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- Complex-algebra helpers (componentwise `Ceq = ⟨Req, Req⟩` lifts of the real laws).
-- ===========================================================================

/-- `Rsub (Rneg x) (Rneg y) ≈ Rneg (Rsub x y)` (both `≈ y − x`). -/
theorem Rsub_RnegRneg (x y : Real) : Req (Rsub (Rneg x) (Rneg y)) (Rneg (Rsub x y)) :=
  Req_symm (Rneg_Radd x (Rneg y))

/-- ℂ addition respects `≈`. -/
theorem Cadd_congr {z z' w w' : Complex} (hz : Ceq z z') (hw : Ceq w w') :
    Ceq (Cadd z w) (Cadd z' w') := ⟨Radd_congr hz.1 hw.1, Radd_congr hz.2 hw.2⟩

/-- ℂ negation respects `≈`. -/
theorem Cneg_congr {z z' : Complex} (h : Ceq z z') : Ceq (Cneg z) (Cneg z') :=
  ⟨Rneg_congr h.1, Rneg_congr h.2⟩

/-- ℂ multiplication respects `≈`. -/
theorem Cmul_congr {z z' w w' : Complex} (hz : Ceq z z') (hw : Ceq w w') :
    Ceq (Cmul z w) (Cmul z' w') :=
  ⟨Rsub_congr (Rmul_congr hz.1 hw.1) (Rmul_congr hz.2 hw.2),
   Radd_congr (Rmul_congr hz.1 hw.2) (Rmul_congr hz.2 hw.1)⟩

/-- ℂ subtraction respects `≈`. -/
theorem Csub_congr {z z' w w' : Complex} (hz : Ceq z z') (hw : Ceq w w') :
    Ceq (Csub z w) (Csub z' w') := Cadd_congr hz (Cneg_congr hw)

/-- `z·(−w) ≈ −(z·w)` on ℂ. -/
theorem Cmul_neg_right (z w : Complex) : Ceq (Cmul z (Cneg w)) (Cneg (Cmul z w)) :=
  ⟨Req_trans (Rsub_congr (Rmul_neg_right z.re w.re) (Rmul_neg_right z.im w.im))
      (Rsub_RnegRneg (Rmul z.re w.re) (Rmul z.im w.im)),
   Req_trans (Radd_congr (Rmul_neg_right z.re w.im) (Rmul_neg_right z.im w.re))
      (Req_symm (Rneg_Radd (Rmul z.re w.im) (Rmul z.im w.re)))⟩

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

/-- **The `n⁻ˢ` consecutive difference** `n⁻ˢ − (n+1)⁻ˢ ≈ n⁻ˢ·(1 − e^{−s·δ_n})` (for `n ≥ 2`) — the form
    on which the variation modulus `|n⁻ˢ − (n+1)⁻ˢ| ≤ |n⁻ˢ|·|1 − e^{−s·δ_n}|` is read off. Factor `n⁻ˢ`
    out of `n⁻ˢ − n⁻ˢ·e^{−s·δ_n}` (`cpowNeg_succ`) via `Cmul_distrib`/`Cmul_one`/`Cmul_neg_right`. -/
theorem cpowNeg_diff (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Ceq (Csub (cpowNeg s n) (cpowNeg s (n + 1)))
      (Cmul (cpowNeg s n)
        (Csub Cone (Cexp ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩))) :=
  Ceq_trans (Cadd_congr (Ceq_refl _) (Cneg_congr (cpowNeg_succ s n hn)))
    (Ceq_trans (Cadd_congr (Ceq_symm (Cmul_one (cpowNeg s n)))
        (Ceq_symm (Cmul_neg_right (cpowNeg s n)
          (Cexp ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩))))
      (Ceq_symm (Cmul_distrib (cpowNeg s n) Cone
        (Cneg (Cexp ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩)))))

-- ===========================================================================
-- The `n⁻ˢ` per-term component bounds `−n⁻ᴿᵉˢ ≤ Re/Im(n⁻ˢ) ≤ n⁻ᴿᵉˢ` (no real-abs; two-sided `Rle`,
-- mirroring `ComplexZeta`'s `czetaTerm_re_le`/`ge`). `cpowNeg s n = e^{−s·log n}` for `n ≥ 2`. -/
-- ===========================================================================

/-- `Re(n⁻ˢ) ≤ e^{−Re s·log n}` (`= n⁻ᴿᵉˢ`). -/
theorem cpowNeg_re_le (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Rle ((cpowNeg s n).re) (RexpReal (Rmul (Rneg s.re) (RlogNat n hn))) := by
  unfold cpowNeg; rw [dif_pos hn]; exact Cexp_re_le _

/-- `−e^{−Re s·log n} ≤ Re(n⁻ˢ)`. -/
theorem cpowNeg_re_ge (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Rle (Rneg (RexpReal (Rmul (Rneg s.re) (RlogNat n hn)))) ((cpowNeg s n).re) := by
  unfold cpowNeg; rw [dif_pos hn]; exact Cexp_re_ge _

/-- `Im(n⁻ˢ) ≤ e^{−Re s·log n}`. -/
theorem cpowNeg_im_le (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Rle ((cpowNeg s n).im) (RexpReal (Rmul (Rneg s.re) (RlogNat n hn))) := by
  unfold cpowNeg; rw [dif_pos hn]; exact Cexp_im_le _

/-- `−e^{−Re s·log n} ≤ Im(n⁻ˢ)`. -/
theorem cpowNeg_im_ge (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Rle (Rneg (RexpReal (Rmul (Rneg s.re) (RlogNat n hn)))) ((cpowNeg s n).im) := by
  unfold cpowNeg; rw [dif_pos hn]; exact Cexp_im_ge _

end UOR.Bridge.F1Square.Analysis
