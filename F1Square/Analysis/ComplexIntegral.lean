/-
F1 square — certified integration over the constructive **Complex** API (Track-2 step 1): the
complex line integral of `gr + i·gi` over a bounded real interval `[a, a+w]`, built componentwise
from the real interval integral.

`∫_a^{a+w} (gr + i·gi) dt = ⟨∫_a^{a+w} gr, ∫_a^{a+w} gi⟩` — each component a certified real integral
(`riemannIntegralI`). This is the form the Mellin integrand `t^{s/2−1}ψ(t)` (item 3) and the
complex-valued Weil test integrals (Track 2) inhabit; the deep content (improper half-line, the
Poisson/modular seam, positivity) is downstream and unchanged.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.IntervalIntegral
import F1Square.Analysis.ImproperIntegral
import F1Square.Analysis.Complex

namespace UOR.Bridge.F1Square.Analysis

/-- **The complex line integral** `∫_a^{a+w} (gr + i·gi) dt` over `[a, a+w]` (`w ≥ 0`), assembled
    from the two real component integrals. Each component integrand is given with its own Lipschitz
    modulus (`Lr`, `Li`). -/
def Cintegral {gr gi : Real → Real} {Lr Li : Q}
    (hLrd : 0 < Lr.den) (hLrn : 0 ≤ Lr.num)
    (hlipr : ∀ x y, Rle (Rabs (Rsub (gr x) (gr y))) (Rmul (ofQ Lr hLrd) (Rabs (Rsub x y))))
    (hfcr : ∀ x y, Req x y → Req (gr x) (gr y))
    (hLid : 0 < Li.den) (hLin : 0 ≤ Li.num)
    (hlipi : ∀ x y, Rle (Rabs (Rsub (gi x) (gi y))) (Rmul (ofQ Li hLid) (Rabs (Rsub x y))))
    (hfci : ∀ x y, Req x y → Req (gi x) (gi y))
    (a w : Q) (ha : 0 < a.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : Complex :=
  ⟨riemannIntegralI hLrd hLrn hlipr hfcr a w ha hw hwn,
   riemannIntegralI hLid hLin hlipi hfci a w ha hw hwn⟩

/-- **`∫_a^{a+w} z = w·z`** for a complex constant `z` (componentwise `riemannIntegralI_const`). -/
theorem Cintegral_const (zr zi : Real) (a w : Q) (ha : 0 < a.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) :
    Ceq (Cintegral (gr := fun _ => zr) (gi := fun _ => zi) (Lr := (⟨0, 1⟩ : Q)) (Li := (⟨0, 1⟩ : Q))
          (by decide) (by decide) (const_lip0 zr) (fun _ _ _ => Req_refl zr)
          (by decide) (by decide) (const_lip0 zi) (fun _ _ _ => Req_refl zi) a w ha hw hwn)
        ⟨Rmul (ofQ w hw) zr, Rmul (ofQ w hw) zi⟩ :=
  ⟨Rmul_congr (Req_refl _) (riemannIntegral_const_gen zr _ _ _ _),
   Rmul_congr (Req_refl _) (riemannIntegral_const_gen zi _ _ _ _)⟩

/-- **The complex half-line integral** `∫₀^∞ (gr + i·gi) dt` — the full Mellin domain for a
    complex-valued integrand, assembled componentwise from the real `halfLineIntegral`. Each component
    carries its own Lipschitz modulus and summable-decay seam (the genuine convergence content). This
    is the object the Mellin transform of the theta relation (item 3) and the windowed Weil pairing
    (Track 2) inhabit. -/
def ChalfLineIntegral {gr gi : Real → Real} {Lr Li Kr Ki : Q}
    (hLrd : 0 < Lr.den) (hLrn : 0 ≤ Lr.num)
    (hlipr : ∀ x y, Rle (Rabs (Rsub (gr x) (gr y))) (Rmul (ofQ Lr hLrd) (Rabs (Rsub x y))))
    (hfcr : ∀ x y, Req x y → Req (gr x) (gr y)) (hKrd : 0 < Kr.den) (hKr0 : 0 ≤ Kr.num)
    (hbr : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul Kr (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKrd (digamma_succ_mul_pos hm))))
          (integralTerm hLrd hLrn hlipr hfcr m)
      ∧ Rle (integralTerm hLrd hLrn hlipr hfcr m)
          (ofQ (mul Kr (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKrd (digamma_succ_mul_pos hm))))
    (hLid : 0 < Li.den) (hLin : 0 ≤ Li.num)
    (hlipi : ∀ x y, Rle (Rabs (Rsub (gi x) (gi y))) (Rmul (ofQ Li hLid) (Rabs (Rsub x y))))
    (hfci : ∀ x y, Req x y → Req (gi x) (gi y)) (hKid : 0 < Ki.den) (hKi0 : 0 ≤ Ki.num)
    (hbi : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul Ki (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKid (digamma_succ_mul_pos hm))))
          (integralTerm hLid hLin hlipi hfci m)
      ∧ Rle (integralTerm hLid hLin hlipi hfci m)
          (ofQ (mul Ki (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKid (digamma_succ_mul_pos hm)))) :
    Complex :=
  ⟨halfLineIntegral hLrd hLrn hlipr hfcr hKrd hKr0 hbr,
   halfLineIntegral hLid hLin hlipi hfci hKid hKi0 hbi⟩

/-- **The complex half-line integral is additive in the integrand**
    `∫₀^∞ ((gfr+ggr) + i·(gfi+ggi)) = ∫₀^∞ (gfr + i·gfi) + ∫₀^∞ (ggr + i·ggi)` — the additive half of
    linearity for the constructive complex Mellin integral, the object the Weil pairing and the
    Mellin transform of the theta relation inhabit. Componentwise from the real `halfLineIntegral_add`
    (real and imaginary parts, each at its own shared Lipschitz constant `Lr`/`Li` and decay rate
    `Kr`/`Ki`). -/
theorem ChalfLineIntegral_add {gfr ggr gfi ggi : Real → Real} {Lr Li Kr Ki : Q}
    (hLrd : 0 < Lr.den) (hLrn : 0 ≤ Lr.num)
    (hlipr_f : ∀ x y, Rle (Rabs (Rsub (gfr x) (gfr y))) (Rmul (ofQ Lr hLrd) (Rabs (Rsub x y))))
    (hfcr_f : ∀ x y, Req x y → Req (gfr x) (gfr y))
    (hlipr_g : ∀ x y, Rle (Rabs (Rsub (ggr x) (ggr y))) (Rmul (ofQ Lr hLrd) (Rabs (Rsub x y))))
    (hfcr_g : ∀ x y, Req x y → Req (ggr x) (ggr y))
    (hlipr_fg : ∀ x y, Rle (Rabs (Rsub (Radd (gfr x) (ggr x)) (Radd (gfr y) (ggr y))))
        (Rmul (ofQ Lr hLrd) (Rabs (Rsub x y))))
    (hfcr_fg : ∀ x y, Req x y → Req (Radd (gfr x) (ggr x)) (Radd (gfr y) (ggr y)))
    (hKrd : 0 < Kr.den) (hKr0 : 0 ≤ Kr.num)
    (hbr_f : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul Kr (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKrd (digamma_succ_mul_pos hm))))
          (integralTerm hLrd hLrn hlipr_f hfcr_f m)
      ∧ Rle (integralTerm hLrd hLrn hlipr_f hfcr_f m)
          (ofQ (mul Kr (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKrd (digamma_succ_mul_pos hm))))
    (hbr_g : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul Kr (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKrd (digamma_succ_mul_pos hm))))
          (integralTerm hLrd hLrn hlipr_g hfcr_g m)
      ∧ Rle (integralTerm hLrd hLrn hlipr_g hfcr_g m)
          (ofQ (mul Kr (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKrd (digamma_succ_mul_pos hm))))
    (hbr_fg : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul Kr (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKrd (digamma_succ_mul_pos hm))))
          (integralTerm hLrd hLrn hlipr_fg hfcr_fg m)
      ∧ Rle (integralTerm hLrd hLrn hlipr_fg hfcr_fg m)
          (ofQ (mul Kr (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKrd (digamma_succ_mul_pos hm))))
    (hLid : 0 < Li.den) (hLin : 0 ≤ Li.num)
    (hlipi_f : ∀ x y, Rle (Rabs (Rsub (gfi x) (gfi y))) (Rmul (ofQ Li hLid) (Rabs (Rsub x y))))
    (hfci_f : ∀ x y, Req x y → Req (gfi x) (gfi y))
    (hlipi_g : ∀ x y, Rle (Rabs (Rsub (ggi x) (ggi y))) (Rmul (ofQ Li hLid) (Rabs (Rsub x y))))
    (hfci_g : ∀ x y, Req x y → Req (ggi x) (ggi y))
    (hlipi_fg : ∀ x y, Rle (Rabs (Rsub (Radd (gfi x) (ggi x)) (Radd (gfi y) (ggi y))))
        (Rmul (ofQ Li hLid) (Rabs (Rsub x y))))
    (hfci_fg : ∀ x y, Req x y → Req (Radd (gfi x) (ggi x)) (Radd (gfi y) (ggi y)))
    (hKid : 0 < Ki.den) (hKi0 : 0 ≤ Ki.num)
    (hbi_f : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul Ki (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKid (digamma_succ_mul_pos hm))))
          (integralTerm hLid hLin hlipi_f hfci_f m)
      ∧ Rle (integralTerm hLid hLin hlipi_f hfci_f m)
          (ofQ (mul Ki (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKid (digamma_succ_mul_pos hm))))
    (hbi_g : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul Ki (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKid (digamma_succ_mul_pos hm))))
          (integralTerm hLid hLin hlipi_g hfci_g m)
      ∧ Rle (integralTerm hLid hLin hlipi_g hfci_g m)
          (ofQ (mul Ki (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKid (digamma_succ_mul_pos hm))))
    (hbi_fg : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul Ki (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKid (digamma_succ_mul_pos hm))))
          (integralTerm hLid hLin hlipi_fg hfci_fg m)
      ∧ Rle (integralTerm hLid hLin hlipi_fg hfci_fg m)
          (ofQ (mul Ki (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKid (digamma_succ_mul_pos hm)))) :
    Ceq (ChalfLineIntegral hLrd hLrn hlipr_fg hfcr_fg hKrd hKr0 hbr_fg
            hLid hLin hlipi_fg hfci_fg hKid hKi0 hbi_fg)
        (Cadd (ChalfLineIntegral hLrd hLrn hlipr_f hfcr_f hKrd hKr0 hbr_f
                  hLid hLin hlipi_f hfci_f hKid hKi0 hbi_f)
              (ChalfLineIntegral hLrd hLrn hlipr_g hfcr_g hKrd hKr0 hbr_g
                  hLid hLin hlipi_g hfci_g hKid hKi0 hbi_g)) :=
  ⟨halfLineIntegral_add hLrd hLrn hlipr_f hfcr_f hlipr_g hfcr_g hlipr_fg hfcr_fg
      hKrd hKr0 hbr_f hbr_g hbr_fg,
   halfLineIntegral_add hLid hLin hlipi_f hfci_f hlipi_g hfci_g hlipi_fg hfci_fg
      hKid hKi0 hbi_f hbi_g hbi_fg⟩

end UOR.Bridge.F1Square.Analysis
