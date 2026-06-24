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

end UOR.Bridge.F1Square.Analysis
