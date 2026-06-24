/-
F1 square — Track 1, item 0/6 substrate: **product-Lipschitz** (`RmulLipschitz.lean`).

The general `t^{σ−1}·ψ(t)` Mellin integrand is a product of two functions, each Lipschitz and bounded on
the integration domain. The integral layer (`DyadicIntegral`/`IntervalIntegral`/`ImproperIntegral`)
consumes a single global Lipschitz constant per integrand, so the product needs its own constant. This is
the standard estimate

    |f(x)g(x) − f(y)g(y)| ≤ |f(x)|·|g(x)−g(y)| + |g(y)|·|f(x)−f(y)| ≤ (M_f·L_g + M_g·L_f)·|x−y|,

via the telescoping `fg − fg = f·(Δg) + (Δf)·g` (`Rsub_split`), `Rabs_Rmul`/`Rabs_Radd`, and product
monotonicity (`Rmul_le_Rmul_both`). Reusable for both tracks (any product integrand).

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.RabsLemmas
import F1Square.Analysis.GammaOne
import F1Square.Analysis.ThetaValueDecay

namespace UOR.Bridge.F1Square.Analysis

/-- The product-Lipschitz constant `M_f·L_g + M_g·L_f` is non-negative — the `0 ≤ L.num` the integral
    layer requires of any Lipschitz constant. -/
theorem Rmul_lip_const_nonneg {Lf Lg Mf Mg : Q}
    (hLf0 : 0 ≤ Lf.num) (hLg0 : 0 ≤ Lg.num) (hMf0 : 0 ≤ Mf.num) (hMg0 : 0 ≤ Mg.num) :
    0 ≤ (add (mul Mf Lg) (mul Mg Lf)).num := by
  show 0 ≤ (Mf.num * Lg.num) * (Mg.den * Lf.den : Nat) + (Mg.num * Lf.num) * (Mf.den * Lg.den : Nat)
  have h1 : 0 ≤ Mf.num * Lg.num := Int.mul_nonneg hMf0 hLg0
  have h2 : 0 ≤ Mg.num * Lf.num := Int.mul_nonneg hMg0 hLf0
  have h3 : (0 : Int) ≤ (Mg.den * Lf.den : Nat) := Int.ofNat_nonneg _
  have h4 : (0 : Int) ≤ (Mf.den * Lg.den : Nat) := Int.ofNat_nonneg _
  have := Int.mul_nonneg h1 h3; have := Int.mul_nonneg h2 h4; omega

/-- **Product-Lipschitz**: `f·g` is `(M_f·L_g + M_g·L_f)`-Lipschitz when `f` is `L_f`-Lipschitz with
    `|f| ≤ M_f` and `g` is `L_g`-Lipschitz with `|g| ≤ M_g`. The constant is the rational
    `add (mul Mf Lg) (mul Mg Lf)`, in the exact `Rmul (ofQ L) (Rabs (Rsub x y))` shape the integral
    layer consumes. -/
theorem Rmul_lipschitz {f g : Real → Real} {Lf Lg Mf Mg : Q}
    (hLfd : 0 < Lf.den) (hLgd : 0 < Lg.den) (hMfd : 0 < Mf.den) (hMgd : 0 < Mg.den)
    (_hLf0 : 0 ≤ Lf.num) (hLg0 : 0 ≤ Lg.num) (_hMf0 : 0 ≤ Mf.num) (hMg0 : 0 ≤ Mg.num)
    (hf_lip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ Lf hLfd) (Rabs (Rsub x y))))
    (hg_lip : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ Lg hLgd) (Rabs (Rsub x y))))
    (hf_bd : ∀ x, Rle (Rabs (f x)) (ofQ Mf hMfd)) (hg_bd : ∀ x, Rle (Rabs (g x)) (ofQ Mg hMgd))
    (x y : Real) :
    Rle (Rabs (Rsub (Rmul (f x) (g x)) (Rmul (f y) (g y))))
        (Rmul (ofQ (add (mul Mf Lg) (mul Mg Lf))
          (add_den_pos (Qmul_den_pos hMfd hLgd) (Qmul_den_pos hMgd hLfd)))
          (Rabs (Rsub x y))) := by
  -- telescoping identity  fg − fg = f·(g x − g y) + (f x − f y)·g
  have htel : Req (Rsub (Rmul (f x) (g x)) (Rmul (f y) (g y)))
      (Radd (Rmul (f x) (Rsub (g x) (g y))) (Rmul (Rsub (f x) (f y)) (g y))) :=
    Req_symm (Req_trans (Radd_congr (Rmul_sub_distrib (f x) (g x) (g y))
        (Rmul_sub_distrib_right (f x) (f y) (g y)))
      (Rsub_split (Rmul (f x) (g x)) (Rmul (f x) (g y)) (Rmul (f y) (g y))))
  -- triangle + |·| multiplicativity
  have htri : Rle (Rabs (Rsub (Rmul (f x) (g x)) (Rmul (f y) (g y))))
      (Radd (Rmul (Rabs (f x)) (Rabs (Rsub (g x) (g y))))
            (Rmul (Rabs (Rsub (f x) (f y))) (Rabs (g y)))) :=
    Rle_trans (Rle_of_Req (Rabs_congr htel))
      (Rle_trans (Rabs_Radd _ _)
        (Rle_of_Req (Radd_congr (Rabs_Rmul (f x) (Rsub (g x) (g y)))
          (Rabs_Rmul (Rsub (f x) (f y)) (g y)))))
  -- bound each product by  M·(L·|x−y|)
  have hwnn : Rnonneg (Rabs (Rsub x y)) := Rnonneg_Rabs _
  have hb1 : Rle (Rmul (Rabs (f x)) (Rabs (Rsub (g x) (g y))))
      (Rmul (ofQ Mf hMfd) (Rmul (ofQ Lg hLgd) (Rabs (Rsub x y)))) :=
    Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_Rmul (Rnonneg_ofQ hLgd hLg0) hwnn)
      (hf_bd x) (hg_lip x y)
  have hb2 : Rle (Rmul (Rabs (Rsub (f x) (f y))) (Rabs (g y)))
      (Rmul (Rmul (ofQ Lf hLfd) (Rabs (Rsub x y))) (ofQ Mg hMgd)) :=
    Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ hMgd hMg0) (hf_lip x y) (hg_bd y)
  -- collect  M_f·(L_g·w) + (L_f·w)·M_g  =  (M_f·L_g + M_g·L_f)·w
  have hcollect : Req (Radd (Rmul (ofQ Mf hMfd) (Rmul (ofQ Lg hLgd) (Rabs (Rsub x y))))
        (Rmul (Rmul (ofQ Lf hLfd) (Rabs (Rsub x y))) (ofQ Mg hMgd)))
      (Rmul (ofQ (add (mul Mf Lg) (mul Mg Lf))
        (add_den_pos (Qmul_den_pos hMfd hLgd) (Qmul_den_pos hMgd hLfd))) (Rabs (Rsub x y))) := by
    refine Req_trans (Radd_congr
        (Req_symm (Rmul_assoc (ofQ Mf hMfd) (ofQ Lg hLgd) (Rabs (Rsub x y))))
        (Req_trans (Rmul_comm (Rmul (ofQ Lf hLfd) (Rabs (Rsub x y))) (ofQ Mg hMgd))
          (Req_trans (Req_symm (Rmul_assoc (ofQ Mg hMgd) (ofQ Lf hLfd) (Rabs (Rsub x y))))
            (Rmul_congr (Rmul_comm (ofQ Mg hMgd) (ofQ Lf hLfd)) (Req_refl _))))) ?_
    refine Req_trans (Req_symm (Rmul_distrib_right (Rmul (ofQ Mf hMfd) (ofQ Lg hLgd))
        (Rmul (ofQ Lf hLfd) (ofQ Mg hMgd)) (Rabs (Rsub x y)))) ?_
    refine Rmul_congr ?_ (Req_refl _)
    have hQeq : Qeq (add (mul Mf Lg) (mul Lf Mg)) (add (mul Mf Lg) (mul Mg Lf)) := by
      simp only [Qeq, add, mul]; push_cast; ring_uor
    exact Req_trans (Radd_congr (Rmul_ofQ_ofQ hMfd hLgd) (Rmul_ofQ_ofQ hLfd hMgd))
      (Req_trans (Radd_ofQ_ofQ (Qmul_den_pos hMfd hLgd) (Qmul_den_pos hLfd hMgd))
        (ofQ_congr _ _ hQeq))
  exact Rle_trans htri (Rle_trans (Radd_le_add hb1 hb2) (Rle_of_Req hcollect))

end UOR.Bridge.F1Square.Analysis
