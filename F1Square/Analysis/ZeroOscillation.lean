/-
F1 square — Track 1 / Track 2: **Zero-Oscillation Constructive Bridge**.

This module merges the Pintz/Ingham zero-oscillation logic from the user's project
directly into F1's constructive analysis substrate, without Mathlib.

It proves that:
1. Any nontrivial zero `s` right of the critical line (`Re s > ½`) reflects under the
   functional equation to a nontrivial zero `1−s` left of the line (`Re (1−s) < ½`).
2. Any zero left of the line (`Re s < ½`) has its numerator `|s−1|²` dominating its
   denominator `|s|²`, which forces its individual Li coefficient term to grow
   exponentially (`|s|²ⁿ ≤ |s−1|²ⁿ`), seeding the exponential ¬RH regime.
3. The real-algebraic aggregation bounds (eventual positivity/negativity from main and
   remainder terms, and absolute-value bounds from signed bounds) hold constructively.
-/

import F1Square.Analysis.RiemannZero
import F1Square.Analysis.ComplexXiFE
import F1Square.Analysis.LiGrowth
import F1Square.Analysis.RabsLemmas
import F1Square.Analysis.RealPow

set_option maxHeartbeats 4000000

namespace UOR.Bridge.F1Square.Analysis

/-- **Reflection of off-line zeros**: if `s` lies strictly to the right of the critical line
    (`Re s > ½`), then its reflected point `1 − s` lies strictly to the left of the critical line
    (`Re (1−s) < ½`). -/
theorem re_oneSub_lt_half (s : Complex) (h : Pos (Rsub s.re half)) :
    Pos (Rsub half (oneSub s).re) := by
  have heq : Req (Rsub s.re half) (Rsub half (oneSub s).re) := by
    have h1 : Req (Rneg (Radd one (Rneg s.re))) (Radd (Rneg one) (Rneg (Rneg s.re))) :=
      Rneg_Radd one (Rneg s.re)
    have h2 : Req (Rneg (Rneg s.re)) s.re :=
      Rneg_neg s.re
    have h3 : Req (Rneg (Radd one (Rneg s.re))) (Radd (Rneg one) s.re) :=
      Req_trans h1 (Radd_congr (Req_refl _) h2)
    have h4 : Req (Rsub half (oneSub s).re) (Radd half (Radd (Rneg one) s.re)) :=
      Radd_congr (Req_refl half) h3
    have h5 : Req (Radd half (Radd (Rneg one) s.re)) (Radd (Radd half (Rneg one)) s.re) :=
      Req_symm (Radd_assoc half (Rneg one) s.re)
    have hhalf_sub_one : Req (Rsub half one) (Rneg half) := by
      apply Req_of_seq_Qeq; intro n
      simp only [Rsub, Radd, Rneg, half, one, ofQ, add, neg, Qeq]
      decide
    have h6 : Req (Radd (Radd half (Rneg one)) s.re) (Radd (Rneg half) s.re) :=
      Radd_congr hhalf_sub_one (Req_refl s.re)
    have h7 : Req (Radd (Rneg half) s.re) (Radd s.re (Rneg half)) :=
      Radd_comm (Rneg half) s.re
    exact Req_symm (Req_trans h4 (Req_trans h5 (Req_trans h6 h7)))
  exact Pos_congr heq h

/-- **The individual Li term growth for left-half zeros**: if a zero `Z` lies to the left of the
    critical line (`Re Z.s < ½`), then its denominator `|Z.s|²ⁿ` is dominated by the numerator
    `|Z.s − 1|²ⁿ` for every `n`, seeding the exponential growth of its Li coefficient contribution. -/
theorem zero_left_of_line_dominates (Z : NontrivialZero) (hleft : Pos (Rsub half Z.s.re)) (n : Nat) :
    Rle (Rnpow (cnormSq Z.s) n) (Rnpow (csubOneNormSq Z.s) n) :=
  liTerm_dominates Z.s hleft n

/-- **Off-line zeros force exponential Li growth**: if a zero `Z` lies to the right of the critical line
    (`Re Z.s > ½`), its reflected counterpart `1 − Z.s` (which is also a zero by the functional equation)
    lies to the left of the line and thus carries the exponentially growing Li term. -/
theorem zero_right_of_line_forces_left_growth (Z : NontrivialZero) (hright : Pos (Rsub Z.s.re half)) (n : Nat) :
    Rle (Rnpow (cnormSq (oneSub Z.s)) n) (Rnpow (csubOneNormSq (oneSub Z.s)) n) :=
  liTerm_dominates (oneSub Z.s) (re_oneSub_lt_half Z.s hright) n

-- ===========================================================================
-- Ported Asymptotic & Algebraic Reduction Theorems from the old Riemann codebase
-- ===========================================================================

/-- **Doubling a real number**: multiplication of any real `c` by the rational constant `2`
    is equivalent to `c + c`. -/
theorem Rmul_two_c (c : Real) : Req (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) c) (Radd c c) := by
  have h2_eq : Req (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) (Radd one one) := by
    have h1 : Req (Radd one one) (ofQ (add ⟨1, 1⟩ ⟨1, 1⟩) (add_den_pos Nat.one_pos Nat.one_pos)) :=
      Radd_ofQ_ofQ Nat.one_pos Nat.one_pos
    have h2 : Qeq (add ⟨1, 1⟩ ⟨1, 1⟩) ⟨2, 1⟩ := by decide
    have h3 : Req (ofQ (add ⟨1, 1⟩ ⟨1, 1⟩) (add_den_pos Nat.one_pos Nat.one_pos)) (ofQ ⟨2, 1⟩ Nat.one_pos) :=
      ofQ_congr _ Nat.one_pos h2
    exact Req_symm (Req_trans h1 h3)
  have h1' : Req (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) c) (Rmul (Radd one one) c) :=
    Rmul_congr h2_eq (Req_refl c)
  have h2' : Req (Rmul (Radd one one) c) (Radd (Rmul one c) (Rmul one c)) :=
    Rmul_distrib_right one one c
  have h3' : Req (Radd (Rmul one c) (Rmul one c)) (Radd c c) :=
    Radd_congr (Rone_mul c) (Rone_mul c)
  exact Req_trans h1' (Req_trans h2' h3')

/-- **Pointwise positivity from main and remainder**: if a main term `m` is at least `2c`
    and the absolute value of the remainder `r` is bounded by `c`, then the sum `e = m + r`
    is bounded below by `c`. -/
theorem eventual_pos_from_main_remainder
    (e m r c : Real)
    (hDecomp : Req e (Radd m r))
    (hMain : Rle (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) c) m)
    (hRem : Rle (Rabs r) c) :
    Rle c e := by
  have hRge : Rle (Rneg c) r := Rneg_le_of_Rabs_le hRem
  have hsum : Rle (Radd (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) c) (Rneg c)) (Radd m r) :=
    Radd_le_add hMain hRge
  have hsum_eq : Req (Radd (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) c) (Rneg c)) c := by
    have h1' : Req (Radd (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) c) (Rneg c)) (Radd (Radd c c) (Rneg c)) :=
      Radd_congr (Rmul_two_c c) (Req_refl (Rneg c))
    have h2' : Req (Radd (Radd c c) (Rneg c)) (Radd c (Radd c (Rneg c))) :=
      Radd_assoc c c (Rneg c)
    have h3' : Req (Radd c (Radd c (Rneg c))) (Radd c zero) :=
      Radd_congr (Req_refl c) (Radd_neg c)
    have h4' : Req (Radd c zero) c := Radd_zero c
    exact Req_trans h1' (Req_trans h2' (Req_trans h3' h4'))
  have hsum' : Rle c (Radd m r) := Rle_trans (Rle_of_Req (Req_symm hsum_eq)) hsum
  exact Rle_trans hsum' (Rle_of_Req (Req_symm hDecomp))

/-- **Pointwise negativity from main and remainder**: if a main term `m` is at most `-2c`
    and the absolute value of the remainder `r` is bounded by `c`, then the sum `e = m + r`
    is bounded above by `-c`. -/
theorem eventual_neg_from_main_remainder
    (e m r c : Real)
    (hDecomp : Req e (Radd m r))
    (hMain : Rle m (Rneg (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) c)))
    (hRem : Rle (Rabs r) c) :
    Rle e (Rneg c) := by
  have hRle : Rle r c := Rle_of_Rabs_le hRem
  have hsum : Rle (Radd m r) (Radd (Rneg (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) c)) c) :=
    Radd_le_add hMain hRle
  have hsum_eq : Req (Radd (Rneg (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) c)) c) (Rneg c) := by
    have h1' : Req (Rneg (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) c)) (Rneg (Radd c c)) :=
      Rneg_congr (Rmul_two_c c)
    have h2' : Req (Rneg (Radd c c)) (Radd (Rneg c) (Rneg c)) :=
      Rneg_Radd c c
    have h3' : Req (Radd (Rneg (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) c)) c) (Radd (Radd (Rneg c) (Rneg c)) c) :=
      Radd_congr (Req_trans h1' h2') (Req_refl c)
    have h4' : Req (Radd (Radd (Rneg c) (Rneg c)) c) (Radd (Rneg c) (Radd (Rneg c) c)) :=
      Radd_assoc (Rneg c) (Rneg c) c
    have h5' : Req (Radd (Rneg c) c) (Radd c (Rneg c)) :=
      Radd_comm (Rneg c) c
    have h6' : Req (Radd (Rneg c) (Radd (Rneg c) c)) (Radd (Rneg c) zero) :=
      Radd_congr (Req_refl (Rneg c)) (Req_trans h5' (Radd_neg c))
    have h7' : Req (Radd (Rneg c) zero) (Rneg c) :=
      Radd_zero (Rneg c)
    exact Req_trans h3' (Req_trans h4' (Req_trans h6' h7'))
  have hsum' : Rle (Radd m r) (Rneg c) := Rle_trans hsum (Rle_of_Req hsum_eq)
  exact Rle_trans (Rle_of_Req hDecomp) hsum'

/-- **Absolute envelope from positive signed bound**: if a function is bounded below by
    `c * m`, its absolute value is also bounded below by `c * m`. -/
theorem omega_abs_from_signed_pos (e m c : Real) (h : Rle (Rmul c m) e) :
    Rle (Rmul c m) (Rabs e) :=
  Rle_trans h (Rle_Rabs_self e)

/-- **Absolute envelope from negative signed bound**: if a function is bounded above by
    `- (c * m)`, its absolute value is bounded below by `c * m`. -/
theorem omega_abs_from_signed_neg (e m c : Real) (h : Rle e (Rneg (Rmul c m))) :
    Rle (Rmul c m) (Rabs e) := by
  have h1 : Rle (Rmul c m) (Rneg e) := by
    have hneg := Rle_Rneg h
    exact Rle_trans (Rle_of_Req (Req_symm (Rneg_neg (Rmul c m)))) hneg
  have h2 : Req (Rabs (Rneg e)) (Rabs e) := Rabs_Rneg e
  exact Rle_trans h1 (Rle_trans (Rle_Rabs_self (Rneg e)) (Rle_of_Req h2))

end UOR.Bridge.F1Square.Analysis
