/-
F1 square — **the exponential functional equation on all of ℝ**: `exp(x+y) ≈ exp x · exp y`
(`RexpReal_add`), lifting the `[0,1]` rational case to general constructive reals. The Cauchy-product
corner is bounded for *arbitrary* arguments (`expSum_corner_le_gen`, via `expSum_mul_le` +
`expSum_trunc_bound`), and the diagonal gap is closed at the `RexpReal` reindex depth.

This is the first brick of the `ζ` analytic stack: it upgrades `exp` to a homomorphism, the prerequisite
for `exp(c·log n) = nᶜ` (real powers) and hence the `ζ(s)` tail bound at `Re s > 1`.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.ExpReal
import F1Square.Analysis.Binomial
import F1Square.Analysis.ROrder

namespace UOR.Bridge.F1Square.Analysis

/-- **The Cauchy-product corner for arbitrary arguments**: with `|a| ≤ Ma`, `|b| ≤ Mb` and `2(Ma+Mb) ≤ M+2`,
    the corner `Σᵢ (Σⱼ≤M − Σⱼ≤M−i)` is bounded by the `exp(a+b)` tail `2(Ma+Mb)^{M+1}/(M+1)!`. Since
    `corner = expSum a M·expSum b M − expSum(a+b) M` (`expSum_mul_eq`) and the product `≤ expSum(a+b)(2M)`
    (`expSum_mul_le`), the corner `≤ expSum(a+b)(2M) − expSum(a+b) M ≤` the truncation tail. -/
theorem expSum_corner_le_gen {a b : Q} {Ma Mb : Nat} (ha0 : 0 ≤ a.num) (had : 0 < a.den)
    (hb0 : 0 ≤ b.num) (hbd : 0 < b.den) (hqa : Qle (Qabs a) ⟨(Ma : Int), 1⟩) (hqb : Qle (Qabs b) ⟨(Mb : Int), 1⟩)
    (M : Nat) (hM : 2 * (Ma + Mb) ≤ M + 2) :
    Qle (Fsum (fun i => Qsub (Fsum (fun j => mul (expTerm a i) (expTerm b j)) M)
          (Fsum (fun j => mul (expTerm a i) (expTerm b j)) (M - i))) M)
      ⟨(2 * npow (Ma + Mb) (M + 1) : Int), fct (M + 1)⟩ := by
  have hpqd : 0 < (add a b).den := add_den_pos had hbd
  have hPM : 0 < (expSum (add a b) M).den := expSum_den_pos hpqd M
  have hP2M : 0 < (expSum (add a b) (2 * M)).den := expSum_den_pos hpqd (2 * M)
  have hprodd : 0 < (mul (expSum a M) (expSum b M)).den :=
    Qmul_den_pos (expSum_den_pos had M) (expSum_den_pos hbd M)
  -- |a+b| ≤ Ma+Mb
  have hsum_bd : Qle (Qabs (add a b)) ⟨((Ma + Mb : Nat) : Int), 1⟩ := by
    refine Qle_trans (add_den_pos Nat.one_pos Nat.one_pos)
      (Qle_trans (add_den_pos (Qabs_den_pos had) (Qabs_den_pos hbd)) (Qabs_add_le a b)
        (Qadd_le_add hqa hqb)) (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor))
  -- corner ≈ product − expSum(a+b) M
  have hcorner_eq : Qeq (Fsum (fun i => Qsub (Fsum (fun j => mul (expTerm a i) (expTerm b j)) M)
          (Fsum (fun j => mul (expTerm a i) (expTerm b j)) (M - i))) M)
      (Qsub (mul (expSum a M) (expSum b M)) (expSum (add a b) M)) := by
    refine Qeq_symm (Qeq_trans (Qsub_den_pos (add_den_pos hPM ?_) hPM)
      (QsubCongr (expSum_mul_eq had hbd M) (Qeq_refl _)) (Qsub_add_left_cancel (expSum (add a b) M) _))
    exact Fsum_den_pos (fun i => Qsub_den_pos
      (Fsum_den_pos (fun j => Qmul_den_pos (expTerm_den_pos had i) (expTerm_den_pos hbd j)) M)
      (Fsum_den_pos (fun j => Qmul_den_pos (expTerm_den_pos had i) (expTerm_den_pos hbd j)) (M - i))) M
  refine Qle_trans (Qsub_den_pos hprodd hPM) (Qeq_le hcorner_eq) ?_
  refine Qle_trans (Qsub_den_pos hP2M hPM) (Qsub_le_sub (expSum_mul_le ha0 had hb0 hbd M)) ?_
  exact Qle_trans (Qabs_den_pos (Qsub_den_pos hP2M hPM)) (Qle_self_Qabs _)
    (expSum_trunc_bound hpqd hsum_bd (a := M) (b := 2 * M) hM (by omega))

end UOR.Bridge.F1Square.Analysis
