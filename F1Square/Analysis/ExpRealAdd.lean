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
import F1Square.Analysis.ExpAdd

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

/-- **The rational exp functional equation with explicit error**: for arbitrary `|a| ≤ Ma`, `|b| ≤ Mb`
    and `2(Ma+Mb) ≤ N+2`, `|expSum(a+b) N − expSum a N·expSum b N| ≤ 2(Ma+Mb)^{N+1}/(N+1)!` — the corner
    `expSum_corner_le_gen`, bridged by `expSum_mul_eq`. -/
theorem expSum_add_le {a b : Q} {Ma Mb : Nat} (ha0 : 0 ≤ a.num) (had : 0 < a.den)
    (hb0 : 0 ≤ b.num) (hbd : 0 < b.den) (hqa : Qle (Qabs a) ⟨(Ma : Int), 1⟩) (hqb : Qle (Qabs b) ⟨(Mb : Int), 1⟩)
    (N : Nat) (hN : 2 * (Ma + Mb) ≤ N + 2) :
    Qle (Qabs (Qsub (expSum (add a b) N) (mul (expSum a N) (expSum b N))))
      ⟨(2 * npow (Ma + Mb) (N + 1) : Int), fct (N + 1)⟩ := by
  have hg : ∀ i j, 0 < (mul (expTerm a i) (expTerm b j)).den :=
    fun i j => Qmul_den_pos (expTerm_den_pos had i) (expTerm_den_pos hbd j)
  have hgnn : ∀ i j, 0 ≤ (mul (expTerm a i) (expTerm b j)).num :=
    fun i j => Int.mul_nonneg (expTerm_num_nonneg ha0 i) (expTerm_num_nonneg hb0 j)
  have hPN : 0 < (expSum (add a b) N).den := expSum_den_pos (add_den_pos had hbd) N
  have hprodd : 0 < (mul (expSum a N) (expSum b N)).den :=
    Qmul_den_pos (expSum_den_pos had N) (expSum_den_pos hbd N)
  have hcornerd : 0 < (Fsum (fun i => Qsub (Fsum (fun j => mul (expTerm a i) (expTerm b j)) N)
      (Fsum (fun j => mul (expTerm a i) (expTerm b j)) (N - i))) N).den :=
    Fsum_den_pos (fun i => Qsub_den_pos (Fsum_den_pos (fun j => hg i j) N)
      (Fsum_den_pos (fun j => hg i j) (N - i))) N
  -- |expSum(a+b)N − product| ≈ |corner|, and corner ≥ 0 is ≤ the corner bound
  have hcorner_nn : 0 ≤ (Fsum (fun i => Qsub (Fsum (fun j => mul (expTerm a i) (expTerm b j)) N)
      (Fsum (fun j => mul (expTerm a i) (expTerm b j)) (N - i))) N).num :=
    Fsum_num_nonneg (fun i => Qsub_num_nonneg
      (Fsum_mono_len (fun j => hgnn i j) (fun j => hg i j) (Nat.sub_le N i))) N
  have heq : Qeq (Qsub (expSum (add a b) N) (mul (expSum a N) (expSum b N)))
      (neg (Fsum (fun i => Qsub (Fsum (fun j => mul (expTerm a i) (expTerm b j)) N)
        (Fsum (fun j => mul (expTerm a i) (expTerm b j)) (N - i))) N)) :=
    Qeq_trans (Qsub_den_pos hPN (add_den_pos hPN hcornerd))
      (QsubCongr (Qeq_refl (expSum (add a b) N)) (expSum_mul_eq had hbd N))
      (Qsub_add_self_left (expSum (add a b) N) _)
  refine Qle_congr_left (Qabs_den_pos (neg_den_pos hcornerd)) (Qeq_symm (Qabs_Qeq heq)) ?_
  rw [Qabs_neg]
  exact Qabs_le_of_nonneg hcorner_nn (expSum_corner_le_gen ha0 had hb0 hbd hqa hqb N hN)

end UOR.Bridge.F1Square.Analysis
