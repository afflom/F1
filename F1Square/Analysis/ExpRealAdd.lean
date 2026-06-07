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

/-- **Exp diagonal reconciliation**: two exp partial sums at different arguments and depths differ by a
    depth tail plus an argument-Lipschitz term — `|expSum a R − expSum b R'| ≤ 2M^{R'+1}/(R'+1)! +
    LipS(M,R')·|a − b|` (for `R' ≤ R`, `2M ≤ R'+2`, `|a|,|b| ≤ M`). Triangle through `expSum a R'`. -/
theorem expSum_reconcile {a b : Q} {M : Nat} (had : 0 < a.den) (hbd : 0 < b.den)
    (ha : Qle (Qabs a) ⟨(M : Int), 1⟩) (hb : Qle (Qabs b) ⟨(M : Int), 1⟩)
    {R R' : Nat} (hR'2 : 2 * M ≤ R' + 2) (hRR' : R' ≤ R) :
    Qle (Qabs (Qsub (expSum a R) (expSum b R')))
      (add ⟨(2 * npow M (R' + 1) : Int), fct (R' + 1)⟩ (mul (LipS M R') (Qabs (Qsub a b)))) := by
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (expSum_den_pos had R) (expSum_den_pos had R')))
      (Qabs_den_pos (Qsub_den_pos (expSum_den_pos had R') (expSum_den_pos hbd R'))))
    (Qabs_sub_triangle (expSum_den_pos had R) (expSum_den_pos had R') (expSum_den_pos hbd R')) ?_
  exact Qadd_le_add (expSum_trunc_bound had ha hR'2 hRR') (expSum_Lip_le had hbd ha hb R')

/-- **Product difference**: `|A·B − A'·B'| ≤ |B|·|A−A'| + |A'|·|B−B'|`, via `AB−A'B' = B(A−A')+A'(B−B')`. -/
theorem Qprod_diff_le (A A' B B' : Q) (hAd : 0 < A.den) (hA'd : 0 < A'.den) (hBd : 0 < B.den) (hB'd : 0 < B'.den) :
    Qle (Qabs (Qsub (mul A B) (mul A' B')))
      (add (mul (Qabs B) (Qabs (Qsub A A'))) (mul (Qabs A') (Qabs (Qsub B B')))) := by
  have hid : Qeq (Qsub (mul A B) (mul A' B'))
      (add (mul B (Qsub A A')) (mul A' (Qsub B B'))) := by
    simp only [Qeq, Qsub, add, mul, neg]; push_cast; ring_uor
  refine Qle_congr_left (Qabs_den_pos (add_den_pos (Qmul_den_pos hBd (Qsub_den_pos hAd hA'd))
      (Qmul_den_pos hA'd (Qsub_den_pos hBd hB'd)))) (Qeq_symm (Qabs_Qeq hid)) ?_
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qmul_den_pos hBd (Qsub_den_pos hAd hA'd)))
      (Qabs_den_pos (Qmul_den_pos hA'd (Qsub_den_pos hBd hB'd))))
    (Qabs_add_le _ _) ?_
  rw [Qabs_mul B (Qsub A A'), Qabs_mul A' (Qsub B B')]
  exact Qle_refl _

/-- **Factorial decay at the exp diagonal depth**: `2·(xBound x)^{R+1}·2(j+1) ≤ (R+1)!` at `R = RexpReal_R x j`. -/
theorem RexpReal_trunc_decay (x : Real) (j : Nat) :
    2 * npow (xBound x) (RexpReal_R x j + 1) * (2 * (j + 1)) ≤ fct (RexpReal_R x j + 1) := by
  have hM : 0 < xBound x := xBound_pos x
  have hK : npow (xBound x) (2 * xBound x + 1) ≤ RexpReal_K x := by unfold RexpReal_K; omega
  have htr := trunc_reindex (xBound x) (2 * (j + 1)) (4 * (j + 1) * RexpReal_K x) hM (by
    have h4 : 4 * (j + 1) * npow (xBound x) (2 * xBound x + 1) ≤ 4 * (j + 1) * RexpReal_K x :=
      Nat.mul_le_mul (Nat.le_refl _) hK
    rw [show 2 * (2 * (j + 1)) = 4 * (j + 1) from by omega]; omega)
  have hd : 2 * xBound x + 1 + 4 * (j + 1) * RexpReal_K x = RexpReal_R x j + 1 := by unfold RexpReal_R; omega
  rw [hd] at htr; exact htr

/-- The exp diagonal truncation term as a rational bound: `2(xBound x)^{R+1}/(R+1)! ≤ 1/(2(j+1))`. -/
theorem RexpReal_trunc_le (x : Real) (j : Nat) :
    Qle (⟨(2 * npow (xBound x) (RexpReal_R x j + 1) : Int), fct (RexpReal_R x j + 1)⟩ : Q) ⟨1, 2 * (j + 1)⟩ := by
  show (2 * npow (xBound x) (RexpReal_R x j + 1) : Int) * ((2 * (j + 1) : Nat) : Int)
      ≤ (1 : Int) * ((fct (RexpReal_R x j + 1) : Nat) : Int)
  have h := RexpReal_trunc_decay x j
  have hI : ((2 * npow (xBound x) (RexpReal_R x j + 1) * (2 * (j + 1)) : Nat) : Int)
      ≤ ((fct (RexpReal_R x j + 1) : Nat) : Int) := by exact_mod_cast h
  push_cast at hI ⊢; omega

/-- Uniform bound `|expSum q N| ≤ Un = (expM_U M (2M)).num.toNat` for `|q| ≤ M` (any `N`). Via the
    absolute-difference domination `|expSum q N − expSum q 0| ≤ expSumM M N − expSumM M 0`, then
    `expSumM M N = LipS M (N+1) ≤ expM_U M (2M) ≤ Un`. -/
theorem expSum_abs_le_Un {q : Q} {M : Nat} (hqd : 0 < q.den) (hq : Qle (Qabs q) ⟨(M : Int), 1⟩) (N : Nat) :
    Qle (Qabs (expSum q N)) ⟨((expM_U M (2 * M)).num.toNat : Int), 1⟩ := by
  have hstep : Qle (Qabs (expSum q N)) (expSumM M N) := by
    have hdiff := expSum_abs_diff_le_M hqd hq (a := 0) (b := N) (Nat.zero_le N)
    have hreg : Qeq (expSum q N) (add (Qsub (expSum q N) (expSum q 0)) (expSum q 0)) := by
      simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
    have h1 : Qle (Qabs (expSum q N))
        (add (Qabs (Qsub (expSum q N) (expSum q 0))) (Qabs (expSum q 0))) :=
      Qle_congr_left (Qabs_den_pos (add_den_pos (Qsub_den_pos (expSum_den_pos hqd N) (expSum_den_pos hqd 0))
          (expSum_den_pos hqd 0))) (Qeq_symm (Qabs_Qeq hreg))
        (Qabs_add_le (Qsub (expSum q N) (expSum q 0)) (expSum q 0))
    refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (expSum_den_pos hqd N) (expSum_den_pos hqd 0)))
        (Qabs_den_pos (expSum_den_pos hqd 0))) h1 ?_
    refine Qle_trans (add_den_pos (Qsub_den_pos (expSumM_den_pos M N) (expSumM_den_pos M 0)) Nat.one_pos)
      (Qadd_le_add hdiff (Qeq_le (show Qeq (Qabs (expSum q 0)) ⟨1, 1⟩ by rfl))) (Qeq_le ?_)
    show Qeq (add (Qsub (expSumM M N) ⟨1, 1⟩) ⟨1, 1⟩) (expSumM M N)
    simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
  refine Qle_trans (expSumM_den_pos M N) hstep ?_
  refine Qle_trans (expM_U_den_pos M (2 * M))
    (Qle_congr_left (LipS_den_pos M (N + 1)) (LipS_shift M N) (LipS_le_U M (N + 1)))
    (Qle_toNat (expM_U_num_nonneg _ _) (expM_U_den_pos _ _))

/-- **The exp functional-equation corner decays to `1/(n+1)` at a deep depth `D`**: combining the rational
    FE `expSum_add_le` with the truncation `truncCoef_QE`, once `D` exceeds the explicit threshold. -/
theorem expSum_add_decay {a b : Q} {Mx My : Nat} (ha0 : 0 ≤ a.num) (had : 0 < a.den)
    (hb0 : 0 ≤ b.num) (hbd : 0 < b.den) (hqa : Qle (Qabs a) ⟨(Mx : Int), 1⟩) (hqb : Qle (Qabs b) ⟨(My : Int), 1⟩)
    (hMxy : 0 < Mx + My) (n D : Nat)
    (hD : 2 * (n + 1) * npow (Mx + My) (2 * (Mx + My) + 1) + 2 * (Mx + My) ≤ D) :
    Qle (Qabs (Qsub (expSum (add a b) D) (mul (expSum a D) (expSum b D)))) ⟨1, n + 1⟩ :=
  Qle_trans (fct_pos _) (expSum_add_le ha0 had hb0 hbd hqa hqb D (by omega))
    (truncCoef_QE (Mx + My) 2 (n + 1) (D + 1) hMxy (by omega) (by omega))

end UOR.Bridge.F1Square.Analysis
