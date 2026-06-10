/-
F1 square — the **cos/sin angle-addition formulas** `cos(a+b) = cos a cos b − sin a sin b` and
`sin(a+b) = sin a cos b + cos a sin b` (the v0.16.0 prerequisite for the complex exponential law
`Cexp(a+b) = Cexp a · Cexp b`, hence for the tight Lipschitz bounds `|cos a − cos b| ≤ |a−b|` that
control the η-series variation `Σ|n⁻ˢ − (n+1)⁻ˢ| < ∞` — the integration-free route to `ζ` on the
critical strip).

This module builds the **formal (finite, exact) heart**: the *antidiagonal binomial identity*

    (a+b)^{2m}/(2m)!  =  Σ_{2i ≤ 2m} a^{2i}·b^{2m−2i}/((2i)!·(2m−2i)!)        [the `cos·cos` diagonal]
                       + Σ_{2i+1 ≤ 2m} a^{2i+1}·b^{2m−2i−1}/((2i+1)!·(2m−2i−1)!)  [the `sin·sin` diagonal]

which is exactly `cos(a+b)`'s degree-`2m` term reorganized into the product diagonals. It is a pure
binomial fact: each coefficient `C(2m,p)/(2m)! = 1/(p!·(2m−p)!)` (`choose_mul_fct_mul_fct`), and the
even/odd split of `p` is `Fsum_parity_split`. The convergence/reconciliation (lifting to `RaltReal`)
builds on top, mirroring `CosSinAdd` / `ExpRealAdd`.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.CosSinAdd
import F1Square.Analysis.RealPow

namespace UOR.Bridge.F1Square.Analysis

/-- **The two-variable pair term** `aᵖ·b^{2m−p}/(p!·(2m−p)!)` — the coefficient-`p` summand of the
    degree-`2m` antidiagonal (a `cos·cos` term when `p` even, a `sin·sin` term when `p` odd). -/
def pairTerm (a b : Q) (m p : Nat) : Q :=
  mul (mul (qpow a p) (qpow b (2 * m - p))) ⟨1, fct p * fct (2 * m - p)⟩

theorem pairTerm_den_pos {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m p : Nat) :
    0 < (pairTerm a b m p).den :=
  Qmul_den_pos (Qmul_den_pos (qpow_den_pos had p) (qpow_den_pos hbd _))
    (Nat.mul_pos (fct_pos _) (fct_pos _))

/-- **Per-term scaling**: the binomial term `C(2m,p)·aᵖ·b^{2m−p}` divided by `(2m)!` equals the pair
    term `aᵖ·b^{2m−p}/(p!·(2m−p)!)` (the binomial-coefficient identity `C(2m,p)/(2m)! = 1/(p!(2m−p)!)`). -/
theorem binTerm_scaled_eq {a b : Q} (m : Nat) {p : Nat} (hp : p ≤ 2 * m) :
    Qeq (mul (⟨1, fct (2 * m)⟩ : Q) (binTerm a b (2 * m) p)) (pairTerm a b m p) := by
  -- `binTerm a b (2m) p = ⟨C(2m,p),1⟩ · (aᵖ · b^{2m−p})`; scale by `1/(2m)!`. The whole thing reduces to
  -- the coefficient identity `⟨C(2m,p), (2m)!⟩ ≈ ⟨1, p!·(2m−p)!⟩` (`choose_mul_fct_mul_fct`).
  have hkeyZ : (choose (2 * m) p : Int) * (fct p : Int) * (fct (2 * m - p) : Int)
      = (fct (2 * m) : Int) := by exact_mod_cast choose_mul_fct_mul_fct hp
  show Qeq (mul (⟨1, fct (2 * m)⟩ : Q)
      (mul (⟨(choose (2 * m) p : Int), 1⟩ : Q) (mul (qpow a p) (qpow b (2 * m - p)))))
    (mul (mul (qpow a p) (qpow b (2 * m - p))) ⟨1, fct p * fct (2 * m - p)⟩)
  simp only [Qeq, mul]
  push_cast
  generalize (qpow a p).num = an
  generalize (qpow b (2 * m - p)).num = bn
  generalize ((qpow a p).den : Int) = ad
  generalize ((qpow b (2 * m - p)).den : Int) = bd
  generalize ((choose (2 * m) p : Nat) : Int) = cc at hkeyZ ⊢
  generalize ((fct p : Nat) : Int) = fp at hkeyZ ⊢
  generalize ((fct (2 * m - p) : Nat) : Int) = fq at hkeyZ ⊢
  generalize ((fct (2 * m) : Nat) : Int) = ff at hkeyZ ⊢
  rw [← hkeyZ]; ring_uor

/-- **The antidiagonal binomial identity** (the formal heart of the addition formula): for `m = m'+1`,

    `(a+b)^{2m}/(2m)!  =  Σ_{j=0}^{m'+1} a^{2j}·b^{2m−2j}/((2j)!·(2m−2j)!)`     [`cos·cos` diagonal]
                        ` + Σ_{j=0}^{m'} a^{2j+1}·b^{2m−2j−1}/((2j+1)!·(2m−2j−1)!)` [`sin·sin` diagonal].

    Pure binomial: expand `(a+b)^{2m}` (`binomial`), divide each term by `(2m)!`
    (`binTerm_scaled_eq`, the coefficient identity), then split the index by parity
    (`Fsum_parity_split`). The `sin·sin` diagonal has the even `p`-terms removed and `+1` shifted. -/
theorem addPow_div_antidiag {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m' : Nat) :
    Qeq (mul (qpow (add a b) (2 * (m' + 1))) ⟨1, fct (2 * (m' + 1))⟩)
      (add (Fsum (fun j => pairTerm a b (m' + 1) (2 * j)) (m' + 1))
           (Fsum (fun j => pairTerm a b (m' + 1) (2 * j + 1)) m')) := by
  have hbtd : ∀ i, 0 < (binTerm a b (2 * (m' + 1)) i).den := binTerm_den_pos had hbd _
  have hptd : ∀ i, 0 < (pairTerm a b (m' + 1) i).den := pairTerm_den_pos had hbd _
  have hc2m : 0 < (⟨1, fct (2 * (m' + 1))⟩ : Q).den := fct_pos _
  -- `(a+b)^{2m}·(1/(2m)!) ≈ (1/(2m)!)·Σ binTerm`.
  have h1 : Qeq (mul (qpow (add a b) (2 * (m' + 1))) ⟨1, fct (2 * (m' + 1))⟩)
      (mul (⟨1, fct (2 * (m' + 1))⟩ : Q) (Fsum (binTerm a b (2 * (m' + 1))) (2 * (m' + 1)))) :=
    Qeq_trans (Qmul_den_pos (Fsum_den_pos hbtd _) hc2m)
      (Qmul_congr (binomial had hbd _) (Qeq_refl _)) (Qmul_swap _ _)
  -- distribute the scaling into the sum, then rewrite each term to `pairTerm`.
  have h2 : Qeq (mul (⟨1, fct (2 * (m' + 1))⟩ : Q) (Fsum (binTerm a b (2 * (m' + 1))) (2 * (m' + 1))))
      (Fsum (pairTerm a b (m' + 1)) (2 * (m' + 1))) :=
    Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos hc2m (hbtd i)) _)
      (Qeq_symm (Fsum_mul_left hc2m hbtd _))
      (Fsum_congr_le (fun i hi => binTerm_scaled_eq (m' + 1) (by omega : i ≤ 2 * (m' + 1))))
  -- parity-split the index `0 ≤ p ≤ 2m = 2m'+2`.
  have h3 : Qeq (Fsum (pairTerm a b (m' + 1)) (2 * (m' + 1)))
      (add (Fsum (fun j => pairTerm a b (m' + 1) (2 * j)) (m' + 1))
           (Fsum (fun j => pairTerm a b (m' + 1) (2 * j + 1)) m')) := by
    have hsplit := Fsum_parity_split (pairTerm a b (m' + 1)) hptd m'
    rwa [show 2 * m' + 2 = 2 * (m' + 1) from by omega] at hsplit
  exact Qeq_trans (Qmul_den_pos hc2m (Fsum_den_pos hbtd _)) h1
    (Qeq_trans (Fsum_den_pos hptd _) h2 h3)

-- ===========================================================================
-- The **signed diagonal relation** `altTerm(a+b,0,m) = cos·cos-diagonal − sin·sin-diagonal`,
-- connecting the (sign-free) antidiagonal sums to the actual product diagonals of `cos`/`sin`.
-- ===========================================================================

/-- `(a²)ʲ ≈ a^{2j}`. -/
theorem qpow_sq_eq {a : Q} (had : 0 < a.den) (j : Nat) :
    Qeq (qpow (mul a a) j) (qpow a (2 * j)) := by
  rw [show 2 * j = j + j from by omega]
  exact Qeq_trans (Qmul_den_pos (qpow_den_pos had j) (qpow_den_pos had j))
    (qpow_mul_dist a a had had j) (Qeq_symm (qpow_add a had j j))

/-- **Signed power split**: `(−a²)ʲ ≈ (−1)ʲ·a^{2j}`. -/
theorem qpow_negsq {a : Q} (had : 0 < a.den) (j : Nat) :
    Qeq (qpow (neg (mul a a)) j) (mul (qpow (⟨-1, 1⟩ : Q) j) (qpow a (2 * j))) := by
  have hneg : Qeq (neg (mul a a)) (mul (⟨-1, 1⟩ : Q) (mul a a)) := by
    simp only [Qeq, neg, mul]; push_cast; ring_uor
  have hN : 0 < (neg (mul a a)).den := Nat.mul_pos had had
  have hM : 0 < (mul (⟨-1, 1⟩ : Q) (mul a a)).den := Qmul_den_pos (by decide) (Qmul_den_pos had had)
  refine Qeq_trans (qpow_den_pos hM j) (qpow_Qeq hneg j) ?_
  refine Qeq_trans (Qmul_den_pos (qpow_den_pos (by decide) j) (qpow_den_pos (Qmul_den_pos had had) j))
    (qpow_mul_dist (⟨-1, 1⟩ : Q) (mul a a) (by decide) (Qmul_den_pos had had) j) ?_
  exact Qmul_congr (Qeq_refl _) (qpow_sq_eq had j)

/-- **Paired signed powers**: `(−a²)ʲ·(−b²)^{m−j} ≈ (−1)ᵐ·a^{2j}·b^{2(m−j)}` (for `j ≤ m`). -/
theorem negsq_pair {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) {j m : Nat} (hjm : j ≤ m) :
    Qeq (mul (qpow (neg (mul a a)) j) (qpow (neg (mul b b)) (m - j)))
        (mul (qpow (⟨-1, 1⟩ : Q) m) (mul (qpow a (2 * j)) (qpow b (2 * (m - j))))) := by
  have hSa : 0 < (qpow (⟨-1, 1⟩ : Q) j).den := qpow_den_pos (by decide) j
  have hSb : 0 < (qpow (⟨-1, 1⟩ : Q) (m - j)).den := qpow_den_pos (by decide) (m - j)
  have hA : 0 < (qpow a (2 * j)).den := qpow_den_pos had (2 * j)
  have hB : 0 < (qpow b (2 * (m - j))).den := qpow_den_pos hbd (2 * (m - j))
  refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hSa hA) (Qmul_den_pos hSb hB))
    (Qmul_congr (qpow_negsq had j) (qpow_negsq hbd (m - j))) ?_
  refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hSa hSb) (Qmul_den_pos hA hB))
    (Qmul4_rearrange _ _ _ _) ?_
  refine Qmul_congr ?_ (Qeq_refl _)
  have hm : j + (m - j) = m := by omega
  have h := Qeq_symm (qpow_add (⟨-1, 1⟩ : Q) (by decide) j (m - j))
  rwa [hm] at h

/-- `(1/d₁)·(1/d₂) ≈ 1/(d₁·d₂)`. -/
private theorem mul_inv_dens (d1 d2 : Nat) : Qeq (mul (⟨1, d1⟩ : Q) ⟨1, d2⟩) ⟨1, d1 * d2⟩ := by
  show (1 * 1 : Int) * ((d1 * d2 : Nat) : Int) = (1 : Int) * ((d1 * d2 : Nat) : Int)
  generalize ((d1 * d2 : Nat) : Int) = X; ring_uor

/-- **The paired alternating-term identity** (any offset `off`): the product of the `off`-shifted
    `j`-th and `(m−j)`-th alternating terms equals `(−1)ᵐ·a^{2j}·b^{2(m−j)}/((2j+off)!·(2(m−j)+off)!)`.
    (`off = 0` gives the `cos·cos` diagonal; `off = 1` the body of the `sin·sin` diagonal.) -/
theorem altPair_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) {j m : Nat} (hjm : j ≤ m)
    (off : Nat) :
    Qeq (mul (altTerm a off j) (altTerm b off (m - j)))
        (mul (qpow (⟨-1, 1⟩ : Q) m)
          (mul (mul (qpow a (2 * j)) (qpow b (2 * (m - j))))
            ⟨1, fct (2 * j + off) * fct (2 * (m - j) + off)⟩)) := by
  have hP1 : 0 < (qpow (neg (mul a a)) j).den := qpow_den_pos (Nat.mul_pos had had) j
  have hP2 : 0 < (qpow (neg (mul b b)) (m - j)).den := qpow_den_pos (Nat.mul_pos hbd hbd) (m - j)
  have hF1 : 0 < (⟨1, fct (2 * j + off)⟩ : Q).den := fct_pos _
  have hF2 : 0 < (⟨1, fct (2 * (m - j) + off)⟩ : Q).den := fct_pos _
  have hSm : 0 < (qpow (⟨-1, 1⟩ : Q) m).den := qpow_den_pos (by decide) m
  have hA : 0 < (qpow a (2 * j)).den := qpow_den_pos had (2 * j)
  have hB : 0 < (qpow b (2 * (m - j))).den := qpow_den_pos hbd (2 * (m - j))
  simp only [altTerm]
  refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hP1 hP2) (Qmul_den_pos hF1 hF2))
    (Qmul4_rearrange _ _ _ _) ?_
  refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hSm (Qmul_den_pos hA hB))
      (Nat.mul_pos (fct_pos _) (fct_pos _) :
        0 < (⟨1, fct (2 * j + off) * fct (2 * (m - j) + off)⟩ : Q).den))
    (Qmul_congr (negsq_pair had hbd hjm) (mul_inv_dens _ _)) ?_
  exact Qeq_symm (Qmul_assoc3 _ _ _)

/-- **The `cos·cos` diagonal term** `cosTermⱼ·cosT_{m−j} ≈ (−1)ᵐ·pairTerm(2j)` (`j ≤ m`). -/
theorem cosPair_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) {j m : Nat} (hjm : j ≤ m) :
    Qeq (mul (altTerm a 0 j) (altTerm b 0 (m - j)))
        (mul (qpow (⟨-1, 1⟩ : Q) m) (pairTerm a b m (2 * j))) := by
  have he : 2 * m - 2 * j = 2 * (m - j) := by omega
  have h := altPair_eq had hbd hjm 0
  simp only [Nat.add_zero] at h
  simp only [pairTerm, he]
  exact h

/-- The `i`-th term of `sin a = a·Σ (−a²)ⁱ/(2i+1)!`. -/
def sinTerm (a : Q) (i : Nat) : Q := mul a (altTerm a 1 i)

theorem sinTerm_den_pos {a : Q} (had : 0 < a.den) (i : Nat) : 0 < (sinTerm a i).den :=
  Qmul_den_pos had (altTerm_den_pos had 1 i)

/-- **The `sin·sin` diagonal term** `sinTermⱼ·sinT_{m'−j} ≈ (−1)^{m'}·pairTerm(2j+1)` (`j ≤ m'`). -/
theorem sinPair_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) {j m' : Nat} (hjm : j ≤ m') :
    Qeq (mul (sinTerm a j) (sinTerm b (m' - j)))
        (mul (qpow (⟨-1, 1⟩ : Q) m') (pairTerm a b (m' + 1) (2 * j + 1))) := by
  have hr : 2 * (m' + 1) - (2 * j + 1) = 2 * (m' - j) + 1 := by omega
  have hAB : 0 < (mul (altTerm a 1 j) (altTerm b 1 (m' - j))).den :=
    Qmul_den_pos (altTerm_den_pos had 1 j) (altTerm_den_pos hbd 1 (m' - j))
  -- pull out the `a·b` factor, reduce the inner alternating product via `altPair_eq`.
  have hstep : Qeq (mul (sinTerm a j) (sinTerm b (m' - j)))
      (mul (mul a b) (mul (qpow (⟨-1, 1⟩ : Q) m')
        (mul (mul (qpow a (2 * j)) (qpow b (2 * (m' - j))))
          ⟨1, fct (2 * j + 1) * fct (2 * (m' - j) + 1)⟩))) := by
    refine Qeq_trans (Qmul_den_pos (Qmul_den_pos had hbd) hAB)
      (Qmul4_rearrange a (altTerm a 1 j) b (altTerm b 1 (m' - j))) ?_
    exact Qmul_congr (Qeq_refl _) (altPair_eq had hbd hjm 1)
  refine Qeq_trans ?_ hstep ?_
  · exact Qmul_den_pos (Qmul_den_pos had hbd) (Qmul_den_pos (qpow_den_pos (by decide) m')
      (Qmul_den_pos (Qmul_den_pos (qpow_den_pos had _) (qpow_den_pos hbd _))
        (Nat.mul_pos (fct_pos _) (fct_pos _))))
  -- the remaining AC rearrangement: `(a·b)·(Sm'·(A·B)·G) = Sm'·((a·A)·(b·B))·G`, with `a·A^{2j}=A^{2j+1}`.
  simp only [pairTerm, hr, qpow_succ]
  simp only [Qeq, mul]
  generalize a.num = an; generalize (a.den : Int) = ad
  generalize b.num = bn; generalize (b.den : Int) = bd
  generalize (qpow a (2 * j)).num = aA; generalize ((qpow a (2 * j)).den : Int) = aD
  generalize (qpow b (2 * (m' - j))).num = bB; generalize ((qpow b (2 * (m' - j))).den : Int) = bD
  generalize (qpow (⟨-1, 1⟩ : Q) m').num = sn; generalize ((qpow (⟨-1, 1⟩ : Q) m').den : Int) = sd
  push_cast
  generalize ((fct (2 * j + 1) : Nat) : Int) = f1
  generalize ((fct (2 * (m' - j) + 1) : Nat) : Int) = f2
  ring_uor

-- ===========================================================================
-- The **Cauchy-product partial-sum identity** `(Σf)(Σg) = Σ-diagonal + corner` (exact).
-- ===========================================================================

/-- **Product of finite sums as a double sum**: `(Σ_{i≤M} fᵢ)(Σ_{j≤N} gⱼ) ≈ Σ_{i≤M} Σ_{j≤N} fᵢ·gⱼ`. -/
theorem Fsum_mul_Fsum {f g : Nat → Q} (hf : ∀ i, 0 < (f i).den) (hg : ∀ j, 0 < (g j).den) (N : Nat) :
    ∀ M, Qeq (mul (Fsum f M) (Fsum g N))
      (Fsum (fun i => Fsum (fun j => mul (f i) (g j)) N) M)
  | 0 => Qeq_symm (Fsum_mul_left (hf 0) hg N)
  | (M + 1) => by
      have hrowd : ∀ i, 0 < (Fsum (fun j => mul (f i) (g j)) N).den :=
        fun i => Fsum_den_pos (fun j => Qmul_den_pos (hf i) (hg j)) N
      refine Qeq_trans (add_den_pos (Qmul_den_pos (Fsum_den_pos hf M) (Fsum_den_pos hg N))
          (Qmul_den_pos (hf (M + 1)) (Fsum_den_pos hg N)))
        (Qmul_add_right (Fsum f M) (f (M + 1)) (Fsum g N)) ?_
      exact Qadd_congr (Fsum_mul_Fsum hf hg N M) (Qeq_symm (Fsum_mul_left (hf (M + 1)) hg N))

/-- **The Cauchy-product partial-sum identity** (exact): `(Σ_{i≤N} fᵢ)(Σ_{j≤N} gⱼ)` equals the diagonal
    sum `Σ_{m≤N} Σ_{i≤m} fᵢ·g_{m−i}` plus the high corner `Σ_{i≤N}(Σ_{j≤N} − Σ_{j≤N−i}) fᵢ·gⱼ`. -/
theorem fsum_cauchy {f g : Nat → Q} (hf : ∀ i, 0 < (f i).den) (hg : ∀ j, 0 < (g j).den) (N : Nat) :
    Qeq (mul (Fsum f N) (Fsum g N))
      (add (Fsum (fun m => Fsum (fun i => mul (f i) (g (m - i))) m) N)
        (Fsum (fun i => Qsub (Fsum (fun j => mul (f i) (g j)) N)
          (Fsum (fun j => mul (f i) (g j)) (N - i))) N)) := by
  have hg' : ∀ i j, 0 < (mul (f i) (g j)).den := fun i j => Qmul_den_pos (hf i) (hg j)
  have htri : 0 < (Fsum (fun i => Fsum (fun j => mul (f i) (g j)) (N - i)) N).den :=
    Fsum_den_pos (fun i => Fsum_den_pos (fun j => hg' i j) (N - i)) N
  have hcor : 0 < (Fsum (fun i => Qsub (Fsum (fun j => mul (f i) (g j)) N)
      (Fsum (fun j => mul (f i) (g j)) (N - i))) N).den :=
    Fsum_den_pos (fun i => Qsub_den_pos (Fsum_den_pos (fun j => hg' i j) N)
      (Fsum_den_pos (fun j => hg' i j) (N - i))) N
  refine Qeq_trans (Fsum_den_pos (fun i => Fsum_den_pos (fun j => hg' i j) N) N)
    (Fsum_mul_Fsum hf hg N N) ?_
  refine Qeq_trans (add_den_pos htri hcor) (Fsum_square_decomp hg' N) ?_
  exact Qadd_congr (Fsum_triangle_reindex hg' N) (Qeq_refl _)

-- ===========================================================================
-- The diagonal convolutions and the **diagonal addition identity**.
-- ===========================================================================

/-- The degree-`m` `cos·cos` diagonal `Σ_{j≤m} cosTermⱼ·cosT_{m−j}`. -/
def cosConv (a b : Q) (m : Nat) : Q := Fsum (fun j => mul (altTerm a 0 j) (altTerm b 0 (m - j))) m

/-- The degree-`m'` `sin·sin` diagonal `Σ_{j≤m'} sinTermⱼ·sinT_{m'−j}`. -/
def sinConv (a b : Q) (m' : Nat) : Q := Fsum (fun j => mul (sinTerm a j) (sinTerm b (m' - j))) m'

theorem cosConv_den_pos {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m : Nat) :
    0 < (cosConv a b m).den :=
  Fsum_den_pos (fun j => Qmul_den_pos (altTerm_den_pos had 0 j) (altTerm_den_pos hbd 0 (m - j))) m

theorem sinConv_den_pos {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m' : Nat) :
    0 < (sinConv a b m').den :=
  Fsum_den_pos (fun j => Qmul_den_pos (sinTerm_den_pos had j) (sinTerm_den_pos hbd (m' - j))) m'

/-- The `cos·cos` diagonal factors as `(−1)ᵐ · Σ_j pairTerm(2j)`. -/
theorem cosConv_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m : Nat) :
    Qeq (cosConv a b m)
        (mul (qpow (⟨-1, 1⟩ : Q) m) (Fsum (fun j => pairTerm a b m (2 * j)) m)) := by
  simp only [cosConv]
  refine Qeq_trans (Fsum_den_pos (fun j => Qmul_den_pos (qpow_den_pos (by decide) m)
      (pairTerm_den_pos had hbd m _)) m)
    (Fsum_congr_le (fun j hj => cosPair_eq had hbd (by omega : j ≤ m))) ?_
  exact Fsum_mul_left (qpow_den_pos (by decide) m) (fun j => pairTerm_den_pos had hbd m _) m

/-- The `sin·sin` diagonal factors as `(−1)^{m'} · Σ_j pairTerm(2j+1)`. -/
theorem sinConv_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m' : Nat) :
    Qeq (sinConv a b m')
        (mul (qpow (⟨-1, 1⟩ : Q) m') (Fsum (fun j => pairTerm a b (m' + 1) (2 * j + 1)) m')) := by
  simp only [sinConv]
  refine Qeq_trans (Fsum_den_pos (fun j => Qmul_den_pos (qpow_den_pos (by decide) m')
      (pairTerm_den_pos had hbd (m' + 1) _)) m')
    (Fsum_congr_le (fun j hj => sinPair_eq had hbd (by omega : j ≤ m'))) ?_
  exact Fsum_mul_left (qpow_den_pos (by decide) m') (fun j => pairTerm_den_pos had hbd (m' + 1) _) m'

/-- `(−1)·x ≈ −x`. -/
private theorem neg_one_mul_eq (x : Q) : Qeq (mul (⟨-1, 1⟩ : Q) x) (neg x) := by
  simp only [Qeq, mul, neg]; push_cast; ring_uor

/-- **Cauchy product for `cos·cos`** (partial sums): `(Σcos a)(Σcos b) = Σ_{m≤N} cosConv(m) + corner`. -/
theorem cosCauchy_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (N : Nat) :
    Qeq (mul (altSum a 0 N) (altSum b 0 N))
      (add (Fsum (cosConv a b) N)
        (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a 0 i) (altTerm b 0 j)) N)
          (Fsum (fun j => mul (altTerm a 0 i) (altTerm b 0 j)) (N - i))) N)) := by
  rw [altSum_eq_Fsum, altSum_eq_Fsum]
  exact fsum_cauchy (altTerm_den_pos had 0) (altTerm_den_pos hbd 0) N

/-- **Cauchy product for `sin·sin`** (partial sums): `(Σsin a)(Σsin b) = Σ_{m≤N} sinConv(m) + corner`. -/
theorem sinCauchy_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (N : Nat) :
    Qeq (mul (Fsum (sinTerm a) N) (Fsum (sinTerm b) N))
      (add (Fsum (sinConv a b) N)
        (Fsum (fun i => Qsub (Fsum (fun j => mul (sinTerm a i) (sinTerm b j)) N)
          (Fsum (fun j => mul (sinTerm a i) (sinTerm b j)) (N - i))) N)) :=
  fsum_cauchy (sinTerm_den_pos had) (sinTerm_den_pos hbd) N

/-- **The diagonal addition identity** (`m = m'+1`): the degree-`m` term of `cos(a+b)` equals the
    `cos·cos` diagonal minus the `sin·sin` diagonal — i.e. the per-degree `cos(a+b) = cos·cos − sin·sin`.
    From the antidiagonal binomial identity (`addPow_div_antidiag`) by extracting the sign `(−1)ᵐ`
    (`qpow_negsq`) and matching the even/odd sums to the `cos·cos`/`sin·sin` diagonals
    (`cosConv_eq`/`sinConv_eq`); the `(−1)^{m'+1}` on the odd sum supplies the subtraction. -/
theorem altTerm_add_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m' : Nat) :
    Qeq (altTerm (add a b) 0 (m' + 1))
        (Qsub (cosConv a b (m' + 1)) (sinConv a b m')) := by
  have habd : 0 < (add a b).den := add_den_pos had hbd
  have hEd : 0 < (Fsum (fun j => pairTerm a b (m' + 1) (2 * j)) (m' + 1)).den :=
    Fsum_den_pos (fun j => pairTerm_den_pos had hbd _ _) _
  have hOd : 0 < (Fsum (fun j => pairTerm a b (m' + 1) (2 * j + 1)) m').den :=
    Fsum_den_pos (fun j => pairTerm_den_pos had hbd _ _) _
  have hS1d : 0 < (qpow (⟨-1, 1⟩ : Q) (m' + 1)).den := qpow_den_pos (by decide) _
  -- step 1: `altTerm(a+b,0,m) ≈ S1 · ((a+b)^{2m}/(2m)!) ≈ S1 · (E + O)`.
  have hsign : Qeq (altTerm (add a b) 0 (m' + 1))
      (mul (qpow (⟨-1, 1⟩ : Q) (m' + 1))
        (mul (qpow (add a b) (2 * (m' + 1))) ⟨1, fct (2 * (m' + 1))⟩)) := by
    show Qeq (mul (qpow (neg (mul (add a b) (add a b))) (m' + 1)) ⟨1, fct (2 * (m' + 1) + 0)⟩)
      (mul (qpow (⟨-1, 1⟩ : Q) (m' + 1))
        (mul (qpow (add a b) (2 * (m' + 1))) ⟨1, fct (2 * (m' + 1))⟩))
    simp only [Nat.add_zero]
    refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hS1d (qpow_den_pos habd _)) (fct_pos _))
      (Qmul_congr (qpow_negsq habd (m' + 1)) (Qeq_refl _)) ?_
    exact Qeq_symm (Qmul_assoc3 _ _ _)
  have hanti : Qeq (mul (qpow (add a b) (2 * (m' + 1))) ⟨1, fct (2 * (m' + 1))⟩)
      (add (Fsum (fun j => pairTerm a b (m' + 1) (2 * j)) (m' + 1))
           (Fsum (fun j => pairTerm a b (m' + 1) (2 * j + 1)) m')) :=
    addPow_div_antidiag had hbd m'
  have hstep1 : Qeq (altTerm (add a b) 0 (m' + 1))
      (add (mul (qpow (⟨-1, 1⟩ : Q) (m' + 1)) (Fsum (fun j => pairTerm a b (m' + 1) (2 * j)) (m' + 1)))
           (mul (qpow (⟨-1, 1⟩ : Q) (m' + 1)) (Fsum (fun j => pairTerm a b (m' + 1) (2 * j + 1)) m'))) :=
    Qeq_trans (Qmul_den_pos hS1d (Qmul_den_pos (qpow_den_pos habd _) (fct_pos _))) hsign
      (Qeq_trans (Qmul_den_pos hS1d (add_den_pos hEd hOd)) (Qmul_congr (Qeq_refl _) hanti)
        (Qmul_add_left _ _ _))
  -- step 2: `S1·E ≈ cosConv`, and `S1·O ≈ −sinConv`.
  have hcos : Qeq (mul (qpow (⟨-1, 1⟩ : Q) (m' + 1))
      (Fsum (fun j => pairTerm a b (m' + 1) (2 * j)) (m' + 1))) (cosConv a b (m' + 1)) :=
    Qeq_symm (cosConv_eq had hbd (m' + 1))
  have hsin : Qeq (mul (qpow (⟨-1, 1⟩ : Q) (m' + 1))
      (Fsum (fun j => pairTerm a b (m' + 1) (2 * j + 1)) m')) (neg (sinConv a b m')) := by
    -- `S1 = (−1)·(−1)^{m'}`, so `S1·O = (−1)·((−1)^{m'}·O) ≈ (−1)·sinConv ≈ −sinConv`.
    rw [show qpow (⟨-1, 1⟩ : Q) (m' + 1) = mul (⟨-1, 1⟩ : Q) (qpow (⟨-1, 1⟩ : Q) m') from qpow_succ _ m']
    refine Qeq_trans (Qmul_den_pos (by decide) (Qmul_den_pos (qpow_den_pos (by decide) m') hOd))
      (Qeq_symm (Qmul_assoc3 _ _ _)) ?_
    refine Qeq_trans (Qmul_den_pos (by decide) (sinConv_den_pos had hbd m'))
      (Qmul_congr (Qeq_refl _) (Qeq_symm (sinConv_eq had hbd m'))) ?_
    exact neg_one_mul_eq _
  -- combine: `add (S1·E) (S1·O) ≈ add cosConv (−sinConv) = Qsub cosConv sinConv`.
  refine Qeq_trans (add_den_pos (Qmul_den_pos hS1d hEd) (Qmul_den_pos hS1d hOd)) hstep1 ?_
  exact Qadd_congr hcos hsin

-- ===========================================================================
-- The **two-variable corner bound** `|corner(2K+1)| → 0` (Mertens split; the absolute-convergence
-- step that makes `(Σf)(Σg) → product` and the diagonal sum converge). Mirrors `CosSinAdd`'s
-- same-variable `altCorner_mertens`, with the `i`-factor from series `a` and the gap from series `b`.
-- ===========================================================================

/-- **Factored two-variable corner**: factor `altTerm a off i` out of each row of the corner. -/
theorem altCorner_factored2 {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (off N : Nat) :
    Qeq (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a off i) (altTerm b off j)) N)
          (Fsum (fun j => mul (altTerm a off i) (altTerm b off j)) (N - i))) N)
      (Fsum (fun i => mul (altTerm a off i)
          (Qsub (Fsum (altTerm b off) N) (Fsum (altTerm b off) (N - i)))) N) := by
  have hbt : ∀ j, 0 < (altTerm b off j).den := altTerm_den_pos hbd off
  refine Fsum_congr (fun i => ?_) N
  exact Qeq_trans
    (Qsub_den_pos (Qmul_den_pos (altTerm_den_pos had off i) (Fsum_den_pos hbt N))
      (Qmul_den_pos (altTerm_den_pos had off i) (Fsum_den_pos hbt (N - i))))
    (QsubCongr (Fsum_mul_left (altTerm_den_pos had off i) hbt N)
      (Fsum_mul_left (altTerm_den_pos had off i) hbt (N - i)))
    (Qeq_symm (Qmul_sub_distrib (altTerm a off i) (Fsum (altTerm b off) N)
      (Fsum (altTerm b off) (N - i))))

/-- `|corner| ≤ Σᵢ |altTerm a i · (Σcos b N − Σcos b (N−i))|`. -/
theorem altCorner_abs_le2 {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (off N : Nat) :
    Qle (Qabs (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a off i) (altTerm b off j)) N)
          (Fsum (fun j => mul (altTerm a off i) (altTerm b off j)) (N - i))) N))
      (Fsum (fun i => Qabs (mul (altTerm a off i)
          (Qsub (Fsum (altTerm b off) N) (Fsum (altTerm b off) (N - i))))) N) := by
  have hbt : ∀ j, 0 < (altTerm b off j).den := altTerm_den_pos hbd off
  have hh : ∀ i, 0 < (mul (altTerm a off i)
      (Qsub (Fsum (altTerm b off) N) (Fsum (altTerm b off) (N - i)))).den :=
    fun i => Qmul_den_pos (altTerm_den_pos had off i)
      (Qsub_den_pos (Fsum_den_pos hbt N) (Fsum_den_pos hbt (N - i)))
  exact Qle_congr_left (Qabs_den_pos (Fsum_den_pos hh N))
    (Qeq_symm (Qabs_Qeq (altCorner_factored2 had hbd off N))) (Fsum_abs_le hh N)

/-- **The two-variable Mertens corner bound** at `N = 2K+1` (for `M` bounding both `|a|,|b|`, `2M² ≤ K+2`):
    `|corner(2K+1)| ≤ U·(4(M²)^{K+2}/(K+2)!) + (2(M²)^{K+1}/(K+1)!)·U` — both summands `→ 0` as `K → ∞`.
    Low block (`i ≤ K`): the gap is the deep `b`-tail (`altTail_deep_le`), `Σ|altTerm a i| ≤ U`
    (`altAbsSum_le_U`). High block (`i = K+1+i'`): `|altTerm a (K+1+i')|` is the small `a`-tail
    (`altAbsTail_le`), the gap `≤ U` (`altGap_le_U`). -/
theorem cornerMertens2 {a b : Q} {M : Nat} (had : 0 < a.den) (hbd : 0 < b.den)
    (ha : Qle (Qabs a) ⟨(M : Int), 1⟩) (hb : Qle (Qabs b) ⟨(M : Int), 1⟩) (off K : Nat)
    (hK : 2 * (M * M) ≤ K + 2) :
    Qle (Qabs (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a off i) (altTerm b off j)) (2 * K + 1))
          (Fsum (fun j => mul (altTerm a off i) (altTerm b off j)) (2 * K + 1 - i))) (2 * K + 1)))
      (add (mul (expM_U (M * M) (2 * (M * M))) ⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩)
        (mul ⟨(2 * npow (M * M) (K + 1) : Int), fct (K + 1)⟩ (expM_U (M * M) (2 * (M * M))))) := by
  have hat : ∀ i, 0 < (altTerm a off i).den := altTerm_den_pos had off
  have hbt : ∀ j, 0 < (altTerm b off j).den := altTerm_den_pos hbd off
  have htd : ∀ i, 0 < (Qsub (Fsum (altTerm b off) (2 * K + 1)) (Fsum (altTerm b off) (2 * K + 1 - i))).den :=
    fun i => Qsub_den_pos (Fsum_den_pos hbt (2 * K + 1)) (Fsum_den_pos hbt (2 * K + 1 - i))
  have hh : ∀ i, 0 < (Qabs (mul (altTerm a off i)
      (Qsub (Fsum (altTerm b off) (2 * K + 1)) (Fsum (altTerm b off) (2 * K + 1 - i))))).den :=
    fun i => Qabs_den_pos (Qmul_den_pos (hat i) (htd i))
  have hCnn : (0 : Int) ≤ (4 * npow (M * M) (K + 2) : Int) := Int.ofNat_nonneg _
  have hUnn : (0 : Int) ≤ (expM_U (M * M) (2 * (M * M))).num := expM_U_num_nonneg _ _
  -- low block `i ≤ K`: `|altTerm a i|·(deep b-tail ≤ 4(M²)^{K+2}/(K+2)!)`, summed `≤ U·(…)`.
  have hlow : Qle (Fsum (fun i => Qabs (mul (altTerm a off i)
        (Qsub (Fsum (altTerm b off) (2 * K + 1)) (Fsum (altTerm b off) (2 * K + 1 - i))))) K)
      (mul (expM_U (M * M) (2 * (M * M))) ⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩) := by
    have hmid : Qle (Fsum (fun i => Qabs (mul (altTerm a off i)
          (Qsub (Fsum (altTerm b off) (2 * K + 1)) (Fsum (altTerm b off) (2 * K + 1 - i))))) K)
        (Fsum (fun i => mul (Qabs (altTerm a off i))
          (⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩ : Q)) K) :=
      Fsum_le_congr (fun i hi => by
        rw [Qabs_mul]
        exact Qmul_le_mul_left (Qabs_num_nonneg _) (altTail_deep_le hbd hb off K i hi (by omega)))
    exact Qle_trans (Fsum_den_pos (fun i => Qmul_den_pos (Qabs_den_pos (hat i)) (fct_pos _)) K) hmid
      (Qle_trans (Qmul_den_pos (Fsum_den_pos (fun i => Qabs_den_pos (hat i)) K) (fct_pos _))
        (Qeq_le (Qeq_symm (Fsum_mul_const_right (fct_pos _) (fun i => Qabs_den_pos (hat i)) K)))
        (Qmul_le_mul_right hCnn (altAbsSum_le_U had ha off K)))
  -- high block `i = K+1+i'`: `|altTerm a (K+1+i')| (small a-tail)·(gap ≤ U)`, summed `≤ (…)·U`.
  have hhigh : Qle (Fsum (fun i' => Qabs (mul (altTerm a off (K + 1 + i'))
        (Qsub (Fsum (altTerm b off) (2 * K + 1)) (Fsum (altTerm b off) (2 * K + 1 - (K + 1 + i')))))) K)
      (mul ⟨(2 * npow (M * M) (K + 1) : Int), fct (K + 1)⟩ (expM_U (M * M) (2 * (M * M)))) := by
    have hmid : Qle (Fsum (fun i' => Qabs (mul (altTerm a off (K + 1 + i'))
          (Qsub (Fsum (altTerm b off) (2 * K + 1)) (Fsum (altTerm b off) (2 * K + 1 - (K + 1 + i')))))) K)
        (Fsum (fun i' => mul (Qabs (altTerm a off (K + 1 + i')))
          (expM_U (M * M) (2 * (M * M)))) K) :=
      Fsum_le_congr (fun i' _ => by
        rw [Qabs_mul]
        exact Qmul_le_mul_left (Qabs_num_nonneg _)
          (altGap_le_U hbd hb off (a := 2 * K + 1 - (K + 1 + i')) (b := 2 * K + 1) (by omega)))
    exact Qle_trans (Fsum_den_pos (fun i' => Qmul_den_pos (Qabs_den_pos (hat (K + 1 + i')))
        (expM_U_den_pos (M * M) (2 * (M * M)))) K) hmid
      (Qle_trans (Qmul_den_pos (Fsum_den_pos (fun i' => Qabs_den_pos (hat (K + 1 + i'))) K)
        (expM_U_den_pos (M * M) (2 * (M * M))))
        (Qeq_le (Qeq_symm (Fsum_mul_const_right (expM_U_den_pos (M * M) (2 * (M * M)))
          (fun i' => Qabs_den_pos (hat (K + 1 + i'))) K)))
        (Qmul_le_mul_right hUnn (altAbsTail_le had ha off K K hK)))
  refine Qle_trans (Fsum_den_pos hh (2 * K + 1)) (altCorner_abs_le2 had hbd off (2 * K + 1)) ?_
  refine Qle_trans (add_den_pos (Fsum_den_pos hh K)
      (Fsum_den_pos (fun i' => hh (K + 1 + i')) K)) (Qeq_le (Fsum_split_at _ hh K)) ?_
  exact Qadd_le_add hlow hhigh

-- ===========================================================================
-- The **partial-sum diagonal identity** `altSum(a+b,0,N) = ΣcosConv − ΣsinConv` (summing the diagonal).
-- ===========================================================================

/-- `(A−B)+(c−d) ≈ (A+c)−(B+d)`. -/
private theorem Qadd_sub_sub (A B c d : Q) :
    Qeq (add (Qsub A B) (Qsub c d)) (Qsub (add A c) (add B d)) := by
  simp only [Qeq, Qsub, add, neg]; push_cast
  generalize A.num = an; generalize (A.den : Int) = ad
  generalize B.num = bn; generalize (B.den : Int) = bd
  generalize c.num = cn; generalize (c.den : Int) = cd
  generalize d.num = dn; generalize (d.den : Int) = dd
  ring_uor

/-- `A+(c−d) ≈ (A+c)−d`. -/
private theorem Qadd_sub_assoc (A c d : Q) : Qeq (add A (Qsub c d)) (Qsub (add A c) d) := by
  simp only [Qeq, Qsub, add, neg]; push_cast
  generalize A.num = an; generalize (A.den : Int) = ad
  generalize c.num = cn; generalize (c.den : Int) = cd
  generalize d.num = dn; generalize (d.den : Int) = dd
  ring_uor

/-- **The partial-sum diagonal identity**: `altSum(a+b,0,N+1) = Σ_{m≤N+1} cosConv(m) − Σ_{m≤N} sinConv(m)`
    — summing the per-degree `altTerm_add_eq` over `m ≤ N+1` (the `m=0` term is `cosConv 0`, and the
    `sin·sin` diagonals reindex by `−1`). This is the `Q`-level partial-sum form of `cos(a+b) =
    cos a cos b − sin a sin b`; the `Real` reconciliation (corner→0) builds on top. -/
theorem altSum_add_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) :
    ∀ N, Qeq (altSum (add a b) 0 (N + 1))
      (Qsub (Fsum (cosConv a b) (N + 1)) (Fsum (sinConv a b) N))
  | 0 => by
      have hbase : Qeq (altTerm (add a b) 0 0) (cosConv a b 0) := by
        simp only [cosConv, Fsum, altTerm, qpow]; decide
      have h1 := altTerm_add_eq had hbd 0
      refine Qeq_trans (add_den_pos (cosConv_den_pos had hbd 0)
          (Qsub_den_pos (cosConv_den_pos had hbd 1) (sinConv_den_pos had hbd 0)))
        (Qadd_congr hbase h1) (Qadd_sub_assoc _ _ _)
  | (N + 1) => by
      have ih := altSum_add_eq had hbd N
      have hstep := altTerm_add_eq had hbd (N + 1)
      have hCd : ∀ m, 0 < (cosConv a b m).den := fun m => cosConv_den_pos had hbd m
      have hSd : ∀ m, 0 < (sinConv a b m).den := fun m => sinConv_den_pos had hbd m
      -- `altSum(…,N+2) = altSum(…,N+1) + altTerm(…,N+2) ≈ (Σcos − Σsin) + (cosConv − sinConv)`.
      refine Qeq_trans (add_den_pos (Qsub_den_pos (Fsum_den_pos hCd (N + 1)) (Fsum_den_pos hSd N))
          (Qsub_den_pos (hCd (N + 2)) (hSd (N + 1))))
        (Qadd_congr ih hstep) (Qadd_sub_sub _ _ _ _)

-- ===========================================================================
-- The **`sinConv` top-diagonal bound** `|sinConv N| ≤ M²·(2M²)^N/N! → 0` (the boundary diagonal vanishes).
-- ===========================================================================

/-- `M·M = M²` as a rational. -/
private theorem MM_eq (M : Nat) : Qeq (mul (⟨(M : Int), 1⟩ : Q) ⟨(M : Int), 1⟩) ⟨(M * M : Int), 1⟩ := by
  simp only [Qeq, mul]

/-- `|sinTermⱼ| ≤ M·(M²)ʲ/j!` (for `|a| ≤ M`). -/
theorem sinTerm_abs_le {a : Q} {M : Nat} (had : 0 < a.den) (ha : Qle (Qabs a) ⟨(M : Int), 1⟩)
    (j : Nat) : Qle (Qabs (sinTerm a j)) (mul (⟨(M : Int), 1⟩ : Q) (expTerm (⟨(M * M : Int), 1⟩ : Q) j)) := by
  rw [sinTerm, Qabs_mul]
  exact Qmul_le_mul (Qabs_den_pos had) Nat.one_pos (Qabs_den_pos (altTerm_den_pos had 1 j))
    (Qabs_num_nonneg _) (Qabs_num_nonneg _) ha (altTerm_abs_le_exp had ha 1 j)

/-- **The `sin·sin` top-diagonal bound**: `|sinConv N| ≤ M²·(2M²)^N/N!` (for `M` bounding `|a|,|b|`),
    which `→ 0` as `N → ∞`. Each term `|sinTermⱼ·sinT_{N−j}| ≤ M²·(M²)ʲ/j!·(M²)^{N−j}/(N−j)!`; summed
    (`expTerm_conv`) it is `M²·expTerm(2M²)(N)`. -/
theorem sinConv_abs_le {a b : Q} {M : Nat} (had : 0 < a.den) (hbd : 0 < b.den)
    (ha : Qle (Qabs a) ⟨(M : Int), 1⟩) (hb : Qle (Qabs b) ⟨(M : Int), 1⟩) (N : Nat) :
    Qle (Qabs (sinConv a b N))
      (mul (⟨(M * M : Int), 1⟩ : Q) (expTerm (add (⟨(M * M : Int), 1⟩ : Q) ⟨(M * M : Int), 1⟩) N)) := by
  have heT : ∀ k, 0 < (expTerm (⟨(M * M : Int), 1⟩ : Q) k).den := fun k => expTerm_den_pos Nat.one_pos k
  have hMeT : ∀ k, 0 < (mul (⟨(M : Int), 1⟩ : Q) (expTerm (⟨(M * M : Int), 1⟩ : Q) k)).den :=
    fun k => Qmul_den_pos Nat.one_pos (heT k)
  have hstd : ∀ j, 0 < (mul (sinTerm a j) (sinTerm b (N - j))).den :=
    fun j => Qmul_den_pos (sinTerm_den_pos had j) (sinTerm_den_pos hbd (N - j))
  simp only [sinConv]
  -- step 1: `|sinConv N| ≤ Σ |sinTermⱼ·sinT_{N−j}|`.
  refine Qle_trans (Fsum_den_pos (fun j => Qabs_den_pos (hstd j)) N)
    (Fsum_abs_le hstd N) ?_
  -- step 2: per term `≤ (M·eTⱼ)(M·eT_{N−j})`, then sum.
  refine Qle_trans (Fsum_den_pos (fun j => Qmul_den_pos (hMeT j) (hMeT (N - j))) N)
    (Fsum_le_congr (fun j _ => by
      rw [Qabs_mul]
      exact Qmul_le_mul (Qabs_den_pos (sinTerm_den_pos had j)) (hMeT j)
        (Qabs_den_pos (sinTerm_den_pos hbd (N - j))) (Qabs_num_nonneg _) (Qabs_num_nonneg _)
        (sinTerm_abs_le had ha j) (sinTerm_abs_le hbd hb (N - j)))) ?_
  -- step 3: `Σ (M·eTⱼ)(M·eT_{N−j}) ≈ M²·Σ eTⱼ·eT_{N−j} = M²·expTerm(2M²)(N)`.
  have hfactor : Qeq (Fsum (fun j => mul (mul (⟨(M : Int), 1⟩ : Q) (expTerm (⟨(M * M : Int), 1⟩ : Q) j))
        (mul (⟨(M : Int), 1⟩ : Q) (expTerm (⟨(M * M : Int), 1⟩ : Q) (N - j)))) N)
      (mul (⟨(M * M : Int), 1⟩ : Q)
        (Fsum (fun j => mul (expTerm (⟨(M * M : Int), 1⟩ : Q) j)
          (expTerm (⟨(M * M : Int), 1⟩ : Q) (N - j))) N)) := by
    refine Qeq_trans (Fsum_den_pos (fun j => Qmul_den_pos Nat.one_pos
        (Qmul_den_pos (heT j) (heT (N - j)))) N)
      (Fsum_congr (fun j => Qeq_trans (Qmul_den_pos (Qmul_den_pos Nat.one_pos Nat.one_pos)
          (Qmul_den_pos (heT j) (heT (N - j))))
        (Qmul4_rearrange (⟨(M : Int), 1⟩ : Q) (expTerm (⟨(M * M : Int), 1⟩ : Q) j)
          (⟨(M : Int), 1⟩ : Q) (expTerm (⟨(M * M : Int), 1⟩ : Q) (N - j)))
        (Qmul_congr (MM_eq M) (Qeq_refl _))) N) ?_
    exact Fsum_mul_left Nat.one_pos (fun j => Qmul_den_pos (heT j) (heT (N - j))) N
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Fsum_den_pos (fun j => Qmul_den_pos (heT j) (heT (N - j))) N))
    (Qeq_le hfactor) ?_
  exact Qeq_le (Qmul_congr (Qeq_refl _)
    (expTerm_conv (x := (⟨(M * M : Int), 1⟩ : Q)) (y := (⟨(M * M : Int), 1⟩ : Q)) Nat.one_pos Nat.one_pos N))

-- ===========================================================================
-- The **residual identity** `altSum(a+b) − (cos·cos − sin·sin partials) = sinConv N − corner_cos + corner_sin`,
-- whose RHS is a sum of terms that each `→ 0` (the gateway to the `Real` reconciliation).
-- ===========================================================================

/-- The `cos·cos` Cauchy-product corner at depth `N`. -/
def cornerCos (a b : Q) (N : Nat) : Q :=
  Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a 0 i) (altTerm b 0 j)) N)
    (Fsum (fun j => mul (altTerm a 0 i) (altTerm b 0 j)) (N - i))) N

/-- The `sin·sin` Cauchy-product corner at depth `N`. -/
def cornerSin (a b : Q) (N : Nat) : Q :=
  Fsum (fun i => Qsub (Fsum (fun j => mul (sinTerm a i) (sinTerm b j)) N)
    (Fsum (fun j => mul (sinTerm a i) (sinTerm b j)) (N - i))) N

/-- `(C−Sp) − ((C+cc) − ((Sp+sN)+cs)) ≈ sN + (cs−cc)`. -/
private theorem resid_rearrange (C Sp sN cc cs : Q) :
    Qeq (Qsub (Qsub C Sp) (Qsub (add C cc) (add (add Sp sN) cs)))
        (add sN (Qsub cs cc)) := by
  simp only [Qeq, Qsub, add, neg]; push_cast
  generalize C.num = cn; generalize (C.den : Int) = cd
  generalize Sp.num = spn; generalize (Sp.den : Int) = spd
  generalize sN.num = snn; generalize (sN.den : Int) = snd
  generalize cc.num = ccn; generalize (cc.den : Int) = ccd
  generalize cs.num = csn; generalize (cs.den : Int) = csd
  ring_uor

/-- **The residual identity**: `altSum(a+b,0,N+1) − (Σcos a · Σcos b − Σsin a · Σsin b) =
    sinConv(N+1) + (cornerSin − cornerCos)`. Exact combination of `altSum_add_eq`, `cosCauchy_eq`,
    `sinCauchy_eq` (using `Σ_{≤N+1}sinConv − Σ_{≤N}sinConv = sinConv(N+1)`). Every term on the RHS
    `→ 0` (`cornerMertens2`, `sinConv_abs_le`), so `cos(a+b) = cos a cos b − sin a sin b` in the limit. -/
theorem cosAdd_resid_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (N : Nat) :
    Qeq (Qsub (altSum (add a b) 0 (N + 1))
          (Qsub (mul (altSum a 0 (N + 1)) (altSum b 0 (N + 1)))
                (mul (Fsum (sinTerm a) (N + 1)) (Fsum (sinTerm b) (N + 1)))))
        (add (sinConv a b (N + 1)) (Qsub (cornerSin a b (N + 1)) (cornerCos a b (N + 1)))) := by
  have hCd : ∀ m, 0 < (cosConv a b m).den := fun m => cosConv_den_pos had hbd m
  have hSd : ∀ m, 0 < (sinConv a b m).den := fun m => sinConv_den_pos had hbd m
  have hccd : 0 < (cornerCos a b (N + 1)).den :=
    Fsum_den_pos (fun i => Qsub_den_pos
      (Fsum_den_pos (fun j => Qmul_den_pos (altTerm_den_pos had 0 i) (altTerm_den_pos hbd 0 j)) _)
      (Fsum_den_pos (fun j => Qmul_den_pos (altTerm_den_pos had 0 i) (altTerm_den_pos hbd 0 j)) _)) _
  have hcsd : 0 < (cornerSin a b (N + 1)).den :=
    Fsum_den_pos (fun i => Qsub_den_pos
      (Fsum_den_pos (fun j => Qmul_den_pos (sinTerm_den_pos had i) (sinTerm_den_pos hbd j)) _)
      (Fsum_den_pos (fun j => Qmul_den_pos (sinTerm_den_pos had i) (sinTerm_den_pos hbd j)) _)) _
  refine Qeq_trans (Qsub_den_pos (Qsub_den_pos (Fsum_den_pos hCd (N + 1)) (Fsum_den_pos hSd N))
      (Qsub_den_pos (add_den_pos (Fsum_den_pos hCd (N + 1)) hccd)
        (add_den_pos (Fsum_den_pos hSd (N + 1)) hcsd)))
    (QsubCongr (altSum_add_eq had hbd N) (QsubCongr (cosCauchy_eq had hbd (N + 1))
      (sinCauchy_eq had hbd (N + 1)))) ?_
  exact resid_rearrange (Fsum (cosConv a b) (N + 1)) (Fsum (sinConv a b) N)
    (sinConv a b (N + 1)) (cornerCos a b (N + 1)) (cornerSin a b (N + 1))

-- ===========================================================================
-- The **assembled decay bound** `|altSum(a+b) − (cos·cos − sin·sin partial)| → 0` at `N = 2K+1`.
-- ===========================================================================

/-- **Factor `a·b` out of `cornerSin`**: `cornerSin a b N = (a·b)·(off=1 alternating corner)`, reducing
    the `sin·sin` corner to the `altTerm`-form corner that `cornerMertens2` (`off = 1`) bounds. -/
theorem cornerSin_factored {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (N : Nat) :
    Qeq (cornerSin a b N)
      (mul (mul a b) (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 1 j)) N)
        (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 1 j)) (N - i))) N)) := by
  have hat1 : ∀ i, 0 < (altTerm a 1 i).den := altTerm_den_pos had 1
  have hbt1 : ∀ j, 0 < (altTerm b 1 j).den := altTerm_den_pos hbd 1
  have habd : 0 < (mul a b).den := Qmul_den_pos had hbd
  have haltd : ∀ i j, 0 < (mul (altTerm a 1 i) (altTerm b 1 j)).den :=
    fun i j => Qmul_den_pos (hat1 i) (hbt1 j)
  have hsubd : ∀ i, 0 < (Qsub (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 1 j)) N)
      (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 1 j)) (N - i))).den :=
    fun i => Qsub_den_pos (Fsum_den_pos (fun j => haltd i j) N) (Fsum_den_pos (fun j => haltd i j) (N - i))
  have hsterm : ∀ i j, Qeq (mul (sinTerm a i) (sinTerm b j))
      (mul (mul a b) (mul (altTerm a 1 i) (altTerm b 1 j))) := fun i j => by
    rw [sinTerm, sinTerm]; exact Qmul4_rearrange a (altTerm a 1 i) b (altTerm b 1 j)
  have hrow : ∀ i K, Qeq (Fsum (fun j => mul (sinTerm a i) (sinTerm b j)) K)
      (mul (mul a b) (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 1 j)) K)) := fun i K =>
    Qeq_trans (Fsum_den_pos (fun j => Qmul_den_pos habd (haltd i j)) K)
      (Fsum_congr (fun j => hsterm i j) K) (Fsum_mul_left habd (fun j => haltd i j) K)
  simp only [cornerSin]
  refine Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos habd (hsubd i)) N)
    (Fsum_congr (fun i => Qeq_trans
      (Qsub_den_pos (Qmul_den_pos habd (Fsum_den_pos (fun j => haltd i j) N))
        (Qmul_den_pos habd (Fsum_den_pos (fun j => haltd i j) (N - i))))
      (QsubCongr (hrow i N) (hrow i (N - i)))
      (Qeq_symm (Qmul_sub_distrib (mul a b)
        (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 1 j)) N)
        (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 1 j)) (N - i))))) N)
    (Fsum_mul_left habd hsubd N)

/-- `|a·b| ≤ M²` (for `|a|,|b| ≤ M`). -/
theorem Qabs_mul_le_MM {a b : Q} {M : Nat} (had : 0 < a.den) (hbd : 0 < b.den)
    (ha : Qle (Qabs a) ⟨(M : Int), 1⟩) (hb : Qle (Qabs b) ⟨(M : Int), 1⟩) :
    Qle (Qabs (mul a b)) (⟨(M * M : Int), 1⟩ : Q) := by
  rw [Qabs_mul]
  exact Qle_trans (Qmul_den_pos Nat.one_pos Nat.one_pos)
    (Qmul_le_mul (Qabs_den_pos had) Nat.one_pos (Qabs_den_pos hbd) (Qabs_num_nonneg _)
      (Qabs_num_nonneg _) ha hb) (Qeq_le (MM_eq M))

/-- **Bound on the `sin·sin` corner**: `|cornerSin(2K+1)| ≤ M²·(Mertens bound)` (via `cornerSin_factored`
    + `cornerMertens2` at `off = 1`), which `→ 0` as `K → ∞`. -/
theorem cornerSin_le {a b : Q} {M : Nat} (had : 0 < a.den) (hbd : 0 < b.den)
    (ha : Qle (Qabs a) ⟨(M : Int), 1⟩) (hb : Qle (Qabs b) ⟨(M : Int), 1⟩) (K : Nat)
    (hK : 2 * (M * M) ≤ K + 2) :
    Qle (Qabs (cornerSin a b (2 * K + 1)))
      (mul (⟨(M * M : Int), 1⟩ : Q)
        (add (mul (expM_U (M * M) (2 * (M * M))) ⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩)
          (mul ⟨(2 * npow (M * M) (K + 1) : Int), fct (K + 1)⟩ (expM_U (M * M) (2 * (M * M)))))) := by
  have haltd : ∀ i j, 0 < (mul (altTerm a 1 i) (altTerm b 1 j)).den :=
    fun i j => Qmul_den_pos (altTerm_den_pos had 1 i) (altTerm_den_pos hbd 1 j)
  have hcornerd : 0 < (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 1 j)) (2 * K + 1))
      (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 1 j)) (2 * K + 1 - i))) (2 * K + 1)).den :=
    Fsum_den_pos (fun i => Qsub_den_pos (Fsum_den_pos (fun j => haltd i j) _)
      (Fsum_den_pos (fun j => haltd i j) _)) _
  refine Qle_congr_left (Qabs_den_pos (Qmul_den_pos (Qmul_den_pos had hbd) hcornerd))
    (Qeq_symm (Qabs_Qeq (cornerSin_factored had hbd (2 * K + 1)))) ?_
  rw [Qabs_mul]
  exact Qmul_le_mul (Qabs_den_pos (Qmul_den_pos had hbd)) Nat.one_pos (Qabs_den_pos hcornerd)
    (Qabs_num_nonneg _) (Qabs_num_nonneg _) (Qabs_mul_le_MM had hbd ha hb)
    (cornerMertens2 had hbd ha hb 1 K hK)

/-- **The assembled decay bound** at `N = 2K+1`: `|altSum(a+b,0,2K+1) − (Σcos a·Σcos b − Σsin a·Σsin b)|`
    is `≤` the sum of the three vanishing bounds (`sinConv_abs_le` + `cornerSin_le` + `cornerMertens2`),
    each `→ 0` as `K → ∞`. The residual identity (`cosAdd_resid_eq`) + triangle inequality. This is the
    `Q`-level statement of `cos(a+b) = cos a cos b − sin a sin b` with an explicit modulus of convergence. -/
theorem cosAdd_decay_le {a b : Q} {M : Nat} (had : 0 < a.den) (hbd : 0 < b.den)
    (ha : Qle (Qabs a) ⟨(M : Int), 1⟩) (hb : Qle (Qabs b) ⟨(M : Int), 1⟩) (K : Nat)
    (hK : 2 * (M * M) ≤ K + 2) :
    Qle (Qabs (Qsub (altSum (add a b) 0 (2 * K + 1))
          (Qsub (mul (altSum a 0 (2 * K + 1)) (altSum b 0 (2 * K + 1)))
                (mul (Fsum (sinTerm a) (2 * K + 1)) (Fsum (sinTerm b) (2 * K + 1))))))
      (add (mul (⟨(M * M : Int), 1⟩ : Q) (expTerm (add (⟨(M * M : Int), 1⟩ : Q) ⟨(M * M : Int), 1⟩) (2 * K + 1)))
        (add (mul (⟨(M * M : Int), 1⟩ : Q)
              (add (mul (expM_U (M * M) (2 * (M * M))) ⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩)
                (mul ⟨(2 * npow (M * M) (K + 1) : Int), fct (K + 1)⟩ (expM_U (M * M) (2 * (M * M))))))
          (add (mul (expM_U (M * M) (2 * (M * M))) ⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩)
            (mul ⟨(2 * npow (M * M) (K + 1) : Int), fct (K + 1)⟩ (expM_U (M * M) (2 * (M * M))))))) := by
  have hsd : 0 < (sinConv a b (2 * K + 1)).den := sinConv_den_pos had hbd _
  have hccd : 0 < (cornerCos a b (2 * K + 1)).den :=
    Fsum_den_pos (fun i => Qsub_den_pos
      (Fsum_den_pos (fun j => Qmul_den_pos (altTerm_den_pos had 0 i) (altTerm_den_pos hbd 0 j)) _)
      (Fsum_den_pos (fun j => Qmul_den_pos (altTerm_den_pos had 0 i) (altTerm_den_pos hbd 0 j)) _)) _
  have hcsd : 0 < (cornerSin a b (2 * K + 1)).den :=
    Fsum_den_pos (fun i => Qsub_den_pos
      (Fsum_den_pos (fun j => Qmul_den_pos (sinTerm_den_pos had i) (sinTerm_den_pos hbd j)) _)
      (Fsum_den_pos (fun j => Qmul_den_pos (sinTerm_den_pos had i) (sinTerm_den_pos hbd j)) _)) _
  refine Qle_trans (Qabs_den_pos (add_den_pos hsd (Qsub_den_pos hcsd hccd)))
    (Qeq_le (Qabs_Qeq (cosAdd_resid_eq had hbd (2 * K)))) ?_
  refine Qle_trans (add_den_pos (Qabs_den_pos hsd) (add_den_pos (Qabs_den_pos hcsd)
      (Qabs_den_pos (neg_den_pos hccd))))
    (Qabs_add3_le (sinConv a b (2 * K + 1)) (cornerSin a b (2 * K + 1))
      (neg (cornerCos a b (2 * K + 1))) hsd hcsd (neg_den_pos hccd)) ?_
  rw [Qabs_neg]
  exact Qadd_le_add (sinConv_abs_le had hbd ha hb (2 * K + 1))
    (Qadd_le_add (cornerSin_le had hbd ha hb K hK) (cornerMertens2 had hbd ha hb 0 K hK))

end UOR.Bridge.F1Square.Analysis
