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

/-- Bridges `cosAdd_decay_le`'s `BOUND` (`↑M·↑M` scalar, order `sinB,cornerSin,cornerCos`) to
    `altErr_bound_decay`'s LHS (`↑(M·M)` scalar, order `sinB,cornerCos,cornerSin`) — a cast + commute. -/
private theorem decay_bridge (M : Nat) (E MERT : Q) :
    Qeq (add (mul (⟨(M * M : Int), 1⟩ : Q) E) (add (mul (⟨(M * M : Int), 1⟩ : Q) MERT) MERT))
        (add (mul (⟨((M * M : Nat) : Int), 1⟩ : Q) E)
          (add MERT (mul (⟨((M * M : Nat) : Int), 1⟩ : Q) MERT))) := by
  simp only [Qeq, add, mul]; push_cast
  generalize E.num = en; generalize (E.den : Int) = ed
  generalize MERT.num = mn; generalize (MERT.den : Int) = md
  generalize (M : Int) = mm
  ring_uor

/-- **The clean decay bound** `|altSum(a+b,0,2K+1) − (cos·cos − sin·sin partial)| ≤ 5/(n+1)` at the deep
    depth `K` satisfying the `altErr_bound_decay` threshold (linear in `n`): `cosAdd_decay_le` gives the
    explicit `BOUND`, and `altErr_bound_decay` collapses that `BOUND` to `5/(n+1)`. The convergence
    modulus the Real reconciliation consumes. -/
theorem cosAdd_decay_5 {a b : Q} {M : Nat} (had : 0 < a.den) (hbd : 0 < b.den)
    (ha : Qle (Qabs a) ⟨(M : Int), 1⟩) (hb : Qle (Qabs b) ⟨(M : Int), 1⟩) (n K : Nat) (hm : 0 < M * M)
    (hK : (expM_U (M * M) (2 * (M * M))).num.toNat * 4 * (n + 1) * npow (M * M) (2 * (M * M) + 1)
        + (expM_U (M * M) (2 * (M * M))).num.toNat * 2 * (n + 1) * npow (M * M) (2 * (M * M) + 1)
        + (expM_U (M * M) (2 * (M * M))).num.toNat * (4 * (M * M)) * (n + 1) * npow (M * M) (2 * (M * M) + 1)
        + (expM_U (M * M) (2 * (M * M))).num.toNat * (2 * (M * M)) * (n + 1) * npow (M * M) (2 * (M * M) + 1)
        + (M * M) * (n + 1) * npow (2 * (M * M)) (2 * (2 * (M * M)) + 1)
        + 2 * (M * M) ≤ K) :
    Qle (Qabs (Qsub (altSum (add a b) 0 (2 * K + 1))
          (Qsub (mul (altSum a 0 (2 * K + 1)) (altSum b 0 (2 * K + 1)))
                (mul (Fsum (sinTerm a) (2 * K + 1)) (Fsum (sinTerm b) (2 * K + 1))))))
      ⟨5, n + 1⟩ := by
  have h2K : 2 * (M * M) ≤ K + 2 := by omega
  have hMERTd : 0 < (add (mul (expM_U (M * M) (2 * (M * M))) ⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩)
      (mul ⟨(2 * npow (M * M) (K + 1) : Int), fct (K + 1)⟩ (expM_U (M * M) (2 * (M * M))))).den :=
    add_den_pos (Qmul_den_pos (expM_U_den_pos _ _) (fct_pos _)) (Qmul_den_pos (fct_pos _) (expM_U_den_pos _ _))
  refine Qle_trans
    (add_den_pos (Qmul_den_pos Nat.one_pos (expTerm_den_pos (add_den_pos Nat.one_pos Nat.one_pos) _))
      (add_den_pos (Qmul_den_pos Nat.one_pos hMERTd) hMERTd))
    (cosAdd_decay_le had hbd ha hb K h2K) ?_
  refine Qle_trans
    (add_den_pos (Qmul_den_pos Nat.one_pos (expTerm_den_pos (add_den_pos Nat.one_pos Nat.one_pos) _))
      (add_den_pos hMERTd (Qmul_den_pos Nat.one_pos hMERTd)))
    (Qeq_le (decay_bridge M _ _)) (altErr_bound_decay M K n hm hK)

-- ===========================================================================
-- The **Real reconciliation** → `Rcos_add`. De-reindex the `Rmul` diagonals to the natural product
-- form (mirroring `Rcos_sq_diag_le`), then reconcile to a common deep depth and apply `cosAdd_decay_le`.
-- ===========================================================================

/-- **`cos·cos` diagonal de-reindex** (two-variable analog of `Rcos_sq_diag_le`): `(Rmul (Rcos a)(Rcos b)).seq n`
    is within `(xBound(cos a)+xBound(cos b))/(n+1)` of the natural diagonal `RaltReal_seq a 0 n · RaltReal_seq b 0 n`.
    `Qprod_diff_le` splits into the two factor drifts, each bounded by `RaltReal_diag_le` (the reindex `≥ n`). -/
theorem cosMul_diag_le (a b : Real) (n : Nat) :
    Qle (Qabs (Qsub ((Rmul (Rcos a) (Rcos b)).seq n)
        (mul (RaltReal_seq a 0 n) (RaltReal_seq b 0 n))))
      (mul (Qbound n) ⟨(xBound (Rcos a) + xBound (Rcos b) : Int), 1⟩) := by
  have hJ : n ≤ Ridx (Rcos a) (Rcos b) n := Ridx_ge (Rcos a) (Rcos b) n
  have hAd : 0 < (RaltReal_seq a 0 (Ridx (Rcos a) (Rcos b) n)).den := (Rcos a).den_pos _
  have hBd : 0 < (RaltReal_seq b 0 (Ridx (Rcos a) (Rcos b) n)).den := (Rcos b).den_pos _
  have hA'd : 0 < (RaltReal_seq a 0 n).den := (Rcos a).den_pos n
  have hB'd : 0 < (RaltReal_seq b 0 n).den := (Rcos b).den_pos n
  show Qle (Qabs (Qsub (mul (RaltReal_seq a 0 (Ridx (Rcos a) (Rcos b) n))
        (RaltReal_seq b 0 (Ridx (Rcos a) (Rcos b) n)))
      (mul (RaltReal_seq a 0 n) (RaltReal_seq b 0 n))))
    (mul (Qbound n) ⟨(xBound (Rcos a) + xBound (Rcos b) : Int), 1⟩)
  refine Qle_trans (add_den_pos (Qmul_den_pos (Qabs_den_pos hBd) (Qabs_den_pos (Qsub_den_pos hAd hA'd)))
      (Qmul_den_pos (Qabs_den_pos hA'd) (Qabs_den_pos (Qsub_den_pos hBd hB'd))))
    (Qprod_diff_le (RaltReal_seq a 0 (Ridx (Rcos a) (Rcos b) n))
      (RaltReal_seq a 0 n) (RaltReal_seq b 0 (Ridx (Rcos a) (Rcos b) n))
      (RaltReal_seq b 0 n) hAd hA'd hBd hB'd) ?_
  refine Qle_trans (add_den_pos (Qmul_den_pos Nat.one_pos (Qbound_den_pos n))
      (Qmul_den_pos Nat.one_pos (Qbound_den_pos n)))
    (Qadd_le_add
      (Qmul_le_mul (Qabs_den_pos hBd) Nat.one_pos (Qabs_den_pos (Qsub_den_pos hAd hA'd))
        (Qabs_num_nonneg _) (Int.ofNat_nonneg _) (canon_bound (Rcos b) _)
        (by rw [Qabs_Qsub_comm]; exact RaltReal_diag_le a 0 hJ))
      (Qmul_le_mul (Qabs_den_pos hA'd) Nat.one_pos (Qabs_den_pos (Qsub_den_pos hBd hB'd))
        (Qabs_num_nonneg _) (Int.ofNat_nonneg _) (canon_bound (Rcos a) n)
        (by rw [Qabs_Qsub_comm]; exact RaltReal_diag_le b 0 hJ)))
    (Qeq_le (by simp only [Qeq, add, mul, Qbound]; push_cast; ring_uor))

/-- **Product drift of two real samples**: `|a.seq i·b.seq j − a.seq i'·b.seq j'| ≤ 2(xBound a+xBound b)/(n+1)`
    (for all four indices `≥ n`). `Qprod_diff_le` + `xreg_n_le` (regularity) + `canon_bound`. -/
theorem xprod_drift (a b : Real) {n i j i' j' : Nat} (hi : n ≤ i) (hj : n ≤ j)
    (hi' : n ≤ i') (hj' : n ≤ j') :
    Qle (Qabs (Qsub (mul (a.seq i) (b.seq j)) (mul (a.seq i') (b.seq j'))))
      ⟨(2 * (xBound a + xBound b) : Int), n + 1⟩ := by
  refine Qle_trans (add_den_pos (Qmul_den_pos (Qabs_den_pos (b.den_pos j))
      (Qabs_den_pos (Qsub_den_pos (a.den_pos i) (a.den_pos i'))))
      (Qmul_den_pos (Qabs_den_pos (a.den_pos i')) (Qabs_den_pos (Qsub_den_pos (b.den_pos j) (b.den_pos j')))))
    (Qprod_diff_le (a.seq i) (a.seq i') (b.seq j) (b.seq j')
      (a.den_pos i) (a.den_pos i') (b.den_pos j) (b.den_pos j')) ?_
  refine Qle_trans (add_den_pos (Qmul_den_pos Nat.one_pos (Nat.succ_pos n))
      (Qmul_den_pos Nat.one_pos (Nat.succ_pos n)))
    (Qadd_le_add
      (Qmul_le_mul (Qabs_den_pos (b.den_pos j)) Nat.one_pos
        (Qabs_den_pos (Qsub_den_pos (a.den_pos i) (a.den_pos i'))) (Qabs_num_nonneg _)
        (Int.ofNat_nonneg _) (canon_bound b j) (xreg_n_le a hi hi'))
      (Qmul_le_mul (Qabs_den_pos (a.den_pos i')) Nat.one_pos
        (Qabs_den_pos (Qsub_den_pos (b.den_pos j) (b.den_pos j'))) (Qabs_num_nonneg _)
        (Int.ofNat_nonneg _) (canon_bound a i') (xreg_n_le b hj hj')))
    (Qeq_le (by simp only [Qeq, add, mul, Qbound]; push_cast; ring_uor))

/-- **Product drift of two alt-series diagonals**: `|RaltReal_seq a 1 i·RaltReal_seq b 1 j −
    RaltReal_seq a 1 n·RaltReal_seq b 1 n| ≤ (Ua+Ub)/(n+1)` (for `n ≤ i,j`), where `Ux` is the uniform
    `expM_U`-bound. `Qprod_diff_le` + `RaltReal_diag_le` (the diagonal regularity) + `altSum_abs_le_U`. -/
theorem altProd_drift (a b : Real) {n i j : Nat} (hi : n ≤ i) (hj : n ≤ j) :
    Qle (Qabs (Qsub (mul (RaltReal_seq a 1 i) (RaltReal_seq b 1 j))
        (mul (RaltReal_seq a 1 n) (RaltReal_seq b 1 n))))
      ⟨((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
        + (expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat : Int), n + 1⟩ := by
  have hUa : ∀ k, Qle (Qabs (RaltReal_seq a 1 k))
      ⟨((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat : Int), 1⟩ := fun k =>
    Qle_trans (expM_U_den_pos _ _) (altSum_abs_le_U (a.den_pos _) (canon_bound a _) 1 _)
      (Q_le_num_toNat _ (expM_U_num_nonneg _ _) (expM_U_den_pos _ _))
  have hUb : ∀ k, Qle (Qabs (RaltReal_seq b 1 k))
      ⟨((expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat : Int), 1⟩ := fun k =>
    Qle_trans (expM_U_den_pos _ _) (altSum_abs_le_U (b.den_pos _) (canon_bound b _) 1 _)
      (Q_le_num_toNat _ (expM_U_num_nonneg _ _) (expM_U_den_pos _ _))
  refine Qle_trans (add_den_pos
      (Qmul_den_pos (Qabs_den_pos ((RsinAux b).den_pos j))
        (Qabs_den_pos (Qsub_den_pos ((RsinAux a).den_pos i) ((RsinAux a).den_pos n))))
      (Qmul_den_pos (Qabs_den_pos ((RsinAux a).den_pos n))
        (Qabs_den_pos (Qsub_den_pos ((RsinAux b).den_pos j) ((RsinAux b).den_pos n)))))
    (Qprod_diff_le (RaltReal_seq a 1 i) (RaltReal_seq a 1 n) (RaltReal_seq b 1 j) (RaltReal_seq b 1 n)
      ((RsinAux a).den_pos i) ((RsinAux a).den_pos n) ((RsinAux b).den_pos j) ((RsinAux b).den_pos n)) ?_
  refine Qle_trans (add_den_pos (Qmul_den_pos Nat.one_pos (Nat.succ_pos n))
      (Qmul_den_pos Nat.one_pos (Nat.succ_pos n)))
    (Qadd_le_add
      (Qmul_le_mul (Qabs_den_pos ((RsinAux b).den_pos j)) Nat.one_pos
        (Qabs_den_pos (Qsub_den_pos ((RsinAux a).den_pos i) ((RsinAux a).den_pos n)))
        (Qabs_num_nonneg _) (Int.ofNat_nonneg _) (hUb j)
        (by rw [Qabs_Qsub_comm]; exact RaltReal_diag_le a 1 hi))
      (Qmul_le_mul (Qabs_den_pos ((RsinAux a).den_pos n)) Nat.one_pos
        (Qabs_den_pos (Qsub_den_pos ((RsinAux b).den_pos j) ((RsinAux b).den_pos n)))
        (Qabs_num_nonneg _) (Int.ofNat_nonneg _) (hUa n)
        (by rw [Qabs_Qsub_comm]; exact RaltReal_diag_le b 1 hj)))
    (Qeq_le (by simp only [Qeq, add, mul, Qbound]; push_cast; ring_uor))

/-- **`sin·sin` diagonal de-reindex** (two-variable analog of `Rsin_sq_diag_le`): `(Rmul (Rsin a)(Rsin b)).seq n`
    is within `C/(n+1)` of the natural diagonal `(a.seq R_a·b.seq R_b)·(RaltReal_seq a 1 n·RaltReal_seq b 1 n)`
    (`R_x = RaltReal_R x n`). `Rsin = Rmul x (RsinAux x)` is doubly reindexed; rearrange (`Qmul4_rearrange`)
    then `Qprod_diff_le` splits into the `x`-factor drift (`xprod_drift`) and the alt-series drift (`altProd_drift`). -/
theorem sinMul_diag_le (a b : Real) (n : Nat) :
    Qle (Qabs (Qsub ((Rmul (Rsin a) (Rsin b)).seq n)
        (mul (mul (a.seq (RaltReal_R a n)) (b.seq (RaltReal_R b n)))
          (mul (RaltReal_seq a 1 n) (RaltReal_seq b 1 n)))))
      ⟨((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
          * (expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat
          * (2 * (xBound a + xBound b))
        + xBound a * xBound b
          * ((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
            + (expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat) : Int), n + 1⟩ := by
  have hUa : ∀ k, Qle (Qabs (RaltReal_seq a 1 k))
      ⟨((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat : Int), 1⟩ := fun k =>
    Qle_trans (expM_U_den_pos _ _) (altSum_abs_le_U (a.den_pos _) (canon_bound a _) 1 _)
      (Q_le_num_toNat _ (expM_U_num_nonneg _ _) (expM_U_den_pos _ _))
  have hUb : ∀ k, Qle (Qabs (RaltReal_seq b 1 k))
      ⟨((expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat : Int), 1⟩ := fun k =>
    Qle_trans (expM_U_den_pos _ _) (altSum_abs_le_U (b.den_pos _) (canon_bound b _) 1 _)
      (Q_le_num_toNat _ (expM_U_num_nonneg _ _) (expM_U_den_pos _ _))
  have hnJ : n ≤ Ridx (Rsin a) (Rsin b) n := Ridx_ge _ _ n
  have hnKa : n ≤ Ridx a (RsinAux a) (Ridx (Rsin a) (Rsin b) n) :=
    Nat.le_trans hnJ (Ridx_ge a (RsinAux a) _)
  have hnKb : n ≤ Ridx b (RsinAux b) (Ridx (Rsin a) (Rsin b) n) :=
    Nat.le_trans hnJ (Ridx_ge b (RsinAux b) _)
  have hnRa : n ≤ RaltReal_R a n := n_le_RaltReal_R a n
  have hnRb : n ≤ RaltReal_R b n := n_le_RaltReal_R b n
  -- den abbreviations for the four factors
  have hAKa : 0 < (a.seq (Ridx a (RsinAux a) (Ridx (Rsin a) (Rsin b) n))).den := a.den_pos _
  have hBKb : 0 < (b.seq (Ridx b (RsinAux b) (Ridx (Rsin a) (Rsin b) n))).den := b.den_pos _
  have hPa : 0 < (RaltReal_seq a 1 (Ridx a (RsinAux a) (Ridx (Rsin a) (Rsin b) n))).den := (RsinAux a).den_pos _
  have hPb : 0 < (RaltReal_seq b 1 (Ridx b (RsinAux b) (Ridx (Rsin a) (Rsin b) n))).den := (RsinAux b).den_pos _
  have hA'd : 0 < (a.seq (RaltReal_R a n)).den := a.den_pos _
  have hB'd : 0 < (b.seq (RaltReal_R b n)).den := b.den_pos _
  have hPa'd : 0 < (RaltReal_seq a 1 n).den := (RsinAux a).den_pos n
  have hPb'd : 0 < (RaltReal_seq b 1 n).den := (RsinAux b).den_pos n
  -- |Q| ≤ Ua·Ub, |P'| ≤ xBa·xBb
  have hQ : Qle (Qabs (mul (RaltReal_seq a 1 (Ridx a (RsinAux a) (Ridx (Rsin a) (Rsin b) n)))
        (RaltReal_seq b 1 (Ridx b (RsinAux b) (Ridx (Rsin a) (Rsin b) n)))))
      ⟨((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
        * (expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat : Int), 1⟩ := by
    rw [Qabs_mul]
    exact Qle_trans (Qmul_den_pos Nat.one_pos Nat.one_pos)
      (Qmul_le_mul (Qabs_den_pos hPa) Nat.one_pos (Qabs_den_pos hPb) (Qabs_num_nonneg _)
        (Qabs_num_nonneg _) (hUa _) (hUb _)) (Qeq_le (by simp only [Qeq, mul]))
  have hP' : Qle (Qabs (mul (a.seq (RaltReal_R a n)) (b.seq (RaltReal_R b n))))
      ⟨(xBound a * xBound b : Int), 1⟩ := by
    rw [Qabs_mul]
    exact Qle_trans (Qmul_den_pos Nat.one_pos Nat.one_pos)
      (Qmul_le_mul (Qabs_den_pos hA'd) Nat.one_pos (Qabs_den_pos hB'd) (Qabs_num_nonneg _)
        (Qabs_num_nonneg _) (canon_bound a _) (canon_bound b _))
      (Qeq_le (by simp only [Qeq, mul]))
  -- unfold and rearrange the nested product, then `Qprod_diff_le`.
  show Qle (Qabs (Qsub
      (mul (mul (a.seq (Ridx a (RsinAux a) (Ridx (Rsin a) (Rsin b) n)))
                (RaltReal_seq a 1 (Ridx a (RsinAux a) (Ridx (Rsin a) (Rsin b) n))))
           (mul (b.seq (Ridx b (RsinAux b) (Ridx (Rsin a) (Rsin b) n)))
                (RaltReal_seq b 1 (Ridx b (RsinAux b) (Ridx (Rsin a) (Rsin b) n)))))
      (mul (mul (a.seq (RaltReal_R a n)) (b.seq (RaltReal_R b n)))
        (mul (RaltReal_seq a 1 n) (RaltReal_seq b 1 n))))) _
  refine Qle_congr_left (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos (Qmul_den_pos hAKa hBKb)
        (Qmul_den_pos hPa hPb)) (Qmul_den_pos (Qmul_den_pos hA'd hB'd) (Qmul_den_pos hPa'd hPb'd))))
    (Qeq_symm (Qabs_Qeq (QsubCongr (Qmul4_rearrange _ _ _ _) (Qeq_refl _)))) ?_
  refine Qle_trans (add_den_pos (Qmul_den_pos (Qabs_den_pos (Qmul_den_pos hPa hPb))
      (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos hAKa hBKb) (Qmul_den_pos hA'd hB'd))))
      (Qmul_den_pos (Qabs_den_pos (Qmul_den_pos hA'd hB'd))
        (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos hPa hPb) (Qmul_den_pos hPa'd hPb'd)))))
    (Qprod_diff_le (mul (a.seq (Ridx a (RsinAux a) (Ridx (Rsin a) (Rsin b) n)))
        (b.seq (Ridx b (RsinAux b) (Ridx (Rsin a) (Rsin b) n))))
      (mul (a.seq (RaltReal_R a n)) (b.seq (RaltReal_R b n)))
      (mul (RaltReal_seq a 1 (Ridx a (RsinAux a) (Ridx (Rsin a) (Rsin b) n)))
        (RaltReal_seq b 1 (Ridx b (RsinAux b) (Ridx (Rsin a) (Rsin b) n))))
      (mul (RaltReal_seq a 1 n) (RaltReal_seq b 1 n))
      (Qmul_den_pos hAKa hBKb) (Qmul_den_pos hA'd hB'd) (Qmul_den_pos hPa hPb)
      (Qmul_den_pos hPa'd hPb'd)) ?_
  refine Qle_trans (add_den_pos (Qmul_den_pos Nat.one_pos (Nat.succ_pos n))
      (Qmul_den_pos Nat.one_pos (Nat.succ_pos n)))
    (Qadd_le_add
      (Qmul_le_mul (Qabs_den_pos (Qmul_den_pos hPa hPb)) Nat.one_pos
        (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos hAKa hBKb) (Qmul_den_pos hA'd hB'd)))
        (Qabs_num_nonneg _) (Int.ofNat_nonneg _) hQ (xprod_drift a b hnKa hnKb hnRa hnRb))
      (Qmul_le_mul (Qabs_den_pos (Qmul_den_pos hA'd hB'd)) Nat.one_pos
        (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos hPa hPb) (Qmul_den_pos hPa'd hPb'd)))
        (Qabs_num_nonneg _) (Int.ofNat_nonneg _) hP' (altProd_drift a b hnKa hnKb)))
    (Qeq_le (by simp only [Qeq, add, mul]; push_cast; ring_uor))

/-- **Single-variable off-diagonal reconcile to a deep literal reference.** The natural cos/sin
    diagonal `RaltReal_seq x off (2N+1) = altSum (x.seq R) off R` (`R = RaltReal_R x (2N+1)`) is within
    `(Uₓ·4·xBound x + 1)/(N+1)` of the deep-reference partial sum `altSum (x.seq s) off (2K+1)` (any
    `s ≥ N`, any deep `2K+1 ≥ R`). Triangle through `altSum (x.seq s) off R`: the **arg-change** part
    (`altSum_Lip_le`, `LipS ≤ Uₓ`, squared regularity `xsq_diff_n_le`) and the **depth-change** part
    (`altSum_trunc_bound`, `RaltReal_trunc_le`). The two-variable analog of `RaltReal_diag_le`, but to a
    *common literal* depth (so both `a` and `b` can be reconciled to the single `2K+1` that `cosAdd_decay_5`
    consumes). -/
theorem altDiag_to_deep (x : Real) (off N s K : Nat) (hNs : N ≤ s)
    (hdeep : RaltReal_R x (2 * N + 1) ≤ 2 * K + 1) :
    Qle (Qabs (Qsub (RaltReal_seq x off (2 * N + 1)) (altSum (x.seq s) off (2 * K + 1))))
      ⟨((expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat * (4 * xBound x) + 1 : Int),
        N + 1⟩ := by
  have hNR : N ≤ RaltReal_R x (2 * N + 1) :=
    Nat.le_trans (by omega) (n_le_RaltReal_R x (2 * N + 1))
  have h2M : 2 * (xBound x * xBound x) ≤ RaltReal_R x (2 * N + 1) := by unfold RaltReal_R; omega
  show Qle (Qabs (Qsub (altSum (x.seq (RaltReal_R x (2 * N + 1))) off (RaltReal_R x (2 * N + 1)))
      (altSum (x.seq s) off (2 * K + 1))))
    ⟨((expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat * (4 * xBound x) + 1 : Int), N + 1⟩
  have htri := Qabs_sub_triangle
    (a := altSum (x.seq (RaltReal_R x (2 * N + 1))) off (RaltReal_R x (2 * N + 1)))
    (b := altSum (x.seq s) off (RaltReal_R x (2 * N + 1)))
    (c := altSum (x.seq s) off (2 * K + 1))
    (altSum_den_pos (x.den_pos _) off _) (altSum_den_pos (x.den_pos _) off _)
    (altSum_den_pos (x.den_pos _) off _)
  -- arg-change (Lipschitz) part
  have hLip : Qle (Qabs (Qsub (altSum (x.seq (RaltReal_R x (2 * N + 1))) off (RaltReal_R x (2 * N + 1)))
        (altSum (x.seq s) off (RaltReal_R x (2 * N + 1)))))
      ⟨((expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat * (4 * xBound x) : Int), N + 1⟩ := by
    have hLS := altSum_Lip_le (x.den_pos (RaltReal_R x (2 * N + 1))) (x.den_pos s)
      (canon_bound x (RaltReal_R x (2 * N + 1))) (canon_bound x s) off (RaltReal_R x (2 * N + 1))
    have hCle : Qle (LipS (xBound x * xBound x) (RaltReal_R x (2 * N + 1)))
        ⟨((expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat : Int), 1⟩ :=
      Qle_trans (expM_U_den_pos _ _) (LipS_le_U (xBound x * xBound x) (RaltReal_R x (2 * N + 1)))
        (Qle_toNat (expM_U_num_nonneg _ _) (expM_U_den_pos _ _))
    have hneg : Qle (Qabs (Qsub (neg (mul (x.seq (RaltReal_R x (2 * N + 1))) (x.seq (RaltReal_R x (2 * N + 1)))))
          (neg (mul (x.seq s) (x.seq s))))) ⟨(4 * xBound x : Nat), N + 1⟩ := by
      have hqe : Qeq (Qsub (neg (mul (x.seq (RaltReal_R x (2 * N + 1))) (x.seq (RaltReal_R x (2 * N + 1)))))
            (neg (mul (x.seq s) (x.seq s))))
          (neg (Qsub (mul (x.seq (RaltReal_R x (2 * N + 1))) (x.seq (RaltReal_R x (2 * N + 1))))
            (mul (x.seq s) (x.seq s)))) := by
        simp only [Qeq, Qsub, neg, mul, add]; push_cast; ring_uor
      have h1 := Qabs_Qeq hqe
      rw [Qabs_neg] at h1
      exact Qle_trans (Qabs_den_pos (Qsub_den_pos
          (Nat.mul_pos (x.den_pos _) (x.den_pos _)) (Nat.mul_pos (x.den_pos _) (x.den_pos _))))
        (Qeq_le h1) (xsq_diff_n_le x hNR hNs)
    refine Qle_trans (Qmul_den_pos (LipS_den_pos _ _) (Qabs_den_pos (Qsub_den_pos
        (Nat.mul_pos (x.den_pos _) (x.den_pos _)) (Nat.mul_pos (x.den_pos _) (x.den_pos _))))) hLS ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos
        (Nat.mul_pos (x.den_pos _) (x.den_pos _)) (Nat.mul_pos (x.den_pos _) (x.den_pos _)))))
      (Qmul_le_mul_right (Qabs_num_nonneg _) hCle) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos N))
      (Qmul_le_mul_left (Int.ofNat_nonneg _) hneg) ?_
    exact Qeq_le (by simp only [Qeq, mul]; push_cast; ring_uor)
  -- depth-change (truncation) part
  have hTr : Qle (Qabs (Qsub (altSum (x.seq s) off (RaltReal_R x (2 * N + 1)))
        (altSum (x.seq s) off (2 * K + 1)))) ⟨1, N + 1⟩ := by
    rw [Qabs_Qsub_comm]
    refine Qle_trans (fct_pos _) (altSum_trunc_bound (x.den_pos s) (canon_bound x s) off
      (a := RaltReal_R x (2 * N + 1)) (b := 2 * K + 1) (Nat.le_trans h2M (Nat.le_add_right _ 2)) hdeep) ?_
    exact Qle_trans (Nat.succ_pos _) (RaltReal_trunc_le x (2 * N + 1))
      (Q_den_mono (by decide) (by omega))
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (altSum_den_pos (x.den_pos _) off _)
      (altSum_den_pos (x.den_pos _) off _))) (Qabs_den_pos (Qsub_den_pos (altSum_den_pos (x.den_pos _) off _)
      (altSum_den_pos (x.den_pos _) off _)))) htri ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos N) (Nat.succ_pos N)) (Qadd_le_add hLip hTr) ?_
  exact Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor)

/-- **`cos·cos` product reconcile to the deep reference.** The natural `cos·cos` diagonal product
    `RaltReal_seq a 0 (2N+1) · RaltReal_seq b 0 (2N+1)` is within `C/(N+1)` of the deep product
    `altSum (a.seq s) 0 (2K+1) · altSum (b.seq s) 0 (2K+1)`. `Qprod_diff_le` splits into the two factor
    reconciles (`altDiag_to_deep`), each weighted by the other factor's uniform `expM_U`-bound. -/
theorem cosMulDeep_le (a b : Real) (N s K : Nat) (hNs : N ≤ s)
    (hda : RaltReal_R a (2 * N + 1) ≤ 2 * K + 1) (hdb : RaltReal_R b (2 * N + 1) ≤ 2 * K + 1) :
    Qle (Qabs (Qsub (mul (RaltReal_seq a 0 (2 * N + 1)) (RaltReal_seq b 0 (2 * N + 1)))
        (mul (altSum (a.seq s) 0 (2 * K + 1)) (altSum (b.seq s) 0 (2 * K + 1)))))
      ⟨((expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat
            * ((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat * (4 * xBound a) + 1)
          + (expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
            * ((expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat * (4 * xBound b) + 1) : Int),
        N + 1⟩ := by
  have hUa' : Qle (Qabs (altSum (a.seq s) 0 (2 * K + 1)))
      ⟨((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat : Int), 1⟩ :=
    Qle_trans (expM_U_den_pos _ _) (altSum_abs_le_U (a.den_pos _) (canon_bound a _) 0 _)
      (Q_le_num_toNat _ (expM_U_num_nonneg _ _) (expM_U_den_pos _ _))
  have hUb : Qle (Qabs (RaltReal_seq b 0 (2 * N + 1)))
      ⟨((expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat : Int), 1⟩ :=
    Qle_trans (expM_U_den_pos _ _) (altSum_abs_le_U (b.den_pos _) (canon_bound b _) 0 _)
      (Q_le_num_toNat _ (expM_U_num_nonneg _ _) (expM_U_den_pos _ _))
  have hAd : 0 < (RaltReal_seq a 0 (2 * N + 1)).den := altSum_den_pos (a.den_pos _) 0 _
  have hA'd : 0 < (altSum (a.seq s) 0 (2 * K + 1)).den := altSum_den_pos (a.den_pos _) 0 _
  have hBd : 0 < (RaltReal_seq b 0 (2 * N + 1)).den := altSum_den_pos (b.den_pos _) 0 _
  have hB'd : 0 < (altSum (b.seq s) 0 (2 * K + 1)).den := altSum_den_pos (b.den_pos _) 0 _
  refine Qle_trans (add_den_pos (Qmul_den_pos (Qabs_den_pos hBd) (Qabs_den_pos (Qsub_den_pos hAd hA'd)))
      (Qmul_den_pos (Qabs_den_pos hA'd) (Qabs_den_pos (Qsub_den_pos hBd hB'd))))
    (Qprod_diff_le (RaltReal_seq a 0 (2 * N + 1)) (altSum (a.seq s) 0 (2 * K + 1))
      (RaltReal_seq b 0 (2 * N + 1)) (altSum (b.seq s) 0 (2 * K + 1)) hAd hA'd hBd hB'd) ?_
  refine Qle_trans (add_den_pos (Qmul_den_pos Nat.one_pos (Nat.succ_pos N))
      (Qmul_den_pos Nat.one_pos (Nat.succ_pos N)))
    (Qadd_le_add
      (Qmul_le_mul (Qabs_den_pos hBd) Nat.one_pos (Qabs_den_pos (Qsub_den_pos hAd hA'd))
        (Qabs_num_nonneg _) (Int.ofNat_nonneg _) hUb (altDiag_to_deep a 0 N s K hNs hda))
      (Qmul_le_mul (Qabs_den_pos hA'd) Nat.one_pos (Qabs_den_pos (Qsub_den_pos hBd hB'd))
        (Qabs_num_nonneg _) (Int.ofNat_nonneg _) hUa' (altDiag_to_deep b 0 N s K hNs hdb)))
    (Qeq_le (by simp only [Qeq, add, mul]; push_cast; ring_uor))

/-- **The `cos(a+b)` LHS depth reconcile.** `(Rcos (Radd a b)).seq N = altSum ((Radd a b).seq R_z) 0 R_z`
    (`R_z = RaltReal_R (Radd a b) N`, and `(Radd a b).seq R_z = a₍₂R_z₊₁₎ + b₍₂R_z₊₁₎`) is within `1/(N+1)`
    of the deep partial sum `altSum (a₍₂R_z₊₁₎ + b₍₂R_z₊₁₎) 0 (2K+1)` — a *same-argument* depth change, so
    pure `altSum_trunc_bound` (modulus `xBound (Radd a b)`) + `RaltReal_trunc_le`. -/
theorem cosAddLHS_le (a b : Real) (N K : Nat)
    (hdeep : RaltReal_R (Radd a b) N ≤ 2 * K + 1) :
    Qle (Qabs (Qsub (RaltReal_seq (Radd a b) 0 N)
        (altSum (add (a.seq (2 * RaltReal_R (Radd a b) N + 1)) (b.seq (2 * RaltReal_R (Radd a b) N + 1)))
          0 (2 * K + 1)))) ⟨1, N + 1⟩ := by
  have h2M : 2 * (xBound (Radd a b) * xBound (Radd a b)) ≤ RaltReal_R (Radd a b) N := by
    unfold RaltReal_R; omega
  show Qle (Qabs (Qsub (altSum ((Radd a b).seq (RaltReal_R (Radd a b) N)) 0 (RaltReal_R (Radd a b) N))
      (altSum (add (a.seq (2 * RaltReal_R (Radd a b) N + 1)) (b.seq (2 * RaltReal_R (Radd a b) N + 1)))
        0 (2 * K + 1)))) ⟨1, N + 1⟩
  rw [Qabs_Qsub_comm]
  refine Qle_trans (fct_pos _) (altSum_trunc_bound ((Radd a b).den_pos _) (canon_bound (Radd a b) _) 0
    (a := RaltReal_R (Radd a b) N) (b := 2 * K + 1) (Nat.le_trans h2M (Nat.le_add_right _ 2)) hdeep) ?_
  exact Qle_trans (Nat.succ_pos _) (RaltReal_trunc_le (Radd a b) N) (Q_den_mono (by decide) (by omega))

/-- `Fsum (sinTerm a) N ≈ a · altSum a 1 N` — the constant factor `a` pulls out of the `sinTerm` sum
    (`Fsum_mul_left`), leaving the `off=1` alternating partial sum. -/
theorem Fsum_sinTerm_eq (a : Q) (had : 0 < a.den) (N : Nat) :
    Qeq (Fsum (sinTerm a) N) (mul a (altSum a 1 N)) := by
  rw [altSum_eq_Fsum a 1 N]
  exact Fsum_mul_left had (fun i => altTerm_den_pos had 1 i) N

/-- **General `off` product reconcile to the deep reference** (the `off`-parameterized `cosMulDeep_le`):
    `RaltReal_seq a off (2N+1) · RaltReal_seq b off (2N+1)` is within `C/(N+1)` of
    `altSum (a.seq s) off (2K+1) · altSum (b.seq s) off (2K+1)`. Used at `off=1` for the `sin·sin` inner
    product. `Qprod_diff_le` + two `altDiag_to_deep` factor reconciles, each weighted by the other's
    uniform bound. -/
theorem altMulDeep_le (a b : Real) (off N s K : Nat) (hNs : N ≤ s)
    (hda : RaltReal_R a (2 * N + 1) ≤ 2 * K + 1) (hdb : RaltReal_R b (2 * N + 1) ≤ 2 * K + 1) :
    Qle (Qabs (Qsub (mul (RaltReal_seq a off (2 * N + 1)) (RaltReal_seq b off (2 * N + 1)))
        (mul (altSum (a.seq s) off (2 * K + 1)) (altSum (b.seq s) off (2 * K + 1)))))
      ⟨((expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat
            * ((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat * (4 * xBound a) + 1)
          + (expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
            * ((expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat * (4 * xBound b) + 1) : Int),
        N + 1⟩ := by
  have hUa' : Qle (Qabs (altSum (a.seq s) off (2 * K + 1)))
      ⟨((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat : Int), 1⟩ :=
    Qle_trans (expM_U_den_pos _ _) (altSum_abs_le_U (a.den_pos _) (canon_bound a _) off _)
      (Q_le_num_toNat _ (expM_U_num_nonneg _ _) (expM_U_den_pos _ _))
  have hUb : Qle (Qabs (RaltReal_seq b off (2 * N + 1)))
      ⟨((expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat : Int), 1⟩ :=
    Qle_trans (expM_U_den_pos _ _) (altSum_abs_le_U (b.den_pos _) (canon_bound b _) off _)
      (Q_le_num_toNat _ (expM_U_num_nonneg _ _) (expM_U_den_pos _ _))
  have hAd : 0 < (RaltReal_seq a off (2 * N + 1)).den := altSum_den_pos (a.den_pos _) off _
  have hA'd : 0 < (altSum (a.seq s) off (2 * K + 1)).den := altSum_den_pos (a.den_pos _) off _
  have hBd : 0 < (RaltReal_seq b off (2 * N + 1)).den := altSum_den_pos (b.den_pos _) off _
  have hB'd : 0 < (altSum (b.seq s) off (2 * K + 1)).den := altSum_den_pos (b.den_pos _) off _
  refine Qle_trans (add_den_pos (Qmul_den_pos (Qabs_den_pos hBd) (Qabs_den_pos (Qsub_den_pos hAd hA'd)))
      (Qmul_den_pos (Qabs_den_pos hA'd) (Qabs_den_pos (Qsub_den_pos hBd hB'd))))
    (Qprod_diff_le (RaltReal_seq a off (2 * N + 1)) (altSum (a.seq s) off (2 * K + 1))
      (RaltReal_seq b off (2 * N + 1)) (altSum (b.seq s) off (2 * K + 1)) hAd hA'd hBd hB'd) ?_
  refine Qle_trans (add_den_pos (Qmul_den_pos Nat.one_pos (Nat.succ_pos N))
      (Qmul_den_pos Nat.one_pos (Nat.succ_pos N)))
    (Qadd_le_add
      (Qmul_le_mul (Qabs_den_pos hBd) Nat.one_pos (Qabs_den_pos (Qsub_den_pos hAd hA'd))
        (Qabs_num_nonneg _) (Int.ofNat_nonneg _) hUb (altDiag_to_deep a off N s K hNs hda))
      (Qmul_le_mul (Qabs_den_pos hA'd) Nat.one_pos (Qabs_den_pos (Qsub_den_pos hBd hB'd))
        (Qabs_num_nonneg _) (Int.ofNat_nonneg _) hUa' (altDiag_to_deep b off N s K hNs hdb)))
    (Qeq_le (by simp only [Qeq, add, mul]; push_cast; ring_uor))

set_option maxHeartbeats 1000000 in
/-- **`sin·sin` product reconcile to the deep reference.** The natural `sin·sin` diagonal
    `(a.seq R_a · b.seq R_b)·(RaltReal_seq a 1 (2N+1) · RaltReal_seq b 1 (2N+1))` is within `C/(N+1)` of
    the deep `sinTerm`-sum product `Fsum (sinTerm a₀) (2K+1) · Fsum (sinTerm b₀) (2K+1)` (`a₀ = a.seq s`).
    Refactor the target with `Fsum_sinTerm_eq`/`Qmul4_rearrange`, then `Qprod_diff_le` splits into the
    leading `x`-factor drift (`xprod_drift`) and the `off=1` alt-series product reconcile (`altMulDeep_le`). -/
theorem sinMulDeep_le (a b : Real) (N s K : Nat) (hNs : N ≤ s)
    (hda : RaltReal_R a (2 * N + 1) ≤ 2 * K + 1) (hdb : RaltReal_R b (2 * N + 1) ≤ 2 * K + 1) :
    Qle (Qabs (Qsub (mul (mul (a.seq (RaltReal_R a (2 * N + 1))) (b.seq (RaltReal_R b (2 * N + 1))))
          (mul (RaltReal_seq a 1 (2 * N + 1)) (RaltReal_seq b 1 (2 * N + 1))))
        (mul (Fsum (sinTerm (a.seq s)) (2 * K + 1)) (Fsum (sinTerm (b.seq s)) (2 * K + 1)))))
      ⟨((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
            * (expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat * (2 * (xBound a + xBound b))
          + xBound a * xBound b
            * ((expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat
                * ((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat * (4 * xBound a) + 1)
              + (expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
                * ((expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat * (4 * xBound b) + 1)) : Int),
        N + 1⟩ := by
  have hnRa : N ≤ RaltReal_R a (2 * N + 1) := Nat.le_trans (by omega) (n_le_RaltReal_R a _)
  have hnRb : N ≤ RaltReal_R b (2 * N + 1) := Nat.le_trans (by omega) (n_le_RaltReal_R b _)
  -- den abbreviations
  have hAd : 0 < (a.seq (RaltReal_R a (2 * N + 1))).den := a.den_pos _
  have hBd : 0 < (b.seq (RaltReal_R b (2 * N + 1))).den := b.den_pos _
  have hPd : 0 < (RaltReal_seq a 1 (2 * N + 1)).den := (RsinAux a).den_pos _
  have hQd : 0 < (RaltReal_seq b 1 (2 * N + 1)).den := (RsinAux b).den_pos _
  have hA'd : 0 < (a.seq s).den := a.den_pos _
  have hB'd : 0 < (b.seq s).den := b.den_pos _
  have hP'd : 0 < (altSum (a.seq s) 1 (2 * K + 1)).den := altSum_den_pos (a.den_pos _) 1 _
  have hQ'd : 0 < (altSum (b.seq s) 1 (2 * K + 1)).den := altSum_den_pos (b.den_pos _) 1 _
  -- refactor the target into `(a₀·b₀)·(altSum a₀ 1 · altSum b₀ 1)`
  have htgt : Qeq (mul (Fsum (sinTerm (a.seq s)) (2 * K + 1)) (Fsum (sinTerm (b.seq s)) (2 * K + 1)))
      (mul (mul (a.seq s) (b.seq s)) (mul (altSum (a.seq s) 1 (2 * K + 1)) (altSum (b.seq s) 1 (2 * K + 1)))) :=
    Qeq_trans (Qmul_den_pos (Qmul_den_pos hA'd hP'd) (Qmul_den_pos hB'd hQ'd))
      (Qmul_congr (Fsum_sinTerm_eq (a.seq s) hA'd (2 * K + 1)) (Fsum_sinTerm_eq (b.seq s) hB'd (2 * K + 1)))
      (Qmul4_rearrange (a.seq s) (altSum (a.seq s) 1 (2 * K + 1)) (b.seq s) (altSum (b.seq s) 1 (2 * K + 1)))
  -- |mul P Q| ≤ Ua·Ub
  have hPQ : Qle (Qabs (mul (RaltReal_seq a 1 (2 * N + 1)) (RaltReal_seq b 1 (2 * N + 1))))
      ⟨((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
        * (expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat : Int), 1⟩ := by
    rw [Qabs_mul]
    exact Qle_trans (Qmul_den_pos Nat.one_pos Nat.one_pos)
      (Qmul_le_mul (Qabs_den_pos hPd) Nat.one_pos (Qabs_den_pos hQd) (Qabs_num_nonneg _) (Qabs_num_nonneg _)
        (Qle_trans (expM_U_den_pos _ _) (altSum_abs_le_U (a.den_pos _) (canon_bound a _) 1 _)
          (Q_le_num_toNat _ (expM_U_num_nonneg _ _) (expM_U_den_pos _ _)))
        (Qle_trans (expM_U_den_pos _ _) (altSum_abs_le_U (b.den_pos _) (canon_bound b _) 1 _)
          (Q_le_num_toNat _ (expM_U_num_nonneg _ _) (expM_U_den_pos _ _))))
      (Qeq_le (by simp only [Qeq, mul]))
  -- |a₀·b₀| ≤ xBa·xBb
  have hAB' : Qle (Qabs (mul (a.seq s) (b.seq s))) ⟨(xBound a * xBound b : Int), 1⟩ := by
    rw [Qabs_mul]
    exact Qle_trans (Qmul_den_pos Nat.one_pos Nat.one_pos)
      (Qmul_le_mul (Qabs_den_pos hA'd) Nat.one_pos (Qabs_den_pos hB'd) (Qabs_num_nonneg _)
        (Qabs_num_nonneg _) (canon_bound a _) (canon_bound b _))
      (Qeq_le (by simp only [Qeq, mul]))
  -- replace the target up to `≈`, then `Qprod_diff_le`
  refine Qle_congr_left (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos (Qmul_den_pos hAd hBd)
        (Qmul_den_pos hPd hQd)) (Qmul_den_pos (Qmul_den_pos hA'd hB'd) (Qmul_den_pos hP'd hQ'd))))
    (Qeq_symm (Qabs_Qeq (QsubCongr (Qeq_refl _) htgt))) ?_
  refine Qle_trans (add_den_pos (Qmul_den_pos (Qabs_den_pos (Qmul_den_pos hPd hQd))
      (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos hAd hBd) (Qmul_den_pos hA'd hB'd))))
      (Qmul_den_pos (Qabs_den_pos (Qmul_den_pos hA'd hB'd))
        (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos hPd hQd) (Qmul_den_pos hP'd hQ'd)))))
    (Qprod_diff_le (mul (a.seq (RaltReal_R a (2 * N + 1))) (b.seq (RaltReal_R b (2 * N + 1))))
      (mul (a.seq s) (b.seq s)) (mul (RaltReal_seq a 1 (2 * N + 1)) (RaltReal_seq b 1 (2 * N + 1)))
      (mul (altSum (a.seq s) 1 (2 * K + 1)) (altSum (b.seq s) 1 (2 * K + 1)))
      (Qmul_den_pos hAd hBd) (Qmul_den_pos hA'd hB'd) (Qmul_den_pos hPd hQd)
      (Qmul_den_pos hP'd hQ'd)) ?_
  refine Qle_trans (add_den_pos (Qmul_den_pos Nat.one_pos (Nat.succ_pos N))
      (Qmul_den_pos Nat.one_pos (Nat.succ_pos N)))
    (Qadd_le_add
      (Qmul_le_mul (Qabs_den_pos (Qmul_den_pos hPd hQd)) Nat.one_pos
        (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos hAd hBd) (Qmul_den_pos hA'd hB'd)))
        (Qabs_num_nonneg _) (Int.ofNat_nonneg _) hPQ (xprod_drift a b hnRa hnRb hNs hNs))
      (Qmul_le_mul (Qabs_den_pos (Qmul_den_pos hA'd hB'd)) Nat.one_pos
        (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos hPd hQd) (Qmul_den_pos hP'd hQ'd)))
        (Qabs_num_nonneg _) (Int.ofNat_nonneg _) hAB' (altMulDeep_le a b 1 N s K hNs hda hdb)))
    (Qeq_le (by simp only [Qeq, add, mul]; push_cast; ring_uor))

/-- `|(p−q) − (p'−q')| ≤ |p−p'| + |q−q'|` — the difference-of-differences triangle. -/
private theorem Qabs_qsub_qsub_le (p q p' q' : Q) (hp : 0 < p.den) (hq : 0 < q.den)
    (hp' : 0 < p'.den) (hq' : 0 < q'.den) :
    Qle (Qabs (Qsub (Qsub p q) (Qsub p' q'))) (add (Qabs (Qsub p p')) (Qabs (Qsub q q'))) := by
  have hid : Qeq (Qsub (Qsub p q) (Qsub p' q')) (add (Qsub p p') (neg (Qsub q q'))) := by
    simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
  have h1 : Qle (Qabs (Qsub (Qsub p q) (Qsub p' q')))
      (add (Qabs (Qsub p p')) (Qabs (neg (Qsub q q')))) :=
    Qle_trans (Qabs_den_pos (add_den_pos (Qsub_den_pos hp hp') (neg_den_pos (Qsub_den_pos hq hq'))))
      (Qeq_le (Qabs_Qeq hid)) (Qabs_add_le (Qsub p p') (neg (Qsub q q')))
  rw [Qabs_neg] at h1
  exact h1

set_option maxHeartbeats 4000000 in
/-- **`cos(a+b) = cos a · cos b − sin a · sin b` as constructive reals.** The diagonal of the RHS at `N`
    (sampled at `2N+1` by `Rsub`/`Radd`) and the LHS `(Rcos (Radd a b)).seq N` are both reconciled to a
    common deep odd reference `2K+1`: the `Rmul` diagonals de-reindex (`cosMul_diag_le`, `sinMul_diag_le`)
    to the natural products, those reconcile to the deep reference (`cosMulDeep_le`, `sinMulDeep_le`), the
    LHS reconciles (`cosAddLHS_le`), and the deep rational identity `cosAdd_decay_5` closes the residual —
    every one of the six pieces `≤ cᵢ/(N+1)`, the `Req` tolerance. -/
theorem Rcos_add (a b : Real) :
    Req (Rcos (Radd a b)) (Rsub (Rmul (Rcos a) (Rcos b)) (Rmul (Rsin a) (Rsin b))) := by
  refine Req_of_lin_bound
    (C := 1 + 5
      + ((expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat
            * ((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat * (4 * xBound a) + 1)
          + (expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
            * ((expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat * (4 * xBound b) + 1))
      + (xBound (Rcos a) + xBound (Rcos b))
      + ((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
            * (expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat * (2 * (xBound a + xBound b))
          + xBound a * xBound b
            * ((expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat
                * ((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat * (4 * xBound a) + 1)
              + (expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
                * ((expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat * (4 * xBound b) + 1)))
      + ((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
            * (expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat * (2 * (xBound a + xBound b))
          + xBound a * xBound b
            * ((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
              + (expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat))) ?_
  intro N
  -- the common deep reference `K`, dominating every natural depth and the decay threshold
  obtain ⟨K, hda, hdb, hdeepK, hKbig⟩ :
      ∃ K, RaltReal_R a (2 * N + 1) ≤ 2 * K + 1 ∧ RaltReal_R b (2 * N + 1) ≤ 2 * K + 1
        ∧ RaltReal_R (Radd a b) N ≤ 2 * K + 1
        ∧ ((expM_U ((xBound a + xBound b) * (xBound a + xBound b)) (2 * ((xBound a + xBound b) * (xBound a + xBound b)))).num.toNat * 4 * (N + 1) * npow ((xBound a + xBound b) * (xBound a + xBound b)) (2 * ((xBound a + xBound b) * (xBound a + xBound b)) + 1)
            + (expM_U ((xBound a + xBound b) * (xBound a + xBound b)) (2 * ((xBound a + xBound b) * (xBound a + xBound b)))).num.toNat * 2 * (N + 1) * npow ((xBound a + xBound b) * (xBound a + xBound b)) (2 * ((xBound a + xBound b) * (xBound a + xBound b)) + 1)
            + (expM_U ((xBound a + xBound b) * (xBound a + xBound b)) (2 * ((xBound a + xBound b) * (xBound a + xBound b)))).num.toNat * (4 * ((xBound a + xBound b) * (xBound a + xBound b))) * (N + 1) * npow ((xBound a + xBound b) * (xBound a + xBound b)) (2 * ((xBound a + xBound b) * (xBound a + xBound b)) + 1)
            + (expM_U ((xBound a + xBound b) * (xBound a + xBound b)) (2 * ((xBound a + xBound b) * (xBound a + xBound b)))).num.toNat * (2 * ((xBound a + xBound b) * (xBound a + xBound b))) * (N + 1) * npow ((xBound a + xBound b) * (xBound a + xBound b)) (2 * ((xBound a + xBound b) * (xBound a + xBound b)) + 1)
            + ((xBound a + xBound b) * (xBound a + xBound b)) * (N + 1) * npow (2 * ((xBound a + xBound b) * (xBound a + xBound b))) (2 * (2 * ((xBound a + xBound b) * (xBound a + xBound b))) + 1)
            + 2 * ((xBound a + xBound b) * (xBound a + xBound b)) ≤ K) := by
    refine ⟨(expM_U ((xBound a + xBound b) * (xBound a + xBound b)) (2 * ((xBound a + xBound b) * (xBound a + xBound b)))).num.toNat * 4 * (N + 1) * npow ((xBound a + xBound b) * (xBound a + xBound b)) (2 * ((xBound a + xBound b) * (xBound a + xBound b)) + 1)
            + (expM_U ((xBound a + xBound b) * (xBound a + xBound b)) (2 * ((xBound a + xBound b) * (xBound a + xBound b)))).num.toNat * 2 * (N + 1) * npow ((xBound a + xBound b) * (xBound a + xBound b)) (2 * ((xBound a + xBound b) * (xBound a + xBound b)) + 1)
            + (expM_U ((xBound a + xBound b) * (xBound a + xBound b)) (2 * ((xBound a + xBound b) * (xBound a + xBound b)))).num.toNat * (4 * ((xBound a + xBound b) * (xBound a + xBound b))) * (N + 1) * npow ((xBound a + xBound b) * (xBound a + xBound b)) (2 * ((xBound a + xBound b) * (xBound a + xBound b)) + 1)
            + (expM_U ((xBound a + xBound b) * (xBound a + xBound b)) (2 * ((xBound a + xBound b) * (xBound a + xBound b)))).num.toNat * (2 * ((xBound a + xBound b) * (xBound a + xBound b))) * (N + 1) * npow ((xBound a + xBound b) * (xBound a + xBound b)) (2 * ((xBound a + xBound b) * (xBound a + xBound b)) + 1)
            + ((xBound a + xBound b) * (xBound a + xBound b)) * (N + 1) * npow (2 * ((xBound a + xBound b) * (xBound a + xBound b))) (2 * (2 * ((xBound a + xBound b) * (xBound a + xBound b))) + 1)
            + 2 * ((xBound a + xBound b) * (xBound a + xBound b))
          + RaltReal_R a (2 * N + 1) + RaltReal_R b (2 * N + 1) + RaltReal_R (Radd a b) N, ?_, ?_, ?_, ?_⟩ <;> omega
  have hNs : N ≤ 2 * RaltReal_R (Radd a b) N + 1 := by
    have := n_le_RaltReal_R (Radd a b) N; omega
  have hm : 0 < (xBound a + xBound b) * (xBound a + xBound b) :=
    Nat.mul_pos (Nat.lt_of_lt_of_le (xBound_pos a) (Nat.le_add_right _ _))
      (Nat.lt_of_lt_of_le (xBound_pos a) (Nat.le_add_right _ _))
  -- the deep-reference samples `a₀ = a₍₂R_z₊₁₎`, `b₀ = b₍₂R_z₊₁₎`
  have ha0 : Qle (Qabs (a.seq (2 * RaltReal_R (Radd a b) N + 1))) ⟨(xBound a + xBound b : Int), 1⟩ :=
    Qle_trans Nat.one_pos (canon_bound a _)
      (by show ((xBound a : Int)) * 1 ≤ ((xBound a + xBound b : Int)) * 1; push_cast; omega)
  have hb0 : Qle (Qabs (b.seq (2 * RaltReal_R (Radd a b) N + 1))) ⟨(xBound a + xBound b : Int), 1⟩ :=
    Qle_trans Nat.one_pos (canon_bound b _)
      (by show ((xBound b : Int)) * 1 ≤ ((xBound a + xBound b : Int)) * 1; push_cast; omega)
  -- den-positivity of the eight compound terms
  have hAden : 0 < ((Rcos (Radd a b)).seq N).den := (Rcos (Radd a b)).den_pos N
  have hBden : 0 < ((Rmul (Rcos a) (Rcos b)).seq (2 * N + 1)).den := (Rmul (Rcos a) (Rcos b)).den_pos _
  have hDden : 0 < ((Rmul (Rsin a) (Rsin b)).seq (2 * N + 1)).den := (Rmul (Rsin a) (Rsin b)).den_pos _
  have hLden : 0 < (altSum (add (a.seq (2 * RaltReal_R (Radd a b) N + 1))
      (b.seq (2 * RaltReal_R (Radd a b) N + 1))) 0 (2 * K + 1)).den :=
    altSum_den_pos (add_den_pos (a.den_pos _) (b.den_pos _)) 0 _
  have hCCden : 0 < (mul (altSum (a.seq (2 * RaltReal_R (Radd a b) N + 1)) 0 (2 * K + 1))
      (altSum (b.seq (2 * RaltReal_R (Radd a b) N + 1)) 0 (2 * K + 1))).den :=
    Qmul_den_pos (altSum_den_pos (a.den_pos _) 0 _) (altSum_den_pos (b.den_pos _) 0 _)
  have hSSden : 0 < (mul (Fsum (sinTerm (a.seq (2 * RaltReal_R (Radd a b) N + 1))) (2 * K + 1))
      (Fsum (sinTerm (b.seq (2 * RaltReal_R (Radd a b) N + 1))) (2 * K + 1))).den :=
    Qmul_den_pos (Fsum_den_pos (fun i => sinTerm_den_pos (a.den_pos _) i) _)
      (Fsum_den_pos (fun i => sinTerm_den_pos (b.den_pos _) i) _)
  have hCCnden : 0 < (mul (RaltReal_seq a 0 (2 * N + 1)) (RaltReal_seq b 0 (2 * N + 1))).den :=
    Qmul_den_pos (altSum_den_pos (a.den_pos _) 0 _) (altSum_den_pos (b.den_pos _) 0 _)
  have hSSnden : 0 < (mul (mul (a.seq (RaltReal_R a (2 * N + 1))) (b.seq (RaltReal_R b (2 * N + 1))))
      (mul (RaltReal_seq a 1 (2 * N + 1)) (RaltReal_seq b 1 (2 * N + 1)))).den :=
    Qmul_den_pos (Qmul_den_pos (a.den_pos _) (b.den_pos _))
      (Qmul_den_pos (altSum_den_pos (a.den_pos _) 1 _) (altSum_den_pos (b.den_pos _) 1 _))
  -- the six reconciliation bounds, each `≤ cᵢ/(N+1)`
  have hb1 := cosAddLHS_le a b N K hdeepK
  have hb2 := cosAdd_decay_5 (M := xBound a + xBound b) (a := a.seq (2 * RaltReal_R (Radd a b) N + 1))
    (b := b.seq (2 * RaltReal_R (Radd a b) N + 1)) (a.den_pos _) (b.den_pos _) ha0 hb0 N K hm hKbig
  have hb3 : Qle (Qabs (Qsub (mul (altSum (a.seq (2 * RaltReal_R (Radd a b) N + 1)) 0 (2 * K + 1))
        (altSum (b.seq (2 * RaltReal_R (Radd a b) N + 1)) 0 (2 * K + 1)))
      (mul (RaltReal_seq a 0 (2 * N + 1)) (RaltReal_seq b 0 (2 * N + 1)))))
      ⟨((expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat
            * ((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat * (4 * xBound a) + 1)
          + (expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
            * ((expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat * (4 * xBound b) + 1) : Int),
        N + 1⟩ := by
    rw [Qabs_Qsub_comm]
    exact cosMulDeep_le a b N (2 * RaltReal_R (Radd a b) N + 1) K hNs hda hdb
  have hb4 : Qle (Qabs (Qsub (mul (RaltReal_seq a 0 (2 * N + 1)) (RaltReal_seq b 0 (2 * N + 1)))
      ((Rmul (Rcos a) (Rcos b)).seq (2 * N + 1))))
      ⟨(xBound (Rcos a) + xBound (Rcos b) : Int), N + 1⟩ := by
    rw [Qabs_Qsub_comm]
    refine Qle_trans (Qmul_den_pos (Qbound_den_pos _) Nat.one_pos) (cosMul_diag_le a b (2 * N + 1)) ?_
    refine Qle_trans (b := ⟨(xBound (Rcos a) + xBound (Rcos b) : Int), 2 * N + 1 + 1⟩) (Nat.succ_pos _)
      (Qeq_le (by simp only [Qeq, mul, Qbound]; push_cast; ring_uor))
      (Q_den_mono (Int.add_nonneg (Int.ofNat_nonneg _) (Int.ofNat_nonneg _)) (by omega))
  have hb5 := sinMulDeep_le a b N (2 * RaltReal_R (Radd a b) N + 1) K hNs hda hdb
  have hb6 : Qle (Qabs (Qsub ((Rmul (Rsin a) (Rsin b)).seq (2 * N + 1))
      (mul (mul (a.seq (RaltReal_R a (2 * N + 1))) (b.seq (RaltReal_R b (2 * N + 1))))
        (mul (RaltReal_seq a 1 (2 * N + 1)) (RaltReal_seq b 1 (2 * N + 1))))))
      ⟨((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
            * (expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat * (2 * (xBound a + xBound b))
          + xBound a * xBound b
            * ((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
              + (expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat) : Int), N + 1⟩ := by
    refine Qle_trans (b := ⟨((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
            * (expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat * (2 * (xBound a + xBound b))
          + xBound a * xBound b
            * ((expM_U (xBound a * xBound a) (2 * (xBound a * xBound a))).num.toNat
              + (expM_U (xBound b * xBound b) (2 * (xBound b * xBound b))).num.toNat) : Int), 2 * N + 1 + 1⟩)
      (Nat.succ_pos _) (sinMul_diag_le a b (2 * N + 1))
      (Q_den_mono (by exact_mod_cast Nat.zero_le _) (by omega))
  -- commute the two `sin·sin` bounds to the orientation the triangle consumes
  have hb5' := hb5
  rw [Qabs_Qsub_comm] at hb5'
  have hb6' := hb6
  rw [Qabs_Qsub_comm] at hb6'
  -- route `|A − (B − D)|` through `L`, the deep `cos·cos/sin·sin` products, and their natural forms
  have htotal := Qle_trans
    (add_den_pos (Qabs_den_pos (Qsub_den_pos hAden hLden))
      (Qabs_den_pos (Qsub_den_pos hLden (Qsub_den_pos hBden hDden))))
    (Qabs_sub_triangle hAden hLden (Qsub_den_pos hBden hDden))
    (Qadd_le_add hb1 (Qle_trans
      (add_den_pos (Qabs_den_pos (Qsub_den_pos hLden (Qsub_den_pos hCCden hSSden)))
        (Qabs_den_pos (Qsub_den_pos (Qsub_den_pos hCCden hSSden) (Qsub_den_pos hBden hDden))))
      (Qabs_sub_triangle hLden (Qsub_den_pos hCCden hSSden) (Qsub_den_pos hBden hDden))
      (Qadd_le_add hb2 (Qle_trans
        (add_den_pos (Qabs_den_pos (Qsub_den_pos hCCden hBden))
          (Qabs_den_pos (Qsub_den_pos hSSden hDden)))
        (Qabs_qsub_qsub_le
          (mul (altSum (a.seq (2 * RaltReal_R (Radd a b) N + 1)) 0 (2 * K + 1))
            (altSum (b.seq (2 * RaltReal_R (Radd a b) N + 1)) 0 (2 * K + 1)))
          (mul (Fsum (sinTerm (a.seq (2 * RaltReal_R (Radd a b) N + 1))) (2 * K + 1))
            (Fsum (sinTerm (b.seq (2 * RaltReal_R (Radd a b) N + 1))) (2 * K + 1)))
          ((Rmul (Rcos a) (Rcos b)).seq (2 * N + 1)) ((Rmul (Rsin a) (Rsin b)).seq (2 * N + 1))
          hCCden hSSden hBden hDden)
        (Qadd_le_add
          (Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hCCden hCCnden))
              (Qabs_den_pos (Qsub_den_pos hCCnden hBden)))
            (Qabs_sub_triangle hCCden hCCnden hBden) (Qadd_le_add hb3 hb4))
          (Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hSSden hSSnden))
              (Qabs_den_pos (Qsub_den_pos hSSnden hDden)))
            (Qabs_sub_triangle hSSden hSSnden hDden) (Qadd_le_add hb5' hb6')))))))
  exact Qle_trans
    (add_den_pos (Nat.succ_pos N) (add_den_pos (Nat.succ_pos N)
      (add_den_pos (add_den_pos (Nat.succ_pos N) (Nat.succ_pos N))
        (add_den_pos (Nat.succ_pos N) (Nat.succ_pos N)))))
    htotal (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor))

-- ===========================================================================
-- The **`sin(a+b)` cross-Cauchy theory** — general (odd) degree antidiagonal + mixed pairing.
-- ===========================================================================

/-- **General-degree pair term** `aᵖ·b^{d−p}/(p!·(d−p)!)` (the `pairTerm` total degree `2m` is now an
    arbitrary `d`; the `sin(a+b)` cross-diagonals live at the odd degree `d = 2m+1`). -/
def pairTermD (a b : Q) (d p : Nat) : Q :=
  mul (mul (qpow a p) (qpow b (d - p))) ⟨1, fct p * fct (d - p)⟩

theorem pairTermD_den_pos {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (d p : Nat) :
    0 < (pairTermD a b d p).den :=
  Qmul_den_pos (Qmul_den_pos (qpow_den_pos had p) (qpow_den_pos hbd _))
    (Nat.mul_pos (fct_pos _) (fct_pos _))

/-- **Per-term scaling, general degree**: `C(d,p)·aᵖ·b^{d−p} / d! = aᵖ·b^{d−p}/(p!·(d−p)!)`. -/
theorem binTermD_scaled_eq {a b : Q} (d : Nat) {p : Nat} (hp : p ≤ d) :
    Qeq (mul (⟨1, fct d⟩ : Q) (binTerm a b d p)) (pairTermD a b d p) := by
  have hkeyZ : (choose d p : Int) * (fct p : Int) * (fct (d - p) : Int) = (fct d : Int) := by
    exact_mod_cast choose_mul_fct_mul_fct hp
  show Qeq (mul (⟨1, fct d⟩ : Q)
      (mul (⟨(choose d p : Int), 1⟩ : Q) (mul (qpow a p) (qpow b (d - p)))))
    (mul (mul (qpow a p) (qpow b (d - p))) ⟨1, fct p * fct (d - p)⟩)
  simp only [Qeq, mul]
  push_cast
  generalize (qpow a p).num = an
  generalize (qpow b (d - p)).num = bn
  generalize ((qpow a p).den : Int) = ad
  generalize ((qpow b (d - p)).den : Int) = bd
  generalize ((choose d p : Nat) : Int) = cc at hkeyZ ⊢
  generalize ((fct p : Nat) : Int) = fp at hkeyZ ⊢
  generalize ((fct (d - p) : Nat) : Int) = fq at hkeyZ ⊢
  generalize ((fct d : Nat) : Int) = ff at hkeyZ ⊢
  rw [← hkeyZ]; ring_uor

/-- **The general-degree antidiagonal**: `(a+b)^d/d! = Σ_{p=0}^{d} aᵖ·b^{d−p}/(p!·(d−p)!)`. -/
theorem addPow_div_diag {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (d : Nat) :
    Qeq (mul (qpow (add a b) d) ⟨1, fct d⟩) (Fsum (pairTermD a b d) d) := by
  have hbtd : ∀ i, 0 < (binTerm a b d i).den := binTerm_den_pos had hbd _
  have hcd : 0 < (⟨1, fct d⟩ : Q).den := fct_pos _
  have h1 : Qeq (mul (qpow (add a b) d) ⟨1, fct d⟩)
      (mul (⟨1, fct d⟩ : Q) (Fsum (binTerm a b d) d)) :=
    Qeq_trans (Qmul_den_pos (Fsum_den_pos hbtd _) hcd)
      (Qmul_congr (binomial had hbd _) (Qeq_refl _)) (Qmul_swap _ _)
  have h2 : Qeq (mul (⟨1, fct d⟩ : Q) (Fsum (binTerm a b d) d)) (Fsum (pairTermD a b d) d) :=
    Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos hcd (hbtd i)) _)
      (Qeq_symm (Fsum_mul_left hcd hbtd _))
      (Fsum_congr_le (fun i hi => binTermD_scaled_eq d (by omega : i ≤ d)))
  exact Qeq_trans (Qmul_den_pos hcd (Fsum_den_pos hbtd _)) h1 h2

/-- **Mixed-offset paired alternating-term identity**: the product of the `off1`-shifted `j`-th term of
    `a` and the `off2`-shifted `(m−j)`-th term of `b` equals `(−1)ᵐ·a^{2j}·b^{2(m−j)}/((2j+off1)!·(2(m−j)+off2)!)`.
    (Generalizes `altPair_eq` to independent offsets — the `sin·cos` cross-diagonal needs `off1=1, off2=0`.) -/
theorem altPairMixed_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) {j m : Nat} (hjm : j ≤ m)
    (off1 off2 : Nat) :
    Qeq (mul (altTerm a off1 j) (altTerm b off2 (m - j)))
        (mul (qpow (⟨-1, 1⟩ : Q) m)
          (mul (mul (qpow a (2 * j)) (qpow b (2 * (m - j))))
            ⟨1, fct (2 * j + off1) * fct (2 * (m - j) + off2)⟩)) := by
  have hP1 : 0 < (qpow (neg (mul a a)) j).den := qpow_den_pos (Nat.mul_pos had had) j
  have hP2 : 0 < (qpow (neg (mul b b)) (m - j)).den := qpow_den_pos (Nat.mul_pos hbd hbd) (m - j)
  have hF1 : 0 < (⟨1, fct (2 * j + off1)⟩ : Q).den := fct_pos _
  have hF2 : 0 < (⟨1, fct (2 * (m - j) + off2)⟩ : Q).den := fct_pos _
  have hSm : 0 < (qpow (⟨-1, 1⟩ : Q) m).den := qpow_den_pos (by decide) m
  have hA : 0 < (qpow a (2 * j)).den := qpow_den_pos had (2 * j)
  have hB : 0 < (qpow b (2 * (m - j))).den := qpow_den_pos hbd (2 * (m - j))
  simp only [altTerm]
  refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hP1 hP2) (Qmul_den_pos hF1 hF2))
    (Qmul4_rearrange _ _ _ _) ?_
  refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hSm (Qmul_den_pos hA hB))
      (Nat.mul_pos (fct_pos _) (fct_pos _) :
        0 < (⟨1, fct (2 * j + off1) * fct (2 * (m - j) + off2)⟩ : Q).den))
    (Qmul_congr (negsq_pair had hbd hjm) (mul_inv_dens _ _)) ?_
  exact Qeq_symm (Qmul_assoc3 _ _ _)

/-- **The `sin·cos` cross-diagonal term** `sinTermⱼ(a)·cosT_{m−j}(b) ≈ (−1)ᵐ·pairTermD(2m+1, 2j+1)`. -/
theorem scPair_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) {j m : Nat} (hjm : j ≤ m) :
    Qeq (mul (sinTerm a j) (altTerm b 0 (m - j)))
        (mul (qpow (⟨-1, 1⟩ : Q) m) (pairTermD a b (2 * m + 1) (2 * j + 1))) := by
  have hr : 2 * m + 1 - (2 * j + 1) = 2 * (m - j) := by omega
  have hstep : Qeq (mul (sinTerm a j) (altTerm b 0 (m - j)))
      (mul a (mul (qpow (⟨-1, 1⟩ : Q) m)
        (mul (mul (qpow a (2 * j)) (qpow b (2 * (m - j))))
          ⟨1, fct (2 * j + 1) * fct (2 * (m - j) + 0)⟩))) := by
    show Qeq (mul (mul a (altTerm a 1 j)) (altTerm b 0 (m - j))) _
    refine Qeq_trans (Qmul_den_pos had (Qmul_den_pos (altTerm_den_pos had 1 j) (altTerm_den_pos hbd 0 _)))
      (Qeq_symm (Qmul_assoc3 a (altTerm a 1 j) (altTerm b 0 (m - j)))) ?_
    exact Qmul_congr (Qeq_refl _) (altPairMixed_eq had hbd hjm 1 0)
  refine Qeq_trans (Qmul_den_pos had (Qmul_den_pos (qpow_den_pos (by decide) m)
      (Qmul_den_pos (Qmul_den_pos (qpow_den_pos had _) (qpow_den_pos hbd _))
        (Nat.mul_pos (fct_pos _) (fct_pos _))))) hstep ?_
  simp only [pairTermD, hr, qpow_succ, Nat.add_zero]
  simp only [Qeq, mul]
  generalize a.num = an; generalize (a.den : Int) = ad
  generalize (qpow a (2 * j)).num = aA; generalize ((qpow a (2 * j)).den : Int) = aD
  generalize (qpow b (2 * (m - j))).num = bB; generalize ((qpow b (2 * (m - j))).den : Int) = bD
  generalize (qpow (⟨-1, 1⟩ : Q) m).num = sn; generalize ((qpow (⟨-1, 1⟩ : Q) m).den : Int) = sd
  push_cast
  generalize ((fct (2 * j + 1) : Nat) : Int) = f1
  generalize ((fct (2 * (m - j)) : Nat) : Int) = f2
  ring_uor

/-- **The `cos·sin` cross-diagonal term** `cosTermⱼ(a)·sinT_{m−j}(b) ≈ (−1)ᵐ·pairTermD(2m+1, 2j)`. -/
theorem csPair_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) {j m : Nat} (hjm : j ≤ m) :
    Qeq (mul (altTerm a 0 j) (sinTerm b (m - j)))
        (mul (qpow (⟨-1, 1⟩ : Q) m) (pairTermD a b (2 * m + 1) (2 * j))) := by
  have hr : 2 * m + 1 - 2 * j = 2 * (m - j) + 1 := by omega
  have hstep : Qeq (mul (altTerm a 0 j) (sinTerm b (m - j)))
      (mul b (mul (qpow (⟨-1, 1⟩ : Q) m)
        (mul (mul (qpow a (2 * j)) (qpow b (2 * (m - j))))
          ⟨1, fct (2 * j + 0) * fct (2 * (m - j) + 1)⟩))) := by
    show Qeq (mul (altTerm a 0 j) (mul b (altTerm b 1 (m - j)))) _
    refine Qeq_trans (Qmul_den_pos hbd
        (Qmul_den_pos (altTerm_den_pos had 0 j) (altTerm_den_pos hbd 1 (m - j)))) ?_ ?_
    · refine Qeq_trans (Qmul_den_pos (Qmul_den_pos (altTerm_den_pos had 0 j) hbd)
          (altTerm_den_pos hbd 1 (m - j)))
        (Qmul_assoc3 (altTerm a 0 j) b (altTerm b 1 (m - j))) ?_
      refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hbd (altTerm_den_pos had 0 j))
          (altTerm_den_pos hbd 1 (m - j)))
        (Qmul_congr (Qmul_swap (altTerm a 0 j) b) (Qeq_refl _)) ?_
      exact Qeq_symm (Qmul_assoc3 b (altTerm a 0 j) (altTerm b 1 (m - j)))
    · exact Qmul_congr (Qeq_refl _) (altPairMixed_eq had hbd hjm 0 1)
  refine Qeq_trans (Qmul_den_pos hbd (Qmul_den_pos (qpow_den_pos (by decide) m)
      (Qmul_den_pos (Qmul_den_pos (qpow_den_pos had _) (qpow_den_pos hbd _))
        (Nat.mul_pos (fct_pos _) (fct_pos _))))) hstep ?_
  simp only [pairTermD, hr, qpow_succ, Nat.add_zero]
  simp only [Qeq, mul]
  generalize b.num = bn; generalize (b.den : Int) = bd
  generalize (qpow a (2 * j)).num = aA; generalize ((qpow a (2 * j)).den : Int) = aD
  generalize (qpow b (2 * (m - j))).num = bB; generalize ((qpow b (2 * (m - j))).den : Int) = bD
  generalize (qpow (⟨-1, 1⟩ : Q) m).num = sn; generalize ((qpow (⟨-1, 1⟩ : Q) m).den : Int) = sd
  push_cast
  generalize ((fct (2 * j) : Nat) : Int) = f1
  generalize ((fct (2 * (m - j) + 1) : Nat) : Int) = f2
  ring_uor

/-- **Odd-degree parity split**: `Σ_{p=0}^{2m+1} a(p) = Σ_{j=0}^{m} a(2j) + Σ_{j=0}^{m} a(2j+1)`. -/
theorem Fsum_parity_split_odd (a : Nat → Q) (ha : ∀ i, 0 < (a i).den) :
    ∀ m, Qeq (Fsum a (2 * m + 1))
      (add (Fsum (fun j => a (2 * j)) m) (Fsum (fun j => a (2 * j + 1)) m))
  | 0 => Qeq_refl _
  | (m + 1) => by
      show Qeq (add (add (Fsum a (2 * m + 1)) (a (2 * m + 1 + 1))) (a (2 * m + 1 + 1 + 1)))
        (add (add (Fsum (fun j => a (2 * j)) m) (a (2 * (m + 1))))
          (add (Fsum (fun j => a (2 * j + 1)) m) (a (2 * (m + 1) + 1))))
      have he1 : a (2 * m + 1 + 1) = a (2 * (m + 1)) := by rw [show 2 * m + 1 + 1 = 2 * (m + 1) from by omega]
      have he2 : a (2 * m + 1 + 1 + 1) = a (2 * (m + 1) + 1) := by
        rw [show 2 * m + 1 + 1 + 1 = 2 * (m + 1) + 1 from by omega]
      rw [he1, he2]
      refine Qeq_trans
        (add_den_pos (add_den_pos (add_den_pos (Fsum_den_pos (fun j => ha (2 * j)) m)
          (Fsum_den_pos (fun j => ha (2 * j + 1)) m)) (ha (2 * (m + 1)))) (ha (2 * (m + 1) + 1)))
        (Qadd_congr (Qadd_congr (Fsum_parity_split_odd a ha m) (Qeq_refl _)) (Qeq_refl _)) ?_
      generalize Fsum (fun j => a (2 * j)) m = E
      generalize Fsum (fun j => a (2 * j + 1)) m = O
      simp only [Qeq, add]; push_cast; ring_uor

/-- The degree-`m` `cos·sin` cross-diagonal `Σ_{i≤m} cosTermᵢ(a)·sinT_{m−i}(b)`. -/
def csConv (a b : Q) (m : Nat) : Q := Fsum (fun i => mul (altTerm a 0 i) (sinTerm b (m - i))) m

/-- The degree-`m` `sin·cos` cross-diagonal `Σ_{i≤m} sinTermᵢ(a)·cosT_{m−i}(b)`. -/
def scConv (a b : Q) (m : Nat) : Q := Fsum (fun i => mul (sinTerm a i) (altTerm b 0 (m - i))) m

theorem csConv_den_pos {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m : Nat) :
    0 < (csConv a b m).den :=
  Fsum_den_pos (fun i => Qmul_den_pos (altTerm_den_pos had 0 i) (sinTerm_den_pos hbd (m - i))) m

theorem scConv_den_pos {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m : Nat) :
    0 < (scConv a b m).den :=
  Fsum_den_pos (fun i => Qmul_den_pos (sinTerm_den_pos had i) (altTerm_den_pos hbd 0 (m - i))) m

/-- The `cos·sin` cross-diagonal factors as `(−1)ᵐ · Σ_j pairTermD(2m+1, 2j)`. -/
theorem csConv_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m : Nat) :
    Qeq (csConv a b m)
        (mul (qpow (⟨-1, 1⟩ : Q) m) (Fsum (fun j => pairTermD a b (2 * m + 1) (2 * j)) m)) := by
  simp only [csConv]
  refine Qeq_trans (Fsum_den_pos (fun j => Qmul_den_pos (qpow_den_pos (by decide) m)
      (pairTermD_den_pos had hbd _ _)) m)
    (Fsum_congr_le (fun j hj => csPair_eq had hbd (by omega : j ≤ m))) ?_
  exact Fsum_mul_left (qpow_den_pos (by decide) m) (fun j => pairTermD_den_pos had hbd _ _) m

/-- The `sin·cos` cross-diagonal factors as `(−1)ᵐ · Σ_j pairTermD(2m+1, 2j+1)`. -/
theorem scConv_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m : Nat) :
    Qeq (scConv a b m)
        (mul (qpow (⟨-1, 1⟩ : Q) m) (Fsum (fun j => pairTermD a b (2 * m + 1) (2 * j + 1)) m)) := by
  simp only [scConv]
  refine Qeq_trans (Fsum_den_pos (fun j => Qmul_den_pos (qpow_den_pos (by decide) m)
      (pairTermD_den_pos had hbd _ _)) m)
    (Fsum_congr_le (fun j hj => scPair_eq had hbd (by omega : j ≤ m))) ?_
  exact Fsum_mul_left (qpow_den_pos (by decide) m) (fun j => pairTermD_den_pos had hbd _ _) m

/-- **The sin diagonal addition identity**: the degree-`m` term of `sin(a+b)` equals the sum of the two
    cross-diagonals — the per-degree `sin(a+b) = cos a·sin b + sin a·cos b`. From the odd-degree
    antidiagonal (`addPow_div_diag` at `2m+1`), extracting the sign `(−1)ᵐ` and matching the even/odd
    `p`-sums to the `cos·sin`/`sin·cos` cross-diagonals (`csConv_eq`/`scConv_eq`). -/
theorem sinTerm_add_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m : Nat) :
    Qeq (sinTerm (add a b) m) (add (csConv a b m) (scConv a b m)) := by
  have habd : 0 < (add a b).den := add_den_pos had hbd
  have hEd : 0 < (Fsum (fun j => pairTermD a b (2 * m + 1) (2 * j)) m).den :=
    Fsum_den_pos (fun j => pairTermD_den_pos had hbd _ _) _
  have hOd : 0 < (Fsum (fun j => pairTermD a b (2 * m + 1) (2 * j + 1)) m).den :=
    Fsum_den_pos (fun j => pairTermD_den_pos had hbd _ _) _
  have hS1d : 0 < (qpow (⟨-1, 1⟩ : Q) m).den := qpow_den_pos (by decide) _
  -- step 1: `sinTerm(a+b,m) ≈ (−1)ᵐ · ((a+b)^{2m+1}/(2m+1)!) ≈ (−1)ᵐ · (E + O)`.
  have hsign : Qeq (sinTerm (add a b) m)
      (mul (qpow (⟨-1, 1⟩ : Q) m) (mul (qpow (add a b) (2 * m + 1)) ⟨1, fct (2 * m + 1)⟩)) := by
    show Qeq (mul (add a b) (mul (qpow (neg (mul (add a b) (add a b))) m) ⟨1, fct (2 * m + 1)⟩))
      (mul (qpow (⟨-1, 1⟩ : Q) m) (mul (qpow (add a b) (2 * m + 1)) ⟨1, fct (2 * m + 1)⟩))
    refine Qeq_trans (Qmul_den_pos habd (Qmul_den_pos (Qmul_den_pos hS1d (qpow_den_pos habd _)) (fct_pos _)))
      (Qmul_congr (Qeq_refl _) (Qmul_congr (qpow_negsq habd m) (Qeq_refl _))) ?_
    rw [show qpow (add a b) (2 * m + 1) = mul (add a b) (qpow (add a b) (2 * m)) from qpow_succ _ _]
    simp only [Qeq, mul]
    generalize (add a b).num = xn; generalize ((add a b).den : Int) = xd
    generalize (qpow (add a b) (2 * m)).num = pn; generalize ((qpow (add a b) (2 * m)).den : Int) = pd
    generalize (qpow (⟨-1, 1⟩ : Q) m).num = sn; generalize ((qpow (⟨-1, 1⟩ : Q) m).den : Int) = sd
    push_cast
    generalize ((fct (2 * m + 1) : Nat) : Int) = f1
    ring_uor
  have hanti : Qeq (mul (qpow (add a b) (2 * m + 1)) ⟨1, fct (2 * m + 1)⟩)
      (Fsum (pairTermD a b (2 * m + 1)) (2 * m + 1)) := addPow_div_diag had hbd (2 * m + 1)
  have hsplit : Qeq (Fsum (pairTermD a b (2 * m + 1)) (2 * m + 1))
      (add (Fsum (fun j => pairTermD a b (2 * m + 1) (2 * j)) m)
           (Fsum (fun j => pairTermD a b (2 * m + 1) (2 * j + 1)) m)) :=
    Fsum_parity_split_odd (pairTermD a b (2 * m + 1)) (fun i => pairTermD_den_pos had hbd _ _) m
  have hfull : Qeq (mul (qpow (add a b) (2 * m + 1)) ⟨1, fct (2 * m + 1)⟩)
      (add (Fsum (fun j => pairTermD a b (2 * m + 1) (2 * j)) m)
           (Fsum (fun j => pairTermD a b (2 * m + 1) (2 * j + 1)) m)) :=
    Qeq_trans (Fsum_den_pos (pairTermD_den_pos had hbd (2 * m + 1)) (2 * m + 1)) hanti hsplit
  have hstep1 : Qeq (sinTerm (add a b) m)
      (add (mul (qpow (⟨-1, 1⟩ : Q) m) (Fsum (fun j => pairTermD a b (2 * m + 1) (2 * j)) m))
           (mul (qpow (⟨-1, 1⟩ : Q) m) (Fsum (fun j => pairTermD a b (2 * m + 1) (2 * j + 1)) m))) :=
    Qeq_trans (Qmul_den_pos hS1d (Qmul_den_pos (qpow_den_pos habd _) (fct_pos _))) hsign
      (Qeq_trans (Qmul_den_pos hS1d (add_den_pos hEd hOd))
        (Qmul_congr (Qeq_refl _) hfull) (Qmul_add_left _ _ _))
  refine Qeq_trans (add_den_pos (Qmul_den_pos hS1d hEd) (Qmul_den_pos hS1d hOd)) hstep1 ?_
  exact Qadd_congr (Qeq_symm (csConv_eq had hbd m)) (Qeq_symm (scConv_eq had hbd m))

/-- **The `sin(a+b)` partial-sum identity**: `Σ_{m≤N} sinTerm(a+b,m) = Σ cos·sin diag + Σ sin·cos diag`
    (sum the per-degree `sinTerm_add_eq` and distribute `Fsum` over the addition). -/
theorem sinAdd_partial_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (N : Nat) :
    Qeq (Fsum (sinTerm (add a b)) N) (add (Fsum (csConv a b) N) (Fsum (scConv a b) N)) :=
  Qeq_trans (Fsum_den_pos (fun m => add_den_pos (csConv_den_pos had hbd m) (scConv_den_pos had hbd m)) N)
    (Fsum_congr_le (fun m _ => sinTerm_add_eq had hbd m))
    (Fsum_add (csConv_den_pos had hbd) (scConv_den_pos had hbd) N)

/-- **Cauchy product for `cos·sin`** (partial sums): `(Σcos a)(Σsin b) = Σ_{m≤N} csConv(m) + corner`. -/
theorem csCauchy_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (N : Nat) :
    Qeq (mul (altSum a 0 N) (Fsum (sinTerm b) N))
      (add (Fsum (csConv a b) N)
        (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a 0 i) (sinTerm b j)) N)
          (Fsum (fun j => mul (altTerm a 0 i) (sinTerm b j)) (N - i))) N)) := by
  rw [altSum_eq_Fsum]
  exact fsum_cauchy (altTerm_den_pos had 0) (sinTerm_den_pos hbd) N

/-- **Cauchy product for `sin·cos`** (partial sums): `(Σsin a)(Σcos b) = Σ_{m≤N} scConv(m) + corner`. -/
theorem scCauchy_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (N : Nat) :
    Qeq (mul (Fsum (sinTerm a) N) (altSum b 0 N))
      (add (Fsum (scConv a b) N)
        (Fsum (fun i => Qsub (Fsum (fun j => mul (sinTerm a i) (altTerm b 0 j)) N)
          (Fsum (fun j => mul (sinTerm a i) (altTerm b 0 j)) (N - i))) N)) := by
  rw [altSum_eq_Fsum]
  exact fsum_cauchy (sinTerm_den_pos had) (altTerm_den_pos hbd 0) N

/-- `(Cs+Sc) − ((Cs+cs)+(Sc+sc)) ≈ −(cs+sc)`. -/
private theorem sinResid_rearrange (Cs Sc cs sc : Q) :
    Qeq (Qsub (add Cs Sc) (add (add Cs cs) (add Sc sc))) (neg (add cs sc)) := by
  simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor

/-- **The `sin(a+b)` residual identity**: `sin(a+b) − (cos a·sin b + sin a·cos b)` (partial sums) equals
    `−(corner_cs + corner_sc)` — the two high Mertens corners. (Both cross-Cauchy products contribute
    their diagonal to `sin(a+b)`, so the residual is *just* the corners — no extra top-diagonal, unlike
    `cos(a+b)` whose subtraction left a `sinConv` tail.) -/
theorem sinAdd_resid_eq {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (N : Nat) :
    Qeq (Qsub (Fsum (sinTerm (add a b)) N)
        (add (mul (altSum a 0 N) (Fsum (sinTerm b) N)) (mul (Fsum (sinTerm a) N) (altSum b 0 N))))
      (neg (add
        (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a 0 i) (sinTerm b j)) N)
          (Fsum (fun j => mul (altTerm a 0 i) (sinTerm b j)) (N - i))) N)
        (Fsum (fun i => Qsub (Fsum (fun j => mul (sinTerm a i) (altTerm b 0 j)) N)
          (Fsum (fun j => mul (sinTerm a i) (altTerm b 0 j)) (N - i))) N))) := by
  have hCsd : 0 < (Fsum (csConv a b) N).den := Fsum_den_pos (csConv_den_pos had hbd) N
  have hScd : 0 < (Fsum (scConv a b) N).den := Fsum_den_pos (scConv_den_pos had hbd) N
  have hccd : 0 < (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a 0 i) (sinTerm b j)) N)
      (Fsum (fun j => mul (altTerm a 0 i) (sinTerm b j)) (N - i))) N).den :=
    Fsum_den_pos (fun i => Qsub_den_pos
      (Fsum_den_pos (fun j => Qmul_den_pos (altTerm_den_pos had 0 i) (sinTerm_den_pos hbd j)) N)
      (Fsum_den_pos (fun j => Qmul_den_pos (altTerm_den_pos had 0 i) (sinTerm_den_pos hbd j)) (N - i))) N
  have hscd : 0 < (Fsum (fun i => Qsub (Fsum (fun j => mul (sinTerm a i) (altTerm b 0 j)) N)
      (Fsum (fun j => mul (sinTerm a i) (altTerm b 0 j)) (N - i))) N).den :=
    Fsum_den_pos (fun i => Qsub_den_pos
      (Fsum_den_pos (fun j => Qmul_den_pos (sinTerm_den_pos had i) (altTerm_den_pos hbd 0 j)) N)
      (Fsum_den_pos (fun j => Qmul_den_pos (sinTerm_den_pos had i) (altTerm_den_pos hbd 0 j)) (N - i))) N
  refine Qeq_trans (Qsub_den_pos (add_den_pos hCsd hScd)
      (add_den_pos (add_den_pos hCsd hccd) (add_den_pos hScd hscd)))
    (QsubCongr (sinAdd_partial_eq had hbd N)
      (Qadd_congr (csCauchy_eq had hbd N) (scCauchy_eq had hbd N))) ?_
  exact sinResid_rearrange _ _ _ _

-- ===========================================================================
-- **Mixed-offset corner Mertens bound** — the cross corners use `off1` for `a`, `off2` for `b`.
-- ===========================================================================

/-- Mixed-offset factored corner (generalizes `altCorner_factored2` to independent offsets). -/
theorem altCorner_factored2_mixed {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (off1 off2 N : Nat) :
    Qeq (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a off1 i) (altTerm b off2 j)) N)
          (Fsum (fun j => mul (altTerm a off1 i) (altTerm b off2 j)) (N - i))) N)
      (Fsum (fun i => mul (altTerm a off1 i)
          (Qsub (Fsum (altTerm b off2) N) (Fsum (altTerm b off2) (N - i)))) N) := by
  have hbt : ∀ j, 0 < (altTerm b off2 j).den := altTerm_den_pos hbd off2
  refine Fsum_congr (fun i => ?_) N
  exact Qeq_trans
    (Qsub_den_pos (Qmul_den_pos (altTerm_den_pos had off1 i) (Fsum_den_pos hbt N))
      (Qmul_den_pos (altTerm_den_pos had off1 i) (Fsum_den_pos hbt (N - i))))
    (QsubCongr (Fsum_mul_left (altTerm_den_pos had off1 i) hbt N)
      (Fsum_mul_left (altTerm_den_pos had off1 i) hbt (N - i)))
    (Qeq_symm (Qmul_sub_distrib (altTerm a off1 i) (Fsum (altTerm b off2) N)
      (Fsum (altTerm b off2) (N - i))))

/-- Mixed-offset `|corner| ≤ Σᵢ |altTerm a off1 i · gap_b|`. -/
theorem altCorner_abs_le2_mixed {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (off1 off2 N : Nat) :
    Qle (Qabs (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a off1 i) (altTerm b off2 j)) N)
          (Fsum (fun j => mul (altTerm a off1 i) (altTerm b off2 j)) (N - i))) N))
      (Fsum (fun i => Qabs (mul (altTerm a off1 i)
          (Qsub (Fsum (altTerm b off2) N) (Fsum (altTerm b off2) (N - i))))) N) := by
  have hbt : ∀ j, 0 < (altTerm b off2 j).den := altTerm_den_pos hbd off2
  have hh : ∀ i, 0 < (mul (altTerm a off1 i)
      (Qsub (Fsum (altTerm b off2) N) (Fsum (altTerm b off2) (N - i)))).den :=
    fun i => Qmul_den_pos (altTerm_den_pos had off1 i)
      (Qsub_den_pos (Fsum_den_pos hbt N) (Fsum_den_pos hbt (N - i)))
  exact Qle_congr_left (Qabs_den_pos (Fsum_den_pos hh N))
    (Qeq_symm (Qabs_Qeq (altCorner_factored2_mixed had hbd off1 off2 N))) (Fsum_abs_le hh N)

/-- **Mixed-offset Mertens corner bound** at `2K+1` (`a` at `off1`, `b` at `off2`, `M` bounds both):
    `|corner| ≤ U·4(M²)^{K+2}/(K+2)! + 2(M²)^{K+1}/(K+1)!·U → 0`. Same shape as `cornerMertens2`, with
    the `a`-factor sums at `off1` and the `b`-factor tails/gaps at `off2`. -/
theorem cornerMertens2_mixed {a b : Q} {M : Nat} (had : 0 < a.den) (hbd : 0 < b.den)
    (ha : Qle (Qabs a) ⟨(M : Int), 1⟩) (hb : Qle (Qabs b) ⟨(M : Int), 1⟩) (off1 off2 K : Nat)
    (hK : 2 * (M * M) ≤ K + 2) :
    Qle (Qabs (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a off1 i) (altTerm b off2 j)) (2 * K + 1))
          (Fsum (fun j => mul (altTerm a off1 i) (altTerm b off2 j)) (2 * K + 1 - i))) (2 * K + 1)))
      (add (mul (expM_U (M * M) (2 * (M * M))) ⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩)
        (mul ⟨(2 * npow (M * M) (K + 1) : Int), fct (K + 1)⟩ (expM_U (M * M) (2 * (M * M))))) := by
  have hat : ∀ i, 0 < (altTerm a off1 i).den := altTerm_den_pos had off1
  have hbt : ∀ j, 0 < (altTerm b off2 j).den := altTerm_den_pos hbd off2
  have htd : ∀ i, 0 < (Qsub (Fsum (altTerm b off2) (2 * K + 1)) (Fsum (altTerm b off2) (2 * K + 1 - i))).den :=
    fun i => Qsub_den_pos (Fsum_den_pos hbt (2 * K + 1)) (Fsum_den_pos hbt (2 * K + 1 - i))
  have hh : ∀ i, 0 < (Qabs (mul (altTerm a off1 i)
      (Qsub (Fsum (altTerm b off2) (2 * K + 1)) (Fsum (altTerm b off2) (2 * K + 1 - i))))).den :=
    fun i => Qabs_den_pos (Qmul_den_pos (hat i) (htd i))
  have hCnn : (0 : Int) ≤ (4 * npow (M * M) (K + 2) : Int) := Int.ofNat_nonneg _
  have hUnn : (0 : Int) ≤ (expM_U (M * M) (2 * (M * M))).num := expM_U_num_nonneg _ _
  have hlow : Qle (Fsum (fun i => Qabs (mul (altTerm a off1 i)
        (Qsub (Fsum (altTerm b off2) (2 * K + 1)) (Fsum (altTerm b off2) (2 * K + 1 - i))))) K)
      (mul (expM_U (M * M) (2 * (M * M))) ⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩) := by
    have hmid : Qle (Fsum (fun i => Qabs (mul (altTerm a off1 i)
          (Qsub (Fsum (altTerm b off2) (2 * K + 1)) (Fsum (altTerm b off2) (2 * K + 1 - i))))) K)
        (Fsum (fun i => mul (Qabs (altTerm a off1 i))
          (⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩ : Q)) K) :=
      Fsum_le_congr (fun i hi => by
        rw [Qabs_mul]
        exact Qmul_le_mul_left (Qabs_num_nonneg _) (altTail_deep_le hbd hb off2 K i hi (by omega)))
    exact Qle_trans (Fsum_den_pos (fun i => Qmul_den_pos (Qabs_den_pos (hat i)) (fct_pos _)) K) hmid
      (Qle_trans (Qmul_den_pos (Fsum_den_pos (fun i => Qabs_den_pos (hat i)) K) (fct_pos _))
        (Qeq_le (Qeq_symm (Fsum_mul_const_right (fct_pos _) (fun i => Qabs_den_pos (hat i)) K)))
        (Qmul_le_mul_right hCnn (altAbsSum_le_U had ha off1 K)))
  have hhigh : Qle (Fsum (fun i' => Qabs (mul (altTerm a off1 (K + 1 + i'))
        (Qsub (Fsum (altTerm b off2) (2 * K + 1)) (Fsum (altTerm b off2) (2 * K + 1 - (K + 1 + i')))))) K)
      (mul ⟨(2 * npow (M * M) (K + 1) : Int), fct (K + 1)⟩ (expM_U (M * M) (2 * (M * M)))) := by
    have hmid : Qle (Fsum (fun i' => Qabs (mul (altTerm a off1 (K + 1 + i'))
          (Qsub (Fsum (altTerm b off2) (2 * K + 1)) (Fsum (altTerm b off2) (2 * K + 1 - (K + 1 + i')))))) K)
        (Fsum (fun i' => mul (Qabs (altTerm a off1 (K + 1 + i')))
          (expM_U (M * M) (2 * (M * M)))) K) :=
      Fsum_le_congr (fun i' _ => by
        rw [Qabs_mul]
        exact Qmul_le_mul_left (Qabs_num_nonneg _)
          (altGap_le_U hbd hb off2 (a := 2 * K + 1 - (K + 1 + i')) (b := 2 * K + 1) (by omega)))
    exact Qle_trans (Fsum_den_pos (fun i' => Qmul_den_pos (Qabs_den_pos (hat (K + 1 + i')))
        (expM_U_den_pos (M * M) (2 * (M * M)))) K) hmid
      (Qle_trans (Qmul_den_pos (Fsum_den_pos (fun i' => Qabs_den_pos (hat (K + 1 + i'))) K)
        (expM_U_den_pos (M * M) (2 * (M * M))))
        (Qeq_le (Qeq_symm (Fsum_mul_const_right (expM_U_den_pos (M * M) (2 * (M * M)))
          (fun i' => Qabs_den_pos (hat (K + 1 + i'))) K)))
        (Qmul_le_mul_right hUnn (altAbsTail_le had ha off1 K K hK)))
  refine Qle_trans (Fsum_den_pos hh (2 * K + 1)) (altCorner_abs_le2_mixed had hbd off1 off2 (2 * K + 1)) ?_
  refine Qle_trans (add_den_pos (Fsum_den_pos hh K)
      (Fsum_den_pos (fun i' => hh (K + 1 + i')) K)) (Qeq_le (Fsum_split_at _ hh K)) ?_
  exact Qadd_le_add hlow hhigh

/-- **Factor `b` out of the `cos·sin` corner**: `corner_cs = b·(off_a=0, off_b=1 mixed corner)`. -/
theorem cornerCs_factored {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (N : Nat) :
    Qeq (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a 0 i) (sinTerm b j)) N)
          (Fsum (fun j => mul (altTerm a 0 i) (sinTerm b j)) (N - i))) N)
      (mul b (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a 0 i) (altTerm b 1 j)) N)
        (Fsum (fun j => mul (altTerm a 0 i) (altTerm b 1 j)) (N - i))) N)) := by
  have hat0 : ∀ i, 0 < (altTerm a 0 i).den := altTerm_den_pos had 0
  have hbt1 : ∀ j, 0 < (altTerm b 1 j).den := altTerm_den_pos hbd 1
  have haltd : ∀ i j, 0 < (mul (altTerm a 0 i) (altTerm b 1 j)).den := fun i j => Qmul_den_pos (hat0 i) (hbt1 j)
  have hsubd : ∀ i, 0 < (Qsub (Fsum (fun j => mul (altTerm a 0 i) (altTerm b 1 j)) N)
      (Fsum (fun j => mul (altTerm a 0 i) (altTerm b 1 j)) (N - i))).den :=
    fun i => Qsub_den_pos (Fsum_den_pos (fun j => haltd i j) N) (Fsum_den_pos (fun j => haltd i j) (N - i))
  have hsterm : ∀ i j, Qeq (mul (altTerm a 0 i) (sinTerm b j))
      (mul b (mul (altTerm a 0 i) (altTerm b 1 j))) := fun i j => by
    rw [sinTerm]
    refine Qeq_trans (Qmul_den_pos (Qmul_den_pos (hat0 i) hbd) (hbt1 j))
      (Qmul_assoc3 (altTerm a 0 i) b (altTerm b 1 j)) ?_
    refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hbd (hat0 i)) (hbt1 j))
      (Qmul_congr (Qmul_swap (altTerm a 0 i) b) (Qeq_refl _)) ?_
    exact Qeq_symm (Qmul_assoc3 b (altTerm a 0 i) (altTerm b 1 j))
  have hrow : ∀ i K, Qeq (Fsum (fun j => mul (altTerm a 0 i) (sinTerm b j)) K)
      (mul b (Fsum (fun j => mul (altTerm a 0 i) (altTerm b 1 j)) K)) := fun i K =>
    Qeq_trans (Fsum_den_pos (fun j => Qmul_den_pos hbd (haltd i j)) K)
      (Fsum_congr (fun j => hsterm i j) K) (Fsum_mul_left hbd (fun j => haltd i j) K)
  refine Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos hbd (hsubd i)) N)
    (Fsum_congr (fun i => Qeq_trans
      (Qsub_den_pos (Qmul_den_pos hbd (Fsum_den_pos (fun j => haltd i j) N))
        (Qmul_den_pos hbd (Fsum_den_pos (fun j => haltd i j) (N - i))))
      (QsubCongr (hrow i N) (hrow i (N - i)))
      (Qeq_symm (Qmul_sub_distrib b (Fsum (fun j => mul (altTerm a 0 i) (altTerm b 1 j)) N)
        (Fsum (fun j => mul (altTerm a 0 i) (altTerm b 1 j)) (N - i))))) N)
    (Fsum_mul_left hbd hsubd N)

/-- **Factor `a` out of the `sin·cos` corner**: `corner_sc = a·(off_a=1, off_b=0 mixed corner)`. -/
theorem cornerSc_factored {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (N : Nat) :
    Qeq (Fsum (fun i => Qsub (Fsum (fun j => mul (sinTerm a i) (altTerm b 0 j)) N)
          (Fsum (fun j => mul (sinTerm a i) (altTerm b 0 j)) (N - i))) N)
      (mul a (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 0 j)) N)
        (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 0 j)) (N - i))) N)) := by
  have hat1 : ∀ i, 0 < (altTerm a 1 i).den := altTerm_den_pos had 1
  have hbt0 : ∀ j, 0 < (altTerm b 0 j).den := altTerm_den_pos hbd 0
  have haltd : ∀ i j, 0 < (mul (altTerm a 1 i) (altTerm b 0 j)).den := fun i j => Qmul_den_pos (hat1 i) (hbt0 j)
  have hsubd : ∀ i, 0 < (Qsub (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 0 j)) N)
      (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 0 j)) (N - i))).den :=
    fun i => Qsub_den_pos (Fsum_den_pos (fun j => haltd i j) N) (Fsum_den_pos (fun j => haltd i j) (N - i))
  have hsterm : ∀ i j, Qeq (mul (sinTerm a i) (altTerm b 0 j))
      (mul a (mul (altTerm a 1 i) (altTerm b 0 j))) := fun i j => by
    rw [sinTerm]; exact Qeq_symm (Qmul_assoc3 a (altTerm a 1 i) (altTerm b 0 j))
  have hrow : ∀ i K, Qeq (Fsum (fun j => mul (sinTerm a i) (altTerm b 0 j)) K)
      (mul a (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 0 j)) K)) := fun i K =>
    Qeq_trans (Fsum_den_pos (fun j => Qmul_den_pos had (haltd i j)) K)
      (Fsum_congr (fun j => hsterm i j) K) (Fsum_mul_left had (fun j => haltd i j) K)
  refine Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos had (hsubd i)) N)
    (Fsum_congr (fun i => Qeq_trans
      (Qsub_den_pos (Qmul_den_pos had (Fsum_den_pos (fun j => haltd i j) N))
        (Qmul_den_pos had (Fsum_den_pos (fun j => haltd i j) (N - i))))
      (QsubCongr (hrow i N) (hrow i (N - i)))
      (Qeq_symm (Qmul_sub_distrib a (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 0 j)) N)
        (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 0 j)) (N - i))))) N)
    (Fsum_mul_left had hsubd N)

/-- **Bound on the `cos·sin` corner**: `|corner_cs(2K+1)| ≤ M·(Mertens bound) → 0`. -/
theorem cornerCs_le {a b : Q} {M : Nat} (had : 0 < a.den) (hbd : 0 < b.den)
    (ha : Qle (Qabs a) ⟨(M : Int), 1⟩) (hb : Qle (Qabs b) ⟨(M : Int), 1⟩) (K : Nat)
    (hK : 2 * (M * M) ≤ K + 2) :
    Qle (Qabs (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a 0 i) (sinTerm b j)) (2 * K + 1))
          (Fsum (fun j => mul (altTerm a 0 i) (sinTerm b j)) (2 * K + 1 - i))) (2 * K + 1)))
      (mul (⟨(M : Int), 1⟩ : Q)
        (add (mul (expM_U (M * M) (2 * (M * M))) ⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩)
          (mul ⟨(2 * npow (M * M) (K + 1) : Int), fct (K + 1)⟩ (expM_U (M * M) (2 * (M * M)))))) := by
  have haltd : ∀ i j, 0 < (mul (altTerm a 0 i) (altTerm b 1 j)).den :=
    fun i j => Qmul_den_pos (altTerm_den_pos had 0 i) (altTerm_den_pos hbd 1 j)
  have hcornerd : 0 < (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a 0 i) (altTerm b 1 j)) (2 * K + 1))
      (Fsum (fun j => mul (altTerm a 0 i) (altTerm b 1 j)) (2 * K + 1 - i))) (2 * K + 1)).den :=
    Fsum_den_pos (fun i => Qsub_den_pos (Fsum_den_pos (fun j => haltd i j) _)
      (Fsum_den_pos (fun j => haltd i j) _)) _
  refine Qle_congr_left (Qabs_den_pos (Qmul_den_pos hbd hcornerd))
    (Qeq_symm (Qabs_Qeq (cornerCs_factored had hbd (2 * K + 1)))) ?_
  rw [Qabs_mul]
  exact Qmul_le_mul (Qabs_den_pos hbd) Nat.one_pos (Qabs_den_pos hcornerd)
    (Qabs_num_nonneg _) (Qabs_num_nonneg _) hb (cornerMertens2_mixed had hbd ha hb 0 1 K hK)

/-- **Bound on the `sin·cos` corner**: `|corner_sc(2K+1)| ≤ M·(Mertens bound) → 0`. -/
theorem cornerSc_le {a b : Q} {M : Nat} (had : 0 < a.den) (hbd : 0 < b.den)
    (ha : Qle (Qabs a) ⟨(M : Int), 1⟩) (hb : Qle (Qabs b) ⟨(M : Int), 1⟩) (K : Nat)
    (hK : 2 * (M * M) ≤ K + 2) :
    Qle (Qabs (Fsum (fun i => Qsub (Fsum (fun j => mul (sinTerm a i) (altTerm b 0 j)) (2 * K + 1))
          (Fsum (fun j => mul (sinTerm a i) (altTerm b 0 j)) (2 * K + 1 - i))) (2 * K + 1)))
      (mul (⟨(M : Int), 1⟩ : Q)
        (add (mul (expM_U (M * M) (2 * (M * M))) ⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩)
          (mul ⟨(2 * npow (M * M) (K + 1) : Int), fct (K + 1)⟩ (expM_U (M * M) (2 * (M * M)))))) := by
  have haltd : ∀ i j, 0 < (mul (altTerm a 1 i) (altTerm b 0 j)).den :=
    fun i j => Qmul_den_pos (altTerm_den_pos had 1 i) (altTerm_den_pos hbd 0 j)
  have hcornerd : 0 < (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 0 j)) (2 * K + 1))
      (Fsum (fun j => mul (altTerm a 1 i) (altTerm b 0 j)) (2 * K + 1 - i))) (2 * K + 1)).den :=
    Fsum_den_pos (fun i => Qsub_den_pos (Fsum_den_pos (fun j => haltd i j) _)
      (Fsum_den_pos (fun j => haltd i j) _)) _
  refine Qle_congr_left (Qabs_den_pos (Qmul_den_pos had hcornerd))
    (Qeq_symm (Qabs_Qeq (cornerSc_factored had hbd (2 * K + 1)))) ?_
  rw [Qabs_mul]
  exact Qmul_le_mul (Qabs_den_pos had) Nat.one_pos (Qabs_den_pos hcornerd)
    (Qabs_num_nonneg _) (Qabs_num_nonneg _) ha (cornerMertens2_mixed had hbd ha hb 1 0 K hK)

-- ===========================================================================
-- The **assembled decay bound** `|sin(a+b) − (cos a·sin b + sin a·cos b partial)| → 0` at `2K+1`.
-- ===========================================================================

/-- **The assembled sin decay bound** at `2K+1`: the residual is `≤ M·Mertens + M·Mertens` (each corner
    bounded by `cornerCs_le`/`cornerSc_le`), both `→ 0`. The `Q`-level `sin(a+b) = cos a·sin b + sin a·cos b`
    with explicit modulus. (`sinAdd_resid_eq` = `−(corner_cs + corner_sc)`, `Qabs_neg` + triangle.) -/
theorem sinAdd_decay_le {a b : Q} {M : Nat} (had : 0 < a.den) (hbd : 0 < b.den)
    (ha : Qle (Qabs a) ⟨(M : Int), 1⟩) (hb : Qle (Qabs b) ⟨(M : Int), 1⟩) (K : Nat)
    (hK : 2 * (M * M) ≤ K + 2) :
    Qle (Qabs (Qsub (Fsum (sinTerm (add a b)) (2 * K + 1))
        (add (mul (altSum a 0 (2 * K + 1)) (Fsum (sinTerm b) (2 * K + 1)))
             (mul (Fsum (sinTerm a) (2 * K + 1)) (altSum b 0 (2 * K + 1))))))
      (add
        (mul (⟨(M : Int), 1⟩ : Q)
          (add (mul (expM_U (M * M) (2 * (M * M))) ⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩)
            (mul ⟨(2 * npow (M * M) (K + 1) : Int), fct (K + 1)⟩ (expM_U (M * M) (2 * (M * M))))))
        (mul (⟨(M : Int), 1⟩ : Q)
          (add (mul (expM_U (M * M) (2 * (M * M))) ⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩)
            (mul ⟨(2 * npow (M * M) (K + 1) : Int), fct (K + 1)⟩ (expM_U (M * M) (2 * (M * M))))))) := by
  have hcsd : 0 < (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm a 0 i) (sinTerm b j)) (2 * K + 1))
      (Fsum (fun j => mul (altTerm a 0 i) (sinTerm b j)) (2 * K + 1 - i))) (2 * K + 1)).den :=
    Fsum_den_pos (fun i => Qsub_den_pos
      (Fsum_den_pos (fun j => Qmul_den_pos (altTerm_den_pos had 0 i) (sinTerm_den_pos hbd j)) _)
      (Fsum_den_pos (fun j => Qmul_den_pos (altTerm_den_pos had 0 i) (sinTerm_den_pos hbd j)) _)) _
  have hscd : 0 < (Fsum (fun i => Qsub (Fsum (fun j => mul (sinTerm a i) (altTerm b 0 j)) (2 * K + 1))
      (Fsum (fun j => mul (sinTerm a i) (altTerm b 0 j)) (2 * K + 1 - i))) (2 * K + 1)).den :=
    Fsum_den_pos (fun i => Qsub_den_pos
      (Fsum_den_pos (fun j => Qmul_den_pos (sinTerm_den_pos had i) (altTerm_den_pos hbd 0 j)) _)
      (Fsum_den_pos (fun j => Qmul_den_pos (sinTerm_den_pos had i) (altTerm_den_pos hbd 0 j)) _)) _
  have hLd : 0 < (Qsub (Fsum (sinTerm (add a b)) (2 * K + 1))
      (add (mul (altSum a 0 (2 * K + 1)) (Fsum (sinTerm b) (2 * K + 1)))
           (mul (Fsum (sinTerm a) (2 * K + 1)) (altSum b 0 (2 * K + 1))))).den :=
    Qsub_den_pos (Fsum_den_pos (sinTerm_den_pos (add_den_pos had hbd)) _)
      (add_den_pos (Qmul_den_pos (altSum_den_pos had 0 _) (Fsum_den_pos (sinTerm_den_pos hbd) _))
        (Qmul_den_pos (Fsum_den_pos (sinTerm_den_pos had) _) (altSum_den_pos hbd 0 _)))
  have _hLd := hLd
  refine Qle_trans (Qabs_den_pos (neg_den_pos (add_den_pos hcsd hscd)))
    (Qeq_le (Qabs_Qeq (sinAdd_resid_eq had hbd (2 * K + 1)))) ?_
  rw [Qabs_neg]
  refine Qle_trans (add_den_pos (Qabs_den_pos hcsd) (Qabs_den_pos hscd))
    (Qabs_add_le _ _) ?_
  exact Qadd_le_add (cornerCs_le had hbd ha hb K hK) (cornerSc_le had hbd ha hb K hK)

/-- **The clean sin decay bound** `|sin(a+b) − (cos a·sin b + sin a·cos b partial)| ≤ 4M/(n+1)` at the
    deep depth `2K+1` (threshold linear in `n`): `sinAdd_decay_le` gives `2·(M·Mertens)`, and `uterm_le`
    collapses each Mertens term to `1/(n+1)`. The convergence modulus the Real reconciliation consumes. -/
theorem sinAdd_decay_5 {a b : Q} {M : Nat} (had : 0 < a.den) (hbd : 0 < b.den)
    (ha : Qle (Qabs a) ⟨(M : Int), 1⟩) (hb : Qle (Qabs b) ⟨(M : Int), 1⟩) (n K : Nat) (hm : 0 < M * M)
    (hK : (expM_U (M * M) (2 * (M * M))).num.toNat * 4 * (n + 1) * npow (M * M) (2 * (M * M) + 1)
        + 2 * (M * M) ≤ K) :
    Qle (Qabs (Qsub (Fsum (sinTerm (add a b)) (2 * K + 1))
        (add (mul (altSum a 0 (2 * K + 1)) (Fsum (sinTerm b) (2 * K + 1)))
             (mul (Fsum (sinTerm a) (2 * K + 1)) (altSum b 0 (2 * K + 1))))))
      ⟨(4 * M : Int), n + 1⟩ := by
  have h24 : (expM_U (M * M) (2 * (M * M))).num.toNat * 2 * (n + 1) * npow (M * M) (2 * (M * M) + 1)
      ≤ (expM_U (M * M) (2 * (M * M))).num.toNat * 4 * (n + 1) * npow (M * M) (2 * (M * M) + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl _) (by omega)) (Nat.le_refl _)) (Nat.le_refl _)
  have hMERTd : 0 < (add (mul (expM_U (M * M) (2 * (M * M))) ⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩)
      (mul ⟨(2 * npow (M * M) (K + 1) : Int), fct (K + 1)⟩ (expM_U (M * M) (2 * (M * M))))).den :=
    add_den_pos (Qmul_den_pos (expM_U_den_pos _ _) (fct_pos _)) (Qmul_den_pos (fct_pos _) (expM_U_den_pos _ _))
  -- each Mertens term ≤ 1/(n+1)
  have ht1 : Qle (mul (expM_U (M * M) (2 * (M * M))) ⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩) ⟨1, n + 1⟩ :=
    uterm_le M (K + 2) n 4 hm (by omega) (by omega)
  have ht2 : Qle (mul (⟨(2 * npow (M * M) (K + 1) : Int), fct (K + 1)⟩ : Q) (expM_U (M * M) (2 * (M * M)))) ⟨1, n + 1⟩ :=
    Qle_trans (Qmul_den_pos (expM_U_den_pos _ _) (fct_pos _))
      (Qeq_le (Qmul_swap _ _)) (uterm_le M (K + 1) n 2 hm (by omega) (by omega))
  have hMert : Qle (add (mul (expM_U (M * M) (2 * (M * M))) ⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩)
        (mul ⟨(2 * npow (M * M) (K + 1) : Int), fct (K + 1)⟩ (expM_U (M * M) (2 * (M * M))))) ⟨2, n + 1⟩ :=
    Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n)) (Qadd_le_add ht1 ht2)
      (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor))
  have hMmert : Qle (mul (⟨(M : Int), 1⟩ : Q)
        (add (mul (expM_U (M * M) (2 * (M * M))) ⟨(4 * npow (M * M) (K + 2) : Int), fct (K + 2)⟩)
          (mul ⟨(2 * npow (M * M) (K + 1) : Int), fct (K + 1)⟩ (expM_U (M * M) (2 * (M * M)))))) ⟨(2 * M : Int), n + 1⟩ :=
    Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos n)) (Qmul_le_mul_left (Int.ofNat_nonneg _) hMert)
      (Qeq_le (by simp only [Qeq, mul]; push_cast; ring_uor))
  refine Qle_trans (add_den_pos (Qmul_den_pos Nat.one_pos hMERTd) (Qmul_den_pos Nat.one_pos hMERTd))
    (sinAdd_decay_le had hbd ha hb K (by omega)) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n)) (Qadd_le_add hMmert hMmert)
    (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor))

end UOR.Bridge.F1Square.Analysis
