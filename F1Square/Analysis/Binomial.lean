/-
F1 square — **binomial coefficients and the factorial identity from scratch** (Lean core here has no
`Nat.choose` / `Nat.factorial` / `Nat.add_pow`). This is the foundational first piece of the v0.15.0
keystone: the exponential/trigonometric functional equation via the Cauchy product needs the binomial
identity `Σ_{i+j=k} (xⁱ/i!)(yʲ/j!) = (x+y)ᵏ/k!`, whose heart is `C(k,i)·i!·(k−i)! = k!`.

This module builds `choose` (Pascal's recurrence) and that factorial identity (the ℤ ring algebra is
discharged by `ring_uor`, the project's from-scratch `ring`). Pure Lean 4, no Mathlib, no `sorry`.
-/

import F1Square.Analysis.Exp
import F1Square.Analysis.ExpGen

namespace UOR.Bridge.F1Square.Analysis

/-- Binomial coefficients via Pascal's recurrence. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, (_ + 1) => 0
  | (n + 1), (k + 1) => choose n k + choose n (k + 1)

@[simp] theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl
@[simp] theorem choose_zero_succ (k : Nat) : choose 0 (k + 1) = 0 := rfl
theorem choose_succ_succ (n k : Nat) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl

/-- `C(n,k) = 0` when `k > n`. -/
theorem choose_eq_zero_of_lt : ∀ {n k : Nat}, n < k → choose n k = 0
  | 0, 0, h => absurd h (by omega)
  | 0, (_ + 1), _ => rfl
  | (_ + 1), 0, h => absurd h (by omega)
  | (n + 1), (k + 1), h => by
      rw [choose_succ_succ, choose_eq_zero_of_lt (by omega : n < k),
        choose_eq_zero_of_lt (by omega : n < k + 1)]

/-- `C(n,n) = 1`. -/
theorem choose_self : ∀ n, choose n n = 1
  | 0 => rfl
  | (n + 1) => by
      rw [choose_succ_succ, choose_self n, choose_eq_zero_of_lt (Nat.lt_succ_self n)]

-- ===========================================================================
-- A finite inclusive sum `Σ_{i=0}^{k} f i` over ℚ, with the algebra lemmas the binomial
-- theorem's Pascal step needs (distribution, additivity, index shift).
-- ===========================================================================

/-- Finite inclusive sum `Σ_{i=0}^{k} f i`. -/
def Fsum (f : Nat → Q) : Nat → Q
  | 0 => f 0
  | (k + 1) => add (Fsum f k) (f (k + 1))

theorem Fsum_den_pos {f : Nat → Q} (hf : ∀ i, 0 < (f i).den) : ∀ k, 0 < (Fsum f k).den
  | 0 => hf 0
  | (k + 1) => add_den_pos (Fsum_den_pos hf k) (hf (k + 1))

/-- Pointwise-equal summands give equal sums. -/
theorem Fsum_congr {f g : Nat → Q} (h : ∀ i, Qeq (f i) (g i)) : ∀ k, Qeq (Fsum f k) (Fsum g k)
  | 0 => h 0
  | (k + 1) => Qadd_congr (Fsum_congr h k) (h (k + 1))

/-- Reassociation `(a+b)+(c+d) ≈ (a+c)+(b+d)`. -/
theorem Qadd_rearrange (a b c d : Q) : Qeq (add (add a b) (add c d)) (add (add a c) (add b d)) := by
  simp only [Qeq, add]; push_cast; ring_uor

/-- Distribution `c·(a+b) ≈ c·a + c·b`. -/
theorem Qmul_add_left (c a b : Q) : Qeq (mul c (add a b)) (add (mul c a) (mul c b)) := by
  simp only [Qeq, mul, add]; push_cast; ring_uor

/-- Sums add termwise. -/
theorem Fsum_add {f g : Nat → Q} (hf : ∀ i, 0 < (f i).den) (hg : ∀ i, 0 < (g i).den) :
    ∀ k, Qeq (Fsum (fun i => add (f i) (g i)) k) (add (Fsum f k) (Fsum g k))
  | 0 => Qeq_refl _
  | (k + 1) =>
      Qeq_trans
        (add_den_pos (add_den_pos (Fsum_den_pos hf k) (Fsum_den_pos hg k))
          (add_den_pos (hf (k + 1)) (hg (k + 1))))
        (Qadd_congr (Fsum_add hf hg k) (Qeq_refl (add (f (k + 1)) (g (k + 1)))))
        (Qadd_rearrange (Fsum f k) (Fsum g k) (f (k + 1)) (g (k + 1)))

/-- A constant factor pulls out of a sum. -/
theorem Fsum_mul_left {c : Q} {f : Nat → Q} (hcd : 0 < c.den) (hf : ∀ i, 0 < (f i).den) :
    ∀ k, Qeq (Fsum (fun i => mul c (f i)) k) (mul c (Fsum f k))
  | 0 => Qeq_refl _
  | (k + 1) =>
      Qeq_trans
        (add_den_pos (Qmul_den_pos hcd (Fsum_den_pos hf k)) (Qmul_den_pos hcd (hf (k + 1))))
        (Qadd_congr (Fsum_mul_left hcd hf k) (Qeq_refl (mul c (f (k + 1)))))
        (Qeq_symm (Qmul_add_left c (Fsum f k) (f (k + 1))))

/-- Index shift: `Σ_{i=0}^{k} f(i+1) ≈ (Σ_{i=0}^{k+1} f i) − f 0`. -/
theorem Fsum_shift {f : Nat → Q} (hf : ∀ i, 0 < (f i).den) :
    ∀ k, Qeq (Fsum (fun i => f (i + 1)) k) (Qsub (Fsum f (k + 1)) (f 0))
  | 0 => by
      show Qeq (f 1) (Qsub (add (f 0) (f 1)) (f 0))
      simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
  | (k + 1) =>
      Qeq_trans
        (add_den_pos (Qsub_den_pos (Fsum_den_pos hf (k + 1)) (hf 0)) (hf (k + 1 + 1)))
        (Qadd_congr (Fsum_shift hf k) (Qeq_refl (f (k + 1 + 1))))
        (by
          show Qeq (add (Qsub (Fsum f (k + 1)) (f 0)) (f (k + 1 + 1)))
            (Qsub (add (Fsum f (k + 1)) (f (k + 1 + 1))) (f 0))
          simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor)

/-- `a + (b − a) ≈ b`. -/
theorem Qadd_sub_cancel_left (a b : Q) : Qeq (add a (Qsub b a)) b := by
  simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor

/-- Front-peel: `Σ_{i=0}^{k+1} f i ≈ f 0 + Σ_{i=0}^{k} f (i+1)`. -/
theorem Fsum_front {f : Nat → Q} (hf : ∀ i, 0 < (f i).den) (k : Nat) :
    Qeq (Fsum f (k + 1)) (add (f 0) (Fsum (fun i => f (i + 1)) k)) :=
  Qeq_symm
    (Qeq_trans (add_den_pos (hf 0) (Qsub_den_pos (Fsum_den_pos hf (k + 1)) (hf 0)))
      (Qadd_congr (Qeq_refl (f 0)) (Fsum_shift hf k))
      (Qadd_sub_cancel_left (f 0) (Fsum f (k + 1))))

/-- Commutativity of `Q` multiplication (up to `≈`). -/
theorem Qmul_swap (a b : Q) : Qeq (mul a b) (mul b a) := by
  simp only [Qeq, mul]; push_cast; ring_uor

/-- The general binomial summand `C(n,i)·xⁱ·yⁿ⁻ⁱ`. -/
def binTerm (x y : Q) (n i : Nat) : Q :=
  mul ⟨(choose n i : Int), 1⟩ (mul (qpow x i) (qpow y (n - i)))

theorem binTerm_den_pos {x y : Q} (hxd : 0 < x.den) (hyd : 0 < y.den) (n i : Nat) :
    0 < (binTerm x y n i).den :=
  Qmul_den_pos Nat.one_pos (Qmul_den_pos (qpow_den_pos hxd i) (qpow_den_pos hyd (n - i)))

/-- Top boundary: `y · binTerm n (n+1) ≈ 0` (since `C(n,n+1) = 0`). -/
theorem binTerm_top_zero (x y : Q) (n : Nat) : Qeq (mul y (binTerm x y n (n + 1))) ⟨0, 1⟩ := by
  have hc : choose n (n + 1) = 0 := choose_eq_zero_of_lt (by omega)
  show Qeq (mul y (mul ⟨(choose n (n + 1) : Int), 1⟩
    (mul (qpow x (n + 1)) (qpow y (n - (n + 1)))))) ⟨0, 1⟩
  rw [hc]; simp [Qeq, mul]

/-- Bottom boundary: `binTerm (n+1) 0 ≈ y · binTerm n 0` (both are `yⁿ⁺¹`). -/
theorem binTerm_zero_bot (x y : Q) (n : Nat) :
    Qeq (binTerm x y (n + 1) 0) (mul y (binTerm x y n 0)) := by
  show Qeq (mul ⟨(choose (n + 1) 0 : Int), 1⟩ (mul (qpow x 0) (qpow y (n + 1 - 0))))
    (mul y (mul ⟨(choose n 0 : Int), 1⟩ (mul (qpow x 0) (qpow y (n - 0)))))
  rw [choose_zero_right, choose_zero_right, Nat.sub_zero, Nat.sub_zero, qpow_succ]
  simp only [Qeq, mul]; push_cast; ring_uor

/-- `a + 0 ≈ a`. -/
theorem Qadd_zero_right (a : Q) : Qeq (add a ⟨0, 1⟩) a := by
  simp only [Qeq, add]; push_cast; ring_uor

/-- `a + (b + c) ≈ b + (a + c)`. -/
theorem Qadd_swap_left (a b c : Q) : Qeq (add a (add b c)) (add b (add a c)) := by
  simp only [Qeq, add]; push_cast; ring_uor

/-- Bounded congruence for `Fsum` (only needs equality up to the summation bound). -/
theorem Fsum_congr_le {f g : Nat → Q} : ∀ {k : Nat}, (∀ i, i ≤ k → Qeq (f i) (g i)) →
    Qeq (Fsum f k) (Fsum g k)
  | 0, h => h 0 (Nat.le_refl 0)
  | (k + 1), h =>
      Qadd_congr (Fsum_congr_le (fun i hik => h i (Nat.le_succ_of_le hik))) (h (k + 1) (Nat.le_refl _))

/-- **The per-term Pascal step** `binTerm (n+1) (i+1) ≈ x·binTerm n i + y·binTerm n (i+1)` (for `i ≤ n`;
    at `i = n` the second summand vanishes since `C(n,n+1) = 0`). -/
theorem binTerm_succ {x y : Q} (hxd : 0 < x.den) (hyd : 0 < y.den) (n : Nat) : ∀ {i : Nat}, i ≤ n →
    Qeq (binTerm x y (n + 1) (i + 1))
      (add (mul x (binTerm x y n i)) (mul y (binTerm x y n (i + 1)))) := by
  intro i hi
  rcases Nat.eq_or_lt_of_le hi with heq | hlt
  · -- i = n : the second summand is 0 (C(n,n+1) = 0)
    subst heq
    have htop := binTerm_top_zero x y i
    have hAB : Qeq (binTerm x y (i + 1) (i + 1)) (mul x (binTerm x y i i)) := by
      show Qeq (mul ⟨(choose (i + 1) (i + 1) : Int), 1⟩
          (mul (qpow x (i + 1)) (qpow y (i + 1 - (i + 1)))))
        (mul x (mul ⟨(choose i i : Int), 1⟩ (mul (qpow x i) (qpow y (i - i)))))
      rw [choose_self, choose_self, Nat.sub_self, Nat.sub_self, qpow_succ]
      simp only [Qeq, mul]; push_cast; ring_uor
    have hC0 : Qeq (add (mul x (binTerm x y i i)) (mul y (binTerm x y i (i + 1))))
        (mul x (binTerm x y i i)) :=
      Qeq_trans (add_den_pos (Qmul_den_pos hxd (binTerm_den_pos hxd hyd i i)) (by decide))
        (Qadd_congr (Qeq_refl (mul x (binTerm x y i i))) htop)
        (Qadd_zero_right (mul x (binTerm x y i i)))
    exact Qeq_trans (Qmul_den_pos hxd (binTerm_den_pos hxd hyd i i)) hAB (Qeq_symm hC0)
  · -- i < n : the generic Pascal identity
    show Qeq (mul ⟨(choose (n + 1) (i + 1) : Int), 1⟩ (mul (qpow x (i + 1)) (qpow y (n + 1 - (i + 1)))))
      (add (mul x (mul ⟨(choose n i : Int), 1⟩ (mul (qpow x i) (qpow y (n - i)))))
        (mul y (mul ⟨(choose n (i + 1) : Int), 1⟩ (mul (qpow x (i + 1)) (qpow y (n - (i + 1)))))))
    rw [show n + 1 - (i + 1) = n - i from by omega, choose_succ_succ, qpow_succ x i,
      show n - i = (n - (i + 1)) + 1 from by omega, qpow_succ y (n - (i + 1))]
    simp only [Qeq, mul, add]; push_cast; ring_uor

/-- **The factorial identity** `C(n,k)·k!·(n−k)! = n!` for `k ≤ n` — the divisibility heart of the
    binomial theorem. -/
theorem choose_mul_fct_mul_fct : ∀ {n k : Nat}, k ≤ n →
    choose n k * fct k * fct (n - k) = fct n
  | _, 0, _ => by simp [fct]
  | 0, (_ + 1), h => absurd h (by omega)
  | (n + 1), (k + 1), h => by
      rcases Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ h) with hkn | hkn
      · -- k = n : the corner term
        subst hkn
        rw [Nat.sub_self, choose_self]; simp [fct]
      · -- k < n : Pascal step (ℤ ring algebra via ring_uor)
        have ih1 := choose_mul_fct_mul_fct (Nat.le_of_lt hkn)
        have ih2 := choose_mul_fct_mul_fct hkn
        have hsub : n + 1 - (k + 1) = n - k := by omega
        -- cast the facts to ℤ, keeping each Nat subterm as an opaque atom
        have ih1Z : (↑(choose n k) : Int) * ↑(fct k) * ↑(fct (n - k)) = ↑(fct n) := by
          exact_mod_cast ih1
        have ih2Z : (↑(choose n (k + 1)) : Int) * ↑(fct (k + 1)) * ↑(fct (n - (k + 1))) = ↑(fct n) := by
          exact_mod_cast ih2
        have hFk1 : (↑(fct (k + 1)) : Int) = ↑(k + 1) * ↑(fct k) := by exact_mod_cast fct_succ k
        have hFnk_nat : fct (n - k) = (n - k) * fct (n - (k + 1)) := by
          rw [show n - k = (n - (k + 1)) + 1 from by omega, fct_succ]
        have hFnk : (↑(fct (n - k)) : Int) = ↑(n - k) * ↑(fct (n - (k + 1))) := by
          exact_mod_cast hFnk_nat
        have hFn1 : (↑(fct (n + 1)) : Int) = ↑(n + 1) * ↑(fct n) := by exact_mod_cast fct_succ n
        have hk1 : (↑(k + 1) : Int) + ↑(n - k) = ↑(n + 1) := by
          exact_mod_cast (show (k + 1) + (n - k) = n + 1 from by omega)
        have hterm1 : (↑(choose n k) : Int) * ↑(fct (k + 1)) * ↑(fct (n - k)) = ↑(k + 1) * ↑(fct n) := by
          rw [hFk1, ← ih1Z]; ring_uor
        have hterm2 : (↑(choose n (k + 1)) : Int) * ↑(fct (k + 1)) * ↑(fct (n - k))
            = ↑(n - k) * ↑(fct n) := by
          rw [hFnk, ← ih2Z]; ring_uor
        have keyZ : ((↑(choose n k) : Int) + ↑(choose n (k + 1))) * ↑(fct (k + 1)) * ↑(fct (n - k))
            = ↑(fct (n + 1)) :=
          calc ((↑(choose n k) : Int) + ↑(choose n (k + 1))) * ↑(fct (k + 1)) * ↑(fct (n - k))
              = (↑(choose n k) : Int) * ↑(fct (k + 1)) * ↑(fct (n - k))
                + ↑(choose n (k + 1)) * ↑(fct (k + 1)) * ↑(fct (n - k)) := by ring_uor
            _ = ↑(k + 1) * ↑(fct n) + ↑(n - k) * ↑(fct n) := by rw [hterm1, hterm2]
            _ = (↑(k + 1) + ↑(n - k)) * ↑(fct n) := by ring_uor
            _ = ↑(n + 1) * ↑(fct n) := by rw [hk1]
            _ = ↑(fct (n + 1)) := by rw [← hFn1]
        rw [hsub, choose_succ_succ]
        exact_mod_cast keyZ

/-- **The binomial theorem** `(x+y)ⁿ ≈ Σ_{i=0}^{n} C(n,i)·xⁱ·yⁿ⁻ⁱ`. -/
theorem binomial {x y : Q} (hxd : 0 < x.den) (hyd : 0 < y.den) :
    ∀ n, Qeq (qpow (add x y) n) (Fsum (binTerm x y n) n)
  | 0 => by show Qeq (⟨1, 1⟩ : Q) (mul ⟨1, 1⟩ (mul ⟨1, 1⟩ ⟨1, 1⟩)); decide
  | (n + 1) => by
      have hbtd : ∀ i, 0 < (binTerm x y n i).den := binTerm_den_pos hxd hyd n
      have hbt1 : ∀ i, 0 < (binTerm x y (n + 1) i).den := binTerm_den_pos hxd hyd (n + 1)
      have hSd : 0 < (Fsum (binTerm x y n) n).den := Fsum_den_pos hbtd n
      have hxbtd : ∀ i, 0 < (mul x (binTerm x y n i)).den := fun i => Qmul_den_pos hxd (hbtd i)
      have hybtd : ∀ i, 0 < (mul y (binTerm x y n i)).den := fun i => Qmul_den_pos hyd (hbtd i)
      -- the `mul x S` and `mul y S` denominators
      have hxSd : 0 < (mul x (Fsum (binTerm x y n) n)).den := Qmul_den_pos hxd hSd
      have hySd : 0 < (mul y (Fsum (binTerm x y n) n)).den := Qmul_den_pos hyd hSd
      -- `Σ x·binTerm n ≈ x·S` and the y-part `binTerm(n+1) 0 + Σ y·binTerm n (·+1) ≈ y·S`
      have h_x : Qeq (Fsum (fun i => mul x (binTerm x y n i)) n) (mul x (Fsum (binTerm x y n) n)) :=
        Fsum_mul_left hxd hbtd n
      have h_yfull : Qeq (Fsum (fun i => mul y (binTerm x y n i)) (n + 1)) (mul y (Fsum (binTerm x y n) n)) :=
        Qeq_trans (add_den_pos hySd (by decide))
          (Qadd_congr (Fsum_mul_left hyd hbtd n) (binTerm_top_zero x y n))
          (Qadd_zero_right (mul y (Fsum (binTerm x y n) n)))
      have h_ypart : Qeq (add (binTerm x y (n + 1) 0) (Fsum (fun i => mul y (binTerm x y n (i + 1))) n))
          (mul y (Fsum (binTerm x y n) n)) :=
        Qeq_trans (add_den_pos (hybtd 0) (Fsum_den_pos (fun i => hybtd (i + 1)) n))
          (Qadd_congr (binTerm_zero_bot x y n) (Qeq_refl _))
          (Qeq_trans (Fsum_den_pos hybtd (n + 1))
            (Qeq_symm (Fsum_front hybtd n)) h_yfull)
      -- the reindexed tail `Σ binTerm(n+1) (·+1) ≈ Σ x·binTerm n + Σ y·binTerm n (·+1)`
      have h_tail : Qeq (Fsum (fun i => binTerm x y (n + 1) (i + 1)) n)
          (add (Fsum (fun i => mul x (binTerm x y n i)) n)
            (Fsum (fun i => mul y (binTerm x y n (i + 1))) n)) :=
        Qeq_trans (Fsum_den_pos (fun i => add_den_pos (hxbtd i) (hybtd (i + 1))) n)
          (Fsum_congr_le (fun i hi => binTerm_succ hxd hyd n hi))
          (Fsum_add hxbtd (fun i => hybtd (i + 1)) n)
      -- assemble: front-peel, congr the tail, swap, then collapse each side to `· S`
      refine Qeq_trans (Qmul_den_pos (add_den_pos hxd hyd) hSd)
        (Qmul_congr (Qeq_refl (add x y)) (binomial hxd hyd n)) ?_
      -- goal: Qeq (mul (add x y) S) (Fsum (binTerm x y (n+1)) (n+1))  -- via Qeq_symm of the chain
      refine Qeq_symm (Qeq_trans (add_den_pos (hbt1 0) (Fsum_den_pos (fun i => hbt1 (i + 1)) n))
        (Fsum_front hbt1 n) ?_)
      refine Qeq_trans (add_den_pos (hbt1 0)
          (add_den_pos (Fsum_den_pos hxbtd n) (Fsum_den_pos (fun i => hybtd (i + 1)) n)))
        (Qadd_congr (Qeq_refl _) h_tail) ?_
      refine Qeq_trans (add_den_pos (Fsum_den_pos hxbtd n)
          (add_den_pos (hbt1 0) (Fsum_den_pos (fun i => hybtd (i + 1)) n)))
        (Qadd_swap_left (binTerm x y (n + 1) 0) (Fsum (fun i => mul x (binTerm x y n i)) n)
          (Fsum (fun i => mul y (binTerm x y n (i + 1))) n)) ?_
      -- goal: Qeq (add (Σ x·binTerm n) (add (binTerm(n+1) 0) (Σ y·binTerm n (·+1)))) (mul (add x y) S)
      refine Qeq_trans (add_den_pos hxSd hySd) (Qadd_congr h_x h_ypart) ?_
      -- goal: Qeq (add (mul x S) (mul y S)) (mul (add x y) S)
      exact Qeq_symm (Qmul_add_right x y (Fsum (binTerm x y n) n))

-- ===========================================================================
-- The per-degree convolution of the exponential series (the bridge to exp(x+y)=exp x·exp y).
-- ===========================================================================

/-- Per-term: `(1/k!)·binTerm k i ≈ (xⁱ/i!)·(yᵏ⁻ⁱ/(k−i)!)`, i.e. `C(k,i)/k! = 1/(i!·(k−i)!)`
    (the factorial identity, for `i ≤ k`). -/
theorem expTerm_conv_term {x y : Q} (k i : Nat) (hik : i ≤ k) :
    Qeq (mul ⟨1, fct k⟩ (binTerm x y k i)) (mul (expTerm x i) (expTerm y (k - i))) := by
  have hfidZ : (↑(fct k) : Int) = ↑(choose k i) * ↑(fct i) * ↑(fct (k - i)) := by
    exact_mod_cast (choose_mul_fct_mul_fct hik).symm
  show Qeq (mul ⟨1, fct k⟩ (mul ⟨(choose k i : Int), 1⟩ (mul (qpow x i) (qpow y (k - i)))))
    (mul (mul (qpow x i) ⟨1, fct i⟩) (mul (qpow y (k - i)) ⟨1, fct (k - i)⟩))
  simp only [Qeq, mul]
  push_cast [hfidZ]
  ring_uor

/-- **The exp convolution** `Σ_{i=0}^{k} (xⁱ/i!)·(yᵏ⁻ⁱ/(k−i)!) ≈ (x+y)ᵏ/k!` — the per-degree
    Cauchy-product identity for the exponential series. -/
theorem expTerm_conv {x y : Q} (hxd : 0 < x.den) (hyd : 0 < y.den) (k : Nat) :
    Qeq (Fsum (fun i => mul (expTerm x i) (expTerm y (k - i))) k) (expTerm (add x y) k) := by
  have hfk : 0 < fct k := fct_pos k
  have hbtd : ∀ i, 0 < (binTerm x y k i).den := binTerm_den_pos hxd hyd k
  refine Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos hfk (hbtd i)) k)
    (Qeq_symm (Fsum_congr_le (fun i hi => expTerm_conv_term k i hi))) ?_
  refine Qeq_trans (Qmul_den_pos hfk (Fsum_den_pos hbtd k)) (Fsum_mul_left hfk hbtd k) ?_
  refine Qeq_trans (Qmul_den_pos (Fsum_den_pos hbtd k) hfk)
    (Qmul_swap ⟨1, fct k⟩ (Fsum (binTerm x y k) k)) ?_
  exact Qmul_congr (Qeq_symm (binomial hxd hyd k)) (Qeq_refl (⟨1, fct k⟩ : Q))

/-- **The alternating binomial identity** `Σ_{i=0}^{n+1} C(n+1,i)·1ⁱ·(−1)ⁿ⁺¹⁻ⁱ ≈ 0` — i.e. `(1+(−1))ⁿ⁺¹ = 0`.
    (The coefficient-vanishing behind `cos² + sin² = 1`.) -/
theorem alternating_binomial (m : Nat) :
    Qeq (Fsum (binTerm ⟨1, 1⟩ ⟨-1, 1⟩ (m + 1)) (m + 1)) ⟨0, 1⟩ := by
  have hb := binomial (x := (⟨1, 1⟩ : Q)) (y := (⟨-1, 1⟩ : Q)) (by decide) (by decide) (m + 1)
  have hz : Qeq (qpow (add (⟨1, 1⟩ : Q) ⟨-1, 1⟩) (m + 1)) ⟨0, 1⟩ := by
    have hnum : (qpow (add (⟨1, 1⟩ : Q) ⟨-1, 1⟩) (m + 1)).num = 0 := qpow_zero_succ_num m
    simp only [Qeq]; rw [hnum]; simp
  exact Qeq_trans (qpow_den_pos (by decide) (m + 1)) (Qeq_symm hb) hz

/-- A constant factor pulls out of a sum (on the right). -/
theorem Fsum_mul_const_right {a : Nat → Q} {c : Q} (hcd : 0 < c.den) (ha : ∀ i, 0 < (a i).den) :
    ∀ M, Qeq (mul (Fsum a M) c) (Fsum (fun i => mul (a i) c) M)
  | 0 => Qeq_refl _
  | (M + 1) =>
      Qeq_trans
        (add_den_pos (Qmul_den_pos (Fsum_den_pos ha M) hcd) (Qmul_den_pos (ha (M + 1)) hcd))
        (Qmul_add_right (Fsum a M) (a (M + 1)) c)
        (Qadd_congr (Fsum_mul_const_right hcd ha M) (Qeq_refl (mul (a (M + 1)) c)))

/-- **Product of two sums as a square double sum**: `(Σ_{i≤M} aᵢ)·(Σ_{j≤M} bⱼ) ≈ Σ_{i≤M} Σ_{j≤M} aᵢ·bⱼ`. -/
theorem Fsum_mul_square {a b : Nat → Q} (ha : ∀ i, 0 < (a i).den) (hb : ∀ j, 0 < (b j).den) (M : Nat) :
    Qeq (mul (Fsum a M) (Fsum b M)) (Fsum (fun i => Fsum (fun j => mul (a i) (b j)) M) M) :=
  Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos (ha i) (Fsum_den_pos hb M)) M)
    (Fsum_mul_const_right (Fsum_den_pos hb M) ha M)
    (Fsum_congr (fun i => Qeq_symm (Fsum_mul_left (ha i) hb M)) M)

/-- The exponential partial sum as an `Fsum` of its terms (bridge to the finite-sum library). -/
theorem expSum_eq_Fsum (q : Q) : ∀ N, Qeq (expSum q N) (Fsum (expTerm q) N)
  | 0 => by show Qeq (⟨1, 1⟩ : Q) (mul ⟨1, 1⟩ ⟨1, 1⟩); decide
  | (n + 1) => Qadd_congr (expSum_eq_Fsum q n) (Qeq_refl (expTerm q (n + 1)))

/-- **The diagonal sum of convolutions equals the `exp(x+y)` partial sum**:
    `Σ_{m=0}^{M} Σ_{i=0}^{m} (xⁱ/i!)·(yᵐ⁻ⁱ/(m−i)!) ≈ Σ_{m=0}^{M} (x+y)ᵐ/m!` — each inner convolution is the
    `m`-th term of `exp(x+y)` (`expTerm_conv`). This is the triangular part of the Cauchy product. -/
theorem Fsum_conv_expSum {x y : Q} (hxd : 0 < x.den) (hyd : 0 < y.den) (M : Nat) :
    Qeq (Fsum (fun m => Fsum (fun i => mul (expTerm x i) (expTerm y (m - i))) m) M)
      (expSum (add x y) M) :=
  Qeq_trans (Fsum_den_pos (fun m => expTerm_den_pos (add_den_pos hxd hyd) m) M)
    (Fsum_congr (fun m => expTerm_conv hxd hyd m) M)
    (Qeq_symm (expSum_eq_Fsum (add x y) M))

end UOR.Bridge.F1Square.Analysis
