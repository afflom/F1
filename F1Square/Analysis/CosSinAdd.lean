/-
F1 square — **the trigonometric Cauchy product** toward `cos² + sin² = 1` (and hence `|cos|,|sin| ≤ 1`,
the keystone for the `Czeta` modulus). This file builds the per-term algebra of the alternating series:
`altTerm q off i · altTerm q off' j ≈ (−q²)^{i+j} / ((2i+off)!·(2j+off')!)`, the trig analogue of the
exponential product term. Combined with `alternating_binomial` (`Σ_k (−1)^k C(2m,k) = 0`) it gives the
per-degree Pythagorean coefficient vanishing.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.Binomial
import F1Square.Analysis.CosSin

namespace UOR.Bridge.F1Square.Analysis

/-- Left-commutativity of `Q` multiplication (up to `≈`). -/
theorem Qmul_left_comm (a b c : Q) : Qeq (mul a (mul b c)) (mul b (mul a c)) := by
  simp only [Qeq, mul]; push_cast; ring_uor

/-- Four-factor rearrangement `(a·b)·(c·d) ≈ (a·c)·(b·d)`. -/
theorem Qmul4_rearrange (a b c d : Q) : Qeq (mul (mul a b) (mul c d)) (mul (mul a c) (mul b d)) := by
  simp only [Qeq, mul]; push_cast; ring_uor

/-- `qⁿ⁺ᵐ ≈ qⁿ · qᵐ`. -/
theorem qpow_add (q : Q) (hqd : 0 < q.den) (a : Nat) :
    ∀ b, Qeq (qpow q (a + b)) (mul (qpow q a) (qpow q b))
  | 0 => by
      rw [Nat.add_zero]
      show Qeq (qpow q a) (mul (qpow q a) ⟨1, 1⟩)
      simp only [Qeq, mul]; push_cast; ring_uor
  | (b + 1) => by
      show Qeq (mul q (qpow q (a + b))) (mul (qpow q a) (mul q (qpow q b)))
      exact Qeq_trans (Qmul_den_pos hqd (Qmul_den_pos (qpow_den_pos hqd a) (qpow_den_pos hqd b)))
        (Qmul_congr (Qeq_refl q) (qpow_add q hqd a b))
        (Qmul_left_comm q (qpow q a) (qpow q b))

/-- **The trig product term**: `((−q²)ⁱ/(2i+off)!) · ((−q²)ʲ/(2j+off')!) ≈ (−q²)^{i+j}/((2i+off)!·(2j+off')!)`. -/
theorem altTerm_mul {q : Q} (hqd : 0 < q.den) (off off' i j : Nat) :
    Qeq (mul (altTerm q off i) (altTerm q off' j))
      (mul (qpow (neg (mul q q)) (i + j)) ⟨1, fct (2 * i + off) * fct (2 * j + off')⟩) := by
  have hN : 0 < (neg (mul q q)).den := Nat.mul_pos hqd hqd
  have h1 : Qeq (mul (altTerm q off i) (altTerm q off' j))
      (mul (mul (qpow (neg (mul q q)) i) (qpow (neg (mul q q)) j))
        (mul (⟨1, fct (2 * i + off)⟩ : Q) ⟨1, fct (2 * j + off')⟩)) :=
    Qmul4_rearrange (qpow (neg (mul q q)) i) ⟨1, fct (2 * i + off)⟩
      (qpow (neg (mul q q)) j) ⟨1, fct (2 * j + off')⟩
  refine Qeq_trans ?_ h1 ?_
  · exact Qmul_den_pos (Qmul_den_pos (qpow_den_pos hN i) (qpow_den_pos hN j))
      (Qmul_den_pos (fct_pos _) (fct_pos _))
  · exact Qmul_congr (Qeq_symm (qpow_add (neg (mul q q)) hN i j)) (Qeq_refl _)

/-- **Convolution factoring**: the degree-`d` self-convolution of the `off`-shifted alternating series
    factors as `(−q²)^d · Σ_{i≤d} 1/((2i+off)!·(2(d−i)+off)!)`. -/
theorem altConv_factor {q : Q} (hqd : 0 < q.den) (off d : Nat) :
    Qeq (Fsum (fun i => mul (altTerm q off i) (altTerm q off (d - i))) d)
      (mul (qpow (neg (mul q q)) d)
        (Fsum (fun i => (⟨1, fct (2 * i + off) * fct (2 * (d - i) + off)⟩ : Q)) d)) := by
  have hN : 0 < (neg (mul q q)).den := Nat.mul_pos hqd hqd
  have hfd : ∀ i, 0 < ((⟨1, fct (2 * i + off) * fct (2 * (d - i) + off)⟩ : Q)).den :=
    fun i => Nat.mul_pos (fct_pos _) (fct_pos _)
  have hstep : Qeq (Fsum (fun i => mul (altTerm q off i) (altTerm q off (d - i))) d)
      (Fsum (fun i => mul (qpow (neg (mul q q)) d)
        (⟨1, fct (2 * i + off) * fct (2 * (d - i) + off)⟩ : Q)) d) :=
    Fsum_congr_le (fun i hi => by
      have h := altTerm_mul hqd off off i (d - i)
      rw [show i + (d - i) = d from by omega] at h
      exact h)
  exact Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos (qpow_den_pos hN d) (hfd i)) d) hstep
    (Fsum_mul_left (qpow_den_pos hN d) hfd d)

/-- `(x+y)+z ≈ (x+z)+y`. -/
theorem Qadd_perm (x y z : Q) : Qeq (add (add x y) z) (add (add x z) y) := by
  simp only [Qeq, add]; push_cast; ring_uor

/-- `((e+o)+x)+y ≈ (e+y)+(o+x)`. -/
theorem Qadd_perm4 (e o x y : Q) : Qeq (add (add (add e o) x) y) (add (add e y) (add o x)) := by
  simp only [Qeq, add]; push_cast; ring_uor

/-- **Parity split**: `Σ_{i=0}^{2m+2} aᵢ ≈ (Σ_{j=0}^{m+1} a_{2j}) + (Σ_{j=0}^{m} a_{2j+1})`. -/
theorem Fsum_parity_split (a : Nat → Q) (ha : ∀ i, 0 < (a i).den) :
    ∀ m, Qeq (Fsum a (2 * m + 2))
      (add (Fsum (fun j => a (2 * j)) (m + 1)) (Fsum (fun j => a (2 * j + 1)) m))
  | 0 => Qadd_perm (a 0) (a 1) (a 2)
  | (m + 1) => by
      show Qeq (add (add (Fsum a (2 * m + 2)) (a (2 * m + 2 + 1))) (a (2 * m + 2 + 2)))
        (add (add (Fsum (fun j => a (2 * j)) (m + 1)) (a (2 * m + 2 + 2)))
          (add (Fsum (fun j => a (2 * j + 1)) m) (a (2 * m + 2 + 1))))
      exact Qeq_trans
        (add_den_pos (add_den_pos (add_den_pos (Fsum_den_pos (fun j => ha (2 * j)) (m + 1))
          (Fsum_den_pos (fun j => ha (2 * j + 1)) m)) (ha (2 * m + 2 + 1))) (ha (2 * m + 2 + 2)))
        (Qadd_congr (Qadd_congr (Fsum_parity_split a ha m) (Qeq_refl (a (2 * m + 2 + 1))))
          (Qeq_refl (a (2 * m + 2 + 2))))
        (Qadd_perm4 (Fsum (fun j => a (2 * j)) (m + 1)) (Fsum (fun j => a (2 * j + 1)) m)
          (a (2 * m + 2 + 1)) (a (2 * m + 2 + 2)))

/-- Integer running sum (the numerator sum for a constant-denominator `Fsum`). -/
def NFsum (f : Nat → Int) : Nat → Int
  | 0 => f 0
  | (k + 1) => NFsum f k + f (k + 1)

/-- `⟨a,D⟩ + ⟨b,D⟩ ≈ ⟨a+b,D⟩`. -/
theorem Qadd_same_den (a b : Int) (D : Nat) : Qeq (add (⟨a, D⟩ : Q) ⟨b, D⟩) ⟨a + b, D⟩ := by
  simp only [Qeq, add]; push_cast; ring_uor

/-- A constant-denominator finite sum collapses to a single fraction. -/
theorem Fsum_const_den (f : Nat → Int) (D : Nat) (hD : 0 < D) :
    ∀ k, Qeq (Fsum (fun i => (⟨f i, D⟩ : Q)) k) ⟨NFsum f k, D⟩
  | 0 => Qeq_refl _
  | (k + 1) =>
      Qeq_trans (add_den_pos (show 0 < (⟨NFsum f k, D⟩ : Q).den from hD) hD)
        (Qadd_congr (Fsum_const_den f D hD k) (Qeq_refl (⟨f (k + 1), D⟩ : Q)))
        (Qadd_same_den (NFsum f k) (f (k + 1)) D)

/-- `(−1)^{2k} = 1`. -/
theorem qpow_neg_one_even : ∀ k, qpow (⟨-1, 1⟩ : Q) (2 * k) = ⟨1, 1⟩
  | 0 => rfl
  | (k + 1) => by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by omega, qpow_succ, qpow_succ, qpow_neg_one_even k]
      rfl

/-- `(−1)^{2k+1} = −1`. -/
theorem qpow_neg_one_odd (k : Nat) : qpow (⟨-1, 1⟩ : Q) (2 * k + 1) = ⟨-1, 1⟩ := by
  rw [qpow_succ, qpow_neg_one_even k]; rfl

/-- `NFsum` distributes over negation. -/
theorem NFsum_neg (f : Nat → Int) : ∀ k, NFsum (fun j => -(f j)) k = -(NFsum f k)
  | 0 => rfl
  | (k + 1) => by
      show NFsum (fun j => -(f j)) k + -(f (k + 1)) = -(NFsum f k + f (k + 1))
      rw [NFsum_neg f k]; omega

/-- The alternating-binomial summand at an even index `2j` equals `+C(2m+2,2j)`. -/
theorem binTerm_even (m j : Nat) (hj : j ≤ m + 1) :
    Qeq (binTerm ⟨1, 1⟩ ⟨-1, 1⟩ (2 * m + 2) (2 * j)) ⟨(choose (2 * m + 2) (2 * j) : Int), 1⟩ := by
  show Qeq (mul ⟨(choose (2 * m + 2) (2 * j) : Int), 1⟩
      (mul (qpow (⟨1, 1⟩ : Q) (2 * j)) (qpow (⟨-1, 1⟩ : Q) ((2 * m + 2) - (2 * j)))))
    ⟨(choose (2 * m + 2) (2 * j) : Int), 1⟩
  rw [qpow_one_eq, show (2 * m + 2) - (2 * j) = 2 * (m + 1 - j) from by omega, qpow_neg_one_even]
  simp only [Qeq, mul]; push_cast; ring_uor

/-- The alternating-binomial summand at an odd index `2j+1` equals `−C(2m+2,2j+1)`. -/
theorem binTerm_odd (m j : Nat) (hj : j ≤ m) :
    Qeq (binTerm ⟨1, 1⟩ ⟨-1, 1⟩ (2 * m + 2) (2 * j + 1))
      ⟨-(choose (2 * m + 2) (2 * j + 1) : Int), 1⟩ := by
  show Qeq (mul ⟨(choose (2 * m + 2) (2 * j + 1) : Int), 1⟩
      (mul (qpow (⟨1, 1⟩ : Q) (2 * j + 1)) (qpow (⟨-1, 1⟩ : Q) ((2 * m + 2) - (2 * j + 1)))))
    ⟨-(choose (2 * m + 2) (2 * j + 1) : Int), 1⟩
  rw [qpow_one_eq, show (2 * m + 2) - (2 * j + 1) = 2 * (m - j) + 1 from by omega, qpow_neg_one_odd]
  simp only [Qeq, mul]; push_cast; ring_uor

/-- **The even/odd binomial-sum equality** `Σ_{i≤m+1} C(2m+2,2i) = Σ_{i≤m} C(2m+2,2i+1)`, the
    combinatorial heart of `cos² + sin² = 1`. Proof: split the alternating-binomial sum
    `Σ_k (−1)^k C(2m+2,k) = 0` by parity (`Fsum_parity_split`); the even part is `+Σ C(·,2i)`, the
    odd part is `−Σ C(·,2i+1)`, so the two are equal. -/
theorem binom_even_odd_eq (m : Nat) :
    NFsum (fun j => (choose (2 * m + 2) (2 * j) : Int)) (m + 1)
      = NFsum (fun j => (choose (2 * m + 2) (2 * j + 1) : Int)) m := by
  have ha : ∀ i, 0 < (binTerm (⟨1, 1⟩ : Q) ⟨-1, 1⟩ (2 * m + 2) i).den :=
    fun i => binTerm_den_pos (by decide) (by decide) (2 * m + 2) i
  have hsplit := Fsum_parity_split (binTerm (⟨1, 1⟩ : Q) ⟨-1, 1⟩ (2 * m + 2)) ha m
  have hzero : Qeq (Fsum (binTerm (⟨1, 1⟩ : Q) ⟨-1, 1⟩ (2 * m + 2)) (2 * m + 2)) ⟨0, 1⟩ :=
    alternating_binomial (2 * m + 1)
  have heven : Qeq (Fsum (fun j => binTerm (⟨1, 1⟩ : Q) ⟨-1, 1⟩ (2 * m + 2) (2 * j)) (m + 1))
      ⟨NFsum (fun j => (choose (2 * m + 2) (2 * j) : Int)) (m + 1), 1⟩ :=
    Qeq_trans (Fsum_den_pos (f := fun j => (⟨(choose (2 * m + 2) (2 * j) : Int), 1⟩ : Q))
        (fun _ => Nat.one_pos) (m + 1))
      (Fsum_congr_le (fun j hj => binTerm_even m j hj))
      (Fsum_const_den (fun j => (choose (2 * m + 2) (2 * j) : Int)) 1 Nat.one_pos (m + 1))
  have hodd : Qeq (Fsum (fun j => binTerm (⟨1, 1⟩ : Q) ⟨-1, 1⟩ (2 * m + 2) (2 * j + 1)) m)
      ⟨NFsum (fun j => -(choose (2 * m + 2) (2 * j + 1) : Int)) m, 1⟩ :=
    Qeq_trans (Fsum_den_pos (f := fun j => (⟨-(choose (2 * m + 2) (2 * j + 1) : Int), 1⟩ : Q))
        (fun _ => Nat.one_pos) m)
      (Fsum_congr_le (fun j hj => binTerm_odd m j hj))
      (Fsum_const_den (fun j => -(choose (2 * m + 2) (2 * j + 1) : Int)) 1 Nat.one_pos m)
  -- add even + odd ≈ 0
  have hsum0 : Qeq (add ⟨NFsum (fun j => (choose (2 * m + 2) (2 * j) : Int)) (m + 1), 1⟩
      ⟨NFsum (fun j => -(choose (2 * m + 2) (2 * j + 1) : Int)) m, 1⟩) ⟨0, 1⟩ :=
    Qeq_trans (add_den_pos (Fsum_den_pos (fun j => ha (2 * j)) (m + 1))
        (Fsum_den_pos (fun j => ha (2 * j + 1)) m))
      (Qeq_symm (Qadd_congr heven hodd))
      (Qeq_trans (Fsum_den_pos ha (2 * m + 2)) (Qeq_symm hsplit) hzero)
  have hSeq : Qeq (⟨NFsum (fun j => (choose (2 * m + 2) (2 * j) : Int)) (m + 1)
      + NFsum (fun j => -(choose (2 * m + 2) (2 * j + 1) : Int)) m, 1⟩ : Q) ⟨0, 1⟩ :=
    Qeq_trans (add_den_pos Nat.one_pos Nat.one_pos) (Qeq_symm (Qadd_same_den _ _ 1)) hsum0
  have hS : NFsum (fun j => (choose (2 * m + 2) (2 * j) : Int)) (m + 1)
      + NFsum (fun j => -(choose (2 * m + 2) (2 * j + 1) : Int)) m = 0 := by
    have h := hSeq; unfold Qeq at h; simpa using h
  rw [NFsum_neg] at hS; omega

/-- A `cos²` factorial term equals `C(2m+2,2i)/(2m+2)!`. -/
theorem cosFct_term (m i : Nat) (hi : i ≤ m + 1) :
    Qeq (⟨1, fct (2 * i) * fct (2 * ((m + 1) - i))⟩ : Q)
      ⟨(choose (2 * m + 2) (2 * i) : Int), fct (2 * m + 2)⟩ := by
  have hfac := choose_mul_fct_mul_fct (n := 2 * m + 2) (k := 2 * i) (by omega)
  rw [show (2 * m + 2) - (2 * i) = 2 * ((m + 1) - i) from by omega] at hfac
  have hN : fct (2 * m + 2) = choose (2 * m + 2) (2 * i) * (fct (2 * i) * fct (2 * ((m + 1) - i))) := by
    rw [← hfac, Nat.mul_assoc]
  show (1 : Int) * ((fct (2 * m + 2) : Nat) : Int)
     = ((choose (2 * m + 2) (2 * i) : Nat) : Int) * ((fct (2 * i) * fct (2 * ((m + 1) - i)) : Nat) : Int)
  rw [hN]; push_cast; ring_uor

/-- A `sin²` factorial term equals `C(2m+2,2i+1)/(2m+2)!`. -/
theorem sinFct_term (m i : Nat) (hi : i ≤ m) :
    Qeq (⟨1, fct (2 * i + 1) * fct (2 * (m - i) + 1)⟩ : Q)
      ⟨(choose (2 * m + 2) (2 * i + 1) : Int), fct (2 * m + 2)⟩ := by
  have hfac := choose_mul_fct_mul_fct (n := 2 * m + 2) (k := 2 * i + 1) (by omega)
  rw [show (2 * m + 2) - (2 * i + 1) = 2 * (m - i) + 1 from by omega] at hfac
  have hN : fct (2 * m + 2) = choose (2 * m + 2) (2 * i + 1) * (fct (2 * i + 1) * fct (2 * (m - i) + 1)) := by
    rw [← hfac, Nat.mul_assoc]
  show (1 : Int) * ((fct (2 * m + 2) : Nat) : Int)
     = ((choose (2 * m + 2) (2 * i + 1) : Nat) : Int) * ((fct (2 * i + 1) * fct (2 * (m - i) + 1) : Nat) : Int)
  rw [hN]; push_cast; ring_uor

/-- **`CosFct(m+1) ≈ SinFct(m)`**: the degree-`(m+1)` `cos²` factorial sum equals the degree-`m` `sin²`
    factorial sum. Both collapse (via `cosFct_term`/`sinFct_term` + `Fsum_const_den`) to a single
    fraction over `(2m+2)!` whose numerators are the even/odd binomial sums, equal by `binom_even_odd_eq`. -/
theorem cosFct_eq_sinFct (m : Nat) :
    Qeq (Fsum (fun i => (⟨1, fct (2 * i) * fct (2 * ((m + 1) - i))⟩ : Q)) (m + 1))
      (Fsum (fun i => (⟨1, fct (2 * i + 1) * fct (2 * (m - i) + 1)⟩ : Q)) m) := by
  have hcos : Qeq (Fsum (fun i => (⟨1, fct (2 * i) * fct (2 * ((m + 1) - i))⟩ : Q)) (m + 1))
      ⟨NFsum (fun i => (choose (2 * m + 2) (2 * i) : Int)) (m + 1), fct (2 * m + 2)⟩ :=
    Qeq_trans (Fsum_den_pos (f := fun i => (⟨(choose (2 * m + 2) (2 * i) : Int), fct (2 * m + 2)⟩ : Q))
        (fun _ => fct_pos _) (m + 1))
      (Fsum_congr_le (fun i hi => cosFct_term m i hi))
      (Fsum_const_den (fun i => (choose (2 * m + 2) (2 * i) : Int)) (fct (2 * m + 2)) (fct_pos _) (m + 1))
  have hsin : Qeq (Fsum (fun i => (⟨1, fct (2 * i + 1) * fct (2 * (m - i) + 1)⟩ : Q)) m)
      ⟨NFsum (fun i => (choose (2 * m + 2) (2 * i + 1) : Int)) m, fct (2 * m + 2)⟩ :=
    Qeq_trans (Fsum_den_pos (f := fun i => (⟨(choose (2 * m + 2) (2 * i + 1) : Int), fct (2 * m + 2)⟩ : Q))
        (fun _ => fct_pos _) m)
      (Fsum_congr_le (fun i hi => sinFct_term m i hi))
      (Fsum_const_den (fun i => (choose (2 * m + 2) (2 * i + 1) : Int)) (fct (2 * m + 2)) (fct_pos _) m)
  have heq : Qeq (⟨NFsum (fun i => (choose (2 * m + 2) (2 * i) : Int)) (m + 1), fct (2 * m + 2)⟩ : Q)
      ⟨NFsum (fun i => (choose (2 * m + 2) (2 * i + 1) : Int)) m, fct (2 * m + 2)⟩ := by
    rw [binom_even_odd_eq m]; exact Qeq_refl _
  exact Qeq_trans (fct_pos _) hcos (Qeq_trans (fct_pos _) heq (Qeq_symm hsin))

/-- `a·(b·c) ≈ (a·b)·c`. -/
theorem Qmul_assoc3 (a b c : Q) : Qeq (mul a (mul b c)) (mul (mul a b) c) := by
  simp only [Qeq, mul]; push_cast; ring_uor

/-- `q²·(−q²)^m ≈ −(−q²)^{m+1}` — the sign/degree shift relating the `sin²` `x²` factor to `cos²`. -/
theorem Qmul_qsq_qpow (q : Q) (m : Nat) :
    Qeq (mul (mul q q) (qpow (neg (mul q q)) m)) (neg (qpow (neg (mul q q)) (m + 1))) := by
  rw [qpow_succ]; simp only [Qeq, mul, neg]; push_cast; ring_uor

/-- **The per-degree Pythagorean coefficient vanishes**: `cosConv(m+1) + q²·sinConv(m) ≈ 0`, where
    `cosConv d = Σ_{i≤d} cosTermᵢ·cosT_{d−i}` and `sinConv d` likewise. Both convolutions factor as
    `(−q²)^· × (factorial sum)` (`altConv_factor`); the factorial sums are equal (`cosFct_eq_sinFct`) and
    the `(−q²)` powers are opposite (`Qmul_qsq_qpow`), so the two terms cancel. -/
theorem altPyth_conv_vanish {q : Q} (hqd : 0 < q.den) (m : Nat) :
    Qeq (add (Fsum (fun i => mul (altTerm q 0 i) (altTerm q 0 ((m + 1) - i))) (m + 1))
      (mul (mul q q) (Fsum (fun i => mul (altTerm q 1 i) (altTerm q 1 (m - i))) m))) ⟨0, 1⟩ := by
  have hN : 0 < (neg (mul q q)).den := Nat.mul_pos hqd hqd
  have hPden : 0 < (qpow (neg (mul q q)) (m + 1)).den := qpow_den_pos hN (m + 1)
  have hPmden : 0 < (qpow (neg (mul q q)) m).den := qpow_den_pos hN m
  have hCfden : 0 < (Fsum (fun i => (⟨1, fct (2 * i + 0) * fct (2 * ((m + 1) - i) + 0)⟩ : Q)) (m + 1)).den :=
    Fsum_den_pos (fun _ => Nat.mul_pos (fct_pos _) (fct_pos _)) (m + 1)
  have hSfden : 0 < (Fsum (fun i => (⟨1, fct (2 * i + 1) * fct (2 * (m - i) + 1)⟩ : Q)) m).den :=
    Fsum_den_pos (fun _ => Nat.mul_pos (fct_pos _) (fct_pos _)) m
  have heq : Qeq (Fsum (fun i => (⟨1, fct (2 * i + 0) * fct (2 * ((m + 1) - i) + 0)⟩ : Q)) (m + 1))
      (Fsum (fun i => (⟨1, fct (2 * i + 1) * fct (2 * (m - i) + 1)⟩ : Q)) m) := cosFct_eq_sinFct m
  -- cosC ≈ P·Sf
  have hc2 : Qeq (Fsum (fun i => mul (altTerm q 0 i) (altTerm q 0 ((m + 1) - i))) (m + 1))
      (mul (qpow (neg (mul q q)) (m + 1))
        (Fsum (fun i => (⟨1, fct (2 * i + 1) * fct (2 * (m - i) + 1)⟩ : Q)) m)) :=
    Qeq_trans (Qmul_den_pos hPden hCfden) (altConv_factor hqd 0 (m + 1))
      (Qmul_congr (Qeq_refl _) heq)
  -- q²·sinC ≈ (−P)·Sf
  have hs2 : Qeq (mul (mul q q) (Fsum (fun i => mul (altTerm q 1 i) (altTerm q 1 (m - i))) m))
      (mul (neg (qpow (neg (mul q q)) (m + 1)))
        (Fsum (fun i => (⟨1, fct (2 * i + 1) * fct (2 * (m - i) + 1)⟩ : Q)) m)) :=
    Qeq_trans (Qmul_den_pos (Qmul_den_pos hqd hqd) (Qmul_den_pos hPmden hSfden))
      (Qmul_congr (Qeq_refl (mul q q)) (altConv_factor hqd 1 m))
      (Qeq_trans (Qmul_den_pos (Qmul_den_pos (Qmul_den_pos hqd hqd) hPmden) hSfden)
        (Qmul_assoc3 (mul q q) (qpow (neg (mul q q)) m)
          (Fsum (fun i => (⟨1, fct (2 * i + 1) * fct (2 * (m - i) + 1)⟩ : Q)) m))
        (Qmul_congr (Qmul_qsq_qpow q m) (Qeq_refl _)))
  -- add ≈ (P + (−P))·Sf ≈ 0
  refine Qeq_trans (add_den_pos (Qmul_den_pos hPden hSfden)
      (Qmul_den_pos (show 0 < (neg (qpow (neg (mul q q)) (m + 1))).den from hPden) hSfden))
    (Qadd_congr hc2 hs2) ?_
  refine Qeq_trans (Qmul_den_pos (add_den_pos (a := qpow (neg (mul q q)) (m + 1))
      (b := neg (qpow (neg (mul q q)) (m + 1))) hPden hPden) hSfden)
    (Qeq_symm (Qmul_add_right (qpow (neg (mul q q)) (m + 1)) (neg (qpow (neg (mul q q)) (m + 1)))
      (Fsum (fun i => (⟨1, fct (2 * i + 1) * fct (2 * (m - i) + 1)⟩ : Q)) m))) ?_
  refine Qeq_trans (Qmul_den_pos (show 0 < (⟨0, 1⟩ : Q).den from Nat.one_pos) hSfden)
    (Qmul_congr (show Qeq (add (qpow (neg (mul q q)) (m + 1)) (neg (qpow (neg (mul q q)) (m + 1)))) ⟨0, 1⟩
      from by simp only [Qeq, add, neg]; push_cast; ring_uor) (Qeq_refl _)) ?_
  simp only [Qeq, mul]; push_cast; ring_uor

/-- `(A+B) + (C+D) ≈ A + D` when `C + B ≈ 0`. -/
theorem Qadd_cancel_mid {A B C D : Q} (hA : 0 < A.den) (hB : 0 < B.den) (hC : 0 < C.den) (hD : 0 < D.den)
    (h : Qeq (add C B) ⟨0, 1⟩) : Qeq (add (add A B) (add C D)) (add A D) := by
  refine Qeq_trans (add_den_pos (add_den_pos hA hD) (add_den_pos hC hB))
    (show Qeq (add (add A B) (add C D)) (add (add A D) (add C B)) by
      simp only [Qeq, add]; push_cast; ring_uor) ?_
  refine Qeq_trans (add_den_pos (add_den_pos hA hD) Nat.one_pos)
    (Qadd_congr (Qeq_refl (add A D)) h) ?_
  exact Qadd_zero_right (add A D)

/-- **The Pythagorean telescope**: `Σ_{m≤N} cosConv(m) + Σ_{m≤N} q²·sinConv(m) ≈ 1 + q²·sinConv(N)`.
    By `altPyth_conv_vanish`, `cosConv(m+1) + q²·sinConv(m) ≈ 0`, so consecutive terms cancel, leaving the
    `m=0` cos term (`=1`) and the final `q²·sinConv(N)`. -/
theorem altPyth_telescope {q : Q} (hqd : 0 < q.den) :
    ∀ N, Qeq (add (Fsum (fun m => Fsum (fun i => mul (altTerm q 0 i) (altTerm q 0 (m - i))) m) N)
        (Fsum (fun m => mul (mul q q) (Fsum (fun i => mul (altTerm q 1 i) (altTerm q 1 (m - i))) m)) N))
      (add ⟨1, 1⟩ (mul (mul q q) (Fsum (fun i => mul (altTerm q 1 i) (altTerm q 1 (N - i))) N)))
  | 0 => by
      refine Qadd_congr ?_ (Qeq_refl _)
      show Qeq (mul (altTerm q 0 0) (altTerm q 0 0)) ⟨1, 1⟩
      rw [show altTerm q 0 0 = (⟨1, 1⟩ : Q) from rfl]; decide
  | (N + 1) => by
      have hcc : ∀ m, 0 < (Fsum (fun i => mul (altTerm q 0 i) (altTerm q 0 (m - i))) m).den :=
        fun m => Fsum_den_pos (fun i => Qmul_den_pos (altTerm_den_pos hqd 0 i) (altTerm_den_pos hqd 0 (m - i))) m
      have hqsc : ∀ m, 0 < (mul (mul q q) (Fsum (fun i => mul (altTerm q 1 i) (altTerm q 1 (m - i))) m)).den :=
        fun m => Qmul_den_pos (Qmul_den_pos hqd hqd)
          (Fsum_den_pos (fun i => Qmul_den_pos (altTerm_den_pos hqd 1 i) (altTerm_den_pos hqd 1 (m - i))) m)
      exact Qeq_trans
        (add_den_pos (add_den_pos (Fsum_den_pos hcc N) (Fsum_den_pos hqsc N))
          (add_den_pos (hcc (N + 1)) (hqsc (N + 1))))
        (Qadd_rearrange (Fsum (fun m => Fsum (fun i => mul (altTerm q 0 i) (altTerm q 0 (m - i))) m) N)
          (Fsum (fun i => mul (altTerm q 0 i) (altTerm q 0 (N + 1 - i))) (N + 1))
          (Fsum (fun m => mul (mul q q) (Fsum (fun i => mul (altTerm q 1 i) (altTerm q 1 (m - i))) m)) N)
          (mul (mul q q) (Fsum (fun i => mul (altTerm q 1 i) (altTerm q 1 (N + 1 - i))) (N + 1))))
        (Qeq_trans
          (add_den_pos (add_den_pos Nat.one_pos (hqsc N)) (add_den_pos (hcc (N + 1)) (hqsc (N + 1))))
          (Qadd_congr (altPyth_telescope hqd N) (Qeq_refl _))
          (Qadd_cancel_mid Nat.one_pos (hqsc N) (hcc (N + 1)) (hqsc (N + 1)) (altPyth_conv_vanish hqd N)))

/-- **The partial-sum Pythagorean identity**: `(cosSum N)² + q²·(sinauxSum N)² ≈ 1 + ERR`, where the error
    `ERR = q²·sinConv(N) + cornerCos + q²·cornerSin` collects the final convolution tail and the two
    Cauchy corners. Assembled from `Fsum_sq_cauchy` (cos² and sin² decompositions) and `altPyth_telescope`
    (the antidiagonal telescope to `1`). -/
theorem altPyth_partial {q : Q} (hqd : 0 < q.den) (N : Nat) :
    Qeq (add (mul (Fsum (altTerm q 0) N) (Fsum (altTerm q 0) N))
        (mul (mul q q) (mul (Fsum (altTerm q 1) N) (Fsum (altTerm q 1) N))))
      (add ⟨1, 1⟩ (add (mul (mul q q) (Fsum (fun i => mul (altTerm q 1 i) (altTerm q 1 (N - i))) N))
        (add (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm q 0 i) (altTerm q 0 j)) N)
              (Fsum (fun j => mul (altTerm q 0 i) (altTerm q 0 j)) (N - i))) N)
          (mul (mul q q) (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm q 1 i) (altTerm q 1 j)) N)
              (Fsum (fun j => mul (altTerm q 1 i) (altTerm q 1 j)) (N - i))) N))))) := by
  have ha0 : ∀ i, 0 < (altTerm q 0 i).den := altTerm_den_pos hqd 0
  have ha1 : ∀ i, 0 < (altTerm q 1 i).den := altTerm_den_pos hqd 1
  have hsqd : 0 < (mul q q).den := Qmul_den_pos hqd hqd
  -- the convolution sums and corners
  have hScosd : 0 < (Fsum (fun m => Fsum (fun i => mul (altTerm q 0 i) (altTerm q 0 (m - i))) m) N).den :=
    Fsum_den_pos (fun m => Fsum_den_pos (fun i => Qmul_den_pos (ha0 i) (ha0 (m - i))) m) N
  have hcorCosd : 0 < (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm q 0 i) (altTerm q 0 j)) N)
      (Fsum (fun j => mul (altTerm q 0 i) (altTerm q 0 j)) (N - i))) N).den :=
    Fsum_den_pos (fun i => Qsub_den_pos (Fsum_den_pos (fun j => Qmul_den_pos (ha0 i) (ha0 j)) N)
      (Fsum_den_pos (fun j => Qmul_den_pos (ha0 i) (ha0 j)) (N - i))) N
  have hsinConvd : ∀ m, 0 < (Fsum (fun i => mul (altTerm q 1 i) (altTerm q 1 (m - i))) m).den :=
    fun m => Fsum_den_pos (fun i => Qmul_den_pos (ha1 i) (ha1 (m - i))) m
  have hSsind : 0 < (Fsum (fun m => Fsum (fun i => mul (altTerm q 1 i) (altTerm q 1 (m - i))) m) N).den :=
    Fsum_den_pos hsinConvd N
  have hcorSind : 0 < (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm q 1 i) (altTerm q 1 j)) N)
      (Fsum (fun j => mul (altTerm q 1 i) (altTerm q 1 j)) (N - i))) N).den :=
    Fsum_den_pos (fun i => Qsub_den_pos (Fsum_den_pos (fun j => Qmul_den_pos (ha1 i) (ha1 j)) N)
      (Fsum_den_pos (fun j => Qmul_den_pos (ha1 i) (ha1 j)) (N - i))) N
  have hSqsind : 0 < (Fsum (fun m => mul (mul q q)
      (Fsum (fun i => mul (altTerm q 1 i) (altTerm q 1 (m - i))) m)) N).den :=
    Fsum_den_pos (fun m => Qmul_den_pos hsqd (hsinConvd m)) N
  -- q²·sin² ≈ Σqsin + q²·cornerSin
  have hqsin : Qeq (mul (mul q q) (mul (Fsum (altTerm q 1) N) (Fsum (altTerm q 1) N)))
      (add (Fsum (fun m => mul (mul q q) (Fsum (fun i => mul (altTerm q 1 i) (altTerm q 1 (m - i))) m)) N)
        (mul (mul q q) (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm q 1 i) (altTerm q 1 j)) N)
            (Fsum (fun j => mul (altTerm q 1 i) (altTerm q 1 j)) (N - i))) N))) :=
    Qeq_trans (Qmul_den_pos hsqd (add_den_pos hSsind hcorSind))
      (Qmul_congr (Qeq_refl (mul q q)) (Fsum_sq_cauchy ha1 N))
      (Qeq_trans (add_den_pos (Qmul_den_pos hsqd hSsind) (Qmul_den_pos hsqd hcorSind))
        (Qmul_add_left (mul q q)
          (Fsum (fun m => Fsum (fun i => mul (altTerm q 1 i) (altTerm q 1 (m - i))) m) N)
          (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm q 1 i) (altTerm q 1 j)) N)
            (Fsum (fun j => mul (altTerm q 1 i) (altTerm q 1 j)) (N - i))) N))
        (Qadd_congr (Qeq_symm (Fsum_mul_left hsqd hsinConvd N)) (Qeq_refl _)))
  -- combine cos² and q²·sin²
  refine Qeq_trans (add_den_pos (add_den_pos hScosd hcorCosd) (add_den_pos hSqsind (Qmul_den_pos hsqd hcorSind)))
    (Qadd_congr (Fsum_sq_cauchy ha0 N) hqsin) ?_
  refine Qeq_trans (add_den_pos (add_den_pos hScosd hSqsind) (add_den_pos hcorCosd (Qmul_den_pos hsqd hcorSind)))
    (Qadd_rearrange
      (Fsum (fun m => Fsum (fun i => mul (altTerm q 0 i) (altTerm q 0 (m - i))) m) N)
      (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm q 0 i) (altTerm q 0 j)) N)
        (Fsum (fun j => mul (altTerm q 0 i) (altTerm q 0 j)) (N - i))) N)
      (Fsum (fun m => mul (mul q q) (Fsum (fun i => mul (altTerm q 1 i) (altTerm q 1 (m - i))) m)) N)
      (mul (mul q q) (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm q 1 i) (altTerm q 1 j)) N)
        (Fsum (fun j => mul (altTerm q 1 i) (altTerm q 1 j)) (N - i))) N))) ?_
  refine Qeq_trans (add_den_pos (add_den_pos Nat.one_pos (Qmul_den_pos hsqd (hsinConvd N)))
      (add_den_pos hcorCosd (Qmul_den_pos hsqd hcorSind)))
    (Qadd_congr (altPyth_telescope hqd N) (Qeq_refl _)) ?_
  exact Qadd_assoc3 ⟨1, 1⟩
    (mul (mul q q) (Fsum (fun i => mul (altTerm q 1 i) (altTerm q 1 (N - i))) N))
    (add (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm q 0 i) (altTerm q 0 j)) N)
        (Fsum (fun j => mul (altTerm q 0 i) (altTerm q 0 j)) (N - i))) N)
      (mul (mul q q) (Fsum (fun i => Qsub (Fsum (fun j => mul (altTerm q 1 i) (altTerm q 1 j)) N)
        (Fsum (fun j => mul (altTerm q 1 i) (altTerm q 1 j)) (N - i))) N)))

end UOR.Bridge.F1Square.Analysis
