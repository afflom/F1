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

end UOR.Bridge.F1Square.Analysis
