/-
F1 square — Track 1, item 6 (pure algebra): **the binomial theorem over the constructive `Complex`
API**, `(1 + b)ⁿ = Σ_{k=0}^{n} C(n,k)·bᵏ`, and its consequence for the Li witness term — the
expansion of `1 − wⁿ` (with `w = 1 − 1/ρ`) into the **power-moments** `(1/ρ)ᵏ = (1−w)ᵏ` that the
explicit formula relates to the Stieltjes/`η` data.

This is the constructive heart of the Bombieri–Lagarias *moment* reading, extending the
`witnessSum_eq_linear` line (`LiLinearize.lean`) one step further: where that factored a single
moment `1/ρ` out of each per-zero term, the binomial expansion exposes the *full* moment polynomial
`Σ_k (−1)^{k+1} C(n,k) (1/ρ)ᵏ`. The remaining `bl` content — the classical identity of the moments
`Σ_ρ ρ^{−k}` with the `η`-polynomial — stays the single labelled seam; the crux fields stay `none`.

Nat-scalar multiplication `Cnsmul` keeps the coefficients in `ℕ` (Pascal's rule becomes the clean
additivity `Cnsmul_add`), so no `ofReal`/`ofQ` embedding of the binomial coefficients is needed.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.ComplexSeries
import F1Square.Analysis.LiLinearize
import F1Square.Analysis.RHWitness
import F1Square.Analysis.Binomial

namespace UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (A) Nat-scalar multiplication on `Complex` and its ring laws.
-- ===========================================================================

/-- **Nat-scalar multiple** `c · z = z + z + … + z` (`c` copies). Keeps binomial coefficients in `ℕ`. -/
def Cnsmul : Nat → Complex → Complex
  | 0, _ => Czero
  | (c + 1), z => Cadd z (Cnsmul c z)

/-- `Cnsmul` is congruent in its complex argument. -/
theorem Cnsmul_congr {z z' : Complex} (h : Ceq z z') : ∀ c, Ceq (Cnsmul c z) (Cnsmul c z')
  | 0 => Ceq_refl _
  | (c + 1) => Cadd_congr h (Cnsmul_congr h c)

/-- `1 · z ≈ z`. -/
theorem Cnsmul_one (z : Complex) : Ceq (Cnsmul 1 z) z := cadd_zero z

/-- **Scalar additivity** `(a + b) · z ≈ a·z + b·z` — Pascal's rule, on the complex side. -/
theorem Cnsmul_add (z : Complex) : ∀ a b, Ceq (Cnsmul (a + b) z) (Cadd (Cnsmul a z) (Cnsmul b z))
  | 0, b => by rw [Nat.zero_add]; exact Ceq_symm (czero_cadd (Cnsmul b z))
  | (a + 1), b => by
      rw [Nat.succ_add]
      -- goal: `Cnsmul ((a+b)+1) z ≈ (z + a·z) + b·z`
      have hIH := Cnsmul_add z a b
      exact Ceq_trans (Cadd_congr (Ceq_refl z) hIH)
        (Ceq_symm (Cadd_assoc z (Cnsmul a z) (Cnsmul b z)))

/-- **Left-multiplication pulls through the scalar** `b · (c · z) ≈ c · (b · z)`. -/
theorem Cmul_Cnsmul (b z : Complex) : ∀ c, Ceq (Cmul b (Cnsmul c z)) (Cnsmul c (Cmul b z))
  | 0 => cmul_czero b
  | (c + 1) =>
      Ceq_trans (Cmul_distrib b z (Cnsmul c z))
        (Cadd_congr (Ceq_refl (Cmul b z)) (Cmul_Cnsmul b z c))

-- ===========================================================================
-- (B) Distribution and index-shift for complex finite sums.
-- ===========================================================================

/-- **Left-multiplication distributes over a finite sum** `b · Σ Fₖ ≈ Σ (b · Fₖ)`. -/
theorem Cmul_CsumN (b : Complex) (F : Nat → Complex) :
    ∀ N, Ceq (Cmul b (CsumN F N)) (CsumN (fun k => Cmul b (F k)) N)
  | 0 => cmul_czero b
  | (N + 1) =>
      Ceq_trans (Cmul_distrib b (CsumN F N) (F N))
        (Cadd_congr (Cmul_CsumN b F N) (Ceq_refl (Cmul b (F N))))

/-- **Bounded congruence** for finite sums: agreement of summands below `N` gives equal sums. -/
theorem CsumN_congr_le {F G : Nat → Complex} :
    ∀ {N : Nat}, (∀ k, k < N → Ceq (F k) (G k)) → Ceq (CsumN F N) (CsumN G N)
  | 0, _ => Ceq_refl _
  | (N + 1), h =>
      Cadd_congr (CsumN_congr_le (fun k hk => h k (Nat.lt_succ_of_lt hk)))
        (h N (Nat.lt_succ_self N))

/-- **Subtraction-free index shift** `F 0 + Σ_{k<N} F(k+1) ≈ Σ_{k<N+1} F k`. The clean reindexing
    that lets the `b·Σ` (shifted) sum align with the unshifted sum in the binomial Pascal step. -/
theorem CsumN_shift (F : Nat → Complex) :
    ∀ N, Ceq (Cadd (F 0) (CsumN (fun k => F (k + 1)) N)) (CsumN F (N + 1))
  | 0 => Ceq_trans (cadd_zero (F 0)) (Ceq_symm (czero_cadd (F 0)))
  | (N + 1) =>
      Ceq_trans (Ceq_symm (Cadd_assoc (F 0) (CsumN (fun k => F (k + 1)) N) (F (N + 1))))
        (Cadd_congr (CsumN_shift F N) (Ceq_refl (F (N + 1))))

-- ===========================================================================
-- (C) The binomial theorem `(1 + b)ⁿ = Σ_{k=0}^{n} C(n,k)·bᵏ`.
-- ===========================================================================

/-- The `k`-th binomial summand `C(n,k)·bᵏ` (with the coefficient kept in `ℕ` via `Cnsmul`). -/
def binTermC (b : Complex) (n k : Nat) : Complex := Cnsmul (choose n k) (Cnpow b k)

/-- `(1 + b)·z ≈ z + b·z`. -/
private theorem Cmul_one_add (a z : Complex) : Ceq (Cmul (Cadd Cone a) z) (Cadd z (Cmul a z)) :=
  Ceq_trans (Cmul_comm (Cadd Cone a) z)
    (Ceq_trans (Cmul_distrib z Cone a)
      (Cadd_congr (Cmul_one z) (Cmul_comm z a)))

/-- The top binomial term vanishes: `C(n, n+1)·b^{n+1} ≈ 0`. -/
private theorem binTermC_top_zero (b : Complex) (n : Nat) : Ceq (binTermC b n (n + 1)) Czero := by
  show Ceq (Cnsmul (choose n (n + 1)) (Cnpow b (n + 1))) Czero
  rw [choose_eq_zero_of_lt (Nat.lt_succ_self n)]
  exact Ceq_refl _

/-- The shifted-moment summand `C(n,k)·b^{k+1}`, packaged so its `(k+1)`-reindex is definitional. -/
private def shiftTermC (b : Complex) (n : Nat) : Nat → Complex
  | 0 => Czero
  | (k + 1) => Cnsmul (choose n k) (Cnpow b (k + 1))

/-- **THE BINOMIAL THEOREM** `(1 + b)ⁿ ≈ Σ_{k=0}^{n} C(n,k)·bᵏ`. By induction on `n`: the inductive
    `(1+b)·Sₙ = Sₙ + b·Sₙ` splits into the unshifted sum and the shifted-moment sum, and Pascal's rule
    `C(n+1,k) = C(n,k) + C(n,k−1)` (`choose_succ_succ`) recombines them termwise (`Cnsmul_add`). -/
theorem Cnpow_one_add_eq (b : Complex) :
    ∀ n, Ceq (Cnpow (Cadd Cone b) n) (CsumN (binTermC b n) (n + 1))
  | 0 =>
      -- `1 ≈ 0 + (1·1)`
      Ceq_symm (Ceq_trans (czero_cadd (binTermC b 0 0)) (Cnsmul_one (Cnpow b 0)))
  | (n + 1) => by
      -- IH: `(1+b)ⁿ ≈ Sₙ`
      have hIH := Cnpow_one_add_eq b n
      -- `(1+b)^{n+1} = (1+b)·(1+b)ⁿ ≈ (1+b)·Sₙ ≈ Sₙ + b·Sₙ`
      refine Ceq_trans (Cmul_congr (Ceq_refl (Cadd Cone b)) hIH) ?_
      refine Ceq_trans (Cmul_one_add b (CsumN (binTermC b n) (n + 1))) ?_
      -- `b·Sₙ ≈ Σ_{k<n+1} C(n,k)·b^{k+1} = Σ_{k<n+1} shiftTermC(k+1)`
      have hbS : Ceq (Cmul b (CsumN (binTermC b n) (n + 1)))
          (CsumN (fun k => shiftTermC b n (k + 1)) (n + 1)) :=
        Ceq_trans (Cmul_CsumN b (binTermC b n) (n + 1))
          (CsumN_congr_le (fun k _ =>
            Ceq_trans (Cmul_Cnsmul b (Cnpow b k) (choose n k)) (Ceq_refl _)))
      -- shift it: `Σ_{k<n+1} shiftTermC(k+1) ≈ (shiftTermC 0) + that = Σ_{k<n+2} shiftTermC`
      refine Ceq_trans (Cadd_congr (Ceq_refl (CsumN (binTermC b n) (n + 1)))
        (Ceq_trans hbS (Ceq_trans (Ceq_symm (czero_cadd
            (CsumN (fun k => shiftTermC b n (k + 1)) (n + 1))))
          (CsumN_shift (shiftTermC b n) (n + 1))))) ?_
      -- extend `Sₙ` with its zero top term: `Sₙ ≈ Σ_{k<n+2} binTermC b n`
      have hSext : Ceq (CsumN (binTermC b n) (n + 1)) (CsumN (binTermC b n) (n + 2)) :=
        Ceq_symm (Ceq_trans (Cadd_congr (Ceq_refl _) (binTermC_top_zero b n))
          (cadd_zero (CsumN (binTermC b n) (n + 1))))
      refine Ceq_trans (Cadd_congr hSext (Ceq_refl (CsumN (shiftTermC b n) (n + 2)))) ?_
      -- combine the two length-(n+2) sums and match termwise by Pascal
      refine Ceq_trans (Ceq_symm (CsumN_add (binTermC b n) (shiftTermC b n) (n + 2))) ?_
      refine CsumN_congr_le (fun k _ => ?_)
      -- `binTermC b n k + shiftTermC b n k ≈ binTermC b (n+1) k`
      cases k with
      | zero =>
          show Ceq (Cadd (Cnsmul (choose n 0) (Cnpow b 0)) Czero)
                   (Cnsmul (choose (n + 1) 0) (Cnpow b 0))
          rw [choose_zero_right, choose_zero_right]
          exact cadd_zero (Cnsmul 1 (Cnpow b 0))
      | succ j =>
          show Ceq (Cadd (Cnsmul (choose n (j + 1)) (Cnpow b (j + 1)))
                          (Cnsmul (choose n j) (Cnpow b (j + 1))))
                   (Cnsmul (choose (n + 1) (j + 1)) (Cnpow b (j + 1)))
          rw [choose_succ_succ]
          exact Ceq_trans
            (Cadd_comm (Cnsmul (choose n (j + 1)) (Cnpow b (j + 1)))
              (Cnsmul (choose n j) (Cnpow b (j + 1))))
            (Ceq_symm (Cnsmul_add (Cnpow b (j + 1)) (choose n j) (choose n (j + 1))))

/-- `Cnpow` is congruent in its base (local copy). -/
private theorem Cnpow_congr_loc {z z' : Complex} (h : Ceq z z') :
    ∀ n, Ceq (Cnpow z n) (Cnpow z' n)
  | 0 => Ceq_refl Cone
  | (k + 1) => Cmul_congr h (Cnpow_congr_loc h k)

/-- **The reciprocal-moment expansion** of a Cayley-type factor `w = 1 − u`:
    `wⁿ ≈ Σ_{k=0}^{n} C(n,k)·(−u)ᵏ`. For the Bombieri–Lagarias factor `w = 1 − 1/ρ` the moment is
    `u = 1/ρ`, so this writes each per-zero power `(1 − 1/ρ)ⁿ` over the explicit-formula reciprocal
    moments `(1/ρ)ᵏ = Σ_ρ ρ^{−k}` — the binomial theorem applied to exactly the object the `bl` witness
    sum `Σ_w (1 − Re(wⁿ))` is built from. The remaining classical content (the moments `Σ_ρ ρ^{−k}` as
    the `η`-polynomial) is the single labelled seam; this is its constructive, moment-by-moment shape. -/
theorem Cnpow_one_sub_eq {w u : Complex} (h : Ceq w (Cadd Cone (Cneg u))) (n : Nat) :
    Ceq (Cnpow w n) (CsumN (binTermC (Cneg u) n) (n + 1)) :=
  Ceq_trans (Cnpow_congr_loc h n) (Cnpow_one_add_eq (Cneg u) n)

-- ===========================================================================
-- (D) The witness term in reciprocal-moment form (the per-zero shape of `bl`).
-- ===========================================================================

/-- The **reciprocal-moment polynomial** `Σ_{k=1}^{n} C(n,k)·(−u)ᵏ` of a single zero (the binomial
    expansion with the constant `k = 0` term dropped). For `u = 1/ρ` this is `Σ_{k=1}^{n} C(n,k)·(−1/ρ)ᵏ`,
    whose negative is the per-zero Li contribution `1 − (1 − 1/ρ)ⁿ`. -/
def reciprocalMomentPoly (u : Complex) (n : Nat) : Complex :=
  CsumN (fun k => binTermC (Cneg u) n (k + 1)) n

/-- `−(a + b) ≈ (−a) + (−b)` (componentwise; local). -/
private theorem Cneg_Cadd_loc (a b : Complex) : Ceq (Cneg (Cadd a b)) (Cadd (Cneg a) (Cneg b)) :=
  ⟨Rneg_Radd a.re b.re, Rneg_Radd a.im b.im⟩

/-- The constant binomial term `C(n,0)·b⁰ ≈ 1`. -/
private theorem binTermC_zero (b : Complex) (n : Nat) : Ceq (binTermC b n 0) Cone := by
  show Ceq (Cnsmul (choose n 0) (Cnpow b 0)) Cone
  rw [choose_zero_right]
  exact Cnsmul_one (Cnpow b 0)

/-- **THE PER-ZERO WITNESS TERM IN RECIPROCAL MOMENTS** (complex form): for `w = 1 − u`,
    `1 − wⁿ ≈ −Σ_{k=1}^{n} C(n,k)·(−u)ᵏ`. The binomial expansion of `wⁿ` with the leading `1` cancelling
    the outer `1`, leaving exactly the negated reciprocal-moment polynomial. With `u = 1/ρ` this is the
    per-zero Li contribution `1 − (1 − 1/ρ)ⁿ` written over the explicit-formula moments `(1/ρ)ᵏ`. -/
theorem Cnpow_one_sub_momentPoly {w u : Complex} (h : Ceq w (Cadd Cone (Cneg u))) (n : Nat) :
    Ceq (Cadd Cone (Cneg (Cnpow w n))) (Cneg (reciprocalMomentPoly u n)) := by
  -- `wⁿ ≈ 1 + P` where `P = reciprocalMomentPoly u n` (front-split the binomial sum)
  have hsplit : Ceq (Cnpow w n) (Cadd Cone (reciprocalMomentPoly u n)) :=
    Ceq_trans (Cnpow_one_sub_eq h n)
      (Ceq_trans (Ceq_symm (CsumN_shift (binTermC (Cneg u) n) n))
        (Cadd_congr (binTermC_zero (Cneg u) n) (Ceq_refl (reciprocalMomentPoly u n))))
  -- `1 + (−(1 + P)) ≈ (1 + (−1)) + (−P) ≈ 0 + (−P) ≈ −P`
  refine Ceq_trans (Cadd_congr (Ceq_refl Cone) (Cneg_congr hsplit)) ?_
  refine Ceq_trans (Cadd_congr (Ceq_refl Cone)
    (Cneg_Cadd_loc Cone (reciprocalMomentPoly u n))) ?_
  refine Ceq_trans (Ceq_symm (Cadd_assoc Cone (Cneg Cone)
    (Cneg (reciprocalMomentPoly u n)))) ?_
  exact Ceq_trans (Cadd_congr (Cadd_neg Cone)
    (Ceq_refl (Cneg (reciprocalMomentPoly u n))))
    (czero_cadd (Cneg (reciprocalMomentPoly u n)))

/-- **THE WITNESS TERM IN RECIPROCAL MOMENTS** (real `RHWitness` form): for `w = 1 − u`, the per-zero
    Li witness term `1 − Re(wⁿ)` equals `−Re(Σ_{k=1}^{n} C(n,k)·(−u)ᵏ)` — the real part of the negated
    reciprocal-moment polynomial. This is the per-zero summand of `witnessSum` (`RHWitness.lean`) written
    over the explicit-formula moments `(1/ρ)ᵏ`; summing over the zeros and interchanging the two finite
    sums gives `λₙ` as `Σ_{k=1}^{n} (−1)^{k+1} C(n,k)·M_k` with `M_k = Σ_ρ Re(ρ^{−k})` the order-`k`
    reciprocal moment — leaving the single classical seam `M_k = η`-data. -/
theorem witnessTerm_moment {w u : Complex} (h : Ceq w (Cadd Cone (Cneg u))) (n : Nat) :
    Req (Rsub one (Cnpow w n).re) (Rneg (reciprocalMomentPoly u n).re) :=
  (Cnpow_one_sub_momentPoly h n).1

/-- The **summed reciprocal-moment polynomial** over a zero list of moments `us = {1/ρ}`:
    `Σ_{u∈us} Σ_{k=1}^{n} C(n,k)·(−u)ᵏ`. Its negated real part is the Li witness sum (`witnessSum`). -/
def momentListPoly : List Complex → Nat → Complex
  | [], _ => Czero
  | (u :: rest), n => Cadd (reciprocalMomentPoly u n) (momentListPoly rest n)

/-- **THE WITNESS SUM IN RECIPROCAL-MOMENT FORM**: over the Cayley factors `w = 1 − u` of a list of
    moments `us = {1/ρ}`, the Li witness sum `Σ_w (1 − Re(wⁿ))` equals `−Re(Σ_{u∈us} Σ_{k=1}^{n}
    C(n,k)·(−u)ᵏ)`. The per-zero `witnessTerm_moment` summed over the list (`Rneg_Radd` regrouping the
    negated head against the negated tail). This is `λₙ`'s zero-sum (`bl`) written entirely over the
    explicit-formula reciprocal moments `(1/ρ)ᵏ`: with the order-`k` moment `M_k = Σ_ρ Re(ρ^{−k})` factored
    out (the finite-sum interchange), `λₙ = Σ_{k=1}^{n} (−1)^{k+1} C(n,k)·M_k`, and the sole remaining
    classical seam is the per-order moment identity `M_k = η`-data (the `−ζ′/ζ` Taylor coefficients). -/
theorem witnessSum_eq_neg_momentList (n : Nat) : ∀ (us : List Complex),
    Req (witnessSum (us.map (fun u => Cadd Cone (Cneg u))) n)
        (Rneg (momentListPoly us n).re)
  | [] => Req_symm Rneg_zero
  | (u :: rest) =>
      Req_trans
        (Radd_congr (witnessTerm_moment (Ceq_refl (Cadd Cone (Cneg u))) n)
          (witnessSum_eq_neg_momentList n rest))
        (Req_symm (Rneg_Radd (reciprocalMomentPoly u n).re (momentListPoly rest n).re))

end UOR.Bridge.F1Square.Analysis
