/-
F1 square — the **Bombieri–Lagarias decomposition of `λ₁`** into its archimedean and arithmetic
places, as a genuine theorem (the v0.15.3 bridge deliverable).

By the explicit-formula / Bombieri–Lagarias decomposition (Bombieri–Lagarias, *Complements to Li's
Criterion*, *J. Number Theory* 77 (1999); Coffey, *Effective method…*, 2005), each Li coefficient
splits over the places of `ℚ`,

    λₙ  =  λₙ^{∞}  +  λₙ^{arith}      (`S_∞(n) + S_f(n)`),

the **archimedean** part `S_∞` (from the Gamma factor `π^{-s/2}Γ(s/2)` and the trivial-pole structure)
plus the **finite/arithmetic** part `S_f` (the regularized prime-power sum, the von Mangoldt side). For
`n = 1` the binomial `ζ`-sums are empty and the two pieces are the *constants*

    λ₁^{arith}  =  S_f(1)  =  −η₀  =  γ            (η₀ = −γ; the regularized `Σ Λ` value),
    λ₁^{∞}      =  S_∞(1)  =  1 − γ/2 − ½·log(4π)   (the Gamma place, incl. the trivial pole "1"),

whose sum is `λ₁ = 1 + γ/2 − ½·log(4π)` (`LambdaOne.Rlambda1`). This module builds both pieces as
constructive reals and proves the decomposition `Rlambda1_decomposition`, then packages it as a
genuine **non-trivial** instance of the `Li.LiDecomposition` interface — promoting it from the trivial
inhabitant `λ = λ + 0` (`Li.liDecomposition_genuine`) to one whose `n = 1` slice is the real two-place
split. (The von Mangoldt `Λ` and the prime side `Σ Λ(n)·h(log n)` that *carry* `S_f` are built in
`Analysis/Mangoldt.lean`; deriving the value `S_f(1) = γ` from that prime sum needs `ζ'/ζ` and its
analytic continuation, which is deferred — so we state the BL value `γ`, faithfully labelled, and do
not fabricate the (unbuilt) analytic identification. None of this bears on positivity: the crux
`liPositivityHolds` stays `none`, RH open.)

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.RealPow
import F1Square.Analysis.LambdaOne
import F1Square.Li

namespace UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- `Rhalf` distributes over the ℝ operations (pointwise — `Rhalf` does not reindex, and `Radd`/`Rneg`
-- reindex both sides identically).
-- ===========================================================================

/-- `½·(a + b) ≈ ½·a + ½·b`. -/
theorem Rhalf_Radd (a b : Real) : Req (Rhalf (Radd a b)) (Radd (Rhalf a) (Rhalf b)) := by
  apply Req_of_seq_Qeq; intro n
  simp only [Rhalf, Radd, mul, add, Qeq]; push_cast; ring_uor

/-- `½·(−a) ≈ −(½·a)`. -/
theorem Rhalf_Rneg (a : Real) : Req (Rhalf (Rneg a)) (Rneg (Rhalf a)) := by
  apply Req_of_seq_Qeq; intro n
  simp only [Rhalf, Rneg, mul, neg, Qeq]; push_cast; ring_uor

/-- `½·2 ≈ 1`. -/
theorem Rhalf_two : Req (Rhalf (ofQ ⟨2, 1⟩ (by decide))) one := by
  apply Req_of_seq_Qeq; intro n
  simp only [Rhalf, ofQ, one, mul, Qeq]; decide

-- ===========================================================================
-- The two places of `λ₁` and their sum.
-- ===========================================================================

/-- **The arithmetic (finite-place) part of `λ₁`**: `λ₁^{arith} = S_f(1) = −η₀ = γ`, the regularized
    prime-power (von Mangoldt) contribution. -/
def Rlambda1_arith : Real := Rgamma_h

/-- **The archimedean part of `λ₁`**: `λ₁^{∞} = S_∞(1) = 1 − γ/2 − ½·log(4π)`, the Gamma-factor place
    (with the trivial-pole "1"). -/
def Rlambda1_arch : Real :=
  Radd (Radd one (Rneg (Rhalf Rgamma_h))) (Rneg (Rhalf Rlog4pic))

/-- The canonical normal form `(1 + γ/2) − ½·log(4π)` that both `λ₁` and `arith + arch` reduce to. -/
private def lambda1_canon : Real :=
  Radd (Radd one (Rhalf Rgamma_h)) (Rneg (Rhalf Rlog4pic))

/-- `γ − γ/2 ≈ γ/2` (from `Rhalf_double`: `γ ≈ γ/2 + γ/2`). -/
private theorem gamma_sub_half :
    Req (Radd Rgamma_h (Rneg (Rhalf Rgamma_h))) (Rhalf Rgamma_h) := by
  refine Req_trans (Radd_congr (Req_symm (Rhalf_double Rgamma_h)) (Req_refl _)) ?_
  refine Req_trans (Radd_assoc _ _ _) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_neg _)) ?_
  exact Radd_zero _

/-- `λ₁ = ½·(2 + γ − log 4π)` reduces to the canonical form `(1 + γ/2) − ½·log(4π)`. -/
private theorem lambda1_eq_canon : Req Rlambda1 lambda1_canon := by
  unfold Rlambda1 Rtwolambda1 lambda1_canon
  refine Req_trans (Rhalf_Radd _ _) ?_
  refine Radd_congr ?_ (Rhalf_Rneg _)
  refine Req_trans (Rhalf_Radd _ _) ?_
  exact Radd_congr Rhalf_two (Req_refl _)

/-- `arith + arch = γ + (1 − γ/2 − ½·log 4π)` reduces to the same canonical form. -/
private theorem arith_arch_eq_canon :
    Req (Radd Rlambda1_arith Rlambda1_arch) lambda1_canon := by
  unfold Rlambda1_arith Rlambda1_arch lambda1_canon
  refine Req_trans (Req_symm (Radd_assoc _ _ _)) ?_
  refine Radd_congr ?_ (Req_refl _)
  refine Req_trans (Req_symm (Radd_assoc _ _ _)) ?_
  refine Req_trans (Radd_congr (Radd_comm _ _) (Req_refl _)) ?_
  refine Req_trans (Radd_assoc _ _ _) ?_
  exact Radd_congr (Req_refl _) gamma_sub_half

/-- **The Bombieri–Lagarias decomposition of `λ₁`**: `λ₁ = λ₁^{arith} + λ₁^{∞}` (`γ` plus the
    archimedean `1 − γ/2 − ½·log 4π`), a genuine theorem on constructive reals. -/
theorem Rlambda1_decomposition :
    Req Rlambda1 (Radd Rlambda1_arith Rlambda1_arch) :=
  Req_trans lambda1_eq_canon (Req_symm arith_arch_eq_canon)

-- ===========================================================================
-- Promotion of `Li.LiDecomposition` to a proven NON-trivial instance.
-- ===========================================================================

/-- The arithmetic sequence: `λ₁^{arith}` at `n = 1`, `0` elsewhere (the higher `λₙ^{arith}` need the
    Stieltjes constants of v0.16.0). -/
def liArithSeq : Nat → Real := fun n => if n = 1 then Rlambda1_arith else zero

/-- The archimedean sequence: `λ₁^{∞}` at `n = 1`, `0` elsewhere. -/
def liArchSeq : Nat → Real := fun n => if n = 1 then Rlambda1_arch else zero

/-- The Li-coefficient sequence: the genuine `λ₁` at `n = 1`, and `arith n + arch n` elsewhere (so the
    decomposition holds at every `n`, genuinely so at `n = 1`). -/
def liLamSeq : Nat → Real :=
  fun n => if n = 1 then Rlambda1 else Radd (liArithSeq n) (liArchSeq n)

/-- **`Li.LiDecomposition` is now realized non-trivially.** The split `λₙ = λₙ^{arith} + λₙ^{∞}` holds
    for `liLamSeq`/`liArithSeq`/`liArchSeq`, and at `n = 1` its pieces are the *genuine* arithmetic and
    archimedean parts of `λ₁` (`Rlambda1_decomposition`), not the trivial `λ = λ + 0`. -/
theorem li_decomposition_realized :
    Li.LiDecomposition liLamSeq liArithSeq liArchSeq := by
  intro n
  by_cases h : n = 1
  · subst h
    simp only [liLamSeq, if_pos rfl]
    exact Rlambda1_decomposition
  · simp only [liLamSeq, if_neg h]
    exact Req_refl _

end UOR.Bridge.F1Square.Analysis
