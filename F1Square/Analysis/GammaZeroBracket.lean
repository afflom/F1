/-
F1 square — v0.22.0 crux frontier: **tightening the Euler–Mascheroni constant `γ`** toward the
`[0.577, 0.578]` bracket the `Pos Rlambda3` (`λ₃`) certificate needs (the dominant constant blocker —
the loose `γ ∈ [0.54, 0.66]` alone keeps `λ₃`'s certified lower bound negative via `−3γ²`).

`γ = Σ_{n≥0} cApprox n ∞`, `cApprox n ∞ = 1/(n+1) − 2·artanh(1/(2n+3))` (the accelerated γ-series term,
`GammaAccel.lean`). The per-term tight rational bracket reuses `GammaOne`'s artanh tail machinery at
`p = n+1` (the term's artanh argument `1/(2n+3) = 1/(2(n+1)+1)`):

  • **lower** `cApprox n T' ≥ cLowQ T n := 1/(n+1) − dPlusQ T (n+1)`  (`dPlusQ` over-estimates `2·artanh`,
    so this under-estimates the term — uniformly in the evaluation depth `T'`, since `artSum` at any
    depth is `≤ artanh ≤ dPlusQ`).

THIS FILE — part (A): the per-term lower bound `cApprox_ge_cLowQ`. The rounded accumulator over `K`
terms, the uniform tail correction `Σ_{n≥K} cApprox n ∞ ≥ 1/(2(K+1))`, and the `Rgamma_h` assembly
follow (mirroring the `GammaOneBracket`/`lnSumLo` pattern).

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.GammaAccel
import F1Square.Analysis.GammaOne

namespace UOR.Bridge.F1Square.Analysis

/-- The **per-term rational lower bound** for the accelerated γ-series term: `1/(n+1) − dPlusQ T (n+1)`
    (`dPlusQ T (n+1)` over-estimates `2·artanh(1/(2n+3))`). -/
def cLowQ (T n : Nat) : Q := Qsub (⟨1, n + 1⟩ : Q) (dPlusQ T (n + 1))

theorem cLowQ_den_pos (T n : Nat) : 0 < (cLowQ T n).den :=
  Qsub_den_pos (Nat.succ_pos n) (dPlusQ_den_pos T (n + 1) (Nat.succ_pos n))

/-- **`cLowQ T n ≤ cApprox n T'`** for every evaluation depth `T'` — the term `cApprox n T'`
    (`= 1/(n+1) − 2·artSum(1/(2n+3), T')`) under-estimated by `cLowQ`, since
    `2·artSum(…, T') ≤ 2·artSum(…, T) + 2·tail = dPlusQ T (n+1)` (`artSum_le_value` + `deltaTail_eq`). -/
theorem cApprox_ge_cLowQ (T n T' : Nat) : Qle (cLowQ T n) (cApprox n T') := by
  -- `2n+3 = 2(n+1)+1` (so `cApprox`'s artanh argument matches `dPlusQ (n+1)`'s)
  have harg : 2 * n + 3 = 2 * (n + 1) + 1 := by omega
  unfold cLowQ cApprox dPlusQ
  rw [harg]
  refine Qadd_le_add (Qle_refl _) (Qneg_le_neg (Qmul_le_mul_left (by decide) ?_))
  -- artSum(1/(2(n+1)+1), T') ≤ artSum(1/(2(n+1)+1), T) + tail
  have htaild : 0 < (⟨1, npow (2 * (n + 1) + 1) (2 * T + 1) * (4 * (n + 1) * ((n + 1) + 1))⟩ : Q).den :=
    Nat.mul_pos (npow_pos (Nat.succ_pos _) _)
      (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos n)) (Nat.succ_pos (n + 1)))
  have hWn : 0 < (Qsub (⟨1, 1⟩ : Q) (mul (⟨1, 2 * (n + 1) + 1⟩ : Q) ⟨1, 2 * (n + 1) + 1⟩)).num := by
    show 0 < (add (⟨1, 1⟩ : Q) (neg (mul ⟨1, 2 * (n + 1) + 1⟩ ⟨1, 2 * (n + 1) + 1⟩))).num
    simp only [add, neg, mul]
    have h9 : ((9 : Nat) : Int)
        ≤ (((2 * (n + 1) + 1) * (2 * (n + 1) + 1) : Nat) : Int) := by
      exact_mod_cast Nat.mul_le_mul (show 3 ≤ 2 * (n + 1) + 1 by omega) (show 3 ≤ 2 * (n + 1) + 1 by omega)
    push_cast at h9 ⊢; omega
  exact artSum_le_value (by show (0 : Int) ≤ 1; decide) (Nat.succ_pos _) htaild hWn T
    (deltaTail_eq (n + 1) T) T'

-- ===========================================================================
-- (B) The rounded accumulator and the partial-sum lower bound `gammaLoBound ≤ Ssum cLowQ ≤ gammaHseq`.
-- ===========================================================================

/-- The **rounded lower-bound accumulator** for `Σ_{n<K} cLowQ T n`, at fixed denominator `D`
    (round down each step, keeping the denominator bounded for a feasible final `decide`). -/
def gammaLoBound (T D : Nat) : Nat → Q
  | 0 => ⟨0, D⟩
  | (K + 1) => qRoundDown (add (gammaLoBound T D K) (cLowQ T K)) D

theorem gammaLoBound_den_pos (T D : Nat) (hD : 0 < D) : ∀ K, 0 < (gammaLoBound T D K).den
  | 0 => hD
  | (_ + 1) => hD

/-- **`gammaLoBound T D K ≤ Σ_{n<K} cLowQ T n`** — the round-down accumulator stays below the exact
    partial sum (`qRoundDown_le` at each step). -/
theorem gammaLoBound_le_Ssum (T D : Nat) (hD : 0 < D) :
    ∀ K, Qle (gammaLoBound T D K) (Ssum (cLowQ T) K)
  | 0 => by
      show Qle (⟨0, D⟩ : Q) (⟨0, 1⟩ : Q); simp only [Qle]; omega
  | (K + 1) => by
      have hadd : 0 < (add (gammaLoBound T D K) (cLowQ T K)).den :=
        add_den_pos (gammaLoBound_den_pos T D hD K) (cLowQ_den_pos T K)
      refine Qle_trans hadd
        (qRoundDown_le (add (gammaLoBound T D K) (cLowQ T K)) hadd D) ?_
      show Qle (add (gammaLoBound T D K) (cLowQ T K)) (add (Ssum (cLowQ T) K) (cLowQ T K))
      exact Qadd_le_add (gammaLoBound_le_Ssum T D hD K) (Qle_refl _)

/-- **`Σ_{n<K} cLowQ T n ≤ gammaHseq j`** for `K ≤ 2(j+1)` — the partial sum of per-term lower bounds
    is dominated by the (longer, deeper) accelerated approximant `gammaHseq j` (`Ssum_le_of_le` with
    `cApprox_ge_cLowQ`, then `Ssum_le` to extend the upper limit; `cApprox` terms are `≥ 0`). -/
theorem Ssum_cLowQ_le_gammaHseq (T j K : Nat) (hK : K ≤ 2 * (j + 1)) :
    Qle (Ssum (cLowQ T) K) (gammaHseq j) := by
  refine Qle_trans (Ssum_den_pos (fun i => cApprox_den_pos i (j + 1)) K)
    (Ssum_le_of_le (fun i => cApprox_ge_cLowQ T i (j + 1)) K) ?_
  show Qle (Ssum (fun i => cApprox i (j + 1)) K) (Ssum (fun i => cApprox i (j + 1)) (gammaHN j))
  exact Ssum_le (fun i => cApprox_num_nonneg i (j + 1)) (fun i => cApprox_den_pos i (j + 1))
    (by unfold gammaHN; omega)

-- ===========================================================================
-- (C) The uniform per-term tail bracket `1/(2(m+1)(m+2)) ≤ cLowQ 3 m ≤ 1/(2m(m+1))`.
-- ===========================================================================

/-- **`dPlusQ 1 (m+1)` in closed form** `[12(2m+3)²(m+1)(m+2) + 4(m+1)(m+2) + 3] / [6(2m+3)³(m+1)(m+2)]`
    (`= 2·(1/(2m+3) + 1/(3(2m+3)³) + 1/(2(2m+3)³(m+1)(m+2)))`). -/
theorem dPlusQ_one_eq (m : Nat) :
    Qeq (dPlusQ 1 (m + 1))
      (⟨12 * (2 * (m : Int) + 3) * (2 * (m : Int) + 3) * ((m : Int) + 1) * ((m : Int) + 2)
          + 4 * ((m : Int) + 1) * ((m : Int) + 2) + 3,
        6 * (2 * m + 3) * (2 * m + 3) * (2 * m + 3) * (m + 1) * (m + 2)⟩ : Q) := by
  unfold dPlusQ
  simp only [artSum, artTerm, qpow, npow, Qeq, mul, add]
  push_cast
  ring_uor

/-- The clean form `≤ (2m+3)/(2(m+1)(m+2))` (cleared difference `= 16·((m+1)(m+2))² ≥ 0`). -/
theorem gcf_le (m : Nat) :
    Qle (⟨12 * (2 * (m : Int) + 3) * (2 * (m : Int) + 3) * ((m : Int) + 1) * ((m : Int) + 2)
          + 4 * ((m : Int) + 1) * ((m : Int) + 2) + 3,
        6 * (2 * m + 3) * (2 * m + 3) * (2 * m + 3) * (m + 1) * (m + 2)⟩ : Q)
        (⟨2 * m + 3, 2 * (m + 1) * (m + 2)⟩ : Q) := by
  simp only [Qle]
  push_cast
  have hX : (0 : Int) ≤ ((m : Int) + 1) * ((m : Int) + 2) := Int.mul_nonneg (by omega) (by omega)
  have key :
      (2 * (m : Int) + 3) * (6 * (2 * (m : Int) + 3) * (2 * (m : Int) + 3) * (2 * (m : Int) + 3)
            * ((m : Int) + 1) * ((m : Int) + 2))
        - (12 * (2 * (m : Int) + 3) * (2 * (m : Int) + 3) * ((m : Int) + 1) * ((m : Int) + 2)
            + 4 * ((m : Int) + 1) * ((m : Int) + 2) + 3) * (2 * ((m : Int) + 1) * ((m : Int) + 2))
      = 16 * (((m : Int) + 1) * ((m : Int) + 2)) * (((m : Int) + 1) * ((m : Int) + 2)) := by ring_uor
  have hnn : (0 : Int) ≤ 16 * (((m : Int) + 1) * ((m : Int) + 2)) * (((m : Int) + 1) * ((m : Int) + 2)) :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) hX) hX
  omega

theorem gcfDen_pos (m : Nat) :
    0 < (⟨12 * (2 * (m : Int) + 3) * (2 * (m : Int) + 3) * ((m : Int) + 1) * ((m : Int) + 2)
          + 4 * ((m : Int) + 1) * ((m : Int) + 2) + 3,
        6 * (2 * m + 3) * (2 * m + 3) * (2 * m + 3) * (m + 1) * (m + 2)⟩ : Q).den :=
  Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide)
    (by omega)) (by omega)) (by omega)) (by omega)) (by omega)

/-- **`dPlusQ 1 (m+1) ≤ (2m+3)/(2(m+1)(m+2))`**. -/
theorem dPlusQ_one_le (m : Nat) :
    Qle (dPlusQ 1 (m + 1)) (⟨2 * m + 3, 2 * (m + 1) * (m + 2)⟩ : Q) :=
  Qle_congr_left (gcfDen_pos m) (Qeq_symm (dPlusQ_one_eq m)) (gcf_le m)

/-- **`d ≤ a − b ⟹ b ≤ a − d`** (both `⟺ b + d ≤ a`). -/
theorem Qle_sub_swap {a b d : Q} (h : Qle d (Qsub a b)) : Qle b (Qsub a d) := by
  simp only [Qle, Qsub, add, neg] at h ⊢
  push_cast at h ⊢
  have key :
      (a.num * (d.den : Int) + -d.num * (a.den : Int)) * (b.den : Int)
        - b.num * ((a.den : Int) * (d.den : Int))
      = (a.num * (b.den : Int) + -b.num * (a.den : Int)) * (d.den : Int)
        - d.num * ((a.den : Int) * (b.den : Int)) := by ring_uor
  omega

/-- **`1/(2(m+1)(m+2)) ≤ cLowQ 1 m`** — the per-term tail lower bound (from `dPlusQ_one_le`). -/
theorem cLowQ_one_tail_lower (m : Nat) :
    Qle (⟨1, 2 * (m + 1) * (m + 2)⟩ : Q) (cLowQ 1 m) := by
  have hQeqR : Qeq (⟨2 * m + 3, 2 * (m + 1) * (m + 2)⟩ : Q)
      (Qsub (⟨1, m + 1⟩ : Q) (⟨1, 2 * (m + 1) * (m + 2)⟩ : Q)) := by
    simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
  have h : Qle (dPlusQ 1 (m + 1)) (Qsub (⟨1, m + 1⟩ : Q) (⟨1, 2 * (m + 1) * (m + 2)⟩ : Q)) :=
    Qle_congr_right (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos m)) (Nat.succ_pos (m + 1)))
      hQeqR (dPlusQ_one_le m)
  exact Qle_sub_swap h

/-- **`1/(2(m+1)(m+2)) ≤ cApprox m T'`** for every depth `T'` — the uniform tail lower bound
    (`cLowQ_one_tail_lower` + `cApprox_ge_cLowQ`). -/
theorem cApprox_tail_lower (m T' : Nat) :
    Qle (⟨1, 2 * (m + 1) * (m + 2)⟩ : Q) (cApprox m T') :=
  Qle_trans (cLowQ_den_pos 1 m) (cLowQ_one_tail_lower m) (cApprox_ge_cLowQ 1 m T')

end UOR.Bridge.F1Square.Analysis
