/-
F1 square — v0.22.0 crux frontier: **the two-sided bracket on the first Stieltjes constant `γ₁`** via
the DISCRETE Euler–Maclaurin acceleration (NO constructive integration), the dominant constant brick
for `Pos Rlambda3` (the `n = 3` coupling coefficient).

The defining sequence `gSeq(N) = Σ_{k≤N+1}(ln k)/k − ½(ln(N+1))²` converges to `γ₁` but OVERSHOOTS by
the leading Euler–Maclaurin term `+½·(ln(N+1))/(N+1)` (a *convergence* limit, not a bound-depth limit —
so the existing one-sided `γ₁ ≤ −0.055` cannot be tightened by deeper artanh). Subtracting that
trapezoidal anchor gives the **accelerated sequence**

    hSeq1(j) = gSeq(j) − ½·(ln(j+1))/(j+1),

whose per-step increment is the trapezoidal residual `sStep1(p) = ½(f(p)+f(p+1)) − ∫_p^{p+1} f`,
`f(x) = (ln x)/x`. Because `∫(ln x)/x = ½(ln x)²`, the residual is the SQUARE-difference analogue of
`GammaTwoBracket`'s cube residual (much simpler): `sStep1(p) = ½·WStep(p)` with
`WStep(p) = (f(p)+f(p+1)) − ((ln(p+1))² − (ln p)²)`, and the clean algebraic lower bound

    WStep(p) ≥ −(ln(p+1) − ln p)² ≥ −1/p²       (so  sStep1(p) ≥ −1/(2p²)),

via the trapezoid-≥-integral cancellation `2δ ≤ 1/p + 1/(p+1)` (`deltaLog_le_mid`, `δ = ln(p+1)−ln p`).
Telescoping the `1/(2p²)` tail (the existing `Usum` machinery) gives `γ₁ ≥ hSeq1(N) − 1/(2N)`, a
TIGHT lower bound (`hSeq1(N) ≈ γ₁ + O(1/N²)`), the genuinely missing `λ₃` input.

THIS FILE — part (A): the accelerated sequence, its increment identity, and the per-step lower bound.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.GammaOne
import F1Square.Analysis.GammaTwoBracket

namespace UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 4000000

-- ===========================================================================
-- (A0) Small reusable algebraic identities (the square-difference analogues).
-- ===========================================================================

/-- **`(a+b) − (a−b) ≈ 2b`** — the `b`-companion of `addsub_linear`. -/
theorem addsub_linear_b (a b : Real) :
    Req (Rsub (Radd a b) (Rsub a b)) (Radd b b) := by
  refine Req_trans (Radd_congr (Req_refl (Radd a b))
    (Req_trans (Rneg_Rsub a b) (Radd_comm b (Rneg a)))) ?_
  refine Req_trans (Radd_swap a b (Rneg a) b) ?_
  exact Req_trans (Radd_congr (Radd_neg a) (Req_refl (Radd b b)))
    (Req_trans (Radd_comm zero (Radd b b)) (Radd_zero (Radd b b)))

/-- **`(a²−b²) − (a−b)² ≈ b·(2(a−b))`** ( = `2b·δ`) — the square-difference identity, `b`-grouped so the
    `2δ` factor is bounded by `1/p+1/(p+1)`. -/
theorem sq_diff_identity_b (a b : Real) :
    Req (Rsub (Rsub (Rmul a a) (Rmul b b)) (Rmul (Rsub a b) (Rsub a b)))
        (Rmul b (Radd (Rsub a b) (Rsub a b))) := by
  refine Req_trans (Rsub_congr (Req_symm (Rmul_sub_add_self a b)) (Req_refl _)) ?_
  refine Req_trans (Req_symm (Rmul_sub_distrib (Rsub a b) (Radd a b) (Rsub a b))) ?_
  refine Req_trans (Rmul_congr (Req_refl (Rsub a b)) (addsub_linear_b a b)) ?_
  -- δ·(2b) ≈ b·(2δ)
  refine Req_trans (Rmul_distrib (Rsub a b) b b) ?_
  refine Req_trans (Radd_congr (Rmul_comm (Rsub a b) b) (Rmul_comm (Rsub a b) b)) ?_
  exact Req_symm (Rmul_distrib b (Rsub a b) (Rsub a b))

/-- **`(X+Y) − (X+Z) ≈ Y − Z`** — left-term cancellation. -/
theorem add_sub_add_cancel_left (X Y Z : Real) :
    Req (Rsub (Radd X Y) (Radd X Z)) (Rsub Y Z) := by
  refine Req_trans (Radd_congr (Req_refl (Radd X Y)) (Rneg_Radd X Z)) ?_
  refine Req_trans (Radd_swap X Y (Rneg X) (Rneg Z)) ?_
  exact Req_trans (Radd_congr (Radd_neg X) (Req_refl (Rsub Y Z)))
    (Req_trans (Radd_comm zero (Rsub Y Z)) (Radd_zero (Rsub Y Z)))

-- ===========================================================================
-- (A1) The accelerated sequence and its increment.
-- ===========================================================================

/-- The Euler–Maclaurin **accelerated sequence** `hSeq1(j) = gSeq(j) − ½·(ln(j+1))/(j+1)` — same limit
    `γ₁` as `gSeq`, but its increment is the summable trapezoidal residual. -/
def hSeq1 (j : Nat) : Real :=
  Rsub (gSeq j) (Rhalf (lnOver (j + 1) (Nat.succ_pos j)))

/-- The **(doubled) trapezoidal residual** `WStep(p) = (f(p+1)+f(p)) − ((ln(p+1))² − (ln p)²)`,
    `f(x) = (ln x)/x`. -/
def WStep (p : Nat) (hp : 1 ≤ p) : Real :=
  Rsub (Radd (lnOver (p + 1) (Nat.succ_pos p)) (lnOver p hp))
       (Rsub (Rmul (logN (p + 1) (Nat.succ_pos p)) (logN (p + 1) (Nat.succ_pos p)))
             (Rmul (logN p hp) (logN p hp)))

/-- The **per-step trapezoidal residual** `s_p = ½·WStep(p)` — the increment of `hSeq1`. -/
def sStep1 (p : Nat) (hp : 1 ≤ p) : Real := Rhalf (WStep p hp)

/-- The regroup identity behind `hSeq1_step_eq`: `(L2 − (½A−½B)) − (½L2 − ½L1) ≈ ½((L2+L1) − (A−B))`. -/
theorem step_regroup (L2 L1 A B : Real) :
    Req (Rsub (Rsub L2 (Rsub (Rhalf A) (Rhalf B))) (Rsub (Rhalf L2) (Rhalf L1)))
        (Rhalf (Rsub (Radd L2 L1) (Rsub A B))) := by
  have hRHS : Req (Rhalf (Rsub (Radd L2 L1) (Rsub A B)))
      (Rsub (Radd (Rhalf L2) (Rhalf L1)) (Rsub (Rhalf A) (Rhalf B))) :=
    Req_trans (Rhalf_Rsub (Radd L2 L1) (Rsub A B))
      (Rsub_congr (Rhalf_Radd L2 L1) (Rhalf_Rsub A B))
  refine Req_trans ?_ (Req_symm hRHS)
  refine Req_trans (Rsub_congr (Rsub_congr (Req_symm (Rhalf_double L2)) (Req_refl _)) (Req_refl _)) ?_
  exact resid_regroup (Rhalf L2) (Rhalf L1) (Rsub (Rhalf A) (Rhalf B))

/-- **`hSeq1(j+1) − hSeq1(j) ≈ s_{j+1}`** — the increment of the accelerated sequence is the
    trapezoidal residual (`gSeq_step_eq` for the `gSeq` part, `step_regroup` for the correction). -/
theorem hSeq1_step_eq (j : Nat) :
    Req (Rsub (hSeq1 (j + 1)) (hSeq1 j)) (sStep1 (j + 1) (Nat.succ_pos j)) := by
  refine Req_trans (Rsub_sub_sub (gSeq (j + 1)) (Rhalf (lnOver (j + 2) (Nat.succ_pos (j + 1))))
    (gSeq j) (Rhalf (lnOver (j + 1) (Nat.succ_pos j)))) ?_
  refine Req_trans (Rsub_congr (gSeq_step_eq j) (Req_refl _)) ?_
  exact step_regroup (lnOver (j + 2) (Nat.succ_pos (j + 1))) (lnOver (j + 1) (Nat.succ_pos j))
    (Rmul (logN (j + 2) (Nat.succ_pos (j + 1))) (logN (j + 2) (Nat.succ_pos (j + 1))))
    (Rmul (logN (j + 1) (Nat.succ_pos j)) (logN (j + 1) (Nat.succ_pos j)))

-- ===========================================================================
-- (A2) The per-step lower bound `s_{j+1} ≥ −1/(2(j+1)²)` (the clean trapezoidal cancellation).
-- ===========================================================================

/-- **Abstract trapezoid cancellation**: `(a·u1 + b·u0) − (a²−b²) ≥ −(a−b)²` whenever `b ≥ 0`,
    `a−b ≥ 0`, `u1 ≥ 0`, and `2(a−b) ≤ u0+u1`.  `LHS + δ² ≈ (a·u1+b·u0) − b·2δ ≥ … = δ·u1 ≥ 0`. -/
theorem WStep_ge_negDsq_gen (a b u0 u1 : Real) (hbnn : Rnonneg b)
    (hδnn : Rnonneg (Rsub a b)) (hu1nn : Rnonneg u1)
    (h2δ : Rle (Radd (Rsub a b) (Rsub a b)) (Radd u0 u1)) :
    Rle (Rneg (Rmul (Rsub a b) (Rsub a b)))
        (Rsub (Radd (Rmul a u1) (Rmul b u0)) (Rsub (Rmul a a) (Rmul b b))) := by
  -- (1) Radd LHS' δ² ≈ Rsub S (b·2δ), where S = a·u1 + b·u0, δ = a−b
  have hWid : Req (Radd (Rsub (Radd (Rmul a u1) (Rmul b u0)) (Rsub (Rmul a a) (Rmul b b)))
        (Rmul (Rsub a b) (Rsub a b)))
      (Rsub (Radd (Rmul a u1) (Rmul b u0)) (Rmul b (Radd (Rsub a b) (Rsub a b)))) := by
    have hstep : Req (Radd (Radd (Radd (Rmul a u1) (Rmul b u0))
          (Rneg (Rsub (Rmul a a) (Rmul b b)))) (Rmul (Rsub a b) (Rsub a b)))
        (Radd (Radd (Rmul a u1) (Rmul b u0))
          (Rneg (Rsub (Rsub (Rmul a a) (Rmul b b)) (Rmul (Rsub a b) (Rsub a b))))) := by
      refine Req_trans (Radd_assoc (Radd (Rmul a u1) (Rmul b u0))
        (Rneg (Rsub (Rmul a a) (Rmul b b))) (Rmul (Rsub a b) (Rsub a b))) ?_
      refine Radd_congr (Req_refl _) ?_
      refine Req_trans (Radd_comm (Rneg (Rsub (Rmul a a) (Rmul b b)))
        (Rmul (Rsub a b) (Rsub a b))) ?_
      exact Req_symm (Rneg_Rsub (Rsub (Rmul a a) (Rmul b b)) (Rmul (Rsub a b) (Rsub a b)))
    refine Req_trans hstep ?_
    exact Rsub_congr (Req_refl _) (sq_diff_identity_b a b)
  have h2bd : Rle (Rmul b (Radd (Rsub a b) (Rsub a b))) (Rmul b (Radd u0 u1)) :=
    Rmul_le_Rmul_left hbnn h2δ
  -- (3) Rsub S (b·(u0+u1)) ≈ δ·u1
  have hScancel : Req (Rsub (Radd (Rmul a u1) (Rmul b u0)) (Rmul b (Radd u0 u1)))
      (Rmul (Rsub a b) u1) := by
    refine Req_trans (Rsub_congr (Req_refl _) (Rmul_distrib b u0 u1)) ?_
    refine Req_trans (Rsub_congr (Radd_comm (Rmul a u1) (Rmul b u0)) (Req_refl _)) ?_
    refine Req_trans (add_sub_add_cancel_left (Rmul b u0) (Rmul a u1) (Rmul b u1)) ?_
    exact Req_symm (Rmul_sub_distrib_right a b u1)
  have hchain : Rle zero (Radd (Rsub (Radd (Rmul a u1) (Rmul b u0)) (Rsub (Rmul a a) (Rmul b b)))
      (Rmul (Rsub a b) (Rsub a b))) :=
    Rle_trans (Rle_zero_of_Rnonneg (Rnonneg_Rmul hδnn hu1nn))
      (Rle_trans (Rle_of_Req (Req_symm hScancel))
        (Rle_trans (Rsub_le_sub (Rle_refl _) h2bd)
          (Rle_of_Req (Req_symm hWid))))
  refine Rle_of_Rnonneg_Rsub (Rnonneg_congr ?_ (Rnonneg_of_Rle_zero hchain))
  exact Radd_congr (Req_refl _) (Req_symm (Rneg_neg (Rmul (Rsub a b) (Rsub a b))))

/-- **`2δ ≤ 1/p + 1/(p+1)`** (`δ = ln(p+1) − ln p`) — the trapezoid-≥-integral cancellation,
    from `deltaLog_le_mid` (`δ ≤ ½(1/p+1/(p+1))`). -/
theorem two_delta_le (p : Nat) (hp : 1 ≤ p) :
    Rle (Radd (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))
              (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp)))
        (Radd (ofQ (⟨1, p⟩ : Q) hp) (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p))) := by
  have hmid := deltaLog_le_mid p hp
  have hMd : 0 < (mul (⟨1, 2⟩ : Q) (add (⟨1, p⟩ : Q) (⟨1, p + 1⟩ : Q))).den :=
    Qmul_den_pos (by decide)
      (add_den_pos (a := (⟨1, p⟩ : Q)) (b := (⟨1, p + 1⟩ : Q)) hp (Nat.succ_pos p))
  refine Rle_trans (Radd_le_add hmid hmid) (Rle_of_Req ?_)
  refine Req_trans (Radd_ofQ_ofQ hMd hMd) ?_
  refine Req_trans (ofQ_congr (add_den_pos hMd hMd)
    (add_den_pos (a := (⟨1, p⟩ : Q)) (b := (⟨1, p + 1⟩ : Q)) hp (Nat.succ_pos p)) ?_) ?_
  · show Qeq (add (mul (⟨1, 2⟩ : Q) (add (⟨1, p⟩ : Q) (⟨1, p + 1⟩ : Q)))
        (mul (⟨1, 2⟩ : Q) (add (⟨1, p⟩ : Q) (⟨1, p + 1⟩ : Q))))
      (add (⟨1, p⟩ : Q) (⟨1, p + 1⟩ : Q))
    simp only [Qeq, add, mul]; push_cast; ring_uor
  · exact Req_symm (Radd_ofQ_ofQ (a := (⟨1, p⟩ : Q)) (b := (⟨1, p + 1⟩ : Q)) hp (Nat.succ_pos p))

/-- **`WStep(p) ≥ −(ln(p+1) − ln p)²`** — `WStep_ge_negDsq_gen` at the log/reciprocal atoms. -/
theorem WStep_ge_negDsq (p : Nat) (hp : 1 ≤ p) :
    Rle (Rneg (Rmul (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))
                    (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))))
        (WStep p hp) :=
  WStep_ge_negDsq_gen (logN (p + 1) (Nat.succ_pos p)) (logN p hp)
    (ofQ (⟨1, p⟩ : Q) hp) (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p))
    (Rnonneg_logN p hp) (Rnonneg_Rsub_of_Rle (logN_mono hp (Nat.le_succ p)))
    (Rnonneg_ofQ (Nat.succ_pos p) (by show (0 : Int) ≤ 1; decide)) (two_delta_le p hp)

/-- **`WStep(p) ≥ −1/p²`** — the numeric per-step lower bound (`δ² ≤ 1/p²`, `dsq_self_le`). -/
theorem WStep_ge (p : Nat) (hp : 1 ≤ p) :
    Rle (Rneg (ofQ (mul (⟨1, p⟩ : Q) (⟨1, p⟩ : Q)) (Qmul_den_pos hp hp))) (WStep p hp) :=
  Rle_trans (Rle_Rneg (dsq_self_le p hp)) (WStep_ge_negDsq p hp)

/-- **`s_{j+1} ≥ −1/(2(j+1)²)`** — the per-step lower bound on the accelerated increment. -/
theorem sStep1_ge (p : Nat) (hp : 1 ≤ p) :
    Rle (Rneg (ofQ (⟨1, 2 * p * p⟩ : Q) (Nat.mul_pos (Nat.mul_pos (by decide) hp) hp)))
        (sStep1 p hp) := by
  have hppd : 0 < (mul (⟨1, p⟩ : Q) (⟨1, p⟩ : Q)).den := Qmul_den_pos hp hp
  refine Rle_trans (Rle_of_Req ?_) (Rhalf_le_Rhalf (WStep_ge p hp))
  -- −1/(2p²) ≈ ½·(−1/p²)
  refine Req_trans ?_ (Req_symm (Req_trans
    (Rhalf_Rneg (ofQ (mul (⟨1, p⟩ : Q) (⟨1, p⟩ : Q)) hppd))
    (Rneg_congr (Rhalf_ofQ (mul (⟨1, p⟩ : Q) (⟨1, p⟩ : Q)) hppd))))
  refine Rneg_congr (ofQ_congr (Nat.mul_pos (Nat.mul_pos (by decide) hp) hp)
    (Qmul_den_pos (by decide) hppd) ?_)
  show Qeq (⟨1, 2 * p * p⟩ : Q) (mul (⟨1, 2⟩ : Q) (mul (⟨1, p⟩ : Q) (⟨1, p⟩ : Q)))
  simp only [Qeq, mul]; push_cast; ring_uor

end UOR.Bridge.F1Square.Analysis
