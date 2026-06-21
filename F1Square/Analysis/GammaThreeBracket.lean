/-
F1 square — v0.22.0 crux frontier: **the certified UPPER bracket on the third Stieltjes constant `γ₃`**
via DISCRETE Euler–Maclaurin (NO constructive integration), the `λ₄` (n=4 coupling) input.

`γ₄`'s closed form (`LambdaFour.lean`) carries `γ₃` ONLY through `η₃` with coefficient `+2/3`, so
`λ₄^{arith}` carries `−(2/3)γ₃ ≈ −0.00137`. Hence `Pos λ₄` needs only a LOOSE UPPER bound on `γ₃`
(the side controlling that negative term) — this file builds it.

`γ₃ = g₃(N) + tail` (`g₃(N) = Σ_{k≤N}(ln k)³/k − ¼(ln N)⁴`, `GammaThree.lean`). The trapezoidal anchor
`½f(N)` (`f(x) = (ln x)³/x`) captures the leading tail `½(ln N)³/N`, leaving the summable residual
`s_p = O((ln p)³/p³)`. So `γ₃ ≤ g₃(N) − ½(ln N)³/N + ε = hSeq3(N) + ε`, certifiable at modest `N` with
the rational cubed/quartic-log evaluators.

THIS FILE — part (A): the cubed-log UPPER-sum evaluator `lnCubeSumUp` (a rational upper bound for
`Σ_{k=1}^N (ln k)³/k`, the `GammaTwoBracket.lnSqSumLo` analogue, upper side, via `logBound` cubed and
round-up) and the quartic- and cubed-log LOWER bounds (`logQuartic`/`lnCubeOver` via `logLowBound`), the
pieces of the upper bound on `hSeq3 N`. The accelerated sequence, residual, telescoping and final
assembly follow.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.GammaThree
import F1Square.Analysis.GammaTwoBracket

namespace UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 4000000

-- ===========================================================================
-- (A) `lnCubeSumUp` — a rational UPPER bound for `lnCubeSum N = Σ_{k=1}^N (ln k)³/k`.
-- ===========================================================================

/-- The accumulated rational upper bound for `Σ_{k=1}^N (ln k)³/k`, at fixed denominator `D`: each new
    term `(log(n+1))³/(n+1) ≤ (logBound n)³·(1/(n+1))`, then round UP. -/
def lnCubeSumUp (T D : Nat) : Nat → Q
  | 0 => ⟨0, D⟩
  | (n + 1) =>
      qRoundUp (add (lnCubeSumUp T D n)
        (mul (mul (mul (logBound T D n) (logBound T D n)) (logBound T D n)) ⟨1, n + 1⟩)) D

theorem lnCubeSumUp_den_pos (T D : Nat) (hD : 0 < D) : ∀ N, 0 < (lnCubeSumUp T D N).den
  | 0 => hD
  | (_ + 1) => hD

/-- **`lnCubeSum N ≤ ofQ(lnCubeSumUp T D N)`** — the partial sum `Σ (log k)³/k` bounded ABOVE
    term-by-term via `logCube_le` (depth-`T` `logBound` cubed), accumulated at denominator `D`
    (round up). -/
theorem lnCubeSum_le (T D : Nat) (hD : 0 < D) :
    ∀ N, Rle (lnCubeSum N) (ofQ (lnCubeSumUp T D N) (lnCubeSumUp_den_pos T D hD N)) := by
  intro N
  induction N with
  | zero =>
    have h0 : Req (ofQ (lnCubeSumUp T D 0) (lnCubeSumUp_den_pos T D hD 0)) zero :=
      Req_of_seq_Qeq (fun n => by show Qeq (⟨0, D⟩ : Q) ⟨0, 1⟩; simp only [Qeq]; push_cast; ring_uor)
    exact Rle_of_Req (Req_symm h0)
  | succ n ih =>
    have Ld := logBound_den_pos T D hD n
    have hcubed : 0 < (mul (mul (logBound T D n) (logBound T D n)) (logBound T D n)).den :=
      Qmul_den_pos (Qmul_den_pos Ld Ld) Ld
    have hmuld : 0 < (mul (mul (mul (logBound T D n) (logBound T D n)) (logBound T D n))
        (⟨1, n + 1⟩ : Q)).den := Qmul_den_pos hcubed (Nat.succ_pos n)
    -- per-term upper bound `(ln(n+1))³·(1/(n+1)) ≤ ofQ((logBound n)³·(1/(n+1)))`
    have hterm : Rle (lnCubeOver (n + 1) (by omega))
        (ofQ (mul (mul (mul (logBound T D n) (logBound T D n)) (logBound T D n)) ⟨1, n + 1⟩) hmuld) := by
      refine Rle_trans (Rmul_le_Rmul_right
        (Rnonneg_ofQ (Nat.succ_pos n) (by show (0 : Int) ≤ 1; decide)) (logCube_le T D n hD)) ?_
      exact Rle_of_Req (Rmul_ofQ_ofQ hcubed (Nat.succ_pos n))
    have hadd := add_den_pos (lnCubeSumUp_den_pos T D hD n) hmuld
    -- accumulate: lnCubeSum n + lnCubeOver(n+1) ≤ ofQ(prev + term) ≤ ofQ(round-up)
    refine Rle_trans (Radd_le_add ih hterm) ?_
    refine Rle_trans (Rle_of_Req (Radd_ofQ_ofQ (lnCubeSumUp_den_pos T D hD n) hmuld)) ?_
    exact Rle_ofQ_ofQ hadd (lnCubeSumUp_den_pos T D hD (n + 1))
      (qRoundUp_ge (add (lnCubeSumUp T D n)
        (mul (mul (mul (logBound T D n) (logBound T D n)) (logBound T D n)) ⟨1, n + 1⟩)) hadd D)

-- ===========================================================================
-- (B) Quartic-/cubed-log LOWER bounds (`logLowBound`) — for the subtracted terms of `hSeq3`.
-- ===========================================================================

/-- `ofQ(logLowBound T D M) ≥ 0`. -/
theorem logLowBound_ofQ_nonneg (T D M : Nat) (hD : 0 < D) :
    Rnonneg (ofQ (logLowBound T D M) (logLowBound_den_pos T D hD M)) :=
  Rnonneg_ofQ (logLowBound_den_pos T D hD M) (logLowBound_num_nonneg T D M)

/-- **Cubed-log lower bound** `(logLowBound M)³ ≤ (ln(M+1))³` (`logCube`), depth `T ≤ 21`. -/
theorem logCube_ge (T D M : Nat) (hD : 0 < D) (hT : T ≤ 21) :
    Rle (ofQ (mul (mul (logLowBound T D M) (logLowBound T D M)) (logLowBound T D M))
          (Qmul_den_pos (Qmul_den_pos (logLowBound_den_pos T D hD M) (logLowBound_den_pos T D hD M))
            (logLowBound_den_pos T D hD M)))
        (logCube (M + 1) (Nat.succ_pos M)) := by
  have LLd := logLowBound_den_pos T D hD M
  refine Rle_trans (Rle_of_Req ?_) (cube_mono (logLowBound_ofQ_nonneg T D M hD)
    (Rnonneg_logN (M + 1) (Nat.succ_pos M)) (logN_ge_logLowBound T D hD hT M))
  exact Req_symm (Req_trans (Rmul_congr (Rmul_ofQ_ofQ LLd LLd) (Req_refl _))
    (Rmul_ofQ_ofQ (Qmul_den_pos LLd LLd) LLd))

/-- **Quartic-log lower bound** `(logLowBound M)⁴ ≤ (ln(M+1))⁴` (`logQuartic = logCube·logN`). -/
theorem logQuartic_ge (T D M : Nat) (hD : 0 < D) (hT : T ≤ 21) :
    Rle (ofQ (mul (mul (mul (logLowBound T D M) (logLowBound T D M)) (logLowBound T D M))
            (logLowBound T D M))
          (Qmul_den_pos (Qmul_den_pos (Qmul_den_pos (logLowBound_den_pos T D hD M)
            (logLowBound_den_pos T D hD M)) (logLowBound_den_pos T D hD M))
            (logLowBound_den_pos T D hD M)))
        (logQuartic (M + 1) (Nat.succ_pos M)) := by
  have LLd := logLowBound_den_pos T D hD M
  have hcubed : 0 < (mul (mul (logLowBound T D M) (logLowBound T D M)) (logLowBound T D M)).den :=
    Qmul_den_pos (Qmul_den_pos LLd LLd) LLd
  have hcubenn : Rnonneg (ofQ (mul (mul (logLowBound T D M) (logLowBound T D M)) (logLowBound T D M))
      hcubed) :=
    Rnonneg_congr (Req_trans (Rmul_congr (Rmul_ofQ_ofQ LLd LLd) (Req_refl _))
        (Rmul_ofQ_ofQ (Qmul_den_pos LLd LLd) LLd))
      (Rnonneg_Rmul (Rnonneg_Rmul (logLowBound_ofQ_nonneg T D M hD) (logLowBound_ofQ_nonneg T D M hD))
        (logLowBound_ofQ_nonneg T D M hD))
  -- (LL)⁴ = (LL)³·LL ≤ (ln)³·LL ≤ (ln)³·(ln) = logQuartic
  refine Rle_trans (Rle_of_Req (Rmul_ofQ_ofQ hcubed LLd)) ?_
  refine Rle_trans (Rmul_le_Rmul_right (logLowBound_ofQ_nonneg T D M hD) (logCube_ge T D M hD hT)) ?_
  exact Rmul_le_Rmul_left (logCube_nonneg (M + 1) (Nat.succ_pos M)) (logN_ge_logLowBound T D hD hT M)

/-- **Cubed-log-over-`N` lower bound** `(logLowBound M)³·(1/(M+1)) ≤ (ln(M+1))³/(M+1)` (`lnCubeOver`)
    — the trapezoidal anchor `f(M+1)`, bounded below. -/
theorem lnCubeOver_ge (T D M : Nat) (hD : 0 < D) (hT : T ≤ 21) :
    Rle (ofQ (mul (mul (mul (logLowBound T D M) (logLowBound T D M)) (logLowBound T D M))
            (⟨1, M + 1⟩ : Q))
          (Qmul_den_pos (Qmul_den_pos (Qmul_den_pos (logLowBound_den_pos T D hD M)
            (logLowBound_den_pos T D hD M)) (logLowBound_den_pos T D hD M)) (Nat.succ_pos M)))
        (lnCubeOver (M + 1) (Nat.succ_pos M)) := by
  have LLd := logLowBound_den_pos T D hD M
  have hcubed : 0 < (mul (mul (logLowBound T D M) (logLowBound T D M)) (logLowBound T D M)).den :=
    Qmul_den_pos (Qmul_den_pos LLd LLd) LLd
  have hovnn : Rnonneg (ofQ (⟨1, M + 1⟩ : Q) (Nat.succ_pos M)) :=
    Rnonneg_ofQ (Nat.succ_pos M) (by show (0 : Int) ≤ 1; decide)
  refine Rle_trans (Rle_of_Req (Rmul_ofQ_ofQ hcubed (Nat.succ_pos M))) ?_
  exact Rmul_le_Rmul_right hovnn (logCube_ge T D M hD hT)

-- ===========================================================================
-- (C1) The accelerated sequence `hSeq3 j = g₃(j) − ½·(ln(j+1))³/(j+1)` (`→ γ₃`), whose per-step
-- increment is the trapezoidal residual `sStep3` (`f(x) = (ln x)³/x`, ∫ = ¼(ln x)⁴).
-- ===========================================================================

/-- The Euler–Maclaurin **accelerated sequence** `hSeq3 j = g₃(j) − ½·(ln(j+1))³/(j+1)` — same limit
    `γ₃` as `g₃`, but its increment is the summable trapezoidal residual. -/
def hSeq3 (j : Nat) : Real :=
  Rsub (g3Seq j) (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver (j + 1) (Nat.succ_pos j)))

/-- The **per-step trapezoidal residual** `s_p = ½[(ln(p+1))³/(p+1) + (ln p)³/p] − ¼[(ln(p+1))⁴ −
    (ln p)⁴]` (`p ≥ 1`) — `O((ln p)³/p³)`, the increment of `hSeq3`. -/
def sStep3 (p : Nat) (hp : 1 ≤ p) : Real :=
  Rsub (Radd (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver (p + 1) (Nat.succ_pos p)))
             (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver p hp)))
       (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide))
         (Rsub (logQuartic (p + 1) (Nat.succ_pos p)) (logQuartic p hp)))

/-- **`hSeq3(j+1) − hSeq3 j ≈ s_{j+1}`** — the increment of the accelerated sequence is the trapezoidal
    residual (`g3Seq_step_eq` gives `e_{j+1}`; `half_add_self`/`resid_regroup` move the correction). -/
theorem hSeq3_step_eq (j : Nat) :
    Req (Rsub (hSeq3 (j + 1)) (hSeq3 j)) (sStep3 (j + 1) (Nat.succ_pos j)) := by
  unfold hSeq3 sStep3
  refine Req_trans (Rsub_sub_sub (g3Seq (j + 1))
    (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver (j + 2) (Nat.succ_pos (j + 1))))
    (g3Seq j) (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver (j + 1) (Nat.succ_pos j)))) ?_
  refine Req_trans (Rsub_congr (g3Seq_step_eq j) (Req_refl _)) ?_
  -- e_{j+1} = (ln(j+2))³/(j+2) − ¼Δ; rewrite the leading `(ln(j+2))³/(j+2)` as ½·+½·
  show Req
    (Rsub (Rsub (lnCubeOver (j + 2) (Nat.succ_pos (j + 1)))
        (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide))
          (Rsub (logQuartic (j + 2) (Nat.succ_pos (j + 1))) (logQuartic (j + 1) (Nat.succ_pos j)))))
      (Rsub (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver (j + 2) (Nat.succ_pos (j + 1))))
        (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver (j + 1) (Nat.succ_pos j))))) _
  refine Req_trans (Rsub_congr
    (Rsub_congr (half_add_self (lnCubeOver (j + 2) (Nat.succ_pos (j + 1)))) (Req_refl _))
    (Req_refl _)) ?_
  exact resid_regroup (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver (j + 2) (Nat.succ_pos (j + 1))))
    (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver (j + 1) (Nat.succ_pos j)))
    (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide))
      (Rsub (logQuartic (j + 2) (Nat.succ_pos (j + 1))) (logQuartic (j + 1) (Nat.succ_pos j))))

end UOR.Bridge.F1Square.Analysis
