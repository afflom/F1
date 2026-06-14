/-
F1 square — v0.20.0 stage F: **the certified bracket `γ₂ ≥ −0.02`** via DISCRETE Euler–Maclaurin
(NO constructive integration), tying off `Pos λ₃`.

`γ₂ = g2Seq(N) + tail`, and the trapezoidal anchor `½f(N)` (`f(x)=ln²x/x`) captures the leading tail
`½ln²N/N`, leaving the summable trapezoidal residual `s_p = O(ln²p/p³)`. So
`γ₂ ≥ g2Seq(N) − ½ln²N/N − ε`, certifiable at `N = 200` with the rational squared/cubed-log evaluators.

THIS FILE — part (A): the squared-log lower-bound evaluator `lnSqSumLo` (a rational lower bound for
`Σ_{k≤N}(ln k)²/k`, the `GammaOne.lnSumBound` analogue, lower side, via `logLowBound` squared and
round-down) and the cubed/squared-log upper bounds (`logCube`/`logN²` via `logBound`). Parts (B)/(C)
(the `½ln²N/N` bound and the trapezoidal residual) and the final assembly follow.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.GammaTwo

namespace UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 1000000

-- ===========================================================================
-- (A) `lnSqSumLo` — a rational LOWER bound for `lnSqSum N = Σ_{k=1}^N (ln k)²/k`.
-- ===========================================================================

/-- The accumulated rational lower bound for `Σ_{k=1}^N (ln k)²/k`, at fixed denominator `D`: each new
    term `(log(n+1))²/(n+1) ≥ (logLowBound n)²·(1/(n+1))`, then round DOWN. -/
def lnSqSumLo (T D : Nat) : Nat → Q
  | 0 => ⟨0, D⟩
  | (n + 1) =>
      qRoundDown (add (lnSqSumLo T D n)
        (mul (mul (logLowBound T D n) (logLowBound T D n)) ⟨1, n + 1⟩)) D

theorem lnSqSumLo_den_pos (T D : Nat) (hD : 0 < D) : ∀ N, 0 < (lnSqSumLo T D N).den
  | 0 => hD
  | (_ + 1) => hD

/-- **`ofQ(lnSqSumLo T D N) ≤ lnSqSum N`** — the partial sum `Σ (log k)²/k` bounded BELOW term-by-term
    via `logN_ge_logLowBound` (squared monotonically, both sides nonneg), accumulated at denominator
    `D` (round down), artanh depth `T ≤ 21`. -/
theorem lnSqSumLo_le (T D : Nat) (hD : 0 < D) (hT : T ≤ 21) :
    ∀ N, Rle (ofQ (lnSqSumLo T D N) (lnSqSumLo_den_pos T D hD N)) (lnSqSum N) := by
  intro N
  induction N with
  | zero =>
    have h0 : Req (ofQ (lnSqSumLo T D 0) (lnSqSumLo_den_pos T D hD 0)) zero :=
      Req_of_seq_Qeq (fun n => by show Qeq (⟨0, D⟩ : Q) ⟨0, 1⟩; simp only [Qeq]; push_cast; ring_uor)
    exact Rle_of_Req h0
  | succ n ih =>
    have hLLd := logLowBound_den_pos T D hD n
    have hLLnn : Rnonneg (ofQ (logLowBound T D n) hLLd) :=
      Rnonneg_ofQ hLLd (logLowBound_num_nonneg T D n)
    have hlow := logN_ge_logLowBound T D hD hT n
    have hlognn : Rnonneg (logN (n + 1) (Nat.succ_pos n)) := Rnonneg_logN _ _
    -- per-term lower bound `(LL)²·(1/(n+1)) ≤ (log(n+1))²·(1/(n+1)) = lnSqOver (n+1)`
    have hsq : Rle (Rmul (ofQ (logLowBound T D n) hLLd) (ofQ (logLowBound T D n) hLLd))
        (Rmul (logN (n + 1) (Nat.succ_pos n)) (logN (n + 1) (Nat.succ_pos n))) :=
      Rle_trans (Rmul_le_Rmul_right hLLnn hlow) (Rmul_le_Rmul_left hlognn hlow)
    have hmuld : 0 < (mul (mul (logLowBound T D n) (logLowBound T D n)) (⟨1, n + 1⟩ : Q)).den :=
      Qmul_den_pos (Qmul_den_pos hLLd hLLd) (Nat.succ_pos n)
    have hsqd : 0 < (mul (logLowBound T D n) (logLowBound T D n)).den := Qmul_den_pos hLLd hLLd
    have hterm : Rle (ofQ (mul (mul (logLowBound T D n) (logLowBound T D n)) ⟨1, n + 1⟩) hmuld)
        (lnSqOver (n + 1) (Nat.succ_pos n)) := by
      -- ofQ(LL²·(1/(n+1))) ≈ (ofQ LL·ofQ LL)·ofQ(1/(n+1)) ≤ (log²)·(1/(n+1)) = lnSqOver
      refine Rle_trans (Rle_of_Req ?_)
        (Rmul_le_Rmul_right (Rnonneg_ofQ (Nat.succ_pos n) (by show (0 : Int) ≤ 1; decide)) hsq)
      refine Req_trans (Req_symm (Rmul_ofQ_ofQ hsqd (Nat.succ_pos n))) ?_
      exact Rmul_congr (Req_symm (Rmul_ofQ_ofQ hLLd hLLd)) (Req_refl _)
    -- accumulate: ofQ(round-down(prev + term)) ≤ prev + term ≤ lnSqSum n + lnSqOver(n+1)
    refine Rle_trans (Rle_ofQ_ofQ (lnSqSumLo_den_pos T D hD (n + 1))
      (add_den_pos (lnSqSumLo_den_pos T D hD n) hmuld)
      (qRoundDown_le (add (lnSqSumLo T D n)
        (mul (mul (logLowBound T D n) (logLowBound T D n)) ⟨1, n + 1⟩))
        (add_den_pos (lnSqSumLo_den_pos T D hD n) hmuld) D)) ?_
    refine Rle_trans (Rle_of_Req (Radd_ofQ_ofQ (lnSqSumLo_den_pos T D hD n) hmuld)) ?_
    exact Radd_le_add ih hterm

-- ===========================================================================
-- (B) Cubed/squared-log UPPER bounds (`logBound`).
-- ===========================================================================

/-- `Rnonneg (ofQ (logBound T D M))` — the upper log bound is `≥ log(M+1) ≥ 0`. -/
theorem logBound_ofQ_nonneg (T D M : Nat) (hD : 0 < D) :
    Rnonneg (ofQ (logBound T D M) (logBound_den_pos T D hD M)) :=
  Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg (Rnonneg_logN (M + 1) (Nat.succ_pos M)))
    (logN_le_logBound T D hD M))

/-- `log(M+1)² ≤ logBound²` (squared monotonicity, both sides nonneg). -/
theorem logNsq_le (T D M : Nat) (hD : 0 < D) :
    Rle (Rmul (logN (M + 1) (Nat.succ_pos M)) (logN (M + 1) (Nat.succ_pos M)))
        (Rmul (ofQ (logBound T D M) (logBound_den_pos T D hD M))
              (ofQ (logBound T D M) (logBound_den_pos T D hD M))) :=
  Rle_trans (Rmul_le_Rmul_right (Rnonneg_logN _ _) (logN_le_logBound T D hD M))
    (Rmul_le_Rmul_left (logBound_ofQ_nonneg T D M hD) (logN_le_logBound T D hD M))

/-- **Cubed-log upper bound** `(ln(M+1))³ ≤ logBound³` (`logCube`). -/
theorem logCube_le (T D M : Nat) (hD : 0 < D) :
    Rle (logCube (M + 1) (Nat.succ_pos M))
        (ofQ (mul (mul (logBound T D M) (logBound T D M)) (logBound T D M))
          (Qmul_den_pos (Qmul_den_pos (logBound_den_pos T D hD M) (logBound_den_pos T D hD M))
            (logBound_den_pos T D hD M))) := by
  have LBd := logBound_den_pos T D hD M
  have hLBsqnn : Rnonneg (Rmul (ofQ (logBound T D M) LBd) (ofQ (logBound T D M) LBd)) :=
    Rnonneg_Rmul (logBound_ofQ_nonneg T D M hD) (logBound_ofQ_nonneg T D M hD)
  refine Rle_trans (Rmul_le_Rmul_right (Rnonneg_logN _ _) (logNsq_le T D M hD)) ?_
  refine Rle_trans (Rmul_le_Rmul_left hLBsqnn (logN_le_logBound T D hD M)) ?_
  exact Rle_of_Req (Req_trans (Rmul_congr (Rmul_ofQ_ofQ LBd LBd) (Req_refl _))
    (Rmul_ofQ_ofQ (Qmul_den_pos LBd LBd) LBd))

/-- **Half-squared-over-`N` upper bound** `½·(ln(M+1))²/(M+1) ≤ ½·logBound²/(M+1)` — the trapezoidal
    anchor `½f(M+1)`, `f(x) = ln²x/x`, bounded above. -/
theorem halfSqOver_le (T D M : Nat) (hD : 0 < D) :
    Rle (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide))
          (Rmul (Rmul (logN (M + 1) (Nat.succ_pos M)) (logN (M + 1) (Nat.succ_pos M)))
            (ofQ (⟨1, M + 1⟩ : Q) (Nat.succ_pos M))))
        (ofQ (mul (⟨1, 2⟩ : Q) (mul (mul (logBound T D M) (logBound T D M)) ⟨1, M + 1⟩))
          (Qmul_den_pos (by decide) (Qmul_den_pos
            (Qmul_den_pos (logBound_den_pos T D hD M) (logBound_den_pos T D hD M)) (Nat.succ_pos M)))) := by
  have LBd := logBound_den_pos T D hD M
  have hovnn : Rnonneg (ofQ (⟨1, M + 1⟩ : Q) (Nat.succ_pos M)) :=
    Rnonneg_ofQ (Nat.succ_pos M) (by show (0 : Int) ≤ 1; decide)
  have hinner : Rle (Rmul (Rmul (logN (M + 1) (Nat.succ_pos M)) (logN (M + 1) (Nat.succ_pos M)))
        (ofQ (⟨1, M + 1⟩ : Q) (Nat.succ_pos M)))
      (Rmul (Rmul (ofQ (logBound T D M) LBd) (ofQ (logBound T D M) LBd))
        (ofQ (⟨1, M + 1⟩ : Q) (Nat.succ_pos M))) :=
    Rmul_le_Rmul_right hovnn (logNsq_le T D M hD)
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by show (0 : Int) ≤ 1; decide)) hinner) ?_
  -- ½·((LB·LB)·(1/(M+1)))  ≈  ofQ(½·((logBound·logBound)·(1/(M+1))))
  have hinnerEq : Req (Rmul (Rmul (ofQ (logBound T D M) LBd) (ofQ (logBound T D M) LBd))
        (ofQ (⟨1, M + 1⟩ : Q) (Nat.succ_pos M)))
      (ofQ (mul (mul (logBound T D M) (logBound T D M)) ⟨1, M + 1⟩)
        (Qmul_den_pos (Qmul_den_pos LBd LBd) (Nat.succ_pos M))) :=
    Req_trans (Rmul_congr (Rmul_ofQ_ofQ LBd LBd) (Req_refl _))
      (Rmul_ofQ_ofQ (Qmul_den_pos LBd LBd) (Nat.succ_pos M))
  exact Rle_of_Req (Req_trans (Rmul_congr (Req_refl _) hinnerEq)
    (Rmul_ofQ_ofQ (by decide) (Qmul_den_pos (Qmul_den_pos LBd LBd) (Nat.succ_pos M))))

-- ===========================================================================
-- (C1) The residual framework: `hSeq j = g₂(j) − ½·(ln(j+1))²/(j+1)` (the trapezoidal-corrected
-- sequence, `→ γ₂`), whose per-step increment is the trapezoidal residual `sStep`.
-- ===========================================================================

/-- `x = ½x + ½x`. -/
theorem half_add_self (x : Real) :
    Req x (Radd (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) x) (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) x)) := by
  have hone : Req (Radd (ofQ (⟨1, 2⟩ : Q) (by decide)) (ofQ (⟨1, 2⟩ : Q) (by decide))) one := by
    apply Req_of_seq_Qeq; intro n; simp only [Radd, one, ofQ, add, Qeq]; push_cast
  refine Req_trans ?_ (Rmul_distrib_right (ofQ (⟨1, 2⟩ : Q) (by decide)) (ofQ (⟨1, 2⟩ : Q) (by decide)) x)
  exact Req_symm (Req_trans (Rmul_congr hone (Req_refl x)) (Req_trans (Rmul_comm one x) (Rmul_one x)))

/-- `((u+u) − C) − (u − v) ≈ (u+v) − C` (the residual regrouping; the `u`/`−u` cancel). -/
theorem resid_regroup (u v C : Real) :
    Req (Rsub (Rsub (Radd u u) C) (Rsub u v)) (Rsub (Radd u v) C) := by
  show Req (Radd (Radd (Radd u u) (Rneg C)) (Rneg (Radd u (Rneg v)))) (Radd (Radd u v) (Rneg C))
  have hrn : Req (Rneg (Radd u (Rneg v))) (Radd (Rneg u) v) :=
    Req_trans (Rneg_Radd u (Rneg v)) (Radd_congr (Req_refl _) (Rneg_neg v))
  refine Req_trans (Radd_congr (Req_refl _) hrn) ?_
  refine Req_trans (Radd_assoc (Radd u u) (Rneg C) (Radd (Rneg u) v)) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_comm (Rneg C) (Radd (Rneg u) v))) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_assoc (Rneg u) v (Rneg C))) ?_
  refine Req_trans (Req_symm (Radd_assoc (Radd u u) (Rneg u) (Radd v (Rneg C)))) ?_
  refine Req_trans (Radd_congr ?_ (Req_refl _)) (Req_symm (Radd_assoc u v (Rneg C)))
  exact Req_trans (Radd_assoc u u (Rneg u))
    (Req_trans (Radd_congr (Req_refl u) (Radd_neg u)) (Radd_zero u))

/-- The **trapezoidal-corrected sequence** `h(j) = g₂(j) − ½·(ln(j+1))²/(j+1)` — same limit `γ₂` as
    `g₂`, but its increment is the summable trapezoidal residual. -/
def hSeq (j : Nat) : Real :=
  Rsub (g2Seq j) (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnSqOver (j + 1) (Nat.succ_pos j)))

/-- The **per-step trapezoidal residual** `s_p = ½[(ln(p+1))²/(p+1) + (ln p)²/p] − ⅓[(ln(p+1))³ −
    (ln p)³]` (`p ≥ 1`) — `O(ln²p/p³)`, the increment of `hSeq`. -/
def sStep (p : Nat) (hp : 1 ≤ p) : Real :=
  Rsub (Radd (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnSqOver (p + 1) (Nat.succ_pos p)))
             (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnSqOver p hp)))
       (Rmul (ofQ (⟨1, 3⟩ : Q) (by decide))
         (Rsub (logCube (p + 1) (Nat.succ_pos p)) (logCube p hp)))

/-- **`h(j+1) − h(j) ≈ s_{j+1}`** — the increment of the corrected sequence is the trapezoidal
    residual (`e_{j+1} − ½(f(j+2)−f(j+1))`, regrouped via `half_add_self`/`resid_regroup`). -/
theorem hSeq_step_eq (j : Nat) :
    Req (Rsub (hSeq (j + 1)) (hSeq j)) (sStep (j + 1) (Nat.succ_pos j)) := by
  unfold hSeq sStep
  refine Req_trans (Rsub_sub_sub (g2Seq (j + 1))
    (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnSqOver (j + 2) (Nat.succ_pos (j + 1))))
    (g2Seq j) (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnSqOver (j + 1) (Nat.succ_pos j)))) ?_
  refine Req_trans (Rsub_congr (g2Seq_step_eq j) (Req_refl _)) ?_
  -- e_{j+1} = (ln(j+2))²/(j+2) − ⅓Δ;  rewrite the leading `(ln(j+2))²/(j+2)` as ½·+½·
  refine Req_trans (Rsub_congr
    (Rsub_congr (half_add_self (lnSqOver (j + 2) (Nat.succ_pos (j + 1)))) (Req_refl _))
    (Req_refl _)) ?_
  exact resid_regroup (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnSqOver (j + 2) (Nat.succ_pos (j + 1))))
    (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnSqOver (j + 1) (Nat.succ_pos j)))
    (Rmul (ofQ (⟨1, 3⟩ : Q) (by decide))
      (Rsub (logCube (j + 2) (Nat.succ_pos (j + 1))) (logCube (j + 1) (Nat.succ_pos j))))

-- ===========================================================================
-- (C2) The `s_p` decomposition.  Stage 1: replace the cube difference `a³−b³` by `δ·(a²+ab+b²)`
-- (`cube_diff_identity`), exposing the trapezoidal structure.  Stage 2 (`a = b+δ` collection) follows.
-- ===========================================================================

/-- **Stage 1 of the `s_p` decomposition**: `s_p = ½a²/(p+1) + ½b²/p − ⅓·δ·(a²+ab+b²)`, with
    `a = ln(p+1)`, `b = ln p`, `δ = a − b`. (`a³−b³ = δ(a²+ab+b²)` via `cube_diff_identity`.) -/
theorem sStep_stage1 (p : Nat) (hp : 1 ≤ p) :
    Req (sStep p hp)
        (Rsub (Radd (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide))
                  (Rmul (Rmul (logN (p + 1) (Nat.succ_pos p)) (logN (p + 1) (Nat.succ_pos p)))
                    (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p))))
                (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide))
                  (Rmul (Rmul (logN p hp) (logN p hp)) (ofQ (⟨1, p⟩ : Q) hp))))
          (Rmul (ofQ (⟨1, 3⟩ : Q) (by decide))
            (Rmul (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))
              (Radd (Radd (Rmul (logN (p + 1) (Nat.succ_pos p)) (logN (p + 1) (Nat.succ_pos p)))
                      (Rmul (logN (p + 1) (Nat.succ_pos p)) (logN p hp)))
                (Rmul (logN p hp) (logN p hp)))))) := by
  -- `s_p` is `½·lnSqOver(p+1) + ½·lnSqOver(p) − ⅓·(logCube(p+1) − logCube(p))`; rewrite the cube diff.
  unfold sStep lnSqOver logCube
  refine Rsub_congr (Req_refl _) (Rmul_congr (Req_refl _) ?_)
  -- a³ − b³  ≈  δ·(a²+ab+b²)
  exact Req_symm (cube_diff_identity (logN (p + 1) (Nat.succ_pos p)) (logN p hp))

-- Scalar-merge helpers (coefficients kept as `ofQ` FACTORS so `RMulNF` collapses `½·2=1`, `⅓·3=1`).

/-- `x + x ≈ 2·x`. -/
theorem two_mul_eq (x : Real) : Req (Radd x x) (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) x) := by
  have htwo : Req (Radd one one) (ofQ (⟨2, 1⟩ : Q) (by decide)) := by
    apply Req_of_seq_Qeq; intro n; simp only [Radd, one, ofQ, add, Qeq]; push_cast
  have hx1 : Req x (Rmul one x) := Req_symm (Req_trans (Rmul_comm one x) (Rmul_one x))
  exact Req_trans (Radd_congr hx1 hx1)
    (Req_trans (Req_symm (Rmul_distrib_right one one x)) (Rmul_congr htwo (Req_refl x)))

/-- `(b+d)² ≈ b² + 2·(b·d) + d²` (cross term with coefficient `2` as a factor). -/
theorem sq_binom2 (b d : Real) :
    Req (Rmul (Radd b d) (Radd b d))
        (Radd (Radd (Rmul b b) (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul b d))) (Rmul d d)) := by
  refine Req_trans (Rmul_distrib_right b d (Radd b d)) ?_
  refine Req_trans (Radd_congr (Rmul_distrib b b d) (Rmul_distrib d b d)) ?_
  -- (b² + b·d) + (d·b + d²);  d·b ≈ b·d
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Rmul_comm d b) (Req_refl _))) ?_
  -- (b² + b·d) + (b·d + d²)  ≈  (b² + 2·(b·d)) + d²
  refine Req_trans (Radd_assoc (Rmul b b) (Rmul b d) (Radd (Rmul b d) (Rmul d d))) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Req_symm (Radd_assoc (Rmul b d) (Rmul b d) (Rmul d d)))) ?_
  refine Req_trans (Req_symm (Radd_assoc (Rmul b b) (Radd (Rmul b d) (Rmul b d)) (Rmul d d))) ?_
  exact Radd_congr (Radd_congr (Req_refl _) (two_mul_eq (Rmul b d))) (Req_refl _)

end UOR.Bridge.F1Square.Analysis
