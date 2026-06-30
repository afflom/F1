/-
F1 square — stage F: **foundations of the `γ₄` numeric bracket** (the sole remaining `n = 5` gate,
toward `Pos λ₅`), via DISCRETE Euler–Maclaurin (NO constructive integration).

The companion-in-progress of `GammaFour.lean` (which built `γ₄ = Rlim g4SeqDyadic`).  THIS FILE builds
the two foundations the bracket rests on:

  (1) the **quartic log cap** `(ln p)⁴ ≤ 256·p` (`logQuart_le_self256`), completing the
      polynomial-log cap family (`logSq_le_self4`, `logCube_le_self27`); the `(ln p)⁴` factor in the
      bracket's leading `b⁴·C2` term is killed by this cap against the `C2 = Θ(1/p³)` trapezoidal
      smallness, giving a CONSTANT per-step bound `sStep4 ≤ C/(p(p+1))` (no log growth);

  (2) the **further-accelerated sequence** `hSeq4 j = g₄(j) − ½·(ln(j+1))⁴/(j+1)` (`→ γ₄`) and its
      per-step trapezoidal residual `sStep4 = O((ln p)⁴/p³)` (`sStep4`, `hSeq4_step_eq`).

What remains (the documented continuation): the `a = b+δ` decomposition
`decompForm4 = b⁴C2 + b³R2 + b²R1 + b·R0 + R0'` (`sStep4 ≈ decompForm4`, the quartic/quintic-binomial
algebra), the per-step bound `sStep4 ≤ C/(p(p+1))`, the telescope `γ₄ ≤ hSeq4(N) + C/(N+1)`, and the
rational evaluator `decide` — exactly the `GammaThreeBracket` ladder one degree up.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.GammaFour
import F1Square.Analysis.GammaThreeBracket

namespace UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 4000000

-- ===========================================================================
-- The quartic cap `(ln p)⁴ ≤ 256·p`.  With `L = ln p ≥ 0`, `M = L/4`:
-- `exp(M) ≥ 1+M ≥ M ≥ 0`, so `exp(L) = exp(4M) = exp(M)⁴ ≥ M⁴`, hence `256·exp(L) ≥ 256·M⁴ = L⁴`.
-- ===========================================================================

/-- **`(a·x)⁴ ≈ a⁴·x⁴`** (quart of a product splits) — `cube_prod_split` plus one reassoc. -/
theorem quart_prod_split (a x : Real) :
    Req (Rmul (Rmul (Rmul (Rmul a x) (Rmul a x)) (Rmul a x)) (Rmul a x))
        (Rmul (Rmul (Rmul (Rmul a a) a) a) (Rmul (Rmul (Rmul x x) x) x)) := by
  refine Req_trans (Rmul_congr (cube_prod_split a x) (Req_refl (Rmul a x))) ?_
  refine Req_trans (Rmul_assoc (Rmul (Rmul a a) a) (Rmul (Rmul x x) x) (Rmul a x)) ?_
  refine Req_trans (Rmul_congr (Req_refl (Rmul (Rmul a a) a))
    (Rmul_left_comm3 (Rmul (Rmul x x) x) a x)) ?_
  exact Req_symm (Rmul_assoc (Rmul (Rmul a a) a) a (Rmul (Rmul (Rmul x x) x) x))

/-- **`L⁴ ≤ 256·exp(L)`** for `L ≥ 0`.  With `M = L/4`: `exp(M) ≥ M ≥ 0`, so
    `exp(L) = exp(M+M+M+M) = exp(M)⁴ ≥ M⁴`, and `256·M⁴ = L⁴`. -/
theorem quart_le_256_exp (L : Real) (hL : Rnonneg L) :
    Rle (Rmul (Rmul (Rmul L L) L) L) (Rmul (ofQ (⟨256, 1⟩ : Q) (by decide)) (RexpReal L)) := by
  have hMnn : Rnonneg (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) L) :=
    Rnonneg_Rmul (Rnonneg_ofQ (by decide) (by decide)) hL
  have hEnn : Rnonneg (RexpReal (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) L)) := RexpReal_nonneg _
  have hMleE : Rle (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) L)
      (RexpReal (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) L)) :=
    Rle_trans (Rle_self_Radd_left Rnonneg_one) (RexpReal_ge_one_add_nonneg hMnn)
  -- M⁴ ≤ E⁴
  have hquart := quartic_mono hMnn hEnn hMleE
  -- M+M+M+M ≈ L
  have hcoef : Req (Radd (Radd (Radd (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) L)
        (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) L)) (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) L))
      (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) L)) L := by
    refine Req_trans (Radd_congr (Radd_congr (Req_symm (Rmul_distrib_right _ _ L)) (Req_refl _))
      (Req_refl _)) ?_
    refine Req_trans (Radd_congr (Req_symm (Rmul_distrib_right _ _ L)) (Req_refl _)) ?_
    refine Req_trans (Req_symm (Rmul_distrib_right _ _ L)) ?_
    refine Req_trans (Rmul_congr ?_ (Req_refl L)) (Rone_mul L)
    refine Req_trans (Radd_congr (Radd_congr (Radd_ofQ_ofQ (by decide) (by decide)) (Req_refl _))
      (Req_refl _)) ?_
    refine Req_trans (Radd_congr (Radd_ofQ_ofQ (by decide) (by decide)) (Req_refl _)) ?_
    exact Req_trans (Radd_ofQ_ofQ (by decide) (by decide)) (ofQ_congr (by decide) (by decide) (by decide))
  -- E⁴ ≈ exp(L)
  have hE4 : Req (Rmul (Rmul (Rmul (RexpReal (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) L))
          (RexpReal (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) L)))
        (RexpReal (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) L)))
        (RexpReal (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) L))) (RexpReal L) := by
    refine Req_trans (Rmul_congr (Rmul_congr (Req_symm (RexpReal_add _ _)) (Req_refl _)) (Req_refl _)) ?_
    refine Req_trans (Rmul_congr (Req_symm (RexpReal_add _ _)) (Req_refl _)) ?_
    exact Req_trans (Req_symm (RexpReal_add _ _)) (RexpReal_congr hcoef)
  -- L⁴ ≈ 256·M⁴
  have hconst : Req (Rmul (ofQ (⟨256, 1⟩ : Q) (by decide))
      (Rmul (Rmul (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) (ofQ (⟨1, 4⟩ : Q) (by decide)))
        (ofQ (⟨1, 4⟩ : Q) (by decide))) (ofQ (⟨1, 4⟩ : Q) (by decide)))) one := by
    refine Req_trans (Rmul_congr (Req_refl _)
        (Req_trans (Rmul_congr (Rmul_congr (Rmul_ofQ_ofQ (by decide) (by decide)) (Req_refl _))
          (Req_refl _)) (Req_trans (Rmul_congr (Rmul_ofQ_ofQ (by decide) (by decide)) (Req_refl _))
            (Rmul_ofQ_ofQ (by decide) (by decide))))) ?_
    exact Req_trans (Rmul_ofQ_ofQ (by decide) (by decide))
      (ofQ_congr (by decide) (by decide) (by decide))
  have hL4 : Req (Rmul (Rmul (Rmul L L) L) L)
      (Rmul (ofQ (⟨256, 1⟩ : Q) (by decide))
        (Rmul (Rmul (Rmul (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) L) (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) L))
            (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) L)) (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) L))) := by
    refine Req_symm ?_
    refine Req_trans (Rmul_congr (Req_refl _) (quart_prod_split (ofQ (⟨1, 4⟩ : Q) (by decide)) L)) ?_
    refine Req_trans (Req_symm (Rmul_assoc (ofQ (⟨256, 1⟩ : Q) (by decide))
        (Rmul (Rmul (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) (ofQ (⟨1, 4⟩ : Q) (by decide)))
          (ofQ (⟨1, 4⟩ : Q) (by decide))) (ofQ (⟨1, 4⟩ : Q) (by decide))) (Rmul (Rmul (Rmul L L) L) L))) ?_
    exact Req_trans (Rmul_congr hconst (Req_refl _)) (Rone_mul _)
  refine Rle_trans (Rle_of_Req hL4) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) hquart) ?_
  exact Rle_of_Req (Rmul_congr (Req_refl _) hE4)

/-- **`(ln p)⁴ ≤ 256·p`** — the quartic cap (`logQuartic p ≤ 256p`), via `quart_le_256_exp` and
    `exp(ln p) = p`.  Completes the polynomial-log cap family (`logSq_le_self4`, `logCube_le_self27`). -/
theorem logQuart_le_self256 (p : Nat) (hp : 1 ≤ p) :
    Rle (logQuartic p hp) (ofQ (⟨256 * (p : Int), 1⟩ : Q) Nat.one_pos) := by
  unfold logQuartic logCube
  refine Rle_trans (quart_le_256_exp (logN p hp) (Rnonneg_logN p hp)) ?_
  refine Rle_trans (Rle_of_Req (Rmul_congr (Req_refl _) (Rexp_logN p hp))) ?_
  exact Rle_of_Req (Req_trans (Rmul_ofQ_ofQ (by decide) Nat.one_pos)
    (ofQ_congr (Qmul_den_pos (by decide) Nat.one_pos) Nat.one_pos
      (by show Qeq (mul (⟨256, 1⟩ : Q) (⟨(p : Int), 1⟩ : Q)) (⟨256 * (p : Int), 1⟩ : Q)
          simp only [Qeq, mul])))

-- ===========================================================================
-- The accelerated sequence `hSeq4 j = g₄(j) − ½·(ln(j+1))⁴/(j+1)` and its per-step residual `sStep4`.
-- ===========================================================================

/-- The trapezoidal-corrected sequence `hSeq4 j = g₄(j) − ½·(ln(j+1))⁴/(j+1)` (`→ γ₄`). -/
def hSeq4 (j : Nat) : Real :=
  Rsub (g4Seq j) (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnQuartOver (j + 1) (Nat.succ_pos j)))

/-- The **per-step trapezoidal residual** `s_p = ½[(ln(p+1))⁴/(p+1) + (ln p)⁴/p] − (1/5)[(ln(p+1))⁵ −
    (ln p)⁵]` (`p ≥ 1`) — `O((ln p)⁴/p³)`, the increment of `hSeq4`. -/
def sStep4 (p : Nat) (hp : 1 ≤ p) : Real :=
  Rsub (Radd (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnQuartOver (p + 1) (Nat.succ_pos p)))
             (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnQuartOver p hp)))
       (Rmul (ofQ (⟨1, 5⟩ : Q) (by decide))
         (Rsub (logQuintic (p + 1) (Nat.succ_pos p)) (logQuintic p hp)))

/-- **`hSeq4(j+1) − hSeq4 j ≈ s_{j+1}`** — the increment of the accelerated sequence is the trapezoidal
    residual (`g4Seq_step_eq` gives `e_{j+1}`; `half_add_self`/`resid_regroup` move the correction). -/
theorem hSeq4_step_eq (j : Nat) :
    Req (Rsub (hSeq4 (j + 1)) (hSeq4 j)) (sStep4 (j + 1) (Nat.succ_pos j)) := by
  unfold hSeq4 sStep4
  refine Req_trans (Rsub_sub_sub (g4Seq (j + 1))
    (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnQuartOver (j + 2) (Nat.succ_pos (j + 1))))
    (g4Seq j) (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnQuartOver (j + 1) (Nat.succ_pos j)))) ?_
  refine Req_trans (Rsub_congr (g4Seq_step_eq j) (Req_refl _)) ?_
  show Req
    (Rsub (Rsub (lnQuartOver (j + 2) (Nat.succ_pos (j + 1)))
        (Rmul (ofQ (⟨1, 5⟩ : Q) (by decide))
          (Rsub (logQuintic (j + 2) (Nat.succ_pos (j + 1))) (logQuintic (j + 1) (Nat.succ_pos j)))))
      (Rsub (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnQuartOver (j + 2) (Nat.succ_pos (j + 1))))
        (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnQuartOver (j + 1) (Nat.succ_pos j))))) _
  refine Req_trans (Rsub_congr
    (Rsub_congr (half_add_self (lnQuartOver (j + 2) (Nat.succ_pos (j + 1)))) (Req_refl _))
    (Req_refl _)) ?_
  exact resid_regroup (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnQuartOver (j + 2) (Nat.succ_pos (j + 1))))
    (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnQuartOver (j + 1) (Nat.succ_pos j)))
    (Rmul (ofQ (⟨1, 5⟩ : Q) (by decide))
      (Rsub (logQuintic (j + 2) (Nat.succ_pos (j + 1))) (logQuintic (j + 1) (Nat.succ_pos j))))

/-- **The quartic binomial** `(b+d)⁴ ≈ b⁴ + 4·b³d + 6·b²d² + 4·bd³ + d⁴` (the `4`s/`6` as `ofQ`
    factors), mirroring `cube_binom` one degree up: start from `cube_binom`, distribute the trailing
    `(b+d)`, normalize the eight monomials with `Rmul_swap_last`/`Rmul_comm`/`Rmul_assoc`, then merge
    like terms via `three_plus_one`/`three_plus_three`/`one_plus_three`. -/
theorem quartic_binom (b d : Real) :
    Req (Rmul (Rmul (Rmul (Radd b d) (Radd b d)) (Radd b d)) (Radd b d))
        (Radd (Radd (Radd (Radd
                  (Rmul (Rmul (Rmul b b) b) b)
                  (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) b) d)))
              (Rmul (ofQ (⟨6, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d)))
            (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b d) d) d)))
          (Rmul (Rmul (Rmul d d) d) d)) := by
  -- (b+d)³ = ((b³ + 3b²d) + 3bd²) + d³, call it C
  refine Req_trans (Rmul_congr (cube_binom b d) (Req_refl (Radd b d))) ?_
  -- distribute trailing (b+d): C·(b+d) = C·b + C·d
  refine Req_trans (Rmul_distrib
    (Radd (Radd (Radd (Rmul (Rmul b b) b)
              (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d)))
          (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d)))
      (Rmul (Rmul d d) d)) b d) ?_
  -- expand C·b into its four monomials, and C·d into its four monomials
  refine Req_trans (Radd_congr
    (Req_trans (Rmul_distrib_right (Radd (Radd (Rmul (Rmul b b) b)
              (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d)))
          (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d)))
        (Rmul (Rmul d d) d) b)
      (Radd_congr (Req_trans (Rmul_distrib_right (Radd (Rmul (Rmul b b) b)
              (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d)))
          (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d)) b)
        (Radd_congr (Rmul_distrib_right (Rmul (Rmul b b) b)
              (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d)) b)
          (Req_refl _))) (Req_refl _)))
    (Req_trans (Rmul_distrib_right (Radd (Radd (Rmul (Rmul b b) b)
              (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d)))
          (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d)))
        (Rmul (Rmul d d) d) d)
      (Radd_congr (Req_trans (Rmul_distrib_right (Radd (Rmul (Rmul b b) b)
              (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d)))
          (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d)) d)
        (Radd_congr (Rmul_distrib_right (Rmul (Rmul b b) b)
              (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d)) d)
          (Req_refl _))) (Req_refl _)))) ?_
  -- normalize the eight monomials.  Canonical: b⁴=((b·b)·b)·b, b³d=((b·b)·b)·d,
  -- b²d²=((b·b)·d)·d, bd³=((b·d)·d)·d, d⁴=((d·d)·d)·d.
  -- (3·X)·f → 3·(X·f) via Rmul_assoc, then normalize X·f.
  have e3b2d_b : Req (Rmul (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d)) b)
      (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) b) d)) :=
    Req_trans (Rmul_assoc (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d) b)
      (Rmul_congr (Req_refl _) (Rmul_swap_last (Rmul b b) d b))
  have e3bd2_b : Req (Rmul (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d)) b)
      (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d)) :=
    Req_trans (Rmul_assoc (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d) b)
      (Rmul_congr (Req_refl _)
        (Req_trans (Rmul_swap_last (Rmul b d) d b)
          (Rmul_congr (Rmul_swap_last b d b) (Req_refl d))))
  have ed3_b : Req (Rmul (Rmul (Rmul d d) d) b) (Rmul (Rmul (Rmul b d) d) d) :=
    Req_trans (Rmul_swap_last (Rmul d d) d b)
      (Rmul_congr (Req_trans (Rmul_swap_last d d b) (Rmul_congr (Rmul_comm d b) (Req_refl d)))
        (Req_refl d))
  have e3b2d_d : Req (Rmul (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d)) d)
      (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d)) :=
    Rmul_assoc (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d) d
  have e3bd2_d : Req (Rmul (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d)) d)
      (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b d) d) d)) :=
    Rmul_assoc (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d) d
  refine Req_trans (Radd_congr
    (Radd_congr (Radd_congr (Radd_congr (Req_refl _) e3b2d_b) e3bd2_b) ed3_b)
    (Radd_congr (Radd_congr (Radd_congr (Req_refl _) e3b2d_d) e3bd2_d) (Req_refl _))) ?_
  -- now: ((b⁴ + 3b³d) + 3b²d²) + bd³  ++  ((b³d + 3b²d²) + 3bd³) + d⁴ ; flatten each 4-term side
  refine Req_trans (Radd_congr
    (Req_trans (Radd_congr (Radd_eq_RsumL3 (Rmul (Rmul (Rmul b b) b) b)
          (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) b) d))
          (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d)))
        (RsumL_singleton (Rmul (Rmul (Rmul b d) d) d)))
      (Req_symm (RsumL_append
        [Rmul (Rmul (Rmul b b) b) b,
         Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) b) d),
         Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d)]
        [Rmul (Rmul (Rmul b d) d) d])))
    (Req_trans (Radd_congr (Radd_eq_RsumL3 (Rmul (Rmul (Rmul b b) b) d)
          (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d))
          (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b d) d) d)))
        (RsumL_singleton (Rmul (Rmul (Rmul d d) d) d)))
      (Req_symm (RsumL_append
        [Rmul (Rmul (Rmul b b) b) d,
         Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d),
         Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b d) d) d)]
        [Rmul (Rmul (Rmul d d) d) d])))) ?_
  -- join the two RsumL's into one 8-list
  refine Req_trans (Req_symm (RsumL_append
    [Rmul (Rmul (Rmul b b) b) b,
     Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) b) d),
     Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d),
     Rmul (Rmul (Rmul b d) d) d]
    [Rmul (Rmul (Rmul b b) b) d,
     Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d),
     Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b d) d) d),
     Rmul (Rmul (Rmul d d) d) d])) ?_
  -- permute [A,B,C1,D,E,C2,G,H] → [A,B,E,C1,C2,D,G,H] (like terms adjacent)
  refine Req_trans (RsumL_perm
    (List.Perm.cons (Rmul (Rmul (Rmul b b) b) b) (List.Perm.cons (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) b) d))
      ((List.Perm.cons (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d)) (List.Perm.swap (Rmul (Rmul (Rmul b b) b) d) (Rmul (Rmul (Rmul b d) d) d) [(Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d)), (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b d) d) d)), (Rmul (Rmul (Rmul d d) d) d)])).trans
        ((List.Perm.swap (Rmul (Rmul (Rmul b b) b) d) (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d)) [(Rmul (Rmul (Rmul b d) d) d), (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d)), (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b d) d) d)), (Rmul (Rmul (Rmul d d) d) d)]).trans
          (List.Perm.cons (Rmul (Rmul (Rmul b b) b) d) (List.Perm.cons (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d))
            (List.Perm.swap (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d)) (Rmul (Rmul (Rmul b d) d) d) [(Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b d) d) d)), (Rmul (Rmul (Rmul d d) d) d)])))))))) ?_
  -- RsumL [A, 3b³d, b³d, 3b²d², 3b²d², bd³, 3bd³, d⁴]; merge adjacent like terms
  -- merge B+E = 3b³d + b³d → 4b³d
  refine Req_trans (Radd_congr (Req_refl _)
    (Req_symm (Radd_assoc (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) b) d))
      (Rmul (Rmul (Rmul b b) b) d)
      (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d))
        (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d))
          (Radd (Rmul (Rmul (Rmul b d) d) d)
            (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b d) d) d))
              (Radd (Rmul (Rmul (Rmul d d) d) d) zero)))))))) ?_
  refine Req_trans (Radd_congr (Req_refl _)
    (Radd_congr (three_plus_one (Rmul (Rmul (Rmul b b) b) d)) (Req_refl _))) ?_
  -- merge C1+C2 = 3b²d² + 3b²d² → 6b²d²
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Req_refl _)
    (Req_symm (Radd_assoc (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d))
      (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d))
      (Radd (Rmul (Rmul (Rmul b d) d) d)
        (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b d) d) d))
          (Radd (Rmul (Rmul (Rmul d d) d) d) zero))))))) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Req_refl _)
    (Radd_congr (three_plus_three (Rmul (Rmul (Rmul b b) d) d)) (Req_refl _)))) ?_
  -- merge D+G = bd³ + 3bd³ → 4bd³
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Req_refl _) (Radd_congr (Req_refl _)
    (Req_symm (Radd_assoc (Rmul (Rmul (Rmul b d) d) d)
      (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b d) d) d))
      (Radd (Rmul (Rmul (Rmul d d) d) d) zero)))))) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Req_refl _) (Radd_congr (Req_refl _)
    (Radd_congr (one_plus_three (Rmul (Rmul (Rmul b d) d) d)) (Req_refl _))))) ?_
  -- strip trailing zero
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Req_refl _) (Radd_congr (Req_refl _)
    (Radd_congr (Req_refl _) (Radd_zero (Rmul (Rmul (Rmul d d) d) d)))))) ?_
  -- right-nested  A·(F·(Sx·(Fo·H)))  →  left-nested  (((A·F)·Sx)·Fo)·H  (3 top-level reassocs)
  refine Req_trans (Req_symm (Radd_assoc (Rmul (Rmul (Rmul b b) b) b) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) b) d)) (Radd (Rmul (ofQ (⟨6, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d)) (Radd (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b d) d) d)) (Rmul (Rmul (Rmul d d) d) d))))) ?_
  refine Req_trans (Req_symm (Radd_assoc (Radd (Rmul (Rmul (Rmul b b) b) b) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) b) d))) (Rmul (ofQ (⟨6, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d)) (Radd (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b d) d) d)) (Rmul (Rmul (Rmul d d) d) d)))) ?_
  exact Req_symm (Radd_assoc (Radd (Radd (Rmul (Rmul (Rmul b b) b) b) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) b) d))) (Rmul (ofQ (⟨6, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) d) d))) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b d) d) d)) (Rmul (Rmul (Rmul d d) d) d))
end UOR.Bridge.F1Square.Analysis
