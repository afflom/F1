/-
F1 square — the **third Stieltjes constant `γ₃`** (the `n = 4` arithmetic ingredient that, with
`γ, γ₁, γ₂` and `ζ(2), ζ(3), ζ(4), log 4π`, gives the fourth Li coefficient `λ₄`).

`γ₃` is the limit of the **defining sequence**

    g₃(N) = S₃(N) − ¼·(ln N)⁴,        S₃(N) = Σ_{k=1}^N (ln k)³/k,

i.e. `γ₃ = lim_{N→∞} [ Σ_{k=1}^N (ln k)³/k − ¼(ln N)⁴ ] ≈ +0.00205`. Telescoping the `¼(ln N)⁴` term,
`g₃(N) = Σ_{k=2}^N e_k` with `e_k = (ln k)³/k − ¼[(ln k)⁴ − (ln(k−1))⁴]`; the leading `(ln k)³/k`
terms cancel against the quartic-log difference, leaving `e_k = O((ln k)³/k²)`, a convergent tail —
so `γ₃ := Rlim g₃Seq` is a genuine constructive real (the regularity is the analytic content scoped
on top of this substrate, mirroring `GammaTwo` for `γ₂`).

THIS FILE (brick 1 of γ₃): the real substrate — the term `(ln k)³/k` (reusing `GammaTwo.logCube`
`= (ln k)³`), the partial sum `S₃(N)`, the quartic `(ln N)⁴`, the sequence `g₃(N)`, the per-step
difference `e₃`, and the telescoping identity `g₃(j+1) − g₃(j) ≈ e₃`. The monotonicity/regularity
layers and the certified bracket follow (the γ₃ analogue of `GammaTwo`'s dyadic-tail stack).

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.GammaTwo

namespace UOR.Bridge.F1Square.Analysis

/-- The cubed-log harmonic term `(ln k)³/k` (for `k ≥ 1`), as a constructive real
    (reuses `logCube k = (ln k)³`). -/
def lnCubeOver (k : Nat) (hk : 1 ≤ k) : Real :=
  Rmul (logCube k hk) (ofQ ⟨1, k⟩ (by show 0 < k; omega))

/-- Each term `(ln k)³/k ≥ 0` (`(ln k)³ ≥ 0` and `1/k > 0`). -/
theorem lnCubeOver_nonneg (k : Nat) (hk : 1 ≤ k) : Rnonneg (lnCubeOver k hk) :=
  Rnonneg_Rmul (logCube_nonneg k hk)
    (Rnonneg_ofQ (by show 0 < k; omega) (by show (0 : Int) ≤ 1; decide))

/-- The partial sum `S₃(N) = Σ_{k=1}^N (ln k)³/k`. -/
def lnCubeSum : Nat → Real
  | 0 => zero
  | (n + 1) => Radd (lnCubeSum n) (lnCubeOver (n + 1) (by omega))

/-- `S₃(n) ≤ S₃(n+1)` (the new term is `≥ 0`). -/
theorem lnCubeSum_step (n : Nat) : Rle (lnCubeSum n) (lnCubeSum (n + 1)) :=
  Rle_self_Radd_right (lnCubeOver_nonneg (n + 1) (by omega))

/-- `S₃` is monotone (non-decreasing). -/
theorem lnCubeSum_mono {a b : Nat} (hab : a ≤ b) : Rle (lnCubeSum a) (lnCubeSum b) := by
  induction hab with
  | refl => exact Rle_refl _
  | step _ ih => exact Rle_trans ih (lnCubeSum_step _)

/-- The quartic `(ln N)⁴` as a constructive real (`= (ln N)³ · ln N`). -/
def logQuartic (N : Nat) (hN : 1 ≤ N) : Real :=
  Rmul (logCube N hN) (logN N hN)

/-- `(ln N)⁴ ≥ 0` for `N ≥ 1`. -/
theorem logQuartic_nonneg (N : Nat) (hN : 1 ≤ N) : Rnonneg (logQuartic N hN) :=
  Rnonneg_Rmul (logCube_nonneg N hN) (Rnonneg_logN N hN)

/-- The **defining sequence** `g₃(j+1) = S₃(j+1) − ¼·(ln (j+1))⁴` (indexed from `j = 0`).
    `γ₃ = Rlim g₃Seq`. -/
def g3Seq (j : Nat) : Real :=
  Rsub (lnCubeSum (j + 1)) (Rmul (ofQ ⟨1, 4⟩ (by decide)) (logQuartic (j + 1) (by omega)))

-- ===========================================================================
-- The per-step difference `e_{p+1} = g₃(p+1) − g₃(p)` and its telescoping identity.
-- ===========================================================================

/-- The per-step difference `e_{p+1} = g₃(p+1) − g₃(p) = (ln(p+1))³/(p+1) − ¼((ln(p+1))⁴ − (ln p)⁴)`
    (`p ≥ 1`). -/
def e3Step (p : Nat) (hp : 1 ≤ p) : Real :=
  Rsub (lnCubeOver (p + 1) (Nat.succ_pos p))
    (Rmul (ofQ ⟨1, 4⟩ (by decide))
      (Rsub (logQuartic (p + 1) (Nat.succ_pos p)) (logQuartic p hp)))

/-- **`g₃(j+1) − g₃(j) ≈ e_{j+1}`** — the consecutive difference is the per-step `e` (telescoping). -/
theorem g3Seq_step_eq (j : Nat) :
    Req (Rsub (g3Seq (j + 1)) (g3Seq j)) (e3Step (j + 1) (Nat.succ_pos j)) := by
  -- the sum telescopes: S₃(j+2) − S₃(j+1) = (ln(j+2))³/(j+2)
  have hA : Req (Rsub (lnCubeSum (j + 2)) (lnCubeSum (j + 1)))
      (lnCubeOver (j + 2) (Nat.succ_pos (j + 1))) := by
    show Req (Rsub (Radd (lnCubeSum (j + 1)) (lnCubeOver (j + 2) (by omega))) (lnCubeSum (j + 1)))
             (lnCubeOver (j + 2) (Nat.succ_pos (j + 1)))
    refine Req_trans (Rsub_congr (Radd_comm (lnCubeSum (j + 1)) (lnCubeOver (j + 2) (by omega)))
      (Req_refl _)) ?_
    refine Req_trans (Radd_assoc (lnCubeOver (j + 2) (by omega)) (lnCubeSum (j + 1))
      (Rneg (lnCubeSum (j + 1)))) ?_
    exact Req_trans (Radd_congr (Req_refl _) (Radd_neg (lnCubeSum (j + 1)))) (Radd_zero _)
  -- the quartic term: ¼Q(j+2) − ¼Q(j+1) = ¼(Q(j+2) − Q(j+1))
  have hB : Req (Rsub (Rmul (ofQ ⟨1, 4⟩ (by decide)) (logQuartic (j + 2) (by omega)))
        (Rmul (ofQ ⟨1, 4⟩ (by decide)) (logQuartic (j + 1) (by omega))))
      (Rmul (ofQ ⟨1, 4⟩ (by decide))
        (Rsub (logQuartic (j + 2) (by omega)) (logQuartic (j + 1) (by omega)))) :=
    Req_symm (Rmul_sub_distrib (ofQ ⟨1, 4⟩ (by decide)) (logQuartic (j + 2) (by omega))
      (logQuartic (j + 1) (by omega)))
  -- rearrange and combine
  refine Req_trans (Rsub_sub_sub (lnCubeSum (j + 2))
    (Rmul (ofQ ⟨1, 4⟩ (by decide)) (logQuartic (j + 2) (by omega)))
    (lnCubeSum (j + 1)) (Rmul (ofQ ⟨1, 4⟩ (by decide)) (logQuartic (j + 1) (by omega)))) ?_
  exact Rsub_congr hA hB

-- ===========================================================================
-- The quartic algebra: `a⁴ − b⁴ = (a−b)(a³+a²b+ab²+b³)` and the cancellation identity.
-- ===========================================================================

/-- `c·(x·y) ≈ x·(c·y)` — pull a left factor inward. -/
theorem Rmul_left_comm3 (c x y : Real) : Req (Rmul c (Rmul x y)) (Rmul x (Rmul c y)) :=
  Req_trans (Req_symm (Rmul_assoc c x y))
    (Req_trans (Rmul_congr (Rmul_comm c x) (Req_refl y)) (Rmul_assoc x c y))

set_option maxHeartbeats 1000000 in
/-- **`(a−b)(a³ + a²b + ab² + b³) ≈ a⁴ − b⁴`** — the difference-of-quartics factoring
    (the quartic analogue of `cube_diff_identity`), with `a⁴ = ((a·a)·a)·a`, `b⁴ = ((b·b)·b)·b`. -/
theorem quartic_diff_identity (a b : Real) :
    Req (Rmul (Rsub a b)
          (Radd (Radd (Radd (Rmul (Rmul a a) a) (Rmul (Rmul a a) b)) (Rmul (Rmul a b) b))
            (Rmul (Rmul b b) b)))
        (Rsub (Rmul (Rmul (Rmul a a) a) a) (Rmul (Rmul (Rmul b b) b) b)) := by
  refine Req_trans (Rmul_sub_distrib_right a b
    (Radd (Radd (Radd (Rmul (Rmul a a) a) (Rmul (Rmul a a) b)) (Rmul (Rmul a b) b))
      (Rmul (Rmul b b) b))) ?_
  have haS : Req (Rmul a (Radd (Radd (Radd (Rmul (Rmul a a) a) (Rmul (Rmul a a) b)) (Rmul (Rmul a b) b))
        (Rmul (Rmul b b) b)))
      (Radd (Radd (Radd (Rmul a (Rmul (Rmul a a) a)) (Rmul a (Rmul (Rmul a a) b)))
        (Rmul a (Rmul (Rmul a b) b))) (Rmul a (Rmul (Rmul b b) b))) :=
    Req_trans (Rmul_distrib a (Radd (Radd (Rmul (Rmul a a) a) (Rmul (Rmul a a) b)) (Rmul (Rmul a b) b))
        (Rmul (Rmul b b) b))
      (Radd_congr (Req_trans (Rmul_distrib a (Radd (Rmul (Rmul a a) a) (Rmul (Rmul a a) b))
            (Rmul (Rmul a b) b))
          (Radd_congr (Rmul_distrib a (Rmul (Rmul a a) a) (Rmul (Rmul a a) b)) (Req_refl _)))
        (Req_refl _))
  have hbS : Req (Rmul b (Radd (Radd (Radd (Rmul (Rmul a a) a) (Rmul (Rmul a a) b)) (Rmul (Rmul a b) b))
        (Rmul (Rmul b b) b)))
      (Radd (Radd (Radd (Rmul b (Rmul (Rmul a a) a)) (Rmul b (Rmul (Rmul a a) b)))
        (Rmul b (Rmul (Rmul a b) b))) (Rmul b (Rmul (Rmul b b) b))) :=
    Req_trans (Rmul_distrib b (Radd (Radd (Rmul (Rmul a a) a) (Rmul (Rmul a a) b)) (Rmul (Rmul a b) b))
        (Rmul (Rmul b b) b))
      (Radd_congr (Req_trans (Rmul_distrib b (Radd (Rmul (Rmul a a) a) (Rmul (Rmul a a) b))
            (Rmul (Rmul a b) b))
          (Radd_congr (Rmul_distrib b (Rmul (Rmul a a) a) (Rmul (Rmul a a) b)) (Req_refl _)))
        (Req_refl _))
  refine Req_trans (Rsub_congr haS hbS) ?_
  -- cross-term identifications: a·A2B = b·A3, a·AB2 = b·A2B, a·B3 = b·AB2
  have hx1 : Req (Rmul a (Rmul (Rmul a a) b)) (Rmul b (Rmul (Rmul a a) a)) :=
    Req_trans (Rmul_left_comm3 a (Rmul a a) b)
      (Req_trans (Rmul_congr (Req_refl _) (Rmul_comm a b)) (Rmul_left_comm3 (Rmul a a) b a))
  have hx2 : Req (Rmul a (Rmul (Rmul a b) b)) (Rmul b (Rmul (Rmul a a) b)) :=
    Req_trans (Rmul_left_comm3 a (Rmul a b) b)
      (Req_trans
        (Req_trans (Rmul_left_comm3 (Rmul a b) a b)
          (Req_trans (Rmul_congr (Req_refl a) (Rmul_assoc a b b))
            (Req_symm (Rmul_assoc a a (Rmul b b)))))
        (Req_symm (Rmul_left_comm3 b (Rmul a a) b)))
  have hx3 : Req (Rmul a (Rmul (Rmul b b) b)) (Rmul b (Rmul (Rmul a b) b)) :=
    Req_trans (Rmul_left_comm3 a (Rmul b b) b)
      (Req_trans (Rmul_comm (Rmul b b) (Rmul a b)) (Req_symm (Rmul_left_comm3 b (Rmul a b) b)))
  refine Req_trans (Rsub_congr
    (Radd_congr (Radd_congr (Radd_congr (Req_refl _) hx1) hx2) hx3) (Req_refl _)) ?_
  -- telescope: (((P+M₁)+M₂)+M₃) − (((M₁+M₂)+M₃)+Q) ≈ P − Q
  have hcancel : ∀ P S Q : Real, Req (Rsub (Radd P S) (Radd S Q)) (Rsub P Q) := by
    intro P S Q
    refine Req_trans (Radd_congr (Req_refl (Radd P S)) (Rneg_Radd S Q)) ?_
    refine Req_trans (Radd_assoc P S (Radd (Rneg S) (Rneg Q))) ?_
    refine Req_trans (Radd_congr (Req_refl P) (Req_symm (Radd_assoc S (Rneg S) (Rneg Q)))) ?_
    refine Req_trans (Radd_congr (Req_refl P) (Radd_congr (Radd_neg S) (Req_refl (Rneg Q)))) ?_
    exact Radd_congr (Req_refl P)
      (Req_trans (Radd_comm zero (Rneg Q)) (Radd_zero (Rneg Q)))
  have htel3 : ∀ P M₁ M₂ M₃ Q : Real,
      Req (Rsub (Radd (Radd (Radd P M₁) M₂) M₃) (Radd (Radd (Radd M₁ M₂) M₃) Q)) (Rsub P Q) := by
    intro P M₁ M₂ M₃ Q
    refine Req_trans (Rsub_congr ?_ (Req_refl _)) (hcancel P (Radd (Radd M₁ M₂) M₃) Q)
    refine Req_trans (Radd_assoc (Radd P M₁) M₂ M₃) ?_
    refine Req_trans (Radd_assoc P M₁ (Radd M₂ M₃)) ?_
    exact Radd_congr (Req_refl P) (Req_symm (Radd_assoc M₁ M₂ M₃))
  refine Req_trans (htel3 (Rmul a (Rmul (Rmul a a) a)) (Rmul b (Rmul (Rmul a a) a))
    (Rmul b (Rmul (Rmul a a) b)) (Rmul b (Rmul (Rmul a b) b)) (Rmul b (Rmul (Rmul b b) b))) ?_
  exact Rsub_congr (Rmul_comm a (Rmul (Rmul a a) a)) (Rmul_comm b (Rmul (Rmul b b) b))

end UOR.Bridge.F1Square.Analysis
