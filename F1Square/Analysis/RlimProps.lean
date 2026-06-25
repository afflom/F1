/-
F1 square — reusable limit-congruence infrastructure for Bishop's `Rlim`.

Two structural facts about the diagonal limit `(lim X)ₙ = (X(4n+3))_{4n+3}`:
* `Rlim_congr` — pointwise-`≈` regular sequences have `≈` limits (from `Req` at the diagonal index,
  since `2/(4n+4) ≤ 2/(n+1)`);
* `Rlim_neg` — the limit of the negated sequence is the negated limit (seq-equal, hence definitional).

These are the limit-level congruences any property/convergence argument over `Rlim`-built objects needs
(e.g. the complex digamma `CDigamma`'s symmetries, and the eventual `CSpougeGamma → Γ` convergence).

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/
import F1Square.Analysis.Complete
import F1Square.Analysis.RealDiv

namespace UOR.Bridge.F1Square.Analysis

/-- **`Rinv` respects `≈`** (even across different positivity witnesses): `x ≈ y ⟹ 1/x ≈ 1/y`. No
    witness-dependent reindexing is needed — the cancellation `1/x ≈ (1/x)·(y·(1/y)) ≈ (1/x)·(x·(1/y))
    ≈ ((1/x)·x)·(1/y) ≈ 1·(1/y) ≈ 1/y` routes through `Rmul_Rinv_self` on both sides. -/
theorem Rinv_congr {x y : Real} {kx ky : Nat} (hkx : Qlt (Qbound kx) (x.seq kx))
    (hky : Qlt (Qbound ky) (y.seq ky)) (h : Req x y) :
    Req (Rinv x kx hkx) (Rinv y ky hky) := by
  have h1 : Req (Rinv x kx hkx) (Rmul (Rinv x kx hkx) (Rmul y (Rinv y ky hky))) :=
    Req_trans (Req_symm (Rmul_one (Rinv x kx hkx)))
      (Rmul_congr (Req_refl _) (Req_symm (Rmul_Rinv_self hky)))
  have h2 : Req (Rmul (Rinv x kx hkx) (Rmul y (Rinv y ky hky)))
      (Rmul (Rinv x kx hkx) (Rmul x (Rinv y ky hky))) :=
    Rmul_congr (Req_refl _) (Rmul_congr (Req_symm h) (Req_refl _))
  have h3 : Req (Rmul (Rinv x kx hkx) (Rmul x (Rinv y ky hky))) (Rinv y ky hky) :=
    Req_trans (Req_symm (Rmul_assoc _ _ _))
      (Req_trans (Rmul_congr (Req_trans (Rmul_comm _ _) (Rmul_Rinv_self hkx)) (Req_refl _))
        (Req_trans (Rmul_comm one _) (Rmul_one _)))
  exact Req_trans h1 (Req_trans h2 h3)

/-- **`Rlim` respects pointwise `≈`**: if `X j ≈ Y j` for every `j`, then `lim X ≈ lim Y`. At index `n`
    both limits read their diagonal entry at `4n+3`; the hypothesis at `(4n+3, 4n+3)` bounds the gap by
    `2/(4n+4) ≤ 2/(n+1)`. -/
theorem Rlim_congr (X Y : Nat → Real) (hX : RReg X) (hY : RReg Y) (h : ∀ j, Req (X j) (Y j)) :
    Req (Rlim X hX) (Rlim Y hY) := by
  intro n
  rw [Rlim_seq, Rlim_seq]
  have hb := h (4 * n + 3) (4 * n + 3)
  have hstep : Qle (⟨2, (4 * n + 3) + 1⟩ : Q) (⟨2, n + 1⟩ : Q) := by
    show (2 : Int) * ((n + 1 : Nat) : Int) ≤ (2 : Int) * (((4 * n + 3) + 1 : Nat) : Int)
    push_cast; omega
  exact Qle_trans (Nat.succ_pos _) hb hstep

/-- **`Rlim` commutes with negation**: `lim (−X) ≈ −(lim X)`. Both sides have the identical diagonal
    `seq` `neg (X(4n+3))_{4n+3}`, so this is definitional. -/
theorem Rlim_neg (X : Nat → Real) (hX : RReg X) (hNX : RReg (fun j => Rneg (X j))) :
    Req (Rlim (fun j => Rneg (X j)) hNX) (Rneg (Rlim X hX)) :=
  Req_of_seq_Qeq (fun _ => Qeq_refl _)

/-- **A pointwise-`0` regular sequence has limit `0`**: `(∀ j, X j ≈ 0) ⟹ lim X ≈ 0` (the `≈ 0`
    specialization of `Rlim_congr`). -/
theorem Rlim_zero (X : Nat → Real) (hX : RReg X) (hz : ∀ j, Req (X j) zero) :
    Req (Rlim X hX) zero := by
  intro n
  rw [Rlim_seq]
  have hstep : Qle (⟨2, (4 * n + 3) + 1⟩ : Q) (⟨2, n + 1⟩ : Q) := by
    show (2 : Int) * ((n + 1 : Nat) : Int) ≤ (2 : Int) * (((4 * n + 3) + 1 : Nat) : Int)
    push_cast; omega
  exact Qle_trans (Nat.succ_pos _) (hz (4 * n + 3) (4 * n + 3)) hstep

set_option maxHeartbeats 1000000 in
/-- **Limit additivity** `lim (X + Y) ≈ lim X + lim Y` — linearity of the Bishop limit under `Radd`.
    The forced gateway to complex limit/series linearity (`Clim_add`/`Cseries_add`), and the piece
    flagged missing in the convergence layer.

    Both diagonals land at the SAME sequence position `8n+7`: `lim(X+Y)` puts the `X`-component at
    `(X (4n+3))_{8n+7}` (the `Radd` index inflation `2·(4n+3)+1 = 8n+7`), while `(lim X)_{2n+1} =
    (X (4(2n+1)+3))_{4(2n+1)+3} = (X (8n+7))_{8n+7}`. So the gap is pure META-regularity — `(X (4n+3))`
    vs `(X (8n+7))` at one position — bounded by `RReg`, giving `5/(8(n+1))` per component and
    `≤ 2/(n+1)` total. No rate doubling (we use `Req_of_lin_bound`, which absorbs the constant). -/
theorem Rlim_add (X Y : Nat → Real) (hX : RReg X) (hY : RReg Y)
    (hXY : RReg (fun j => Radd (X j) (Y j))) :
    Req (Rlim (fun j => Radd (X j) (Y j)) hXY) (Radd (Rlim X hX) (Rlim Y hY)) := by
  refine Req_of_lin_bound (C := 2) (fun n => ?_)
  -- Align the RHS diagonal index `4·(2n+1)+3` to the LHS `Radd` index `2·(4n+3)+1` (both `= 8n+7`).
  have hpe : 4 * (2 * n + 1) + 3 = 2 * (4 * n + 3) + 1 := by omega
  show Qle (Qabs (Qsub
      (add ((X (4 * n + 3)).seq (2 * (4 * n + 3) + 1))
           ((Y (4 * n + 3)).seq (2 * (4 * n + 3) + 1)))
      (add ((X (4 * (2 * n + 1) + 3)).seq (4 * (2 * n + 1) + 3))
           ((Y (4 * (2 * n + 1) + 3)).seq (4 * (2 * n + 1) + 3)))))
    (⟨2, n + 1⟩ : Q)
  rw [hpe]
  -- abbreviations (P := 8n+7); the four diagonal samples
  have ha : (0 : Nat) < ((X (4 * n + 3)).seq (2 * (4 * n + 3) + 1)).den := (X (4 * n + 3)).den_pos _
  have hb : (0 : Nat) < ((Y (4 * n + 3)).seq (2 * (4 * n + 3) + 1)).den := (Y (4 * n + 3)).den_pos _
  have hc : (0 : Nat) < ((X (2 * (4 * n + 3) + 1)).seq (2 * (4 * n + 3) + 1)).den :=
    (X (2 * (4 * n + 3) + 1)).den_pos _
  have hd : (0 : Nat) < ((Y (2 * (4 * n + 3) + 1)).seq (2 * (4 * n + 3) + 1)).den :=
    (Y (2 * (4 * n + 3) + 1)).den_pos _
  -- regroup the difference of sums into a sum of component differences
  have hregroup : Qeq
      (Qsub (add ((X (4 * n + 3)).seq (2 * (4 * n + 3) + 1))
                 ((Y (4 * n + 3)).seq (2 * (4 * n + 3) + 1)))
            (add ((X (2 * (4 * n + 3) + 1)).seq (2 * (4 * n + 3) + 1))
                 ((Y (2 * (4 * n + 3) + 1)).seq (2 * (4 * n + 3) + 1))))
      (add (Qsub ((X (4 * n + 3)).seq (2 * (4 * n + 3) + 1))
                 ((X (2 * (4 * n + 3) + 1)).seq (2 * (4 * n + 3) + 1)))
           (Qsub ((Y (4 * n + 3)).seq (2 * (4 * n + 3) + 1))
                 ((Y (2 * (4 * n + 3) + 1)).seq (2 * (4 * n + 3) + 1)))) := by
    simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
  -- the two component RReg bounds
  have hXbd := hX (4 * n + 3) (2 * (4 * n + 3) + 1) (2 * (4 * n + 3) + 1)
  have hYbd := hY (4 * n + 3) (2 * (4 * n + 3) + 1) (2 * (4 * n + 3) + 1)
  -- the combined bound `B + B ≤ 2/(n+1)` (each `B = 5/(8n+8)`)
  have hfin : Qle (add (add (add (⟨1, (4 * n + 3) + 1⟩ : Q) ⟨1, (2 * (4 * n + 3) + 1) + 1⟩)
                            ⟨2, (2 * (4 * n + 3) + 1) + 1⟩)
                       (add (add (⟨1, (4 * n + 3) + 1⟩ : Q) ⟨1, (2 * (4 * n + 3) + 1) + 1⟩)
                            ⟨2, (2 * (4 * n + 3) + 1) + 1⟩))
      (⟨2, n + 1⟩ : Q) := by
    have heq : Qeq (add (add (add (⟨1, (4 * n + 3) + 1⟩ : Q) ⟨1, (2 * (4 * n + 3) + 1) + 1⟩)
                            ⟨2, (2 * (4 * n + 3) + 1) + 1⟩)
                       (add (add (⟨1, (4 * n + 3) + 1⟩ : Q) ⟨1, (2 * (4 * n + 3) + 1) + 1⟩)
                            ⟨2, (2 * (4 * n + 3) + 1) + 1⟩))
        (⟨10, 8 * n + 8⟩ : Q) := by
      simp only [Qeq, add]; push_cast; ring_uor
    refine Qle_trans (Nat.succ_pos _) (Qeq_le heq) ?_
    show (10 : Int) * ((n + 1 : Nat) : Int) ≤ (2 : Int) * ((8 * n + 8 : Nat) : Int)
    push_cast; omega
  -- assemble: |Σ-diff| = |Σ comp-diffs| ≤ |dX| + |dY| ≤ B + B ≤ 2/(n+1)
  refine Qle_trans (Qabs_den_pos (add_den_pos (Qsub_den_pos ha hc) (Qsub_den_pos hb hd)))
    (Qeq_le (Qabs_Qeq hregroup)) ?_
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos ha hc))
      (Qabs_den_pos (Qsub_den_pos hb hd)))
    (Qabs_add_le _ _) ?_
  exact Qle_trans
    (add_den_pos
      (add_den_pos (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _))
      (add_den_pos (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _)))
    (Qadd_le_add hXbd hYbd) hfin

end UOR.Bridge.F1Square.Analysis
