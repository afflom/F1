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

namespace UOR.Bridge.F1Square.Analysis

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

end UOR.Bridge.F1Square.Analysis
