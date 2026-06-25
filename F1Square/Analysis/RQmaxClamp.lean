/-
F1 square — Track 1, item 6: **the per-index clamp `qClampOne`** (`RQmaxClamp.lean`).

The integral layer needs a total `f : Real → Real`, and every `[1,B]` Lipschitz theorem (`RrpowAbsLipNat`,
`LogDiffBoundGen`, …) consumes the **per-index** envelope `∀n, 1 ≤ x.seq n`. The real-abs clamp
`clampOne t = max(t,1)` gives only *real* `≥ 1` (its sequence dips to `1 − Qbound`). The fix is a per-index
rational max: `qClampOne x` with `seq n := Qmax (x.seq n) 1`, which is `≥ 1` **by construction** at every
index.

`Qmax` is `1`-Lipschitz at the `Q` level (`Qmax_const_lip`, a clean 2-case argument via `Qabs_le_of_both`
+ `Qsub_le_2` + `Qmax_ge_*` — no `omega` cross-multiplication), so `qClampOne` is regular. Per-index it is
`≥ 1` (`qClampOne_ge1`), positive (`qClampOne_pos`), and `≤ B` for `B ≥ 1` (`qClampOne_le`) — exactly the
envelope `RrpowPos_abs_lipschitz_natB` wants.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.QOrder
import F1Square.Analysis.ROrder
import F1Square.Analysis.Real

namespace UOR.Bridge.F1Square.Analysis

/-- `a ≤ b ⟹ −b ≤ −a`. -/
private theorem Qneg_le_neg' {a b : Q} (h : Qle a b) : Qle (neg b) (neg a) := by
  unfold Qle neg at *; simp only [Int.neg_mul]; omega

/-- `|a − b| = |b − a|` (proved structurally to keep this file a leaf). -/
private theorem Qabs_Qsub_comm' (a b : Q) : Qabs (Qsub a b) = Qabs (Qsub b a) := by
  unfold Qabs Qsub add neg
  congr 1
  · congr 1
    rw [show a.num * (b.den : Int) + -b.num * (a.den : Int)
          = -(b.num * (a.den : Int) + -a.num * (b.den : Int)) from by ring_uor, Int.natAbs_neg]
  · exact Nat.mul_comm a.den b.den

/-- Subtraction is monotone: `a ≤ a'`, `b' ≤ b ⟹ a − b ≤ a' − b'`. -/
private theorem Qsub_le_2' {a a' b b' : Q} (ha : Qle a a') (hb : Qle b' b) :
    Qle (Qsub a b) (Qsub a' b') := Qadd_le_add ha (Qneg_le_neg' hb)

/-- Rational max via decidable `Qle`. -/
def Qmax (a b : Q) : Q := if Qle a b then b else a

theorem Qmax_eq_right {a b : Q} (h : Qle a b) : Qmax a b = b := if_pos h
theorem Qmax_eq_left {a b : Q} (h : ¬ Qle a b) : Qmax a b = a := if_neg h

theorem Qmax_den_pos {a b : Q} (ha : 0 < a.den) (hb : 0 < b.den) : 0 < (Qmax a b).den := by
  by_cases h : Qle a b
  · rw [Qmax_eq_right h]; exact hb
  · rw [Qmax_eq_left h]; exact ha

/-- `a ≤ max a b`. -/
theorem Qmax_ge_left (a b : Q) : Qle a (Qmax a b) := by
  by_cases h : Qle a b
  · rw [Qmax_eq_right h]; exact h
  · rw [Qmax_eq_left h]; exact Qle_refl a

/-- `b ≤ max a b`. -/
theorem Qmax_ge_right (a b : Q) : Qle b (Qmax a b) := by
  by_cases h : Qle a b
  · rw [Qmax_eq_right h]; exact Qle_refl b
  · rw [Qmax_eq_left h]
    rcases Qle_or_Qlt a b with h' | h'
    · exact absurd h' h
    · exact (by unfold Qle Qlt at *; omega : Qle b a)

/-- `max a b ≤ c` from `a ≤ c`, `b ≤ c`. -/
theorem Qmax_le {a b c : Q} (ha : Qle a c) (hb : Qle b c) : Qle (Qmax a b) c := by
  by_cases h : Qle a b
  · rw [Qmax_eq_right h]; exact hb
  · rw [Qmax_eq_left h]; exact ha

/-- `c − c ≤ |y|` for any `y` (the zero difference is below any absolute value). -/
theorem Qsub_self_le_Qabs (c y : Q) : Qle (Qsub c c) (Qabs y) := by
  show (Qsub c c).num * ((Qabs y).den : Int) ≤ (Qabs y).num * ((Qsub c c).den : Int)
  have h0 : (Qsub c c).num = 0 := by simp only [Qsub, add, neg]; ring_uor
  rw [h0]
  have h := Int.mul_nonneg (Qabs_num_nonneg y) (Int.ofNat_nonneg (Qsub c c).den)
  simpa using h

/-- The asymmetric Lipschitz step `max a c − max b c ≤ |a − b|` — 2 cases on `a ≤ c`. -/
private theorem qmax_lem (a b c : Q) (had : 0 < a.den) (hbd : 0 < b.den) (hcd : 0 < c.den) :
    Qle (Qsub (Qmax a c) (Qmax b c)) (Qabs (Qsub a b)) := by
  by_cases h : Qle a c
  · rw [Qmax_eq_right h]
    exact Qle_trans (Qsub_den_pos hcd hcd) (Qsub_le_2' (Qle_refl c) (Qmax_ge_right b c))
      (Qsub_self_le_Qabs c (Qsub a b))
  · rw [Qmax_eq_left h]
    exact Qle_trans (Qsub_den_pos had hbd) (Qsub_le_2' (Qle_refl a) (Qmax_ge_left b c))
      (Qle_self_Qabs (Qsub a b))

/-- **`Qmax` is `1`-Lipschitz in the first argument**: `|max a c − max b c| ≤ |a − b|`. -/
theorem Qmax_const_lip (a b c : Q) (had : 0 < a.den) (hbd : 0 < b.den) (hcd : 0 < c.den) :
    Qle (Qabs (Qsub (Qmax a c) (Qmax b c))) (Qabs (Qsub a b)) := by
  refine Qabs_le_of_both (qmax_lem a b c had hbd hcd) ?_
  have key : Qle (Qsub (Qmax b c) (Qmax a c)) (Qabs (Qsub a b)) := by
    rw [Qabs_Qsub_comm' a b]; exact qmax_lem b a c hbd had hcd
  refine Qle_congr_left (Qsub_den_pos (Qmax_den_pos hbd hcd) (Qmax_den_pos had hcd)) ?_ key
  show (Qsub (Qmax b c) (Qmax a c)).num * ((neg (Qsub (Qmax a c) (Qmax b c))).den : Int)
      = (neg (Qsub (Qmax a c) (Qmax b c))).num * ((Qsub (Qmax b c) (Qmax a c)).den : Int)
  simp only [Qsub, add, neg]; push_cast; ring_uor

/-- **The per-index clamp** `qClampOne x = max(x, 1)` — total, regular, per-index `≥ 1` by construction. -/
def qClampOne (x : Real) : Real where
  seq := fun n => Qmax (x.seq n) (⟨1, 1⟩ : Q)
  reg := by
    intro m n
    exact Qle_trans
      (Qabs_den_pos (Qsub_den_pos (x.den_pos m) (x.den_pos n)))
      (Qmax_const_lip (x.seq m) (x.seq n) (⟨1, 1⟩ : Q) (x.den_pos m) (x.den_pos n) Nat.one_pos)
      (x.reg m n)
  den_pos := fun n => Qmax_den_pos (x.den_pos n) Nat.one_pos

/-- `qClampOne x ≥ 1` per index — by construction (`Qmax_ge_right`). -/
theorem qClampOne_ge1 (x : Real) (n : Nat) : Qle (⟨1, 1⟩ : Q) ((qClampOne x).seq n) :=
  Qmax_ge_right (x.seq n) (⟨1, 1⟩ : Q)

/-- `qClampOne x` is positive per index. -/
theorem qClampOne_pos (x : Real) (n : Nat) : 0 < ((qClampOne x).seq n).num := by
  have h := qClampOne_ge1 x n
  have hd := (qClampOne x).den_pos n
  simp only [Qle] at h; push_cast at h; omega

/-- `qClampOne x ≤ B` per index, from `x ≤ B` and `B ≥ 1`. -/
theorem qClampOne_le {x : Real} {B : Q} (hB1 : Qle (⟨1, 1⟩ : Q) B) (hxB : ∀ n, Qle (x.seq n) B)
    (n : Nat) : Qle ((qClampOne x).seq n) B :=
  Qmax_le (hxB n) hB1

end UOR.Bridge.F1Square.Analysis
