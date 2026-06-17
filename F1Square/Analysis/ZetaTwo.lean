/-
F1 square — the **lower bracket `ζ(2) ≥ 1.63`** (a constituent of `Pos λ₂`, v0.16.0).

`ζ(s) = Σ_{i≥1} 1/iˢ` (`Zeta.zeta`) has **non-negative** terms, so every partial sum is a lower bound:
`ζ(s) ≥ zetaSum s N` (`zeta_ge_partial`), because the omitted tail is `≥ 0` (and within `1/(n+1)` of the
approximant, by `zetaabs_bound`). At `N = 70` the rational partial sum already exceeds `1.63`
(`Σ_{k=1}^{70} 1/k² ≈ 1.6307`; one `decide`), giving `ζ(2) ≥ 163/100`. (Plain `Σ 1/k²` decides cheaply —
no `lcm`-denominator blow-up, unlike the alternating `γ`-series.)

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.Zeta
import F1Square.Analysis.RealPow
import F1Square.Analysis.GammaUpper

namespace UOR.Bridge.F1Square.Analysis

/-- **`ζ(s) ≥ zetaSum s N`** — the value dominates each partial sum (the tail is `≥ 0`). -/
theorem zeta_ge_partial (s : Nat) (hs : 2 ≤ s) (N : Nat) :
    Rle (ofQ (zetaSum s N) (zetaSum_den_pos s N)) (zeta s hs) := by
  intro n
  show Qle (zetaSum s N) (add (zetaSum s n) ⟨2, n + 1⟩)
  rcases Nat.le_total n N with hnN | hNn
  · -- n ≤ N: zetaSum s N ≤ zetaSum s n + 1/(n+1) ≤ + 2/(n+1)
    have habs := zetaabs_bound s hs hnN
    have habs' : Qle (Qabs (Qsub (zetaSum s n) (zetaSum s N))) (⟨1, n + 1⟩ : Q) := by
      rw [Qabs_Qsub_comm]; exact habs
    have hb1 : Qle (zetaSum s N) (add (zetaSum s n) ⟨1, n + 1⟩) :=
      Qabs_upper (zetaSum_den_pos s n) (zetaSum_den_pos s N) (by show 0 < n + 1; omega) habs'
    have he : Qle (add (zetaSum s n) (⟨1, n + 1⟩ : Q)) (add (zetaSum s n) ⟨2, n + 1⟩) :=
      Qadd_le_add (Qle_refl _) (by simp only [Qle]; push_cast; omega)
    exact Qle_trans (add_den_pos (zetaSum_den_pos s n) (by show 0 < n + 1; omega)) hb1 he
  · -- n ≥ N: zetaSum s N ≤ zetaSum s n ≤ + 2/(n+1)
    exact Qle_trans (zetaSum_den_pos s n) (zetaSum_le s hNn)
      (Qle_self_add (by show (0 : Int) ≤ 2; decide))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- `Σ_{k=1}^{70} 1/k² ≥ 163/100` (one rational `decide`). -/
theorem zetaSum_two_70_ge : Qle (⟨163, 100⟩ : Q) (zetaSum 2 70) := by decide

/-- **`ζ(2) ≥ 1.63`** — the lower bracket for the Basel constant. -/
theorem zeta2_lower : Rle (ofQ (⟨163, 100⟩ : Q) (by decide)) (zeta 2 (by decide)) :=
  Rle_trans (Rle_ofQ_ofQ (by decide) (zetaSum_den_pos 2 70) zetaSum_two_70_ge)
    (zeta_ge_partial 2 (by decide) 70)

end UOR.Bridge.F1Square.Analysis
