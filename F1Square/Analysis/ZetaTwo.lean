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

/-- **`ζ(s) ≤ zetaU s N = S(N) + 1/(N+1)`** — the value is dominated by the decreasing upper sequence
    `U` (`zetaU_le`), the rigorous tail-overestimate `Σ_{k>N+1} 1/kˢ ≤ 1/(N+1)` made an explicit
    rational upper bound. The mirror of `zeta_ge_partial` (the upper bracket). -/
theorem zeta_le_partial (s : Nat) (hs : 2 ≤ s) (N : Nat) :
    Rle (zeta s hs) (ofQ (zetaU s N) (zetaU_den_pos s N)) := by
  intro n
  show Qle (zetaSum s n) (add (zetaU s N) ⟨2, n + 1⟩)
  rcases Nat.le_total n N with hnN | hNn
  · -- n ≤ N: S(n) ≤ S(N) ≤ S(N)+1/(N+1) = U(N) ≤ + 2/(n+1)
    have h1 : Qle (zetaSum s n) (zetaU s N) :=
      Qle_trans (zetaSum_den_pos s N) (zetaSum_le s hnN)
        (Qle_self_add (show (0 : Int) ≤ 1 by decide))
    exact Qle_trans (zetaU_den_pos s N) h1 (Qle_self_add (show (0 : Int) ≤ 2 by decide))
  · -- n ≥ N: S(n) ≤ S(N)+1/(N+1) = U(N) (zetadiff_bound) ≤ + 2/(n+1)
    have h1 : Qle (zetaSum s n) (zetaU s N) :=
      Qle_add_of_Qsub_le (zetaSum_den_pos s n) (zetaSum_den_pos s N) (Nat.succ_pos N)
        (zetadiff_bound s hs hNn)
    exact Qle_trans (zetaU_den_pos s N) h1 (Qle_self_add (show (0 : Int) ≤ 2 by decide))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- `zetaU 2 70 = Σ_{k=1}^{71} 1/k² + 1/71 ≤ 1645/1000` (one rational `decide`; `≈ 1.6450`). -/
theorem zetaU_two_70_le : Qle (zetaU 2 70) (⟨1646, 1000⟩ : Q) := by decide

/-- **`ζ(2) ≤ 1.646`** — the upper bracket for the Basel constant (true value `≈ 1.64493`), via the
    decreasing upper sequence `zetaU` at `N = 70`. With `zeta2_lower` this two-sided-brackets `ζ(2)`. -/
theorem zeta2_upper : Rle (zeta 2 (by decide)) (ofQ (⟨1646, 1000⟩ : Q) (by decide)) :=
  Rle_trans (zeta_le_partial 2 (by decide) 70)
    (Rle_ofQ_ofQ (zetaU_den_pos 2 70) (by decide) zetaU_two_70_le)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- `Σ_{k=1}^{71} 1/k³ ≥ 1201/1000` (`≈ 1.20206`; one rational `decide`). -/
theorem zetaSum_three_70_ge : Qle (⟨1201, 1000⟩ : Q) (zetaSum 3 70) := by decide

/-- **`ζ(3) ≥ 1.201`** — the lower bracket for Apéry's constant (true value `≈ 1.2020569`). -/
theorem zeta3_lower : Rle (ofQ (⟨1201, 1000⟩ : Q) (by decide)) (zeta 3 (by decide)) :=
  Rle_trans (Rle_ofQ_ofQ (by decide) (zetaSum_den_pos 3 70) zetaSum_three_70_ge)
    (zeta_ge_partial 3 (by decide) 70)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- `zetaU 3 70 = Σ_{k=1}^{71} 1/k³ + 1/71 ≤ 1217/1000` (one rational `decide`; `≈ 1.2161`). -/
theorem zetaU_three_70_le : Qle (zetaU 3 70) (⟨1217, 1000⟩ : Q) := by decide

/-- **`ζ(3) ≤ 1.217`** — the upper bracket for Apéry's constant, via the decreasing upper sequence
    `zetaU` at `N = 70`. With `zeta3_lower` this two-sided-brackets `ζ(3) ∈ [1.201, 1.217]` — the
    `two-sided ζ(3)` named missing for the `Pos Rlambda3` (`λ₃`) certificate. -/
theorem zeta3_upper : Rle (zeta 3 (by decide)) (ofQ (⟨1217, 1000⟩ : Q) (by decide)) :=
  Rle_trans (zeta_le_partial 3 (by decide) 70)
    (Rle_ofQ_ofQ (zetaU_den_pos 3 70) (by decide) zetaU_three_70_le)

end UOR.Bridge.F1Square.Analysis
