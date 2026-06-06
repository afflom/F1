/-
F1 square — the order `≤` on constructive ℝ (the v0.11.0 foundation for the transcendentals).

Every transcendental yet to come — `exp` on ℝ, `cos`/`sin`, `log` — rests on a genuine *order* on the
reals with the expected laws (reflexive, transitive, antisymmetric up to `≈`, compatible with `≈`).
This brick supplies it, the Bishop way:

  x ≤ y  :⟺  ∀ n, xₙ ≤ yₙ + 2/(n+1).

With this pointwise form, reflexivity, antisymmetry (`x ≤ y` and `y ≤ x` ⟹ `x ≈ y`), and the bridge
from `≈` are immediate (the `2/(n+1)` slack absorbs the modulus at the *same* index). Transitivity is
the one genuine limiting step: chaining `x ≤ y ≤ z` through an auxiliary index `m` gives
`xₙ ≤ zₙ + 2/(n+1) + 6/(m+1)` for every `m`, and the **generalized Archimedean lemma** (`Qarch_gen`)
kills the `6/(m+1)` tail — exactly the argument behind `Req_trans`.

It also gives `Rnonneg` (Bishop `x ≥ 0`, `−1/(n+1) ≤ xₙ`) its canonical home (moved here from `Li`),
with `Rnonneg → Rle 0 x`.

Pure Lean 4, no Mathlib, no `sorry`.
-/

import F1Square.Analysis.Real

namespace UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- ℚ signed-bound helpers (extracting one-sided bounds, and `|·|` from two-sided).
-- ===========================================================================

/-- A rational is `≤` its own absolute value. -/
theorem Qle_self_Qabs (a : Q) : Qle a (Qabs a) := by
  show a.num * (a.den : Int) ≤ ((a.num.natAbs : Int)) * (a.den : Int)
  have hle : a.num ≤ (a.num.natAbs : Int) := by omega
  exact Int.mul_le_mul_of_nonneg_right hle (Int.ofNat_nonneg _)

/-- `|a| ≤ c` from the two one-sided bounds `a ≤ c` and `−a ≤ c`. -/
theorem Qabs_le_of_both {a c : Q} (h1 : Qle a c) (h2 : Qle (neg a) c) : Qle (Qabs a) c := by
  simp only [Qle, neg, Qabs] at h1 h2 ⊢
  have hcase : ((a.num.natAbs : Int)) = a.num ∨ ((a.num.natAbs : Int)) = -a.num := by omega
  rcases hcase with h | h <;> rw [h]
  · exact h1
  · exact h2

/-- From `|a − b| ≤ c` (positive denominators) conclude the one-sided `a ≤ b + c`. -/
theorem Qle_add_of_Qabs_sub {a b c : Q} (ha : 0 < a.den) (hb : 0 < b.den) (_hc : 0 < c.den)
    (h : Qle (Qabs (Qsub a b)) c) : Qle a (add b c) := by
  have hsubpos : 0 < (Qsub a b).den := Qsub_den_pos ha hb
  have h1 : Qle (Qsub a b) c :=
    Qle_trans (Qabs_den_pos hsubpos) (Qle_self_Qabs (Qsub a b)) h
  have h2 : Qeq a (add b (Qsub a b)) := by
    simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
  have h3 : Qle (add b (Qsub a b)) (add b c) := Qadd_le_add (Qle_refl b) h1
  exact Qle_congr_left (add_den_pos hb hsubpos) (Qeq_symm h2) h3

/-- From `a ≤ b + c` (positive denominators) conclude `a − b ≤ c`. -/
theorem Qsub_le_of_le_add {a b c : Q} (hb : 0 < b.den) (hc : 0 < c.den)
    (h : Qle a (add b c)) : Qle (Qsub a b) c := by
  have h3 := Qadd_le_add h (Qle_refl (neg b))
  have he : Qeq (add (add b c) (neg b)) c := by
    simp only [Qeq, add, neg]; push_cast; ring_uor
  exact Qle_congr_right (add_den_pos (add_den_pos hb hc) (neg_den_pos hb)) he h3

-- ===========================================================================
-- Bishop non-negativity `x ≥ 0` (canonical home; moved from `Li`).
-- ===========================================================================

/-- **Bishop non-negativity** `x ≥ 0`: every approximant is at least `−1/(n+1)`. The non-strict
    companion of `Pos` (the witnessed strict `> 0`). -/
def Rnonneg (x : Real) : Prop := ∀ n : Nat, Qle (neg (Qbound n)) (x.seq n)

/-- `0 ≥ 0`. -/
theorem Rnonneg_zero : Rnonneg zero := by
  intro n
  show Qle (neg (Qbound n)) ⟨0, 1⟩
  unfold Qle neg Qbound; push_cast; omega

/-- `1 ≥ 0`. -/
theorem Rnonneg_one : Rnonneg one := by
  intro n
  show Qle (neg (Qbound n)) ⟨1, 1⟩
  unfold Qle neg Qbound; push_cast; omega

/-- A **generic** `ℝ≥0` fact: the sum of two non-negative reals is non-negative. The Bishop addition
    reindexes to `2n+1`, where `−1/(2n+2) − 1/(2n+2) = −1/(n+1)` exactly, so the bound lands on the
    nose. -/
theorem Rnonneg_Radd {x y : Real} (hx : Rnonneg x) (hy : Rnonneg y) : Rnonneg (Radd x y) := by
  intro n
  show Qle (neg (Qbound n)) (add (x.seq (2 * n + 1)) (y.seq (2 * n + 1)))
  have hsum := Qadd_le_add (hx (2 * n + 1)) (hy (2 * n + 1))
  refine Qle_trans
    (add_den_pos (neg_den_pos (Qbound_den_pos _)) (neg_den_pos (Qbound_den_pos _))) ?_ hsum
  apply Qeq_le
  simp only [Qeq, neg, Qbound, add]; push_cast; ring_uor

-- ===========================================================================
-- The order `≤` on ℝ.
-- ===========================================================================

/-- **The order on ℝ** (Bishop): `x ≤ y ⟺ ∀ n, xₙ ≤ yₙ + 2/(n+1)`. -/
def Rle (x y : Real) : Prop := ∀ n : Nat, Qle (x.seq n) (add (y.seq n) ⟨2, n + 1⟩)

/-- `≤` is reflexive. -/
theorem Rle_refl (x : Real) : Rle x x := fun n => Qle_self_add (by show (0 : Int) ≤ 2; decide)

/-- `≈` implies `≤` (the `2/(n+1)` slack matches Bishop equality exactly). -/
theorem Rle_of_Req {x y : Real} (h : Req x y) : Rle x y :=
  fun n => Qle_add_of_Qabs_sub (x.den_pos n) (y.den_pos n) (Nat.succ_pos _) (h n)

/-- `≤` is antisymmetric up to `≈`: `x ≤ y` and `y ≤ x` give `x ≈ y`. -/
theorem Rle_antisymm {x y : Real} (hxy : Rle x y) (hyx : Rle y x) : Req x y := by
  intro n
  have h1 : Qle (Qsub (x.seq n) (y.seq n)) ⟨2, n + 1⟩ :=
    Qsub_le_of_le_add (y.den_pos n) (Nat.succ_pos _) (hxy n)
  have h2 : Qle (Qsub (y.seq n) (x.seq n)) ⟨2, n + 1⟩ :=
    Qsub_le_of_le_add (x.den_pos n) (Nat.succ_pos _) (hyx n)
  have h2' : Qle (neg (Qsub (x.seq n) (y.seq n))) ⟨2, n + 1⟩ := by
    have heq : Qeq (Qsub (y.seq n) (x.seq n)) (neg (Qsub (x.seq n) (y.seq n))) := by
      simp only [Qeq, neg, Qsub, add]; push_cast; ring_uor
    exact Qle_congr_left (Qsub_den_pos (y.den_pos n) (x.den_pos n)) heq h2
  exact Qabs_le_of_both h1 h2'

/-- `≤` is transitive — the genuine limiting step. For each `n`, `xₙ ≤ zₙ + 2/(n+1)` is shown to hold
    within `6/(m+1)` for *every* auxiliary index `m` (four steps: reg `x` at `n,m`; `x ≤ y` at `m`;
    `y ≤ z` at `m`; reg `z` at `m,n`), and `Qarch_gen` kills the `6/(m+1)` tail. -/
theorem Rle_trans {x y z : Real} (hxy : Rle x y) (hyz : Rle y z) : Rle x z := by
  intro n
  apply Qarch_gen (C := 6) (x.den_pos n) (add_den_pos (z.den_pos n) (Nat.succ_pos _))
  intro m
  have s1 : Qle (x.seq n) (add (x.seq m) (add (Qbound n) (Qbound m))) :=
    Qle_add_of_Qabs_sub (x.den_pos n) (x.den_pos m)
      (add_den_pos (Qbound_den_pos n) (Qbound_den_pos m)) (x.reg n m)
  have s4 : Qle (z.seq m) (add (z.seq n) (add (Qbound m) (Qbound n))) :=
    Qle_add_of_Qabs_sub (z.den_pos m) (z.den_pos n)
      (add_den_pos (Qbound_den_pos m) (Qbound_den_pos n)) (z.reg m n)
  have c1 : Qle (x.seq n) (add (add (y.seq m) ⟨2, m + 1⟩) (add (Qbound n) (Qbound m))) :=
    Qle_trans (add_den_pos (x.den_pos m) (add_den_pos (Qbound_den_pos n) (Qbound_den_pos m)))
      s1 (Qadd_le_add (hxy m) (Qle_refl _))
  have c2 : Qle (x.seq n)
      (add (add (add (z.seq m) ⟨2, m + 1⟩) ⟨2, m + 1⟩) (add (Qbound n) (Qbound m))) :=
    Qle_trans (add_den_pos (add_den_pos (y.den_pos m) (Nat.succ_pos _))
      (add_den_pos (Qbound_den_pos n) (Qbound_den_pos m)))
      c1 (Qadd_le_add (Qadd_le_add (hyz m) (Qle_refl _)) (Qle_refl _))
  have c3 : Qle (x.seq n)
      (add (add (add (add (z.seq n) (add (Qbound m) (Qbound n))) ⟨2, m + 1⟩) ⟨2, m + 1⟩)
        (add (Qbound n) (Qbound m))) :=
    Qle_trans (add_den_pos (add_den_pos (add_den_pos (z.den_pos m) (Nat.succ_pos _)) (Nat.succ_pos _))
      (add_den_pos (Qbound_den_pos n) (Qbound_den_pos m)))
      c2 (Qadd_le_add (Qadd_le_add (Qadd_le_add s4 (Qle_refl _)) (Qle_refl _)) (Qle_refl _))
  refine Qle_trans ?_ c3 (Qeq_le ?_)
  · exact add_den_pos (add_den_pos (add_den_pos (add_den_pos (z.den_pos n)
      (add_den_pos (Qbound_den_pos m) (Qbound_den_pos n))) (Nat.succ_pos _)) (Nat.succ_pos _))
      (add_den_pos (Qbound_den_pos n) (Qbound_den_pos m))
  · simp only [Qeq, add, Qbound, neg]; push_cast; ring_uor

/-- `x ≥ 0` (Bishop) implies `0 ≤ x` (the order). -/
theorem Rle_zero_of_Rnonneg {x : Real} (h : Rnonneg x) : Rle zero x := by
  intro n
  have hbound : Qle (Qbound n) (⟨2, n + 1⟩ : Q) := by
    show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 2 * ((n + 1 : Nat) : Int); push_cast; omega
  have hcomb := Qadd_le_add (h n) hbound
  have hz : Qeq (add (neg (Qbound n)) (Qbound n)) (⟨0, 1⟩ : Q) := by
    simp only [Qeq, add, neg, Qbound]; push_cast; ring_uor
  exact Qle_congr_left (add_den_pos (neg_den_pos (Qbound_den_pos n)) (Qbound_den_pos n)) hz hcomb

end UOR.Bridge.F1Square.Analysis
