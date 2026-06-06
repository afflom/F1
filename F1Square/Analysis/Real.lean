/-
F1 square — the second analysis brick: constructive ℝ as Bishop regular sequences over our exact ℚ
(the v0.3.0 continuation of the analysis roadmap).

Per the standing directive, the analytic substrate is built from first principles the UOR way. Brick
one was exact ℚ (`Analysis.Rat`); this is brick two: the real numbers as **regular sequences of
rationals** (Bishop), the constructive encoding that bakes the modulus of convergence into the data
so no choice principle is needed:

  a sequence `x : ℕ → ℚ` is *regular* iff `|xₘ − xₙ| ≤ 1/(m+1) + 1/(n+1)` for all `m, n`.

The index *is* the modulus. A real number is a regular sequence; equality is the (undecidable, but
Prop-valued) Bishop relation `x ≈ y  ⟺  |xₙ − yₙ| ≤ 2/(n+1) ∀ n`; positivity is the witnessed
`∃ n, xₙ > 1/(n+1)`. This is the standard no-Mathlib encoding (cf. Bishop–Bridges; the Agda
constructive-analysis development arXiv:2205.08354).

Scope (v0.4.0 — ℝ as an ordered additive group): on top of the v0.3.0 type/setoid, this release adds
**ℝ arithmetic with full regularity proofs** — negation `Rneg` and the (reindexed) Bishop addition
`Radd` — built on the new ℚ ordered-field library (`Analysis.QOrder`) and the from-scratch `ring_uor`
tactic. The `Real` structure now also carries `den_pos` (every term has a positive denominator), which
the order arguments need. Multiplication, `≈`-transitivity (a genuine limiting/Archimedean argument),
ℂ = ℝ×ℝ, and the transcendentals are the v0.5.0 continuation. None of this is the crux: making ζ/λₙ
exact-bounded objects is statable here; proving `λₙ ≥ 0 ∀n` is RH.

Pure Lean 4, no Mathlib, no `sorry`.
-/

import F1Square.Analysis.QOrder

namespace UOR.Bridge.F1Square.Analysis

/-- Strict order on ℚ: `a < b ⟺ a·d_b < b·d_a`. -/
def Qlt (a b : Q) : Prop := a.num * (b.den : Int) < b.num * (a.den : Int)

instance (a b : Q) : Decidable (Qlt a b) := by unfold Qlt; infer_instance

/-- The modulus rational `1/(n+1) > 0` — both the regularity bound and the positivity threshold. -/
def Qbound (n : Nat) : Q := ⟨1, n + 1⟩

/-- The modulus rational has a positive denominator. -/
theorem Qbound_den_pos (k : Nat) : 0 < (Qbound k).den := Nat.succ_pos k

/-- The numerator of `a − a` is `0` (exact cancellation; via the additive structure). -/
theorem Qsub_self_num (a : Q) : (Qsub a a).num = 0 := by
  simp only [Qsub, add, neg]; rw [Int.neg_mul]; omega

/-- `b − a` has the negated numerator of `a − b`. -/
theorem Qsub_swap_num (a b : Q) : (Qsub b a).num = -(Qsub a b).num := by
  simp only [Qsub, add, neg]; rw [Int.neg_mul, Int.neg_mul]; omega

/-- `b − a` and `a − b` share a denominator (it is `dₐ·d_b` either way). -/
theorem Qsub_swap_den (a b : Q) : (Qsub b a).den = (Qsub a b).den := by
  simp only [Qsub, add, neg]; exact Nat.mul_comm b.den a.den

/-- **Regularity** (Bishop): `|xₘ − xₙ| ≤ 1/(m+1) + 1/(n+1)` for all `m, n`. -/
def IsRegular (x : Nat → Q) : Prop :=
  ∀ m n : Nat, Qle (Qabs (Qsub (x m) (x n))) (add (Qbound m) (Qbound n))

/-- A **constructive real number**: a regular sequence of rationals, every term with a positive
    denominator (so the ℚ order/equality cross-multiplications behave). -/
structure Real where
  seq : Nat → Q
  reg : IsRegular seq
  den_pos : ∀ n, 0 < (seq n).den

/-- The constant sequence at `q` is regular (its gaps are `0 ≤` a positive bound). -/
theorem const_regular (q : Q) : IsRegular (fun _ => q) := by
  intro m n
  unfold Qle Qabs
  rw [Qsub_self_num]
  simp only [Int.natAbs_zero, Int.ofNat_zero, Int.zero_mul]
  -- 0 ≤ (1/(m+1) + 1/(n+1)).num · (denominator)
  have hden : (0 : Int) ≤ ((Qsub q q).den : Int) := Int.ofNat_nonneg _
  have hnum : (0 : Int) ≤ (add (Qbound m) (Qbound n)).num := by
    simp only [add, Qbound]; omega
  exact Int.mul_nonneg hnum hden

/-- The canonical embedding ℚ ↪ ℝ as the constant sequence (needs a positive denominator). -/
def ofQ (q : Q) (hq : 0 < q.den) : Real := ⟨fun _ => q, const_regular q, fun _ => hq⟩

/-- Zero and one in ℝ. -/
def zero : Real := ofQ ⟨0, 1⟩ (by decide)
def one : Real := ofQ ⟨1, 1⟩ (by decide)

/-- **Bishop equality** on ℝ: `x ≈ y ⟺ |xₙ − yₙ| ≤ 2/(n+1)` for all `n`. -/
def Req (x y : Real) : Prop :=
  ∀ n : Nat, Qle (Qabs (Qsub (x.seq n) (y.seq n))) ⟨2, n + 1⟩

/-- `≈` is reflexive. -/
theorem Req_refl (x : Real) : Req x x := by
  intro n
  unfold Qle Qabs
  rw [Qsub_self_num]
  simp only [Int.natAbs_zero, Int.ofNat_zero, Int.zero_mul]
  have hden : (0 : Int) ≤ ((Qsub (x.seq n) (x.seq n)).den : Int) := Int.ofNat_nonneg _
  omega

/-- `≈` is symmetric (`|xₙ − yₙ| = |yₙ − xₙ|`). -/
theorem Req_symm {x y : Real} (h : Req x y) : Req y x := by
  intro n
  have hnum := Qsub_swap_num (x.seq n) (y.seq n)
  have hden := Qsub_swap_den (x.seq n) (y.seq n)
  have hx := h n
  unfold Qle Qabs at hx ⊢
  rw [hnum, Int.natAbs_neg, hden]
  exact hx

/-- The embedding respects ℚ value-equality: `q = r` (as rationals) ⟹ `ofQ q ≈ ofQ r`. -/
theorem ofQ_respects {q r : Q} (hq : 0 < q.den) (hr : 0 < r.den) (h : Qeq q r) :
    Req (ofQ q hq) (ofQ r hr) := by
  intro n
  unfold Qle Qabs ofQ
  simp only
  -- |q − r| = 0 since q = r (value), so ≤ 2/(n+1)
  have h0 : (Qsub q r).num = 0 := by
    simp only [Qsub, add, neg]; rw [Int.neg_mul]
    have := h; unfold Qeq at this; omega
  rw [h0]
  simp only [Int.natAbs_zero, Int.ofNat_zero, Int.zero_mul]
  have hden : (0 : Int) ≤ ((Qsub q r).den : Int) := Int.ofNat_nonneg _
  omega

/-- **Positivity** (Bishop): `x > 0 ⟺ ∃ n, xₙ > 1/(n+1)`. -/
def Pos (x : Real) : Prop := ∃ n : Nat, Qlt (Qbound n) (x.seq n)

/-- `1/2`, as a constructive real. -/
def half : Real := ofQ ⟨1, 2⟩ (by decide)

/-- `half` is positive — witnessed at `n = 2` (`1/3 < 1/2`). -/
theorem Pos_half : Pos half := ⟨2, by decide⟩

-- ===========================================================================
-- v0.4.0 — ℝ arithmetic with regularity proofs (ℝ as an ordered additive group).
-- ===========================================================================

/-- `|(−a) − (−b)| = |a − b|` exactly, as rationals (numerator negated, denominator preserved). -/
theorem Qabs_Qsub_neg (a b : Q) : Qabs (Qsub (neg a) (neg b)) = Qabs (Qsub a b) := by
  simp only [Qabs, Qsub, add, neg]
  congr 1
  have e : (-a.num) * (b.den : Int) + (- -b.num) * (a.den : Int)
      = -(a.num * (b.den : Int) + (-b.num) * (a.den : Int)) := by ring_uor
  rw [e, Int.natAbs_neg]

/-- **Negation** of a constructive real: `(−x)ₙ := −(xₙ)`. Regular, since negation is an isometry. -/
def Rneg (x : Real) : Real where
  seq := fun n => neg (x.seq n)
  reg := by
    intro m n
    rw [Qabs_Qsub_neg]
    exact x.reg m n
  den_pos := fun n => neg_den_pos (x.den_pos n)

/-- **Addition** of constructive reals (Bishop): `(x ⊕ y)ₙ := x₍₂ₙ₊₁₎ + y₍₂ₙ₊₁₎`. The factor-2
    reindexing is exactly what restores regularity (`2·1/(2k+2) = 1/(k+1)`). -/
def Radd (x y : Real) : Real where
  seq := fun n => add (x.seq (2 * n + 1)) (y.seq (2 * n + 1))
  reg := by
    intro m n
    have hxm := x.den_pos (2 * m + 1); have hxn := x.den_pos (2 * n + 1)
    have hym := y.den_pos (2 * m + 1); have hyn := y.den_pos (2 * n + 1)
    -- triangle: split the difference of sums coordinatewise
    have htri := Qabs_sub_add4 (a := x.seq (2 * m + 1)) (b := y.seq (2 * m + 1))
        (c := x.seq (2 * n + 1)) (d := y.seq (2 * n + 1)) hxm hym hxn hyn
    -- each coordinate ≤ its regularity bound; sum them monotonically
    have hsum := Qadd_le_add (x.reg (2 * m + 1) (2 * n + 1)) (y.reg (2 * m + 1) (2 * n + 1))
    -- the doubled bound equals 1/(m+1) + 1/(n+1)
    have hbound : Qle (add (add (Qbound (2 * m + 1)) (Qbound (2 * n + 1)))
                          (add (Qbound (2 * m + 1)) (Qbound (2 * n + 1)))) (add (Qbound m) (Qbound n)) := by
      apply Qeq_le; simp only [Qeq, add, Qbound]; push_cast; ring_uor
    have hpos1 : 0 < (add (Qabs (Qsub (x.seq (2 * m + 1)) (x.seq (2 * n + 1))))
                        (Qabs (Qsub (y.seq (2 * m + 1)) (y.seq (2 * n + 1))))).den :=
      add_den_pos (Qabs_den_pos (Qsub_den_pos hxm hxn)) (Qabs_den_pos (Qsub_den_pos hym hyn))
    have hpos2 : 0 < (add (add (Qbound (2 * m + 1)) (Qbound (2 * n + 1)))
                        (add (Qbound (2 * m + 1)) (Qbound (2 * n + 1)))).den :=
      add_den_pos (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))
        (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))
    exact Qle_trans hpos2 (Qle_trans hpos1 htri hsum) hbound
  den_pos := fun n => add_den_pos (x.den_pos (2 * n + 1)) (y.den_pos (2 * n + 1))

/-- `Rneg` is an involution on the underlying sequences (`−(−x) = x` pointwise in value). -/
theorem Rneg_Rneg_seq (x : Real) (n : Nat) : ((Rneg (Rneg x)).seq n).num = (x.seq n).num := by
  simp only [Rneg, neg]; omega

end UOR.Bridge.F1Square.Analysis
