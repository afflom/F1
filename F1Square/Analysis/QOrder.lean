/-
F1 square — ℚ as a verified ordered field (the v0.4.0 order library).

The constructive-ℝ arithmetic of `Analysis.Real` rests on ℚ being a genuine *ordered* field: the
order must be reflexive and transitive, addition must be monotone, and the absolute value must obey
the triangle inequality and respect value-equality. v0.3.0 gave ℚ its field laws (via the ring
normalizer); this brick gives ℚ its order laws, on the same exact `Q` (raw fractions with positive
denominators). These are the lemmas the real-number regularity proofs consume.

Everything is proved from the core ℤ order/`natAbs` lemmas (`Int.mul_le_mul_of_nonneg_right`,
`le_of_mul_le_mul_right`, `Int.natAbs_add_le`, `Int.natAbs_mul`, …) and the v0.3.0 ring normalizer
for the polynomial rearrangements — pure Lean 4, no Mathlib, no `sorry`. Order/equality on `Q` are
the cross-multiplication relations, which are correct precisely when denominators are positive; the
positivity hypotheses are threaded explicitly (and discharged automatically for everything the reals
construct, since every rational they build has a positive denominator).
-/

import F1Square.Analysis.Rat
import F1Square.Analysis.RingTac

namespace UOR.Bridge.F1Square.Analysis

/-- `≤` on ℚ is reflexive. -/
theorem Qle_refl (a : Q) : Qle a a := by unfold Qle; omega

/-- Value-equality implies `≤` (no positivity needed). -/
theorem Qeq_le {a b : Q} (h : Qeq a b) : Qle a b := by unfold Qeq Qle at *; omega

/-- `≤` on ℚ is transitive (needs the middle denominator positive). -/
theorem Qle_trans {a b c : Q} (hb : 0 < b.den)
    (hab : Qle a b) (hbc : Qle b c) : Qle a c := by
  have hb' : (0 : Int) < (b.den : Int) := by omega
  unfold Qle at *
  apply Int.le_of_mul_le_mul_right _ hb'
  have t1 : a.num * (b.den : Int) * (c.den : Int) ≤ b.num * (a.den : Int) * (c.den : Int) :=
    Int.mul_le_mul_of_nonneg_right hab (Int.ofNat_nonneg _)
  have t2 : b.num * (c.den : Int) * (a.den : Int) ≤ c.num * (b.den : Int) * (a.den : Int) :=
    Int.mul_le_mul_of_nonneg_right hbc (Int.ofNat_nonneg _)
  have e1 : a.num * (c.den : Int) * (b.den : Int) = a.num * (b.den : Int) * (c.den : Int) :=
    Int.mul_right_comm _ _ _
  have e2 : b.num * (a.den : Int) * (c.den : Int) = b.num * (c.den : Int) * (a.den : Int) :=
    Int.mul_right_comm _ _ _
  have e3 : c.num * (a.den : Int) * (b.den : Int) = c.num * (b.den : Int) * (a.den : Int) :=
    Int.mul_right_comm _ _ _
  omega

/-- `|·|` respects ℚ value-equality. -/
theorem Qabs_Qeq {a b : Q} (h : Qeq a b) : Qeq (Qabs a) (Qabs b) := by
  unfold Qeq Qabs at *
  have hn : (a.num * (b.den : Int)).natAbs = (b.num * (a.den : Int)).natAbs := by rw [h]
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_ofNat, Int.natAbs_ofNat] at hn
  rw [← Int.natCast_mul, ← Int.natCast_mul, hn]

/-- Transport `≤` along value-equality on the left (needs the replaced denominator positive). -/
theorem Qle_congr_left {a a' b : Q} (ha : 0 < a.den) (h : Qeq a a')
    (hab : Qle a b) : Qle a' b := by
  have ha' : (0 : Int) < (a.den : Int) := by omega
  unfold Qle Qeq at *
  apply Int.le_of_mul_le_mul_right _ ha'
  have t1 : a.num * (b.den : Int) * (a'.den : Int) ≤ b.num * (a.den : Int) * (a'.den : Int) :=
    Int.mul_le_mul_of_nonneg_right hab (Int.ofNat_nonneg _)
  have eL : a'.num * (b.den : Int) * (a.den : Int) = a.num * (b.den : Int) * (a'.den : Int) := by
    rw [Int.mul_right_comm a'.num, ← h, Int.mul_right_comm a.num]
  have eR : b.num * (a'.den : Int) * (a.den : Int) = b.num * (a.den : Int) * (a'.den : Int) :=
    Int.mul_right_comm _ _ _
  omega

/-- Transport `≤` along value-equality on the right (needs the replaced denominator positive). -/
theorem Qle_congr_right {a b b' : Q} (hb : 0 < b.den) (h : Qeq b b')
    (hab : Qle a b) : Qle a b' := by
  have hb' : (0 : Int) < (b.den : Int) := by omega
  unfold Qle Qeq at *
  apply Int.le_of_mul_le_mul_right _ hb'
  have t1 : a.num * (b.den : Int) * (b'.den : Int) ≤ b.num * (a.den : Int) * (b'.den : Int) :=
    Int.mul_le_mul_of_nonneg_right hab (Int.ofNat_nonneg _)
  have eL : a.num * (b'.den : Int) * (b.den : Int) = a.num * (b.den : Int) * (b'.den : Int) :=
    Int.mul_right_comm _ _ _
  have eR : b'.num * (a.den : Int) * (b.den : Int) = b.num * (a.den : Int) * (b'.den : Int) := by
    rw [Int.mul_right_comm b'.num, ← h, Int.mul_right_comm b.num]
  omega

-- The pure-ℤ kernel of additive monotonicity (rearrangements via the v0.3.0 ring normalizer).
private theorem add_mono_core (an bn cn dn ad bd cd dd : Int)
    (h1 : an * bd ≤ bn * ad) (h2 : cn * dd ≤ dn * cd)
    (had : 0 ≤ ad) (hbd : 0 ≤ bd) (hcd : 0 ≤ cd) (hdd : 0 ≤ dd) :
    (an * cd + cn * ad) * (bd * dd) ≤ (bn * dd + dn * bd) * (ad * cd) := by
  have t1 : (an * bd) * (cd * dd) ≤ (bn * ad) * (cd * dd) :=
    Int.mul_le_mul_of_nonneg_right h1 (Int.mul_nonneg hcd hdd)
  have t2 : (cn * dd) * (ad * bd) ≤ (dn * cd) * (ad * bd) :=
    Int.mul_le_mul_of_nonneg_right h2 (Int.mul_nonneg had hbd)
  have eL : (an * cd + cn * ad) * (bd * dd) = (an * bd) * (cd * dd) + (cn * dd) * (ad * bd) := by
    have h := RingNF.nf_eq (ρ := RingNF.env [an, bn, cn, dn, ad, bd, cd, dd])
      (a := .mul (.add (.mul (.var 0) (.var 6)) (.mul (.var 2) (.var 4))) (.mul (.var 5) (.var 7)))
      (b := .add (.mul (.mul (.var 0) (.var 5)) (.mul (.var 6) (.var 7)))
            (.mul (.mul (.var 2) (.var 7)) (.mul (.var 4) (.var 5))))
      (by decide)
    simpa [RingNF.denote, RingNF.env] using h
  have eR : (bn * dd + dn * bd) * (ad * cd) = (bn * ad) * (cd * dd) + (dn * cd) * (ad * bd) := by
    have h := RingNF.nf_eq (ρ := RingNF.env [an, bn, cn, dn, ad, bd, cd, dd])
      (a := .mul (.add (.mul (.var 1) (.var 7)) (.mul (.var 3) (.var 5))) (.mul (.var 4) (.var 6)))
      (b := .add (.mul (.mul (.var 1) (.var 4)) (.mul (.var 6) (.var 7)))
            (.mul (.mul (.var 3) (.var 6)) (.mul (.var 4) (.var 5))))
      (by decide)
    simpa [RingNF.denote, RingNF.env] using h
  rw [eL, eR]; exact Int.add_le_add t1 t2

/-- Addition on ℚ is monotone: `a ≤ b → c ≤ d → a + c ≤ b + d`. -/
theorem Qadd_le_add {a b c d : Q} (hab : Qle a b) (hcd : Qle c d) :
    Qle (add a c) (add b d) := by
  unfold Qle add at *
  simp only [Int.natCast_mul]
  exact add_mono_core a.num b.num c.num d.num a.den b.den c.den d.den
    hab hcd (Int.ofNat_nonneg _) (Int.ofNat_nonneg _) (Int.ofNat_nonneg _) (Int.ofNat_nonneg _)

/-- The triangle inequality for sums on ℚ: `|a + b| ≤ |a| + |b|`. -/
theorem Qabs_add_le (a b : Q) : Qle (Qabs (add a b)) (add (Qabs a) (Qabs b)) := by
  unfold Qle Qabs add
  simp only [Int.natCast_mul]
  -- both sides share denominator ↑a.den * ↑b.den; reduce to the numerator inequality
  have key : ((a.num * (b.den : Int) + b.num * (a.den : Int)).natAbs : Int)
      ≤ ((a.num.natAbs : Int) * (b.den : Int) + (b.num.natAbs : Int) * (a.den : Int)) := by
    have e1 : (a.num.natAbs : Int) * (b.den : Int) = ((a.num * (b.den : Int)).natAbs : Int) := by
      rw [Int.natAbs_mul, Int.natAbs_ofNat, Int.natCast_mul]
    have e2 : (b.num.natAbs : Int) * (a.den : Int) = ((b.num * (a.den : Int)).natAbs : Int) := by
      rw [Int.natAbs_mul, Int.natAbs_ofNat, Int.natCast_mul]
    rw [e1, e2]
    have := Int.natAbs_add_le (a.num * (b.den : Int)) (b.num * (a.den : Int))
    omega
  have hD : (0 : Int) ≤ (a.den : Int) * (b.den : Int) :=
    Int.mul_nonneg (Int.ofNat_nonneg _) (Int.ofNat_nonneg _)
  exact Int.mul_le_mul_of_nonneg_right key hD

/-- The telescoping triangle inequality on ℚ: `|(a+b) − (c+d)| ≤ |a−c| + |b−d|`. This is exactly the
    bound the constructive-ℝ addition needs (split a difference of sums coordinatewise). -/
theorem Qabs_sub_add4 {a b c d : Q} (ha : 0 < a.den) (hb : 0 < b.den)
    (hc : 0 < c.den) (hd : 0 < d.den) :
    Qle (Qabs (Qsub (add a b) (add c d))) (add (Qabs (Qsub a c)) (Qabs (Qsub b d))) := by
  have htel : Qeq (Qsub (add a b) (add c d)) (add (Qsub a c) (Qsub b d)) := by
    simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
  have h2 := Qabs_add_le (Qsub a c) (Qsub b d)
  have hpos : 0 < (Qabs (add (Qsub a c) (Qsub b d))).den :=
    Qabs_den_pos (add_den_pos (Qsub_den_pos ha hc) (Qsub_den_pos hb hd))
  exact Qle_congr_left hpos (Qeq_symm (Qabs_Qeq htel)) h2

end UOR.Bridge.F1Square.Analysis
