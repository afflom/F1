/-
π as a constructive real, via Machin's formula  π = 16·arctan(1/5) − 4·arctan(1/239).

This is the standard constructive *definition* of π: the Machin combination of two arctangents at
rational arguments (Arctan.lean), each with |t| ≤ 1/2 < 1 so the geometric-tail diagonal applies.
Pure Lean 4, no Mathlib, no `sorry`.

`Rpi` is the real; the rational brackets `S₁ ≤ arctanSum ≤ S₀` that pin its value (and give `Pos Rpi`,
needed for `log π`) are developed next.
-/
import F1Square.Analysis.Arctan
import F1Square.Analysis.ROrder

namespace UOR.Bridge.F1Square.Analysis

-- The nonlinear core of `Pos_of_Rle_ofQ` (explicit ℤ, so `omega` only sees linear facts).
private theorem pos_core (cn cd p q : Int) (hcn : 1 ≤ cn) (hcd : 1 ≤ cd) (hq : 1 ≤ q)
    (h : cn * (q * (3 * cd + 1)) ≤ (p * (3 * cd + 1) + 2 * q) * cd) : q < p * (3 * cd + 1) := by
  have hqNnn : 0 ≤ q * (3 * cd + 1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : q * (3 * cd + 1) ≤ cn * (q * (3 * cd + 1)) := by
    have hh := Int.mul_le_mul_of_nonneg_right hcn hqNnn
    rwa [Int.one_mul] at hh
  have h2 : q * (3 * cd + 1) ≤ (p * (3 * cd + 1) + 2 * q) * cd := Int.le_trans h1 h
  have e1 : q * (3 * cd + 1) = 3 * (q * cd) + q := by ring_uor
  have e2 : (p * (3 * cd + 1) + 2 * q) * cd = (p * (3 * cd + 1)) * cd + 2 * (q * cd) := by ring_uor
  rw [e1, e2] at h2
  have h3 : q * cd < (p * (3 * cd + 1)) * cd := by omega
  exact Int.lt_of_mul_lt_mul_right h3 (by omega)

-- The ℤ core of left-subtraction cancellation (explicit, `omega` sees only linear facts).
private theorem sub_le_core (un ud an ad bn bd : Int) (hud : 1 ≤ ud)
    (h : (un * ad - an * ud) * (ud * bd) ≤ (un * bd - bn * ud) * (ud * ad)) : bn * ad ≤ an * bd := by
  have key : (an * bd - bn * ad) * (ud * ud)
      = (un * bd - bn * ud) * (ud * ad) - (un * ad - an * ud) * (ud * bd) := by ring_uor
  have hnn : 0 ≤ (an * bd - bn * ad) * (ud * ud) := by omega
  have hud2 : (0 : Int) < ud * ud := Int.mul_pos (by omega) (by omega)
  have hz : 0 * (ud * ud) ≤ (an * bd - bn * ad) * (ud * ud) := by rw [Int.zero_mul]; exact hnn
  have := Int.le_of_mul_le_mul_right hz hud2
  omega

/-- Left-subtraction cancellation: `u − a ≤ u − b  ⟹  b ≤ a`. -/
theorem Qle_of_Qsub_le_Qsub_left {u a b : Q} (hud : 0 < u.den)
    (h : Qle (Qsub u a) (Qsub u b)) : Qle b a := by
  have hudI : (1 : Int) ≤ (u.den : Int) := by exact_mod_cast hud
  show b.num * (a.den : Int) ≤ a.num * (b.den : Int)
  apply sub_le_core u.num (u.den : Int) a.num (a.den : Int) b.num (b.den : Int) hudI
  simp only [Qle, Qsub, add, neg] at h
  show (u.num * (a.den : Int) - a.num * (u.den : Int)) * ((u.den : Int) * (b.den : Int))
      ≤ (u.num * (b.den : Int) - b.num * (u.den : Int)) * ((u.den : Int) * (a.den : Int))
  have e1 : (u.num * (a.den : Int) - a.num * (u.den : Int))
      = u.num * (a.den : Int) + -a.num * (u.den : Int) := by ring_uor
  have e2 : (u.num * (b.den : Int) - b.num * (u.den : Int))
      = u.num * (b.den : Int) + -b.num * (u.den : Int) := by ring_uor
  rw [e1, e2]; exact h

/-- **Strict positivity from a rational lower bound**: if `c ≤ x` for a positive rational `c`
    (`Rle (ofQ c) x`), then `Pos x`. The reusable keystone for every numeric positivity claim. -/
theorem Pos_of_Rle_ofQ {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den) {x : Real}
    (h : Rle (ofQ c hcd) x) : Pos x := by
  refine ⟨3 * c.den, ?_⟩
  have hRle := h (3 * c.den)
  have hcdI : (1 : Int) ≤ (c.den : Int) := by exact_mod_cast hcd
  have hqI : (1 : Int) ≤ ((x.seq (3 * c.den)).den : Int) := by exact_mod_cast x.den_pos _
  have hcond : c.num * (((x.seq (3 * c.den)).den : Int) * (3 * (c.den : Int) + 1))
      ≤ ((x.seq (3 * c.den)).num * (3 * (c.den : Int) + 1) + 2 * ((x.seq (3 * c.den)).den : Int))
        * (c.den : Int) := by
    have hu : Qle c (add (x.seq (3 * c.den)) ⟨2, 3 * c.den + 1⟩) := hRle
    simp only [Qle, add] at hu
    push_cast at hu
    have hgoal : c.num * (((x.seq (3 * c.den)).den : Int) * ((3 * c.den + 1 : Nat) : Int))
        ≤ ((x.seq (3 * c.den)).num * ((3 * c.den + 1 : Nat) : Int)
          + 2 * ((x.seq (3 * c.den)).den : Int)) * (c.den : Int) := by
      push_cast; push_cast at hu; omega
    push_cast at hgoal; omega
  have key := pos_core c.num (c.den : Int) (x.seq (3 * c.den)).num ((x.seq (3 * c.den)).den : Int)
    (by omega) hcdI hqI hcond
  show Qlt (Qbound (3 * c.den)) (x.seq (3 * c.den))
  simp only [Qlt, Qbound]
  push_cast
  push_cast at key
  omega

/-- `arctan(1/5)` (radius 1/2). -/
def Ratan5 : Real :=
  Rarctan (⟨1, 5⟩ : Q) (by decide) (ρ := ⟨1, 2⟩) (by decide) (by decide) (by decide) (by decide)

/-- `arctan(1/239)` (radius 1/2). -/
def Ratan239 : Real :=
  Rarctan (⟨1, 239⟩ : Q) (by decide) (ρ := ⟨1, 2⟩) (by decide) (by decide) (by decide) (by decide)

/-- **π**, via Machin: `π = 16·arctan(1/5) − 4·arctan(1/239)`. -/
def Rpi : Real :=
  Rsub (Rmul (ofQ (⟨16, 1⟩ : Q) (by decide)) Ratan5)
    (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) Ratan239)

end UOR.Bridge.F1Square.Analysis
