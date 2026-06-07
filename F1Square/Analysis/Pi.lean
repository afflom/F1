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

-- The ℤ core of right-subtraction cancellation.
private theorem sub_le_core_r (xn yn un xd yd ud : Int) (hud : 1 ≤ ud)
    (h : (xn * ud - un * xd) * (yd * ud) ≤ (yn * ud - un * yd) * (xd * ud)) : xn * yd ≤ yn * xd := by
  have key : (yn * xd - xn * yd) * (ud * ud)
      = (yn * ud - un * yd) * (xd * ud) - (xn * ud - un * xd) * (yd * ud) := by ring_uor
  have hnn : 0 ≤ (yn * xd - xn * yd) * (ud * ud) := by omega
  have hud2 : (0 : Int) < ud * ud := Int.mul_pos (by omega) (by omega)
  have hz : 0 * (ud * ud) ≤ (yn * xd - xn * yd) * (ud * ud) := by rw [Int.zero_mul]; exact hnn
  have := Int.le_of_mul_le_mul_right hz hud2
  omega

/-- Right-subtraction cancellation: `x − u ≤ y − u  ⟹  x ≤ y`. -/
theorem Qle_of_Qsub_le_Qsub_right {x y u : Q} (hud : 0 < u.den)
    (h : Qle (Qsub x u) (Qsub y u)) : Qle x y := by
  have hudI : (1 : Int) ≤ (u.den : Int) := by exact_mod_cast hud
  show x.num * (y.den : Int) ≤ y.num * (x.den : Int)
  apply sub_le_core_r x.num y.num u.num (x.den : Int) (y.den : Int) (u.den : Int) hudI
  simp only [Qle, Qsub, add, neg] at h
  show (x.num * (u.den : Int) - u.num * (x.den : Int)) * ((y.den : Int) * (u.den : Int))
      ≤ (y.num * (u.den : Int) - u.num * (y.den : Int)) * ((x.den : Int) * (u.den : Int))
  have e1 : (x.num * (u.den : Int) - u.num * (x.den : Int))
      = x.num * (u.den : Int) + -u.num * (x.den : Int) := by ring_uor
  have e2 : (y.num * (u.den : Int) - u.num * (y.den : Int))
      = y.num * (u.den : Int) + -u.num * (y.den : Int) := by ring_uor
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

-- W = 1 − ρ² is positive when ρ.num.toNat < ρ.den (shared by the brackets).
private theorem W_pos {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hlt : ρ.num.toNat < ρ.den) :
    0 < (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).num := by
  show 0 < 1 * ((ρ.den * ρ.den : Nat) : Int) + -(ρ.num * ρ.num) * ((1 : Nat) : Int)
  have h1 : (ρ.num.toNat : Int) < (ρ.den : Int) := by exact_mod_cast hlt
  have h2 : (ρ.num.toNat : Int) = ρ.num := Int.toNat_of_nonneg hρ0
  have hd1 : (1 : Int) ≤ (ρ.den : Int) := by exact_mod_cast hρd
  have hp2 : ρ.num * ρ.num ≤ ((ρ.den : Int) - 1) * ((ρ.den : Int) - 1) :=
    Int.mul_le_mul (by omega) (by omega) hρ0 (by omega)
  have he2 : ((ρ.den : Int) - 1) * ((ρ.den : Int) - 1)
      = (ρ.den : Int) * (ρ.den : Int) - 2 * (ρ.den : Int) + 1 := by ring_uor
  push_cast; omega

-- ===========================================================================
-- Order toolkit: ℝ addition/negation/subtraction are monotone (reusable for λ₁).
-- ===========================================================================

-- ℤ core of negation antitonicity.
private theorem neg_le_core (an ad bn bd s : Int)
    (h : an * (bd * s) ≤ (bn * s + 2 * bd) * ad) :
    (-bn) * (ad * s) ≤ (-an * s + 2 * ad) * bd := by
  have e : (-an * s + 2 * ad) * bd - (-bn) * (ad * s)
      = (bn * s + 2 * bd) * ad - an * (bd * s) := by ring_uor
  omega

/-- ℝ negation is antitone: `a ≤ b ⟹ −b ≤ −a`. -/
theorem Rle_Rneg {a b : Real} (h : Rle a b) : Rle (Rneg b) (Rneg a) := by
  intro n
  have hh := h n
  show Qle (neg (b.seq n)) (add (neg (a.seq n)) ⟨2, n + 1⟩)
  simp only [Qle, neg, add] at hh ⊢
  have hc := neg_le_core (a.seq n).num (a.seq n).den (b.seq n).num (b.seq n).den ((n : Int) + 1) ?_
  · push_cast at hc ⊢; omega
  · push_cast at hh ⊢; omega

/-- ℝ addition is monotone. -/
theorem Radd_le_add {a a' b b' : Real} (ha : Rle a a') (hb : Rle b b') :
    Rle (Radd a b) (Radd a' b') := by
  intro n
  show Qle (add (a.seq (2 * n + 1)) (b.seq (2 * n + 1)))
    (add (add (a'.seq (2 * n + 1)) (b'.seq (2 * n + 1))) ⟨2, n + 1⟩)
  have hsum := Qadd_le_add (ha (2 * n + 1)) (hb (2 * n + 1))
  refine Qle_congr_right ?_ ?_ hsum
  · exact add_den_pos (add_den_pos (a'.den_pos (2 * n + 1)) (Nat.succ_pos _))
      (add_den_pos (b'.den_pos (2 * n + 1)) (Nat.succ_pos _))
  · simp only [Qeq, add]; push_cast; ring_uor

/-- ℝ subtraction is monotone: `a' ≤ a` and `b ≤ b' ⟹ a' − b' ≤ a − b`. -/
theorem Rsub_le_sub {a a' b b' : Real} (ha : Rle a' a) (hb : Rle b b') :
    Rle (Rsub a' b') (Rsub a b) := Radd_le_add ha (Rle_Rneg hb)

/-- **Lower pointwise bracket**: `L ≤ arctanSum t (Rₙ)` at every diagonal index `n`. -/
theorem arctanSum_diag_ge (t : Q) (htd : 0 < t.den) {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (htρ : Qle (Qabs t) ρ) {L : Q} (hLd : 0 < L.den)
    (hcond : Qle (qpow ρ 5) (mul (Qsub (arctanSum t 1) L) (Qsub ⟨1, 1⟩ (mul ρ ρ)))) (n : Nat) :
    Qle L (arctanSum t (Rartanh_R ρ n)) := by
  have hWn : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).num := W_pos hρ0 hρd hlt
  have hWd : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).den := Qsub_den_pos Nat.one_pos (Nat.mul_pos hρd hρd)
  have hWnn : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).num := Int.le_of_lt hWn
  have hRd : 0 < (arctanSum t (Rartanh_R ρ n)).den := arctanSum_den_pos htd _
  have h1d : 0 < (arctanSum t 1).den := arctanSum_den_pos htd 1
  have h1Rn : 1 ≤ Rartanh_R ρ n := by
    unfold Rartanh_R
    have : 1 ≤ ρ.den * ρ.den + 4 * ρ.den := by have := hρd; exact Nat.le_trans hρd (by omega)
    exact Nat.le_trans this (Nat.le_mul_of_pos_right _ (Nat.succ_pos n))
  have hsign : Qle (Qsub (arctanSum t 1) (arctanSum t (Rartanh_R ρ n)))
      (Qabs (Qsub (arctanSum t (Rartanh_R ρ n)) (arctanSum t 1))) := by
    have hs := Qle_self_Qabs (Qsub (arctanSum t 1) (arctanSum t (Rartanh_R ρ n)))
    rwa [Qabs_Qsub_comm] at hs
  have htrunc := arctanSum_trunc htd hρ0 hρd htρ hWnn (a := 1) h1Rn
  have hmain : Qle (mul (Qsub (arctanSum t 1) (arctanSum t (Rartanh_R ρ n)))
        (Qsub ⟨1, 1⟩ (mul ρ ρ)))
      (mul (Qsub (arctanSum t 1) L) (Qsub ⟨1, 1⟩ (mul ρ ρ))) :=
    Qle_trans (Qmul_den_pos (Qabs_den_pos (Qsub_den_pos hRd h1d)) hWd)
      (Qmul_le_mul_right hWnn hsign)
      (Qle_trans (qpow_den_pos hρd _) htrunc hcond)
  have hmain' : Qle (Qsub (mul (arctanSum t 1) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
        (mul (arctanSum t (Rartanh_R ρ n)) (Qsub ⟨1, 1⟩ (mul ρ ρ))))
      (Qsub (mul (arctanSum t 1) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
        (mul L (Qsub ⟨1, 1⟩ (mul ρ ρ)))) :=
    Qle_trans (Qmul_den_pos (Qsub_den_pos h1d hRd) hWd)
      (Qeq_le (Qeq_symm (Qmul_sub_right _ _ _)))
      (Qle_trans (Qmul_den_pos (Qsub_den_pos h1d hLd) hWd) hmain
        (Qeq_le (Qmul_sub_right _ _ _)))
  exact Qmul_le_cancel_right hWn hWd (Qle_of_Qsub_le_Qsub_left (Qmul_den_pos h1d hWd) hmain')

/-- **Lower bracket**: a rational `L` with `(arctanSum t 1 − L)·(1−ρ²) ≥ ρ⁵` is `≤ arctan t`. -/
theorem Rarctan_ge (t : Q) (htd : 0 < t.den) {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (htρ : Qle (Qabs t) ρ) {L : Q} (hLd : 0 < L.den)
    (hcond : Qle (qpow ρ 5) (mul (Qsub (arctanSum t 1) L) (Qsub ⟨1, 1⟩ (mul ρ ρ)))) :
    Rle (ofQ L hLd) (Rarctan t htd hρ0 hρd hlt htρ) := by
  intro n
  exact Qle_trans (arctanSum_den_pos htd _) (arctanSum_diag_ge t htd hρ0 hρd hlt htρ hLd hcond n)
    (Qle_self_add (by show (0 : Int) ≤ 2; decide))

/-- **Upper pointwise bracket**: `arctanSum t (Rₙ) ≤ U` at every diagonal index `n`. -/
theorem arctanSum_diag_le (t : Q) (htd : 0 < t.den) {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (htρ : Qle (Qabs t) ρ) {U : Q} (hUd : 0 < U.den)
    (hcond : Qle (qpow ρ 3) (mul (Qsub U (arctanSum t 0)) (Qsub ⟨1, 1⟩ (mul ρ ρ)))) (n : Nat) :
    Qle (arctanSum t (Rartanh_R ρ n)) U := by
  have hWn : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).num := W_pos hρ0 hρd hlt
  have hWd : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).den := Qsub_den_pos Nat.one_pos (Nat.mul_pos hρd hρd)
  have hWnn : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).num := Int.le_of_lt hWn
  have hRd : 0 < (arctanSum t (Rartanh_R ρ n)).den := arctanSum_den_pos htd _
  have h0d : 0 < (arctanSum t 0).den := arctanSum_den_pos htd 0
  have hsign : Qle (Qsub (arctanSum t (Rartanh_R ρ n)) (arctanSum t 0))
      (Qabs (Qsub (arctanSum t (Rartanh_R ρ n)) (arctanSum t 0))) := Qle_self_Qabs _
  have htrunc := arctanSum_trunc htd hρ0 hρd htρ hWnn (a := 0) (b := Rartanh_R ρ n) (Nat.zero_le _)
  have hmain : Qle (mul (Qsub (arctanSum t (Rartanh_R ρ n)) (arctanSum t 0))
        (Qsub ⟨1, 1⟩ (mul ρ ρ)))
      (mul (Qsub U (arctanSum t 0)) (Qsub ⟨1, 1⟩ (mul ρ ρ))) :=
    Qle_trans (Qmul_den_pos (Qabs_den_pos (Qsub_den_pos hRd h0d)) hWd)
      (Qmul_le_mul_right hWnn hsign)
      (Qle_trans (qpow_den_pos hρd _) htrunc hcond)
  have hmain' : Qle (Qsub (mul (arctanSum t (Rartanh_R ρ n)) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
        (mul (arctanSum t 0) (Qsub ⟨1, 1⟩ (mul ρ ρ))))
      (Qsub (mul U (Qsub ⟨1, 1⟩ (mul ρ ρ))) (mul (arctanSum t 0) (Qsub ⟨1, 1⟩ (mul ρ ρ)))) :=
    Qle_trans (Qmul_den_pos (Qsub_den_pos hRd h0d) hWd)
      (Qeq_le (Qeq_symm (Qmul_sub_right _ _ _)))
      (Qle_trans (Qmul_den_pos (Qsub_den_pos hUd h0d) hWd) hmain
        (Qeq_le (Qmul_sub_right _ _ _)))
  exact Qmul_le_cancel_right hWn hWd (Qle_of_Qsub_le_Qsub_right (Qmul_den_pos h0d hWd) hmain')

/-- **Upper bracket**: a rational `U` with `(U − arctanSum t 0)·(1−ρ²) ≥ ρ³` is `≥ arctan t`. -/
theorem Rarctan_le (t : Q) (htd : 0 < t.den) {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (htρ : Qle (Qabs t) ρ) {U : Q} (hUd : 0 < U.den)
    (hcond : Qle (qpow ρ 3) (mul (Qsub U (arctanSum t 0)) (Qsub ⟨1, 1⟩ (mul ρ ρ)))) :
    Rle (Rarctan t htd hρ0 hρd hlt htρ) (ofQ U hUd) := by
  intro n
  exact Qle_trans hUd (arctanSum_diag_le t htd hρ0 hρd hlt htρ hUd hcond n)
    (Qle_self_add (by show (0 : Int) ≤ 2; decide))

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
