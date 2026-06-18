/-
F1 square — v0.22.0 Track 1, brick (complex lift / log-multiplicativity): **the rational `artanh`
addition law** — `2·artanh a + 2·artanh b = 2·artanh((a+b)/(1+ab))` for rational `0 ≤ a, b` with
`a, b, (a+b)/(1+ab) < 1`.

This is the arithmetic heart of log-multiplicativity `log(xy) = log x + log y` (hence of `Clog`
additivity, hence of the Hadamard `log ξ`). The route is exactly the one recorded: three instances
of the exp/artanh identity `exp(2·artanh τ) = (1+τ)/(1−τ)` feed the exp-injectivity additivity core
`Req_add_of_exp_values` (`RArctanCongr.lean`), with the algebraic identity
`(1+c)/(1−c) = ((1+a)/(1−a))·((1+b)/(1−b))` (for `c = (a+b)/(1+ab)`) supplying its `gC = gA·gB`.

The first brick here, `Rexp_twoArtanh_general`, packages the heavy `Rexp_two_artanh_ofQ` parameter
thicket **once** for an arbitrary rational `0 ≤ τ < 1`, with the generic choices
`g = (1+τ)/(1−τ) = (q+p)/(q−p)`, `K = q/(q−p)`, `M' = 2q`, `C = (2L+4)q²` (where `τ = p/q`,
`d = q−p`); the budget slack is `(2L+4)q²·d(j+1)²·(d−1) ≥ 0`, clean because `d ≥ 1`. This is the
radius-`ρ = τ` analog of `Rexp_twoArtanhRecip` (`GammaOne.lean`) at a *general* base.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.RArctanCongr
import F1Square.Analysis.GammaOne

namespace UOR.Bridge.F1Square.Analysis

-- The two cleared `Int` inequalities behind the general instantiation (clean atoms for `ring_uor`).

/-- `hM2` cleared: `K·2 ≤ 2q`, `K = q/(q−p)`. Slack `2q·((q−p)−1) ≥ 0` (the `q−p ≥ 1` margin). -/
private theorem twoArtanhGen_hM2_int (Q P : Int) (hQ : 1 ≤ Q) (hPQ : P < Q) :
    Q * 2 * 1 ≤ 2 * Q * ((Q - P) * 1) := by
  have hnn : (0 : Int) ≤ 2 * Q * ((Q - P) - 1) := Int.mul_nonneg (by omega) (by omega)
  have key : 2 * Q * ((Q - P) * 1) - Q * 2 * 1 = 2 * Q * ((Q - P) - 1) := by ring_uor
  omega

/-- `hBC` cleared, `C = (2L+4)q²`: slack `RHS − LHS = (2L+4)q²·(q−p)·(j+1)²·((q−p)−1) ≥ 0`
    (the `q−p ≥ 1` margin, multiplied by manifestly non-negative factors). -/
private theorem twoArtanhGen_hBC_int (L Q P J : Int) (hL : 0 ≤ L) (hQ : 1 ≤ Q) (hPQ : P < Q)
    (hJ : 0 ≤ J) :
    (L * (Q * (2 * Q)) * ((Q - P) * (1 * (J + 1)))
        + Q * (4 * Q) * (1 * ((Q - P) * (1 * (J + 1))))) * (J + 1)
      ≤ (2 * L + 4) * Q * Q * (1 * ((Q - P) * (1 * (J + 1))) * ((Q - P) * (1 * (J + 1)))) := by
  have hnn : (0 : Int) ≤ (2 * L + 4) * Q * Q * (Q - P) * ((J + 1) * (J + 1)) * ((Q - P) - 1) :=
    Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg
      (by omega) (by omega)) (by omega)) (by omega))
      (Int.mul_nonneg (by omega) (by omega))) (by omega)
  have key : (2 * L + 4) * Q * Q * (1 * ((Q - P) * (1 * (J + 1))) * ((Q - P) * (1 * (J + 1))))
        - (L * (Q * (2 * Q)) * ((Q - P) * (1 * (J + 1)))
            + Q * (4 * Q) * (1 * ((Q - P) * (1 * (J + 1))))) * (J + 1)
      = (2 * L + 4) * Q * Q * (Q - P) * ((J + 1) * (J + 1)) * ((Q - P) - 1) := by ring_uor
  omega

/-- **`artanh τ ≥ 0` doubled**: `2·artanh τ ≥ 0` for `0 ≤ τ`. `TwoArtanhConst = 2·RartanhConst`, and
    both factors are non-negative (`Rnonneg_ofQ`, `Rnonneg_RartanhConst`). -/
theorem Rnonneg_TwoArtanhConst (τ ρ : Q) (hτd : 0 < τ.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hρlt : ρ.num.toNat < ρ.den) (hb : Qle (Qabs τ) ρ) (hτ0 : 0 ≤ τ.num) :
    Rnonneg (TwoArtanhConst τ ρ hτd hρ0 hρd hρlt hb) :=
  Rnonneg_Rmul (Rnonneg_ofQ (by decide) (by show (0 : Int) ≤ 2; decide))
    (Rnonneg_RartanhConst τ ρ hτd hρ0 hρd hρlt hb hτ0)

-- ===========================================================================
-- The general exp/artanh identity at radius ρ = τ, for an arbitrary rational 0 ≤ τ < 1.
-- Generic parameters: p = τ.num, q = τ.den, d = q − p; g = (q+p)/d, K = q/d, M' = 2q, C = (2L+4)q².
-- ===========================================================================

/-- **`exp(2·artanh τ) = (1+τ)/(1−τ)` for a general rational `0 ≤ τ < 1`** (radius `ρ = τ`).
    Packages the `Rexp_two_artanh_ofQ` parameter thicket once: with `τ = p/q` and `d = q − p`, the
    target `g = (q+p)/d` is `(1+τ)/(1−τ)`, and the regularity budget `C = (2L+4)q²` clears with slack
    `(2L+4)q²·d(j+1)²·(d−1) ≥ 0`. -/
theorem Rexp_twoArtanh_general (τ : Q) (hτd : 0 < τ.den) (hτ0 : 0 ≤ τ.num)
    (hτlt : τ.num.toNat < τ.den) :
    Req (RexpReal (TwoArtanhConst τ τ hτd hτ0 hτd hτlt (Qeq_le (Qabs_of_nonneg hτ0))))
      (ofQ (⟨(τ.den : Int) + τ.num, τ.den - τ.num.toNat⟩ : Q)
        (by show 0 < τ.den - τ.num.toNat; omega)) := by
  -- d = q − p as an Int equation
  have hpI : (τ.num.toNat : Int) = τ.num := Int.toNat_of_nonneg hτ0
  have hdI : ((τ.den - τ.num.toNat : Nat) : Int) = (τ.den : Int) - τ.num := by
    rw [Int.ofNat_sub (Nat.le_of_lt hτlt), hpI]
  have hdpos : 0 < τ.den - τ.num.toNat := by omega
  refine Rexp_two_artanh_ofQ τ τ
    (⟨(τ.den : Int) + τ.num, τ.den - τ.num.toNat⟩ : Q)
    (⟨(τ.den : Int), τ.den - τ.num.toNat⟩ : Q)
    (2 * τ.den) ((expM_U (2 * τ.den) (2 * (2 * τ.den))).num.toNat)
    ((2 * (expM_U (2 * τ.den) (2 * (2 * τ.den))).num.toNat + 4) * τ.den * τ.den)
    hτd hτ0 ?_ hτlt hτ0 hτd hτlt (Qeq_le (Qabs_of_nonneg hτ0))
    hdpos ?_ hdpos (by show (0 : Int) ≤ τ.den; exact Int.ofNat_nonneg _) ?_ rfl ?_ ?_
  · -- hτ1 : τ ≤ 1
    show Qle τ ⟨1, 1⟩; simp only [Qle]; push_cast; omega
  · -- hg : g·(1−τ) = 1+τ
    show Qeq (mul (⟨(τ.den : Int) + τ.num, τ.den - τ.num.toNat⟩ : Q) (Qsub ⟨1, 1⟩ τ)) (add ⟨1, 1⟩ τ)
    simp only [Qeq, mul, Qsub, add, neg]; push_cast [hdI]; ring_uor
  · -- hKF : 1 ≤ K·(1−τ)   (in fact = 1)
    refine Qeq_le ?_
    show Qeq (⟨1, 1⟩ : Q) (mul (⟨(τ.den : Int), τ.den - τ.num.toNat⟩ : Q) (Qsub ⟨1, 1⟩ τ))
    simp only [Qeq, mul, Qsub, add, neg]; push_cast [hdI]; ring_uor
  · -- hM2 : K·2 ≤ ⟨2q,1⟩
    show Qle (mul (⟨(τ.den : Int), τ.den - τ.num.toNat⟩ : Q) ⟨2, 1⟩) ⟨2 * τ.den, 1⟩
    simp only [Qle, mul]; push_cast [hdI]
    exact twoArtanhGen_hM2_int (τ.den : Int) τ.num (by omega) (by omega)
  · -- hBC : the per-index regularity budget, slack (2L+4)q²·d(j+1)²·(d−1) ≥ 0
    intro j
    show Qle (add (mul ⟨((expM_U (2 * τ.den) (2 * (2 * τ.den))).num.toNat : Int), 1⟩
            (mul (⟨(τ.den : Int), τ.den - τ.num.toNat⟩ : Q) (mul ⟨2, 1⟩ (⟨(τ.den : Int), j + 1⟩ : Q))))
          (mul (⟨(τ.den : Int), τ.den - τ.num.toNat⟩ : Q) (mul ⟨4, 1⟩ (⟨(τ.den : Int), j + 1⟩ : Q))))
        (⟨((2 * (expM_U (2 * τ.den) (2 * (2 * τ.den))).num.toNat + 4) * τ.den * τ.den : Int), j + 1⟩ : Q)
    simp only [Qle, add, mul]
    push_cast [hdI]
    exact twoArtanhGen_hBC_int ((expM_U (2 * τ.den) (2 * (2 * τ.den))).num.toNat : Int)
      (τ.den : Int) τ.num (j : Int) (Int.ofNat_nonneg _) (by omega) (by omega) (Int.ofNat_nonneg _)

-- ===========================================================================
-- The rational artanh addition law: 2·artanh c = 2·artanh a + 2·artanh b, gated on the
-- multiplicativity of the (1+τ)/(1−τ) values (which is exactly c = (a+b)/(1+ab)).
-- ===========================================================================

/-- **The rational `artanh` addition law**: `2·artanh c = 2·artanh a + 2·artanh b` for rationals
    `0 ≤ a, b, c < 1`, **provided** the `(1+τ)/(1−τ)` values multiply:
    `(1+c)/(1−c) = ((1+a)/(1−a))·((1+b)/(1−b))` (the `hg` side-condition, which is exactly
    `c = (a+b)/(1+ab)`). Three instances of `Rexp_twoArtanh_general` feed the exp-injectivity
    additivity core `Req_add_of_exp_values`. This is the arithmetic heart of log-multiplicativity. -/
theorem TwoArtanh_add_rat (a b c : Q)
    (had : 0 < a.den) (ha0 : 0 ≤ a.num) (halt : a.num.toNat < a.den)
    (hbd : 0 < b.den) (hb0 : 0 ≤ b.num) (hblt : b.num.toNat < b.den)
    (hcd : 0 < c.den) (hc0 : 0 ≤ c.num) (hclt : c.num.toNat < c.den)
    (hg : Qeq (⟨(c.den : Int) + c.num, c.den - c.num.toNat⟩ : Q)
              (mul (⟨(a.den : Int) + a.num, a.den - a.num.toNat⟩ : Q)
                   (⟨(b.den : Int) + b.num, b.den - b.num.toNat⟩ : Q))) :
    Req (TwoArtanhConst c c hcd hc0 hcd hclt (Qeq_le (Qabs_of_nonneg hc0)))
        (Radd (TwoArtanhConst a a had ha0 had halt (Qeq_le (Qabs_of_nonneg ha0)))
              (TwoArtanhConst b b hbd hb0 hbd hblt (Qeq_le (Qabs_of_nonneg hb0)))) := by
  have hda : 0 < a.den - a.num.toNat := by omega
  have hdb : 0 < b.den - b.num.toNat := by omega
  have hdc : 0 < c.den - c.num.toNat := by omega
  exact Req_add_of_exp_values hda hdb hdc
    (Rexp_twoArtanh_general a had ha0 halt)
    (Rexp_twoArtanh_general b hbd hb0 hblt)
    (Rexp_twoArtanh_general c hcd hc0 hclt)
    hg
    (Rnonneg_TwoArtanhConst a a had ha0 had halt (Qeq_le (Qabs_of_nonneg ha0)) ha0)
    (Rnonneg_TwoArtanhConst b b hbd hb0 hbd hblt (Qeq_le (Qabs_of_nonneg hb0)) hb0)
    (Rnonneg_TwoArtanhConst c c hcd hc0 hcd hclt (Qeq_le (Qabs_of_nonneg hc0)) hc0)

end UOR.Bridge.F1Square.Analysis
