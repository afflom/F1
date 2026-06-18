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

/-- **`exp(2·artanh τ) = (1+τ)/(1−τ)` at a FREE radius `ρ ≥ |τ|`** (`0 ≤ τ < 1`). The radius-general
    form of `Rexp_twoArtanh_general` (which fixed `ρ = τ`); the radius enters only the depth reindex
    (absorbed by `Rexp_two_artanh_via`), so the `hg`/`hKF`/`hM2`/`hBC` goals are identical. Needed so the
    diagonal addition can put all three artanh's at one common radius. -/
theorem Rexp_twoArtanh_general_rho (τ ρ : Q) (hτd : 0 < τ.den) (hτ0 : 0 ≤ τ.num)
    (hτlt : τ.num.toNat < τ.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hρlt : ρ.num.toNat < ρ.den) (hb : Qle (Qabs τ) ρ) :
    Req (RexpReal (TwoArtanhConst τ ρ hτd hρ0 hρd hρlt hb))
      (ofQ (⟨(τ.den : Int) + τ.num, τ.den - τ.num.toNat⟩ : Q)
        (by show 0 < τ.den - τ.num.toNat; omega)) := by
  have hpI : (τ.num.toNat : Int) = τ.num := Int.toNat_of_nonneg hτ0
  have hdI : ((τ.den - τ.num.toNat : Nat) : Int) = (τ.den : Int) - τ.num := by
    rw [Int.ofNat_sub (Nat.le_of_lt hτlt), hpI]
  have hdpos : 0 < τ.den - τ.num.toNat := by omega
  refine Rexp_two_artanh_ofQ τ ρ
    (⟨(τ.den : Int) + τ.num, τ.den - τ.num.toNat⟩ : Q)
    (⟨(τ.den : Int), τ.den - τ.num.toNat⟩ : Q)
    (2 * τ.den) ((expM_U (2 * τ.den) (2 * (2 * τ.den))).num.toNat)
    ((2 * (expM_U (2 * τ.den) (2 * (2 * τ.den))).num.toNat + 4) * τ.den * τ.den)
    hτd hτ0 ?_ hτlt hρ0 hρd hρlt hb
    hdpos ?_ hdpos (by show (0 : Int) ≤ τ.den; exact Int.ofNat_nonneg _) ?_ rfl ?_ ?_
  · show Qle τ ⟨1, 1⟩; simp only [Qle]; push_cast; omega
  · show Qeq (mul (⟨(τ.den : Int) + τ.num, τ.den - τ.num.toNat⟩ : Q) (Qsub ⟨1, 1⟩ τ)) (add ⟨1, 1⟩ τ)
    simp only [Qeq, mul, Qsub, add, neg]; push_cast [hdI]; ring_uor
  · refine Qeq_le ?_
    show Qeq (⟨1, 1⟩ : Q) (mul (⟨(τ.den : Int), τ.den - τ.num.toNat⟩ : Q) (Qsub ⟨1, 1⟩ τ))
    simp only [Qeq, mul, Qsub, add, neg]; push_cast [hdI]; ring_uor
  · show Qle (mul (⟨(τ.den : Int), τ.den - τ.num.toNat⟩ : Q) ⟨2, 1⟩) ⟨2 * τ.den, 1⟩
    simp only [Qle, mul]; push_cast [hdI]
    exact twoArtanhGen_hM2_int (τ.den : Int) τ.num (by omega) (by omega)
  · intro j
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

-- ===========================================================================
-- The division-free addition map `wval a b = (a+b)/(1+ab)` and its multiplicativity identity,
-- which discharges the `hg` side-condition of `TwoArtanh_add_rat` once and for all.
-- ===========================================================================

/-- **The `artanh`/`tanh` addition map** `wval a b = (a+b)/(1+ab)`, in division-free unreduced form:
    numerator `pa·qb + pb·qa`, denominator `qa·qb + pa·pb` (where `a = pa/qa`, `b = pb/qb`). -/
def wval (a b : Q) : Q :=
  ⟨a.num * (b.den : Int) + b.num * (a.den : Int), a.den * b.den + (a.num * b.num).toNat⟩

@[simp] theorem wval_num (a b : Q) : (wval a b).num = a.num * (b.den : Int) + b.num * (a.den : Int) := rfl
@[simp] theorem wval_den (a b : Q) : (wval a b).den = a.den * b.den + (a.num * b.num).toNat := rfl

/-- `wval a b` has positive denominator (`qa·qb > 0`). -/
theorem wval_den_pos (a b : Q) (had : 0 < a.den) (hbd : 0 < b.den) : 0 < (wval a b).den := by
  rw [wval_den]; exact Nat.lt_of_lt_of_le (Nat.mul_pos had hbd) (Nat.le_add_right _ _)

/-- `wval a b` has non-negative numerator (for `a, b ≥ 0`). -/
theorem wval_num_nonneg (a b : Q) (ha0 : 0 ≤ a.num) (hb0 : 0 ≤ b.num) : 0 ≤ (wval a b).num := by
  rw [wval_num]
  exact Int.add_nonneg (Int.mul_nonneg ha0 (Int.ofNat_nonneg _)) (Int.mul_nonneg hb0 (Int.ofNat_nonneg _))

/-- **`wval a b < 1`** for `0 ≤ a, b < 1`: `pa·qb + pb·qa < qa·qb + pa·pb`, the slack being
    `(qa−pa)(qb−pb) > 0` (the `a, b < 1` margins). -/
theorem wval_lt (a b : Q) (_had : 0 < a.den) (ha0 : 0 ≤ a.num) (halt : a.num.toNat < a.den)
    (_hbd : 0 < b.den) (hb0 : 0 ≤ b.num) (hblt : b.num.toNat < b.den) :
    (wval a b).num.toNat < (wval a b).den := by
  have hpaI : (a.num.toNat : Int) = a.num := Int.toNat_of_nonneg ha0
  have hpbI : (b.num.toNat : Int) = b.num := Int.toNat_of_nonneg hb0
  have ha1 : a.num < (a.den : Int) := by omega
  have hb1 : b.num < (b.den : Int) := by omega
  have hnum0 : 0 ≤ (wval a b).num := wval_num_nonneg a b ha0 hb0
  -- it suffices to show the Int inequality (wval).num < (wval).den
  have hkey : (wval a b).num < ((wval a b).den : Int) := by
    rw [wval_num, wval_den]
    have hPP : ((a.num * b.num).toNat : Int) = a.num * b.num :=
      Int.toNat_of_nonneg (Int.mul_nonneg ha0 hb0)
    push_cast [hPP]
    have hslack : 0 < ((a.den : Int) - a.num) * ((b.den : Int) - b.num) :=
      Int.mul_pos (by omega) (by omega)
    have key : ((a.den : Int) - a.num) * ((b.den : Int) - b.num)
        = ((a.den : Int) * b.den + a.num * b.num)
            - (a.num * (b.den : Int) + b.num * (a.den : Int)) := by ring_uor
    omega
  omega

/-- The pure-`Int` polynomial identity behind `wval_hg` (clean atoms for `ring_uor`, no `Nat.cast`):
    both sides clear to `(qa+pa)(qb+pb)(qa−pa)(qb−pb)`. -/
private theorem wval_hg_poly (qa pa qb pb : Int) :
    (qa * qb + pa * pb + (pa * qb + pb * qa)) * ((qa - pa) * (qb - pb))
      = (qa + pa) * (qb + pb) * (qa * qb + pa * pb - (pa * qb + pb * qa)) := by ring_uor

/-- **The multiplicativity identity** `(1+wval)/(1−wval) = ((1+a)/(1−a))·((1+b)/(1−b))` — exactly the
    `hg` of `TwoArtanh_add_rat` for `c = wval a b`. Both sides clear to `(qa+pa)(qb+pb)·(qa−pa)(qb−pb)`. -/
theorem wval_hg (a b : Q) (had : 0 < a.den) (ha0 : 0 ≤ a.num) (halt : a.num.toNat < a.den)
    (hbd : 0 < b.den) (hb0 : 0 ≤ b.num) (hblt : b.num.toNat < b.den) :
    Qeq (⟨((wval a b).den : Int) + (wval a b).num, (wval a b).den - (wval a b).num.toNat⟩ : Q)
        (mul (⟨(a.den : Int) + a.num, a.den - a.num.toNat⟩ : Q)
             (⟨(b.den : Int) + b.num, b.den - b.num.toNat⟩ : Q)) := by
  have hpaI : (a.num.toNat : Int) = a.num := Int.toNat_of_nonneg ha0
  have hpbI : (b.num.toNat : Int) = b.num := Int.toNat_of_nonneg hb0
  have hgA : ((a.den - a.num.toNat : Nat) : Int) = (a.den : Int) - a.num := by
    rw [Int.ofNat_sub (Nat.le_of_lt halt), hpaI]
  have hgB : ((b.den - b.num.toNat : Nat) : Int) = (b.den : Int) - b.num := by
    rw [Int.ofNat_sub (Nat.le_of_lt hblt), hpbI]
  have hPP : ((a.num * b.num).toNat : Int) = a.num * b.num :=
    Int.toNat_of_nonneg (Int.mul_nonneg ha0 hb0)
  have hWnum : ((wval a b).num.toNat : Int) = a.num * (b.den : Int) + b.num * (a.den : Int) := by
    rw [Int.toNat_of_nonneg (wval_num_nonneg a b ha0 hb0), wval_num]
  have hWden : ((wval a b).den : Int) = (a.den : Int) * b.den + a.num * b.num := by
    rw [wval_den]; push_cast [hPP]; ring_uor
  have hWlt : (wval a b).num.toNat ≤ (wval a b).den := Nat.le_of_lt (wval_lt a b had ha0 halt hbd hb0 hblt)
  simp only [Qeq, mul]
  rw [Int.ofNat_sub hWlt, hWnum, hWden, wval_num]
  push_cast [hgA, hgB]
  exact wval_hg_poly (a.den : Int) a.num (b.den : Int) b.num

/-- **The `artanh` addition law in directly-usable form**: `2·artanh(wval a b) = 2·artanh a + 2·artanh b`
    for rationals `0 ≤ a, b < 1`, with the sum-argument `c = wval a b = (a+b)/(1+ab)` computed and the
    `hg` side-condition discharged by `wval_hg`. -/
theorem TwoArtanh_add_wval (a b : Q)
    (had : 0 < a.den) (ha0 : 0 ≤ a.num) (halt : a.num.toNat < a.den)
    (hbd : 0 < b.den) (hb0 : 0 ≤ b.num) (hblt : b.num.toNat < b.den) :
    Req (TwoArtanhConst (wval a b) (wval a b)
          (wval_den_pos a b had hbd) (wval_num_nonneg a b ha0 hb0) (wval_den_pos a b had hbd)
          (wval_lt a b had ha0 halt hbd hb0 hblt) (Qeq_le (Qabs_of_nonneg (wval_num_nonneg a b ha0 hb0))))
        (Radd (TwoArtanhConst a a had ha0 had halt (Qeq_le (Qabs_of_nonneg ha0)))
              (TwoArtanhConst b b hbd hb0 hbd hblt (Qeq_le (Qabs_of_nonneg hb0)))) :=
  TwoArtanh_add_rat a b (wval a b) had ha0 halt hbd hb0 hblt
    (wval_den_pos a b had hbd) (wval_num_nonneg a b ha0 hb0) (wval_lt a b had ha0 halt hbd hb0 hblt)
    (wval_hg a b had ha0 halt hbd hb0 hblt)

/-- **The artanh addition law at a common free radius σ** — `2·artanh(wval a b) = 2·artanh a +
    2·artanh b` with all three `artanh`'s evaluated at one radius `σ` (≥ each `|·|`). The radius-general
    form of `TwoArtanh_add_wval`, needed so the real-lift diagonal can compare the three series at a
    common truncation depth. -/
theorem TwoArtanh_add_wval_rho (a b σ : Q)
    (had : 0 < a.den) (ha0 : 0 ≤ a.num) (halt : a.num.toNat < a.den)
    (hbd : 0 < b.den) (hb0 : 0 ≤ b.num) (hblt : b.num.toNat < b.den)
    (hσ0 : 0 ≤ σ.num) (hσd : 0 < σ.den) (hσlt : σ.num.toNat < σ.den)
    (hba : Qle (Qabs a) σ) (hbb : Qle (Qabs b) σ) (hbc : Qle (Qabs (wval a b)) σ) :
    Req (TwoArtanhConst (wval a b) σ (wval_den_pos a b had hbd) hσ0 hσd hσlt hbc)
        (Radd (TwoArtanhConst a σ had hσ0 hσd hσlt hba)
              (TwoArtanhConst b σ hbd hσ0 hσd hσlt hbb)) := by
  have hda : 0 < a.den - a.num.toNat := by omega
  have hdb : 0 < b.den - b.num.toNat := by omega
  have hdc : 0 < (wval a b).den - (wval a b).num.toNat := by
    have := wval_lt a b had ha0 halt hbd hb0 hblt; omega
  exact Req_add_of_exp_values hda hdb hdc
    (Rexp_twoArtanh_general_rho a σ had ha0 halt hσ0 hσd hσlt hba)
    (Rexp_twoArtanh_general_rho b σ hbd hb0 hblt hσ0 hσd hσlt hbb)
    (Rexp_twoArtanh_general_rho (wval a b) σ (wval_den_pos a b had hbd)
      (wval_num_nonneg a b ha0 hb0) (wval_lt a b had ha0 halt hbd hb0 hblt) hσ0 hσd hσlt hbc)
    (wval_hg a b had ha0 halt hbd hb0 hblt)
    (Rnonneg_TwoArtanhConst a σ had hσ0 hσd hσlt hba ha0)
    (Rnonneg_TwoArtanhConst b σ hbd hσ0 hσd hσlt hbb hb0)
    (Rnonneg_TwoArtanhConst (wval a b) σ (wval_den_pos a b had hbd) hσ0 hσd hσlt hbc
      (wval_num_nonneg a b ha0 hb0))

/-- `½·(2·x) ≈ x` (local copy; `half_two_cancel` lives downstream). The `Rmul`-coefficient collapse
    `½·2 = 1`, via `Rmul_ofQ_ofQ` + `ofQ_congr` + `Rmul_assoc` + `Rone_mul`. -/
private theorem two_half_cancel (x : Real) :
    Req (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) x)) x := by
  have hc : Req (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (ofQ (⟨2, 1⟩ : Q) (by decide))) one :=
    Req_trans (Rmul_ofQ_ofQ (by decide) (by decide)) (ofQ_congr (by decide) (by decide) (by decide))
  refine Req_trans (Req_symm (Rmul_assoc (ofQ (⟨1, 2⟩ : Q) (by decide))
    (ofQ (⟨2, 1⟩ : Q) (by decide)) x)) ?_
  exact Req_trans (Rmul_congr hc (Req_refl x)) (Rone_mul x)

/-- **The single-`artanh` addition law at a common radius** (the `×2` stripped): `artanh(wval a b) =
    artanh a + artanh b` as `RartanhConst`s. From `TwoArtanh_add_wval_rho` (definitionally
    `Rmul 2 ∘ RartanhConst`) by `Rmul_distrib` + cancelling the `2` via `half_two_cancel`. This
    single-level form has clean depths for the diagonal's combination bound. -/
theorem RartanhConst_add_wval_rho (a b σ : Q)
    (had : 0 < a.den) (ha0 : 0 ≤ a.num) (halt : a.num.toNat < a.den)
    (hbd : 0 < b.den) (hb0 : 0 ≤ b.num) (hblt : b.num.toNat < b.den)
    (hσ0 : 0 ≤ σ.num) (hσd : 0 < σ.den) (hσlt : σ.num.toNat < σ.den)
    (hba : Qle (Qabs a) σ) (hbb : Qle (Qabs b) σ) (hbc : Qle (Qabs (wval a b)) σ) :
    Req (RartanhConst (wval a b) σ (wval_den_pos a b had hbd) hσ0 hσd hσlt hbc)
        (Radd (RartanhConst a σ had hσ0 hσd hσlt hba)
              (RartanhConst b σ hbd hσ0 hσd hσlt hbb)) := by
  have hlaw := TwoArtanh_add_wval_rho a b σ had ha0 halt hbd hb0 hblt hσ0 hσd hσlt hba hbb hbc
  have hmul2 : Req (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide))
        (RartanhConst (wval a b) σ (wval_den_pos a b had hbd) hσ0 hσd hσlt hbc))
      (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide))
        (Radd (RartanhConst a σ had hσ0 hσd hσlt hba)
              (RartanhConst b σ hbd hσ0 hσd hσlt hbb))) :=
    Req_trans hlaw (Req_symm (Rmul_distrib _ _ _))
  exact Req_trans (Req_symm (two_half_cancel _))
    (Req_trans (Rmul_congr (Req_refl (ofQ (⟨1, 2⟩ : Q) (by decide))) hmul2) (two_half_cancel _))

-- ===========================================================================
-- The binary Lipschitz core for the REAL lift of the addition law.
--
-- Structural finding (this is why the real lift is materially harder than the unary doubling
-- `Rartanh_double_real_via`): doubling `2·artanh t = artanh(2t/(1+t²))` lifts to real `t` through a
-- SINGLE-variable polynomial composition (`dcomp_artSum` / `peval (fcomp acoef kdbl)`), composing
-- the doubling polynomial `kdbl` with the artanh series. Binary addition has NO such single-variable
-- composition, so its real lift needs a genuine two-variable continuity argument over a sign-robust
-- binary map. The certified algebraic heart of that argument is the cleared difference numerator:
-- varying ONE argument of `(s+t)/(1+st)` factors as `(Δ-cross)·(1 − other²)`, so each one-sided
-- variation is Lipschitz with the `(1 − other²)` constant — the exact analog of `uval_diff_cleared`.
-- ===========================================================================

/-- **Binary cleared difference, first argument** (the Lipschitz numerator of `(·+c)/(1+·c)`):
    `N(a,c)·D(b,c) − N(b,c)·D(a,c) = (pa·qb − pb·qa)·(qc² − pc²)`, where `N(x,y) = px·qy + py·qx` and
    `D(x,y) = qx·qy + px·py` are the unreduced numerator/denominator of `(x+y)/(1+xy)`. The cross-term
    `pa·qb − pb·qa` is the unreduced `a − b`; the factor `qc² − pc²` is the unreduced `1 − c²`. So the
    one-sided variation is Lipschitz with constant `1 − c²` (`≤ 1`). Certified by `ring_uor`. -/
theorem wval_argdiff1_cleared (pa qa pb qb pc qc : Int) :
    (pa * qc + pc * qa) * (qb * qc + pb * pc) - (pb * qc + pc * qb) * (qa * qc + pa * pc)
      = (pa * qb - pb * qa) * (qc * qc - pc * pc) := by ring_uor

/-- **Binary cleared difference, second argument** (the symmetric companion of `wval_argdiff1_cleared`,
    since `(s+t)/(1+st)` is symmetric): varying the second argument of `(a+·)/(1+a·)` factors as
    `(pc·qd − pd·qc)·(qa² − pa²)` — the unreduced `(c − d)·(1 − a²)`. Certified by `ring_uor`. -/
theorem wval_argdiff2_cleared (pa qa pc qc pd qd : Int) :
    (pa * qc + pc * qa) * (qa * qd + pa * pd) - (pa * qd + pd * qa) * (qa * qc + pa * pc)
      = (pc * qd - pd * qc) * (qa * qa - pa * pa) := by ring_uor

/-- **The sign-robust binary addition map** `wvalR a b = (a+b)/(1+ab)`, with denominator `(1+ab)`'s
    *whole* numerator under `.toNat` (positive whenever `|a|,|b| < 1`, i.e. `1+ab > 0`) — unlike `wval`
    (which puts only the `a.num·b.num` term under `.toNat`, correct only for `a, b ≥ 0`). This is the
    basis for the real binary map `wvalReal` (whose approximant signs wobble). -/
def wvalR (a b : Q) : Q :=
  ⟨a.num * (b.den : Int) + b.num * (a.den : Int), ((a.den : Int) * b.den + a.num * b.num).toNat⟩

@[simp] theorem wvalR_num (a b : Q) :
    (wvalR a b).num = a.num * (b.den : Int) + b.num * (a.den : Int) := rfl
@[simp] theorem wvalR_den (a b : Q) :
    (wvalR a b).den = ((a.den : Int) * b.den + a.num * b.num).toNat := rfl

/-- **`wvalR a b` has positive denominator** when `1 + ab > 0` (`(a.den·b.den : Int) + a.num·b.num > 0`),
    which holds for `|a|, |b| < 1`. -/
theorem wvalR_den_pos (a b : Q) (h : 0 < (a.den : Int) * b.den + a.num * b.num) :
    0 < (wvalR a b).den := by
  rw [wvalR_den]; omega

/-- **`wval = wvalR` for non-negative arguments** (`a.num·b.num ≥ 0`): the `≥0` map `wval` and the
    sign-robust `wvalR` coincide (same numerator; the denominators `a.den·b.den + (a.num·b.num).toNat`
    and `((a.den·b.den : Int) + a.num·b.num).toNat` agree when `a.num·b.num ≥ 0`). Bridges the rational
    addition law (`wval`) to the Lipschitz machinery (`wvalR`). -/
theorem wval_eq_wvalR (a b : Q) (h : 0 ≤ a.num * b.num) : wval a b = wvalR a b := by
  have hden : a.den * b.den + (a.num * b.num).toNat = ((a.den : Int) * b.den + a.num * b.num).toNat := by
    omega
  unfold wval wvalR; rw [hden]

/-- The pure-`Int` form of `wvalR_argdiff1` (post-`simp` arrangement, clean atoms for `ring_uor`). -/
private theorem wvalR_argdiff1_poly (pa qa pb qb pc qc : Int) :
    (pa * qc + pc * qa) * (qb * qc + pb * pc) + -(pb * qc + pc * qb) * (qa * qc + pa * pc)
      = (pa * qb + -pb * qa) * (qc * qc - pc * pc) := by ring_uor

/-- **First-argument difference of the real binary map, cleared**: the numerator of
    `wvalR a c − wvalR b c` is `(a − b)·(1 − c²)` in unreduced cross-product form,
    `(Qsub a b).num · (qc² − pc²)` — wiring `wval_argdiff1_cleared` to an actual `Qsub` of map values.
    The toNat denominators resolve via `1+ac, 1+bc > 0`. -/
theorem wvalR_argdiff1 (a b c : Q)
    (hac : 0 < (a.den : Int) * c.den + a.num * c.num)
    (hbc : 0 < (b.den : Int) * c.den + b.num * c.num) :
    (Qsub (wvalR a c) (wvalR b c)).num
      = (Qsub a b).num * ((c.den : Int) * c.den - c.num * c.num) := by
  have hAd : ((wvalR a c).den : Int) = (a.den : Int) * c.den + a.num * c.num := by
    rw [wvalR_den]; exact Int.toNat_of_nonneg (Int.le_of_lt hac)
  have hBd : ((wvalR b c).den : Int) = (b.den : Int) * c.den + b.num * c.num := by
    rw [wvalR_den]; exact Int.toNat_of_nonneg (Int.le_of_lt hbc)
  simp only [Qsub, add, neg, wvalR_num]
  rw [hAd, hBd]
  exact wvalR_argdiff1_poly a.num (a.den : Int) b.num (b.den : Int) c.num (c.den : Int)

/-- The pure-`Int` form of `wvalR_argdiff2` (post-`simp` arrangement, clean atoms for `ring_uor`). -/
private theorem wvalR_argdiff2_poly (pa qa pc qc pd qd : Int) :
    (pa * qc + pc * qa) * (qa * qd + pa * pd) + -(pa * qd + pd * qa) * (qa * qc + pa * pc)
      = (pc * qd + -pd * qc) * (qa * qa - pa * pa) := by ring_uor

/-- **Second-argument difference of the real binary map, cleared**: the numerator of
    `wvalR a c − wvalR a d` is `(c − d)·(1 − a²)` in unreduced cross-product form,
    `(Qsub c d).num · (qa² − pa²)` (the symmetric companion of `wvalR_argdiff1`). -/
theorem wvalR_argdiff2 (a c d : Q)
    (hac : 0 < (a.den : Int) * c.den + a.num * c.num)
    (had : 0 < (a.den : Int) * d.den + a.num * d.num) :
    (Qsub (wvalR a c) (wvalR a d)).num
      = (Qsub c d).num * ((a.den : Int) * a.den - a.num * a.num) := by
  have hCd : ((wvalR a c).den : Int) = (a.den : Int) * c.den + a.num * c.num := by
    rw [wvalR_den]; exact Int.toNat_of_nonneg (Int.le_of_lt hac)
  have hDd : ((wvalR a d).den : Int) = (a.den : Int) * d.den + a.num * d.num := by
    rw [wvalR_den]; exact Int.toNat_of_nonneg (Int.le_of_lt had)
  simp only [Qsub, add, neg, wvalR_num]
  rw [hCd, hDd]
  exact wvalR_argdiff2_poly a.num (a.den : Int) c.num (c.den : Int) d.num (d.den : Int)

/-- The pure-`Int` denominator estimate behind the Lipschitz constant `4`: if both shifted
    denominators clear the half-bound `qa·qc ≤ 2·(qa·qc+pa·pc)` (which holds for `|a|,|c| ≤ ρ`,
    `ρ² ≤ ½`), then `(qc²−pc²)·qa·qb ≤ 4·D(a,c)·D(b,c)`. The chain
    `(qc²−pc²)qa·qb ≤ qc²·qa·qb = (qa·qc)(qb·qc) ≤ (2D_ac)(2D_bc) = 4 D_ac D_bc`. -/
private theorem wval_lip1_den (qa pa qb pb qc pc : Int)
    (hqa : 0 < qa) (hqb : 0 < qb) (hqc : 0 < qc)
    (hDac : qa * qc ≤ 2 * (qa * qc + pa * pc))
    (hDbc : qb * qc ≤ 2 * (qb * qc + pb * pc)) :
    (qc * qc - pc * pc) * (qa * qb) ≤ 4 * ((qa * qc + pa * pc) * (qb * qc + pb * pc)) := by
  have hacp : 0 < qa * qc := Int.mul_pos hqa hqc
  have hbcp : 0 < qb * qc := Int.mul_pos hqb hqc
  have hprod : (qa * qc) * (qb * qc)
      ≤ (2 * (qa * qc + pa * pc)) * (2 * (qb * qc + pb * pc)) :=
    Int.mul_le_mul hDac hDbc (Int.le_of_lt hbcp) (by omega)
  have hpc2 : (0 : Int) ≤ pc * pc := by rw [← Int.natAbs_mul_self]; exact Int.ofNat_nonneg _
  have hP : (0 : Int) ≤ (pc * pc) * (qa * qb) :=
    Int.mul_nonneg hpc2 (Int.le_of_lt (Int.mul_pos hqa hqb))
  have key1 : (qc * qc) * (qa * qb) - (qc * qc - pc * pc) * (qa * qb) = (pc * pc) * (qa * qb) := by
    ring_uor
  have key2 : (qc * qc) * (qa * qb) = (qa * qc) * (qb * qc) := by ring_uor
  have key3 : (2 * (qa * qc + pa * pc)) * (2 * (qb * qc + pb * pc))
      = 4 * ((qa * qc + pa * pc) * (qb * qc + pb * pc)) := by ring_uor
  omega

/-- **The denominator half-bound from the radius**: for `|a|, |c| ≤ ρ` with `ρ² ≤ ½`, the shifted
    denominator `1 + ac` clears half: `qa·qc ≤ 2·(qa·qc + pa·pc)` (i.e. `2|pa·pc| ≤ qa·qc`). This is the
    hypothesis `wval_lip1_den` needs, and the reason the binary lift requires the small-radius `ρ² ≤ ½`
    that the unary doubling also used. -/
theorem wval_halfbound (ρ a c : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num)
    (had : 0 < a.den) (hcd : 0 < c.den)
    (ha : Qle (Qabs a) ρ) (hc : Qle (Qabs c) ρ) (hρ2 : Qle (mul ρ ρ) ⟨1, 2⟩) :
    (a.den : Int) * c.den ≤ 2 * ((a.den : Int) * c.den + a.num * c.num) := by
  simp only [Qle, Qabs] at ha hc
  simp only [Qle, mul] at hρ2
  push_cast at hρ2
  have hrd : (0 : Int) < ρ.den := by exact_mod_cast hρd
  have hqa : (0 : Int) < a.den := by exact_mod_cast had
  have hqc : (0 : Int) < c.den := by exact_mod_cast hcd
  -- multiply the two abs bounds
  have hpos1 : (0 : Int) ≤ (c.num.natAbs : Int) * ρ.den :=
    Int.mul_nonneg (Int.ofNat_nonneg _) (Int.le_of_lt hrd)
  have hpos2 : (0 : Int) ≤ ρ.num * a.den := Int.mul_nonneg hρ0 (Int.le_of_lt hqa)
  have hprod : ((a.num.natAbs : Int) * ρ.den) * ((c.num.natAbs : Int) * ρ.den)
      ≤ (ρ.num * a.den) * (ρ.num * c.den) := Int.mul_le_mul ha hc hpos1 hpos2
  -- rearrange both sides (explicitly-typed ring_uor handles the cast atoms)
  have eL : ((a.num.natAbs : Int) * ρ.den) * ((c.num.natAbs : Int) * ρ.den)
      = ((a.num.natAbs : Int) * c.num.natAbs) * ((ρ.den : Int) * ρ.den) := by ring_uor
  have eR : (ρ.num * a.den) * (ρ.num * c.den)
      = (ρ.num * ρ.num) * ((a.den : Int) * c.den) := by ring_uor
  rw [eL, eR] at hprod
  -- |pa|·|pc| = |pa·pc| ; and 2ρ.num² ≤ ρ.den²
  have hnatmul : ((a.num.natAbs : Int) * c.num.natAbs) = ((a.num * c.num).natAbs : Int) := by
    rw [Int.natAbs_mul]; push_cast; ring_uor
  rw [hnatmul] at hprod
  -- 2·|pa·pc|·ρ.den² ≤ 2ρ.num²·(qa·qc) ≤ ρ.den²·(qa·qc)
  have hrd2pos : (0 : Int) < (ρ.den : Int) * ρ.den := Int.mul_pos hrd hrd
  have hqac : (0 : Int) ≤ (a.den : Int) * c.den := Int.le_of_lt (Int.mul_pos hqa hqc)
  -- from hprod: |m|·ρ.den² ≤ ρ.num²·(qa qc); ×2 with hρ2 gives 2|m|·ρ.den² ≤ ρ.den²·(qa qc)
  have hstep : (2 * ((a.num * c.num).natAbs : Int)) * ((ρ.den : Int) * ρ.den)
      ≤ ((ρ.den : Int) * ρ.den) * ((a.den : Int) * c.den) := by
    have h1 : 2 * (((a.num * c.num).natAbs : Int) * ((ρ.den : Int) * ρ.den))
        ≤ 2 * ((ρ.num * ρ.num) * ((a.den : Int) * c.den)) := by omega
    have h2 : 2 * ((ρ.num * ρ.num) * ((a.den : Int) * c.den))
        ≤ ((ρ.den : Int) * ρ.den) * ((a.den : Int) * c.den) := by
      have hmul := Int.mul_le_mul_of_nonneg_right (by omega : ρ.num * ρ.num * 2 ≤ 1 * ((ρ.den : Int) * ρ.den)) hqac
      have e2 : (ρ.num * ρ.num * 2) * ((a.den : Int) * c.den)
          = 2 * ((ρ.num * ρ.num) * ((a.den : Int) * c.den)) := by ring_uor
      have e3 : (1 * ((ρ.den : Int) * ρ.den)) * ((a.den : Int) * c.den)
          = ((ρ.den : Int) * ρ.den) * ((a.den : Int) * c.den) := by ring_uor
      rw [e2, e3] at hmul; exact hmul
    have e4 : (2 * ((a.num * c.num).natAbs : Int)) * ((ρ.den : Int) * ρ.den)
        = 2 * (((a.num * c.num).natAbs : Int) * ((ρ.den : Int) * ρ.den)) := by ring_uor
    rw [e4]; exact Int.le_trans h1 h2
  -- cancel ρ.den²: 2|m| ≤ qa·qc
  have hcancel : 2 * ((a.num * c.num).natAbs : Int) ≤ (a.den : Int) * c.den := by
    have hcomm : ((ρ.den : Int) * ρ.den) * (2 * ((a.num * c.num).natAbs : Int))
        ≤ ((ρ.den : Int) * ρ.den) * ((a.den : Int) * c.den) := by
      have e5 : ((ρ.den : Int) * ρ.den) * (2 * ((a.num * c.num).natAbs : Int))
          = (2 * ((a.num * c.num).natAbs : Int)) * ((ρ.den : Int) * ρ.den) := by ring_uor
      rw [e5]; exact hstep
    exact Int.le_of_mul_le_mul_left hcomm hrd2pos
  -- conclude via omega (natAbs of the atom a.num*c.num)
  omega

/-- **`|c| < 1` from the radius**: `pc² ≤ qc²` for `|c| ≤ ρ`, `ρ² ≤ ½` (so `ρ < 1`). -/
theorem wval_csq_le (ρ c : Q) (hρd : 0 < ρ.den) (_hρ0 : 0 ≤ ρ.num) (hcd : 0 < c.den)
    (hc : Qle (Qabs c) ρ) (hρ2 : Qle (mul ρ ρ) ⟨1, 2⟩) :
    c.num * c.num ≤ (c.den : Int) * c.den := by
  simp only [Qle, Qabs] at hc
  simp only [Qle, mul] at hρ2
  push_cast at hρ2
  have hrd : (0 : Int) < ρ.den := by exact_mod_cast hρd
  have hqc : (0 : Int) < c.den := by exact_mod_cast hcd
  -- ρ < 1: ρ.num ≤ ρ.den (from 2ρ.num² ≤ ρ.den², ρ.num ≥ 0)
  have hn2 : (0 : Int) ≤ ρ.num * ρ.num := by rw [← Int.natAbs_mul_self]; exact Int.ofNat_nonneg _
  have hρlt1 : ρ.num ≤ (ρ.den : Int) := by
    rcases Int.le_total ρ.num (ρ.den : Int) with h | h
    · exact h
    · exfalso
      have hsq : (ρ.den : Int) * ρ.den ≤ ρ.num * ρ.num :=
        Int.mul_le_mul h h (Int.le_of_lt hrd) (Int.le_trans (Int.le_of_lt hrd) h)
      have hrd2 : (0 : Int) < (ρ.den : Int) * ρ.den := Int.mul_pos hrd hrd
      omega
  -- |c|·1 ≤ ρ.num·c.den ≤ c.den·c.den ... actually |pc|·ρ.den ≤ ρ.num·qc ≤ qc·qc gives |pc| ≤ qc
  have habs : (c.num.natAbs : Int) * ρ.den ≤ ρ.num * c.den := hc
  have hpcle : (c.num.natAbs : Int) ≤ (c.den : Int) := by
    have h1 : (c.num.natAbs : Int) * ρ.den ≤ (c.den : Int) * ρ.den := by
      have : ρ.num * c.den ≤ (c.den : Int) * ρ.den := by
        have := Int.mul_le_mul_of_nonneg_right hρlt1 (Int.le_of_lt hqc)
        have e : ρ.num * (c.den : Int) ≤ (c.den : Int) * ρ.den := by
          have e2 : (ρ.den : Int) * c.den = (c.den : Int) * ρ.den := by ring_uor
          rw [← e2]; exact Int.mul_le_mul_of_nonneg_right hρlt1 (Int.le_of_lt hqc)
        exact e
      exact Int.le_trans habs this
    exact Int.le_of_mul_le_mul_right h1 hrd
  -- pc² = |pc|² ≤ qc²
  have hpc2 : c.num * c.num = (c.num.natAbs : Int) * c.num.natAbs := (Int.natAbs_mul_self' c.num).symm
  rw [hpc2]
  exact Int.mul_le_mul hpcle hpcle (Int.ofNat_nonneg _) (Int.le_of_lt hqc)

/-- **Binary Lipschitz bound, first argument**: `|wvalR a c − wvalR b c| ≤ 4·|a − b|` for `|a|,|b|,|c| ≤ ρ`
    with `ρ² ≤ ½` — the analog of `uval_lip` for the addition map. The cleared numerator
    `(a−b)·(1−c²)` (`wvalR_argdiff1`) over the denominator estimate `wval_lip1_den` (using the radius
    half-bound `wval_halfbound` and `|c| < 1` via `wval_csq_le`) yields the Lipschitz constant `4`. -/
theorem wval_lip1 (ρ a b c : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num)
    (had : 0 < a.den) (hbd : 0 < b.den) (hcd : 0 < c.den)
    (ha : Qle (Qabs a) ρ) (hb : Qle (Qabs b) ρ) (hc : Qle (Qabs c) ρ)
    (hρ2 : Qle (mul ρ ρ) ⟨1, 2⟩) :
    Qle (Qabs (Qsub (wvalR a c) (wvalR b c))) (mul ⟨4, 1⟩ (Qabs (Qsub a b))) := by
  have hqa : (0 : Int) < a.den := by exact_mod_cast had
  have hqb : (0 : Int) < b.den := by exact_mod_cast hbd
  have hqc : (0 : Int) < c.den := by exact_mod_cast hcd
  have hHac := wval_halfbound ρ a c hρd hρ0 had hcd ha hc hρ2
  have hHbc := wval_halfbound ρ b c hρd hρ0 hbd hcd hb hc hρ2
  have hac : 0 < (a.den : Int) * c.den + a.num * c.num := by have := Int.mul_pos hqa hqc; omega
  have hbc : 0 < (b.den : Int) * c.den + b.num * c.num := by have := Int.mul_pos hqb hqc; omega
  have hND := wvalR_argdiff1 a b c hac hbc
  have hcsq := wval_csq_le ρ c hρd hρ0 hcd hc hρ2
  have hden := wval_lip1_den (a.den : Int) a.num (b.den : Int) b.num (c.den : Int) c.num
    hqa hqb hqc hHac hHbc
  have hqcpc : (0 : Int) ≤ (c.den : Int) * c.den - c.num * c.num := by omega
  have hn : (0 : Int) ≤ ((Qsub a b).num.natAbs : Int) := Int.ofNat_nonneg _
  -- |S.num| = |T.num|·(qc²−pc²)
  have hSabs : ((Qsub (wvalR a c) (wvalR b c)).num.natAbs : Int)
      = ((Qsub a b).num.natAbs : Int) * ((c.den : Int) * c.den - c.num * c.num) := by
    rw [hND, Int.natAbs_mul]; push_cast; rw [Int.natAbs_of_nonneg hqcpc]
  -- ↑S.den = D_ac·D_bc
  have hSden : ((Qsub (wvalR a c) (wvalR b c)).den : Int)
      = ((a.den : Int) * c.den + a.num * c.num) * ((b.den : Int) * c.den + b.num * c.num) := by
    have e : (Qsub (wvalR a c) (wvalR b c)).den = (wvalR a c).den * (wvalR b c).den := rfl
    rw [e, Int.natCast_mul, wvalR_den, wvalR_den,
      Int.toNat_of_nonneg (Int.le_of_lt hac), Int.toNat_of_nonneg (Int.le_of_lt hbc)]
  have hTd : (Qsub a b).den = a.den * b.den := rfl
  simp only [Qle, Qabs, mul]
  rw [hSabs, hSden, hTd]
  push_cast
  -- goal: ↑|T.num|·(qc²−pc²)·(↑a.den·↑b.den) ≤ 4·↑|T.num|·(D_ac·D_bc)
  have key_le := Int.mul_le_mul_of_nonneg_left hden hn
  have eL : ((Qsub a b).num.natAbs : Int) * ((c.den : Int) * c.den - c.num * c.num)
        * (1 * ((a.den : Int) * b.den))
      = ((Qsub a b).num.natAbs : Int)
          * (((c.den : Int) * c.den - c.num * c.num) * ((a.den : Int) * b.den)) := by ring_uor
  have eR : 4 * ((Qsub a b).num.natAbs : Int)
        * (((a.den : Int) * c.den + a.num * c.num) * ((b.den : Int) * c.den + b.num * c.num))
      = ((Qsub a b).num.natAbs : Int)
          * (4 * (((a.den : Int) * c.den + a.num * c.num) * ((b.den : Int) * c.den + b.num * c.num))) := by
    ring_uor
  rw [eL, eR]
  exact Int.mul_le_mul_of_nonneg_left hden hn

/-- **`wvalR` is symmetric**: `wvalR a b = wvalR b a` (both numerator and denominator symmetric under
    `add`/`mul` commutativity). Lets the second-argument Lipschitz bound reduce to the first. -/
theorem wvalR_comm (a b : Q) : wvalR a b = wvalR b a := by
  have hn : a.num * (b.den : Int) + b.num * (a.den : Int)
      = b.num * (a.den : Int) + a.num * (b.den : Int) := by ring_uor
  have hd : (a.den : Int) * b.den + a.num * b.num
      = (b.den : Int) * a.den + b.num * a.num := by ring_uor
  unfold wvalR
  rw [hn, hd]

/-- **Binary Lipschitz bound, second argument**: `|wvalR a c − wvalR a d| ≤ 4·|c − d|` — free from
    `wval_lip1` by `wvalR_comm` (the second-argument variation is the first under symmetry). -/
theorem wval_lip2 (ρ a c d : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num)
    (had : 0 < a.den) (hcd : 0 < c.den) (hdd : 0 < d.den)
    (ha : Qle (Qabs a) ρ) (hc : Qle (Qabs c) ρ) (hd : Qle (Qabs d) ρ)
    (hρ2 : Qle (mul ρ ρ) ⟨1, 2⟩) :
    Qle (Qabs (Qsub (wvalR a c) (wvalR a d))) (mul ⟨4, 1⟩ (Qabs (Qsub c d))) := by
  rw [wvalR_comm a c, wvalR_comm a d]
  exact wval_lip1 ρ c d a hρd hρ0 hcd hdd had hc hd ha hρ2

/-- **The real binary addition map** `wvalReal s t = (s+t)/(1+s·t)`, for reals `s, t` with `|s|,|t| ≤ ρ`,
    `ρ² ≤ ½`. Diagonal `wvalR (s.seq (8n+7)) (t.seq (8n+7))`: the `8n+7` reindex absorbs the *two*
    Lipschitz-`4` terms (one per argument, via `wval_lip1`/`wval_lip2` + triangle) into the regularity
    modulus, since `8·Qbound(8n+7) = Qbound n`. The analog of `uvalReal` for the addition map. -/
def wvalReal (s t : Real) (ρ : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hρ2 : Qle (mul ρ ρ) ⟨1, 2⟩)
    (hbs : ∀ n, Qle (Qabs (s.seq n)) ρ) (hbt : ∀ n, Qle (Qabs (t.seq n)) ρ) : Real where
  seq := fun n => wvalR (s.seq (8 * n + 7)) (t.seq (8 * n + 7))
  den_pos := by
    intro n
    apply wvalR_den_pos
    have hh := wval_halfbound ρ (s.seq (8 * n + 7)) (t.seq (8 * n + 7)) hρd hρ0
      (s.den_pos _) (t.den_pos _) (hbs _) (hbt _) hρ2
    have hp := Int.mul_pos (show (0 : Int) < (s.seq (8 * n + 7)).den by exact_mod_cast s.den_pos _)
      (show (0 : Int) < (t.seq (8 * n + 7)).den by exact_mod_cast t.den_pos _)
    omega
  reg := by
    intro m n
    have hDsv : ∀ k, 0 < (wvalR (s.seq k) (t.seq k)).den := by
      intro k
      apply wvalR_den_pos
      have hh := wval_halfbound ρ (s.seq k) (t.seq k) hρd hρ0 (s.den_pos _) (t.den_pos _)
        (hbs k) (hbt k) hρ2
      have hp := Int.mul_pos (show (0 : Int) < (s.seq k).den by exact_mod_cast s.den_pos _)
        (show (0 : Int) < (t.seq k).den by exact_mod_cast t.den_pos _)
      omega
    have hDmid : 0 < (wvalR (s.seq (8 * n + 7)) (t.seq (8 * m + 7))).den := by
      apply wvalR_den_pos
      have hh := wval_halfbound ρ (s.seq (8 * n + 7)) (t.seq (8 * m + 7)) hρd hρ0
        (s.den_pos _) (t.den_pos _) (hbs _) (hbt _) hρ2
      have hp := Int.mul_pos (show (0 : Int) < (s.seq (8 * n + 7)).den by exact_mod_cast s.den_pos _)
        (show (0 : Int) < (t.seq (8 * m + 7)).den by exact_mod_cast t.den_pos _)
      omega
    show Qle (Qabs (Qsub (wvalR (s.seq (8 * m + 7)) (t.seq (8 * m + 7)))
        (wvalR (s.seq (8 * n + 7)) (t.seq (8 * n + 7))))) (add (Qbound m) (Qbound n))
    -- bound each leg by 4·(reindexed reg modulus)
    have hT1 : Qle (Qabs (Qsub (wvalR (s.seq (8 * m + 7)) (t.seq (8 * m + 7)))
          (wvalR (s.seq (8 * n + 7)) (t.seq (8 * m + 7)))))
        (mul ⟨4, 1⟩ (add (Qbound (8 * m + 7)) (Qbound (8 * n + 7)))) :=
      Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos (s.den_pos _) (s.den_pos _))))
        (wval_lip1 ρ (s.seq (8 * m + 7)) (s.seq (8 * n + 7)) (t.seq (8 * m + 7)) hρd hρ0
          (s.den_pos _) (s.den_pos _) (t.den_pos _) (hbs _) (hbs _) (hbt _) hρ2)
        (Qmul_le_mul_left (by decide) (s.reg (8 * m + 7) (8 * n + 7)))
    have hT2 : Qle (Qabs (Qsub (wvalR (s.seq (8 * n + 7)) (t.seq (8 * m + 7)))
          (wvalR (s.seq (8 * n + 7)) (t.seq (8 * n + 7)))))
        (mul ⟨4, 1⟩ (add (Qbound (8 * m + 7)) (Qbound (8 * n + 7)))) :=
      Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos (t.den_pos _) (t.den_pos _))))
        (wval_lip2 ρ (s.seq (8 * n + 7)) (t.seq (8 * m + 7)) (t.seq (8 * n + 7)) hρd hρ0
          (s.den_pos _) (t.den_pos _) (t.den_pos _) (hbs _) (hbt _) (hbt _) hρ2)
        (Qmul_le_mul_left (by decide) (t.reg (8 * m + 7) (8 * n + 7)))
    -- triangle through wvalR (s_{8n+7}) (t_{8m+7})
    refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (hDsv (8 * m + 7)) hDmid))
        (Qabs_den_pos (Qsub_den_pos hDmid (hDsv (8 * n + 7)))))
      (Qabs_sub_triangle (hDsv (8 * m + 7)) hDmid (hDsv (8 * n + 7))) ?_
    refine Qle_trans (add_den_pos
        (Qmul_den_pos Nat.one_pos (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)))
        (Qmul_den_pos Nat.one_pos (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))))
      (Qadd_le_add hT1 hT2) ?_
    apply Qeq_le
    show Qeq (add (mul ⟨4, 1⟩ (add (Qbound (8 * m + 7)) (Qbound (8 * n + 7))))
        (mul ⟨4, 1⟩ (add (Qbound (8 * m + 7)) (Qbound (8 * n + 7)))))
      (add (Qbound m) (Qbound n))
    simp only [Qeq, mul, add, Qbound]; push_cast; ring_uor

/-- **`1 + ab > 0` from the radius** (`(a.den·b.den : Int) + a.num·b.num > 0`): for `|a|,|b| ≤ ρ`,
    `ρ² ≤ ½`. The `wvalR_den_pos` / `wvalR_rel` hypothesis, derived from the radius bound — reusable
    across the diagonal-lift bricks. -/
theorem wval_inner_pos (ρ a b : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num)
    (had : 0 < a.den) (hbd : 0 < b.den) (ha : Qle (Qabs a) ρ) (hb : Qle (Qabs b) ρ)
    (hρ2 : Qle (mul ρ ρ) ⟨1, 2⟩) : 0 < (a.den : Int) * b.den + a.num * b.num := by
  have hh := wval_halfbound ρ a b hρd hρ0 had hbd ha hb hρ2
  have hp := Int.mul_pos (show (0 : Int) < a.den by exact_mod_cast had)
    (show (0 : Int) < b.den by exact_mod_cast hbd)
  omega

/-- The pure-`Int` identity behind `wvalR_rel` (clean atoms for `ring_uor`). -/
private theorem wvalR_rel_poly (pa qa pb qb : Int) :
    (1 * (qa * qb) + pa * pb * 1) * (pa * qb + pb * qa) * (qa * qb)
      = (pa * qb + pb * qa) * (1 * (qa * qb) * (qa * qb + pa * pb)) := by ring_uor

/-- **The defining relation of `wvalR`**: `(1 + a·b)·wvalR a b = a + b` (cleared), for `1 + ab > 0`.
    The binary analog of `uval_rel`. -/
theorem wvalR_rel (a b : Q) (h : 0 < (a.den : Int) * b.den + a.num * b.num) :
    Qeq (mul (add ⟨1, 1⟩ (mul a b)) (wvalR a b)) (add a b) := by
  have hbridge : ((((a.den : Int) * b.den + a.num * b.num).toNat : Int))
      = (a.den : Int) * b.den + a.num * b.num := Int.toNat_of_nonneg (Int.le_of_lt h)
  simp only [Qeq, mul, add, wvalR]
  push_cast [hbridge]
  exact wvalR_rel_poly a.num (a.den : Int) b.num (b.den : Int)

/-- The pure-`Int` core identity behind `tmap_mul_wvalR` (4 fresh vars, dodging the `ring_uor`
    cast-reifier issue): `(1 + tmap x·tmap y)·tmap(xy) = tmap x + tmap y` fully cleared. -/
private theorem tmap_wval_core (px qx py qy : Int) :
    (1 * (qx * 1 * (px * 1 + 1 * qx) * (qy * 1 * (py * 1 + 1 * qy))) +
          (px * 1 + -1 * qx) * (qx * 1) * ((py * 1 + -1 * qy) * (qy * 1)) * 1) *
        ((px * py * 1 + -1 * (qx * qy)) * (qx * qy * 1)) *
      (qx * 1 * (px * 1 + 1 * qx) * (qy * 1 * (py * 1 + 1 * qy)))
      = ((px * 1 + -1 * qx) * (qx * 1) * (qy * 1 * (py * 1 + 1 * qy)) +
          (py * 1 + -1 * qy) * (qy * 1) * (qx * 1 * (px * 1 + 1 * qx))) *
        (1 * (qx * 1 * (px * 1 + 1 * qx) * (qy * 1 * (py * 1 + 1 * qy))) *
          (qx * qy * 1 * (px * py * 1 + 1 * (qx * qy)))) := by ring_uor

/-- **The `tmap`–`wvalR` multiplication identity**: `tmap(x·y) = wvalR(tmap x, tmap y)`, the binary
    analog of `tmap_sq_uval` and the bridge from `log(xy)` to the addition map (since
    `wvalR(tmap x, tmap y) = (xy−1)/(xy+1) = tmap(xy)`). Cleared via the defining relations of both
    sides plus `Qmul_cancel_left`, exactly as `tmap_sq_uval`. -/
theorem tmap_mul_wvalR (x y : Q) (hxd : 0 < x.den) (hyd : 0 < y.den)
    (hx1 : 0 < (add x ⟨1, 1⟩).num) (hy1 : 0 < (add y ⟨1, 1⟩).num)
    (hxy1 : 0 < (add (mul x y) ⟨1, 1⟩).num)
    (hD : 0 < ((tmap x).den : Int) * (tmap y).den + (tmap x).num * (tmap y).num) :
    Qeq (tmap (mul x y)) (wvalR (tmap x) (tmap y)) := by
  have htdx : 0 < (tmap x).den := Qmul_den_pos (Qsub_den_pos hxd Nat.one_pos) (Qinv_den_pos hx1)
  have htdy : 0 < (tmap y).den := Qmul_den_pos (Qsub_den_pos hyd Nat.one_pos) (Qinv_den_pos hy1)
  have hcd : 0 < (add ⟨1, 1⟩ (mul (tmap x) (tmap y))).den :=
    add_den_pos Nat.one_pos (Qmul_den_pos htdx htdy)
  have hcn : 0 < (add ⟨1, 1⟩ (mul (tmap x) (tmap y))).num := by
    show 0 < 1 * (((tmap x).den * (tmap y).den : Nat) : Int) + (tmap x).num * (tmap y).num * 1
    push_cast; omega
  have rel1 : Qeq (mul (add ⟨1, 1⟩ (mul (tmap x) (tmap y))) (tmap (mul x y)))
      (add (tmap x) (tmap y)) := by
    have hx1c := hx1; have hy1c := hy1; have hxy1c := hxy1
    simp only [mul, add] at hx1c hy1c hxy1c
    push_cast at hx1c hy1c hxy1c
    simp only [tmap, mul, add, Qsub, neg, Qinv, Qeq]
    push_cast [Int.toNat_of_nonneg (Int.le_of_lt hx1c), Int.toNat_of_nonneg (Int.le_of_lt hy1c),
      Int.toNat_of_nonneg (Int.le_of_lt hxy1c)]
    exact tmap_wval_core x.num (x.den : Int) y.num (y.den : Int)
  exact Qmul_cancel_left hcn hcd
    (Qeq_trans (add_den_pos htdx htdy) rel1
      (Qeq_symm (wvalR_rel (tmap x) (tmap y) hD)))

/-- **The two `Rartanh` arguments of log-multiplication agree** — `tmap((xy).seq) ≈ wvalR(tmap(x.seq),
    tmap(y.seq))` pointwise, i.e. the `t`-real of `xy` equals `wvalReal` of the `t`-reals of `x, y`. The
    binary analog of `tsq_uvalReal_via`. Per index: `tmap(mul x_A y_A) ≈ wvalR(tmap x_A, tmap y_A)`
    (`tmap_mul_wvalR`), then two `wval_lip`/`tmap_lip`/reg legs (one per argument) bound the drift from
    index `A` to the `wxy`-index `B`. `ρ` (`ρ² ≤ ½`) bounds `tmap(·.seq ·)`. -/
theorem tmul_wvalReal_via (x y txy wxy : Real) (ρ : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num)
    (hρ2 : Qle (mul ρ ρ) ⟨1, 2⟩) (hxpos : ∀ n, 0 < (x.seq n).num) (hypos : ∀ n, 0 < (y.seq n).num)
    (hbx : ∀ m, Qle (Qabs (tmap (x.seq m))) ρ) (hby : ∀ m, Qle (Qabs (tmap (y.seq m))) ρ)
    (htxyseq : ∀ n, txy.seq n = tmap ((Rmul x y).seq (Rlog_R n)))
    (hwxyseq : ∀ n, wxy.seq n
      = wvalR (tmap (x.seq (Rlog_R (8 * n + 7)))) (tmap (y.seq (Rlog_R (8 * n + 7))))) :
    Req txy wxy := by
  have hxd : ∀ m, 0 < (x.seq m).den := fun m => x.den_pos m
  have hyd : ∀ m, 0 < (y.seq m).den := fun m => y.den_pos m
  have hcax : ∀ m, 0 < (add (x.seq m) ⟨1, 1⟩).num := by
    intro m; have h := hxpos m; have h2 := Int.ofNat_nonneg (x.seq m).den
    show 0 < (x.seq m).num * 1 + 1 * ((x.seq m).den : Int); omega
  have hcay : ∀ m, 0 < (add (y.seq m) ⟨1, 1⟩).num := by
    intro m; have h := hypos m; have h2 := Int.ofNat_nonneg (y.seq m).den
    show 0 < (y.seq m).num * 1 + 1 * ((y.seq m).den : Int); omega
  have hcgex : ∀ m, Qle (⟨1, 1⟩ : Q) (add (x.seq m) ⟨1, 1⟩) := by
    intro m; have h := hxpos m; have h2 := Int.ofNat_nonneg (x.seq m).den
    simp only [Qle, add, mul]; push_cast; omega
  have hcgey : ∀ m, Qle (⟨1, 1⟩ : Q) (add (y.seq m) ⟨1, 1⟩) := by
    intro m; have h := hypos m; have h2 := Int.ofNat_nonneg (y.seq m).den
    simp only [Qle, add, mul]; push_cast; omega
  have htmdx : ∀ m, 0 < (tmap (x.seq m)).den := fun m =>
    Qmul_den_pos (Qsub_den_pos (hxd m) Nat.one_pos) (Qinv_den_pos (hcax m))
  have htmdy : ∀ m, 0 < (tmap (y.seq m)).den := fun m =>
    Qmul_den_pos (Qsub_den_pos (hyd m) Nat.one_pos) (Qinv_den_pos (hcay m))
  have hcaxy : ∀ a, 0 < (add (mul (x.seq a) (y.seq a)) ⟨1, 1⟩).num := by
    intro a
    have hprodn : 0 < (x.seq a).num * (y.seq a).num := Int.mul_pos (hxpos a) (hypos a)
    have hd : 0 < (((x.seq a).den * (y.seq a).den : Nat) : Int) := by exact_mod_cast Nat.mul_pos (hxd a) (hyd a)
    show 0 < (x.seq a).num * (y.seq a).num * 1 + 1 * (((x.seq a).den * (y.seq a).den : Nat) : Int); omega
  have hDpos : ∀ i j, 0 < ((tmap (x.seq i)).den : Int) * (tmap (y.seq j)).den
      + (tmap (x.seq i)).num * (tmap (y.seq j)).num := fun i j =>
    wval_inner_pos ρ (tmap (x.seq i)) (tmap (y.seq j)) hρd hρ0 (htmdx i) (htmdy j) (hbx i) (hby j) hρ2
  refine Req_of_lin_bound (C := 32) ?_
  intro n
  rw [htxyseq n, hwxyseq n]
  let A := Ridx x y (Rlog_R n)
  let B := Rlog_R (8 * n + 7)
  show Qle (Qabs (Qsub (tmap (mul (x.seq A) (y.seq A)))
      (wvalR (tmap (x.seq B)) (tmap (y.seq B))))) (⟨32, n + 1⟩ : Q)
  have hQbA : Qle (Qbound A) (Qbound n) := by
    show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((A + 1 : Nat) : Int)
    have hge := Ridx_ge x y (Rlog_R n); have hr : n ≤ Rlog_R n := by unfold Rlog_R; omega
    rw [Int.one_mul, Int.one_mul]
    exact_mod_cast (show n + 1 ≤ A + 1 by show n + 1 ≤ Ridx x y (Rlog_R n) + 1; omega)
  have hQbB : Qle (Qbound B) (Qbound n) := by
    show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((B + 1 : Nat) : Int)
    have hr : n ≤ B := by show n ≤ Rlog_R (8 * n + 7); unfold Rlog_R; omega
    rw [Int.one_mul, Int.one_mul]; exact_mod_cast (show n + 1 ≤ B + 1 by omega)
  -- leg 1: vary the first argument (x) from A to B, second fixed at A
  have leg1 : Qle (Qabs (Qsub (wvalR (tmap (x.seq A)) (tmap (y.seq A)))
      (wvalR (tmap (x.seq B)) (tmap (y.seq A))))) (⟨16, n + 1⟩ : Q) := by
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos (htmdx A) (htmdx B))))
      (wval_lip1 ρ (tmap (x.seq A)) (tmap (x.seq B)) (tmap (y.seq A)) hρd hρ0
        (htmdx A) (htmdx B) (htmdy A) (hbx A) (hbx B) (hby A) hρ2) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos
        (Qabs_den_pos (Qsub_den_pos (hxd A) (hxd B)))))
      (Qmul_le_mul_left (by decide) (tmap_lip (x.seq A) (x.seq B) (hxd A) (hxd B)
        (hcax A) (hcax B) (hcgex A) (hcgex B))) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos
        (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))))
      (Qmul_le_mul_left (by decide) (Qmul_le_mul_left (by decide) (x.reg A B))) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos
        (add_den_pos (Qbound_den_pos n) (Qbound_den_pos n))))
      (Qmul_le_mul_left (by decide) (Qmul_le_mul_left (by decide) (Qadd_le_add hQbA hQbB))) ?_
    apply Qeq_le
    show Qeq (mul ⟨4, 1⟩ (mul ⟨2, 1⟩ (add (Qbound n) (Qbound n)))) (⟨16, n + 1⟩ : Q)
    simp only [Qeq, mul, add, Qbound]; push_cast; ring_uor
  -- leg 2: vary the second argument (y) from A to B, first fixed at B
  have leg2 : Qle (Qabs (Qsub (wvalR (tmap (x.seq B)) (tmap (y.seq A)))
      (wvalR (tmap (x.seq B)) (tmap (y.seq B))))) (⟨16, n + 1⟩ : Q) := by
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos (htmdy A) (htmdy B))))
      (wval_lip2 ρ (tmap (x.seq B)) (tmap (y.seq A)) (tmap (y.seq B)) hρd hρ0
        (htmdx B) (htmdy A) (htmdy B) (hbx B) (hby A) (hby B) hρ2) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos
        (Qabs_den_pos (Qsub_den_pos (hyd A) (hyd B)))))
      (Qmul_le_mul_left (by decide) (tmap_lip (y.seq A) (y.seq B) (hyd A) (hyd B)
        (hcay A) (hcay B) (hcgey A) (hcgey B))) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos
        (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))))
      (Qmul_le_mul_left (by decide) (Qmul_le_mul_left (by decide) (y.reg A B))) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos
        (add_den_pos (Qbound_den_pos n) (Qbound_den_pos n))))
      (Qmul_le_mul_left (by decide) (Qmul_le_mul_left (by decide) (Qadd_le_add hQbA hQbB))) ?_
    apply Qeq_le
    show Qeq (mul ⟨4, 1⟩ (mul ⟨2, 1⟩ (add (Qbound n) (Qbound n)))) (⟨16, n + 1⟩ : Q)
    simp only [Qeq, mul, add, Qbound]; push_cast; ring_uor
  -- Step A: tmap(xy) ≈ wvalR(tmap x_A, tmap y_A); then triangle through wvalR(tmap x_B, tmap y_A)
  refine Qle_trans (Qabs_den_pos (Qsub_den_pos (wvalR_den_pos _ _ (hDpos A A))
      (wvalR_den_pos _ _ (hDpos B B))))
    (Qeq_le (Qabs_Qeq (Qsub_congr (tmap_mul_wvalR (x.seq A) (y.seq A) (hxd A) (hyd A)
      (hcax A) (hcay A) (hcaxy A) (hDpos A A)) (Qeq_refl _)))) ?_
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (wvalR_den_pos _ _ (hDpos A A))
        (wvalR_den_pos _ _ (hDpos B A))))
      (Qabs_den_pos (Qsub_den_pos (wvalR_den_pos _ _ (hDpos B A)) (wvalR_den_pos _ _ (hDpos B B)))))
    (Qabs_sub_triangle (wvalR_den_pos _ _ (hDpos A A)) (wvalR_den_pos _ _ (hDpos B A))
      (wvalR_den_pos _ _ (hDpos B B))) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n)) (Qadd_le_add leg1 leg2) ?_
  apply Qeq_le; exact Qadd_same_den_loc 16 16 (n + 1)

/-- **artSum arg-variation (via wvalR)**: `|artSum(wvalR a b, M) − artSum(wvalR a' b', M)| ≤
    8·(|a−a'| + |b−b'|)` for `|a|,|b|,|a'|,|b'| ≤ ρ` (`ρ² ≤ ½`) and `|wvalR ·| ≤ σ ≤ 1/2`. The binary
    analog of `artSum_uval_argdiff`: `artSum_Lip_le` + `geoEvenSum_le_two`, then the wval map's two
    one-sided Lipschitz bounds (`wval_lip1`/`wval_lip2`) through the mixed midpoint `wvalR a' b`. -/
theorem artSum_wval_argdiff (ρ σ a b a' b' : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num)
    (hρ2 : Qle (mul ρ ρ) ⟨1, 2⟩) (hσ0 : 0 ≤ σ.num) (hσd : 0 < σ.den)
    (hσ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul σ σ)))
    (had : 0 < a.den) (hbd : 0 < b.den) (ha'd : 0 < a'.den) (hb'd : 0 < b'.den)
    (ha : Qle (Qabs a) ρ) (hb : Qle (Qabs b) ρ) (ha' : Qle (Qabs a') ρ) (hb' : Qle (Qabs b') ρ)
    (hwσ : Qle (Qabs (wvalR a b)) σ) (hw'σ : Qle (Qabs (wvalR a' b')) σ) (M : Nat) :
    Qle (Qabs (Qsub (artSum (wvalR a b) M) (artSum (wvalR a' b') M)))
        (mul ⟨8, 1⟩ (add (Qabs (Qsub a a')) (Qabs (Qsub b b')))) := by
  have hwd : 0 < (wvalR a b).den := wvalR_den_pos a b (wval_inner_pos ρ a b hρd hρ0 had hbd ha hb hρ2)
  have hw'd : 0 < (wvalR a' b').den :=
    wvalR_den_pos a' b' (wval_inner_pos ρ a' b' hρd hρ0 ha'd hb'd ha' hb' hρ2)
  have hw2d : 0 < (wvalR a' b).den :=
    wvalR_den_pos a' b (wval_inner_pos ρ a' b hρd hρ0 ha'd hbd ha' hb hρ2)
  -- Lipschitz of artSum in its argument
  refine Qle_trans (Qmul_den_pos (geoEvenSum_den_pos hσd M) (Qabs_den_pos (Qsub_den_pos hwd hw'd)))
    (artSum_Lip_le hwd hw'd hσd hwσ hw'σ M) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos hwd hw'd)))
    (Qmul_le_mul_right (Qabs_num_nonneg _) (geoEvenSum_le_two hσ0 hσd hσ2 M)) ?_
  -- |wvalR a b − wvalR a' b'| ≤ |wvalR a b − wvalR a' b| + |wvalR a' b − wvalR a' b'| ≤ 4|a−a'| + 4|b−b'|
  have hleg1 : Qle (Qabs (Qsub (wvalR a b) (wvalR a' b))) (mul ⟨4, 1⟩ (Qabs (Qsub a a'))) :=
    wval_lip1 ρ a a' b hρd hρ0 had ha'd hbd ha ha' hb hρ2
  have hleg2 : Qle (Qabs (Qsub (wvalR a' b) (wvalR a' b'))) (mul ⟨4, 1⟩ (Qabs (Qsub b b'))) :=
    wval_lip2 ρ a' b b' hρd hρ0 ha'd hbd hb'd ha' hb hb' hρ2
  refine Qle_trans (Qmul_den_pos Nat.one_pos (add_den_pos
      (Qabs_den_pos (Qsub_den_pos hwd hw2d)) (Qabs_den_pos (Qsub_den_pos hw2d hw'd))))
    (Qmul_le_mul_left (by decide) (Qabs_sub_triangle hwd hw2d hw'd)) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (add_den_pos
      (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos had ha'd)))
      (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos hbd hb'd)))))
    (Qmul_le_mul_left (by decide) (Qadd_le_add hleg1 hleg2)) ?_
  apply Qeq_le
  show Qeq (mul ⟨2, 1⟩ (add (mul ⟨4, 1⟩ (Qabs (Qsub a a'))) (mul ⟨4, 1⟩ (Qabs (Qsub b b')))))
    (mul ⟨8, 1⟩ (add (Qabs (Qsub a a')) (Qabs (Qsub b b'))))
  simp only [Qeq, mul, add]; push_cast; ring_uor

set_option maxHeartbeats 1200000 in
/-- **★ The real `artanh` ADDITION (real arguments)** — the binary analog of `Rartanh_double_real_via`.
    For nonneg reals `s, t` with `|s.seq m|, |t.seq m|, |wval(s.seq m, t.seq m)| ≤ σ` (`σ² ≤ ½`) and
    abstract diagonals `X1 = Rartanh s`, `X2 = Rartanh t`, `Y = Rartanh(wvalReal s t)` (via the seq
    equations), `X1 + X2 = Y`. Via `Req_of_lin_bound` and a 2-way split of the diagonal gap: the
    combination leg (`RartanhConst_add_wval_rho` — the exact rational addition, which inherently relates
    the depth-`n` wval to the depth-`(2n+1)` summands, so NO `Dterm`-style polynomial bound is needed)
    and the argument-variation leg (`artSum_wval_argdiff` + `s.reg`/`t.reg`). The capstone of Track-1
    log-multiplicativity. -/
theorem Rartanh_add_real_via (s t X1 X2 Y : Real) (σ : Q) (R_Y : Nat → Nat)
    (hσ0 : 0 ≤ σ.num) (hσd : 0 < σ.den) (hσlt : σ.num.toNat < σ.den)
    (hσ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul σ σ))) (hRY : ∀ n, n ≤ R_Y n)
    (hs0 : ∀ m, 0 ≤ (s.seq m).num) (ht0 : ∀ m, 0 ≤ (t.seq m).num)
    (hslt : ∀ m, (s.seq m).num.toNat < (s.seq m).den) (htlt : ∀ m, (t.seq m).num.toNat < (t.seq m).den)
    (hbs : ∀ m, Qle (Qabs (s.seq m)) σ) (hbt : ∀ m, Qle (Qabs (t.seq m)) σ)
    (hbw : ∀ i, Qle (Qabs (wvalR (s.seq i) (t.seq i))) σ)
    (hX1seq : ∀ j, X1.seq j = artSum (s.seq (Rartanh_R σ j)) (Rartanh_R σ j))
    (hX2seq : ∀ j, X2.seq j = artSum (t.seq (Rartanh_R σ j)) (Rartanh_R σ j))
    (hYseq : ∀ n, Y.seq n = artSum (wvalR (s.seq (R_Y n)) (t.seq (R_Y n))) (Rartanh_R σ n)) :
    Req (Radd X1 X2) Y := by
  have hsd : ∀ m, 0 < (s.seq m).den := fun m => s.den_pos m
  have htd : ∀ m, 0 < (t.seq m).den := fun m => t.den_pos m
  have hσhalf : Qle (mul σ σ) ⟨1, 2⟩ := by
    have h := hσ2; simp only [Qle, Qsub, add, neg, mul] at h ⊢; push_cast at h ⊢; omega
  -- Rartanh_R σ k ≥ k
  have hRge : ∀ k, k ≤ Rartanh_R σ k := by
    intro k; unfold Rartanh_R
    have hk : 1 ≤ σ.den * σ.den + 4 * σ.den := Nat.le_trans (by omega) (Nat.le_add_left _ _)
    calc k ≤ 1 * (k + 1) := by omega
      _ ≤ (σ.den * σ.den + 4 * σ.den) * (k + 1) := Nat.mul_le_mul_right _ hk
  refine Req_of_lin_bound (C := 34) ?_
  intro n
  -- term_radd = artSum(s_P,P) + artSum(t_P,P), P = Rartanh_R σ (2n+1)
  have hae : (Radd X1 X2).seq n
      = add (artSum (s.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1)))
          (artSum (t.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1))) := by
    show add (X1.seq (2 * n + 1)) (X2.seq (2 * n + 1)) = _; rw [hX1seq, hX2seq]
  rw [hae, hYseq n]
  -- den-positivities
  have hWd : 0 < (artSum (wvalR (s.seq (Rartanh_R σ (2 * n + 1))) (t.seq (Rartanh_R σ (2 * n + 1))))
      (Rartanh_R σ n)).den :=
    artSum_den_pos (wvalR_den_pos _ _ (wval_inner_pos σ _ _ hσd hσ0 (hsd _) (htd _) (hbs _) (hbt _) hσhalf)) _
  have hYd : 0 < (artSum (wvalR (s.seq (R_Y n)) (t.seq (R_Y n))) (Rartanh_R σ n)).den :=
    artSum_den_pos (wvalR_den_pos _ _ (wval_inner_pos σ _ _ hσd hσ0 (hsd _) (htd _) (hbs _) (hbt _) hσhalf)) _
  have hRd : 0 < (add (artSum (s.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1)))
      (artSum (t.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1)))).den :=
    add_den_pos (artSum_den_pos (hsd _) _) (artSum_den_pos (htd _) _)
  -- combination leg (the rational addition law at the diagonal rationals), in artSum form (defeq)
  have hcomb : Qle (Qabs (Qsub
        (artSum (wval (s.seq (Rartanh_R σ (2 * n + 1))) (t.seq (Rartanh_R σ (2 * n + 1)))) (Rartanh_R σ n))
        (add (artSum (s.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1)))
          (artSum (t.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1)))))) (⟨2, n + 1⟩ : Q) :=
    RartanhConst_add_wval_rho (s.seq (Rartanh_R σ (2 * n + 1)))
      (t.seq (Rartanh_R σ (2 * n + 1))) σ (hsd _) (hs0 _) (hslt _) (htd _) (ht0 _) (htlt _)
      hσ0 hσd hσlt (hbs _) (hbt _)
      (by rw [wval_eq_wvalR _ _ (Int.mul_nonneg (hs0 _) (ht0 _))]; exact hbw _) n
  rw [wval_eq_wvalR _ _ (Int.mul_nonneg (hs0 _) (ht0 _))] at hcomb
  -- arg-variation leg
  have hvar := artSum_wval_argdiff σ σ (s.seq (Rartanh_R σ (2 * n + 1)))
    (t.seq (Rartanh_R σ (2 * n + 1))) (s.seq (R_Y n)) (t.seq (R_Y n))
    hσd hσ0 hσhalf hσ0 hσd hσ2 (hsd _) (htd _) (hsd _) (htd _)
    (hbs _) (hbt _) (hbs _) (hbt _) (hbw _) (hbw _) (Rartanh_R σ n)
  -- Qbound reindex bounds
  have hQbP : Qle (Qbound (Rartanh_R σ (2 * n + 1))) (Qbound n) := by
    show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((Rartanh_R σ (2 * n + 1) + 1 : Nat) : Int)
    have := hRge (2 * n + 1); rw [Int.one_mul, Int.one_mul]
    exact_mod_cast (show n + 1 ≤ Rartanh_R σ (2 * n + 1) + 1 by omega)
  have hQbM : Qle (Qbound (R_Y n)) (Qbound n) := by
    show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((R_Y n + 1 : Nat) : Int)
    have := hRY n; rw [Int.one_mul, Int.one_mul]
    exact_mod_cast (show n + 1 ≤ R_Y n + 1 by omega)
  -- leg B bounded by ⟨32, n+1⟩
  have hlegB : Qle (Qabs (Qsub
        (artSum (wvalR (s.seq (Rartanh_R σ (2 * n + 1))) (t.seq (Rartanh_R σ (2 * n + 1)))) (Rartanh_R σ n))
        (artSum (wvalR (s.seq (R_Y n)) (t.seq (R_Y n))) (Rartanh_R σ n)))) (⟨32, n + 1⟩ : Q) := by
    refine Qle_trans (Qmul_den_pos Nat.one_pos (add_den_pos
        (Qabs_den_pos (Qsub_den_pos (hsd _) (hsd _))) (Qabs_den_pos (Qsub_den_pos (htd _) (htd _)))))
      hvar ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (add_den_pos
        (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))
        (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))))
      (Qmul_le_mul_left (by decide) (Qadd_le_add (s.reg _ _) (t.reg _ _))) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (add_den_pos
        (add_den_pos (Qbound_den_pos n) (Qbound_den_pos n))
        (add_den_pos (Qbound_den_pos n) (Qbound_den_pos n))))
      (Qmul_le_mul_left (by decide)
        (Qadd_le_add (Qadd_le_add hQbP hQbM) (Qadd_le_add hQbP hQbM))) ?_
    apply Qeq_le
    show Qeq (mul ⟨8, 1⟩ (add (add (Qbound n) (Qbound n)) (add (Qbound n) (Qbound n))))
      (⟨32, n + 1⟩ : Q)
    simp only [Qeq, mul, add, Qbound]; push_cast; ring_uor
  -- leg A: |term_radd − W| = |W − term_radd| ≤ ⟨2, n+1⟩
  have hlegA : Qle (Qabs (Qsub
        (add (artSum (s.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1)))
          (artSum (t.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1))))
        (artSum (wvalR (s.seq (Rartanh_R σ (2 * n + 1))) (t.seq (Rartanh_R σ (2 * n + 1)))) (Rartanh_R σ n))))
      (⟨2, n + 1⟩ : Q) := by
    rw [Qabs_Qsub_comm]; exact hcomb
  -- triangle through W and combine
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hRd hWd))
      (Qabs_den_pos (Qsub_den_pos hWd hYd)))
    (Qabs_sub_triangle hRd hWd hYd) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n)) (Qadd_le_add hlegA hlegB) ?_
  apply Qeq_le; exact Qadd_same_den_loc 2 32 (n + 1)

/-- **Log-multiplication (abstract `×2` wiring)**: from `X1 + X2 = Xadd` and `Xadd ≈ R`, the scaled
    `c·X1 + c·X2 = c·R`. The binary analog of `Rlog_double_algebra`, via `Rmul_distrib`. -/
theorem Rlog_mul_algebra (c X1 X2 Xadd R : Real)
    (hadd : Req (Radd X1 X2) Xadd) (hcong : Req Xadd R) :
    Req (Radd (Rmul c X1) (Rmul c X2)) (Rmul c R) :=
  Req_trans (Req_symm (Rmul_distrib c X1 X2)) (Rmul_congr (Req_refl c) (Req_trans hadd hcong))

/-- **Log-multiplication (abstract wiring)**: with the `t`-reals `tx, ty, txy` all at a common radius
    `σ` (`σ² ≤ ½`, non-negative sequences) and `txy ≈ wvalReal tx ty` (from `tmul_wvalReal_via`), the two
    `c·Rartanh` reals — `c·Rlog x + c·Rlog y` and `c·Rlog (xy)` — agree. Chains `Rartanh_add_real_via`
    (the real addition), `Rartanh_congr` (the argument identity), `Rlog_mul_algebra` (the `×2`
    distribution). Pure wiring, no new analysis (cf. `Rlog_sq_via`). -/
theorem Rlog_mul_via (c tx ty txy : Real) (σ : Q)
    (hσ0 : 0 ≤ σ.num) (hσd : 0 < σ.den) (hσlt : σ.num.toNat < σ.den)
    (hσhalf : Qle (mul σ σ) ⟨1, 2⟩)
    (hs0 : ∀ m, 0 ≤ (tx.seq m).num) (ht0 : ∀ m, 0 ≤ (ty.seq m).num)
    (hslt : ∀ m, (tx.seq m).num.toNat < (tx.seq m).den)
    (htlt : ∀ m, (ty.seq m).num.toNat < (ty.seq m).den)
    (hbx : ∀ m, Qle (Qabs (tx.seq m)) σ) (hby : ∀ m, Qle (Qabs (ty.seq m)) σ)
    (hbw : ∀ i, Qle (Qabs (wvalR (tx.seq i) (ty.seq i))) σ) (hbtxy : ∀ m, Qle (Qabs (txy.seq m)) σ)
    (htmul : Req txy (wvalReal tx ty σ hσd hσ0 hσhalf hbx hby)) :
    Req (Radd (Rmul c (Rartanh tx σ hσ0 hσd hσlt hbx)) (Rmul c (Rartanh ty σ hσ0 hσd hσlt hby)))
        (Rmul c (Rartanh txy σ hσ0 hσd hσlt hbtxy)) := by
  have hσ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul σ σ)) := by
    have h := hσhalf; simp only [Qle, Qsub, add, neg, mul] at h ⊢; push_cast at h ⊢; omega
  have hbW : ∀ n, Qle (Qabs ((wvalReal tx ty σ hσd hσ0 hσhalf hbx hby).seq n)) σ :=
    fun n => hbw (8 * n + 7)
  have hRY : ∀ n, n ≤ 8 * Rartanh_R σ n + 7 := by
    intro n
    have hk : 1 ≤ σ.den * σ.den + 4 * σ.den := Nat.le_trans (by omega) (Nat.le_add_left _ _)
    have : n ≤ Rartanh_R σ n := by
      unfold Rartanh_R
      calc n ≤ 1 * (n + 1) := by omega
        _ ≤ (σ.den * σ.den + 4 * σ.den) * (n + 1) := Nat.mul_le_mul_right _ hk
    omega
  have hadd : Req (Radd (Rartanh tx σ hσ0 hσd hσlt hbx) (Rartanh ty σ hσ0 hσd hσlt hby))
      (Rartanh (wvalReal tx ty σ hσd hσ0 hσhalf hbx hby) σ hσ0 hσd hσlt hbW) :=
    Rartanh_add_real_via tx ty (Rartanh tx σ hσ0 hσd hσlt hbx) (Rartanh ty σ hσ0 hσd hσlt hby)
      (Rartanh (wvalReal tx ty σ hσd hσ0 hσhalf hbx hby) σ hσ0 hσd hσlt hbW)
      σ (fun n => 8 * Rartanh_R σ n + 7) hσ0 hσd hσlt hσ2 hRY hs0 ht0 hslt htlt hbx hby hbw
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have hcong : Req (Rartanh (wvalReal tx ty σ hσd hσ0 hσhalf hbx hby) σ hσ0 hσd hσlt hbW)
      (Rartanh txy σ hσ0 hσd hσlt hbtxy) :=
    Rartanh_congr (wvalReal tx ty σ hσd hσ0 hσhalf hbx hby) txy σ hσ0 hσd hσlt hσ2 hbW hbtxy
      (Req_symm htmul)
  exact Rlog_mul_algebra c (Rartanh tx σ hσ0 hσd hσlt hbx) (Rartanh ty σ hσ0 hσd hσlt hby)
    (Rartanh (wvalReal tx ty σ hσd hσ0 hσhalf hbx hby) σ hσ0 hσd hσlt hbW)
    (Rartanh txy σ hσ0 hσd hσlt hbtxy) hadd hcong

/-- **`wvalR(tmap a, tmap b)` is bounded by `tmap(Ma·Mb)`** — the `hbw` bound for the concrete
    `Rlog_mul`, via the identity `wvalR(tmap a, tmap b) = tmap(a·b)` (`tmap_mul_wvalR`) and `tmap`'s
    monotone bound `tmap_abs_le` (since `a·b ≤ Ma·Mb`). This is why the addition map stays in-radius:
    the combined argument is `tmap` of the product. -/
theorem wvalR_tmap_bound (a b Ma Mb : Q) (had : 0 < a.den) (hbd : 0 < b.den)
    (ha1 : 0 < (add a ⟨1, 1⟩).num) (hb1 : 0 < (add b ⟨1, 1⟩).num)
    (hab1 : 0 < (add (mul a b) ⟨1, 1⟩).num)
    (hD : 0 < ((tmap a).den : Int) * (tmap b).den + (tmap a).num * (tmap b).num)
    (hMabd : 0 < (mul Ma Mb).den) (hMab1 : 0 < (add (mul Ma Mb) ⟨1, 1⟩).num)
    (habM : Qle (mul a b) (mul Ma Mb)) (habMge : Qle (⟨1, 1⟩ : Q) (mul (mul a b) (mul Ma Mb))) :
    Qle (Qabs (wvalR (tmap a) (tmap b))) (tmap (mul Ma Mb)) := by
  have hbridge : Qeq (tmap (mul a b)) (wvalR (tmap a) (tmap b)) :=
    tmap_mul_wvalR a b had hbd ha1 hb1 hab1 hD
  refine Qle_trans (Qabs_den_pos (Qmul_den_pos (Qsub_den_pos (Qmul_den_pos had hbd) Nat.one_pos)
      (Qinv_den_pos hab1)))
    (Qeq_le (Qabs_Qeq (Qeq_symm hbridge)))
    (tmap_abs_le (Qmul_den_pos had hbd) hMabd hab1 hMab1 habM habMge)

/-- **`tmap` maps `[1,∞)` into `[0,1)`**: for `q ≥ 1`, `0 ≤ (tmap q).num` and `(tmap q).num.toNat <
    (tmap q).den` (i.e. `0 ≤ tmap q < 1`). The sign+bound facts the addition law needs of the `Rlog`
    `artanh` arguments `tmap(x.seq)` when `x.seq ≥ 1` (discharges `Rlog_mul_via`'s `hs0`/`hslt`). -/
theorem tmap_nonneg_lt_one (q : Q) (hqd : 0 < q.den) (hq : Qle (⟨1, 1⟩ : Q) q) :
    0 ≤ (tmap q).num ∧ (tmap q).num.toNat < (tmap q).den := by
  have hqn : (q.den : Int) ≤ q.num := by have := hq; simp only [Qle] at this; omega
  have hd0 : (0 : Int) < q.den := by exact_mod_cast hqd
  have hnum : (tmap q).num = (q.num - (q.den : Int)) * q.den := by
    unfold tmap mul Qsub Qinv add neg; push_cast; ring_uor
  have hdenI : ((tmap q).den : Int) = (q.den : Int) * (q.num + q.den) := by
    show (((tmap q).den : Nat) : Int) = _
    unfold tmap mul Qsub Qinv add neg
    push_cast [Int.toNat_of_nonneg (show (0 : Int) ≤ q.num * 1 + 1 * (q.den : Int) by omega)]
    ring_uor
  have hnn : 0 ≤ (tmap q).num := by rw [hnum]; exact Int.mul_nonneg (by omega) (Int.ofNat_nonneg _)
  refine ⟨hnn, ?_⟩
  have htn : ((tmap q).num.toNat : Int) = (q.num - (q.den : Int)) * q.den := by
    rw [Int.toNat_of_nonneg hnn]; exact hnum
  have hlt : ((tmap q).num.toNat : Int) < ((tmap q).den : Int) := by
    rw [htn, hdenI]
    have key : (q.den : Int) * (q.num + q.den) - (q.num - q.den) * q.den = 2 * (q.den * q.den) := by
      ring_uor
    have hpos : (0 : Int) < 2 * (q.den * q.den) := by have := Int.mul_pos hd0 hd0; omega
    omega
  exact_mod_cast hlt

/-- **The `hbw` bound packaged for `[1,B]` arguments**: for `a, b ∈ [1, B]`,
    `|wvalR(tmap a, tmap b)| ≤ ρ_{B²}` (`= tmap(B²)`). Packages `wvalR_tmap_bound`'s sub-hypotheses from
    `1 ≤ a, b ≤ B`; this is `Rlog_mul`'s `hbw` per index. -/
theorem wvalR_tmap_seq_bound (a b B : Q) (had : 0 < a.den) (hbd : 0 < b.den) (hBd : 0 < B.den)
    (ha1 : Qle (⟨1, 1⟩ : Q) a) (hb1 : Qle (⟨1, 1⟩ : Q) b) (haB : Qle a B) (hbB : Qle b B)
    (hBge : Qle (⟨1, 1⟩ : Q) B) :
    Qle (Qabs (wvalR (tmap a) (tmap b)))
        (⟨(mul B B).num - ((mul B B).den : Int), (mul B B).num.toNat + (mul B B).den⟩ : Q) := by
  have ha0 : 0 ≤ a.num := by have := ha1; simp only [Qle] at this; omega
  have hb0 : 0 ≤ b.num := by have := hb1; simp only [Qle] at this; omega
  have hBn : 0 ≤ B.num := by have := hBge; simp only [Qle] at this; omega
  have ha1' : 0 < (add a ⟨1, 1⟩).num := by
    show 0 < a.num * 1 + 1 * (a.den : Int); have := Int.ofNat_nonneg a.den; omega
  have hb1' : 0 < (add b ⟨1, 1⟩).num := by
    show 0 < b.num * 1 + 1 * (b.den : Int); have := Int.ofNat_nonneg b.den; omega
  have hab1 : 0 < (add (mul a b) ⟨1, 1⟩).num := by
    show 0 < a.num * b.num * 1 + 1 * ((a.den * b.den : Nat) : Int)
    have h1 : 0 ≤ a.num * b.num := Int.mul_nonneg ha0 hb0
    have h2 : 0 < ((a.den * b.den : Nat) : Int) := by exact_mod_cast Nat.mul_pos had hbd
    omega
  have htad : 0 < (tmap a).den := Qmul_den_pos (Qsub_den_pos had Nat.one_pos) (Qinv_den_pos ha1')
  have htbd : 0 < (tmap b).den := Qmul_den_pos (Qsub_den_pos hbd Nat.one_pos) (Qinv_den_pos hb1')
  have hta0 : 0 ≤ (tmap a).num := (tmap_nonneg_lt_one a had ha1).1
  have htb0 : 0 ≤ (tmap b).num := (tmap_nonneg_lt_one b hbd hb1).1
  have hD : 0 < ((tmap a).den : Int) * (tmap b).den + (tmap a).num * (tmap b).num := by
    have hdd : 0 < ((tmap a).den : Int) * (tmap b).den :=
      Int.mul_pos (by exact_mod_cast htad) (by exact_mod_cast htbd)
    have hnn : 0 ≤ (tmap a).num * (tmap b).num := Int.mul_nonneg hta0 htb0
    omega
  have hB2d : 0 < (mul B B).den := Qmul_den_pos hBd hBd
  have hB2n : 0 ≤ (mul B B).num := Int.mul_nonneg hBn hBn
  have hMab1 : 0 < (add (mul B B) ⟨1, 1⟩).num := by
    show 0 < B.num * B.num * 1 + 1 * ((B.den * B.den : Nat) : Int)
    have h2 : 0 < ((B.den * B.den : Nat) : Int) := by exact_mod_cast Nat.mul_pos hBd hBd
    have h1 : 0 ≤ B.num * B.num := Int.mul_nonneg hBn hBn; omega
  have habM : Qle (mul a b) (mul B B) := Qmul_le_mul had hBd hbd ha0 hb0 haB hbB
  have habMge : Qle (⟨1, 1⟩ : Q) (mul (mul a b) (mul B B)) := by
    have hab1ge : Qle (⟨1, 1⟩ : Q) (mul a b) :=
      Qle_trans (by decide) (Qeq_le (by decide : Qeq (⟨1, 1⟩ : Q) (mul ⟨1, 1⟩ ⟨1, 1⟩)))
        (Qmul_le_mul Nat.one_pos had Nat.one_pos (by decide) (by decide) ha1 hb1)
    have hB2ge : Qle (⟨1, 1⟩ : Q) (mul B B) :=
      Qle_trans (by decide) (Qeq_le (by decide : Qeq (⟨1, 1⟩ : Q) (mul ⟨1, 1⟩ ⟨1, 1⟩)))
        (Qmul_le_mul Nat.one_pos hBd Nat.one_pos (by decide) (by decide) hBge hBge)
    exact Qle_trans (by decide) (Qeq_le (by decide : Qeq (⟨1, 1⟩ : Q) (mul ⟨1, 1⟩ ⟨1, 1⟩)))
      (Qmul_le_mul Nat.one_pos (Qmul_den_pos had hbd) Nat.one_pos (by decide) (by decide)
        hab1ge hB2ge)
  exact Qle_trans (Qmul_den_pos (Qsub_den_pos hB2d Nat.one_pos) (Qinv_den_pos hMab1))
    (wvalR_tmap_bound a b B B had hbd ha1' hb1' hab1 hD hB2d hMab1 habM habMge)
    (Qeq_le (tmap_M_eq hB2d hB2n))

set_option maxHeartbeats 1600000 in
/-- **★ Real log-multiplicativity** `Rlog(x·y) = Rlog x + Rlog y` (binary analog of `Rlog_sq`). For
    `x, y` presented in `[1,B]` *pointwise* (`x.seq, y.seq ≥ 1`, so the `artanh` arguments are
    non-negative) at small radius, the two `Rlog`s agree. Unfolds via `Rlog_eq_Rmul`, aligns
    `ρ_B → σ = ρ_{B²}` via `Rartanh_radius_indep`, and applies `Rlog_mul_via` — `hs0`/`hslt` from
    `tmap_nonneg_lt_one`, `hbw` from `wvalR_tmap_seq_bound`, `htmul` from `tmul_wvalReal_via`
    (`wxy := wvalReal tx ty`, defeq), `t`-bounds from `Rlog_tbound`. `log(xy)=log x+log y` is what
    `Clog` additivity needs; the capstone consumer of the real-artanh-addition substrate. -/
theorem Rlog_mul (x y : Real) (B : Q) (hBd : 0 < B.den) (hBge : Qle (⟨1, 1⟩ : Q) B)
    (hxpos : ∀ n, 0 < (x.seq n).num) (hxhiB : ∀ n, Qle (x.seq n) B)
    (hxloB : ∀ n, Qle (⟨1, 1⟩ : Q) (mul (x.seq n) B)) (hxge1 : ∀ n, Qle (⟨1, 1⟩ : Q) (x.seq n))
    (hypos : ∀ n, 0 < (y.seq n).num) (hyhiB : ∀ n, Qle (y.seq n) B)
    (hyloB : ∀ n, Qle (⟨1, 1⟩ : Q) (mul (y.seq n) B)) (hyge1 : ∀ n, Qle (⟨1, 1⟩ : Q) (y.seq n))
    (hB2d : 0 < (mul B B).den) (hB2ge : Qle (⟨1, 1⟩ : Q) (mul B B))
    (hxypos : ∀ n, 0 < ((Rmul x y).seq n).num) (hxyhi : ∀ n, Qle ((Rmul x y).seq n) (mul B B))
    (hxylo : ∀ n, Qle (⟨1, 1⟩ : Q) (mul ((Rmul x y).seq n) (mul B B)))
    (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩
              ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩)))
    (hρσ : Qle (⟨B.num - (B.den : Int), B.num.toNat + B.den⟩ : Q)
              (⟨(mul B B).num - ((mul B B).den : Int), (mul B B).num.toNat + (mul B B).den⟩ : Q))
    (hσhalf : Qle (mul ⟨(mul B B).num - ((mul B B).den : Int), (mul B B).num.toNat + (mul B B).den⟩
              ⟨(mul B B).num - ((mul B B).den : Int), (mul B B).num.toNat + (mul B B).den⟩) ⟨1, 2⟩) :
    Req (Radd (Rlog x B hBd hBge hxpos hxhiB hxloB) (Rlog y B hBd hBge hypos hyhiB hyloB))
        (Rlog (Rmul x y) (mul B B) hB2d hB2ge hxypos hxyhi hxylo) := by
  obtain ⟨hBn, hB1, hρ0, hρd, hρlt, hρ1⟩ := Rlog_radius_facts B hBd hBge
  obtain ⟨hB2n, hB21, hσ0, hσd, hσlt, hσ1⟩ := Rlog_radius_facts (mul B B) hB2d hB2ge
  have hden_x : ∀ n, 0 < (Rlog_seq x n).den := fun n => Qmul_den_pos
    (Qsub_den_pos (x.den_pos _) Nat.one_pos) (Qinv_den_pos (by
      have := hxpos (Rlog_R n); have h := Int.ofNat_nonneg (x.seq (Rlog_R n)).den
      show 0 < (x.seq (Rlog_R n)).num * 1 + 1 * ((x.seq (Rlog_R n)).den : Int); omega))
  have hden_y : ∀ n, 0 < (Rlog_seq y n).den := fun n => Qmul_den_pos
    (Qsub_den_pos (y.den_pos _) Nat.one_pos) (Qinv_den_pos (by
      have := hypos (Rlog_R n); have h := Int.ofNat_nonneg (y.seq (Rlog_R n)).den
      show 0 < (y.seq (Rlog_R n)).num * 1 + 1 * ((y.seq (Rlog_R n)).den : Int); omega))
  have hden_xy : ∀ n, 0 < (Rlog_seq (Rmul x y) n).den := fun n => Qmul_den_pos
    (Qsub_den_pos ((Rmul x y).den_pos _) Nat.one_pos) (Qinv_den_pos (by
      have := hxypos (Rlog_R n); have h := Int.ofNat_nonneg ((Rmul x y).seq (Rlog_R n)).den
      show 0 < ((Rmul x y).seq (Rlog_R n)).num * 1 + 1 * (((Rmul x y).seq (Rlog_R n)).den : Int); omega))
  have hbtρx := Rlog_tbound x B hBd hBn hB1 hxhiB hxloB hxpos
  have hbtρy := Rlog_tbound y B hBd hBn hB1 hyhiB hyloB hypos
  have hbtσxy := Rlog_tbound (Rmul x y) (mul B B) hB2d hB2n hB21 hxyhi hxylo hxypos
  have hbxσ : ∀ k, Qle (Qabs (tmap (x.seq k))) (⟨(mul B B).num - ((mul B B).den : Int),
      (mul B B).num.toNat + (mul B B).den⟩ : Q) := fun k => Qle_trans hρd (hbtρx k) hρσ
  have hbyσ : ∀ k, Qle (Qabs (tmap (y.seq k))) (⟨(mul B B).num - ((mul B B).den : Int),
      (mul B B).num.toNat + (mul B B).den⟩ : Q) := fun k => Qle_trans hρd (hbtρy k) hρσ
  rw [Rlog_eq_Rmul x B hBd hBge hxpos hxhiB hxloB hden_x hρ0 hρd hρlt (fun n => hbtρx (Rlog_R n)),
    Rlog_eq_Rmul y B hBd hBge hypos hyhiB hyloB hden_y hρ0 hρd hρlt (fun n => hbtρy (Rlog_R n)),
    Rlog_eq_Rmul (Rmul x y) (mul B B) hB2d hB2ge hxypos hxyhi hxylo hden_xy hσ0 hσd hσlt
      (fun n => hbtσxy (Rlog_R n))]
  have hradx : Req (Rartanh ⟨Rlog_seq x, Rlog_regular x hxpos, hden_x⟩
        ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩ hρ0 hρd hρlt (fun n => hbtρx (Rlog_R n)))
      (Rartanh ⟨Rlog_seq x, Rlog_regular x hxpos, hden_x⟩
        ⟨(mul B B).num - ((mul B B).den : Int), (mul B B).num.toNat + (mul B B).den⟩
        hσ0 hσd hσlt (fun n => hbxσ (Rlog_R n))) :=
    Rartanh_radius_indep ⟨Rlog_seq x, Rlog_regular x hxpos, hden_x⟩ _ _
      ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩
      ⟨(mul B B).num - ((mul B B).den : Int), (mul B B).num.toNat + (mul B B).den⟩
      ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩ hρd hσd hρ0 hρd hρlt hρ2
      (fun n => hbtρx (Rlog_R n)) (fun _ => rfl) (fun _ => rfl)
  have hrady : Req (Rartanh ⟨Rlog_seq y, Rlog_regular y hypos, hden_y⟩
        ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩ hρ0 hρd hρlt (fun n => hbtρy (Rlog_R n)))
      (Rartanh ⟨Rlog_seq y, Rlog_regular y hypos, hden_y⟩
        ⟨(mul B B).num - ((mul B B).den : Int), (mul B B).num.toNat + (mul B B).den⟩
        hσ0 hσd hσlt (fun n => hbyσ (Rlog_R n))) :=
    Rartanh_radius_indep ⟨Rlog_seq y, Rlog_regular y hypos, hden_y⟩ _ _
      ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩
      ⟨(mul B B).num - ((mul B B).den : Int), (mul B B).num.toNat + (mul B B).den⟩
      ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩ hρd hσd hρ0 hρd hρlt hρ2
      (fun n => hbtρy (Rlog_R n)) (fun _ => rfl) (fun _ => rfl)
  have hvia := Rlog_mul_via (ofQ (⟨2, 1⟩ : Q) (by decide))
    ⟨Rlog_seq x, Rlog_regular x hxpos, hden_x⟩ ⟨Rlog_seq y, Rlog_regular y hypos, hden_y⟩
    ⟨Rlog_seq (Rmul x y), Rlog_regular (Rmul x y) hxypos, hden_xy⟩
    ⟨(mul B B).num - ((mul B B).den : Int), (mul B B).num.toNat + (mul B B).den⟩
    hσ0 hσd hσlt hσhalf
    (fun m => (tmap_nonneg_lt_one (x.seq (Rlog_R m)) (x.den_pos _) (hxge1 (Rlog_R m))).1)
    (fun m => (tmap_nonneg_lt_one (y.seq (Rlog_R m)) (y.den_pos _) (hyge1 (Rlog_R m))).1)
    (fun m => (tmap_nonneg_lt_one (x.seq (Rlog_R m)) (x.den_pos _) (hxge1 (Rlog_R m))).2)
    (fun m => (tmap_nonneg_lt_one (y.seq (Rlog_R m)) (y.den_pos _) (hyge1 (Rlog_R m))).2)
    (fun m => hbxσ (Rlog_R m)) (fun m => hbyσ (Rlog_R m))
    (fun i => wvalR_tmap_seq_bound (x.seq (Rlog_R i)) (y.seq (Rlog_R i)) B (x.den_pos _) (y.den_pos _)
      hBd (hxge1 (Rlog_R i)) (hyge1 (Rlog_R i)) (hxhiB (Rlog_R i)) (hyhiB (Rlog_R i)) hBge)
    (fun m => hbtσxy (Rlog_R m))
    (tmul_wvalReal_via x y ⟨Rlog_seq (Rmul x y), Rlog_regular (Rmul x y) hxypos, hden_xy⟩
      (wvalReal ⟨Rlog_seq x, Rlog_regular x hxpos, hden_x⟩ ⟨Rlog_seq y, Rlog_regular y hypos, hden_y⟩
        ⟨(mul B B).num - ((mul B B).den : Int), (mul B B).num.toNat + (mul B B).den⟩
        hσd hσ0 hσhalf (fun m => hbxσ (Rlog_R m)) (fun m => hbyσ (Rlog_R m)))
      ⟨(mul B B).num - ((mul B B).den : Int), (mul B B).num.toNat + (mul B B).den⟩
      hσd hσ0 hσhalf hxpos hypos hbxσ hbyσ (fun _ => rfl) (fun _ => rfl))
  exact Req_trans
    (Radd_congr (Rmul_congr (Req_refl _) hradx) (Rmul_congr (Req_refl _) hrady)) hvia

-- ===========================================================================
-- The arctan ADDITION map `vval a b = (a+b)/(1−ab)` (the `Carg`/`arg` analog of `wvalR`), for the
-- forthcoming `Clog` additivity (imaginary part `arg(zw) = arg z + arg w`). The sign flip `1−ab`
-- (vs `wvalR`'s `1+ab`) is the difference between `arctan` (oscillatory) and `artanh`. The cleared
-- one-sided difference factors as `(Δ-cross)·(1 + other²)` (vs `wvalR`'s `1 − other²`): the certified
-- Lipschitz core. (The combination ENGINE differs: artanh had the real identity exp(2·artanh τ) =
-- (1+τ)/(1−τ); arctan has no real-exponential engine, so its addition awaits a tangent/complex route.)
-- ===========================================================================

/-- **The `arctan`/`tan` addition map** `vval a b = (a+b)/(1−ab)`, division-free (numerator
    `pa·qb + pb·qa`, denominator `qa·qb − pa·pb`, the latter under `.toNat` — positive when `ab < 1`). -/
def vval (a b : Q) : Q :=
  ⟨a.num * (b.den : Int) + b.num * (a.den : Int), ((a.den : Int) * b.den - a.num * b.num).toNat⟩

@[simp] theorem vval_num (a b : Q) :
    (vval a b).num = a.num * (b.den : Int) + b.num * (a.den : Int) := rfl
@[simp] theorem vval_den (a b : Q) :
    (vval a b).den = ((a.den : Int) * b.den - a.num * b.num).toNat := rfl

/-- **`vval a b` has positive denominator** when `1 − ab > 0` (`(a.den·b.den : Int) − a.num·b.num > 0`),
    which holds for `|a·b| < 1`. -/
theorem vval_den_pos (a b : Q) (h : 0 < (a.den : Int) * b.den - a.num * b.num) :
    0 < (vval a b).den := by rw [vval_den]; omega

/-- **Binary cleared difference, first argument** for the `arctan` map: `N(a,c)·D(b,c) − N(b,c)·D(a,c)
    = (pa·qb − pb·qa)·(qc² + pc²)` where `N(x,y) = px·qy+py·qx`, `D(x,y) = qx·qy − px·py`. The factor is
    `1 + c²` (vs `wvalR`'s `1 − c²`), so the one-sided variation is Lipschitz with constant `1 + c²`.
    Certified by `ring_uor`. -/
theorem vval_argdiff1_cleared (pa qa pb qb pc qc : Int) :
    (pa * qc + pc * qa) * (qb * qc - pb * pc) - (pb * qc + pc * qb) * (qa * qc - pa * pc)
      = (pa * qb - pb * qa) * (qc * qc + pc * pc) := by ring_uor

/-- **Binary cleared difference, second argument** for the `arctan` map (symmetric companion):
    `(pc·qd − pd·qc)·(qa² + pa²)`. Certified by `ring_uor`. -/
theorem vval_argdiff2_cleared (pa qa pc qc pd qd : Int) :
    (pa * qc + pc * qa) * (qa * qd - pa * pd) - (pa * qd + pd * qa) * (qa * qc - pa * pc)
      = (pc * qd - pd * qc) * (qa * qa + pa * pa) := by ring_uor

end UOR.Bridge.F1Square.Analysis
