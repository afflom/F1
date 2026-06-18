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

end UOR.Bridge.F1Square.Analysis
