import F1Square.Analysis.ClogAddBounded
import F1Square.Analysis.Gamma

/-!
# Signed-τ artanh/exp substrate — toward general-modulus `Rlog`/`Clog` additivity

The bounded-modulus discharge (`RlogMulPos`, `ClogAddBounded`) requires squared moduli `≥ 1`
(so the `tmap` arguments are `≥ 0`). Extending to the symmetric band `[1/B, B]` (moduli near 1,
above *and* below) needs the artanh/exp identities for **signed** arguments.

The key observation that sidesteps re-deriving the `t≥0` corner bounds: `exp(2·artanh τ) =
(1+τ)/(1−τ)` for `τ < 0` follows from the nonnegative case by **oddness**
(`artanh(−σ) = −artanh σ`, `Rartanh_neg`) and **exp-of-negation** (`exp(−x)·exp(x) = 1`,
`RexpReal_add`), with the addition law lifted through `RexpReal_inj_gen` (no nonneg restriction).

This file builds that substrate bottom-up.
-/

namespace UOR.Bridge.F1Square.Analysis

/-- **`artanh` is odd**: `Rartanh(−t) = −Rartanh t`. Per diagonal index the partial sum negates
    (`artSum_neg`), since the artanh series has only odd-degree terms. The bound for `−t` follows
    from the bound for `t` (`Qabs_neg`). -/
theorem Rartanh_neg (t : Real) (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs (t.seq n)) ρ)
    (hb' : ∀ n, Qle (Qabs ((Rneg t).seq n)) ρ) :
    Req (Rartanh (Rneg t) ρ hρ0 hρd hlt hb') (Rneg (Rartanh t ρ hρ0 hρd hlt hb)) := by
  refine Req_of_seq_Qeq (fun j => ?_)
  show Qeq (artSum ((Rneg t).seq (Rartanh_R ρ j)) (Rartanh_R ρ j))
        (neg (artSum (t.seq (Rartanh_R ρ j)) (Rartanh_R ρ j)))
  exact artSum_neg (t.den_pos _) (Rartanh_R ρ j)

/-- **`artanh` of a negated rational constant**: `RartanhConst(−τ) = −RartanhConst τ` (at any valid
    radius). Per-diagonal `artSum (neg τ) N = neg(artSum τ N)` (`artSum_neg`); no small-radius needed. -/
theorem RartanhConst_neg (τ ρ : Q) (hτd : 0 < τ.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hρlt : ρ.num.toNat < ρ.den) (hb : Qle (Qabs τ) ρ) (hbn : Qle (Qabs (neg τ)) ρ) :
    Req (RartanhConst (neg τ) ρ (by exact hτd) hρ0 hρd hρlt hbn)
        (Rneg (RartanhConst τ ρ hτd hρ0 hρd hρlt hb)) := by
  refine Req_of_seq_Qeq (fun j => ?_)
  show Qeq (artSum (neg τ) (Rartanh_R ρ j)) (neg (artSum τ (Rartanh_R ρ j)))
  exact artSum_neg hτd (Rartanh_R ρ j)

/-- **`2·artanh` of a negated rational constant**: `TwoArtanhConst(−τ) = −TwoArtanhConst τ`. -/
theorem TwoArtanhConst_neg (τ ρ : Q) (hτd : 0 < τ.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hρlt : ρ.num.toNat < ρ.den) (hb : Qle (Qabs τ) ρ) (hbn : Qle (Qabs (neg τ)) ρ) :
    Req (TwoArtanhConst (neg τ) ρ (by exact hτd) hρ0 hρd hρlt hbn)
        (Rneg (TwoArtanhConst τ ρ hτd hρ0 hρd hρlt hb)) :=
  Req_trans (Rmul_congr (Req_refl _) (RartanhConst_neg τ ρ hτd hρ0 hρd hρlt hb hbn))
    (Rmul_neg_right (ofQ ⟨2, 1⟩ (by decide)) (RartanhConst τ ρ hτd hρ0 hρd hρlt hb))

set_option maxHeartbeats 800000 in
/-- **★ The signed exp/artanh identity** `exp(2·artanh τ) = (1+τ)/(1−τ)` for `τ < 0`, derived from the
    nonnegative case (`hσid`, supplied for `σ = −τ > 0`) by oddness + exp-of-negation — *no* re-derivation
    of the `t ≥ 0` corner bounds. With `gσ = (1+σ)/(1−σ) > 1` (`hgσwit`) and `gτ·gσ = 1` (`hrecip`,
    i.e. `gτ = 1/gσ = (1+τ)/(1−τ)`): `exp(2artanh τ) = exp(−2artanh σ) = 1/exp(2artanh σ) = 1/gσ = gτ`. -/
theorem Rexp_TwoArtanh_of_neg (τ ρ gσ gτ : Q) (hτd : 0 < τ.den)
    (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρlt : ρ.num.toNat < ρ.den)
    (hb : Qle (Qabs τ) ρ) (hbn : Qle (Qabs (neg τ)) ρ)
    (hgσd : 0 < gσ.den) (hgτd : 0 < gτ.den)
    (hgσwit : Qlt (Qbound 0) gσ) (hrecip : Qeq (mul gτ gσ) ⟨1, 1⟩)
    (hσid : Req (RexpReal (TwoArtanhConst (neg τ) ρ (by exact hτd) hρ0 hρd hρlt hbn)) (ofQ gσ hgσd)) :
    Req (RexpReal (TwoArtanhConst τ ρ hτd hρ0 hρd hρlt hb)) (ofQ gτ hgτd) := by
  let Y := TwoArtanhConst (neg τ) ρ (by exact hτd) hρ0 hρd hρlt hbn
  let Yτ := TwoArtanhConst τ ρ hτd hρ0 hρd hρlt hb
  have hA : Req Y (Rneg Yτ) := TwoArtanhConst_neg τ ρ hτd hρ0 hρd hρlt hb hbn
  have htac : Req Yτ (Rneg Y) := Req_symm (Req_trans (Rneg_congr hA) (Rneg_neg Yτ))
  have hsum0 : Req (Radd (Rneg Y) Y) zero := Req_trans (Radd_comm (Rneg Y) Y) (Radd_neg Y)
  have hprod1 : Req (Rmul (RexpReal (Rneg Y)) (RexpReal Y)) one :=
    Req_trans (Req_symm (RexpReal_add (Rneg Y) Y))
      (Req_trans (RexpReal_congr hsum0) RexpReal_zero)
  have hprodσ : Req (Rmul (RexpReal (Rneg Y)) (ofQ gσ hgσd)) one :=
    Req_trans (Rmul_congr (Req_refl _) (Req_symm hσid)) hprod1
  have hprodgτ : Req (Rmul (ofQ gτ hgτd) (ofQ gσ hgσd)) one :=
    Req_trans (Rmul_ofQ_ofQ hgτd hgσd) (ofQ_congr (Qmul_den_pos hgτd hgσd) (by decide) hrecip)
  have hk : Qlt (Qbound 0) ((ofQ gσ hgσd).seq 0) := hgσwit
  have hcancel : Req (RexpReal (Rneg Y)) (ofQ gτ hgτd) :=
    Rmul_right_cancel hk (Req_trans hprodσ (Req_symm hprodgτ))
  exact Req_trans (RexpReal_congr htac) hcancel

/-- Pure-`Int` multiplicativity identity behind the signed `hg`: `(1+c)/(1−c) = (1+a)/(1−a)·(1+b)/(1−b)`
    cleared, where `c = wvalR a b` has `(num,den) = (pa qb+pb qa, qa qb+pa pb)`. -/
private theorem wvalR_hg_poly (pa qa pb qb : Int) :
    ((qa * qb + pa * pb) + (pa * qb + pb * qa)) * ((qa - pa) * (qb - pb))
      = ((qa + pa) * (qb + pb)) * ((qa - pa) * (qb - pb)) := by ring_uor

/-- **Signed `hg` multiplicativity** for the normalized `(den+num)/(den−num)` exp-values: with
    `c = wvalR a b`, `gC = gA·gB`. The signed analog of `wval_hg`, using the `(·.den−·.num).toNat`
    (Int-toNat) dens that match `Rexp_TwoArtanh_signed_rho`'s output. Requires `|a|, |b| < 1`
    (`a.num < a.den`, `−a.den < a.num`, etc.) and `1 + ab > 0`. -/
theorem wvalR_hg (a b : Q) (haL : a.num < (a.den : Int)) (hbL : b.num < (b.den : Int))
    (hab : 0 < (a.den : Int) * b.den + a.num * b.num) :
    Qeq (⟨((wvalR a b).den : Int) + (wvalR a b).num,
          (((wvalR a b).den : Int) - (wvalR a b).num).toNat⟩ : Q)
        (mul (⟨(a.den : Int) + a.num, ((a.den : Int) - a.num).toNat⟩ : Q)
             (⟨(b.den : Int) + b.num, ((b.den : Int) - b.num).toNat⟩ : Q)) := by
  have hWden : ((wvalR a b).den : Int) = (a.den : Int) * b.den + a.num * b.num := by
    rw [wvalR_den]; exact Int.toNat_of_nonneg (Int.le_of_lt hab)
  have hgA : (((a.den : Int) - a.num).toNat : Int) = (a.den : Int) - a.num :=
    Int.toNat_of_nonneg (by omega)
  have hgB : (((b.den : Int) - b.num).toNat : Int) = (b.den : Int) - b.num :=
    Int.toNat_of_nonneg (by omega)
  have hCnn : 0 ≤ ((wvalR a b).den : Int) - (wvalR a b).num := by
    rw [hWden, wvalR_num]
    have hfac : (a.den : Int) * b.den + a.num * b.num - (a.num * (b.den : Int) + b.num * (a.den : Int))
        = ((a.den : Int) - a.num) * ((b.den : Int) - b.num) := by
      generalize (a.den : Int) = qa; generalize (b.den : Int) = qb; ring_uor
    rw [hfac]; exact Int.mul_nonneg (by omega) (by omega)
  have hgC : ((((wvalR a b).den : Int) - (wvalR a b).num).toNat : Int)
      = (a.den : Int) * b.den + a.num * b.num - (a.num * (b.den : Int) + b.num * (a.den : Int)) := by
    rw [Int.toNat_of_nonneg hCnn, hWden, wvalR_num]
  simp only [Qeq, mul]
  rw [hgC]
  push_cast [hgA, hgB, hWden, wvalR_num]
  generalize (a.den : Int) = qa; generalize (b.den : Int) = qb
  generalize a.num = pa; generalize b.num = pb
  rw [show qa * qb + pa * pb + (pa * qb + pb * qa) = (qa + pa) * (qb + pb) from by ring_uor,
    show qa * qb + pa * pb - (pa * qb + pb * qa) = (qa - pa) * (qb - pb) from by ring_uor]

/-- **Additivity from exp-values, no sign restriction** (the `RexpReal_inj_gen` core): if `exp A = gA`,
    `exp B = gB`, `exp C = gC` with `gC = gA·gB`, then `C = A + B` — for **any** reals `A, B, C`
    (dropping the `≥ 0` hypotheses of `Req_add_of_exp_values`, via the general injectivity
    `RexpReal_inj_gen`). The engine for the *signed* artanh addition law. -/
theorem Req_add_of_exp_values_gen {A B C : Real} {gA gB gC : Q}
    (hgAd : 0 < gA.den) (hgBd : 0 < gB.den) (hgCd : 0 < gC.den)
    (hA : Req (RexpReal A) (ofQ gA hgAd)) (hB : Req (RexpReal B) (ofQ gB hgBd))
    (hC : Req (RexpReal C) (ofQ gC hgCd)) (hg : Qeq gC (mul gA gB)) :
    Req C (Radd A B) := by
  apply RexpReal_inj_gen
  have hmul : Req (RexpReal (Radd A B)) (ofQ gC hgCd) :=
    Req_trans (RexpReal_add A B)
      (Req_trans (Rmul_congr hA hB)
        (Req_trans (Rmul_ofQ_ofQ hgAd hgBd)
          (ofQ_congr (Qmul_den_pos hgAd hgBd) hgCd (Qeq_symm hg))))
  exact Req_trans hC (Req_symm hmul)

set_option maxHeartbeats 800000 in
/-- **★ sign-agnostic exp/artanh identity** `exp(2·artanh τ) = (1+τ)/(1−τ)` for **any** rational `τ`
    with `|τ| < 1` (`τ.num.toNat < τ.den` and `(−τ).num.toNat < τ.den`), at any radius `ρ ≥ |τ|`.
    Case-splits on the (decidable) sign of `τ.num`: the nonnegative packager
    `Rexp_twoArtanh_general_rho` for `τ ≥ 0`, the new `Rexp_TwoArtanh_of_neg` for `τ < 0`. Output
    normalized to `(τ.den+τ.num)/(τ.den−τ.num)`. -/
theorem Rexp_TwoArtanh_signed_rho (τ ρ : Q) (hτd : 0 < τ.den)
    (hτlt : τ.num.toNat < τ.den) (hτlt' : (neg τ).num.toNat < τ.den)
    (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρlt : ρ.num.toNat < ρ.den)
    (hb : Qle (Qabs τ) ρ) (hbn : Qle (Qabs (neg τ)) ρ) :
    Req (RexpReal (TwoArtanhConst τ ρ hτd hρ0 hρd hρlt hb))
      (ofQ (⟨(τ.den : Int) + τ.num, (τ.den - τ.num).toNat⟩ : Q)
        (by show 0 < (τ.den - τ.num).toNat
            have h' := hτlt'; simp only [neg] at h'; omega)) := by
  have hdpos : 0 < (τ.den - τ.num).toNat := by
    have h' := hτlt'; simp only [neg] at h'; omega
  have hqI : ((τ.den - τ.num).toNat : Int) = (τ.den : Int) - τ.num :=
    Int.toNat_of_nonneg (by have := hτlt; omega)
  by_cases hneg : τ.num < 0
  · -- τ < 0: reduce to the nonneg case for σ = −τ
    have hσge : 0 ≤ (neg τ).num := by show 0 ≤ -τ.num; omega
    have hσlt : (neg τ).num.toNat < (neg τ).den := by simpa only [neg] using hτlt'
    have hσd : 0 < (neg τ).den := hτd
    have hND : ((τ.den - (-τ.num).toNat : Nat) : Int) = (τ.den : Int) + τ.num := by
      rw [Int.ofNat_sub (by simpa only [neg] using Nat.le_of_lt hσlt),
        Int.toNat_of_nonneg (show (0 : Int) ≤ -τ.num by omega)]; omega
    have hσid := Rexp_twoArtanh_general_rho (neg τ) ρ hσd hσge hσlt hρ0 hρd hρlt hbn
    refine Rexp_TwoArtanh_of_neg τ ρ _ _ hτd hρ0 hρd hρlt hb hbn _ _ ?_ ?_ hσid
    · -- gσ > 1
      show Qlt (Qbound 0) (⟨((neg τ).den : Int) + (neg τ).num, ((neg τ).den - (neg τ).num.toNat)⟩ : Q)
      simp only [Qlt, Qbound, neg]; push_cast [hND]; omega
    · -- gτ · gσ = 1
      show Qeq (mul (⟨(τ.den : Int) + τ.num, (τ.den - τ.num).toNat⟩ : Q)
        (⟨((neg τ).den : Int) + (neg τ).num, ((neg τ).den - (neg τ).num.toNat)⟩ : Q)) ⟨1, 1⟩
      simp only [Qeq, mul, neg]; push_cast [hqI, hND]
      generalize (τ.den : Int) = d; ring_uor
  · -- τ ≥ 0: the nonneg packager, output bridged to the normalized form
    have hτge : 0 ≤ τ.num := Int.not_lt.mp hneg
    have hid := Rexp_twoArtanh_general_rho τ ρ hτd hτge hτlt hρ0 hρd hρlt hb
    refine Req_trans hid (ofQ_congr (by show 0 < τ.den - τ.num.toNat; omega) hdpos ?_)
    show Qeq (⟨(τ.den : Int) + τ.num, τ.den - τ.num.toNat⟩ : Q)
      (⟨(τ.den : Int) + τ.num, (τ.den - τ.num).toNat⟩ : Q)
    have hpI : (τ.num.toNat : Int) = τ.num := Int.toNat_of_nonneg hτge
    have hqI2 : ((τ.den - τ.num.toNat : Nat) : Int) = (τ.den : Int) - τ.num := by
      rw [Int.ofNat_sub (Nat.le_of_lt hτlt), hpI]
    show ((τ.den : Int) + τ.num) * (((τ.den - τ.num).toNat : Nat) : Int)
        = ((τ.den : Int) + τ.num) * ((τ.den - τ.num.toNat : Nat) : Int)
    rw [hqI, hqI2]

end UOR.Bridge.F1Square.Analysis
