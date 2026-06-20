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

set_option maxHeartbeats 800000 in
/-- **★ signed artanh addition law at a common radius** `2·artanh(wvalR a b) = 2·artanh a + 2·artanh b`
    for **signed** rationals `a, b` with `|a|, |b| < 1` and `1 + ab > 0`, all three `artanh`'s at one
    radius `σ`. The signed analog of `TwoArtanh_add_wval_rho`, using `wvalR` (sign-robust) +
    `Rexp_TwoArtanh_signed_rho` (×3) + `Req_add_of_exp_values_gen` + `wvalR_hg`. -/
theorem TwoArtanh_add_wvalR_rho (a b σ : Q)
    (had : 0 < a.den) (haL : a.num.toNat < a.den) (haL' : (neg a).num.toNat < a.den)
    (hbd : 0 < b.den) (hbL : b.num.toNat < b.den) (hbL' : (neg b).num.toNat < b.den)
    (hσ0 : 0 ≤ σ.num) (hσd : 0 < σ.den) (hσlt : σ.num.toNat < σ.den)
    (hab : 0 < (a.den : Int) * b.den + a.num * b.num)
    (hba : Qle (Qabs a) σ) (hbb : Qle (Qabs b) σ) (hbc : Qle (Qabs (wvalR a b)) σ) :
    Req (TwoArtanhConst (wvalR a b) σ (wvalR_den_pos a b hab) hσ0 hσd hσlt hbc)
        (Radd (TwoArtanhConst a σ had hσ0 hσd hσlt hba)
              (TwoArtanhConst b σ hbd hσ0 hσd hσlt hbb)) := by
  -- Int forms of the `|·| < 1` bounds
  have haLi : a.num < (a.den : Int) := by omega
  have haGi : -(a.den : Int) < a.num := by have := haL'; simp only [neg] at this; omega
  have hbLi : b.num < (b.den : Int) := by omega
  have hbGi : -(b.den : Int) < b.num := by have := hbL'; simp only [neg] at this; omega
  have hWd : ((wvalR a b).den : Int) = (a.den : Int) * b.den + a.num * b.num := by
    rw [wvalR_den]; exact Int.toNat_of_nonneg (Int.le_of_lt hab)
  -- |wvalR a b| < 1: den ± num = (qa∓pa)(qb∓pb) > 0
  have hcnum_lt : (wvalR a b).num < ((wvalR a b).den : Int) := by
    rw [hWd, wvalR_num]
    have hfac : (a.den : Int) * b.den + a.num * b.num - (a.num * (b.den : Int) + b.num * (a.den : Int))
        = ((a.den : Int) - a.num) * ((b.den : Int) - b.num) := by
      generalize (a.den : Int) = qa; generalize (b.den : Int) = qb; ring_uor
    have hpos : 0 < ((a.den : Int) - a.num) * ((b.den : Int) - b.num) :=
      Int.mul_pos (by omega) (by omega)
    omega
  have hcnum_gt : -((wvalR a b).den : Int) < (wvalR a b).num := by
    rw [hWd, wvalR_num]
    have hfac : (a.num * (b.den : Int) + b.num * (a.den : Int)) + ((a.den : Int) * b.den + a.num * b.num)
        = ((a.den : Int) + a.num) * ((b.den : Int) + b.num) := by
      generalize (a.den : Int) = qa; generalize (b.den : Int) = qb; ring_uor
    have hpos : 0 < ((a.den : Int) + a.num) * ((b.den : Int) + b.num) :=
      Int.mul_pos (by omega) (by omega)
    omega
  have hcL : (wvalR a b).num.toNat < (wvalR a b).den := by omega
  have hcL' : (neg (wvalR a b)).num.toNat < (wvalR a b).den := by
    have : ((neg (wvalR a b)).num) = -(wvalR a b).num := rfl
    simp only [this]; omega
  -- the three signed exp identities, via Rexp_TwoArtanh_signed_rho
  have hA := Rexp_TwoArtanh_signed_rho a σ had haL haL' hσ0 hσd hσlt hba
    (by rw [Qabs_neg]; exact hba)
  have hB := Rexp_TwoArtanh_signed_rho b σ hbd hbL hbL' hσ0 hσd hσlt hbb
    (by rw [Qabs_neg]; exact hbb)
  have hC := Rexp_TwoArtanh_signed_rho (wvalR a b) σ (wvalR_den_pos a b hab) hcL hcL'
    hσ0 hσd hσlt hbc (by rw [Qabs_neg]; exact hbc)
  exact Req_add_of_exp_values_gen
    (by show 0 < (a.den - a.num).toNat; omega) (by show 0 < (b.den - b.num).toNat; omega)
    (by show 0 < ((wvalR a b).den - (wvalR a b).num).toNat
        have := hcnum_lt; rw [hWd] at this ⊢; omega)
    hA hB hC (wvalR_hg a b haLi hbLi hab)

/-- `½·(2·x) ≈ x` (local copy; the private one lives in `ArtanhAdd`). -/
private theorem two_half_cancel_s (x : Real) :
    Req (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) x)) x := by
  have hc : Req (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (ofQ (⟨2, 1⟩ : Q) (by decide))) one :=
    Req_trans (Rmul_ofQ_ofQ (by decide) (by decide)) (ofQ_congr (by decide) (by decide) (by decide))
  refine Req_trans (Req_symm (Rmul_assoc (ofQ (⟨1, 2⟩ : Q) (by decide))
    (ofQ (⟨2, 1⟩ : Q) (by decide)) x)) ?_
  exact Req_trans (Rmul_congr hc (Req_refl x)) (Rone_mul x)

set_option maxHeartbeats 800000 in
/-- **★ signed single-`artanh` addition law at a common radius** (the `×2` stripped):
    `artanh(wvalR a b) = artanh a + artanh b` as `RartanhConst`s, for signed `a, b`. The signed analog
    of `RartanhConst_add_wval_rho` — from `TwoArtanh_add_wvalR_rho` by `Rmul_distrib` + cancelling `2`.
    This single-level form has the clean depths the real-lift diagonal's combination leg needs. -/
theorem RartanhConst_add_wvalR_rho (a b σ : Q)
    (had : 0 < a.den) (haL : a.num.toNat < a.den) (haL' : (neg a).num.toNat < a.den)
    (hbd : 0 < b.den) (hbL : b.num.toNat < b.den) (hbL' : (neg b).num.toNat < b.den)
    (hσ0 : 0 ≤ σ.num) (hσd : 0 < σ.den) (hσlt : σ.num.toNat < σ.den)
    (hab : 0 < (a.den : Int) * b.den + a.num * b.num)
    (hba : Qle (Qabs a) σ) (hbb : Qle (Qabs b) σ) (hbc : Qle (Qabs (wvalR a b)) σ) :
    Req (RartanhConst (wvalR a b) σ (wvalR_den_pos a b hab) hσ0 hσd hσlt hbc)
        (Radd (RartanhConst a σ had hσ0 hσd hσlt hba)
              (RartanhConst b σ hbd hσ0 hσd hσlt hbb)) := by
  have hlaw := TwoArtanh_add_wvalR_rho a b σ had haL haL' hbd hbL hbL' hσ0 hσd hσlt hab hba hbb hbc
  have hmul2 : Req (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide))
        (RartanhConst (wvalR a b) σ (wvalR_den_pos a b hab) hσ0 hσd hσlt hbc))
      (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide))
        (Radd (RartanhConst a σ had hσ0 hσd hσlt hba)
              (RartanhConst b σ hbd hσ0 hσd hσlt hbb))) :=
    Req_trans hlaw (Req_symm (Rmul_distrib _ _ _))
  exact Req_trans (Req_symm (two_half_cancel_s _))
    (Req_trans (Rmul_congr (Req_refl (ofQ (⟨1, 2⟩ : Q) (by decide))) hmul2) (two_half_cancel_s _))

set_option maxHeartbeats 1600000 in
/-- **★ signed real artanh addition diagonal** `artanh s + artanh t = artanh(wvalReal s t)` for **signed**
    real `s, t` (`|s.seq m|, |t.seq m| < 1` both ways). The signed analog of `Rartanh_add_real_via`:
    identical diagonal assembly (arg-variation leg `artSum_wval_argdiff` and the den-positivity
    `wval_inner_pos` are already sign-agnostic over `wvalR`), with the combination leg now the signed
    `RartanhConst_add_wvalR_rho`. Drops the `≥0` hypotheses `hs0`/`ht0`, adds the `−num`-side bounds
    `hslt'`/`htlt'`. -/
theorem Rartanh_add_real_via_signed (s t X1 X2 Y : Real) (σ : Q) (R_Y : Nat → Nat)
    (hσ0 : 0 ≤ σ.num) (hσd : 0 < σ.den) (hσlt : σ.num.toNat < σ.den)
    (hσ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul σ σ))) (hRY : ∀ n, n ≤ R_Y n)
    (hslt : ∀ m, (s.seq m).num.toNat < (s.seq m).den) (htlt : ∀ m, (t.seq m).num.toNat < (t.seq m).den)
    (hslt' : ∀ m, (neg (s.seq m)).num.toNat < (s.seq m).den)
    (htlt' : ∀ m, (neg (t.seq m)).num.toNat < (t.seq m).den)
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
  have hRge : ∀ k, k ≤ Rartanh_R σ k := by
    intro k; unfold Rartanh_R
    have hk : 1 ≤ σ.den * σ.den + 4 * σ.den := Nat.le_trans (by omega) (Nat.le_add_left _ _)
    calc k ≤ 1 * (k + 1) := by omega
      _ ≤ (σ.den * σ.den + 4 * σ.den) * (k + 1) := Nat.mul_le_mul_right _ hk
  refine Req_of_lin_bound (C := 34) ?_
  intro n
  have hae : (Radd X1 X2).seq n
      = add (artSum (s.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1)))
          (artSum (t.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1))) := by
    show add (X1.seq (2 * n + 1)) (X2.seq (2 * n + 1)) = _; rw [hX1seq, hX2seq]
  rw [hae, hYseq n]
  have hWd : 0 < (artSum (wvalR (s.seq (Rartanh_R σ (2 * n + 1))) (t.seq (Rartanh_R σ (2 * n + 1))))
      (Rartanh_R σ n)).den :=
    artSum_den_pos (wvalR_den_pos _ _ (wval_inner_pos σ _ _ hσd hσ0 (hsd _) (htd _) (hbs _) (hbt _) hσhalf)) _
  have hYd : 0 < (artSum (wvalR (s.seq (R_Y n)) (t.seq (R_Y n))) (Rartanh_R σ n)).den :=
    artSum_den_pos (wvalR_den_pos _ _ (wval_inner_pos σ _ _ hσd hσ0 (hsd _) (htd _) (hbs _) (hbt _) hσhalf)) _
  have hRd : 0 < (add (artSum (s.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1)))
      (artSum (t.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1)))).den :=
    add_den_pos (artSum_den_pos (hsd _) _) (artSum_den_pos (htd _) _)
  -- combination leg: the SIGNED rational addition law at the diagonal rationals (already in wvalR form)
  have hcomb : Qle (Qabs (Qsub
        (artSum (wvalR (s.seq (Rartanh_R σ (2 * n + 1))) (t.seq (Rartanh_R σ (2 * n + 1)))) (Rartanh_R σ n))
        (add (artSum (s.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1)))
          (artSum (t.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1)))))) (⟨2, n + 1⟩ : Q) :=
    RartanhConst_add_wvalR_rho (s.seq (Rartanh_R σ (2 * n + 1)))
      (t.seq (Rartanh_R σ (2 * n + 1))) σ (hsd _) (hslt _) (hslt' _) (htd _) (htlt _) (htlt' _)
      hσ0 hσd hσlt (wval_inner_pos σ _ _ hσd hσ0 (hsd _) (htd _) (hbs _) (hbt _) hσhalf)
      (hbs _) (hbt _) (hbw _) n
  have hvar := artSum_wval_argdiff σ σ (s.seq (Rartanh_R σ (2 * n + 1)))
    (t.seq (Rartanh_R σ (2 * n + 1))) (s.seq (R_Y n)) (t.seq (R_Y n))
    hσd hσ0 hσhalf hσ0 hσd hσ2 (hsd _) (htd _) (hsd _) (htd _)
    (hbs _) (hbt _) (hbs _) (hbt _) (hbw _) (hbw _) (Rartanh_R σ n)
  have hQbP : Qle (Qbound (Rartanh_R σ (2 * n + 1))) (Qbound n) := by
    show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((Rartanh_R σ (2 * n + 1) + 1 : Nat) : Int)
    have := hRge (2 * n + 1); rw [Int.one_mul, Int.one_mul]
    exact_mod_cast (show n + 1 ≤ Rartanh_R σ (2 * n + 1) + 1 by omega)
  have hQbM : Qle (Qbound (R_Y n)) (Qbound n) := by
    show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((R_Y n + 1 : Nat) : Int)
    have := hRY n; rw [Int.one_mul, Int.one_mul]
    exact_mod_cast (show n + 1 ≤ R_Y n + 1 by omega)
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
  have hlegA : Qle (Qabs (Qsub
        (add (artSum (s.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1)))
          (artSum (t.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1))))
        (artSum (wvalR (s.seq (Rartanh_R σ (2 * n + 1))) (t.seq (Rartanh_R σ (2 * n + 1)))) (Rartanh_R σ n))))
      (⟨2, n + 1⟩ : Q) := by
    rw [Qabs_Qsub_comm]; exact hcomb
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hRd hWd))
      (Qabs_den_pos (Qsub_den_pos hWd hYd)))
    (Qabs_sub_triangle hRd hWd hYd) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n)) (Qadd_le_add hlegA hlegB) ?_
  apply Qeq_le; exact Qadd_same_den_loc 2 32 (n + 1)

end UOR.Bridge.F1Square.Analysis
