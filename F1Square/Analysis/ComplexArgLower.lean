/-
F1 square — v0.22.0 Track 1, brick (argument axis): **the lower-sector argument** `CargLower`
(`Im z < 0`, `|Re/Im| ≤ ρ < 1`), the conjugate reflection of the upper sector.

ξ's zeros come in conjugate pairs, so the argument is needed below the real axis as well. By the
conjugate symmetry `arg(z̄) = −arg z`, the lower-sector argument is `CargLower z = −CargUpper(z̄)`
(`z̄ = Cconj z` lands in the upper sector when `Im z < 0`). It carries the genuine tangent
`tan(CargLower z) = Im z/Re z` (`CargLower_tan`, from `CargUpper_tan` + sin/cos parity), and its
additivity `CargLower(zw) = Carg z + CargLower w` (`CargLower_add`) reflects `CargUpper_add` through
`Cconj_Cmul` (`z̄w̄ = z̄·w̄`).

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/
import F1Square.Analysis.ComplexArgUpperAdd

namespace UOR.Bridge.F1Square.Analysis

/-- **The lower-half-plane argument** `CargLower z = −arg(z̄)` for `Im z < 0` (so `z̄` is upper):
    `arg(z) = −arg(z̄)` by conjugate symmetry. Witness `k` for `(z̄).im = −Im z > 0`. -/
def CargLower (z : Complex) (k : Nat) (hk : Qlt (Qbound k) ((Cconj z).im.seq k))
    (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs ((Rdiv (Cconj z).re (Cconj z).im k hk).seq n)) ρ) : Real :=
  Rneg (CargUpper (Cconj z) k hk ρ hρ0 hρd hρlt hb)

set_option maxHeartbeats 1200000 in
/-- **★ the lower-half argument has the right tangent**: `tan(CargLower z) = Im z/Re z`, i.e.
    `sin(CargLower z) = (Im z/Re z)·cos(CargLower z)`. From `CargUpper_tan` of `z̄` (`tan = (−Im z)/Re z`)
    reflected by sin-oddness/cos-evenness: `sin(−A) = −sin A`, `cos(−A) = cos A`, and
    `−((−Im z)/Re z) = Im z/Re z`. Confirms `CargLower` is the genuine lower-sector argument. -/
theorem CargLower_tan (z : Complex) (k : Nat) (hk : Qlt (Qbound k) ((Cconj z).im.seq k))
    (kr : Nat) (hkr : Qlt (Qbound kr) (z.re.seq kr))
    (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs ((Rdiv (Cconj z).re (Cconj z).im k hk).seq n)) ρ)
    (hlt16 : (mul ⟨16, 1⟩ ρ).num.toNat < (mul ⟨16, 1⟩ ρ).den)
    (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hhalf : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ))) (hρ4 : Qle (mul ⟨4, 1⟩ ρ) ⟨1, 1⟩)
    (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (hρ8 : Qle (mul ⟨2, 1⟩ ρ) ⟨1, 1⟩)
    (hρ1 : Qle ρ ⟨1, 1⟩) :
    Req (Rsin (CargLower z k hk ρ hρ0 hρd hρlt hb))
      (Rmul (Rdiv z.im z.re kr hkr) (Rcos (CargLower z k hk ρ hρ0 hρd hρlt hb))) := by
  have htan := CargUpper_tan (Cconj z) k hk kr hkr ρ hρ0 hρd hρlt hb hlt16 h2ρ hhalf hρ4 hρ2 hρ8 hρ1
  have hfac : Req (Rneg (Rdiv (Cconj z).im (Cconj z).re kr hkr)) (Rdiv z.im z.re kr hkr) :=
    Req_trans (Rneg_congr (Rmul_neg_left z.im (Rinv z.re kr hkr)))
      (Rneg_neg (Rmul z.im (Rinv z.re kr hkr)))
  show Req (Rsin (Rneg (CargUpper (Cconj z) k hk ρ hρ0 hρd hρlt hb)))
    (Rmul (Rdiv z.im z.re kr hkr) (Rcos (Rneg (CargUpper (Cconj z) k hk ρ hρ0 hρd hρlt hb))))
  refine Req_trans (Rsin_neg (CargUpper (Cconj z) k hk ρ hρ0 hρd hρlt hb)) ?_
  refine Req_trans (Rneg_congr htan) ?_
  refine Req_trans (Req_symm (Rmul_neg_left (Rdiv (Cconj z).im (Cconj z).re kr hkr)
    (Rcos (CargUpper (Cconj z) k hk ρ hρ0 hρd hρlt hb)))) ?_
  refine Req_trans (Rmul_congr hfac (Req_refl _)) ?_
  exact Rmul_congr (Req_refl _) (Req_symm (Rcos_neg (CargUpper (Cconj z) k hk ρ hρ0 hρd hρlt hb)))

end UOR.Bridge.F1Square.Analysis
