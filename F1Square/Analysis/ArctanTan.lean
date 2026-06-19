/-
# `tan(arctan t) = t` and the `cos(arctan t)` closed form

Building on the value-level identity `sin(arctan t) = t·cos(arctan t)`
(`Rsin_arctan_value_eq`, `ArctanODE.lean`) and the genuine Pythagorean identity
`cos² + sin² = 1` (`Rcos_sq_add_sin_sq`, `CosSinAdd.lean`):

* `Rcos_arctan_sq` — `cos²(arctan t)·(1+t²) = 1`, the closed form `cos²(arctan t) = 1/(1+t²)`.
  Substituting `sin = t·cos` into Pythagoras collapses to `cos²·(1+t²) = 1`. Since the right side
  is `1 > 0`, this is the gateway to `cos(arctan t) ≠ 0` and hence `tan(arctan t) = t`.

All RH-*independent* (the `arctan`-addition substrate feeding `arg(zw) = arg z + arg w`); crux
fields stay `none`, RH open.
-/
import F1Square.Analysis.ArctanODE
import F1Square.Analysis.RMulNF

namespace UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 1000000 in
/-- **`cos²(arctan t)·(1+t²) = 1`** (`|t| ≤ ρ < 1/16`), i.e. the closed form `cos²(arctan t) =
    1/(1+t²)`. Substitute `sin(arctan t) = t·cos(arctan t)` (`Rsin_arctan_value_eq`) into the
    Pythagorean identity `cos² + sin² = 1` (`Rcos_sq_add_sin_sq`): `cos² + t²·cos² = cos²·(1+t²) = 1`.
    The right side `1 > 0` gives `cos(arctan t) ≠ 0`, the gateway to `tan(arctan t) = t`. -/
theorem Rcos_arctan_sq (t₀ ρ : Q) (htd : 0 < t₀.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (htρ : Qle (Qabs t₀) ρ)
    (hlt16 : (mul ⟨16, 1⟩ ρ).num.toNat < (mul ⟨16, 1⟩ ρ).den)
    (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hhalf : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ))) (hρ4 : Qle (mul ⟨4, 1⟩ ρ) ⟨1, 1⟩)
    (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (hρ8 : Qle (mul ⟨2, 1⟩ ρ) ⟨1, 1⟩)
    (hρ1 : Qle ρ ⟨1, 1⟩) :
    Req (Rmul (Rmul (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ)) (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ)))
          (Radd one (Rmul (ofQ t₀ htd) (ofQ t₀ htd)))) one := by
  have hval := Rsin_arctan_value_eq t₀ ρ htd hρ0 hρd hlt htρ hlt16 h2ρ hhalf hρ4 hρ2 hρ8 hρ1
  have hpyth := Rcos_sq_add_sin_sq (Rarctan t₀ htd hρ0 hρd hlt htρ)
  -- t²·cos² = sin²  (substitute sin = t·cos and reassociate)
  have hT2 : Req (Rmul (Rmul (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ))
        (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ))) (Rmul (ofQ t₀ htd) (ofQ t₀ htd)))
      (Rmul (Rsin (Rarctan t₀ htd hρ0 hρd hlt htρ)) (Rsin (Rarctan t₀ htd hρ0 hρd hlt htρ))) := by
    refine Req_trans (Rmul_comm (Rmul (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ))
      (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ))) (Rmul (ofQ t₀ htd) (ofQ t₀ htd))) ?_
    refine Req_trans (Req_symm (prod_sq_reassoc (ofQ t₀ htd)
      (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ)))) ?_
    exact Req_symm (Rmul_congr hval hval)
  -- cos²·(1+t²) = cos²·1 + cos²·t² = cos² + sin² = 1
  refine Req_trans (Rmul_distrib (Rmul (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ))
    (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ))) one (Rmul (ofQ t₀ htd) (ofQ t₀ htd))) ?_
  refine Req_trans (Radd_congr (Rmul_one (Rmul (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ))
    (Rcos (Rarctan t₀ htd hρ0 hρd hlt htρ)))) hT2) ?_
  exact hpyth

end UOR.Bridge.F1Square.Analysis
