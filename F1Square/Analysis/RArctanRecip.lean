/-
F1 square — Track 1, item-0 brick: **the reciprocal-arctan reduction, value level** —
`arctan(1/s) = π/2 − arctan s` for `s > 0`, expressed division-free as the tangent value identity

        `s · sin(π/2 − arctan s) = cos(π/2 − arctan s)`.

This is the forced next brick after the four-sector `Clog`-additivity: it extends the constructive
argument `Carg z = arctan(Im z / Re z)` PAST the value-identity radius `|t| < 1/16`. Inside a sector
the ratio `t = Im/Re` runs all the way to the imaginary axis (`t → ∞`); the principal value identity
`RarctanR_value_eq` (`sin(arctan t) = t·cos(arctan t)`) only certifies the small-`t` end. The classical
remedy is the reciprocal reduction `arctan t = π/2 − arctan(1/t)`: for LARGE `t` the complementary
angle `π/2 − arctan s` (with `s = 1/t` SMALL, inside the radius) supplies the value, and this brick
proves that complementary angle has tangent `1/s = t`, division-free.

The proof is pure algebra over three existing facts: the complementary-angle formulas
`sin(π/2 − x) = cos x` / `cos(π/2 − x) = sin x` (`Rsin_pi_half_sub` / `Rcos_pi_half_sub`,
`TanPiQuarter.lean`, built from the Gauss `π/2` anchors `sin(π/2)=1`, `cos(π/2)=0`), and the
small-argument value identity `sin(arctan s) = s·cos(arctan s)` (`RarctanR_value_eq`,
`RArctanValue.lean`). With `A := arctan s` and `B := π/2 − A`:
`sin B = cos A`, `cos B = sin A = s·cos A`, so `s·sin B = s·cos A = cos B`. ∎ No `Rinv`, no new range.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`. RH-independent (the `arg`-range substrate toward `log ξ`); crux fields
stay `none`, RH open.
-/
import F1Square.Analysis.TanPiQuarter
import F1Square.Analysis.RArctanValue

namespace UOR.Bridge.F1Square.Analysis

/-- **★ the reciprocal-arctan reduction, value level** — `s · sin(π/2 − arctan s) =
    cos(π/2 − arctan s)` for a small real argument `s` (`|s.seq n| ≤ ρ < 1/16`). Equivalently:
    `π/2 − arctan s` has tangent `1/s`, i.e. it IS `arctan(1/s)` — the constructive reduction
    `arctan(1/s) = π/2 − arctan s` that carries the argument `Carg z = arctan(Im z / Re z)` past the
    `|t| < 1/16` value-identity radius (apply with `s = Re z / Im z` small near the imaginary axis).

    Division-free, matching the program's value-identity convention: with `A = arctan s`,
    `sin(π/2 − A) = cos A` and `cos(π/2 − A) = sin A = s·cos A` (`RarctanR_value_eq`), so
    `s·sin(π/2 − A) = s·cos A = cos(π/2 − A)`. -/
theorem RarctanR_recip_value (s : Real) (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (hbs : ∀ n, Qle (Qabs (s.seq n)) ρ)
    (hlt16 : (mul ⟨16, 1⟩ ρ).num.toNat < (mul ⟨16, 1⟩ ρ).den)
    (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hhalf : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ))) (hρ4 : Qle (mul ⟨4, 1⟩ ρ) ⟨1, 1⟩)
    (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (hρ8 : Qle (mul ⟨2, 1⟩ ρ) ⟨1, 1⟩)
    (hρ1 : Qle ρ ⟨1, 1⟩) :
    Req (Rmul s (Rsin (Rsub Rpi_half (RarctanR s ρ hρ0 hρd hlt hbs))))
        (Rcos (Rsub Rpi_half (RarctanR s ρ hρ0 hρd hlt hbs))) := by
  -- A = arctan s, with its small-argument value identity sin A = s·cos A.
  have hA : Req (Rsin (RarctanR s ρ hρ0 hρd hlt hbs))
      (Rmul s (Rcos (RarctanR s ρ hρ0 hρd hlt hbs))) :=
    RarctanR_value_eq s ρ hρ0 hρd hlt hbs hlt16 h2ρ hhalf hρ4 hρ2 hρ8 hρ1
  -- complementary-angle formulas at A: sin(π/2 − A) = cos A, cos(π/2 − A) = sin A.
  have hsinB : Req (Rsin (Rsub Rpi_half (RarctanR s ρ hρ0 hρd hlt hbs)))
      (Rcos (RarctanR s ρ hρ0 hρd hlt hbs)) :=
    Rsin_pi_half_sub (RarctanR s ρ hρ0 hρd hlt hbs)
  have hcosB : Req (Rcos (Rsub Rpi_half (RarctanR s ρ hρ0 hρd hlt hbs)))
      (Rsin (RarctanR s ρ hρ0 hρd hlt hbs)) :=
    Rcos_pi_half_sub (RarctanR s ρ hρ0 hρd hlt hbs)
  -- s·sin B ≈ s·cos A ;  cos B ≈ sin A ≈ s·cos A.  Both sides meet at s·cos A.
  exact Req_trans (Rmul_congr (Req_refl s) hsinB) (Req_symm (Req_trans hcosB hA))

end UOR.Bridge.F1Square.Analysis
