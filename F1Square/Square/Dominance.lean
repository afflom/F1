/-
F1 square — v0.19.0 stage E, brick 3: **THE DOMINANCE FACE OF THE CRUX** — the crux as a
SINGLE UNIFORM BOUND: the oscillating arithmetic part can never overwhelm the archimedean
trend.

THE SHAPE. Through the explicit-formula trace `λₙ = λₙ^{arith} + λₙ^{∞}` (the realized
`Analysis.WeilTrace`), the crux `λₙ > 0 ∀n` says exactly: at every `n`, the arithmetic
part's negative excursion stays strictly below the archimedean value. `Dominates B arith
arch` packages that as ONE object — a single bound sequence `B` with
      `−B(n) ≤ arith(n)`   (the bound controls the oscillation's negative excursions)
      `arch(n) − B(n) > 0` (the bound stays strictly below the archimedean trend)
— and `Dominated arith arch` is its single existential. This is the strongest honest shape
available for the universal:
  • it is genuinely universal WITHOUT enumeration — no slice ladder, no finite checks
    (which provably never reach the crux: `Li.liPositive_iff_all_upTo`,
    `spectral_iff_all_upTo`); the open content is relocated into ONE object, the bound;
  • the sign-dichotomy is CLEAN — there is no third option to eliminate and no crossover
    case split: the formulation is sign-agnostic in both parts (for small `n` the
    archimedean part is the NEGATIVE one — `λ₁^{∞} ≈ −0.554`, `λ₂^{∞} ≈ −0.875`, with the
    arithmetic part carrying the positivity; asymptotically the roles swap, the archimedean
    part growing like `(n/2)·log n` [CLASSICAL, unconditional — the Γ-factor asymptotics]
    while RH holds iff the arithmetic oscillation stays subdominant). A single `B`
    (itself of either sign, slice by slice) expresses both regimes uniformly.

THE THEOREMS. For any sequences satisfying the trace identity at positive indices:
      `dominated_liPositive`     : Dominated arith arch → LiPositive lam
      `liPositive_dominated`     : LiPositive lam → Dominated arith arch
      `dominated_iff_liPositive` : Dominated arith arch ⟺ LiPositive lam
      `dominance_crux_equivalent`: Dominated arith arch ⟺ SpectralCrux S   (through the
                                   v0.18.0 bridge — so the crux now has THREE equivalent
                                   faces: geometric `⟨Cₙ,Cₙ⟩ < 0 ∀n`, analytic `λₙ > 0 ∀n`,
                                   and dominance `∃ one bound under which oscillation
                                   loses`)
      `weilTrace_dominance`      : Dominated W.primePart W.archPart ⟺ LiCrux W.zeroSide
                                   (the dominance reading of the completed explicit-formula
                                   trace).

FAITHFULNESS (the standing discipline, enforced):
  • The equivalence RELOCATES the difficulty; it does not remove it (the Conrey–Li
    discipline, *IMRN* 2000 — positivity reformulations never make RH easier). What the
    relocation buys is the honest pinpoint: for the GENUINE sequences, whether such a
    bound exists is governed by the location of the zeros — each zero `ρ` contributes
    oscillations to the arithmetic part whose amplitude is controlled by `|1 − 1/ρ|`;
    zeros ON the critical line keep the oscillation tempered, a zero OFF the line makes
    the amplitude grow geometrically and defeats EVERY bound dominated by the archimedean
    trend [CLASSICAL — the growth/oscillation sharpening of Li's criterion; the
    archimedean asymptotics are unconditional]. Proving `Dominated` for the genuine parts
    IS proving RH; it is exactly as open as the crux, and stays so here.
  • Two-sidedness: the property is satisfiable (`dominance_satisfiable` — no hidden
    impossibility in the encoding, and the loose existential `∃ arith arch, Dominated …`
    is true and hence NOT RH), and the realized two-slice instance provably FAILS it
    (`twoSlice_not_dominated`, via `weilTraceTwo_not_crux`): no finite assembly of
    certified slices acquires the universal through this face either — the guard
    transfers to the dominance face.
  • The crux fields stay `none`: nothing here asserts `Dominated` for the genuine parts.

Pure Lean 4 core, no Mathlib, no `sorry`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Square.Spectral
import F1Square.Analysis.LiComplete
import F1Square.Analysis.Pi

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open UOR.Bridge.F1Square.Li

-- ===========================================================================
-- The dominance property: one bound, all `n`.
-- ===========================================================================

/-- **The dominance bound**: `B` controls the arithmetic part's negative excursions
    (`−B(n) ≤ arith(n)`) while staying strictly below the archimedean trend
    (`arch(n) − B(n) > 0`) — at every positive index, via the SAME `B`. Sign-agnostic in
    both parts: no case split between the small-`n` regime (archimedean part negative,
    arithmetic part positive) and the asymptotic regime (roles swapped). -/
def Dominates (B arith arch : Nat → Real) : Prop :=
  (∀ n : Nat, 0 < n → Rle (Rneg (B n)) (arith n)) ∧
  (∀ n : Nat, 0 < n → Pos (Rsub (arch n) (B n)))

/-- **The dominance face**: SOME single bound dominates — the oscillation loses, for all
    `n`, via one object. For the genuine arithmetic/archimedean parts this is RH
    (`dominance_crux_equivalent`); it is never asserted for them here. -/
def Dominated (arith arch : Nat → Real) : Prop :=
  ∃ B : Nat → Real, Dominates B arith arch

-- ===========================================================================
-- Dominance ⟺ Li positivity (under the explicit-formula trace).
-- ===========================================================================

/-- **Dominance suffices**: if one bound dominates, every `λₙ` is strictly positive —
    `λₙ = arith(n) + arch(n) ≥ arch(n) − B(n) > 0`. The proof is the one-line order
    algebra; no enumeration, no asymptotics: the single bound carries the universal. -/
theorem dominated_liPositive {lam arith arch : Nat → Real}
    (htrace : ∀ n : Nat, 0 < n → Li.ExplicitFormulaTrace (lam n) (arith n) (arch n))
    (hdom : Dominated arith arch) : LiPositive lam := by
  obtain ⟨B, hB1, hB2⟩ := hdom
  intro n hn
  have hle : Rle (Rsub (arch n) (B n)) (Radd (arch n) (arith n)) :=
    Radd_le_add (Rle_refl (arch n)) (hB1 n hn)
  have hpos : Pos (Radd (arith n) (arch n)) :=
    Pos_congr (Radd_comm (arch n) (arith n)) (Pos_mono hle (hB2 n hn))
  exact Pos_congr (Req_symm (htrace n hn)) hpos

/-- **Dominance is necessary**: if every `λₙ` is strictly positive, the bound
    `B(n) := arch(n) − λₙ` dominates — `−B(n) ≈ arith(n)` (so the excursion control is
    tight) and `arch(n) − B(n) ≈ λₙ > 0`. So the dominance face loses nothing. -/
theorem liPositive_dominated {lam arith arch : Nat → Real}
    (htrace : ∀ n : Nat, 0 < n → Li.ExplicitFormulaTrace (lam n) (arith n) (arch n))
    (hpos : LiPositive lam) : Dominated arith arch := by
  refine ⟨fun n => Rsub (arch n) (lam n), fun n hn => ?_, fun n hn => ?_⟩
  · -- `−(arch − λ) ≈ −arch + λ ≈ −arch + (arith + arch) ≈ arith`
    refine Rle_of_Req ?_
    refine Req_trans (Rneg_Radd (arch n) (Rneg (lam n))) ?_
    refine Req_trans (Radd_congr (Req_refl (Rneg (arch n))) (Rneg_Rneg (lam n))) ?_
    refine Req_trans (Radd_congr (Req_refl (Rneg (arch n))) (htrace n hn)) ?_
    refine Req_trans (Radd_congr (Req_refl (Rneg (arch n)))
      (Radd_comm (arith n) (arch n))) ?_
    refine Req_trans (Req_symm (Radd_assoc (Rneg (arch n)) (arch n) (arith n))) ?_
    refine Req_trans (Radd_congr
      (Req_trans (Radd_comm (Rneg (arch n)) (arch n)) (Radd_neg (arch n)))
      (Req_refl (arith n))) ?_
    exact Req_trans (Radd_comm zero (arith n)) (Radd_zero (arith n))
  · -- `arch − (arch − λ) ≈ λ > 0`
    refine Pos_congr (Req_symm ?_) (hpos n hn)
    refine Req_trans (Radd_congr (Req_refl (arch n)) (Rneg_Radd (arch n) (Rneg (lam n)))) ?_
    refine Req_trans (Radd_congr (Req_refl (arch n))
      (Radd_congr (Req_refl (Rneg (arch n))) (Rneg_Rneg (lam n)))) ?_
    refine Req_trans (Req_symm (Radd_assoc (arch n) (Rneg (arch n)) (lam n))) ?_
    refine Req_trans (Radd_congr (Radd_neg (arch n)) (Req_refl (lam n))) ?_
    exact Req_trans (Radd_comm zero (lam n)) (Radd_zero (lam n))

/-- **THE DOMINANCE EQUIVALENCE**: under the explicit-formula trace, "some single bound
    dominates" and "every `λₙ` is strictly positive" are the SAME proposition. -/
theorem dominated_iff_liPositive {lam arith arch : Nat → Real}
    (htrace : ∀ n : Nat, 0 < n → Li.ExplicitFormulaTrace (lam n) (arith n) (arch n)) :
    Dominated arith arch ↔ LiPositive lam :=
  ⟨dominated_liPositive htrace, liPositive_dominated htrace⟩

-- ===========================================================================
-- The third face of the crux.
-- ===========================================================================

/-- **THE THIRD FACE — the v0.19.0 keystone**: for any spectral square whose trace data
    satisfies the explicit-formula split, the dominance face is equivalent to the
    geometric crux (and hence, through `crux_faces_equivalent`, to the analytic one):
        `∃ one bound under which oscillation loses  ⟺  ⟨Cₙ,Cₙ⟩ < 0 ∀n  ⟺  λₙ > 0 ∀n`.
    For the genuine instance all three are RH; none is asserted. The equivalence is a
    constructive theorem — the difficulty is RELOCATED into the single bound `B`, whose
    existence for the genuine parts is governed by the zeros' location (module
    docstring). -/
theorem dominance_crux_equivalent (S : SpectralSquare) {arith arch : Nat → Real}
    (htrace : ∀ n : Nat, 0 < n → Li.ExplicitFormulaTrace (S.lam n) (arith n) (arch n)) :
    Dominated arith arch ↔ SpectralCrux S :=
  Iff.trans (dominated_iff_liPositive htrace) (crux_faces_equivalent S).symm

/-- **The dominance reading of the completed explicit-formula trace**: for any
    `Analysis.WeilTrace`, the crux of its zero side is exactly the dominance of its
    finite-place part by its archimedean part under one bound. -/
theorem weilTrace_dominance (W : WeilTrace) :
    Dominated W.primePart W.archPart ↔ LiCrux W.zeroSide :=
  dominated_iff_liPositive W.trace

-- ===========================================================================
-- The honesty guards (two-sided, as theorems).
-- ===========================================================================

/-- **The realized two-slice trace is NOT the crux** (analytic-face guard for
    `Analysis.weilTraceTwo`): its `n = 3` zero-side slice vanishes, so zero-side
    positivity provably fails — completing the trace at the built slices asserts
    nothing about RH. -/
theorem weilTraceTwo_not_crux : ¬ LiCrux weilTraceTwo.zeroSide := by
  intro h
  have h3 := h 3 (by omega)
  have hz : Req (liLamSeqTwo 3) (Radd zero zero) := Req_refl _
  exact not_Pos_zero_double (Pos_congr hz h3)

/-- **The guard transfers to the dominance face**: the genuine certified two-slice parts
    are provably NOT dominated by any single bound (their `n = 3` zero-side slice
    vanishes) — no finite assembly of certified slices acquires the universal through
    the dominance face either. -/
theorem twoSlice_not_dominated : ¬ Dominated liArithSeqTwo liArchSeqTwo := by
  intro hd
  exact weilTraceTwo_not_crux (dominated_liPositive weilTraceTwo.trace hd)

/-- **The two-sidedness guard**: the dominance property is satisfiable (the template
    split `1 = 1 + 0` is dominated by the constant bound `B = −1`), so the encoding
    hides no impossibility — and the loose existential `∃ arith arch, Dominated …` is
    true and hence NOT RH: the crux is dominance of the GENUINE parts, never an
    existential over sequences. -/
theorem dominance_satisfiable : Dominated (fun _ => one) (fun _ => zero) := by
  refine ⟨fun _ => Rneg one, fun n _ => ?_, fun n _ => ?_⟩
  · exact Rle_of_Req (Rneg_Rneg one)
  · refine Pos_congr (Req_symm ?_) Pos_one
    refine Req_trans (Radd_congr (Req_refl zero) (Rneg_Rneg one)) ?_
    exact Req_trans (Radd_comm zero one) (Radd_zero one)

end UOR.Bridge.F1Square.Square
