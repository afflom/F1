/-
F1 square — v0.19.0 stage E, bricks 1–2 (analysis layer): the COMPLETE explicit-formula
trace (the zero side, realized at the Bombieri–Lagarias slices) and the retirement of the
`Li.LiAgreesWith` interface at the built slices.

THE THREE SIDES OF THE WEIL EXPLICIT FORMULA in this substrate:
  • the PRIME side — built since v0.15.3 (`Analysis.Mangoldt.primeSide`: the finite sums
    `Σ_{m ≤ N} Λ(m)·h(log m)`, stable past the support of `h`, `primeSide_stable`);
  • the ARCHIMEDEAN side — built since v0.16.0 (`Analysis.Gamma.Digamma`: the exact
    `ψ = Γ′/Γ` place, `ψ(1) = −γ`);
  • the ZERO side — `Σ` over the nontrivial zeros. THE ZEROS ARE NOT CONSTRUCTED here; what
    is constructive is the Bombieri–Lagarias reading [CLASSICAL] (Bombieri–Lagarias,
    *J. Number Theory* 77 (1999), 274–287): at the BL test functions the zero side IS the
    Li coefficient, `λₙ = Σ_ρ [1 − (1−1/ρ)ⁿ]` (paired/symmetric sum), and the explicit
    formula evaluates it as `λₙ = λₙ^{arith} + λₙ^{∞}`. The arithmetic part is the
    finite-place (prime-side) contribution — as a CLOSED FORM it is the polynomial in the
    Stieltjes constants built here (`Rlambda1_arith = γ`, `Rlambda2_arith = 2γ − (γ²+2γ₁)`);
    its identification with the literal `−Σ Λ(m)·wₙ(m)` prime sums needs the `ζ′/ζ`
    continuation [CLASSICAL] — the standing LiOne hedge, unchanged. The archimedean parts
    are built (`Rlambda1_arch`, `Rlambda2_arch`).

THE COMPLETION (roadmap E, first goal). `Li.ExplicitFormulaTrace` — until now inhabited
only by the trivial split `z = z + 0` (`explicitFormulaTrace_genuine`) — is REALIZED with
the genuine three-sided reading at both built slices (`explicitFormulaTrace_one_realized`,
`explicitFormulaTrace_two_realized`), and packaged as the `WeilTrace` ladder: a zero side,
a finite-place part, an archimedean part, and the trace identity at every positive index
(`weilTraceTwo`). Completing the TRACE (the equality) bears NO positivity content — what
stays open is exactly the crux, positivity of the zero side for all `n` (= RH through
`Square.crux_faces_equivalent`); the not-the-crux guard for this instance is a theorem on
the square side (`Square.weilTraceTwo_not_crux`).

THE RETIREMENT (roadmap E, second goal). `Li.LiAgreesWith` — until now inhabited only
reflexively (`liAgreesWith_genuine`) — is realized with two genuinely DISTINCT routes to
the same values (`liAgreesWith_two_realized`): computed = the direct certified builds
(`Rlambda1` via the accelerated-γ assembly, v0.14.0; `Rlambda2` via the Stieltjes/ζ(2)
assembly, v0.16.0); classical = the Bombieri–Lagarias closed-form assemblies
(`liClassicalSeqTwo`). Their agreement at the built slices is the non-trivial content of
`Rlambda1_decomposition`/`Rlambda2_decomposition`. The hedge, stated exactly: the right
side equals the classical `λₙ` (the zero-sum) by [CLASSICAL] Bombieri–Lagarias 1999; what
is mechanized is build-vs-closed-form agreement. Beyond `n = 2` both sequences are the
same trivial value (the higher slices await `γ₂, γ₃, …`) — the interface is retired AT the
built slices, never asserted beyond them.

Pure Lean 4 core, no Mathlib, no `sorry`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.LiTwo
import F1Square.Li

namespace UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- The explicit-formula trace, realized (the zero side at the BL slices).
-- ===========================================================================

/-- **`Li.ExplicitFormulaTrace`, realized at the `n = 1` Bombieri–Lagarias slice**: the
    zero side `λ₁` (its sum-over-zeros reading is [CLASSICAL] BL 1999) equals the
    finite-place part `γ` plus the archimedean part `1 − γ/2 − ½·log 4π` — the first
    non-trivial instance of the interface, with all three reals built. -/
theorem explicitFormulaTrace_one_realized :
    Li.ExplicitFormulaTrace Rlambda1 Rlambda1_arith Rlambda1_arch :=
  Rlambda1_decomposition

/-- **`Li.ExplicitFormulaTrace`, realized at the `n = 2` slice**: the zero side `λ₂`
    equals `[2γ − (γ² + 2γ₁)] + [(1−γ) − log 4π + ¾·ζ(2)]`. -/
theorem explicitFormulaTrace_two_realized :
    Li.ExplicitFormulaTrace Rlambda2 Rlambda2_arith Rlambda2_arch :=
  Rlambda2_decomposition

/-- **The Weil-trace ladder** (the completion package): a zero side, a finite-place
    (prime) part, and an archimedean part, with the explicit-formula trace identity
    `zeroSide(n) = primePart(n) + archPart(n)` at every positive index. The GENUINE
    instance's zero side is the Li sequence of ζ — positivity of a `WeilTrace`'s zero side
    is never asserted here (that is the crux; see `Square.weilTrace_dominance`). -/
structure WeilTrace where
  /-- the zero side (`λₙ` for the genuine instance, by the [CLASSICAL] BL reading) -/
  zeroSide : Nat → Real
  /-- the finite-place (prime-side) part — `λₙ^{arith}` as a closed form -/
  primePart : Nat → Real
  /-- the archimedean (`Γ′/Γ`-place) part — `λₙ^{∞}` -/
  archPart : Nat → Real
  /-- the explicit-formula trace identity at every positive index -/
  trace : ∀ n : Nat, 0 < n →
    Li.ExplicitFormulaTrace (zeroSide n) (primePart n) (archPart n)

/-- **The realized two-slice Weil trace**: zero side `λ₁, λ₂` (genuine certified builds),
    finite-place parts `γ` and `2γ − (γ²+2γ₁)`, archimedean parts `1 − γ/2 − ½log 4π` and
    `(1−γ) − log 4π + ¾ζ(2)` — the trace identity genuine at both built slices, trivial
    beyond. NOT the crux (`Square.weilTraceTwo_not_crux`). -/
def weilTraceTwo : WeilTrace where
  zeroSide := liLamSeqTwo
  primePart := liArithSeqTwo
  archPart := liArchSeqTwo
  trace := fun n _ => li_decomposition_two_realized n

/-- The two built slices of the realized trace's zero side are certified positive —
    evidence at `n = 1, 2`, NOT the crux (the `n ≥ 3` slices of THIS instance vanish;
    the genuine zero side for all `n` is RH). -/
theorem weilTraceTwo_evidence :
    Pos (weilTraceTwo.zeroSide 1) ∧ Pos (weilTraceTwo.zeroSide 2) :=
  liTwo_evidence

-- ===========================================================================
-- `Li.LiAgreesWith`, retired at the built slices.
-- ===========================================================================

/-- The CLASSICAL route to the built Li values: the Bombieri–Lagarias closed-form
    assemblies `λₙ^{arith} + λₙ^{∞}` (equal to the classical `λₙ` by [CLASSICAL] BL 1999). -/
def liClassicalSeqTwo : Nat → Real := fun n =>
  Radd (liArithSeqTwo n) (liArchSeqTwo n)

/-- **`Li.LiAgreesWith`, retired at the built slices**: the computed sequence (the direct
    certified builds — `Rlambda1` via the accelerated-γ assembly, `Rlambda2` via the
    Stieltjes/ζ(2) assembly) agrees with the classical sequence (the Bombieri–Lagarias
    closed forms) — a genuinely NON-reflexive agreement at `n = 1, 2`, the two routes
    being distinct constructions reconciled by `Rlambda1_decomposition` /
    `Rlambda2_decomposition`. Beyond the built slices the agreement is trivial; nothing
    is asserted there. -/
theorem liAgreesWith_two_realized : Li.LiAgreesWith liLamSeqTwo liClassicalSeqTwo :=
  li_decomposition_two_realized

end UOR.Bridge.F1Square.Analysis
