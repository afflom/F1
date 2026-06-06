# Changelog

All notable changes to this project are documented here. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and this project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html), starting at `v0.0.1`.

## [0.4.0] - 2026-06-06

### Added — a from-scratch `ring` tactic; ℚ as an ordered field; ℝ as an ordered additive group (pure Lean 4, no Mathlib, no `sorry`)
- `F1Square/Analysis/RingTac.lean` — **`ring_uor`, a from-scratch commutative-ring decision
  procedure**, the capstone of the v0.3.0 normalizer. A real Lean tactic (core metaprogramming,
  `Lean.Elab.Tactic` — *not* Mathlib): it reifies an integer equality goal into the `PExpr` syntax,
  applies the soundness lemma `nf_eq`, and discharges the residual `norm lhs = norm rhs` by `decide`.
  Reification is fuel-bounded (no `partial def`); the tactic only *builds* a `nf_eq` proof, so every
  goal it closes is as axiom-clean as `nf_eq`. (`ring` is confirmed absent from core; `push_cast` and
  `omega` are core and are used for cast/linear steps.)
- `F1Square/Analysis/QOrder.lean` — **ℚ as a verified ordered field**: reflexivity, transitivity
  (`Qle_trans`), `Qeq → Qle`, additive monotonicity (`Qadd_le_add`), the absolute-value triangle
  inequality (`Qabs_add_le`), `|·|` respects value-equality (`Qabs_Qeq`), order transport along `≈`
  (`Qle_congr_left/right`), and the telescoping triangle `|(a+b)−(c+d)| ≤ |a−c|+|b−d|`
  (`Qabs_sub_add4`) — the exact bound real addition consumes. Built from the core ℤ order/`natAbs`
  lemmas and `ring_uor`.
- `F1Square/Analysis/Real.lean` — **ℝ arithmetic with full regularity proofs**: negation `Rneg`
  (an isometry) and the reindexed **Bishop addition** `Radd` (`(x⊕y)ₙ = x₍₂ₙ₊₁₎+y₍₂ₙ₊₁₎`, regular
  because `2·1/(2k+2) = 1/(k+1)`, proved via the telescoping triangle + monotonicity + `ring_uor`).
  The `Real` structure now carries `den_pos` (every term has a positive denominator). With
  denominator-positivity helpers added to `Analysis/Rat.lean`.
- `scripts/audit_axioms.lean` extended to all new theorems; the honesty gate stays green.

### Changed
- `Real` gains the `den_pos` field; `ofQ` now takes a positivity proof (`zero`/`one`/`half` supply it
  by `decide`). `Qsub`/`Qabs` moved from `Real.lean` to `Analysis/Rat.lean` (basic ℚ operations).
- `docs/`: the analysis-substrate roadmap advances (ℝ is now an ordered additive group with a
  from-scratch `ring`); ℝ multiplication, `≈`-transitivity (an Archimedean argument), ℂ = ℝ×ℝ, and
  the transcendentals are the v0.5.0 continuation. `F1Square.lean` gains a v0.4.0 `example`.

### Note
- RH remains **open**. v0.4.0 makes ℝ an ordered additive group and gives the project a genuine
  `ring`; it does not resolve λₙ / Weil-positivity / the crux. The substrate makes the analytic half
  *statable and checkable*, never proven — proving `λₙ ≥ 0 ∀n` / the Hodge index on 𝕊 is RH.

## [0.3.0] - 2026-06-06

### Added — the analysis substrate, brick two: a ℤ ring normalizer + constructive ℝ (pure Lean 4, no Mathlib, no `sorry`)
- `F1Square/Analysis/RingNF.lean` — a **reflective commutative-ring normalizer over ℤ**: polynomial
  expressions (`PExpr`) get a **canonical form** (a sorted, merged `(monomial, coefficient)` list —
  their content-address), with a single soundness theorem `norm_sound : pden ρ (norm e) = denote ρ e`
  and the decision lemma `nf_eq` (equal canonical forms ⇒ equal as ℤ-functions). This lifts the
  no-`ring` ceiling: general nonlinear identities — `(a+b)² = a²+2ab+b²`, `(a+b)(a−b) = a²−b²`,
  `(a+b+c)²`, commuted distributivity — are now genuine theorems for ALL integers, proved by `decide`
  on the finite normal form. Soundness is built from the core ℤ ring lemmas, never assumed.
- `F1Square/Analysis/Rat.lean` — the v0.2.0 ℚ brick's field laws are now **general** (all rationals,
  not just numerals): `add_comm`, `mul_comm`, `add_assoc`, `mul_assoc`, `mul_add` (distributivity),
  `mul_one`, `add_zero`, `add_neg` — each discharged by the ring normalizer after pushing the
  `Nat → Int` casts to the leaves. Dogfooding the v0.3.0 tool.
- `F1Square/Analysis/Real.lean` — **constructive ℝ** as **Bishop regular sequences** over the exact ℚ
  (`|xₘ − xₙ| ≤ 1/(m+1) + 1/(n+1)`): the `Real` type, the regularity predicate, the canonical
  embedding ℚ ↪ ℝ (proved regular and value-respecting, `const_regular` / `ofQ_respects`), the Bishop
  equality setoid (`Req_refl`, `Req_symm`), and the witnessed positivity predicate (`Pos`, `Pos_half`).
- `scripts/audit_axioms.lean` extended to all 29 new theorems; the honesty gate stays green.

### Changed
- `docs/`: the analysis-substrate roadmap advances one brick (ℚ → **ℤ ring normalizer + ℝ** →
  ℂ+transcendentals → ζ/λₙ); the v0.3.0 status is recorded. `F1Square.lean` gains a v0.3.0
  elaboration-checked `example`. Literature note refreshed (the Feb-2026 Connes–Consani *Jacobian of
  `Spec ℤ̄`*, arXiv:2602.15941, is Arakelov–Picard — it does **not** construct the square or prove
  Hodge positivity; RH remains open as of mid-2026).

### Note
- RH remains **open**. v0.3.0 builds the algebraic tool (the ring normalizer) and the ℝ foundation;
  ℝ arithmetic (`+`, `·`), `≈`-transitivity (a limiting argument), and completeness are the v0.4.0
  continuation. The substrate makes the analytic half *statable and checkable*, never proven —
  proving `λₙ ≥ 0 ∀n` / the Hodge index on 𝕊 is RH.

## [0.2.0] - 2026-06-06

### Added — finite tropical stack mechanized + first analysis brick (pure Lean 4, no Mathlib, no `sorry`)
- `F1Square/Tropical/Closure.lean` — tropical (max-plus) matrix closure: the canonical `W*` (matches
  the companion) and **R2** Kleene-star idempotence `W* ⊗ W* = W*`, by `decide`.
- `F1Square/Tropical/Spectrum.lean` — the content-address κ and the cycle-mean spectrum: **R3** κ
  permutation-invariance, **R4** the cycle spectrum, and the headline **R9/R10** κ⊥spectrum
  counterexample (same κ, different spectrum) with **R11** the κ-fiber.
- `F1Square/Tropical/Siblings.lean` — the boolean sibling carrier: **R14** κ permutation-invariance,
  **R15** the faceted `(κ_trop, κ_bool)` address, **R16** boolean-facet degeneracy on a
  strongly-connected graph.
- `F1Square/Tropical/Signature.lean` — tropical Hodge-index signatures: the §2.3 parallel pencil
  `Δ·Γ_n = 0` (`det((1,1),(1,1)) = 0`), the fan-vs-fiber correction (fan recession form degenerate,
  so `(1,ρ−1)` is the fiber form), and a Babaee–Huh counterexample (the signature is NOT automatic).
- `F1Square/Analysis/Rat.lean` — the first analysis brick: exact rationals ℚ from ℤ, the **UOR way**
  (canonical reduced form = content-address; decidable exact equality/order; idempotent `reduce`).
  The analysis-substrate roadmap (ℚ → constructive ℝ → ℂ+transcendentals → ζ/λₙ) is documented.
- `scripts/audit_axioms.lean` extended to all new theorems; the honesty gate stays green.

### Changed
- `docs/`: the finite R1–R16 stack is marked kernel-checked (was runtime-verified); the analysis
  roadmap and the v0.2.0 mechanization status are recorded. `F1Square.lean` gains a v0.2.0
  elaboration-checked `example`.

### Note
- RH remains **open**. v0.2.0 resolves the finite/decidable open questions and lays the ℚ brick; it
  does not resolve λₙ / Weil-positivity / the crux (those are RH). The analysis substrate makes them
  *statable and checkable*, not proven.

## [0.1.0] - 2026-06-06

### Added — the genuine-proof layer (real Lean 4 theorems, no Mathlib, no `sorry`)
- `F1Square/Mechanism.lean` — the function-field Hodge mechanism as the square-root-free integer
  Hasse condition (`hodgeType_iff : hodgeType q a ↔ a² ≤ 4q`) with the §9.1 flip cases at
  `q = 4, 9, 25`; tropical intersection-positivity `mult = mu·mv·|det| ≥ 0` and tropical Bézout (R13).
- `F1Square/Template.lean` — the product-of-curves intersection template (§2.2): pairing symmetry,
  the sourced numbers `E₁·E₂ = 1`, `E₃² = −2`, the ample class `H² = 2 > 0`, and genuine
  negative-definiteness on the primitive complement `H^⊥` (`diag(−2,−2)`, nondegenerate) — the §1.4
  Hodge-type `(1,2)` decomposition.
- `F1Square/CharOne.lean` — the characteristic-1 (max-plus) base: idempotency (R1), the semiring
  laws, and the reversal theorem (R12: cycle weight/length invariant under reversal).
- `F1Square/CycleCounts.lean` — the Bowen–Lanford trace identity (R6) `N_m = tr(Bᵐ)` for the example
  graph, `N₁…N₈ = 0,2,6,2,10,14,14,34`, kernel-checked by `decide` on exact integer `Bᵐ`.
- `F1Square/Bridge.lean` — the mechanism bridge (Hodge type ⟹ spectral bound) and the §2.3 control
  mechanized (a rank-1 cos/sin Gram is PSD for ANY spectrum, so its positivity is vacuous w.r.t. RH).
- `F1Square/Crux.lean` — the crux stated faithfully: `HodgeIndex` proved for the Template
  (`template_hodgeIndex`); `CruxFor 𝕊` left OPEN (not forbidden) for the unconstructed square.
- `scripts/honesty_audit.sh` + `scripts/audit_axioms.lean` — the mechanized-honesty gate:
  `#print axioms` over every proof-layer theorem must show only `{propext, Classical.choice,
  Quot.sound}` — no `sorry` (sorryAx), no `native_decide` (ofReduceBool), no stray axioms. Wired into CI.
- `F1Square.lean` now imports the proof layer and carries an elaboration-checked `example` tying the
  manifest's established status fields to the genuine theorems; the crux field stays `none`.

### Changed
- `docs/f1_square_intersection_theory.md` §2 — citation corrections from an independent full-text
  verification (2026-06-06): Pietromonaco (not "Bryan et al.") for 1905.07085; Sagnier (not
  Connes–Consani) for 1703.10521; Moscovici added to the prolate paper; 2310.15367 is a 2023
  "tropical fans" preprint; the Feb-2026 *Jacobian of `Spec ℤ̄`* (2602.15941) proves moduli, **not**
  positivity; the deferred Hermitian-Jacobi computation (critical path to T5) has not appeared.

### Note
- The Riemann Hypothesis remains **open**. The crux (the Hodge index theorem for the 𝔽₁ square) is
  proved nowhere; the honesty audit is a *verifier*, not a prohibition.

## [0.0.1] - 2026-06-06

Initial research base for the 𝔽₁-square / Riemann Hypothesis program.

### Added
- `F1Square.lean` — Lean 4 formalization of the target object
  `Spec ℤ ×_{𝔽₁} Spec ℤ` and its intersection theory, in the `UOR.Bridge.F1Square`
  namespace. Encodes each result's honest epistemic status: verified/classical results
  carry their established status (`universallyValid := some true`); the RH crux (the
  Hodge index theorem) is encoded as not-asserted (`universallyValid := none`) and is
  **never** asserted true. Includes the `F1SquareStatus` roll-up record.
- `docs/` — the three research documents that this formalization companions:
  - `f1_square_intersection_theory.md` — precise specification of the target object,
    the candidate-construction gap table, the named obstructions, and the T1–T5
    verification ladder.
  - `missing_object_over_Q.md` — the four equivalent solution routes and the
    `λₙ` / Hodge-index convergence map.
  - `characteristic_1_constructions.md` — the verified characteristic-1 / tropical
    stack (R1–R16) supplying the 1-dimensional arithmetic-site curve.
- Lake project: `lakefile.lean`, `lean-toolchain` (`leanprover/lean4:v4.16.0`), and
  `lake-manifest.json` pinning the `uor` dependency to UOR-Framework **v0.5.2**
  (`392c7f91e202cf7d119997ac14497444416ed2ce`) — the latest UOR-Framework release that
  ships the `lean4/` library. `lake build` compiles cleanly against this pin.
- Repository infrastructure: `README.md`, `CITATION.cff`, this changelog, `.gitignore`,
  and a GitHub Actions CI workflow that runs `lake build`.

### Notes
- The Riemann Hypothesis remains **open**. This release builds the research *base*, not a
  solution: the formalization compiles and states the construction problem precisely; it
  does not assert the crux.

[0.4.0]: https://github.com/afflom/F1/releases/tag/v0.4.0
[0.3.0]: https://github.com/afflom/F1/releases/tag/v0.3.0
[0.2.0]: https://github.com/afflom/F1/releases/tag/v0.2.0
[0.1.0]: https://github.com/afflom/F1/releases/tag/v0.1.0
[0.0.1]: https://github.com/afflom/F1/releases/tag/v0.0.1
