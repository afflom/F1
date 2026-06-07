# The 𝔽₁ Square with an Intersection Theory

[![DOI](https://zenodo.org/badge/1261199945.svg)](https://zenodo.org/badge/latestdoi/1261199945)

**An active research program toward `Spec ℤ ×_{𝔽₁} Spec ℤ` — the missing surface whose
intersection-positivity is the Riemann Hypothesis.**

> **Status: the Riemann Hypothesis is OPEN.** This repository is the research *base*, not a
> solution. It states the construction problem with precision and formalizes the honest status of
> every piece. The central open object — a 2-dimensional self-product of `Spec ℤ` over `𝔽₁` carrying
> an intersection pairing with a **Hodge index theorem** — is *named, shaped, and partially built*,
> not constructed. The crux is **never** asserted as proven anywhere in this repository.

## The problem, in one paragraph

Over a function field `C/𝔽_q`, the Riemann Hypothesis is a theorem: Frobenius acts on the étale
cohomology of `C × C`, and the **Hodge index theorem** (a positivity) confines its eigenvalues to the
critical circle. Over ℚ the analogous object is missing. RH is exactly the statement that a
still-unconstructed cohomology of "`Spec ℤ` as a curve over `𝔽₁`" carries a Frobenius (the scaling
flow) whose intersection-positivity holds. Every other ingredient — the characteristic-1 base, the
scaling flow, the prime orbits, the trace formula — is built. The one unbuilt thing is the
**2-dimensional square `Spec ℤ ×_{𝔽₁} Spec ℤ` with a Hodge index theorem**, and that
negative-definiteness *is* RH.

## What is in this repository

| path | what it is |
|---|---|
| [`F1Square.lean`](F1Square.lean) | Lean 4 formalization of the target object and its intersection theory (`UOR.Bridge.F1Square`), with the honest status of each result and a `F1SquareStatus` roll-up, now imports the proof layer and carries an elaboration-checked `example` tying each established field to a genuine theorem. |
| [`F1Square/`](F1Square/) | The **genuine-proof layer** — real Lean 4 theorems (no Mathlib, no `sorry`): the function-field Hodge mechanism (`Mechanism`, `Template`), the characteristic-1 base (`CharOne`), exact Bowen–Lanford counts (`CycleCounts`), the mechanism bridge + §2.3 control (`Bridge`), the crux stated faithfully (`Crux`), the tropical κ/spectrum stack incl. the κ⊥spectrum counterexample (`Tropical/`), and the analysis substrate — exact ℚ (a verified ordered field), a reflective ℤ ring normalizer with a from-scratch `ring` tactic (`ring_uor`), constructive ℝ as Bishop regular sequences and ℂ = ℝ×ℝ — both **commutative rings up to `≈`** (multiplication well-defined on the setoid, with associativity and distributivity, via a linear-bound criterion built on the generalized Archimedean lemma), ℝ is **Cauchy complete** (every regular sequence of reals converges to its diagonal limit, choice-free), and the **transcendentals arc** is under construction — Euler's number `e = Σ 1/i!` and the general exponential `exp(q) = Σ qⁱ/i!` on the rational interval `[0,1]`, both built via the exponential series with a rigorous rational error bound (the `exp(q)` bound reuses `e`'s tail bound by termwise domination, `qⁱ/i! ≤ 1/i!`) (`Analysis/`). The **λₙ / RH proof boundary** is now pinned faithfully (`Li`): by Li's criterion RH ⟺ `λₙ > 0 ∀ n ≥ 1`, stated as `LiPositive` on the (unconstructed) genuine ζ-derived Li sequence — the **analytic face** of the crux, encoded open (`none`), with a finite-check guard (`LiPositive = ⋀ all finite truncations`, so no `decide` is a proof) and the Bombieri–Lagarias / Weil-explicit-formula substrate stated as honest interfaces. **ζ and λₙ ship as exact-bounded objects** (`ExactBounded`, `Zeta`): a constructive real is a stream of certified rational enclosures of width `2/(n+1)`, and `ζ(s) = Σ 1/iˢ` for integer `s ≥ 2` is a concrete such object (with a rigorous rational tail bound) — honestly in the convergent regime `Re(s) > 1` only (no zeros; the critical-strip continuation and the genuine `λₙ` values are deferred, not fabricated). ℝ carries a genuine **order `≤`** (`ROrder`): the Bishop `xₙ ≤ yₙ + 2/(n+1)`, reflexive, antisymmetric up to `≈`, and transitive via the Archimedean lemma. ℝ is now a constructive **field with powers** (`Pow`, `Inv`): real powers `Rpow`, the reciprocal `1/x` of a positive real (positivity-as-data, full Bishop regularity), and division `Rdiv`. And the **everywhere-defined exponential `exp` on ℝ** (`ExpReal`) is built as the diagonal of rational partial sums `S_{R j}(x_{R j})` — itself a Bishop-regular sequence of rationals, so a constructive real directly (no limit needed), rigorous via three rational bounds on `expSum`: a geometric truncation tail, a uniform Lipschitz bound, and a factorial-growth estimate. The **transcendentals are now complete** (v0.13.0): **`cos`/`sin`** (`CosSin`) as the alternating diagonal `Σ(−x²)ⁿ/(2n+off)!` dominated by `exp(M²)`, and **`log` on every positive real** (`Log`) as `2·artanh((x−1)/(x+1))` — the artanh odd series on every `[−ρ,ρ]` (`ρ<1`) tamed by a general Bernoulli reindex, composed with the Möbius t-map `q↦(q−1)/(q+1)` (cleared difference identity, 2-Lipschitz on `x≥0`, range bound keeping the argument in `[−ρ,ρ]`). |
| [`scripts/honesty_audit.sh`](scripts/honesty_audit.sh) | The mechanized-honesty gate (run in CI): `#print axioms` over **every** proof-layer theorem must show only `{propext, Quot.sound}` — the proof layer is **choice-free** (`Classical.choice` is eliminated; the two surviving axioms are forced by `omega`/`simp`/`Int` core internals and constructively uncontroversial) — no `sorry`, no `native_decide`, no stray axioms. Coverage is **self-enforcing**: the gate fails CI if any non-private proof-layer theorem is left un-audited. |
| [`docs/f1_square_intersection_theory.md`](docs/f1_square_intersection_theory.md) | Precise specification of the target object (§1), the candidate-construction gap table (§2), the named obstructions (§3), and the T1–T5 verification ladder (§4). |
| [`docs/missing_object_over_Q.md`](docs/missing_object_over_Q.md) | The four equivalent solution routes and the `λₙ` / Hodge-index convergence map. |
| [`docs/characteristic_1_constructions.md`](docs/characteristic_1_constructions.md) | The verified characteristic-1 / tropical stack (R1–R16) that supplies the 1-dimensional arithmetic-site curve. |

## The epistemic convention

The formalization is deliberately honest about what is and is not established. It mirrors the
convention of the upstream UOR-Foundation library:

- `universallyValid := some true` ⇒ asserted established (verified in a runtime, or a classical
  theorem, cited).
- `universallyValid := none` ⇒ **not** asserted proven in this encoding (open or conditional).

The open crux — the Hodge index theorem for the square, which is RH — is encoded with `none` because
it is open. The mechanized audit ([`scripts/honesty_audit.sh`](scripts/honesty_audit.sh)) makes this
honesty a **verifier, not a prohibition**: it forbids `sorry` / `native_decide` / stray axioms in the
proof layer, not a genuine proof. No field asserts an unproven claim as true; if the crux is ever
genuinely (axiom-clean, faithfully) proved, its status becomes `some true` because that is then the
truth. Results that *are* established
(the intersection-pairing template, the ample class on the template, the parallel-pencil structure)
carry their genuine status; the crux does not.

## Dependency

The Lean formalization extends the **UOR-Foundation** library and is pinned, for reproducibility, to
[`UOR-Framework` **v0.5.2**](https://github.com/UOR-Foundation/UOR-Framework/releases/tag/v0.5.2) —
the latest UOR-Framework release that ships the `lean4/` library. The exact revision is frozen in
[`lake-manifest.json`](lake-manifest.json).

## Building

Requires [`elan`](https://github.com/leanprover/elan) (the Lean toolchain manager). The toolchain
version (`leanprover/lean4:v4.16.0`) is read from [`lean-toolchain`](lean-toolchain).

```sh
lake update   # resolve and fetch the pinned `uor` dependency (first time only)
lake build    # compile F1Square against UOR-Framework v0.5.2
```

CI runs `lake build` on every push and pull request.

## Versioning

This project uses [Semantic Versioning](https://semver.org), starting at **v0.0.1**. See
[`CHANGELOG.md`](CHANGELOG.md).

## Publishing (Zenodo)

This repository is prepared for archival on [Zenodo](https://zenodo.org) the same way
`UOR-Framework` is: metadata flows from [`CITATION.cff`](CITATION.cff) (no `.zenodo.json` is used),
and a tagged GitHub release triggers a DOI. The remaining, account-gated steps for the maintainer:

1. Confirm the `repository-code` URL in `CITATION.cff` matches the published GitHub repo.
2. Enable the repository in the Zenodo ↔ GitHub integration.
3. Tag and publish the current release: `git tag -a v0.9.0 -m "v0.9.0" && git push --tags`, then
   create the GitHub release for that tag (substitute the version being released).
4. After Zenodo mints the DOI, add a `doi:` field (the concept DOI) to `CITATION.cff` in a follow-up
   commit — exactly the pattern UOR-Framework follows.

## Citation

See [`CITATION.cff`](CITATION.cff). Until the first Zenodo deposit assigns a DOI, cite the repository
and the current release tag (e.g. `v0.9.0`).

## License

[MIT](LICENSE) © 2026 Alex Flom.
