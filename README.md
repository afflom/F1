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
| [`F1Square/`](F1Square/) | The **genuine-proof layer** — real Lean 4 theorems (no Mathlib, no `sorry`): the function-field Hodge mechanism (`Mechanism`, `Template`), the characteristic-1 base (`CharOne`), exact Bowen–Lanford counts (`CycleCounts`), the mechanism bridge + §2.3 control (`Bridge`), and the crux stated faithfully (`Crux`). |
| [`scripts/honesty_audit.sh`](scripts/honesty_audit.sh) | The mechanized-honesty gate (run in CI): `#print axioms` over every proof-layer theorem must show only `{propext, Classical.choice, Quot.sound}` — no `sorry`, no `native_decide`, no stray axioms. |
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
3. Tag and publish the release: `git tag -a v0.0.1 -m "v0.0.1" && git push --tags`, then create the
   GitHub release for `v0.0.1`.
4. After Zenodo mints the DOI, add a `doi:` field (the concept DOI) to `CITATION.cff` in a follow-up
   commit — exactly the pattern UOR-Framework follows.

## Citation

See [`CITATION.cff`](CITATION.cff). Until the first Zenodo deposit assigns a DOI, cite the repository
and the `v0.0.1` tag.

## License

[MIT](LICENSE) © 2026 Alex Flom.
