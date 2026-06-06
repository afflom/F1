# Changelog

All notable changes to this project are documented here. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and this project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html), starting at `v0.0.1`.

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

[0.0.1]: https://github.com/afflom/F1/releases/tag/v0.0.1
