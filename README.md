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
| [`F1Square/`](F1Square/) | The **genuine-proof layer** — real Lean 4 theorems (no Mathlib, no `sorry`): the function-field Hodge mechanism (`Mechanism`, `Template`), the characteristic-1 base (`CharOne`), exact Bowen–Lanford counts (`CycleCounts`), the mechanism bridge + §2.3 control (`Bridge`), the crux stated faithfully (`Crux`), the tropical κ/spectrum stack incl. the κ⊥spectrum counterexample (`Tropical/`), and the analysis substrate — exact ℚ (a verified ordered field), a reflective ℤ ring normalizer with a from-scratch `ring` tactic (`ring_uor`), constructive ℝ as Bishop regular sequences and ℂ = ℝ×ℝ — both **commutative rings up to `≈`** (multiplication well-defined on the setoid, with associativity and distributivity, via a linear-bound criterion built on the generalized Archimedean lemma), ℝ is **Cauchy complete** (every regular sequence of reals converges to its diagonal limit, choice-free), and the **transcendentals are built from first principles** (`Analysis/`) — beginning with Euler's number `e = Σ 1/i!` and the general exponential `exp(q) = Σ qⁱ/i!` on the rational interval `[0,1]`, both via the exponential series with a rigorous rational error bound (the `exp(q)` bound reuses `e`'s tail bound by termwise domination, `qⁱ/i! ≤ 1/i!`), and extended below to all of ℝ. The **λₙ / RH proof boundary** is now pinned faithfully (`Li`): by Li's criterion RH ⟺ `λₙ > 0 ∀ n ≥ 1`, stated as `LiPositive` on the (unconstructed) genuine ζ-derived Li sequence — the **analytic face** of the crux, encoded open (`none`), with a finite-check guard (`LiPositive = ⋀ all finite truncations`, so no `decide` is a proof) and the Bombieri–Lagarias / Weil-explicit-formula substrate stated as honest interfaces. **ζ and λₙ ship as exact-bounded objects** (`ExactBounded`, `Zeta`): a constructive real is a stream of certified rational enclosures of width `2/(n+1)`, and `ζ(s) = Σ 1/iˢ` for integer `s ≥ 2` is a concrete such object (with a rigorous rational tail bound) — honestly in the convergent regime `Re(s) > 1` only (no zeros; the critical-strip continuation and the genuine `λₙ` values are deferred, not fabricated). ℝ carries a genuine **order `≤`** (`ROrder`): the Bishop `xₙ ≤ yₙ + 2/(n+1)`, reflexive, antisymmetric up to `≈`, and transitive via the Archimedean lemma. ℝ is now a constructive **field with powers** (`Pow`, `Inv`): real powers `Rpow`, the reciprocal `1/x` of a positive real (positivity-as-data, full Bishop regularity), and division `Rdiv`. And the **everywhere-defined exponential `exp` on ℝ** (`ExpReal`) is built as the diagonal of rational partial sums `S_{R j}(x_{R j})` — itself a Bishop-regular sequence of rationals, so a constructive real directly (no limit needed), rigorous via three rational bounds on `expSum`: a geometric truncation tail, a uniform Lipschitz bound, and a factorial-growth estimate. The **transcendentals are now complete** (v0.13.0): **`cos`/`sin`** (`CosSin`) as the alternating diagonal `Σ(−x²)ⁿ/(2n+off)!` dominated by `exp(M²)`, and **`log` on positive reals** (`Log`) as `2·artanh((x−1)/(x+1))` — the artanh odd series on every `[−ρ,ρ]` (`ρ<1`) tamed by a general Bernoulli reindex, composed with the Möbius t-map `q↦(q−1)/(q+1)` (cleared difference identity, 2-Lipschitz on `x≥0`, range bound keeping the argument in `[−ρ,ρ]`). `log` is genuine **positivity-as-data** — the *same* idiom as the reciprocal `Rinv`: from a witness `x_k > 1/(k+1)`, `RlogPos x k` **derives** the rational modulus `1/M ≤ x ≤ M` (`M = |x₀| + 2 + 1/L`, `L = δ/2` the witness floor) rather than demanding it of the caller (constructively a modulus is *necessary* — `log` has no uniform modulus of continuity on `(0,∞)`). The example binds `log 2` built through this path. The **analytic constants of the Li/Keiper bridge** are now built (v0.14.0): **π** (`Pi`) via Machin's `16·arctan(1/5) − 4·arctan(1/239)` as one Bishop-regular diagonal (with `π ≥ 6/5` for `Pos π` and the tight `π ≤ 3.142` from the alternating arctan truncation at the tightest radius), the clean logs **`log 2`/`log π`/`log 4π`** with kernel-certified upper bounds (`log 2 ≤ 0.6931`, `log π ≤ 1.1453`; the varying `π`-argument is dominated by the constant `15/29 = tmap(22/7)` then geometrically truncated), and the **convergence-accelerated Euler–Mascheroni constant** `γ = Σ(1/i − 2·artanh(1/(2i+1)))` with `γ ≥ 0.54` — feasible where the alternating-ζ-series `γ` is not (that series' running `lcm` denominator already has ~7000 digits at depth 2). These culminate in the **first Li/Keiper coefficient `λ₁ = ½·(2 + γ − log 4π)` as a *positivity-certified* constructive real**: `Rlambda1_pos : Pos Rlambda1` (`λ₁ ≈ 0.0231 > 0`), carried through the ℝ-order bridges. This realizes the `n = 1` slice of Li's criterion as **evidence** — it does **not** assert `λₙ > 0 ∀ n` (which *is* RH); the crux stays `none` and RH stays open. The **complex analytic engine — exponential core** is now built (v0.15.0): `exp` is a genuine **homomorphism on all of ℝ** (`ExpRealAdd`, `RexpReal_add : exp(x+y) ≈ exp x · exp y`), the diagonal lift of the rational Cauchy-product functional equation (signed corner bound → deep-reference reconciliation); the **Pythagorean identity `cos² + sin² ≈ 1`** (`CosSinAdd`) via the trig Cauchy product, giving `|cos|,|sin| ≤ 1` (`CosSinBound`); the **complex exponential** `Cexp z = exp(re z)·(cos(im z) + i·sin(im z))` (`ComplexExp`); and `nˢ = Cexp(s·log n)` (`ComplexPow`) with the **modulus identity** `|Cexp z|² = (exp Re z)²` (`ComplexMod`) — the squared modulus depends only on `Re s`. The **ζ-convergence gate `exp∘log = id`** is now closed (v0.15.1): the power-series composition identity **`exp(2·artanh τ) = (1+τ)/(1−τ)`** (`Rexp_two_artanh_ofQ`) — composing the exp factorial series with the artanh geometric series from scratch (corner bound `exp_corner_le`, rational identity `exp_artanh_rat_cleared`, diagonal reconciliation `Rexp_two_artanh_via`) — and its corollary **`exp(log n) = n` for the *literal* `Rlog` term** (`Rexp_log_nat_Rlog`: `RexpReal (Rlog (ofQ n) …) ≈ n`; the radius-general construction matches `Rlog`'s own convergence radius by definitional equality, so no `τ²≤½` smallness is needed), both axiom-clean. This unlocks the squared-modulus tail `|n^{-s}| = n^{-Re s}`. **ζ for complex argument is now built (v0.15.2):** `Czeta s = Σ_{n≥1} n^{-s}` for *complex* `s` with `Re s > 1` (witnessed by a rational `τ > 0`, `τ ≤ (Re s − 1)·log 2`) is a genuine constructive ℂ — its real and imaginary parts are Bishop diagonal limits (`Rlim`) of the reindexed dyadic partial sums `Σ_{n<2^{M(j)}} Re/Im(n^{-s})`, converging with the canonical rate `2/(k+1)` (`Czeta_re/im_tendsTo`). The convergence proof is the full dyadic-geometric stack: log-multiplicativity `log(2ᵏ) = k·log 2` via exp injectivity (`RexpReal_inj`, re-routing the artanh addition boundary wall), the block modulus bound `≤ ofQ(rᵏ)` (`r = 1/(1+τ) < 1`), the geometric tail `Σ rᵏ ≤ rʲ/(1−r)` (`geoFrom_le`), the Bernoulli reindex `r^{M(j)}/(1−r) ≤ 1/(j+1)` (`geom_reindex`, `M(j) = (j+1)·r.den²`), and the completeness bridge `seq_diff_le`/`RReg_of_real_bound` (a real bound becomes the rational Cauchy condition `RReg`) feeding Bishop's `Rlim`. This is ζ across its *full* convergent half-plane `Re s > 1` (no zeros), not merely integer `s ≥ 2`; the critical-strip continuation and the genuine `λₙ` stay deferred (`liPositivityHolds = none`, RH open); nothing is faked. The **explicit formula's arithmetic ingredient is now built (v0.15.3):** the **von Mangoldt function** `Λ` (`Mangoldt`, via the smallest factor `spf` — `Λ(4) = log 2`, `Λ(6) = 0`, `Λ ≥ 0`, computable so the values hold by reduction) and the **prime side** `Σ_p Σ_k log p · h(k log p) = Σ_{n≥2} Λ(n)·h(log n)` (`primeSide`) — a finite sum for compactly-supported `h` (constant past the support cutoff, `primeSide_stable`), hence a genuine real. And the **Bombieri–Lagarias decomposition of `λ₁`** (`LiOne`, `Rlambda1_decomposition`): `λ₁ = λ₁^{arith} + λ₁^{∞} = γ + (1 − γ/2 − ½·log 4π)`, the finite/arithmetic place `S_f(1) = −η₀ = γ` plus the archimedean `S_∞(1)`, **promoting `Li.LiDecomposition` from the trivial inhabitant `λ = λ + 0` to a proven non-trivial instance** (`li_decomposition_realized`) whose `n = 1` slice is the genuine two-place split (deriving `γ` from the prime sum needs `ζ'/ζ` continuation, deferred and faithfully labelled, not fabricated; the crux stays `none`, RH open). **Stage B is now complete (v0.16.0)** — the three goals: **(B) `ζ(s)` on the critical strip `0 < Re s < 1`** via the integration-free **Dirichlet-eta** route, where `η(s) = Σ(−1)^{n−1}n⁻ˢ` converges by bounded variation across the whole strip the raw `ζ` series cannot reach: `Ceta` (`EtaVariation`) is `η(s)` for every `Re s > 0` as a constructive ℂ (the diagonal limit of the reindexed paired partial sums through the full dyadic-geometric `RReg` stack adapted to `σ > 0`), and `CzetaStrip` (`CriticalZeta`) is `ζ(s) = η(s)/(1 − 2^{1−s})` with the non-vanishing `etaDenom_Pos_normSq` (`|1 − 2^{1−s}|² ≥ (2^{1−σ}−1)² > 0`, the spurious zeros all on `Re s = 1`) and the certificate `CzetaStrip_functional : (1 − 2^{1−s})·ζ ≈ η` — the real/imaginary parts are `ExactBoundedReal` automatically; **(A) the archimedean `Γ′/Γ` place** (`Gamma`): the single real-power combinator `RrpowPos x y = exp(y·log x)` (so `√(2π) = exp(½·log 2π)` — no sqrt primitive, no complex `Clog`), the **exact** digamma `ψ = Γ′/Γ` (`Digamma`, the convergent series `−γ + Σ[1/(n+1) − 1/(n+z)]` → `RReg`/`Rlim`, reusing `Rgamma_h`), and `SpougeGamma`, Spouge's `Γ`-approximant built only from `exp`/`log`/reciprocal of positive reals (Spouge's explicit relative-error bound is cited, not formalized — a rigorous proof presupposes an independent `Γ`, so the exact archimedean place is carried by `Digamma`); **(C) `Pos λ₂`** (`LambdaTwo`, `Rlambda2_pos`, `λ₂ ≈ 0.0043 > 0`) — the higher-Stieltjes-`γₙ` → `λₙ` capstone, a `λ₁`-style positivity certificate at `n = 2`, **evidence** for Li's criterion (not the crux): `liPositivityHolds` stays `none`, `λₙ > 0 ∀ n` (= RH) and the off-line zeros remain deferred, RH open. **Stage C is now complete (v0.17.0)** — the **canonical arithmetic square `𝕊 = Spec ℤ ×_𝔽₁ Spec ℤ` is constructed and mechanized** (`Square/`): Deitmar 𝔽₁-algebras are commutative monoids and `𝔽₁` (the trivial monoid) is proved **initial**, so the tensor `F ⊗_𝔽₁ F` is the plain coproduct — realized as `ℕ₊ × ℕ₊` with the **universal property proved** (`copair_unique`; canonicality = the universal property, not a candidate model), strictly 2-dimensional (`gen2_injective` — the §3.1 ℤ-collapse avoided by theorems), projections recovering the curve; the **intersection lattice is derived, never entered by hand** (every primitive number a point count with translation-pencil moving, `Δ² = 0` from the parallel-pencil disjointness itself, `E₃² = −2` forced by bilinearity, the sourced product-of-curves template **emerging** as a consistency theorem `sqPair_eq_template`, the five §2.2 gate self-checks as theorems, the class lattice finitely generated); the **parallel pencil carries the arithmetic as constructive-real shift lengths** (`pencil_separation`: constant `log n`; `= Λ(p) = log p` at primes — the explicit-formula prime weight, reached geometrically); and the polarized instance `squarePolarized` (now `𝕊`'s own lattice) satisfies the **Hodge index** (`square_hodgeIndex`) — **which is provably pencil-blind** (`square_hodge_pencil_blind`: `[Γ_n] = [Δ]`, `Δ·Γ_n = 0` ∀n — no spectral input, the §2.3-control geometric face), so it is **not** the crux: the crux is the Hodge index / Weil positivity of the `H¹`-bearing pairing (⟺ `λₙ ≥ 0`), `hodgeIndexHolds`/`liPositivityHolds` stay `none`, RH open. **Stage D is now complete (v0.18.0)** — **the bridge and the crux attempt**: the function-field anchor is a genuine lattice derivation (`BridgeFF.ff_hodge_iff_hasse`: Hodge-index negativity on the primitive `{Δ,Γ}`-span ⟺ the Hasse bound `a² ≤ 4q`, with the trace datum `Δ·Γ = q+1−a` inside the lattice — the v0.1.0 governor is now DERIVED); the λ₂ Bombieri–Lagarias split is a theorem (`Rlambda2_decomposition`) and `Li.LiDecomposition` is realized with two genuine certified slices; **the geometric and analytic faces of the crux are proven equivalent** (`Square/Spectral.lean`: the `SpectralSquare` interface with the dictionary `⟨Cₙ,Cₙ⟩ = −2λₙ`, and `crux_faces_equivalent : SpectralCrux S ⟺ Li.LiCrux S.lam` — a genuine constructive theorem), inhabited with the certified `λ₁, λ₂` (`⟨C₁,C₁⟩ < 0`, `⟨C₂,C₂⟩ < 0`) and guarded by theorems (`spectralTwoSlice_not_crux`: no finite assembly of certified slices can be passed off as RH); and **the crux attempt ran under the gate** (`Square/Attempt.lean`): certified through `n = 2`, frontier exact (`crux_attempt_frontier`: the crux ⟺ `∀ n ≥ 3, λₙ > 0`; the next slice needs the second Stieltjes constant `γ₂`), post-mortem recorded — **the universal did not close**, so `hodgeIndexHolds`/`liPositivityHolds` stay `none` and RH stays open, with the bridge substrate shipped exactly as scoped. |
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
[`CHANGELOG.md`](CHANGELOG.md) for the release history and [`ROADMAP.md`](ROADMAP.md) for the remaining
construction of the F1 square, scoped into releases v0.15.0–v0.19.0 (the crux stays `none` until RH is
genuinely proven).

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
