# v0.17.0 peer-review hardening — findings and resolutions

An adversarial self-review of the stage-C release (the canonical arithmetic square `𝕊` and its
derived intersection lattice), conducted after the six release bricks shipped, with every finding
**resolved in-repo** (no deferrals). Every new theorem is axiom-clean (`{propext, Quot.sound}`,
choice-free) and audited in `scripts/audit_axioms.lean`; the honesty gate passes.

## Findings (each: the weakness → the resolution)

**F1 — Canonicality was proved but not packaged; "unique up to unique isomorphism" was prose.**
The universal property was three separate theorems (`copair_inl/inr/unique`), and the claim that the
universal property *makes `𝕊` canonical* (unique up to canonical isomorphism) was a docstring remark.
→ *Resolved* (`Square/Tensor.lean`): `IsCoproduct` packages the full coproduct property as one
proposition; `sq_isCoproduct` proves it for `(𝕊, inl, inr)`; **`coproduct_unique_upto_iso`** proves
that ANY `(T, i₁, i₂)` satisfying `IsCoproduct` is isomorphic to `𝕊` by the canonical mediating homs,
mutually inverse and matching the injections. "The" tensor is now well-defined *by theorem*.
(Supporting combinators `idHom`, `compHom` added to `Square/Monoid.lean`.)

**F2 — The Λ-tie of the pencil was proven only at primes; prime powers were sampled.**
`pencil_separation_vonMangoldt` covered `Γ_p` for primes `p`; at prime powers the identification
"separation = explicit-formula weight" rested on `Λ(8)`, `Λ(9)`-style sampled values, because
`Λ(pᵏ) = log p` in general needs `spf(pᵏ) = p` — which needs Euclid's lemma, absent from core Lean
(no `Nat.Coprime`/Bézout API).
→ *Resolved* (`Analysis/Mangoldt.lean`): **Euclid's lemma from scratch, Bézout-free**
(`prime_dvd_mul`, via the Gauss descent: reduce the factor mod `q`, and `q` mod the factor, on a fuel
parameter — no gcd machinery), then `prime_dvd_pow`, **`spf_prime_pow`** (`spf(pᵏ) = p`),
`isPrimePow_pow`, and **`vonMangoldt_prime_pow`** (`Λ(pᵏ) = log p` for every prime `p`, every
`k ≥ 1` — the full defining clause of `Λ`, closed). The pencil tie is completed by
**`pencil_separation_pow_vonMangoldt`** (`Square/Pencil.lean`): the separation of `Γ_{pᵏ}` is
`k·Λ(pᵏ)` — the shift lengths now match the explicit-formula weights on the FULL prime-power support
of `Λ`. (Euclid's lemma is also a reusable arithmetic brick for later stages.)

**F3 — Tensor-level imprecision: `⊗_𝔽₁` (monoid) vs `⊗_𝔹` (semiring).**
Header/doc phrasing could be read as claiming the concrete description of the SEMIRING-level tensor
`F ⊗_𝔹 F` over the Boolean semiring — the object Sagnier (arXiv 1703.10521) reports open.
→ *Resolved*: precision paragraphs added to `F1Square.lean` (header), `ROADMAP.md` (stays-open), and
`docs/f1_square_intersection_theory.md` §2.4: what is constructed canonically is the **monoid-level**
tensor (Deitmar 𝔽₁-algebras = commutative monoids); the semiring-level description is finer, remains
open, and is **not** claimed.

**F4 — An unproved claim in a docstring: "the free commutative monoid on the primes".**
Freeness = unique factorization, which is not formalized (and not needed).
→ *Resolved* (`Square/Monoid.lean`): the remark is now explicitly tagged [CLASSICAL], with the honest
scope stated — what the construction *uses* are the proved monoid laws and the prime machinery
(`spf_prime`, now also `prime_dvd_mul`).

**F5 — Asymmetries and silent cases in the divisor layer.**
`vFiber_translate` had no horizontal mirror; the non-divisible case of `Γ_n ∩ H_b` was only a
docstring remark ("cofinal divisible representatives"); `Γ_0` was silently degenerate; the "single
translation class" phrase was not pinned to a theorem.
→ *Resolved* (`Square/Divisors.lean`): **`hFiber_translate`** (the mirror),
**`graph_inter_hFiber_empty`** (`Γ_n ∩ H_b = ∅` when `n ∤ b` — the monoid-level coarseness stated as
a theorem rather than hidden; the stable/tropical count `1` is realized exactly on the divisible
family), **`graph_zero_empty`** (`Γ_0 = ∅`, the pencil is genuinely indexed by `ℕ₊`), and
**`vFiber_translate_unit`** (every vertical fiber is a translate of the unit fiber `V₁` — the precise
"single translation class" used in the `E₁² = 0` moving derivation).

**F6 — A citation error propagated into the proof layer.**
`Template.lean` still credited the sourced `NS(E×E)` form to "Bryan et al., arXiv 1905.07085" — the
companion §2.1 citation verification had already corrected this (1905.07085 is **Pietromonaco**, an
MSc thesis; the underlying DT computation is Bryan, arXiv 1902.08695).
→ *Resolved*: `Template.lean` header corrected to match §2.1.

## What was checked and found sound (no change needed)

- **The honesty gate**: every non-private theorem audited; `{propext, Quot.sound}` only; coverage
  self-enforcing; no `sorry`/`native_decide`/stray axioms; duplicate-leaf-name guard passes.
- **The pencil-blindness boundary** (`square_hodge_pencil_blind`) and the crux discipline: the
  coarse-lattice Hodge index is never presented as the crux; `hodgeIndexHolds`/`liPositivityHolds`
  remain `none` in the manifest, with the sharpened faithfulness caution in `Crux.lean`.
- **The derivation discipline**: no intersection number is hand-entered; `E₃² = −2` is forced by
  bilinearity from point counts (`e3_sq_forced`), and the template emerges (`sqPair_eq_template`).
- **Repo hygiene**: no stale version strings (CITATION at 0.17.0), no TODO/FIXME markers in the
  proof layer, CHANGELOG/ROADMAP/README consistent with the shipped state.

## Stage-D readiness (the v0.18.0 prerequisites, all in place)

The bridge release needs both crux faces statable against concrete objects: the geometric face now
has `Square.squarePolarized` (𝕊's own polarized lattice) plus the proven boundary theorems that pin
*which* Hodge-index statement is the crux (the `H¹`-bearing pairing, not the coarse lattice); the
analytic face has `Li.LiCrux` with the genuine `λ₁`, `λ₂` positivity certificates and the
explicit-formula prime side (`primeSide`, `Λ` now correct on its full support). The equivalence
`HodgeIndex(spectral 𝕊) ⟺ LiPositive λ` is exactly what v0.18.0 states faithfully.
