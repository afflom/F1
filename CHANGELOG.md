# Changelog

All notable changes to this project are documented here. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and this project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html), starting at `v0.0.1`.

## [0.20.0] - 2026-06-13

### Added — stage F: the UOR construction of the crux — the canonical `H¹`-object and the FORCED dictionary (pure Lean 4, no Mathlib, no `sorry`, choice-free)

The v0.18.0 bridge carried the dictionary `⟨Cₙ,Cₙ⟩ = −2λₙ` as INTERFACE DATA — a `SpectralSquare`
field that any instance supplied definitionally (`cSq := −2λ`, `dict := rfl`). Stage F removes
that assumption and **derives** the dictionary, mirroring `BridgeFF`'s dictionary column over ℤ: a
genuine rank-4 Néron–Severi-style lattice, the primitive projection with PROVEN orthogonality, and
the self-pairing computed from the Gram. **The gate then ran on the constructed object and LOCATED
THE FRONTIER** — the forced signature did *not* come out positive (proving `λₙ > 0 ∀n` *is* RH), so
the construction is complete down to one irreducible input (the genuine Stieltjes η-tail = the
zeros) and `hodgeIndexHolds`/`liPositivityHolds` stay `none` — the gate flips the instant a
faithful, axiom-clean proof of the criterion lands; until then **RH stays OPEN**. Every theorem is
choice-free (`{propext, Quot.sound}`), audited; the build is warning-free; the gate passes.

- **A1 — the `H¹` carrier by universal property** (`F1Square/Square/Cohomology.lean`): a
  `FrobSys` is a carrier with a scaling/Frobenius action `φ` and a fundamental class `g`; the
  canonical `H¹` is `H1 = (ℕ, succ, 0)`, the **free / initial Frobenius system on one generator**
  — a morphism out of it is FORCED (`H1_universal`, `H1_isFree`, `freeFrob_unique_upto_iso`),
  exactly as the coproduct forced `𝕊` (v0.17.0). The Frobenius orbit **realizes the built
  prime-power pencil** as ONE equivariant identification (`orbit_realizes_pencil` — the orbit
  position's log-separation from the diagonal equals the built `pencil_separation_pow`;
  `orbitShift_succ` — each Frobenius step adds `log p = Λ(pᵏ)`, the Connes–Consani closed orbit).
  Honest scope: this builds the ABSTRACT carrier of the action, NOT the genuine spectral `H¹`
  (whose spectrum is the zeros) — that is the open frontier.
- **A2 — the intrinsic lattice and the trace datum** (`F1Square/Square/WeilLattice.lean`): `hPair`
  is the symmetric bilinear form on the rank-4 lattice `{F_h, F_v, Δ, Γ}` with the sourced/derived
  ruling intersections and the spectral data `Δ², Γ², Δ·Γ` as parameters. The vanishing cycle
  `Cₙ = Δ − Γₙ` is **proven GENUINELY PRIMITIVE** — orthogonal to both rulings for every spectral
  datum (`vanCyc_perp_Fh`, `vanCyc_perp_Fv`, the `BridgeFF.primDG_perp` analog) — not hand-picked.
  On `𝕊`'s coarse lattice the spectral data is `Δ²=Γ²=Δ·Γ=0` (pencil-blind, `vanCyc_blind`); the
  `H¹` enrichment lifts `Δ·Γₙ` to the explicit-formula value `λₙ`.
- **A3 — THE FORCED DICTIONARY**: the vanishing-cycle self-pairing is `Δ²−2(Δ·Γ)+Γ² = dd+gg−2dg`
  (`vanCyc_selfpair_gen`, the `BridgeFF.primDG_sq` analog), the `−2` being the lattice's own cross
  term. The geometric inputs `Δ²=Γ²=0` are **TIED to the v0.17.0 derived lattice**
  (`vanCyc_selfpair_built`, from `pair_diag_self_derived`/`pair_graph_self_derived`), not plugged.
  `IntrinsicH1` is **assumption-free by construction** — its only datum is `lam`; `cSq` is FORCED
  to the pairing diagonal, so no false dictionary CAN be inhabited; `intrinsicH1_dict` is a
  theorem. `genuineSpectralSquare` routes through it, so `⟨Cₙ,Cₙ⟩ = −2λₙ` is now DERIVED
  (`genuineSpectralSquare_dict`), not a field — the v0.18.0 interface converted to construction.
- **B — the forced signature and the located frontier** (`F1Square/Square/Forced.lean`):
  `genuine_vanCyc_normal` (`−⟨Cₙ,Cₙ⟩ = 2λₙ`, the completed-square normal form);
  `genuine_crux_equivalent` (the geometric crux on the constructed object ⟺ `LiCrux genuineLamSeq`
  = RH, now on an object whose dictionary is a theorem); `genuine_evidence_head` (`⟨C₁,C₁⟩ < 0`,
  `⟨C₂,C₂⟩ < 0` on the DERIVED object). **`genuine_crux_frontier_located` pins the FRONTIER** as
  one proposition: the forced criterion is exactly `∀n, Pos (genuineLamSeq n)`, the head `λ₁,λ₂`
  is discharged, no finite run reaches it (`genuine_iff_all_upTo`), and it is satisfiable
  (`genuine_signature_satisfiable`, no hidden impossibility) — the remaining input is the genuine
  Stieltjes η-tail (the zeros; the truncated `etaTwoSlice` is not it), and the gate flips the
  instant a faithful proof of the criterion lands. **Which
  `BridgeFF` column is done, which is open**: the DICTIONARY column (`primDG_sq`) is now a genuine
  theorem; the SIGNATURE-FORCING column (`ff_hodge_iff_hasse`, where the function field's `4q−a²`
  completed square forces the bound) has no unconditional analog over ℤ — the forced criterion is
  RH.
- **The roll-up** (`F1Square.lean`): the stage-F backing block and elaboration-checked witness
  (the carrier's universal property, the proven primitivity, the built-tied dictionary, the forced
  criterion, the located frontier); the crux fields stay `none`. The dictionary is a theorem;
  the construction is complete down to its one honest input (the η-tail / the zeros); the
  positivity does not close from anything built. **RH stays OPEN.**
- **The Voros growth dichotomy, mechanized** (`F1Square/Analysis/Voros.lean`) — a frontier brick.
  Voros (*Math. Phys. Anal. Geom.* 9 (2006)) is the sharpest statement of the RH-hardness of Li
  positivity: `λₙ` has exactly two mutually-exclusive asymptotic forms — tempered `∼ (n/2)log n`
  (RH) vs exponentially oscillating `∼ Σ((τₖ+i/2)/(τₖ−i/2))ⁿ` (¬RH), no third option. The genuine
  CONSTRUCTIVE skeleton is built unconditionally: `tempered_not_exp`/`exp_not_tempered` — a
  polynomially-bounded sequence (`|λₙ| ≤ C(n+1)²`) can NEVER exceed `2ⁿ` infinitely often (the
  regimes are disjoint), via `cube_le_pow2` (`(n+1)³ ≤ 2ⁿ`, `n ≥ 11`) → `quad_lt_pow2`. The
  RH-equivalent *identification* of a regime (the saddle-point content) stays faithful interface.
  Deep-research-confirmed (104 agents) against the primary Voros/Coffey/Lagarias/Yoshida sources,
  which pin the genuine unconditional levers (Coffey's `λₙ ≥ trend − |S2|`, math-ph/0505052;
  Yoshida–Bombieri small-support Weil positivity) — all bottoming out at the same `|S2|`/RH-hard
  step, so no unconditional closure exists.
- **The second Stieltjes constant `γ₂ ≈ −0.00969` as a genuine constructive real**
  (`F1Square/Analysis/GammaTwo.lean`) — `Rgamma2 := Rlim g2SeqDyadic`, the `H¹`-object ingredient
  feeding `λ₃`. The defining sequence `g₂(N) = Σ_{k≤N}(ln k)²/k − ⅓(ln N)³` telescopes to `Σ eₖ`,
  `eₖ = (ln k)²/k − ⅓((ln k)³−(ln(k−1))³)`; the cubic-difference algebra (`cube_diff_identity`,
  `tri_sum_3a2` — discharged by the new UOR **`RAddNF`** signed-atom normalizer, the κ-form solution
  to the absent Real ring/abel tactic) yields the two-sided per-step envelopes
  `−ln(p+1)²/(p(p+1)) ≤ eₖ ≤ ln(p+1)/p²`. These are summed over dyadic blocks (log/log² caps
  `logN(j+2) ≤ a+2`) and telescoped with the discrete antiderivatives `T_U(m)=(4m+12)/2^m` and the
  QUADRATIC `T_L(m)=(2m²+12m+22)/2^m` — the new ingredient over `γ₁`, whose outer sum was linear.
  Reindex `M(j)=2j+8` with domination `(j+1)(2M²+12M+22) ≤ 2^M` (via `8j²+88j+246 ≤ 2^{j+8}`) gives
  pairwise Cauchy `±1/(j+1)` → `RReg_of_real_bound` → `Rlim`. Choice-free (`{propext, Quot.sound}`),
  audited. Mirrors the `GammaOne`/`γ₁` regularity endgame column-for-column. The tight numeric
  bracket (`γ₂ ≥ −0.02`) is the open computational frontier: the dyadic tail is loose (`T_L(8) ≈
  0.96`) and a tight bracket needs an anchor `N ∼ 10⁴` (`ln²N/N ≲ 0.01`), beyond kernel `decide`'s
  reach with the current artanh log-evaluator — `γ₂`'s tail is `ln²(N)/N`, intrinsically heavier
  than `γ₁`'s clean `1/(2N)`.
- **The third Li coefficient `λ₃` in closed form** (`F1Square/Analysis/LambdaThree.lean`) — the next
  rung of the genuine λ-ladder, the first to carry `γ₂` (`Rgamma2`). The genuine `λₙ = λₙ^{arith} +
  λₙ^{∞}` is already general; this adds the next η-anchor (deep-research-confirmed
  Bombieri–Lagarias / Keiper–Li): **`η₂ = −γ³ − 3γγ₁ − (3/2)γ₂`** (`Reta2`, the first anchor needing
  `γ₂`), the `StieltjesEta3` structure extending `StieltjesEta` with it, and `λ₃^{arith} = −(3η₀ +
  3η₁ + η₂)` (`Rlambda3_arith`). The archimedean side `λ₃^{∞} = genuineArchSeq 3` (already general,
  via `ζ(2), ζ(3)`) needs no new work, so `Rlambda3 = λ₃^{arith} + λ₃^{∞}` is a closed-form
  constructive real. For ANY η-data anchored through `η₂` the genuine ladder meets it at `n = 3`
  (`genuineArith_three`, `genuineLam_three`) exactly as at `n = 1, 2` — the closed form is faithful,
  not ad hoc. `Pos λ₃` is NOT claimed: it is gated by a tight numeric bracket on `γ₂` (the `η₂`
  coefficient is `3/2`), the open Euler–Maclaurin sharp-tail frontier (`γ₂`'s `ln²N/N` tail is
  heavier than `γ₁`'s clean `1/(2N)`). Choice-free, audited. The crux fields stay `none`.
- **Lever 1 — the Li/zero growth geometry** (`F1Square/Analysis/ZeroGeometry.lean`): the constructive
  bridge from a zero's POSITION to the GROWTH of its Li contribution, feeding the Voros dichotomy and
  the de la Vallée-Poussin zero-free region. Each Riemann zero `ρ` contributes `1 − (1−1/ρ)ⁿ` to
  `λₙ`, whose growth is governed by the squared ratio `|1−1/ρ|² = |ρ−1|²/|ρ|²`. The genuine
  constructive nugget, proved unconditionally and without `sqrt` (`liRatio_diff_eq`):
  **`|ρ−1|² − |ρ|² = 1 − 2·Re ρ`** — the `Im ρ` terms cancel exactly, so the regime is fixed by which
  side of the critical line the zero lies on: `Re ρ = ½` ⟹ ratio `1` (bounded, Voros's tempered/RH
  seed, `liRatio_on_line`); `Re ρ < ½` ⟹ ratio `> 1` (an exponentially growing Li term, the ¬RH seed,
  `liRatio_left_of_line`); `Re ρ > ½` ⟹ ratio `< 1` (`liRatio_right_of_line`). The dVP band
  (`DVPBand δ`) does NOT collapse to the line — `dvp_band_admits_off_line` exhibits a band-resident
  off-line zero (ratio `> 1` AND band membership coexisting), so `DVPBand δ` for `δ > 0` is strictly
  weaker than `AllZerosOnLine`; that residual gap (band ⟹ line) is RH itself. The additive
  rearrangements run through the genuine abelian-group laws (`Req_of_seq_Qeq` can't see through
  `Rmul`'s nor reshape `Radd`'s Bishop reindexing). WHERE the zeros sit, and that the SUM `λₙ`
  inherits a single term's growth (Voros's saddle-point), stay [CLASSICAL] interface; the crux fields
  stay `none`.
- **The UOR Real additive-group normalizer `RAddNF`** (`F1Square/Analysis/RAddNF.lean`) — the κ-form
  solution to the central mechanization blocker. `ring_uor` is Int/ℚ-only and the pointwise Real
  route clears denominators multiplicatively (any atom occurring 3+ times explodes), so additive
  Real identities had no tactic. `RsumL` canonicalizes a `Radd`/`Rneg`/`Rsub` tree to a list of
  signed-atom summands; equality is decided by the multiset (`RsumL_perm` permutation-invariance +
  `RsumL_cancel_anywhere` choice-free positional cancellation — no `List.Perm` `decide`, which pulls
  `Classical.choice`). The reusable abelian-group analogue of `ring_uor`; it drives the `γ₂` cubic
  telescoping and every `λₙ` assembly.
- **The UOR Real multiplicative normalizer `RMulNF`** (`F1Square/Analysis/RMulNF.lean`) — the κ-form
  companion of `RAddNF`, the second half of a `Real` "ring" engine. Real MULTIPLICATIVE identities had
  no tactic for the same reason additive ones didn't (`ring_uor` is ℤ/ℚ-only; the pointwise route
  can't see through `Rmul`'s Bishop reindexing). `RprodL` canonicalizes a `Rmul`-tree to the product
  of a factor LIST; equality is decided by the multiset (`RprodL_perm`, from the genuine `Rmul`
  commutativity/associativity). Permutation-only — `Real` has no universal multiplicative inverse, so
  there is no cancellation layer (all degree-`d` monomial normalization needs is permutation).
  `Rmul_pair_eq_RprodL4` is the degree-4 flatten; `prod_sq_reassoc` (`(ac)² ≈ a²c²`) and
  `prod_cross_reassoc` (`(ac)(bd) ≈ (ad)(bc)`) are the validated monomial atoms (the square and the
  cross-term of `|zw|² = |z|²|w|²`), with the permutations built EXPLICITLY via `List.Perm`
  constructors (`decide` on `List.Perm` pulls `Classical.choice`). With `RAddNF` this stands in for a
  `Real` `ring` tactic: expand to monomials, normalize each with `RprodL_perm`, match the sum with
  `RsumL_perm`. Choice-free, audited.
- **Honesty-gate rigor fix** (`scripts/honesty_audit.sh`) — load-bearing. Checks 3 (no
  `sorry`/`native_decide`) and 4 (choice-free) used `… | grep -q …` inside an `if`-condition
  under `set -o pipefail`: a matching `grep -q` exits early, SIGPIPEs the upstream `grep`, and
  pipefail makes the pipeline's status that non-zero code — which `if` reads as FALSE, so the
  FAIL branch never ran. **The forbidden-axiom and choice-free gates were effectively disabled.**
  Fixed (capture-then-test, no `grep -q`); verified the gate now FIRES on violations and PASSES
  clean. The fix exposed and removed a pre-existing `Classical.choice` leak (`graph_one_diag`,
  `omega` on an `↔`; reproved `Nat.one_mul`+`eq_comm`) — so the choice-free claim
  (`{propext, Quot.sound}` only) is now genuinely *enforced*, not merely asserted.

## [0.19.0] - 2026-06-13

### Added — stage E: completion — the explicit formula, the dominance face, the roll-up (pure Lean 4, no Mathlib, no `sorry`, choice-free)

The three stage-E release goals are delivered: **the explicit-formula trace is completed** (the zero
side realized at the Bombieri–Lagarias slices), **the remaining `Li` interfaces are retired** at the
built slices, and **the final F1-square roll-up** records the v1.0.0-candidate state — plus **THE
DOMINANCE FACE**: the crux as a single uniform bound, proven equivalent to both prior faces. The
crux did not close — now a *sourced* result, not a presumption — so `hodgeIndexHolds`/
`liPositivityHolds` stay `none` and **RH stays OPEN**. Every theorem is choice-free
(`{propext, Quot.sound}`), audited; the build is warning-free; the gate passes.

- **The completed explicit-formula trace** (`F1Square/Analysis/LiComplete.lean`) —
  `Li.ExplicitFormulaTrace`, until now inhabited only by the trivial split `z = z + 0`, is REALIZED
  with the genuine three-sided reading at both built slices (`explicitFormulaTrace_one_realized`,
  `explicitFormulaTrace_two_realized`): zero side `λ₁`/`λ₂` (the sum-over-zeros reading is
  [CLASSICAL], BL 1999 — the zeros are not constructed and nothing pretends they are), finite-place
  closed forms `γ` and `2γ − (γ² + 2γ₁)`, archimedean parts — all three reals built. Packaged as the
  **`WeilTrace` ladder** (`weilTraceTwo`, the trace identity at every positive index;
  `weilTraceTwo_evidence`). Convention notes pinned (deep-research-verified): the Lagarias⟷BL
  grouping (`λₙ = S∞(n) − S_f(n) + 1` vs `λₙ^{arith} = −S_f`, `λₙ^{∞} = S∞ + 1`, confirmed against
  both built slices to 30 digits); the arithmetic closed form sourced from the η-polynomial form
  (the arXiv print of Lagarias eq. (4.13) carries a sign typo — not used); unconditionally the
  finite-place part equals the zero sum truncated at height `√n` up to `O(√n·log n)` (Lagarias
  Thm 6.1) — the precise sense in which the prime side IS an incomplete zero side.
- **`Li.LiAgreesWith` retired at the built slices** (`liAgreesWith_two_realized`) — computed (the
  direct certified builds `Rlambda1` via the accelerated-γ assembly, `Rlambda2` via the
  Stieltjes/ζ(2) assembly) agrees with classical (the BL closed-form assemblies,
  `liClassicalSeqTwo`) — genuinely non-reflexive at `n = 1, 2`, the agreement being the content of
  `Rlambda1_decomposition`/`Rlambda2_decomposition`. A REALIZATION LEDGER in `Li.lean` records the
  boundary: every `Li` interface is realized exactly as far as the built slices reach, no further.
- **THE DOMINANCE FACE** (`F1Square/Square/Dominance.lean`) — the crux as ONE uniform bound:
  `Dominates B arith arch` (`−B(n) ≤ arith(n)` — the bound controls the oscillation's negative
  excursions — and `arch(n) − B(n) > 0` — it stays strictly below the archimedean trend),
  `Dominated` its single existential. Sign-agnostic in both parts: no case split between the
  small-`n` regime (archimedean part NEGATIVE: `λ₁^{∞} ≈ −0.5541`, `λ₂^{∞} ≈ −0.8745`, re-verified
  to 30 digits) and the asymptotic regime (roles swapped); the dichotomy is clean, no third option.
  **The theorems**: `dominated_liPositive` / `liPositive_dominated` / `dominated_iff_liPositive`
  (under the trace, "some single bound dominates" ⟺ `λₙ > 0 ∀n` — genuinely universal WITHOUT
  enumeration; the necessity witness is the tight bound `B(n) = arch(n) − λₙ`), and
  **`dominance_crux_equivalent`**: `Dominated ⟺ SpectralCrux ⟺ LiCrux` through the v0.18.0 bridge —
  **the crux now has THREE provably equivalent faces** (geometric `⟨Cₙ,Cₙ⟩ < 0 ∀n`, analytic
  `λₙ > 0 ∀n`, dominance `∃ one bound under which oscillation loses`); `weilTrace_dominance` reads
  the completed trace ladder through it. **The assembly shape, exact**: `dominance_head_tail` +
  `crux_closure_route` — the certified head (today `n ≤ 2`) plus ONE tail bound from `n = 3` on
  yields the crux; the tail bound for the genuine parts is the single remaining object, provably
  equivalent to the v0.18.0 frontier. **Honesty guards, two-sided**: `dominance_satisfiable` (no
  hidden impossibility; the loose existential is NOT RH), `twoSlice_not_dominated` +
  `weilTraceTwo_not_crux` (the finite-assembly guard transfers to this face).
- **The classical sourcing, deep-research-verified** (101 agents, 23 claims confirmed 3-0 against
  the primary PDFs, 2 refuted): **Voros's strict dichotomy** (*Math. Phys. Anal. Geom.* 9 (2006)
  53–63, arXiv math/0506326 — "two sharply distinct and mutually exclusive asymptotic forms", NO
  third option): RH ⟺ `λₙ ~ ½n(log n − 1 + γ − log 2π)` mod `o(n)`; ¬RH ⟺ exponential oscillation
  `Σ((τₖ+i/2)/(τₖ−i/2))ⁿ + c.c.`, rate `|1 − 1/ρ| > 1` for the `Re ρ < 1/2` member of each
  off-line pair (rigorous via Darboux in the 2006 paper; the 2004 note's sign erratum pinned as a
  convention trap). **Lagarias** (*Ann. Inst. Fourier* 57 (2007) 1689–1740): the archimedean trend
  `(n/2)log n + cn + O(1)`, `c = (γ − 1 − log 2π)/2`, **unconditional** (Thm 5.1; Voros pins the ζ
  `O(1)` to `+3/4`); the `O(√n·log n)` excursion bound on the arithmetic part — a THEOREM under RH
  (Thm 6.1). The general-`n` archimedean closed form
  `λₙ^{∞} = 1 − (n/2)(γ + log 4π) + Σ_{j=2}^n (−1)ʲ C(n,j)(1 − 2^{−j})ζ(j)` matches the built
  slices exactly. Net: `Dominated`(genuine parts) is TRUE iff RH — both directions confirmed at the
  asymptotic level — and **no unconditional tail bound exists in the verified literature** (the
  one-sided shape is published only as Coffey's sufficiency Conjectures 2–3, math-ph/0505052); the
  equivalence-by-regrouping is this release's theorem, per the Conrey–Li relocation discipline.
- **THE GENUINE ARCHIMEDEAN TREND, ALL `n`** (`F1Square/Analysis/ArchTrend.lean`) — the closure
  push: the archimedean side of the crux as a single constructed object, `genuineArchSeq n =
  1 − (n/2)(γ + log 4π) + Σ_{j=2}^n (−1)ʲC(n,j)(1 − 2^{−j})ζ(j)` for EVERY `n` — one definition, no
  enumeration; every ingredient already built (`γ`, `log 4π`, `ζ(j)` for all `j ≥ 2`, binomials).
  Consistency THEOREMS at both independently-built slices (`genuineArch_one`/`genuineArch_two` —
  genuine reconciliations of distinct constructions). **`crux_vs_constructed_trend`** — the sharpest
  honest statement of RH this substrate provides: for any spectral square whose trace splits against
  the BUILT trend, the crux ⟺ "the arithmetic part admits one bound strictly below
  `genuineArchSeq`". The open content of RH contracts to the arithmetic side alone; the trend's
  classical growth is sourced, not mechanized; nothing touches positivity of the genuine `λₙ`.
- **THE GENUINE LI SEQUENCE IN CLOSED FORM** (`F1Square/Analysis/GenuineLi.lean`) — the
  implementation's deepest open question ("the genuine sequences are unconstructed") closed modulo
  the Stieltjes tail: `StieltjesEta` (η-data with the BUILT anchors `η₀ = −γ`, `η₁ = γ² + 2γ₁` as
  proof fields), `genuineArithSeq` (`λₙ^{arith} = −Σ_{j=1}^n C(n,j)·η_{j−1}`, every `n` — the
  verified non-alternating closed form, anchored to BOTH mechanized slices as theorems
  `genuineArith_one/two`; the Coffey recursion deliberately NOT used, convention guard), and
  **`genuineLamSeq` — the genuine Li sequence with both sides closed forms** (`weilTraceGenuine`:
  the full-ladder trace, definitional at every positive index, exactly as classically `λₙ` is
  defined through the explicit formula). The closed form MEETS the certified values
  (`genuineLam_one/two`), so **the head is a THEOREM** (`genuineLam_head`: `Pos` at `n = 1, 2` for
  ANY anchored η-data). `etaTwoSlice` inhabits the structure; its `n ≥ 3` outputs are flagged
  TRUNCATIONS (caution (d)). **`crux_genuine_form`** + **`crux_genuine_route`** (the maximal honest
  reduction): the crux follows from exactly TWO open inputs — the genuine η-tail (`γ₂, γ₃, …`,
  constructible one at a time by the `GammaOne` pattern) and ONE bound between the two closed forms
  from `n = 3` on, a bound that exists iff RH. The head is DISCHARGED; neither input is asserted.
- **The final roll-up** (`F1Square.lean`) — the stage-E backing block, the elaboration-checked
  v0.19.0 witness (both trace realizations, the retirement, the ∀-form three-face equivalence, the
  dominance reading, both guards, crux fields `none`), and the **v1.0.0-candidate state**: complete
  construction, honest crux. Workspace hygiene: warning-free build; `Li.lean` realization ledger;
  `Attempt.lean` frontier cross-pointer.

- **THE GENUINE-PAIRING ARC** (the closure push, continued — the formerly-planned v0.20/v0.21
  work folded into this release; deep-research #4: 99 agents, 21 claims confirmed 3-0 against the
  primary PDFs, 4 refuted):
  - *Substrate*: `Analysis/RMax.lean` — `Rabs` (Bishop-regular with no reindex, via the reverse
    triangle inequality on exact ℚ), `RmaxZero = ½(t+|t|)`, and the tent calculus (non-negativity,
    vanishing off support, identity on support) — compactly-supported piecewise-linear test
    functions as total `Real → Real` functions; `Analysis/RSum.lean` — finite real sums with the
    congruence/PSD/monotonicity transports.
  - **THE WEIL FUNCTIONAL, assembled** (`Analysis/Weil.lean`, `Square/Pairing.lean`): in the pinned
    CC unsymmetrized normalization (arXiv 2006.13771 App. B; the three-normalization trap and the
    `dx` vs `dx/x` involution trap recorded), `W(f) = poles − (primes + archimedean)` — **the zero
    side is the DEFECT of the built sides; no zeros are inputs**. CONSTRUCTED: the whole
    finite-place side `weilPrimePart = Σ_{n≤X} Λ(n)(f(n) + n⁻¹f(1/n))` (rational weights, finite by
    support, stable past the cutoff) and the archimedean constant `(log 4π + γ)·f(1)` (both factors
    built). INTERFACE (the faithful boundary): the pole terms and the archimedean integral — their
    piecewise-linear closed forms are routine but **unverified in print** (the deep-research open
    question), so transcribing them would breach the gate. Piecewise-linear test data is ADMISSIBLE
    to Weil's criterion directly (Bombieri's class `W`, the official Clay problem description §V).
  - **THE FOURTH FACE** : `weilSpectralSquare` — the FIRST `SpectralSquare` whose `cSq` comes from a
    pairing-valued assembly (the dictionary holds by construction) — with `weil_psd_iff_hodge` and
    `weil_strict_iff_crux`: positivity of the pairing family ⟺ the crux ⟺ Li positivity ⟺
    dominance. For the genuine family this is Weil positivity = RH — **elementary in both
    directions** (Weil 1952; Burnol math/9810169 proves the Lemma directly, no density argument —
    the presumed 'hard direction' was adversarially refuted). Guard: `weil_template_crux`.
  - **The first computed pairing value** (`weilPrime_demo`): the finite-place side at the
    piecewise-linear tent peaked at `2` is exactly `log 2` — the pairing sees the prime through the
    test function (the §2.3 "separation = Λ" finding, now on the pairing side, as a theorem).
  - **The unconditional territory, recorded** (pinned, not asserted): Connes–Consani (Selecta
    Math. 27 (2021), Thm 1) — Weil positivity is UNCONDITIONAL for test support in
    `[2^{−1/2}, 2^{1/2}]` (the prime-free window — where the constructed finite-place side vanishes
    by `weilPrimePart_stable`'s discipline); the certificate is the Sonine-space projection
    (infinite-dimensional). Burnol's precursor window carries an EXPLICIT nonnegative spectral
    multiplier `α(τ) = 8√2·cos(τ log 2)/(1+4τ²) + h₊(τ)`, `h₊ = −log π + Re ψ(1/4 + iτ/2)` — the
    natural constructive SOS target (needs uniform-in-τ digamma bounds; the pinned next
    mechanization). **The window theorem holds on the built object** (`weilPrime_window`/
    `weilValue_window`): a test datum with support inside the prime-free window has identically
    vanishing finite-place side at every truncation depth, so the assembled `W` reduces in-window
    to `poles − archimedean` — the exact statement the certificate program starts from, as a
    theorem of the assembly. Bombieri's Lincei truncations were verified to be ZERO-INDEXED (not
    zero-free certification targets) — that route is honestly closed.
  - **THE WINDOW CERTIFICATE, computed** (`Analysis/PsiQuarter.lean`, `Analysis/BurnolAlpha.lean`):
    Burnol's spectral multiplier `α(τ) = 8√2·cos(τ log2)/(1+4τ²) + h₊(τ)`,
    `h₊(τ) = −logπ + Re ψ(1/4 + iτ/2)`, evaluated at the center of the prime-free window. **ψ(1/4)**
    is built as the FIRST exact non-trivial digamma value — at `z = 1/4` the digamma series has
    exact-rational terms `1/(n+1) − 1/(n+1/4) = −3/[(n+1)(4n+1)]`, a sign-definite series with a
    telescoping tail, giving a genuine direct-sequence constructive real with `ψ(1/4) ≥ −4.32`
    (true `≈ −4.2270`, via `Rgamma_h_upper` and a uniform partial-sum bound). **`α(0) > 0`**
    (`burnolAlphaZero_pos`, true `≈ 5.94`) is then an axiom-clean theorem — `8√2 − logπ + ψ(1/4)`,
    with `√2 = exp(½ log2) ≥ 1` (`RrpowPos`, no sqrt primitive) — certified from the wide margin
    `8·1 − 1.15 − 4.32 = 2.53 > 0`. This is EVIDENCE for the windowed Weil positivity (the
    multiplier at one point), exactly as `weilPrime_demo` / the certified `λ`-slices are evidence —
    NOT the universal `α(τ) ≥ 0 ∀τ` (needs the uniform-in-τ complex-digamma bound), still less RH
    (the window excludes every prime). The universal window theorem stays the pinned next target.
  - **THE τ-PARAMETERIZED KERNEL + THE HONEST INDEFINITENESS FINDING** (`Analysis/DigammaWindow.lean`):
    the kernel `Re ψ(1/4 + iτ/2)` has exact-rational terms (even in `τ`); `windowKernel`
    `g_n(s) = (n+1/4)/((n+1/4)²+s)` is proven ANTITONE in `s = τ²/4` (`windowKernel_antitone`), so
    `windowTerm = 1/(n+1) − g_n` is MONOTONE INCREASING in `τ²` (`windowTerm_mono`) — hence `h₊(τ)`
    increases from `h₊(0) ≈ −5.37` toward `+∞`; `windowTerm_zero` reduces the kernel at `τ = 0` to
    `ψ(1/4)`'s summand. **The load-bearing finding** (recorded faithfully): the BARE multiplier `α`
    is **NOT** pointwise non-negative — `α(0) ≈ 5.94 > 0` but `α` is INDEFINITE, dipping to `≈ −1.0`
    near `τ ≈ 2.27`. This is exactly why Burnol needs the restricted-class `A_ε`-correction and
    Connes–Consani need the Sonine projection: **`α(τ) ≥ 0 ∀τ` is NOT a theorem**, so the
    unconditional window positivity stays the honest interface — the monotone kernel (which bounds
    the negative band) is the correct object the genuine window theorem is built from (v0.20.0).

### Honest scope (the bright line, unchanged)
- The dominance face RELOCATES the difficulty (Conrey–Li); it does not remove it. The open content
  of RH is now ONE object: a single bound sequence dominating the genuine arithmetic part strictly
  below the genuine archimedean trend — which exists iff RH (verified both directions). Nothing
  asserts it; `hodgeIndexHolds`/`liPositivityHolds` stay `none`; **RH stays OPEN**. The certified
  slices remain `n = 1, 2`; the next slice needs `γ₂`.

## [0.18.0] - 2026-06-12

### Added — stage D: the bridge and the crux attempt (pure Lean 4, no Mathlib, no `sorry`, choice-free)

The two stage-D release goals are delivered: **the geometric and analytic faces of the crux are proven
equivalent**, and **the crux attempt ran under the gate** — it did not close the universal, so
`hodgeIndexHolds`/`liPositivityHolds` stay `none` and **RH stays OPEN**, with the bridge substrate shipped
exactly as scoped. Every theorem is choice-free (`{propext, Quot.sound}`), audited; the gate passes.

- **The Castelnuovo–Severi anchor** (`F1Square/BridgeFF.lean`) — the function-field model of
  "Hodge index ⟹ RH" as a genuine lattice derivation, no governor shortcut: the `E × E` lattice
  `{F_h, F_v, Δ, Γ}` with the standard Gram (`Γ` bidegree `(1, q)`; `Δ² = Γ² = 0`, genus-1 adjunction;
  the **trace datum** `Δ·Γ = q+1−a` by Lefschetz — `ff_trace_datum`); the primitive projection
  `D° = D − (D·F_v)F_h − (D·F_h)F_v` of `D = xΔ + yΓ` (`primDG_perp_h/v`); the computation
  **`primDG_sq`**: `D°² = −2(x² + a·xy + q·y²)` — the Hodge-index form IS the binary quadratic form of
  discriminant `a² − 4q`; and **`ff_hodge_iff_hasse`**: `∀x,y D°² ≤ 0 ⟺ a² ≤ 4q` (forward: instantiate
  `(a, −2)`; backward: `4(x²+axy+qy²) = (2x+ay)² + (4q−a²)y²`). `ff_hodge_iff_hodgeType` derives the
  v0.1.0 governor from lattice positivity — "§0.3: the mechanism is not the gap" is now a theorem.
- **The λ₂ Bombieri–Lagarias decomposition** (`F1Square/Analysis/LiTwo.lean`) —
  `λ₂^{arith} = −(2η₀ + η₁) = 2γ − (γ² + 2γ₁)` (the prime side, via the Stieltjes `γ₁`) and
  `λ₂^{∞} = (1−γ) − log 4π + ¾ζ(2)` (the Γ-factor place); **`Rlambda2_decomposition`** proves
  `λ₂ = λ₂^{arith} + λ₂^{∞}` as a constructive-real identity. **`li_decomposition_two_realized`**:
  `Li.LiDecomposition` realized with BOTH genuine slices (`n = 1` from v0.15.3, `n = 2` new), both
  certified positive (`liTwo_evidence`).
- **THE BRIDGE** (`F1Square/Square/Spectral.lean`) — the release goal. `SpectralSquare`: the `H¹`-bearing
  enrichment of `𝕊` as an interface — the Li/trace data `lam`, the primitive-class self-intersections
  `cSq`, and the **dictionary** `⟨Cₙ,Cₙ⟩ = −2λₙ` (Deninger's Hodge-index reading of Li's criterion,
  Proc. Symp. Pure Math. 55 (1994); normalized exactly as `BridgeFF.primDG_sq` derives it on the
  function-field model; the classical chain "RH ⟺ Weil positivity ⟺ λₙ ≥ 0" is Weil 1952 / Li 1997 /
  Bombieri–Lagarias 1999 / Bombieri 2000). The equivalence is a genuine constructive **theorem**:
  `spectral_bridge_nonneg` (`⟨Cₙ,Cₙ⟩ ≤ 0 ∀n ⟺ Li.LiNonneg`), `spectral_bridge_pos(_slice)` (strict ⟺
  `Li.LiPositive`), and **`crux_faces_equivalent : SpectralCrux S ⟺ Li.LiCrux S.lam`** — via new
  doubling lemmas (`Pos_of_Radd_self` at the sequence level: a witness `1/(n+1) < 2x_{2n+1}` halves to
  `1/(2n+2) < x_{2n+1}`). Inhabited by `spectralTwoSlice` (the genuine certified `λ₁, λ₂`;
  `spectral_evidence_two`: `⟨C₁,C₁⟩ < 0` and `⟨C₂,C₂⟩ < 0` — the geometric face's first genuine
  negativity slices). **Honesty guards as theorems**: `spectralTwoSlice_not_crux` (the finite-slice
  instance provably FAILS the crux — its `n = 3` slice vanishes) and `spectral_iff_all_upTo` (no finite
  run of negativity checks reaches the crux — the finite-check guard, geometric face).
- **The crux attempt, under the gate** (`F1Square/Square/Attempt.lean`) — run, recorded, honestly
  concluded. Certified: strict Hodge negativity through `n = 2` (`spectral_strict_upTo_two`), the
  furthest any axiom-clean run reaches in this substrate. The frontier, exact:
  **`crux_attempt_frontier(_geometric)`** — given the certified slices, the crux ⟺ `∀ n ≥ 3, λₙ > 0`
  (the next slice needs `γ₂`, a fresh `GammaOne`-scale mechanization). The post-mortem records why the
  general routes are blocked, with the program's own controls as evidence (vacuous-kernel control
  `Bridge.control_psd`; pencil-blindness `square_hodge_pencil_blind`; the BL cancellation, companion
  §8.1; the Conrey–Li precedent) and what would close it (the genuine `H¹` instance, T4/§3.4 —
  Connes–Consani's archimedean/semilocal Weil positivity, Selecta Math. 27 (2021), being the strongest
  partial result). **Conclusion: the universal did not close; the fields stay `none`.**

### Honest scope (the bright line, unchanged)
- The bridge makes the two crux faces ONE proposition; it does not make that proposition easier. The
  certified slices are `n = 1, 2`; `λₙ > 0 ∀n` (= RH, both faces) stays open;
  `hodgeIndexHolds`/`liPositivityHolds` stay `none`. The genuine spectral instance (`H¹` with spectrum =
  the zeros) remains the program's single open object (T4/§3.4), now with the exact shape of what
  carrying it buys (`BridgeFF`).

## [0.17.0] - 2026-06-12

### Added — stage C: the canonical arithmetic square `𝕊 = Spec ℤ ×_𝔽₁ Spec ℤ` with its derived intersection lattice (pure Lean 4, no Mathlib, no `sorry`, choice-free)

The stage-C release goals are delivered (`F1Square/Square/`, six bricks). Every theorem is choice-free
(`#print axioms` = `{propext, Quot.sound}`), audited in `scripts/audit_axioms.lean`; the build is green and the
honesty gate passes. The crux fields stay `none` — **RH stays open**.

- **Canonical `𝕊` = the tensor `F ⊗_𝔽₁ F`, with its universal property PROVED**
  (`Square/Monoid.lean`, `Square/Tensor.lean`). Deitmar 𝔽₁-algebras are commutative monoids (realized as a
  bundled `CMon` record — the pure-core substitute for the typeclass hierarchy); the curve is the
  multiplicative monoid `ℕ₊` (free commutative on the primes — the canonical form of an element is its prime
  factorization, the UOR content-address); `𝔽₁` is the trivial monoid, proved **initial** (`f1_initial`), so
  the fiber coproduct over it is the plain coproduct: `𝕊 = ℕ₊ × ℕ₊` with injections `a ↦ a⊗1`, `b ↦ 1⊗b` and
  the **universal property** `copair_inl`/`copair_inr`/`copair_unique` (uniqueness via the tensor
  decomposition `z = z₁⊗z₂`, `sq_factor`); the 𝔽₁-cocone condition is automatic (`square_base_cocone`), so
  coproduct = pushout over `𝔽₁`. **Canonicality = the universal property** — `𝕊` is THE object, unique up to
  unique isomorphism, not a candidate model. Non-collapse of §3.1 (`ℤ ⊗_ℤ ℤ = ℤ`) by theorems: `inl ≠ inr`,
  the codiagonal identifies distinct points (`codiag_not_injective`, `gen2_codiag_collapse`), and the
  monomial family `2^a ⊗ 2^b` is **free of rank 2** (`gen2_injective`) — strict 2-dimensionality (T1 for all
  points, not a finite truncation); both projections recover the curve (`proj1_inl`, `proj_faithful`). The
  power Frobenius `frobPow k : a ↦ aᵏ` (a genuine hom) is distinguished from the Connes–Consani scaling flow
  `mScale n : a ↦ n·a` (NOT a hom, `mScale_not_hom` — a correspondence; its graphs are the pencil).
- **The distinguished divisors and their point counts** (`Square/Divisors.lean`): rulings `V_a = {a}×C`,
  `H_b = C×{b}`, diagonal `Δ`, Frobenius correspondences `Γ_n = {(m, n·m)}` as genuine subsets of `𝕊`;
  transverse singletons (`vFiber_inter_hFiber`, `diag_inter_vFiber/_hFiber`, `graph_inter_vFiber/_hFiber`),
  moving disjointness (`vFiber_disjoint`, `hFiber_disjoint`, `graph_disjoint`), the translate structure
  (`graph_translate_diag` — `Γ_n` is the flow translate of `Δ`; `vFiber_translate`), and the §2.3 finding at
  the point level: **`Δ ∩ Γ_n = ∅` for `n ≥ 2`** (`diag_inter_graph_empty`) — the scaling Frobenius has no
  transverse fixed points on canonical `𝕊`.
- **The parallel pencil with its shift lengths `log n`** (`Square/Pencil.lean`) — the §2.3 structural finding
  lifted from the candidate bi-tropical model to theorems on `𝕊`: **`logN_mul_general`**
  (`log(ab) = log a + log b` for ALL positive naturals, by exp injectivity — generalizing the v0.15.2 base-2
  keystone) and `logN_pow_general` (`log pᵏ = k·log p`); **`pencil_shift`** (`log y = log x + log n` on `Γ_n`
  — the affine shift, exact), **`pencil_parallel`** (slope 1 ⇒ recession direction `(1,1)`, the diagonal's
  own), **`pencil_det_zero`** (stable count `Δ·Γ_n = |det((1,1),(1,1))| = 0`, tied to the mechanized
  `Tropical.Signature.parallel_pencil`), **`pencil_separation`** (constant separation `log n`),
  **`pencil_separation_vonMangoldt`** (at a prime the separation IS `Λ(p) = log p`, the explicit-formula
  prime weight of `Analysis/Mangoldt.lean`), and `pencil_separation_pow` (`k·log p` — the closed orbit of
  length `log p` traversed `k` times). **The arithmetic content provably relocates to the shift lengths.**
- **The intersection lattice, DERIVED — never entered by hand** (`Square/Lattice.lean`, the §2.2 declarative
  discipline mechanized): every primitive number is a point count with classes moved along their translation
  pencils (`pair_*_derived`: `V·H = 1`, `V² = H² = 0`, `Δ·V = Δ·H = 1`, **`Δ² = 0` from the parallel-pencil
  disjointness itself**, `Γ·V = Γ·H = 1` — degree-1 translation correspondences, `Γ·Γ = Δ·Γ = 0`);
  bilinearity (`sqPair_add_left`, `sqPair_smul_left`) **forces `E₃² = −2`** (`e3_sq_forced`); the sourced
  §2.2 product-of-curves template **emerges** (`sqPair_eq_template`) — **T3's "realize the pairing
  intrinsically" is closed by derivation**, agreement with the template is now a consistency theorem. The
  five §2.2 gate self-checks are theorems (`sqPair_symm`, `sq_boundary_checks`, `sq_adjunction_checks`,
  `sq_signature_diag` — signature `(1,2)` by explicit diagonalization `{V+H, V−H, E₃} → diag(2,−2,−2)` with
  complementarity). The class lattice is **finitely generated** on the derived basis (`cls_generated`,
  T2 on `𝕊`); the graph class is **forced** (`graph_class_unique`), so `[Γ_n] = [Δ]` for all `n`
  (`pencil_numerically_trivial`).
- **Polarized `𝕊`, the Hodge index of the derived lattice, and the faithfulness boundary**
  (`Square/Polarized.lean`): `squarePolarized` — the `Crux.Polarized` instance is now `𝕊`'s own derived
  lattice (the stage-C lift); the ample class `H = [V]+[H]` has `H² = 2 > 0` (`sq_ample_pos` — verified, NOT
  automatic for a tropical surface) with Nakai-style meets (`sq_ample_meets`); `H^⊥` is negative-definite
  (`sq_hperp_neg_semidef`, `sq_hperp_definite`); **`square_hodgeIndex : HodgeIndex squarePolarized`** holds.
  **And the boundary** (`square_hodge_pencil_blind`): the lattice is **pencil-blind** — `[Γ_n] = [Δ]` and
  `Δ·Γ_n = 0` for ALL `n`, so the function-field trace input (`Δ·Γ_q = q+1−a`, `Mechanism.hodgeType`) is
  provably absent and the positivity carries **no spectral content** — the geometric face of the §2.3
  control (`Bridge.control_psd`). It is therefore **NOT the crux**.
- **Manifest de-hedge** (`F1Square.lean`, `Crux.lean`): `surfaceConstructed` and `parallelPencilFinding`
  flip `none → some true` (honest scope documented: canonical at the monoid-scheme / T1–T3 level; the
  `H¹`-bearing spectral enrichment is NOT constructed); `classGroupFinitelyGen` /
  `intersectionTemplateValid` / `ampleClassExists` are now carried by canonical `𝕊`; the
  `parallelPencilStructure` identity flips to universally valid; two new elaboration-checked witness
  examples bind the layer to the manifest; the `Crux` faithfulness caution is sharpened with the proven
  pencil-blindness boundary.

### Honest scope (the bright line, unchanged)
- The crux is the Hodge index / Weil positivity of the **`H¹`-bearing** pairing — the form on which the
  scaling flow acts with spectrum = the zeta zeros (T4/T5), equivalently `λₙ ≥ 0 ∀n` (Li). `𝕊`'s coarse
  numerical lattice provably does not carry it (`square_hodge_pencil_blind`), so `square_hodgeIndex` is a
  result about the constructed object and **not** an RH claim. `hodgeIndexHolds` / `liPositivityHolds` stay
  `none` — **RH stays open**. Stating the geometric⟺analytic equivalence faithfully is stage D (v0.18.0).

## [0.16.0] - 2026-06-11

### Added — stage B: critical-strip `ζ`, the archimedean `Γ′/Γ` place, and `Pos λ₂` (pure Lean 4, no Mathlib, no `sorry`, choice-free)

The three v0.16.0 release goals are delivered. Every theorem below is choice-free
(`#print axioms` = `{propext, Quot.sound}`), audited in `scripts/audit_axioms.lean`; the build is green
and the honesty gate passes. The crux `liPositivityHolds`/`hodgeIndexHolds` stay `none` — **RH stays open**.

- **(B) `ζ(s)` on the critical strip `0 < Re s < 1`** — built the integration-free way, via the **Dirichlet
  eta** `η(s) = Σ (−1)^{n−1} n⁻ˢ`, which converges by **bounded variation** across the whole strip where the
  raw `ζ` series diverges.
  - `F1Square/Analysis/EtaVariation.lean` — **`Ceta`**: `η(s)` for every `Re s > 0` as a genuine constructive
    `ℂ`, the Bishop diagonal limit (`Rlim`) of the reindexed paired partial sums. The convergence is the full
    dyadic-geometric `RReg` stack adapted to `σ > 0`: the per-term variation bound (a new alternating-series
    quadratic remainder `altSum_quad`, the `RlogNat ↔ logN` bridge, a two-sided product keystone), the pairing
    identity, the geometric block bound `≤ ofQ(Vconst·rᵏ)` (`r = 1/(1+τ) < 1`), the telescoping tail
    `EtaVSum_tail_full → ofQ(Vconst/(j+1))`, the odd-offset subsum, and the reindex `etaMidx` (absorbing the
    `Vconst` prefactor) → `RReg_of_real_bound` → `Rlim`.
  - `F1Square/Analysis/CriticalZeta.lean` — **`CzetaStrip`**: `ζ(s) = η(s) / (1 − 2^{1−s})` for `0 < Re s < 1`,
    a genuine constructive `ℂ`. `cpowNeg_normSq` (`|n⁻ˢ|² = n⁻²ᴿᵉˢ`), the denominator
    `1 − 2^{1−s} = 1 − 2·cpowNeg s 2` (reusing `cpowNeg`, no new `Cexp`), its **non-vanishing**
    `etaDenom_Pos_normSq` (`|1 − 2^{1−s}|² ≥ (2^{1−σ} − 1)² > 0`, the spurious zeros all sit on `Re s = 1`),
    the constructive inverse `Cinv`, and the certificate `CzetaStrip_functional : (1 − 2^{1−s})·ζ ≈ η`. Since
    `ExactBoundedReal = Real`, the real and imaginary parts are exact-bounded objects automatically.
- **(A) The Gamma function via Spouge; the archimedean `Γ′/Γ` place** (`F1Square/Analysis/Gamma.lean`).
  - **`RrpowPos`** — the real power `x^y := exp(y·log x)` for a positive base, the single combinator behind
    every Spouge power (`√(2π) = exp(½·log 2π)`, `(z+a)^{z+½}`, the half-integer `(a−k)^{k−½}`). **No sqrt
    primitive and no complex `Clog` are needed.**
  - **`Digamma`** — the archimedean place `ψ = Γ′/Γ` as a genuine constructive real (the **exact** object, not an
    approximation), via the convergent series `ψ(z) = −γ + Σ_{n≥0}[1/(n+1) − 1/(n+z)]`. Architecture mirrors
    `Ceta`: per-term two-sided bound `|t_n| ≤ B/((n+1)n)` (`Rinv_le_ofQ_Qinv` + a two-sided product bound),
    the telescoping tail `digammaTail_two_sided`, the reindex `digammaMidx` absorbing `B = |z−1|`, then
    `RReg_of_real_bound` → `Rlim`; reuses the Euler–Mascheroni constant `Rgamma_h`.
  - **`SpougeGamma`** — Spouge's approximant of `Γ(z+1) = (z+a)^{z+½}·e^{−(z+a)}·(c₀ + Σ_{k=1}^{N} c_k/(z+k))`,
    `c₀ = √(2π)`, `c_k = ((−1)^{k−1}/(k−1)!)(a−k)^{k−½}e^{a−k}`, as a constructive real built entirely from
    `exp`/`log`/reciprocal of positive reals (general rational parameter `a`). Spouge's explicit **relative**-error
    bound `|ε_S(a,z)| < √a·(2π)^{−(a+½)}/Re(z+a)` (`a ≥ 3`; Spouge 1994 SIAM J. Numer. Anal. 31(3); Pugh thesis
    eqns 2.18–2.19) is **documented, not asserted as a Lean theorem** — a rigorous proof presupposes an
    independent `Γ`, so the *exact* archimedean place is carried by the `Digamma` series instead.
- **(C) `Pos λ₂`** (`F1Square/Analysis/LambdaTwo.lean`) — the second Li/Keiper coefficient is positive
  (`Rlambda2_pos : Pos Rlambda2`, certified lower bound `λ₂ ≥ 0.0043`; true value `λ₂ ≈ 0.0923457`),
  the higher-Stieltjes-`γₙ` → `λₙ` capstone, a
  `λ₁`-style positivity certificate for `n = 2`.

### Honest scope (unchanged)
- `Pos λ₂` is **evidence** for Li's criterion at `n = 2`, **not** the crux: `liPositivityHolds` stays `none`
  and **RH stays open**. `λₙ > 0 ∀ n` (= RH), the off-critical-line zeros, and the arithmetic square remain
  deferred. The Spouge `Γ`-value's error bound is cited, not formalized; the archimedean place used downstream
  is the exact `Digamma`.

## [0.15.3] - 2026-06-10

### Added — the explicit formula's arithmetic ingredient: von Mangoldt `Λ`, the prime side, and the Bombieri–Lagarias `n = 1` decomposition (pure Lean 4, no Mathlib, no `sorry`)
- **The von Mangoldt function `Λ`** (`F1Square/Analysis/Mangoldt.lean`) — `vonMangoldt n`: `log p` when
  `n = pᵏ` is a prime power, else `0`. Built with no primality predicate beyond the **smallest factor**
  `spf n` (least `d ≥ 2` dividing `n`) and a prime-power test (strip `spf` to `1`). Everything is
  computable, so the defining values hold by reduction: `Λ(1) = 0`, `Λ(2) = Λ(4) = Λ(8) = log 2`,
  `Λ(3) = Λ(9) = log 3`, `Λ(6) = 0`; and `Λ ≥ 0` everywhere (`vonMangoldt_nonneg`).
- **`spf` is proved to be the least PRIME factor** — `spf_dvd` (it divides `n`), `spf_two_le` (`≥ 2`),
  and `spf_prime` (its only divisors are `1` and itself), via the fuel-sufficient search specification
  `spfFrom_spec`. So `Λ` is genuinely the von Mangoldt function (not a table matching at sampled
  points): `vonMangoldt_prime` gives `Λ(p) = log p` for **every** prime `p`.
- **The explicit-formula prime side** — `primeSide h N = Σ_{n=2}^N Λ(n)·h(log n)`, the prime side
  `Σ_p Σ_k log p · h(k·log p)` reindexed through `k·log p = log(pᵏ) = log n`. A finite sum, hence a
  genuine constructive real with **no convergence hypothesis**; `primeSide_stable` proves it is constant
  past the support cutoff, so a **compactly supported** `h` gives a single well-defined real
  (`primeTerm_zero_of_h` derives term-support from `h`-support).
- **The Bombieri–Lagarias decomposition of `λ₁`** (`F1Square/Analysis/LiOne.lean`) —
  `Rlambda1_decomposition : λ₁ ≈ λ₁^{arith} + λ₁^{∞}`, the two-place split of the explicit formula:
  - `Rlambda1_arith = γ` — the **finite/arithmetic place** `S_f(1) = −η₀` (`η₀ = −γ`; the regularized
    von Mangoldt / prime-power contribution).
  - `Rlambda1_arch = 1 − γ/2 − ½·log(4π)` — the **archimedean Gamma-factor place** `S_∞(1)` (incl. the
    trivial-pole "1").
  - proved by reducing both `λ₁ = ½·(2 + γ − log 4π)` and `arith + arch` to the canonical form
    `(1 + γ/2) − ½·log(4π)` via the pointwise `Rhalf` distribution (`Rhalf_Radd`, `Rhalf_Rneg`,
    `Rhalf_two`) and `γ − γ/2 ≈ γ/2` (`Rhalf_double`).
- **`Li.LiDecomposition` is now realized non-trivially** — `li_decomposition_realized`:
  `LiDecomposition liLamSeq liArithSeq liArchSeq`, a proven instance whose `n = 1` slice is the genuine
  arithmetic/archimedean split (`Rlambda1_decomposition`), promoting the interface from the trivial
  inhabitant `λ = λ + 0` (`Li.liDecomposition_genuine`).

### Honest scope (unchanged)
- Deriving the value `S_f(1) = γ` *from* the prime sum needs `ζ'/ζ` and its analytic continuation
  (v0.16.0+), so the Bombieri–Lagarias value is stated faithfully and **not** identified with the
  built `primeSide` — nothing is fabricated. None of this bears on positivity: the crux
  `liPositivityHolds` stays `none` and **RH stays open**. Critical strip, zeros, and the genuine `λₙ`
  for `n ≥ 2` remain deferred.
- All new theorems are choice-free (`{propext, Quot.sound}`), audited in `scripts/audit_axioms.lean`;
  the build is green and the honesty gate passes (coverage: 1211 proof-layer theorems).

## [0.15.2] - 2026-06-10

### Added — ζ(s) = Σ n⁻ˢ for **complex** s with Re s > 1, as a genuine constructive ℂ (pure Lean 4, no Mathlib, no `sorry`)
- **The Riemann zeta function for complex argument** (`F1Square/Analysis/ComplexZeta.lean`) — `Czeta s hσ … hθ`:
  for any complex `s` with `Re s ≥ 0` and a rational witness `τ > 0` of `Re s > 1` (`τ ≤ (Re s − 1)·log 2`),
  `ζ(s) = Σ_{n≥1} n⁻ˢ` is a genuine constructive complex number — its real and imaginary parts are Bishop
  diagonal limits (`Rlim`) of the reindexed dyadic partial sums `Σ_{n<2^{M(j)}} Re/Im(n⁻ˢ)`. This replaces
  the previous integer-only `ζ(s)` (`Σ 1/iˢ`, `s ≥ 2`): convergence now holds across the **full half-plane
  `Re s > 1`**, with `s` genuinely complex.
- **Convergence with a rate** — `Czeta_re_tendsTo` / `Czeta_im_tendsTo`: the partial sums converge to
  `Re/Im ζ(s)` with the canonical Bishop modulus `2/(k+1)` (`Rlim_tendsTo`). The rigorous complex geometric
  tail, certified.
- **The dyadic-geometric convergence proof**, built from scratch:
  - **exp injectivity → log-multiplicativity** (`F1Square/Analysis/RealPow.lean`) — `RexpReal_inj`,
    `logN_mul`, `logN_pow_two` (`log(2ᵏ) = k·log 2`), re-routing around the artanh addition boundary wall.
  - **dyadic block bound** — `czetaExp_block_geo`: the `[2ᵏ, 2ᵏ⁺¹)` block modulus `≤ ofQ(rᵏ)`,
    `r = 1/(1+τ) < 1` (the ratio `2·exp(−σ log2) = exp(−θ) ≤ r`, from `Re s > 1`).
  - **geometric tail** — `geoFrom_telescope` (`Σ_{k=j}^{j+d−1} rᵏ·(1−r) = rʲ − r^{j+d}`), `geoFrom_le`
    (`≤ rʲ/(1−r)`), and the dyadic telescoping `czetaExp_tail` (`E(2^{j+d}) − E(2ʲ) ≤ ofQ(Σ rᵏ)`).
  - **the geometric reindex** — `geom_reindex`: the Bernoulli `1/(linear)` decay `qpow_geom_bound` with the
    quadratic index `M(j) = (j+1)·r.den²` collapses `r^{M(j)}/(1−r) ≤ 1/(j+1)` (`czetaExp_tail_reindex`).
  - **the completeness bridge** — `seq_diff_le` (a real upper bound `a − b ≤ c` gives the same-index rational
    bound `aₙ − bₙ ≤ c + 2/(n+1)`, via regularity + the generalized Archimedean lemma) and `RReg_of_real_bound`
    (pairwise real differences `≤ 1/(j+1)+1/(k+1)` ⟹ a regular sequence of reals), feeding Bishop's `Rlim`.
  - **the Cauchy partial sums** — `czetaRe_RReg` / `czetaIm_RReg`: the reindexed real/imaginary partial sums
    are regular sequences of reals (the four two-sided tail bounds `czetaRe/Im_tail_le/ge`, case-split on `j ≤ k`).
- **Non-vacuity** — `czeta_two_theta` + a fully-closed `F1Square.lean` instance: `ζ(2) = Σ 1/n²` is built as
  `Czeta` and its partial sums converge (the `Re s > 1` hypothesis is satisfiable, `τ = 1/2 ≤ log 2`).
- **Full-sequence convergence** (not just the dyadic subsequence) — `czetaExp_mono` (E monotone),
  `czetaExp_tail_full` / `czetaRe`,`czetaIm_tail_full(_neg)` (the tail bound for *arbitrary* `N ≥ 2^{M(j)}`),
  `czetaRe`/`czetaIm_cauchy_full` (the **whole** partial-sum sequence is uniformly Cauchy: `|S(N) − S(N')| ≤
  2/(j+1)` for all `N, N' ≥ 2^{M(j)}`), and `czetaRe`/`czetaIm_full_tendsTo` (`|S(N) − ζ(s)| ≤ 3/(k+1)`). So
  `Σ_{n=1}^N n⁻ˢ` converges as a genuine series for every `N`, not merely along `2^{M(k)}`.
- **Canonicity** — `Czeta_re_canonical` / `Czeta_im_canonical`: `ζ(s)` is independent of the convergence
  witness `τ` (any two witnesses give `≈`-equal values — both are the limit of the same full sequence, via
  `RTendsTo_to_Rle` and the real-level Archimedean `Req_of_Rle_ofQ_all`). So `ζ(s)` is a well-defined function
  of `s` alone on `Re s > 1`.
- **`F1Square.lean` witnesses** binding `Czeta_re/im_tendsTo`, the concrete `ζ(2)`, the full-sequence Cauchy
  property, and canonicity — all for complex `s` with `Re s > 1`.
- Choice-free throughout (`{propext, Quot.sound}` only), `sorry`-free, `#print axioms`-audited at every commit.

### Unchanged — the honesty audit
- The crux `liPositivityHolds = none` (= RH) stays open; ζ ships in its convergent half-plane `Re s > 1`
  (where it has no zeros), and the analytic continuation to the critical strip is not built.

## [0.15.1] - 2026-06-09

### Added — the ζ-convergence gate `exp∘log = id` via genuine power-series composition (pure Lean 4, no Mathlib, no `sorry`)
- **`exp(2·artanh τ) = (1+τ)/(1−τ)` at the real level** (`F1Square/Analysis/ExpLog.lean`) —
  `Rexp_two_artanh_ofQ`: `RexpReal (TwoArtanhConst τ) ≈ (1+τ)/(1−τ)` for a constant rational `τ` (`0 ≤ τ < 1`).
  This is the roadmap's **research-grade base identity** (v0.15.1), built from scratch as a power-series
  composition — the elementary squeeze `1 + log x ≤ exp(log x) ≤ 1/(1−log x)` never pins equality, so the
  exp factorial series is composed with the artanh geometric series directly. The analytic core: the
  composition **corner bound** `exp_corner_le` (via finite-support truncation `truncTo`, the no-corner power
  `peval_fpow_pow_eq`, and the corner inequality `qpow_peval_le`), the formal-ODE identity `formal_exp_geom`
  (`fcomp ecoef (2·acoef) = dgeom`, by multiplicative-ODE uniqueness `fderiv_mul_inj`), the geometric closed
  form (`dgeom_geom_gap_le`), and the **rational identity** `exp_artanh_rat_cleared`. Lifted to the reals by
  the **diagonal reconciliation** `Rexp_two_artanh_via` (mirrors `RexpReal_congr`: a Lipschitz `P_match`
  matching the artanh inner depth to the exp outer depth via `peval_twoacoef_cauchy` + `expSum_Lip_le`/
  `LipS_le_U`, plus the `exp_artanh_recip` tail), with the argument-magnitude bounds `peval_twoacoef_abs_le_gpow`
  and `two_gPow_le`, and the clearing-division helper `mul_div_gen`.
- **`exp(log n) = n` for the *literal* `Rlog` term** (`F1Square/Analysis/ExpLog.lean`) — `Rexp_log_nat_Rlog`:
  `RexpReal (Rlog (ofQ n) …) ≈ n`, where `Rlog (ofQ n)` is the actual constructive logarithm
  `2·artanh((n−1)/(n+1))`. The base construction `RartanhConst`/`TwoArtanhConst`/`Rexp_two_artanh_ofQ` is
  **radius-general** (the convergence radius enters only through the depth reindex, which `Rexp_two_artanh_via`
  abstracts), so it applies directly at `Rlog`'s own smaller radius `ρ_M = (n−1)/(n+1)`, and
  `Rlog (ofQ n) = TwoArtanhConst (tmap n) ρ_M` holds by `rfl` (definitional equality of the constant-sequence
  artanh arguments). No `τ²≤½` smallness is needed. (`Rexp_log_nat` gives the same at the convenience radius
  `ρ = τ`.) The `tmap`-arithmetic (`1−τ = 2/(n+1)`, `g·(1−τ) = 1+τ`, `K·(1−τ) = 1`) is pure ℚ (`tmap_nat_den`/`num`).
- **Why it matters.** This closes the discovered dependency of stage A: `Σ n^{-s}` converges because
  `|n^{-s}| = n^{-Re s}`, i.e. `exp(log n) = n`. The honesty gate is met — the identity closes **axiom-clean**
  (`{propext, Quot.sound}` only), so the ζ-complex tail (v0.15.2) need not ship its convergence as an interface.
- **The crux stays `none`; RH is open.** `liPositivityHolds`/`hodgeIndexHolds` remain `none`.

## [0.15.0] - 2026-06-08

### Added — the complex analytic engine (stage A, exponential core): `exp` is a homomorphism, `nˢ` and its modulus (pure Lean 4, no Mathlib, no `sorry`)
- **The exponential functional equation on all of ℝ** (`F1Square/Analysis/ExpRealAdd.lean`) — `RexpReal_add`:
  `exp(x+y) ≈ exp x · exp y` for arbitrary constructive reals, the roadmap's technical core of stage A.
  Built from scratch as the diagonal lift of the rational Cauchy-product functional equation: the
  general-argument corner bound (`expSum_corner_le_gen`), its **signed** generalization
  (`expSum_corner_le_gen_signed`, `expSum_add_le_signed` — constructive-real samples dip negative even for
  positive reals), the exp diagonal reconciliations (`expSum_reconcile`, `rexp_factor_reconcile`), the uniform
  partial-sum bound (`expSum_abs_le_Un`), the factorial decay at the diagonal depth (`RexpReal_trunc_le`), and
  the deep-reference assembly (`rexp_add_gap`, `RexpReal_add_aux`). General exp-tail decay lemmas
  (`npow_fct_decay`, `truncCoef_Q/QE`) relocated to `ExpReal` for shared use.
- **The Pythagorean identity `cos² + sin² ≈ 1`** (`F1Square/Analysis/CosSinAdd.lean`) — `Rcos_sq_add_sin_sq`
  via the trigonometric Cauchy product from scratch, and its corollary **`|cos| ≤ 1`, `|sin| ≤ 1`**
  (`F1Square/Analysis/CosSinBound.lean`, `Rcos_sq_le_one`/`Rsin_sq_le_one`, through `Rnonneg_Rmul_self`).
- **The complex exponential `e^z`** (`F1Square/Analysis/ComplexExp.lean`) — `Cexp z = exp(re z)·(cos(im z) +
  i·sin(im z))` with component identities and `Cexp 0 ≈ 1` (`Cexp_zero`, `RexpReal_zero`, `Rcos_zero`,
  `Rsin_zero`).
- **`nˢ` and the modulus identity** (`F1Square/Analysis/ComplexMod.lean`, `ComplexPow.lean`) — `ncpow n s =
  Cexp(s·log n)` (positive-integer base via the real `RlogNat`), and `|Cexp z|² = (exp Re z)²` (`Cexp_normSq`,
  the analytic payoff of `cos²+sin²=1`) / `|nˢ|² = (exp(Re s·log n))²` (`ncpow_normSq`) — the squared modulus
  depends only on `Re s`, the basis of the future ζ tail bound.
- **The crux stays `none`; RH is open.** This release ships the *exponential core* of stage A. ζ for complex
  argument is **not** shipped: its convergence is gated on `exp(log n) = n` (`exp∘log = id`), a power-series
  composition that — because `log` is built independently as `2·artanh((x−1)/(x+1))` — is not definitional and
  is scoped to the **v0.15.x** series (see `ROADMAP.md`). `liPositivityHolds`/`hodgeIndexHolds` remain `none`.

## [0.14.0] - 2026-06-07

### Added — the analytic constants of the Li/Keiper bridge, and a positivity certificate for λ₁ (pure Lean 4, no Mathlib, no `sorry`)
- **π as a constructive real** (`F1Square/Analysis/Pi.lean`) — `Rpi` via Machin's formula
  `π = 16·arctan(1/5) − 4·arctan(1/239)` as a single Bishop-regular diagonal (`Arctan.lean` supplies the
  alternating arctan series on `[−ρ,ρ]`, `ρ<1`). Lower bracket `Rpi_lower` (π ≥ 6/5) gives `Pos Rpi`;
  the tight `Rpi_seq_ub_tight` (π ≤ 3.142) comes from the one-sided arctan truncation
  `arctanSum_deep_le`/`arctanSum_deep_ge` at the tightest radius `ρ = t`.
- **`log 2`, `log π`, `log 4π`** (`F1Square/Analysis/GammaAccel.lean`) — clean `2·artanh((x−1)/(x+1))`
  logs `Rlog2c`, `Rlogπc`, with kernel-certified upper bounds `Rlog2c_le` (`log 2 ≤ 0.6931`) and
  `Rlogπc_le` (`log π ≤ 1.1453`). The varying `π`-argument is dominated by the constant `15/29 = tmap(22/7)`
  (`artSum_base_mono`, since `π ≤ 22/7`), then truncated with an explicit geometric tail (`artSum_le_value`).
- **Euler–Mascheroni γ, convergence-accelerated** (`F1Square/Analysis/GammaAccel.lean`) — `Rgamma_h`, the
  harmonic-telescoped `γ = Σ(1/i − 2·artanh(1/(2i+1)))`, with the kernel-certified lower bracket
  `Rgamma_h_lower` (γ ≥ 0.54). This route is *feasible* where the alternating-ζ-series γ is not: that
  series carries the running `lcm` denominator (already `gammaSeq 2` has ~7000 digits), so a positivity
  certificate from it was out of computational reach.
- **`Pos λ₁` — the first Li coefficient is a positivity-certified constructive real**
  (`F1Square/Analysis/LambdaOne.lean`) — `Rlambda1 = ½·(2 + γ − log 4π)` (Bombieri–Lagarias), with
  `Rlambda1_pos : Pos Rlambda1`. Proven through `2λ₁ = 2 + γ − log 4π` (integer coefficients):
  `2λ₁ ≥ (2 + 0.54) − (2·0.6931 + 1.1453) = 0.0084 > 0`, hence `λ₁ ≥ 0.0042 > 0`. The ℝ-order bridges
  `Radd_le_add`, `Rneg_le`, `Rhalf`/`Rhalf_ge` carry the rational bounds through the ring operations.
- **The crux stays `none`; RH is open.** `λ₁ > 0` is the `n = 1` slice of Li's criterion realized as
  **evidence** — it does **not** assert `λₙ > 0 ∀ n` (which *is* RH). `liPositivityHolds` and
  `hodgeIndexHolds` remain `none`, never asserted. De-hedging here removes false modesty about the proven
  `λ₁` result (its certificate was previously documented as computationally infeasible); it adds no
  confidence about RH.
- All new theorems are `#print axioms`-audited and choice-free (`{propext, Quot.sound}`).

## [0.13.0] - 2026-06-07

### Added — the transcendentals on ℝ: `cos`, `sin`, and `log` on positive reals (pure Lean 4, no Mathlib, no `sorry`)
- **`cos` / `sin` on ℝ** (`F1Square/Analysis/CosSin.lean`) — the alternating power series as a directly
  Bishop-regular diagonal `RaltReal x off = ⟨Σ (−x²)ⁿ/(2n+off)!⟩`. The alternating term is dominated by
  the exponential of `M²` (`altTerm_abs_le`, `fct_mono`, `qsq_abs_le`), giving the truncation bound
  `altSum_trunc_bound` (geometric/factorial tail) and the Lipschitz bound `altSum_Lip_le`; the diagonal
  is regular (`RaltReal_regular`). `Rcos = RaltReal x 0`, `Rsin = x · RaltReal x 1`.
- **`log` on positive reals, positivity-as-data** (`F1Square/Analysis/Log.lean`) —
  `RlogPos x k = 2·artanh((x−1)/(x+1))` from a positivity witness `x_k > 1/(k+1)`, the *same* idiom as
  the reciprocal `Rinv`: the rational modulus `1/M ≤ x ≤ M` (`M = |x₀| + 2 + 1/L`, `L = δ/2` the witness
  floor via `Rinv_lb`) is **derived**, not demanded of the caller. (Constructively a modulus *is*
  necessary — `log` has no uniform modulus of continuity on `(0,∞)`.) The explicit-modulus engine
  `Rlog x M` takes `M` directly (`Rlog_two_ok` exhibits it on `x ≡ 2`):
  - **`artanh` on every `[−ρ,ρ]`, `ρ<1`** (`Rartanh`): the odd series `Σ t^{2n+1}/(2n+1)` as a regular
    diagonal, via the geometric telescoping `geo_diff_bound`, the truncation `artSum_trunc`, the
    Lipschitz `artSum_Lip_le` (with `geoEven_bound`), and the **general Bernoulli reindex**
    `qpow_geom_bound` (`ρᵐ ≤ q/(q+m(q−p))`) that tames the geometric tail.
  - **the t-map `q ↦ (q−1)/(q+1)`**: its cleared difference identity `tmap_diff_cleared`
    (`(tmap a − tmap b)·(a+1)(b+1) = 2(a−b)`), the Lipschitz bound `tmap_lipschitz`
    (`|tmap a − tmap b| ≤ (2/(L+1)²)·|a−b|`), and the range bound `tmap_abs_le`
    (`|tmap q| ≤ tmap M` for `q ∈ [1/M, M]`, keeping the artanh argument inside `[−ρ,ρ]`).
  - the diagonal `t.seq n = tmap(x_{2(n+1)})` is regular because the t-map is 2-Lipschitz on `x ≥ 0`
    (`Rlog_regular`); `tmap_M_eq` identifies the radius `ρ = tmap M < 1`.

### Changed — axiom-minimization (the axiom footprint cannot be a peer-review weakness)
- The entire proof layer is now **choice-free**: `Classical.choice` is eliminated. The only remaining
  axioms are `{propext, Quot.sound}`, both forced by `omega`/`simp`/`Int` core internals and
  constructively uncontroversial. (The two theorems that pulled choice did so only because `omega`
  discharged an `↔` goal directly; splitting into `Iff.intro` per direction is choice-free.)
- `scripts/honesty_audit.sh` tightened: the allowlist drops `Classical.choice`, so any future
  re-introduction of choice (or any other named axiom) fails CI. Coverage 399/399, enforced.

### Unchanged — the honest demarcation
- The crux stays `none` on both faces (`hodgeIndexHolds`, `liPositivityHolds`); RH is **open**
  (June 2026) and is never asserted. The transcendentals make more of the analytic half *statable and
  checkable*; they do not touch the crux.

## [0.12.0] - 2026-06-06

### Added — ℝ as a constructive field with powers, and `exp` on all of ℝ (pure Lean 4, no Mathlib, no `sorry`)
- **Real field / powers** (the multiplicative substrate the transcendentals need):
  - `F1Square/Analysis/Pow.lean` — real powers `Rpow` (iterated `Rmul`) with `Rpow_one`, `Rpow_congr`
    (powers respect `≈`).
  - `F1Square/Analysis/Inv.lean` — the reciprocal `1/x` of a positive real, **positivity-as-data**: from
    a witness `k` with `x_k > 1/(k+1)`, floor `x` by `L = δ/2 > 0` on the tail and reindex
    `R n = 4δ.den²(n+1) + 2δ.den`; `RinvSeq_regular` assembles full Bishop regularity. Plus the rational
    reciprocal `Qinv` (inverse law `a·(1/a) ≈ 1`, antitonicity, the difference identity
    `1/a − 1/b = (b−a)·(1/a)·(1/b)`) and division `Rdiv`.
  - `QOrder.lean` gains `Qmul_congr` and `Qmul_add_right` (ℚ multiplication respects `≈`; right
    distributivity).
- **`exp` on ℝ** (`F1Square/Analysis/ExpReal.lean`) — the everywhere-defined real exponential, as the
  **diagonal of rational partial sums**: `exp(x)_j = S_{R j}(x_{R j})` with `S_N(q) = Σ_{i≤N} qⁱ/i!`
  and a single reindex `R j` for both argument index and truncation depth. The diagonal sequence of
  rationals is itself Bishop-regular (`RexpReal_regular`: `|exp(x)_j − exp(x)_k| ≤ 1/(j+1)+1/(k+1)`), so
  it *is* a constructive real directly. Its three rational ingredients, all axiom-clean:
  - **truncation bound** `expSum_trunc_bound` — `|S_q(b) − S_q(a)| ≤ 2Mᵃ⁺¹/(a+1)!` for `|q| ≤ M`,
    `2M ≤ a ≤ b` (the dominating `M`-series `expSumM` with its telescoping tail `expM_diff_bound`, and
    termwise domination of the general-`q` gap);
  - **Lipschitz bound** `expSum_Lip_le` + `LipS_le_U` — `|S_q(N) − S_{q'}(N)| ≤ C·|q − q'|` with `C`
    uniform in `N` (per-power `|qⁱ − q'ⁱ| ≤ i·Mⁱ⁻¹·|q−q'|`, summed);
  - **factorial-growth** `fct_ge_geom` + `trunc_reindex` — the super-fast factorial tail converts to a
    `1/(j+1)` reindex.
- `F1Square.lean` gains the v0.12.0 manifest mapping + an elaboration-checked `example` (real powers
  `x¹ ≈ x`; `exp` is genuinely constructed with its rigorous diagonal gap bound).
  `scripts/audit_axioms.lean` extended (coverage 341/341, enforced); honesty audit PASS, axiom-clean.

### Note
- This completes the field/powers + `exp` substrate. Next: **v0.13.0** `cos`/`sin` + `log` (prereqs —
  `Rinv`, `qpow` with its bounds, ℝ-completeness — are all in place). Then the next phase: ζ's
  continuation into the critical strip (needs complex exp/log), the genuine `λₙ` realizing the v0.10.0
  interfaces, and the explicit-formula trace, ending at `λₙ > 0 ∀n` = RH (the open frontier). RH remains
  open (June 2026); no 𝔽₁-square construction exists.

## [0.11.0] - 2026-06-06

### Added — the order `≤` on constructive ℝ (pure Lean 4, no Mathlib, no `sorry`): the foundation for the transcendentals
- `F1Square/Analysis/ROrder.lean` — **`Rle`**, the Bishop order `x ≤ y ⟺ ∀ n, xₙ ≤ yₙ + 2/(n+1)`,
  with the genuine order laws: `Rle_refl`, `Rle_of_Req` (`≈ ⟹ ≤`), `Rle_antisymm` (`x ≤ y` and
  `y ≤ x` ⟹ `x ≈ y`), and **`Rle_trans`** — the one genuine limiting step: chaining `x ≤ y ≤ z`
  through an auxiliary index `m` gives `xₙ ≤ zₙ + 2/(n+1) + 6/(m+1)` for every `m`, and the generalized
  Archimedean lemma `Qarch_gen` kills the `6/(m+1)` tail (the argument behind `Req_trans`).
- **`Rnonneg` canonicalized** here (moved from `Li`): Bishop `x ≥ 0` (`−1/(n+1) ≤ xₙ`), with
  `Rnonneg_zero`/`Rnonneg_one`/`Rnonneg_Radd`, and `Rle_zero_of_Rnonneg` (`x ≥ 0 ⟹ 0 ≤ x`).
- ℚ signed-bound helpers (`Qle_self_Qabs`, `Qabs_le_of_both`, `Qle_add_of_Qabs_sub`,
  `Qsub_le_of_le_add`); `Qle_self_add`/`Qle_add_self` moved to `QOrder` (their natural home).
- `F1Square.lean` gains a v0.11.0 `example`; `scripts/audit_axioms.lean` extended (coverage 288/288,
  enforced); the honesty gate is hardened to also fail on **duplicate proof-layer theorem short-names**;
  honesty audit PASS, axiom-clean and choice-free.

### Note
- This is the foundation the transcendentals build on. The roadmap for the rest, concretely (no open
  `+`): **v0.12.0** reciprocal `Rinv` + `exp` on ℝ; **v0.13.0** `cos`/`sin` + `log`; then the next
  phase — ζ's continuation into the critical strip (needs complex exp/log), the genuine `λₙ` realizing
  the v0.10.0 interfaces, and the explicit-formula trace, which ends at `λₙ > 0 ∀n` = RH (the open
  frontier). RH remains open (June 2026); no 𝔽₁-square construction exists.

## [0.10.0] - 2026-06-06

### Added — the λₙ / Riemann-Hypothesis proof boundary, locked faithfully (pure Lean 4, no Mathlib, no `sorry`)
- `F1Square/Li.lean` — the **analytic face** of the same crux `Crux.lean` states geometrically. By
  **Li's criterion** (Li 1997), RH ⟺ `λₙ > 0` for all `n ≥ 1` (the paired sum over the nontrivial
  zeros; the non-strict `≥ 0` form is the general Bombieri–Lagarias 1999 multiset criterion, also
  ⟺ RH). This brick states that boundary precisely, before ζ is built, so the proof boundary is pinned.
- **Bishop ℝ order**: `Rnonneg` (the non-strict `x ≥ 0`, companion to the existing strict `Pos`), with
  `Rnonneg_zero`, `Rnonneg_one`, `Pos_one`, and the generic `Rnonneg_Radd` (sum of non-negatives is
  non-negative — *explicitly disclaimed* as **not** the mechanism behind Li-positivity, since the
  Bombieri–Lagarias parts `λₙ^{arith} = −Σ Λ(m)wₙ(m)` and `λₙ^{∞}` have opposite signs and `λₙ > 0` is
  a delicate cancellation, which is the open difficulty).
- **The Li-positivity property** `LiPositive` (strict, ζ-specific) and `LiNonneg` (BL non-strict),
  proven genuine/satisfiable by `template_liPositive`/`template_liNonneg` (the constant-`1` sequence) —
  the analytic analogue of `Crux.template_hodgeIndex`.
- **The finite-check guard** `liPositive_iff_all_upTo`: `LiPositive lam ↔ ∀ N, LiPositiveUpTo lam N`.
  This encodes precisely why the numerical positivity of the first ~10⁵ Li coefficients (computed to
  n = 100 000, Feb 2025) is **not** a proof: the theorem is the universal `∀ N`, which no finite
  `decide` reaches.
- **THE CRUX (analytic face)** `LiCrux λ` for the unconstructed genuine ζ-derived Li sequence — OPEN,
  never asserted, never axiomatized. A detailed **faithfulness caution** forbids the standard traps
  (existential witness, manifestly-positive definition, finite/truncated `decide`); `LiPositive λ ⟺ RH`
  is [CLASSICAL] (Li 1997), and positivity reformulations do not make RH easier (Conrey–Li 2000).
- **ζ-layer substrate as honest interfaces** (genuine/inhabited, never asserted for the real `λ`):
  `LiDecomposition` (Bombieri–Lagarias), `ExplicitFormulaTrace` (Weil 1952 / Connes 1999), `LiAgreesWith`.

### Added — ζ and λₙ as exact-bounded objects
- `F1Square/Analysis/ExactBounded.lean` — **`ExactBoundedReal`**: a constructive real presented as a
  stream of certified rational enclosures `[xₙ − 1/(n+1), xₙ + 1/(n+1)]`, with the exact-width identity
  `enclosure_width` (`upperB − lowerB = 2/(n+1)`), `lowerB_le_upperB`, and the regularity `certificate`.
  The Li coefficients are typed `λ : Nat → ExactBoundedReal`.
- `F1Square/Analysis/Zeta.lean` — **`ζ(s)` for integer `s ≥ 2` as a genuine exact-bounded constructive
  real**: `Σ_{i≥1} 1/iˢ` (natural powers `npow` from scratch), with the rigorous rational tail bound
  `zetadiff_bound` (`S(b) − S(a) ≤ 1/(a+1)` for `a ≤ b`) via the telescoping decreasing
  `U(N) := S(N) + 1/(N+1)` (the added term `1/(N+2)ˢ ≤ 1/((N+1)(N+2))` since `(N+1)(N+2) ≤ (N+2)ˢ`).
  The bound is already the Bishop modulus, so the partial sums are directly regular (`zetaSeq_regular`,
  no reindex). `zeta_pos`: `ζ(s) > 0`. **Honest scope:** this is ζ in the convergent half-plane
  `Re(s) > 1` at integer points — where ζ has **no zeros** and RH does **not** live; the analytic
  continuation to the critical strip (and ζ at complex `s`) is **not** built, and the genuine `λₙ`
  *values* (needing the continuation + `log`) are not fabricated — only their exact-bounded *type* and
  the boundary are shipped.
- `F1Square.lean`: the status roll-up `F1SquareStatus` gains `liPositivityHolds := none` — the analytic
  face of RH, alongside the geometric `hodgeIndexHolds := none`. Both crux faces are `none`. New v0.10.0
  mapping + two elaboration-checked `example`s (the Li boundary; ζ as an exact-bounded object);
  `scripts/audit_axioms.lean` extended (coverage now 279/279, enforced); honesty audit PASS,
  axiom-clean and choice-free.

### Note
- RH remains **open** (June 2026); Li-positivity is unproven for all `n` (only finite ranges checked
  numerically). No 𝔽₁-square construction exists. This brick makes the analytic boundary *statable and
  checkable* — it does not, and cannot here, prove `λₙ > 0 ∀n`, which is RH.

## [0.9.0] - 2026-06-06

### Added — the general exponential `exp(q)` on the rational interval `[0,1]` (pure Lean 4, no Mathlib, no `sorry`, choice-free)
- `F1Square/Analysis/ExpGen.lean` — **`exp(q) = Σ qⁱ/i!` for rational `q ∈ [0,1]`, as a constructive
  real**, with a rigorous rational error bound. This continues the transcendentals arc opened by
  `e = exp(1)` (v0.8.0) and reuses its machinery almost verbatim — the only genuinely new input is
  **termwise domination**: for `q ∈ [0,1]` every power `qⁱ ≤ 1`, so each term `qⁱ/i! ≤ 1/i!`.
- **Rational powers from scratch** `qpow` (core has no `q^i`), with `qpow_le_one` (`q ∈ [0,1] ⇒ qⁱ ≤ 1`),
  `qpow_nonneg`, `qpow_den_pos`.
- **The domination bridge** `expTerm_le` (`qⁱ/i! ≤ 1/i!`) and `expdiff_dom` (the `exp(q)` partial-sum
  gaps are dominated termwise by those of `e`), giving the rigorous error bound `expdiff_bound`: for
  `a ≤ b`, `S_q(b) − S_q(a) ≤ 2/(a+1)!` — the *same* rational tail bound as `e`, no new tail analysis.
  The reindex `n ↦ S_q(n+1)` reuses `efct_reindex` verbatim, so `expSeq q` is regular
  (`expSeq_regular`) and `Rexp q` is a genuine constructive real.
- **Correctness anchors**: `Rexp_zero` (`exp 0 ≈ 1`), `Rexp_one_pos` (`exp 1 > 0`), and
  `Rexp_one_eq_e` (`exp 1 ≈ e` — the general construction specializes to v0.8.0's Euler number, a
  genuine regression anchor).
- `F1Square/Analysis/QOrder.lean` gains `Qeq_trans` (ℚ value-equality is an equivalence — the
  cross-multiplied identities are linear-combined and cancelled via `b.den > 0`), reusable infrastructure.
- `scripts/audit_axioms.lean` extended; the honesty gate stays green (every theorem
  `⊆ {propext, Classical.choice, Quot.sound}`; in fact choice-free; no `sorry`/`native_decide`/stray axiom).
  `F1Square.lean` gains a v0.9.0 `example`.

### Hardened (peer-review readiness)
- **Self-enforcing audit coverage.** `scripts/honesty_audit.sh` now mechanically checks that *every*
  non-private proof-layer `theorem`/`lemma` (248 of them) is `#print axioms`-audited in
  `audit_axioms.lean`, and fails CI otherwise. Previously the audit list was hand-maintained and ~30
  declarations (4 of them un-reachable leaf `rfl`-lemmas) were unlisted; all are now audited and the
  "every theorem is checked" invariant can no longer silently drift.
- **Honest prose pass.** Tightened documentation wording so sub-result status is unambiguous: T1 is
  scoped to "point-set level, surface unbuilt" (no longer "the 2D surface exists"); the §2.3
  shift-length finding leads with its *vacuity* (it equals RH, not a step toward it); the §9.1 lift is
  labelled as re-verification on genuine product surfaces `C × C` (not the unbuilt `𝕊`); the
  characteristic-1 status block distinguishes Lean kernel-checked (R1–R6, R9–R16) from
  numerically-checked (R7/R8). Stale `v0.0.1` publishing/citation instructions in `README.md` updated.

### Changed
- `docs/` roadmap re-paced within the transcendentals arc: v0.9.0 delivers `exp(q)` on `[0,1]`; the
  everywhere-defined `exp` on ℝ (via the halving/squaring identity `exp x = exp(x/2ᵏ)^{2ᵏ}`), `cos`/`sin`
  (alternating series with the even/odd sandwich remainder — genuinely new machinery), and `log`
  (positivity-as-data + the artanh series) follow in v0.10.0+.

### Note
- RH remains **open** (June 2026), and no construction of the 𝔽₁-square exists (fresh mid-2026
  synthesis: the Feb-2026 Connes–Consani *On the Jacobian of Spec ℤ̄* [arXiv:2602.15941] is a
  Jacobian/adele-class-space construction — a monoidal extension of the Picard group of the arithmetic
  curve — **not** the square and **not** an intrinsic intersection theory; nothing newer on that axis
  was found). The transcendentals make more of the analytic half *statable and checkable*, never
  proven — proving `λₙ ≥ 0 ∀n` / the Hodge index on 𝕊 is RH.

## [0.8.0] - 2026-06-06

### Added — the first transcendental: Euler's number `e` via the exponential series (pure Lean 4, no Mathlib, no `sorry`)
- `F1Square/Analysis/Exp.lean` — **`e = Σ 1/i!` as a constructive real**, with a rigorous rational
  error bound. Standing on completeness (a convergent series is a regular sequence of its partial
  sums); since the partial sums are *rational*, the reindexed partial-sum sequence is directly a
  regular sequence of rationals — a `Real`. Factorial is built from scratch (`fct`) because Lean core
  has no `Nat.factorial`.
- **The rigorous error bound** `ediff_bound`: for `a ≤ b`, the partial-sum gap `S(b) − S(a) ≤ 2/(a+1)!`,
  via the telescoping observation that `U(n) := S(n) + 2/(n+1)!` is **decreasing** (`eU_step`, since
  `2/(n+2)! ≤ 1/(n+1)!`) — a fully rational, explicitly computable tail bound. The reindex `n ↦ S(n+1)`
  makes `2/(n+2)! ≤ 1/(n+1)`, so `eSeq` is regular (`eSeq_regular`) and `e` is a genuine real.
- **`e_pos`**: `e` is positive (witnessed at index 0, where its approximant is `2`).
- `scripts/audit_axioms.lean` extended; the honesty gate stays green (every theorem
  `⊆ {propext, Classical.choice, Quot.sound}`; no `sorry`/`native_decide`/stray axiom).

### Changed
- `docs/` roadmap re-paced: the transcendentals are a multi-release **arc** — v0.8.0 delivers the
  exponential-series machinery and `e`; the general `exp(q)` (on `[0,1]`), `cos`/`sin` (alternating
  series), and `log` follow in v0.9.0+. `F1Square.lean` gains a v0.8.0 `example`.

### Note
- RH remains **open**, and no construction of the 𝔽₁-square exists (fresh mid-2026 synthesis: the
  Feb-2026 Connes–Consani *On the Jacobian of Spec ℤ̄* is an Arakelov–Picard reinterpretation, not the
  square; there is still no accepted 𝔽₁-scheme theory realizing `Spec ℤ ×_𝔽₁ Spec ℤ` with an intrinsic
  intersection theory). The transcendentals make more of the analytic half *statable and checkable*,
  never proven — proving `λₙ ≥ 0 ∀n` / the Hodge index on 𝕊 is RH.

## [0.7.0] - 2026-06-06

### Added — Cauchy completeness of ℝ (pure Lean 4, no Mathlib, no `sorry`, choice-free)
- `F1Square/Analysis/Complete.lean` — **every regular sequence of reals converges**. A sequence
  `X : ℕ → Real` is **regular** (`RReg`) when `X j` and `X k` agree within `1/(j+1) + 1/(k+1)` as reals
  (`|(X j)ₙ − (X k)ₙ| ≤ 1/(j+1) + 1/(k+1) + 2/(n+1)`, the canonical modulus). The limit `Rlim X` is
  **Bishop's diagonal** `n ↦ (X(4n+3))_{4n+3}` — the `4n+3` reindex reads each real far enough out that
  the diagonal is itself a regular sequence of rationals (`RlimSeq_regular`), so `Rlim X` is a genuine
  constructive real. **Convergence with a rate** `Rlim_tendsTo`: `X k → Rlim X` within `1/(k+1)` (gap
  `≤ 2/(k+1) + 2/(n+1)`). **Uniqueness** `RTendsTo_unique`: limits are unique up to `≈` (via the
  generalized Archimedean lemma `Qarch_gen` + the linear-bound criterion `Req_of_lin_bound`).
- Supporting ℚ lemmas: `Qfrac_le` / `Qcollapse_le` (collapse a scaled-denominator sum to a unit
  fraction) and `Qabs_Qsub_comm` (`|a−b| = |b−a|`).
- The construction is **choice-free**: because the regular-sequence data carries its own modulus, the
  diagonal needs no countable choice (the `#print axioms` audit shows no `Classical.choice` — only
  `propext`, `Quot.sound`). `scripts/audit_axioms.lean` extended; the honesty gate stays green.

### Changed
- `docs/` roadmap re-paced: the **transcendentals** (exp/log/cos via convergent series with rigorous
  rational error bounds) — which stand directly on this completeness brick (a power series is a regular
  sequence of its partial sums) — move to v0.8.0. `F1Square.lean` gains a v0.7.0 `example`.

### Note
- RH remains **open**, and no construction of the 𝔽₁-square exists (fresh mid-2026 synthesis: the
  Feb-2026 Connes–Consani *On the Jacobian of Spec ℤ̄* is an Arakelov–Picard reinterpretation, not the
  square; there is still no accepted 𝔽₁-scheme theory realizing `Spec ℤ ×_𝔽₁ Spec ℤ` with an intrinsic
  intersection theory). Completeness makes the analytic half *statable and checkable*, never proven —
  proving `λₙ ≥ 0 ∀n` / the Hodge index on 𝕊 is RH.

## [0.6.0] - 2026-06-06

### Added — ℝ and ℂ are commutative rings up to `≈`; ℝ multiplication well-defined on the setoid (pure Lean 4, no Mathlib, no `sorry`)
- `F1Square/Analysis/QOrder.lean` — the **generalized Archimedean lemma** `Qarch_gen`: if
  `p ≤ q + C/(m+1)` for every `m` (any fixed coefficient `C : ℕ`), then `p ≤ q`. Plus `Qscale_le`,
  the bound-fraction monotonicity `c ≤ d, j ≤ k ⟹ c/(k+1) ≤ d/(j+1)`.
- `F1Square/Analysis/Real.lean` — **the linear-bound criterion** `Req_of_lin_bound` (Lemma A): if
  `|xₙ − yₙ| ≤ C/(n+1)` for every `n` (any constant `C`), then `x ≈ y` — our packaging of the Bishop
  ε-shift transitivity argument into one reusable engine that converts every reindex-mismatch into a
  clean `≈`. Supporting product-gap engine: `Rmul_gap` (`|x_a y_a − x_b y_b| ≤ L(s+t)/(n+1)`),
  `Rgap_le`/`Rcross_le` (collapse same/`≈`-cross gaps to scale `1/(n+1)`), `canon_bound_mul`/`canon_bound_le`.
- `F1Square/Analysis/Real.lean` — **ℝ is a commutative ring up to `≈`**: `Rmul_congr` (multiplication
  is well-defined on the Bishop setoid — the v0.5.0-deferred congruence, now proved), `Rmul_assoc`
  (triple product, nested product-gaps), `Rmul_distrib`, `Rmul_one`, `Radd_assoc`, `Rmul_zero`,
  `Radd_zero`, `Rsub_zero`; plus `Rmul_neg_left/right`, `Rmul_sub_distrib(_right)`, `Rmul_distrib_right`
  and the pointwise re-association lemmas (`Rsub_Radd_Radd`, `Radd_swap`, `Rreassoc_sub`, `Rreassoc_add`).
- `F1Square/Analysis/Complex.lean` — **ℂ is a commutative ring up to `≈`**: `Cadd_assoc`, `Cmul_one`,
  `Cmul_distrib`, and `Cmul_assoc` (the bilinear expansion of `(a+bi)(c+di)`, reduced via the ℝ ring
  laws to pointwise additive re-associations). Together with v0.5.0's `Cadd_comm`/`Cadd_neg`/`Cmul_comm`,
  ℂ now satisfies all commutative-ring axioms up to `≈`.
- `scripts/audit_axioms.lean` extended to all new theorems; the honesty gate stays green
  (every theorem `⊆ {propext, Classical.choice, Quot.sound}`; no `sorry`/`native_decide`/stray axiom).

### Changed
- `docs/` roadmap re-paced: **completeness** (every regular sequence of reals converges) and the
  **transcendentals** (exp/cos via convergent series with rigorous error bounds) move to v0.7.0, now
  that ℝ/ℂ are verified commutative rings. `F1Square.lean` gains a v0.6.0 `example`.

### Note
- RH remains **open**, and no construction of the 𝔽₁-square exists (fresh mid-2026 synthesis: the
  Feb-2026 Connes–Consani *On the Jacobian of Spec ℤ̄* is an Arakelov–Picard reinterpretation of the
  adele class space, not the square; tropical Hodge-index theory is mature geometrically but unbridged
  to the arithmetic setting). v0.6.0 finishes the ℝ/ℂ algebraic substrate (commutative rings up to
  `≈`); it makes the analytic half *statable and checkable*, never proven — proving `λₙ ≥ 0 ∀n` / the
  Hodge index on 𝕊 is RH.

## [0.5.0] - 2026-06-06

### Added — ℝ's equality is an equivalence, ℝ multiplication, ℂ = ℝ×ℝ (pure Lean 4, no Mathlib, no `sorry`)
- `F1Square/Analysis/QOrder.lean` — the **Archimedean lemma** `Qarch` (if `p ≤ q + 6/(m+1)` for all
  `m`, then `p ≤ q`), the 3-point triangle inequality, ℚ order totality, and the **ℚ
  multiplication-order library**: `Qabs_mul` (|ab|=|a||b|), non-negative product monotonicity
  `Qmul_le_mul`, and the product-difference triangle `Qabs_mul_diff`
  (`|x_a y_a − x_b y_b| ≤ |x_a||y_a−y_b| + |y_b||x_a−x_b|`).
- `F1Square/Analysis/Real.lean` — **`≈` is now a full equivalence**: transitivity `Req_trans` via the
  Archimedean lemma (the `2/(n+1) + 6/(m+1)` four-triangle argument). **ℝ multiplication** `Rmul`:
  reindex both factors at `r(n) = 2K(n+1)−1` with `K` the canonical bound `|xₙ| ≤ |x₀|+2`
  (`canon_bound`), regularity proved (the `2K` reindexing cancels the bound, via `ring_uor`);
  commutativity `Rmul_comm`. Plus `Rsub` and the additive-group laws `Radd_comm`, `Radd_neg`.
- `F1Square/Analysis/Real.lean` — **operation-congruence over `≈`**: `Rneg_congr`, `Radd_congr`,
  `Rsub_congr` (the operations are well-defined on the Bishop setoid — the prerequisite for the ℂ ring
  laws).
- `F1Square/Analysis/Complex.lean` — **ℂ = ℝ×ℝ** with componentwise Bishop equality (an equivalence,
  `Ceq_refl/symm/trans`) and **all four operations**: `Cadd`, `Cneg`, `Cmul` (`(ac−bd, ad+bc)`), the
  constants `0, 1, i`, and the embedding ℝ ↪ ℂ; the additive-group laws (`Cadd_comm`, `Cadd_neg`) and
  **commutative multiplication** `Cmul_comm` (up to `≈`, via the operation-congruences + `Rmul_comm`).
- `scripts/audit_axioms.lean` extended to all new theorems; the honesty gate stays green.

### Changed
- `Qsub`/`Qabs`/`Qlt` and the denominator-positivity helpers now live in `Analysis/Rat.lean` (basic
  ℚ operations). `docs/` roadmap advances; `F1Square.lean` gains a v0.5.0 `example`.

### Note
- RH remains **open**. v0.5.0 completes the ℝ/ℂ field arithmetic, makes Bishop equality an
  equivalence, and gives ℂ a commutative multiplication up to `≈`. The remaining ℂ ring laws
  (associativity, distributivity) need `Rmul`-congruence and `Rmul`-associativity — a reindex-
  reconciliation theorem — which, with completeness and the transcendentals, is the v0.6.0
  continuation. The substrate makes the analytic half *statable and checkable*, never proven —
  proving `λₙ ≥ 0 ∀n` / the Hodge index on 𝕊 is RH.

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

[0.12.0]: https://github.com/afflom/F1/releases/tag/v0.12.0
[0.11.0]: https://github.com/afflom/F1/releases/tag/v0.11.0
[0.10.0]: https://github.com/afflom/F1/releases/tag/v0.10.0
[0.9.0]: https://github.com/afflom/F1/releases/tag/v0.9.0
[0.8.0]: https://github.com/afflom/F1/releases/tag/v0.8.0
[0.7.0]: https://github.com/afflom/F1/releases/tag/v0.7.0
[0.6.0]: https://github.com/afflom/F1/releases/tag/v0.6.0
[0.5.0]: https://github.com/afflom/F1/releases/tag/v0.5.0
[0.4.0]: https://github.com/afflom/F1/releases/tag/v0.4.0
[0.3.0]: https://github.com/afflom/F1/releases/tag/v0.3.0
[0.2.0]: https://github.com/afflom/F1/releases/tag/v0.2.0
[0.1.0]: https://github.com/afflom/F1/releases/tag/v0.1.0
[0.0.1]: https://github.com/afflom/F1/releases/tag/v0.0.1
