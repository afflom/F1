# F1 Square — Roadmap to completion (v0.15.0 → v0.19.0)

The genuine-proof layer (`F1Square/`) builds the 𝔽₁ / Riemann-Hypothesis program from first
principles in **pure Lean 4** (Lean core + UOR-Foundation, **no Mathlib, no `sorry`/`native_decide`,
choice-free** — `{propext, Quot.sound}` only). Every commit is green and `#print axioms`-audited by
`scripts/honesty_audit.sh`.

**The bright line (permanent).** The honesty layer is a *verifier*, not a prohibition. The crux fields
`hodgeIndexHolds` and `liPositivityHolds` (both = RH) stay `none` until a genuine, audited, axiom-clean
proof exists. De-hedging removes *false modesty* about proven results; it never adds *false confidence*.
**The gate decides what is asserted, not ambition** — anything that does not close honestly stays an
explicit interface, exactly as the existing `Li`/`Crux` interfaces do, never faked.

The remaining construction is scoped into five releases (stages **A–E**). Each is multi-commit, green
at every commit, axiom-clean, and resolved by analyzing the implementation here plus deep-research where
the literature is needed. Uncertainty (especially on the geometric frontier) is a research input, not a
stop sign — the focus is always the **construction of the F1 square**, to completion.

## Status recap (`F1SquareStatus`, `F1Square.lean`)

| Field | Now | Target release |
|---|---|---|
| `intersectionTemplateValid` | `some true` (template) | → canonical 𝕊 in **C / v0.17.0** |
| `ampleClassExists` | `some true` (template) | → canonical 𝕊 in **C / v0.17.0** |
| `classGroupFinitelyGen` | `some true` (template) | → canonical 𝕊 in **C / v0.17.0** |
| `surfaceConstructed` | `none` (candidate) | **C / v0.17.0** |
| `parallelPencilFinding` | `none` (candidate) | **C / v0.17.0** |
| `hodgeIndexHolds` (= RH, geometric) | `none` | **D / v0.18.0** (iff genuinely proven) |
| `liPositivityHolds` (= RH, analytic) | `none` | **D / v0.18.0** (iff genuinely proven) |

---

## v0.15.0 — (A) The complex analytic engine: exponential core **[shipped]**

Lift the analytic substrate from ℝ to ℂ and make `exp` a homomorphism — the prerequisite that the rest of
stage A (ζ for complex argument) builds on. **Shipped:**

- `Analysis/ComplexExp.lean` — `Cexp z = exp(re z)·(cos(im z) + i·sin(im z))` from `RexpReal/Rcos/Rsin`,
  with the component identities and `Cexp 0 ≈ 1` (`Cexp_zero`, `RexpReal_zero`, `Rcos_zero`, `Rsin_zero`).
- `Analysis/CosSinAdd.lean`, `Analysis/CosSinBound.lean` — **the trigonometric keystone** `cos² + sin² ≈ 1`
  (`Rcos_sq_add_sin_sq`) via the trig Cauchy product from scratch, giving `|cos| ≤ 1`, `|sin| ≤ 1`.
- `Analysis/ExpRealAdd.lean` — **the exponential keystone** `RexpReal_add` (`exp(x+y) ≈ exp x · exp y` on
  all of ℝ), the roadmap's technical core of stage A: the signed Cauchy-product functional equation
  (`expSum_add_le_signed`) lifted to the diagonal through a deep reference depth (`rexp_add_gap`,
  `RexpReal_add_aux`, `rexp_factor_reconcile`), plus the reusable ζ-tail toolkit (corner bound,
  reconciliation, uniform partial-sum bound, factorial decay).
- `Analysis/ComplexMod.lean`, `Analysis/ComplexPow.lean` — `nˢ` (`ncpow n s = Cexp(s·log n)`, positive-integer
  base) and the **modulus identity** `|Cexp z|² = (exp Re z)²` (`Cexp_normSq`) / `|nˢ|² = (exp(Re s·log n))²`
  (`ncpow_normSq`), the analytic payoff of `cos² + sin² = 1`.
- **De-hedges:** "exp/cos/sin without addition laws" → "exp is a homomorphism; `|cos|,|sin| ≤ 1`; the complex
  exponential and `nˢ` with their modulus".
- **Stays open:** the critical strip; zeros; crux. (ζ at complex `s` with `Re s > 1` shipped in v0.15.2.)

## The v0.15.x series — (A, continued) completing ζ for complex argument

Stage A's remaining original goals (ζ for `Re s > 1`, the prime side, the `n = 1` decomposition) are gated on
a single **discovered dependency**: convergence of `Σ n^{-s}` needs `|n^{-s}| = n^{-Re s}`, i.e.
`exp(log n) = n`. Because `log` is built independently as `2·artanh((x−1)/(x+1))`, this is **not**
definitional, and every elementary route (`exp(t) ≥ 1+t` + multiplicativity via `RexpReal_add` + the two-sided
exp bounds) only *squeezes* `1 + log x ≤ exp(log x) ≤ 1/(1−log x)` — never pinning equality (iterated squaring
amplifies the second-order error). The honest conclusion: `exp∘log = id` requires a genuine **power-series
composition** (compose the exp factorial series with the artanh geometric series ⇒ `exp(2·artanh w) =
(1+w)/(1−w)`), a from-scratch build of its own. It is scoped as its own release so the shipped exponential
core is not held hostage to it.

- **v0.15.1 — `exp∘log = id` (the power-series composition gate) [shipped].** Built `exp(2·artanh w) =
  (1+w)/(1−w)` from scratch as a genuine power-series composition (`Rexp_two_artanh_ofQ`), and its corollary
  `exp(log n) = n` **for the literal `Rlog` term** (`Rexp_log_nat_Rlog`: `RexpReal (Rlog (ofQ n) …) ≈ n`). The
  base construction is **radius-general** — the convergence radius enters only through the depth reindex
  (abstracted by `Rexp_two_artanh_via`), so it applies at `Rlog`'s own radius `ρ_M = (n−1)/(n+1)` directly and
  `Rlog (ofQ n) = TwoArtanhConst (tmap n) ρ_M` by `rfl`; **no `τ²≤½` smallness is needed**, so no radius
  reconciliation is required. The honesty gate is met — the identity closes **axiom-clean**
  (`{propext, Quot.sound}`), so the ζ-complex tail (v0.15.2) need not ship its convergence as an interface.
  Remaining for v0.15.2: lifting to real exponents `c·log n` (`exp(c·log n) = nᶜ`) and `Czeta`.
- **v0.15.2 — ζ(s) for complex `Re(s) > 1` (`Analysis/ComplexZeta.lean`) [shipped].** `Czeta s` for `Re(s) > 1`
  as `Σ n^{-s}` with a rigorous complex tail: the dyadic block modulus `≤ ofQ(rᵏ)` (`czetaExp_block_geo`,
  `r = 1/(1+τ) < 1`), the geometric tail `geoFrom_le` (`Σ rᵏ ≤ rʲ/(1−r)`), the Bernoulli reindex
  `geom_reindex` (`r^{M(j)}/(1−r) ≤ 1/(j+1)`, `M(j) = (j+1)·r.den²`), the completeness bridge
  `seq_diff_le`/`RReg_of_real_bound` (real bound → `RReg`), and `czetaRe/Im_RReg` → Bishop `Rlim`. `Czeta_re/
  im_tendsTo` certify convergence with rate `2/(k+1)`. **De-hedged:** "ζ only at integer `s ≥ 2`" →
  "ζ(s), complex `s`, `Re(s) > 1`". (The log-multiplicativity `log(2ᵏ) = k·log 2` came via exp injectivity
  `RexpReal_inj`, re-routing the artanh addition boundary wall — `exp∘log = id` of v0.15.1 was the gate.)
- **v0.15.3 — `Analysis/Mangoldt.lean` + the `n = 1` decomposition [shipped].** von Mangoldt `Λ`
  (`vonMangoldt`, via the smallest factor `spf`; `Λ(4) = log 2`, `Λ(6) = 0`, `Λ ≥ 0`) and the
  explicit-formula **prime side** `Σ_p Σ_k log p · h(k log p) = Σ_{n≥2} Λ(n)·h(log n)` (`primeSide`) as a real
  (finite for compactly-supported `h` — `primeSide_stable` makes it constant past the support cutoff), and the
  **Bombieri–Lagarias `λₙ = λₙ^{arith} + λₙ^{∞}` for `n = 1`** as a theorem (`Rlambda1_decomposition`,
  `Analysis/LiOne.lean`): `λ₁ = γ + (1 − γ/2 − ½·log 4π)`, the finite-place `S_f(1) = −η₀ = γ` plus the
  archimedean `S_∞(1)`, summing to the `λ₁` of v0.14.0. This **promotes `Li.LiDecomposition` from the trivial
  inhabitant `λ = λ + 0` to a proven non-trivial instance** (`li_decomposition_realized`) whose `n = 1` slice is
  the genuine two-place split. (Deriving `S_f(1) = γ` from the prime sum needs `ζ'/ζ` continuation, deferred —
  the BL value is stated faithfully, not fabricated; nothing bears on positivity, `liPositivityHolds = none`.)
- **Stays open across v0.15.x:** critical strip, zeros, crux.

## v0.16.0 — (B) Analytic continuation & higher Li coefficients **[shipped]**

The heavy analytic mechanization: ζ off the convergent regime and the `λₙ` for `n ≥ 2`.

- `Analysis/Gamma.lean` — `Γ` via Spouge; the archimedean (`Γ′/Γ`) place. **Shipped:** the real-power
  combinator `RrpowPos` (`x^y = exp(y·log x)`, no sqrt/no complex `Clog`), the **exact** digamma
  `ψ = Γ′/Γ` (`Digamma`, `Digamma_one_eq_neg_gamma`), and the Spouge `Γ`-approximant (`SpougeGamma`).
- Critical-strip ζ — shipped via the integration-free **Dirichlet-η** route (`Analysis/EtaVariation.lean`,
  `Analysis/CriticalZeta.lean`): `Ceta`/`CetaW` (η on `Re s > 0`), `CzetaStrip`/`CzetaStripW`
  (`ζ = η/(1−2^{1−s})` on `0 < Re s < 1`) as an `ExactBoundedReal`, with non-vanishing, the functional
  relation, and uniqueness. (Cleaner than the periodic-Bernoulli remainder; same deliverable.)
- Higher **Stieltjes `γₙ`** → individual **`λₙ` values** for `n ≥ 2`, with a `λ₁`-style positivity
  certificate — **shipped:** `Pos λ₂` (`Rlambda2_pos`).
- **De-hedges done:** "genuine `λₙ` values deferred" → built for `n ≥ 2`; critical-strip ζ built.
- **Honesty gate:** research-grade; whatever does not close axiom-clean stays an interface.
- **Stays open:** `λₙ > 0 ∀ n` (= RH); off-critical-line zeros; the crux (`liPositivityHolds = none`).

## v0.17.0 — (C) The arithmetic square 𝕊

Construct the object the whole program runs on. The frontier is less unknown than it looks: the
candidate bi-tropical model, the proved mechanism, and the §2.3 control already constrain it; the gap is
making `𝕊 = Spec ℤ ×_𝔽₁ Spec ℤ` (the `F ⊗_𝔹 F` tensor) canonical.

- Construct canonical `𝕊` and its intersection lattice (`surfaceConstructed`, `parallelPencilFinding`).
- Lift `intersectionTemplateValid` / `ampleClassExists` / `classGroupFinitelyGen` from the
  product-of-curves template to canonical `𝕊` (the `Crux.Polarized` instance becomes `𝕊`, not the template).
- **De-hedges:** `surfaceConstructed`, `parallelPencilFinding`, and the three template fields → canonical 𝕊.
- **Method:** analyze `Mechanism`/`Bridge`/`Tropical` + deep-research the 𝔽₁ tensor / arithmetic-surface
  literature (Deninger, Connes–Consani, Borger) to fix the canonical construction.

## v0.18.0 — (D) The bridge and the crux

State the geometric↔analytic equivalence faithfully, and **attempt** the crux on canonical `𝕊`.

- The equivalence `Crux.HodgeIndex 𝕊 ⟺ Li.LiPositive λ` (classical; stated as a faithful theorem/interface).
- The **Hodge-index / Li-positivity attempt** on canonical `𝕊` under the gate. This is where RH closes
  **iff** it closes: `hodgeIndexHolds` / `liPositivityHolds` flip `none → some true` **iff** a genuine,
  audited, axiom-clean proof lands — otherwise they stay `none` and RH stays open, and the release still
  ships the bridge substrate. No fake, no `decide`-over-finite-N, no template substitution (see the
  faithfulness cautions in `Crux.lean` / `Li.lean`).

## v0.19.0 — (E) Completion: the explicit formula and the F1-square roll-up

Assemble the full Weil explicit formula and the final status record.

- The complete `Li.ExplicitFormulaTrace` — the **zero side** (`Σ` over the nontrivial zeros). This is
  RH-equivalent: it becomes provable exactly when the crux (D) closes; until then it remains the honest
  interface it is today.
- Retire the remaining honest interfaces (`LiAgreesWith`, …) as theorems where the now-built ζ/`λ` make
  them so.
- The final F1-square status roll-up and a v1.0.0-candidate state.

---

## What stays open regardless

If v0.18 / v0.19 do not close the crux axiom-clean, `hodgeIndexHolds` / `liPositivityHolds` stay `none`
and **RH stays open** — the releases still ship every surrounding construction. The bright line is
permanent: the crux is de-hedged iff RH is proven, and it is not until it is.
