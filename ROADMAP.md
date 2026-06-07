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

## v0.15.0 — (A) The complex analytic engine

Lift the analytic substrate from ℝ to ℂ and build ζ for complex argument in the convergent regime.

- `Analysis/ComplexExp.lean` — `Cexp z = exp(re z)·(cos(im z) + i·sin(im z))` from `RexpReal/Rcos/Rsin`;
  principal `Clog` on `Re > 0`; `ncpow n s = Cexp (s · log n)` (`nˢ`, positive-integer base — the only
  base ζ needs, so full multi-branch `Clog` is off the critical path).
- `Analysis/ZetaC.lean` — `Czeta s` for `Re(s) > 1` via `Σ n^{-s}` with a rigorous complex tail bound
  (`|n^{-s}| = n^{-Re s}`, mirroring `Zeta.lean`).
- `Analysis/Mangoldt.lean` — von Mangoldt `Λ` and the explicit-formula **prime side**
  `Σ_p Σ_k log p · h(k log p)` as a real (finite, intrinsically computable).
- Realize the **Bombieri–Lagarias `λₙ = λₙ^{arith} + λₙ^{∞}` for `n = 1`** as a theorem (uses the
  `γ`/`log 4π`/`λ₁` built in v0.14.0), promoting `Li.LiDecomposition` from inhabited-interface to a proven
  instance.
- **De-hedges:** "ζ only at integer `s ≥ 2`" → "ζ(s), complex `s`, `Re(s) > 1`"; `LiDecomposition` (n=1).
- **Stays open:** critical strip, zeros, crux.

## v0.16.0 — (B) Analytic continuation & higher Li coefficients

The heavy analytic mechanization: ζ off the convergent regime and the `λₙ` for `n ≥ 2`.

- `Analysis/Gamma.lean` — `Γ` via Spouge/Lanczos (uses `ncpow`/`Cexp`); the archimedean (`Γ′/Γ`) place.
- `Analysis/EulerMaclaurin.lean` — periodic-Bernoulli remainder (fix-`K`, grow-`N`) → `Czeta` on the
  **critical strip** as an `ExactBoundedReal`.
- Higher **Stieltjes `γₙ`** by the same engine → individual **`λₙ` values** for `n ≥ 2`, with
  `λ₁`-style positivity certificates for *specific small* `n` (e.g. `Pos λ₂`).
- **De-hedges:** "genuine `λₙ` values deferred" → built for `n ≥ 2`; critical-strip ζ.
- **Honesty gate:** research-grade; whatever does not close axiom-clean stays an interface.
- **Stays open:** `λₙ > 0 ∀ n` (= RH).

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
