# Changelog

All notable changes to this project are documented here. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and this project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html), starting at `v0.0.1`.

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
- **`exp(log n) = n`** (`F1Square/Analysis/ExpLog.lean`) — `Rexp_log_nat`: `RexpReal (TwoArtanhConst (tmap n))
  ≈ n`. Since `log n = 2·artanh((n−1)/(n+1))` is the constructive definition of `Rlog`, this is `exp∘log = id`
  on the naturals. Instantiates the base identity at `τ = tmap n = (n−1)/(n+1)`, `g = n`, `K = (n+1)/2`; the
  closed forms `1−τ = 2/(n+1)`, `g·(1−τ) = 1+τ`, `K·(1−τ) = 1` are pure `tmap`-arithmetic (`tmap_nat_den`/`num`).
- **Why it matters.** This closes the discovered dependency of stage A: `Σ n^{-s}` converges because
  `|n^{-s}| = n^{-Re s}`, i.e. `exp(log n) = n`. The honesty gate is met — the identity closes **axiom-clean**
  (`{propext, Quot.sound}` only), so the ζ-complex tail (v0.15.2) need not ship its convergence as an interface.
- **Scope (honest).** `Rexp_log_nat` is stated for `TwoArtanhConst (tmap n)` — which *is* `log n` by the
  constructive definition `log n = 2·artanh((n−1)/(n+1))`, but takes the argument value `τ = tmap n` as the
  artanh radius. Identifying it with the *literal* `Rlog (ofQ n)` term (whose radius `ρ_M` is deliberately
  smaller) needs a radius reconciliation valid for `τ` up to `1` — deferred to v0.15.2 (the existing
  `Rartanh_radius_indep`/`Rartanh_congr` assume `τ² ≤ ½`, which `tmap n` violates for `n ≥ 6`), never faked.
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
