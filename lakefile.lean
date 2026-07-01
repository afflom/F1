import Lake
open Lake DSL

/-!
The 𝔽₁ Square with an Intersection Theory — a research program toward
`Spec ℤ ×_{𝔽₁} Spec ℤ` and the Hodge-index positivity that is the Riemann Hypothesis.

This package extends the UOR-Foundation Lean library (the `uor` package). It is pinned to a
concrete release tag (v0.5.2 — the latest UOR-Framework release that ships the `lean4/` library)
for reproducibility; the exact resolved revision is frozen in `lake-manifest.json`.
-/

package f1square where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]
  -- Raise the kernel evaluator's thread stack so the tightened n=5 constant-precision brackets
  -- (large-N `decide` certificates: γ₂/γ₃ uppers, etc.) reduce without a C-stack overflow.
  -- This is a stack-size flag only — the proofs stay fully kernel-checked (NOT `native_decide`).
  moreLeanArgs := #["--tstack=16000000"]

require uor from git
  "https://github.com/UOR-Foundation/UOR-Framework" @ "v0.5.2"

@[default_target]
lean_lib F1Square where
  -- Root module: `F1Square.lean` at the repository root (default srcDir ".").
  -- Keeps the seed's `UOR.Bridge.F1Square` namespace, extending the `UOR` library.
