/-
F1 square — Track 1, item 6 (the `bl` arithmetic bridge): the constructive **moment-expansion** face
of `λₙ` (`ComplexBinomial.lean`, `witnessSum_moment_order`) meets the constructive **arithmetic
`η`-face** (`GenuineLi.lean`, `genuineArithSeq`), modulo exactly one classical input per order.

The witness sum (the `bl` zero-sum form of `λₙ`) was decomposed into the per-order reciprocal moments
`M_k = Σ_ρ C(n,k)·(−1/ρ)ᵏ` (`witnessSum_moment_order`). The genuine arithmetic side is
`λₙ^{arith} = −Σ_{j=1}^{n} C(n,j)·η_{j−1}` (`genuineArithSeq`, the `−ζ′/ζ` Taylor data). Both carry the
*same* binomial weighting `C(n,·)`, so they coincide term-by-term as soon as each order's moment equals
its `η` coefficient — `Re(M_k) = C(n,k)·η_{k−1}`, which is precisely the **explicit formula at order `k`**
(the moments of the nontrivial zeros are the `−ζ′/ζ` Taylor coefficients). That per-order identity is the
single labelled classical seam, entered here as an explicit, audit-visible hypothesis (`seam`), never an
axiom and never discharged. Under it, the two faces are *equal* — a faithful, RH-independent relocation
that shrinks the `bl` interface from a monolithic limit to one identity per order.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
The crux fields stay `none`; RH is open.
-/

import F1Square.Analysis.ComplexBinomial
import F1Square.Analysis.GenuineLi

namespace UOR.Bridge.F1Square.Analysis

/-- **The order sum matches the arithmetic tail**: under the per-order seam `Re(M_k) = C(n,k)·η_{k−1}`,
    the real part of the partial moment sum `Σ_{k<N} M_k` equals the arithmetic tail `Σ_{j=1}^{N} C(n,j)·η_{j−1}`
    (`arithTail`), for every `N ≤ n`. A clean induction — both sides append the same `k`-th term (`(CsumN …).re`
    unfolds to `Radd` of the real parts; `arithTail` appends `nsmulR (C(n,k+1)) (η k)`), matched by `seam`. -/
theorem moment_re_eq_arithTail (E : StieltjesEta) (us : List Complex) (n : Nat)
    (seam : ∀ k, k < n → Req (momentList us n k).re (nsmulR (choose n (k + 1)) (E.eta k))) :
    ∀ N, N ≤ n → Req (CsumN (fun k => momentList us n k) N).re (arithTail E.eta n N)
  | 0, _ => Req_refl zero
  | (N + 1), hle =>
      Radd_congr (moment_re_eq_arithTail E us n seam N (Nat.le_of_succ_le hle))
        (seam N (Nat.lt_of_succ_le hle))

/-- **THE `bl` ARITHMETIC BRIDGE** — under the per-order explicit-formula seam, the `bl` zero-sum form of
    `λₙ` (the Li witness sum over the Cayley factors `w = 1 − u`, `u = 1/ρ`) equals the genuine arithmetic
    closed form `genuineArithSeq = −Σ_{j=1}^{n} C(n,j)·η_{j−1}`:

      `Σ_w (1 − Re(wⁿ)) = −Σ_{j=1}^{n} C(n,j)·η_{j−1}`.

    The constructive moment expansion (`witnessSum_moment_order`) and the constructive `η`-form
    (`genuineArithSeq`) are the **same object**, separated only by the per-order identity
    `Re(Σ_ρ C(n,k)·(−1/ρ)ᵏ) = C(n,k)·η_{k−1}` — the explicit formula, order by order. This is the
    faithful relocation Track 1 targets: `bl` is no longer a monolithic limit but one clean identity per
    moment order. The seam is a hypothesis, never discharged; the crux stays `none`. -/
theorem witnessSum_eq_genuineArith (E : StieltjesEta) (us : List Complex) (n : Nat)
    (seam : ∀ k, k < n → Req (momentList us n k).re (nsmulR (choose n (k + 1)) (E.eta k))) :
    Req (witnessSum (us.map (fun u => Cadd Cone (Cneg u))) n) (genuineArithSeq E.eta n) :=
  Req_trans (witnessSum_moment_order n us)
    (Rneg_congr (moment_re_eq_arithTail E us n seam n (Nat.le_refl n)))

end UOR.Bridge.F1Square.Analysis
