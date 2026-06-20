/-
F1 square — v0.22.0 Track 1: **real-part conjugation invariance of the complex digamma**
`Re ψ(s̄) = Re ψ(s)` (`CDigamma_re_conj`), a genuine *property* of the constructed `CDigamma`.

The real part of `1/(s+n)` is `(Re s + n)/|s+n|²`, and both `Re(s+n)` and `|s+n|² = (Re s+n)² +
(Im s)²` are invariant under `s ↦ s̄` (the `Im` enters only squared). So every term's real part — hence
the whole real series — is conjugation-invariant. This is the digamma face of ξ's conjugate-pair zero
symmetry, and it is exactly the part Track 2's `Re ψ(1/4 + iτ/2)` (`BurnolAlpha`/`PsiLine`) lives on.

Demonstrates the reusable limit/reciprocal congruences `Rlim_congr` and `Rinv_congr` (`RlimProps.lean`):
the two real-part partial-sum sequences are pointwise `≈` (each term `≈` via `Rinv_congr` on
`|s̄+n|² ≈ |s+n|²`), so their diagonal limits agree.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/
import F1Square.Analysis.ComplexDigamma
import F1Square.Analysis.RlimProps
import F1Square.Analysis.Reflection

namespace UOR.Bridge.F1Square.Analysis

/-- **`genSum` respects pointwise `≈`** (termwise congruence of the finite partial sum). -/
theorem genSum_congr (T T' : Nat → Real) (h : ∀ n, Req (T n) (T' n)) :
    ∀ N, Req (genSum T N) (genSum T' N)
  | 0 => Req_refl _
  | (N + 1) => Radd_congr (genSum_congr T T' h N) (h N)

/-- **`|s̄+n|² ≈ |s+n|²`**: the modulus-squared is conjugation-invariant (`Im` enters only as
    `(±Im s)²`). -/
theorem CnormSq_CdigammaArg_conj (s : Complex) (n : Nat) :
    Req (CnormSq (CdigammaArg (Cconj s) n)) (CnormSq (CdigammaArg s n)) := by
  show Req (Radd (Rmul (Radd s.re (RofNat n)) (Radd s.re (RofNat n))) (Rmul (Rneg s.im) (Rneg s.im)))
    (Radd (Rmul (Radd s.re (RofNat n)) (Radd s.re (RofNat n))) (Rmul s.im s.im))
  refine Radd_congr (Req_refl _) ?_
  exact Req_trans (Rmul_neg_left s.im (Rneg s.im))
    (Req_trans (Rneg_congr (Rmul_neg_right s.im s.im)) (Rneg_neg (Rmul s.im s.im)))

set_option maxHeartbeats 400000 in
/-- **The `n`-th term's real part is conjugation-invariant**: `Re Cterm(s̄,n) ≈ Re Cterm(s,n)`. The
    `1/(n+1)` and `Re(s+n) = Re(s̄+n)` parts are identical; the reciprocal `1/|s̄+n|² ≈ 1/|s+n|²` is
    `Rinv_congr` of `CnormSq_CdigammaArg_conj`. -/
theorem CdigammaTerm_re_conj (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) (n : Nat) :
    Req (CdigammaTerm (Cconj s) hcn hcd hcs n).re (CdigammaTerm s hcn hcd hcs n).re := by
  simp only [CdigammaTerm_re]
  refine Radd_congr (Req_refl _) (Rneg_congr (Rmul_congr (Req_refl _) ?_))
  exact Rinv_congr (CdigammaArg_witness (s := Cconj s) hcn hcd hcs n)
    (CdigammaArg_witness (s := s) hcn hcd hcs n) (CnormSq_CdigammaArg_conj s n)

/-- **The complex digamma core's real part is conjugation-invariant**: `Re (Σ-core)(s̄) ≈ Re
    (Σ-core)(s)`. The two `Re`-partial-sum sequences share the same reindex `Midx` (same `B1, B2`) and
    are pointwise `≈` (`genSum_congr` + `CdigammaTerm_re_conj`), so `Rlim_congr` equates their limits. -/
theorem CDigammaCore_re_conj (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) {B1 B2 : Q} (hB1d : 0 < B1.den) (hB2d : 0 < B2.den)
    (hB10 : 0 ≤ B1.num) (hB20 : 0 ≤ B2.num)
    (hB1lo : Rle (Rneg (ofQ B1 hB1d)) (Rsub s.re one)) (hB1hi : Rle (Rsub s.re one) (ofQ B1 hB1d))
    (hB2lo : Rle (Rneg (ofQ B2 hB2d)) s.im) (hB2hi : Rle s.im (ofQ B2 hB2d)) :
    Req (CDigammaCore (Cconj s) hcn hcd hcs hB1d hB2d hB10 hB20 hB1lo hB1hi
          (Rle_Rneg hB2hi) (Rle_trans (Rle_Rneg hB2lo) (Rle_of_Req (Rneg_neg (ofQ B2 hB2d))))).re
        (CDigammaCore s hcn hcd hcs hB1d hB2d hB10 hB20 hB1lo hB1hi hB2lo hB2hi).re :=
  Rlim_congr
    (fun j => genSum (fun n => (CdigammaTerm (Cconj s) hcn hcd hcs n).re)
      (digammaMidx (add B1 (mul B2 B2)) j))
    (fun j => genSum (fun n => (CdigammaTerm s hcn hcd hcs n).re)
      (digammaMidx (add B1 (mul B2 B2)) j))
    (CdigammaReSum_RReg (Cconj s) hcn hcd hcs hB1d hB2d hB10 hB20 hB1lo hB1hi
      (Rle_Rneg hB2hi) (Rle_trans (Rle_Rneg hB2lo) (Rle_of_Req (Rneg_neg (ofQ B2 hB2d)))))
    (CdigammaReSum_RReg s hcn hcd hcs hB1d hB2d hB10 hB20 hB1lo hB1hi hB2lo hB2hi)
    (fun _j => genSum_congr _ _ (fun n => CdigammaTerm_re_conj s hcn hcd hcs n) _)

/-- **★ real-part conjugation invariance of `ψ`** `Re ψ(s̄) = Re ψ(s)`: with `ψ(s) = −γ + core(s)`, the
    `−γ` (real) contributes the same real part, and `Re core(s̄) ≈ Re core(s)` by `CDigammaCore_re_conj`.
    The archimedean face of ξ's conjugate-pair symmetry; the line `Re ψ(1/4 + iτ/2)` of Track 2 is its
    instance. -/
theorem CDigamma_re_conj (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) {B1 B2 : Q} (hB1d : 0 < B1.den) (hB2d : 0 < B2.den)
    (hB10 : 0 ≤ B1.num) (hB20 : 0 ≤ B2.num)
    (hB1lo : Rle (Rneg (ofQ B1 hB1d)) (Rsub s.re one)) (hB1hi : Rle (Rsub s.re one) (ofQ B1 hB1d))
    (hB2lo : Rle (Rneg (ofQ B2 hB2d)) s.im) (hB2hi : Rle s.im (ofQ B2 hB2d)) :
    Req (CDigamma (Cconj s) hcn hcd hcs hB1d hB2d hB10 hB20 hB1lo hB1hi
          (Rle_Rneg hB2hi) (Rle_trans (Rle_Rneg hB2lo) (Rle_of_Req (Rneg_neg (ofQ B2 hB2d))))).re
        (CDigamma s hcn hcd hcs hB1d hB2d hB10 hB20 hB1lo hB1hi hB2lo hB2hi).re :=
  Radd_congr (Req_refl _)
    (CDigammaCore_re_conj s hcn hcd hcs hB1d hB2d hB10 hB20 hB1lo hB1hi hB2lo hB2hi)

end UOR.Bridge.F1Square.Analysis
