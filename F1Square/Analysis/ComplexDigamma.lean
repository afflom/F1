/-
F1 square — v0.22.0 Track 1, item 1 (the Γ place on the strip): **the complex digamma term**
`ψ(s) = −γ + Σ_{n≥0} [1/(n+1) − 1/(s+n)]` lifted to complex `s` with `Re s ≥ c > 0` (the strip).

This is the archimedean `Γ′/Γ` place generalized off the real line — the piece of item 1 the
real-line `Gamma.lean` construction does not yet provide. Crucially it is built from the complex
reciprocal `Cinv` ALONE (no `Cpow`/`Clog`), so it is entirely free of the `1/16` value-identity
barrier that gates the argument/power axis; each term `1/(s+n)` is a genuine constructive complex
number with `|s+n|² ≥ c² > 0`.

This file (increment 1) builds the term layer: the shifted complex argument `s+n` (`CdigammaArg`),
its modulus-squared floor `|s+n|² ≥ c²` (`ofQ_le_CnormSq_CdigammaArg`) and the resulting positivity
witness (`CdigammaArg_witness`, mirroring `digammaArg_witness`), and the complex term `CdigammaTerm`.
The per-term bounds, the regular partial sums, and the limit object `CDigamma` follow in later
increments through the generic `RReg_of_real_bound` convergence engine.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/
import F1Square.Analysis.ComplexInv
import F1Square.Analysis.Gamma

namespace UOR.Bridge.F1Square.Analysis

/-- **The shifted complex argument** `s + n` of the `n`-th digamma term, as the explicit pair
    `⟨Re s + n, Im s⟩` (definitionally `s + n` up to `≈`; the explicit form keeps `Re`/`Im`
    projections clean). Its real part is exactly `digammaArg (Re s) n`, so the real-line floor
    machinery transfers verbatim. -/
def CdigammaArg (s : Complex) (n : Nat) : Complex := ⟨Radd s.re (RofNat n), s.im⟩

@[simp] theorem CdigammaArg_re (s : Complex) (n : Nat) :
    (CdigammaArg s n).re = Radd s.re (RofNat n) := rfl
@[simp] theorem CdigammaArg_im (s : Complex) (n : Nat) : (CdigammaArg s n).im = s.im := rfl

/-- **The modulus-squared floor** `|s+n|² ≥ c²` (from the real-part floor `Re s ≥ c > 0`):
    `|s+n|² = (Re s + n)² + (Im s)² ≥ (Re s + n)² ≥ c²` since `Re s + n ≥ c ≥ 0` and `(Im s)² ≥ 0`.
    The complex analogue of the floor `c ≤ z` behind `digammaArg_witness`. -/
theorem ofQ_le_CnormSq_CdigammaArg {s : Complex} {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) (n : Nat) :
    Rle (ofQ (mul c c) (Qmul_den_pos hcd hcd)) (CnormSq (CdigammaArg s n)) := by
  -- σn := Re s + n, with floor ofQ c ≤ σn (reusing the real-line `digammaArg` floor) and σn ≥ 0
  have hfloor : Rle (ofQ c hcd) (Radd s.re (RofNat n)) := ofQ_le_digammaArg hcd hcs n
  have cnn : Rnonneg (ofQ c hcd) := Rnonneg_ofQ hcd (Int.le_of_lt hcn)
  have σnn : Rnonneg (Radd s.re (RofNat n)) := Rnonneg_of_ofQ_le hcn hcd hfloor
  -- c² ≤ c·σn ≤ σn·σn
  have ha : Rle (Rmul (ofQ c hcd) (ofQ c hcd)) (Rmul (ofQ c hcd) (Radd s.re (RofNat n))) :=
    Rmul_le_Rmul_left cnn hfloor
  have hb : Rle (Rmul (ofQ c hcd) (Radd s.re (RofNat n)))
      (Rmul (Radd s.re (RofNat n)) (Radd s.re (RofNat n))) :=
    Rle_trans (Rle_of_Req (Rmul_comm (ofQ c hcd) (Radd s.re (RofNat n))))
      (Rmul_le_Rmul_left σnn hfloor)
  -- c² ≈ ofQ(c·c), and σn² ≤ σn² + (Im s)² = |s+n|²
  have hchain : Rle (ofQ (mul c c) (Qmul_den_pos hcd hcd))
      (Rmul (Radd s.re (RofNat n)) (Radd s.re (RofNat n))) :=
    Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ hcd hcd))) (Rle_trans ha hb)
  exact Rle_trans hchain (Rle_self_Radd_right (Rnonneg_Rmul_self s.im))

/-- The uniform positivity witness index for `|s+n|²`, `3·(c·c).den` (the squared-floor analogue of
    `digammaArgK`). -/
def CdigK (c : Q) : Nat := digammaArgK (mul c c)

/-- **The positivity witness for `|s+n|²`**, derived uniformly from the real-part floor `c ≤ Re s`
    (so `Cinv (s+n)` is well-formed for every `n`). The complex analogue of `digammaArg_witness`. -/
theorem CdigammaArg_witness {s : Complex} {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) (n : Nat) :
    Qlt (Qbound (CdigK c)) ((CnormSq (CdigammaArg s n)).seq (CdigK c)) :=
  Rlt_Qbound_of_Rle_ofQ (show 0 < (mul c c).num from Int.mul_pos hcn hcn) (Qmul_den_pos hcd hcd)
    (ofQ_le_CnormSq_CdigammaArg hcn hcd hcs n)

/-- **The `n`-th complex digamma term** `1/(n+1) − 1/(s+n)`, a genuine constructive complex number
    for `Re s ≥ c > 0`. The first summand is the real rational `1/(n+1)` (embedded via `ofReal`); the
    second is the complex reciprocal `1/(s+n)` (`Cinv`, well-formed by `CdigammaArg_witness`). Built
    from `Cinv` only — no `Cpow`/`Clog`, hence no `1/16` barrier. -/
def CdigammaTerm (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) (n : Nat) : Complex :=
  Cadd (ofReal (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n)))
    (Cneg (Cinv (CdigammaArg s n) (CdigK c) (CdigammaArg_witness hcn hcd hcs n)))

/-- The real part of the `n`-th term: `1/(n+1) − (Re s + n)/|s+n|²`. -/
@[simp] theorem CdigammaTerm_re (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) (n : Nat) :
    (CdigammaTerm s hcn hcd hcs n).re =
      Radd (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n))
        (Rneg (Rmul (Radd s.re (RofNat n))
          (Rinv (CnormSq (CdigammaArg s n)) (CdigK c) (CdigammaArg_witness hcn hcd hcs n)))) := rfl

/-- The imaginary part of the `n`-th term: `Im s/|s+n|²` (up to `≈`), here in the raw
    `0 + −(−(Im s·I))` form. -/
@[simp] theorem CdigammaTerm_im (s : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcs : Rle (ofQ c hcd) s.re) (n : Nat) :
    (CdigammaTerm s hcn hcd hcs n).im =
      Radd zero (Rneg (Rneg (Rmul s.im
        (Rinv (CnormSq (CdigammaArg s n)) (CdigK c) (CdigammaArg_witness hcn hcd hcs n))))) := rfl

/-- **The complex digamma term is non-vacuous** (instantiation witness at `s = 1`, `c = 1`,
    `n = 0`). Confirms the floor/witness hypotheses are satisfiable. -/
noncomputable def cdigammaTermWitness : Complex :=
  CdigammaTerm Cone (c := ⟨1, 1⟩) (by decide) (by decide)
    (Rle_of_Req (Req_of_seq_Qeq (fun _ => Qeq_refl _))) 0

end UOR.Bridge.F1Square.Analysis
