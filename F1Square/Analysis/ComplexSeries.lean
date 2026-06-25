/-
F1 square — **complex finite sums and products** (`CsumN`, `CprodN`) and the bridge to the real
completeness, the algebraic substrate for the Track-1 Hadamard product `ξ(s) = ξ(0)·∏_ρ(1 − s/ρ)`
and its log-derivative series.

`CsumN F N = Σ_{k<N} F k` and `CprodN F N = ∏_{k<N} F k` are the partial sum / partial product, built
from `Cadd`/`Cmul`. Two facts make them usable:
  * the **congruences** `CsumN_congr`/`CprodN_congr` (pointwise `≈` ⟹ `≈` partials), needed to
    transport across `≈`-equal reindexings of the zero enumeration; and
  * the **component projection** `(CsumN F N).re = RsumN (re∘F) N` (and `.im`), which reduces the
    regularity / limit of a complex series to the real completeness (`ComplexLimit.lean`,
    `Complete.lean`) — a complex series converges iff both real-component partial-sum sequences do.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.ComplexLimit
import F1Square.Analysis.EtaVariation
import F1Square.Analysis.RSum

namespace UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (A) Complex finite sums `CsumN F N = Σ_{k<N} F k`.
-- ===========================================================================

/-- The **complex partial sum** `Σ_{k<N} F k`. -/
def CsumN (F : Nat → Complex) : Nat → Complex
  | 0 => Czero
  | (n + 1) => Cadd (CsumN F n) (F n)

/-- The real part of a complex partial sum is the real partial sum of the real parts (`= RsumN`). -/
theorem CsumN_re (F : Nat → Complex) : ∀ N, (CsumN F N).re = RsumN (fun n => (F n).re) N
  | 0 => rfl
  | (n + 1) => by
      show Radd (CsumN F n).re (F n).re = Radd (RsumN (fun n => (F n).re) n) (F n).re
      rw [CsumN_re F n]

/-- The imaginary part of a complex partial sum is the real partial sum of the imaginary parts. -/
theorem CsumN_im (F : Nat → Complex) : ∀ N, (CsumN F N).im = RsumN (fun n => (F n).im) N
  | 0 => rfl
  | (n + 1) => by
      show Radd (CsumN F n).im (F n).im = Radd (RsumN (fun n => (F n).im) n) (F n).im
      rw [CsumN_im F n]

/-- **Partial-sum congruence**: pointwise-`≈` summands give `≈` partial sums. -/
theorem CsumN_congr {F G : Nat → Complex} (h : ∀ n, Ceq (F n) (G n)) :
    ∀ N, Ceq (CsumN F N) (CsumN G N)
  | 0 => Ceq_refl _
  | (n + 1) => Cadd_congr (CsumN_congr h n) (h n)

/-- **Four-term addition interchange** `(a+b)+(c+d) ≈ (a+c)+(b+d)` — the complex middle-four swap,
    from `Cadd_assoc`/`Cadd_comm`. The inductive heart of `CsumN_add` (regroup the appended summands
    against the appended partial sums). -/
private theorem Cadd_add_add_comm (a b c d : Complex) :
    Ceq (Cadd (Cadd a b) (Cadd c d)) (Cadd (Cadd a c) (Cadd b d)) :=
  Ceq_trans (Cadd_assoc a b (Cadd c d))
    (Ceq_trans (Cadd_congr (Ceq_refl a) (Ceq_symm (Cadd_assoc b c d)))
      (Ceq_trans (Cadd_congr (Ceq_refl a) (Cadd_congr (Cadd_comm b c) (Ceq_refl d)))
        (Ceq_trans (Cadd_congr (Ceq_refl a) (Cadd_assoc c b d))
          (Ceq_symm (Cadd_assoc a c (Cadd b d))))))

/-- **★ Partial-sum additivity** `Σ_{n<N} (Fₙ + Gₙ) ≈ (Σ_{n<N} Fₙ) + (Σ_{n<N} Gₙ)` — linearity of
    the complex finite sum. By induction: the appended summand `Fₙ + Gₙ` and the inductive split
    regroup via the four-term interchange `Cadd_add_add_comm`. The forced algebraic substrate for
    splitting a witness/log-derivative series by its two component series (toward the Hadamard `bl`
    expansion); the complex lift of finite-sum linearity (no real `RsumN_add` is needed — the swap is
    done directly over `Cadd`). -/
theorem CsumN_add (F G : Nat → Complex) :
    ∀ N, Ceq (CsumN (fun n => Cadd (F n) (G n)) N) (Cadd (CsumN F N) (CsumN G N))
  | 0 => ⟨Req_symm (Radd_zero zero), Req_symm (Radd_zero zero)⟩
  | (N + 1) =>
      Ceq_trans (Cadd_congr (CsumN_add F G N) (Ceq_refl (Cadd (F N) (G N))))
        (Cadd_add_add_comm (CsumN F N) (CsumN G N) (F N) (G N))

-- ===========================================================================
-- (B) Complex finite products `CprodN F N = ∏_{k<N} F k`.
-- ===========================================================================

/-- The **complex partial product** `∏_{k<N} F k` (empty product `= 1`). -/
def CprodN (F : Nat → Complex) : Nat → Complex
  | 0 => Cone
  | (n + 1) => Cmul (CprodN F n) (F n)

/-- **Partial-product congruence**: pointwise-`≈` factors give `≈` partial products. -/
theorem CprodN_congr {F G : Nat → Complex} (h : ∀ n, Ceq (F n) (G n)) :
    ∀ N, Ceq (CprodN F N) (CprodN G N)
  | 0 => Ceq_refl _
  | (n + 1) => Cmul_congr (CprodN_congr h n) (h n)

/-- A partial product with a unit factor appended is `≈` the shorter product (`∏·1 ≈ ∏`). -/
theorem CprodN_succ_one {F : Nat → Complex} {N : Nat} (h : Ceq (F N) Cone) :
    Ceq (CprodN F (N + 1)) (CprodN F N) :=
  Ceq_trans (Cmul_congr (Ceq_refl (CprodN F N)) h) (Cmul_one (CprodN F N))

-- ===========================================================================
-- (C) The complex series / infinite product as the limit of partials (when regular).
-- ===========================================================================

/-- A complex series **converges** iff its partial sums form a regular complex sequence. -/
def CsumConv (F : Nat → Complex) : Prop := CReg (CsumN F)

/-- The **complex series** `Σ_k F k` — the limit of the partial sums, given convergence. -/
def Cseries (F : Nat → Complex) (h : CsumConv F) : Complex := Clim (CsumN F) h

/-- A complex infinite product **converges** iff its partial products form a regular sequence. -/
def CprodConv (F : Nat → Complex) : Prop := CReg (CprodN F)

/-- The **complex infinite product** `∏_k F k` — the limit of the partial products, given convergence. -/
def CprodInf (F : Nat → Complex) (h : CprodConv F) : Complex := Clim (CprodN F) h

/-- The partial-sum real-part sequence **is** the real partial-sum of the real parts (as functions). -/
theorem CsumN_re_fun (F : Nat → Complex) :
    (fun N => (CsumN F N).re) = RsumN (fun n => (F n).re) := funext (CsumN_re F)

/-- The partial-sum imaginary-part sequence **is** the real partial-sum of the imaginary parts. -/
theorem CsumN_im_fun (F : Nat → Complex) :
    (fun N => (CsumN F N).im) = RsumN (fun n => (F n).im) := funext (CsumN_im F)

/-- **Complex-series convergence reduces to two real-series convergences**: `Σ F` converges iff both
    the real-part series `Σ Re(F)` and imaginary-part series `Σ Im(F)` are regular (`RReg`). This is
    the bridge that lets any concrete complex series be shown convergent via the real completeness —
    the workhorse for the Hadamard/log-derivative limits. -/
theorem CsumConv_iff (F : Nat → Complex) :
    CsumConv F ↔ RReg (RsumN (fun n => (F n).re)) ∧ RReg (RsumN (fun n => (F n).im)) := by
  unfold CsumConv CReg
  rw [CsumN_re_fun F, CsumN_im_fun F]

end UOR.Bridge.F1Square.Analysis
