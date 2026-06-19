/-
F1 square — v0.22.0 Track 1, brick (complex lift): toward **complex argument additivity**
`arg(zw) = arg z + arg w` (`Carg`), the imaginary half of `Clog` additivity.

Built on the real-argument arctan addition `RarctanR_add_real_via` (`ArctanTan.lean`) and the real
arctan map `vvalReal` (`ArtanhAdd.lean`). The route: the complex-division **ratio identity**
`Im(zw)/Re(zw) ≈ vvalReal(Im z/Re z, Im w/Re w)` (the tangent-addition identity at the value level),
then `RarctanR_congr` + the real addition law. This file collects the cancellation infrastructure and
the `vvalReal` real defining relation that the ratio identity needs.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.ArctanTan
import F1Square.Analysis.RArctanCongr

namespace UOR.Bridge.F1Square.Analysis

/-- **Right cancellation for `Rmul`**: if `a·c ≈ b·c` and `c` is apart from `0` (a positive lower
    bound at index `k`), then `a ≈ b`. Via `(a−b)·c ≈ a·c − b·c ≈ 0` and `Rmul_eq_zero_cancel`. -/
theorem Rmul_right_cancel {a b c : Real} {k : Nat} (hk : Qlt (Qbound k) (c.seq k))
    (h : Req (Rmul a c) (Rmul b c)) : Req a b := by
  have hz : Req (Rmul (Rsub a b) c) zero :=
    Req_trans (Rmul_sub_distrib_right a b c)
      (Req_trans (Rsub_congr h (Req_refl (Rmul b c))) (Radd_neg (Rmul b c)))
  exact Req_of_Rsub_zero_loc (Rmul_eq_zero_cancel hk hz)

/-- **`(a/b)·b ≈ a`** (the division defining relation), for `b` apart from `0`: `Rdiv a b = a·(1/b)`,
    reassociate and cancel `b·(1/b) ≈ 1` (`Rmul_Rinv_self`). -/
theorem Rdiv_mul_cancel {a b : Real} {k : Nat} (hk : Qlt (Qbound k) (b.seq k)) :
    Req (Rmul (Rdiv a b k hk) b) a := by
  show Req (Rmul (Rmul a (Rinv b k hk)) b) a
  refine Req_trans (Rmul_assoc a (Rinv b k hk) b) ?_
  refine Req_trans (Rmul_congr (Req_refl a)
    (Req_trans (Rmul_comm (Rinv b k hk) b) (Rmul_Rinv_self hk))) ?_
  exact Rmul_one a

end UOR.Bridge.F1Square.Analysis
