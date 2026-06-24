/-
F1 square — Track 1, item 0/3 substrate: **`RrpowPos` bounds from the convexity modulus**.

`RrpowPos x k hk y = exp(y · log x)` (`Gamma.lean`). With the now-general convexity bound
`RlogPos x ≤ x − 1` (`RartanhBounds.lean`, transported from the wall-break `Rlog_le_sub_one_real`),
the real power is bounded above by `exp(y·(x−1))` for a non-negative exponent — `Rmul`-monotone in the
exponent times `RexpReal`-monotone. This is the integrand bound the general `t^{σ−1}` Mellin step needs.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.Gamma
import F1Square.Analysis.RartanhBounds
import F1Square.Analysis.ThetaLipschitz

namespace UOR.Bridge.F1Square.Analysis

/-- **Directed exp-Lipschitz**: `exp a − exp b ≤ 4·max(a−b,0)·exp a`. Via the exact factorization
    `exp a − exp b = (1 − exp(−(a−b)))·exp a` (`RexpReal_add`, since `exp(−(a−b))·exp a = exp b`) and the
    order-free variation `1 − exp(−z) ≤ 4·max(z,0)` (`RexpReal_one_sub_neg_le_maxZero`). The exp half of
    the `RrpowPos` Lipschitz: with `a, b` bounded above (so `exp a ≤ M`) this is genuine Lipschitz. -/
theorem RexpReal_sub_le (a b : Real) :
    Rle (Rsub (RexpReal a) (RexpReal b))
      (Rmul (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (RmaxZero (Rsub a b))) (RexpReal a)) := by
  have hEa : Req (Rmul (RexpReal (Rneg (Rsub a b))) (RexpReal a)) (RexpReal b) := by
    refine Req_trans (Req_symm (RexpReal_add (Rneg (Rsub a b)) a)) (RexpReal_congr ?_)
    exact Req_trans (Radd_congr (Rneg_Rsub a b) (Req_refl a))
      (Req_trans (Radd_assoc b (Rneg a) a)
        (Req_trans (Radd_congr (Req_refl b) (Req_trans (Radd_comm (Rneg a) a) (Radd_neg a)))
          (Radd_zero b)))
  have hid : Req (Rmul (Rsub one (RexpReal (Rneg (Rsub a b)))) (RexpReal a))
      (Rsub (RexpReal a) (RexpReal b)) :=
    Req_trans (Rmul_sub_distrib_right one (RexpReal (Rneg (Rsub a b))) (RexpReal a))
      (Rsub_congr (Rone_mul (RexpReal a)) hEa)
  exact Rle_trans (Rle_of_Req (Req_symm hid))
    (Rmul_le_Rmul_right (RexpReal_nonneg a) (RexpReal_one_sub_neg_le_maxZero (Rsub a b)))

/-- **`x^y ≤ exp(y·(x−1))`** for a non-negative exponent `y` and a base `x` presented in `[1,B]` at a
    small radius. Directly from `RlogPos_le_sub_one` (`log x ≤ x−1`): `y·log x ≤ y·(x−1)` (`Rmul`-monotone,
    `y ≥ 0`), then `exp`-monotone. The integrand upper bound for the general real Mellin transform. -/
theorem RrpowPos_le_exp_sub_one (x : Real) (k : Nat) (hk : Qlt (Qbound k) (x.seq k)) (y : Real)
    (hy : Rnonneg y)
    (B : Q) (hBd : 0 < B.den) (hBge : Qle (⟨1, 1⟩ : Q) B)
    (hxposB : ∀ n, 0 < (x.seq n).num) (hxhiB : ∀ n, Qle (x.seq n) B)
    (hxloB : ∀ n, Qle (⟨1, 1⟩ : Q) (mul (x.seq n) B))
    (hρB2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩
              ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩))) :
    Rle (RrpowPos x k hk y) (RexpReal (Rmul y (Rsub x one))) :=
  RexpReal_le_of_Rle (Rmul_le_Rmul_left hy
    (RlogPos_le_sub_one x k hk B hBd hBge hxposB hxhiB hxloB hρB2))

end UOR.Bridge.F1Square.Analysis
