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

/-- **`RrpowPos` difference reduced to the log difference**: `xᵉ − yᵉ ≤ 4·max(e·(log x − log y),0)·xᵉ`.
    Apply the directed exp-Lipschitz `RexpReal_sub_le` to `a = e·log x`, `b = e·log y` (`RrpowPos = exp(e·log·)`
    by definition), then `Rmul_sub_distrib` exposes `e·(log x − log y)`. The structural reduction of
    `RrpowPos` Lipschitz to log-Lipschitz: the remaining content is the `log x − log y` bound. -/
theorem RrpowPos_sub_le (x : Real) (kx : Nat) (hx : Qlt (Qbound kx) (x.seq kx))
    (y : Real) (ky : Nat) (hy : Qlt (Qbound ky) (y.seq ky)) (e : Real) :
    Rle (Rsub (RrpowPos x kx hx e) (RrpowPos y ky hy e))
      (Rmul (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide))
          (RmaxZero (Rmul e (Rsub (RlogPos x kx hx) (RlogPos y ky hy)))))
        (RrpowPos x kx hx e)) := by
  refine Rle_trans (RexpReal_sub_le (Rmul e (RlogPos x kx hx)) (Rmul e (RlogPos y ky hy))) ?_
  refine Rmul_le_Rmul_right (RexpReal_nonneg _)
    (Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) ?_)
  exact Rle_of_Req (RmaxZero_congr (Req_symm (Rmul_sub_distrib e (RlogPos x kx hx) (RlogPos y ky hy))))

end UOR.Bridge.F1Square.Analysis
