/-
F1 square — certified integration, **convergence layer**: the per-pair Lipschitz estimate for the
dyadic Riemann-sum refinement.

For a Lipschitz integrand `f` (constant `L`), consecutive dyadic partition points `2j/(2M)` and
`(2j+1)/(2M)` are spaced `1/(2M)`, so `|f((2j+1)/(2M)) − f(2j/(2M))| ≤ L/(2M)`. This is the per-term
bound that, summed over the `M` even/odd pairs (`RsumN_split2`/`RsumN_Rabs_le`) and scaled by the
width `1/(2M)`, yields the geometric refinement `|R_M − R_{2M}| ≤ L/(4M)` → `RReg` → the `Rlim`
integral (the next step).

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.RiemannSum
import F1Square.Analysis.RabsLemmas

namespace UOR.Bridge.F1Square.Analysis

/-- **The consecutive dyadic points are spaced `1/(2M)`**: `(2j+1)/(2M) − 2j/(2M) = 1/(2M)`. -/
theorem dyadic_pair_spacing (j M : Nat) (hM : 0 < M) :
    Req (Rsub (ofQ (⟨2 * j + 1, 2 * M⟩ : Q) (Nat.mul_pos (by decide) hM))
              (ofQ (⟨2 * j, 2 * M⟩ : Q) (Nat.mul_pos (by decide) hM)))
        (ofQ (⟨1, 2 * M⟩ : Q) (Nat.mul_pos (by decide) hM)) :=
  Req_of_seq_Qeq (fun _ => by
    show Qeq (add (⟨2 * j + 1, 2 * M⟩ : Q) (neg (⟨2 * j, 2 * M⟩ : Q))) (⟨1, 2 * M⟩ : Q)
    simp only [Qeq, add, neg]; push_cast; ring_uor)

/-- **The per-pair Lipschitz bound** `|f((2j+1)/(2M)) − f(2j/(2M))| ≤ L/(2M)`. From the Lipschitz
    hypothesis and the `1/(2M)` spacing (`dyadic_pair_spacing`, `Rabs_ofQ_nonneg`). -/
theorem dyadic_pair_lip {f : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (j M : Nat) (hM : 0 < M) :
    Rle (Rabs (Rsub (f (ofQ (⟨2 * j + 1, 2 * M⟩ : Q) (Nat.mul_pos (by decide) hM)))
                    (f (ofQ (⟨2 * j, 2 * M⟩ : Q) (Nat.mul_pos (by decide) hM)))))
        (ofQ (mul L (⟨1, 2 * M⟩ : Q)) (Qmul_den_pos hLd (Nat.mul_pos (by decide) hM))) := by
  refine Rle_trans (hlip _ _) ?_
  -- L·|p₂−p₁| ≤ L·(1/(2M)) = L/(2M)
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ hLd hLn) ?_)
    (Rle_of_Req (Rmul_ofQ_ofQ hLd (Nat.mul_pos (by decide) hM)))
  -- |p₂ − p₁| ≤ 1/(2M)
  exact Rle_of_Req
    (Req_trans (Rabs_congr (dyadic_pair_spacing j M hM))
      (Rabs_ofQ_nonneg (Nat.mul_pos (by decide) hM) (show (0 : Int) ≤ 1 by decide)))

end UOR.Bridge.F1Square.Analysis
