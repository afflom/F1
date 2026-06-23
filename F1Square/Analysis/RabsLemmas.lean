/-
F1 square — **`Rabs` triangle inequality and its finite-sum form**, foundational reals API.

`Rabs` (`RMax.lean`) carries only congruence and non-negativity; the triangle inequality
`|a+b| ≤ |a|+|b|` and its sum form `|Σ F| ≤ Σ|F|` were missing. They are the basic estimates every
absolute-value bound needs — in particular the dyadic Riemann-sum refinement convergence
(`RiemannSum.lean`, the certified-integration gateway) and the Weil-pairing bounds (Track 2).

Both lift the rational facts (`Qabs_add_le`) through the `Rabs x = ⟨n ↦ |xₙ|⟩` definition, with the
`Rle` regularity slack `⟨2,n+1⟩` absorbed by `Qle_self_add`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.RMax
import F1Square.Analysis.RSum

namespace UOR.Bridge.F1Square.Analysis

/-- **Triangle inequality** `|a + b| ≤ |a| + |b|`. -/
theorem Rabs_Radd (a b : Real) : Rle (Rabs (Radd a b)) (Radd (Rabs a) (Rabs b)) := by
  intro n
  show Qle (Qabs (add (a.seq (2 * n + 1)) (b.seq (2 * n + 1))))
    (add (add (Qabs (a.seq (2 * n + 1))) (Qabs (b.seq (2 * n + 1)))) (⟨2, n + 1⟩ : Q))
  exact Qle_trans
    (add_den_pos (Qabs_den_pos (a.den_pos (2 * n + 1))) (Qabs_den_pos (b.den_pos (2 * n + 1))))
    (Qabs_add_le (a.seq (2 * n + 1)) (b.seq (2 * n + 1)))
    (Qle_self_add (show (0 : Int) ≤ 2 by decide))

/-- `|0| = 0`. -/
theorem Rabs_zero : Req (Rabs zero) zero := Req_of_seq_Qeq (fun _ => Qeq_refl _)

/-- **The finite-sum triangle inequality** `|Σ_{i<N} F i| ≤ Σ_{i<N} |F i|`. -/
theorem RsumN_Rabs_le (F : Nat → Real) :
    ∀ N, Rle (Rabs (RsumN F N)) (RsumN (fun i => Rabs (F i)) N)
  | 0 => Rle_of_Req Rabs_zero
  | (N + 1) =>
      Rle_trans (Rabs_Radd (RsumN F N) (F N))
        (Radd_le_add (RsumN_Rabs_le F N) (Rle_refl (Rabs (F N))))

end UOR.Bridge.F1Square.Analysis
