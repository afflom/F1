/-
F1 square — **square-root Lipschitz bound and the real-radicand √**.

The constructive √ of a *rational* (`Rsqrt`) is Lipschitz-½ on `[1, ∞)`:
`|√x − √y| ≤ ½|x − y|` for `x, y ≥ 1` (`Rsqrt_lipschitz`). The engine is the difference-of-squares
factoring `(√x − √y)(√x + √y) = x − y` (from `(√·)² = ·`) divided through by `√x + √y ≥ 2` — but the
lower bound `2 ≤ |√x + √y|` is read off `√x + √y ≥ 2` via `x ≤ |x|` (no `|·|`-of-nonnegative needed),
keeping the argument multiplicative throughout (`Rabs_Rmul`).

This is the regularity modulus (`½ · 2/(j+1) = 1/(j+1)`) for the real-radicand square root: the limit
of the rational √'s of the (clamped-to-`≥1`) rational approximants of `a ≥ 1` — the `√t` factor of the
theta modular transform at a real argument.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.SqrtRealCmp
import F1Square.Analysis.RabsLemmas

namespace UOR.Bridge.F1Square.Analysis

/-- `(ofQ a) − (ofQ b) ≈ ofQ (a − b)` (both are pointwise constant `a − b`). -/
private theorem Rsub_ofQ {a b : Q} (ha : 0 < a.den) (hb : 0 < b.den) :
    Req (Rsub (ofQ a ha) (ofQ b hb)) (ofQ (Qsub a b) (Qsub_den_pos ha hb)) :=
  Req_of_seq_Qeq (fun _ => Qeq_refl _)

/-- `½ · 2 · x ≈ x`. -/
private theorem Rhalf_two_mul (x : Real) :
    Req (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) x)) x := by
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
  refine Req_trans (Rmul_congr (Rmul_ofQ_ofQ (by decide) (by decide)) (Req_refl _)) ?_
  refine Req_trans (Rmul_congr
    (ofQ_congr (by decide) (by decide) (by decide : Qeq (mul (⟨1, 2⟩ : Q) (⟨2, 1⟩ : Q)) (⟨1, 1⟩ : Q)))
    (Req_refl _)) ?_
  exact Req_trans (Rmul_comm _ x) (Rmul_one x)

/-- **`Rsqrt` is Lipschitz-½ on `[1, ∞)`**: `|√x − √y| ≤ ½|x − y|` for rationals `x, y ≥ 1`. -/
theorem Rsqrt_lipschitz {x y : Q} (hxd : 0 < x.den) (hyd : 0 < y.den)
    (hx0 : Qle (⟨0, 1⟩ : Q) x) (hy0 : Qle (⟨0, 1⟩ : Q) y)
    (hx1 : Qle (⟨1, 1⟩ : Q) x) (hy1 : Qle (⟨1, 1⟩ : Q) y) :
    Rle (Rabs (Rsub (Rsqrt x hxd hx0) (Rsqrt y hyd hy0)))
        (ofQ (mul (⟨1, 2⟩ : Q) (Qabs (Qsub x y)))
          (Qmul_den_pos (by decide) (Qabs_den_pos (Qsub_den_pos hxd hyd)))) := by
  let s := Rsqrt x hxd hx0
  let t := Rsqrt y hyd hy0
  -- `2 ≤ |s + t|`, from `s, t ≥ 1` and `u ≤ |u|`.
  have hreq2 : Req (ofQ (⟨2, 1⟩ : Q) (by decide)) (Radd one one) :=
    Req_trans (ofQ_congr (by decide) (add_den_pos (by decide) (by decide))
        (by decide : Qeq (⟨2, 1⟩ : Q) (add (⟨1, 1⟩ : Q) (⟨1, 1⟩ : Q))))
      (Req_symm (Radd_ofQ_ofQ (by decide) (by decide)))
  have h2st : Rle (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rabs (Radd s t)) :=
    Rle_trans (Rle_trans (Rle_of_Req hreq2)
        (Radd_le_add (Rsqrt_ge_one hxd hx0 hx1) (Rsqrt_ge_one hyd hy0 hy1)))
      (Rle_Rabs_self (Radd s t))
  -- `(s − t)(s + t) ≈ ofQ (x − y)`, so `|s − t|·|s + t| ≈ ofQ |x − y|`.
  have hprod : Req (Rmul (Rsub s t) (Radd s t)) (ofQ (Qsub x y) (Qsub_den_pos hxd hyd)) :=
    Req_trans (Rmul_sub_add_self s t)
      (Req_trans (Rsub_congr (Rsqrt_sq x hxd hx0) (Rsqrt_sq y hyd hy0))
        (Rsub_ofQ hxd hyd))
  have habs : Req (Rmul (Rabs (Rsub s t)) (Rabs (Radd s t)))
      (ofQ (Qabs (Qsub x y)) (Qabs_den_pos (Qsub_den_pos hxd hyd))) :=
    Req_trans (Req_symm (Rabs_Rmul (Rsub s t) (Radd s t)))
      (Req_trans (Rabs_congr hprod) (Rabs_ofQ (Qsub_den_pos hxd hyd)))
  -- `2·|s − t| ≤ |s + t|·|s − t| = |s − t|·|s + t| ≈ ofQ |x − y|`.
  have hchain : Rle (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rabs (Rsub s t)))
      (ofQ (Qabs (Qsub x y)) (Qabs_den_pos (Qsub_den_pos hxd hyd))) :=
    Rle_trans (Rmul_le_Rmul_right (Rnonneg_Rabs (Rsub s t)) h2st)
      (Rle_of_Req (Req_trans (Rmul_comm (Rabs (Radd s t)) (Rabs (Rsub s t))) habs))
  -- multiply by `½ ≥ 0`: `|s − t| ≈ ½·2·|s − t| ≤ ½·ofQ|x − y| = ofQ (½|x − y|)`.
  refine Rle_trans (Rle_of_Req (Req_symm (Rhalf_two_mul (Rabs (Rsub s t))))) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) hchain) ?_
  exact Rle_of_Req (Rmul_ofQ_ofQ (by decide) (Qabs_den_pos (Qsub_den_pos hxd hyd)))

-- ===========================================================================
-- The real-radicand square root `√a` for `a ≥ 1`, as the limit of the rational √'s of the shifted
-- approximants `cₙ = a_{4n+3} + 2/(4n+4) ≥ 1` (the shift makes `cₙ ≥ 1` automatic, the reindex
-- tightens the Lipschitz modulus `½·|cⱼ−cₖ|` to `1/(2(j+1))+1/(2(k+1)) ≤ 1/(j+1)+1/(k+1)`).
-- ===========================================================================

/-- `Qeq` commutes with `Qabs` (the rational reverse of `Rabs_congr`). -/
private theorem Qabs_congr_q {a b : Q} (h : Qeq a b) : Qeq (Qabs a) (Qabs b) := by
  have key : a.num.natAbs * b.den = b.num.natAbs * a.den := by
    unfold Qeq at h
    have hh := congrArg Int.natAbs h
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_ofNat, Int.natAbs_ofNat] at hh
    exact hh
  show ((a.num.natAbs : Int)) * (b.den : Int) = ((b.num.natAbs : Int)) * (a.den : Int)
  exact_mod_cast key

/-- The shifted rational approximant `cₙ = a_{4n+3} + 2/(4n+4)` of `a` — always `≥ 1` when `a ≥ 1`. -/
def rsqrtRealSeq (a : Real) (n : Nat) : Q := add (a.seq (4 * n + 3)) (⟨2, 4 * n + 4⟩ : Q)

theorem rsqrtRealSeq_den_pos (a : Real) (n : Nat) : 0 < (rsqrtRealSeq a n).den :=
  add_den_pos (a.den_pos _) (by show 0 < 4 * n + 4; omega)

/-- `cₙ ≥ 1` — exactly the `a ≥ 1` regularity statement at index `4n+3` (the shift is `Qbound`). -/
theorem rsqrtRealSeq_ge_one (a : Real) (ha : Rle one a) (n : Nat) :
    Qle (⟨1, 1⟩ : Q) (rsqrtRealSeq a n) := ha (4 * n + 3)

theorem rsqrtRealSeq_ge_zero (a : Real) (ha : Rle one a) (n : Nat) :
    Qle (⟨0, 1⟩ : Q) (rsqrtRealSeq a n) :=
  Qle_trans (by decide) (by decide : Qle (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q)) (rsqrtRealSeq_ge_one a ha n)

/-- The sequence of rational square roots `√cₙ`. -/
def rsqrtRealX (a : Real) (ha : Rle one a) (n : Nat) : Real :=
  Rsqrt (rsqrtRealSeq a n) (rsqrtRealSeq_den_pos a n) (rsqrtRealSeq_ge_zero a ha n)

set_option maxHeartbeats 800000 in
/-- **The approximant gap** `|cⱼ − cₖ| ≤ 4/(4j+4) + 4/(4k+4)` — triangle split into the `a`-gap (from
    `a`'s regularity) and the `2/(4·+4)`-gap (both bounded by `2/(4·+4)`). -/
theorem rsqrtRealSeq_diff_le (a : Real) (j k : Nat) :
    Qle (Qabs (Qsub (rsqrtRealSeq a j) (rsqrtRealSeq a k)))
        (add (add (⟨1, 4 * j + 4⟩ : Q) (⟨1, 4 * k + 4⟩ : Q))
             (add (⟨2, 4 * j + 4⟩ : Q) (⟨2, 4 * k + 4⟩ : Q))) := by
  have hjd : 0 < (⟨2, 4 * j + 4⟩ : Q).den := by show 0 < 4 * j + 4; omega
  have hkd : 0 < (⟨2, 4 * k + 4⟩ : Q).den := by show 0 < 4 * k + 4; omega
  have heq : Qeq (Qsub (rsqrtRealSeq a j) (rsqrtRealSeq a k))
      (add (Qsub (a.seq (4 * j + 3)) (a.seq (4 * k + 3)))
           (Qsub (⟨2, 4 * j + 4⟩ : Q) (⟨2, 4 * k + 4⟩ : Q))) := by
    simp only [rsqrtRealSeq, Qeq, Qsub, add, neg]; push_cast; ring_uor
  have h1 : Qeq (Qabs (⟨2, 4 * j + 4⟩ : Q)) (⟨2, 4 * j + 4⟩ : Q) :=
    Qabs_of_nonneg (by show (0 : Int) ≤ 2; decide)
  have h2 : Qeq (Qabs (neg (⟨2, 4 * k + 4⟩ : Q))) (⟨2, 4 * k + 4⟩ : Q) := by
    rw [Qabs_neg]; exact Qabs_of_nonneg (by show (0 : Int) ≤ 2; decide)
  have hbd : Qle (Qabs (Qsub (⟨2, 4 * j + 4⟩ : Q) (⟨2, 4 * k + 4⟩ : Q)))
      (add (⟨2, 4 * j + 4⟩ : Q) (⟨2, 4 * k + 4⟩ : Q)) :=
    Qle_trans (add_den_pos (Qabs_den_pos hjd) (Qabs_den_pos hkd))
      (Qabs_add_le (⟨2, 4 * j + 4⟩ : Q) (neg (⟨2, 4 * k + 4⟩ : Q)))
      (Qadd_le_add (Qeq_le h1) (Qeq_le h2))
  have hareg : Qle (Qabs (Qsub (a.seq (4 * j + 3)) (a.seq (4 * k + 3))))
      (add (⟨1, 4 * j + 4⟩ : Q) (⟨1, 4 * k + 4⟩ : Q)) := by
    have h := a.reg (4 * j + 3) (4 * k + 3); unfold Qbound at h; exact h
  have e1 : Qle (Qabs (Qsub (rsqrtRealSeq a j) (rsqrtRealSeq a k)))
      (Qabs (add (Qsub (a.seq (4 * j + 3)) (a.seq (4 * k + 3)))
           (Qsub (⟨2, 4 * j + 4⟩ : Q) (⟨2, 4 * k + 4⟩ : Q)))) :=
    Qeq_le (Qabs_congr_q heq)
  have e2 : Qle (Qabs (add (Qsub (a.seq (4 * j + 3)) (a.seq (4 * k + 3)))
        (Qsub (⟨2, 4 * j + 4⟩ : Q) (⟨2, 4 * k + 4⟩ : Q))))
      (add (Qabs (Qsub (a.seq (4 * j + 3)) (a.seq (4 * k + 3))))
        (Qabs (Qsub (⟨2, 4 * j + 4⟩ : Q) (⟨2, 4 * k + 4⟩ : Q)))) :=
    Qabs_add_le _ _
  have e3 : Qle (add (Qabs (Qsub (a.seq (4 * j + 3)) (a.seq (4 * k + 3))))
        (Qabs (Qsub (⟨2, 4 * j + 4⟩ : Q) (⟨2, 4 * k + 4⟩ : Q))))
      (add (add (⟨1, 4 * j + 4⟩ : Q) (⟨1, 4 * k + 4⟩ : Q))
           (add (⟨2, 4 * j + 4⟩ : Q) (⟨2, 4 * k + 4⟩ : Q))) :=
    Qadd_le_add hareg hbd
  exact Qle_trans (Qabs_den_pos (add_den_pos (Qsub_den_pos (a.den_pos _) (a.den_pos _))
      (Qsub_den_pos hjd hkd))) e1
    (Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (a.den_pos _) (a.den_pos _)))
        (Qabs_den_pos (Qsub_den_pos hjd hkd))) e2 e3)

set_option maxHeartbeats 800000 in
/-- The reindexed √cₙ partial sequence is regular. -/
theorem rsqrtRealX_RReg (a : Real) (ha : Rle one a) : RReg (rsqrtRealX a ha) := by
  refine RReg_of_real_bound (rsqrtRealX a ha)
    (fun j k => add (⟨3, 8 * (j + 1)⟩ : Q) (⟨3, 8 * (k + 1)⟩ : Q))
    (fun j k => add_den_pos (by show 0 < 8 * (j + 1); omega) (by show 0 < 8 * (k + 1); omega))
    (fun j k => Qadd_le_add (by simp only [Qle]; push_cast; omega)
      (by simp only [Qle]; push_cast; omega)) ?_
  intro j k
  refine Rle_trans (Rle_of_Rabs_le (Rsqrt_lipschitz (rsqrtRealSeq_den_pos a j)
      (rsqrtRealSeq_den_pos a k) (rsqrtRealSeq_ge_zero a ha j) (rsqrtRealSeq_ge_zero a ha k)
      (rsqrtRealSeq_ge_one a ha j) (rsqrtRealSeq_ge_one a ha k))) ?_
  refine Rle_ofQ_ofQ _ _ ?_
  have hstep : Qle (mul (⟨1, 2⟩ : Q) (Qabs (Qsub (rsqrtRealSeq a j) (rsqrtRealSeq a k))))
      (mul (⟨1, 2⟩ : Q) (add (add (⟨1, 4 * j + 4⟩ : Q) (⟨1, 4 * k + 4⟩ : Q))
        (add (⟨2, 4 * j + 4⟩ : Q) (⟨2, 4 * k + 4⟩ : Q)))) :=
    Qmul_le_mul_left (by show (0 : Int) ≤ 1; decide) (rsqrtRealSeq_diff_le a j k)
  refine Qle_trans (Qmul_den_pos (by decide) (add_den_pos
      (add_den_pos (by show 0 < 4 * j + 4; omega) (by show 0 < 4 * k + 4; omega))
      (add_den_pos (by show 0 < 4 * j + 4; omega) (by show 0 < 4 * k + 4; omega)))) hstep (Qeq_le ?_)
  simp only [Qeq, mul, add]; push_cast; ring_uor

/-- **The constructive square root of a real `a ≥ 1`** — the Bishop limit of the rational √'s of the
    shifted approximants. The defining identity `(√a)² = a` is the remaining piece (needs limit
    arithmetic for the squaring step). -/
def RsqrtReal (a : Real) (ha : Rle one a) : Real := Rlim (rsqrtRealX a ha) (rsqrtRealX_RReg a ha)

/-- **`√a ≥ 0`.** -/
theorem RsqrtReal_nonneg (a : Real) (ha : Rle one a) : Rnonneg (RsqrtReal a ha) :=
  Rnonneg_Rlim_seq _ (fun _n => Rsqrt_nonneg _ _ _)

end UOR.Bridge.F1Square.Analysis
