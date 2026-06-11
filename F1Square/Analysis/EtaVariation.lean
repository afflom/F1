/-
F1 square — the **`n⁻ˢ` multiplicative recurrence** `(n+1)⁻ˢ = n⁻ˢ · e^{−s·δ_n}` (`δ_n = log(n+1) − log n`),
the engine of the η-series **variation bound** `Σ |n⁻ˢ − (n+1)⁻ˢ| < ∞` (`Re s > 0`) — the integration-free
route to `ζ` on the critical strip. The recurrence is the direct consequence of the complex exponential
law `Cexp_add`: `n⁻ˢ = e^{−s·log n}` (`cpowNeg`), and `log(n+1) = log n + δ_n`, so
`e^{−s·log(n+1)} = e^{−s·log n}·e^{−s·δ_n}`.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.EulerMaclaurin
import F1Square.Analysis.ComplexExpAdd
import F1Square.Analysis.ComplexZeta
import F1Square.Analysis.GammaOne
import F1Square.Analysis.EtaFunction

namespace UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- Complex-algebra helpers (componentwise `Ceq = ⟨Req, Req⟩` lifts of the real laws).
-- ===========================================================================

/-- `Rsub (Rneg x) (Rneg y) ≈ Rneg (Rsub x y)` (both `≈ y − x`). -/
theorem Rsub_RnegRneg (x y : Real) : Req (Rsub (Rneg x) (Rneg y)) (Rneg (Rsub x y)) :=
  Req_symm (Rneg_Radd x (Rneg y))

/-- ℂ addition respects `≈`. -/
theorem Cadd_congr {z z' w w' : Complex} (hz : Ceq z z') (hw : Ceq w w') :
    Ceq (Cadd z w) (Cadd z' w') := ⟨Radd_congr hz.1 hw.1, Radd_congr hz.2 hw.2⟩

/-- ℂ negation respects `≈`. -/
theorem Cneg_congr {z z' : Complex} (h : Ceq z z') : Ceq (Cneg z) (Cneg z') :=
  ⟨Rneg_congr h.1, Rneg_congr h.2⟩

/-- ℂ multiplication respects `≈`. -/
theorem Cmul_congr {z z' w w' : Complex} (hz : Ceq z z') (hw : Ceq w w') :
    Ceq (Cmul z w) (Cmul z' w') :=
  ⟨Rsub_congr (Rmul_congr hz.1 hw.1) (Rmul_congr hz.2 hw.2),
   Radd_congr (Rmul_congr hz.1 hw.2) (Rmul_congr hz.2 hw.1)⟩

/-- ℂ subtraction respects `≈`. -/
theorem Csub_congr {z z' w w' : Complex} (hz : Ceq z z') (hw : Ceq w w') :
    Ceq (Csub z w) (Csub z' w') := Cadd_congr hz (Cneg_congr hw)

/-- `z·(−w) ≈ −(z·w)` on ℂ. -/
theorem Cmul_neg_right (z w : Complex) : Ceq (Cmul z (Cneg w)) (Cneg (Cmul z w)) :=
  ⟨Req_trans (Rsub_congr (Rmul_neg_right z.re w.re) (Rmul_neg_right z.im w.im))
      (Rsub_RnegRneg (Rmul z.re w.re) (Rmul z.im w.im)),
   Req_trans (Radd_congr (Rmul_neg_right z.re w.im) (Rmul_neg_right z.im w.re))
      (Req_symm (Rneg_Radd (Rmul z.re w.im) (Rmul z.im w.re)))⟩

/-- **The consecutive-log gap** `δ_n = log(n+1) − log n` (for `n ≥ 2`), as a constructive real. -/
def deltaLogNat (n : Nat) (hn : 2 ≤ n) : Real :=
  Rsub (RlogNat (n + 1) (by omega)) (RlogNat n hn)

/-- **The `n⁻ˢ` multiplicative recurrence** `(n+1)⁻ˢ ≈ n⁻ˢ · e^{−s·δ_n}` (for `n ≥ 2`). Both sides are
    `Cexp` of an argument; `log(n+1) = log n + δ_n` (`Radd_Rsub_self`) lifts through `Rmul_distrib` to the
    complex argument additivity, and `Cexp_add`/`Cexp_congr` close it. -/
theorem cpowNeg_succ (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Ceq (cpowNeg s (n + 1))
      (Cmul (cpowNeg s n)
        (Cexp ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩)) := by
  have h1 : 2 ≤ n + 1 := by omega
  unfold cpowNeg
  rw [dif_pos h1, dif_pos hn]
  -- both `ncpow` are `Cexp` of the argument `−s·log`; reduce to `Cexp_add` via argument additivity
  refine Ceq_trans (Cexp_congr (z := ⟨Rmul (Rneg s.re) (RlogNat (n + 1) h1), Rmul (Rneg s.im) (RlogNat (n + 1) h1)⟩)
      (w := Cadd ⟨Rmul (Rneg s.re) (RlogNat n hn), Rmul (Rneg s.im) (RlogNat n hn)⟩
        ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩) ?_)
    (Cexp_add ⟨Rmul (Rneg s.re) (RlogNat n hn), Rmul (Rneg s.im) (RlogNat n hn)⟩
      ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩)
  -- argument additivity: `−s·log(n+1) ≈ −s·log n + (−s)·δ_n`, componentwise
  have hlog : Req (RlogNat (n + 1) h1) (Radd (RlogNat n hn) (deltaLogNat n hn)) :=
    Req_symm (Radd_Rsub_self (RlogNat n hn) (RlogNat (n + 1) h1))
  exact ⟨Req_trans (Rmul_congr (Req_refl _) hlog)
      (Rmul_distrib (Rneg s.re) (RlogNat n hn) (deltaLogNat n hn)),
    Req_trans (Rmul_congr (Req_refl _) hlog)
      (Rmul_distrib (Rneg s.im) (RlogNat n hn) (deltaLogNat n hn))⟩

/-- **The `n⁻ˢ` consecutive difference** `n⁻ˢ − (n+1)⁻ˢ ≈ n⁻ˢ·(1 − e^{−s·δ_n})` (for `n ≥ 2`) — the form
    on which the variation modulus `|n⁻ˢ − (n+1)⁻ˢ| ≤ |n⁻ˢ|·|1 − e^{−s·δ_n}|` is read off. Factor `n⁻ˢ`
    out of `n⁻ˢ − n⁻ˢ·e^{−s·δ_n}` (`cpowNeg_succ`) via `Cmul_distrib`/`Cmul_one`/`Cmul_neg_right`. -/
theorem cpowNeg_diff (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Ceq (Csub (cpowNeg s n) (cpowNeg s (n + 1)))
      (Cmul (cpowNeg s n)
        (Csub Cone (Cexp ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩))) :=
  Ceq_trans (Cadd_congr (Ceq_refl _) (Cneg_congr (cpowNeg_succ s n hn)))
    (Ceq_trans (Cadd_congr (Ceq_symm (Cmul_one (cpowNeg s n)))
        (Ceq_symm (Cmul_neg_right (cpowNeg s n)
          (Cexp ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩))))
      (Ceq_symm (Cmul_distrib (cpowNeg s n) Cone
        (Cneg (Cexp ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩)))))

/-- **`e^{−d} ≤ 1` for `d ≥ 0`** (the exponential of a non-positive argument is at most `1`). From
    `e^{−d}·e^d = 1` and `e^d ≥ 1`: `e^{−d} = e^{−d}·1 ≤ e^{−d}·e^d = 1`. -/
theorem RexpReal_neg_le_one (d : Real) (hd : Rnonneg d) : Rle (RexpReal (Rneg d)) one := by
  have hprod : Req (Rmul (RexpReal (Rneg d)) (RexpReal d)) one :=
    Req_trans (Req_symm (RexpReal_add (Rneg d) d))
      (Req_trans (RexpReal_congr (Req_trans (Radd_comm (Rneg d) d) (Radd_neg d))) RexpReal_zero)
  exact Rle_trans (Rle_of_Req (Req_symm (Rmul_one (RexpReal (Rneg d)))))
    (Rle_trans (Rmul_le_Rmul_left (RexpReal_nonneg (Rneg d)) (RexpReal_ge_one hd))
      (Rle_of_Req hprod))

-- ===========================================================================
-- The `n⁻ˢ` per-term component bounds `−n⁻ᴿᵉˢ ≤ Re/Im(n⁻ˢ) ≤ n⁻ᴿᵉˢ` (no real-abs; two-sided `Rle`,
-- mirroring `ComplexZeta`'s `czetaTerm_re_le`/`ge`). `cpowNeg s n = e^{−s·log n}` for `n ≥ 2`. -/
-- ===========================================================================

/-- `Re(n⁻ˢ) ≤ e^{−Re s·log n}` (`= n⁻ᴿᵉˢ`). -/
theorem cpowNeg_re_le (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Rle ((cpowNeg s n).re) (RexpReal (Rmul (Rneg s.re) (RlogNat n hn))) := by
  unfold cpowNeg; rw [dif_pos hn]; exact Cexp_re_le _

/-- `−e^{−Re s·log n} ≤ Re(n⁻ˢ)`. -/
theorem cpowNeg_re_ge (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Rle (Rneg (RexpReal (Rmul (Rneg s.re) (RlogNat n hn)))) ((cpowNeg s n).re) := by
  unfold cpowNeg; rw [dif_pos hn]; exact Cexp_re_ge _

/-- `Im(n⁻ˢ) ≤ e^{−Re s·log n}`. -/
theorem cpowNeg_im_le (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Rle ((cpowNeg s n).im) (RexpReal (Rmul (Rneg s.re) (RlogNat n hn))) := by
  unfold cpowNeg; rw [dif_pos hn]; exact Cexp_im_le _

/-- `−e^{−Re s·log n} ≤ Im(n⁻ˢ)`. -/
theorem cpowNeg_im_ge (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Rle (Rneg (RexpReal (Rmul (Rneg s.re) (RlogNat n hn)))) ((cpowNeg s n).im) := by
  unfold cpowNeg; rw [dif_pos hn]; exact Cexp_im_ge _


-- ===========================================================================
-- The tight exponential lower bound  1 + 4t ≤ e^t  (t ∈ [−1/2,0]), i.e. 1 − e^{−d} ≤ 4d.
-- The analytic crux of the η variation bound: lifts the Q-level quadratic remainder
-- `expSum_quad` (|expSum q N − (1+q)| ≤ |q|²·expSumM ≤ 3q²) through the diagonal, using the
-- algebra (1+q)−3q² ≥ 1+4q (q∈[−1,0]) to get a LINEAR bound (no real-side product to reconcile).
-- ===========================================================================

-- GOAL 1 (Q-level): for |q| ≤ 1 and q ≤ 1/(N+1) (the wiggle/upper bound) and N ≥ 1,
--   1 + 4q ≤ expSum q N + 3/(N+1).
-- Proof idea (by_cases on sign of q):
--   q ≥ 0:  expSum q N ≥ 1+q (expSum_ge_one_add, index N-1+1=N); 1+4q = (1+q)+3q ≤ expSum+3q ≤ expSum+3/(N+1)
--           since 3q ≤ 3/(N+1) (q ≤ 1/(N+1)).
--   q < 0:  expSum_quad gives |expSum q N − (1+q)| ≤ |q|²·expSumM 1 N ≤ 3q² (expSumM 1 N ≤ 3).
--           So expSum q N ≥ (1+q) − 3q². For q ∈ [−1,0): (1+q)−3q² ≥ 1+4q  (⟺ q(q+1) ≤ 0). Hence
--           1+4q ≤ expSum q N ≤ expSum q N + 3/(N+1).
-- expSumM 1 N ≤ ⟨3,1⟩ :  Qle_trans (expM_U_den_pos 1 2) (expSumM_le_U 1 N) (by decide)
theorem expSum_ge_one_add_four {q : Q} (hqd : 0 < q.den) (N : Nat) (hN1 : 1 ≤ N)
    (hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q)) (hqhi : Qle q (⟨1, N + 1⟩ : Q)) :
    Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) q)) (add (expSum q N) (⟨3, N + 1⟩ : Q)) := by
  by_cases hq0 : 0 ≤ q.num
  · -- q ≥ 0 :  1+4q = (1+q) + 3q ≤ expSum + 3/(N+1)
    have hge : Qle (add (⟨1, 1⟩ : Q) q) (expSum q N) := by
      have h := expSum_ge_one_add hq0 hqd (N - 1)
      rwa [(by omega : N - 1 + 1 = N)] at h
    -- 3q ≤ 3/(N+1)
    have h3q : Qle (mul (⟨3, 1⟩ : Q) q) (⟨3, N + 1⟩ : Q) := by
      have h := Qmul_le_mul_left (c := (⟨3, 1⟩ : Q)) (by decide) hqhi
      refine Qle_trans (Qmul_den_pos (by decide) (Nat.succ_pos N)) h (Qeq_le ?_)
      simp only [Qeq, mul]; push_cast; ring_uor
    -- assemble
    have hsum : Qle (add (add (⟨1, 1⟩ : Q) q) (mul (⟨3, 1⟩ : Q) q))
        (add (expSum q N) (⟨3, N + 1⟩ : Q)) := Qadd_le_add hge h3q
    refine Qle_trans (add_den_pos (add_den_pos (by decide) hqd) (Qmul_den_pos (by decide) hqd))
      (Qeq_le ?_) hsum
    simp only [Qeq, add, mul]; push_cast; ring_uor
  · -- q < 0 :  1+4q ≤ (1+q) - 3q² ≤ expSum  ≤ expSum + 3/(N+1)
    have hq0 : q.num < 0 := Int.not_le.mp hq0
    have hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q) := hq1
    -- quadratic remainder:  expSum q N ≥ (1+q) - |q|²·expSumM 1 N
    have hNsucc : N - 1 + 1 = N := by omega
    have hquad := expSum_quad hqd hq1 (N - 1)
    rw [hNsucc] at hquad
    -- |q|² ≤ |q|·1 = |q| = -q  (since q<0);  expSumM ≤ 3
    have hnn_q : 0 ≤ (Qabs q).num := Qabs_num_nonneg q
    have hEbound : Qle (expSumM 1 N) (⟨3, 1⟩ : Q) :=
      Qle_trans (expM_U_den_pos 1 2) (expSumM_le_U 1 N) (by decide)
    have hRden : 0 < (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)).den :=
      Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (expSumM_den_pos 1 N)
    -- expSum q N ≥ (1+q) − R   where R = |q|²·expSumM
    have hlow : Qle (Qsub (add (⟨1, 1⟩ : Q) q) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)))
        (expSum q N) := by
      -- (1+q) ≤ expSum + R
      have hle1 : Qle (add (⟨1, 1⟩ : Q) q)
          (add (expSum q N) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))) :=
        Qle_add_of_Qabs_sub (add_den_pos (by decide) hqd) (expSum_den_pos hqd N) hRden
          (by rw [Qabs_Qsub_comm]; exact hquad)
      -- commute to  (1+q) ≤ R + expSum
      have hle2 : Qle (add (⟨1, 1⟩ : Q) q)
          (add (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (expSum q N)) :=
        Qle_trans (add_den_pos (expSum_den_pos hqd N) hRden) hle1
          (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor))
      exact Qsub_le_of_le_add hRden (expSum_den_pos hqd N) hle2
    -- 1+4q ≤ (1+q) − 3q²    (⟺ q(q+1) ≤ 0, here via |q|²≤|q|=−q)
    -- step: |q|·|q| ≤ |q|·1
    have hsq : Qle (mul (Qabs q) (Qabs q)) (Qabs q) := by
      have h := Qmul_le_mul_left (c := Qabs q) hnn_q hq1
      refine Qle_trans (Qmul_den_pos (Qabs_den_pos hqd) (by decide)) h (Qeq_le ?_)
      simp only [Qeq, mul, Qabs]; push_cast; ring_uor
    -- now 1+4q ≤ (1+q) − |q|²·expSumM
    have hfinal : Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) q))
        (Qsub (add (⟨1, 1⟩ : Q) q) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))) := by
      -- R := |q|²·expSumM ;  show R ≤ (-q)·3 = -3q.
      -- step a:  R ≤ |q|²·3
      have hRle : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))
          (mul (mul (Qabs q) (Qabs q)) (⟨3, 1⟩ : Q)) :=
        Qmul_le_mul_left (Int.mul_nonneg hnn_q hnn_q) hEbound
      -- step b:  |q|²·3 ≤ |q|·3
      have hR3 : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (mul (Qabs q) (⟨3, 1⟩ : Q)) :=
        Qle_trans (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (by decide))
          hRle (Qmul_le_mul_right (by decide) hsq)
      -- |q|·3 = (-q)·3   (|q| = -q since q<0)
      have habsneg : Qeq (mul (Qabs q) (⟨3, 1⟩ : Q)) (mul (neg q) (⟨3, 1⟩ : Q)) := by
        have hna : (q.num.natAbs : Int) = -q.num := by omega
        simp only [Qeq, mul, Qabs, neg]; push_cast; rw [hna]
      have hkey : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (mul (neg q) (⟨3, 1⟩ : Q)) :=
        Qle_trans (Qmul_den_pos (Qabs_den_pos hqd) (by decide)) hR3 (Qeq_le habsneg)
      -- subtraction antitone:  (1+q) − (-3q) ≤ (1+q) − R ,  and (1+q) − (-3q) = 1+4q.
      refine Qle_trans (b := Qsub (add (⟨1, 1⟩ : Q) q) (mul (neg q) (⟨3, 1⟩ : Q)))
        (Qsub_den_pos (add_den_pos (by decide) hqd)
        (Qmul_den_pos (neg_den_pos hqd) (by decide))) ?_ ?_
      · -- 1+4q = (1+q) − (-q)·3
        exact Qeq_le (by simp only [Qeq, Qsub, add, neg, mul, Qabs]; push_cast; ring_uor)
      · -- (1+q) − (-q)·3 ≤ (1+q) − R  via R ≤ (-q)·3
        simp only [Qsub]
        exact Qadd_le_add (Qle_refl _) (Qneg_le_neg hkey)
    -- chain: 1+4q ≤ (1+q)−R ≤ expSum ≤ expSum + 3/(N+1)
    refine Qle_trans (Qsub_den_pos (add_den_pos (by decide) hqd)
      (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (expSumM_den_pos 1 N)))
      hfinal ?_
    exact Qle_trans (expSum_den_pos hqd N) hlow
      (Qle_self_add (by show (0 : Int) ≤ 3; decide))

-- Helper: the loose form of GOAL 1 with the Bishop upper bound `q ≤ 2/(N+1)` (slack `6/(N+1)`).
-- This is the form actually available at the diagonal (the real `t ≤ 0` only gives `2/(N+1)`).
private theorem expSum_ge_four_loose {q : Q} (hqd : 0 < q.den) (N : Nat) (hN1 : 1 ≤ N)
    (hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q)) (hqhi : Qle q (⟨2, N + 1⟩ : Q)) :
    Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) q)) (add (expSum q N) (⟨6, N + 1⟩ : Q)) := by
  by_cases hq0 : 0 ≤ q.num
  · -- q ≥ 0 :  1+4q = (1+q) + 3q ≤ expSum + 6/(N+1)
    have hge : Qle (add (⟨1, 1⟩ : Q) q) (expSum q N) := by
      have h := expSum_ge_one_add hq0 hqd (N - 1)
      rwa [(by omega : N - 1 + 1 = N)] at h
    have h3q : Qle (mul (⟨3, 1⟩ : Q) q) (⟨6, N + 1⟩ : Q) := by
      have h := Qmul_le_mul_left (c := (⟨3, 1⟩ : Q)) (by decide) hqhi
      refine Qle_trans (Qmul_den_pos (by decide) (Nat.succ_pos N)) h (Qeq_le ?_)
      simp only [Qeq, mul]; push_cast; ring_uor
    have hsum : Qle (add (add (⟨1, 1⟩ : Q) q) (mul (⟨3, 1⟩ : Q) q))
        (add (expSum q N) (⟨6, N + 1⟩ : Q)) := Qadd_le_add hge h3q
    refine Qle_trans (add_den_pos (add_den_pos (by decide) hqd) (Qmul_den_pos (by decide) hqd))
      (Qeq_le ?_) hsum
    simp only [Qeq, add, mul]; push_cast; ring_uor
  · -- q < 0 :  identical to GOAL 1, slack 3 ≤ 6
    have hq0 : q.num < 0 := Int.not_le.mp hq0
    have hNsucc : N - 1 + 1 = N := by omega
    have hquad := expSum_quad hqd hq1 (N - 1)
    rw [hNsucc] at hquad
    have hnn_q : 0 ≤ (Qabs q).num := Qabs_num_nonneg q
    have hEbound : Qle (expSumM 1 N) (⟨3, 1⟩ : Q) :=
      Qle_trans (expM_U_den_pos 1 2) (expSumM_le_U 1 N) (by decide)
    have hRden : 0 < (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)).den :=
      Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (expSumM_den_pos 1 N)
    have hlow : Qle (Qsub (add (⟨1, 1⟩ : Q) q) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)))
        (expSum q N) := by
      have hle1 : Qle (add (⟨1, 1⟩ : Q) q)
          (add (expSum q N) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))) :=
        Qle_add_of_Qabs_sub (add_den_pos (by decide) hqd) (expSum_den_pos hqd N) hRden
          (by rw [Qabs_Qsub_comm]; exact hquad)
      have hle2 : Qle (add (⟨1, 1⟩ : Q) q)
          (add (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (expSum q N)) :=
        Qle_trans (add_den_pos (expSum_den_pos hqd N) hRden) hle1
          (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor))
      exact Qsub_le_of_le_add hRden (expSum_den_pos hqd N) hle2
    have hsq : Qle (mul (Qabs q) (Qabs q)) (Qabs q) := by
      have h := Qmul_le_mul_left (c := Qabs q) hnn_q hq1
      refine Qle_trans (Qmul_den_pos (Qabs_den_pos hqd) (by decide)) h (Qeq_le ?_)
      simp only [Qeq, mul, Qabs]; push_cast; ring_uor
    have hfinal : Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) q))
        (Qsub (add (⟨1, 1⟩ : Q) q) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))) := by
      have hRle : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))
          (mul (mul (Qabs q) (Qabs q)) (⟨3, 1⟩ : Q)) :=
        Qmul_le_mul_left (Int.mul_nonneg hnn_q hnn_q) hEbound
      have hR3 : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (mul (Qabs q) (⟨3, 1⟩ : Q)) :=
        Qle_trans (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (by decide))
          hRle (Qmul_le_mul_right (by decide) hsq)
      have habsneg : Qeq (mul (Qabs q) (⟨3, 1⟩ : Q)) (mul (neg q) (⟨3, 1⟩ : Q)) := by
        have hna : (q.num.natAbs : Int) = -q.num := by omega
        simp only [Qeq, mul, Qabs, neg]; push_cast; rw [hna]
      have hkey : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (mul (neg q) (⟨3, 1⟩ : Q)) :=
        Qle_trans (Qmul_den_pos (Qabs_den_pos hqd) (by decide)) hR3 (Qeq_le habsneg)
      refine Qle_trans (b := Qsub (add (⟨1, 1⟩ : Q) q) (mul (neg q) (⟨3, 1⟩ : Q)))
        (Qsub_den_pos (add_den_pos (by decide) hqd)
        (Qmul_den_pos (neg_den_pos hqd) (by decide))) ?_ ?_
      · exact Qeq_le (by simp only [Qeq, Qsub, add, neg, mul, Qabs]; push_cast; ring_uor)
      · simp only [Qsub]
        exact Qadd_le_add (Qle_refl _) (Qneg_le_neg hkey)
    refine Qle_trans (Qsub_den_pos (add_den_pos (by decide) hqd) hRden) hfinal ?_
    exact Qle_trans (expSum_den_pos hqd N) hlow
      (Qle_self_add (by show (0 : Int) ≤ 6; decide))

-- GOAL 2 (real lift): for t ≤ 0 and t ≥ −1/2,  1 + 4t ≤ e^t.
-- Mirror RexpReal_ge_one_add_nonneg (RealPow:899-942). Diagonal j, R := RexpReal_R t j (≥ 4(j+1)).
-- LHS.seq(2j+1) = add ⟨1,1⟩ (mul ⟨4,1⟩ (t.seq A)) with A = Ridx (ofQ⟨4,1⟩) t (2*(2j+1)+1) (deep, ≥ R-scale).
-- Sample q := t.seq R.  From ht0 (t≤0): q ≤ 1/(R+1).  From htlo (t≥−1/2): q ≥ −1 (R large).  ⟹ |q|≤1.
-- Use expSum_ge_one_add_four at q,R; reconcile t.seq A ↔ t.seq R (and t.seq(2j+1)) by xreg_n_le × 4.
theorem RexpReal_ge_one_add_four {t : Real} (ht0 : Rle t zero)
    (htlo : Rle (Rneg (ofQ (⟨1, 2⟩ : Q) (by decide))) t) :
    Rle (Radd one (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) t)) (RexpReal t) := by
  intro j
  show Qle (add (⟨1, 1⟩ : Q)
      (mul (⟨4, 1⟩ : Q) (t.seq (Ridx (ofQ (⟨4, 1⟩ : Q) (by decide)) t (2 * j + 1)))))
    (add (expSum (t.seq (RexpReal_R t j)) (RexpReal_R t j)) ⟨2, j + 1⟩)
  -- xBound t ≥ 2 (since (t.seq 0).den ≥ 1)
  have hxB : 2 ≤ xBound t := by unfold xBound; have := t.den_pos 0; omega
  -- RexpReal_K t ≥ 2
  have hK2 : 2 ≤ RexpReal_K t := by
    unfold RexpReal_K
    have hp : 0 < npow (xBound t) (2 * xBound t + 1) := npow_pos (by omega) _
    omega
  -- R ≥ 8*(j+1) + 4
  have hRlb : 8 * (j + 1) + 4 ≤ RexpReal_R t j := by
    unfold RexpReal_R
    have hmul : 4 * (j + 1) * 2 ≤ 4 * (j + 1) * RexpReal_K t := Nat.mul_le_mul_left _ hK2
    omega
  -- RmulK ≥ 2  (xBound t ≥ 2)
  have hKmul : 2 ≤ RmulK (ofQ (⟨4, 1⟩ : Q) (by decide)) t := by unfold RmulK; omega
  -- A ≥ 8*(j+1) - 1
  have hAlb : 8 * (j + 1) ≤ Ridx (ofQ (⟨4, 1⟩ : Q) (by decide)) t (2 * j + 1) + 1 := by
    rw [Ridx_succ (ofQ (⟨4, 1⟩ : Q) (by decide)) t (2 * j + 1)]
    have hmul : 2 * 2 * (2 * j + 1 + 1)
        ≤ 2 * RmulK (ofQ (⟨4, 1⟩ : Q) (by decide)) t * (2 * j + 1 + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hKmul)
    omega
  -- abstract the two heavy indices
  generalize hRdef : RexpReal_R t j = R at hRlb ⊢
  generalize hAdef : Ridx (ofQ (⟨4, 1⟩ : Q) (by decide)) t (2 * j + 1) = A at hAlb ⊢
  have hqd : 0 < (t.seq R).den := t.den_pos _
  -- the floor n₀ = 8(j+1) - 1, so n₀ + 1 = 8(j+1)
  have hn0A : 8 * (j + 1) - 1 ≤ A := by omega
  have hn0R : 8 * (j + 1) - 1 ≤ R := by omega
  have hn0succ : (8 * (j + 1) - 1) + 1 = 8 * (j + 1) := by omega
  -- q-bounds:  upper  q ≤ 2/(R+1)
  have hqhi : Qle (t.seq R) (⟨2, R + 1⟩ : Q) := by
    have h := ht0 R
    -- zero.seq R = ⟨0,1⟩ ;  add ⟨0,1⟩ ⟨2,R+1⟩ ≈ ⟨2,R+1⟩
    refine Qle_trans (add_den_pos (zero.den_pos R) (Nat.succ_pos R)) h (Qeq_le ?_)
    simp only [zero, ofQ, Qeq, add]; push_cast; ring_uor
  -- q-bounds: lower  -1/2 - 2/(R+1) ≤ q  ⟹  |q| ≤ 1
  have hq1 : Qle (Qabs (t.seq R)) (⟨1, 1⟩ : Q) := by
    have hlo := htlo R
    -- (Rneg (ofQ ⟨1,2⟩)).seq R = ⟨-1,2⟩
    have hlo' : Qle (⟨-1, 2⟩ : Q) (add (t.seq R) (⟨2, R + 1⟩ : Q)) := by
      refine Qle_trans (b := (Rneg (ofQ (⟨1, 2⟩ : Q) (by decide))).seq R)
        (Real.den_pos _ R) (Qeq_le ?_) hlo
      simp only [Rneg, ofQ, neg, Qeq]
    -- so q.num ≥ -(q.den)  (i.e. q ≥ -1) using R ≥ 3
    by_cases hsgn : 0 ≤ (t.seq R).num
    · -- q ≥ 0:  |q| = q ≤ 2/(R+1) ≤ 1
      have habsq : Qeq (Qabs (t.seq R)) (t.seq R) := by
        have hna : ((t.seq R).num.natAbs : Int) = (t.seq R).num := by omega
        simp only [Qeq, Qabs]; push_cast; rw [hna]
      have hle2 : Qle (Qabs (t.seq R)) (⟨2, R + 1⟩ : Q) :=
        Qle_trans hqd (Qeq_le habsq) hqhi
      exact Qle_trans (Nat.succ_pos R) hle2 (by simp only [Qle]; push_cast; omega)
    · -- q < 0:  |q| = -q ≤ 1/2 + 2/(R+1) ≤ 1  (R ≥ 3)
      have hneg : (t.seq R).num < 0 := Int.not_le.mp hsgn
      have hRbig : (3 : Int) ≤ ((R : Nat) : Int) := by
        have : 3 ≤ R := by omega
        exact_mod_cast this
      have hdpos : (1 : Int) ≤ ((t.seq R).den : Int) := by have := hqd; omega
      have hP : (0 : Int) < ((R : Nat) : Int) + 1 := by omega
      -- unfold hlo':  -(d·(R+1)) ≤ (n·(R+1) + 2·d)·2
      simp only [Qle, add] at hlo'
      push_cast at hlo'
      -- abbreviate the two products
      have hkey : -(t.seq R).num ≤ ((t.seq R).den : Int) := by
        -- write d, n, P
        -- hstar :  -(d*P) ≤ 2*n*P + 4*d
        have hstar : -(((t.seq R).den : Int) * (((R : Nat) : Int) + 1))
            ≤ 2 * ((t.seq R).num * (((R : Nat) : Int) + 1)) + 4 * ((t.seq R).den : Int) := by
          have h := hlo'
          have e : (-1 : Int) * (((t.seq R).den : Int) * (((R : Nat) : Int) + 1))
              = -(((t.seq R).den : Int) * (((R : Nat) : Int) + 1)) := by ring_uor
          have e2 : ((t.seq R).num * (((R : Nat) : Int) + 1) + 2 * ((t.seq R).den : Int)) * 2
              = 2 * ((t.seq R).num * (((R : Nat) : Int) + 1)) + 4 * ((t.seq R).den : Int) := by ring_uor
          rw [e, e2] at h; exact h
        -- h4d :  4*d ≤ d*P   (since P ≥ 4)
        have h4d : 4 * ((t.seq R).den : Int) ≤ ((t.seq R).den : Int) * (((R : Nat) : Int) + 1) := by
          have := Int.mul_le_mul_of_nonneg_left (a := (4 : Int)) (b := ((R : Nat) : Int) + 1)
            (c := ((t.seq R).den : Int)) (by omega) (by omega)
          have e : ((t.seq R).den : Int) * 4 = 4 * ((t.seq R).den : Int) := by ring_uor
          have e2 : ((t.seq R).den : Int) * (((R : Nat) : Int) + 1)
              = ((t.seq R).den : Int) * (((R : Nat) : Int) + 1) := rfl
          omega
        -- combine:  -(2n)*P ≤ (2d)*P
        have hcomb : (-(2 * (t.seq R).num)) * (((R : Nat) : Int) + 1)
            ≤ (2 * ((t.seq R).den : Int)) * (((R : Nat) : Int) + 1) := by
          have e1 : (-(2 * (t.seq R).num)) * (((R : Nat) : Int) + 1)
              = -(2 * ((t.seq R).num * (((R : Nat) : Int) + 1))) := by ring_uor
          have e2 : (2 * ((t.seq R).den : Int)) * (((R : Nat) : Int) + 1)
              = 2 * (((t.seq R).den : Int) * (((R : Nat) : Int) + 1)) := by ring_uor
          rw [e1, e2]; omega
        have hcanc : -(2 * (t.seq R).num) ≤ 2 * ((t.seq R).den : Int) :=
          Int.le_of_mul_le_mul_right hcomb hP
        omega
      simp only [Qle, Qabs]
      push_cast
      have hna : ((t.seq R).num.natAbs : Int) = -(t.seq R).num := by omega
      rw [hna]; omega
  -- the loose lower bound at q = t.seq R, N = R
  have hlb : Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) (t.seq R)))
      (add (expSum (t.seq R) R) (⟨6, R + 1⟩ : Q)) :=
    expSum_ge_four_loose hqd R (by omega) hq1 hqhi
  -- reconcile t.seq A with t.seq R at floor n0 (×4)
  have hAR : Qle (Qabs (Qsub (t.seq A) (t.seq R))) (⟨2, (8 * (j + 1) - 1) + 1⟩ : Q) :=
    xreg_n_le t hn0A hn0R
  -- 4·|t.seq A − t.seq R| ≤ 8/(n0+1) = 1/(j+1)
  have hrec : Qle (mul (⟨4, 1⟩ : Q) (t.seq A))
      (add (mul (⟨4, 1⟩ : Q) (t.seq R)) (⟨1, j + 1⟩ : Q)) := by
    -- |4·(A) − 4·(R)| = 4·|A−R| ≤ 8/(n0+1)
    have hmuldiff : Qle (Qabs (Qsub (mul (⟨4, 1⟩ : Q) (t.seq A)) (mul (⟨4, 1⟩ : Q) (t.seq R))))
        (⟨1, j + 1⟩ : Q) := by
      have he : Qeq (Qsub (mul (⟨4, 1⟩ : Q) (t.seq A)) (mul (⟨4, 1⟩ : Q) (t.seq R)))
          (mul (⟨4, 1⟩ : Q) (Qsub (t.seq A) (t.seq R))) := by
        simp only [Qeq, Qsub, mul, add, neg]; push_cast; ring_uor
      have h2 : Qle (Qabs (mul (⟨4, 1⟩ : Q) (Qsub (t.seq A) (t.seq R))))
          (⟨1, j + 1⟩ : Q) := by
        rw [Qabs_mul]
        -- |4|·|A−R| ≤ ⟨4,1⟩·⟨2,n0+1⟩ = ⟨8,n0+1⟩ ≤ ⟨1,j+1⟩
        have h4 : Qeq (Qabs (⟨4, 1⟩ : Q)) (⟨4, 1⟩ : Q) := by simp only [Qeq, Qabs]; push_cast
        have hstep : Qle (mul (Qabs (⟨4, 1⟩ : Q)) (Qabs (Qsub (t.seq A) (t.seq R))))
            (mul (⟨4, 1⟩ : Q) (⟨2, (8 * (j + 1) - 1) + 1⟩ : Q)) :=
          Qmul_le_mul (Qabs_den_pos (by decide)) (by decide)
            (Qabs_den_pos (Qsub_den_pos (t.den_pos _) (t.den_pos _)))
            (by decide) (Qabs_num_nonneg _) (Qeq_le h4) hAR
        refine Qle_trans (Qmul_den_pos (by decide) (Nat.succ_pos _)) hstep ?_
        exact Qeq_le (by rw [hn0succ]; simp only [Qeq, mul]; push_cast; ring_uor)
      exact Qle_trans (Qabs_den_pos (Qmul_den_pos (by decide)
        (Qsub_den_pos (t.den_pos _) (t.den_pos _)))) (Qeq_le (Qabs_Qeq he)) h2
    exact Qle_add_of_Qabs_sub (Qmul_den_pos (by decide) (t.den_pos _))
      (Qmul_den_pos (by decide) (t.den_pos _)) (Nat.succ_pos _) hmuldiff
  -- assemble:  LHS ≤ add ⟨1,1⟩ (mul ⟨4,1⟩ (t.seq R)) + 1/(j+1)
  --               ≤ expSum + 6/(R+1) + 1/(j+1)  ≤ expSum + 2/(j+1)
  have hLHS : Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) (t.seq A)))
      (add (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) (t.seq R))) (⟨1, j + 1⟩ : Q)) := by
    refine Qle_trans (b := add (⟨1, 1⟩ : Q)
      (add (mul (⟨4, 1⟩ : Q) (t.seq R)) (⟨1, j + 1⟩ : Q)))
      (add_den_pos (by decide) (add_den_pos (Qmul_den_pos (by decide) (t.den_pos _))
        (Nat.succ_pos _))) (Qadd_le_add (Qle_refl _) hrec) ?_
    exact Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor)
  -- chain hLHS with hlb (add 1/(j+1) on both)
  have hchain : Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) (t.seq A)))
      (add (add (expSum (t.seq R) R) (⟨6, R + 1⟩ : Q)) (⟨1, j + 1⟩ : Q)) :=
    Qle_trans (add_den_pos (add_den_pos (by decide) (Qmul_den_pos (by decide) (t.den_pos _)))
      (Nat.succ_pos _)) hLHS (Qadd_le_add hlb (Qle_refl _))
  -- final slack:  6/(R+1) + 1/(j+1) ≤ 2/(j+1)
  refine Qle_trans (add_den_pos (add_den_pos (expSum_den_pos hqd R) (Nat.succ_pos _))
    (Nat.succ_pos _)) hchain ?_
  -- (expSum + 6/(R+1)) + 1/(j+1) = expSum + (6/(R+1) + 1/(j+1)) ≤ expSum + 2/(j+1)
  refine Qle_trans (b := add (expSum (t.seq R) R)
    (add (⟨6, R + 1⟩ : Q) (⟨1, j + 1⟩ : Q)))
    (add_den_pos (expSum_den_pos hqd R) (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
    (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor)) ?_
  refine Qadd_le_add (Qle_refl _) ?_
  -- 6/(R+1) + 1/(j+1) ≤ 2/(j+1)   (R ≥ 8(j+1)+4 ⟹ 6/(R+1) ≤ 1/(j+1))
  have h6 : Qle (⟨6, R + 1⟩ : Q) (⟨1, j + 1⟩ : Q) := by
    have hRi : (8 : Int) * ((j : Int) + 1) + 4 ≤ (R : Int) := by exact_mod_cast hRlb
    simp only [Qle]; push_cast; omega
  refine Qle_trans (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Qadd_le_add h6 (Qle_refl _)) ?_
  exact Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor)

-- real-algebra rearrangements (copied from GammaOne, which is not in this import chain)
private theorem Rsub_le_of_le_add' {x y z : Real} (h : Rle x (Radd z y)) : Rle (Rsub x y) z :=
  Rle_trans (Rsub_le_sub h (Rle_refl y))
    (Rle_of_Req (Req_trans (Radd_assoc z y (Rneg y))
      (Req_trans (Radd_congr (Req_refl z) (Radd_neg y)) (Radd_zero z))))

private theorem Rle_add_of_Rsub_le' {x y z : Real} (h : Rle (Rsub x y) z) : Rle x (Radd y z) := by
  have heq : Req (Radd (Rsub x y) y) x :=
    Req_trans (Radd_assoc x (Rneg y) y)
      (Req_trans (Radd_congr (Req_refl x) (Req_trans (Radd_comm (Rneg y) y) (Radd_neg y)))
        (Radd_zero x))
  exact Rle_trans (Rle_of_Req (Req_symm heq))
    (Rle_trans (Radd_le_add h (Rle_refl y)) (Rle_of_Req (Radd_comm z y)))

-- GOAL 3 (corollary, the applied form): 1 − e^{−d} ≤ 4d  for 0 ≤ d ≤ 1/2.
theorem RexpReal_one_sub_neg_le {d : Real} (hd0 : Rnonneg d)
    (hd1 : Rle d (ofQ (⟨1, 2⟩ : Q) (by decide))) :
    Rle (Rsub one (RexpReal (Rneg d))) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) d) := by
  -- apply GOAL 2 at t := Rneg d
  have ht0 : Rle (Rneg d) zero :=
    Rle_trans (Rle_Rneg (Rle_zero_of_Rnonneg hd0)) (Rle_of_Req Rneg_zero)
  have htlo : Rle (Rneg (ofQ (⟨1, 2⟩ : Q) (by decide))) (Rneg d) := Rle_Rneg hd1
  have hG2 : Rle (Radd one (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rneg d)))
      (RexpReal (Rneg d)) := RexpReal_ge_one_add_four ht0 htlo
  -- rewrite LHS:  1 + 4·(−d) ≈ 1 − 4·d
  have hEq : Req (Radd one (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rneg d)))
      (Rsub one (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) d)) :=
    Radd_congr (Req_refl _) (Rmul_neg_right (ofQ (⟨4, 1⟩ : Q) (by decide)) d)
  have hG2' : Rle (Rsub one (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) d)) (RexpReal (Rneg d)) :=
    Rle_trans (Rle_of_Req (Req_symm hEq)) hG2
  -- rearrange:  1 − 4d ≤ e^{−d}  ⟹  1 ≤ 4d + e^{−d}  ⟹  1 − e^{−d} ≤ 4d
  have h1 : Rle one (Radd (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) d) (RexpReal (Rneg d))) :=
    Rle_add_of_Rsub_le' hG2'
  exact Rsub_le_of_le_add' h1


-- ===========================================================================
-- Tight cos/sin bounds for the η variation: 1 − cos x ≤ 3x² and RsinAux x ∈ [1−3x², 1+3x²]
-- (for x ∈ [−1,1]). Lifts the alternating-series quadratic remainder altSum_quad (|altSum q off N −
-- ⟨1,fct off⟩| ≤ 3|q|²) through the RaltReal diagonal, with a Bishop-overshoot clamp reconciled by
-- the established Lipschitz machinery (altSum_Lip_le/qsq_diff_le/LipS_le_U, as in RaltReal_diag_le).
-- ===========================================================================

-- altTerm q off n = (−q²)^n / (2n+off)!   [CosSin.lean:43]
-- altSum  q off 0 = altTerm q off 0 = ⟨1, fct off⟩ ;  altSum q off (n+1) = altSum q off n + altTerm q off (n+1)
-- For off ∈ {0,1}:  fct off = 1, so altSum q off 0 = ⟨1,1⟩.
-- (RaltReal x off).seq j = altSum (x.seq (RaltReal_R x j)) off (RaltReal_R x j)   [diagonal]
-- RaltReal_diag_le : j ≤ k → |RaltReal_seq x off j − RaltReal_seq x off k| ≤ ⟨1, j+1⟩   (Qbound j)
-- Rcos x = RaltReal x 0 ;  RsinAux x = RaltReal x 1 ;  Rsin x = Rmul x (RsinAux x)

-- GOAL 1 (Q-level, the keystone — mirror expSum_quad @ ExpLog.lean:597):
-- the deviation of altSum from its first term ⟨1,fct off⟩ is O(q²):  |altSum q off N − ⟨1,fct off⟩| ≤ 3·|q|².
-- Proof idea: altSum q off N − altSum q off 0 = Σ_{k=1}^N altTerm q off k ;  triangle-ineq + each
-- |altTerm q off k| = (q²)^k/(2k+off)! = q²·(q²)^{k-1}/(2k+off)! ≤ q²·1/(2k+off)! (|q|≤1), and Σ 1/(2k+off)! ≤ 3.
-- |neg(q²)| = |q|·|q| as a Q-equality.
private theorem altq2_abs {q : Q} : Qabs (neg (mul q q)) = mul (Qabs q) (Qabs q) := by
  rw [Qabs_neg, Qabs_mul]

-- |q|² ≤ ⟨1,1⟩ from |q| ≤ ⟨1,1⟩.
private theorem altq2_le_one {q : Q} (hqd : 0 < q.den) (hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q)) :
    Qle (mul (Qabs q) (Qabs q)) (⟨1, 1⟩ : Q) := by
  have h := Qmul_le_mul (a := Qabs q) (b := ⟨1, 1⟩) (c := Qabs q) (d := ⟨1, 1⟩)
    (Qabs_den_pos hqd) (by decide) (Qabs_den_pos hqd) (Qabs_num_nonneg q) (Qabs_num_nonneg q) hq1 hq1
  refine Qle_trans (Qmul_den_pos (by decide) (by decide)) h (Qeq_le ?_)
  simp only [Qeq, mul]; push_cast

-- **Per-term quadratic bound** for the alternating series (k ≥ 1):
-- |altTerm q off k| ≤ |q|²·(1/k!).
private theorem altTerm_quad {q : Q} (hqd : 0 < q.den) (hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q))
    {off n : Nat} (hn : 1 ≤ n) :
    Qle (Qabs (altTerm q off n)) (mul (mul (Qabs q) (Qabs q)) (⟨1, fct n⟩ : Q)) := by
  have hq2d : 0 < (mul (Qabs q) (Qabs q)).den := Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)
  have hq2n : 0 ≤ (mul (Qabs q) (Qabs q)).num :=
    Int.mul_nonneg (Qabs_num_nonneg q) (Qabs_num_nonneg q)
  have hq2one : Qle (mul (Qabs q) (Qabs q)) (⟨1, 1⟩ : Q) := altq2_le_one hqd hq1
  -- |altTerm| = qpow |neg q²| n · ⟨1,fct(2n+off)⟩
  have habs : Qabs (altTerm q off n)
      = mul (Qabs (qpow (neg (mul q q)) n)) ⟨1, fct (2 * n + off)⟩ := by
    unfold altTerm; rw [Qabs_mul]; rfl
  rw [habs]
  -- Qabs (qpow b n) = qpow (Qabs b) n = qpow (mul |q| |q|) n
  have hbabs : Qeq (Qabs (qpow (neg (mul q q)) n)) (qpow (mul (Qabs q) (Qabs q)) n) := by
    rw [← altq2_abs]; exact qpow_abs (neg (mul q q)) n
  -- qpow q2 n ≤ q2  (n ≥ 1):  qpow q2 n = q2 · qpow q2 (n-1) ≤ q2·1
  have hsplit : Qeq (qpow (mul (Qabs q) (Qabs q)) n)
      (mul (mul (Qabs q) (Qabs q)) (qpow (mul (Qabs q) (Qabs q)) (n - 1))) := by
    have hid : 1 + (n - 1) = n := by omega
    have h := qpow_add (mul (Qabs q) (Qabs q)) hq2d 1 (n - 1)
    rw [hid] at h
    refine Qeq_trans (Qmul_den_pos (qpow_den_pos hq2d 1) (qpow_den_pos hq2d (n - 1))) h ?_
    refine Qmul_congr ?_ (Qeq_refl _)
    show Qeq (qpow (mul (Qabs q) (Qabs q)) 1) (mul (Qabs q) (Qabs q))
    show Qeq (mul (mul (Qabs q) (Qabs q)) (⟨1, 1⟩ : Q)) (mul (Qabs q) (Qabs q))
    simp only [Qeq, mul]; push_cast; ring_uor
  have hle1 : Qle (qpow (mul (Qabs q) (Qabs q)) (n - 1)) (⟨1, 1⟩ : Q) :=
    qpow_le_one hq2n hq2d hq2one (n - 1)
  have hpow : Qle (qpow (mul (Qabs q) (Qabs q)) n) (mul (Qabs q) (Qabs q)) := by
    refine Qle_trans (Qmul_den_pos hq2d (qpow_den_pos hq2d (n - 1))) (Qeq_le hsplit) ?_
    refine Qle_trans (Qmul_den_pos hq2d (by decide)) (Qmul_le_mul_left hq2n hle1) (Qeq_le ?_)
    show Qeq (mul (mul (Qabs q) (Qabs q)) (⟨1, 1⟩ : Q)) (mul (Qabs q) (Qabs q))
    simp only [Qeq, mul]; push_cast; ring_uor
  -- |altTerm| ≤ q2·⟨1,fct(2n+off)⟩ ≤ q2·⟨1,fct n⟩
  have hstep1 : Qle (mul (Qabs (qpow (neg (mul q q)) n)) ⟨1, fct (2 * n + off)⟩)
      (mul (mul (Qabs q) (Qabs q)) ⟨1, fct (2 * n + off)⟩) := by
    refine Qmul_le_mul_right (by show (0 : Int) ≤ 1; decide) ?_
    exact Qle_trans (qpow_den_pos hq2d n) (Qeq_le hbabs) hpow
  have hstep2 : Qle (mul (mul (Qabs q) (Qabs q)) ⟨1, fct (2 * n + off)⟩)
      (mul (mul (Qabs q) (Qabs q)) ⟨1, fct n⟩) := by
    refine Qmul_le_mul_left hq2n ?_
    show (1 : Int) * ((fct n : Nat) : Int) ≤ 1 * ((fct (2 * n + off) : Nat) : Int)
    have := fct_mono (show n ≤ 2 * n + off by omega); push_cast; omega
  exact Qle_trans (Qmul_den_pos hq2d (fct_pos _)) hstep1 hstep2

-- **Quadratic remainder with M-series RHS** (mirror expSum_quad): for |q|≤1,
-- |altSum q off (N+1) − ⟨1,fct off⟩| ≤ |q|²·(expSumM 1 (N+1) − ⟨1,1⟩).
-- Note: altSum q off 0 = ⟨1,fct off⟩, so the k=0 term is excluded; we subtract the ⟨1,1⟩ = 1/0!.
private theorem altSum_quad_M {q : Q} {off : Nat} (hqd : 0 < q.den) (hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q))
    (N : Nat) : Qle (Qabs (Qsub (altSum q off N) (⟨1, fct off⟩ : Q)))
      (mul (mul (Qabs q) (Qabs q)) (Qsub (expSumM 1 N) (⟨1, 1⟩ : Q))) := by
  induction N with
  | zero =>
      -- altSum q off 0 = ⟨1,fct off⟩, so |difference| = 0; RHS = |q|²·0 = 0
      have hidx : 2 * 0 + off = off := by omega
      -- |Qsub (altSum q off 0) ⟨1,fct off⟩| ≈ 0
      have habs0 : Qeq (Qabs (Qsub (altSum q off 0) (⟨1, fct off⟩ : Q))) ⟨0, 1⟩ := by
        show Qeq (Qabs (Qsub (mul (⟨1, 1⟩ : Q) ⟨1, fct (2 * 0 + off)⟩) (⟨1, fct off⟩ : Q))) ⟨0, 1⟩
        rw [hidx]
        have : (Qsub (mul (⟨1, 1⟩ : Q) ⟨1, fct off⟩) (⟨1, fct off⟩ : Q)).num = 0 := by
          simp only [Qsub, add, neg, mul]; push_cast; ring_uor
        simp only [Qeq, Qabs]; rw [this]; simp
      have hz : Qeq (mul (mul (Qabs q) (Qabs q)) (Qsub (expSumM 1 0) (⟨1, 1⟩ : Q))) ⟨0, 1⟩ := by
        show Qeq (mul (mul (Qabs q) (Qabs q)) (Qsub (⟨1, 1⟩ : Q) (⟨1, 1⟩ : Q))) ⟨0, 1⟩
        simp only [Qeq, Qsub, add, neg, mul]; push_cast; ring_uor
      have habsd : 0 < (Qabs (Qsub (altSum q off 0) (⟨1, fct off⟩ : Q))).den :=
        Qabs_den_pos (Qsub_den_pos (altSum_den_pos hqd off 0) (fct_pos off))
      refine Qle_trans (b := (⟨0, 1⟩ : Q)) (by decide) (Qeq_le habs0) ?_
      exact Qeq_le (Qeq_symm hz)
  | succ N ih =>
      -- altSum q off (N+1) = altSum q off N + altTerm q off (N+1)
      show Qle (Qabs (Qsub (add (altSum q off N) (altTerm q off (N + 1))) (⟨1, fct off⟩ : Q)))
        (mul (mul (Qabs q) (Qabs q))
          (Qsub (add (expSumM 1 N) ⟨(npow 1 (N + 1) : Int), fct (N + 1)⟩) (⟨1, 1⟩ : Q)))
      have hrw : Qeq (Qsub (add (altSum q off N) (altTerm q off (N + 1))) (⟨1, fct off⟩ : Q))
          (add (Qsub (altSum q off N) (⟨1, fct off⟩ : Q)) (altTerm q off (N + 1))) := by
        simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
      refine Qle_congr_left (Qabs_den_pos (add_den_pos (Qsub_den_pos (altSum_den_pos hqd off N)
          (fct_pos off)) (altTerm_den_pos hqd off (N + 1))))
        (Qeq_symm (Qabs_Qeq hrw)) ?_
      refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (altSum_den_pos hqd off N) (fct_pos off)))
          (Qabs_den_pos (altTerm_den_pos hqd off (N + 1))))
        (Qabs_add_le _ _) ?_
      refine Qle_trans (add_den_pos (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd))
          (Qsub_den_pos (expSumM_den_pos 1 N) (by decide)))
          (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (fct_pos _)))
        (Qadd_le_add ih (altTerm_quad hqd hq1 (by omega : 1 ≤ N + 1))) (Qeq_le ?_)
      rw [npow_one]
      simp only [Qeq, mul, add, Qsub, neg]; push_cast; ring_uor

theorem altSum_quad {q : Q} {off : Nat} (hqd : 0 < q.den) (hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q)) (N : Nat) :
    Qle (Qabs (Qsub (altSum q off N) (⟨1, fct off⟩ : Q)))
      (mul (mul (Qabs q) (Qabs q)) (⟨3, 1⟩ : Q)) := by
  cases N with
  | zero =>
      -- |difference| is 0 ≤ |q|²·3
      have hidx : 2 * 0 + off = off := by omega
      have habs0 : Qeq (Qabs (Qsub (altSum q off 0) (⟨1, fct off⟩ : Q))) ⟨0, 1⟩ := by
        show Qeq (Qabs (Qsub (mul (⟨1, 1⟩ : Q) ⟨1, fct (2 * 0 + off)⟩) (⟨1, fct off⟩ : Q))) ⟨0, 1⟩
        rw [hidx]
        have : (Qsub (mul (⟨1, 1⟩ : Q) ⟨1, fct off⟩) (⟨1, fct off⟩ : Q)).num = 0 := by
          simp only [Qsub, add, neg, mul]; push_cast; ring_uor
        simp only [Qeq, Qabs]; rw [this]; simp
      refine Qle_trans (b := (⟨0, 1⟩ : Q)) (by decide) (Qeq_le habs0) ?_
      exact Qsq_mul_nonneg q (⟨3, 1⟩ : Q) (by decide)
  | succ M =>
      -- use the M-series bound, then expSumM 1 (M+1) − 1 ≤ 3
      have hM := altSum_quad_M (off := off) hqd hq1 (M + 1)
      have hnn : 0 ≤ (mul (Qabs q) (Qabs q)).num :=
        Int.mul_nonneg (Qabs_num_nonneg q) (Qabs_num_nonneg q)
      -- expSumM 1 (M+1) ≤ ⟨3,1⟩ , so expSumM 1 (M+1) − ⟨1,1⟩ ≤ ⟨3,1⟩
      have hEbound : Qle (expSumM 1 (M + 1)) (⟨3, 1⟩ : Q) :=
        Qle_trans (expM_U_den_pos 1 2) (expSumM_le_U 1 (M + 1)) (by decide)
      have hsuble : Qle (Qsub (expSumM 1 (M + 1)) (⟨1, 1⟩ : Q)) (⟨3, 1⟩ : Q) :=
        Qle_trans (expSumM_den_pos 1 (M + 1))
          (Qsub_le_self (by show (0 : Int) ≤ 1; decide)) hEbound
      have hstep : Qle (mul (mul (Qabs q) (Qabs q)) (Qsub (expSumM 1 (M + 1)) (⟨1, 1⟩ : Q)))
          (mul (mul (Qabs q) (Qabs q)) (⟨3, 1⟩ : Q)) := Qmul_le_mul_left hnn hsuble
      exact Qle_trans (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd))
        (Qsub_den_pos (expSumM_den_pos 1 (M + 1)) (by decide))) hM hstep

-- GOAL 2 (real lift, two-sided — mirror RexpReal_ge_one_add_four @ EtaVariation.lean):
-- for x ∈ [−1,1],  |RaltReal x off − 1| ≤ 3·x²  (both sides). Here off ∈ {0,1} so the first term is 1.
-- The diagonal sample q = x.seq R can overshoot [−1,1] by ≤ 2/(R+1), so altSum_quad is applied not
-- to q but to its CLAMP q' ∈ [−1,1] (|q'|≤1), and the gap |altSum q − altSum q'| is killed by the
-- Lipschitz machinery (altSum_Lip_le + qsq_diff_le + LipS_le_U), exactly as in RaltReal_diag_le.
-- The RHS product diagonal x.seq A is then reconciled with q' by product-Lipschitz.

-- npow B (2B+1) ≥ B² (B ≥ 1), used to floor RaltReal_K below.
private theorem npow_ge_sq {B : Nat} (hB : 0 < B) : B * B ≤ npow B (2 * B + 1) := by
  have h1 : B ≤ npow B (2 * B) := by
    have := npow_mono (i := B) hB (a := 1) (b := 2 * B) (by omega)
    rwa [(by rfl : npow B 1 = B * npow B 0), (by rfl : npow B 0 = 1), Nat.mul_one] at this
  calc B * B ≤ B * npow B (2 * B) := Nat.mul_le_mul_left B h1
    _ = npow B (2 * B + 1) := (npow_succ B (2 * B)).symm

-- The **central scalar estimate** at diagonal index j: the alternating diagonal approximant is within
-- 3·(x.seq A)² + 2/(j+1) of 1, for ANY deep index A (A ≥ 24(j+1)). Both lifts follow.
set_option maxHeartbeats 4000000 in
private theorem RaltReal_central {x : Real} {off : Nat} (hoff : fct off = 1)
    (hx1 : Rle x one) (hx2 : Rle (Rneg one) x) (j : Nat) {A : Nat}
    (hAlb : 36 * (j + 1) ≤ A + 1) :
    Qle (Qabs (Qsub (RaltReal_seq x off j) (⟨1, 1⟩ : Q)))
      (add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))) (⟨2, j + 1⟩ : Q)) := by
  -- abbreviations and index lower bounds
  have hM2 : 2 ≤ xBound x := by unfold xBound; have := x.den_pos 0; omega
  have hB : 0 < xBound x * xBound x := Nat.mul_pos (by omega) (by omega)
  have hB4 : 4 ≤ xBound x * xBound x := Nat.mul_le_mul hM2 hM2
  -- K_alt ≥ 8·xBound·Cx  and  K_alt ≥ B² (≥ 16)
  have hKmid : 8 * xBound x * (expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat
      ≤ RaltReal_K x := by unfold RaltReal_K; omega
  have hKsq : (xBound x * xBound x) * (xBound x * xBound x) ≤ RaltReal_K x := by
    have h := npow_ge_sq hB; unfold RaltReal_K; omega
  -- R lower bounds : R ≥ 24(j+1)
  have hR_K : 4 * (j + 1) * RaltReal_K x ≤ RaltReal_R x j := by unfold RaltReal_R; omega
  have hR_big : 36 * (j + 1) ≤ RaltReal_R x j := by
    have ha : 4 * (j + 1) * ((xBound x * xBound x) * (xBound x * xBound x))
        ≤ 4 * (j + 1) * RaltReal_K x := Nat.mul_le_mul_left _ hKsq
    have hBB : 16 ≤ (xBound x * xBound x) * (xBound x * xBound x) := Nat.mul_le_mul hB4 hB4
    have hb : 4 * (j + 1) * 16 ≤ 4 * (j + 1) * ((xBound x * xBound x) * (xBound x * xBound x)) :=
      Nat.mul_le_mul_left _ hBB
    omega
  -- expand the diagonal and abstract R
  show Qle (Qabs (Qsub (altSum (x.seq (RaltReal_R x j)) off (RaltReal_R x j)) (⟨1, 1⟩ : Q)))
    (add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))) (⟨2, j + 1⟩ : Q))
  generalize hRdef : RaltReal_R x j = R at hR_big hR_K ⊢
  have hqd : 0 < (x.seq R).den := x.den_pos R
  have had : 0 < (x.seq A).den := x.den_pos A
  -- the clamp:  q' ∈ [−1,1] with |x.seq R − q'| ≤ 2/(R+1)
  have hqU : Qle (x.seq R) (add (⟨1, 1⟩ : Q) (⟨2, R + 1⟩ : Q)) := hx1 R
  have hqL : Qle (neg (⟨1, 1⟩ : Q)) (add (x.seq R) (⟨2, R + 1⟩ : Q)) := hx2 R
  obtain ⟨q', hq'd, hq'1, hq'dist⟩ :
      ∃ q', 0 < q'.den ∧ Qle (Qabs q') (⟨1, 1⟩ : Q) ∧
        Qle (Qabs (Qsub (x.seq R) q')) (⟨2, R + 1⟩ : Q) := by
    by_cases h1 : Qle (x.seq R) (⟨1, 1⟩ : Q)
    · by_cases h2 : Qle (neg (⟨1, 1⟩ : Q)) (x.seq R)
      · -- |q| ≤ 1, q' = q
        refine ⟨x.seq R, hqd, ?_, ?_⟩
        · simp only [Qle, Qabs, neg] at h1 h2 ⊢
          push_cast at h1 h2 ⊢
          rcases Int.natAbs_eq (x.seq R).num with he | he
          · rw [he]; push_cast; omega
          · rw [he]; push_cast; omega
        · have h0 : (Qsub (x.seq R) (x.seq R)).num = 0 := Qsub_self_num _
          simp only [Qle, Qabs, h0]
          simp only [Int.natAbs_zero, Int.ofNat_zero, Int.zero_mul]
          have : (0 : Int) ≤ 2 * (((Qsub (x.seq R) (x.seq R)).den : Nat) : Int) := by
            have := Qsub_den_pos hqd hqd; omega
          omega
      · -- q < −1, clamp to −1
        refine ⟨neg (⟨1, 1⟩ : Q), by decide, by decide, ?_⟩
        -- |q − (−1)| = |q+1| = |(−1) − q| with (−1) − q ≥ 0, and (−1) − q ≤ 2/(R+1) from hqL
        rw [Qabs_Qsub_comm]
        have hnn : 0 ≤ (Qsub (neg (⟨1, 1⟩ : Q)) (x.seq R)).num := by
          simp only [Qle, neg] at h2; simp only [Qsub, add, neg]; push_cast at h2 ⊢; omega
        refine Qabs_le_of_nonneg hnn ?_
        exact Qsub_le_of_le_add hqd (Nat.succ_pos _) hqL
    · -- q > 1, clamp to 1
      refine ⟨(⟨1, 1⟩ : Q), by decide, by decide, ?_⟩
      have hnn : 0 ≤ (Qsub (x.seq R) (⟨1, 1⟩ : Q)).num := by
        simp only [Qle] at h1; simp only [Qsub, add, neg]; push_cast at h1 ⊢; omega
      refine Qabs_le_of_nonneg hnn ?_
      exact Qsub_le_of_le_add (by decide) (Nat.succ_pos _) hqU
  -- bounds  |q| ≤ ⟨xBound,1⟩ and |q'| ≤ ⟨xBound,1⟩  (for altSum_Lip_le with M = xBound)
  have hqM : Qle (Qabs (x.seq R)) (⟨xBound x, 1⟩ : Q) := canon_bound x R
  have hq'M : Qle (Qabs q') (⟨xBound x, 1⟩ : Q) :=
    Qle_trans (by decide) hq'1 (by simp only [Qle]; push_cast; have := hM2; omega)
  -- ============ clamp gap:  |altSum q off R − altSum q' off R| ≤ ⟨1, 2(j+1)⟩ ============
  have hgap : Qle (Qabs (Qsub (altSum (x.seq R) off R) (altSum q' off R))) (⟨1, 2 * (j + 1)⟩ : Q) := by
    have hLS := altSum_Lip_le (M := xBound x) hqd hq'd hqM hq'M off R
    have hCle : Qle (LipS (xBound x * xBound x) R)
        (⟨((expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat : Int), 1⟩ : Q) :=
      Qle_trans (expM_U_den_pos _ _) (LipS_le_U (xBound x * xBound x) R)
        (Qle_toNat (expM_U_num_nonneg _ _) (expM_U_den_pos _ _))
    have hbridge := qsq_diff_le (M := xBound x) hqd hq'd hqM hq'M
    have hnqbridge : Qle (Qabs (Qsub (neg (mul (x.seq R) (x.seq R))) (neg (mul q' q'))))
        (mul (⟨(2 * xBound x : Nat), 1⟩ : Q) (⟨2, R + 1⟩ : Q)) :=
      Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos hqd hq'd)))
        hbridge (Qmul_le_mul_left (Int.ofNat_nonneg _) hq'dist)
    refine Qle_trans (Qmul_den_pos (LipS_den_pos _ _)
        (Qabs_den_pos (Qsub_den_pos (Nat.mul_pos hqd hqd) (Nat.mul_pos hq'd hq'd)))) hLS ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos
        (Nat.mul_pos hqd hqd) (Nat.mul_pos hq'd hq'd))))
      (Qmul_le_mul_right (Qabs_num_nonneg _) hCle) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (Nat.succ_pos _)))
      (Qmul_le_mul_left (Int.ofNat_nonneg _) hnqbridge) ?_
    show ((expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat : Int)
        * (((2 * xBound x : Nat) : Int) * 2) * (2 * (j + 1) : Nat)
        ≤ 1 * (((1 : Nat) * (1 * (R + 1)) : Nat) : Int)
    have harith : (expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat
        * (2 * xBound x * 2) * (2 * (j + 1)) ≤ 1 * (1 * (1 * (R + 1))) := by
      have he : (expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat
          * (2 * xBound x * 2) * (2 * (j + 1))
          = 8 * xBound x * (expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat
            * (j + 1) := by
        have hI : (((expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat
              * (2 * xBound x * 2) * (2 * (j + 1)) : Nat) : Int)
            = ((8 * xBound x
              * (expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat
                * (j + 1) : Nat) : Int) := by push_cast; ring_uor
        exact_mod_cast hI
      have hfin : 8 * xBound x * (expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat
          * (j + 1) ≤ R + 1 := by
        have h1 : 8 * xBound x * (expM_U (xBound x * xBound x) (2 * (xBound x * xBound x))).num.toNat
            * (j + 1) ≤ RaltReal_K x * (j + 1) := Nat.mul_le_mul_right _ hKmid
        have h2 : RaltReal_K x * (j + 1) ≤ 4 * (j + 1) * RaltReal_K x := by
          have e : 4 * (j + 1) * RaltReal_K x = 4 * (RaltReal_K x * (j + 1)) := by
            rw [Nat.mul_assoc, Nat.mul_comm (j + 1) (RaltReal_K x)]
          rw [e]; exact Nat.le_mul_of_pos_left (RaltReal_K x * (j + 1)) (by decide)
        exact Nat.le_trans (Nat.le_trans h1 h2) (Nat.le_trans hR_K (Nat.le_succ R))
      rw [he]; omega
    exact_mod_cast harith
  -- ============ altSum_quad at the CLAMP:  |altSum q' off R − 1| ≤ 3·q'² ============
  have hquad : Qle (Qabs (Qsub (altSum q' off R) (⟨1, 1⟩ : Q)))
      (mul (mul (Qabs q') (Qabs q')) (⟨3, 1⟩ : Q)) := by
    have h := altSum_quad (off := off) hq'd hq'1 R; rwa [hoff] at h
  -- ============ product reconciliation ============
  -- |x.seq R − x.seq A| ≤ 2/(36(j+1)) = ⟨1,18(j+1)⟩
  have hn0R : 36 * (j + 1) - 1 ≤ R := by omega
  have hn0A : 36 * (j + 1) - 1 ≤ A := by omega
  have hn0s : (36 * (j + 1) - 1) + 1 = 36 * (j + 1) := by omega
  have hqa : Qle (Qabs (Qsub (x.seq R) (x.seq A))) (⟨1, 18 * (j + 1)⟩ : Q) := by
    have h := xreg_n_le x hn0R hn0A; rw [hn0s] at h
    have hstep : Qle (⟨2, 36 * (j + 1)⟩ : Q) (⟨1, 18 * (j + 1)⟩ : Q) := by
      simp only [Qle]; push_cast; omega
    exact Qle_trans (by show 0 < 36 * (j + 1); omega) h hstep
  -- |q' − x.seq R| ≤ 2/(R+1) ≤ ⟨1,18(j+1)⟩  (since R+1 ≥ 36(j+1))
  have hq'R : Qle (Qabs (Qsub q' (x.seq R))) (⟨1, 18 * (j + 1)⟩ : Q) := by
    rw [Qabs_Qsub_comm]
    refine Qle_trans (Nat.succ_pos _) hq'dist ?_
    have hRi : (36 : Int) * ((j : Int) + 1) ≤ ((R : Nat) : Int) := by exact_mod_cast hR_big
    simp only [Qle]; push_cast
    have : (2 : Int) * (18 * ((j : Int) + 1)) ≤ 1 * (((R : Nat) : Int) + 1) := by omega
    exact this
  -- |q' − x.seq A| ≤ ⟨1,18(j+1)⟩ + ⟨1,18(j+1)⟩ = ⟨1,9(j+1)⟩
  have hq'a : Qle (Qabs (Qsub q' (x.seq A))) (⟨1, 9 * (j + 1)⟩ : Q) := by
    have htri := Qabs_sub_triangle (a := q') (b := x.seq R) (c := x.seq A) hq'd hqd had
    refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hq'd hqd))
        (Qabs_den_pos (Qsub_den_pos hqd had))) htri ?_
    refine Qle_trans (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Qadd_le_add hq'R hqa) ?_
    exact Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor)
  -- |x.seq A| ≤ |q'| + |q' − a| ≤ ⟨1,1⟩ + ⟨1,9(j+1)⟩ ≤ ⟨2,1⟩  (no canon_bound; uses tight q' bound)
  have ham : Qle (Qabs (x.seq A)) (⟨2, 1⟩ : Q) := by
    have haq' : Qle (Qabs (Qsub (x.seq A) q')) (⟨1, 9 * (j + 1)⟩ : Q) := by
      rw [Qabs_Qsub_comm]; exact hq'a
    refine Qle_trans (add_den_pos (Qabs_den_pos hq'd) (Qabs_den_pos (Qsub_den_pos had hq'd)))
      (Qabs_le_add hq'd had) ?_
    refine Qle_trans (add_den_pos Nat.one_pos (Nat.succ_pos _)) (Qadd_le_add hq'1 haq') ?_
    simp only [Qle, add]; push_cast; omega
  -- product-Lipschitz : |q'·q' − a·a| ≤ ⟨3,1⟩·|q' − a|
  have hprodL : Qle (Qabs (Qsub (mul q' q') (mul (x.seq A) (x.seq A))))
      (mul (⟨3, 1⟩ : Q) (Qabs (Qsub q' (x.seq A)))) := by
    have hfac : Qeq (Qsub (mul q' q') (mul (x.seq A) (x.seq A)))
        (mul (Qsub q' (x.seq A)) (add q' (x.seq A))) := by
      simp only [Qeq, Qsub, mul, add, neg]; push_cast; ring_uor
    have heq1 : Qeq (Qabs (Qsub (mul q' q') (mul (x.seq A) (x.seq A))))
        (mul (Qabs (Qsub q' (x.seq A))) (Qabs (add q' (x.seq A)))) := by
      have h := Qabs_Qeq hfac; rw [Qabs_mul] at h; exact h
    have hsum : Qle (Qabs (add q' (x.seq A))) (⟨3, 1⟩ : Q) := by
      have ha1 : Qle (Qabs (add q' (x.seq A))) (add (Qabs q') (Qabs (x.seq A))) := Qabs_add_le q' _
      have ha2 : Qle (add (Qabs q') (Qabs (x.seq A))) (add (⟨1, 1⟩ : Q) (⟨2, 1⟩ : Q)) :=
        Qadd_le_add hq'1 ham
      have ha3 : Qle (add (⟨1, 1⟩ : Q) (⟨2, 1⟩ : Q)) (⟨3, 1⟩ : Q) := by decide
      exact Qle_trans (add_den_pos (Qabs_den_pos hq'd) (Qabs_den_pos had)) ha1
        (Qle_trans (add_den_pos (by decide) (by decide)) ha2 ha3)
    refine Qle_trans (Qmul_den_pos (Qabs_den_pos (Qsub_den_pos hq'd had))
        (Qabs_den_pos (add_den_pos hq'd had)))
      (Qeq_le heq1) ?_
    refine Qle_trans (Qmul_den_pos (Qabs_den_pos (Qsub_den_pos hq'd had)) (by decide))
      (Qmul_le_mul_left (Qabs_num_nonneg _) hsum) (Qeq_le (mul_comm _ _))
  -- 3·|q'²−a²| ≤ 3·(3·⟨1,9(j+1)⟩) = ⟨1,j+1⟩
  have hprod3 : Qle (mul (⟨3, 1⟩ : Q) (Qabs (Qsub (mul q' q') (mul (x.seq A) (x.seq A)))))
      (⟨1, j + 1⟩ : Q) := by
    have h1 : Qle (Qabs (Qsub (mul q' q') (mul (x.seq A) (x.seq A))))
        (mul (⟨3, 1⟩ : Q) (⟨1, 9 * (j + 1)⟩ : Q)) :=
      Qle_trans (Qmul_den_pos (by decide) (Qabs_den_pos (Qsub_den_pos hq'd had)))
        hprodL (Qmul_le_mul_left (by decide) hq'a)
    have h2 : Qle (mul (⟨3, 1⟩ : Q) (Qabs (Qsub (mul q' q') (mul (x.seq A) (x.seq A)))))
        (mul (⟨3, 1⟩ : Q) (mul (⟨3, 1⟩ : Q) (⟨1, 9 * (j + 1)⟩ : Q))) :=
      Qmul_le_mul_left (by decide) h1
    refine Qle_trans (Qmul_den_pos (by decide) (Qmul_den_pos (by decide) (Nat.succ_pos _)))
      h2 (Qeq_le ?_)
    simp only [Qeq, mul]; push_cast; ring_uor
  -- ============ ASSEMBLE ============
  have htri := Qabs_sub_triangle (a := altSum (x.seq R) off R) (b := altSum q' off R)
    (c := (⟨1, 1⟩ : Q)) (altSum_den_pos hqd off R) (altSum_den_pos hq'd off R) (by decide)
  have hstep1 : Qle (Qabs (Qsub (altSum (x.seq R) off R) (⟨1, 1⟩ : Q)))
      (add (⟨1, 2 * (j + 1)⟩ : Q) (mul (mul (Qabs q') (Qabs q')) (⟨3, 1⟩ : Q))) :=
    Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (altSum_den_pos hqd off R)
        (altSum_den_pos hq'd off R)))
        (Qabs_den_pos (Qsub_den_pos (altSum_den_pos hq'd off R) (by decide)))) htri
      (Qle_trans (add_den_pos (Nat.succ_pos _)
        (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hq'd) (Qabs_den_pos hq'd)) (by decide)))
        (Qadd_le_add hgap hquad) (Qle_refl _))
  -- mul (mul |q'| |q'|) ⟨3,1⟩ ≈ mul ⟨3,1⟩ (mul q' q')   (|q'|²=q'²)
  have hsqval : Qeq (mul (mul (Qabs q') (Qabs q')) (⟨3, 1⟩ : Q)) (mul (⟨3, 1⟩ : Q) (mul q' q')) := by
    have hge : Qeq (mul (Qabs q') (Qabs q')) (mul q' q') := by
      have hnum : (q'.num.natAbs : Int) * (q'.num.natAbs : Int) = q'.num * q'.num := by
        have := Int.natAbs_mul_self (a := q'.num); push_cast at this; omega
      simp only [Qeq, mul, Qabs]; push_cast; rw [hnum]
    refine Qeq_trans (Qmul_den_pos (Qmul_den_pos hq'd hq'd) (by decide))
      (Qmul_congr hge (Qeq_refl _)) ?_
    simp only [Qeq, mul]; push_cast; ring_uor
  -- 3·q'·q' ≤ 3·a·a + ⟨1,j+1⟩  (signed, from hprod3 via value-eq rearrangement)
  have h3le : Qle (mul (⟨3, 1⟩ : Q) (mul q' q'))
      (add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))) (⟨1, j + 1⟩ : Q)) := by
    have hdiff : Qle (Qsub (mul (⟨3, 1⟩ : Q) (mul q' q')) (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))))
        (⟨1, j + 1⟩ : Q) := by
      have hle : Qle (Qsub (mul (⟨3, 1⟩ : Q) (mul q' q'))
            (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))))
          (mul (⟨3, 1⟩ : Q) (Qabs (Qsub (mul q' q') (mul (x.seq A) (x.seq A))))) := by
        have he : Qeq (Qsub (mul (⟨3, 1⟩ : Q) (mul q' q'))
              (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))))
            (mul (⟨3, 1⟩ : Q) (Qsub (mul q' q') (mul (x.seq A) (x.seq A)))) := by
          simp only [Qeq, Qsub, mul, add, neg]; push_cast; ring_uor
        refine Qle_trans (Qmul_den_pos (by decide) (Qsub_den_pos (Qmul_den_pos hq'd hq'd)
          (Qmul_den_pos had had))) (Qeq_le he) ?_
        exact Qmul_le_mul_left (by decide) (Qle_self_Qabs _)
      exact Qle_trans (Qmul_den_pos (by decide) (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos hq'd hq'd)
        (Qmul_den_pos had had)))) hle hprod3
    -- 3q'² = 3a² + (3q'² − 3a²) ≤ 3a² + ⟨1,j+1⟩
    have hval : Qeq (mul (⟨3, 1⟩ : Q) (mul q' q'))
        (add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A)))
          (Qsub (mul (⟨3, 1⟩ : Q) (mul q' q')) (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))))) := by
      simp only [Qeq, Qsub, mul, add, neg]; push_cast; ring_uor
    refine Qle_trans (add_den_pos (Qmul_den_pos (by decide) (Qmul_den_pos had had))
        (Qsub_den_pos (Qmul_den_pos (by decide) (Qmul_den_pos hq'd hq'd))
          (Qmul_den_pos (by decide) (Qmul_den_pos had had)))) (Qeq_le hval) ?_
    exact Qadd_le_add (Qle_refl _) hdiff
  have hRHSbound : Qle (mul (mul (Qabs q') (Qabs q')) (⟨3, 1⟩ : Q))
      (add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))) (⟨1, j + 1⟩ : Q)) :=
    Qle_trans (Qmul_den_pos (by decide) (Qmul_den_pos hq'd hq'd))
      (Qeq_le hsqval) h3le
  refine Qle_trans (add_den_pos (Nat.succ_pos _) (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hq'd)
    (Qabs_den_pos hq'd)) (by decide))) hstep1 ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos _) (add_den_pos (Qmul_den_pos (by decide)
    (Qmul_den_pos had had)) (Nat.succ_pos _))) (Qadd_le_add (Qle_refl _) hRHSbound) ?_
  -- ⟨1,2(j+1)⟩ + (3a² + ⟨1,j+1⟩) = 3a² + (⟨1,2(j+1)⟩+⟨1,j+1⟩) ≤ 3a² + ⟨2,j+1⟩
  refine Qle_trans (b := add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A)))
      (add (⟨1, 2 * (j + 1)⟩ : Q) (⟨1, j + 1⟩ : Q)))
    (add_den_pos (Qmul_den_pos (by decide) (Qmul_den_pos had had))
      (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
    (Qeq_le (by simp only [Qeq, add, mul]; push_cast; ring_uor)) ?_
  refine Qadd_le_add (Qle_refl _) ?_
  -- 1/(2(j+1)) + 1/(j+1) = 3/(2(j+1)) ≤ 2/(j+1)
  simp only [Qle, add]; push_cast
  -- goal reduces to  3·(j+1)² ≤ 4·(j+1)²  with the product as an atom
  have key : (1 * ((j : Int) + 1) + 1 * (2 * ((j : Int) + 1))) * ((j : Int) + 1)
      = 3 * (((j : Int) + 1) * ((j : Int) + 1)) := by ring_uor
  have key2 : 2 * (2 * ((j : Int) + 1) * ((j : Int) + 1))
      = 4 * (((j : Int) + 1) * ((j : Int) + 1)) := by ring_uor
  rw [key, key2]
  have hsq : (0 : Int) ≤ ((j : Int) + 1) * ((j : Int) + 1) := Int.mul_nonneg (by omega) (by omega)
  omega

-- the deep product index A = Ridx x x (Ridx (ofQ⟨3,1⟩) (Rmul x x) (2j+1)) satisfies A+1 ≥ 36(j+1).
private theorem prodIdx_lb (x : Real) (j : Nat) :
    36 * (j + 1) ≤ Ridx x x (Ridx (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1)) + 1 := by
  have hM2 : 2 ≤ xBound x := by unfold xBound; have := x.den_pos 0; omega
  have hKxx : 2 ≤ RmulK x x := by unfold RmulK; omega
  have hKo : 5 ≤ RmulK (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) := by
    have hxo : xBound (ofQ (⟨3, 1⟩ : Q) (by decide)) = 5 := rfl
    have := Nat.le_max_left (xBound (ofQ (⟨3, 1⟩ : Q) (by decide))) (xBound (Rmul x x))
    unfold RmulK; omega
  rw [Ridx_succ x x (Ridx (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1))]
  rw [Ridx_succ (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1)]
  -- A+1 = 2·K(x,x)·(2·K'·(2j+2)) ≥ 2·2·(2·5·(2(j+1))) = 80(j+1)
  have h1 : 2 * 5 * (2 * j + 1 + 1) ≤ 2 * RmulK (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) * (2 * j + 1 + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hKo)
  have h2 : 2 * 2 * (2 * RmulK (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) * (2 * j + 1 + 1))
      ≤ 2 * RmulK x x * (2 * RmulK (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) * (2 * j + 1 + 1)) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hKxx)
  -- 2·2·(2·5·(2j+2)) = 80(j+1)
  omega

theorem RaltReal_upper_le {x : Real} {off : Nat} (hoff : fct off = 1)
    (hx1 : Rle x one) (hx2 : Rle (Rneg one) x) :
    Rle (RaltReal x off) (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x))) := by
  intro j
  have hA := prodIdx_lb x j
  -- (RaltReal x off).seq j = RaltReal_seq x off j ;  RHS.seq j = add ⟨1,1⟩ (mul ⟨3,1⟩ (a·a))
  show Qle (RaltReal_seq x off j)
    (add (add (⟨1, 1⟩ : Q)
      (mul (⟨3, 1⟩ : Q) (mul (x.seq (Ridx x x (Ridx (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1))))
        (x.seq (Ridx x x (Ridx (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1))))))) (⟨2, j + 1⟩ : Q))
  generalize hAdef : Ridx x x (Ridx (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1)) = A
    at hA ⊢
  have hcent := RaltReal_central hoff hx1 hx2 j hA
  -- from |RaltReal_seq − 1| ≤ 3a² + ⟨2,j+1⟩  get  RaltReal_seq ≤ 1 + (3a² + ⟨2,j+1⟩)
  have h := Qle_add_of_Qabs_sub
    (a := RaltReal_seq x off j) (b := (⟨1, 1⟩ : Q))
    (c := add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))) (⟨2, j + 1⟩ : Q))
    (altSum_den_pos (x.den_pos _) off _) (by decide)
    (add_den_pos (Qmul_den_pos (by decide) (Qmul_den_pos (x.den_pos _) (x.den_pos _)))
      (Nat.succ_pos _)) hcent
  refine Qle_trans (add_den_pos (by decide)
    (add_den_pos (Qmul_den_pos (by decide) (Qmul_den_pos (x.den_pos _) (x.den_pos _)))
      (Nat.succ_pos _))) h (Qeq_le ?_)
  simp only [Qeq, add, mul]; push_cast; ring_uor

theorem RaltReal_lower_ge {x : Real} {off : Nat} (hoff : fct off = 1)
    (hx1 : Rle x one) (hx2 : Rle (Rneg one) x) :
    Rle (Rsub one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x))) (RaltReal x off) := by
  intro j
  have hA := prodIdx_lb x j
  -- LHS.seq j = Qsub ⟨1,1⟩ (mul ⟨3,1⟩ (a·a)) ;  RHS.seq j = RaltReal_seq x off j
  show Qle (add (⟨1, 1⟩ : Q)
      (neg (mul (⟨3, 1⟩ : Q) (mul (x.seq (Ridx x x (Ridx (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1))))
        (x.seq (Ridx x x (Ridx (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1))))))))
    (add (RaltReal_seq x off j) (⟨2, j + 1⟩ : Q))
  generalize hAdef : Ridx x x (Ridx (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x) (2 * j + 1)) = A
    at hA ⊢
  have hcent := RaltReal_central hoff hx1 hx2 j hA
  have hRd : 0 < (RaltReal_seq x off j).den := (RaltReal x off).den_pos j
  -- from |RaltReal_seq − 1| ≤ 3a² + ⟨2,j+1⟩  get  1 − 3a² ≤ RaltReal_seq + ⟨2,j+1⟩
  -- i.e.  1 ≤ RaltReal_seq + (3a² + ⟨2,j+1⟩)  via the OTHER side of the abs.
  have hsub : Qle (Qabs (Qsub (⟨1, 1⟩ : Q) (RaltReal_seq x off j)))
      (add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))) (⟨2, j + 1⟩ : Q)) := by
    rw [Qabs_Qsub_comm]; exact hcent
  have h := Qle_add_of_Qabs_sub
    (a := (⟨1, 1⟩ : Q)) (b := RaltReal_seq x off j)
    (c := add (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A))) (⟨2, j + 1⟩ : Q))
    (by decide) hRd
    (add_den_pos (Qmul_den_pos (by decide) (Qmul_den_pos (x.den_pos A) (x.den_pos A)))
      (Nat.succ_pos _)) hsub
  -- h : 1 ≤ RaltReal_seq + (3a² + ⟨2,j+1⟩).  Add (neg 3a²) to both, cancel.
  have hstep := Qadd_le_add h (Qle_refl (neg (mul (⟨3, 1⟩ : Q) (mul (x.seq A) (x.seq A)))))
  -- hstep : add ⟨1,1⟩ (neg 3a²) ≤ add (add RaltReal (add 3a² ⟨2,j+1⟩)) (neg 3a²)
  --        and the RHS cancels to add RaltReal ⟨2,j+1⟩.
  exact Qle_congr_right (add_den_pos (add_den_pos hRd
      (add_den_pos (Qmul_den_pos (by decide) (Qmul_den_pos (x.den_pos A) (x.den_pos A)))
        (Nat.succ_pos _)))
      (neg_den_pos (Qmul_den_pos (by decide) (Qmul_den_pos (x.den_pos A) (x.den_pos A)))))
    (by simp only [Qeq, add, mul, neg]; push_cast; ring_uor) hstep

-- GOAL 3 (corollaries):
-- cos:  1 − cos x ≤ 3x²   (for x ∈ [−1,1])
theorem Rcos_one_sub_le_sq {x : Real} (hx1 : Rle x one) (hx2 : Rle (Rneg one) x) :
    Rle (Rsub one (Rcos x)) (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x)) := by
  -- from  1 − 3x² ≤ cos x   get   1 ≤ 3x² + cos x   get   1 − cos x ≤ 3x²
  have hG : Rle (Rsub one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x))) (Rcos x) :=
    RaltReal_lower_ge (by decide : fct 0 = 1) hx1 hx2
  exact Rsub_le_of_le_add' (Rle_add_of_Rsub_le' hG)

-- sin amplitude:  RsinAux x ≤ 1 + 3x²   and   1 − 3x² ≤ RsinAux x   (for x ∈ [−1,1])
theorem RsinAux_upper_le {x : Real} (hx1 : Rle x one) (hx2 : Rle (Rneg one) x) :
    Rle (RsinAux x) (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x))) := by
  unfold RsinAux
  exact RaltReal_upper_le (by decide) hx1 hx2

theorem RsinAux_lower_ge {x : Real} (hx1 : Rle x one) (hx2 : Rle (Rneg one) x) :
    Rle (Rsub one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul x x))) (RsinAux x) := by
  unfold RsinAux
  exact RaltReal_lower_ge (by decide) hx1 hx2


-- ===========================================================================
-- The RlogNat ↔ logN bridge: RlogNat n (used by deltaLogNat/cpowNeg) equals logN n (used by
-- deltaLog_upper/ComplexZeta). Via exp(RlogNat n) ≈ n (RlogNat's TwoArtanhConst form is rfl,
-- then Rexp_two_artanh_ofQ) + RexpReal_inj with Rexp_logN. Converts the cpowNeg component bounds
-- e^{−σ·RlogNat n} into the genuine n^{−σ} decay and transfers deltaLog_upper for the δ_n bound.
-- ===========================================================================

-- BRIDGE: RlogNat n (= RlogPos (RofNat n) 0, used by deltaLogNat / cpowNeg) equals logN n
-- (= Rlog (ofQ⟨n,1⟩) ⟨n,1⟩ …, used by deltaLog_upper / ComplexZeta).  Both are "log n".
-- Route: prove exp(RlogNat n) ≈ n (GOAL 1), then RexpReal_inj with Rexp_logN gives the bridge (GOAL 2).
--
-- Facts found in the codebase (verify against source):
--  · RlogNat n hn := RlogPos (RofNat n) 0 (proof)   [ComplexPow.lean:19],  RofNat n = ofQ⟨n,1⟩ [ComplexPow:16]
--  · RlogPos x k hk := Rlog ⟨reindexed x, …⟩ (M = |x₀|+2 + 1/L) …   [Log.lean:1069] — value-seq is
--    Rmul(ofQ⟨2,1⟩)(Rartanh ⟨Rlog_seq (reindexed x), …⟩ ρ' …),  Rlog_seq y j = tmap(y.seq (2(j+1))) [Log:883].
--    For y = reindexed (RofNat n): y.seq k = ⟨n,1⟩ (constant), so Rlog_seq y j = tmap⟨n,1⟩ (constant).
--  · TwoArtanhConst τ ρ … := Rmul (ofQ⟨2,1⟩) (RartanhConst τ ρ …)   [ExpLog:4979];  RartanhConst τ ρ is the
--    constant-argument Rartanh (seq = artSum τ …).  So RlogNat n ≈ TwoArtanhConst (tmap⟨n,1⟩) ρ' … (identical
--    Rartanh seqs: both artSum (tmap⟨n,1⟩) …, since (ofQ τ).seq = ⟨reindexed RofNat n⟩.seq = const τ).
--  · Rexp_two_artanh_ofQ (τ ρ g K …) : exp(TwoArtanhConst τ ρ …) ≈ ofQ g  [ExpLog:4989] — ρ-GENERAL.
--    g satisfies g·(1−τ)=(1+τ); for τ = tmap⟨n,1⟩ = (n−1)/(n+1) this gives g = n.  Rexp_log_nat_Rlog
--    [ExpLog:5070] already supplies concrete (g,K,M',L,C,hBC) for exactly this τ — MIRROR its argument values.
--  · Rexp_logN n : exp(logN n) ≈ ofQ⟨n,1⟩  [RealPow:2723].  RexpReal_inj (hX:Rnonneg X)(hY)(exp X≈exp Y):X≈Y
--    [RealPow:2678].  Rnonneg_logN [RealPow:2726].  Rnonneg_RartanhConst [GammaOne:270] → Rnonneg (RlogNat n).
--  · tmap_nat_num/tmap_nat_den give tmap⟨n,1⟩ = ⟨n−1, n+1⟩.

theorem Rexp_RlogNat (n : Nat) (hn : 2 ≤ n) :
    Req (RexpReal (RlogNat n hn)) (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) := by
  have hτd : 0 < (tmap (⟨(n : Int), 1⟩ : Q)).den := by rw [tmap_nat_den n]; omega
  have hτ0 : 0 ≤ (tmap (⟨(n : Int), 1⟩ : Q)).num := by rw [tmap_nat_num n]; omega
  have hτlt : (tmap (⟨(n : Int), 1⟩ : Q)).num.toNat < (tmap (⟨(n : Int), 1⟩ : Q)).den := by
    rw [tmap_nat_num n, tmap_nat_den n]; omega
  have h2 : (2 : Int) ≤ (n : Int) := by exact_mod_cast hn
  have hsq : (n : Int) * 2 ≤ (n : Int) * (n : Int) := Int.mul_le_mul_of_nonneg_left h2 (by omega)
  have htn : (((n : Int) * 1 + -1).toNat : Int) = (n : Int) - 1 := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  -- the RlogPos-derived modulus M' and its derived artanh radius ρ'
  let M' : Q := add (add (Qabs ((ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos).seq 0)) ⟨2, 1⟩)
    (Qinv (RL (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 0))
  -- closed forms for the modulus M' = (n²+n)/(n−1)
  have hM'n : M'.num = (n : Int) * (n : Int) + (n : Int) := by
    show (((n : Int) * 1 + 2 * 1) * ((Qinv (RL (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 0)).den : Int)
       + (Qinv (RL (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 0)).num * 1) = (n : Int) * (n : Int) + (n : Int)
    simp only [Qinv, RL, Rdelta, Qsub, add, neg, Qbound, ofQ, Qabs]
    push_cast [htn]; ring_uor
  have hM'd : M'.den = n - 1 := by
    show (1 * (Qinv (RL (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 0)).den) = n - 1
    simp only [Qinv, RL, Rdelta, Qsub, add, neg, Qbound, ofQ, Qabs]
    omega
  -- the derived radius ρ' = (M'.num − M'.den)/(M'.num.toNat + M'.den)
  have htoNatNum : (M'.num.toNat : Int) = (n : Int) * (n : Int) + (n : Int) := by
    rw [hM'n]; rw [Int.toNat_of_nonneg (by omega)]
  have hρ0 : 0 ≤ (⟨M'.num - (M'.den : Int), M'.num.toNat + M'.den⟩ : Q).num := by
    show (0 : Int) ≤ M'.num - (M'.den : Int); rw [hM'n, hM'd]; push_cast; omega
  have hρd : 0 < (⟨M'.num - (M'.den : Int), M'.num.toNat + M'.den⟩ : Q).den := by
    show 0 < M'.num.toNat + M'.den
    have : 0 < M'.num.toNat := by
      have := htoNatNum; omega
    omega
  have hρlt : (⟨M'.num - (M'.den : Int), M'.num.toNat + M'.den⟩ : Q).num.toNat
      < (⟨M'.num - (M'.den : Int), M'.num.toNat + M'.den⟩ : Q).den := by
    show (M'.num - (M'.den : Int)).toNat < M'.num.toNat + M'.den
    have e1 : ((M'.num - (M'.den : Int)).toNat : Int) = M'.num - (M'.den : Int) :=
      Int.toNat_of_nonneg hρ0
    have : ((M'.num - (M'.den : Int)).toNat : Int) < ((M'.num.toNat + M'.den : Nat) : Int) := by
      rw [e1, hM'd]; push_cast [htoNatNum]; omega
    exact_mod_cast this
  have hb : Qle (Qabs (tmap (⟨(n : Int), 1⟩ : Q)))
      (⟨M'.num - (M'.den : Int), M'.num.toNat + M'.den⟩ : Q) := by
    have habs : Qeq (Qabs (tmap (⟨(n : Int), 1⟩ : Q))) (tmap (⟨(n : Int), 1⟩ : Q)) :=
      Qabs_of_nonneg hτ0
    refine Qle_trans hτd (Qeq_le habs) ?_
    show (tmap (⟨(n : Int), 1⟩ : Q)).num * ((M'.num.toNat + M'.den : Nat) : Int)
       ≤ (M'.num - (M'.den : Int)) * ((tmap (⟨(n : Int), 1⟩ : Q)).den : Int)
    rw [tmap_nat_num n, tmap_nat_den n, hM'n, hM'd]
    have hcast : (((n : Int) * (n : Int) + (n : Int)).toNat : Int) = (n : Int) * (n : Int) + (n : Int) :=
      Int.toNat_of_nonneg (by omega)
    have hd1 : ((n - 1 : Nat) : Int) = (n : Int) - 1 := by omega
    have hdiff : ((n : Int) * (n : Int) + (n : Int) - ((n : Int) - 1)) * ((n : Int) + 1)
        - ((n : Int) - 1) * ((((n : Int) * (n : Int) + (n : Int)).toNat : Int) + ((n - 1 : Nat) : Int))
        = 4 * (n : Int) := by rw [hcast, hd1]; ring_uor
    push_cast [hcast, hd1] at hdiff ⊢
    omega
  have hbridge : RlogNat n hn = TwoArtanhConst (tmap (⟨(n : Int), 1⟩ : Q))
      (⟨M'.num - (M'.den : Int), M'.num.toNat + M'.den⟩ : Q)
      hτd hρ0 hρd hρlt hb := rfl
  rw [hbridge]
  refine Rexp_two_artanh_ofQ (tmap (⟨(n : Int), 1⟩ : Q))
    (⟨M'.num - (M'.den : Int), M'.num.toNat + M'.den⟩ : Q) ⟨(n : Int), 1⟩ ⟨(n : Int) + 1, 2⟩
    (n + 1) ((expM_U (n + 1) (2 * (n + 1))).num.toNat)
    ((n + 1) * (n + 1) * ((expM_U (n + 1) (2 * (n + 1))).num.toNat + 2))
    hτd hτ0 ?_ hτlt hρ0 hρd hρlt hb Nat.one_pos ?_ (by decide : (0:Nat) < 2) ?_ ?_ rfl ?_ ?_
  · simp only [Qle]; rw [tmap_nat_num n, tmap_nat_den n]; push_cast; omega
  · simp only [Qeq, mul, Qsub, add, neg]; rw [tmap_nat_num n, tmap_nat_den n]; push_cast; ring_uor
  · simp only [Qle]; push_cast; omega
  · refine Qeq_le ?_
    simp only [Qeq, mul, Qsub, add, neg]; rw [tmap_nat_num n, tmap_nat_den n]; push_cast; ring_uor
  · simp only [Qle, mul]; push_cast; omega
  · intro j; refine Qeq_le ?_
    simp only [Qeq, add, mul]; rw [tmap_nat_den n]; push_cast; ring_uor

theorem Rnonneg_RlogNat (n : Nat) (hn : 2 ≤ n) : Rnonneg (RlogNat n hn) := by
  have hτd : 0 < (tmap (⟨(n : Int), 1⟩ : Q)).den := by rw [tmap_nat_den n]; omega
  have hτ0 : 0 ≤ (tmap (⟨(n : Int), 1⟩ : Q)).num := by rw [tmap_nat_num n]; omega
  have h2 : (2 : Int) ≤ (n : Int) := by exact_mod_cast hn
  have hsq : (n : Int) * 2 ≤ (n : Int) * (n : Int) := Int.mul_le_mul_of_nonneg_left h2 (by omega)
  have htn : (((n : Int) * 1 + -1).toNat : Int) = (n : Int) - 1 := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  let M' : Q := add (add (Qabs ((ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos).seq 0)) ⟨2, 1⟩)
    (Qinv (RL (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 0))
  have hM'n : M'.num = (n : Int) * (n : Int) + (n : Int) := by
    show (((n : Int) * 1 + 2 * 1) * ((Qinv (RL (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 0)).den : Int)
       + (Qinv (RL (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 0)).num * 1) = (n : Int) * (n : Int) + (n : Int)
    simp only [Qinv, RL, Rdelta, Qsub, add, neg, Qbound, ofQ, Qabs]
    push_cast [htn]; ring_uor
  have hM'd : M'.den = n - 1 := by
    show (1 * (Qinv (RL (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 0)).den) = n - 1
    simp only [Qinv, RL, Rdelta, Qsub, add, neg, Qbound, ofQ, Qabs]
    omega
  have htoNatNum : (M'.num.toNat : Int) = (n : Int) * (n : Int) + (n : Int) := by
    rw [hM'n]; rw [Int.toNat_of_nonneg (by omega)]
  have hρ0 : 0 ≤ (⟨M'.num - (M'.den : Int), M'.num.toNat + M'.den⟩ : Q).num := by
    show (0 : Int) ≤ M'.num - (M'.den : Int); rw [hM'n, hM'd]; push_cast; omega
  have hρd : 0 < (⟨M'.num - (M'.den : Int), M'.num.toNat + M'.den⟩ : Q).den := by
    show 0 < M'.num.toNat + M'.den
    have : 0 < M'.num.toNat := by have := htoNatNum; omega
    omega
  have hρlt : (⟨M'.num - (M'.den : Int), M'.num.toNat + M'.den⟩ : Q).num.toNat
      < (⟨M'.num - (M'.den : Int), M'.num.toNat + M'.den⟩ : Q).den := by
    show (M'.num - (M'.den : Int)).toNat < M'.num.toNat + M'.den
    have e1 : ((M'.num - (M'.den : Int)).toNat : Int) = M'.num - (M'.den : Int) :=
      Int.toNat_of_nonneg hρ0
    have : ((M'.num - (M'.den : Int)).toNat : Int) < ((M'.num.toNat + M'.den : Nat) : Int) := by
      rw [e1, hM'd]; push_cast [htoNatNum]; omega
    exact_mod_cast this
  have hb : Qle (Qabs (tmap (⟨(n : Int), 1⟩ : Q)))
      (⟨M'.num - (M'.den : Int), M'.num.toNat + M'.den⟩ : Q) := by
    have habs : Qeq (Qabs (tmap (⟨(n : Int), 1⟩ : Q))) (tmap (⟨(n : Int), 1⟩ : Q)) :=
      Qabs_of_nonneg hτ0
    refine Qle_trans hτd (Qeq_le habs) ?_
    show (tmap (⟨(n : Int), 1⟩ : Q)).num * ((M'.num.toNat + M'.den : Nat) : Int)
       ≤ (M'.num - (M'.den : Int)) * ((tmap (⟨(n : Int), 1⟩ : Q)).den : Int)
    rw [tmap_nat_num n, tmap_nat_den n, hM'n, hM'd]
    have hcast : (((n : Int) * (n : Int) + (n : Int)).toNat : Int) = (n : Int) * (n : Int) + (n : Int) :=
      Int.toNat_of_nonneg (by omega)
    have hd1 : ((n - 1 : Nat) : Int) = (n : Int) - 1 := by omega
    have hdiff : ((n : Int) * (n : Int) + (n : Int) - ((n : Int) - 1)) * ((n : Int) + 1)
        - ((n : Int) - 1) * ((((n : Int) * (n : Int) + (n : Int)).toNat : Int) + ((n - 1 : Nat) : Int))
        = 4 * (n : Int) := by rw [hcast, hd1]; ring_uor
    push_cast [hcast, hd1] at hdiff ⊢
    omega
  have hbridge : RlogNat n hn = TwoArtanhConst (tmap (⟨(n : Int), 1⟩ : Q))
      (⟨M'.num - (M'.den : Int), M'.num.toNat + M'.den⟩ : Q)
      hτd hρ0 hρd hρlt hb := rfl
  rw [hbridge]
  have hartnn : Rnonneg (RartanhConst (tmap (⟨(n : Int), 1⟩ : Q))
      (⟨M'.num - (M'.den : Int), M'.num.toNat + M'.den⟩ : Q) hτd hρ0 hρd hρlt hb) := by
    intro k
    show Qle (neg (Qbound k)) (artSum (tmap (⟨(n : Int), 1⟩ : Q))
      (Rartanh_R (⟨M'.num - (M'.den : Int), M'.num.toNat + M'.den⟩ : Q) k))
    have hnum : 0 ≤ (artSum (tmap (⟨(n : Int), 1⟩ : Q))
        (Rartanh_R (⟨M'.num - (M'.den : Int), M'.num.toNat + M'.den⟩ : Q) k)).num :=
      artSum_nonneg hτ0 hτd _
    have hpp : (0 : Int) ≤ (artSum (tmap (⟨(n : Int), 1⟩ : Q))
        (Rartanh_R (⟨M'.num - (M'.den : Int), M'.num.toNat + M'.den⟩ : Q) k)).num * ((k : Int) + 1) :=
      Int.mul_nonneg hnum (by omega)
    simp only [Qle, neg, Qbound]; push_cast; omega
  exact Rnonneg_Rmul (Rnonneg_ofQ (by decide) (by show (0 : Int) ≤ 2; decide)) hartnn

theorem RlogNat_eq_logN (n : Nat) (hn : 2 ≤ n) :
    Req (RlogNat n hn) (logN n (by omega)) :=
  RexpReal_inj (Rnonneg_RlogNat n hn) (Rnonneg_logN n (by omega))
    (Req_trans (Rexp_RlogNat n hn) (Req_symm (Rexp_logN n (by omega))))

-- ===========================================================================
-- The consecutive-log gap bounds 0 ≤ δ_n ≤ 1/n (δ_n = deltaLogNat n = log(n+1) − log n), transferring
-- the logN facts (deltaLog_upper, logN_mono) through the RlogNat ↔ logN bridge. These give the δ_n → 0
-- decay that makes the per-term η variation summable (n^{−σ}·δ_n ~ n^{−σ−1}).
-- ===========================================================================

/-- **`δ_n ≥ 0`**: `log(n+1) − log n ≥ 0` (log is monotone), via the bridge + `logN_mono`. -/
theorem Rnonneg_deltaLogNat (n : Nat) (hn : 2 ≤ n) : Rnonneg (deltaLogNat n hn) := by
  have hle : Rle (RlogNat n hn) (RlogNat (n + 1) (by omega)) :=
    Rle_trans (Rle_of_Req (RlogNat_eq_logN n hn))
      (Rle_trans (logN_mono (by omega : 1 ≤ n) (Nat.le_succ n))
        (Rle_of_Req (Req_symm (RlogNat_eq_logN (n + 1) (by omega)))))
  exact Rnonneg_Rsub_of_Rle hle

/-- **`δ_n ≤ 1/n`**: transfers `deltaLog_upper` (`logN(p+1) − logN p ≤ 1/p`) via the bridge. -/
theorem deltaLogNat_le_recip (n : Nat) (hn : 2 ≤ n) :
    Rle (deltaLogNat n hn) (ofQ (⟨1, n⟩ : Q) (show 0 < n by omega)) := by
  have hRw : Req (deltaLogNat n hn) (Rsub (logN (n + 1) (by omega)) (logN n (by omega))) :=
    Rsub_congr (RlogNat_eq_logN (n + 1) (by omega)) (RlogNat_eq_logN n hn)
  exact Rle_trans (Rle_of_Req hRw) (deltaLog_upper n (by omega))


-- ===========================================================================
-- The two-sided product bound (no real-abs): −A≤x≤A, −B≤y≤B ⟹ −AB ≤ xy ≤ AB. Constructive,
-- case-split-free, via 2(AB∓xy) = (A−x)(B±y) + (A+x)(B∓y) (sums of nonneg products) + the ½ collapse.
-- The keystone for bounding the per-term η variation Re/Im(n⁻ˢ·(1−e^{−s·δ_n})) two-sided.
-- ===========================================================================

-- The two-sided product bound (no real-abs): if |x| ≤ A and |y| ≤ B (A,B ≥ 0), then |xy| ≤ AB.
-- Constructive identity (NO case split):  2(AB − xy) = (A−x)(B+y) + (A+x)(B−y)  [each factor ≥ 0],
-- and  2(AB + xy) = (A−x)(B−y) + (A+x)(B+y).  So AB − xy ≥ 0 and AB + xy ≥ 0.

-- An additive-only normal form: ((D + E) + (D − E)) ≈ D + D.
-- Proven via the structure-preserving middle-four swap, so reindexing matches.
private theorem Radd_add_sub_self (D E : Real) :
    Req (Radd (Radd D E) (Rsub D E)) (Radd D D) :=
  -- Rsub D E ≡ Radd D (Rneg E) (defeq), so Radd_swap applies.
  Req_trans (Radd_swap D E D (Rneg E))
    (Req_trans (Radd_congr (Req_refl (Radd D D)) (Radd_neg E)) (Radd_zero (Radd D D)))

private theorem Radd_sub_add_self (D E : Real) :
    Req (Radd (Rsub D E) (Radd D E)) (Radd D D) :=
  -- Rsub D E ≡ Radd D (Rneg E), so this is Radd (Radd D (Rneg E)) (Radd D E).
  Req_trans (Radd_swap D (Rneg E) D E)
    (Req_trans (Radd_congr (Req_refl (Radd D D))
        (Req_trans (Radd_comm (Rneg E) E) (Radd_neg E)))
      (Radd_zero (Radd D D)))

-- (A−x)(B+y) ≈ (AB − xy) + (Ay − xB).
private theorem expand_minus_plus (A x B y : Real) :
    Req (Rmul (Rsub A x) (Radd B y))
        (Radd (Rsub (Rmul A B) (Rmul x y)) (Rsub (Rmul A y) (Rmul x B))) := by
  -- (A−x)(B+y) = A(B+y) − x(B+y) = (AB + Ay) − (xB + xy)
  refine Req_trans (Rmul_sub_distrib_right A x (Radd B y)) ?_
  refine Req_trans (Rsub_congr (Rmul_distrib A B y) (Rmul_distrib x B y)) ?_
  -- (AB + Ay) − (xB + xy) ≈ (AB − xy) + (Ay − xB)  : additive rearrangement
  apply Req_of_seq_Qeq
  intro n
  simp only [Rsub, Radd, Rneg, Qeq, add, neg]; push_cast; ring_uor

-- (A+x)(B−y) ≈ (AB − xy) − (Ay − xB).
private theorem expand_plus_minus (A x B y : Real) :
    Req (Rmul (Radd A x) (Rsub B y))
        (Rsub (Rsub (Rmul A B) (Rmul x y)) (Rsub (Rmul A y) (Rmul x B))) := by
  -- (A+x)(B−y) = A(B−y) + x(B−y) = (AB − Ay) + (xB − xy)
  refine Req_trans (Rmul_distrib_right A x (Rsub B y)) ?_
  refine Req_trans (Radd_congr (Rmul_sub_distrib A B y) (Rmul_sub_distrib x B y)) ?_
  -- (AB − Ay) + (xB − xy) ≈ (AB − xy) − (Ay − xB)  : additive rearrangement
  apply Req_of_seq_Qeq
  intro n
  simp only [Rsub, Radd, Rneg, Qeq, add, neg]; push_cast; ring_uor

-- (A−x)(B−y) ≈ (AB + xy) − (Ay + xB).
private theorem expand_minus_minus (A x B y : Real) :
    Req (Rmul (Rsub A x) (Rsub B y))
        (Rsub (Radd (Rmul A B) (Rmul x y)) (Radd (Rmul A y) (Rmul x B))) := by
  refine Req_trans (Rmul_sub_distrib_right A x (Rsub B y)) ?_
  refine Req_trans (Rsub_congr (Rmul_sub_distrib A B y) (Rmul_sub_distrib x B y)) ?_
  apply Req_of_seq_Qeq
  intro n
  simp only [Rsub, Radd, Rneg, Qeq, add, neg]; push_cast; ring_uor

-- (A+x)(B+y) ≈ (AB + xy) + (Ay + xB).
private theorem expand_plus_plus (A x B y : Real) :
    Req (Rmul (Radd A x) (Radd B y))
        (Radd (Radd (Rmul A B) (Rmul x y)) (Radd (Rmul A y) (Rmul x B))) := by
  refine Req_trans (Rmul_distrib_right A x (Radd B y)) ?_
  refine Req_trans (Radd_congr (Rmul_distrib A B y) (Rmul_distrib x B y)) ?_
  apply Req_of_seq_Qeq
  intro n
  simp only [Rsub, Radd, Rneg, Qeq, add, neg]; push_cast; ring_uor

-- y − (−B) ≈ B + y  (additive, pointwise).
private theorem Rsub_neg_eq_add (B y : Real) :
    Req (Rsub y (Rneg B)) (Radd B y) := by
  apply Req_of_seq_Qeq
  intro n
  simp only [Rsub, Radd, Rneg, Qeq, add, neg]; push_cast; ring_uor

theorem Rmul_le_mul_of_abs {x y A B : Real}
    (hx1 : Rle (Rneg A) x) (hx2 : Rle x A) (hy1 : Rle (Rneg B) y) (hy2 : Rle y B) :
    Rle (Rmul x y) (Rmul A B) := by
  -- Four non-negative factors.
  have hAx : Rnonneg (Rsub A x) := Rnonneg_Rsub_of_Rle hx2
  have hBy : Rnonneg (Radd B y) :=
    Rnonneg_congr (Rsub_neg_eq_add B y) (Rnonneg_Rsub_of_Rle hy1)
  have hAx2 : Rnonneg (Radd A x) :=
    Rnonneg_congr (Rsub_neg_eq_add A x) (Rnonneg_Rsub_of_Rle hx1)
  have hBy2 : Rnonneg (Rsub B y) := Rnonneg_Rsub_of_Rle hy2
  -- P = (A−x)(B+y) ≥ 0,  Q = (A+x)(B−y) ≥ 0.
  have hP : Rnonneg (Rmul (Rsub A x) (Radd B y)) := Rnonneg_Rmul hAx hBy
  have hQ : Rnonneg (Rmul (Radd A x) (Rsub B y)) := Rnonneg_Rmul hAx2 hBy2
  -- D := AB − xy ;  E := Ay − xB.  P ≈ D+E, Q ≈ D−E, so P+Q ≈ (D+E)+(D−E) ≈ D+D.
  have hPQ : Rnonneg (Radd (Rmul (Rsub A x) (Radd B y)) (Rmul (Radd A x) (Rsub B y))) :=
    Rnonneg_Radd hP hQ
  have hsum : Req (Radd (Rmul (Rsub A x) (Radd B y)) (Rmul (Radd A x) (Rsub B y)))
      (Radd (Rsub (Rmul A B) (Rmul x y)) (Rsub (Rmul A B) (Rmul x y))) :=
    Req_trans (Radd_congr (expand_minus_plus A x B y) (expand_plus_minus A x B y))
      (Radd_add_sub_self (Rsub (Rmul A B) (Rmul x y)) (Rsub (Rmul A y) (Rmul x B)))
  -- D+D ≥ 0  ⟹  half ≥ 0  ⟹  D ≥ 0.
  have hDD : Rnonneg (Radd (Rsub (Rmul A B) (Rmul x y)) (Rsub (Rmul A B) (Rmul x y))) :=
    Rnonneg_congr hsum hPQ
  have hD : Rnonneg (Rsub (Rmul A B) (Rmul x y)) :=
    Rnonneg_congr
      (Req_trans (Rhalf_Radd (Rsub (Rmul A B) (Rmul x y)) (Rsub (Rmul A B) (Rmul x y)))
        (Rhalf_double (Rsub (Rmul A B) (Rmul x y))))
      (Rhalf_nonneg hDD)
  exact Rle_of_Rnonneg_Rsub hD

-- xy − (−AB) ≈ AB + xy  (additive, pointwise).
private theorem Rsub_neg_mul_eq (A B x y : Real) :
    Req (Rsub (Rmul x y) (Rneg (Rmul A B))) (Radd (Rmul A B) (Rmul x y)) := by
  apply Req_of_seq_Qeq
  intro n
  simp only [Rsub, Radd, Rneg, Qeq, add, neg]; push_cast; ring_uor

theorem Rneg_mul_le_of_abs {x y A B : Real}
    (hx1 : Rle (Rneg A) x) (hx2 : Rle x A) (hy1 : Rle (Rneg B) y) (hy2 : Rle y B) :
    Rle (Rneg (Rmul A B)) (Rmul x y) := by
  -- Four non-negative factors.
  have hAx : Rnonneg (Rsub A x) := Rnonneg_Rsub_of_Rle hx2
  have hBy : Rnonneg (Radd B y) :=
    Rnonneg_congr (Rsub_neg_eq_add B y) (Rnonneg_Rsub_of_Rle hy1)
  have hAx2 : Rnonneg (Radd A x) :=
    Rnonneg_congr (Rsub_neg_eq_add A x) (Rnonneg_Rsub_of_Rle hx1)
  have hBy2 : Rnonneg (Rsub B y) := Rnonneg_Rsub_of_Rle hy2
  -- P = (A−x)(B−y) ≥ 0,  Q = (A+x)(B+y) ≥ 0.
  have hP : Rnonneg (Rmul (Rsub A x) (Rsub B y)) := Rnonneg_Rmul hAx hBy2
  have hQ : Rnonneg (Rmul (Radd A x) (Radd B y)) := Rnonneg_Rmul hAx2 hBy
  have hPQ : Rnonneg (Radd (Rmul (Rsub A x) (Rsub B y)) (Rmul (Radd A x) (Radd B y))) :=
    Rnonneg_Radd hP hQ
  -- D := AB + xy ;  E := Ay + xB.  P ≈ D−E, Q ≈ D+E, so P+Q ≈ (D−E)+(D+E) ≈ D+D.
  have hsum : Req (Radd (Rmul (Rsub A x) (Rsub B y)) (Rmul (Radd A x) (Radd B y)))
      (Radd (Radd (Rmul A B) (Rmul x y)) (Radd (Rmul A B) (Rmul x y))) :=
    Req_trans (Radd_congr (expand_minus_minus A x B y) (expand_plus_plus A x B y))
      (Radd_sub_add_self (Radd (Rmul A B) (Rmul x y)) (Radd (Rmul A y) (Rmul x B)))
  have hDD : Rnonneg (Radd (Radd (Rmul A B) (Rmul x y)) (Radd (Rmul A B) (Rmul x y))) :=
    Rnonneg_congr hsum hPQ
  have hD : Rnonneg (Radd (Rmul A B) (Rmul x y)) :=
    Rnonneg_congr
      (Req_trans (Rhalf_Radd (Radd (Rmul A B) (Rmul x y)) (Radd (Rmul A B) (Rmul x y)))
        (Rhalf_double (Radd (Rmul A B) (Rmul x y))))
      (Rhalf_nonneg hDD)
  -- AB + xy ≥ 0  ⟹  xy − (−AB) ≥ 0  ⟹  −AB ≤ xy.
  exact Rle_of_Rnonneg_Rsub (Rnonneg_congr (Req_symm (Rsub_neg_mul_eq A B x y)) hD)


-- ===========================================================================
-- Two-sided component bounds for u = Cone − Cexp ⟨Rneg d, b⟩ (d∈[0,1/2], b∈[−1,1]): u.re ∈ [0, 4d+3b²]
-- and |u.im| ≤ (1+3b²)·Bb for −Bb≤b≤Bb. Assembles the tight exp/cos/sin bounds + the two-sided product
-- keystone. The (1−e^{−s·δ_n}) factor of the per-term η variation D_n = n⁻ˢ·(1−e^{−s·δ_n}).
-- ===========================================================================

-- Two-sided component bounds for u = Cone − Cexp ⟨Rneg d, b⟩  (a = Rneg d ≤ 0, b the imaginary arg):
--   u.re = Rsub one (Rmul (RexpReal (Rneg d)) (Rcos b))
--   u.im = Rneg (Rmul (RexpReal (Rneg d)) (Rsin b))
-- These feed the per-term η variation bound. All inputs are committed in EtaVariation:
--   RexpReal_one_sub_neg_le : 1 − e^{−d} ≤ 4d   (d ∈ [0,1/2])
--   RexpReal_neg_le_one     : e^{−d} ≤ 1        (d ≥ 0)
--   RexpReal_nonneg         : 0 ≤ e^{−d}
--   Rcos_le_one             : Rcos b ≤ 1
--   Rcos_one_sub_le_sq      : 1 − Rcos b ≤ 3b²   (b ∈ [−1,1])
--   RsinAux_upper_le/lower_ge : RsinAux b ∈ [1−3b², 1+3b²]  (b ∈ [−1,1]);  Rsin b = Rmul b (RsinAux b)
--   Rmul_le_mul_of_abs / Rneg_mul_le_of_abs : two-sided product bound (the keystone)
--   Rmul_le_Rmul_left/right, Rmul_one, Rmul_sub_distrib, Rmul_neg_left/right, Radd/Rsub congruences.

-- Additive regrouping helper: (1 − E) + (E − M) ≈ 1 − M  (pointwise in leaf terms one, E, M).
private theorem oneSubCexp_regroup (E M : Real) :
    Req (Radd (Rsub one E) (Rsub E M)) (Rsub one M) := by
  -- (1 + (−E)) + (E + (−M)) ≈ 1 + ((−E) + (E + (−M)))
  refine Req_trans (Radd_assoc one (Rneg E) (Radd E (Rneg M))) ?_
  -- inner: (−E) + (E + (−M)) ≈ ((−E) + E) + (−M) ≈ 0 + (−M) ≈ (−M)
  refine Radd_congr (Req_refl one) ?_
  refine Req_trans (Req_symm (Radd_assoc (Rneg E) E (Rneg M))) ?_
  have hcancel : Req (Radd (Rneg E) E) zero :=
    Req_trans (Radd_comm (Rneg E) E) (Radd_neg E)
  refine Req_trans (Radd_congr hcancel (Req_refl (Rneg M))) ?_
  exact Req_trans (Radd_comm zero (Rneg M)) (Radd_zero (Rneg M))

-- u.re ≤ 4d + 3b²   (decompose 1 − e^{−d}cos b = (1−e^{−d}) + e^{−d}(1−cos b) ≤ 4d + 1·3b²).
theorem oneSubCexp_re_upper {d b : Real} (hd0 : Rnonneg d)
    (hd1 : Rle d (ofQ (⟨1, 2⟩ : Q) (by decide)))
    (hb1 : Rle (Rneg one) b) (hb2 : Rle b one) :
    Rle (Rsub one (Rmul (RexpReal (Rneg d)) (Rcos b)))
        (Radd (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) d)
              (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b))) := by
  -- 1 − C ≥ 0
  have hCnn : Rnonneg (Rsub one (Rcos b)) := Rnonneg_Rsub_of_Rle (Rcos_le_one b)
  -- decomposition: 1 − E·C ≈ (1 − E) + E·(1 − C)
  have hdecomp : Req (Rsub one (Rmul (RexpReal (Rneg d)) (Rcos b)))
      (Radd (Rsub one (RexpReal (Rneg d)))
            (Rmul (RexpReal (Rneg d)) (Rsub one (Rcos b)))) := by
    have hdist : Req (Rmul (RexpReal (Rneg d)) (Rsub one (Rcos b)))
        (Rsub (RexpReal (Rneg d)) (Rmul (RexpReal (Rneg d)) (Rcos b))) :=
      Req_trans (Rmul_sub_distrib (RexpReal (Rneg d)) one (Rcos b))
        (Rsub_congr (Rmul_one (RexpReal (Rneg d)))
          (Req_refl (Rmul (RexpReal (Rneg d)) (Rcos b))))
    refine Req_symm ?_
    exact Req_trans
      (Radd_congr (Req_refl (Rsub one (RexpReal (Rneg d)))) hdist)
      (oneSubCexp_regroup (RexpReal (Rneg d)) (Rmul (RexpReal (Rneg d)) (Rcos b)))
  -- (1 − E) ≤ 4d
  have h1 : Rle (Rsub one (RexpReal (Rneg d))) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) d) :=
    RexpReal_one_sub_neg_le hd0 hd1
  -- E·(1−C) ≤ 1·(1−C)
  have hEle1 : Rle (RexpReal (Rneg d)) one := RexpReal_neg_le_one d hd0
  have h2 : Rle (Rmul (RexpReal (Rneg d)) (Rsub one (Rcos b)))
      (Rmul one (Rsub one (Rcos b))) :=
    Rmul_le_Rmul_right hCnn hEle1
  -- 1·(1−C) ≈ 1 − C  ≤ 3b²
  have h3 : Rle (Rmul one (Rsub one (Rcos b)))
      (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b)) :=
    Rle_trans (Rle_of_Req (Req_trans (Rmul_comm one (Rsub one (Rcos b)))
        (Rmul_one (Rsub one (Rcos b)))))
      (Rcos_one_sub_le_sq hb2 hb1)
  refine Rle_trans (Rle_of_Req hdecomp) ?_
  exact Radd_le_add h1 (Rle_trans h2 h3)

-- u.re ≥ 0   (e^{−d}cos b ≤ e^{−d}·1 ≤ 1).
theorem oneSubCexp_re_lower {d b : Real} (hd0 : Rnonneg d) :
    Rle zero (Rsub one (Rmul (RexpReal (Rneg d)) (Rcos b))) := by
  -- E·C ≤ E·1 ≈ E ≤ 1
  have hEC : Rle (Rmul (RexpReal (Rneg d)) (Rcos b)) one :=
    Rle_trans (Rmul_le_Rmul_left (RexpReal_nonneg (Rneg d)) (Rcos_le_one b))
      (Rle_trans (Rle_of_Req (Rmul_one (RexpReal (Rneg d)))) (RexpReal_neg_le_one d hd0))
  -- 0 ≤ 1 − E·C
  exact Rle_zero_of_Rnonneg (Rnonneg_Rsub_of_Rle hEC)

-- |u.im| ≤ (1 + 3b²)·Bb  given the bound −Bb ≤ b ≤ Bb (Bb ≥ 0).  Via Rsin b = b·RsinAux b,
-- |RsinAux b| ≤ 1+3b², |e^{−d}| ≤ 1, two applications of the product keystone.
-- 0 ≤ 1.
private theorem oneSubCexp_zero_le_one : Rle zero one :=
  Rle_ofQ_ofQ (by decide) (by decide) (by decide)

-- −1 ≤ zero.
private theorem oneSubCexp_negone_le_zero :
    Rle (Rneg one) zero :=
  Rle_trans (Rle_Rneg oneSubCexp_zero_le_one) (Rle_of_Req Rneg_zero)

-- −1 ≤ 1.
private theorem oneSubCexp_negone_le_one :
    Rle (Rneg one) one :=
  Rle_trans oneSubCexp_negone_le_zero oneSubCexp_zero_le_one

-- −B3 ≤ 1 − 3b²  where B3 = 1 + 3b²  (difference is 2 ≥ 0).
--   −(1+X) ≈ (−1) + (−X) ≤ 1 + (−X) ≈ 1 − X.
private theorem oneSubCexp_negB3_le (b : Real) :
    Rle (Rneg (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b))))
        (Rsub one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b))) := by
  refine Rle_trans
    (Rle_of_Req (Rneg_Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b)))) ?_
  -- (−1) + (−X) ≤ 1 + (−X) = 1 − X
  exact Radd_le_add oneSubCexp_negone_le_one
    (Rle_refl (Rneg (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b))))

-- 1·(Bb·B3) ≈ B3·Bb  (Rmul one collapse + commute).
private theorem oneSubCexp_oneBbB3 (Bb B3 : Real) :
    Req (Rmul one (Rmul Bb B3)) (Rmul B3 Bb) := by
  exact Req_trans (Req_trans (Rmul_comm one (Rmul Bb B3)) (Rmul_one (Rmul Bb B3)))
    (Rmul_comm Bb B3)

-- Two-sided bound on E·(b·RsinAux b) by ±(Bb·B3), packaged for both im theorems.
private theorem oneSubCexp_im_core {d b Bb : Real} (hd0 : Rnonneg d)
    (hb1 : Rle (Rneg one) b) (hb2 : Rle b one)
    (hbB1 : Rle (Rneg Bb) b) (hbB2 : Rle b Bb) :
    Rle (Rneg (Rmul one (Rmul Bb
            (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b))))))
        (Rmul (RexpReal (Rneg d)) (Rsin b))
  ∧ Rle (Rmul (RexpReal (Rneg d)) (Rsin b))
        (Rmul one (Rmul Bb
            (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b))))) := by
  -- abbreviation B3 = 1 + 3b²
  -- Step 1: bound RsinAux b
  have hAuxU : Rle (RsinAux b)
      (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b))) :=
    RsinAux_upper_le hb2 hb1
  have hAuxL : Rle (Rneg (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b))))
      (RsinAux b) :=
    Rle_trans (oneSubCexp_negB3_le b) (RsinAux_lower_ge hb2 hb1)
  -- Step 1 product: Rsin b = b·RsinAux b ∈ ±(Bb·B3)
  have hSinU : Rle (Rmul b (RsinAux b))
      (Rmul Bb (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b)))) :=
    Rmul_le_mul_of_abs hbB1 hbB2 hAuxL hAuxU
  have hSinL : Rle (Rneg (Rmul Bb (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b)))))
      (Rmul b (RsinAux b)) :=
    Rneg_mul_le_of_abs hbB1 hbB2 hAuxL hAuxU
  -- unfold Rsin
  have hRsin : Rsin b = Rmul b (RsinAux b) := rfl
  rw [hRsin]
  -- Step 2: bound E = e^{−d} ∈ ±1
  have hEU : Rle (RexpReal (Rneg d)) one := RexpReal_neg_le_one d hd0
  have hEL : Rle (Rneg one) (RexpReal (Rneg d)) :=
    Rle_trans oneSubCexp_negone_le_zero (Rle_zero_of_Rnonneg (RexpReal_nonneg (Rneg d)))
  -- Step 2 product
  constructor
  · exact Rneg_mul_le_of_abs hEL hEU hSinL hSinU
  · exact Rmul_le_mul_of_abs hEL hEU hSinL hSinU

theorem oneSubCexp_im_upper {d b Bb : Real} (hd0 : Rnonneg d)
    (hb1 : Rle (Rneg one) b) (hb2 : Rle b one)
    (hbB1 : Rle (Rneg Bb) b) (hbB2 : Rle b Bb) (_hBb : Rnonneg Bb) :
    Rle (Rneg (Rmul (RexpReal (Rneg d)) (Rsin b)))
        (Rmul (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b))) Bb) := by
  obtain ⟨hlo, _⟩ := oneSubCexp_im_core hd0 hb1 hb2 hbB1 hbB2
  -- from −(1·(Bb·B3)) ≤ E·Rsin b  get  −(E·Rsin b) ≤ 1·(Bb·B3) ≈ B3·Bb
  have hneg : Rle (Rneg (Rmul (RexpReal (Rneg d)) (Rsin b)))
      (Rneg (Rneg (Rmul one (Rmul Bb
        (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b))))))) :=
    Rle_Rneg hlo
  refine Rle_trans hneg ?_
  refine Rle_of_Req (Req_trans (Rneg_neg _) ?_)
  exact oneSubCexp_oneBbB3 Bb (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b)))

theorem oneSubCexp_im_lower {d b Bb : Real} (hd0 : Rnonneg d)
    (hb1 : Rle (Rneg one) b) (hb2 : Rle b one)
    (hbB1 : Rle (Rneg Bb) b) (hbB2 : Rle b Bb) (_hBb : Rnonneg Bb) :
    Rle (Rneg (Rmul (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b))) Bb))
        (Rneg (Rmul (RexpReal (Rneg d)) (Rsin b))) := by
  obtain ⟨_, hhi⟩ := oneSubCexp_im_core hd0 hb1 hb2 hbB1 hbB2
  -- from E·Rsin b ≤ 1·(Bb·B3) ≈ B3·Bb  get  −(B3·Bb) ≤ −(E·Rsin b)
  have hbound : Rle (Rmul (RexpReal (Rneg d)) (Rsin b))
      (Rmul (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b))) Bb) :=
    Rle_trans hhi (Rle_of_Req
      (oneSubCexp_oneBbB3 Bb (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b)))))
  exact Rle_Rneg hbound


-- ===========================================================================
-- The per-term η variation bound: −V_n ≤ Re/Im(n⁻ˢ − (n+1)⁻ˢ) ≤ V_n, V_n = Vterm ~ n^{−σ−1} (summable).
-- Combines the cpowNeg z-bounds and the oneSubCexp u-bounds via the two-sided product keystone
-- (abstract combinators Rmul_sub/add_two_sided) and the cpowNeg_diff Ceq-transport (D_n = z·u).
-- Hypotheses are the n ≥ N₀(s) smallness conditions (d=Re s·δ_n ≤ 1/2, b=−Im s·δ_n ∈ [−1,1], etc.).
-- ===========================================================================

-- ABSTRACT two-sided combinators (keystone Rmul_le_mul_of_abs/Rneg_mul_le_of_abs applied to each product,
-- then Rsub/Radd two-sided). For zr,zi ∈ [−A,A], ur ∈ [−U,U], ui ∈ [−M,M]:
--   Rsub (zr·ur) (zi·ui) ∈ [−(AU+AM), AU+AM]   and   Radd (zr·ui) (zi·ur) ∈ [−(AM+AU), AM+AU].

theorem Rmul_sub_two_sided {zr zi ur ui A U M : Real}
    (hzr1 : Rle (Rneg A) zr) (hzr2 : Rle zr A) (hzi1 : Rle (Rneg A) zi) (hzi2 : Rle zi A)
    (hur1 : Rle (Rneg U) ur) (hur2 : Rle ur U) (hui1 : Rle (Rneg M) ui) (hui2 : Rle ui M) :
    Rle (Rsub (Rmul zr ur) (Rmul zi ui)) (Radd (Rmul A U) (Rmul A M))
  ∧ Rle (Rneg (Radd (Rmul A U) (Rmul A M))) (Rsub (Rmul zr ur) (Rmul zi ui)) := by
  -- p = zr·ur ∈ [−AU, AU],  q = zi·ui ∈ [−AM, AM]
  have hp_up : Rle (Rmul zr ur) (Rmul A U) := Rmul_le_mul_of_abs hzr1 hzr2 hur1 hur2
  have hp_lo : Rle (Rneg (Rmul A U)) (Rmul zr ur) := Rneg_mul_le_of_abs hzr1 hzr2 hur1 hur2
  have hq_up : Rle (Rmul zi ui) (Rmul A M) := Rmul_le_mul_of_abs hzi1 hzi2 hui1 hui2
  have hq_lo : Rle (Rneg (Rmul A M)) (Rmul zi ui) := Rneg_mul_le_of_abs hzi1 hzi2 hui1 hui2
  constructor
  · -- p − q ≤ AU + AM.  −q ≤ AM  from  −(AM) ≤ q.
    have hnegq : Rle (Rneg (Rmul zi ui)) (Rmul A M) :=
      Rle_trans (Rle_Rneg hq_lo) (Rle_of_Req (Rneg_neg (Rmul A M)))
    exact Radd_le_add hp_up hnegq
  · -- −(AU+AM) ≤ p − q.  −(AU+AM) ≈ (−AU)+(−AM) ≤ p + (−q).
    have hnegq : Rle (Rneg (Rmul A M)) (Rneg (Rmul zi ui)) := Rle_Rneg hq_up
    refine Rle_trans (Rle_of_Req (Rneg_Radd (Rmul A U) (Rmul A M))) ?_
    exact Radd_le_add hp_lo hnegq

theorem Rmul_add_two_sided {zr zi ur ui A U M : Real}
    (hzr1 : Rle (Rneg A) zr) (hzr2 : Rle zr A) (hzi1 : Rle (Rneg A) zi) (hzi2 : Rle zi A)
    (hur1 : Rle (Rneg U) ur) (hur2 : Rle ur U) (hui1 : Rle (Rneg M) ui) (hui2 : Rle ui M) :
    Rle (Radd (Rmul zr ui) (Rmul zi ur)) (Radd (Rmul A M) (Rmul A U))
  ∧ Rle (Rneg (Radd (Rmul A M) (Rmul A U))) (Radd (Rmul zr ui) (Rmul zi ur)) := by
  -- p = zr·ui ∈ [−AM, AM],  q = zi·ur ∈ [−AU, AU]
  have hp_up : Rle (Rmul zr ui) (Rmul A M) := Rmul_le_mul_of_abs hzr1 hzr2 hui1 hui2
  have hp_lo : Rle (Rneg (Rmul A M)) (Rmul zr ui) := Rneg_mul_le_of_abs hzr1 hzr2 hui1 hui2
  have hq_up : Rle (Rmul zi ur) (Rmul A U) := Rmul_le_mul_of_abs hzi1 hzi2 hur1 hur2
  have hq_lo : Rle (Rneg (Rmul A U)) (Rmul zi ur) := Rneg_mul_le_of_abs hzi1 hzi2 hur1 hur2
  constructor
  · exact Radd_le_add hp_up hq_up
  · refine Rle_trans (Rle_of_Req (Rneg_Radd (Rmul A M) (Rmul A U))) ?_
    exact Radd_le_add hp_lo hq_lo

-- The per-term variation bound V_n.  δ = deltaLogNat n hn, d = s.re·δ, b = −s.im·δ,
-- A = exp(−s.re·log n), U = 4d+3b², M = (1+3b²)·Bb.  Bb is a caller-supplied bound with −Bb ≤ b ≤ Bb.
-- Vterm = A·(U + M).
def Vterm (s : Complex) (n : Nat) (hn : 2 ≤ n) (Bb : Real) : Real :=
  Rmul (RexpReal (Rmul (Rneg s.re) (RlogNat n hn)))
    (Radd
      (Radd (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul s.re (deltaLogNat n hn)))
            (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide))
                  (Rmul (Rmul (Rneg s.im) (deltaLogNat n hn)) (Rmul (Rneg s.im) (deltaLogNat n hn)))))
      (Rmul (Radd one (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide))
                  (Rmul (Rmul (Rneg s.im) (deltaLogNat n hn)) (Rmul (Rneg s.im) (deltaLogNat n hn))))) Bb))

-- Per-term variation: −V_n ≤ Re(n⁻ˢ − (n+1)⁻ˢ) ≤ V_n  (and same for Im).
-- Hypotheses (the n ≥ N₀(s) smallness, supplied by the caller):
--   hσ : Re s ≥ 0,  hd1 : s.re·δ ≤ 1/2,  hb1/hb2 : b ∈ [−1,1],  hBb1/hBb2 : −Bb ≤ b ≤ Bb,  hBb : Bb ≥ 0.
theorem cpowNeg_diff_re_bound (s : Complex) (n : Nat) (hn : 2 ≤ n) {Bb : Real}
    (hσ : Rnonneg s.re)
    (hd1 : Rle (Rmul s.re (deltaLogNat n hn)) (ofQ (⟨1, 2⟩ : Q) (by decide)))
    (hb1 : Rle (Rneg one) (Rmul (Rneg s.im) (deltaLogNat n hn)))
    (hb2 : Rle (Rmul (Rneg s.im) (deltaLogNat n hn)) one)
    (hBb1 : Rle (Rneg Bb) (Rmul (Rneg s.im) (deltaLogNat n hn)))
    (hBb2 : Rle (Rmul (Rneg s.im) (deltaLogNat n hn)) Bb)
    (hBb : Rnonneg Bb) :
    Rle (Rsub (cpowNeg s n).re (cpowNeg s (n + 1)).re) (Vterm s n hn Bb)
  ∧ Rle (Rneg (Vterm s n hn Bb)) (Rsub (cpowNeg s n).re (cpowNeg s (n + 1)).re) := by
  -- abbreviations (let-bound; defeq to their definitions)
  let δ := deltaLogNat n hn
  let b := Rmul (Rneg s.im) δ
  let d := Rmul s.re δ
  let A := RexpReal (Rmul (Rneg s.re) (RlogNat n hn))
  let E := RexpReal (Rmul (Rneg s.re) δ)
  let three : Real := ofQ (⟨3, 1⟩ : Q) (by decide)
  let four : Real := ofQ (⟨4, 1⟩ : Q) (by decide)
  let U := Radd (Rmul four d) (Rmul three (Rmul b b))
  let M := Rmul (Radd one (Rmul three (Rmul b b))) Bb
  let z := cpowNeg s n
  let u := Csub Cone (Cexp ⟨Rmul (Rneg s.re) δ, b⟩)
  -- d ≥ 0
  have hdnn : Rnonneg d := Rnonneg_Rmul hσ (Rnonneg_deltaLogNat n hn)
  -- z-component bounds (A)
  have hzr_up : Rle z.re A := cpowNeg_re_le s n hn
  have hzr_lo : Rle (Rneg A) z.re := cpowNeg_re_ge s n hn
  have hzi_up : Rle z.im A := cpowNeg_im_le s n hn
  have hzi_lo : Rle (Rneg A) z.im := cpowNeg_im_ge s n hn
  -- the Req lifting RexpReal (Rmul (Rneg s.re) δ) = RexpReal (Rneg d)
  have hEeq : Req E (RexpReal (Rneg d)) := RexpReal_congr (Rmul_neg_left s.re δ)
  -- u.re / u.im components (definitional)
  have hure : u.re = Rsub one (Rmul E (Rcos b)) := rfl
  have huim : u.im = Radd zero (Rneg (Rmul E (Rsin b))) := rfl
  -- u.re bounds via oneSubCexp, transported across E ≈ exp(−d)
  have hcongr_re : Req (Rsub one (Rmul E (Rcos b)))
      (Rsub one (Rmul (RexpReal (Rneg d)) (Rcos b))) :=
    Rsub_congr (Req_refl one) (Rmul_congr hEeq (Req_refl (Rcos b)))
  have hur_up : Rle u.re U := by
    rw [hure]
    refine Rle_trans (Rle_of_Req hcongr_re) ?_
    exact oneSubCexp_re_upper hdnn hd1 hb1 hb2
  -- U ≥ 0
  have hUnn : Rnonneg U :=
    Rnonneg_Radd (Rnonneg_Rmul (Rnonneg_ofQ (by decide) (by decide)) hdnn)
      (Rnonneg_Rmul (Rnonneg_ofQ (by decide) (by decide)) (Rnonneg_Rmul_self b))
  have hur_lo : Rle (Rneg U) u.re := by
    rw [hure]
    have h0 : Rle zero (Rsub one (Rmul (RexpReal (Rneg d)) (Rcos b))) :=
      oneSubCexp_re_lower hdnn
    have h0' : Rle zero (Rsub one (Rmul E (Rcos b))) :=
      Rle_trans h0 (Rle_of_Req (Req_symm hcongr_re))
    have hnU0 : Rle (Rneg U) zero :=
      Rle_trans (Rle_Rneg (Rle_zero_of_Rnonneg hUnn)) (Rle_of_Req Rneg_zero)
    exact Rle_trans hnU0 h0'
  -- u.im bounds via oneSubCexp_im_*, transported across E ≈ exp(−d) and Radd zero
  have hcongr_im : Req (Rneg (Rmul E (Rsin b)))
      (Rneg (Rmul (RexpReal (Rneg d)) (Rsin b))) :=
    Rneg_congr (Rmul_congr hEeq (Req_refl (Rsin b)))
  have huim_eq : Req u.im (Rneg (Rmul (RexpReal (Rneg d)) (Rsin b))) := by
    rw [huim]
    exact Req_trans (Req_trans (Radd_comm zero (Rneg (Rmul E (Rsin b))))
      (Radd_zero (Rneg (Rmul E (Rsin b))))) hcongr_im
  have hui_up : Rle u.im M := by
    refine Rle_trans (Rle_of_Req huim_eq) ?_
    exact oneSubCexp_im_upper hdnn hb1 hb2 hBb1 hBb2 hBb
  have hui_lo : Rle (Rneg M) u.im := by
    refine Rle_trans ?_ (Rle_of_Req (Req_symm huim_eq))
    exact oneSubCexp_im_lower hdnn hb1 hb2 hBb1 hBb2 hBb
  -- combine via the abstract combinator
  have hcomb := Rmul_sub_two_sided (A := A) (U := U) (M := M)
    hzr_lo hzr_up hzi_lo hzi_up hur_lo hur_up hui_lo hui_up
  -- (Cmul z u).re = Rsub (Rmul z.re u.re) (Rmul z.im u.im)
  have hCmulre : (Cmul z u).re = Rsub (Rmul z.re u.re) (Rmul z.im u.im) := rfl
  -- Vterm ≈ Radd (A·U) (A·M)
  have hVterm : Req (Vterm s n hn Bb) (Radd (Rmul A U) (Rmul A M)) :=
    Rmul_distrib A U M
  -- cpowNeg_diff transport: hdiff : Req (Rsub z.re (n+1).re) (Cmul z u).re
  have hdiff := (cpowNeg_diff s n hn).1
  constructor
  · -- upper:  Rsub z.re (n+1).re ≤ Vterm
    refine Rle_trans (Rle_of_Req hdiff) ?_
    rw [hCmulre]
    exact Rle_trans hcomb.1 (Rle_of_Req (Req_symm hVterm))
  · -- lower:  −Vterm ≤ Rsub z.re (n+1).re
    refine Rle_trans (Rle_of_Req (Rneg_congr hVterm)) ?_
    refine Rle_trans hcomb.2 ?_
    rw [← hCmulre]
    exact Rle_of_Req (Req_symm hdiff)

theorem cpowNeg_diff_im_bound (s : Complex) (n : Nat) (hn : 2 ≤ n) {Bb : Real}
    (hσ : Rnonneg s.re)
    (hd1 : Rle (Rmul s.re (deltaLogNat n hn)) (ofQ (⟨1, 2⟩ : Q) (by decide)))
    (hb1 : Rle (Rneg one) (Rmul (Rneg s.im) (deltaLogNat n hn)))
    (hb2 : Rle (Rmul (Rneg s.im) (deltaLogNat n hn)) one)
    (hBb1 : Rle (Rneg Bb) (Rmul (Rneg s.im) (deltaLogNat n hn)))
    (hBb2 : Rle (Rmul (Rneg s.im) (deltaLogNat n hn)) Bb)
    (hBb : Rnonneg Bb) :
    Rle (Rsub (cpowNeg s n).im (cpowNeg s (n + 1)).im) (Vterm s n hn Bb)
  ∧ Rle (Rneg (Vterm s n hn Bb)) (Rsub (cpowNeg s n).im (cpowNeg s (n + 1)).im) := by
  -- abbreviations (let-bound; defeq to their definitions)
  let δ := deltaLogNat n hn
  let b := Rmul (Rneg s.im) δ
  let d := Rmul s.re δ
  let A := RexpReal (Rmul (Rneg s.re) (RlogNat n hn))
  let E := RexpReal (Rmul (Rneg s.re) δ)
  let three : Real := ofQ (⟨3, 1⟩ : Q) (by decide)
  let four : Real := ofQ (⟨4, 1⟩ : Q) (by decide)
  let U := Radd (Rmul four d) (Rmul three (Rmul b b))
  let M := Rmul (Radd one (Rmul three (Rmul b b))) Bb
  let z := cpowNeg s n
  let u := Csub Cone (Cexp ⟨Rmul (Rneg s.re) δ, b⟩)
  have hdnn : Rnonneg d := Rnonneg_Rmul hσ (Rnonneg_deltaLogNat n hn)
  have hzr_up : Rle z.re A := cpowNeg_re_le s n hn
  have hzr_lo : Rle (Rneg A) z.re := cpowNeg_re_ge s n hn
  have hzi_up : Rle z.im A := cpowNeg_im_le s n hn
  have hzi_lo : Rle (Rneg A) z.im := cpowNeg_im_ge s n hn
  have hEeq : Req E (RexpReal (Rneg d)) := RexpReal_congr (Rmul_neg_left s.re δ)
  have hure : u.re = Rsub one (Rmul E (Rcos b)) := rfl
  have huim : u.im = Radd zero (Rneg (Rmul E (Rsin b))) := rfl
  have hcongr_re : Req (Rsub one (Rmul E (Rcos b)))
      (Rsub one (Rmul (RexpReal (Rneg d)) (Rcos b))) :=
    Rsub_congr (Req_refl one) (Rmul_congr hEeq (Req_refl (Rcos b)))
  have hur_up : Rle u.re U := by
    rw [hure]
    refine Rle_trans (Rle_of_Req hcongr_re) ?_
    exact oneSubCexp_re_upper hdnn hd1 hb1 hb2
  have hUnn : Rnonneg U :=
    Rnonneg_Radd (Rnonneg_Rmul (Rnonneg_ofQ (by decide) (by decide)) hdnn)
      (Rnonneg_Rmul (Rnonneg_ofQ (by decide) (by decide)) (Rnonneg_Rmul_self b))
  have hur_lo : Rle (Rneg U) u.re := by
    rw [hure]
    have h0 : Rle zero (Rsub one (Rmul (RexpReal (Rneg d)) (Rcos b))) :=
      oneSubCexp_re_lower hdnn
    have h0' : Rle zero (Rsub one (Rmul E (Rcos b))) :=
      Rle_trans h0 (Rle_of_Req (Req_symm hcongr_re))
    have hnU0 : Rle (Rneg U) zero :=
      Rle_trans (Rle_Rneg (Rle_zero_of_Rnonneg hUnn)) (Rle_of_Req Rneg_zero)
    exact Rle_trans hnU0 h0'
  have hcongr_im : Req (Rneg (Rmul E (Rsin b)))
      (Rneg (Rmul (RexpReal (Rneg d)) (Rsin b))) :=
    Rneg_congr (Rmul_congr hEeq (Req_refl (Rsin b)))
  have huim_eq : Req u.im (Rneg (Rmul (RexpReal (Rneg d)) (Rsin b))) := by
    rw [huim]
    exact Req_trans (Req_trans (Radd_comm zero (Rneg (Rmul E (Rsin b))))
      (Radd_zero (Rneg (Rmul E (Rsin b))))) hcongr_im
  have hui_up : Rle u.im M := by
    refine Rle_trans (Rle_of_Req huim_eq) ?_
    exact oneSubCexp_im_upper hdnn hb1 hb2 hBb1 hBb2 hBb
  have hui_lo : Rle (Rneg M) u.im := by
    refine Rle_trans ?_ (Rle_of_Req (Req_symm huim_eq))
    exact oneSubCexp_im_lower hdnn hb1 hb2 hBb1 hBb2 hBb
  -- combine via the ADD abstract combinator (.im uses Radd of cross products)
  have hcomb := Rmul_add_two_sided (A := A) (U := U) (M := M)
    hzr_lo hzr_up hzi_lo hzi_up hur_lo hur_up hui_lo hui_up
  -- (Cmul z u).im = Radd (Rmul z.re u.im) (Rmul z.im u.re)
  have hCmulim : (Cmul z u).im = Radd (Rmul z.re u.im) (Rmul z.im u.re) := rfl
  -- Vterm ≈ Radd (A·M) (A·U)
  have hVterm : Req (Vterm s n hn Bb) (Radd (Rmul A M) (Rmul A U)) :=
    Req_trans (Rmul_distrib A U M) (Radd_comm (Rmul A U) (Rmul A M))
  -- cpowNeg_diff transport: hdiff : Req (Rsub z.im (n+1).im) (Cmul z u).im
  have hdiff := (cpowNeg_diff s n hn).2
  constructor
  · refine Rle_trans (Rle_of_Req hdiff) ?_
    rw [hCmulim]
    exact Rle_trans hcomb.1 (Rle_of_Req (Req_symm hVterm))
  · refine Rle_trans (Rle_of_Req (Rneg_congr hVterm)) ?_
    refine Rle_trans hcomb.2 ?_
    rw [← hCmulim]
    exact Rle_of_Req (Req_symm hdiff)

-- ===========================================================================
-- Step 7a — the PAIRING identity for the alternating η partial sums: czEtaSum s (2K) ≈ Σ_{j<K} D_{2j+1}
-- (D_n = n⁻ˢ − (n+1)⁻ˢ). The even partial sums equal the sum of the consecutive differences bounded above,
-- so the η-Cauchy criterion reduces to the (summable) variation Σ Vterm. Exact Cadd-rearrangement.
-- ===========================================================================

/-- The `n`-th consecutive difference `n⁻ˢ − (n+1)⁻ˢ`. -/
def cpowNegDiff (s : Complex) (n : Nat) : Complex := Csub (cpowNeg s n) (cpowNeg s (n + 1))

/-- The paired-difference sum `Σ_{j=0}^{K−1} D_{2j+1}` (the even η partial sums in paired form). -/
def czEtaPaired (s : Complex) : Nat → Complex
  | 0 => Czero
  | (K + 1) => Cadd (czEtaPaired s K) (cpowNegDiff s (2 * K + 1))

/-- **The pairing identity**: `czEtaSum s (2K) ≈ Σ_{j<K} D_{2j+1}`. Each even/odd pair
    `(+a_{2j+1}) + (−a_{2j+2})` is the difference `D_{2j+1}`; `Cadd_assoc` regroups. -/
theorem czEtaSum_two_eq_paired (s : Complex) (K : Nat) :
    Ceq (czEtaSum s (2 * K)) (czEtaPaired s K) := by
  induction K with
  | zero => exact Ceq_refl _
  | succ K ih =>
    have h2 : 2 * (K + 1) = 2 * K + 1 + 1 := by omega
    rw [h2, czEtaSum_succ, czEtaSum_succ,
      czEtaTerm_even s (2 * K) (by omega), czEtaTerm_odd s (2 * K + 1) (by omega)]
    refine Ceq_trans
      (Cadd_assoc (czEtaSum s (2 * K)) (cpowNeg s (2 * K + 1))
        (Cneg (cpowNeg s (2 * K + 1 + 1)))) ?_
    exact Cadd_congr ih (Ceq_refl _)

-- ===========================================================================
-- Step 7b-i — the PAIRED-SUM TAIL BOUND (abstract telescoping): the change in the paired partial sum over
-- a block is controlled by the sum of the per-term variation bounds V i. A direct mirror of
-- czeta_re_diff_le/ge_aux, taking the per-term bounds as a hypothesis (the n ≥ N₀(s) smallness lives at the
-- call site). RsumRange V d = Σ_{i<d} V i.
-- ===========================================================================

/-- Partial sums `Σ_{i=0}^{d−1} V i` of an arbitrary term sequence. -/
def RsumRange (V : Nat → Real) : Nat → Real
  | 0 => zero
  | (d + 1) => Radd (RsumRange V d) (V d)

/-- **Paired tail, upper (real part)**: `S(K+d).re − S(K).re ≤ Σ_{i<d} V i` from the per-term upper bounds. -/
theorem czEtaPaired_re_diff_le (s : Complex) (K : Nat) (V : Nat → Real)
    (hb : ∀ i, Rle (Rsub (cpowNeg s (2 * (K + i) + 1)).re (cpowNeg s (2 * (K + i) + 1 + 1)).re) (V i)) :
    ∀ d, Rle (Rsub (czEtaPaired s (K + d)).re (czEtaPaired s K).re) (RsumRange V d)
  | 0 => Rle_of_Req (Radd_neg _)
  | (d + 1) =>
      Rle_trans (Rle_of_Req (Rsub_Radd_left (czEtaPaired s (K + d)).re
          (cpowNegDiff s (2 * (K + d) + 1)).re (czEtaPaired s K).re))
        (Radd_le_add (czEtaPaired_re_diff_le s K V hb d) (hb d))

/-- **Paired tail, lower (real part)**: `−Σ_{i<d} V i ≤ S(K+d).re − S(K).re` from the per-term lower bounds. -/
theorem czEtaPaired_re_diff_ge (s : Complex) (K : Nat) (V : Nat → Real)
    (hb : ∀ i, Rle (Rneg (V i)) (Rsub (cpowNeg s (2 * (K + i) + 1)).re (cpowNeg s (2 * (K + i) + 1 + 1)).re)) :
    ∀ d, Rle (Rneg (RsumRange V d)) (Rsub (czEtaPaired s (K + d)).re (czEtaPaired s K).re)
  | 0 => Rle_of_Req (Req_trans Rneg_zero (Req_symm (Radd_neg _)))
  | (d + 1) =>
      Rle_trans (Rle_of_Req (Rneg_Radd (RsumRange V d) (V d)))
        (Rle_trans (Radd_le_add (czEtaPaired_re_diff_ge s K V hb d) (hb d))
          (Rle_of_Req (Req_symm (Rsub_Radd_left (czEtaPaired s (K + d)).re
            (cpowNegDiff s (2 * (K + d) + 1)).re (czEtaPaired s K).re))))

/-- **Paired tail, upper (imaginary part)**. -/
theorem czEtaPaired_im_diff_le (s : Complex) (K : Nat) (V : Nat → Real)
    (hb : ∀ i, Rle (Rsub (cpowNeg s (2 * (K + i) + 1)).im (cpowNeg s (2 * (K + i) + 1 + 1)).im) (V i)) :
    ∀ d, Rle (Rsub (czEtaPaired s (K + d)).im (czEtaPaired s K).im) (RsumRange V d)
  | 0 => Rle_of_Req (Radd_neg _)
  | (d + 1) =>
      Rle_trans (Rle_of_Req (Rsub_Radd_left (czEtaPaired s (K + d)).im
          (cpowNegDiff s (2 * (K + d) + 1)).im (czEtaPaired s K).im))
        (Radd_le_add (czEtaPaired_im_diff_le s K V hb d) (hb d))

/-- **Paired tail, lower (imaginary part)**. -/
theorem czEtaPaired_im_diff_ge (s : Complex) (K : Nat) (V : Nat → Real)
    (hb : ∀ i, Rle (Rneg (V i)) (Rsub (cpowNeg s (2 * (K + i) + 1)).im (cpowNeg s (2 * (K + i) + 1 + 1)).im)) :
    ∀ d, Rle (Rneg (RsumRange V d)) (Rsub (czEtaPaired s (K + d)).im (czEtaPaired s K).im)
  | 0 => Rle_of_Req (Req_trans Rneg_zero (Req_symm (Radd_neg _)))
  | (d + 1) =>
      Rle_trans (Rle_of_Req (Rneg_Radd (RsumRange V d) (V d)))
        (Rle_trans (Radd_le_add (czEtaPaired_im_diff_ge s K V hb d) (hb d))
          (Rle_of_Req (Req_symm (Rsub_Radd_left (czEtaPaired s (K + d)).im
            (cpowNegDiff s (2 * (K + d) + 1)).im (czEtaPaired s K).im))))


-- ===========================================================================
-- Step 7b-ii(α) — the SMALLNESS SETUP: packages the per-term bound for n ≥ N₀(s), deriving the
-- cpowNeg_diff smallness hypotheses (d_n ≤ 1/2, b_n ∈ [−1,1], −Bb ≤ b_n ≤ Bb) from rational bounds
-- s.re ≤ sb, |s.im| ≤ T plus the largeness conditions (sb/n ≤ 1/2, T/n ≤ 1), via deltaLogNat_le_recip
-- (δ_n ≤ 1/n) + Rmul-monotonicity. Bb := T·δ_n. Feeds the V-function of the paired-tail telescoping.
-- ===========================================================================

-- Packaged per-term variation bound for n ≥ N₀(s): derives the cpowNeg_diff_re/im_bound smallness hypotheses
-- from rational bounds on s (s.re ≤ sb, |s.im| ≤ T) plus the largeness conditions (sb/n ≤ 1/2, T/n ≤ 1),
-- using deltaLogNat_le_recip (δ_n ≤ 1/n) + Rnonneg_deltaLogNat + Rmul-monotonicity.  Bb := T·δ_n.
-- Smallness derived internally:
--   d_n = s.re·δ_n ≤ sb·δ_n ≤ sb·(1/n) = sb/n ≤ 1/2                          (hd1)
--   b_n = (−s.im)·δ_n ∈ [−(T·δ_n), T·δ_n] = [−Bb, Bb]                       (hBb1, hBb2)
--   b_n ≤ Bb ≤ T·(1/n) = T/n ≤ 1  and  −1 ≤ −Bb ≤ b_n                       (hb1, hb2)
--   Bb = T·δ_n ≥ 0                                                          (hBb)
-- Then cpowNeg_diff_re_bound / im_bound apply.

theorem cpowNeg_diff_re_tail (s : Complex) {sb T : Q} (hsbd : 0 < sb.den) (hTd : 0 < T.den)
    (hT0 : 0 ≤ T.num) (hσ : Rnonneg s.re) (hsb : Rle s.re (ofQ sb hsbd))
    (hT1 : Rle (Rneg (ofQ T hTd)) s.im) (hT2 : Rle s.im (ofQ T hTd))
    (n : Nat) (hn : 2 ≤ n)
    (hdn : Qle (mul sb (⟨1, n⟩ : Q)) (⟨1, 2⟩ : Q))
    (hbn : Qle (mul T (⟨1, n⟩ : Q)) (⟨1, 1⟩ : Q)) :
    Rle (Rsub (cpowNeg s n).re (cpowNeg s (n + 1)).re)
        (Vterm s n hn (Rmul (ofQ T hTd) (deltaLogNat n hn)))
  ∧ Rle (Rneg (Vterm s n hn (Rmul (ofQ T hTd) (deltaLogNat n hn))))
        (Rsub (cpowNeg s n).re (cpowNeg s (n + 1)).re) := by
  let δ := deltaLogNat n hn
  have hδnn : Rnonneg δ := Rnonneg_deltaLogNat n hn
  have hδle : Rle δ (ofQ (⟨1, n⟩ : Q) (show 0 < n by omega)) := deltaLogNat_le_recip n hn
  -- den positivity facts
  have hnpos : 0 < n := by omega
  have hrecd : 0 < (⟨1, n⟩ : Q).den := by show 0 < n; omega
  have h12d : 0 < (⟨1, 2⟩ : Q).den := by decide
  have h11d : 0 < (⟨1, 1⟩ : Q).den := by decide
  -- Rnonneg (ofQ sb) via 0 ≤ s.re ≤ ofQ sb
  have hsbnn : Rnonneg (ofQ sb hsbd) :=
    Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg hσ) hsb)
  have hTnn : Rnonneg (ofQ T hTd) := Rnonneg_ofQ hTd hT0
  -- ===== hd1 : Rmul s.re δ ≤ ofQ ⟨1,2⟩ =====
  have hd1 : Rle (Rmul s.re δ) (ofQ (⟨1, 2⟩ : Q) (by decide)) := by
    have step1 : Rle (Rmul s.re δ) (Rmul (ofQ sb hsbd) δ) :=
      Rmul_le_Rmul_right hδnn hsb
    have step2 : Rle (Rmul (ofQ sb hsbd) δ)
        (Rmul (ofQ sb hsbd) (ofQ (⟨1, n⟩ : Q) hrecd)) :=
      Rmul_le_Rmul_left hsbnn hδle
    have step3 : Req (Rmul (ofQ sb hsbd) (ofQ (⟨1, n⟩ : Q) hrecd))
        (ofQ (mul sb (⟨1, n⟩ : Q)) (Qmul_den_pos hsbd hrecd)) :=
      Rmul_ofQ_ofQ hsbd hrecd
    have step4 : Rle (ofQ (mul sb (⟨1, n⟩ : Q)) (Qmul_den_pos hsbd hrecd))
        (ofQ (⟨1, 2⟩ : Q) (by decide)) :=
      Rle_ofQ_ofQ (Qmul_den_pos hsbd hrecd) (by decide) hdn
    exact Rle_trans step1 (Rle_trans step2 (Rle_trans (Rle_of_Req step3) step4))
  -- Bb := Rmul (ofQ T) δ
  have hBb : Rnonneg (Rmul (ofQ T hTd) δ) := Rnonneg_Rmul hTnn hδnn
  -- ===== hBb2 : Rmul (Rneg s.im) δ ≤ Bb =====
  have hnegim : Rle (Rneg s.im) (ofQ T hTd) := by
    have h := Rle_Rneg hT1
    exact Rle_trans h (Rle_of_Req (Rneg_neg (ofQ T hTd)))
  have hBb2 : Rle (Rmul (Rneg s.im) δ) (Rmul (ofQ T hTd) δ) :=
    Rmul_le_Rmul_right hδnn hnegim
  -- ===== hBb1 : Rneg Bb ≤ Rmul (Rneg s.im) δ =====
  have hnegim2 : Rle (Rneg (ofQ T hTd)) (Rneg s.im) := Rle_Rneg hT2
  have hBb1 : Rle (Rneg (Rmul (ofQ T hTd) δ)) (Rmul (Rneg s.im) δ) := by
    have step : Rle (Rmul (Rneg (ofQ T hTd)) δ) (Rmul (Rneg s.im) δ) :=
      Rmul_le_Rmul_right hδnn hnegim2
    exact Rle_trans (Rle_of_Req (Req_symm (Rmul_neg_left (ofQ T hTd) δ))) step
  -- Bb ≤ one  (used by hb1, hb2)
  have hBble1 : Rle (Rmul (ofQ T hTd) δ) one := by
    have s1 : Rle (Rmul (ofQ T hTd) δ) (Rmul (ofQ T hTd) (ofQ (⟨1, n⟩ : Q) hrecd)) :=
      Rmul_le_Rmul_left hTnn hδle
    have s2 : Req (Rmul (ofQ T hTd) (ofQ (⟨1, n⟩ : Q) hrecd))
        (ofQ (mul T (⟨1, n⟩ : Q)) (Qmul_den_pos hTd hrecd)) :=
      Rmul_ofQ_ofQ hTd hrecd
    have s3 : Rle (ofQ (mul T (⟨1, n⟩ : Q)) (Qmul_den_pos hTd hrecd))
        (ofQ (⟨1, 1⟩ : Q) (by decide)) :=
      Rle_ofQ_ofQ (Qmul_den_pos hTd hrecd) (by decide) hbn
    exact Rle_trans s1 (Rle_trans (Rle_of_Req s2) s3)
  -- ===== hb2 : Rmul (Rneg s.im) δ ≤ one =====
  have hb2 : Rle (Rmul (Rneg s.im) δ) one := Rle_trans hBb2 hBble1
  -- ===== hb1 : Rneg one ≤ Rmul (Rneg s.im) δ =====
  have hb1 : Rle (Rneg one) (Rmul (Rneg s.im) δ) :=
    Rle_trans (Rle_Rneg hBble1) hBb1
  exact cpowNeg_diff_re_bound s n hn hσ hd1 hb1 hb2 hBb1 hBb2 hBb

theorem cpowNeg_diff_im_tail (s : Complex) {sb T : Q} (hsbd : 0 < sb.den) (hTd : 0 < T.den)
    (hT0 : 0 ≤ T.num) (hσ : Rnonneg s.re) (hsb : Rle s.re (ofQ sb hsbd))
    (hT1 : Rle (Rneg (ofQ T hTd)) s.im) (hT2 : Rle s.im (ofQ T hTd))
    (n : Nat) (hn : 2 ≤ n)
    (hdn : Qle (mul sb (⟨1, n⟩ : Q)) (⟨1, 2⟩ : Q))
    (hbn : Qle (mul T (⟨1, n⟩ : Q)) (⟨1, 1⟩ : Q)) :
    Rle (Rsub (cpowNeg s n).im (cpowNeg s (n + 1)).im)
        (Vterm s n hn (Rmul (ofQ T hTd) (deltaLogNat n hn)))
  ∧ Rle (Rneg (Vterm s n hn (Rmul (ofQ T hTd) (deltaLogNat n hn))))
        (Rsub (cpowNeg s n).im (cpowNeg s (n + 1)).im) := by
  let δ := deltaLogNat n hn
  have hδnn : Rnonneg δ := Rnonneg_deltaLogNat n hn
  have hδle : Rle δ (ofQ (⟨1, n⟩ : Q) (show 0 < n by omega)) := deltaLogNat_le_recip n hn
  have hnpos : 0 < n := by omega
  have hrecd : 0 < (⟨1, n⟩ : Q).den := by show 0 < n; omega
  have h12d : 0 < (⟨1, 2⟩ : Q).den := by decide
  have h11d : 0 < (⟨1, 1⟩ : Q).den := by decide
  have hsbnn : Rnonneg (ofQ sb hsbd) :=
    Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg hσ) hsb)
  have hTnn : Rnonneg (ofQ T hTd) := Rnonneg_ofQ hTd hT0
  have hd1 : Rle (Rmul s.re δ) (ofQ (⟨1, 2⟩ : Q) (by decide)) := by
    have step1 : Rle (Rmul s.re δ) (Rmul (ofQ sb hsbd) δ) :=
      Rmul_le_Rmul_right hδnn hsb
    have step2 : Rle (Rmul (ofQ sb hsbd) δ)
        (Rmul (ofQ sb hsbd) (ofQ (⟨1, n⟩ : Q) hrecd)) :=
      Rmul_le_Rmul_left hsbnn hδle
    have step3 : Req (Rmul (ofQ sb hsbd) (ofQ (⟨1, n⟩ : Q) hrecd))
        (ofQ (mul sb (⟨1, n⟩ : Q)) (Qmul_den_pos hsbd hrecd)) :=
      Rmul_ofQ_ofQ hsbd hrecd
    have step4 : Rle (ofQ (mul sb (⟨1, n⟩ : Q)) (Qmul_den_pos hsbd hrecd))
        (ofQ (⟨1, 2⟩ : Q) (by decide)) :=
      Rle_ofQ_ofQ (Qmul_den_pos hsbd hrecd) (by decide) hdn
    exact Rle_trans step1 (Rle_trans step2 (Rle_trans (Rle_of_Req step3) step4))
  have hBb : Rnonneg (Rmul (ofQ T hTd) δ) := Rnonneg_Rmul hTnn hδnn
  have hnegim : Rle (Rneg s.im) (ofQ T hTd) := by
    have h := Rle_Rneg hT1
    exact Rle_trans h (Rle_of_Req (Rneg_neg (ofQ T hTd)))
  have hBb2 : Rle (Rmul (Rneg s.im) δ) (Rmul (ofQ T hTd) δ) :=
    Rmul_le_Rmul_right hδnn hnegim
  have hnegim2 : Rle (Rneg (ofQ T hTd)) (Rneg s.im) := Rle_Rneg hT2
  have hBb1 : Rle (Rneg (Rmul (ofQ T hTd) δ)) (Rmul (Rneg s.im) δ) := by
    have step : Rle (Rmul (Rneg (ofQ T hTd)) δ) (Rmul (Rneg s.im) δ) :=
      Rmul_le_Rmul_right hδnn hnegim2
    exact Rle_trans (Rle_of_Req (Req_symm (Rmul_neg_left (ofQ T hTd) δ))) step
  have hBble1 : Rle (Rmul (ofQ T hTd) δ) one := by
    have s1 : Rle (Rmul (ofQ T hTd) δ) (Rmul (ofQ T hTd) (ofQ (⟨1, n⟩ : Q) hrecd)) :=
      Rmul_le_Rmul_left hTnn hδle
    have s2 : Req (Rmul (ofQ T hTd) (ofQ (⟨1, n⟩ : Q) hrecd))
        (ofQ (mul T (⟨1, n⟩ : Q)) (Qmul_den_pos hTd hrecd)) :=
      Rmul_ofQ_ofQ hTd hrecd
    have s3 : Rle (ofQ (mul T (⟨1, n⟩ : Q)) (Qmul_den_pos hTd hrecd))
        (ofQ (⟨1, 1⟩ : Q) (by decide)) :=
      Rle_ofQ_ofQ (Qmul_den_pos hTd hrecd) (by decide) hbn
    exact Rle_trans s1 (Rle_trans (Rle_of_Req s2) s3)
  have hb2 : Rle (Rmul (Rneg s.im) δ) one := Rle_trans hBb2 hBble1
  have hb1 : Rle (Rneg one) (Rmul (Rneg s.im) δ) :=
    Rle_trans (Rle_Rneg hBble1) hBb1
  exact cpowNeg_diff_im_bound s n hn hσ hd1 hb1 hb2 hBb1 hBb2 hBb


-- ===========================================================================
-- Step 7b-ii(β-1) — reduce Vterm to A·C·δ: the per-term variation ≤ exp(−σ·log n)·C·δ_n for a fixed
-- rational C (the polynomial part U+M ≤ C·δ_n via the product keystone + δ_n ≤ 1). With δ_n ≤ 1/n this
-- is the clean input to the dyadic summability (the δ_n factor improves the czeta ratio to u<1, σ>0).
-- ===========================================================================

-- Reduce Vterm to the clean form A·C·δ:  Vterm s n hn (T·δ) ≤ A · (C · δ) for a rational constant C
-- (depending on sb, T), where A = exp(−s.re·log n), δ = deltaLogNat n hn.  This is the entry to the dyadic
-- summability: Σ Vterm ≤ C·Σ A·δ, and Σ A_n δ_n converges geometrically (the δ_n~1/n factor improves the
-- czeta dyadic ratio to u = exp(−σ log2) < 1 for σ > 0).
--
-- The polynomial part U + M ≤ C·δ:
--   U = 4d + 3b²,  d = s.re·δ ≤ sb·δ,  b² = (s.im·δ)² ≤ (T·δ)² = T²δ² ≤ T²δ  (δ ≤ 1)
--   M = (1+3b²)·(T·δ) ≤ (1+3T²)·T·δ
--   so U + M ≤ (4·sb + 3·T² + (1+3T²)·T)·δ.  Take C = that rational.
-- Inputs: sb,T rational bounds on s (as in cpowNeg_diff_re_tail) + the smallness (b ∈ [−Tδ, Tδ], δ ≤ 1).
-- The δ ≤ 1 comes from δ ≤ 1/n ≤ 1/2 (deltaLogNat_le_recip, n ≥ 2).  b ∈ [−Tδ,Tδ] derived as in the smallness setup.
-- Construct C existentially (its exact value is immaterial — only that it is a fixed rational ≥ 0).

theorem Vterm_le_A_delta (s : Complex) {sb T : Q} (hsbd : 0 < sb.den) (hTd : 0 < T.den)
    (hT0 : 0 ≤ T.num) (hσ : Rnonneg s.re) (hsb : Rle s.re (ofQ sb hsbd))
    (hT1 : Rle (Rneg (ofQ T hTd)) s.im) (hT2 : Rle s.im (ofQ T hTd))
    (n : Nat) (hn : 2 ≤ n) :
    ∃ (C : Q) (hCd : 0 < C.den),
      Rle (Vterm s n hn (Rmul (ofQ T hTd) (deltaLogNat n hn)))
        (Rmul (RexpReal (Rmul (Rneg s.re) (RlogNat n hn)))
          (Rmul (ofQ C hCd) (deltaLogNat n hn))) := by
  -- abbreviations
  let δ := deltaLogNat n hn
  let b := Rmul (Rneg s.im) δ
  let d := Rmul s.re δ
  let A := RexpReal (Rmul (Rneg s.re) (RlogNat n hn))
  let three : Real := ofQ (⟨3, 1⟩ : Q) (by decide)
  let four : Real := ofQ (⟨4, 1⟩ : Q) (by decide)
  let Td := Rmul (ofQ T hTd) δ
  -- den positivity
  have hnpos : 0 < n := by omega
  have hrecd : 0 < (⟨1, n⟩ : Q).den := by show 0 < n; omega
  have hT2d : 0 < (mul T T).den := Qmul_den_pos hTd hTd
  -- δ ≥ 0
  have hδnn : Rnonneg δ := Rnonneg_deltaLogNat n hn
  -- δ ≤ 1
  have hδle : Rle δ (ofQ (⟨1, n⟩ : Q) hrecd) := deltaLogNat_le_recip n hn
  have hδ1 : Rle δ one := by
    have hrec1 : Rle (ofQ (⟨1, n⟩ : Q) hrecd) one := by
      have : Rle (ofQ (⟨1, n⟩ : Q) hrecd) (ofQ (⟨1, 1⟩ : Q) (by decide)) :=
        Rle_ofQ_ofQ hrecd (by decide) (by show Qle (⟨1, n⟩ : Q) (⟨1, 1⟩ : Q); simp only [Qle]; push_cast; omega)
      exact this
    exact Rle_trans hδle hrec1
  -- ofQ T ≥ 0, ofQ sb ≥ 0
  have hTnn : Rnonneg (ofQ T hTd) := Rnonneg_ofQ hTd hT0
  have hsbnn : Rnonneg (ofQ sb hsbd) :=
    Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg hσ) hsb)
  -- Td = ofQ T · δ bounds on b:  −Td ≤ b ≤ Td
  have hnegim : Rle (Rneg s.im) (ofQ T hTd) :=
    Rle_trans (Rle_Rneg hT1) (Rle_of_Req (Rneg_neg (ofQ T hTd)))
  have hb2 : Rle b Td := Rmul_le_Rmul_right hδnn hnegim
  have hnegim2 : Rle (Rneg (ofQ T hTd)) (Rneg s.im) := Rle_Rneg hT2
  have hb1 : Rle (Rneg Td) b := by
    have step : Rle (Rmul (Rneg (ofQ T hTd)) δ) b := Rmul_le_Rmul_right hδnn hnegim2
    exact Rle_trans (Rle_of_Req (Req_symm (Rmul_neg_left (ofQ T hTd) δ))) step
  -- b² ≤ Td·Td
  have hbb : Rle (Rmul b b) (Rmul Td Td) := Rmul_le_mul_of_abs hb1 hb2 hb1 hb2
  -- Td·Td ≈ (ofQ T · ofQ T)·(δ·δ) ≤ (ofQ T · ofQ T)·δ ≈ ofQ(T·T)·δ
  have hTTnn : Rnonneg (Rmul (ofQ T hTd) (ofQ T hTd)) := Rnonneg_Rmul hTnn hTnn
  have hddle : Rle (Rmul δ δ) δ :=
    Rle_trans (Rmul_le_Rmul_left hδnn hδ1) (Rle_of_Req (Rmul_one δ))
  have hTd2 : Rle (Rmul Td Td) (Rmul (ofQ (mul T T) hT2d) δ) := by
    have e1 : Req (Rmul Td Td) (Rmul (Rmul (ofQ T hTd) (ofQ T hTd)) (Rmul δ δ)) :=
      Rmul4_rearrange (ofQ T hTd) δ (ofQ T hTd) δ
    have step2 : Rle (Rmul (Rmul (ofQ T hTd) (ofQ T hTd)) (Rmul δ δ))
        (Rmul (Rmul (ofQ T hTd) (ofQ T hTd)) δ) := Rmul_le_Rmul_left hTTnn hddle
    have e3 : Req (Rmul (Rmul (ofQ T hTd) (ofQ T hTd)) δ) (Rmul (ofQ (mul T T) hT2d) δ) :=
      Rmul_congr (Rmul_ofQ_ofQ hTd hTd) (Req_refl δ)
    exact Rle_trans (Rle_of_Req e1) (Rle_trans step2 (Rle_of_Req e3))
  -- b² ≤ ofQ(T·T)·δ
  have hbb2 : Rle (Rmul b b) (Rmul (ofQ (mul T T) hT2d) δ) := Rle_trans hbb hTd2
  -- =============== Bound U = 4d + 3b² ===============
  -- 4d ≤ 4·(sb·δ) ≈ ofQ(4·sb)·δ
  have hsbdd : 0 < (mul (⟨4, 1⟩ : Q) sb).den := Qmul_den_pos (by decide) hsbd
  have hU1 : Rle (Rmul four d) (Rmul (ofQ (mul (⟨4, 1⟩ : Q) sb) hsbdd) δ) := by
    have s1 : Rle d (Rmul (ofQ sb hsbd) δ) := Rmul_le_Rmul_right hδnn hsb
    have s2 : Rle (Rmul four d) (Rmul four (Rmul (ofQ sb hsbd) δ)) :=
      Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) s1
    have e3 : Req (Rmul four (Rmul (ofQ sb hsbd) δ)) (Rmul (ofQ (mul (⟨4, 1⟩ : Q) sb) hsbdd) δ) :=
      Req_trans (Req_symm (Rmul_assoc four (ofQ sb hsbd) δ))
        (Rmul_congr (Rmul_ofQ_ofQ (by decide) hsbd) (Req_refl δ))
    exact Rle_trans s2 (Rle_of_Req e3)
  -- 3b² ≤ 3·(ofQ(T²)·δ) ≈ ofQ(3·T²)·δ
  have h3T2d : 0 < (mul (⟨3, 1⟩ : Q) (mul T T)).den := Qmul_den_pos (by decide) hT2d
  have hU2 : Rle (Rmul three (Rmul b b)) (Rmul (ofQ (mul (⟨3, 1⟩ : Q) (mul T T)) h3T2d) δ) := by
    have s2 : Rle (Rmul three (Rmul b b)) (Rmul three (Rmul (ofQ (mul T T) hT2d) δ)) :=
      Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) hbb2
    have e3 : Req (Rmul three (Rmul (ofQ (mul T T) hT2d) δ))
        (Rmul (ofQ (mul (⟨3, 1⟩ : Q) (mul T T)) h3T2d) δ) :=
      Req_trans (Req_symm (Rmul_assoc three (ofQ (mul T T) hT2d) δ))
        (Rmul_congr (Rmul_ofQ_ofQ (by decide) hT2d) (Req_refl δ))
    exact Rle_trans s2 (Rle_of_Req e3)
  -- U ≤ ofQ(4sb)·δ + ofQ(3T²)·δ ≈ ofQ(4sb + 3T²)·δ
  let Cu : Q := add (mul (⟨4, 1⟩ : Q) sb) (mul (⟨3, 1⟩ : Q) (mul T T))
  have hCud : 0 < Cu.den := add_den_pos hsbdd h3T2d
  have hU : Rle (Radd (Rmul four d) (Rmul three (Rmul b b))) (Rmul (ofQ Cu hCud) δ) := by
    have hsum : Rle (Radd (Rmul four d) (Rmul three (Rmul b b)))
        (Radd (Rmul (ofQ (mul (⟨4, 1⟩ : Q) sb) hsbdd) δ) (Rmul (ofQ (mul (⟨3, 1⟩ : Q) (mul T T)) h3T2d) δ)) :=
      Radd_le_add hU1 hU2
    have e : Req (Radd (Rmul (ofQ (mul (⟨4, 1⟩ : Q) sb) hsbdd) δ) (Rmul (ofQ (mul (⟨3, 1⟩ : Q) (mul T T)) h3T2d) δ))
        (Rmul (ofQ Cu hCud) δ) :=
      Req_trans (Req_symm (Rmul_distrib_right (ofQ (mul (⟨4, 1⟩ : Q) sb) hsbdd)
          (ofQ (mul (⟨3, 1⟩ : Q) (mul T T)) h3T2d) δ))
        (Rmul_congr (Radd_ofQ_ofQ hsbdd h3T2d) (Req_refl δ))
    exact Rle_trans hsum (Rle_of_Req e)
  -- =============== Bound M = (1 + 3b²)·Td ===============
  -- 1 + 3b² ≤ 1 + 3T²  (b² ≤ T²δ ≤ T², using δ ≤ 1)
  -- first b² ≤ ofQ(T²)  (from b² ≤ ofQ(T²)·δ ≤ ofQ(T²)·1 ≈ ofQ(T²))
  have hbbT2 : Rle (Rmul b b) (ofQ (mul T T) hT2d) := by
    have s1 : Rle (Rmul (ofQ (mul T T) hT2d) δ) (Rmul (ofQ (mul T T) hT2d) one) :=
      Rmul_le_Rmul_left (Rnonneg_ofQ hT2d (by
        show (0 : Int) ≤ T.num * T.num
        exact Int.mul_nonneg hT0 hT0)) hδ1
    exact Rle_trans hbb2 (Rle_trans s1 (Rle_of_Req (Rmul_one (ofQ (mul T T) hT2d))))
  -- 3b² ≤ ofQ(3·T²)
  have h3bbT2 : Rle (Rmul three (Rmul b b)) (ofQ (mul (⟨3, 1⟩ : Q) (mul T T)) h3T2d) := by
    have s2 : Rle (Rmul three (Rmul b b)) (Rmul three (ofQ (mul T T) hT2d)) :=
      Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) hbbT2
    exact Rle_trans s2 (Rle_of_Req (Rmul_ofQ_ofQ (by decide) hT2d))
  -- 1 + 3b² ≤ ofQ(1) + ofQ(3T²) ≈ ofQ(1 + 3T²)
  have h1pd : 0 < (add (⟨1, 1⟩ : Q) (mul (⟨3, 1⟩ : Q) (mul T T))).den := add_den_pos (by decide) h3T2d
  have hfac : Rle (Radd one (Rmul three (Rmul b b)))
      (ofQ (add (⟨1, 1⟩ : Q) (mul (⟨3, 1⟩ : Q) (mul T T))) h1pd) := by
    have hone : Req one (ofQ (⟨1, 1⟩ : Q) (by decide)) := Req_refl one
    have hsum : Rle (Radd one (Rmul three (Rmul b b)))
        (Radd (ofQ (⟨1, 1⟩ : Q) (by decide)) (ofQ (mul (⟨3, 1⟩ : Q) (mul T T)) h3T2d)) :=
      Radd_le_add (Rle_of_Req hone) h3bbT2
    exact Rle_trans hsum (Rle_of_Req (Radd_ofQ_ofQ (by decide) h3T2d))
  -- M = fac · Td ≤ ofQ(1+3T²) · (ofQ T · δ) ≈ ofQ((1+3T²)·T) · δ
  let Cm : Q := mul (add (⟨1, 1⟩ : Q) (mul (⟨3, 1⟩ : Q) (mul T T))) T
  have hCmd : 0 < Cm.den := Qmul_den_pos h1pd hTd
  have hM : Rle (Rmul (Radd one (Rmul three (Rmul b b))) Td) (Rmul (ofQ Cm hCmd) δ) := by
    -- monotone in left factor (Td ≥ 0)
    have hTdnn : Rnonneg Td := Rnonneg_Rmul hTnn hδnn
    have s1 : Rle (Rmul (Radd one (Rmul three (Rmul b b))) Td)
        (Rmul (ofQ (add (⟨1, 1⟩ : Q) (mul (⟨3, 1⟩ : Q) (mul T T))) h1pd) Td) :=
      Rmul_le_Rmul_right hTdnn hfac
    -- ofQ(1+3T²) · (ofQ T · δ) ≈ (ofQ(1+3T²) · ofQ T) · δ ≈ ofQ((1+3T²)·T) · δ
    have e : Req (Rmul (ofQ (add (⟨1, 1⟩ : Q) (mul (⟨3, 1⟩ : Q) (mul T T))) h1pd) Td)
        (Rmul (ofQ Cm hCmd) δ) :=
      Req_trans (Req_symm (Rmul_assoc (ofQ (add (⟨1, 1⟩ : Q) (mul (⟨3, 1⟩ : Q) (mul T T))) h1pd) (ofQ T hTd) δ))
        (Rmul_congr (Rmul_ofQ_ofQ h1pd hTd) (Req_refl δ))
    exact Rle_trans s1 (Rle_of_Req e)
  -- =============== Combine U + M ≤ ofQ(Cu + Cm) · δ ===============
  let C : Q := add Cu Cm
  have hCd : 0 < C.den := add_den_pos hCud hCmd
  have hUM : Rle (Radd (Radd (Rmul four d) (Rmul three (Rmul b b)))
        (Rmul (Radd one (Rmul three (Rmul b b))) Td)) (Rmul (ofQ C hCd) δ) := by
    have hsum : Rle (Radd (Radd (Rmul four d) (Rmul three (Rmul b b)))
          (Rmul (Radd one (Rmul three (Rmul b b))) Td))
        (Radd (Rmul (ofQ Cu hCud) δ) (Rmul (ofQ Cm hCmd) δ)) :=
      Radd_le_add hU hM
    have e : Req (Radd (Rmul (ofQ Cu hCud) δ) (Rmul (ofQ Cm hCmd) δ)) (Rmul (ofQ C hCd) δ) :=
      Req_trans (Req_symm (Rmul_distrib_right (ofQ Cu hCud) (ofQ Cm hCmd) δ))
        (Rmul_congr (Radd_ofQ_ofQ hCud hCmd) (Req_refl δ))
    exact Rle_trans hsum (Rle_of_Req e)
  -- =============== Lift through A = exp(...) ≥ 0 ===============
  refine ⟨C, hCd, ?_⟩
  -- Vterm s n hn Td is defeq to Rmul A (Radd U M)
  show Rle (Rmul A (Radd (Radd (Rmul four d) (Rmul three (Rmul b b)))
        (Rmul (Radd one (Rmul three (Rmul b b))) Td)))
      (Rmul A (Rmul (ofQ C hCd) δ))
  exact Rmul_le_Rmul_left (RexpReal_nonneg _) hUM

-- ===========================================================================
-- Step 7b-ii(β-2c) — the η geometric ratio: u = exp(−σ·log2) ≤ 1/(1+τ) < 1 for σ > 0 (Pos s.re).
-- (czetaU s IS exactly u.) Unlike czeta's 2u (needs σ>1), the η dyadic ratio is u itself — the δ_n ≤ 2⁻ᵏ
-- factor cancels the 2ᵏ block size — so it is < 1 for every σ > 0 (the critical strip). Mirrors
-- czeta_theta_ge + czetaU_2u_le_of_theta with θ = σ·log2 (not (σ−1)·log2).
-- ===========================================================================

/-- **The η dyadic ratio `u = exp(−Re s·log 2) ≤ 1/(1+τ) < 1`** for some rational `τ > 0`, whenever
    `Re s > 0`. The `θ = Re s·log 2 ≥ ε/2` lower bound (from `Pos(Re s)` via `Pos_imp_ofQ_le`, `log2 ≥ ½`)
    feeds `Rexp_neg_le_ratio`. -/
theorem etaU_le_ratio (s : Complex) (hs : Pos s.re) :
    ∃ (τ : Q) (hτd : 0 < τ.den) (hτn : 0 < τ.num),
      Rle (czetaU s)
        (ofQ (Qinv (add ⟨1, 1⟩ τ)) (Qinv_den_pos (by simp only [add]; push_cast; omega))) := by
  obtain ⟨ε, hεd, hεn, hε⟩ := Pos_imp_ofQ_le hs
  refine ⟨mul ε ⟨1, 2⟩, Qmul_den_pos hεd (by decide), by simp only [mul]; omega, ?_⟩
  have hθ : Rle (ofQ (mul ε (⟨1, 2⟩ : Q)) (Qmul_den_pos hεd (by decide)))
      (Rmul s.re (logN 2 (by omega))) := by
    refine Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ hεd (by decide)))) ?_
    exact Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ hεd (Int.le_of_lt hεn)) logN_2_ge_half)
      (Rmul_le_Rmul_right (Rnonneg_logN 2 (by omega)) hε)
  exact Rexp_neg_le_ratio (by simp only [mul]; omega) (Qmul_den_pos hεd (by decide)) hθ

end UOR.Bridge.F1Square.Analysis
