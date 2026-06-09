/-
F1 square — **v0.15.1: toward `exp∘log = id`** (the ζ-convergence gate).

`exp(log n) = n` is the bound that makes `Σ n^{-s}` converge for `Re s > 1`. Because `log` is built
independently (`log x = 2·artanh((x−1)/(x+1))`, `Log.lean`), this is a genuine power-series composition,
not a definitional identity. This file assembles the pieces toward it. First brick: the **congruence**
`exp` respects `≈` (`RexpReal_congr`) — needed to substitute log-equalities under `exp` — and the
**reciprocal law** `exp(−y)·exp(y) ≈ 1` (`RexpReal_mul_neg`, from the keystone `RexpReal_add`).

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.ExpRealAdd
import F1Square.Analysis.ComplexExp
import F1Square.Analysis.Log

namespace UOR.Bridge.F1Square.Analysis

/-- `0 + a ≈ a`. -/
theorem Qzero_add (a : Q) : Qeq (add ⟨0, 1⟩ a) a := by simp only [Qeq, add]; push_cast; ring_uor

/-- Commutativity of `ℚ` addition (up to `≈`). -/
theorem Qadd_comm (a b : Q) : Qeq (add a b) (add b a) := by simp only [Qeq, add]; push_cast; ring_uor

/-- Commutativity of `ℚ` multiplication (up to `≈`). -/
theorem Qmul_comm (a b : Q) : Qeq (mul a b) (mul b a) := by simp only [Qeq, mul]; push_cast; ring_uor

/-- Associativity of `ℚ` multiplication (up to `≈`). -/
theorem Qmul_assoc (a b c : Q) : Qeq (mul (mul a b) c) (mul a (mul b c)) := by
  simp only [Qeq, mul]; push_cast; ring_uor

/-- **`exp` respects Bishop equality**: `x ≈ y ⇒ exp x ≈ exp y`. The two exp diagonals are reconciled
    through a common deep depth `D = Rₓ + R_y`: depth tails on each side (`expSum_trunc_bound`,
    `RexpReal_trunc_le`) and the Lipschitz middle (`expSum_Lip_le`, `LipS ≤ U`) with the argument gap
    `|xₐ − yᵦ| ≤ 4/(n+1)` (regularity `xreg_n_le` + the hypothesis `h`). -/
theorem RexpReal_congr {x y : Real} (h : Req x y) : Req (RexpReal x) (RexpReal y) := by
  refine Req_of_lin_bound
    (C := 1 + 4 * (expM_U (xBound x + xBound y) (2 * (xBound x + xBound y))).num.toNat) ?_
  intro n
  show Qle (Qabs (Qsub (expSum (x.seq (RexpReal_R x n)) (RexpReal_R x n))
      (expSum (y.seq (RexpReal_R y n)) (RexpReal_R y n)))) _
  have hRxn : n ≤ RexpReal_R x n := n_le_RexpReal_R x n
  have hRyn : n ≤ RexpReal_R y n := n_le_RexpReal_R y n
  have hxLe : Qle (Qabs (x.seq (RexpReal_R x n))) ⟨((xBound x + xBound y : Nat) : Int), 1⟩ :=
    canon_bound_le (Nat.le_add_right _ _) _
  have hyLe : Qle (Qabs (y.seq (RexpReal_R y n))) ⟨((xBound x + xBound y : Nat) : Int), 1⟩ :=
    canon_bound_le (Nat.le_add_left _ _) _
  -- piece 1: |exp(xₐ, Rₓ) − exp(xₐ, D)| ≤ 1/(2(n+1))
  have hP1 : Qle (Qabs (Qsub (expSum (x.seq (RexpReal_R x n)) (RexpReal_R x n))
      (expSum (x.seq (RexpReal_R x n)) (RexpReal_R x n + RexpReal_R y n)))) ⟨1, 2 * (n + 1)⟩ := by
    rw [Qabs_Qsub_comm]
    exact Qle_trans (fct_pos _)
      (expSum_trunc_bound (M := xBound x) (x.den_pos _) (canon_bound x _)
        (a := RexpReal_R x n) (b := RexpReal_R x n + RexpReal_R y n) (by unfold RexpReal_R; omega) (by omega))
      (RexpReal_trunc_le x n)
  -- piece 3: |exp(yᵦ, D) − exp(yᵦ, R_y)| ≤ 1/(2(n+1))
  have hP3 : Qle (Qabs (Qsub (expSum (y.seq (RexpReal_R y n)) (RexpReal_R x n + RexpReal_R y n))
      (expSum (y.seq (RexpReal_R y n)) (RexpReal_R y n)))) ⟨1, 2 * (n + 1)⟩ :=
    Qle_trans (fct_pos _)
      (expSum_trunc_bound (M := xBound y) (y.den_pos _) (canon_bound y _)
        (a := RexpReal_R y n) (b := RexpReal_R x n + RexpReal_R y n) (by unfold RexpReal_R; omega) (by omega))
      (RexpReal_trunc_le y n)
  -- argument gap: |xₐ − yᵦ| ≤ 4/(n+1)
  have hh : Qle (Qabs (Qsub (x.seq (RexpReal_R y n)) (y.seq (RexpReal_R y n)))) ⟨2, n + 1⟩ :=
    Qle_trans (b := (⟨2, RexpReal_R y n + 1⟩ : Q)) (by omega : (0:Nat) < RexpReal_R y n + 1)
      (h (RexpReal_R y n)) (by simp only [Qle]; push_cast; omega)
  have hargs : Qle (Qabs (Qsub (x.seq (RexpReal_R x n)) (y.seq (RexpReal_R y n)))) ⟨4, n + 1⟩ := by
    refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (x.den_pos _) (x.den_pos _)))
        (Qabs_den_pos (Qsub_den_pos (x.den_pos _) (y.den_pos _))))
      (Qabs_sub_triangle (a := x.seq (RexpReal_R x n)) (b := x.seq (RexpReal_R y n))
        (c := y.seq (RexpReal_R y n)) (x.den_pos _) (x.den_pos _) (y.den_pos _)) ?_
    refine Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n))
      (Qadd_le_add (xreg_n_le x hRxn hRyn) hh) (Qeq_le ?_)
    simp only [Qeq, add]; push_cast; ring_uor
  -- piece 2: Lipschitz middle ≤ U·4/(n+1)
  have hLip : Qle (LipS (xBound x + xBound y) (RexpReal_R x n + RexpReal_R y n))
      ⟨((expM_U (xBound x + xBound y) (2 * (xBound x + xBound y))).num.toNat : Int), 1⟩ :=
    Qle_trans (expM_U_den_pos _ _) (LipS_le_U _ _) (Qle_toNat (expM_U_num_nonneg _ _) (expM_U_den_pos _ _))
  have hP2 : Qle (Qabs (Qsub (expSum (x.seq (RexpReal_R x n)) (RexpReal_R x n + RexpReal_R y n))
      (expSum (y.seq (RexpReal_R y n)) (RexpReal_R x n + RexpReal_R y n))))
      (mul ⟨((expM_U (xBound x + xBound y) (2 * (xBound x + xBound y))).num.toNat : Int), 1⟩ ⟨4, n + 1⟩) := by
    refine Qle_trans (Qmul_den_pos (LipS_den_pos _ _) (Qabs_den_pos (Qsub_den_pos (x.den_pos _) (y.den_pos _))))
      (expSum_Lip_le (x.den_pos _) (y.den_pos _) hxLe hyLe _) ?_
    exact Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos (x.den_pos _) (y.den_pos _))))
      (Qmul_le_mul_right (Qabs_num_nonneg _) hLip) (Qmul_le_mul_left (Int.ofNat_nonneg _) hargs)
  -- assemble: piece1 + (piece2 + piece3)
  have h2 : 0 < 2 * (n + 1) := by omega
  have hRest : Qle (Qabs (Qsub (expSum (x.seq (RexpReal_R x n)) (RexpReal_R x n + RexpReal_R y n))
      (expSum (y.seq (RexpReal_R y n)) (RexpReal_R y n))))
      (add (mul ⟨((expM_U (xBound x + xBound y) (2 * (xBound x + xBound y))).num.toNat : Int), 1⟩ ⟨4, n + 1⟩)
        ⟨1, 2 * (n + 1)⟩) :=
    Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (expSum_den_pos (x.den_pos _) _)
        (expSum_den_pos (y.den_pos _) _))) (Qabs_den_pos (Qsub_den_pos (expSum_den_pos (y.den_pos _) _)
        (expSum_den_pos (y.den_pos _) _))))
      (Qabs_sub_triangle
        (a := expSum (x.seq (RexpReal_R x n)) (RexpReal_R x n + RexpReal_R y n))
        (b := expSum (y.seq (RexpReal_R y n)) (RexpReal_R x n + RexpReal_R y n))
        (c := expSum (y.seq (RexpReal_R y n)) (RexpReal_R y n))
        (expSum_den_pos (x.den_pos _) _) (expSum_den_pos (y.den_pos _) _)
        (expSum_den_pos (y.den_pos _) _)) (Qadd_le_add hP2 hP3)
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (expSum_den_pos (x.den_pos _) _)
      (expSum_den_pos (x.den_pos _) _))) (Qabs_den_pos (Qsub_den_pos (expSum_den_pos (x.den_pos _) _)
      (expSum_den_pos (y.den_pos _) _))))
    (Qabs_sub_triangle
      (a := expSum (x.seq (RexpReal_R x n)) (RexpReal_R x n))
      (b := expSum (x.seq (RexpReal_R x n)) (RexpReal_R x n + RexpReal_R y n))
      (c := expSum (y.seq (RexpReal_R y n)) (RexpReal_R y n))
      (expSum_den_pos (x.den_pos _) _) (expSum_den_pos (x.den_pos _) _)
      (expSum_den_pos (y.den_pos _) _)) ?_
  refine Qle_trans (add_den_pos h2 (add_den_pos (Qmul_den_pos Nat.one_pos (Nat.succ_pos n)) h2))
    (Qadd_le_add hP1 hRest) (Qeq_le ?_)
  simp only [Qeq, add, mul]; push_cast; ring_uor

/-- **The reciprocal law** `exp(−y)·exp(y) ≈ 1`: from the homomorphism keystone `RexpReal_add` at
    `(−y, y)` and `exp 0 ≈ 1`. Hence `exp(−y)` is the multiplicative inverse of `exp y`. -/
theorem RexpReal_mul_neg (y : Real) : Req (Rmul (RexpReal (Rneg y)) (RexpReal y)) one :=
  Req_trans (Req_symm (RexpReal_add (Rneg y) y))
    (Req_trans (RexpReal_congr (Req_trans (Radd_comm (Rneg y) y) (Radd_neg y))) RexpReal_zero)

/-- The finite geometric sum `Σ_{k=0}^N wᵏ`. -/
def gPow (w : Q) : Nat → Q
  | 0 => ⟨1, 1⟩
  | (n + 1) => add (gPow w n) (qpow w (n + 1))

theorem gPow_den_pos {w : Q} (hwd : 0 < w.den) : ∀ N, 0 < (gPow w N).den
  | 0 => Nat.one_pos
  | (n + 1) => add_den_pos (gPow_den_pos hwd n) (qpow_den_pos hwd (n + 1))

theorem gPow_num_nonneg {w : Q} (hw0 : 0 ≤ w.num) : ∀ N, 0 ≤ (gPow w N).num
  | 0 => by show (0 : Int) ≤ 1; decide
  | (n + 1) => by
      show 0 ≤ (gPow w n).num * ((qpow w (n + 1)).den : Int)
          + (qpow w (n + 1)).num * ((gPow w n).den : Int)
      exact Int.add_nonneg
        (Int.mul_nonneg (gPow_num_nonneg hw0 n) (Int.ofNat_nonneg _))
        (Int.mul_nonneg (qpow_nonneg hw0 (n + 1)) (Int.ofNat_nonneg _))

/-- **The geometric telescoping closed form**: `(Σ_{k=0}^N wᵏ)·(1 − w) = 1 − w^{N+1}`. -/
theorem gPow_telescope {w : Q} (hwd : 0 < w.den) :
    ∀ N, Qeq (mul (gPow w N) (Qsub ⟨1, 1⟩ w)) (Qsub ⟨1, 1⟩ (qpow w (N + 1)))
  | 0 => by
      show Qeq (mul (⟨1, 1⟩ : Q) (Qsub ⟨1, 1⟩ w)) (Qsub ⟨1, 1⟩ (mul w ⟨1, 1⟩))
      simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor
  | (N + 1) => by
      show Qeq (mul (add (gPow w N) (qpow w (N + 1))) (Qsub ⟨1, 1⟩ w))
        (Qsub ⟨1, 1⟩ (mul w (qpow w (N + 1))))
      have hd1w : 0 < (Qsub (⟨1, 1⟩ : Q) w).den := Qsub_den_pos Nat.one_pos hwd
      have hqp : 0 < (qpow w (N + 1)).den := qpow_den_pos hwd (N + 1)
      have hgp : 0 < (gPow w N).den := gPow_den_pos hwd N
      have hdistrib : Qeq (mul (add (gPow w N) (qpow w (N + 1))) (Qsub ⟨1, 1⟩ w))
          (add (mul (gPow w N) (Qsub ⟨1, 1⟩ w)) (mul (qpow w (N + 1)) (Qsub ⟨1, 1⟩ w))) := by
        simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor
      have hfin : Qeq (add (Qsub ⟨1, 1⟩ (qpow w (N + 1))) (mul (qpow w (N + 1)) (Qsub ⟨1, 1⟩ w)))
          (Qsub ⟨1, 1⟩ (mul w (qpow w (N + 1)))) := by
        simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor
      exact Qeq_trans (add_den_pos (Qmul_den_pos hgp hd1w) (Qmul_den_pos hqp hd1w)) hdistrib
        (Qeq_trans (add_den_pos (Qsub_den_pos Nat.one_pos hqp) (Qmul_den_pos hqp hd1w))
          (Qadd_congr (gPow_telescope hwd N) (Qeq_refl _)) hfin)

-- ===========================================================================
-- Formal power series calculus (coefficient sequences `Nat → Q`), toward the
-- chain rule `(exp∘a)' = a'·(exp∘a)` that pins exp(2·artanh w) = (1+w)/(1−w).
-- ===========================================================================

/-- The **formal derivative** of a power series: `(c')ₖ = (k+1)·c_{k+1}`. -/
def fderiv (c : Nat → Q) (k : Nat) : Q := mul ⟨(k + 1 : Int), 1⟩ (c (k + 1))

/-- The **formal (Cauchy) product** of two power series: `(a·b)ₖ = Σ_{i≤k} aᵢ·b_{k−i}`. -/
def fmul (a b : Nat → Q) (k : Nat) : Q := Fsum (fun i => mul (a i) (b (k - i))) k

theorem fderiv_den_pos {c : Nat → Q} (hc : ∀ i, 0 < (c i).den) (k : Nat) : 0 < (fderiv c k).den :=
  Qmul_den_pos Nat.one_pos (hc (k + 1))

theorem fmul_den_pos {a b : Nat → Q} (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den) (k : Nat) :
    0 < (fmul a b k).den := Fsum_den_pos (fun i => Qmul_den_pos (ha i) (hb (k - i))) k

/-- **The Leibniz product rule for formal power series**: `(a·b)' = a'·b + a·b'`. -/
theorem fderiv_fmul (a b : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den) (k : Nat) :
    Qeq (fderiv (fmul a b) k) (add (fmul (fderiv a) b k) (fmul a (fderiv b) k)) := by
  have hT : ∀ i, 0 < (mul (a i) (b (k + 1 - i))).den := fun i => Qmul_den_pos (ha i) (hb _)
  have hTL : ∀ i, 0 < (mul (⟨((i : Nat) : Int), 1⟩ : Q) (mul (a i) (b (k + 1 - i)))).den :=
    fun i => Qmul_den_pos Nat.one_pos (hT i)
  have hTR : ∀ i, 0 < (mul (⟨((k + 1 - i : Nat) : Int), 1⟩ : Q) (mul (a i) (b (k + 1 - i)))).den :=
    fun i => Qmul_den_pos Nat.one_pos (hT i)
  have hTk1 : ∀ i, 0 < (mul (⟨(k + 1 : Int), 1⟩ : Q) (mul (a i) (b (k + 1 - i)))).den :=
    fun i => Qmul_den_pos Nat.one_pos (hT i)
  -- left factor sum  Σ_{i≤k+1} i·(aᵢ b_{k+1−i})  =  a'·b at k
  have hLeft : Qeq (Fsum (fun i => mul (⟨((i : Nat) : Int), 1⟩ : Q) (mul (a i) (b (k + 1 - i)))) (k + 1))
      (fmul (fderiv a) b k) := by
    refine Qeq_trans (add_den_pos (hTL 0) (Fsum_den_pos (fun i => hTL (i + 1)) k)) (Fsum_front hTL k) ?_
    refine Qeq_trans (add_den_pos Nat.one_pos (fmul_den_pos (fun i => fderiv_den_pos ha i) hb k)) (Qadd_congr
        (show Qeq (mul (⟨((0 : Nat) : Int), 1⟩ : Q) (mul (a 0) (b (k + 1 - 0)))) (⟨0, 1⟩ : Q) by
          simp only [Qeq, mul]; push_cast; ring_uor)
        (Fsum_congr_le (fun i _ =>
          show Qeq (mul (⟨((i + 1 : Nat) : Int), 1⟩ : Q) (mul (a (i + 1)) (b (k + 1 - (i + 1)))))
              (mul (fderiv a i) (b (k - i))) by
            show Qeq (mul (⟨((i + 1 : Nat) : Int), 1⟩ : Q) (mul (a (i + 1)) (b (k + 1 - (i + 1)))))
              (mul (mul (⟨((i + 1 : Nat) : Int), 1⟩ : Q) (a (i + 1))) (b (k - i)))
            rw [Nat.succ_sub_succ]; simp only [Qeq, mul]; push_cast; ring_uor))) ?_
    exact Qzero_add (fmul (fderiv a) b k)
  -- right factor sum  Σ_{i≤k+1} (k+1−i)·(aᵢ b_{k+1−i})  =  a·b' at k
  have hRight : Qeq (Fsum (fun i => mul (⟨((k + 1 - i : Nat) : Int), 1⟩ : Q) (mul (a i) (b (k + 1 - i)))) (k + 1))
      (fmul a (fderiv b) k) := by
    show Qeq (add (Fsum (fun i => mul (⟨((k + 1 - i : Nat) : Int), 1⟩ : Q) (mul (a i) (b (k + 1 - i)))) k)
        (mul (⟨((k + 1 - (k + 1) : Nat) : Int), 1⟩ : Q) (mul (a (k + 1)) (b (k + 1 - (k + 1))))))
      (fmul a (fderiv b) k)
    refine Qeq_trans (add_den_pos (Fsum_den_pos hTR k) Nat.one_pos) (Qadd_congr (Qeq_refl _)
        (show Qeq (mul (⟨((k + 1 - (k + 1) : Nat) : Int), 1⟩ : Q) (mul (a (k + 1)) (b (k + 1 - (k + 1))))) (⟨0, 1⟩ : Q) by
          rw [Nat.sub_self]; simp only [Qeq, mul]; push_cast; ring_uor)) ?_
    refine Qeq_trans (Fsum_den_pos hTR k) (Qadd_zero_right
        (Fsum (fun i => mul (⟨((k + 1 - i : Nat) : Int), 1⟩ : Q) (mul (a i) (b (k + 1 - i)))) k)) ?_
    refine Fsum_congr_le (fun i hi => ?_)
    have hidx : k + 1 - i = (k - i) + 1 := by omega
    rw [hidx]
    show Qeq (mul (⟨(((k - i) + 1 : Nat) : Int), 1⟩ : Q) (mul (a i) (b ((k - i) + 1))))
      (mul (a i) (mul (⟨((k - i : Nat) : Int) + 1, 1⟩ : Q) (b ((k - i) + 1))))
    simp only [Qeq, mul]; push_cast; ring_uor
  -- assemble: (k+1)·Σ T = Σ (i + (k+1−i))·T = hLeft + hRight
  show Qeq (mul (⟨(k + 1 : Int), 1⟩ : Q) (Fsum (fun i => mul (a i) (b (k + 1 - i))) (k + 1)))
    (add (fmul (fderiv a) b k) (fmul a (fderiv b) k))
  refine Qeq_trans (Fsum_den_pos hTk1 (k + 1))
    (Qeq_symm (Fsum_mul_left (c := (⟨(k + 1 : Int), 1⟩ : Q)) Nat.one_pos hT (k + 1))) ?_
  refine Qeq_trans (Fsum_den_pos (fun i => add_den_pos (hTL i) (hTR i)) (k + 1))
    (Fsum_congr_le (k := k + 1) (fun i hi => by
      have hcoef : Qeq (add (⟨((i : Nat) : Int), 1⟩ : Q) (⟨((k + 1 - i : Nat) : Int), 1⟩ : Q))
          (⟨(k + 1 : Int), 1⟩ : Q) := by simp only [Qeq, add]; push_cast; omega
      exact Qeq_trans (Qmul_den_pos (add_den_pos Nat.one_pos Nat.one_pos) (hT i))
        (Qmul_congr (Qeq_symm hcoef) (Qeq_refl (mul (a i) (b (k + 1 - i)))))
        (Qmul_add_right (⟨((i : Nat) : Int), 1⟩ : Q) (⟨((k + 1 - i : Nat) : Int), 1⟩ : Q)
          (mul (a i) (b (k + 1 - i)))))) ?_
  refine Qeq_trans (add_den_pos (Fsum_den_pos hTL (k + 1)) (Fsum_den_pos hTR (k + 1)))
    (Fsum_add hTL hTR (k + 1)) ?_
  exact Qadd_congr hLeft hRight

/-- **Sum reversal**: `Σ_{i=0}^{k} fᵢ ≈ Σ_{i=0}^{k} f_{k−i}`. -/
theorem Fsum_reverse {f : Nat → Q} (hf : ∀ i, 0 < (f i).den) :
    ∀ k, Qeq (Fsum f k) (Fsum (fun i => f (k - i)) k)
  | 0 => Qeq_refl _
  | (k + 1) => by
      have hrev := Fsum_reverse hf k
      have hRHS : Qeq (Fsum (fun i => f (k + 1 - i)) (k + 1))
          (add (f (k + 1)) (Fsum (fun i => f (k - i)) k)) := by
        refine Qeq_trans (add_den_pos (hf (k + 1 - 0)) (Fsum_den_pos (fun i => hf (k + 1 - (i + 1))) k))
          (Fsum_front (fun i => hf (k + 1 - i)) k) (Qadd_congr (Qeq_refl _)
          (Fsum_congr_le (fun i hi => ?_)))
        have hidx : k + 1 - (i + 1) = k - i := by omega
        rw [hidx]; exact Qeq_refl _
      exact Qeq_trans (add_den_pos (hf (k + 1)) (Fsum_den_pos (fun i => hf (k - i)) k))
        (Qeq_trans (add_den_pos (hf (k + 1)) (Fsum_den_pos hf k))
          (Qadd_comm (Fsum f k) (f (k + 1))) (Qadd_congr (Qeq_refl _) hrev))
        (Qeq_symm hRHS)

/-- **Commutativity of the formal Cauchy product**: `a·b ≈ b·a`. -/
theorem fmul_comm (a b : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den) (k : Nat) :
    Qeq (fmul a b k) (fmul b a k) := by
  show Qeq (Fsum (fun i => mul (a i) (b (k - i))) k) (Fsum (fun i => mul (b i) (a (k - i))) k)
  refine Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos (ha (k - i)) (hb (k - (k - i)))) k)
    (Fsum_reverse (fun i => Qmul_den_pos (ha i) (hb (k - i))) k)
    (Fsum_congr_le (fun i hi => ?_))
  have hidx : k - (k - i) = i := by omega
  show Qeq (mul (a (k - i)) (b (k - (k - i)))) (mul (b i) (a (k - i)))
  rw [hidx]
  exact Qmul_comm (a (k - i)) (b i)

/-- **Associativity of the formal Cauchy product**: `(a·b)·c ≈ a·(b·c)` — both are `Σ_{i+j+l=k} aᵢbⱼc_l`,
    connected by the triangle/antidiagonal reindex. -/
theorem fmul_assoc (a b c : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den)
    (hc : ∀ i, 0 < (c i).den) (k : Nat) :
    Qeq (fmul (fmul a b) c k) (fmul a (fmul b c) k) := by
  have hg : ∀ i j, 0 < (mul (mul (a i) (b j)) (c (k - (i + j)))).den :=
    fun i j => Qmul_den_pos (Qmul_den_pos (ha i) (hb j)) (hc _)
  have hLHS : Qeq (fmul (fmul a b) c k)
      (Fsum (fun m => Fsum (fun i => mul (mul (a i) (b (m - i))) (c (k - (i + (m - i))))) m) k) := by
    show Qeq (Fsum (fun m => mul (Fsum (fun i => mul (a i) (b (m - i))) m) (c (k - m))) k) _
    refine Fsum_congr_le (fun m hm => ?_)
    refine Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos (Qmul_den_pos (ha i) (hb (m - i))) (hc (k - m))) m)
      (Fsum_mul_const_right (hc (k - m)) (fun i => Qmul_den_pos (ha i) (hb (m - i))) m)
      (Fsum_congr_le (fun i hi => ?_))
    have hidx : k - (i + (m - i)) = k - m := by omega
    rw [hidx]; exact Qeq_refl _
  have hRHS : Qeq (fmul a (fmul b c) k)
      (Fsum (fun i => Fsum (fun j => mul (mul (a i) (b j)) (c (k - (i + j)))) (k - i)) k) := by
    show Qeq (Fsum (fun i => mul (a i) (Fsum (fun j => mul (b j) (c (k - i - j))) (k - i))) k) _
    refine Fsum_congr_le (fun i hi => ?_)
    refine Qeq_trans (Fsum_den_pos (fun j => Qmul_den_pos (ha i) (Qmul_den_pos (hb j) (hc (k - i - j)))) (k - i))
      (Qeq_symm (Fsum_mul_left (ha i) (fun j => Qmul_den_pos (hb j) (hc (k - i - j))) (k - i)))
      (Fsum_congr_le (fun j hj => ?_))
    have hidx : k - i - j = k - (i + j) := by omega
    rw [hidx]; exact Qeq_symm (Qmul_assoc (a i) (b j) (c (k - (i + j))))
  exact Qeq_trans (Fsum_den_pos (fun m => Fsum_den_pos (fun i => hg i (m - i)) m) k) hLHS
    (Qeq_trans (Fsum_den_pos (fun i => Fsum_den_pos (fun j => hg i j) (k - i)) k)
      (Qeq_symm (Fsum_triangle_reindex hg k)) (Qeq_symm hRHS))

/-- The formal power-series unit `1`: coefficient `1` at degree `0`, else `0`. -/
def fone (k : Nat) : Q := if k = 0 then ⟨1, 1⟩ else ⟨0, 1⟩

theorem fone_den_pos (k : Nat) : 0 < (fone k).den := by unfold fone; split <;> exact Nat.one_pos

/-- A finite sum of zeros is zero. -/
theorem Fsum_zeros : ∀ k, Qeq (Fsum (fun _ => (⟨0, 1⟩ : Q)) k) ⟨0, 1⟩
  | 0 => Qeq_refl _
  | (k + 1) => by
      show Qeq (add (Fsum (fun _ => (⟨0, 1⟩ : Q)) k) ⟨0, 1⟩) ⟨0, 1⟩
      exact Qeq_trans (Fsum_den_pos (fun _ => Nat.one_pos) k)
        (Qadd_zero_right _) (Fsum_zeros k)

/-- **The unit law for the formal Cauchy product**: `a·1 ≈ a`. -/
theorem fmul_one (a : Nat → Q) (ha : ∀ i, 0 < (a i).den) (k : Nat) : Qeq (fmul a fone k) (a k) := by
  cases k with
  | zero =>
      show Qeq (mul (a 0) (fone 0)) (a 0)
      show Qeq (mul (a 0) ⟨1, 1⟩) (a 0)
      simp only [Qeq, mul]; push_cast; ring_uor
  | succ n =>
      show Qeq (add (Fsum (fun i => mul (a i) (fone (n + 1 - i))) n)
        (mul (a (n + 1)) (fone (n + 1 - (n + 1))))) (a (n + 1))
      have hzeros : Qeq (Fsum (fun i => mul (a i) (fone (n + 1 - i))) n) ⟨0, 1⟩ := by
        refine Qeq_trans (Fsum_den_pos (fun _ => Nat.one_pos) n)
          (Fsum_congr_le (fun i hi => ?_)) (Fsum_zeros n)
        have hne : n + 1 - i ≠ 0 := by omega
        show Qeq (mul (a i) (fone (n + 1 - i))) ⟨0, 1⟩
        unfold fone; rw [if_neg hne]; simp only [Qeq, mul]; push_cast; ring_uor
      refine Qeq_trans (add_den_pos Nat.one_pos (Qmul_den_pos (ha (n + 1)) (fone_den_pos _)))
        (Qadd_congr hzeros (Qeq_refl _)) ?_
      refine Qeq_trans (Qmul_den_pos (ha (n + 1)) (fone_den_pos _)) (Qzero_add _) ?_
      rw [Nat.sub_self]
      show Qeq (mul (a (n + 1)) ⟨1, 1⟩) (a (n + 1))
      simp only [Qeq, mul]; push_cast; ring_uor

-- ===========================================================================
-- The formal coefficient identity: the (1+w)/(1−w) coefficients satisfy the
-- exp∘artanh chain-rule ODE  E' = (2/(1−w²))·E.
-- ===========================================================================

/-- `2/(1−w²)` coefficients — the formal derivative of the `2·artanh` series: `2` at even degree, `0` at odd. -/
def dexpderiv (k : Nat) : Q := ⟨(2 - 2 * (k % 2) : Nat), 1⟩

/-- The `exp(2·artanh w) = (1+w)/(1−w)` coefficients: `1` at degree 0, `2` after. -/
def dgeom (k : Nat) : Q := if k = 0 then ⟨1, 1⟩ else ⟨2, 1⟩

theorem dexpderiv_den (k : Nat) : 0 < (dexpderiv k).den := Nat.one_pos
theorem dgeom_den (k : Nat) : 0 < (dgeom k).den := by unfold dgeom; split <;> exact Nat.one_pos

/-- Partial sums of the `2/(1−w²)` coefficients: `Σ_{i≤k} = 2·⌊k/2⌋ + 2`. -/
theorem dexpderiv_sum : ∀ k, Qeq (Fsum dexpderiv k) ⟨(2 * (k / 2) + 2 : Nat), 1⟩
  | 0 => by show Qeq (dexpderiv 0) ⟨(2 * (0 / 2) + 2 : Nat), 1⟩; decide
  | (k + 1) => by
      show Qeq (add (Fsum dexpderiv k) (dexpderiv (k + 1))) ⟨(2 * ((k + 1) / 2) + 2 : Nat), 1⟩
      refine Qeq_trans (add_den_pos Nat.one_pos Nat.one_pos)
        (Qadd_congr (dexpderiv_sum k) (Qeq_refl _)) ?_
      show Qeq (add (⟨(2 * (k / 2) + 2 : Nat), 1⟩ : Q) ⟨(2 - 2 * ((k + 1) % 2) : Nat), 1⟩)
        ⟨(2 * ((k + 1) / 2) + 2 : Nat), 1⟩
      simp only [Qeq, add]; push_cast; omega

/-- **The formal coefficient identity**: the `(1+w)/(1−w)` coefficients `dgeom` satisfy the chain-rule
    ODE `E' = (2/(1−w²))·E` (`fderiv dgeom = dexpderiv · dgeom`) — i.e. `exp(2·artanh w)` formally *is*
    the geometric series. The parity recurrence `2(k+1) = Σ_{i≤k} dexpderivᵢ·dgeom_{k−i}`. -/
theorem dgeom_ode (k : Nat) : Qeq (fderiv dgeom k) (fmul dexpderiv dgeom k) := by
  have hLHS : Qeq (fderiv dgeom k) ⟨(2 * (k + 1) : Nat), 1⟩ := by
    show Qeq (mul ⟨(k + 1 : Int), 1⟩ (dgeom (k + 1))) ⟨(2 * (k + 1) : Nat), 1⟩
    have hg : dgeom (k + 1) = ⟨2, 1⟩ := by unfold dgeom; rw [if_neg (by omega)]
    rw [hg]; simp only [Qeq, mul]; push_cast; omega
  have hRHS : Qeq (fmul dexpderiv dgeom k) ⟨(2 * (k + 1) : Nat), 1⟩ := by
    cases k with
    | zero => show Qeq (mul (dexpderiv 0) (dgeom 0)) ⟨(2 * (0 + 1) : Nat), 1⟩; decide
    | succ n =>
        show Qeq (add (Fsum (fun i => mul (dexpderiv i) (dgeom (n + 1 - i))) n)
          (mul (dexpderiv (n + 1)) (dgeom (n + 1 - (n + 1))))) ⟨(2 * (n + 1 + 1) : Nat), 1⟩
        have hsum : Qeq (Fsum (fun i => mul (dexpderiv i) (dgeom (n + 1 - i))) n)
            (mul (Fsum dexpderiv n) ⟨2, 1⟩) := by
          refine Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos (dexpderiv_den i) (by decide)) n)
            (Fsum_congr_le (fun i hi => ?_))
            (Qeq_symm (Fsum_mul_const_right (by decide) (fun _ => Nat.one_pos) n))
          have hg : dgeom (n + 1 - i) = ⟨2, 1⟩ := by unfold dgeom; rw [if_neg (by omega)]
          rw [hg]; exact Qeq_refl _
        refine Qeq_trans (add_den_pos (Qmul_den_pos (Fsum_den_pos (fun i => dexpderiv_den i) n) (by decide))
            (Qmul_den_pos (dexpderiv_den _) (dgeom_den _))) (Qadd_congr hsum (Qeq_refl _)) ?_
        rw [Nat.sub_self]
        refine Qeq_trans (add_den_pos (Qmul_den_pos Nat.one_pos (by decide))
            (Qmul_den_pos (dexpderiv_den _) Nat.one_pos))
          (Qadd_congr (Qmul_congr (dexpderiv_sum n) (Qeq_refl _))
            (Qmul_congr (Qeq_refl _) (show Qeq (dgeom 0) ⟨1, 1⟩ by decide))) ?_
        show Qeq (add (mul (⟨(2 * (n / 2) + 2 : Nat), 1⟩ : Q) ⟨2, 1⟩)
          (mul ⟨(2 - 2 * ((n + 1) % 2) : Nat), 1⟩ ⟨1, 1⟩)) ⟨(2 * (n + 1 + 1) : Nat), 1⟩
        simp only [Qeq, add, mul]; push_cast; omega
  exact Qeq_trans Nat.one_pos hLHS (Qeq_symm hRHS)

-- ===========================================================================
-- Power-series evaluation  peval c w N = Σ_{k≤N} cₖ wᵏ, and the target side.
-- ===========================================================================

/-- **Partial evaluation** of a formal power series `c` at `w`: `Σ_{k=0}^N cₖ·wᵏ`. -/
def peval (c : Nat → Q) (w : Q) (N : Nat) : Q := Fsum (fun k => mul (c k) (qpow w k)) N

theorem peval_den_pos {c : Nat → Q} {w : Q} (hc : ∀ k, 0 < (c k).den) (hwd : 0 < w.den) (N : Nat) :
    0 < (peval c w N).den := Fsum_den_pos (fun k => Qmul_den_pos (hc k) (qpow_den_pos hwd k)) N

/-- **Eval congruence**: coefficientwise-equal series evaluate equally. -/
theorem peval_congr {a b : Nat → Q} (h : ∀ k, Qeq (a k) (b k)) (w : Q) (M : Nat) :
    Qeq (peval a w M) (peval b w M) :=
  Fsum_congr (fun k => Qmul_congr (h k) (Qeq_refl _)) M

/-- **Eval scalar-linearity**: `eval(c·a) = c·eval(a)`. -/
theorem peval_smul (c : Q) (hcd : 0 < c.den) (a : Nat → Q) (ha : ∀ k, 0 < (a k).den)
    (w : Q) (hwd : 0 < w.den) (M : Nat) :
    Qeq (peval (fun k => mul c (a k)) w M) (mul c (peval a w M)) :=
  Qeq_trans (Fsum_den_pos (fun k => Qmul_den_pos hcd (Qmul_den_pos (ha k) (qpow_den_pos hwd k))) M)
    (Fsum_congr (fun k => Qmul_assoc c (a k) (qpow w k)) M)
    (Fsum_mul_left hcd (fun k => Qmul_den_pos (ha k) (qpow_den_pos hwd k)) M)

/-- **Termwise sum monotonicity**: `f ≤ g` coordinatewise ⇒ `Σf ≤ Σg`. -/
theorem Fsum_le_Fsum {f g : Nat → Q} (h : ∀ i, Qle (f i) (g i)) : ∀ M, Qle (Fsum f M) (Fsum g M)
  | 0 => h 0
  | (M + 1) => Qadd_le_add (Fsum_le_Fsum h M) (h (M + 1))

/-- **Gap domination** (the general `artSum_abs_diff_le`): if `|fₖ| ≤ gₖ` then the partial-sum gap of `f`
    is dominated by the gap of `g`. -/
theorem Fsum_abs_diff_le {f g : Nat → Q} (hf : ∀ i, 0 < (f i).den) (hg : ∀ i, 0 < (g i).den)
    (hfg : ∀ i, Qle (Qabs (f i)) (g i)) {a b : Nat} (hab : a ≤ b) :
    Qle (Qabs (Qsub (Fsum f b) (Fsum f a))) (Qsub (Fsum g b) (Fsum g a)) := by
  induction hab with
  | refl =>
      have h := Qsub_self_num (Fsum f a)
      have h' := Qsub_self_num (Fsum g a)
      unfold Qle Qabs; rw [h, h']; simp
  | @step k _ ih =>
      have hstep : Qle (Qabs (Qsub (Fsum f (k + 1)) (Fsum f a)))
          (add (Qabs (Qsub (Fsum f k) (Fsum f a))) (Qabs (f (k + 1)))) :=
        Qle_congr_left (Qabs_den_pos (add_den_pos (Qsub_den_pos (Fsum_den_pos hf k)
            (Fsum_den_pos hf a)) (hf (k + 1))))
          (Qeq_symm (Qabs_Qeq (Qsub_add_right (Fsum f k) (f (k + 1)) (Fsum f a)))) (Qabs_add_le _ _)
      refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (Fsum_den_pos hf k) (Fsum_den_pos hf a)))
          (Qabs_den_pos (hf (k + 1)))) hstep
        (Qle_trans (add_den_pos (Qsub_den_pos (Fsum_den_pos hg k) (Fsum_den_pos hg a)) (hg (k + 1)))
          (Qadd_le_add ih (hfg (k + 1)))
          (Qeq_le (Qeq_symm (Qsub_add_right (Fsum g k) (g (k + 1)) (Fsum g a)))))

/-- **Geometric bound on evaluation**: if `|cₖ| ≤ B` and `|w| ≤ ρ`, then `|eval c w M| ≤ Σ_{k≤M} B·ρᵏ`. -/
theorem peval_abs_bound (c : Nat → Q) (hc : ∀ k, 0 < (c k).den) (w : Q) (hwd : 0 < w.den)
    {B ρ : Q} (hBd : 0 < B.den) (hρd : 0 < ρ.den) (hB : ∀ k, Qle (Qabs (c k)) B)
    (hw : Qle (Qabs w) ρ) (M : Nat) :
    Qle (Qabs (peval c w M)) (Fsum (fun k => mul B (qpow ρ k)) M) := by
  refine Qle_trans (Fsum_den_pos (fun k => Qabs_den_pos (Qmul_den_pos (hc k) (qpow_den_pos hwd k))) M)
    (Fsum_abs_le (fun k => Qmul_den_pos (hc k) (qpow_den_pos hwd k)) M) ?_
  refine Fsum_le_Fsum (fun k => ?_) M
  rw [Qabs_mul]
  exact Qmul_le_mul (Qabs_den_pos (hc k)) hBd (Qabs_den_pos (qpow_den_pos hwd k))
    (Qabs_num_nonneg _) (Qabs_num_nonneg _) (hB k)
    (Qle_trans (qpow_den_pos (Qabs_den_pos hwd) k) (Qeq_le (qpow_abs w k))
      (qpow_base_mono (Qabs_den_pos hwd) hρd (Qabs_num_nonneg w) hw k))

/-- The coefficientwise absolute value of a formal series. -/
def fabs (b : Nat → Q) : Nat → Q := fun k => Qabs (b k)

theorem fabs_den_pos {b : Nat → Q} (hb : ∀ i, 0 < (b i).den) (k : Nat) : 0 < (fabs b k).den :=
  Qabs_den_pos (hb k)

theorem fabs_nonneg (b : Nat → Q) (k : Nat) : 0 ≤ (fabs b k).num := Qabs_num_nonneg (b k)

/-- **Eval is monotone in coefficients** at a nonnegative point. -/
theorem peval_mono {c d : Nat → Q} (hcd : ∀ k, Qle (c k) (d k)) (ρ : Q) (hρ0 : 0 ≤ ρ.num) (M : Nat) :
    Qle (peval c ρ M) (peval d ρ M) :=
  Fsum_le_Fsum (fun k => Qmul_le_mul_right (qpow_nonneg hρ0 k) (hcd k)) M

/-- **The unit series evaluates to 1.** -/
theorem peval_fone (ρ : Q) (hρd : 0 < ρ.den) : ∀ M, Qeq (peval fone ρ M) ⟨1, 1⟩
  | 0 => by
      show Qeq (mul (fone 0) (qpow ρ 0)) ⟨1, 1⟩
      rw [show qpow ρ 0 = ⟨1, 1⟩ from rfl]; simp [fone, Qeq, mul]
  | (M + 1) => by
      show Qeq (add (peval fone ρ M) (mul (fone (M + 1)) (qpow ρ (M + 1)))) ⟨1, 1⟩
      have hz : Qeq (mul (fone (M + 1)) (qpow ρ (M + 1))) ⟨0, 1⟩ := by
        rw [show fone (M + 1) = ⟨0, 1⟩ from by simp [fone]]; simp [Qeq, mul]
      exact Qeq_trans (add_den_pos Nat.one_pos Nat.one_pos)
        (Qadd_congr (peval_fone ρ hρd M) hz) (Qadd_zero_right _)

/-- **Per-coefficient abs bound**: `|eval c w M| ≤ eval(|c|, ρ, M)` for `|w| ≤ ρ`. -/
theorem peval_abs_le_peval_fabs (c : Nat → Q) (hc : ∀ k, 0 < (c k).den) (w : Q) (hwd : 0 < w.den)
    {ρ : Q} (hρd : 0 < ρ.den) (hw : Qle (Qabs w) ρ) (M : Nat) :
    Qle (Qabs (peval c w M)) (peval (fabs c) ρ M) := by
  refine Qle_trans (Fsum_den_pos (fun k => Qabs_den_pos (Qmul_den_pos (hc k) (qpow_den_pos hwd k))) M)
    (Fsum_abs_le (fun k => Qmul_den_pos (hc k) (qpow_den_pos hwd k)) M) ?_
  refine Fsum_le_Fsum (fun k => ?_) M
  rw [Qabs_mul]
  exact Qmul_le_mul_left (Qabs_num_nonneg (c k))
    (Qle_trans (qpow_den_pos (Qabs_den_pos hwd) k) (Qeq_le (qpow_abs w k))
      (qpow_base_mono (Qabs_den_pos hwd) hρd (Qabs_num_nonneg w) hw k))

/-- **The target side**: the geometric-coefficient evaluation is `2·(Σ_{k≤N} wᵏ) − 1`. With
    `gPow_telescope` this gives `peval dgeom w N · (1−w) → (1+w)` — the closed form `(1+w)/(1−w)`. -/
theorem peval_dgeom (w : Q) (hwd : 0 < w.den) :
    ∀ N, Qeq (peval dgeom w N) (Qsub (mul ⟨2, 1⟩ (gPow w N)) ⟨1, 1⟩)
  | 0 => by
      show Qeq (mul (dgeom 0) (qpow w 0)) (Qsub (mul ⟨2, 1⟩ (gPow w 0)) ⟨1, 1⟩)
      show Qeq (mul (dgeom 0) ⟨1, 1⟩) (Qsub (mul ⟨2, 1⟩ ⟨1, 1⟩) ⟨1, 1⟩)
      decide
  | (N + 1) => by
      show Qeq (add (peval dgeom w N) (mul (dgeom (N + 1)) (qpow w (N + 1))))
        (Qsub (mul ⟨2, 1⟩ (add (gPow w N) (qpow w (N + 1)))) ⟨1, 1⟩)
      have hd : dgeom (N + 1) = ⟨2, 1⟩ := by unfold dgeom; rw [if_neg (by omega)]
      rw [hd]
      refine Qeq_trans (add_den_pos (Qsub_den_pos (Qmul_den_pos (by decide) (gPow_den_pos hwd N)) Nat.one_pos)
          (Qmul_den_pos (by decide) (qpow_den_pos hwd (N + 1))))
        (Qadd_congr (peval_dgeom w hwd N) (Qeq_refl _)) ?_
      simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor

/-- **Per-row convolution**: the `m`-th antidiagonal of `(aᵢwⁱ)·(bⱼwʲ)` collapses to `(a·b)_m · wᵐ`
    (`wⁱ·w^{m−i} = wᵐ` via `qpow_add`). The bridge between the product double sum and `peval (a·b)`. -/
theorem peval_conv (a b : Nat → Q) {w : Q} (ha : ∀ i, 0 < (a i).den) (hb : ∀ j, 0 < (b j).den)
    (hwd : 0 < w.den) (m : Nat) :
    Qeq (Fsum (fun i => mul (mul (a i) (qpow w i)) (mul (b (m - i)) (qpow w (m - i)))) m)
      (mul (fmul a b m) (qpow w m)) := by
  refine Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos (Qmul_den_pos (ha i) (hb (m - i)))
      (qpow_den_pos hwd m)) m)
    (Fsum_congr_le (fun i hi => ?_))
    (Qeq_symm (Fsum_mul_const_right (qpow_den_pos hwd m)
      (fun i => Qmul_den_pos (ha i) (hb (m - i))) m))
  -- termwise: (aᵢwⁱ)(b_{m−i}w^{m−i}) ≈ (aᵢ·b_{m−i})·wᵐ
  have hqp : Qeq (mul (qpow w i) (qpow w (m - i))) (qpow w m) := by
    have h1 : i + (m - i) = m := by omega
    have hpa := qpow_add w hwd i (m - i)
    rw [h1] at hpa
    exact Qeq_symm hpa
  refine Qeq_trans (Qmul_den_pos (Qmul_den_pos (ha i) (hb (m - i)))
      (Qmul_den_pos (qpow_den_pos hwd i) (qpow_den_pos hwd (m - i))))
    (show Qeq (mul (mul (a i) (qpow w i)) (mul (b (m - i)) (qpow w (m - i))))
        (mul (mul (a i) (b (m - i))) (mul (qpow w i) (qpow w (m - i)))) by
      simp only [Qeq, mul]; push_cast; ring_uor)
    (Qmul_congr (Qeq_refl _) hqp)

/-- **The product (Cauchy) bridge**: `eval(a,w)·eval(b,w) ≈ eval(a·b, w) + corner`, the corner being the
    high antidiagonal part. Mirrors `expSum_mul_eq` for general coefficient series via `Fsum_mul_square`
    → `Fsum_square_decomp` → `Fsum_triangle_reindex` → `peval_conv`. -/
theorem peval_mul (a b : Nat → Q) {w : Q} (ha : ∀ i, 0 < (a i).den) (hb : ∀ j, 0 < (b j).den)
    (hwd : 0 < w.den) (M : Nat) :
    Qeq (mul (peval a w M) (peval b w M))
      (add (peval (fmul a b) w M)
        (Fsum (fun i => Qsub
          (Fsum (fun j => mul (mul (a i) (qpow w i)) (mul (b j) (qpow w j))) M)
          (Fsum (fun j => mul (mul (a i) (qpow w i)) (mul (b j) (qpow w j))) (M - i))) M)) := by
  have hta : ∀ i, 0 < (mul (a i) (qpow w i)).den := fun i => Qmul_den_pos (ha i) (qpow_den_pos hwd i)
  have htb : ∀ j, 0 < (mul (b j) (qpow w j)).den := fun j => Qmul_den_pos (hb j) (qpow_den_pos hwd j)
  have hg : ∀ i j, 0 < (mul (mul (a i) (qpow w i)) (mul (b j) (qpow w j))).den :=
    fun i j => Qmul_den_pos (hta i) (htb j)
  have hcorner : 0 < (Fsum (fun i => Qsub (Fsum (fun j => mul (mul (a i) (qpow w i)) (mul (b j) (qpow w j))) M)
      (Fsum (fun j => mul (mul (a i) (qpow w i)) (mul (b j) (qpow w j))) (M - i))) M).den :=
    Fsum_den_pos (fun i => Qsub_den_pos (Fsum_den_pos (fun j => hg i j) M)
      (Fsum_den_pos (fun j => hg i j) (M - i))) M
  refine Qeq_trans (Fsum_den_pos (fun i => Fsum_den_pos (fun j => hg i j) M) M)
    (Fsum_mul_square hta htb M) ?_
  refine Qeq_trans (add_den_pos (Fsum_den_pos (fun i => Fsum_den_pos (fun j => hg i j) (M - i)) M) hcorner)
    (Fsum_square_decomp hg M) ?_
  refine Qeq_trans (add_den_pos (Fsum_den_pos (fun m => Fsum_den_pos (fun i => hg i (m - i)) m) M) hcorner)
    (Qadd_congr (Fsum_triangle_reindex hg M) (Qeq_refl _)) ?_
  exact Qadd_congr (Fsum_congr (fun m => peval_conv a b ha hb hwd m) M) (Qeq_refl _)

-- ===========================================================================
-- The new (research-validated) route to exp∘log = id:
--   functional equation + O(u²) + integer-division limit.
-- Brick (A): the exp quadratic remainder  |expSum q N − (1+q)| ≤ |q|²·(M-series).
-- ===========================================================================

/-- **Per-term quadratic bound**: `|qⁱ/i!| ≤ |q|²·(1/i!)` for `i ≥ 2`, `|q| ≤ 1`. Since `|q|ⁱ =
    |q|²·|q|^{i−2} ≤ |q|²` (`qpow_add` + `qpow_le_one`). -/
theorem expTerm_quad {q : Q} (hqd : 0 < q.den) (hq : Qle (Qabs q) ⟨1, 1⟩) {i : Nat} (hi : 2 ≤ i) :
    Qle (Qabs (expTerm q i)) (mul (mul (Qabs q) (Qabs q)) ⟨1, fct i⟩) := by
  have habs : Qeq (Qabs (expTerm q i)) (mul (qpow (Qabs q) i) ⟨1, fct i⟩) := by
    show Qeq (Qabs (mul (qpow q i) ⟨1, fct i⟩)) (mul (qpow (Qabs q) i) ⟨1, fct i⟩)
    rw [Qabs_mul]
    exact Qmul_congr (qpow_abs q i) (Qeq_refl _)
  -- qpow |q| i = qpow |q| 2 · qpow |q| (i−2) ≤ qpow |q| 2 · 1 ≈ |q|²
  have hsplit : Qeq (qpow (Qabs q) i) (mul (qpow (Qabs q) 2) (qpow (Qabs q) (i - 2))) := by
    have hid : 2 + (i - 2) = i := by omega
    have h := qpow_add (Qabs q) (Qabs_den_pos hqd) 2 (i - 2)
    rw [hid] at h; exact h
  have hle1 : Qle (qpow (Qabs q) (i - 2)) ⟨1, 1⟩ :=
    qpow_le_one (Qabs_num_nonneg q) (Qabs_den_pos hqd) hq (i - 2)
  have hpow : Qle (qpow (Qabs q) i) (mul (Qabs q) (Qabs q)) := by
    refine Qle_trans (Qmul_den_pos (qpow_den_pos (Qabs_den_pos hqd) 2) (qpow_den_pos (Qabs_den_pos hqd) (i - 2)))
      (Qeq_le hsplit) ?_
    refine Qle_trans (Qmul_den_pos (qpow_den_pos (Qabs_den_pos hqd) 2) Nat.one_pos)
      (Qmul_le_mul_left (qpow_nonneg (Qabs_num_nonneg q) 2) hle1) (Qeq_le ?_)
    show Qeq (mul (qpow (Qabs q) 2) ⟨1, 1⟩) (mul (Qabs q) (Qabs q))
    show Qeq (mul (mul (Qabs q) (mul (Qabs q) ⟨1, 1⟩)) ⟨1, 1⟩) (mul (Qabs q) (Qabs q))
    simp only [Qeq, mul]; push_cast; ring_uor
  refine Qle_trans (Qmul_den_pos (qpow_den_pos (Qabs_den_pos hqd) i) (fct_pos i)) (Qeq_le habs) ?_
  exact Qmul_le_mul_right (by show (0:Int) ≤ 1; decide) hpow

/-- `|q|²·S ≥ 0`. -/
theorem Qsq_mul_nonneg (q s : Q) (hs : 0 ≤ s.num) : Qle (⟨0, 1⟩ : Q) (mul (mul (Qabs q) (Qabs q)) s) := by
  have h : (0 : Int) ≤ (Qabs q).num * (Qabs q).num * s.num :=
    Int.mul_nonneg (Int.mul_nonneg (Qabs_num_nonneg q) (Qabs_num_nonneg q)) hs
  simp only [Qle, mul]; omega

/-- **The exp quadratic remainder** (brick A): `|expSum q (N+1) − (1+q)| ≤ |q|²·(Σ_{i≤N+1} 1/i!)`
    for `|q| ≤ 1`. The remainder past the linear term `1 + q` is second-order, by `expTerm_quad`. -/
theorem expSum_quad {q : Q} (hqd : 0 < q.den) (hq : Qle (Qabs q) ⟨1, 1⟩) :
    ∀ N, Qle (Qabs (Qsub (expSum q (N + 1)) (add ⟨1, 1⟩ q)))
      (mul (mul (Qabs q) (Qabs q)) (expSumM 1 (N + 1)))
  | 0 => by
      have h0 : Qeq (Qsub (expSum q 1) (add ⟨1, 1⟩ q)) ⟨0, 1⟩ := by
        show Qeq (Qsub (add (⟨1, 1⟩ : Q) (mul (mul q ⟨1, 1⟩) ⟨1, 1⟩)) (add ⟨1, 1⟩ q)) ⟨0, 1⟩
        simp only [Qeq, Qsub, add, neg, mul]; push_cast; ring_uor
      refine Qle_trans (b := (⟨0, 1⟩ : Q)) Nat.one_pos
        (Qeq_le (Qeq_trans Nat.one_pos (Qabs_Qeq h0) (Qeq_refl _)))
        (Qsq_mul_nonneg q (expSumM 1 1) (by decide))
  | (N + 1) => by
      show Qle (Qabs (Qsub (add (expSum q (N + 1)) (expTerm q (N + 1 + 1))) (add ⟨1, 1⟩ q)))
        (mul (mul (Qabs q) (Qabs q)) (add (expSumM 1 (N + 1)) ⟨(npow 1 (N + 1 + 1) : Int), fct (N + 1 + 1)⟩))
      have hrw : Qeq (Qsub (add (expSum q (N + 1)) (expTerm q (N + 1 + 1))) (add ⟨1, 1⟩ q))
          (add (Qsub (expSum q (N + 1)) (add ⟨1, 1⟩ q)) (expTerm q (N + 1 + 1))) := by
        simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
      refine Qle_congr_left (Qabs_den_pos (add_den_pos (Qsub_den_pos (expSum_den_pos hqd (N + 1))
          (add_den_pos Nat.one_pos hqd)) (expTerm_den_pos hqd (N + 1 + 1))))
        (Qeq_symm (Qabs_Qeq hrw)) ?_
      refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (expSum_den_pos hqd (N + 1))
          (add_den_pos Nat.one_pos hqd))) (Qabs_den_pos (expTerm_den_pos hqd (N + 1 + 1))))
        (Qabs_add_le _ _) ?_
      refine Qle_trans (add_den_pos (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd))
          (expSumM_den_pos 1 (N + 1))) (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (fct_pos _)))
        (Qadd_le_add (expSum_quad hqd hq N) (expTerm_quad hqd hq (by omega : 2 ≤ N + 1 + 1))) (Qeq_le ?_)
      rw [npow_one]
      simp only [Qeq, mul, add]; push_cast; ring_uor

/-- **The artanh quadratic remainder** (brick B): `|artSum t b − t|·(1−ρ²) ≤ ρ³` for `|t| ≤ ρ`. Since
    `artSum t 0 = artTerm t 0 ≈ t`, the remainder past the linear term `t` is the geometric tail
    `Σ_{n≥1} t^{2n+1}/(2n+1)`, bounded by `ρ³/(1−ρ²)` via `artSum_trunc` (a = 0). -/
theorem artSum_lin_quad {t ρ : Q} (htd : 0 < t.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (htρ : Qle (Qabs t) ρ) (hW : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).num) (b : Nat) :
    Qle (mul (Qabs (Qsub (artSum t b) t)) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (qpow ρ 3) := by
  have h0 : Qeq (artSum t 0) t := by
    have e1 : artSum t 0 = mul (mul t ⟨1, 1⟩) ⟨1, 1⟩ := rfl
    rw [e1]; simp [Qeq, mul]
  have htrunc : Qle (mul (Qabs (Qsub (artSum t b) (artSum t 0))) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
      (qpow ρ 3) := artSum_trunc htd hρ0 hρd htρ hW (Nat.zero_le b)
  -- `artSum t 0 ≈ t`, so the bound on `|artSum t b − artSum t 0|` transfers to `|artSum t b − t|`.
  have hsub : Qeq (Qsub (artSum t b) (artSum t 0)) (Qsub (artSum t b) t) :=
    Qsub_congr (Qeq_refl _) h0
  refine Qle_congr_left ?_ (Qmul_congr (Qabs_Qeq hsub) (Qeq_refl _)) htrunc
  exact Qmul_den_pos (Qabs_den_pos (Qsub_den_pos (artSum_den_pos htd b) (artSum_den_pos htd 0)))
    (Qsub_den_pos Nat.one_pos (Nat.mul_pos hρd hρd))

-- ===========================================================================
-- Toward the DOUBLING formula 2·artanh(t) = artanh(2t/(1+t²)) (the reduced crux C).
-- Formal-ring foundations: sparse sums and monomial multiplication (= coefficient shift).
-- ===========================================================================

/-- **Sparse sum**: a finite sum of a sequence supported at a single index `j ≤ k` is its value
    there. The engine for multiplying a formal series by a monomial. -/
theorem Fsum_single {f : Nat → Q} (hf : ∀ i, 0 < (f i).den) {j : Nat}
    (hz : ∀ i, i ≠ j → Qeq (f i) ⟨0, 1⟩) : ∀ {k : Nat}, j ≤ k → Qeq (Fsum f k) (f j)
  | 0, hjk => by
      have hj : j = 0 := Nat.le_zero.mp hjk
      subst hj; exact Qeq_refl _
  | (k + 1), hjk => by
      show Qeq (add (Fsum f k) (f (k + 1))) (f j)
      by_cases hjeq : j = k + 1
      · subst hjeq
        have hsum0 : Qeq (Fsum f k) ⟨0, 1⟩ :=
          Qeq_trans (Fsum_den_pos (fun _ => Nat.one_pos) k)
            (Fsum_congr_le (g := fun _ => (⟨0, 1⟩ : Q)) (k := k) (fun i hi => hz i (by omega)))
            (Fsum_zeros k)
        have hc : Qeq (add (Fsum f k) (f (k + 1))) (add ⟨0, 1⟩ (f (k + 1))) :=
          Qadd_congr hsum0 (Qeq_refl _)
        exact Qeq_trans (add_den_pos Nat.one_pos (hf (k + 1))) hc (Qzero_add _)
      · have hjk' : j ≤ k := by omega
        have hc : Qeq (add (Fsum f k) (f (k + 1))) (add (f j) ⟨0, 1⟩) :=
          Qadd_congr (Fsum_single hf hz hjk') (hz (k + 1) (by omega))
        exact Qeq_trans (add_den_pos (hf j) Nat.one_pos) hc (Qadd_zero_right _)

/-- The monomial `tᵈ` as a coefficient sequence. -/
def fmono (d : Nat) (k : Nat) : Q := if k = d then ⟨1, 1⟩ else ⟨0, 1⟩

theorem fmono_den (d k : Nat) : 0 < (fmono d k).den := by unfold fmono; split <;> exact Nat.one_pos

/-- **Multiplying by a monomial is a shift**: `fmul (tᵈ) c k = c(k−d)` for `d ≤ k`. -/
theorem fmul_fmono {c : Nat → Q} (hc : ∀ i, 0 < (c i).den) (d : Nat) {k : Nat} (hdk : d ≤ k) :
    Qeq (fmul (fmono d) c k) (c (k - d)) := by
  have hg : ∀ i, 0 < (mul (fmono d i) (c (k - i))).den :=
    fun i => Qmul_den_pos (fmono_den d i) (hc (k - i))
  have hz : ∀ i, i ≠ d → Qeq (mul (fmono d i) (c (k - i))) ⟨0, 1⟩ := by
    intro i hi
    have he : fmono d i = ⟨0, 1⟩ := by unfold fmono; rw [if_neg hi]
    rw [he]; simp [Qeq, mul]
  have hgd : Qeq (mul (fmono d d) (c (k - d))) (c (k - d)) := by
    have he : fmono d d = ⟨1, 1⟩ := by unfold fmono; rw [if_pos rfl]
    rw [he]; simp [Qeq, mul]
  show Qeq (Fsum (fun i => mul (fmono d i) (c (k - i))) k) (c (k - d))
  exact Qeq_trans (hg d) (Fsum_single hg hz hdk) hgd

/-- Below the monomial degree, the shift is zero: `fmul (tᵈ) c k = 0` for `k < d`. -/
theorem fmul_fmono_zero {c : Nat → Q} (hc : ∀ i, 0 < (c i).den) {d k : Nat} (hdk : k < d) :
    Qeq (fmul (fmono d) c k) ⟨0, 1⟩ := by
  show Qeq (Fsum (fun i => mul (fmono d i) (c (k - i))) k) ⟨0, 1⟩
  refine Qeq_trans (Fsum_den_pos (fun _ => Nat.one_pos) k)
    (Fsum_congr_le (g := fun _ => (⟨0, 1⟩ : Q)) (k := k) (fun i hi => ?_)) (Fsum_zeros k)
  have he : fmono d i = ⟨0, 1⟩ := by unfold fmono; rw [if_neg (by omega)]
  rw [he]; simp [Qeq, mul]

/-- **Left-distributivity of the formal Cauchy product**: `(a+b)·c = a·c + b·c`. -/
theorem fmul_add_left {a b c : Nat → Q} (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den)
    (hc : ∀ i, 0 < (c i).den) (k : Nat) :
    Qeq (fmul (fun i => add (a i) (b i)) c k) (add (fmul a c k) (fmul b c k)) := by
  show Qeq (Fsum (fun i => mul (add (a i) (b i)) (c (k - i))) k)
    (add (Fsum (fun i => mul (a i) (c (k - i))) k) (Fsum (fun i => mul (b i) (c (k - i))) k))
  refine Qeq_trans
    (Fsum_den_pos (fun i => add_den_pos (Qmul_den_pos (ha i) (hc (k - i)))
      (Qmul_den_pos (hb i) (hc (k - i)))) k)
    (Fsum_congr (fun i => Qmul_add_right (a i) (b i) (c (k - i))) k)
    (Fsum_add (fun i => Qmul_den_pos (ha i) (hc (k - i)))
      (fun i => Qmul_den_pos (hb i) (hc (k - i))) k)

/-- The coefficient sequence of `2t/(1+t²)`: `0` at even degree, `2·(−1)ʲ` at degree `2j+1`
    (encoded by `m % 4`). -/
def kdbl (m : Nat) : Q := ⟨(if m % 4 = 1 then 2 else if m % 4 = 3 then -2 else 0 : Int), 1⟩

theorem kdbl_den (m : Nat) : 0 < (kdbl m).den := Nat.one_pos

/-- The `1+t²` and `2t` coefficient sequences. -/
def oneplusSq (k : Nat) : Q := add (fmono 0 k) (fmono 2 k)
def twoT (k : Nat) : Q := ⟨(if k = 1 then 2 else 0 : Int), 1⟩
theorem twoT_den (k : Nat) : 0 < (twoT k).den := Nat.one_pos

/-- The two-step sign cancellation `kdbl_{m+2} + kdbl_m = 0` (`(−1)ʲ⁺¹ + (−1)ʲ = 0`). -/
theorem kdbl_shift_cancel (m : Nat) : Qeq (add (kdbl (m + 2)) (kdbl m)) ⟨0, 1⟩ := by
  have hm2 : (m + 2) % 4 = (m % 4 + 2) % 4 := by omega
  have hm : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  unfold kdbl
  rcases hm with h | h | h | h <;> rw [hm2, h] <;> decide

/-- The per-degree split `((1+t²)·kdbl)_k = kdbl_k + kdbl_{k−2} = (2t)_k`. -/
theorem kdbl_main : ∀ k, Qeq (add (fmul (fmono 0) kdbl k) (fmul (fmono 2) kdbl k)) (twoT k)
  | 0 => by
      have h0 : Qeq (fmul (fmono 0) kdbl 0) (kdbl 0) := fmul_fmono (fun i => kdbl_den i) 0 (by omega)
      have h2 : Qeq (fmul (fmono 2) kdbl 0) ⟨0, 1⟩ := fmul_fmono_zero (fun i => kdbl_den i) (by omega)
      exact Qeq_trans (add_den_pos (kdbl_den 0) Nat.one_pos) (Qadd_congr h0 h2) (by decide)
  | 1 => by
      have h0 : Qeq (fmul (fmono 0) kdbl 1) (kdbl 1) := fmul_fmono (fun i => kdbl_den i) 0 (by omega)
      have h2 : Qeq (fmul (fmono 2) kdbl 1) ⟨0, 1⟩ := fmul_fmono_zero (fun i => kdbl_den i) (by omega)
      exact Qeq_trans (add_den_pos (kdbl_den 1) Nat.one_pos) (Qadd_congr h0 h2) (by decide)
  | (m + 2) => by
      have h0 : Qeq (fmul (fmono 0) kdbl (m + 2)) (kdbl (m + 2)) :=
        fmul_fmono (fun i => kdbl_den i) 0 (by omega)
      have h2 : Qeq (fmul (fmono 2) kdbl (m + 2)) (kdbl m) :=
        fmul_fmono (fun i => kdbl_den i) 2 (by omega)
      refine Qeq_trans (add_den_pos (kdbl_den (m + 2)) (kdbl_den m)) (Qadd_congr h0 h2) ?_
      have ht : Qeq (⟨0, 1⟩ : Q) (twoT (m + 2)) := by
        unfold twoT; rw [if_neg (show m + 2 ≠ 1 by omega)]; exact Qeq_refl _
      exact Qeq_trans Nat.one_pos (kdbl_shift_cancel m) ht

/-- **The defining relation** `(1+t²)·kdbl = 2t` of the doubling inner function `k = 2t/(1+t²)`. -/
theorem kdbl_rel (k : Nat) : Qeq (fmul oneplusSq kdbl k) (twoT k) :=
  Qeq_trans (add_den_pos (fmul_den_pos (fun i => fmono_den 0 i) (fun i => kdbl_den i) k)
      (fmul_den_pos (fun i => fmono_den 2 i) (fun i => kdbl_den i) k))
    (fmul_add_left (fun i => fmono_den 0 i) (fun i => fmono_den 2 i) (fun i => kdbl_den i) k)
    (kdbl_main k)

theorem oneplusSq_den (k : Nat) : 0 < (oneplusSq k).den := add_den_pos (fmono_den 0 k) (fmono_den 2 k)

/-- `fderiv` respects `≈` coefficient-wise. -/
theorem fderiv_congr {a b : Nat → Q} (h : ∀ i, Qeq (a i) (b i)) (k : Nat) :
    Qeq (fderiv a k) (fderiv b k) := Qmul_congr (Qeq_refl _) (h (k + 1))

/-- `fmul` respects `≈` in its left argument. -/
theorem fmul_congr_left {a a' b : Nat → Q} (h : ∀ i, Qeq (a i) (a' i)) (k : Nat) :
    Qeq (fmul a b k) (fmul a' b k) :=
  Fsum_congr (fun i => Qmul_congr (h i) (Qeq_refl _)) k

/-- The constant `2` series `(2,0,0,…)` = `d/dt(2t)`. -/
def twoFone (k : Nat) : Q := ⟨(if k = 0 then 2 else 0 : Int), 1⟩
theorem twoFone_den (k : Nat) : 0 < (twoFone k).den := Nat.one_pos

/-- `d/dt(1+t²) = 2t`. -/
theorem fderiv_oneplusSq : ∀ k, Qeq (fderiv oneplusSq k) (twoT k)
  | 0 => by decide
  | 1 => by decide
  | (k + 2) => by
      show Qeq (mul ⟨(k + 2 + 1 : Int), 1⟩ (oneplusSq (k + 2 + 1))) (twoT (k + 2))
      have ho : oneplusSq (k + 2 + 1) = ⟨0, 1⟩ := by
        unfold oneplusSq fmono; rw [if_neg (by omega), if_neg (by omega)]; rfl
      have ht : twoT (k + 2) = ⟨0, 1⟩ := by unfold twoT; rw [if_neg (by omega)]
      rw [ho, ht]; simp [Qeq, mul]

/-- `d/dt(2t) = 2`. -/
theorem fderiv_twoT : ∀ k, Qeq (fderiv twoT k) (twoFone k)
  | 0 => by decide
  | (k + 1) => by
      show Qeq (mul ⟨(k + 1 + 1 : Int), 1⟩ (twoT (k + 1 + 1))) (twoFone (k + 1))
      have ht : twoT (k + 1 + 1) = ⟨0, 1⟩ := by unfold twoT; rw [if_neg (by omega)]
      have hf : twoFone (k + 1) = ⟨0, 1⟩ := by unfold twoFone; rw [if_neg (by omega)]
      rw [ht, hf]; simp [Qeq, mul]

/-- **The differentiated relation** `2t·k + (1+t²)·k' = 2` (from `kdbl_rel` via the Leibniz rule
    `fderiv_fmul`). With `kdbl_rel` this is the linear system pinning `k = 2t/(1+t²)` and `k'`. -/
theorem kdbl_deriv_rel (k : Nat) :
    Qeq (add (fmul twoT kdbl k) (fmul oneplusSq (fderiv kdbl) k)) (twoFone k) := by
  have e1 : Qeq (fderiv (fmul oneplusSq kdbl) k)
      (add (fmul (fderiv oneplusSq) kdbl k) (fmul oneplusSq (fderiv kdbl) k)) :=
    fderiv_fmul oneplusSq kdbl (fun i => oneplusSq_den i) (fun i => kdbl_den i) k
  have e4 : Qeq (fmul (fderiv oneplusSq) kdbl k) (fmul twoT kdbl k) :=
    fmul_congr_left (fun i => fderiv_oneplusSq i) k
  -- fderiv(fmul oneplusSq kdbl) ≈ add (fmul twoT kdbl) (fmul oneplusSq kdbl')
  have step1 : Qeq (fderiv (fmul oneplusSq kdbl) k)
      (add (fmul twoT kdbl k) (fmul oneplusSq (fderiv kdbl) k)) :=
    Qeq_trans (add_den_pos (fmul_den_pos (fun i => fderiv_den_pos (fun j => oneplusSq_den j) i)
        (fun i => kdbl_den i) k) (fmul_den_pos (fun i => oneplusSq_den i)
        (fun i => fderiv_den_pos (fun i => kdbl_den i) i) k)) e1
      (Qadd_congr e4 (Qeq_refl _))
  -- and fderiv(fmul oneplusSq kdbl) ≈ fderiv twoT ≈ 2
  have step2 : Qeq (fderiv (fmul oneplusSq kdbl) k) (twoFone k) :=
    Qeq_trans (fderiv_den_pos (fun i => Nat.one_pos) k)
      (fderiv_congr (fun i => kdbl_rel i) k) (fderiv_twoT k)
  exact Qeq_trans (fderiv_den_pos (fun i => fmul_den_pos (fun j => oneplusSq_den j)
      (fun i => kdbl_den i) i) k) (Qeq_symm step1) step2

-- ===========================================================================
-- Formal composition foundations: powers fpow b m = bᵐ, and the vanishing lemma
-- (when b(0)=0, bᵐ has lowest degree ≥ m) that makes composition coefficient-finite.
-- ===========================================================================

/-- Formal powers of a series: `bᵐ`. -/
def fpow (b : Nat → Q) : Nat → Nat → Q
  | 0 => fone
  | (m + 1) => fmul b (fpow b m)

theorem fpow_den_pos {b : Nat → Q} (hb : ∀ i, 0 < (b i).den) : ∀ (m k : Nat), 0 < (fpow b m k).den
  | 0, k => fone_den_pos k
  | (m + 1), k => fmul_den_pos hb (fun j => fpow_den_pos hb m j) k

/-- **The vanishing lemma**: if `b(0) = 0`, then `bᵐ` has no terms below degree `m`
    (`fpow b m k = 0` for `k < m`) — the finiteness that makes formal composition well-defined. -/
theorem fpow_vanish {b : Nat → Q} (hb : ∀ i, 0 < (b i).den) (hb0 : Qeq (b 0) ⟨0, 1⟩) :
    ∀ (m k : Nat), k < m → Qeq (fpow b m k) ⟨0, 1⟩
  | 0, k, hk => absurd hk (Nat.not_lt_zero k)
  | (m + 1), k, hk => by
      show Qeq (Fsum (fun i => mul (b i) (fpow b m (k - i))) k) ⟨0, 1⟩
      refine Qeq_trans (Fsum_den_pos (fun _ => Nat.one_pos) k)
        (Fsum_congr_le (g := fun _ => (⟨0, 1⟩ : Q)) (k := k) (fun i hi => ?_)) (Fsum_zeros k)
      by_cases hi0 : i = 0
      · subst hi0
        refine Qeq_trans (Qmul_den_pos Nat.one_pos (fpow_den_pos hb m (k - 0)))
          (Qmul_congr hb0 (Qeq_refl _)) ?_
        simp [Qeq, mul]
      · have hkm : k - i < m := by omega
        have hv : Qeq (fpow b m (k - i)) ⟨0, 1⟩ := fpow_vanish hb hb0 m (k - i) hkm
        refine Qeq_trans (Qmul_den_pos (hb i) Nat.one_pos)
          (Qmul_congr (Qeq_refl _) hv) ?_
        simp [Qeq, mul]

/-- **Abs of a Cauchy product is dominated by the Cauchy product of abs**: `|a·b| ≤ |a|·|b|` coefficientwise. -/
theorem Qabs_fmul_le (a b : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den) (k : Nat) :
    Qle (Qabs (fmul a b k)) (fmul (fabs a) (fabs b) k) := by
  show Qle (Qabs (Fsum (fun i => mul (a i) (b (k - i))) k))
    (Fsum (fun i => mul (Qabs (a i)) (Qabs (b (k - i)))) k)
  refine Qle_trans (Fsum_den_pos (fun i => Qabs_den_pos (Qmul_den_pos (ha i) (hb (k - i)))) k)
    (Fsum_abs_le (fun i => Qmul_den_pos (ha i) (hb (k - i))) k) ?_
  refine Fsum_le_Fsum (fun i => ?_) k
  rw [Qabs_mul]; exact Qle_refl _

/-- **`fmul` is monotone in its right argument** when the left is nonnegative. -/
theorem fmul_mono_right {a c d : Nat → Q} (ha0 : ∀ i, 0 ≤ (a i).num)
    (hcd : ∀ j, Qle (c j) (d j)) (k : Nat) : Qle (fmul a c k) (fmul a d k) :=
  Fsum_le_Fsum (fun i => Qmul_le_mul_left (ha0 i) (hcd (k - i))) k

/-- **Coefficient domination of powers**: `|（bᵐ)_k| ≤ (|b|ᵐ)_k`. -/
theorem fpow_abs_dom (b : Nat → Q) (hb : ∀ i, 0 < (b i).den) :
    ∀ (m k : Nat), Qle (Qabs (fpow b m k)) (fpow (fabs b) m k)
  | 0, k => by
      show Qle (Qabs (fone k)) (fone k)
      unfold fone; by_cases h : k = 0
      · rw [if_pos h]; exact (by decide : Qle (Qabs (⟨1, 1⟩ : Q)) ⟨1, 1⟩)
      · rw [if_neg h]; exact (by decide : Qle (Qabs (⟨0, 1⟩ : Q)) ⟨0, 1⟩)
  | (m + 1), k =>
      Qle_trans (fmul_den_pos (fun i => fabs_den_pos hb i) (fun j => fabs_den_pos (fpow_den_pos hb m) j) k)
        (Qabs_fmul_le b (fpow b m) hb (fpow_den_pos hb m) k)
        (fmul_mono_right (fun i => fabs_nonneg b i) (fun j => fpow_abs_dom b hb m j) k)

/-- **Formal composition** `(a∘b)_k = Σ_{m=0}^{k} aₘ·(bᵐ)_k`. When `b(0)=0` (`fpow_vanish`) the terms
    with `m > k` vanish, so this finite sum is the full composition coefficient. -/
def fcomp (a b : Nat → Q) (k : Nat) : Q := Fsum (fun m => mul (a m) (fpow b m k)) k

theorem fcomp_den_pos {a b : Nat → Q} (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den)
    (k : Nat) : 0 < (fcomp a b k).den :=
  Fsum_den_pos (fun m => Qmul_den_pos (ha m) (fpow_den_pos hb m k)) k

/-- The constant term of a composition is the constant term of the outer series: `(a∘b)_0 = a_0`. -/
theorem fcomp_const (a b : Nat → Q) : Qeq (fcomp a b 0) (a 0) := by
  show Qeq (mul (a 0) (fpow b 0 0)) (a 0)
  show Qeq (mul (a 0) ⟨1, 1⟩) (a 0)
  simp [Qeq, mul]

/-- The formal derivative of the constant series `1` is `0`. -/
theorem fderiv_fone (k : Nat) : Qeq (fderiv fone k) ⟨0, 1⟩ := by
  show Qeq (mul ⟨(k + 1 : Int), 1⟩ (fone (k + 1))) ⟨0, 1⟩
  have h : fone (k + 1) = ⟨0, 1⟩ := by unfold fone; rw [if_neg (by omega)]
  rw [h]; simp [Qeq, mul]

/-- `fmul` respects `≈` in its right argument. -/
theorem fmul_congr_right {a b b' : Nat → Q} (h : ∀ i, Qeq (b i) (b' i)) (k : Nat) :
    Qeq (fmul a b k) (fmul a b' k) :=
  Fsum_congr (fun i => Qmul_congr (Qeq_refl _) (h (k - i))) k

/-- Scalar multiplication of a formal series: `(c·a)_k = c·aₖ`. -/
def fsmul (c : Q) (a : Nat → Q) (k : Nat) : Q := mul c (a k)

theorem fsmul_den {c : Q} (hc : 0 < c.den) {a : Nat → Q} (ha : ∀ i, 0 < (a i).den) (k : Nat) :
    0 < (fsmul c a k).den := Qmul_den_pos hc (ha k)

/-- `fmul a (zero series) = 0`. -/
theorem fmul_zero_right (a : Nat → Q) (ha : ∀ i, 0 < (a i).den) (k : Nat) :
    Qeq (fmul a (fun _ => (⟨0, 1⟩ : Q)) k) ⟨0, 1⟩ := by
  show Qeq (Fsum (fun i => mul (a i) ((fun _ => (⟨0, 1⟩ : Q)) (k - i))) k) ⟨0, 1⟩
  refine Qeq_trans (Fsum_den_pos (fun _ => Nat.one_pos) k)
    (Fsum_congr_le (g := fun _ => (⟨0, 1⟩ : Q)) (k := k) (fun i _ => ?_)) (Fsum_zeros k)
  simp [Qeq, mul]

/-- **Scalars pull out of the Cauchy product**: `a·(c·b) = c·(a·b)`. -/
theorem fmul_smul_right (a b : Nat → Q) (c : Q) (hc : 0 < c.den) (ha : ∀ i, 0 < (a i).den)
    (hb : ∀ i, 0 < (b i).den) (k : Nat) : Qeq (fmul a (fsmul c b) k) (mul c (fmul a b k)) := by
  show Qeq (Fsum (fun i => mul (a i) (mul c (b (k - i)))) k)
    (mul c (Fsum (fun i => mul (a i) (b (k - i))) k))
  refine Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos hc (Qmul_den_pos (ha i) (hb (k - i)))) k)
    (Fsum_congr (fun i => ?_) k)
    (Fsum_mul_left hc (fun i => Qmul_den_pos (ha i) (hb (k - i))) k)
  show Qeq (mul (a i) (mul c (b (k - i)))) (mul c (mul (a i) (b (k - i))))
  simp only [Qeq, mul]; push_cast; ring_uor

/-- `a·(c·d) = c·(a·d)` (swap the left factors of a nested Cauchy product). -/
theorem fmul_swap_left (a c d : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hc : ∀ i, 0 < (c i).den)
    (hd : ∀ i, 0 < (d i).den) (k : Nat) : Qeq (fmul a (fmul c d) k) (fmul c (fmul a d) k) := by
  have s1 : Qeq (fmul a (fmul c d) k) (fmul (fmul a c) d k) := Qeq_symm (fmul_assoc a c d ha hc hd k)
  have s2 : Qeq (fmul (fmul a c) d k) (fmul (fmul c a) d k) :=
    fmul_congr_left (fun i => fmul_comm a c ha hc i) k
  have s3 : Qeq (fmul (fmul c a) d k) (fmul c (fmul a d) k) := fmul_assoc c a d hc ha hd k
  exact Qeq_trans (fmul_den_pos (fun i => fmul_den_pos ha hc i) hd k) s1
    (Qeq_trans (fmul_den_pos (fun i => fmul_den_pos hc ha i) hd k) s2 s3)

/-- `p + (m+1)·p = (m+2)·p`. -/
theorem Qcombine_succ (m : Nat) (p : Q) :
    Qeq (add p (mul ⟨(m + 1 : Int), 1⟩ p)) (mul ⟨(m + 1 + 1 : Int), 1⟩ p) := by
  simp only [Qeq, add, mul]; push_cast; ring_uor

/-- **The power rule** `(bᵐ⁺¹)' = (m+1)·bᵐ·b'` (induction via the Leibniz rule). -/
theorem fpow_deriv {b : Nat → Q} (hb : ∀ i, 0 < (b i).den) :
    ∀ (m k : Nat), Qeq (fderiv (fpow b (m + 1)) k)
      (fsmul ⟨(m + 1 : Int), 1⟩ (fmul (fderiv b) (fpow b m)) k)
  | 0, k => by
      have hb' : ∀ i, 0 < (fderiv b i).den := fun i => fderiv_den_pos hb i
      have e1 : Qeq (fderiv (fpow b 1) k)
          (add (fmul (fderiv b) (fpow b 0) k) (fmul b (fderiv (fpow b 0)) k)) :=
        fderiv_fmul b (fpow b 0) hb (fun i => fpow_den_pos hb 0 i) k
      have e2 : Qeq (fmul b (fderiv (fpow b 0)) k) ⟨0, 1⟩ :=
        Qeq_trans (fmul_den_pos hb (fun i => fderiv_den_pos (fun j => fone_den_pos j) i) k)
          (fmul_congr_right (fun i => fderiv_fone i) k) (fmul_zero_right b hb k)
      have eA : Qeq (fderiv (fpow b 1) k) (add (fmul (fderiv b) (fpow b 0) k) ⟨0, 1⟩) :=
        Qeq_trans (add_den_pos (fmul_den_pos hb' (fun i => fpow_den_pos hb 0 i) k)
            (fmul_den_pos hb (fun i => fderiv_den_pos (fun j => fpow_den_pos hb 0 j) i) k))
          e1 (Qadd_congr (Qeq_refl _) e2)
      have eB : Qeq (fderiv (fpow b 1) k) (fmul (fderiv b) (fpow b 0) k) :=
        Qeq_trans (add_den_pos (fmul_den_pos hb' (fun i => fpow_den_pos hb 0 i) k) Nat.one_pos)
          eA (Qadd_zero_right _)
      have eR : Qeq (fsmul ⟨(0 + 1 : Int), 1⟩ (fmul (fderiv b) (fpow b 0)) k)
          (fmul (fderiv b) (fpow b 0) k) := by
        show Qeq (mul ⟨(0 + 1 : Int), 1⟩ (fmul (fderiv b) (fpow b 0) k)) (fmul (fderiv b) (fpow b 0) k)
        simp only [Qeq, mul]; push_cast; ring_uor
      exact Qeq_trans (fmul_den_pos hb' (fun i => fpow_den_pos hb 0 i) k) eB (Qeq_symm eR)
  | (m + 1), k => by
      have hb' : ∀ i, 0 < (fderiv b i).den := fun i => fderiv_den_pos hb i
      have hP : 0 < (fmul (fderiv b) (fpow b (m + 1)) k).den :=
        fmul_den_pos hb' (fun i => fpow_den_pos hb (m + 1) i) k
      have e1 : Qeq (fderiv (fpow b (m + 2)) k)
          (add (fmul (fderiv b) (fpow b (m + 1)) k) (fmul b (fderiv (fpow b (m + 1))) k)) :=
        fderiv_fmul b (fpow b (m + 1)) hb (fun i => fpow_den_pos hb (m + 1) i) k
      have eIH : Qeq (fmul b (fderiv (fpow b (m + 1))) k)
          (fmul b (fsmul ⟨(m + 1 : Int), 1⟩ (fmul (fderiv b) (fpow b m))) k) :=
        fmul_congr_right (fun i => fpow_deriv hb m i) k
      have eS : Qeq (fmul b (fsmul ⟨(m + 1 : Int), 1⟩ (fmul (fderiv b) (fpow b m))) k)
          (mul ⟨(m + 1 : Int), 1⟩ (fmul b (fmul (fderiv b) (fpow b m)) k)) :=
        fmul_smul_right b (fmul (fderiv b) (fpow b m)) ⟨(m + 1 : Int), 1⟩ Nat.one_pos hb
          (fun i => fmul_den_pos hb' (fun j => fpow_den_pos hb m j) i) k
      have eRw : Qeq (fmul b (fmul (fderiv b) (fpow b m)) k) (fmul (fderiv b) (fpow b (m + 1)) k) :=
        fmul_swap_left b (fderiv b) (fpow b m) hb hb' (fun i => fpow_den_pos hb m i) k
      have eP : Qeq (fmul b (fderiv (fpow b (m + 1))) k)
          (mul ⟨(m + 1 : Int), 1⟩ (fmul (fderiv b) (fpow b (m + 1)) k)) :=
        Qeq_trans (fmul_den_pos hb (fun i => fsmul_den Nat.one_pos
            (fun j => fmul_den_pos hb' (fun l => fpow_den_pos hb m l) j) i) k) eIH
          (Qeq_trans (Qmul_den_pos Nat.one_pos (fmul_den_pos hb
              (fun i => fmul_den_pos hb' (fun j => fpow_den_pos hb m j) i) k)) eS
            (Qmul_congr (Qeq_refl _) eRw))
      refine Qeq_trans (add_den_pos hP (fmul_den_pos hb
          (fun i => fderiv_den_pos (fun j => fpow_den_pos hb (m + 1) j) i) k)) e1 ?_
      refine Qeq_trans (add_den_pos hP (Qmul_den_pos Nat.one_pos hP)) (Qadd_congr (Qeq_refl _) eP) ?_
      show Qeq (add (fmul (fderiv b) (fpow b (m + 1)) k)
          (mul ⟨(m + 1 : Int), 1⟩ (fmul (fderiv b) (fpow b (m + 1)) k)))
        (mul ⟨(m + 1 + 1 : Int), 1⟩ (fmul (fderiv b) (fpow b (m + 1)) k))
      exact Qcombine_succ m (fmul (fderiv b) (fpow b (m + 1)) k)

/-- **`fderiv` commutes with the composition sum**: `(a∘b)'_k = Σ_{m=0}^{k+1} aₘ·(bᵐ)'_k`. The first
    half of the chain rule — the outer derivative passes through the (extended) composition sum. -/
theorem fderiv_fcomp_sum (a b : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den)
    (k : Nat) : Qeq (fderiv (fcomp a b) k)
      (Fsum (fun m => mul (a m) (fderiv (fpow b m) k)) (k + 1)) := by
  show Qeq (mul ⟨(k + 1 : Int), 1⟩ (Fsum (fun m => mul (a m) (fpow b m (k + 1))) (k + 1)))
    (Fsum (fun m => mul (a m) (mul ⟨(k + 1 : Int), 1⟩ (fpow b m (k + 1)))) (k + 1))
  have h1 : Qeq (mul ⟨(k + 1 : Int), 1⟩ (Fsum (fun m => mul (a m) (fpow b m (k + 1))) (k + 1)))
      (Fsum (fun m => mul ⟨(k + 1 : Int), 1⟩ (mul (a m) (fpow b m (k + 1)))) (k + 1)) :=
    Qeq_symm (Fsum_mul_left Nat.one_pos
      (fun m => Qmul_den_pos (ha m) (fpow_den_pos hb m (k + 1))) (k + 1))
  have h2 : Qeq (Fsum (fun m => mul ⟨(k + 1 : Int), 1⟩ (mul (a m) (fpow b m (k + 1)))) (k + 1))
      (Fsum (fun m => mul (a m) (mul ⟨(k + 1 : Int), 1⟩ (fpow b m (k + 1)))) (k + 1)) :=
    Fsum_congr (fun m => by simp only [Qeq, mul]; push_cast; ring_uor) (k + 1)
  exact Qeq_trans (Fsum_den_pos (fun m => Qmul_den_pos Nat.one_pos
    (Qmul_den_pos (ha m) (fpow_den_pos hb m (k + 1)))) (k + 1)) h1 h2

/-- Chain rule, part 1: peel the constant term (which vanishes via `fderiv_fone`) and rewrite each
    `(bᵐ⁺¹)'` by the power rule, giving `(a∘b)'_k = Σ_{m=0}^{k} (a')ₘ·(b'·bᵐ)_k`. -/
theorem fcomp_chain_pre (a b : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den) (k : Nat) :
    Qeq (fderiv (fcomp a b) k)
      (Fsum (fun m => mul (fderiv a m) (fmul (fderiv b) (fpow b m) k)) k) := by
  have hb' : ∀ i, 0 < (fderiv b i).den := fun i => fderiv_den_pos hb i
  have s1 := fderiv_fcomp_sum a b ha hb k
  have s2 : Qeq (Fsum (fun m => mul (a m) (fderiv (fpow b m) k)) (k + 1))
      (add (mul (a 0) (fderiv (fpow b 0) k))
        (Fsum (fun i => mul (a (i + 1)) (fderiv (fpow b (i + 1)) k)) k)) :=
    Fsum_front (fun m => Qmul_den_pos (ha m) (fderiv_den_pos (fun j => fpow_den_pos hb m j) k)) k
  have sf0 : Qeq (mul (a 0) (fderiv (fpow b 0) k)) ⟨0, 1⟩ := by
    refine Qeq_trans (Qmul_den_pos (ha 0) Nat.one_pos)
      (Qmul_congr (Qeq_refl _) (fderiv_fone k)) ?_
    simp [Qeq, mul]
  have stail : Qeq (Fsum (fun i => mul (a (i + 1)) (fderiv (fpow b (i + 1)) k)) k)
      (Fsum (fun m => mul (fderiv a m) (fmul (fderiv b) (fpow b m) k)) k) := by
    refine Fsum_congr_le (k := k) (fun i _ => ?_)
    refine Qeq_trans (Qmul_den_pos (ha (i + 1)) (fsmul_den Nat.one_pos
        (fun j => fmul_den_pos hb' (fun l => fpow_den_pos hb i l) j) k))
      (Qmul_congr (Qeq_refl _) (fpow_deriv hb i k)) ?_
    show Qeq (mul (a (i + 1)) (mul ⟨(i + 1 : Int), 1⟩ (fmul (fderiv b) (fpow b i) k)))
      (mul (mul ⟨(i + 1 : Int), 1⟩ (a (i + 1))) (fmul (fderiv b) (fpow b i) k))
    simp only [Qeq, mul]; push_cast; ring_uor
  refine Qeq_trans (Fsum_den_pos (fun m => Qmul_den_pos (ha m)
      (fderiv_den_pos (fun j => fpow_den_pos hb m j) k)) (k + 1)) s1 ?_
  refine Qeq_trans (add_den_pos (Qmul_den_pos (ha 0)
      (fderiv_den_pos (fun j => fpow_den_pos hb 0 j) k))
      (Fsum_den_pos (fun i => Qmul_den_pos (ha (i + 1))
        (fderiv_den_pos (fun j => fpow_den_pos hb (i + 1) j) k)) k)) s2 ?_
  refine Qeq_trans (add_den_pos Nat.one_pos (Fsum_den_pos (fun m => Qmul_den_pos
      (fderiv_den_pos (fun j => ha j) m)
      (fmul_den_pos hb' (fun l => fpow_den_pos hb m l) k)) k)) (Qadd_congr sf0 stail) ?_
  exact Qzero_add _

/-- **Extend a sum by trailing zeros**: if `f` vanishes on `(i, k]` then `Σ_{0}^{i} f = Σ_{0}^{k} f`.
    (Used to pad the truncated composition sum `(a∘b)ᵢ` up to a uniform bound.) -/
theorem Fsum_extend_zero {f : Nat → Q} (hf : ∀ m, 0 < (f m).den) {i : Nat} :
    ∀ {k}, i ≤ k → (∀ m, i < m → m ≤ k → Qeq (f m) ⟨0, 1⟩) → Qeq (Fsum f i) (Fsum f k)
  | 0, hik, _ => by have hi : i = 0 := by omega
                    rw [hi]; exact Qeq_refl _
  | (k + 1), _, hz => by
      by_cases h : i = k + 1
      · rw [h]; exact Qeq_refl _
      · have hIH : Qeq (Fsum f i) (Fsum f k) :=
          Fsum_extend_zero hf (by omega) (fun m hm1 hm2 => hz m hm1 (by omega))
        have hfk1 : Qeq (f (k + 1)) ⟨0, 1⟩ := hz (k + 1) (by omega) (Nat.le_refl _)
        have hstep : Qeq (add (Fsum f k) (f (k + 1))) (Fsum f k) :=
          Qeq_trans (add_den_pos (Fsum_den_pos hf k) Nat.one_pos)
            (Qadd_congr (Qeq_refl _) hfk1) (Qadd_zero_right _)
        exact Qeq_trans (Fsum_den_pos hf k) hIH (Qeq_symm hstep)

/-- **The chain rule** for formal composition: `(a∘b)' = (a'∘b)·b'` (requires `b(0)=0`). Built from
    `fcomp_chain_pre` by a double-sum reindex — expand the inner Cauchy product, swap the order
    (`Fsum_swap`), reverse the outer index (`Fsum_reverse`), and pad the truncated composition
    coefficient back up (`Fsum_extend_zero`, terms vanishing by `fpow_vanish`). -/
theorem fcomp_chain (a b : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den)
    (hb0 : Qeq (b 0) ⟨0, 1⟩) (k : Nat) :
    Qeq (fderiv (fcomp a b) k) (fmul (fcomp (fderiv a) b) (fderiv b) k) := by
  have hA' : ∀ i, 0 < (fderiv a i).den := fun i => fderiv_den_pos (fun j => ha j) i
  have hB' : ∀ i, 0 < (fderiv b i).den := fun i => fderiv_den_pos hb i
  have hA : Qeq (Fsum (fun m => mul (fderiv a m) (fmul (fderiv b) (fpow b m) k)) k)
      (Fsum (fun m => Fsum (fun j =>
        mul (fderiv a m) (mul (fderiv b j) (fpow b m (k - j)))) k) k) := by
    refine Fsum_congr (fun m => ?_) k
    exact Qeq_symm (Fsum_mul_left (hA' m)
      (fun j => Qmul_den_pos (hB' j) (fpow_den_pos hb m (k - j))) k)
  have hB : Qeq (Fsum (fun m => Fsum (fun j =>
        mul (fderiv a m) (mul (fderiv b j) (fpow b m (k - j)))) k) k)
      (Fsum (fun j => Fsum (fun m =>
        mul (fderiv a m) (mul (fderiv b j) (fpow b m (k - j)))) k) k) :=
    Fsum_swap (fun m j => Qmul_den_pos (hA' m) (Qmul_den_pos (hB' j) (fpow_den_pos hb m (k - j)))) k k
  have hC : Qeq (Fsum (fun j => Fsum (fun m =>
        mul (fderiv a m) (mul (fderiv b j) (fpow b m (k - j)))) k) k)
      (Fsum (fun j => Fsum (fun m =>
        mul (fderiv a m) (mul (fderiv b (k - j)) (fpow b m (k - (k - j))))) k) k) :=
    Fsum_reverse (fun j => Fsum_den_pos
      (fun m => Qmul_den_pos (hA' m) (Qmul_den_pos (hB' j) (fpow_den_pos hb m (k - j)))) k) k
  have hD : Qeq (Fsum (fun j => Fsum (fun m =>
        mul (fderiv a m) (mul (fderiv b (k - j)) (fpow b m (k - (k - j))))) k) k)
      (Fsum (fun j => Fsum (fun m =>
        mul (mul (fderiv a m) (fpow b m j)) (fderiv b (k - j))) k) k) := by
    refine Fsum_congr_le (k := k) (fun j hj => Fsum_congr (fun m => ?_) k)
    rw [show k - (k - j) = j from by omega]
    simp only [Qeq, mul]; push_cast; ring_uor
  have hE : Qeq (Fsum (fun j => Fsum (fun m =>
        mul (mul (fderiv a m) (fpow b m j)) (fderiv b (k - j))) k) k)
      (fmul (fcomp (fderiv a) b) (fderiv b) k) := by
    show Qeq (Fsum (fun j => Fsum (fun m =>
        mul (mul (fderiv a m) (fpow b m j)) (fderiv b (k - j))) k) k)
      (Fsum (fun i => mul (fcomp (fderiv a) b i) (fderiv b (k - i))) k)
    refine Fsum_congr_le (k := k) (fun i hi => ?_)
    have hext : Qeq (Fsum (fun m => mul (fderiv a m) (fpow b m i)) k) (fcomp (fderiv a) b i) :=
      Qeq_symm (Fsum_extend_zero (fun m => Qmul_den_pos (hA' m) (fpow_den_pos hb m i)) hi
        (fun m hm1 _ => Qeq_trans (Qmul_den_pos (hA' m) Nat.one_pos)
          (Qmul_congr (Qeq_refl _) (fpow_vanish hb hb0 m i hm1)) (by simp [Qeq, mul])))
    exact Qeq_trans (Qmul_den_pos (Fsum_den_pos
        (fun m => Qmul_den_pos (hA' m) (fpow_den_pos hb m i)) k) (hB' (k - i)))
      (Qeq_symm (Fsum_mul_const_right (hB' (k - i))
        (fun m => Qmul_den_pos (hA' m) (fpow_den_pos hb m i)) k))
      (Qmul_congr hext (Qeq_refl _))
  exact Qeq_trans (Fsum_den_pos (fun m => Qmul_den_pos (hA' m)
      (fmul_den_pos hB' (fun l => fpow_den_pos hb m l) k)) k) (fcomp_chain_pre a b ha hb k)
    (Qeq_trans (Fsum_den_pos (fun m => Fsum_den_pos (fun j =>
        Qmul_den_pos (hA' m) (Qmul_den_pos (hB' j) (fpow_den_pos hb m (k - j)))) k) k) hA
      (Qeq_trans (Fsum_den_pos (fun j => Fsum_den_pos (fun m =>
          Qmul_den_pos (hA' m) (Qmul_den_pos (hB' j) (fpow_den_pos hb m (k - j)))) k) k) hB
        (Qeq_trans (Fsum_den_pos (fun j => Fsum_den_pos (fun m =>
            Qmul_den_pos (hA' m) (Qmul_den_pos (hB' (k - j))
              (fpow_den_pos hb m (k - (k - j))))) k) k) hC
          (Qeq_trans (Fsum_den_pos (fun j => Fsum_den_pos (fun m =>
              Qmul_den_pos (Qmul_den_pos (hA' m) (fpow_den_pos hb m j)) (hB' (k - j))) k) k) hD hE))))

-- ===========================================================================
-- The artanh ODE (1−t²)·artanh' = 1.  Scaled monomial machinery + the coefficient identity.
-- ===========================================================================

/-- A scaled monomial `c·tᵈ`. -/
def fsmono (c : Q) (d : Nat) (k : Nat) : Q := if k = d then c else ⟨0, 1⟩

theorem fsmono_den {c : Q} (hc : 0 < c.den) (d k : Nat) : 0 < (fsmono c d k).den := by
  unfold fsmono; split
  · exact hc
  · exact Nat.one_pos

/-- `fmul (c·tᵈ) e k = c·e(k−d)` for `d ≤ k`. -/
theorem fmul_fsmono {c : Q} (hc : 0 < c.den) (e : Nat → Q) (he : ∀ i, 0 < (e i).den) (d : Nat)
    {k : Nat} (hdk : d ≤ k) : Qeq (fmul (fsmono c d) e k) (mul c (e (k - d))) := by
  have hg : ∀ i, 0 < (mul (fsmono c d i) (e (k - i))).den :=
    fun i => Qmul_den_pos (fsmono_den hc d i) (he (k - i))
  have hz : ∀ i, i ≠ d → Qeq (mul (fsmono c d i) (e (k - i))) ⟨0, 1⟩ := by
    intro i hi
    have he2 : fsmono c d i = ⟨0, 1⟩ := by unfold fsmono; rw [if_neg hi]
    rw [he2]; simp [Qeq, mul]
  have hgd : Qeq (mul (fsmono c d d) (e (k - d))) (mul c (e (k - d))) := by
    have he2 : fsmono c d d = c := by unfold fsmono; rw [if_pos rfl]
    rw [he2]; exact Qeq_refl _
  show Qeq (Fsum (fun i => mul (fsmono c d i) (e (k - i))) k) (mul c (e (k - d)))
  exact Qeq_trans (hg d) (Fsum_single hg hz hdk) hgd

theorem fmul_fsmono_zero {c : Q} (hc : 0 < c.den) (e : Nat → Q) (he : ∀ i, 0 < (e i).den) (d : Nat)
    {k : Nat} (hk : k < d) : Qeq (fmul (fsmono c d) e k) ⟨0, 1⟩ := by
  show Qeq (Fsum (fun i => mul (fsmono c d i) (e (k - i))) k) ⟨0, 1⟩
  refine Qeq_trans (Fsum_den_pos (fun _ => Nat.one_pos) k)
    (Fsum_congr_le (g := fun _ => (⟨0, 1⟩ : Q)) (k := k) (fun i _ => ?_)) (Fsum_zeros k)
  have he2 : fsmono c d i = ⟨0, 1⟩ := by unfold fsmono; rw [if_neg (by omega)]
  rw [he2]; simp [Qeq, mul]

/-- The geometric coefficients `1/(1−t²) = Σ t²ʲ`: `1` at even degree, `0` at odd. (`= artanh'`.) -/
def gcoef (k : Nat) : Q := if k % 2 = 0 then ⟨1, 1⟩ else ⟨0, 1⟩
theorem gcoef_den (k : Nat) : 0 < (gcoef k).den := by unfold gcoef; split <;> exact Nat.one_pos

/-- The artanh coefficients `Σ t^{2n+1}/(2n+1)`: `1/k` at odd `k`, `0` at even. -/
def acoef (k : Nat) : Q := if k % 2 = 1 then ⟨1, k⟩ else ⟨0, 1⟩
theorem acoef_den (k : Nat) : 0 < (acoef k).den := by
  unfold acoef
  by_cases h : k % 2 = 1
  · rw [if_pos h]; show 0 < k; omega
  · rw [if_neg h]; exact Nat.one_pos

/-- The exp coefficients `Σ wᵏ/k!`: `1/k!` at every degree. -/
def ecoef (k : Nat) : Q := ⟨1, fct k⟩

theorem ecoef_den (k : Nat) : 0 < (ecoef k).den := fct_pos k

/-- **Exp is its own formal derivative**: `fderiv ecoef ≈ ecoef` (since `(k+1)·(1/(k+1)!) = 1/k!`). The
    formal backbone of `exp' = exp` driving the `exp(2·artanh w) = (1+w)/(1−w)` ODE. -/
theorem fderiv_ecoef (k : Nat) : Qeq (fderiv ecoef k) (ecoef k) := by
  have hsucc : (↑(fct (k + 1)) : Int) = (↑(k + 1)) * ↑(fct k) := by exact_mod_cast fct_succ k
  show Qeq (mul ⟨(k + 1 : Int), 1⟩ ⟨1, fct (k + 1)⟩) ⟨1, fct k⟩
  simp only [Qeq, mul]; push_cast [hsucc]; ring_uor

/-- The even-index terms of the formal artanh evaluation vanish. -/
theorem acoef_even_zero (w : Q) (n : Nat) :
    Qeq (mul (acoef (2 * n)) (qpow w (2 * n))) ⟨0, 1⟩ := by
  have h : acoef (2 * n) = ⟨0, 1⟩ := by unfold acoef; rw [if_neg (by omega : ¬ (2 * n) % 2 = 1)]
  rw [h]; simp [Qeq, mul]

/-- The odd-index term of the formal artanh evaluation is the analytic artanh term `w^{2n+1}/(2n+1)`. -/
theorem acoef_odd_artTerm (w : Q) (n : Nat) :
    Qeq (mul (acoef (2 * n + 1)) (qpow w (2 * n + 1))) (artTerm w n) := by
  have h : acoef (2 * n + 1) = ⟨1, 2 * n + 1⟩ := by unfold acoef; rw [if_pos (by omega)]
  rw [h]; exact Qmul_comm ⟨1, 2 * n + 1⟩ (qpow w (2 * n + 1))

/-- **Eval bridge, piece 1**: the formal artanh series evaluated at `w` (truncated at the odd cutoff
    `2N+1`) is exactly the analytic partial sum `artSum w N = Σ_{n≤N} w^{2n+1}/(2n+1)`. -/
theorem peval_acoef_artSum (w : Q) (hwd : 0 < w.den) (N : Nat) :
    Qeq (peval acoef w (2 * N + 1)) (artSum w N) := by
  induction N with
  | zero =>
      show Qeq (add (mul (acoef 0) (qpow w 0)) (mul (acoef 1) (qpow w 1))) (artTerm w 0)
      refine Qeq_trans (add_den_pos Nat.one_pos (artTerm_den_pos hwd 0))
        (Qadd_congr (acoef_even_zero w 0) (acoef_odd_artTerm w 0)) (Qzero_add _)
  | succ N ih =>
      rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 from by omega]
      show Qeq (add (add (peval acoef w (2 * N + 1)) (mul (acoef (2 * N + 1 + 1)) (qpow w (2 * N + 1 + 1))))
        (mul (acoef (2 * N + 1 + 1 + 1)) (qpow w (2 * N + 1 + 1 + 1)))) (add (artSum w N) (artTerm w (N + 1)))
      have he : Qeq (mul (acoef (2 * N + 1 + 1)) (qpow w (2 * N + 1 + 1))) ⟨0, 1⟩ := by
        rw [show 2 * N + 1 + 1 = 2 * (N + 1) from by omega]; exact acoef_even_zero w (N + 1)
      have ho : Qeq (mul (acoef (2 * N + 1 + 1 + 1)) (qpow w (2 * N + 1 + 1 + 1))) (artTerm w (N + 1)) := by
        rw [show 2 * N + 1 + 1 + 1 = 2 * (N + 1) + 1 from by omega]; exact acoef_odd_artTerm w (N + 1)
      refine Qeq_trans (add_den_pos (add_den_pos (artSum_den_pos hwd N) Nat.one_pos)
        (artTerm_den_pos hwd (N + 1))) (Qadd_congr (Qadd_congr ih he) ho) ?_
      exact Qadd_congr (Qadd_zero_right _) (Qeq_refl _)

/-- `artanh' = 1/(1−t²)` at the coefficient level: `fderiv acoef = gcoef`. -/
theorem fderiv_acoef (k : Nat) : Qeq (fderiv acoef k) (gcoef k) := by
  show Qeq (mul ⟨(k + 1 : Int), 1⟩ (acoef (k + 1))) (gcoef k)
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h
  · have h1 : acoef (k + 1) = ⟨1, k + 1⟩ := by unfold acoef; rw [if_pos (by omega)]
    have h2 : gcoef k = ⟨1, 1⟩ := by unfold gcoef; rw [if_pos h]
    rw [h1, h2]; simp [Qeq, mul]
  · have h1 : acoef (k + 1) = ⟨0, 1⟩ := by unfold acoef; rw [if_neg (by omega)]
    have h2 : gcoef k = ⟨0, 1⟩ := by unfold gcoef; rw [if_neg (by omega)]
    rw [h1, h2]; simp [Qeq, mul]

/-- The `1−t²` coefficient sequence. -/
def oneMinusSq (k : Nat) : Q := add (fsmono ⟨1, 1⟩ 0 k) (fsmono ⟨-1, 1⟩ 2 k)
theorem oneMinusSq_den (k : Nat) : 0 < (oneMinusSq k).den :=
  add_den_pos (fsmono_den Nat.one_pos 0 k) (fsmono_den Nat.one_pos 2 k)

/-- Two-step parity cancellation `gcoef_{k+2} − gcoef_k = 0`. -/
theorem gcoef_shift_cancel (k : Nat) :
    Qeq (add (mul ⟨1, 1⟩ (gcoef (k + 2))) (mul ⟨-1, 1⟩ (gcoef k))) ⟨0, 1⟩ := by
  have h2 : (k + 2) % 2 = k % 2 := by omega
  unfold gcoef; rw [h2]
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h <;> rw [h] <;> decide

/-- The per-degree split `((1−t²)·gcoef)_k = gcoef_k − gcoef_{k−2} = (fone)_k`. -/
theorem artanh_main : ∀ k,
    Qeq (add (fmul (fsmono ⟨1, 1⟩ 0) gcoef k) (fmul (fsmono ⟨-1, 1⟩ 2) gcoef k)) (fone k)
  | 0 => by
      have h0 : Qeq (fmul (fsmono ⟨1, 1⟩ 0) gcoef 0) (mul ⟨1, 1⟩ (gcoef 0)) :=
        fmul_fsmono Nat.one_pos gcoef (fun _ => gcoef_den _) 0 (by omega)
      have h2 : Qeq (fmul (fsmono ⟨-1, 1⟩ 2) gcoef 0) ⟨0, 1⟩ :=
        fmul_fsmono_zero Nat.one_pos gcoef (fun _ => gcoef_den _) 2 (by omega)
      exact Qeq_trans (add_den_pos (Qmul_den_pos Nat.one_pos (gcoef_den 0)) Nat.one_pos)
        (Qadd_congr h0 h2) (by decide)
  | 1 => by
      have h0 : Qeq (fmul (fsmono ⟨1, 1⟩ 0) gcoef 1) (mul ⟨1, 1⟩ (gcoef 1)) :=
        fmul_fsmono Nat.one_pos gcoef (fun _ => gcoef_den _) 0 (by omega)
      have h2 : Qeq (fmul (fsmono ⟨-1, 1⟩ 2) gcoef 1) ⟨0, 1⟩ :=
        fmul_fsmono_zero Nat.one_pos gcoef (fun _ => gcoef_den _) 2 (by omega)
      exact Qeq_trans (add_den_pos (Qmul_den_pos Nat.one_pos (gcoef_den 1)) Nat.one_pos)
        (Qadd_congr h0 h2) (by decide)
  | (k + 2) => by
      have h0 : Qeq (fmul (fsmono ⟨1, 1⟩ 0) gcoef (k + 2)) (mul ⟨1, 1⟩ (gcoef (k + 2))) :=
        fmul_fsmono Nat.one_pos gcoef (fun _ => gcoef_den _) 0 (by omega)
      have h2 : Qeq (fmul (fsmono ⟨-1, 1⟩ 2) gcoef (k + 2)) (mul ⟨-1, 1⟩ (gcoef k)) := by
        have h := fmul_fsmono (c := ⟨-1, 1⟩) Nat.one_pos gcoef (fun _ => gcoef_den _) 2
          (show 2 ≤ k + 2 by omega)
        rwa [show k + 2 - 2 = k from by omega] at h
      refine Qeq_trans (add_den_pos (Qmul_den_pos Nat.one_pos (gcoef_den (k + 2)))
        (Qmul_den_pos Nat.one_pos (gcoef_den k))) (Qadd_congr h0 h2) ?_
      have ht : Qeq (⟨0, 1⟩ : Q) (fone (k + 2)) := by
        unfold fone; rw [if_neg (by omega)]; exact Qeq_refl _
      exact Qeq_trans Nat.one_pos (gcoef_shift_cancel k) ht

/-- `fcomp` respects `≈` in its outer (composed) argument. -/
theorem fcomp_congr_left {a a' b : Nat → Q} (h : ∀ i, Qeq (a i) (a' i)) (k : Nat) :
    Qeq (fcomp a b k) (fcomp a' b k) :=
  Fsum_congr (fun m => Qmul_congr (h m) (Qeq_refl _)) k

/-- Finite sums distribute over subtraction. -/
theorem Fsum_sub {f g : Nat → Q} (hf : ∀ i, 0 < (f i).den) (hg : ∀ i, 0 < (g i).den) :
    ∀ k, Qeq (Fsum (fun i => Qsub (f i) (g i)) k) (Qsub (Fsum f k) (Fsum g k))
  | 0 => Qeq_refl _
  | (k + 1) => by
      show Qeq (add (Fsum (fun i => Qsub (f i) (g i)) k) (Qsub (f (k + 1)) (g (k + 1))))
        (Qsub (add (Fsum f k) (f (k + 1))) (add (Fsum g k) (g (k + 1))))
      refine Qeq_trans (add_den_pos (Qsub_den_pos (Fsum_den_pos hf k) (Fsum_den_pos hg k))
          (Qsub_den_pos (hf _) (hg _))) (Qadd_congr (Fsum_sub hf hg k) (Qeq_refl _)) ?_
      simp only [Qeq, add, Qsub, neg]; push_cast; ring_uor

/-- **Left-distributivity over subtraction**: `(a−b)·c = a·c − b·c` (formal Cauchy product). -/
theorem fmul_sub_left {a b c : Nat → Q} (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den)
    (hc : ∀ i, 0 < (c i).den) (k : Nat) :
    Qeq (fmul (fun i => Qsub (a i) (b i)) c k) (Qsub (fmul a c k) (fmul b c k)) := by
  show Qeq (Fsum (fun i => mul (Qsub (a i) (b i)) (c (k - i))) k)
    (Qsub (Fsum (fun i => mul (a i) (c (k - i))) k) (Fsum (fun i => mul (b i) (c (k - i))) k))
  refine Qeq_trans (Fsum_den_pos (fun i => Qsub_den_pos (Qmul_den_pos (ha i) (hc (k - i)))
      (Qmul_den_pos (hb i) (hc (k - i)))) k)
    (Fsum_congr (fun i => Qmul_sub_right (a i) (b i) (c (k - i))) k)
    (Fsum_sub (fun i => Qmul_den_pos (ha i) (hc (k - i)))
      (fun i => Qmul_den_pos (hb i) (hc (k - i))) k)

/-- From `a − b = 0` conclude `a = b`. -/
theorem Qeq_of_Qsub_zero {a b : Q} (h : Qeq (Qsub a b) ⟨0, 1⟩) : Qeq a b := by
  simp only [Qeq, Qsub, add, neg, Int.neg_mul, Int.mul_one, Int.zero_mul] at h ⊢
  omega

/-- The 2-step evaluation `((1−t²)·X)_{j+2} = X_{j+2} − X_j`. -/
theorem oneMinusSq_eval2 (X : Nat → Q) (hX : ∀ i, 0 < (X i).den) (j : Nat) :
    Qeq (fmul oneMinusSq X (j + 2)) (Qsub (X (j + 2)) (X j)) := by
  have hsplit := fmul_add_left (fun i => fsmono_den (c := ⟨1, 1⟩) Nat.one_pos 0 i)
    (fun i => fsmono_den (c := ⟨-1, 1⟩) Nat.one_pos 2 i) hX (j + 2)
  have e1 : Qeq (fmul (fsmono ⟨1, 1⟩ 0) X (j + 2)) (X (j + 2)) := by
    have hh := fmul_fsmono (c := ⟨1, 1⟩) Nat.one_pos X hX 0 (Nat.zero_le (j + 2))
    rw [Nat.sub_zero] at hh
    exact Qeq_trans (Qmul_den_pos Nat.one_pos (hX _)) hh (by simp [Qeq, mul])
  have e2 : Qeq (fmul (fsmono ⟨-1, 1⟩ 2) X (j + 2)) (mul ⟨-1, 1⟩ (X j)) := by
    have hh := fmul_fsmono (c := ⟨-1, 1⟩) Nat.one_pos X hX 2 (show 2 ≤ j + 2 by omega)
    rwa [show j + 2 - 2 = j from by omega] at hh
  refine Qeq_trans (add_den_pos (fmul_den_pos (fun i => fsmono_den (c := ⟨1, 1⟩) Nat.one_pos 0 i) hX (j + 2))
      (fmul_den_pos (fun i => fsmono_den (c := ⟨-1, 1⟩) Nat.one_pos 2 i) hX (j + 2))) hsplit ?_
  refine Qeq_trans (add_den_pos (hX (j + 2)) (Qmul_den_pos Nat.one_pos (hX j)))
    (Qadd_congr e1 e2) ?_
  simp only [Qeq, add, mul, Qsub, neg]; push_cast; ring_uor

/-- The base evaluations `((1−t²)·X)_0 = X_0` and `((1−t²)·X)_1 = X_1`. -/
theorem oneMinusSq_eval0 (X : Nat → Q) (hX : ∀ i, 0 < (X i).den) :
    Qeq (fmul oneMinusSq X 0) (X 0) := by
  have hsplit := fmul_add_left (fun i => fsmono_den (c := ⟨1, 1⟩) Nat.one_pos 0 i)
    (fun i => fsmono_den (c := ⟨-1, 1⟩) Nat.one_pos 2 i) hX 0
  have e1 : Qeq (fmul (fsmono ⟨1, 1⟩ 0) X 0) (X 0) := by
    have hh := fmul_fsmono (c := ⟨1, 1⟩) Nat.one_pos X hX 0 (Nat.le_refl 0)
    exact Qeq_trans (Qmul_den_pos Nat.one_pos (hX _)) hh (by simp [Qeq, mul])
  have e2 : Qeq (fmul (fsmono ⟨-1, 1⟩ 2) X 0) ⟨0, 1⟩ :=
    fmul_fsmono_zero Nat.one_pos X hX 2 (by omega)
  refine Qeq_trans (add_den_pos (fmul_den_pos (fun i => fsmono_den (c := ⟨1, 1⟩) Nat.one_pos 0 i) hX 0)
      (fmul_den_pos (fun i => fsmono_den (c := ⟨-1, 1⟩) Nat.one_pos 2 i) hX 0)) hsplit ?_
  refine Qeq_trans (add_den_pos (hX 0) Nat.one_pos) (Qadd_congr e1 e2) (Qadd_zero_right _)

theorem oneMinusSq_eval1 (X : Nat → Q) (hX : ∀ i, 0 < (X i).den) :
    Qeq (fmul oneMinusSq X 1) (X 1) := by
  have hsplit := fmul_add_left (fun i => fsmono_den (c := ⟨1, 1⟩) Nat.one_pos 0 i)
    (fun i => fsmono_den (c := ⟨-1, 1⟩) Nat.one_pos 2 i) hX 1
  have e1 : Qeq (fmul (fsmono ⟨1, 1⟩ 0) X 1) (X 1) := by
    have hh := fmul_fsmono (c := ⟨1, 1⟩) (k := 1) Nat.one_pos X hX 0 (by omega)
    rw [Nat.sub_zero] at hh
    exact Qeq_trans (Qmul_den_pos Nat.one_pos (hX _)) hh (by simp [Qeq, mul])
  have e2 : Qeq (fmul (fsmono ⟨-1, 1⟩ 2) X 1) ⟨0, 1⟩ :=
    fmul_fsmono_zero Nat.one_pos X hX 2 (by omega)
  refine Qeq_trans (add_den_pos (fmul_den_pos (fun i => fsmono_den (c := ⟨1, 1⟩) Nat.one_pos 0 i) hX 1)
      (fmul_den_pos (fun i => fsmono_den (c := ⟨-1, 1⟩) Nat.one_pos 2 i) hX 1)) hsplit ?_
  refine Qeq_trans (add_den_pos (hX 1) Nat.one_pos) (Qadd_congr e1 e2) (Qadd_zero_right _)

/-- **`(1−t²)` is a unit**: `(1−t²)·Z = 0 ⇒ Z = 0` (the `Z_k = Z_{k−2}` recurrence with `Z₀=Z₁=0`,
    proved by ordinary induction on the consecutive pair `(Z_k, Z_{k+1})`). -/
theorem oneMinusSq_zero_cancel {Z : Nat → Q} (hZ : ∀ i, 0 < (Z i).den)
    (h : ∀ k, Qeq (fmul oneMinusSq Z k) ⟨0, 1⟩) : ∀ k, Qeq (Z k) ⟨0, 1⟩ := by
  have key : ∀ k, Qeq (Z k) ⟨0, 1⟩ ∧ Qeq (Z (k + 1)) ⟨0, 1⟩ := by
    intro k
    induction k with
    | zero => exact ⟨Qeq_trans (fmul_den_pos (fun i => oneMinusSq_den i) hZ 0)
                       (Qeq_symm (oneMinusSq_eval0 Z hZ)) (h 0),
                     Qeq_trans (fmul_den_pos (fun i => oneMinusSq_den i) hZ 1)
                       (Qeq_symm (oneMinusSq_eval1 Z hZ)) (h 1)⟩
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        have hev : Qeq (Qsub (Z (n + 2)) (Z n)) ⟨0, 1⟩ :=
          Qeq_trans (fmul_den_pos (fun i => oneMinusSq_den i) hZ (n + 2))
            (Qeq_symm (oneMinusSq_eval2 Z hZ n)) (h (n + 2))
        have hrw : Qeq (Z (n + 2)) (add (Qsub (Z (n + 2)) (Z n)) (Z n)) := by
          simp only [Qeq, add, Qsub, neg]; push_cast; ring_uor
        have hsum : Qeq (add (Qsub (Z (n + 2)) (Z n)) (Z n)) ⟨0, 1⟩ :=
          Qeq_trans (add_den_pos Nat.one_pos Nat.one_pos) (Qadd_congr hev ih.1)
            (by simp [Qeq, add])
        exact Qeq_trans (add_den_pos (Qsub_den_pos (hZ (n + 2)) (hZ n)) (hZ n)) hrw hsum
  exact fun k => (key k).1

/-- **`fmul oneMinusSq` is injective**: the ODE-uniqueness cancellation. -/
theorem fmul_oneMinusSq_cancel {X Y : Nat → Q} (hX : ∀ i, 0 < (X i).den) (hY : ∀ i, 0 < (Y i).den)
    (h : ∀ k, Qeq (fmul oneMinusSq X k) (fmul oneMinusSq Y k)) (k : Nat) : Qeq (X k) (Y k) := by
  have hZ : ∀ i, 0 < (Qsub (X i) (Y i)).den := fun i => Qsub_den_pos (hX i) (hY i)
  have hzero : ∀ m, Qeq (fmul oneMinusSq (fun i => Qsub (X i) (Y i)) m) ⟨0, 1⟩ := by
    intro m
    have hXc : Qeq (fmul X oneMinusSq m) (fmul oneMinusSq X m) :=
      fmul_comm X oneMinusSq hX (fun i => oneMinusSq_den i) m
    have hYc : Qeq (fmul Y oneMinusSq m) (fmul oneMinusSq Y m) :=
      fmul_comm Y oneMinusSq hY (fun i => oneMinusSq_den i) m
    refine Qeq_trans (fmul_den_pos hZ (fun i => oneMinusSq_den i) m)
      (fmul_comm oneMinusSq (fun i => Qsub (X i) (Y i)) (fun i => oneMinusSq_den i) hZ m) ?_
    refine Qeq_trans (Qsub_den_pos (fmul_den_pos hX (fun i => oneMinusSq_den i) m)
        (fmul_den_pos hY (fun i => oneMinusSq_den i) m))
      (fmul_sub_left hX hY (fun i => oneMinusSq_den i) m) ?_
    refine Qeq_trans (Qsub_den_pos (fmul_den_pos (fun i => oneMinusSq_den i) hX m)
        (fmul_den_pos (fun i => oneMinusSq_den i) hY m)) (Qsub_congr hXc hYc) ?_
    exact Qeq_trans (Qsub_den_pos (fmul_den_pos (fun i => oneMinusSq_den i) hX m)
        (fmul_den_pos (fun i => oneMinusSq_den i) hX m))
      (Qsub_congr (Qeq_refl _) (Qeq_symm (h m)))
      (by simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor)
  exact Qeq_of_Qsub_zero (oneMinusSq_zero_cancel hZ hzero k)

/-- The 2-step evaluation `((1+t²)·X)_{j+2} = X_{j+2} + X_j`. -/
theorem oneplusSq_eval2 (X : Nat → Q) (hX : ∀ i, 0 < (X i).den) (j : Nat) :
    Qeq (fmul oneplusSq X (j + 2)) (add (X (j + 2)) (X j)) := by
  have hsplit := fmul_add_left (fun i => fmono_den 0 i) (fun i => fmono_den 2 i) hX (j + 2)
  have e1 : Qeq (fmul (fmono 0) X (j + 2)) (X (j + 2)) := by
    have hh := fmul_fmono hX 0 (Nat.zero_le (j + 2)); rwa [Nat.sub_zero] at hh
  have e2 : Qeq (fmul (fmono 2) X (j + 2)) (X j) := by
    have hh := fmul_fmono hX 2 (show 2 ≤ j + 2 by omega); rwa [show j + 2 - 2 = j from by omega] at hh
  exact Qeq_trans (add_den_pos (fmul_den_pos (fun i => fmono_den 0 i) hX (j + 2))
    (fmul_den_pos (fun i => fmono_den 2 i) hX (j + 2))) hsplit (Qadd_congr e1 e2)

theorem oneplusSq_eval0 (X : Nat → Q) (hX : ∀ i, 0 < (X i).den) :
    Qeq (fmul oneplusSq X 0) (X 0) := by
  have hsplit := fmul_add_left (fun i => fmono_den 0 i) (fun i => fmono_den 2 i) hX 0
  have e1 : Qeq (fmul (fmono 0) X 0) (X 0) := fmul_fmono hX 0 (Nat.le_refl 0)
  have e2 : Qeq (fmul (fmono 2) X 0) ⟨0, 1⟩ := fmul_fmono_zero hX (by omega)
  refine Qeq_trans (add_den_pos (fmul_den_pos (fun i => fmono_den 0 i) hX 0)
      (fmul_den_pos (fun i => fmono_den 2 i) hX 0)) hsplit ?_
  exact Qeq_trans (add_den_pos (hX 0) Nat.one_pos) (Qadd_congr e1 e2) (Qadd_zero_right _)

theorem oneplusSq_eval1 (X : Nat → Q) (hX : ∀ i, 0 < (X i).den) :
    Qeq (fmul oneplusSq X 1) (X 1) := by
  have hsplit := fmul_add_left (fun i => fmono_den 0 i) (fun i => fmono_den 2 i) hX 1
  have e1 : Qeq (fmul (fmono 0) X 1) (X 1) := by
    have hh := fmul_fmono (k := 1) hX 0 (by omega); rwa [Nat.sub_zero] at hh
  have e2 : Qeq (fmul (fmono 2) X 1) ⟨0, 1⟩ := fmul_fmono_zero hX (by omega)
  refine Qeq_trans (add_den_pos (fmul_den_pos (fun i => fmono_den 0 i) hX 1)
      (fmul_den_pos (fun i => fmono_den 2 i) hX 1)) hsplit ?_
  exact Qeq_trans (add_den_pos (hX 1) Nat.one_pos) (Qadd_congr e1 e2) (Qadd_zero_right _)

/-- **`(1+t²)` is a unit**: `(1+t²)·Z = 0 ⇒ Z = 0` (`Z_{k+2} = −Z_k`, `Z₀=Z₁=0`). -/
theorem oneplusSq_zero_cancel {Z : Nat → Q} (hZ : ∀ i, 0 < (Z i).den)
    (h : ∀ k, Qeq (fmul oneplusSq Z k) ⟨0, 1⟩) : ∀ k, Qeq (Z k) ⟨0, 1⟩ := by
  have key : ∀ k, Qeq (Z k) ⟨0, 1⟩ ∧ Qeq (Z (k + 1)) ⟨0, 1⟩ := by
    intro k
    induction k with
    | zero => exact ⟨Qeq_trans (fmul_den_pos (fun i => oneplusSq_den i) hZ 0)
                       (Qeq_symm (oneplusSq_eval0 Z hZ)) (h 0),
                     Qeq_trans (fmul_den_pos (fun i => oneplusSq_den i) hZ 1)
                       (Qeq_symm (oneplusSq_eval1 Z hZ)) (h 1)⟩
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        have hev : Qeq (add (Z (n + 2)) (Z n)) ⟨0, 1⟩ :=
          Qeq_trans (fmul_den_pos (fun i => oneplusSq_den i) hZ (n + 2))
            (Qeq_symm (oneplusSq_eval2 Z hZ n)) (h (n + 2))
        have hrw : Qeq (Z (n + 2)) (Qsub (add (Z (n + 2)) (Z n)) (Z n)) := by
          simp only [Qeq, add, Qsub, neg]; push_cast; ring_uor
        have hsum : Qeq (Qsub (add (Z (n + 2)) (Z n)) (Z n)) ⟨0, 1⟩ :=
          Qeq_trans (Qsub_den_pos Nat.one_pos Nat.one_pos) (Qsub_congr hev ih.1)
            (by simp [Qeq, Qsub, add, neg])
        exact Qeq_trans (Qsub_den_pos (add_den_pos (hZ (n + 2)) (hZ n)) (hZ n)) hrw hsum
  exact fun k => (key k).1

/-- **`fmul oneplusSq` is injective**. -/
theorem fmul_oneplusSq_cancel {X Y : Nat → Q} (hX : ∀ i, 0 < (X i).den) (hY : ∀ i, 0 < (Y i).den)
    (h : ∀ k, Qeq (fmul oneplusSq X k) (fmul oneplusSq Y k)) (k : Nat) : Qeq (X k) (Y k) := by
  have hZ : ∀ i, 0 < (Qsub (X i) (Y i)).den := fun i => Qsub_den_pos (hX i) (hY i)
  have hzero : ∀ m, Qeq (fmul oneplusSq (fun i => Qsub (X i) (Y i)) m) ⟨0, 1⟩ := by
    intro m
    have hXc : Qeq (fmul X oneplusSq m) (fmul oneplusSq X m) :=
      fmul_comm X oneplusSq hX (fun i => oneplusSq_den i) m
    have hYc : Qeq (fmul Y oneplusSq m) (fmul oneplusSq Y m) :=
      fmul_comm Y oneplusSq hY (fun i => oneplusSq_den i) m
    refine Qeq_trans (fmul_den_pos hZ (fun i => oneplusSq_den i) m)
      (fmul_comm oneplusSq (fun i => Qsub (X i) (Y i)) (fun i => oneplusSq_den i) hZ m) ?_
    refine Qeq_trans (Qsub_den_pos (fmul_den_pos hX (fun i => oneplusSq_den i) m)
        (fmul_den_pos hY (fun i => oneplusSq_den i) m))
      (fmul_sub_left hX hY (fun i => oneplusSq_den i) m) ?_
    refine Qeq_trans (Qsub_den_pos (fmul_den_pos (fun i => oneplusSq_den i) hX m)
        (fmul_den_pos (fun i => oneplusSq_den i) hY m)) (Qsub_congr hXc hYc) ?_
    exact Qeq_trans (Qsub_den_pos (fmul_den_pos (fun i => oneplusSq_den i) hX m)
        (fmul_den_pos (fun i => oneplusSq_den i) hX m))
      (Qsub_congr (Qeq_refl _) (Qeq_symm (h m)))
      (by simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor)
  exact Qeq_of_Qsub_zero (oneplusSq_zero_cancel hZ hzero k)

/-- Sub-identity `(1+t²)·k² = 2t·k` (`= fmul twoT kdbl`), via associativity + `kdbl_rel`. -/
theorem ksq_rel (k : Nat) : Qeq (fmul oneplusSq (fmul kdbl kdbl) k) (fmul twoT kdbl k) := by
  refine Qeq_trans (fmul_den_pos (fun i => fmul_den_pos (fun j => oneplusSq_den j)
      (fun i => kdbl_den i) i) (fun i => kdbl_den i) k)
    (Qeq_symm (fmul_assoc oneplusSq kdbl kdbl (fun i => oneplusSq_den i) (fun i => kdbl_den i)
      (fun i => kdbl_den i) k)) ?_
  exact fmul_congr_left (fun i => kdbl_rel i) k

/-- The 1-shift `t·(2t) = 2t²`: `fmul (fmono 1) twoT = 2·t²` (`= fsmono ⟨2,1⟩ 2`). -/
theorem fmono1_twoT : ∀ k, Qeq (fmul (fmono 1) twoT k) (fsmono ⟨2, 1⟩ 2 k)
  | 0 => by
      have h := fmul_fmono_zero (fun i => twoT_den i) (show (0 : Nat) < 1 by omega)
      exact Qeq_trans Nat.one_pos h (by decide)
  | 1 => by
      have h := fmul_fmono (fun i => twoT_den i) 1 (show 1 ≤ 1 by omega)
      exact Qeq_trans (twoT_den _) h (by decide)
  | 2 => by
      have h := fmul_fmono (fun i => twoT_den i) 1 (show 1 ≤ 2 by omega)
      exact Qeq_trans (twoT_den _) h (by decide)
  | (j + 3) => by
      have h := fmul_fmono (fun i => twoT_den i) 1 (show 1 ≤ j + 3 by omega)
      refine Qeq_trans (twoT_den _) h ?_
      have ht : twoT (j + 3 - 1) = ⟨0, 1⟩ := by unfold twoT; rw [if_neg (by omega)]
      have hf : fsmono (⟨2, 1⟩ : Q) 2 (j + 3) = ⟨0, 1⟩ := by unfold fsmono; rw [if_neg (by omega)]
      rw [ht, hf]; simp [Qeq, mul]

/-- Sub-identity `(1+t²)·(t·k) = 2t²` (`fmul (fmono 1) kdbl = t·k`), via `fmul_swap_left` + `kdbl_rel`. -/
theorem tk_rel (k : Nat) : Qeq (fmul oneplusSq (fmul (fmono 1) kdbl) k) (fsmono ⟨2, 1⟩ 2 k) := by
  have h1 : Qeq (fmul oneplusSq (fmul (fmono 1) kdbl) k) (fmul (fmono 1) (fmul oneplusSq kdbl) k) :=
    fmul_swap_left oneplusSq (fmono 1) kdbl (fun i => oneplusSq_den i) (fun i => fmono_den 1 i)
      (fun i => kdbl_den i) k
  have h2 : Qeq (fmul (fmono 1) (fmul oneplusSq kdbl) k) (fmul (fmono 1) twoT k) :=
    fmul_congr_right (fun i => kdbl_rel i) k
  exact Qeq_trans (fmul_den_pos (fun i => fmono_den 1 i)
      (fun i => fmul_den_pos (fun j => oneplusSq_den j) (fun i => kdbl_den i) i) k) h1
    (Qeq_trans (fmul_den_pos (fun i => fmono_den 1 i) (fun i => twoT_den i) k) h2 (fmono1_twoT k))

/-- **Right-distributivity of the Cauchy product**: `a·(b+c) = a·b + a·c`. -/
theorem fmul_add_right {a b c : Nat → Q} (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den)
    (hc : ∀ i, 0 < (c i).den) (k : Nat) :
    Qeq (fmul a (fun i => add (b i) (c i)) k) (add (fmul a b k) (fmul a c k)) := by
  refine Qeq_trans (fmul_den_pos (fun i => add_den_pos (hb i) (hc i)) ha k)
    (fmul_comm a (fun i => add (b i) (c i)) ha (fun i => add_den_pos (hb i) (hc i)) k) ?_
  refine Qeq_trans (add_den_pos (fmul_den_pos hb ha k) (fmul_den_pos hc ha k))
    (fmul_add_left hb hc ha k) ?_
  exact Qadd_congr (fmul_comm b a hb ha k) (fmul_comm c a hc ha k)

/-- `(1+t²)·2 = 2 + 2t²` (`= twoFone + 2t²`). -/
theorem oneplusSq_twoFone : ∀ m, Qeq (fmul oneplusSq twoFone m) (add (twoFone m) (fsmono ⟨2, 1⟩ 2 m))
  | 0 => Qeq_trans (twoFone_den 0) (oneplusSq_eval0 twoFone (fun i => twoFone_den i)) (by decide)
  | 1 => Qeq_trans (twoFone_den 1) (oneplusSq_eval1 twoFone (fun i => twoFone_den i)) (by decide)
  | 2 => Qeq_trans (add_den_pos (twoFone_den 2) (twoFone_den 0))
      (oneplusSq_eval2 twoFone (fun i => twoFone_den i) 0) (by decide)
  | (j + 3) => by
      refine Qeq_trans (add_den_pos (twoFone_den (j + 3)) (twoFone_den (j + 1)))
        (oneplusSq_eval2 twoFone (fun i => twoFone_den i) (j + 1)) ?_
      have h2 : Qeq (twoFone (j + 1)) (fsmono (⟨2, 1⟩ : Q) 2 (j + 3)) := by
        have ha : twoFone (j + 1) = ⟨0, 1⟩ := by unfold twoFone; rw [if_neg (by omega)]
        have hb : fsmono (⟨2, 1⟩ : Q) 2 (j + 3) = ⟨0, 1⟩ := by unfold fsmono; rw [if_neg (by omega)]
        rw [ha, hb]; exact Qeq_refl _
      exact Qadd_congr (Qeq_refl _) h2

/-- From `kdbl_deriv_rel`: `(1+t²)·k' = 2 − 2t·k` in sequence form. -/
theorem oneplusSq_kderiv (m : Nat) :
    Qeq (fmul oneplusSq (fderiv kdbl) m) (Qsub (twoFone m) (fmul twoT kdbl m)) := by
  have hr : Qeq (fmul oneplusSq (fderiv kdbl) m)
      (Qsub (add (fmul twoT kdbl m) (fmul oneplusSq (fderiv kdbl) m)) (fmul twoT kdbl m)) := by
    simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
  refine Qeq_trans (Qsub_den_pos (add_den_pos (fmul_den_pos (fun i => twoT_den i) (fun i => kdbl_den i) m)
      (fmul_den_pos (fun i => oneplusSq_den i) (fun i => fderiv_den_pos (fun i => kdbl_den i) i) m))
      (fmul_den_pos (fun i => twoT_den i) (fun i => kdbl_den i) m)) hr ?_
  exact Qsub_congr (kdbl_deriv_rel m) (Qeq_refl _)

/-- **The `kdbl²` identity, internal form**: `k' + t·k + k² = 2` (`fmul_oneplusSq_cancel` of
    `(1+t²)(k'+t·k+k²) = 2(1+t²)`, the latter from the three sub-identities). -/
theorem kdbl_W (k : Nat) :
    Qeq (add (fderiv kdbl k) (add (fmul (fmono 1) kdbl k) (fmul kdbl kdbl k))) (twoFone k) := by
  have htk : ∀ i, 0 < (fmul (fmono 1) kdbl i).den :=
    fun i => fmul_den_pos (fun j => fmono_den 1 j) (fun i => kdbl_den i) i
  have hksq : ∀ i, 0 < (fmul kdbl kdbl i).den :=
    fun i => fmul_den_pos (fun i => kdbl_den i) (fun i => kdbl_den i) i
  have hk' : ∀ i, 0 < (fderiv kdbl i).den := fun i => fderiv_den_pos (fun i => kdbl_den i) i
  refine fmul_oneplusSq_cancel
    (fun i => add_den_pos (hk' i) (add_den_pos (htk i) (hksq i))) (fun i => twoFone_den i) ?_ k
  intro m
  -- distribute (1+t²) over W = k' + (t·k + k²)
  have hdist : Qeq (fmul oneplusSq
        (fun i => add (fderiv kdbl i) (add (fmul (fmono 1) kdbl i) (fmul kdbl kdbl i))) m)
      (add (fmul oneplusSq (fderiv kdbl) m)
        (add (fmul oneplusSq (fmul (fmono 1) kdbl) m) (fmul oneplusSq (fmul kdbl kdbl) m))) := by
    refine Qeq_trans (add_den_pos (fmul_den_pos (fun i => oneplusSq_den i) hk' m)
        (fmul_den_pos (fun i => oneplusSq_den i) (fun i => add_den_pos (htk i) (hksq i)) m))
      (fmul_add_right (fun i => oneplusSq_den i) hk' (fun i => add_den_pos (htk i) (hksq i)) m) ?_
    exact Qadd_congr (Qeq_refl _) (fmul_add_right (fun i => oneplusSq_den i) htk hksq m)
  -- substitute the three relations
  have hsub : Qeq (add (fmul oneplusSq (fderiv kdbl) m)
        (add (fmul oneplusSq (fmul (fmono 1) kdbl) m) (fmul oneplusSq (fmul kdbl kdbl) m)))
      (add (Qsub (twoFone m) (fmul twoT kdbl m))
        (add (fsmono ⟨2, 1⟩ 2 m) (fmul twoT kdbl m))) :=
    Qadd_congr (oneplusSq_kderiv m) (Qadd_congr (tk_rel m) (ksq_rel m))
  -- the ±(2t·k) cancel: (C − A) + (B + A) = C + B = 2 + 2t²
  have hcancel : Qeq (add (Qsub (twoFone m) (fmul twoT kdbl m))
        (add (fsmono ⟨2, 1⟩ 2 m) (fmul twoT kdbl m)))
      (add (twoFone m) (fsmono ⟨2, 1⟩ 2 m)) := by
    simp only [Qeq, add, Qsub, neg]; push_cast; ring_uor
  -- chain: (1+t²)W ≈ 2+2t² ≈ (1+t²)·2
  refine Qeq_trans (add_den_pos (fmul_den_pos (fun i => oneplusSq_den i) hk' m)
      (add_den_pos (fmul_den_pos (fun i => oneplusSq_den i) htk m)
        (fmul_den_pos (fun i => oneplusSq_den i) hksq m))) hdist ?_
  refine Qeq_trans (add_den_pos (Qsub_den_pos (twoFone_den m)
        (fmul_den_pos (fun i => twoT_den i) (fun i => kdbl_den i) m))
      (add_den_pos (fsmono_den (c := ⟨2, 1⟩) Nat.one_pos 2 m)
        (fmul_den_pos (fun i => twoT_den i) (fun i => kdbl_den i) m))) hsub ?_
  refine Qeq_trans (add_den_pos (twoFone_den m) (fsmono_den (c := ⟨2, 1⟩) Nat.one_pos 2 m))
    hcancel ?_
  exact Qeq_symm (oneplusSq_twoFone m)

/-- `2 = 2·1` (`twoFone = 2·fone`). -/
theorem twoFone_2fone (m : Nat) : Qeq (twoFone m) (mul ⟨2, 1⟩ (fone m)) := by
  unfold twoFone fone; by_cases h : m = 0
  · rw [if_pos h, if_pos h]; decide
  · rw [if_neg h, if_neg h]; decide

/-- `twoFone = 2·t⁰` as a scaled monomial. -/
theorem twoFone_fsmono (m : Nat) : Qeq (twoFone m) (fsmono ⟨2, 1⟩ 0 m) := by
  unfold twoFone fsmono; by_cases h : m = 0
  · rw [if_pos h, if_pos h]; decide
  · rw [if_neg h, if_neg h]; decide

/-- `fmul twoFone X = 2·X` (the constant `2` series scales). -/
theorem fmul_twoFone (X : Nat → Q) (hX : ∀ i, 0 < (X i).den) (m : Nat) :
    Qeq (fmul twoFone X m) (mul ⟨2, 1⟩ (X m)) := by
  refine Qeq_trans (fmul_den_pos (fun i => fsmono_den (c := ⟨2, 1⟩) Nat.one_pos 0 i) hX m)
    (fmul_congr_left (fun i => twoFone_fsmono i) m) ?_
  have hh := fmul_fsmono (c := ⟨2, 1⟩) Nat.one_pos X hX 0 (Nat.zero_le m)
  rwa [Nat.sub_zero] at hh

/-- `twoT = 2·t` as a scaled monomial. -/
theorem twoT_fmono (m : Nat) : Qeq (twoT m) (mul ⟨2, 1⟩ (fmono 1 m)) := by
  unfold twoT fmono; by_cases h : m = 1
  · rw [if_pos h, if_pos h]; decide
  · rw [if_neg h, if_neg h]; decide

/-- `2t·k = 2·(t·k)`. -/
theorem twoT_2tk (m : Nat) :
    Qeq (fmul twoT kdbl m) (mul ⟨2, 1⟩ (fmul (fmono 1) kdbl m)) := by
  refine Qeq_trans (fmul_den_pos (fun i => kdbl_den i) (fun i => twoT_den i) m)
    (fmul_comm twoT kdbl (fun i => twoT_den i) (fun i => kdbl_den i) m) ?_
  refine Qeq_trans (fmul_den_pos (fun i => kdbl_den i)
      (fun i => Qmul_den_pos Nat.one_pos (fmono_den 1 i)) m)
    (fmul_congr_right (fun i => twoT_fmono i) m) ?_
  refine Qeq_trans (Qmul_den_pos Nat.one_pos (fmul_den_pos (fun i => kdbl_den i)
      (fun i => fmono_den 1 i) m))
    (fmul_smul_right kdbl (fmono 1) ⟨2, 1⟩ Nat.one_pos (fun i => kdbl_den i) (fun i => fmono_den 1 i) m) ?_
  exact Qmul_congr (Qeq_refl _) (fmul_comm kdbl (fmono 1) (fun i => kdbl_den i) (fun i => fmono_den 1 i) m)

/-- `(1−t²) = 2 − (1+t²)` as a sequence. -/
theorem oneMinusSq_as_sub (m : Nat) : Qeq (oneMinusSq m) (Qsub (twoFone m) (oneplusSq m)) := by
  unfold oneMinusSq oneplusSq fsmono fmono twoFone
  by_cases h0 : m = 0
  · subst h0; decide
  · by_cases h2 : m = 2
    · subst h2; decide
    · simp only [if_neg h0, if_neg h2]; decide

/-- **The `kdbl²` identity** `(1−t²)·k' = 2·(1 − k²)` — from `kdbl_W` (`k'+t·k+k²=2`) by the
    `1−t² = 2 − (1+t²)` algebra: `(1−t²)k' = 2k' − (2 − 2t·k) = 2k' − 2 + 2t·k`, and `k² = 2 − k' − t·k`
    gives `2(1−k²) = −2 + 2k' + 2t·k`. The bridge from the kdbl relations to the composition side. -/
theorem kdbl_sq_id (m : Nat) :
    Qeq (fmul oneMinusSq (fderiv kdbl) m) (mul ⟨2, 1⟩ (Qsub (fone m) (fmul kdbl kdbl m))) := by
  have hk' : ∀ i, 0 < (fderiv kdbl i).den := fun i => fderiv_den_pos (fun i => kdbl_den i) i
  have htk : ∀ i, 0 < (fmul (fmono 1) kdbl i).den :=
    fun i => fmul_den_pos (fun j => fmono_den 1 j) (fun i => kdbl_den i) i
  have hksq : ∀ i, 0 < (fmul kdbl kdbl i).den :=
    fun i => fmul_den_pos (fun i => kdbl_den i) (fun i => kdbl_den i) i
  have hLHS : Qeq (fmul oneMinusSq (fderiv kdbl) m)
      (Qsub (mul ⟨2, 1⟩ (fderiv kdbl m))
        (Qsub (twoFone m) (mul ⟨2, 1⟩ (fmul (fmono 1) kdbl m)))) := by
    refine Qeq_trans (fmul_den_pos (fun i => Qsub_den_pos (twoFone_den i) (oneplusSq_den i)) hk' m)
      (fmul_congr_left (fun i => oneMinusSq_as_sub i) m) ?_
    refine Qeq_trans (Qsub_den_pos (fmul_den_pos (fun i => twoFone_den i) hk' m)
        (fmul_den_pos (fun i => oneplusSq_den i) hk' m))
      (fmul_sub_left (fun i => twoFone_den i) (fun i => oneplusSq_den i) hk' m) ?_
    refine Qeq_trans (Qsub_den_pos (Qmul_den_pos Nat.one_pos (hk' m))
        (Qsub_den_pos (twoFone_den m) (fmul_den_pos (fun i => twoT_den i) (fun i => kdbl_den i) m)))
      (Qsub_congr (fmul_twoFone (fderiv kdbl) hk' m) (oneplusSq_kderiv m)) ?_
    exact Qsub_congr (Qeq_refl _) (Qsub_congr (Qeq_refl _) (twoT_2tk m))
  have hC' : Qeq (fmul kdbl kdbl m)
      (Qsub (Qsub (mul ⟨2, 1⟩ (fone m)) (fderiv kdbl m)) (fmul (fmono 1) kdbl m)) := by
    have hr : Qeq (fmul kdbl kdbl m)
        (Qsub (Qsub (add (fderiv kdbl m) (add (fmul (fmono 1) kdbl m) (fmul kdbl kdbl m)))
          (fderiv kdbl m)) (fmul (fmono 1) kdbl m)) := by
      simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
    refine Qeq_trans (Qsub_den_pos (Qsub_den_pos (add_den_pos (hk' m) (add_den_pos (htk m) (hksq m)))
        (hk' m)) (htk m)) hr ?_
    exact Qsub_congr (Qsub_congr (Qeq_trans (twoFone_den m)
      (kdbl_W m) (twoFone_2fone m)) (Qeq_refl _)) (Qeq_refl _)
  have hfin : Qeq (Qsub (mul ⟨2, 1⟩ (fderiv kdbl m))
        (Qsub (twoFone m) (mul ⟨2, 1⟩ (fmul (fmono 1) kdbl m))))
      (mul ⟨2, 1⟩ (Qsub (fone m) (fmul kdbl kdbl m))) := by
    have step1 : Qeq (Qsub (mul ⟨2, 1⟩ (fderiv kdbl m))
          (Qsub (twoFone m) (mul ⟨2, 1⟩ (fmul (fmono 1) kdbl m))))
        (Qsub (mul ⟨2, 1⟩ (fderiv kdbl m))
          (Qsub (mul ⟨2, 1⟩ (fone m)) (mul ⟨2, 1⟩ (fmul (fmono 1) kdbl m)))) :=
      Qsub_congr (Qeq_refl _) (Qsub_congr (twoFone_2fone m) (Qeq_refl _))
    have step2 : Qeq (mul ⟨2, 1⟩ (Qsub (fone m) (fmul kdbl kdbl m)))
        (mul ⟨2, 1⟩ (Qsub (fone m)
          (Qsub (Qsub (mul ⟨2, 1⟩ (fone m)) (fderiv kdbl m)) (fmul (fmono 1) kdbl m)))) :=
      Qmul_congr (Qeq_refl _) (Qsub_congr (Qeq_refl _) hC')
    have step3 : Qeq (Qsub (mul ⟨2, 1⟩ (fderiv kdbl m))
          (Qsub (mul ⟨2, 1⟩ (fone m)) (mul ⟨2, 1⟩ (fmul (fmono 1) kdbl m))))
        (mul ⟨2, 1⟩ (Qsub (fone m)
          (Qsub (Qsub (mul ⟨2, 1⟩ (fone m)) (fderiv kdbl m)) (fmul (fmono 1) kdbl m)))) := by
      simp only [Qeq, Qsub, add, neg, mul]; push_cast; ring_uor
    refine Qeq_trans (Qsub_den_pos (Qmul_den_pos Nat.one_pos (hk' m))
        (Qsub_den_pos (Qmul_den_pos Nat.one_pos (fone_den_pos m))
          (Qmul_den_pos Nat.one_pos (htk m)))) step1 ?_
    exact Qeq_trans (Qmul_den_pos Nat.one_pos (Qsub_den_pos (fone_den_pos m)
        (Qsub_den_pos (Qsub_den_pos (Qmul_den_pos Nat.one_pos (fone_den_pos m)) (hk' m)) (htk m))))
      step3 (Qeq_symm step2)
  exact Qeq_trans (Qsub_den_pos (Qmul_den_pos Nat.one_pos (hk' m))
      (Qsub_den_pos (twoFone_den m) (Qmul_den_pos Nat.one_pos (htk m)))) hLHS hfin

/-- **Power addition** `cⁱ⁺ʲ = cⁱ·cʲ` (induction on `i` via `fmul_assoc`). -/
theorem fpow_add {c : Nat → Q} (hc : ∀ i, 0 < (c i).den) : ∀ (i j k : Nat),
    Qeq (fpow c (i + j) k) (fmul (fpow c i) (fpow c j) k)
  | 0, j, k => by
      rw [Nat.zero_add]
      show Qeq (fpow c j k) (fmul fone (fpow c j) k)
      exact Qeq_symm (Qeq_trans (fmul_den_pos (fun _ => fpow_den_pos hc j _)
        (fun _ => fone_den_pos _) k)
        (fmul_comm fone (fpow c j) (fun _ => fone_den_pos _) (fun _ => fpow_den_pos hc j _) k)
        (fmul_one (fpow c j) (fun _ => fpow_den_pos hc j _) k))
  | (i + 1), j, k => by
      have hid : i + 1 + j = (i + j) + 1 := by omega
      rw [hid]
      show Qeq (fmul c (fpow c (i + j)) k) (fmul (fmul c (fpow c i)) (fpow c j) k)
      refine Qeq_trans (fmul_den_pos hc (fun _ => fmul_den_pos (fun _ => fpow_den_pos hc i _)
          (fun _ => fpow_den_pos hc j _) _) k)
        (fmul_congr_right (fun l => fpow_add hc i j l) k) ?_
      exact Qeq_symm (fmul_assoc c (fpow c i) (fpow c j) hc (fun _ => fpow_den_pos hc i _)
        (fun _ => fpow_den_pos hc j _) k)

/-- `fcomp` distributes over addition (outer argument). -/
theorem fcomp_add {a b c : Nat → Q} (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den)
    (hc : ∀ i, 0 < (c i).den) (k : Nat) :
    Qeq (fcomp (fun i => add (a i) (b i)) c k) (add (fcomp a c k) (fcomp b c k)) := by
  show Qeq (Fsum (fun m => mul (add (a m) (b m)) (fpow c m k)) k)
    (add (Fsum (fun m => mul (a m) (fpow c m k)) k) (Fsum (fun m => mul (b m) (fpow c m k)) k))
  refine Qeq_trans (Fsum_den_pos (fun m => add_den_pos (Qmul_den_pos (ha m) (fpow_den_pos hc m k))
      (Qmul_den_pos (hb m) (fpow_den_pos hc m k))) k)
    (Fsum_congr (fun m => Qmul_add_right (a m) (b m) (fpow c m k)) k)
    (Fsum_add (fun m => Qmul_den_pos (ha m) (fpow_den_pos hc m k))
      (fun m => Qmul_den_pos (hb m) (fpow_den_pos hc m k)) k)

/-- `fcomp fone c = fone` (composing the unit). -/
theorem fcomp_fone {c : Nat → Q} (hc : ∀ i, 0 < (c i).den) (k : Nat) :
    Qeq (fcomp fone c k) (fone k) := by
  show Qeq (Fsum (fun m => mul (fone m) (fpow c m k)) k) (fone k)
  have hg : ∀ m, 0 < (mul (fone m) (fpow c m k)).den :=
    fun m => Qmul_den_pos (fone_den_pos m) (fpow_den_pos hc m k)
  have hz : ∀ m, m ≠ 0 → Qeq (mul (fone m) (fpow c m k)) ⟨0, 1⟩ := by
    intro m hm
    have he : fone m = ⟨0, 1⟩ := by unfold fone; rw [if_neg hm]
    rw [he]; simp [Qeq, mul]
  have hg0 : Qeq (mul (fone 0) (fpow c 0 k)) (fone k) := by
    show Qeq (mul ⟨1, 1⟩ (fone k)) (fone k); simp [Qeq, mul]
  exact Qeq_trans (hg 0) (Fsum_single hg hz (Nat.zero_le k)) hg0

/-- `(A−B) + (B−C) = A−C` (abstract telescope, atoms `A B C`). -/
theorem Qsub_telescope3 (A B C : Q) : Qeq (add (Qsub A B) (Qsub B C)) (Qsub A C) := by
  simp only [Qeq, add, Qsub, neg]; push_cast; ring_uor

/-- **Collapse the odd terms**: if `f` vanishes at odd indices then `Σ_{m≤2N+1} f = Σ_{j≤N} f(2j)`. -/
theorem Fsum_collapse_odd {f : Nat → Q} (hf : ∀ i, 0 < (f i).den)
    (hodd : ∀ m, Qeq (f (2 * m + 1)) ⟨0, 1⟩) (N : Nat) :
    Qeq (Fsum f (2 * N + 1)) (Fsum (fun j => f (2 * j)) N) := by
  induction N with
  | zero =>
      show Qeq (add (f 0) (f 1)) (f 0)
      exact Qeq_trans (add_den_pos (hf 0) Nat.one_pos)
        (Qadd_congr (Qeq_refl _) (show Qeq (f 1) ⟨0, 1⟩ from hodd 0)) (Qadd_zero_right _)
  | succ N ih =>
      rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 from by omega]
      show Qeq (add (add (Fsum f (2 * N + 1)) (f (2 * N + 1 + 1))) (f (2 * N + 1 + 1 + 1)))
        (add (Fsum (fun j => f (2 * j)) N) (f (2 * (N + 1))))
      have ho : Qeq (f (2 * N + 1 + 1 + 1)) ⟨0, 1⟩ := by
        rw [show 2 * N + 1 + 1 + 1 = 2 * (N + 1) + 1 from by omega]; exact hodd (N + 1)
      have he : f (2 * N + 1 + 1) = f (2 * (N + 1)) := by
        rw [show 2 * N + 1 + 1 = 2 * (N + 1) from by omega]
      refine Qeq_trans (add_den_pos (add_den_pos (Fsum_den_pos hf (2 * N + 1)) (hf _)) Nat.one_pos)
        (Qadd_congr (Qeq_refl _) ho) ?_
      refine Qeq_trans (add_den_pos (Fsum_den_pos hf (2 * N + 1)) (hf _)) (Qadd_zero_right _) ?_
      rw [he]
      exact Qadd_congr ih (Qeq_refl _)

/-- The even-power geometric partial sum `Σ_{j=0}^{N} c^{2j}` as a coefficient sequence. -/
def geoEvenPow (c : Nat → Q) (N k : Nat) : Q := Fsum (fun j => fpow c (2 * j) k) N

theorem geoEvenPow_den {c : Nat → Q} (hc : ∀ i, 0 < (c i).den) (N k : Nat) :
    0 < (geoEvenPow c N k).den := Fsum_den_pos (fun j => fpow_den_pos hc (2 * j) k) N

/-- `c²·c^{2(N+1)} = c^{2(N+2)}`: the telescope step's power bump. -/
theorem fpow_sq_bump {c : Nat → Q} (hc : ∀ i, 0 < (c i).den) (N k : Nat) :
    Qeq (fmul (fmul c c) (fpow c (2 * (N + 1))) k) (fpow c (2 * (N + 2)) k) := by
  have hcc : ∀ l, Qeq (fmul c c l) (fpow c 2 l) :=
    fun l => fmul_congr_right (fun j => Qeq_symm (fmul_one c hc j)) l
  have hadd := Qeq_symm (fpow_add hc 2 (2 * (N + 1)) k)
  rw [show 2 + 2 * (N + 1) = 2 * (N + 2) from by omega] at hadd
  exact Qeq_trans (fmul_den_pos (fun _ => fpow_den_pos hc 2 _)
    (fun _ => fpow_den_pos hc (2 * (N + 1)) _) k) (fmul_congr_left hcc k) hadd

/-- **The geometric telescope** `(1−c²)·Σ_{j≤N} c^{2j} = 1 − c^{2(N+1)}`. -/
theorem geoEven_telescope {c : Nat → Q} (hc : ∀ i, 0 < (c i).den) (N k : Nat) :
    Qeq (fmul (fun i => Qsub (fone i) (fmul c c i)) (geoEvenPow c N) k)
      (Qsub (fone k) (fpow c (2 * (N + 1)) k)) := by
  induction N with
  | zero =>
      have hge : Qeq (fmul (fun i => Qsub (fone i) (fmul c c i)) (geoEvenPow c 0) k)
          (fmul (fun i => Qsub (fone i) (fmul c c i)) fone k) :=
        fmul_congr_right (fun l => Qeq_refl _) k
      refine Qeq_trans (fmul_den_pos (fun i => Qsub_den_pos (fone_den_pos i) (fmul_den_pos hc hc i))
          (fun _ => fone_den_pos _) k) hge ?_
      refine Qeq_trans (Qsub_den_pos (fone_den_pos k) (fmul_den_pos hc hc k))
        (fmul_one (fun i => Qsub (fone i) (fmul c c i)) (fun i => Qsub_den_pos (fone_den_pos i)
          (fmul_den_pos hc hc i)) k) ?_
      refine Qsub_congr (Qeq_refl _) ?_
      show Qeq (fmul c c k) (fmul c (fmul c fone) k)
      exact fmul_congr_right (fun l => Qeq_symm (fmul_one c hc l)) k
  | succ N ih =>
      have hrec : Qeq (fmul (fun i => Qsub (fone i) (fmul c c i)) (geoEvenPow c (N + 1)) k)
          (add (fmul (fun i => Qsub (fone i) (fmul c c i)) (geoEvenPow c N) k)
            (fmul (fun i => Qsub (fone i) (fmul c c i)) (fpow c (2 * (N + 1))) k)) :=
        fmul_add_right (fun i => Qsub_den_pos (fone_den_pos i) (fmul_den_pos hc hc i))
          (fun i => geoEvenPow_den hc N i) (fun i => fpow_den_pos hc (2 * (N + 1)) i) k
      have hstep : Qeq (fmul (fun i => Qsub (fone i) (fmul c c i)) (fpow c (2 * (N + 1))) k)
          (Qsub (fpow c (2 * (N + 1)) k) (fpow c (2 * (N + 2)) k)) := by
        refine Qeq_trans (Qsub_den_pos (fmul_den_pos (fun _ => fone_den_pos _)
            (fun _ => fpow_den_pos hc (2 * (N + 1)) _) k) (fmul_den_pos (fun _ => fmul_den_pos hc hc _)
            (fun _ => fpow_den_pos hc (2 * (N + 1)) _) k))
          (fmul_sub_left (fun _ => fone_den_pos _) (fun _ => fmul_den_pos hc hc _)
            (fun _ => fpow_den_pos hc (2 * (N + 1)) _) k) ?_
        refine Qsub_congr (Qeq_trans (fmul_den_pos (fun _ => fpow_den_pos hc (2 * (N + 1)) _)
            (fun _ => fone_den_pos _) k)
          (fmul_comm fone (fpow c (2 * (N + 1))) (fun _ => fone_den_pos _)
            (fun _ => fpow_den_pos hc (2 * (N + 1)) _) k)
          (fmul_one (fpow c (2 * (N + 1))) (fun _ => fpow_den_pos hc (2 * (N + 1)) _) k))
          (fpow_sq_bump hc N k)
      refine Qeq_trans (add_den_pos (fmul_den_pos (fun i => Qsub_den_pos (fone_den_pos i)
            (fmul_den_pos hc hc i)) (fun i => geoEvenPow_den hc N i) k)
          (fmul_den_pos (fun i => Qsub_den_pos (fone_den_pos i) (fmul_den_pos hc hc i))
            (fun _ => fpow_den_pos hc (2 * (N + 1)) _) k)) hrec ?_
      refine Qeq_trans (add_den_pos (Qsub_den_pos (fone_den_pos k) (fpow_den_pos hc (2 * (N + 1)) k))
          (Qsub_den_pos (fpow_den_pos hc (2 * (N + 1)) k) (fpow_den_pos hc (2 * (N + 2)) k)))
        (Qadd_congr ih hstep) ?_
      exact Qsub_telescope3 (fone k) (fpow c (2 * (N + 1)) k) (fpow c (2 * (N + 2)) k)

/-- `kdbl 0 = 0` (the inner function vanishes at the origin). -/
theorem kdbl_zero : Qeq (kdbl 0) ⟨0, 1⟩ := by decide

/-- **`artanh'∘kdbl` is the even-power geometric series**: `fcomp gcoef kdbl i = geoEvenPow kdbl k i`
    for `i ≤ k` (the odd terms of `gcoef` vanish; the high even terms `2j>i` vanish by `fpow_vanish`). -/
theorem fcomp_gcoef_geoEven (k i : Nat) (hik : i ≤ k) :
    Qeq (fcomp gcoef kdbl i) (geoEvenPow kdbl k i) := by
  have hg : ∀ m, 0 < (mul (gcoef m) (fpow kdbl m i)).den :=
    fun m => Qmul_den_pos (gcoef_den m) (fpow_den_pos (fun i => kdbl_den i) m i)
  have hext : Qeq (Fsum (fun m => mul (gcoef m) (fpow kdbl m i)) i)
      (Fsum (fun m => mul (gcoef m) (fpow kdbl m i)) (2 * k + 1)) :=
    Fsum_extend_zero hg (by omega) (fun m hm1 _ =>
      Qeq_trans (Qmul_den_pos (gcoef_den m) Nat.one_pos)
        (Qmul_congr (Qeq_refl _) (fpow_vanish (fun i => kdbl_den i) kdbl_zero m i hm1))
        (by simp [Qeq, mul]))
  have hcol : Qeq (Fsum (fun m => mul (gcoef m) (fpow kdbl m i)) (2 * k + 1))
      (Fsum (fun j => mul (gcoef (2 * j)) (fpow kdbl (2 * j) i)) k) :=
    Fsum_collapse_odd hg (fun m => by
      have he : gcoef (2 * m + 1) = ⟨0, 1⟩ := by unfold gcoef; rw [if_neg (by omega)]
      rw [he]; simp [Qeq, mul]) k
  have hcongr : Qeq (Fsum (fun j => mul (gcoef (2 * j)) (fpow kdbl (2 * j) i)) k)
      (geoEvenPow kdbl k i) := by
    show Qeq (Fsum (fun j => mul (gcoef (2 * j)) (fpow kdbl (2 * j) i)) k)
      (Fsum (fun j => fpow kdbl (2 * j) i) k)
    refine Fsum_congr (fun j => ?_) k
    have he : gcoef (2 * j) = ⟨1, 1⟩ := by unfold gcoef; rw [if_pos (by omega)]
    rw [he]; simp [Qeq, mul]
  show Qeq (Fsum (fun m => mul (gcoef m) (fpow kdbl m i)) i) (geoEvenPow kdbl k i)
  exact Qeq_trans (Fsum_den_pos hg (2 * k + 1)) hext
    (Qeq_trans (Fsum_den_pos (fun j => Qmul_den_pos (gcoef_den _)
      (fpow_den_pos (fun i => kdbl_den i) _ i)) k) hcol hcongr)

/-- **The composition identity** `(1−k²)·(artanh'∘kdbl) = 1` (piece ii). Replace `artanh'∘kdbl` by the
    geometric partial sum on `[0,k]`, then the telescope gives `1 − kdbl^{2(k+1)}_k = 1` (high power
    vanishes). -/
theorem comp_recip (k : Nat) :
    Qeq (fmul (fun i => Qsub (fone i) (fmul kdbl kdbl i)) (fcomp gcoef kdbl) k) (fone k) := by
  have hcong : Qeq (fmul (fun i => Qsub (fone i) (fmul kdbl kdbl i)) (fcomp gcoef kdbl) k)
      (fmul (fun i => Qsub (fone i) (fmul kdbl kdbl i)) (geoEvenPow kdbl k) k) := by
    show Qeq (Fsum (fun p => mul (Qsub (fone p) (fmul kdbl kdbl p)) (fcomp gcoef kdbl (k - p))) k)
      (Fsum (fun p => mul (Qsub (fone p) (fmul kdbl kdbl p)) (geoEvenPow kdbl k (k - p))) k)
    exact Fsum_congr_le (k := k) (fun p _ =>
      Qmul_congr (Qeq_refl _) (fcomp_gcoef_geoEven k (k - p) (by omega)))
  have htel : Qeq (fmul (fun i => Qsub (fone i) (fmul kdbl kdbl i)) (geoEvenPow kdbl k) k)
      (Qsub (fone k) (fpow kdbl (2 * (k + 1)) k)) :=
    geoEven_telescope (fun i => kdbl_den i) k k
  have hvan : Qeq (fpow kdbl (2 * (k + 1)) k) ⟨0, 1⟩ :=
    fpow_vanish (fun i => kdbl_den i) kdbl_zero (2 * (k + 1)) k (by omega)
  refine Qeq_trans (fmul_den_pos (fun i => Qsub_den_pos (fone_den_pos i) (fmul_den_pos
      (fun i => kdbl_den i) (fun i => kdbl_den i) i)) (fun i => geoEvenPow_den (fun i => kdbl_den i) k i) k)
    hcong ?_
  refine Qeq_trans (Qsub_den_pos (fone_den_pos k) (fpow_den_pos (fun i => kdbl_den i) (2 * (k + 1)) k))
    htel ?_
  refine Qeq_trans (Qsub_den_pos (fone_den_pos k) Nat.one_pos) (Qsub_congr (Qeq_refl _) hvan) ?_
  exact Qadd_zero_right _

/-- **Antiderivative uniqueness**: equal formal derivatives + equal constant term ⇒ equal series. -/
theorem fderiv_inj {y z : Nat → Q} (hd : ∀ k, Qeq (fderiv y k) (fderiv z k))
    (h0 : Qeq (y 0) (z 0)) (k : Nat) : Qeq (y k) (z k) := by
  cases k with
  | zero => exact h0
  | succ n =>
      have hh := hd n
      simp only [Qeq, fderiv, mul, Nat.one_mul] at hh
      push_cast at hh
      show Qeq (y (n + 1)) (z (n + 1))
      simp only [Qeq]; push_cast
      refine Int.eq_of_mul_eq_mul_left (a := (n : Int) + 1) (by omega) ?_
      rw [← Int.mul_assoc, ← Int.mul_assoc]; exact hh

/-- **Multiplicative-ODE uniqueness**: if `y' = d·y` and `z' = d·z` (formally, `fderiv · ≈ fmul d ·`) with
    `y 0 ≈ z 0`, then `y ≈ z`. Unlike `fderiv_inj` (additive: `y' = z'` given), here the derivative depends
    on the unknown, so we use STRONG induction — the recursion `(k+1)·y_{k+1} = Σ_{i≤k} dᵢ·y_{k−i}` determines
    `y_{k+1}` from `y_0..y_k`. The uniqueness behind `exp(2·artanh w) = (1+w)/(1−w)` (both solve `y'=d·y`). -/
theorem fderiv_mul_inj {d y z : Nat → Q} (hyd : ∀ i, 0 < (y i).den) (hzd : ∀ i, 0 < (z i).den)
    (hdd : ∀ i, 0 < (d i).den)
    (hy : ∀ k, Qeq (fderiv y k) (fmul d y k)) (hz : ∀ k, Qeq (fderiv z k) (fmul d z k))
    (h0 : Qeq (y 0) (z 0)) : ∀ k, Qeq (y k) (z k) := by
  have aux : ∀ k j, j ≤ k → Qeq (y j) (z j) := by
    intro k
    induction k with
    | zero => intro j hj; have : j = 0 := Nat.le_zero.mp hj; subst this; exact h0
    | succ n ih =>
        intro j hj
        rcases Nat.lt_or_ge j (n + 1) with hlt | hge
        · exact ih j (by omega)
        · have hjn : j = n + 1 := by omega
          subst hjn
          have hfmul : Qeq (fmul d y n) (fmul d z n) :=
            Fsum_congr_le (fun i _ => Qmul_congr (Qeq_refl _) (ih (n - i) (by omega)))
          have hh : Qeq (fderiv y n) (fderiv z n) :=
            Qeq_trans (fmul_den_pos hdd hyd n) (hy n)
              (Qeq_trans (fmul_den_pos hdd hzd n) hfmul (Qeq_symm (hz n)))
          simp only [Qeq, fderiv, mul, Nat.one_mul] at hh
          push_cast at hh
          show Qeq (y (n + 1)) (z (n + 1))
          simp only [Qeq]; push_cast
          refine Int.eq_of_mul_eq_mul_left (a := (n : Int) + 1) (by omega) ?_
          rw [← Int.mul_assoc, ← Int.mul_assoc]; exact hh
  exact fun k => aux k k (Nat.le_refl k)

/-- **The artanh ODE** `(1−t²)·artanh' = 1` at the coefficient level. -/
theorem artanh_ode (k : Nat) : Qeq (fmul oneMinusSq gcoef k) (fone k) :=
  Qeq_trans (add_den_pos (fmul_den_pos (fun i => fsmono_den Nat.one_pos 0 i) (fun _ => gcoef_den _) k)
      (fmul_den_pos (fun i => fsmono_den Nat.one_pos 2 i) (fun _ => gcoef_den _) k))
    (fmul_add_left (fun i => fsmono_den Nat.one_pos 0 i) (fun i => fsmono_den Nat.one_pos 2 i)
      (fun _ => gcoef_den _) k)
    (artanh_main k)

/-- The `2·artanh` side of the ODE: `(1−t²)·(2·artanh)' = 2`. -/
theorem twoacoef_ode (j : Nat) :
    Qeq (fmul oneMinusSq (fderiv (fun i => mul ⟨2, 1⟩ (acoef i))) j) (twoFone j) := by
  have hd2 : ∀ l, Qeq (fderiv (fun i => mul ⟨2, 1⟩ (acoef i)) l) (mul ⟨2, 1⟩ (gcoef l)) := by
    intro l
    show Qeq (mul ⟨(l + 1 : Int), 1⟩ (mul ⟨2, 1⟩ (acoef (l + 1)))) (mul ⟨2, 1⟩ (gcoef l))
    refine Qeq_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (acoef_den (l + 1)))) ?_
      (Qmul_congr (Qeq_refl _) (fderiv_acoef l))
    show Qeq (mul ⟨(l + 1 : Int), 1⟩ (mul ⟨2, 1⟩ (acoef (l + 1))))
      (mul ⟨2, 1⟩ (mul ⟨(l + 1 : Int), 1⟩ (acoef (l + 1))))
    simp only [Qeq, mul]; push_cast; ring_uor
  refine Qeq_trans (fmul_den_pos (fun i => oneMinusSq_den i)
      (fun i => Qmul_den_pos Nat.one_pos (gcoef_den i)) j) (fmul_congr_right (fun l => hd2 l) j) ?_
  refine Qeq_trans (Qmul_den_pos Nat.one_pos (fmul_den_pos (fun i => oneMinusSq_den i)
      (fun i => gcoef_den i) j)) (fmul_smul_right oneMinusSq gcoef ⟨2, 1⟩ Nat.one_pos
      (fun i => oneMinusSq_den i) (fun i => gcoef_den i) j) ?_
  refine Qeq_trans (Qmul_den_pos Nat.one_pos (fone_den_pos j))
    (Qmul_congr (Qeq_refl _) (artanh_ode j)) ?_
  exact Qeq_symm (twoFone_2fone j)

/-- The `artanh∘kdbl` side of the ODE: `(1−t²)·(artanh∘kdbl)' = 2` (chain rule + `kdbl_sq_id` +
    `comp_recip`). -/
theorem fcomp_acoef_ode (j : Nat) :
    Qeq (fmul oneMinusSq (fderiv (fcomp acoef kdbl)) j) (twoFone j) := by
  have hgk : ∀ i, 0 < (fcomp gcoef kdbl i).den :=
    fun i => fcomp_den_pos (fun m => gcoef_den m) (fun m => kdbl_den m) i
  have hkd : ∀ i, 0 < (fderiv kdbl i).den := fun i => fderiv_den_pos (fun m => kdbl_den m) i
  have h1k : ∀ i, 0 < (Qsub (fone i) (fmul kdbl kdbl i)).den :=
    fun i => Qsub_den_pos (fone_den_pos i) (fmul_den_pos (fun m => kdbl_den m) (fun m => kdbl_den m) i)
  have hsq : ∀ i, 0 < (mul ⟨(2 : Int), 1⟩ (Qsub (fone i) (fmul kdbl kdbl i))).den :=
    fun i => Qmul_den_pos Nat.one_pos (h1k i)
  have hchain : ∀ l, Qeq (fderiv (fcomp acoef kdbl) l) (fmul (fcomp gcoef kdbl) (fderiv kdbl) l) :=
    fun l => Qeq_trans (fmul_den_pos (fun i => fcomp_den_pos
        (fun m => fderiv_den_pos (fun p => acoef_den p) m) (fun m => kdbl_den m) i) hkd l)
      (fcomp_chain acoef kdbl (fun m => acoef_den m) (fun m => kdbl_den m) kdbl_zero l)
      (fmul_congr_left (fun i => fcomp_congr_left (fun m => fderiv_acoef m) i) l)
  refine Qeq_trans (fmul_den_pos (fun i => oneMinusSq_den i) (fun i => fmul_den_pos hgk hkd i) j)
    (fmul_congr_right (fun l => hchain l) j) ?_
  refine Qeq_trans (fmul_den_pos hgk (fun i => fmul_den_pos (fun m => oneMinusSq_den m) hkd i) j)
    (fmul_swap_left oneMinusSq (fcomp gcoef kdbl) (fderiv kdbl) (fun m => oneMinusSq_den m) hgk hkd j) ?_
  refine Qeq_trans (fmul_den_pos hgk hsq j) (fmul_congr_right (fun l => kdbl_sq_id l) j) ?_
  refine Qeq_trans (Qmul_den_pos Nat.one_pos (fmul_den_pos hgk h1k j))
    (fmul_smul_right (fcomp gcoef kdbl) (fun i => Qsub (fone i) (fmul kdbl kdbl i)) ⟨2, 1⟩
      Nat.one_pos hgk h1k j) ?_
  refine Qeq_trans (Qmul_den_pos Nat.one_pos (fone_den_pos j)) (Qmul_congr (Qeq_refl _)
    (Qeq_trans (fmul_den_pos h1k hgk j) (fmul_comm (fcomp gcoef kdbl)
      (fun i => Qsub (fone i) (fmul kdbl kdbl i)) hgk h1k j) (comp_recip j))) ?_
  exact Qeq_symm (twoFone_2fone j)

/-- **THE FORMAL DOUBLING** `artanh∘kdbl = 2·artanh` (as coefficient sequences). Both sides solve the
    formal ODE `(1−t²)y'=2` with `y(0)=0`, so they are equal by `fderiv_inj` + the `(1−t²)` cancellation. -/
theorem formal_doubling (k : Nat) :
    Qeq (fcomp acoef kdbl k) (mul ⟨2, 1⟩ (acoef k)) := by
  refine fderiv_inj (y := fcomp acoef kdbl) (z := fun i => mul ⟨2, 1⟩ (acoef i)) (fun m => ?_) ?_ k
  · exact fmul_oneMinusSq_cancel (X := fderiv (fcomp acoef kdbl))
      (Y := fderiv (fun i => mul ⟨2, 1⟩ (acoef i)))
      (fun i => fderiv_den_pos (fun p => fcomp_den_pos
        (fun q => acoef_den q) (fun q => kdbl_den q) p) i)
      (fun i => fderiv_den_pos (fun p => Qmul_den_pos Nat.one_pos (acoef_den p)) i)
      (fun j => Qeq_trans (twoFone_den j) (fcomp_acoef_ode j) (Qeq_symm (twoacoef_ode j))) m
  · refine Qeq_trans (Qmul_den_pos (acoef_den 0) (fpow_den_pos (fun m => kdbl_den m) 0 0))
      (fcomp_const acoef kdbl) ?_
    show Qeq (acoef 0) (mul ⟨2, 1⟩ (acoef 0))
    have h00 : acoef 0 = ⟨0, 1⟩ := by decide
    rw [h00]; decide

/-- The `2·artanh` derivative coefficients equal `2/(1−w²)`: `fderiv (2·acoef) ≈ dexpderiv`. -/
theorem fderiv_twoacoef (l : Nat) :
    Qeq (fderiv (fun i => mul ⟨2, 1⟩ (acoef i)) l) (dexpderiv l) := by
  have h1 : Qeq (fderiv (fun i => mul ⟨2, 1⟩ (acoef i)) l) (mul ⟨2, 1⟩ (gcoef l)) := by
    show Qeq (mul ⟨(l + 1 : Int), 1⟩ (mul ⟨2, 1⟩ (acoef (l + 1)))) (mul ⟨2, 1⟩ (gcoef l))
    refine Qeq_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (acoef_den (l + 1)))) ?_
      (Qmul_congr (Qeq_refl _) (fderiv_acoef l))
    show Qeq (mul ⟨(l + 1 : Int), 1⟩ (mul ⟨2, 1⟩ (acoef (l + 1))))
      (mul ⟨2, 1⟩ (mul ⟨(l + 1 : Int), 1⟩ (acoef (l + 1))))
    simp only [Qeq, mul]; push_cast; ring_uor
  refine Qeq_trans (Qmul_den_pos Nat.one_pos (gcoef_den l)) h1 ?_
  rcases (by omega : l % 2 = 0 ∨ l % 2 = 1) with h | h
  · have hg : gcoef l = ⟨1, 1⟩ := by unfold gcoef; rw [if_pos h]
    rw [hg]; unfold dexpderiv; rw [h]; decide
  · have hg : gcoef l = ⟨0, 1⟩ := by unfold gcoef; rw [if_neg (by omega)]
    rw [hg]; unfold dexpderiv; rw [h]; decide

/-- **★ THE FORMAL EXP IDENTITY** `exp∘(2·artanh) = (1+w)/(1−w)` (as coefficient sequences):
    `fcomp ecoef (2·acoef) ≈ dgeom`. Both solve the MULTIPLICATIVE ODE `y' = (2/(1−w²))·y` with `y(0)=1`
    (`fcomp` side: `fcomp_chain` + `exp'=exp` (`fderiv_ecoef`) + `fderiv(2·acoef)=dexpderiv`; `dgeom` side:
    `dgeom_ode`), so they are equal by `fderiv_mul_inj`. The formal backbone of `exp(2·artanh t) = (1+t)/(1−t)`. -/
theorem formal_exp_geom (k : Nat) :
    Qeq (fcomp ecoef (fun i => mul ⟨2, 1⟩ (acoef i)) k) (dgeom k) := by
  have htad : ∀ i, 0 < ((fun i => mul ⟨2, 1⟩ (acoef i)) i).den :=
    fun i => Qmul_den_pos Nat.one_pos (acoef_den i)
  have htz : Qeq ((fun i => mul ⟨2, 1⟩ (acoef i)) 0) ⟨0, 1⟩ := by
    show Qeq (mul ⟨2, 1⟩ (acoef 0)) ⟨0, 1⟩
    have h00 : acoef 0 = ⟨0, 1⟩ := by decide
    rw [h00]; decide
  have hfd : ∀ i, 0 < (fcomp ecoef (fun i => mul ⟨2, 1⟩ (acoef i)) i).den :=
    fun i => fcomp_den_pos (fun m => ecoef_den m) htad i
  refine fderiv_mul_inj (d := dexpderiv) (y := fcomp ecoef (fun i => mul ⟨2, 1⟩ (acoef i)))
    (z := dgeom) hfd (fun i => dgeom_den i) (fun i => dexpderiv_den i) (fun l => ?_)
    (fun l => dgeom_ode l) ?_ k
  · refine Qeq_trans (fmul_den_pos (fun i => fcomp_den_pos
        (fun m => fderiv_den_pos (fun p => ecoef_den p) m) htad i) (fun i => fderiv_den_pos htad i) l)
      (fcomp_chain ecoef (fun i => mul ⟨2, 1⟩ (acoef i)) (fun m => ecoef_den m) htad htz l) ?_
    refine Qeq_trans (fmul_den_pos hfd (fun i => fderiv_den_pos htad i) l)
      (fmul_congr_left (fun i => fcomp_congr_left (fun m => fderiv_ecoef m) i) l) ?_
    refine Qeq_trans (fmul_den_pos hfd (fun i => dexpderiv_den i) l)
      (fmul_congr_right (fun i => fderiv_twoacoef i) l) ?_
    exact fmul_comm (fcomp ecoef (fun i => mul ⟨2, 1⟩ (acoef i))) dexpderiv hfd
      (fun i => dexpderiv_den i) l
  · refine Qeq_trans (Qmul_den_pos (ecoef_den 0) (fpow_den_pos htad 0 0)) (fcomp_const ecoef _) ?_
    show Qeq (ecoef 0) (dgeom 0)
    decide

/-- **exp partial sum = `peval` of `ecoef`**: `expSum q N ≈ peval ecoef q N`. Connects the analytic `exp`
    series (`Σ qᵏ/k!`) to the formal-`peval` machinery, so `formal_exp_geom` can drive the eval bridge. -/
theorem expSum_eq_peval_ecoef (q : Q) (hqd : 0 < q.den) :
    ∀ N, Qeq (expSum q N) (peval ecoef q N)
  | 0 => by show Qeq ⟨1, 1⟩ (mul (ecoef 0) (⟨1, 1⟩ : Q)); decide
  | (N + 1) => by
      have hterm : Qeq (expTerm q (N + 1)) (mul (ecoef (N + 1)) (qpow q (N + 1))) :=
        Qmul_comm (qpow q (N + 1)) ⟨1, fct (N + 1)⟩
      show Qeq (add (expSum q N) (expTerm q (N + 1)))
        (add (peval ecoef q N) (mul (ecoef (N + 1)) (qpow q (N + 1))))
      exact Qadd_congr (expSum_eq_peval_ecoef q hqd N) hterm

/-- **The `2·artanh` outer-eval = `2·artSum`**: `peval (2·acoef) t (2N+1) ≈ 2·artSum t N`. The inner series
    of the `exp∘(2·artanh)` composition, as a doubled artanh partial sum. (`peval_smul` + `peval_acoef_artSum`.) -/
theorem peval_twoacoef_artSum (t : Q) (htd : 0 < t.den) (N : Nat) :
    Qeq (peval (fun i => mul ⟨2, 1⟩ (acoef i)) t (2 * N + 1)) (mul ⟨2, 1⟩ (artSum t N)) :=
  Qeq_trans (Qmul_den_pos Nat.one_pos (peval_den_pos (fun k => acoef_den k) htd (2 * N + 1)))
    (peval_smul ⟨2, 1⟩ Nat.one_pos acoef (fun k => acoef_den k) t htd (2 * N + 1))
    (Qmul_congr (Qeq_refl _) (peval_acoef_artSum t htd N))

/-- From `x = p + c` recover `p = x − c`. -/
theorem Qeq_sub_of_eq_add {x p c : Q} (hp : 0 < p.den) (hc : 0 < c.den) (h : Qeq x (add p c)) :
    Qeq p (Qsub x c) :=
  Qeq_symm (Qeq_trans (Qsub_den_pos (add_den_pos hc hp) hc)
    (Qsub_congr (Qeq_trans (add_den_pos hp hc) h (Qadd_comm p c)) (Qeq_refl c))
    (Qsub_add_cancel c p))

/-- **Power recursion** (the telescoping backbone): `eval(bᵐ⁺¹,w,M) = eval(b,w,M)·eval(bᵐ,w,M) − corner`,
    the corner being the high-antidiagonal (`i+j>M`) part of the product (from `peval_mul`). -/
theorem peval_fpow_succ (b : Nat → Q) (hb : ∀ i, 0 < (b i).den) (w : Q) (hwd : 0 < w.den) (m M : Nat) :
    Qeq (peval (fpow b (m + 1)) w M)
      (Qsub (mul (peval b w M) (peval (fpow b m) w M))
        (Fsum (fun i => Qsub
          (Fsum (fun j => mul (mul (b i) (qpow w i)) (mul (fpow b m j) (qpow w j))) M)
          (Fsum (fun j => mul (mul (b i) (qpow w i)) (mul (fpow b m j) (qpow w j))) (M - i))) M)) :=
  Qeq_sub_of_eq_add (peval_den_pos (fpow_den_pos hb (m + 1)) hwd M)
    (Fsum_den_pos (fun i => Qsub_den_pos
      (Fsum_den_pos (fun j => Qmul_den_pos (Qmul_den_pos (hb i) (qpow_den_pos hwd i))
        (Qmul_den_pos (fpow_den_pos hb m j) (qpow_den_pos hwd j))) M)
      (Fsum_den_pos (fun j => Qmul_den_pos (Qmul_den_pos (hb i) (qpow_den_pos hwd i))
        (Qmul_den_pos (fpow_den_pos hb m j) (qpow_den_pos hwd j))) (M - i))) M)
    (peval_mul b (fpow b m) hb (fpow_den_pos hb m) hwd M)

/-- `0 ≤ a.num`, `0 ≤ b.num` ⇒ `0 ≤ (a·b).num`. -/
theorem Qmul_num_nonneg {a b : Q} (ha : 0 ≤ a.num) (hb : 0 ≤ b.num) : 0 ≤ (mul a b).num :=
  Int.mul_nonneg ha hb

/-- Powers of a nonnegative-coefficient series have nonnegative coefficients. -/
theorem fpow_num_nonneg {c : Nat → Q} (hc0 : ∀ k, 0 ≤ (c k).num) :
    ∀ m k, 0 ≤ (fpow c m k).num
  | 0, k => by
      show 0 ≤ (fone k).num
      by_cases h : k = 0
      · rw [show fone k = ⟨1, 1⟩ from by simp [fone, h]]; decide
      · rw [show fone k = ⟨0, 1⟩ from by simp [fone, h]]; decide
  | (m + 1), k =>
      Fsum_num_nonneg (fun i => Qmul_num_nonneg (hc0 i) (fpow_num_nonneg hc0 m (k - i))) k

/-- Evaluation of a nonnegative-coefficient series at a nonnegative point is nonnegative. -/
theorem peval_num_nonneg {c : Nat → Q} (hc0 : ∀ k, 0 ≤ (c k).num) (ρ : Q) (hρ0 : 0 ≤ ρ.num) (M : Nat) :
    0 ≤ (peval c ρ M).num :=
  Fsum_num_nonneg (fun k => Qmul_num_nonneg (hc0 k) (qpow_nonneg hρ0 k)) M

/-- **Truncated power ≤ power of truncation** (nonnegative coefficients, nonnegative point): the corner
    is nonnegative, so dropping it only decreases the value: `eval(cᵐ,ρ,M) ≤ (eval c ρ M)ᵐ`. -/
theorem peval_fpow_le_pow (c : Nat → Q) (hc : ∀ k, 0 < (c k).den) (hc0 : ∀ k, 0 ≤ (c k).num)
    (ρ : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (M : Nat) :
    ∀ m, Qle (peval (fpow c m) ρ M) (qpow (peval c ρ M) m)
  | 0 => Qeq_le (peval_fone ρ hρd M)
  | (m + 1) => by
      have hgd : ∀ i j, 0 < (mul (mul (c i) (qpow ρ i)) (mul (fpow c m j) (qpow ρ j))).den :=
        fun i j => Qmul_den_pos (Qmul_den_pos (hc i) (qpow_den_pos hρd i))
          (Qmul_den_pos (fpow_den_pos hc m j) (qpow_den_pos hρd j))
      have hgn : ∀ i j, 0 ≤ (mul (mul (c i) (qpow ρ i)) (mul (fpow c m j) (qpow ρ j))).num :=
        fun i j => Qmul_num_nonneg (Qmul_num_nonneg (hc0 i) (qpow_nonneg hρ0 i))
          (Qmul_num_nonneg (fpow_num_nonneg hc0 m j) (qpow_nonneg hρ0 j))
      have hcorner_nonneg : 0 ≤ (Fsum (fun i => Qsub
          (Fsum (fun j => mul (mul (c i) (qpow ρ i)) (mul (fpow c m j) (qpow ρ j))) M)
          (Fsum (fun j => mul (mul (c i) (qpow ρ i)) (mul (fpow c m j) (qpow ρ j))) (M - i))) M).num :=
        Fsum_num_nonneg (fun i => Qsub_num_nonneg
          (Fsum_mono_len (fun j => hgn i j) (fun j => hgd i j) (Nat.sub_le M i))) M
      refine Qle_trans (Qsub_den_pos (Qmul_den_pos (peval_den_pos hc hρd M)
          (peval_den_pos (fpow_den_pos hc m) hρd M))
          (Fsum_den_pos (fun i => Qsub_den_pos (Fsum_den_pos (fun j => hgd i j) M)
            (Fsum_den_pos (fun j => hgd i j) (M - i))) M))
        (Qeq_le (peval_fpow_succ c hc ρ hρd m M)) ?_
      refine Qle_trans (Qmul_den_pos (peval_den_pos hc hρd M) (peval_den_pos (fpow_den_pos hc m) hρd M))
        (Qsub_le_self hcorner_nonneg) ?_
      exact Qmul_le_mul_left (peval_num_nonneg hc0 ρ hρ0 M) (peval_fpow_le_pow c hc hc0 ρ hρd hρ0 M m)

/-- **Geometric domination of the powers**: `|eval(bᵐ, w, M)| ≤ (eval |b| ρ M)ᵐ` for `|w| ≤ ρ`, `ρ ≥ 0`.
    Chains per-coefficient abs (`peval_abs_le_peval_fabs`), coefficient domination (`fpow_abs_dom`,
    `peval_mono`), and the truncated-power bound (`peval_fpow_le_pow`). -/
theorem peval_fpow_abs_bound (b : Nat → Q) (hb : ∀ i, 0 < (b i).den) (w : Q) (hwd : 0 < w.den)
    {ρ : Q} (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hw : Qle (Qabs w) ρ) (m M : Nat) :
    Qle (Qabs (peval (fpow b m) w M)) (qpow (peval (fabs b) ρ M) m) := by
  refine Qle_trans (peval_den_pos (fun k => fabs_den_pos (fpow_den_pos hb m) k) hρd M)
    (peval_abs_le_peval_fabs (fpow b m) (fpow_den_pos hb m) w hwd hρd hw M) ?_
  refine Qle_trans (peval_den_pos (fpow_den_pos (fun i => fabs_den_pos hb i) m) hρd M)
    (peval_mono (fun k => fpow_abs_dom b hb m k) ρ hρ0 M) ?_
  exact peval_fpow_le_pow (fabs b) (fun i => fabs_den_pos hb i) (fabs_nonneg b) ρ hρd hρ0 M m

/-- `0·x = 0`. -/
theorem mul_left_zero (x : Q) : Qeq (mul ⟨0, 1⟩ x) ⟨0, 1⟩ := by simp [Qeq, mul]

/-- `x·0 = 0`. -/
theorem mul_right_zero (x : Q) : Qeq (mul x ⟨0, 1⟩) ⟨0, 1⟩ := by simp [Qeq, mul]

/-- **Eval bridge, the structural identity**: since `b(0)=0`, the formal composition evaluates as
    `eval(a∘b, w, M) = Σ_{m≤M} a(m)·eval(bᵐ, w, M)` — the inner sum extends to `M` because `(bᵐ)_k`
    vanishes for `k<m`, then the triangular double sum is swapped. -/
theorem peval_fcomp_swap (a b : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den)
    (hb0 : Qeq (b 0) ⟨0, 1⟩) (w : Q) (hwd : 0 < w.den) (M : Nat) :
    Qeq (peval (fcomp a b) w M) (Fsum (fun m => mul (a m) (peval (fpow b m) w M)) M) := by
  have hg : ∀ m k, 0 < (mul (mul (a m) (fpow b m k)) (qpow w k)).den :=
    fun m k => Qmul_den_pos (Qmul_den_pos (ha m) (fpow_den_pos hb m k)) (qpow_den_pos hwd k)
  -- each outer term, rewritten as a length-`M` inner sum over `m`
  have hrow : ∀ k, k ≤ M → Qeq (mul (fcomp a b k) (qpow w k))
      (Fsum (fun m => mul (mul (a m) (fpow b m k)) (qpow w k)) M) := by
    intro k hk
    refine Qeq_trans (Fsum_den_pos (fun m => hg m k) k)
      (Fsum_mul_const_right (qpow_den_pos hwd k)
        (fun m => Qmul_den_pos (ha m) (fpow_den_pos hb m k)) k) ?_
    refine Fsum_extend_zero (fun m => hg m k) hk (fun m hm1 _ => ?_)
    have hv : Qeq (fpow b m k) ⟨0, 1⟩ := fpow_vanish hb hb0 m k (by omega)
    exact Qeq_trans (Qmul_den_pos (Qmul_den_pos (ha m) Nat.one_pos) (qpow_den_pos hwd k))
      (Qmul_congr (Qmul_congr (Qeq_refl _) hv) (Qeq_refl _))
      (Qeq_trans (Qmul_den_pos Nat.one_pos (qpow_den_pos hwd k))
        (Qmul_congr (mul_right_zero (a m)) (Qeq_refl _)) (mul_left_zero (qpow w k)))
  -- assemble: congr → swap → pull a(m) out
  refine Qeq_trans (Fsum_den_pos (fun k => Fsum_den_pos (fun m => hg m k) M) M)
    (Fsum_congr_le (k := M) (fun k hk => hrow k hk)) ?_
  refine Qeq_trans (Fsum_den_pos (fun m => Fsum_den_pos (fun k => hg m k) M) M)
    (Fsum_swap (fun k m => hg m k) M M) ?_
  refine Fsum_congr (fun m => ?_) M
  exact Qeq_trans (Fsum_den_pos (fun k => Qmul_den_pos (ha m)
      (Qmul_den_pos (fpow_den_pos hb m k) (qpow_den_pos hwd k))) M)
    (Fsum_congr (fun k => Qmul_assoc (a m) (fpow b m k) (qpow w k)) M)
    (Fsum_mul_left (ha m) (fun k => Qmul_den_pos (fpow_den_pos hb m k) (qpow_den_pos hwd k)) M)

/-- Every `|kdbl|` coefficient is `≤ 2`. -/
theorem fabs_kdbl_le2 (i : Nat) : Qle (fabs kdbl i) ⟨2, 1⟩ := by
  show Qle (Qabs (kdbl i)) ⟨2, 1⟩
  by_cases h1 : i % 4 = 1
  · rw [show kdbl i = ⟨2, 1⟩ from by unfold kdbl; rw [if_pos h1]]; decide
  · by_cases h3 : i % 4 = 3
    · rw [show kdbl i = ⟨-2, 1⟩ from by unfold kdbl; rw [if_neg h1, if_pos h3]]; decide
    · rw [show kdbl i = ⟨0, 1⟩ from by unfold kdbl; rw [if_neg h1, if_neg h3]]; decide

/-- The integer geometric sum `Σ_{j≤k} 2ʲ = 2^{k+1} − 1`. -/
theorem pow2_sum : ∀ k, Qeq (Fsum (fun j => (⟨(2 : Int) ^ j, 1⟩ : Q)) k) ⟨(2 : Int) ^ (k + 1) - 1, 1⟩
  | 0 => by decide
  | (k + 1) => by
      show Qeq (add (Fsum (fun j => (⟨(2 : Int) ^ j, 1⟩ : Q)) k) ⟨(2 : Int) ^ (k + 1), 1⟩)
        ⟨(2 : Int) ^ (k + 1 + 1) - 1, 1⟩
      refine Qeq_trans (add_den_pos Nat.one_pos Nat.one_pos) (Qadd_congr (pow2_sum k) (Qeq_refl _)) ?_
      show Qeq (add (⟨(2 : Int) ^ (k + 1) - 1, 1⟩ : Q) ⟨(2 : Int) ^ (k + 1), 1⟩)
        ⟨(2 : Int) ^ (k + 1 + 1) - 1, 1⟩
      simp only [Qeq, add]
      rw [show (2 : Int) ^ (k + 1 + 1) = 2 ^ (k + 1) * 2 from by rw [Int.pow_succ]]
      push_cast; ring_uor

/-- `qpow` distributes over products: `(a·b)ᵏ = aᵏ·bᵏ`. -/
theorem qpow_mul (a b : Q) (ha : 0 < a.den) (hb : 0 < b.den) (k : Nat) :
    Qeq (qpow (mul a b) k) (mul (qpow a k) (qpow b k)) := by
  induction k with
  | zero => simp [qpow, Qeq, mul]
  | succ k ih =>
      show Qeq (mul (mul a b) (qpow (mul a b) k)) (mul (mul a (qpow a k)) (mul b (qpow b k)))
      refine Qeq_trans (Qmul_den_pos (Qmul_den_pos ha hb)
          (Qmul_den_pos (qpow_den_pos ha k) (qpow_den_pos hb k)))
        (Qmul_congr (Qeq_refl _) ih) ?_
      simp only [Qeq, mul]; push_cast; ring_uor

/-- `qpow ⟨2,1⟩ k = 2ᵏ`. -/
theorem qpow_two_nat (k : Nat) : Qeq (qpow (⟨2, 1⟩ : Q) k) ⟨(2 : Int) ^ k, 1⟩ := by
  induction k with
  | zero => decide
  | succ k ih =>
      show Qeq (mul (⟨2, 1⟩ : Q) (qpow ⟨2, 1⟩ k)) ⟨(2 : Int) ^ (k + 1), 1⟩
      refine Qeq_trans (Qmul_den_pos Nat.one_pos Nat.one_pos)
        (Qmul_congr (Qeq_refl _) ih) ?_
      show Qeq (mul (⟨2, 1⟩ : Q) ⟨(2 : Int) ^ k, 1⟩) ⟨(2 : Int) ^ (k + 1), 1⟩
      simp only [Qeq, mul]; rw [Int.pow_succ]; push_cast; ring_uor

/-- **Coefficient bound on the majorant powers**: `(|kdbl|ᵐ)_k ≤ 4ᵐ·2ᵏ` (induction on `m`, using
    `|kdbl|≤2`, `pow2_sum`, and the geometric inflation `Σ_{i≤k} 2^{k-i} ≤ 2^{k+1}`). -/
theorem fpow_fabs_kdbl_bound (m k : Nat) : Qle (fpow (fabs kdbl) m k) ⟨(4 : Int) ^ m * 2 ^ k, 1⟩ := by
  induction m generalizing k with
  | zero =>
      show Qle (fone k) ⟨(4 : Int) ^ 0 * 2 ^ k, 1⟩
      by_cases h : k = 0
      · subst h; rw [show fone 0 = (⟨1, 1⟩ : Q) from by simp [fone]]; decide
      · rw [show fone k = (⟨0, 1⟩ : Q) from by simp [fone, h]]
        show (0 : Int) * 1 ≤ ((4 : Int) ^ 0 * 2 ^ k) * 1
        have h2 : (0 : Int) ≤ (4 : Int) ^ 0 * 2 ^ k := by exact_mod_cast Nat.zero_le (4 ^ 0 * 2 ^ k)
        omega
  | succ m ih =>
      have hterm : ∀ i, Qle (mul (fabs kdbl i) (fpow (fabs kdbl) m (k - i)))
          (mul (⟨2 * (4 : Int) ^ m, 1⟩ : Q) ⟨2 ^ (k - i), 1⟩) := by
        intro i
        refine Qle_trans (Qmul_den_pos Nat.one_pos Nat.one_pos)
          (Qmul_le_mul (fabs_den_pos (fun j => kdbl_den j) i) Nat.one_pos
            (fpow_den_pos (fun j => fabs_den_pos (fun l => kdbl_den l) j) m (k - i))
            (fabs_nonneg kdbl i) (fpow_num_nonneg (fun j => fabs_nonneg kdbl j) m (k - i))
            (fabs_kdbl_le2 i) (ih (k - i)))
          (Qeq_le (by simp only [Qeq, mul]; push_cast; ring_uor))
      show Qle (Fsum (fun i => mul (fabs kdbl i) (fpow (fabs kdbl) m (k - i))) k)
        ⟨(4 : Int) ^ (m + 1) * 2 ^ k, 1⟩
      refine Qle_trans (Fsum_den_pos (fun i => Qmul_den_pos Nat.one_pos Nat.one_pos) k)
        (Fsum_le_Fsum hterm k) ?_
      refine Qle_trans (Qmul_den_pos Nat.one_pos (Fsum_den_pos (fun _ => Nat.one_pos) k))
        (Qeq_le (Fsum_mul_left Nat.one_pos (fun _ => Nat.one_pos) k)) ?_
      refine Qle_trans (Qmul_den_pos Nat.one_pos Nat.one_pos)
        (Qeq_le (Qmul_congr (Qeq_refl _) (Qeq_trans (Fsum_den_pos (fun _ => Nat.one_pos) k)
          (Qeq_symm (Fsum_reverse (f := fun j => (⟨(2 : Int) ^ j, 1⟩ : Q)) (fun _ => Nat.one_pos) k))
          (pow2_sum k)))) ?_
      show ((2 * (4 : Int) ^ m) * (2 ^ (k + 1) - 1)) * 1 ≤ ((4 : Int) ^ (m + 1) * 2 ^ k) * 1
      rw [show (4 : Int) ^ (m + 1) = 4 ^ m * 4 from by rw [Int.pow_succ],
          show (2 : Int) ^ (k + 1) = 2 ^ k * 2 from by rw [Int.pow_succ]]
      have hgen : ∀ A B : Int, 0 ≤ A → ((2 * A) * (B * 2 - 1)) * 1 ≤ (A * 4 * B) * 1 := by
        intro A B hA
        have key : (A * 4 * B) * 1 - ((2 * A) * (B * 2 - 1)) * 1 = 2 * A := by ring_uor
        omega
      exact hgen ((4 : Int) ^ m) ((2 : Int) ^ k) (by exact_mod_cast Nat.zero_le (4 ^ m))

/-- **Per-term geometric domination**: the `k`-th `|kdbl|ᵐ` evaluation term is `≤ 4ᵐ·(2ρ)ᵏ`. -/
theorem fpow_kdbl_term_bound (ρ : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (m k : Nat) :
    Qle (mul (fpow (fabs kdbl) m k) (qpow ρ k)) (mul (⟨(4 : Int) ^ m, 1⟩ : Q) (qpow (mul ⟨2, 1⟩ ρ) k)) := by
  refine Qle_trans (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd k))
    (Qmul_le_mul_right (qpow_nonneg hρ0 k) (fpow_fabs_kdbl_bound m k)) ?_
  refine Qeq_le (Qeq_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd k)))
    (Qeq_trans (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd k))
      (by simp only [Qeq, mul] : Qeq (mul (⟨(4:Int)^m * 2^k, 1⟩ : Q) (qpow ρ k))
        (mul (mul (⟨(4:Int)^m,1⟩ : Q) ⟨(2:Int)^k,1⟩) (qpow ρ k)))
      (Qmul_assoc ⟨(4:Int)^m,1⟩ ⟨(2:Int)^k,1⟩ (qpow ρ k)))
    (Qmul_congr (Qeq_refl _) (Qeq_trans (Qmul_den_pos (qpow_den_pos (by decide) k) (qpow_den_pos hρd k))
      (Qmul_congr (Qeq_symm (qpow_two_nat k)) (Qeq_refl _)) (Qeq_symm (qpow_mul ⟨2, 1⟩ ρ (by decide) hρd k)))))

/-- `Σ_{k≤N} rᵏ = gPow r N`. -/
theorem gPow_eq_Fsum (r : Q) : ∀ N, Qeq (Fsum (fun k => qpow r k) N) (gPow r N)
  | 0 => Qeq_refl _
  | (N + 1) => Qadd_congr (gPow_eq_Fsum r N) (Qeq_refl _)

/-- `(1−A) − (1−B) = B − A`. -/
theorem Qsub_sub_one (A B : Q) :
    Qeq (Qsub (Qsub ⟨1, 1⟩ A) (Qsub ⟨1, 1⟩ B)) (Qsub B A) := by
  simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor

/-- **Geometric gap bound**: `(gPow r M' − gPow r M)·(1−r) ≤ r^{M+1}` for `M ≤ M'`, `0 ≤ r`. -/
theorem gPow_gap_le (r : Q) (hr0 : 0 ≤ r.num) (hrd : 0 < r.den) {M M' : Nat} (hMM : M ≤ M') :
    Qle (mul (Qsub (gPow r M') (gPow r M)) (Qsub ⟨1, 1⟩ r)) (qpow r (M + 1)) := by
  have hw : 0 < (Qsub (⟨1, 1⟩ : Q) r).den := Qsub_den_pos Nat.one_pos hrd
  have e1 : Qeq (mul (Qsub (gPow r M') (gPow r M)) (Qsub ⟨1, 1⟩ r))
      (Qsub (Qsub ⟨1, 1⟩ (qpow r (M' + 1))) (Qsub ⟨1, 1⟩ (qpow r (M + 1)))) :=
    Qeq_trans (Qsub_den_pos (Qmul_den_pos (gPow_den_pos hrd M') hw) (Qmul_den_pos (gPow_den_pos hrd M) hw))
      (Qmul_sub_right (gPow r M') (gPow r M) (Qsub ⟨1, 1⟩ r))
      (Qsub_congr (gPow_telescope hrd M') (gPow_telescope hrd M))
  have eXY : Qeq (mul (Qsub (gPow r M') (gPow r M)) (Qsub ⟨1, 1⟩ r))
      (Qsub (qpow r (M + 1)) (qpow r (M' + 1))) :=
    Qeq_trans (Qsub_den_pos (Qsub_den_pos Nat.one_pos (qpow_den_pos hrd _))
        (Qsub_den_pos Nat.one_pos (qpow_den_pos hrd _)))
      e1 (Qsub_sub_one (qpow r (M' + 1)) (qpow r (M + 1)))
  exact Qle_congr_left (Qsub_den_pos (qpow_den_pos hrd _) (qpow_den_pos hrd _)) (Qeq_symm eXY)
    (Qsub_le_self (qpow_nonneg hr0 (M' + 1)))

/-- **The Cauchy gap for `kdblᵐ` evaluation**: for `|w| ≤ ρ`, `M ≤ M'`, the partial-sum gap of
    `peval(kdblᵐ, w, ·)` is dominated by the geometric gap `Σ 4ᵐ(2ρ)ᵏ`. -/
theorem peval_kdbl_pow_gap (ρ w : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hwd : 0 < w.den)
    (hw : Qle (Qabs w) ρ) (m : Nat) {M M' : Nat} (hMM : M ≤ M') :
    Qle (Qabs (Qsub (peval (fpow kdbl m) w M') (peval (fpow kdbl m) w M)))
      (Qsub (Fsum (fun k => mul (⟨(4 : Int) ^ m, 1⟩ : Q) (qpow (mul ⟨2, 1⟩ ρ) k)) M')
            (Fsum (fun k => mul (⟨(4 : Int) ^ m, 1⟩ : Q) (qpow (mul ⟨2, 1⟩ ρ) k)) M)) :=
  Fsum_abs_diff_le
    (fun k => Qmul_den_pos (fpow_den_pos (fun i => kdbl_den i) m k) (qpow_den_pos hwd k))
    (fun k => Qmul_den_pos Nat.one_pos (qpow_den_pos (Qmul_den_pos (by decide) hρd) k))
    (fun k => Qle_trans (Qmul_den_pos (Qabs_den_pos (fpow_den_pos (fun i => kdbl_den i) m k))
        (Qabs_den_pos (qpow_den_pos hwd k)))
      (Qeq_le (by rw [Qabs_mul]; exact Qeq_refl _ : Qeq (Qabs (mul (fpow kdbl m k) (qpow w k)))
        (mul (Qabs (fpow kdbl m k)) (Qabs (qpow w k)))))
      (Qle_trans (Qmul_den_pos (fpow_den_pos (fun i => fabs_den_pos (fun j => kdbl_den j) i) m k)
          (qpow_den_pos hρd k))
        (Qmul_le_mul (Qabs_den_pos (fpow_den_pos (fun i => kdbl_den i) m k))
          (fpow_den_pos (fun i => fabs_den_pos (fun j => kdbl_den j) i) m k)
          (Qabs_den_pos (qpow_den_pos hwd k))
          (Qabs_num_nonneg _) (Qabs_num_nonneg _)
          (fpow_abs_dom kdbl (fun i => kdbl_den i) m k)
          (Qle_trans (qpow_den_pos (Qabs_den_pos hwd) k) (Qeq_le (qpow_abs w k))
            (qpow_base_mono (Qabs_den_pos hwd) hρd (Qabs_num_nonneg w) hw k)))
        (fpow_kdbl_term_bound ρ hρd hρ0 m k)))
    hMM

/-- `c·(a−b) = c·a − c·b` (local; `Qmul_sub_left` lives in Pi, not imported here). -/
theorem Qmul_sub_left_loc (c a b : Q) : Qeq (mul c (Qsub a b)) (Qsub (mul c a) (mul c b)) := by
  simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor

/-- **The Cauchy modulus for `kdblᵐ` evaluation**: `|peval(kdblᵐ,w,M') − peval(kdblᵐ,w,M)|·(1−2ρ)
    ≤ 4ᵐ·(2ρ)^{M+1}` for `|w| ≤ ρ`, `2ρ ≤ 1`, `M ≤ M'`. The explicit modulus (→ 0) that makes
    `peval(kdblᵐ, w, ·)` a regular real sequence. -/
theorem peval_kdbl_pow_cauchy (ρ w : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hwd : 0 < w.den)
    (hw : Qle (Qabs w) ρ) (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (m : Nat) {M M' : Nat} (hMM : M ≤ M') :
    Qle (mul (Qabs (Qsub (peval (fpow kdbl m) w M') (peval (fpow kdbl m) w M)))
          (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ)))
      (mul (⟨(4 : Int) ^ m, 1⟩ : Q) (qpow (mul ⟨2, 1⟩ ρ) (M + 1))) := by
  have hrd : 0 < (mul (⟨2, 1⟩ : Q) ρ).den := Qmul_den_pos (by decide) hρd
  have hr0 : 0 ≤ (mul (⟨2, 1⟩ : Q) ρ).num := Qmul_num_nonneg (by decide) hρ0
  have hgN : ∀ N, 0 < (Fsum (fun k => mul (⟨(4 : Int) ^ m, 1⟩ : Q) (qpow (mul ⟨2, 1⟩ ρ) k)) N).den :=
    fun N => Fsum_den_pos (fun k => Qmul_den_pos Nat.one_pos (qpow_den_pos hrd k)) N
  have hDden : 0 < (Qsub (gPow (mul ⟨2, 1⟩ ρ) M') (gPow (mul ⟨2, 1⟩ ρ) M)).den :=
    Qsub_den_pos (gPow_den_pos hrd M') (gPow_den_pos hrd M)
  have hwd1 : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).den := Qsub_den_pos Nat.one_pos hrd
  -- RHS gap = 4ᵐ · (gPow gap)
  have eRG : ∀ N, Qeq (Fsum (fun k => mul (⟨(4 : Int) ^ m, 1⟩ : Q) (qpow (mul ⟨2, 1⟩ ρ) k)) N)
      (mul (⟨(4 : Int) ^ m, 1⟩ : Q) (gPow (mul ⟨2, 1⟩ ρ) N)) :=
    fun N => Qeq_trans (Qmul_den_pos Nat.one_pos (Fsum_den_pos (fun k => qpow_den_pos hrd k) N))
      (Fsum_mul_left Nat.one_pos (fun k => qpow_den_pos hrd k) N)
      (Qmul_congr (Qeq_refl _) (gPow_eq_Fsum (mul ⟨2, 1⟩ ρ) N))
  have eGap : Qeq (Qsub (Fsum (fun k => mul (⟨(4 : Int) ^ m, 1⟩ : Q) (qpow (mul ⟨2, 1⟩ ρ) k)) M')
        (Fsum (fun k => mul (⟨(4 : Int) ^ m, 1⟩ : Q) (qpow (mul ⟨2, 1⟩ ρ) k)) M))
      (mul (⟨(4 : Int) ^ m, 1⟩ : Q) (Qsub (gPow (mul ⟨2, 1⟩ ρ) M') (gPow (mul ⟨2, 1⟩ ρ) M))) :=
    Qeq_trans (Qsub_den_pos (Qmul_den_pos Nat.one_pos (gPow_den_pos hrd M'))
        (Qmul_den_pos Nat.one_pos (gPow_den_pos hrd M)))
      (Qsub_congr (eRG M') (eRG M))
      (Qeq_symm (Qmul_sub_left_loc ⟨(4 : Int) ^ m, 1⟩ (gPow (mul ⟨2, 1⟩ ρ) M') (gPow (mul ⟨2, 1⟩ ρ) M)))
  -- chain: |gap|·(1−2ρ) ≤ RHSgap·(1−2ρ) = 4ᵐ·(gPowGap·(1−2ρ)) ≤ 4ᵐ·(2ρ)^{M+1}
  refine Qle_trans (Qmul_den_pos (Qsub_den_pos (hgN M') (hgN M)) hwd1)
    (Qmul_le_mul_right h2ρ (peval_kdbl_pow_gap ρ w hρd hρ0 hwd hw m hMM)) ?_
  refine Qle_trans (Qmul_den_pos (Qmul_den_pos Nat.one_pos hDden) hwd1)
    (Qeq_le (Qmul_congr eGap (Qeq_refl _))) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos hDden hwd1))
    (Qeq_le (Qmul_assoc ⟨(4 : Int) ^ m, 1⟩ (Qsub (gPow (mul ⟨2, 1⟩ ρ) M') (gPow (mul ⟨2, 1⟩ ρ) M))
      (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ)))) ?_
  exact Qmul_le_mul_left (by show (0 : Int) ≤ (4 : Int) ^ m; exact_mod_cast Nat.zero_le (4 ^ m))
    (gPow_gap_le (mul ⟨2, 1⟩ ρ) hr0 hrd hMM)

/-- `ρ ≤ 2ρ` for `ρ ≥ 0`. -/
theorem Qle_rho_two_rho (ρ : Q) (hρ0 : 0 ≤ ρ.num) : Qle ρ (mul ⟨2, 1⟩ ρ) := by
  show ρ.num * ((1 * ρ.den : Nat) : Int) ≤ (2 * ρ.num) * (ρ.den : Int)
  rw [show ((1 * ρ.den : Nat) : Int) = (ρ.den : Int) from by push_cast; ring_uor]
  exact Int.mul_le_mul_of_nonneg_right (by omega) (Int.ofNat_nonneg _)

/-- **Geometric convolution inequality**: `ρⁱ·(2ρ)^{M−i+1} ≤ (2ρ)^{M+1}` for `i ≤ M`. -/
theorem qpow_conv_le (ρ : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (i M : Nat) (hiM : i ≤ M) :
    Qle (mul (qpow ρ i) (qpow (mul ⟨2, 1⟩ ρ) (M - i + 1))) (qpow (mul ⟨2, 1⟩ ρ) (M + 1)) := by
  have h2d : 0 < (mul (⟨2, 1⟩ : Q) ρ).den := Qmul_den_pos (by decide) hρd
  have h2n : 0 ≤ (mul (⟨2, 1⟩ : Q) ρ).num := Qmul_num_nonneg (by decide) hρ0
  have hexp : i + (M - i + 1) = M + 1 := by omega
  refine Qle_trans (Qmul_den_pos (qpow_den_pos h2d i) (qpow_den_pos h2d _))
    (Qmul_le_mul_right (qpow_nonneg h2n _)
      (qpow_base_mono hρd h2d hρ0 (Qle_rho_two_rho ρ hρ0) i)) ?_
  refine Qeq_le ?_
  rw [← hexp]
  exact Qeq_symm (qpow_add (mul ⟨2, 1⟩ ρ) h2d i (M - i + 1))

/-- Product rearrange `(a·b)·(c·d) = (a·c)·(b·d)`. -/
theorem mul_rearrange (a b c d : Q) : Qeq (mul (mul a b) (mul c d)) (mul (mul a c) (mul b d)) := by
  simp only [Qeq, mul]; push_cast; ring_uor

/-- `|kdbl_i·wⁱ| ≤ 2·ρⁱ` for `|w| ≤ ρ`. -/
theorem Qabs_C_le (ρ w : Q) (hρd : 0 < ρ.den) (hwd : 0 < w.den) (hw : Qle (Qabs w) ρ) (i : Nat) :
    Qle (Qabs (mul (kdbl i) (qpow w i))) (mul ⟨2, 1⟩ (qpow ρ i)) := by
  refine Qle_trans (Qmul_den_pos (Qabs_den_pos (kdbl_den i)) (Qabs_den_pos (qpow_den_pos hwd i)))
    (Qeq_le (by rw [Qabs_mul]; exact Qeq_refl _ :
      Qeq (Qabs (mul (kdbl i) (qpow w i))) (mul (Qabs (kdbl i)) (Qabs (qpow w i)))))
    (Qmul_le_mul (Qabs_den_pos (kdbl_den i)) (by decide) (Qabs_den_pos (qpow_den_pos hwd i))
      (Qabs_num_nonneg _) (Qabs_num_nonneg _) (fabs_kdbl_le2 i)
      (Qle_trans (qpow_den_pos (Qabs_den_pos hwd) i) (Qeq_le (qpow_abs w i))
        (qpow_base_mono (Qabs_den_pos hwd) hρd (Qabs_num_nonneg w) hw i)))

/-- The `i`-th inner gap of the `peval_fpow_succ` corner factors as `(kdbl_i·wⁱ)·(p_m gap)`. -/
theorem corner_inner_eq (w : Q) (hwd : 0 < w.den) (m M i : Nat) :
    Qeq (Qsub (Fsum (fun j => mul (mul (kdbl i) (qpow w i)) (mul (fpow kdbl m j) (qpow w j))) M)
              (Fsum (fun j => mul (mul (kdbl i) (qpow w i)) (mul (fpow kdbl m j) (qpow w j))) (M - i)))
      (mul (mul (kdbl i) (qpow w i))
        (Qsub (peval (fpow kdbl m) w M) (peval (fpow kdbl m) w (M - i)))) := by
  have hC : 0 < (mul (kdbl i) (qpow w i)).den := Qmul_den_pos (kdbl_den i) (qpow_den_pos hwd i)
  have hterm : ∀ N, Qeq (Fsum (fun j => mul (mul (kdbl i) (qpow w i))
        (mul (fpow kdbl m j) (qpow w j))) N)
      (mul (mul (kdbl i) (qpow w i)) (peval (fpow kdbl m) w N)) :=
    fun N => Fsum_mul_left hC
      (fun j => Qmul_den_pos (fpow_den_pos (fun l => kdbl_den l) m j) (qpow_den_pos hwd j)) N
  exact Qeq_trans (Qsub_den_pos
      (Qmul_den_pos hC (peval_den_pos (fpow_den_pos (fun l => kdbl_den l) m) hwd M))
      (Qmul_den_pos hC (peval_den_pos (fpow_den_pos (fun l => kdbl_den l) m) hwd (M - i))))
    (Qsub_congr (hterm M) (hterm (M - i)))
    (Qeq_symm (Qmul_sub_left_loc (mul (kdbl i) (qpow w i))
      (peval (fpow kdbl m) w M) (peval (fpow kdbl m) w (M - i))))

/-- `|kdbl_a·wᵇ| ≤ 2·ρᵇ` for `|w| ≤ ρ`. -/
theorem Qabs_kdbl_qpow_le (ρ w : Q) (hρd : 0 < ρ.den) (hwd : 0 < w.den) (hw : Qle (Qabs w) ρ)
    (a b : Nat) : Qle (Qabs (mul (kdbl a) (qpow w b))) (mul ⟨2, 1⟩ (qpow ρ b)) :=
  Qle_trans (Qmul_den_pos (Qabs_den_pos (kdbl_den a)) (Qabs_den_pos (qpow_den_pos hwd b)))
    (Qeq_le (by rw [Qabs_mul]; exact Qeq_refl _ :
      Qeq (Qabs (mul (kdbl a) (qpow w b))) (mul (Qabs (kdbl a)) (Qabs (qpow w b)))))
    (Qmul_le_mul (Qabs_den_pos (kdbl_den a)) (by decide) (Qabs_den_pos (qpow_den_pos hwd b))
      (Qabs_num_nonneg _) (Qabs_num_nonneg _) (fabs_kdbl_le2 a)
      (Qle_trans (qpow_den_pos (Qabs_den_pos hwd) b) (Qeq_le (qpow_abs w b))
        (qpow_base_mono (Qabs_den_pos hwd) hρd (Qabs_num_nonneg w) hw b)))


/-- The inner value `u = 2w/(1+w²)` as a rational. -/
def uval (w : Q) : Q := ⟨2 * w.num * (w.den : Int), w.num.natAbs * w.num.natAbs + w.den * w.den⟩

theorem uval_den_pos (w : Q) (hwd : 0 < w.den) : 0 < (uval w).den := by
  show 0 < w.num.natAbs * w.num.natAbs + w.den * w.den
  have : 0 < w.den * w.den := Nat.mul_pos hwd hwd
  omega

/-- The defining relation `(1+w²)·u = 2w`. -/
theorem uval_rel (w : Q) (hwd : 0 < w.den) :
    Qeq (mul (add ⟨1, 1⟩ (mul w w)) (uval w)) (mul ⟨2, 1⟩ w) := by
  simp only [Qeq, mul, add, uval]; push_cast; rw [Int.natAbs_mul_self' w.num]; ring_uor

/-- `wᵏ·w² = w^{k+2}`. -/
theorem qpow_mul_sq (w : Q) (hwd : 0 < w.den) (k : Nat) :
    Qeq (mul (qpow w k) (mul w w)) (qpow w (k + 2)) :=
  Qeq_trans (Qmul_den_pos (qpow_den_pos hwd k) (qpow_den_pos hwd 2))
    (Qmul_congr (Qeq_refl _) (by simp [Qeq, mul, qpow] : Qeq (mul w w) (qpow w 2)))
    (Qeq_symm (qpow_add w hwd k 2))

/-- Period-4 cancellation: `kdbl N + kdbl (N+2) = 0`. -/
theorem kdbl_period (N : Nat) : Qeq (add (kdbl N) (kdbl (N + 2))) ⟨0, 1⟩ := by
  by_cases h1 : N % 4 = 1
  · rw [show kdbl N = ⟨2, 1⟩ from by unfold kdbl; rw [if_pos h1],
        show kdbl (N + 2) = ⟨-2, 1⟩ from by unfold kdbl; rw [if_neg (by omega), if_pos (by omega)]]
    decide
  · by_cases h3 : N % 4 = 3
    · rw [show kdbl N = ⟨-2, 1⟩ from by unfold kdbl; rw [if_neg h1, if_pos h3],
          show kdbl (N + 2) = ⟨2, 1⟩ from by unfold kdbl; rw [if_pos (by omega)]]
      decide
    · rw [show kdbl N = ⟨0, 1⟩ from by unfold kdbl; rw [if_neg h1, if_neg h3],
          show kdbl (N + 2) = ⟨0, 1⟩ from by unfold kdbl; rw [if_neg (by omega), if_neg (by omega)]]
      decide

/-- Sum rearrange `(A+B)+(C+D) = (A+C)+(B+D)`. -/
theorem add_rearrange (A B C D : Q) : Qeq (add (add A B) (add C D)) (add (add A C) (add B D)) := by
  simp only [Qeq, add]; push_cast; ring_uor

/-- **The inner-value telescope**: `(1+w²)·peval(kdbl,w,N+1) = 2w + (kdbl_N·w^{N+2} + kdbl_{N+1}·w^{N+3})`.
    The boundary → 0, so `peval(kdbl,w,·) → 2w/(1+w²)`. -/
theorem kdbl_innerval (w : Q) (hwd : 0 < w.den) : ∀ N,
    Qeq (mul (peval kdbl w (N + 1)) (add ⟨1, 1⟩ (mul w w)))
      (add (mul ⟨2, 1⟩ w)
        (add (mul (kdbl N) (qpow w (N + 2))) (mul (kdbl (N + 1)) (qpow w (N + 3)))))
  | 0 => by
      show Qeq (mul (add (mul (kdbl 0) (qpow w 0)) (mul (kdbl 1) (qpow w 1))) (add ⟨1, 1⟩ (mul w w)))
        (add (mul ⟨2, 1⟩ w) (add (mul (kdbl 0) (qpow w 2)) (mul (kdbl 1) (qpow w 3))))
      rw [show kdbl 0 = (⟨0, 1⟩ : Q) from by decide, show kdbl 1 = (⟨2, 1⟩ : Q) from by decide]
      simp only [Qeq, mul, add, qpow]; push_cast; ring_uor
  | (N + 1) => by
      have hP : 0 < (peval kdbl w (N + 1)).den := peval_den_pos (fun i => kdbl_den i) hwd (N + 1)
      have hS : 0 < (add (⟨1, 1⟩ : Q) (mul w w)).den := add_den_pos Nat.one_pos (Qmul_den_pos hwd hwd)
      have hQt : 0 < (mul (kdbl (N + 2)) (qpow w (N + 2))).den :=
        Qmul_den_pos (kdbl_den (N + 2)) (qpow_den_pos hwd (N + 2))
      have hw2 : 0 < (mul w w).den := Qmul_den_pos hwd hwd
      -- expand Q_term·S = kdbl_{N+2}·w^{N+2} + kdbl_{N+2}·w^{N+4}
      have hPS : Qeq (mul (qpow w (N + 2)) (add ⟨1, 1⟩ (mul w w)))
          (add (qpow w (N + 2)) (qpow w (N + 4))) :=
        Qeq_trans (add_den_pos (Qmul_den_pos (qpow_den_pos hwd (N + 2)) Nat.one_pos)
            (Qmul_den_pos (qpow_den_pos hwd (N + 2)) hw2))
          (Qmul_add_left (qpow w (N + 2)) ⟨1, 1⟩ (mul w w))
          (Qadd_congr (mul_one (qpow w (N + 2))) (qpow_mul_sq w hwd (N + 2)))
      have hQexp : Qeq (mul (mul (kdbl (N + 2)) (qpow w (N + 2))) (add ⟨1, 1⟩ (mul w w)))
          (add (mul (kdbl (N + 2)) (qpow w (N + 2))) (mul (kdbl (N + 2)) (qpow w (N + 4)))) :=
        Qeq_trans (Qmul_den_pos (kdbl_den (N + 2)) (Qmul_den_pos (qpow_den_pos hwd (N + 2)) hS))
          (Qmul_assoc (kdbl (N + 2)) (qpow w (N + 2)) (add ⟨1, 1⟩ (mul w w)))
          (Qeq_trans (Qmul_den_pos (kdbl_den (N + 2))
              (add_den_pos (qpow_den_pos hwd (N + 2)) (qpow_den_pos hwd (N + 4))))
            (Qmul_congr (Qeq_refl _) hPS)
            (Qmul_add_left (kdbl (N + 2)) (qpow w (N + 2)) (qpow w (N + 4))))
      have hA : 0 < (mul (kdbl N) (qpow w (N + 2))).den := Qmul_den_pos (kdbl_den N) (qpow_den_pos hwd (N + 2))
      have hB : 0 < (mul (kdbl (N + 1)) (qpow w (N + 3))).den :=
        Qmul_den_pos (kdbl_den (N + 1)) (qpow_den_pos hwd (N + 3))
      have hC : 0 < (mul (kdbl (N + 2)) (qpow w (N + 2))).den := hQt
      have hD : 0 < (mul (kdbl (N + 2)) (qpow w (N + 4))).den :=
        Qmul_den_pos (kdbl_den (N + 2)) (qpow_den_pos hwd (N + 4))
      have h2w : 0 < (mul (⟨2, 1⟩ : Q) w).den := Qmul_den_pos Nat.one_pos hwd
      -- A + C ≈ 0  (period cancellation)
      have hAC : Qeq (add (mul (kdbl N) (qpow w (N + 2))) (mul (kdbl (N + 2)) (qpow w (N + 2)))) ⟨0, 1⟩ :=
        Qeq_trans (Qmul_den_pos (add_den_pos (kdbl_den N) (kdbl_den (N + 2))) (qpow_den_pos hwd (N + 2)))
          (Qeq_symm (Qmul_add_right (kdbl N) (kdbl (N + 2)) (qpow w (N + 2))))
          (Qeq_trans (Qmul_den_pos Nat.one_pos (qpow_den_pos hwd (N + 2)))
            (Qmul_congr (kdbl_period N) (Qeq_refl _)) (mul_left_zero _))
      -- assemble
      show Qeq (mul (add (peval kdbl w (N + 1)) (mul (kdbl (N + 2)) (qpow w (N + 2))))
          (add ⟨1, 1⟩ (mul w w)))
        (add (mul ⟨2, 1⟩ w) (add (mul (kdbl (N + 1)) (qpow w (N + 3)))
          (mul (kdbl (N + 2)) (qpow w (N + 4)))))
      refine Qeq_trans (add_den_pos (Qmul_den_pos hP hS) (Qmul_den_pos hQt hS))
        (Qmul_add_right (peval kdbl w (N + 1)) (mul (kdbl (N + 2)) (qpow w (N + 2)))
          (add ⟨1, 1⟩ (mul w w))) ?_
      refine Qeq_trans (add_den_pos (add_den_pos h2w (add_den_pos hA hB)) (add_den_pos hC hD))
        (Qadd_congr (kdbl_innerval w hwd N) hQexp) ?_
      refine Qeq_trans (add_den_pos h2w (add_den_pos (add_den_pos hA hB) (add_den_pos hC hD)))
        (Qadd_assoc3 _ _ _) ?_
      refine Qeq_trans (add_den_pos h2w (add_den_pos (add_den_pos hA hC) (add_den_pos hB hD)))
        (Qadd_congr (Qeq_refl _) (add_rearrange (mul (kdbl N) (qpow w (N + 2)))
          (mul (kdbl (N + 1)) (qpow w (N + 3))) (mul (kdbl (N + 2)) (qpow w (N + 2)))
          (mul (kdbl (N + 2)) (qpow w (N + 4))))) ?_
      refine Qadd_congr (Qeq_refl _) ?_
      exact Qeq_trans (add_den_pos Nat.one_pos (add_den_pos hB hD))
        (Qadd_congr hAC (Qeq_refl _)) (Qzero_add _)

/-- **`|u| ≤ 2ρ`** for `|w| ≤ ρ` (so `|u| < 1` when `ρ < ½`). -/
theorem uval_abs_le (ρ w : Q) (hwd : 0 < w.den) (hw : Qle (Qabs w) ρ) :
    Qle (Qabs (uval w)) (mul ⟨2, 1⟩ ρ) := by
  have hSden : 0 < (add (⟨1, 1⟩ : Q) (mul w w)).den := add_den_pos Nat.one_pos (Qmul_den_pos hwd hwd)
  have hSnn : 0 ≤ (add (⟨1, 1⟩ : Q) (mul w w)).num := by
    show 0 ≤ 1 * ((w.den * w.den : Nat) : Int) + (w.num * w.num) * 1
    have h1 : (0 : Int) ≤ ((w.den * w.den : Nat) : Int) := Int.ofNat_nonneg _
    have h2 : (0 : Int) ≤ w.num * w.num := by rw [← Int.natAbs_mul_self]; exact Int.ofNat_nonneg _
    omega
  have hud : 0 < (uval w).den := uval_den_pos w hwd
  -- |u|·(1+w²) = |2w| = 2|w| ≤ 2ρ
  have habs : Qeq (mul (Qabs (uval w)) (add ⟨1, 1⟩ (mul w w))) (mul ⟨2, 1⟩ (Qabs w)) :=
    Qeq_trans (Qmul_den_pos (Qabs_den_pos hud) (Qabs_den_pos hSden))
      (Qmul_congr (Qeq_refl _) (Qeq_symm (Qabs_of_nonneg hSnn)))
      (Qeq_trans (Qabs_den_pos (Qmul_den_pos hud hSden))
        (by rw [Qabs_mul]; exact Qeq_refl _ :
          Qeq (mul (Qabs (uval w)) (Qabs (add ⟨1, 1⟩ (mul w w))))
            (Qabs (mul (uval w) (add ⟨1, 1⟩ (mul w w)))))
        (Qeq_trans (Qabs_den_pos (Qmul_den_pos hSden hud))
          (Qabs_Qeq (Qmul_comm (uval w) (add ⟨1, 1⟩ (mul w w))))
          (Qeq_trans (Qabs_den_pos (Qmul_den_pos Nat.one_pos hwd)) (Qabs_Qeq (uval_rel w hwd))
            (by rw [Qabs_mul]; exact Qeq_refl _ :
              Qeq (Qabs (mul ⟨2, 1⟩ w)) (mul ⟨2, 1⟩ (Qabs w))))))
  refine Qle_trans (Qmul_den_pos (Qabs_den_pos hud) Nat.one_pos)
    (Qeq_le (Qeq_symm (mul_one (Qabs (uval w))))) ?_
  exact Qle_trans (Qmul_den_pos (Qabs_den_pos hud) hSden)
    (Qmul_le_mul_left (Qabs_num_nonneg _) (Qle_add_right_nonneg
      (by rw [← Int.natAbs_mul_self]; exact Int.ofNat_nonneg _ : (0 : Int) ≤ w.num * w.num)))
    (Qle_congr_left (Qmul_den_pos Nat.one_pos (Qabs_den_pos hwd)) (Qeq_symm habs)
      (Qmul_le_mul_left (by decide) hw))

/-- **Inner-value convergence**: `|peval(kdbl,w,N+1) − u| ≤ 2ρ^{N+2} + 2ρ^{N+3} → 0`. -/
theorem q_conv (ρ w : Q) (hρd : 0 < ρ.den) (hwd : 0 < w.den) (hw : Qle (Qabs w) ρ) (N : Nat) :
    Qle (Qabs (Qsub (peval kdbl w (N + 1)) (uval w)))
      (add (mul ⟨2, 1⟩ (qpow ρ (N + 2))) (mul ⟨2, 1⟩ (qpow ρ (N + 3)))) := by
  have hSden : 0 < (add (⟨1, 1⟩ : Q) (mul w w)).den := add_den_pos Nat.one_pos (Qmul_den_pos hwd hwd)
  have hSnn : 0 ≤ (add (⟨1, 1⟩ : Q) (mul w w)).num := by
    show 0 ≤ 1 * ((w.den * w.den : Nat) : Int) + (w.num * w.num) * 1
    have h1 : (0 : Int) ≤ ((w.den * w.den : Nat) : Int) := Int.ofNat_nonneg _
    have h2 : (0 : Int) ≤ w.num * w.num := by rw [← Int.natAbs_mul_self]; exact Int.ofNat_nonneg _
    omega
  have hqd : 0 < (Qsub (peval kdbl w (N + 1)) (uval w)).den :=
    Qsub_den_pos (peval_den_pos (fun i => kdbl_den i) hwd (N + 1)) (uval_den_pos w hwd)
  have hBDd : 0 < (add (mul (kdbl N) (qpow w (N + 2))) (mul (kdbl (N + 1)) (qpow w (N + 3)))).den :=
    add_den_pos (Qmul_den_pos (kdbl_den N) (qpow_den_pos hwd (N + 2)))
      (Qmul_den_pos (kdbl_den (N + 1)) (qpow_den_pos hwd (N + 3)))
  -- (1+w²)·(q−u) ≈ BD
  have hident : Qeq (mul (add ⟨1, 1⟩ (mul w w)) (Qsub (peval kdbl w (N + 1)) (uval w)))
      (add (mul (kdbl N) (qpow w (N + 2))) (mul (kdbl (N + 1)) (qpow w (N + 3)))) :=
    Qeq_trans (Qsub_den_pos (Qmul_den_pos hSden (peval_den_pos (fun i => kdbl_den i) hwd (N + 1)))
        (Qmul_den_pos hSden (uval_den_pos w hwd)))
      (Qmul_sub_left_loc (add ⟨1, 1⟩ (mul w w)) (peval kdbl w (N + 1)) (uval w))
      (Qeq_trans (Qsub_den_pos (add_den_pos (Qmul_den_pos Nat.one_pos hwd) hBDd)
          (Qmul_den_pos Nat.one_pos hwd))
        (Qsub_congr
          (Qeq_trans (Qmul_den_pos (peval_den_pos (fun i => kdbl_den i) hwd (N + 1)) hSden)
            (Qmul_comm (add ⟨1, 1⟩ (mul w w)) (peval kdbl w (N + 1))) (kdbl_innerval w hwd N))
          (uval_rel w hwd))
        (Qsub_add_cancel (mul ⟨2, 1⟩ w)
          (add (mul (kdbl N) (qpow w (N + 2))) (mul (kdbl (N + 1)) (qpow w (N + 3))))))
  -- |q−u| ≤ |(1+w²)(q−u)| = |BD| ≤ bound
  have habs : Qeq (mul (Qabs (Qsub (peval kdbl w (N + 1)) (uval w))) (add ⟨1, 1⟩ (mul w w)))
      (Qabs (add (mul (kdbl N) (qpow w (N + 2))) (mul (kdbl (N + 1)) (qpow w (N + 3))))) :=
    Qeq_trans (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hSden))
      (Qmul_congr (Qeq_refl _) (Qeq_symm (Qabs_of_nonneg hSnn)))
      (Qeq_trans (Qabs_den_pos (Qmul_den_pos hqd hSden))
        (by rw [Qabs_mul]; exact Qeq_refl _ :
          Qeq (mul (Qabs (Qsub (peval kdbl w (N + 1)) (uval w))) (Qabs (add ⟨1, 1⟩ (mul w w))))
            (Qabs (mul (Qsub (peval kdbl w (N + 1)) (uval w)) (add ⟨1, 1⟩ (mul w w)))))
        (Qeq_trans (Qabs_den_pos (Qmul_den_pos hSden hqd))
          (Qabs_Qeq (Qmul_comm (Qsub (peval kdbl w (N + 1)) (uval w)) (add ⟨1, 1⟩ (mul w w))))
          (Qabs_Qeq hident)))
  refine Qle_trans (Qabs_den_pos hBDd) ?_ ?_
  · -- |q−u| ≤ |BD|
    refine Qle_trans (Qmul_den_pos (Qabs_den_pos hqd) Nat.one_pos)
      (Qeq_le (Qeq_symm (mul_one (Qabs (Qsub (peval kdbl w (N + 1)) (uval w)))))) ?_
    exact Qle_trans (Qmul_den_pos (Qabs_den_pos hqd) hSden)
      (Qmul_le_mul_left (Qabs_num_nonneg _) (Qle_add_right_nonneg ((by rw [← Int.natAbs_mul_self]; exact Int.ofNat_nonneg _ : (0:Int) ≤ w.num * w.num))))
      (Qeq_le habs)
  · -- |BD| ≤ 2ρ^{N+2} + 2ρ^{N+3}
    exact Qle_trans (add_den_pos (Qabs_den_pos (Qmul_den_pos (kdbl_den N) (qpow_den_pos hwd (N + 2))))
        (Qabs_den_pos (Qmul_den_pos (kdbl_den (N + 1)) (qpow_den_pos hwd (N + 3)))))
      (Qabs_add_le _ _)
      (Qadd_le_add (Qabs_kdbl_qpow_le ρ w hρd hwd hw N (N + 2))
        (Qabs_kdbl_qpow_le ρ w hρd hwd hw (N + 1) (N + 3)))

/-- `|a − b| ≤ |a| + |b|`. -/
theorem Qabs_sub_le_add (a b : Q) : Qle (Qabs (Qsub a b)) (add (Qabs a) (Qabs b)) := by
  show Qle (Qabs (add a (neg b))) (add (Qabs a) (Qabs b))
  have h := Qabs_add_le a (neg b); rw [Qabs_neg b] at h; exact h

/-- The recursion algebra `(q·pm − cor) − u·um = q·(pm − um) + ((q−u)·um − cor)`. -/
theorem e_rec_alg (q pm um u cor : Q) :
    Qeq (Qsub (Qsub (mul q pm) cor) (mul u um))
      (add (mul q (Qsub pm um)) (Qsub (mul (Qsub q u) um) cor)) := by
  simp only [Qeq, mul, add, Qsub, neg]; push_cast; ring_uor

/-- Bounded termwise sum monotonicity (`f ≤ g` for `i ≤ M`). -/
theorem Fsum_le_Fsum_le {f g : Nat → Q} :
    ∀ {M}, (∀ i, i ≤ M → Qle (f i) (g i)) → Qle (Fsum f M) (Fsum g M)
  | 0, h => h 0 (Nat.le_refl 0)
  | (M + 1), h => Qadd_le_add (Fsum_le_Fsum_le (fun i hi => h i (by omega))) (h (M + 1) (Nat.le_refl _))

/-- **Per-`i` corner term bound**: `|inner_i|·(1−2ρ) ≤ 2·4ᵐ·(2ρ)^{M+1}` for `i ≤ M`. -/
theorem corner_term_le (ρ w : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hwd : 0 < w.den)
    (hw : Qle (Qabs w) ρ) (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num) (m M i : Nat) (hiM : i ≤ M) :
    Qle (mul (Qabs (Qsub
          (Fsum (fun j => mul (mul (kdbl i) (qpow w i)) (mul (fpow kdbl m j) (qpow w j))) M)
          (Fsum (fun j => mul (mul (kdbl i) (qpow w i)) (mul (fpow kdbl m j) (qpow w j))) (M - i))))
          (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ)))
      (mul (⟨2 * (4 : Int) ^ m, 1⟩ : Q) (qpow (mul ⟨2, 1⟩ ρ) (M + 1))) := by
  have hpd : ∀ N, 0 < (peval (fpow kdbl m) w N).den :=
    fun N => peval_den_pos (fpow_den_pos (fun l => kdbl_den l) m) hwd N
  have hC : 0 < (mul (kdbl i) (qpow w i)).den := Qmul_den_pos (kdbl_den i) (qpow_den_pos hwd i)
  have hgap : 0 < (Qsub (peval (fpow kdbl m) w M) (peval (fpow kdbl m) w (M - i))).den :=
    Qsub_den_pos (hpd M) (hpd (M - i))
  have h2d : 0 < (mul (⟨2, 1⟩ : Q) ρ).den := Qmul_den_pos (by decide) hρd
  have hwd1 : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).den := Qsub_den_pos Nat.one_pos h2d
  have h4n : (0 : Int) ≤ (4 : Int) ^ m := by exact_mod_cast Nat.zero_le (4 ^ m)
  have hRHSn : 0 ≤ (mul (⟨(4 : Int) ^ m, 1⟩ : Q) (qpow (mul ⟨2, 1⟩ ρ) (M - i + 1))).num :=
    Qmul_num_nonneg h4n (qpow_nonneg (Qmul_num_nonneg (by decide) hρ0) _)
  have heq : Qeq (Qabs (Qsub
        (Fsum (fun j => mul (mul (kdbl i) (qpow w i)) (mul (fpow kdbl m j) (qpow w j))) M)
        (Fsum (fun j => mul (mul (kdbl i) (qpow w i)) (mul (fpow kdbl m j) (qpow w j))) (M - i))))
      (mul (Qabs (mul (kdbl i) (qpow w i)))
        (Qabs (Qsub (peval (fpow kdbl m) w M) (peval (fpow kdbl m) w (M - i))))) :=
    Qeq_trans (Qabs_den_pos (Qmul_den_pos hC hgap)) (Qabs_Qeq (corner_inner_eq w hwd m M i))
      (by rw [Qabs_mul]; exact Qeq_refl _)
  refine Qle_trans (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hC) (Qabs_den_pos hgap)) hwd1)
    (Qeq_le (Qmul_congr heq (Qeq_refl _))) ?_
  refine Qle_trans (Qmul_den_pos (Qabs_den_pos hC) (Qmul_den_pos (Qabs_den_pos hgap) hwd1))
    (Qeq_le (Qmul_assoc (Qabs (mul (kdbl i) (qpow w i)))
      (Qabs (Qsub (peval (fpow kdbl m) w M) (peval (fpow kdbl m) w (M - i))))
      (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ)))) ?_
  refine Qle_trans (Qmul_den_pos (Qabs_den_pos hC) (Qmul_den_pos Nat.one_pos (qpow_den_pos h2d _)))
    (Qmul_le_mul_left (Qabs_num_nonneg _)
      (peval_kdbl_pow_cauchy ρ w hρd hρ0 hwd hw h2ρ m (M := M - i) (M' := M) (by omega))) ?_
  refine Qle_trans (Qmul_den_pos (Qmul_den_pos (by decide) (qpow_den_pos hρd i))
      (Qmul_den_pos Nat.one_pos (qpow_den_pos h2d _)))
    (Qmul_le_mul_right hRHSn (Qabs_C_le ρ w hρd hwd hw i)) ?_
  refine Qle_trans (Qmul_den_pos (Qmul_den_pos (by decide) Nat.one_pos)
      (Qmul_den_pos (qpow_den_pos hρd i) (qpow_den_pos h2d _)))
    (Qeq_le (mul_rearrange ⟨2, 1⟩ (qpow ρ i) ⟨(4 : Int) ^ m, 1⟩ (qpow (mul ⟨2, 1⟩ ρ) (M - i + 1)))) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos (qpow_den_pos hρd i) (qpow_den_pos h2d _)))
    (Qeq_le (Qmul_congr (by simp [Qeq, mul] :
      Qeq (mul (⟨2, 1⟩ : Q) ⟨(4 : Int) ^ m, 1⟩) ⟨2 * (4 : Int) ^ m, 1⟩) (Qeq_refl _))) ?_
  exact Qmul_le_mul_left (by show (0 : Int) ≤ 2 * (4 : Int) ^ m; omega)
    (qpow_conv_le ρ hρd hρ0 i M hiM)

/-- **The corner bound**: `|corner_m(M)|·(1−2ρ) ≤ Σ_{i≤M} 2·4ᵐ·(2ρ)^{M+1}` (= `(M+1)·2·4ᵐ·(2ρ)^{M+1}`),
    which → 0 as `M → ∞`. The corner of `peval_fpow_succ` for `kdbl`. -/
theorem corner_bound (ρ w : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hwd : 0 < w.den)
    (hw : Qle (Qabs w) ρ) (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num) (m M : Nat) :
    Qle (mul (Qabs (Fsum (fun i => Qsub
            (Fsum (fun j => mul (mul (kdbl i) (qpow w i)) (mul (fpow kdbl m j) (qpow w j))) M)
            (Fsum (fun j => mul (mul (kdbl i) (qpow w i)) (mul (fpow kdbl m j) (qpow w j))) (M - i))) M))
          (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ)))
      (Fsum (fun _ => mul (⟨2 * (4 : Int) ^ m, 1⟩ : Q) (qpow (mul ⟨2, 1⟩ ρ) (M + 1))) M) := by
  have hgd : ∀ i j, 0 < (mul (mul (kdbl i) (qpow w i)) (mul (fpow kdbl m j) (qpow w j))).den :=
    fun i j => Qmul_den_pos (Qmul_den_pos (kdbl_den i) (qpow_den_pos hwd i))
      (Qmul_den_pos (fpow_den_pos (fun l => kdbl_den l) m j) (qpow_den_pos hwd j))
  have hid : ∀ i, 0 < (Qsub
      (Fsum (fun j => mul (mul (kdbl i) (qpow w i)) (mul (fpow kdbl m j) (qpow w j))) M)
      (Fsum (fun j => mul (mul (kdbl i) (qpow w i)) (mul (fpow kdbl m j) (qpow w j))) (M - i))).den :=
    fun i => Qsub_den_pos (Fsum_den_pos (fun j => hgd i j) M) (Fsum_den_pos (fun j => hgd i j) (M - i))
  have hwd1 : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).den :=
    Qsub_den_pos Nat.one_pos (Qmul_den_pos (by decide) hρd)
  refine Qle_trans (Qmul_den_pos (Fsum_den_pos (fun i => Qabs_den_pos (hid i)) M) hwd1)
    (Qmul_le_mul_right h2ρ (Fsum_abs_le (fun i => hid i) M)) ?_
  refine Qle_trans (Fsum_den_pos (fun i => Qmul_den_pos (Qabs_den_pos (hid i)) hwd1) M)
    (Qeq_le (Fsum_mul_const_right hwd1 (fun i => Qabs_den_pos (hid i)) M)) ?_
  exact Fsum_le_Fsum_le (fun i hi => corner_term_le ρ w hρd hρ0 hwd hw h2ρ m M i hi)

/-- Per-term geometric telescope: `ρ^{2N+1}·(1−ρ²) = ρ^{2N+1} − ρ^{2N+3}`. -/
theorem geoTerm_tel (ρ : Q) (hρd : 0 < ρ.den) (N : Nat) :
    Qeq (mul (geoTerm ρ N) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
      (Qsub (qpow ρ (2 * N + 1)) (qpow ρ (2 * N + 3))) := by
  have hexp : Qeq (qpow ρ (2 * N + 3)) (mul (qpow ρ (2 * N + 1)) (mul ρ ρ)) :=
    Qeq_trans (Qmul_den_pos (qpow_den_pos hρd (2 * N + 1)) (qpow_den_pos hρd 2))
      (by rw [show 2 * N + 3 = (2 * N + 1) + 2 from by omega]; exact qpow_add ρ hρd (2 * N + 1) 2)
      (Qmul_congr (Qeq_refl _) (by show Qeq (qpow ρ 2) (mul ρ ρ); simp only [Qeq, mul, qpow]; push_cast; ring_uor))
  show Qeq (mul (qpow ρ (2 * N + 1)) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
    (Qsub (qpow ρ (2 * N + 1)) (qpow ρ (2 * N + 3)))
  refine Qeq_trans (Qsub_den_pos (qpow_den_pos hρd _)
      (Qmul_den_pos (qpow_den_pos hρd _) (Qmul_den_pos hρd hρd)))
    (by simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor)
    (Qsub_congr (Qeq_refl _) (Qeq_symm hexp))

/-- **Geometric telescope** for `geoSum`: `(Σ_{n≤N} ρ^{2n+1})·(1−ρ²) = ρ − ρ^{2N+3}`. -/
theorem geoSum_telescope (ρ : Q) (hρd : 0 < ρ.den) :
    ∀ N, Qeq (mul (geoSum ρ N) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (Qsub (qpow ρ 1) (qpow ρ (2 * N + 3)))
  | 0 => geoTerm_tel ρ hρd 0
  | (N + 1) => by
      show Qeq (mul (add (geoSum ρ N) (geoTerm ρ (N + 1))) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
        (Qsub (qpow ρ 1) (qpow ρ (2 * (N + 1) + 3)))
      have hW : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).den := Qsub_den_pos Nat.one_pos (Qmul_den_pos hρd hρd)
      refine Qeq_trans (add_den_pos (Qmul_den_pos (geoSum_den_pos hρd N) hW)
          (Qmul_den_pos (qpow_den_pos hρd _) hW))
        (Qmul_add_right (geoSum ρ N) (geoTerm ρ (N + 1)) (Qsub ⟨1, 1⟩ (mul ρ ρ))) ?_
      refine Qeq_trans (add_den_pos (Qsub_den_pos (qpow_den_pos hρd _) (qpow_den_pos hρd _))
          (Qsub_den_pos (qpow_den_pos hρd _) (qpow_den_pos hρd _)))
        (Qadd_congr (geoSum_telescope ρ hρd N)
          (by rw [show 2 * (N + 1) + 1 = 2 * N + 3 from by omega] at *; exact geoTerm_tel ρ hρd (N + 1))) ?_
      show Qeq (add (Qsub (qpow ρ 1) (qpow ρ (2 * N + 3))) (Qsub (qpow ρ (2 * N + 3)) (qpow ρ (2 * N + 5))))
        (Qsub (qpow ρ 1) (qpow ρ (2 * (N + 1) + 3)))
      rw [show 2 * (N + 1) + 3 = 2 * N + 5 from by omega]
      simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor

/-- `geoSum ρ N · (1−ρ²) ≤ ρ` (drop the nonnegative `ρ^{2N+3}` tail). -/
theorem geoSum_tel_le (ρ : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (N : Nat) :
    Qle (mul (geoSum ρ N) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (qpow ρ 1) :=
  Qle_congr_left (Qsub_den_pos (qpow_den_pos hρd _) (qpow_den_pos hρd _))
    (Qeq_symm (geoSum_telescope ρ hρd N)) (Qsub_le_self (qpow_nonneg hρ0 _))

/-- The even-index terms of `|kdbl|·ρ^•` vanish. -/
theorem fabs_kdbl_even (ρ : Q) (n : Nat) :
    Qeq (mul (fabs kdbl (2 * n)) (qpow ρ (2 * n))) ⟨0, 1⟩ := by
  have h : fabs kdbl (2 * n) = ⟨0, 1⟩ := by
    show Qabs (kdbl (2 * n)) = ⟨0, 1⟩
    rw [show kdbl (2 * n) = ⟨0, 1⟩ from by
      unfold kdbl; rw [if_neg (by omega), if_neg (by omega)]]
    decide
  rw [h]; exact mul_left_zero _

/-- The odd-index term of `|kdbl|·ρ^•` is `2·ρ^{2n+1} = 2·geoTerm`. -/
theorem fabs_kdbl_odd (ρ : Q) (n : Nat) :
    Qeq (mul (fabs kdbl (2 * n + 1)) (qpow ρ (2 * n + 1))) (mul ⟨2, 1⟩ (geoTerm ρ n)) := by
  have h : fabs kdbl (2 * n + 1) = ⟨2, 1⟩ := by
    show Qabs (kdbl (2 * n + 1)) = ⟨2, 1⟩
    rcases (by omega : (2 * n + 1) % 4 = 1 ∨ (2 * n + 1) % 4 = 3) with h1 | h3
    · rw [show kdbl (2 * n + 1) = ⟨2, 1⟩ from by unfold kdbl; rw [if_pos h1]]; decide
    · rw [show kdbl (2 * n + 1) = ⟨-2, 1⟩ from by unfold kdbl; rw [if_neg (by omega), if_pos h3]]
      decide
  rw [h]; exact Qeq_refl _

/-- **The geometric majorant evaluation**: `eval(|kdbl|, ρ, 2N+1) = 2·geoSum ρ N` (= `2 Σ_{n≤N} ρ^{2n+1}`). -/
theorem peval_fabs_kdbl_geoSum (ρ : Q) (hρd : 0 < ρ.den) (N : Nat) :
    Qeq (peval (fabs kdbl) ρ (2 * N + 1)) (mul ⟨2, 1⟩ (geoSum ρ N)) := by
  induction N with
  | zero =>
      show Qeq (add (mul (fabs kdbl 0) (qpow ρ 0)) (mul (fabs kdbl 1) (qpow ρ 1)))
        (mul ⟨2, 1⟩ (geoTerm ρ 0))
      exact Qeq_trans (add_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd 1)))
        (Qadd_congr (fabs_kdbl_even ρ 0) (fabs_kdbl_odd ρ 0)) (Qzero_add _)
  | succ N ih =>
      rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 from by omega]
      show Qeq (add (add (peval (fabs kdbl) ρ (2 * N + 1))
          (mul (fabs kdbl (2 * N + 1 + 1)) (qpow ρ (2 * N + 1 + 1))))
          (mul (fabs kdbl (2 * N + 1 + 1 + 1)) (qpow ρ (2 * N + 1 + 1 + 1))))
        (mul ⟨2, 1⟩ (add (geoSum ρ N) (geoTerm ρ (N + 1))))
      have he : Qeq (mul (fabs kdbl (2 * N + 1 + 1)) (qpow ρ (2 * N + 1 + 1))) ⟨0, 1⟩ := by
        rw [show 2 * N + 1 + 1 = 2 * (N + 1) from by omega]; exact fabs_kdbl_even ρ (N + 1)
      have ho : Qeq (mul (fabs kdbl (2 * N + 1 + 1 + 1)) (qpow ρ (2 * N + 1 + 1 + 1)))
          (mul ⟨2, 1⟩ (geoTerm ρ (N + 1))) := by
        rw [show 2 * N + 1 + 1 + 1 = 2 * (N + 1) + 1 from by omega]; exact fabs_kdbl_odd ρ (N + 1)
      refine Qeq_trans (add_den_pos (add_den_pos (Qmul_den_pos Nat.one_pos (geoSum_den_pos hρd N))
          Nat.one_pos) (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd (2 * (N + 1) + 1))))
        (Qadd_congr (Qadd_congr ih he) ho) ?_
      refine Qeq_trans (add_den_pos (Qmul_den_pos Nat.one_pos (geoSum_den_pos hρd N))
        (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd (2 * (N + 1) + 1))))
        (Qadd_congr (Qadd_zero_right _) (Qeq_refl _)) ?_
      exact Qeq_symm (Qmul_add_left ⟨2, 1⟩ (geoSum ρ N) (geoTerm ρ (N + 1)))

/-- **Uniform power bound**: `|peval(kdblᵐ, w, M)| ≤ (2·geoSum ρ M)ᵐ` for `|w| ≤ ρ` (the `M`-uniform
    geometric bound `≤ σᵐ` once `2·geoSum ρ M ≤ σ`). -/
theorem peval_kdbl_pow_abs_le (ρ w : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hwd : 0 < w.den)
    (hw : Qle (Qabs w) ρ) (m M : Nat) :
    Qle (Qabs (peval (fpow kdbl m) w M)) (qpow (mul ⟨2, 1⟩ (geoSum ρ M)) m) := by
  refine Qle_trans (qpow_den_pos (peval_den_pos (fun k => fabs_den_pos (fun i => kdbl_den i) k) hρd M) m)
    (peval_fpow_abs_bound kdbl (fun i => kdbl_den i) w hwd hρd hρ0 hw m M) ?_
  refine qpow_base_mono (peval_den_pos (fun k => fabs_den_pos (fun i => kdbl_den i) k) hρd M)
    (Qmul_den_pos (by decide) (geoSum_den_pos hρd M))
    (peval_num_nonneg (fun k => fabs_nonneg kdbl k) ρ hρ0 M) ?_ m
  exact Qle_trans (peval_den_pos (fun k => fabs_den_pos (fun i => kdbl_den i) k) hρd (2 * M + 1))
    (Fsum_mono_len (fun i => Qmul_num_nonneg (fabs_nonneg kdbl i) (qpow_nonneg hρ0 i))
      (fun i => Qmul_den_pos (fabs_den_pos (fun j => kdbl_den j) i) (qpow_den_pos hρd i))
      (by omega : M ≤ 2 * M + 1))
    (Qeq_le (peval_fabs_kdbl_geoSum ρ hρd M))

/-- **The composed-series evaluation IS twice the artanh sum** (formal_doubling, evaluated): the formal
    series `artanh∘kdbl`, evaluated at `w` and truncated at `2N+1`, equals `2·artSum w N`. This carries
    `formal_doubling` to the analytic `artSum` side; combined with the composition eval bridge
    (`peval(artanh∘kdbl,w) → Rartanh(2w/(1+w²))`) it gives the real doubling `2 Rartanh w = Rartanh(2w/(1+w²))`. -/
theorem dcomp_artSum (w : Q) (hwd : 0 < w.den) (N : Nat) :
    Qeq (peval (fcomp acoef kdbl) w (2 * N + 1)) (mul ⟨2, 1⟩ (artSum w N)) := by
  refine Qeq_trans (peval_den_pos (fun k => Qmul_den_pos Nat.one_pos (acoef_den k)) hwd _)
    (peval_congr (fun k => formal_doubling k) w (2 * N + 1)) ?_
  refine Qeq_trans (Qmul_den_pos Nat.one_pos (peval_den_pos (fun k => acoef_den k) hwd _))
    (peval_smul ⟨2, 1⟩ Nat.one_pos acoef (fun k => acoef_den k) w hwd (2 * N + 1)) ?_
  exact Qmul_congr (Qeq_refl _) (peval_acoef_artSum w hwd N)

/-- The `peval_fpow_succ` corner for `kdbl` (abbreviation). -/
def kcorner (w : Q) (m M : Nat) : Q :=
  Fsum (fun i => Qsub
    (Fsum (fun j => mul (mul (kdbl i) (qpow w i)) (mul (fpow kdbl m j) (qpow w j))) M)
    (Fsum (fun j => mul (mul (kdbl i) (qpow w i)) (mul (fpow kdbl m j) (qpow w j))) (M - i))) M

theorem kcorner_den (w : Q) (hwd : 0 < w.den) (m M : Nat) : 0 < (kcorner w m M).den :=
  Fsum_den_pos (fun i => Qsub_den_pos
    (Fsum_den_pos (fun j => Qmul_den_pos (Qmul_den_pos (kdbl_den i) (qpow_den_pos hwd i))
      (Qmul_den_pos (fpow_den_pos (fun l => kdbl_den l) m j) (qpow_den_pos hwd j))) M)
    (Fsum_den_pos (fun j => Qmul_den_pos (Qmul_den_pos (kdbl_den i) (qpow_den_pos hwd i))
      (Qmul_den_pos (fpow_den_pos (fun l => kdbl_den l) m j) (qpow_den_pos hwd j))) (M - i))) M

/-- **Per-`m` error recursion step**: `|e_{m+1}| ≤ |q|·|e_m| + |q−u|·|uᵐ| + |corner_m|`,
    where `e_m = peval(kdblᵐ,w,M) − uᵐ`, `q = peval(kdbl,w,M)`, `u = uval w`. -/
theorem per_m_step (w : Q) (hwd : 0 < w.den) (m M : Nat) :
    Qle (Qabs (Qsub (peval (fpow kdbl (m + 1)) w M) (qpow (uval w) (m + 1))))
      (add (mul (Qabs (peval kdbl w M))
              (Qabs (Qsub (peval (fpow kdbl m) w M) (qpow (uval w) m))))
        (add (mul (Qabs (Qsub (peval kdbl w M) (uval w))) (Qabs (qpow (uval w) m)))
          (Qabs (kcorner w m M)))) := by
  have hq : 0 < (peval kdbl w M).den := peval_den_pos (fun i => kdbl_den i) hwd M
  have hpm : 0 < (peval (fpow kdbl m) w M).den := peval_den_pos (fpow_den_pos (fun i => kdbl_den i) m) hwd M
  have hu : 0 < (uval w).den := uval_den_pos w hwd
  have hum : 0 < (qpow (uval w) m).den := qpow_den_pos hu m
  have hem : 0 < (Qsub (peval (fpow kdbl m) w M) (qpow (uval w) m)).den := Qsub_den_pos hpm hum
  have hqu : 0 < (Qsub (peval kdbl w M) (uval w)).den := Qsub_den_pos hq hu
  have hcor : 0 < (kcorner w m M).den := kcorner_den w hwd m M
  -- e_{m+1} = q·e_m + ((q−u)·uᵐ − corner)
  have hid : Qeq (Qsub (peval (fpow kdbl (m + 1)) w M) (qpow (uval w) (m + 1)))
      (add (mul (peval kdbl w M) (Qsub (peval (fpow kdbl m) w M) (qpow (uval w) m)))
        (Qsub (mul (Qsub (peval kdbl w M) (uval w)) (qpow (uval w) m)) (kcorner w m M))) :=
    Qeq_trans (Qsub_den_pos (Qsub_den_pos (Qmul_den_pos hq hpm) hcor) (qpow_den_pos hu (m + 1)))
      (Qsub_congr (peval_fpow_succ kdbl (fun i => kdbl_den i) w hwd m M) (Qeq_refl _))
      (e_rec_alg (peval kdbl w M) (peval (fpow kdbl m) w M) (qpow (uval w) m) (uval w) (kcorner w m M))
  refine Qle_trans (Qabs_den_pos (add_den_pos (Qmul_den_pos hq hem) (Qsub_den_pos (Qmul_den_pos hqu hum) hcor)))
    (Qeq_le (Qabs_Qeq hid)) ?_
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qmul_den_pos hq hem))
      (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos hqu hum) hcor)))
    (Qabs_add_le _ _) ?_
  refine Qadd_le_add (Qeq_le (by rw [Qabs_mul]; exact Qeq_refl _ :
    Qeq (Qabs (mul (peval kdbl w M) (Qsub (peval (fpow kdbl m) w M) (qpow (uval w) m))))
      (mul (Qabs (peval kdbl w M)) (Qabs (Qsub (peval (fpow kdbl m) w M) (qpow (uval w) m)))))) ?_
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qmul_den_pos hqu hum)) (Qabs_den_pos hcor))
    (Qabs_sub_le_add _ _) ?_
  exact Qadd_le_add (Qeq_le (by rw [Qabs_mul]; exact Qeq_refl _ :
    Qeq (Qabs (mul (Qsub (peval kdbl w M) (uval w)) (qpow (uval w) m)))
      (mul (Qabs (Qsub (peval kdbl w M) (uval w))) (Qabs (qpow (uval w) m))))) (Qle_refl _)

/-- **Per-`m` error bound**: `|peval(kdblᵐ⁺¹,w,M) − uᵐ⁺¹| ≤ Σ_{j≤m} (|q−u| + |corner_j|)`, given
    `|q| ≤ 1` and `|u| ≤ 1`. By induction via `per_m_step`. -/
theorem per_m_bound (w : Q) (M : Nat) (hwd : 0 < w.den)
    (hq1 : Qle (Qabs (peval kdbl w M)) ⟨1, 1⟩) (hu1 : Qle (Qabs (uval w)) ⟨1, 1⟩) (m : Nat) :
    Qle (Qabs (Qsub (peval (fpow kdbl (m + 1)) w M) (qpow (uval w) (m + 1))))
      (Fsum (fun j => add (Qabs (Qsub (peval kdbl w M) (uval w))) (Qabs (kcorner w j M))) m) := by
  have hud : 0 < (uval w).den := uval_den_pos w hwd
  have hqd : 0 < (peval kdbl w M).den := peval_den_pos (fun i => kdbl_den i) hwd M
  have hqud : 0 < (Qsub (peval kdbl w M) (uval w)).den := Qsub_den_pos hqd hud
  have hpd : ∀ k, 0 < (peval (fpow kdbl k) w M).den :=
    fun k => peval_den_pos (fpow_den_pos (fun i => kdbl_den i) k) hwd M
  have hum1 : ∀ k, Qle (Qabs (qpow (uval w) k)) ⟨1, 1⟩ := by
    intro k
    induction k with
    | zero => show Qle (Qabs (⟨1, 1⟩ : Q)) ⟨1, 1⟩; decide
    | succ k ih =>
        show Qle (Qabs (mul (uval w) (qpow (uval w) k))) ⟨1, 1⟩
        refine Qle_trans (Qmul_den_pos (Qabs_den_pos hud) (Qabs_den_pos (qpow_den_pos hud k)))
          (Qeq_le (by rw [Qabs_mul]; exact Qeq_refl _ :
            Qeq (Qabs (mul (uval w) (qpow (uval w) k)))
              (mul (Qabs (uval w)) (Qabs (qpow (uval w) k))))) ?_
        exact Qle_trans (Qmul_den_pos Nat.one_pos Nat.one_pos)
          (Qmul_le_mul (Qabs_den_pos hud) Nat.one_pos (Qabs_den_pos (qpow_den_pos hud k))
            (Qabs_num_nonneg _) (Qabs_num_nonneg _) hu1 ih)
          (by decide : Qle (mul (⟨1, 1⟩ : Q) ⟨1, 1⟩) ⟨1, 1⟩)
  -- bound1: |q|·|e| ≤ |e|
  have bound1 : ∀ {e : Q}, 0 < e.den → Qle (mul (Qabs (peval kdbl w M)) (Qabs e)) (Qabs e) :=
    fun {e} he => Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos he))
      (Qmul_le_mul_right (Qabs_num_nonneg _) hq1) (Qeq_le (Qone_mul _))
  induction m with
  | zero =>
      have hz : Qeq (Qsub (peval (fpow kdbl 0) w M) (qpow (uval w) 0)) ⟨0, 1⟩ := by
        show Qeq (Qsub (peval fone w M) ⟨1, 1⟩) ⟨0, 1⟩
        refine Qeq_trans (Qsub_den_pos Nat.one_pos Nat.one_pos)
          (Qsub_congr (peval_fone w hwd M) (Qeq_refl _)) ?_
        simp [Qeq, Qsub, add, neg]
      have he0 : Qle (Qabs (Qsub (peval (fpow kdbl 0) w M) (qpow (uval w) 0))) ⟨0, 1⟩ :=
        Qeq_le (Qeq_trans Nat.one_pos (Qabs_Qeq hz) (by decide : Qeq (Qabs (⟨0, 1⟩ : Q)) ⟨0, 1⟩))
      show Qle (Qabs (Qsub (peval (fpow kdbl 1) w M) (qpow (uval w) 1)))
        (add (Qabs (Qsub (peval kdbl w M) (uval w))) (Qabs (kcorner w 0 M)))
      refine Qle_trans (add_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos (Qsub_den_pos (hpd 0) (qpow_den_pos hud 0))))
          (add_den_pos (Qmul_den_pos (Qabs_den_pos hqud) (Qabs_den_pos (qpow_den_pos hud 0))) (Qabs_den_pos (kcorner_den w hwd 0 M))))
        (per_m_step w hwd 0 M) ?_
      refine Qle_trans (add_den_pos Nat.one_pos
          (add_den_pos (Qabs_den_pos hqud) (Qabs_den_pos (kcorner_den w hwd 0 M))))
        (Qadd_le_add (Qle_trans (Qabs_den_pos (Qsub_den_pos (hpd 0) (qpow_den_pos hud 0)))
            (bound1 (Qsub_den_pos (hpd 0) (qpow_den_pos hud 0))) he0)
          (Qadd_le_add (Qle_trans (Qmul_den_pos (Qabs_den_pos hqud) Nat.one_pos)
            (Qmul_le_mul_left (Qabs_num_nonneg _) (hum1 0)) (Qeq_le (mul_one _))) (Qle_refl _))) ?_
      exact Qeq_le (Qzero_add _)
  | succ m ih =>
      refine Qle_trans (add_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos (Qsub_den_pos (hpd (m + 1)) (qpow_den_pos hud (m + 1)))))
          (add_den_pos (Qmul_den_pos (Qabs_den_pos hqud) (Qabs_den_pos (qpow_den_pos hud (m + 1)))) (Qabs_den_pos (kcorner_den w hwd (m + 1) M))))
        (per_m_step w hwd (m + 1) M) ?_
      refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (hpd (m + 1)) (qpow_den_pos hud (m + 1))))
          (add_den_pos (Qabs_den_pos hqud) (Qabs_den_pos (kcorner_den w hwd (m + 1) M))))
        (Qadd_le_add (bound1 (Qsub_den_pos (hpd (m + 1)) (qpow_den_pos hud (m + 1))))
          (Qadd_le_add (Qle_trans (Qmul_den_pos (Qabs_den_pos hqud) Nat.one_pos)
            (Qmul_le_mul_left (Qabs_num_nonneg _) (hum1 (m + 1))) (Qeq_le (mul_one _))) (Qle_refl _))) ?_
      -- add |e_{m+1}| (add |q−u| |kcorner (m+1)|) ≤ add (Fsum g m) (g (m+1)) = Fsum g (m+1)
      exact Qadd_le_add ih (Qle_refl _)

/-- `0 ≤ acoef m`. -/
theorem acoef_num_nonneg (m : Nat) : 0 ≤ (acoef m).num := by
  unfold acoef; by_cases h : m % 2 = 1
  · rw [if_pos h]; show (0 : Int) ≤ 1; decide
  · rw [if_neg h]; show (0 : Int) ≤ 0; decide

/-- `acoef m ≤ 1`. -/
theorem acoef_le_one (m : Nat) : Qle (acoef m) ⟨1, 1⟩ := by
  unfold acoef; by_cases h : m % 2 = 1
  · rw [if_pos h]
    show (1 : Int) * ((1 : Nat) : Int) ≤ (1 : Int) * ((m : Nat) : Int)
    have hm : 1 ≤ m := by omega
    have h1 : (1 : Int) ≤ ((m : Nat) : Int) := by exact_mod_cast hm
    omega
  · rw [if_neg h]; show (0 : Int) * ((1 : Nat) : Int) ≤ (1 : Int) * ((1 : Nat) : Int); decide

/-- **The `D_N` identity**: `eval(artanh∘kdbl,w,2N+1) − eval(acoef,u,2N+1) = Σ_{m≤2N+1} acoef(m)·(p_m − uᵐ)`. -/
theorem DN_eq (w : Q) (hwd : 0 < w.den) (N : Nat) :
    Qeq (Qsub (peval (fcomp acoef kdbl) w (2 * N + 1)) (peval acoef (uval w) (2 * N + 1)))
      (Fsum (fun m => mul (acoef m)
        (Qsub (peval (fpow kdbl m) w (2 * N + 1)) (qpow (uval w) m))) (2 * N + 1)) := by
  have hpm : ∀ m, 0 < (peval (fpow kdbl m) w (2 * N + 1)).den :=
    fun m => peval_den_pos (fpow_den_pos (fun i => kdbl_den i) m) hwd _
  have hum : ∀ m, 0 < (qpow (uval w) m).den := fun m => qpow_den_pos (uval_den_pos w hwd) m
  refine Qeq_trans (Qsub_den_pos (Fsum_den_pos (fun m => Qmul_den_pos (acoef_den m) (hpm m)) _)
      (peval_den_pos (fun k => acoef_den k) (uval_den_pos w hwd) _))
    (Qsub_congr (peval_fcomp_swap acoef kdbl (fun i => acoef_den i) (fun i => kdbl_den i)
      kdbl_zero w hwd (2 * N + 1)) (Qeq_refl _)) ?_
  refine Qeq_trans (Fsum_den_pos (fun m => Qsub_den_pos (Qmul_den_pos (acoef_den m) (hpm m))
      (Qmul_den_pos (acoef_den m) (hum m))) _)
    (Qeq_symm (Fsum_sub (fun m => Qmul_den_pos (acoef_den m) (hpm m))
      (fun m => Qmul_den_pos (acoef_den m) (hum m)) (2 * N + 1))) ?_
  exact Fsum_congr (fun m => Qeq_symm (Qmul_sub_left_loc (acoef m)
    (peval (fpow kdbl m) w (2 * N + 1)) (qpow (uval w) m))) (2 * N + 1)

/-- **`|D_N|` bound**: `|D_N| ≤ Σ_{m≤2N+1} |p_m − uᵐ|` (since `acoef m ≤ 1`). -/
theorem DN_abs_le (w : Q) (hwd : 0 < w.den) (N : Nat) :
    Qle (Qabs (Qsub (peval (fcomp acoef kdbl) w (2 * N + 1)) (peval acoef (uval w) (2 * N + 1))))
      (Fsum (fun m => Qabs (Qsub (peval (fpow kdbl m) w (2 * N + 1)) (qpow (uval w) m))) (2 * N + 1)) := by
  have hem : ∀ m, 0 < (Qsub (peval (fpow kdbl m) w (2 * N + 1)) (qpow (uval w) m)).den :=
    fun m => Qsub_den_pos (peval_den_pos (fpow_den_pos (fun i => kdbl_den i) m) hwd _)
      (qpow_den_pos (uval_den_pos w hwd) m)
  refine Qle_trans (Qabs_den_pos (Fsum_den_pos (fun m => Qmul_den_pos (acoef_den m) (hem m)) _))
    (Qeq_le (Qabs_Qeq (DN_eq w hwd N))) ?_
  refine Qle_trans (Fsum_den_pos (fun m => Qabs_den_pos (Qmul_den_pos (acoef_den m) (hem m))) _)
    (Fsum_abs_le (fun m => Qmul_den_pos (acoef_den m) (hem m)) _) ?_
  refine Fsum_le_Fsum (fun m => ?_) _
  refine Qle_trans (Qmul_den_pos (Qabs_den_pos (acoef_den m)) (Qabs_den_pos (hem m)))
    (Qeq_le (by rw [Qabs_mul]; exact Qeq_refl _ :
      Qeq (Qabs (mul (acoef m) (Qsub (peval (fpow kdbl m) w (2 * N + 1)) (qpow (uval w) m))))
        (mul (Qabs (acoef m)) (Qabs (Qsub (peval (fpow kdbl m) w (2 * N + 1)) (qpow (uval w) m)))))) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (hem m)))
    (Qmul_le_mul_right (Qabs_num_nonneg _) (Qabs_le_of_nonneg (acoef_num_nonneg m) (acoef_le_one m))) ?_
  exact Qeq_le (Qone_mul _)

/-- `0 ≤ (a+b).num` from non-negative numerators. -/
theorem Qadd_num_nonneg_loc {a b : Q} (ha : 0 ≤ a.num) (hb : 0 ≤ b.num) : 0 ≤ (add a b).num := by
  show 0 ≤ a.num * (b.den : Int) + b.num * (a.den : Int)
  exact Int.add_nonneg (Int.mul_nonneg ha (by exact_mod_cast Nat.zero_le _))
    (Int.mul_nonneg hb (by exact_mod_cast Nat.zero_le _))

/-- `0 ≤ q` (as `Qle ⟨0,1⟩ q`) from `0 ≤ q.num`. -/
theorem Qzero_le_loc {q : Q} (h : 0 ≤ q.num) : Qle (⟨0, 1⟩ : Q) q := by
  show (0 : Int) * (q.den : Int) ≤ q.num * ((1 : Nat) : Int)
  rw [Int.zero_mul]; omega

/-- **Each head term `|p_m − uᵐ| ≤ T`** for `m ≤ 2N+1`, where `T = Σ_{j≤2N+1}(|q−u|+|corner_j|)`. -/
theorem e_le_T (w : Q) (N : Nat) (hwd : 0 < w.den)
    (hq1 : Qle (Qabs (peval kdbl w (2 * N + 1))) ⟨1, 1⟩) (hu1 : Qle (Qabs (uval w)) ⟨1, 1⟩)
    (m : Nat) (hm : m ≤ 2 * N + 1) :
    Qle (Qabs (Qsub (peval (fpow kdbl m) w (2 * N + 1)) (qpow (uval w) m)))
      (Fsum (fun j => add (Qabs (Qsub (peval kdbl w (2 * N + 1)) (uval w)))
        (Qabs (kcorner w j (2 * N + 1)))) (2 * N + 1)) := by
  have hud : 0 < (uval w).den := uval_den_pos w hwd
  have hqd : 0 < (peval kdbl w (2 * N + 1)).den := peval_den_pos (fun i => kdbl_den i) hwd _
  have hqud : 0 < (Qsub (peval kdbl w (2 * N + 1)) (uval w)).den := Qsub_den_pos hqd hud
  have hg0 : ∀ j, 0 ≤ (add (Qabs (Qsub (peval kdbl w (2 * N + 1)) (uval w)))
      (Qabs (kcorner w j (2 * N + 1)))).num :=
    fun j => Qadd_num_nonneg_loc (Qabs_num_nonneg _) (Qabs_num_nonneg _)
  have hgd : ∀ j, 0 < (add (Qabs (Qsub (peval kdbl w (2 * N + 1)) (uval w)))
      (Qabs (kcorner w j (2 * N + 1)))).den :=
    fun j => add_den_pos (Qabs_den_pos hqud) (Qabs_den_pos (kcorner_den w hwd j _))
  cases m with
  | zero =>
    have hp0 : Qeq (peval (fpow kdbl 0) w (2 * N + 1)) ⟨1, 1⟩ := peval_fone w hwd (2 * N + 1)
    have he0 : Qeq (Qabs (Qsub (peval (fpow kdbl 0) w (2 * N + 1)) (qpow (uval w) 0))) ⟨0, 1⟩ := by
      refine Qeq_trans (Qabs_den_pos (Qsub_den_pos Nat.one_pos (qpow_den_pos hud 0)))
        (Qabs_Qeq (Qsub_congr hp0 (Qeq_refl _))) ?_
      show Qeq (Qabs (Qsub (⟨1, 1⟩ : Q) ⟨1, 1⟩)) ⟨0, 1⟩
      decide
    refine Qle_trans Nat.one_pos (Qeq_le he0) ?_
    exact Qzero_le_loc (Fsum_num_nonneg hg0 (2 * N + 1))
  | succ k =>
    refine Qle_trans (Fsum_den_pos hgd k)
      (per_m_bound w (2 * N + 1) hwd hq1 hu1 k) ?_
    exact Fsum_mono_len hg0 hgd (by omega : k ≤ 2 * N + 1)

/-- **`|D_N|` collapsed to a double sum** that `→ 0`:
    `|D_N| ≤ Σ_{m≤2N+1} Σ_{j≤2N+1}(|q−u| + |corner_j|)` (= `(2N+2)·T`). -/
theorem DN_double_le (w : Q) (N : Nat) (hwd : 0 < w.den)
    (hq1 : Qle (Qabs (peval kdbl w (2 * N + 1))) ⟨1, 1⟩) (hu1 : Qle (Qabs (uval w)) ⟨1, 1⟩) :
    Qle (Qabs (Qsub (peval (fcomp acoef kdbl) w (2 * N + 1)) (peval acoef (uval w) (2 * N + 1))))
      (Fsum (fun _ => Fsum (fun j => add (Qabs (Qsub (peval kdbl w (2 * N + 1)) (uval w)))
        (Qabs (kcorner w j (2 * N + 1)))) (2 * N + 1)) (2 * N + 1)) := by
  have hem : ∀ m, 0 < (Qsub (peval (fpow kdbl m) w (2 * N + 1)) (qpow (uval w) m)).den :=
    fun m => Qsub_den_pos (peval_den_pos (fpow_den_pos (fun i => kdbl_den i) m) hwd _)
      (qpow_den_pos (uval_den_pos w hwd) m)
  refine Qle_trans (Fsum_den_pos (fun m => Qabs_den_pos (hem m)) (2 * N + 1))
    (DN_abs_le w hwd N) ?_
  exact Fsum_le_congr (fun m hm => e_le_T w N hwd hq1 hu1 m hm)

/-- **Polynomial-into-geometric absorption**: `(M+1)² ≤ 4ᴹ` for all `M`. This is what lets the
    `(M+1)`-factors in the `D_N` bound be absorbed into a slightly larger geometric base. -/
theorem sq_le_four_pow : ∀ M : Nat, (M + 1) * (M + 1) ≤ 4 ^ M
  | 0 => by decide
  | (M + 1) => by
    have ih := sq_le_four_pow M
    have key : (M + 1 + 1) * (M + 1 + 1) = (M + 1) * (M + 1) + (2 * (M + 1) + 1) := by
      have h : (((M + 1 + 1) * (M + 1 + 1) : Nat) : Int)
          = (((M + 1) * (M + 1) + (2 * (M + 1) + 1) : Nat) : Int) := by push_cast; ring_uor
      exact_mod_cast h
    have h1 : M + 1 ≤ (M + 1) * (M + 1) := by
      calc M + 1 = (M + 1) * 1 := (Nat.mul_one _).symm
        _ ≤ (M + 1) * (M + 1) := Nat.mul_le_mul_left _ (by omega)
    have hpow : 4 ^ (M + 1) = 4 * 4 ^ M := by rw [Nat.pow_succ]; omega
    have hP1 : 1 ≤ 4 ^ M := by
      clear ih key h1 hpow
      induction M with
      | zero => decide
      | succ k ih => rw [Nat.pow_succ]; omega
    omega

/-- **Corner-sum bound** (carrying the `(1−2ρ)` factor): `(Σ_{j≤2N+1}|corner_j|)·(1−2ρ) ≤
    Σ_{j≤2N+1} (2N+2)·2·4ʲ·(2ρ)^{2N+2}` — via `Fsum_mul_const_right` to factor `(1−2ρ)` out, then
    `corner_bound` termwise. -/
theorem corner_sum_bound (ρ w : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hwd : 0 < w.den)
    (hw : Qle (Qabs w) ρ) (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num) (N : Nat) :
    Qle (mul (Fsum (fun j => Qabs (kcorner w j (2 * N + 1))) (2 * N + 1))
          (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ)))
      (Fsum (fun j => Fsum (fun _ => mul (⟨2 * (4 : Int) ^ j, 1⟩ : Q)
        (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2))) (2 * N + 1)) (2 * N + 1)) := by
  have hcd : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).den :=
    Qsub_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos hρd)
  have ha : ∀ j, 0 < (Qabs (kcorner w j (2 * N + 1))).den :=
    fun j => Qabs_den_pos (kcorner_den w hwd j _)
  refine Qle_trans (Fsum_den_pos (fun j => Qmul_den_pos (ha j) hcd) (2 * N + 1))
    (Qeq_le (Fsum_mul_const_right hcd ha (2 * N + 1))) ?_
  exact Fsum_le_congr (fun j _ => corner_bound ρ w hρd hρ0 hwd hw h2ρ j (2 * N + 1))

/-- `(a·c) + c ≈ (a+1)·c`. -/
theorem Qadd_const_mul (a : Int) (c : Q) :
    Qeq (add (mul (⟨a, 1⟩ : Q) c) c) (mul (⟨a + 1, 1⟩ : Q) c) := by
  simp only [Qeq, add, mul]; push_cast; ring_uor

/-- A constant finite sum: `Σ_{i≤M} c = (M+1)·c`. -/
theorem Fsum_const_eq (c : Q) (hcd : 0 < c.den) (M : Nat) :
    Qeq (Fsum (fun _ => c) M) (mul (⟨(M : Int) + 1, 1⟩ : Q) c) := by
  induction M with
  | zero =>
    show Qeq c (mul (⟨((0 : Nat) : Int) + 1, 1⟩ : Q) c)
    simp only [Qeq, mul]; push_cast; ring_uor
  | succ M ih =>
    refine Qeq_trans (add_den_pos (Qmul_den_pos Nat.one_pos hcd) hcd)
      (Qadd_congr ih (Qeq_refl c)) ?_
    simp only [Qeq, add, mul]; push_cast; ring_uor

/-- **Geometric `4ʲ` sum bound**: `Σ_{j≤k} 4ʲ ≤ 4^{k+1}`. -/
theorem pow4_sum_le : ∀ k, Qle (Fsum (fun j => (⟨(4 : Int) ^ j, 1⟩ : Q)) k) (⟨(4 : Int) ^ (k + 1), 1⟩ : Q)
  | 0 => by decide
  | (k + 1) => by
    have hnn : (0 : Int) ≤ (4 : Int) ^ (k + 1) := by
      have h : (4 : Int) ^ (k + 1) = (((4 : Nat) ^ (k + 1) : Nat) : Int) := by push_cast; ring_uor
      rw [h]; exact Int.ofNat_nonneg _
    have hp : (4 : Int) ^ (k + 1 + 1) = 4 * (4 : Int) ^ (k + 1) := by rw [Int.pow_succ]; ring_uor
    refine Qle_trans (add_den_pos Nat.one_pos Nat.one_pos)
      (Qadd_le_add (pow4_sum_le k) (Qle_refl _)) ?_
    show Qle (add (⟨(4 : Int) ^ (k + 1), 1⟩ : Q) (⟨(4 : Int) ^ (k + 1), 1⟩ : Q))
      (⟨(4 : Int) ^ (k + 1 + 1), 1⟩ : Q)
    simp only [Qle, add]
    rw [hp]
    generalize (4 : Int) ^ (k + 1) = A at hnn ⊢
    push_cast
    omega

/-- `A·(E·D) ≈ (A·D)·E` (abstract rearrangement). -/
theorem Qmul_rearr3 (A E D : Q) : Qeq (mul A (mul E D)) (mul (mul A D) E) := by
  simp only [Qeq, mul]; push_cast; ring_uor

/-- **`2·4ʲ` sum bound**: `Σ_{j≤k} 2·4ʲ ≤ 2·4^{k+1}`. -/
theorem pow4_2_sum_le :
    ∀ k, Qle (Fsum (fun j => (⟨2 * (4 : Int) ^ j, 1⟩ : Q)) k) (⟨2 * (4 : Int) ^ (k + 1), 1⟩ : Q)
  | 0 => by decide
  | (k + 1) => by
    have hnn : (0 : Int) ≤ (4 : Int) ^ (k + 1) := by
      have h : (4 : Int) ^ (k + 1) = (((4 : Nat) ^ (k + 1) : Nat) : Int) := by push_cast; ring_uor
      rw [h]; exact Int.ofNat_nonneg _
    have hp : (4 : Int) ^ (k + 1 + 1) = 4 * (4 : Int) ^ (k + 1) := by rw [Int.pow_succ]; ring_uor
    refine Qle_trans (add_den_pos Nat.one_pos Nat.one_pos)
      (Qadd_le_add (pow4_2_sum_le k) (Qle_refl _)) ?_
    show Qle (add (⟨2 * (4 : Int) ^ (k + 1), 1⟩ : Q) (⟨2 * (4 : Int) ^ (k + 1), 1⟩ : Q))
      (⟨2 * (4 : Int) ^ (k + 1 + 1), 1⟩ : Q)
    simp only [Qle, add]
    rw [hp]
    generalize (4 : Int) ^ (k + 1) = A at hnn ⊢
    push_cast
    omega

/-- **Closed corner-sum bound**: `(Σ_{j≤2N+1}|corner_j|)·(1−2ρ) ≤ ((2N+2)·(2ρ)^{2N+2})·(2·4^{2N+2})`. -/
theorem corner_sum_closed (ρ w : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hwd : 0 < w.den)
    (hw : Qle (Qabs w) ρ) (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num) (N : Nat) :
    Qle (mul (Fsum (fun j => Qabs (kcorner w j (2 * N + 1))) (2 * N + 1))
          (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ)))
      (mul (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q) (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2)))
        (⟨2 * (4 : Int) ^ (2 * N + 2), 1⟩ : Q)) := by
  have hQpd : 0 < (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2)).den :=
    qpow_den_pos (Qmul_den_pos Nat.one_pos hρd) (2 * N + 2)
  have h2ρ0 : 0 ≤ (mul ⟨2, 1⟩ ρ).num := by show 0 ≤ 2 * ρ.num; omega
  have hQpnn : 0 ≤ (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2)).num := qpow_nonneg h2ρ0 (2 * N + 2)
  have hcstnn : 0 ≤ (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q).num := by
    have : (0 : Int) ≤ ((2 * N + 1 : Nat) : Int) := Int.ofNat_nonneg _
    show 0 ≤ ((2 * N + 1 : Nat) : Int) + 1; omega
  have hKd : 0 < (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
      (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2))).den := Qmul_den_pos Nat.one_pos hQpd
  have hKnn : 0 ≤ (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
      (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2))).num := Qmul_num_nonneg hcstnn hQpnn
  refine Qle_trans (Fsum_den_pos (fun j =>
      Fsum_den_pos (fun _ => Qmul_den_pos Nat.one_pos hQpd) (2 * N + 1)) (2 * N + 1))
    (corner_sum_bound ρ w hρd hρ0 hwd hw h2ρ N) ?_
  refine Qle_trans (Fsum_den_pos (fun j =>
      Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos hQpd)) (2 * N + 1))
    (Qeq_le (Fsum_congr (fun j => Fsum_const_eq
      (mul (⟨2 * (4 : Int) ^ j, 1⟩ : Q) (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2)))
      (Qmul_den_pos Nat.one_pos hQpd) (2 * N + 1)) (2 * N + 1))) ?_
  refine Qle_trans (Fsum_den_pos (fun j =>
      Qmul_den_pos (Qmul_den_pos Nat.one_pos hQpd) Nat.one_pos) (2 * N + 1))
    (Qeq_le (Fsum_congr (fun j => Qmul_rearr3 (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
      (⟨2 * (4 : Int) ^ j, 1⟩ : Q) (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2))) (2 * N + 1))) ?_
  refine Qle_trans (Qmul_den_pos hKd (Fsum_den_pos
      (f := fun j => (⟨2 * (4 : Int) ^ j, 1⟩ : Q)) (fun _ => Nat.one_pos) (2 * N + 1)))
    (Qeq_le (Fsum_mul_left
      (c := mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q) (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2)))
      (f := fun j => (⟨2 * (4 : Int) ^ j, 1⟩ : Q)) hKd
      (fun _ => Nat.one_pos) (2 * N + 1))) ?_
  exact Qmul_le_mul_left hKnn (pow4_2_sum_le (2 * N + 1))

/-- `a·(c·F) ≈ c·(a·F)` (swap the outer factor inward). -/
theorem Qmul_swap_outer (a c F : Q) : Qeq (mul a (mul c F)) (mul c (mul a F)) := by
  simp only [Qeq, mul]; push_cast; ring_uor

/-- **Divide out a factor `F ≥ 1/2`**: `a·F ≤ B` with `a ≥ 0` gives `a ≤ 2·B`. -/
theorem mul_div2 {a B F : Q} (ha : 0 ≤ a.num) (had : 0 < a.den) (hFd : 0 < F.den) (hBd : 0 < B.den)
    (hF : Qle (⟨1, 2⟩ : Q) F) (hab : Qle (mul a F) B) : Qle a (mul ⟨2, 1⟩ B) := by
  have h2F : Qle (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ F) :=
    Qle_trans (Qmul_den_pos Nat.one_pos (by decide : 0 < (⟨1, 2⟩ : Q).den))
      (by decide : Qle (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ⟨1, 2⟩))
      (Qmul_le_mul_left (by decide) hF)
  have ea : Qeq a (mul a ⟨1, 1⟩) := by simp only [Qeq, mul]; push_cast; ring_uor
  refine Qle_trans (Qmul_den_pos had (Qmul_den_pos Nat.one_pos hFd))
    (Qle_trans (Qmul_den_pos had Nat.one_pos) (Qeq_le ea) (Qmul_le_mul_left ha h2F)) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos had hFd))
    (Qeq_le (Qmul_swap_outer a ⟨2, 1⟩ F)) ?_
  exact Qmul_le_mul_left (by decide) hab

/-- **Corner sum (factor removed)**: `Σ_{j≤2N+1}|corner_j| ≤ 2·((2N+2)·(2ρ)^{2N+2})·(2·4^{2N+2})`
    (for `ρ ≤ 1/4`, so `1−2ρ ≥ 1/2`). -/
theorem corner_sum_final (ρ w : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hwd : 0 < w.den)
    (hw : Qle (Qabs w) ρ) (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hρ4 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ))) (N : Nat) :
    Qle (Fsum (fun j => Qabs (kcorner w j (2 * N + 1))) (2 * N + 1))
      (mul ⟨2, 1⟩ (mul (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q) (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2)))
        (⟨2 * (4 : Int) ^ (2 * N + 2), 1⟩ : Q))) := by
  refine mul_div2 (Fsum_num_nonneg (fun j => Qabs_num_nonneg _) (2 * N + 1))
    (Fsum_den_pos (fun j => Qabs_den_pos (kcorner_den w hwd j _)) (2 * N + 1))
    (Qsub_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos hρd))
    (Qmul_den_pos (Qmul_den_pos Nat.one_pos
      (qpow_den_pos (Qmul_den_pos Nat.one_pos hρd) (2 * N + 2))) Nat.one_pos)
    hρ4 (corner_sum_closed ρ w hρd hρ0 hwd hw h2ρ N)

/-- **`T` bound**: `Σ_{j≤2N+1}(|q−u| + |corner_j|) ≤ (2N+2)·(2ρ^{2N+2}+2ρ^{2N+3}) + 2·(2N+2)(2ρ)^{2N+2}·2·4^{2N+2}`. -/
theorem T_le (ρ w : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hwd : 0 < w.den)
    (hw : Qle (Qabs w) ρ) (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hρ4 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ))) (N : Nat) :
    Qle (Fsum (fun j => add (Qabs (Qsub (peval kdbl w (2 * N + 1)) (uval w)))
          (Qabs (kcorner w j (2 * N + 1)))) (2 * N + 1))
      (add (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
            (add (mul ⟨2, 1⟩ (qpow ρ (2 * N + 2))) (mul ⟨2, 1⟩ (qpow ρ (2 * N + 3)))))
        (mul ⟨2, 1⟩ (mul (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
          (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2))) (⟨2 * (4 : Int) ^ (2 * N + 2), 1⟩ : Q)))) := by
  have hqud : 0 < (Qsub (peval kdbl w (2 * N + 1)) (uval w)).den :=
    Qsub_den_pos (peval_den_pos (fun i => kdbl_den i) hwd _) (uval_den_pos w hwd)
  have hcornerd : ∀ j, 0 < (Qabs (kcorner w j (2 * N + 1))).den :=
    fun j => Qabs_den_pos (kcorner_den w hwd j _)
  have hcstnn : 0 ≤ (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q).num := by
    have : (0 : Int) ≤ ((2 * N + 1 : Nat) : Int) := Int.ofNat_nonneg _
    show 0 ≤ ((2 * N + 1 : Nat) : Int) + 1; omega
  refine Qle_trans (add_den_pos (Fsum_den_pos (fun _ => Qabs_den_pos hqud) _)
      (Fsum_den_pos hcornerd _))
    (Qeq_le (Fsum_add (fun _ => Qabs_den_pos hqud) hcornerd (2 * N + 1))) ?_
  refine Qadd_le_add ?_ (corner_sum_final ρ w hρd hρ0 hwd hw h2ρ hρ4 N)
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos hqud))
    (Qeq_le (Fsum_const_eq (Qabs (Qsub (peval kdbl w (2 * N + 1)) (uval w)))
      (Qabs_den_pos hqud) (2 * N + 1))) ?_
  exact Qmul_le_mul_left hcstnn (q_conv ρ w hρd hwd hw (2 * N))

/-- **`|D_N|` in closed geometric form**: `|D_N| ≤ (2N+2)·T_closed`, the product of the outer `(2N+2)`
    (from `DN_double_le`) and the closed `T` bound (`T_le`). -/
theorem DN_geom_le (ρ w : Q) (N : Nat) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hwd : 0 < w.den)
    (hw : Qle (Qabs w) ρ) (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hρ4 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ)))
    (hq1 : Qle (Qabs (peval kdbl w (2 * N + 1))) ⟨1, 1⟩) (hu1 : Qle (Qabs (uval w)) ⟨1, 1⟩) :
    Qle (Qabs (Qsub (peval (fcomp acoef kdbl) w (2 * N + 1)) (peval acoef (uval w) (2 * N + 1))))
      (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
        (add (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
              (add (mul ⟨2, 1⟩ (qpow ρ (2 * N + 2))) (mul ⟨2, 1⟩ (qpow ρ (2 * N + 3)))))
          (mul ⟨2, 1⟩ (mul (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
            (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2))) (⟨2 * (4 : Int) ^ (2 * N + 2), 1⟩ : Q))))) := by
  have hqud : 0 < (Qsub (peval kdbl w (2 * N + 1)) (uval w)).den :=
    Qsub_den_pos (peval_den_pos (fun i => kdbl_den i) hwd _) (uval_den_pos w hwd)
  have hTd : 0 < (Fsum (fun j => add (Qabs (Qsub (peval kdbl w (2 * N + 1)) (uval w)))
      (Qabs (kcorner w j (2 * N + 1)))) (2 * N + 1)).den :=
    Fsum_den_pos (fun j => add_den_pos (Qabs_den_pos hqud)
      (Qabs_den_pos (kcorner_den w hwd j _))) (2 * N + 1)
  have hCd : 0 < (add (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
        (add (mul ⟨2, 1⟩ (qpow ρ (2 * N + 2))) (mul ⟨2, 1⟩ (qpow ρ (2 * N + 3)))))
      (mul ⟨2, 1⟩ (mul (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
        (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2))) (⟨2 * (4 : Int) ^ (2 * N + 2), 1⟩ : Q)))).den :=
    add_den_pos
      (Qmul_den_pos Nat.one_pos (add_den_pos (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd _))
        (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd _))))
      (Qmul_den_pos Nat.one_pos (Qmul_den_pos (Qmul_den_pos Nat.one_pos
        (qpow_den_pos (Qmul_den_pos Nat.one_pos hρd) _)) Nat.one_pos))
  refine Qle_trans (Fsum_den_pos (fun _ => hTd) (2 * N + 1)) (DN_double_le w N hwd hq1 hu1) ?_
  refine Qle_trans (Fsum_den_pos (fun _ => hCd) (2 * N + 1))
    (Fsum_le_congr (fun _ _ => T_le ρ w hρd hρ0 hwd hw h2ρ hρ4 N)) ?_
  exact Qeq_le (Fsum_const_eq _ hCd (2 * N + 1))

/-- **Exponent halving**: `qpow x (2N) ≈ qpow (x²) N`. -/
theorem qpow_double (x : Q) (hxd : 0 < x.den) :
    ∀ N, Qeq (qpow x (2 * N)) (qpow (mul x x) N)
  | 0 => Qeq_refl _
  | (N + 1) => by
    have e : 2 * (N + 1) = 2 * N + 1 + 1 := by omega
    rw [e]
    show Qeq (mul x (mul x (qpow x (2 * N)))) (mul (mul x x) (qpow (mul x x) N))
    exact Qeq_trans (Qmul_den_pos hxd (Qmul_den_pos hxd (qpow_den_pos (Qmul_den_pos hxd hxd) N)))
      (Qmul_congr (Qeq_refl x) (Qmul_congr (Qeq_refl x) (qpow_double x hxd N)))
      (Qeq_symm (Qmul_assoc x x (qpow (mul x x) N)))

/-- **`qpow` is antitone in the exponent** for `0 ≤ η ≤ 1`: `qpow η (a+d) ≤ qpow η a`. -/
theorem qpow_mono_exp {η : Q} (hη0 : 0 ≤ η.num) (hηd : 0 < η.den) (hη1 : Qle η ⟨1, 1⟩) :
    ∀ a d, Qle (qpow η (a + d)) (qpow η a)
  | a, 0 => Qle_refl _
  | a, (d + 1) => by
    have ih := qpow_mono_exp hη0 hηd hη1 a d
    show Qle (mul η (qpow η (a + d))) (qpow η a)
    refine Qle_trans (qpow_den_pos hηd (a + d))
      (Qle_trans (Qmul_den_pos Nat.one_pos (qpow_den_pos hηd (a + d)))
        (Qmul_le_mul_right (qpow_nonneg hη0 (a + d)) hη1)
        (Qeq_le (Qone_mul _))) ih

/-- `qpow ⟨c,1⟩ k = ⟨cᵏ,1⟩`. -/
theorem qpow_const_nat (c : Int) : ∀ k, Qeq (qpow (⟨c, 1⟩ : Q) k) (⟨c ^ k, 1⟩ : Q)
  | 0 => Qeq_refl _
  | (k + 1) => by
    show Qeq (mul (⟨c, 1⟩ : Q) (qpow ⟨c, 1⟩ k)) ⟨c ^ (k + 1), 1⟩
    refine Qeq_trans (Qmul_den_pos Nat.one_pos Nat.one_pos)
      (Qmul_congr (Qeq_refl _) (qpow_const_nat c k)) ?_
    show Qeq (mul (⟨c, 1⟩ : Q) ⟨c ^ k, 1⟩) ⟨c ^ (k + 1), 1⟩
    simp only [Qeq, mul]; rw [Int.pow_succ]; push_cast; ring_uor

/-- **Geometric constant absorption**: `qpow ρ k · ⟨cᵏ,1⟩ ≈ qpow (ρ·c) k`. -/
theorem qpow_const_combine (c : Int) (ρ : Q) (hρd : 0 < ρ.den) (k : Nat) :
    Qeq (mul (qpow ρ k) (⟨c ^ k, 1⟩ : Q)) (qpow (mul ρ ⟨c, 1⟩) k) := by
  refine Qeq_trans (Qmul_den_pos (qpow_den_pos hρd k) (qpow_den_pos Nat.one_pos k))
    (Qmul_congr (Qeq_refl _) (Qeq_symm (qpow_const_nat c k))) ?_
  exact Qeq_symm (qpow_mul ρ ⟨c, 1⟩ hρd Nat.one_pos k)

/-- `2·Y + 2·Y ≈ 4·Y`. -/
theorem Qadd_2_2_4 (Y : Q) : Qeq (add (mul ⟨2, 1⟩ Y) (mul ⟨2, 1⟩ Y)) (mul ⟨4, 1⟩ Y) := by
  simp only [Qeq, add, mul]; push_cast; ring_uor

/-- `4·Y + 4·Y ≈ 8·Y`. -/
theorem Qadd_4_4_8 (Y : Q) : Qeq (add (mul ⟨4, 1⟩ Y) (mul ⟨4, 1⟩ Y)) (mul ⟨8, 1⟩ Y) := by
  simp only [Qeq, add, mul]; push_cast; ring_uor

/-- `2·(a·(2·Y)) ≈ 4·(a·Y)`. -/
theorem Qmul_2_2_4 (a Y : Q) : Qeq (mul ⟨2, 1⟩ (mul a (mul ⟨2, 1⟩ Y))) (mul ⟨4, 1⟩ (mul a Y)) := by
  simp only [Qeq, mul]; push_cast; ring_uor

/-- `qpow` respects `≈` of the base (local copy). -/
theorem qpow_Qeq_loc {a b : Q} (h : Qeq a b) : ∀ n, Qeq (qpow a n) (qpow b n)
  | 0 => Qeq_refl _
  | (n + 1) => by
    show Qeq (mul a (qpow a n)) (mul b (qpow b n))
    exact Qmul_congr h (qpow_Qeq_loc h n)

set_option maxHeartbeats 1000000 in
/-- **`T_closed` collapsed to one geometric**: `T_closed ≤ 8·(2N+2)·(8ρ)^{2N+2}` (for `0 ≤ ρ ≤ 1`). -/
theorem T_pow_le (ρ : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hρ1 : Qle ρ ⟨1, 1⟩) (N : Nat) :
    Qle (add (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
            (add (mul ⟨2, 1⟩ (qpow ρ (2 * N + 2))) (mul ⟨2, 1⟩ (qpow ρ (2 * N + 3)))))
          (mul ⟨2, 1⟩ (mul (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
            (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2))) (⟨2 * (4 : Int) ^ (2 * N + 2), 1⟩ : Q))))
      (mul ⟨8, 1⟩ (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
        (qpow (mul ρ ⟨8, 1⟩) (2 * N + 2)))) := by
  have h8d : 0 < (mul ρ ⟨8, 1⟩).den := Qmul_den_pos hρd Nat.one_pos
  have hQ8d : 0 < (qpow (mul ρ ⟨8, 1⟩) (2 * N + 2)).den := qpow_den_pos h8d (2 * N + 2)
  have hP2ρd : 0 < (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2)).den :=
    qpow_den_pos (Qmul_den_pos Nat.one_pos hρd) (2 * N + 2)
  have hcstnn : 0 ≤ (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q).num := by
    have : (0 : Int) ≤ ((2 * N + 1 : Nat) : Int) := Int.ofNat_nonneg _
    show 0 ≤ ((2 * N + 1 : Nat) : Int) + 1; omega
  have hbase : Qle ρ (mul ρ ⟨8, 1⟩) :=
    Qle_trans (Qmul_den_pos hρd Nat.one_pos)
      (Qeq_le (Qeq_symm (mul_one ρ))) (Qmul_le_mul_left hρ0 (by decide))
  have hb2 : Qle (qpow ρ (2 * N + 2)) (qpow (mul ρ ⟨8, 1⟩) (2 * N + 2)) :=
    qpow_base_mono hρd h8d hρ0 hbase (2 * N + 2)
  have hb3 : Qle (qpow ρ (2 * N + 3)) (qpow (mul ρ ⟨8, 1⟩) (2 * N + 2)) :=
    Qle_trans (qpow_den_pos hρd (2 * N + 2)) (qpow_mono_exp hρ0 hρd hρ1 (2 * N + 2) 1) hb2
  -- Part 1
  have hinner : Qle (add (mul ⟨2, 1⟩ (qpow ρ (2 * N + 2))) (mul ⟨2, 1⟩ (qpow ρ (2 * N + 3))))
      (mul ⟨4, 1⟩ (qpow (mul ρ ⟨8, 1⟩) (2 * N + 2))) :=
    Qle_trans (add_den_pos (Qmul_den_pos Nat.one_pos hQ8d) (Qmul_den_pos Nat.one_pos hQ8d))
      (Qadd_le_add (Qmul_le_mul_left (by decide) hb2) (Qmul_le_mul_left (by decide) hb3))
      (Qeq_le (Qadd_2_2_4 (qpow (mul ρ ⟨8, 1⟩) (2 * N + 2))))
  have hP1 : Qle (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
        (add (mul ⟨2, 1⟩ (qpow ρ (2 * N + 2))) (mul ⟨2, 1⟩ (qpow ρ (2 * N + 3)))))
      (mul ⟨4, 1⟩ (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
        (qpow (mul ρ ⟨8, 1⟩) (2 * N + 2)))) :=
    Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos hQ8d))
      (Qmul_le_mul_left hcstnn hinner)
      (Qeq_le (Qmul_swap_outer (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q) ⟨4, 1⟩
        (qpow (mul ρ ⟨8, 1⟩) (2 * N + 2))))
  -- Part 2 (exact): bridge (2ρ)^k·⟨2·4^k⟩ ≈ 2·(8ρ)^k
  have hE : Qeq (⟨2 * (4 : Int) ^ (2 * N + 2), 1⟩ : Q) (mul ⟨2, 1⟩ ⟨(4 : Int) ^ (2 * N + 2), 1⟩) := by
    simp only [Qeq, mul]
  have hbq : Qeq (mul (mul ⟨2, 1⟩ ρ) ⟨4, 1⟩) (mul ρ ⟨8, 1⟩) := by
    simp only [Qeq, mul]; push_cast; ring_uor
  have hcombine2 : Qeq (mul (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2)) (⟨2 * (4 : Int) ^ (2 * N + 2), 1⟩ : Q))
      (mul ⟨2, 1⟩ (qpow (mul ρ ⟨8, 1⟩) (2 * N + 2))) := by
    refine Qeq_trans (Qmul_den_pos hP2ρd (Qmul_den_pos Nat.one_pos Nat.one_pos))
      (Qmul_congr (Qeq_refl _) hE) ?_
    refine Qeq_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos hP2ρd Nat.one_pos))
      (Qmul_swap_outer (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2)) ⟨2, 1⟩ ⟨(4 : Int) ^ (2 * N + 2), 1⟩) ?_
    refine Qmul_congr (Qeq_refl _) ?_
    exact Qeq_trans (qpow_den_pos (Qmul_den_pos (Qmul_den_pos Nat.one_pos hρd) Nat.one_pos) _)
      (qpow_const_combine 4 (mul ⟨2, 1⟩ ρ) (Qmul_den_pos Nat.one_pos hρd) (2 * N + 2))
      (qpow_Qeq_loc hbq (2 * N + 2))
  have hP2 : Qle (mul ⟨2, 1⟩ (mul (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
          (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2))) (⟨2 * (4 : Int) ^ (2 * N + 2), 1⟩ : Q)))
      (mul ⟨4, 1⟩ (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
        (qpow (mul ρ ⟨8, 1⟩) (2 * N + 2)))) := by
    apply Qeq_le
    refine Qeq_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos
        (Qmul_den_pos hP2ρd Nat.one_pos)))
      (Qmul_congr (Qeq_refl _) (Qmul_assoc (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
        (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2)) (⟨2 * (4 : Int) ^ (2 * N + 2), 1⟩ : Q))) ?_
    refine Qeq_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos
        (Qmul_den_pos Nat.one_pos hQ8d)))
      (Qmul_congr (Qeq_refl _) (Qmul_congr (Qeq_refl _) hcombine2)) ?_
    exact Qmul_2_2_4 (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q) (qpow (mul ρ ⟨8, 1⟩) (2 * N + 2))
  -- Combine Part1 + Part2
  exact Qle_trans (add_den_pos (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos hQ8d))
      (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos hQ8d)))
    (Qadd_le_add hP1 hP2)
    (Qeq_le (Qadd_4_4_8 (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
      (qpow (mul ρ ⟨8, 1⟩) (2 * N + 2)))))

/-- `2^{2N+2} = 4·4ᴺ`. -/
theorem two_pow_2Nplus2 : ∀ N : Nat, (2 : Nat) ^ (2 * N + 2) = 4 * 4 ^ N
  | 0 => by decide
  | (N + 1) => by
    have e : 2 * (N + 1) + 2 = (2 * N + 2) + 2 := by omega
    rw [e, Nat.pow_add, two_pow_2Nplus2 N, Nat.pow_succ]
    show (4 * 4 ^ N) * 4 = 4 * (4 ^ N * 4)
    omega

/-- `c·(8·(c·Y)) ≈ 8·((c·c)·Y)`. -/
theorem Qmul_8rearr (c Y : Q) :
    Qeq (mul c (mul ⟨8, 1⟩ (mul c Y))) (mul ⟨8, 1⟩ (mul (mul c c) Y)) := by
  simp only [Qeq, mul]; push_cast; ring_uor

set_option maxHeartbeats 1000000 in
/-- **Piece-A endpoint**: `|D_N| ≤ 8·(16ρ)^{2N+2}` (for `0 ≤ ρ ≤ 1`), a pure geometric (no leading poly).
    Feeds `qpow_geom_bound` at `N = R_n` to give the `C/(n+1)` form for the real `Req`. -/
theorem DN_pow_le (ρ w : Q) (N : Nat) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hρ1 : Qle ρ ⟨1, 1⟩)
    (hwd : 0 < w.den) (hw : Qle (Qabs w) ρ) (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hρ4 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ)))
    (hq1 : Qle (Qabs (peval kdbl w (2 * N + 1))) ⟨1, 1⟩) (hu1 : Qle (Qabs (uval w)) ⟨1, 1⟩) :
    Qle (Qabs (Qsub (peval (fcomp acoef kdbl) w (2 * N + 1)) (peval acoef (uval w) (2 * N + 1))))
      (mul ⟨8, 1⟩ (qpow (mul ρ ⟨16, 1⟩) (2 * N + 2))) := by
  have hQ8d : 0 < (qpow (mul ρ ⟨8, 1⟩) (2 * N + 2)).den :=
    qpow_den_pos (Qmul_den_pos hρd Nat.one_pos) (2 * N + 2)
  have hQ8nn : 0 ≤ (qpow (mul ρ ⟨8, 1⟩) (2 * N + 2)).num :=
    qpow_nonneg (Qmul_num_nonneg hρ0 (by decide)) (2 * N + 2)
  have hcstnn : 0 ≤ (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q).num := by
    have : (0 : Int) ≤ ((2 * N + 1 : Nat) : Int) := Int.ofNat_nonneg _
    show 0 ≤ ((2 * N + 1 : Nat) : Int) + 1; omega
  have hTcd : 0 < (add (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
          (add (mul ⟨2, 1⟩ (qpow ρ (2 * N + 2))) (mul ⟨2, 1⟩ (qpow ρ (2 * N + 3)))))
        (mul ⟨2, 1⟩ (mul (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q)
          (qpow (mul ⟨2, 1⟩ ρ) (2 * N + 2))) (⟨2 * (4 : Int) ^ (2 * N + 2), 1⟩ : Q)))).den :=
    add_den_pos
      (Qmul_den_pos Nat.one_pos (add_den_pos (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd _))
        (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd _))))
      (Qmul_den_pos Nat.one_pos (Qmul_den_pos (Qmul_den_pos Nat.one_pos
        (qpow_den_pos (Qmul_den_pos Nat.one_pos hρd) _)) Nat.one_pos))
  -- (2N+2)² ≤ 2^{2N+2}
  have hcst2 : Qle (mul (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q) (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q))
      (⟨(2 : Int) ^ (2 * N + 2), 1⟩ : Q) := by
    have hnat : (2 * N + 2) * (2 * N + 2) ≤ (2 : Nat) ^ (2 * N + 2) := by
      rw [two_pow_2Nplus2 N]
      have hsq := sq_le_four_pow N
      have he : (2 * N + 2) * (2 * N + 2) = 4 * ((N + 1) * (N + 1)) := by
        have h : (((2 * N + 2) * (2 * N + 2) : Nat) : Int)
            = ((4 * ((N + 1) * (N + 1)) : Nat) : Int) := by push_cast; ring_uor
        exact_mod_cast h
      rw [he]; omega
    have hI : (((2 * N + 1 : Nat) : Int) + 1) * (((2 * N + 1 : Nat) : Int) + 1)
        ≤ (2 : Int) ^ (2 * N + 2) := by
      have hc : (((2 * N + 1 : Nat) : Int) + 1) = ((2 * N + 2 : Nat) : Int) := by push_cast; omega
      rw [hc]
      have hh : (((2 * N + 2) * (2 * N + 2) : Nat) : Int) ≤ (((2 : Nat) ^ (2 * N + 2) : Nat) : Int) := by
        exact_mod_cast hnat
      push_cast at hh; exact hh
    show (((2 * N + 1 : Nat) : Int) + 1) * (((2 * N + 1 : Nat) : Int) + 1) * ((1 : Nat) : Int)
      ≤ (2 : Int) ^ (2 * N + 2) * (((1 : Nat) * (1 : Nat) : Nat) : Int)
    calc (((2 * N + 1 : Nat) : Int) + 1) * (((2 * N + 1 : Nat) : Int) + 1) * ((1 : Nat) : Int)
        = (((2 * N + 1 : Nat) : Int) + 1) * (((2 * N + 1 : Nat) : Int) + 1) := by push_cast; ring_uor
      _ ≤ (2 : Int) ^ (2 * N + 2) := hI
      _ = (2 : Int) ^ (2 * N + 2) * (((1 : Nat) * (1 : Nat) : Nat) : Int) := by push_cast; ring_uor
  -- 2^{2N+2}·(8ρ)^{2N+2} = (16ρ)^{2N+2}
  have hcomb : Qeq (mul (⟨(2 : Int) ^ (2 * N + 2), 1⟩ : Q) (qpow (mul ρ ⟨8, 1⟩) (2 * N + 2)))
      (qpow (mul ρ ⟨16, 1⟩) (2 * N + 2)) := by
    refine Qeq_trans (Qmul_den_pos hQ8d Nat.one_pos)
      (mul_comm (⟨(2 : Int) ^ (2 * N + 2), 1⟩ : Q) (qpow (mul ρ ⟨8, 1⟩) (2 * N + 2))) ?_
    refine Qeq_trans (qpow_den_pos (Qmul_den_pos (Qmul_den_pos hρd Nat.one_pos) Nat.one_pos) _)
      (qpow_const_combine 2 (mul ρ ⟨8, 1⟩) (Qmul_den_pos hρd Nat.one_pos) (2 * N + 2)) ?_
    exact qpow_Qeq_loc (by simp only [Qeq, mul]; push_cast; ring_uor :
      Qeq (mul (mul ρ ⟨8, 1⟩) ⟨2, 1⟩) (mul ρ ⟨16, 1⟩)) (2 * N + 2)
  -- chain
  refine Qle_trans (Qmul_den_pos Nat.one_pos hTcd)
    (DN_geom_le ρ w N hρd hρ0 hwd hw h2ρ hρ4 hq1 hu1) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos hQ8d)))
    (Qmul_le_mul_left hcstnn (T_pow_le ρ hρd hρ0 hρ1 N)) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos (Qmul_den_pos Nat.one_pos Nat.one_pos) hQ8d))
    (Qeq_le (Qmul_8rearr (⟨((2 * N + 1 : Nat) : Int) + 1, 1⟩ : Q) (qpow (mul ρ ⟨8, 1⟩) (2 * N + 2)))) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos hQ8d))
    (Qmul_le_mul_left (by decide) (Qmul_le_mul_right hQ8nn hcst2)) ?_
  exact Qeq_le (Qmul_congr (Qeq_refl _) hcomb)

/-- **Geometric ⇒ reciprocal**: for `0 ≤ η < 1` and `n+1 ≤ M`, `qpow η M ≤ η.den/(n+1)`. The bridge from
    `qpow_geom_bound` (denominator linear in `M`) to the `C/(n+1)` form `Req_of_lin_bound` consumes. -/
theorem qpow_le_recip {η : Q} (hη0 : 0 ≤ η.num) (hηd : 0 < η.den) (hlt : η.num.toNat < η.den)
    {M n : Nat} (hMn : n + 1 ≤ M) : Qle (qpow η M) (⟨(η.den : Int), n + 1⟩ : Q) := by
  have hk : 1 ≤ η.den - η.num.toNat := by omega
  have hMk : M * 1 ≤ M * (η.den - η.num.toNat) := Nat.mul_le_mul_left M hk
  have hden : n + 1 ≤ η.den + M * (η.den - η.num.toNat) := by omega
  refine Qle_trans (by omega : 0 < η.den + M * (η.den - η.num.toNat))
    (qpow_geom_bound hη0 hηd (Nat.le_of_lt hlt) M) ?_
  show (η.den : Int) * ((n + 1 : Nat) : Int)
    ≤ (η.den : Int) * ((η.den + M * (η.den - η.num.toNat) : Nat) : Int)
  exact Int.mul_le_mul_of_nonneg_left (by exact_mod_cast hden) (by exact_mod_cast Nat.zero_le η.den)

/-- `2·(2·X) ≈ 4·X`. -/
theorem Qmul_2_2 (X : Q) : Qeq (mul ⟨2, 1⟩ (mul ⟨2, 1⟩ X)) (mul ⟨4, 1⟩ X) := by
  simp only [Qeq, mul]; push_cast; ring_uor

/-- `0 ≤ geoSum ρ N` for `0 ≤ ρ`. -/
theorem geoSum_num_nonneg {ρ : Q} (hρ0 : 0 ≤ ρ.num) : ∀ N, 0 ≤ (geoSum ρ N).num
  | 0 => qpow_nonneg hρ0 _
  | (n + 1) => Qadd_num_nonneg_loc (geoSum_num_nonneg hρ0 n) (qpow_nonneg hρ0 _)

/-- **Uniform partial-sum bound**: `|peval kdbl w (2N+1)| ≤ 1` for all `N` (for `ρ ≤ 1/4`, `|w| ≤ ρ`).
    `|peval| ≤ 2·geoSum ρ N ≤ 4ρ ≤ 1`. This discharges `DN_pow_le`'s `hq1` uniformly in `N`. -/
theorem peval_kdbl_abs_le_one (ρ w : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hwd : 0 < w.den)
    (hw : Qle (Qabs w) ρ) (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
    (hρ8 : Qle (mul ⟨4, 1⟩ ρ) ⟨1, 1⟩) (N : Nat) :
    Qle (Qabs (peval kdbl w (2 * N + 1))) ⟨1, 1⟩ := by
  have h1 : Qle (Qabs (peval kdbl w (2 * N + 1))) (mul ⟨2, 1⟩ (geoSum ρ N)) :=
    Qle_trans (peval_den_pos (fun k => Qabs_den_pos (kdbl_den k)) hρd (2 * N + 1))
      (peval_abs_le_peval_fabs kdbl (fun k => kdbl_den k) w hwd hρd hw (2 * N + 1))
      (Qeq_le (peval_fabs_kdbl_geoSum ρ hρd N))
  have hg : Qle (geoSum ρ N) (mul ⟨2, 1⟩ (qpow ρ 1)) :=
    mul_div2 (geoSum_num_nonneg hρ0 N) (geoSum_den_pos hρd N)
      (Qsub_den_pos Nat.one_pos (Qmul_den_pos hρd hρd)) (qpow_den_pos hρd 1) hρ2
      (geoSum_tel_le ρ hρd hρ0 N)
  refine Qle_trans (Qmul_den_pos Nat.one_pos (geoSum_den_pos hρd N)) h1 ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd 1)))
    (Qmul_le_mul_left (by decide) hg) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd 1))
    (Qeq_le (Qmul_2_2 (qpow ρ 1))) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos hρd)
    (Qeq_le (Qmul_congr (Qeq_refl _) (mul_one ρ))) hρ8

set_option maxHeartbeats 1000000 in
/-- **`|D_N| ≤ (8·ρ.den)/(n+1)`** whenever `n+1 ≤ 2N+2` (for `ρ < 1/16`, `|w| ≤ ρ`). Combines `DN_pow_le`
    (geometric) with `qpow_le_recip` and the uniform `hq1`/`hu1`. This is the per-index input to the real `Req`. -/
theorem DN_recip (ρ w : Q) (N n : Nat) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hρ1 : Qle ρ ⟨1, 1⟩)
    (hwd : 0 < w.den) (hw : Qle (Qabs w) ρ) (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hρ4 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ)))
    (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (hρ8 : Qle (mul ⟨4, 1⟩ ρ) ⟨1, 1⟩)
    (hlt : (mul ρ ⟨16, 1⟩).num.toNat < (mul ρ ⟨16, 1⟩).den) (hMn : n + 1 ≤ 2 * N + 2) :
    Qle (Qabs (Qsub (peval (fcomp acoef kdbl) w (2 * N + 1)) (peval acoef (uval w) (2 * N + 1))))
      (⟨((8 * ρ.den : Nat) : Int), n + 1⟩ : Q) := by
  have h2ρle1 : Qle (mul ⟨2, 1⟩ ρ) ⟨1, 1⟩ :=
    Qle_trans (Qmul_den_pos Nat.one_pos hρd) (Qmul_le_mul_right hρ0 (by decide)) hρ8
  have hu1 : Qle (Qabs (uval w)) ⟨1, 1⟩ :=
    Qle_trans (Qmul_den_pos Nat.one_pos hρd) (uval_abs_le ρ w hwd hw) h2ρle1
  have hq1 := peval_kdbl_abs_le_one ρ w hρd hρ0 hwd hw hρ2 hρ8 N
  have h16d : 0 ≤ (mul ρ ⟨16, 1⟩).num := Qmul_num_nonneg hρ0 (by decide)
  have hdn := DN_pow_le ρ w N hρd hρ0 hρ1 hwd hw h2ρ hρ4 hq1 hu1
  have hrec := qpow_le_recip h16d (Qmul_den_pos hρd Nat.one_pos) hlt hMn
  refine Qle_trans (Qmul_den_pos Nat.one_pos
      (qpow_den_pos (Qmul_den_pos hρd Nat.one_pos) (2 * N + 2))) hdn ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos n))
    (Qmul_le_mul_left (by decide) hrec) ?_
  apply Qeq_le
  simp only [Qeq, mul]; push_cast; ring_uor

/-- `add x x ≈ 2·x`. -/
theorem Qadd_self (x : Q) : Qeq (add x x) (mul ⟨2, 1⟩ x) := by
  simp only [Qeq, add, mul]; push_cast; ring_uor

/-- `⟨a,d⟩ + ⟨b,d⟩ ≈ ⟨a+b,d⟩` (same denominator). -/
theorem Qadd_same_den_loc (a b : Int) (d : Nat) :
    Qeq (add (⟨a, d⟩ : Q) (⟨b, d⟩ : Q)) (⟨a + b, d⟩ : Q) := by
  simp only [Qeq, add]; push_cast; ring_uor

/-- `Rartanh` of a constant rational real (clean wrapper taking the single bound `|v| ≤ ρ`). -/
def RartanhAtQ (v : Q) (hvd : 0 < v.den) (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (hb : Qle (Qabs v) ρ) : Real :=
  Rartanh (ofQ v hvd) ρ hρ0 hρd hlt (fun _ => hb)

/-- The diagonal of `RartanhAtQ` is `artSum v` at the `Rartanh` modulus. -/
theorem RartanhAtQ_seq (v : Q) (hvd : 0 < v.den) (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (hb : Qle (Qabs v) ρ) (j : Nat) :
    (RartanhAtQ v hvd ρ hρ0 hρd hlt hb).seq j = artSum v (Rartanh_R ρ j) := rfl

set_option maxHeartbeats 1000000 in
/-- **⭐ The real artanh doubling (abstract diagonals)**: for reals `X, Y` whose diagonals are
    `artSum w` and `artSum (uval w)` at the `Rartanh σ` modulus, `2·X = Y` (= `Req (Radd X X) Y`),
    via `Req_of_lin_bound` splitting the diagonal gap into the `D`-term (`DN_recip`) and the
    artSum-Cauchy tail (`Y.reg`). Needs `|w| ≤ ρ < 1/16`. -/
theorem Rartanh_double_via (X Y : Real) (w ρ σ : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num)
    (hρ1 : Qle ρ ⟨1, 1⟩) (hwd : 0 < w.den) (hw : Qle (Qabs w) ρ)
    (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hρ4 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ))) (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
    (hρ8 : Qle (mul ⟨4, 1⟩ ρ) ⟨1, 1⟩) (hlt : (mul ρ ⟨16, 1⟩).num.toNat < (mul ρ ⟨16, 1⟩).den)
    (hσd : 0 < σ.den) (huvd : 0 < (uval w).den)
    (hXseq : ∀ j, X.seq j = artSum w (Rartanh_R σ j))
    (hYseq : ∀ j, Y.seq j = artSum (uval w) (Rartanh_R σ j)) :
    Req (Radd X X) Y := by
  refine Req_of_lin_bound (C := 8 * ρ.den + 2) ?_
  intro n
  have hAAd : 0 < ((Radd X X).seq n).den := (Radd X X).den_pos n
  have hBd : 0 < (Y.seq n).den := Y.den_pos n
  have hB1d : 0 < (Y.seq (2 * n + 1)).den := Y.den_pos (2 * n + 1)
  have hMn : n + 1 ≤ 2 * Rartanh_R σ (2 * n + 1) + 2 := by
    have hge : 2 * n + 2 ≤ Rartanh_R σ (2 * n + 1) := by
      unfold Rartanh_R
      have hk : 1 ≤ σ.den * σ.den + 4 * σ.den :=
        Nat.le_trans (by omega : 1 ≤ 4 * σ.den) (Nat.le_add_left _ _)
      calc 2 * n + 2 = 1 * (2 * n + 1 + 1) := by omega
        _ ≤ (σ.den * σ.den + 4 * σ.den) * (2 * n + 1 + 1) := Nat.mul_le_mul_right _ hk
    omega
  have ha2 : Qeq ((Radd X X).seq n)
      (peval (fcomp acoef kdbl) w (2 * Rartanh_R σ (2 * n + 1) + 1)) := by
    have e1 : (Radd X X).seq n
        = add (artSum w (Rartanh_R σ (2 * n + 1))) (artSum w (Rartanh_R σ (2 * n + 1))) := by
      show add (X.seq (2 * n + 1)) (X.seq (2 * n + 1)) = _
      rw [hXseq]
    rw [e1]
    exact Qeq_trans (Qmul_den_pos Nat.one_pos (artSum_den_pos hwd _))
      (Qadd_self (artSum w (Rartanh_R σ (2 * n + 1))))
      (Qeq_symm (dcomp_artSum w hwd (Rartanh_R σ (2 * n + 1))))
  have hb2 : Qeq (Y.seq (2 * n + 1))
      (peval acoef (uval w) (2 * Rartanh_R σ (2 * n + 1) + 1)) := by
    rw [hYseq]
    exact Qeq_symm (peval_acoef_artSum (uval w) huvd (Rartanh_R σ (2 * n + 1)))
  have hab : Qle (Qabs (Qsub ((Radd X X).seq n) (Y.seq (2 * n + 1))))
      (⟨((8 * ρ.den : Nat) : Int), n + 1⟩ : Q) := by
    refine Qle_trans (Qabs_den_pos (Qsub_den_pos
        (peval_den_pos (fun k => Fsum_den_pos
          (fun m => Qmul_den_pos (acoef_den m) (fpow_den_pos (fun i => kdbl_den i) m k)) k) hwd _)
        (peval_den_pos (fun k => acoef_den k) huvd _)))
      (Qeq_le (Qabs_Qeq (Qsub_congr ha2 hb2))) ?_
    exact DN_recip ρ w (Rartanh_R σ (2 * n + 1)) n hρd hρ0 hρ1 hwd hw h2ρ hρ4 hρ2 hρ8 hlt hMn
  have hbc : Qle (Qabs (Qsub (Y.seq (2 * n + 1)) (Y.seq n))) (add (Qbound (2 * n + 1)) (Qbound n)) :=
    Y.reg (2 * n + 1) n
  have hb2n : Qle (Qbound (2 * n + 1)) (Qbound n) := by
    show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((2 * n + 1 + 1 : Nat) : Int)
    rw [Int.one_mul, Int.one_mul]; exact_mod_cast (show n + 1 ≤ 2 * n + 1 + 1 by omega)
  have hstep : Qle (add (Qbound (2 * n + 1)) (Qbound n)) (⟨2, n + 1⟩ : Q) :=
    Qle_trans (add_den_pos (Qbound_den_pos n) (Qbound_den_pos n))
      (Qadd_le_add hb2n (Qle_refl _)) (Qeq_le (Qadd_same_den_loc 1 1 (n + 1)))
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hAAd hB1d))
      (Qabs_den_pos (Qsub_den_pos hB1d hBd)))
    (Qabs_sub_triangle hAAd hB1d hBd) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos n) (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)))
    (Qadd_le_add hab hbc) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n))
    (Qadd_le_add (Qle_refl _) hstep) ?_
  refine Qle_trans (Nat.succ_pos n)
    (Qeq_le (Qadd_same_den_loc ((8 * ρ.den : Nat) : Int) 2 (n + 1))) ?_
  apply Qeq_le; simp only [Qeq]; push_cast; ring_uor

/-- **⭐ The real artanh doubling (rational argument)**: `2·Rartanh(w) = Rartanh(2w/(1+w²))` for rational
    `w` with `|w| ≤ ρ < 1/16`, at `Rartanh`-radius `σ`. -/
theorem Rartanh_double_rat (ρ w σ : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hρ1 : Qle ρ ⟨1, 1⟩)
    (hwd : 0 < w.den) (hw : Qle (Qabs w) ρ) (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hρ4 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ))) (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
    (hρ8 : Qle (mul ⟨4, 1⟩ ρ) ⟨1, 1⟩) (hlt : (mul ρ ⟨16, 1⟩).num.toNat < (mul ρ ⟨16, 1⟩).den)
    (hσ0 : 0 ≤ σ.num) (hσd : 0 < σ.den) (hσlt : σ.num.toNat < σ.den)
    (hbw : Qle (Qabs w) σ) (hbu : Qle (Qabs (uval w)) σ) (huvd : 0 < (uval w).den) :
    Req (Radd (RartanhAtQ w hwd σ hσ0 hσd hσlt hbw) (RartanhAtQ w hwd σ hσ0 hσd hσlt hbw))
      (RartanhAtQ (uval w) huvd σ hσ0 hσd hσlt hbu) :=
  Rartanh_double_via (RartanhAtQ w hwd σ hσ0 hσd hσlt hbw)
    (RartanhAtQ (uval w) huvd σ hσ0 hσd hσlt hbu) w ρ σ hρd hρ0 hρ1 hwd hw h2ρ hρ4 hρ2 hρ8 hlt hσd huvd
    (fun j => RartanhAtQ_seq w hwd σ hσ0 hσd hσlt hbw j)
    (fun j => RartanhAtQ_seq (uval w) huvd σ hσ0 hσd hσlt hbu j)

/-- `0 ≤ geoEvenSum ρ N` for `0 ≤ ρ`. -/
theorem geoEvenSum_num_nonneg {ρ : Q} (hρ0 : 0 ≤ ρ.num) : ∀ N, 0 ≤ (geoEvenSum ρ N).num
  | 0 => qpow_nonneg hρ0 0
  | (n + 1) => Qadd_num_nonneg_loc (geoEvenSum_num_nonneg hρ0 n) (qpow_nonneg hρ0 _)

/-- **Uniform even-geometric bound**: `geoEvenSum ρ N ≤ 2` for all `N` (`ρ ≤ 1/2`, so `1−ρ² ≥ 1/2`).
    From `geoEven_eq` (`E_N·(1−ρ²) = 1 − ρ^{2N+2} ≤ 1`) via `mul_div2`. -/
theorem geoEvenSum_le_two {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (N : Nat) : Qle (geoEvenSum ρ N) ⟨2, 1⟩ := by
  have hsd : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).den := Qsub_den_pos Nat.one_pos (Qmul_den_pos hρd hρd)
  have hab : Qle (mul (geoEvenSum ρ N) (Qsub ⟨1, 1⟩ (mul ρ ρ))) ⟨1, 1⟩ :=
    Qle_trans (add_den_pos (Qmul_den_pos (geoEvenSum_den_pos hρd N) hsd) (qpow_den_pos hρd _))
      (Qle_self_add (qpow_nonneg hρ0 (2 * N + 2)))
      (Qeq_le (geoEven_eq hρd N))
  refine Qle_trans (Qmul_den_pos Nat.one_pos Nat.one_pos)
    (mul_div2 (geoEvenSum_num_nonneg hρ0 N) (geoEvenSum_den_pos hρd N) hsd Nat.one_pos hρ2 hab) ?_
  exact Qeq_le (mul_one ⟨2, 1⟩)

set_option maxHeartbeats 800000 in
/-- **⭐ `Rartanh` argument-congruence**: `Req t t' ⟹ Req (Rartanh t) (Rartanh t')` (same radius `ρ ≤ 1/2`).
    Via `artSum_Lip_le` (argument-Lipschitz) + `geoEvenSum_le_two` (uniform `≤ 2`): the diagonal gap is
    `≤ 2·|t.seq(R_n) − t'.seq(R_n)| ≤ 2·2/(R_n+1) ≤ 4/(n+1)`. Lets real arguments be swapped up to `≈`. -/
theorem Rartanh_congr (t t' : Real) (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
    (hbt : ∀ n, Qle (Qabs (t.seq n)) ρ) (hbt' : ∀ n, Qle (Qabs (t'.seq n)) ρ) (heq : Req t t') :
    Req (Rartanh t ρ hρ0 hρd hlt hbt) (Rartanh t' ρ hρ0 hρd hlt hbt') := by
  refine Req_of_lin_bound (C := 4) ?_
  intro n
  show Qle (Qabs (Qsub (artSum (t.seq (Rartanh_R ρ n)) (Rartanh_R ρ n))
      (artSum (t'.seq (Rartanh_R ρ n)) (Rartanh_R ρ n)))) (⟨(4 : Int), n + 1⟩ : Q)
  have hdiffd : 0 < (Qsub (t.seq (Rartanh_R ρ n)) (t'.seq (Rartanh_R ρ n))).den :=
    Qsub_den_pos (t.den_pos _) (t'.den_pos _)
  refine Qle_trans (Qmul_den_pos (geoEvenSum_den_pos hρd _) (Qabs_den_pos hdiffd))
    (artSum_Lip_le (t.den_pos _) (t'.den_pos _) hρd (hbt _) (hbt' _) (Rartanh_R ρ n)) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos hdiffd))
    (Qmul_le_mul_right (Qabs_num_nonneg _) (geoEvenSum_le_two hρ0 hρd hρ2 (Rartanh_R ρ n))) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos _))
    (Qmul_le_mul_left (by decide) (heq (Rartanh_R ρ n))) ?_
  have hRge : n ≤ Rartanh_R ρ n := by
    unfold Rartanh_R
    have hk : 1 ≤ ρ.den * ρ.den + 4 * ρ.den :=
      Nat.le_trans (by omega : 1 ≤ 4 * ρ.den) (Nat.le_add_left _ _)
    calc n ≤ 1 * (n + 1) := by omega
      _ ≤ (ρ.den * ρ.den + 4 * ρ.den) * (n + 1) := Nat.mul_le_mul_right _ hk
  show (2 * 2 : Int) * ((n + 1 : Nat) : Int) ≤ (4 : Int) * ((1 * (Rartanh_R ρ n + 1) : Nat) : Int)
  push_cast; omega

/-- **Cleared `uval` difference**: `(uval a − uval b)·(1+a²)(1+b²) = 2(a−b)(1−ab)`. -/
theorem uval_diff_cleared (a b : Q) :
    Qeq (mul (Qsub (uval a) (uval b)) (mul (add ⟨1, 1⟩ (mul a a)) (add ⟨1, 1⟩ (mul b b))))
      (mul ⟨2, 1⟩ (mul (Qsub a b) (Qsub ⟨1, 1⟩ (mul a b)))) := by
  simp only [Qeq, uval, mul, add, Qsub, neg]
  push_cast [Int.natAbs_mul_self']
  ring_uor

/-- **`uval` Lipschitz**: `|uval a − uval b| ≤ 4·|a − b|` for `|a|, |b| ≤ ρ ≤ 1`. -/
theorem uval_lip (ρ a b : Q) (hρd : 0 < ρ.den) (hρ1 : Qle ρ ⟨1, 1⟩) (had : 0 < a.den) (hbd : 0 < b.den)
    (ha : Qle (Qabs a) ρ) (hb : Qle (Qabs b) ρ) :
    Qle (Qabs (Qsub (uval a) (uval b))) (mul ⟨4, 1⟩ (Qabs (Qsub a b))) := by
  have hsad : 0 < (add (⟨1, 1⟩ : Q) (mul a a)).den := add_den_pos Nat.one_pos (Qmul_den_pos had had)
  have hsbd : 0 < (add (⟨1, 1⟩ : Q) (mul b b)).den := add_den_pos Nat.one_pos (Qmul_den_pos hbd hbd)
  have hFd : 0 < (mul (add (⟨1, 1⟩ : Q) (mul a a)) (add (⟨1, 1⟩ : Q) (mul b b))).den :=
    Qmul_den_pos hsad hsbd
  have hXd : 0 < (Qsub (uval a) (uval b)).den := Qsub_den_pos (uval_den_pos a had) (uval_den_pos b hbd)
  have haa0 : 0 ≤ (mul a a).num := by show 0 ≤ a.num * a.num; rw [← Int.natAbs_mul_self]; exact Int.ofNat_nonneg _
  have hbb0 : 0 ≤ (mul b b).num := by show 0 ≤ b.num * b.num; rw [← Int.natAbs_mul_self]; exact Int.ofNat_nonneg _
  have hsa1 : Qle (⟨1, 1⟩ : Q) (add ⟨1, 1⟩ (mul a a)) := Qle_self_add haa0
  have hsb1 : Qle (⟨1, 1⟩ : Q) (add ⟨1, 1⟩ (mul b b)) := Qle_self_add hbb0
  have hsann : 0 ≤ (add (⟨1, 1⟩ : Q) (mul a a)).num :=
    Qadd_num_nonneg_loc (by show (0 : Int) ≤ 1; decide) haa0
  have hsbnn : 0 ≤ (add (⟨1, 1⟩ : Q) (mul b b)).num :=
    Qadd_num_nonneg_loc (by show (0 : Int) ≤ 1; decide) hbb0
  have hFnn : 0 ≤ (mul (add (⟨1, 1⟩ : Q) (mul a a)) (add (⟨1, 1⟩ : Q) (mul b b))).num :=
    Qmul_num_nonneg hsann hsbnn
  have hF1 : Qle (⟨1, 1⟩ : Q) (mul (add ⟨1, 1⟩ (mul a a)) (add ⟨1, 1⟩ (mul b b))) :=
    Qle_trans hsad hsa1
      (Qle_trans (Qmul_den_pos hsad Nat.one_pos) (Qeq_le (Qeq_symm (mul_one _)))
        (Qmul_le_mul_left hsann hsb1))
  -- |1 − ab| ≤ 2
  have habab : Qle (Qabs (mul a b)) ⟨1, 1⟩ := by
    rw [Qabs_mul]
    exact Qle_trans (Qmul_den_pos Nat.one_pos Nat.one_pos)
      (Qmul_le_mul (Qabs_den_pos had) Nat.one_pos (Qabs_den_pos hbd) (Qabs_num_nonneg _)
        (Qabs_num_nonneg _) (Qle_trans hρd ha hρ1) (Qle_trans hρd hb hρ1))
      (Qeq_le (mul_one _))
  have hable : Qle (Qabs (Qsub ⟨1, 1⟩ (mul a b))) ⟨2, 1⟩ := by
    refine Qle_trans (add_den_pos (Qabs_den_pos Nat.one_pos) (Qabs_den_pos (Qmul_den_pos had hbd)))
      (Qabs_sub_le_add ⟨1, 1⟩ (mul a b)) ?_
    refine Qle_trans (add_den_pos Nat.one_pos Nat.one_pos)
      (Qadd_le_add (Qeq_le (Qabs_of_nonneg (by decide : (0 : Int) ≤ 1))) habab) ?_
    exact Qeq_le (Qadd_same_den_loc 1 1 1)
  -- |X| ≤ |X|·F
  refine Qle_trans (Qmul_den_pos (Qabs_den_pos hXd) hFd)
    (Qle_trans (Qmul_den_pos (Qabs_den_pos hXd) Nat.one_pos) (Qeq_le (Qeq_symm (mul_one _)))
      (Qmul_le_mul_left (Qabs_num_nonneg _) hF1)) ?_
  -- |X|·F = |X·F| = |2(a−b)(1−ab)|
  have key2 : Qeq (mul (Qabs (Qsub (uval a) (uval b)))
        (mul (add ⟨1, 1⟩ (mul a a)) (add ⟨1, 1⟩ (mul b b))))
      (Qabs (mul (Qsub (uval a) (uval b))
        (mul (add ⟨1, 1⟩ (mul a a)) (add ⟨1, 1⟩ (mul b b))))) := by
    rw [Qabs_mul]; exact Qmul_congr (Qeq_refl _) (Qeq_symm (Qabs_of_nonneg hFnn))
  refine Qle_trans (Qabs_den_pos (Qmul_den_pos Nat.one_pos (Qmul_den_pos (Qsub_den_pos had hbd)
      (Qsub_den_pos Nat.one_pos (Qmul_den_pos had hbd)))))
    (Qeq_le (Qeq_trans (Qabs_den_pos (Qmul_den_pos hXd hFd)) key2
      (Qabs_Qeq (uval_diff_cleared a b)))) ?_
  -- |2(a−b)(1−ab)| ≤ 4|a−b|
  rw [Qabs_mul, Qabs_mul, show Qabs (⟨2, 1⟩ : Q) = ⟨2, 1⟩ from rfl]
  refine Qle_trans (Qmul_den_pos Nat.one_pos
      (Qmul_den_pos (Qabs_den_pos (Qsub_den_pos had hbd)) Nat.one_pos))
    (Qmul_le_mul_left (by decide) (Qmul_le_mul_left (Qabs_num_nonneg _) hable)) ?_
  apply Qeq_le; simp only [Qeq, mul]; push_cast; ring_uor

/-- **`uvalReal t`**: the real `2t/(1+t²)`, with diagonal `uval(t.seq(4n+3))` — the `4n+3` reindex absorbs
    `uval`'s Lipschitz-4 into the regularity modulus (`4·Qbound(4n+3) = Qbound n`). -/
def uvalReal (t : Real) (ρ : Q) (hρd : 0 < ρ.den) (hρ1 : Qle ρ ⟨1, 1⟩)
    (hb : ∀ n, Qle (Qabs (t.seq n)) ρ) : Real where
  seq := fun n => uval (t.seq (4 * n + 3))
  reg := by
    intro m n
    refine Qle_trans (Qmul_den_pos Nat.one_pos
        (Qabs_den_pos (Qsub_den_pos (t.den_pos _) (t.den_pos _))))
      (uval_lip ρ (t.seq (4 * m + 3)) (t.seq (4 * n + 3)) hρd hρ1 (t.den_pos _) (t.den_pos _)
        (hb _) (hb _)) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos
        (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)))
      (Qmul_le_mul_left (by decide) (t.reg (4 * m + 3) (4 * n + 3))) ?_
    apply Qeq_le
    show Qeq (mul ⟨4, 1⟩ (add (Qbound (4 * m + 3)) (Qbound (4 * n + 3))))
      (add (Qbound m) (Qbound n))
    simp only [Qeq, mul, add, Qbound]; push_cast; ring_uor
  den_pos := fun n => uval_den_pos (t.seq (4 * n + 3)) (t.den_pos _)

/-- **artSum depth-Cauchy ⇒ reciprocal**: `|artSum(u,b) − artSum(u,a)| ≤ 2σ.den/(n+1)` for `a ≤ b`,
    `n+1 ≤ 2a+3`, `|u| ≤ σ < 1`, `1/2 ≤ 1−σ²`. (artSum_trunc + mul_div2 + qpow_le_recip.) -/
theorem artSum_depth_recip (u σ : Q) (hud : 0 < u.den) (hσ0 : 0 ≤ σ.num) (hσd : 0 < σ.den)
    (hu : Qle (Qabs u) σ) (hσ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul σ σ)))
    (hσlt : σ.num.toNat < σ.den) {a b n : Nat} (hab : a ≤ b) (hn : n + 1 ≤ 2 * a + 3) :
    Qle (Qabs (Qsub (artSum u b) (artSum u a))) (⟨2 * (σ.den : Int), n + 1⟩ : Q) := by
  have hW : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul σ σ)).num := by
    have h := hσ2; simp only [Qle] at h
    have hd : 0 < (Qsub (⟨1, 1⟩ : Q) (mul σ σ)).den := Qsub_den_pos Nat.one_pos (Qmul_den_pos hσd hσd)
    omega
  have htrunc := artSum_trunc hud hσ0 hσd hu hW hab
  have hd2 := mul_div2 (Qabs_num_nonneg _)
    (Qabs_den_pos (Qsub_den_pos (artSum_den_pos hud b) (artSum_den_pos hud a)))
    (Qsub_den_pos Nat.one_pos (Qmul_den_pos hσd hσd)) (qpow_den_pos hσd _) hσ2 htrunc
  refine Qle_trans (Qmul_den_pos Nat.one_pos (qpow_den_pos hσd _)) hd2 ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos n))
    (Qmul_le_mul_left (by decide) (qpow_le_recip hσ0 hσd hσlt hn)) ?_
  apply Qeq_le; simp only [Qeq, mul]; push_cast; ring_uor

/-- **D-term ⇒ reciprocal**: `|2·artSum(w,R) − artSum(uval w,R)| ≤ 8ρ.den/(n+1)` for `|w| ≤ ρ < 1/16`,
    `n+1 ≤ 2R+2`. (Qadd_self + dcomp_artSum + peval_acoef_artSum + DN_recip.) -/
theorem Dterm_recip (ρ w : Q) (R n : Nat) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (hρ1 : Qle ρ ⟨1, 1⟩)
    (hwd : 0 < w.den) (hw : Qle (Qabs w) ρ) (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hρ4 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ))) (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
    (hρ8 : Qle (mul ⟨4, 1⟩ ρ) ⟨1, 1⟩) (hlt : (mul ρ ⟨16, 1⟩).num.toNat < (mul ρ ⟨16, 1⟩).den)
    (hMn : n + 1 ≤ 2 * R + 2) :
    Qle (Qabs (Qsub (add (artSum w R) (artSum w R)) (artSum (uval w) R)))
      (⟨((8 * ρ.den : Nat) : Int), n + 1⟩ : Q) := by
  have huvd := uval_den_pos w hwd
  have ha2 : Qeq (add (artSum w R) (artSum w R)) (peval (fcomp acoef kdbl) w (2 * R + 1)) :=
    Qeq_trans (Qmul_den_pos Nat.one_pos (artSum_den_pos hwd R)) (Qadd_self (artSum w R))
      (Qeq_symm (dcomp_artSum w hwd R))
  have hb2 : Qeq (artSum (uval w) R) (peval acoef (uval w) (2 * R + 1)) :=
    Qeq_symm (peval_acoef_artSum (uval w) huvd R)
  refine Qle_trans (Qabs_den_pos (Qsub_den_pos
      (peval_den_pos (fun k => Fsum_den_pos
        (fun m => Qmul_den_pos (acoef_den m) (fpow_den_pos (fun i => kdbl_den i) m k)) k) hwd _)
      (peval_den_pos (fun k => acoef_den k) huvd _)))
    (Qeq_le (Qabs_Qeq (Qsub_congr ha2 hb2))) ?_
  exact DN_recip ρ w R n hρd hρ0 hρ1 hwd hw h2ρ hρ4 hρ2 hρ8 hlt hMn

/-- **artSum arg-variation (via uval)**: `|artSum(uval w,M) − artSum(uval w',M)| ≤ 8·|w − w'|` for
    `|uval w|, |uval w'| ≤ σ ≤ 1/2`, `|w|, |w'| ≤ ρ ≤ 1`. (artSum_Lip_le + geoEvenSum_le_two + uval_lip.) -/
theorem artSum_uval_argdiff (ρ σ w w' : Q) (hρd : 0 < ρ.den) (hρ1 : Qle ρ ⟨1, 1⟩) (hσ0 : 0 ≤ σ.num)
    (hσd : 0 < σ.den) (hσ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul σ σ))) (hwd : 0 < w.den) (hw'd : 0 < w'.den)
    (hw : Qle (Qabs w) ρ) (hw' : Qle (Qabs w') ρ) (huσ : Qle (Qabs (uval w)) σ)
    (hu'σ : Qle (Qabs (uval w')) σ) (M : Nat) :
    Qle (Qabs (Qsub (artSum (uval w) M) (artSum (uval w') M))) (mul ⟨8, 1⟩ (Qabs (Qsub w w'))) := by
  refine Qle_trans (Qmul_den_pos (geoEvenSum_den_pos hσd M)
      (Qabs_den_pos (Qsub_den_pos (uval_den_pos w hwd) (uval_den_pos w' hw'd))))
    (artSum_Lip_le (uval_den_pos w hwd) (uval_den_pos w' hw'd) hσd huσ hu'σ M) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos
      (Qabs_den_pos (Qsub_den_pos (uval_den_pos w hwd) (uval_den_pos w' hw'd))))
    (Qmul_le_mul_right (Qabs_num_nonneg _) (geoEvenSum_le_two hσ0 hσd hσ2 M)) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos
      (Qabs_den_pos (Qsub_den_pos hwd hw'd))))
    (Qmul_le_mul_left (by decide) (uval_lip ρ w w' hρd hρ1 hwd hw'd hw hw')) ?_
  apply Qeq_le; simp only [Qeq, mul]; push_cast; ring_uor

set_option maxHeartbeats 1200000 in
/-- **⭐ The real artanh doubling (real argument)**: for a real `t` with `|t.seq m| ≤ ρ < 1/16` and abstract
    diagonals `X = Rartanh t`, `Y = Rartanh (uvalReal t)` (at radius `σ`, `2ρ ≤ σ ≤ 1/2`), `2·X = Y`. Via
    `Req_of_lin_bound` and the 3-way split of the diagonal gap (D-term `Dterm_recip`, depth-Cauchy
    `artSum_depth_recip`, arg-variation `artSum_uval_argdiff` + `t.reg`). The doubling at real arguments. -/
theorem Rartanh_double_real_via (t X Y : Real) (ρ σ : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num)
    (hρ1 : Qle ρ ⟨1, 1⟩) (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hρ4 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ))) (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
    (hρ8 : Qle (mul ⟨4, 1⟩ ρ) ⟨1, 1⟩) (hlt : (mul ρ ⟨16, 1⟩).num.toNat < (mul ρ ⟨16, 1⟩).den)
    (hσ0 : 0 ≤ σ.num) (hσd : 0 < σ.den) (hσ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul σ σ)))
    (hσlt : σ.num.toNat < σ.den) (hbtρ : ∀ m, Qle (Qabs (t.seq m)) ρ)
    (hbu : ∀ m, Qle (Qabs (uval (t.seq m))) σ)
    (hXseq : ∀ j, X.seq j = artSum (t.seq (Rartanh_R σ j)) (Rartanh_R σ j))
    (hYseq : ∀ j, Y.seq j = artSum (uval (t.seq (4 * Rartanh_R σ j + 3))) (Rartanh_R σ j)) :
    Req (Radd X X) Y := by
  -- index facts (Rartanh_R σ j = (σ.den²+4σ.den)(j+1))
  have hk : 1 ≤ σ.den * σ.den + 4 * σ.den :=
    Nat.le_trans (by omega : 1 ≤ 4 * σ.den) (Nat.le_add_left _ _)
  have hRge : ∀ j, j + 1 ≤ Rartanh_R σ j := by
    intro j; unfold Rartanh_R
    calc j + 1 = 1 * (j + 1) := by omega
      _ ≤ (σ.den * σ.den + 4 * σ.den) * (j + 1) := Nat.mul_le_mul_right _ hk
  have hmono : ∀ {i j}, i ≤ j → Rartanh_R σ i ≤ Rartanh_R σ j := by
    intro i j hij; unfold Rartanh_R; exact Nat.mul_le_mul_left _ (by omega)
  refine Req_of_lin_bound (C := 8 * ρ.den + 2 * σ.den + 16) ?_
  intro n
  have htd : ∀ m, 0 < (t.seq m).den := fun m => t.den_pos m
  have hud : ∀ m, 0 < (uval (t.seq m)).den := fun m => uval_den_pos _ (htd m)
  -- the four diagonal points
  have hae : (Radd X X).seq n
      = add (artSum (t.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1)))
          (artSum (t.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1))) := by
    show add (X.seq (2 * n + 1)) (X.seq (2 * n + 1)) = _; rw [hXseq]
  rw [hae, hYseq n]
  -- index conditions
  have hMn1 : n + 1 ≤ 2 * Rartanh_R σ (2 * n + 1) + 2 := by have := hRge (2 * n + 1); omega
  have hn2 : n + 1 ≤ 2 * Rartanh_R σ n + 3 := by have := hRge n; omega
  have hRnR : Rartanh_R σ n ≤ Rartanh_R σ (2 * n + 1) := hmono (by omega)
  -- the three term bounds
  have hT1 := Dterm_recip ρ (t.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1)) n
    hρd hρ0 hρ1 (htd _) (hbtρ _) h2ρ hρ4 hρ2 hρ8 hlt hMn1
  have hT2 := artSum_depth_recip (uval (t.seq (Rartanh_R σ (2 * n + 1)))) σ (hud _) hσ0 hσd
    (hbu _) hσ2 hσlt hRnR hn2
  have hT3 : Qle (Qabs (Qsub (artSum (uval (t.seq (Rartanh_R σ (2 * n + 1)))) (Rartanh_R σ n))
        (artSum (uval (t.seq (4 * Rartanh_R σ n + 3))) (Rartanh_R σ n)))) (⟨16, n + 1⟩ : Q) := by
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos (htd _) (htd _))))
      (artSum_uval_argdiff ρ σ (t.seq (Rartanh_R σ (2 * n + 1))) (t.seq (4 * Rartanh_R σ n + 3))
        hρd hρ1 hσ0 hσd hσ2 (htd _) (htd _) (hbtρ _) (hbtρ _) (hbu _) (hbu _) (Rartanh_R σ n)) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)))
      (Qmul_le_mul_left (by decide) (t.reg (Rartanh_R σ (2 * n + 1)) (4 * Rartanh_R σ n + 3))) ?_
    -- 8·(Qbound R + Qbound (4 Rn+3)) ≤ ⟨16, n+1⟩
    have hR1 : Qle (Qbound (Rartanh_R σ (2 * n + 1))) (Qbound n) := by
      show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((Rartanh_R σ (2 * n + 1) + 1 : Nat) : Int)
      have := hRge (2 * n + 1); rw [Int.one_mul, Int.one_mul]
      exact_mod_cast (show n + 1 ≤ Rartanh_R σ (2 * n + 1) + 1 by omega)
    have hR2 : Qle (Qbound (4 * Rartanh_R σ n + 3)) (Qbound n) := by
      show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((4 * Rartanh_R σ n + 3 + 1 : Nat) : Int)
      have := hRge n; rw [Int.one_mul, Int.one_mul]
      exact_mod_cast (show n + 1 ≤ 4 * Rartanh_R σ n + 3 + 1 by omega)
    refine Qle_trans (Qmul_den_pos Nat.one_pos (add_den_pos (Qbound_den_pos n) (Qbound_den_pos n)))
      (Qmul_le_mul_left (by decide) (Qadd_le_add hR1 hR2)) ?_
    apply Qeq_le; show Qeq (mul ⟨8, 1⟩ (add (Qbound n) (Qbound n))) (⟨16, n + 1⟩ : Q)
    simp only [Qeq, mul, add, Qbound]; push_cast; ring_uor
  -- combine via two triangles
  have hp1d : 0 < (artSum (uval (t.seq (Rartanh_R σ (2 * n + 1)))) (Rartanh_R σ (2 * n + 1))).den :=
    artSum_den_pos (hud _) _
  have hp2d : 0 < (artSum (uval (t.seq (Rartanh_R σ (2 * n + 1)))) (Rartanh_R σ n)).den :=
    artSum_den_pos (hud _) _
  have had : 0 < (add (artSum (t.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1)))
      (artSum (t.seq (Rartanh_R σ (2 * n + 1))) (Rartanh_R σ (2 * n + 1)))).den :=
    add_den_pos (artSum_den_pos (htd _) _) (artSum_den_pos (htd _) _)
  have hcd : 0 < (artSum (uval (t.seq (4 * Rartanh_R σ n + 3))) (Rartanh_R σ n)).den :=
    artSum_den_pos (hud _) _
  have hpc : Qle (Qabs (Qsub (artSum (uval (t.seq (Rartanh_R σ (2 * n + 1)))) (Rartanh_R σ (2 * n + 1)))
        (artSum (uval (t.seq (4 * Rartanh_R σ n + 3))) (Rartanh_R σ n))))
      (add (⟨2 * (σ.den : Int), n + 1⟩ : Q) (⟨16, n + 1⟩ : Q)) :=
    Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hp1d hp2d))
        (Qabs_den_pos (Qsub_den_pos hp2d hcd)))
      (Qabs_sub_triangle hp1d hp2d hcd) (Qadd_le_add hT2 hT3)
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos had hp1d))
      (Qabs_den_pos (Qsub_den_pos hp1d hcd)))
    (Qabs_sub_triangle had hp1d hcd) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos n) (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n)))
    (Qadd_le_add hT1 hpc) ?_
  -- ⟨8ρ.den,n+1⟩ + (⟨2σ.den,n+1⟩ + ⟨16,n+1⟩) ≤ ⟨8ρ.den+2σ.den+16, n+1⟩
  refine Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n))
    (Qadd_le_add (Qle_refl _) (Qeq_le (Qadd_same_den_loc (2 * (σ.den : Int)) 16 (n + 1)))) ?_
  refine Qle_trans (Nat.succ_pos n)
    (Qeq_le (Qadd_same_den_loc ((8 * ρ.den : Nat) : Int) (2 * (σ.den : Int) + 16) (n + 1))) ?_
  apply Qeq_le; simp only [Qeq]; push_cast; ring_uor

/-- **`Q` left-cancellation**: `c·A ≈ c·B` with `0 < c.num`, `0 < c.den` gives `A ≈ B`. -/
theorem Qmul_cancel_left {c A B : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (h : Qeq (mul c A) (mul c B)) : Qeq A B := by
  have hP : (0 : Int) < c.num * (c.den : Int) := Int.mul_pos hcn (by exact_mod_cast hcd)
  simp only [Qeq, mul] at h
  simp only [Qeq]
  refine Int.eq_of_mul_eq_mul_left (a := c.num * (c.den : Int)) (by omega) ?_
  rw [show (c.num * (c.den : Int)) * (A.num * (B.den : Int))
        = (c.num * A.num) * ((c.den * B.den : Nat) : Int) from by push_cast; ring_uor,
    show (c.num * (c.den : Int)) * (B.num * (A.den : Int))
        = (c.num * B.num) * ((c.den * A.den : Nat) : Int) from by push_cast; ring_uor]
  exact h

/-- The core polynomial identity behind `tmap_sq_uval` (fresh `Int` vars, to dodge the cast-reifier
    issue `ring_uor` hits on the `↑y.den` form). -/
theorem tmap_uval_core (a d : Int) :
    (1 * (d * 1 * (a * 1 + 1 * d) * (d * 1 * (a * 1 + 1 * d))) +
          (a * 1 + -1 * d) * (d * 1) * ((a * 1 + -1 * d) * (d * 1)) * 1) *
        ((a * a * 1 + -1 * (d * d)) * (d * d * 1)) *
      (1 * (d * 1 * (a * 1 + 1 * d))) =
    2 * ((a * 1 + -1 * d) * (d * 1)) *
      (1 * (d * 1 * (a * 1 + 1 * d) * (d * 1 * (a * 1 + 1 * d))) *
        (d * d * 1 * (a * a * 1 + 1 * (d * d)))) := by ring_uor

/-- **The `tmap`–`uval` doubling identity**: `tmap(y²) = uval(tmap y)`. Cleared `(1+t²)·tmap(y²) = 2t` +
    `uval_rel` uniqueness, via `Qmul_cancel_left`. Needs `y+1 > 0`, `y²+1 > 0`. -/
theorem tmap_sq_uval (y : Q) (hyd : 0 < y.den) (hy1 : 0 < (add y ⟨1, 1⟩).num)
    (hy2 : 0 < (add (mul y y) ⟨1, 1⟩).num) :
    Qeq (tmap (mul y y)) (uval (tmap y)) := by
  have htd : 0 < (tmap y).den := Qmul_den_pos (Qsub_den_pos hyd Nat.one_pos) (Qinv_den_pos hy1)
  have ht2n : 0 ≤ (mul (tmap y) (tmap y)).num := by
    show 0 ≤ (tmap y).num * (tmap y).num; rw [← Int.natAbs_mul_self]; exact Int.ofNat_nonneg _
  have hcn : 0 < (add ⟨1, 1⟩ (mul (tmap y) (tmap y))).num := by
    show 0 < 1 * ((mul (tmap y) (tmap y)).den : Int) + (mul (tmap y) (tmap y)).num * 1
    have hd : (0 : Int) < ((mul (tmap y) (tmap y)).den : Int) := by
      exact_mod_cast Qmul_den_pos htd htd
    omega
  have hcd : 0 < (add ⟨1, 1⟩ (mul (tmap y) (tmap y))).den :=
    add_den_pos Nat.one_pos (Qmul_den_pos htd htd)
  have rel1 : Qeq (mul (add ⟨1, 1⟩ (mul (tmap y) (tmap y))) (tmap (mul y y)))
      (mul ⟨2, 1⟩ (tmap y)) := by
    have hy1c := hy1; have hy2c := hy2
    simp only [mul, add] at hy1c hy2c
    push_cast at hy1c hy2c
    simp only [tmap, mul, add, Qsub, neg, Qinv, Qeq]
    push_cast [Int.toNat_of_nonneg (Int.le_of_lt hy1c), Int.toNat_of_nonneg (Int.le_of_lt hy2c)]
    exact tmap_uval_core y.num (y.den : Int)
  exact Qmul_cancel_left hcn hcd
    (Qeq_trans (Qmul_den_pos Nat.one_pos htd) rel1 (Qeq_symm (uval_rel (tmap y) htd)))

/-- **`tmap` Lipschitz**: `|tmap a − tmap b| ≤ 2·|a − b|` for `a+1, b+1 ≥ 1` (i.e. `a, b ≥ 0`). From
    `tmap_diff_cleared` ((tmap a − tmap b)·(a+1)(b+1) = 2(a−b)), since `(a+1)(b+1) ≥ 1`. -/
theorem tmap_lip (a b : Q) (had : 0 < a.den) (hbd : 0 < b.den) (ha1 : 0 < (add a ⟨1, 1⟩).num)
    (hb1 : 0 < (add b ⟨1, 1⟩).num) (hage : Qle ⟨1, 1⟩ (add a ⟨1, 1⟩))
    (hbge : Qle ⟨1, 1⟩ (add b ⟨1, 1⟩)) :
    Qle (Qabs (Qsub (tmap a) (tmap b))) (mul ⟨2, 1⟩ (Qabs (Qsub a b))) := by
  have hXd : 0 < (Qsub (tmap a) (tmap b)).den :=
    Qsub_den_pos (Qmul_den_pos (Qsub_den_pos had Nat.one_pos) (Qinv_den_pos ha1))
      (Qmul_den_pos (Qsub_den_pos hbd Nat.one_pos) (Qinv_den_pos hb1))
  have hsad : 0 < (add a ⟨1, 1⟩).den := add_den_pos had Nat.one_pos
  have hsbd : 0 < (add b ⟨1, 1⟩).den := add_den_pos hbd Nat.one_pos
  have hFd : 0 < (mul (add a ⟨1, 1⟩) (add b ⟨1, 1⟩)).den := Qmul_den_pos hsad hsbd
  have hFnn : 0 ≤ (mul (add a ⟨1, 1⟩) (add b ⟨1, 1⟩)).num :=
    Qmul_num_nonneg (Int.le_of_lt ha1) (Int.le_of_lt hb1)
  have hF1 : Qle (⟨1, 1⟩ : Q) (mul (add a ⟨1, 1⟩) (add b ⟨1, 1⟩)) :=
    Qle_trans hsad hage
      (Qle_trans (Qmul_den_pos hsad Nat.one_pos) (Qeq_le (Qeq_symm (mul_one _)))
        (Qmul_le_mul_left (Int.le_of_lt ha1) hbge))
  have key2 : Qeq (mul (Qabs (Qsub (tmap a) (tmap b))) (mul (add a ⟨1, 1⟩) (add b ⟨1, 1⟩)))
      (Qabs (mul (Qsub (tmap a) (tmap b)) (mul (add a ⟨1, 1⟩) (add b ⟨1, 1⟩)))) := by
    rw [Qabs_mul]; exact Qmul_congr (Qeq_refl _) (Qeq_symm (Qabs_of_nonneg hFnn))
  refine Qle_trans (Qmul_den_pos (Qabs_den_pos hXd) hFd)
    (Qle_trans (Qmul_den_pos (Qabs_den_pos hXd) Nat.one_pos) (Qeq_le (Qeq_symm (mul_one _)))
      (Qmul_le_mul_left (Qabs_num_nonneg _) hF1)) ?_
  refine Qle_trans (Qabs_den_pos (Qmul_den_pos Nat.one_pos (Qsub_den_pos had hbd)))
    (Qeq_le (Qeq_trans (Qabs_den_pos (Qmul_den_pos hXd hFd)) key2
      (Qabs_Qeq (tmap_diff_cleared had hbd ha1 hb1)))) ?_
  rw [Qabs_mul, show Qabs (⟨2, 1⟩ : Q) = ⟨2, 1⟩ from rfl]
  exact Qle_refl _

/-- **(a) the two `Rartanh` arguments of the log-doubling agree** — `tmap((Y²).seq) ≈ uval(tmap(Y.seq))`
    pointwise, i.e. the `t`-real of `Y²` equals `uvalReal` of the `t`-real of `Y`. Per index: rewrite
    `tmap((Y²).seq) = tmap((Y.seq R₂)²) ≈ uval(tmap(Y.seq R₂))` (`tmap_sq_uval`), then
    `|uval(tmap(Y.seq R₂)) − uval(tmap(Y.seq R₃))| ≤ 4·2·|Y.seq R₂ − Y.seq R₃| ≤ 16/(n+1)` via
    `uval_lip`, `tmap_lip`, `Y`-regularity, `Ridx_ge`. `ρ` bounds `tmap(Y.seq ·)` (`= ρ_M` from `Rlog`). -/
theorem tsq_uvalReal_via (Y tY2 uY : Real) (ρ : Q) (hρd : 0 < ρ.den) (hρ1 : Qle ρ ⟨1, 1⟩)
    (hYpos : ∀ n, 0 < (Y.seq n).num) (hbt : ∀ m, Qle (Qabs (tmap (Y.seq m))) ρ)
    (htY2seq : ∀ n, tY2.seq n = tmap ((Rmul Y Y).seq (Rlog_R n)))
    (huYseq : ∀ n, uY.seq n = uval (tmap (Y.seq (Rlog_R (4 * n + 3))))) :
    Req tY2 uY := by
  have hYd : ∀ m, 0 < (Y.seq m).den := fun m => Y.den_pos m
  have hca : ∀ m, 0 < (add (Y.seq m) ⟨1, 1⟩).num := by
    intro m; have h := hYpos m; have h2 := Int.ofNat_nonneg (Y.seq m).den
    show 0 < (Y.seq m).num * 1 + 1 * ((Y.seq m).den : Int); omega
  have hcge : ∀ m, Qle (⟨1, 1⟩ : Q) (add (Y.seq m) ⟨1, 1⟩) := by
    intro m; have h := hYpos m; have h2 := Int.ofNat_nonneg (Y.seq m).den
    simp only [Qle, add, mul]; push_cast; omega
  have hca2 : ∀ m, 0 < (add (mul (Y.seq m) (Y.seq m)) ⟨1, 1⟩).num := by
    intro m
    have h1 : 0 ≤ (Y.seq m).num * (Y.seq m).num := by
      rw [← Int.natAbs_mul_self]; exact Int.ofNat_nonneg _
    have h2 : 0 < (((Y.seq m).den * (Y.seq m).den : Nat) : Int) := by
      exact_mod_cast Nat.mul_pos (hYd m) (hYd m)
    show 0 < (Y.seq m).num * (Y.seq m).num * 1 + 1 * (((Y.seq m).den * (Y.seq m).den : Nat) : Int)
    omega
  have htmd : ∀ m, 0 < (tmap (Y.seq m)).den := fun m =>
    Qmul_den_pos (Qsub_den_pos (hYd m) Nat.one_pos) (Qinv_den_pos (hca m))
  refine Req_of_lin_bound (C := 16) ?_
  intro n
  rw [htY2seq n, huYseq n]
  show Qle (Qabs (Qsub (tmap (mul (Y.seq (Ridx Y Y (Rlog_R n))) (Y.seq (Ridx Y Y (Rlog_R n)))))
      (uval (tmap (Y.seq (Rlog_R (4 * n + 3))))))) (⟨16, n + 1⟩ : Q)
  -- Step A: tmap(mul a a) ≈ uval(tmap a)
  refine Qle_trans (Qabs_den_pos (Qsub_den_pos (uval_den_pos _ (htmd _)) (uval_den_pos _ (htmd _))))
    (Qeq_le (Qabs_Qeq (Qsub_congr
      (tmap_sq_uval (Y.seq (Ridx Y Y (Rlog_R n))) (hYd _) (hca _) (hca2 _)) (Qeq_refl _)))) ?_
  -- Step B: uval_lip (radius ρ)
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos (htmd _) (htmd _))))
    (uval_lip ρ (tmap (Y.seq (Ridx Y Y (Rlog_R n)))) (tmap (Y.seq (Rlog_R (4 * n + 3))))
      hρd hρ1 (htmd _) (htmd _) (hbt _) (hbt _)) ?_
  -- Step C: tmap_lip
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos
      (Qabs_den_pos (Qsub_den_pos (hYd _) (hYd _)))))
    (Qmul_le_mul_left (by decide) (tmap_lip (Y.seq (Ridx Y Y (Rlog_R n)))
      (Y.seq (Rlog_R (4 * n + 3))) (hYd _) (hYd _) (hca _) (hca _) (hcge _) (hcge _))) ?_
  -- Step D: Y-regularity
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos
      (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))))
    (Qmul_le_mul_left (by decide) (Qmul_le_mul_left (by decide)
      (Y.reg (Ridx Y Y (Rlog_R n)) (Rlog_R (4 * n + 3))))) ?_
  -- Step E: Qbound bounds + final equality
  have hR2 : Qle (Qbound (Ridx Y Y (Rlog_R n))) (Qbound n) := by
    show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((Ridx Y Y (Rlog_R n) + 1 : Nat) : Int)
    have hge := Ridx_ge Y Y (Rlog_R n)
    have hr : n ≤ Rlog_R n := by unfold Rlog_R; omega
    rw [Int.one_mul, Int.one_mul]; exact_mod_cast (show n + 1 ≤ Ridx Y Y (Rlog_R n) + 1 by omega)
  have hR3 : Qle (Qbound (Rlog_R (4 * n + 3))) (Qbound n) := by
    show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((Rlog_R (4 * n + 3) + 1 : Nat) : Int)
    have hr : n ≤ Rlog_R (4 * n + 3) := by unfold Rlog_R; omega
    rw [Int.one_mul, Int.one_mul]; exact_mod_cast (show n + 1 ≤ Rlog_R (4 * n + 3) + 1 by omega)
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos
      (add_den_pos (Qbound_den_pos n) (Qbound_den_pos n))))
    (Qmul_le_mul_left (by decide) (Qmul_le_mul_left (by decide) (Qadd_le_add hR2 hR3))) ?_
  apply Qeq_le
  show Qeq (mul ⟨4, 1⟩ (mul ⟨2, 1⟩ (add (Qbound n) (Qbound n)))) (⟨16, n + 1⟩ : Q)
  simp only [Qeq, mul, add, Qbound]; push_cast; ring_uor

set_option maxHeartbeats 800000 in
/-- **`Rartanh` radius-independence**: `Rartanh t` at two radii `ρ, ρ'` (both validly bounding `t` by a common
    `τ ≤ 1/2`) gives the same real. Per index `n`: with `a = Rartanh_R ρ n`, `b = Rartanh_R ρ' n`, `M = max a b`,
    split `|artSum(t a)(a) − artSum(t b)(b)| ≤ depth(a→M) + argvar(M) + depth(b→M)` via `artSum_depth_recip`,
    `artSum_Lip_le`/`geoEvenSum_le_two`, `t.reg`. Resolves the `ρ_B` vs `ρ_{B²}` reindex gap in the log-doubling. -/
theorem Rartanh_radius_indep (t X X' : Real) (ρ ρ' τ : Q) (hρd : 0 < ρ.den) (hρ'd : 0 < ρ'.den)
    (hτ0 : 0 ≤ τ.num) (hτd : 0 < τ.den) (hτlt : τ.num.toNat < τ.den)
    (hτ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul τ τ))) (hbt : ∀ m, Qle (Qabs (t.seq m)) τ)
    (hXseq : ∀ j, X.seq j = artSum (t.seq (Rartanh_R ρ j)) (Rartanh_R ρ j))
    (hX'seq : ∀ j, X'.seq j = artSum (t.seq (Rartanh_R ρ' j)) (Rartanh_R ρ' j)) :
    Req X X' := by
  have htd : ∀ m, 0 < (t.seq m).den := fun m => t.den_pos m
  have hRge : ∀ (r : Q), 0 < r.den → ∀ j, j + 1 ≤ Rartanh_R r j := by
    intro r hrd j; unfold Rartanh_R
    have hk : 1 ≤ r.den * r.den + 4 * r.den := Nat.le_trans (by omega : 1 ≤ 4 * r.den) (Nat.le_add_left _ _)
    calc j + 1 = 1 * (j + 1) := by omega
      _ ≤ (r.den * r.den + 4 * r.den) * (j + 1) := Nat.mul_le_mul_right _ hk
  refine Req_of_lin_bound (C := 4 * τ.den + 4) ?_
  intro n
  rw [hXseq, hX'seq]
  -- a, b, M and index facts
  have hage := hRge ρ hρd n
  have hbge := hRge ρ' hρ'd n
  have haM : Rartanh_R ρ n ≤ max (Rartanh_R ρ n) (Rartanh_R ρ' n) := Nat.le_max_left _ _
  have hbM : Rartanh_R ρ' n ≤ max (Rartanh_R ρ n) (Rartanh_R ρ' n) := Nat.le_max_right _ _
  have hna : n + 1 ≤ 2 * Rartanh_R ρ n + 3 := by omega
  have hnb : n + 1 ≤ 2 * Rartanh_R ρ' n + 3 := by omega
  -- term bounds
  have hT1 : Qle (Qabs (Qsub (artSum (t.seq (Rartanh_R ρ n)) (Rartanh_R ρ n))
        (artSum (t.seq (Rartanh_R ρ n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n)))))
      (⟨2 * (τ.den : Int), n + 1⟩ : Q) := by
    rw [Qabs_Qsub_comm]
    exact artSum_depth_recip (t.seq (Rartanh_R ρ n)) τ (htd _) hτ0 hτd (hbt _) hτ2 hτlt haM hna
  have hT3 : Qle (Qabs (Qsub (artSum (t.seq (Rartanh_R ρ' n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n)))
        (artSum (t.seq (Rartanh_R ρ' n)) (Rartanh_R ρ' n)))) (⟨2 * (τ.den : Int), n + 1⟩ : Q) :=
    artSum_depth_recip (t.seq (Rartanh_R ρ' n)) τ (htd _) hτ0 hτd (hbt _) hτ2 hτlt hbM hnb
  have hT2 : Qle (Qabs (Qsub (artSum (t.seq (Rartanh_R ρ n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n)))
        (artSum (t.seq (Rartanh_R ρ' n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n))))) (⟨4, n + 1⟩ : Q) := by
    refine Qle_trans (Qmul_den_pos (geoEvenSum_den_pos hτd _)
        (Qabs_den_pos (Qsub_den_pos (htd _) (htd _))))
      (artSum_Lip_le (htd _) (htd _) hτd (hbt _) (hbt _) _) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos (htd _) (htd _))))
      (Qmul_le_mul_right (Qabs_num_nonneg _) (geoEvenSum_le_two hτ0 hτd hτ2 _)) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)))
      (Qmul_le_mul_left (by decide) (t.reg (Rartanh_R ρ n) (Rartanh_R ρ' n))) ?_
    have hRa : Qle (Qbound (Rartanh_R ρ n)) (Qbound n) := by
      show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((Rartanh_R ρ n + 1 : Nat) : Int)
      rw [Int.one_mul, Int.one_mul]; exact_mod_cast (show n + 1 ≤ Rartanh_R ρ n + 1 by omega)
    have hRb : Qle (Qbound (Rartanh_R ρ' n)) (Qbound n) := by
      show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((Rartanh_R ρ' n + 1 : Nat) : Int)
      rw [Int.one_mul, Int.one_mul]; exact_mod_cast (show n + 1 ≤ Rartanh_R ρ' n + 1 by omega)
    refine Qle_trans (Qmul_den_pos Nat.one_pos (add_den_pos (Qbound_den_pos n) (Qbound_den_pos n)))
      (Qmul_le_mul_left (by decide) (Qadd_le_add hRa hRb)) ?_
    apply Qeq_le; show Qeq (mul ⟨2, 1⟩ (add (Qbound n) (Qbound n))) (⟨4, n + 1⟩ : Q)
    simp only [Qeq, mul, add, Qbound]; push_cast; ring_uor
  -- combine via two triangles
  have hP0d : 0 < (artSum (t.seq (Rartanh_R ρ n)) (Rartanh_R ρ n)).den := artSum_den_pos (htd _) _
  have hP1d : 0 < (artSum (t.seq (Rartanh_R ρ n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n))).den :=
    artSum_den_pos (htd _) _
  have hP2d : 0 < (artSum (t.seq (Rartanh_R ρ' n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n))).den :=
    artSum_den_pos (htd _) _
  have hP3d : 0 < (artSum (t.seq (Rartanh_R ρ' n)) (Rartanh_R ρ' n)).den := artSum_den_pos (htd _) _
  have hpc : Qle (Qabs (Qsub (artSum (t.seq (Rartanh_R ρ n)) (max (Rartanh_R ρ n) (Rartanh_R ρ' n)))
        (artSum (t.seq (Rartanh_R ρ' n)) (Rartanh_R ρ' n))))
      (add (⟨4, n + 1⟩ : Q) (⟨2 * (τ.den : Int), n + 1⟩ : Q)) :=
    Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hP1d hP2d))
        (Qabs_den_pos (Qsub_den_pos hP2d hP3d)))
      (Qabs_sub_triangle hP1d hP2d hP3d) (Qadd_le_add hT2 hT3)
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hP0d hP1d))
      (Qabs_den_pos (Qsub_den_pos hP1d hP3d)))
    (Qabs_sub_triangle hP0d hP1d hP3d) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos n) (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n)))
    (Qadd_le_add hT1 hpc) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n))
    (Qadd_le_add (Qle_refl _) (Qeq_le (Qadd_same_den_loc 4 (2 * (τ.den : Int)) (n + 1)))) ?_
  refine Qle_trans (Nat.succ_pos n)
    (Qeq_le (Qadd_same_den_loc (2 * (τ.den : Int)) (4 + 2 * (τ.den : Int)) (n + 1))) ?_
  apply Qeq_le; simp only [Qeq]; push_cast; ring_uor

/-- **Log-doubling, algebraic assembly**: for `X = Rartanh t_Y`, `Xdbl = Rartanh(uvalReal t_Y)`,
    `R2 = Rartanh t_{Y²}` (all at the common radius `σ = ρ_{M²}`), given the doubling `Radd X X ≈ Xdbl`
    and `Xdbl ≈ R2` (= `Rartanh_congr` of `(a)`), we get `Radd (c·X) (c·X) ≈ c·R2`, i.e.
    `Rlog Y + Rlog Y ≈ Rlog (Y²)` once `c = ofQ 2`. Pure ℝ-algebra: `Rmul_distrib` + `Rmul_congr`. -/
theorem Rlog_double_algebra (c X Xdbl R2 : Real) (hdbl : Req (Radd X X) Xdbl) (hcong : Req Xdbl R2) :
    Req (Radd (Rmul c X) (Rmul c X)) (Rmul c R2) :=
  Req_trans (Req_symm (Rmul_distrib c X X))
    (Rmul_congr (Req_refl c) (Req_trans hdbl hcong))

/-- **Log-doubling (abstract wiring)**: with `c = ofQ 2`, `t_Y` (radius `ρ`, bound on `t_Y`), `t_{Y²}` (radius
    `σ = ρ_{B²}`), and `t_{Y²} ≈ uvalReal t_Y` (from `(a)`), the two `Rmul c (Rartanh …)` reals — i.e.
    `2·Rlog Y` and `Rlog (Y²)` — agree. Chains `Rartanh_radius_indep` (`ρ→σ`), `Rartanh_double_real_via`
    (doubling), `Rartanh_congr` (`(a)`), `Rlog_double_algebra` (`Rmul_distrib`). Pure wiring, no new analysis. -/
theorem Rlog_sq_via (c tY tY2 : Real) (ρ σ : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num)
    (hρ1 : Qle ρ ⟨1, 1⟩) (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hρ4 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ))) (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
    (hρ8 : Qle (mul ⟨4, 1⟩ ρ) ⟨1, 1⟩) (hlt : (mul ρ ⟨16, 1⟩).num.toNat < (mul ρ ⟨16, 1⟩).den)
    (hρlt : ρ.num.toNat < ρ.den) (hσ0 : 0 ≤ σ.num) (hσd : 0 < σ.den)
    (hσ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul σ σ))) (hσlt : σ.num.toNat < σ.den) (hσ1 : Qle σ ⟨1, 1⟩)
    (hbtρ : ∀ m, Qle (Qabs (tY.seq m)) ρ) (hbtσ : ∀ m, Qle (Qabs (tY.seq m)) σ)
    (hbu : ∀ m, Qle (Qabs (uval (tY.seq m))) σ) (hbtY2 : ∀ m, Qle (Qabs (tY2.seq m)) σ)
    (htsq : Req tY2 (uvalReal tY σ hσd hσ1 hbtσ)) :
    Req (Radd (Rmul c (Rartanh tY ρ hρ0 hρd hρlt hbtρ)) (Rmul c (Rartanh tY ρ hρ0 hρd hρlt hbtρ)))
        (Rmul c (Rartanh tY2 σ hσ0 hσd hσlt hbtY2)) := by
  have hbur : ∀ n, Qle (Qabs ((uvalReal tY σ hσd hσ1 hbtσ).seq n)) σ := fun n => hbu (4 * n + 3)
  have hrad : Req (Rartanh tY ρ hρ0 hρd hρlt hbtρ) (Rartanh tY σ hσ0 hσd hσlt hbtσ) :=
    Rartanh_radius_indep tY (Rartanh tY ρ hρ0 hρd hρlt hbtρ) (Rartanh tY σ hσ0 hσd hσlt hbtσ)
      ρ σ ρ hρd hσd hρ0 hρd hρlt hρ2 hbtρ (fun _ => rfl) (fun _ => rfl)
  have hdbl : Req (Radd (Rartanh tY σ hσ0 hσd hσlt hbtσ) (Rartanh tY σ hσ0 hσd hσlt hbtσ))
      (Rartanh (uvalReal tY σ hσd hσ1 hbtσ) σ hσ0 hσd hσlt hbur) :=
    Rartanh_double_real_via tY (Rartanh tY σ hσ0 hσd hσlt hbtσ)
      (Rartanh (uvalReal tY σ hσd hσ1 hbtσ) σ hσ0 hσd hσlt hbur) ρ σ
      hρd hρ0 hρ1 h2ρ hρ4 hρ2 hρ8 hlt hσ0 hσd hσ2 hσlt hbtρ hbu (fun _ => rfl) (fun _ => rfl)
  have hcong : Req (Rartanh (uvalReal tY σ hσd hσ1 hbtσ) σ hσ0 hσd hσlt hbur)
      (Rartanh tY2 σ hσ0 hσd hσlt hbtY2) :=
    Rartanh_congr (uvalReal tY σ hσd hσ1 hbtσ) tY2 σ hσ0 hσd hσlt hσ2 hbur hbtY2 (Req_symm htsq)
  exact Req_trans (Radd_congr (Rmul_congr (Req_refl c) hrad) (Rmul_congr (Req_refl c) hrad))
    (Rlog_double_algebra c (Rartanh tY σ hσ0 hσd hσlt hbtσ)
      (Rartanh (uvalReal tY σ hσd hσ1 hbtσ) σ hσ0 hσd hσlt hbur)
      (Rartanh tY2 σ hσ0 hσd hσlt hbtY2) hdbl hcong)

/-- **`Rlog` `t`-bound**: `|tmap(x.seq k)| ≤ ρ_M = (M−1)/(M+1)` for `x ≤ M`, `x·M ≥ 1` (at every index `k`).
    The bound on `Rlog`'s internal `t`-real (`= Rlog`'s internal `hb`, extracted and generalized for reuse). -/
theorem Rlog_tbound (x : Real) (M : Q) (hMd : 0 < M.den) (hMn : 0 ≤ M.num)
    (hM1 : 0 < (add M ⟨1, 1⟩).num) (hhi : ∀ n, Qle (x.seq n) M)
    (hlo : ∀ n, Qle (⟨1, 1⟩ : Q) (mul (x.seq n) M)) (hxpos : ∀ n, 0 < (x.seq n).num) :
    ∀ k, Qle (Qabs (tmap (x.seq k))) (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q) := by
  intro k
  have hq1 : 0 < (add (x.seq k) ⟨1, 1⟩).num := by
    have := hxpos k; have h2 := Int.ofNat_nonneg (x.seq k).den
    show 0 < (x.seq k).num * 1 + 1 * ((x.seq k).den : Int); omega
  exact Qle_trans (show 0 < (tmap M).den from
      Qmul_den_pos (Qsub_den_pos hMd Nat.one_pos) (Qinv_den_pos hM1))
    (tmap_abs_le (x.den_pos _) hMd hq1 hM1 (hhi k) (hlo k))
    (Qeq_le (tmap_M_eq hMd hMn))

/-- **`Rlog` radius facts**: for `M ≥ 1`, the `M`-derivable validity of `ρ_M = ⟨M.num−M.den, M.num.toNat+M.den⟩`
    (`= (M−1)/(M+1)`): `M.num ≥ 0`, `M+1 > 0`, `ρ_M.num ≥ 0`, `ρ_M.den > 0`, `ρ_M.num.toNat < ρ_M.den`, `ρ_M ≤ 1`.
    Exactly `Rlog`'s internal radius bookkeeping, packaged. -/
theorem Rlog_radius_facts (M : Q) (hMd : 0 < M.den) (hMge : Qle (⟨1, 1⟩ : Q) M) :
    0 ≤ M.num ∧ 0 < (add M ⟨1, 1⟩).num ∧
    0 ≤ (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q).num ∧
    0 < (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q).den ∧
    (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q).num.toNat
      < (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q).den ∧
    Qle (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q) ⟨1, 1⟩ := by
  have hMge' : (1 : Int) * (M.den : Int) ≤ M.num * 1 := hMge
  have hMn : 0 ≤ M.num := by omega
  have h1 : ((M.num.toNat : Nat) : Int) = M.num := Int.toNat_of_nonneg hMn
  refine ⟨hMn, by show 0 < M.num * 1 + 1 * (M.den : Int); omega, by show 0 ≤ M.num - (M.den : Int); omega,
    by show 0 < M.num.toNat + M.den; omega, ?_, ?_⟩
  · show (M.num - (M.den : Int)).toNat < M.num.toNat + M.den
    have h2 : ((M.num - (M.den : Int)).toNat : Int) = M.num - (M.den : Int) := Int.toNat_of_nonneg (by omega)
    have : ((M.num - (M.den : Int)).toNat : Int) < ((M.num.toNat + M.den : Nat) : Int) := by
      push_cast [h1, h2]; omega
    exact_mod_cast this
  · show (M.num - (M.den : Int)) * ((1 : Nat) : Int) ≤ (1 : Int) * ((M.num.toNat + M.den : Nat) : Int)
    push_cast [h1]; omega

/-- **`Rlog` unfolding handle**: `Rlog x M = Rmul (ofQ 2) (Rartanh t_x ρ_M …)` with `ρ_M = (M−1)/(M+1)`
    in clean form `⟨M.num − M.den, M.num.toNat + M.den⟩`. Holds by `rfl` (proof irrelevance on the `Prop`
    arguments). The bridge from `Rlog`'s tactic-mode definition to the `Rmul`/`Rartanh` form `Rlog_sq_via`
    consumes. -/
theorem Rlog_eq_Rmul (x : Real) (M : Q) (hMd : 0 < M.den) (hMge : Qle (⟨1, 1⟩ : Q) M)
    (hxpos : ∀ n, 0 < (x.seq n).num) (hhi : ∀ n, Qle (x.seq n) M)
    (hlo : ∀ n, Qle (⟨1, 1⟩ : Q) (mul (x.seq n) M)) (hden : ∀ n, 0 < (Rlog_seq x n).den)
    (hρ0 : 0 ≤ (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q).num)
    (hρd : 0 < (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q).den)
    (hlt : (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q).num.toNat
            < (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q).den)
    (hb : ∀ n, Qle (Qabs ((⟨Rlog_seq x, Rlog_regular x hxpos, hden⟩ : Real).seq n))
            (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q)) :
    Rlog x M hMd hMge hxpos hhi hlo
      = Rmul (ofQ ⟨2, 1⟩ (by decide))
          (Rartanh ⟨Rlog_seq x, Rlog_regular x hxpos, hden⟩
            ⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ hρ0 hρd hlt hb) := rfl

set_option maxHeartbeats 800000 in
/-- **★ The log-doubling** `Rlog(Y²) = 2·Rlog Y` for real `Y` (bounded near 1). With `ρ_B = (B−1)/(B+1)`
    and `σ = (B²−1)/(B²+1)`, given `Y ≤ B`, `Y² ≤ B²` (`B ≥ 1`), `ρ_B ≤ σ`, and the convergence-radius
    smallness `ρ_B < 1/16`, `σ ≤ 1/2`, the two `Rlog`s agree. Unfolds both via `Rlog_eq_Rmul` and applies
    `Rlog_sq_via`; bounds via `Rlog_tbound` (+ `tmap_sq_uval` for `hbu`), `htsq` via `tsq_uvalReal_via`. -/
theorem Rlog_sq (Y : Real) (B : Q) (hBd : 0 < B.den) (hBge : Qle (⟨1, 1⟩ : Q) B)
    (hYpos : ∀ n, 0 < (Y.seq n).num) (hYhiB : ∀ n, Qle (Y.seq n) B)
    (hYloB : ∀ n, Qle (⟨1, 1⟩ : Q) (mul (Y.seq n) B)) (hB2d : 0 < (mul B B).den)
    (hB2ge : Qle (⟨1, 1⟩ : Q) (mul B B)) (hY2pos : ∀ n, 0 < ((Rmul Y Y).seq n).num)
    (hY2hi : ∀ n, Qle ((Rmul Y Y).seq n) (mul B B))
    (hY2lo : ∀ n, Qle (⟨1, 1⟩ : Q) (mul ((Rmul Y Y).seq n) (mul B B)))
    (hρσ : Qle (⟨B.num - (B.den : Int), B.num.toNat + B.den⟩ : Q)
              (⟨(mul B B).num - ((mul B B).den : Int), (mul B B).num.toNat + (mul B B).den⟩ : Q))
    (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩)).num)
    (hρ4 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩)))
    (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩
              ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩)))
    (hρ8 : Qle (mul ⟨4, 1⟩ ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩) ⟨1, 1⟩)
    (hlt16 : (mul ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩ ⟨16, 1⟩).num.toNat
              < (mul ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩ ⟨16, 1⟩).den)
    (hσ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨(mul B B).num - ((mul B B).den : Int),
              (mul B B).num.toNat + (mul B B).den⟩ ⟨(mul B B).num - ((mul B B).den : Int),
              (mul B B).num.toNat + (mul B B).den⟩))) :
    Req (Radd (Rlog Y B hBd hBge hYpos hYhiB hYloB) (Rlog Y B hBd hBge hYpos hYhiB hYloB))
        (Rlog (Rmul Y Y) (mul B B) hB2d hB2ge hY2pos hY2hi hY2lo) := by
  obtain ⟨hBn, hB1, hρ0, hρd, hρlt, hρ1⟩ := Rlog_radius_facts B hBd hBge
  obtain ⟨hB2n, hB21, hσ0, hσd, hσlt, hσ1⟩ := Rlog_radius_facts (mul B B) hB2d hB2ge
  have hden_Y : ∀ n, 0 < (Rlog_seq Y n).den := by
    intro n; refine Qmul_den_pos (Qsub_den_pos (Y.den_pos _) Nat.one_pos) (Qinv_den_pos ?_)
    have := hYpos (Rlog_R n); have h := Int.ofNat_nonneg (Y.seq (Rlog_R n)).den
    show 0 < (Y.seq (Rlog_R n)).num * 1 + 1 * ((Y.seq (Rlog_R n)).den : Int); omega
  have hden_Y2 : ∀ n, 0 < (Rlog_seq (Rmul Y Y) n).den := by
    intro n; refine Qmul_den_pos (Qsub_den_pos ((Rmul Y Y).den_pos _) Nat.one_pos) (Qinv_den_pos ?_)
    have := hY2pos (Rlog_R n); have h := Int.ofNat_nonneg ((Rmul Y Y).seq (Rlog_R n)).den
    show 0 < ((Rmul Y Y).seq (Rlog_R n)).num * 1 + 1 * (((Rmul Y Y).seq (Rlog_R n)).den : Int); omega
  have hbtρ := Rlog_tbound Y B hBd hBn hB1 hYhiB hYloB hYpos
  have hbtY2 := Rlog_tbound (Rmul Y Y) (mul B B) hB2d hB2n hB21 hY2hi hY2lo hY2pos
  have hbtσ : ∀ m, Qle (Qabs (tmap (Y.seq (Rlog_R m))))
      (⟨(mul B B).num - ((mul B B).den : Int), (mul B B).num.toNat + (mul B B).den⟩ : Q) :=
    fun m => Qle_trans hρd (hbtρ (Rlog_R m)) hρσ
  have hbu : ∀ m, Qle (Qabs (uval (tmap (Y.seq (Rlog_R m)))))
      (⟨(mul B B).num - ((mul B B).den : Int), (mul B B).num.toNat + (mul B B).den⟩ : Q) := by
    intro m
    have hqd := Y.den_pos (Rlog_R m)
    have hq1 : 0 < (add (Y.seq (Rlog_R m)) ⟨1, 1⟩).num := by
      have := hYpos (Rlog_R m); have h := Int.ofNat_nonneg (Y.seq (Rlog_R m)).den
      show 0 < (Y.seq (Rlog_R m)).num * 1 + 1 * ((Y.seq (Rlog_R m)).den : Int); omega
    have hq2 : 0 < (add (mul (Y.seq (Rlog_R m)) (Y.seq (Rlog_R m))) ⟨1, 1⟩).num := by
      have h1 : 0 ≤ (Y.seq (Rlog_R m)).num * (Y.seq (Rlog_R m)).num := by
        rw [← Int.natAbs_mul_self]; exact Int.ofNat_nonneg _
      have h2 : 0 < (((Y.seq (Rlog_R m)).den * (Y.seq (Rlog_R m)).den : Nat) : Int) := by
        exact_mod_cast Nat.mul_pos hqd hqd
      show 0 < (Y.seq (Rlog_R m)).num * (Y.seq (Rlog_R m)).num * 1
        + 1 * (((Y.seq (Rlog_R m)).den * (Y.seq (Rlog_R m)).den : Nat) : Int); omega
    have hq2leB2 : Qle (mul (Y.seq (Rlog_R m)) (Y.seq (Rlog_R m))) (mul B B) :=
      Qmul_le_mul hqd hBd hqd (Int.le_of_lt (hYpos _)) (Int.le_of_lt (hYpos _)) (hYhiB _) (hYhiB _)
    have hq2B2ge : Qle (⟨1, 1⟩ : Q) (mul (mul (Y.seq (Rlog_R m)) (Y.seq (Rlog_R m))) (mul B B)) := by
      have hsq : Qle (mul (⟨1, 1⟩ : Q) ⟨1, 1⟩)
          (mul (mul (Y.seq (Rlog_R m)) B) (mul (Y.seq (Rlog_R m)) B)) :=
        Qmul_le_mul Nat.one_pos (Qmul_den_pos hqd hBd) Nat.one_pos (by decide) (by decide)
          (hYloB _) (hYloB _)
      refine Qle_trans (Qmul_den_pos (Qmul_den_pos hqd hBd) (Qmul_den_pos hqd hBd))
        (Qle_trans (Qmul_den_pos Nat.one_pos Nat.one_pos)
          (Qeq_le (by decide : Qeq (⟨1, 1⟩ : Q) (mul ⟨1, 1⟩ ⟨1, 1⟩))) hsq) ?_
      exact Qeq_le (Qmul_rearrange4b (Y.seq (Rlog_R m)) B (Y.seq (Rlog_R m)) B)
    refine Qle_trans (Qabs_den_pos (Qmul_den_pos (Qsub_den_pos (Qmul_den_pos hqd hqd) Nat.one_pos)
        (Qinv_den_pos hq2)))
      (Qeq_le (Qabs_Qeq (Qeq_symm (tmap_sq_uval (Y.seq (Rlog_R m)) hqd hq1 hq2)))) ?_
    refine Qle_trans (show 0 < (tmap (mul B B)).den from
        Qmul_den_pos (Qsub_den_pos hB2d Nat.one_pos) (Qinv_den_pos hB21))
      (tmap_abs_le (Qmul_den_pos hqd hqd) hB2d hq2 hB21 hq2leB2 hq2B2ge) ?_
    exact Qeq_le (tmap_M_eq hB2d hB2n)
  have htsq := tsq_uvalReal_via Y ⟨Rlog_seq (Rmul Y Y), Rlog_regular (Rmul Y Y) hY2pos, hden_Y2⟩
    (uvalReal ⟨Rlog_seq Y, Rlog_regular Y hYpos, hden_Y⟩
      ⟨(mul B B).num - ((mul B B).den : Int), (mul B B).num.toNat + (mul B B).den⟩ hσd hσ1
      (fun m => hbtσ m)) ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩ hρd hρ1 hYpos hbtρ
    (fun _ => rfl) (fun _ => rfl)
  exact Rlog_sq_via (ofQ ⟨2, 1⟩ (by decide)) ⟨Rlog_seq Y, Rlog_regular Y hYpos, hden_Y⟩
    ⟨Rlog_seq (Rmul Y Y), Rlog_regular (Rmul Y Y) hY2pos, hden_Y2⟩
    ⟨B.num - (B.den : Int), B.num.toNat + B.den⟩
    ⟨(mul B B).num - ((mul B B).den : Int), (mul B B).num.toNat + (mul B B).den⟩
    hρd hρ0 hρ1 h2ρ hρ4 hρ2 hρ8 hlt16 hρlt hσ0 hσd hσ2 hσlt hσ1
    (fun m => hbtρ (Rlog_R m)) (fun m => hbtσ m) (fun m => hbu m) (fun m => hbtY2 (Rlog_R m)) htsq

/-- **Composition-eval gap ≤ Σ corners**: `|peval(a∘b) w M − peval a (peval b w M) M| ≤ Σ_{m≤M} |aₘ|·Cₘ`
    where `Cₘ = (peval b w M)ᵐ − peval(bᵐ) w M ≥ 0` is the degree-`>M` corner (`peval_fpow_le_pow`). The generic
    backbone of the exp eval bridge: with `a=ecoef` (`|aₘ|=1/m!`) the corner sum converges for `|w|<1`. -/
theorem comp_eval_gap_le (a b : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den)
    (hb0 : Qeq (b 0) ⟨0, 1⟩) (hbn : ∀ k, 0 ≤ (b k).num) (w : Q) (hwd : 0 < w.den)
    (hw0 : 0 ≤ w.num) (M : Nat) :
    Qle (Qabs (Qsub (peval (fcomp a b) w M) (peval a (peval b w M) M)))
      (Fsum (fun m => mul (Qabs (a m))
        (Qsub (qpow (peval b w M) m) (peval (fpow b m) w M))) M) := by
  have hS1d : ∀ m, 0 < (mul (a m) (peval (fpow b m) w M)).den :=
    fun m => Qmul_den_pos (ha m) (peval_den_pos (fpow_den_pos hb m) hwd M)
  have hS2d : ∀ m, 0 < (mul (a m) (qpow (peval b w M) m)).den :=
    fun m => Qmul_den_pos (ha m) (qpow_den_pos (peval_den_pos hb hwd M) m)
  refine Qle_trans (Qabs_den_pos (Qsub_den_pos (Fsum_den_pos hS1d M)
      (peval_den_pos ha (peval_den_pos hb hwd M) M)))
    (Qeq_le (Qabs_Qeq (Qsub_congr (peval_fcomp_swap a b ha hb hb0 w hwd M) (Qeq_refl _)))) ?_
  refine Qle_trans (Qabs_den_pos (Fsum_den_pos (fun m => Qsub_den_pos (hS1d m) (hS2d m)) M))
    (Qeq_le (Qabs_Qeq (Qeq_symm (Fsum_sub hS1d hS2d M)))) ?_
  refine Qle_trans (Fsum_den_pos (fun m => Qabs_den_pos (Qsub_den_pos (hS1d m) (hS2d m))) M)
    (Fsum_abs_le (fun m => Qsub_den_pos (hS1d m) (hS2d m)) M) ?_
  refine Fsum_le_congr (fun m _ => ?_)
  have hpfd : 0 < (peval (fpow b m) w M).den := peval_den_pos (fpow_den_pos hb m) hwd M
  have hqpd : 0 < (qpow (peval b w M) m).den := qpow_den_pos (peval_den_pos hb hwd M) m
  have hple : Qle (peval (fpow b m) w M) (qpow (peval b w M) m) :=
    peval_fpow_le_pow b hb hbn w hwd hw0 M m
  have hnn : 0 ≤ (Qsub (qpow (peval b w M) m) (peval (fpow b m) w M)).num := by
    have h := hple; simp only [Qle] at h
    show 0 ≤ (qpow (peval b w M) m).num * ((peval (fpow b m) w M).den : Int)
      + -(peval (fpow b m) w M).num * ((qpow (peval b w M) m).den : Int)
    rw [Int.neg_mul]; omega
  apply Qeq_le
  refine Qeq_trans (Qabs_den_pos (Qmul_den_pos (ha m) (Qsub_den_pos hpfd hqpd)))
    (Qabs_Qeq (Qeq_symm (Qmul_sub_distrib (a m) (peval (fpow b m) w M)
      (qpow (peval b w M) m)))) ?_
  rw [Qabs_mul]
  refine Qmul_congr (Qeq_refl _) ?_
  rw [Qabs_Qsub_comm]
  exact Qabs_of_nonneg hnn

/-- **The geometric closed form, cleared**: `(peval dgeom t N)·(1−t) ≈ (1+t) − 2·t^{N+1}`. So the geometric
    side of the exp identity converges: `peval dgeom t N → (1+t)/(1−t)` with gap `2t^{N+1}/(1−t)`. Via
    `peval_dgeom` (`= 2·gPow−1`) + `gPow_telescope` (`gPow·(1−t) = 1−t^{N+1}`). -/
theorem peval_dgeom_mul_cleared (t : Q) (htd : 0 < t.den) (N : Nat) :
    Qeq (mul (peval dgeom t N) (Qsub ⟨1, 1⟩ t))
      (Qsub (add ⟨1, 1⟩ t) (mul ⟨2, 1⟩ (qpow t (N + 1)))) := by
  have h := gPow_telescope htd N
  have hGd : 0 < (gPow t N).den := gPow_den_pos htd N
  have hsd : 0 < (Qsub (⟨1, 1⟩ : Q) t).den := Qsub_den_pos Nat.one_pos htd
  have hPd : 0 < (qpow t (N + 1)).den := qpow_den_pos htd (N + 1)
  have I1 : Qeq (mul (Qsub (mul ⟨2, 1⟩ (gPow t N)) ⟨1, 1⟩) (Qsub ⟨1, 1⟩ t))
      (Qsub (mul ⟨2, 1⟩ (mul (gPow t N) (Qsub ⟨1, 1⟩ t))) (Qsub ⟨1, 1⟩ t)) := by
    simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor
  have I2 : Qeq (Qsub (mul ⟨2, 1⟩ (mul (gPow t N) (Qsub ⟨1, 1⟩ t))) (Qsub ⟨1, 1⟩ t))
      (Qsub (mul ⟨2, 1⟩ (Qsub ⟨1, 1⟩ (qpow t (N + 1)))) (Qsub ⟨1, 1⟩ t)) :=
    Qsub_congr (Qmul_congr (Qeq_refl _) h) (Qeq_refl _)
  have I3 : Qeq (Qsub (mul ⟨2, 1⟩ (Qsub ⟨1, 1⟩ (qpow t (N + 1)))) (Qsub ⟨1, 1⟩ t))
      (Qsub (add ⟨1, 1⟩ t) (mul ⟨2, 1⟩ (qpow t (N + 1)))) := by
    simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor
  exact Qeq_trans (Qmul_den_pos (Qsub_den_pos (Qmul_den_pos Nat.one_pos hGd) Nat.one_pos) hsd)
    (Qmul_congr (peval_dgeom t htd N) (Qeq_refl _))
    (Qeq_trans (Qsub_den_pos (Qmul_den_pos Nat.one_pos (Qmul_den_pos hGd hsd)) hsd) I1
      (Qeq_trans (Qsub_den_pos (Qmul_den_pos Nat.one_pos (Qsub_den_pos Nat.one_pos hPd)) hsd) I2 I3))

/-- **The geometric tail, cleared**: `(peval dgeom t M2 − peval dgeom t M)·(1−t) ≈ 2·(t^{M+1} − t^{M2+1})`
    for `M ≤ M2`. The exp eval-bridge corner `Σ_{m≤M}(1/m!)·Cₘ` is bounded by this geometric tail
    `Σ_{M<k≤M2} dgeom_k tᵏ → 2t^{M+1}/(1−t)`. Two applications of `peval_dgeom_mul_cleared`. -/
theorem peval_dgeom_tail_cleared (t : Q) (htd : 0 < t.den) (M M2 : Nat) :
    Qeq (mul (Qsub (peval dgeom t M2) (peval dgeom t M)) (Qsub ⟨1, 1⟩ t))
      (mul ⟨2, 1⟩ (Qsub (qpow t (M + 1)) (qpow t (M2 + 1)))) := by
  have hAc := peval_dgeom_mul_cleared t htd M2
  have hBc := peval_dgeom_mul_cleared t htd M
  have hpM2 : 0 < (peval dgeom t M2).den := peval_den_pos (fun k => dgeom_den k) htd M2
  have hpM : 0 < (peval dgeom t M).den := peval_den_pos (fun k => dgeom_den k) htd M
  have hcd : 0 < (Qsub (⟨1, 1⟩ : Q) t).den := Qsub_den_pos Nat.one_pos htd
  have hrd : ∀ k, 0 < (Qsub (add (⟨1, 1⟩ : Q) t) (mul ⟨2, 1⟩ (qpow t k))).den :=
    fun k => Qsub_den_pos (add_den_pos Nat.one_pos htd) (Qmul_den_pos Nat.one_pos (qpow_den_pos htd k))
  have step1 : Qeq (mul (Qsub (peval dgeom t M2) (peval dgeom t M)) (Qsub ⟨1, 1⟩ t))
      (Qsub (mul (peval dgeom t M2) (Qsub ⟨1, 1⟩ t)) (mul (peval dgeom t M) (Qsub ⟨1, 1⟩ t))) := by
    simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor
  refine Qeq_trans (Qsub_den_pos (Qmul_den_pos hpM2 hcd) (Qmul_den_pos hpM hcd)) step1 ?_
  refine Qeq_trans (Qsub_den_pos (hrd (M2 + 1)) (hrd (M + 1))) (Qsub_congr hAc hBc) ?_
  simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor

/-- **Truncated coefficient series** `truncTo b M`: keeps `b k` for `k ≤ M`, zero above. Finite support
    `≤ M` — essential for the no-corner power identity (`2·acoef` has infinite support). -/
def truncTo (b : Nat → Q) (M : Nat) (k : Nat) : Q := if k ≤ M then b k else ⟨0, 1⟩

theorem truncTo_den {b : Nat → Q} (hb : ∀ i, 0 < (b i).den) (M k : Nat) : 0 < (truncTo b M k).den := by
  unfold truncTo; split
  · exact hb k
  · exact Nat.one_pos

theorem truncTo_le {b : Nat → Q} (hb0 : ∀ i, 0 ≤ (b i).num) (M k : Nat) : Qle (truncTo b M k) (b k) := by
  unfold truncTo; split
  · exact Qle_refl _
  · exact Qzero_le_loc (hb0 k)

/-- The truncation evaluated past its support equals the original partial sum: `peval (truncTo b M) t (M+d)
    ≈ peval b t M`. -/
theorem peval_truncTo {b : Nat → Q} (hb : ∀ i, 0 < (b i).den) (t : Q) (htd : 0 < t.den) (M : Nat) :
    ∀ d, Qeq (peval (truncTo b M) t (M + d)) (peval b t M)
  | 0 => by
      refine Fsum_congr_le (fun i hi => ?_)
      show Qeq (mul (truncTo b M i) (qpow t i)) (mul (b i) (qpow t i))
      have hbi : truncTo b M i = b i := by unfold truncTo; rw [if_pos (by omega : i ≤ M)]
      rw [hbi]; exact Qeq_refl _
  | (d + 1) => by
      rw [Nat.add_succ]
      have hz : truncTo b M (M + d + 1) = ⟨0, 1⟩ := by unfold truncTo; rw [if_neg (by omega)]
      show Qeq (add (peval (truncTo b M) t (M + d))
        (mul (truncTo b M (M + d + 1)) (qpow t (M + d + 1)))) (peval b t M)
      refine Qeq_trans (add_den_pos (peval_den_pos hb htd M) Nat.one_pos)
        (Qadd_congr (peval_truncTo hb t htd M d) ?_) (Qadd_zero_right _)
      rw [hz]; exact mul_left_zero _

/-- **Extending a finite sum over zero terms**: `Fsum f (a+d) ≈ Fsum f a` when `f j ≈ 0` for `a < j ≤ a+d`. -/
theorem Fsum_ext_zero {f : Nat → Q} (hf : ∀ k, 0 < (f k).den) (a : Nat) :
    ∀ d, (∀ j, a < j → j ≤ a + d → Qeq (f j) ⟨0, 1⟩) → Qeq (Fsum f (a + d)) (Fsum f a)
  | 0, _ => Qeq_refl _
  | (d + 1), hz => by
      rw [Nat.add_succ]
      show Qeq (add (Fsum f (a + d)) (f (a + d + 1))) (Fsum f a)
      refine Qeq_trans (add_den_pos (Fsum_den_pos hf a) Nat.one_pos)
        (Qadd_congr (Fsum_ext_zero hf a d (fun j hj1 hj2 => hz j hj1 (by omega)))
          (hz (a + d + 1) (by omega) (by omega))) (Qadd_zero_right _)

/-- **`peval_mul` with no corner** (finite support): if `a` has support `≤ Sa`, `b` support `≤ Sb`, and the
    evaluation depth `M2 ≥ Sa + Sb`, then `peval a · peval b ≈ peval (a*b)` exactly — the high-antidiagonal
    corner vanishes because every corner term `aᵢ·bⱼ` (with `i+j > M2`) has `i > Sa` or `j > Sb`. -/
theorem peval_mul_no_corner (a b : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hb : ∀ j, 0 < (b j).den)
    {t : Q} (htd : 0 < t.den) (Sa Sb M2 : Nat) (hasupp : ∀ k, Sa < k → Qeq (a k) ⟨0, 1⟩)
    (hbsupp : ∀ k, Sb < k → Qeq (b k) ⟨0, 1⟩) (hM2 : Sa + Sb ≤ M2) :
    Qeq (mul (peval a t M2) (peval b t M2)) (peval (fmul a b) t M2) := by
  have hta : ∀ i, 0 < (mul (a i) (qpow t i)).den := fun i => Qmul_den_pos (ha i) (qpow_den_pos htd i)
  have htb : ∀ j, 0 < (mul (b j) (qpow t j)).den := fun j => Qmul_den_pos (hb j) (qpow_den_pos htd j)
  have hg : ∀ i j, 0 < (mul (mul (a i) (qpow t i)) (mul (b j) (qpow t j))).den :=
    fun i j => Qmul_den_pos (hta i) (htb j)
  have hg0a : ∀ i j, Qeq (a i) ⟨0, 1⟩ →
      Qeq (mul (mul (a i) (qpow t i)) (mul (b j) (qpow t j))) ⟨0, 1⟩ := by
    intro i j h
    have h1 : Qeq (mul (a i) (qpow t i)) ⟨0, 1⟩ :=
      Qeq_trans (Qmul_den_pos Nat.one_pos (qpow_den_pos htd i)) (Qmul_congr h (Qeq_refl _)) (mul_left_zero _)
    exact Qeq_trans (Qmul_den_pos Nat.one_pos (htb j)) (Qmul_congr h1 (Qeq_refl _)) (mul_left_zero _)
  have hg0b : ∀ i j, Qeq (b j) ⟨0, 1⟩ →
      Qeq (mul (mul (a i) (qpow t i)) (mul (b j) (qpow t j))) ⟨0, 1⟩ := by
    intro i j h
    have h1 : Qeq (mul (b j) (qpow t j)) ⟨0, 1⟩ :=
      Qeq_trans (Qmul_den_pos Nat.one_pos (qpow_den_pos htd j)) (Qmul_congr h (Qeq_refl _)) (mul_left_zero _)
    exact Qeq_trans (Qmul_den_pos (hta i) Nat.one_pos) (Qmul_congr (Qeq_refl _) h1) (mul_right_zero _)
  have hcorner : Qeq (Fsum (fun i => Qsub
      (Fsum (fun j => mul (mul (a i) (qpow t i)) (mul (b j) (qpow t j))) M2)
      (Fsum (fun j => mul (mul (a i) (qpow t i)) (mul (b j) (qpow t j))) (M2 - i))) M2) ⟨0, 1⟩ := by
    refine Qeq_trans (Fsum_den_pos (fun _ => Nat.one_pos) M2)
      (Fsum_congr_le (fun i hi => ?_)) (Fsum_zeros M2)
    have htail : Qeq (Fsum (fun j => mul (mul (a i) (qpow t i)) (mul (b j) (qpow t j))) M2)
        (Fsum (fun j => mul (mul (a i) (qpow t i)) (mul (b j) (qpow t j))) (M2 - i)) := by
      have he : (M2 - i) + i = M2 := Nat.sub_add_cancel hi
      have hz := Fsum_ext_zero (fun j => hg i j) (M2 - i) i (fun j hj1 _ => by
        by_cases hiSa : i ≤ Sa
        · exact hg0b i j (hbsupp j (by omega))
        · exact hg0a i j (hasupp i (by omega)))
      rw [he] at hz; exact hz
    refine Qeq_trans (Qsub_den_pos (Fsum_den_pos (fun j => hg i j) (M2 - i))
        (Fsum_den_pos (fun j => hg i j) (M2 - i))) (Qsub_congr htail (Qeq_refl _)) ?_
    simp only [Qeq, Qsub, add, neg]; ring_uor
  refine Qeq_trans (add_den_pos (peval_den_pos (fun k => fmul_den_pos ha hb k) htd M2)
      (Fsum_den_pos (fun i => Qsub_den_pos (Fsum_den_pos (fun j => hg i j) M2)
        (Fsum_den_pos (fun j => hg i j) (M2 - i))) M2)) (peval_mul a b ha hb htd M2) ?_
  refine Qeq_trans (add_den_pos (peval_den_pos (fun k => fmul_den_pos ha hb k) htd M2) Nat.one_pos)
    (Qadd_congr (Qeq_refl _) hcorner) (Qadd_zero_right _)

/-- **Support of a formal power**: if `c` has support `≤ S`, then `fpow c m` has support `≤ m·S`
    (`fpow c m k ≈ 0` for `k > m·S`). By induction on `m` via the `fmul` convolution. -/
theorem fpow_supp {c : Nat → Q} (hc : ∀ i, 0 < (c i).den) (S : Nat)
    (hcs : ∀ k, S < k → Qeq (c k) ⟨0, 1⟩) : ∀ m k, m * S < k → Qeq (fpow c m k) ⟨0, 1⟩
  | 0, k, hk => by
      have hk0 : k ≠ 0 := by rw [Nat.zero_mul] at hk; omega
      show Qeq (fone k) ⟨0, 1⟩
      unfold fone; rw [if_neg hk0]; exact Qeq_refl _
  | (m + 1), k, hk => by
      show Qeq (Fsum (fun i => mul (c i) (fpow c m (k - i))) k) ⟨0, 1⟩
      refine Qeq_trans (Fsum_den_pos (fun _ => Nat.one_pos) k)
        (Fsum_congr_le (fun i hi => ?_)) (Fsum_zeros k)
      by_cases hiS : i ≤ S
      · have hki : m * S < k - i := by
          have hsm : (m + 1) * S = m * S + S := Nat.succ_mul m S
          omega
        exact Qeq_trans (Qmul_den_pos (hc i) Nat.one_pos)
          (Qmul_congr (Qeq_refl _) (fpow_supp hc S hcs m (k - i) hki)) (mul_right_zero _)
      · exact Qeq_trans (Qmul_den_pos Nat.one_pos (fpow_den_pos hc m _))
          (Qmul_congr (hcs i (by omega)) (Qeq_refl _)) (mul_left_zero _)

/-- **No-corner power**: for `c` of support `≤ S` and depth `M2 ≥ m·S`, `(peval c t M2)ᵐ ≈ peval (fpow c m) t M2`
    EXACTLY (the power of the truncation = truncation of the power, no corner). Induction via `peval_mul_no_corner`
    (corner vanishes: `c` support `≤ S`, `fpow c m` support `≤ m·S`, `M2 ≥ (m+1)·S`) + `fpow_supp`. -/
theorem peval_fpow_pow_eq {c : Nat → Q} (hc : ∀ i, 0 < (c i).den) {t : Q} (htd : 0 < t.den)
    (S : Nat) (hcs : ∀ k, S < k → Qeq (c k) ⟨0, 1⟩) :
    ∀ m M2, m * S ≤ M2 → Qeq (qpow (peval c t M2) m) (peval (fpow c m) t M2)
  | 0, M2, _ => by
      show Qeq ⟨1, 1⟩ (peval (fpow c 0) t M2)
      exact Qeq_symm (peval_fone t htd M2)
  | (m + 1), M2, hM2 => by
      have hsm : (m + 1) * S = m * S + S := Nat.succ_mul m S
      have hIH := peval_fpow_pow_eq hc htd S hcs m M2 (by omega)
      show Qeq (mul (peval c t M2) (qpow (peval c t M2) m)) (peval (fpow c (m + 1)) t M2)
      refine Qeq_trans (Qmul_den_pos (peval_den_pos hc htd M2)
          (peval_den_pos (fpow_den_pos hc m) htd M2)) (Qmul_congr (Qeq_refl _) hIH) ?_
      exact peval_mul_no_corner c (fpow c m) hc (fpow_den_pos hc m) htd S (m * S) M2
        hcs (fun k hk => fpow_supp hc S hcs m k hk) (by omega)

theorem truncTo_nonneg {b : Nat → Q} (hb0 : ∀ i, 0 ≤ (b i).num) (M k : Nat) :
    0 ≤ (truncTo b M k).num := by
  unfold truncTo; split
  · exact hb0 k
  · decide

/-- **Monotonicity of formal powers**: `c ≤ d` coeffwise (`c` nonnegative) ⇒ `fpow c m ≤ fpow d m` coeffwise. -/
theorem fpow_mono {c d : Nat → Q} (hcd : ∀ i, 0 < (c i).den) (hdd : ∀ i, 0 < (d i).den)
    (hc0 : ∀ i, 0 ≤ (c i).num) (hle : ∀ i, Qle (c i) (d i)) :
    ∀ m k, Qle (fpow c m k) (fpow d m k)
  | 0, k => by show Qle (fone k) (fone k); exact Qle_refl _
  | (m + 1), k => by
      show Qle (Fsum (fun i => mul (c i) (fpow c m (k - i))) k)
        (Fsum (fun i => mul (d i) (fpow d m (k - i))) k)
      exact Fsum_le_Fsum (fun i => Qmul_le_mul (hcd i) (hdd i) (fpow_den_pos hcd m _) (hc0 i)
        (fpow_num_nonneg hc0 m _) (hle i) (fpow_mono hcd hdd hc0 hle m (k - i))) k

/-- **★ The corner inequality** `(peval b t M)ᵐ ≤ peval (fpow b m) t M2` for `M2 ≥ m·M` (nonneg `b`, `t`).
    Power of the `M`-truncation ≤ the higher `M2`-truncation of the formal power. Via `truncTo` (so the power
    is exact, `peval_fpow_pow_eq`) + `fpow_mono` (`truncTo b M ≤ b`) lifted by `peval_mono`. -/
theorem qpow_peval_le {b : Nat → Q} (hb : ∀ i, 0 < (b i).den) (hb0 : ∀ i, 0 ≤ (b i).num)
    {t : Q} (htd : 0 < t.den) (ht0 : 0 ≤ t.num) (M m M2 : Nat) (hMM2 : M ≤ M2) (hmM : m * M ≤ M2) :
    Qle (qpow (peval b t M) m) (peval (fpow b m) t M2) := by
  have hsupp : ∀ k, M < k → Qeq (truncTo b M k) ⟨0, 1⟩ := by
    intro k hk; unfold truncTo; rw [if_neg (Nat.not_le.mpr hk)]; exact Qeq_refl _
  have he : Qeq (peval (truncTo b M) t M2) (peval b t M) := by
    have h := peval_truncTo hb t htd M (M2 - M)
    rw [show M + (M2 - M) = M2 from by omega] at h; exact h
  have hchain : Qeq (qpow (peval b t M) m) (peval (fpow (truncTo b M) m) t M2) :=
    Qeq_trans (qpow_den_pos (peval_den_pos (truncTo_den hb M) htd M2) m)
      (qpow_Qeq_loc (Qeq_symm he) m)
      (peval_fpow_pow_eq (truncTo_den hb M) htd M hsupp m M2 hmM)
  refine Qle_trans (peval_den_pos (fpow_den_pos (truncTo_den hb M) m) htd M2) (Qeq_le hchain) ?_
  exact peval_mono (fun k => fpow_mono (truncTo_den hb M) hb (truncTo_nonneg hb0 M)
    (truncTo_le hb0 M) m k) t ht0 M2

/-- **Extending a finite sum of nonnegatives only grows it**: `Fsum f M ≤ Fsum f (M+d)`. -/
theorem Fsum_le_extend {f : Nat → Q} (hf : ∀ i, 0 < (f i).den) (hf0 : ∀ i, 0 ≤ (f i).num) (M : Nat) :
    ∀ d, Qle (Fsum f M) (Fsum f (M + d))
  | 0 => Qle_refl _
  | (d + 1) => by
      rw [Nat.add_succ]
      show Qle (Fsum f M) (add (Fsum f (M + d)) (f (M + d + 1)))
      exact Qle_trans (Fsum_den_pos hf (M + d)) (Fsum_le_extend hf hf0 M d)
        (Qle_add_right_nonneg (hf0 (M + d + 1)))

/-- **★ The exp eval-bridge corner bound**: `|peval(exp∘2artanh) t M − peval exp (peval 2artanh t M) M| ≤
    peval dgeom t M² − peval dgeom t M` (the geometric tail). Combines `comp_eval_gap_le` (gap ≤ Σ corners),
    `qpow_peval_le` (each corner ≤ a higher-truncation difference), and `formal_exp_geom` (the sums collapse
    to `peval dgeom`). The convergence of the exp series at the doubled-artanh partial sum. -/
theorem exp_corner_le {t : Q} (htd : 0 < t.den) (ht0 : 0 ≤ t.num) (M : Nat) :
    Qle (Qabs (Qsub (peval (fcomp ecoef (fun i => mul ⟨2, 1⟩ (acoef i))) t M)
          (peval ecoef (peval (fun i => mul ⟨2, 1⟩ (acoef i)) t M) M)))
      (Qsub (peval dgeom t (M * M)) (peval dgeom t M)) := by
  have hbd : ∀ i, 0 < ((fun i => mul ⟨2, 1⟩ (acoef i)) i).den :=
    fun i => Qmul_den_pos Nat.one_pos (acoef_den i)
  have hb0n : ∀ i, 0 ≤ ((fun i => mul ⟨2, 1⟩ (acoef i)) i).num :=
    fun i => Qmul_num_nonneg (by decide) (acoef_num_nonneg i)
  have hb0 : Qeq ((fun i => mul ⟨2, 1⟩ (acoef i)) 0) ⟨0, 1⟩ := by
    show Qeq (mul ⟨2, 1⟩ (acoef 0)) ⟨0, 1⟩
    have h00 : acoef 0 = ⟨0, 1⟩ := by decide
    rw [h00]; decide
  have hec0 : ∀ i, 0 ≤ (ecoef i).num := fun _ => by show (0 : Int) ≤ 1; decide
  have hpAd : ∀ m, 0 ≤ (mul (ecoef m) (peval (fpow (fun i => mul ⟨2, 1⟩ (acoef i)) m) t (M * M))).num :=
    fun m => Qmul_num_nonneg (hec0 m) (peval_num_nonneg (fpow_num_nonneg hb0n m) t ht0 (M * M))
  have hMMle : M ≤ M * M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; decide
    · calc M = 1 * M := (Nat.one_mul M).symm
        _ ≤ M * M := Nat.mul_le_mul_right M h
  -- Step 1: comp_eval_gap_le
  refine Qle_trans (Fsum_den_pos (fun m => Qmul_den_pos (Qabs_den_pos (ecoef_den m))
      (Qsub_den_pos (qpow_den_pos (peval_den_pos hbd htd M) m)
        (peval_den_pos (fpow_den_pos hbd m) htd M))) M)
    (comp_eval_gap_le ecoef (fun i => mul ⟨2, 1⟩ (acoef i)) (fun i => ecoef_den i) hbd hb0 hb0n t htd ht0 M) ?_
  -- Step 2: termwise corner ≤ higher-truncation difference
  refine Qle_trans (Fsum_den_pos (fun m => Qmul_den_pos (ecoef_den m)
      (Qsub_den_pos (peval_den_pos (fpow_den_pos hbd m) htd (M * M))
        (peval_den_pos (fpow_den_pos hbd m) htd M))) M)
    (Fsum_le_congr (fun m hm => ?_)) ?_
  · refine Qle_congr_left (Qmul_den_pos (Qabs_den_pos (ecoef_den m))
        (Qsub_den_pos (qpow_den_pos (peval_den_pos hbd htd M) m) (peval_den_pos (fpow_den_pos hbd m) htd M)))
      (Qmul_congr (Qabs_of_nonneg (hec0 m)) (Qeq_refl _)) ?_
    exact Qmul_le_mul_left (hec0 m) (Qsub_le_sub
      (qpow_peval_le hbd hb0n htd ht0 M m (M * M) hMMle (Nat.mul_le_mul_right M hm)))
  -- Step 3: Σ ecoef m (A_m − B_m) ≤ peval dgeom (M*M) − peval dgeom M
  have hfM : Qeq (Fsum (fun m => mul (ecoef m)
      (peval (fpow (fun i => mul ⟨2, 1⟩ (acoef i)) m) t M)) M) (peval dgeom t M) :=
    Qeq_trans (peval_den_pos (fun k => fcomp_den_pos (fun i => ecoef_den i) hbd k) htd M)
      (Qeq_symm (peval_fcomp_swap ecoef (fun i => mul ⟨2, 1⟩ (acoef i)) (fun i => ecoef_den i) hbd hb0 t htd M))
      (peval_congr (fun k => formal_exp_geom k) t M)
  have hfMM : Qle (Fsum (fun m => mul (ecoef m)
      (peval (fpow (fun i => mul ⟨2, 1⟩ (acoef i)) m) t (M * M))) M) (peval dgeom t (M * M)) := by
    have hext : Qle (Fsum (fun m => mul (ecoef m)
          (peval (fpow (fun i => mul ⟨2, 1⟩ (acoef i)) m) t (M * M))) M)
        (Fsum (fun m => mul (ecoef m)
          (peval (fpow (fun i => mul ⟨2, 1⟩ (acoef i)) m) t (M * M))) (M * M)) := by
      have h := Fsum_le_extend (fun m => Qmul_den_pos (ecoef_den m)
        (peval_den_pos (fpow_den_pos hbd m) htd (M * M))) hpAd M (M * M - M)
      rw [show M + (M * M - M) = M * M from by omega] at h; exact h
    refine Qle_trans (Fsum_den_pos (fun m => Qmul_den_pos (ecoef_den m)
        (peval_den_pos (fpow_den_pos hbd m) htd (M * M))) (M * M)) hext ?_
    exact Qeq_le (Qeq_trans (peval_den_pos (fun k => fcomp_den_pos (fun i => ecoef_den i) hbd k) htd (M * M))
      (Qeq_symm (peval_fcomp_swap ecoef (fun i => mul ⟨2, 1⟩ (acoef i)) (fun i => ecoef_den i) hbd hb0 t htd (M * M)))
      (peval_congr (fun k => formal_exp_geom k) t (M * M)))
  -- assemble Step 3
  refine Qle_trans (Fsum_den_pos (fun m => Qsub_den_pos
      (Qmul_den_pos (ecoef_den m) (peval_den_pos (fpow_den_pos hbd m) htd (M * M)))
      (Qmul_den_pos (ecoef_den m) (peval_den_pos (fpow_den_pos hbd m) htd M))) M)
    (Qeq_le (Fsum_congr (fun m => Qmul_sub_distrib (ecoef m) _ _) M)) ?_
  refine Qle_trans (Qsub_den_pos (Fsum_den_pos (fun m => Qmul_den_pos (ecoef_den m)
        (peval_den_pos (fpow_den_pos hbd m) htd (M * M))) M)
      (Fsum_den_pos (fun m => Qmul_den_pos (ecoef_den m) (peval_den_pos (fpow_den_pos hbd m) htd M)) M))
    (Qeq_le (Fsum_sub (fun m => Qmul_den_pos (ecoef_den m) (peval_den_pos (fpow_den_pos hbd m) htd (M * M)))
      (fun m => Qmul_den_pos (ecoef_den m) (peval_den_pos (fpow_den_pos hbd m) htd M)) M)) ?_
  exact Qle_trans (Qsub_den_pos (Fsum_den_pos (fun m => Qmul_den_pos (ecoef_den m)
        (peval_den_pos (fpow_den_pos hbd m) htd (M * M))) M) (peval_den_pos (fun k => dgeom_den k) htd M))
    (Qeq_le (Qsub_congr (Qeq_refl _) hfM)) (Qsub_le_sub hfMM)

/-- **Geometric-limit gap, cleared**: `|peval dgeom t M − g|·(1−t) = 2·t^{M+1}` when `g·(1−t) = 1+t`
    (i.e. `g = (1+t)/(1−t)`). Half of the rational exp identity bound. -/
theorem dgeom_geom_gap_le (τ g : Q) (hτd : 0 < τ.den) (hτ0 : 0 ≤ τ.num) (hτ1 : Qle τ ⟨1, 1⟩)
    (hgd : 0 < g.den) (hg : Qeq (mul g (Qsub ⟨1, 1⟩ τ)) (add ⟨1, 1⟩ τ)) (M : Nat) :
    Qle (mul (Qabs (Qsub (peval dgeom τ M) g)) (Qsub ⟨1, 1⟩ τ)) (mul ⟨2, 1⟩ (qpow τ (M + 1))) := by
  have hDd : 0 < (peval dgeom τ M).den := peval_den_pos (fun k => dgeom_den k) hτd M
  have hWd : 0 < (Qsub (⟨1, 1⟩ : Q) τ).den := Qsub_den_pos Nat.one_pos hτd
  have hPd : 0 < (qpow τ (M + 1)).den := qpow_den_pos hτd (M + 1)
  have hW0 : 0 ≤ (Qsub (⟨1, 1⟩ : Q) τ).num := by
    have h := hτ1; simp only [Qle, Qsub, add, neg] at h ⊢; push_cast at h ⊢; omega
  have h2Pnn : 0 ≤ (mul ⟨2, 1⟩ (qpow τ (M + 1))).num := Qmul_num_nonneg (by decide) (qpow_nonneg hτ0 (M + 1))
  have hSgd : 0 < (Qsub (peval dgeom τ M) g).den := Qsub_den_pos hDd hgd
  have hkey : Qeq (mul (Qsub (peval dgeom τ M) g) (Qsub ⟨1, 1⟩ τ))
      (neg (mul ⟨2, 1⟩ (qpow τ (M + 1)))) := by
    refine Qeq_trans (Qsub_den_pos (Qmul_den_pos hDd hWd) (Qmul_den_pos hgd hWd))
      (Qmul_sub_right (peval dgeom τ M) g (Qsub ⟨1, 1⟩ τ)) ?_
    refine Qeq_trans (Qsub_den_pos (Qsub_den_pos (add_den_pos Nat.one_pos hτd)
        (Qmul_den_pos Nat.one_pos hPd)) (add_den_pos Nat.one_pos hτd))
      (Qsub_congr (peval_dgeom_mul_cleared τ hτd M) hg) ?_
    simp only [Qeq, Qsub, add, neg, mul]; push_cast; ring_uor
  have e1 : Qeq (mul (Qabs (Qsub (peval dgeom τ M) g)) (Qsub ⟨1, 1⟩ τ))
      (Qabs (mul (Qsub (peval dgeom τ M) g) (Qsub ⟨1, 1⟩ τ))) := by
    rw [Qabs_mul]; exact Qmul_congr (Qeq_refl _) (Qeq_symm (Qabs_of_nonneg hW0))
  refine Qeq_le (Qeq_trans (Qabs_den_pos (Qmul_den_pos hSgd hWd)) e1 ?_)
  refine Qeq_trans (Qabs_den_pos (neg_den_pos (Qmul_den_pos Nat.one_pos hPd))) (Qabs_Qeq hkey) ?_
  rw [Qabs_neg]; exact Qabs_of_nonneg h2Pnn

/-- **★ The rational exp identity bound (cleared)**: `|expSum(2·artSum τ partial, M) − g|·(1−τ) ≤ 4·τ^{M+1}`
    for `g = (1+τ)/(1−τ)` (`g·(1−τ) = 1+τ`), `0 ≤ τ ≤ 1`. So `exp(2·artanh τ) = (1+τ)/(1−τ)` at the rational
    level. Triangle through `peval dgeom τ M`: corner half (`exp_corner_le` + `peval_dgeom_tail_cleared`) +
    geometric half (`dgeom_geom_gap_le`). -/
theorem exp_artanh_rat_cleared (τ g : Q) (hτd : 0 < τ.den) (hτ0 : 0 ≤ τ.num) (hτ1 : Qle τ ⟨1, 1⟩)
    (hgd : 0 < g.den) (hg : Qeq (mul g (Qsub ⟨1, 1⟩ τ)) (add ⟨1, 1⟩ τ)) (M : Nat) :
    Qle (mul (Qabs (Qsub (expSum (peval (fun i => mul ⟨2, 1⟩ (acoef i)) τ M) M) g)) (Qsub ⟨1, 1⟩ τ))
      (mul ⟨4, 1⟩ (qpow τ (M + 1))) := by
  have hbd : ∀ i, 0 < ((fun i => mul ⟨2, 1⟩ (acoef i)) i).den :=
    fun i => Qmul_den_pos Nat.one_pos (acoef_den i)
  have hSd : 0 < (peval (fun i => mul ⟨2, 1⟩ (acoef i)) τ M).den := peval_den_pos hbd hτd M
  have hEd : 0 < (expSum (peval (fun i => mul ⟨2, 1⟩ (acoef i)) τ M) M).den := expSum_den_pos hSd M
  have hDd : 0 < (peval dgeom τ M).den := peval_den_pos (fun k => dgeom_den k) hτd M
  have hDMMd : 0 < (peval dgeom τ (M * M)).den := peval_den_pos (fun k => dgeom_den k) hτd (M * M)
  have hWd : 0 < (Qsub (⟨1, 1⟩ : Q) τ).den := Qsub_den_pos Nat.one_pos hτd
  have hPd : 0 < (qpow τ (M + 1)).den := qpow_den_pos hτd (M + 1)
  have hW0 : 0 ≤ (Qsub (⟨1, 1⟩ : Q) τ).num := by
    have h := hτ1; simp only [Qle, Qsub, add, neg] at h ⊢; push_cast at h ⊢; omega
  have hED : Qle (Qabs (Qsub (peval dgeom τ M)
        (expSum (peval (fun i => mul ⟨2, 1⟩ (acoef i)) τ M) M)))
      (Qsub (peval dgeom τ (M * M)) (peval dgeom τ M)) :=
    Qle_congr_left (Qabs_den_pos (Qsub_den_pos
        (peval_den_pos (fun k => fcomp_den_pos (fun i => ecoef_den i) hbd k) hτd M)
        (peval_den_pos (fun i => ecoef_den i) hSd M)))
      (Qabs_Qeq (Qsub_congr (peval_congr (fun k => formal_exp_geom k) τ M)
        (Qeq_symm (expSum_eq_peval_ecoef (peval (fun i => mul ⟨2, 1⟩ (acoef i)) τ M) hSd M))))
      (exp_corner_le hτd hτ0 M)
  have hED' : Qle (Qabs (Qsub (expSum (peval (fun i => mul ⟨2, 1⟩ (acoef i)) τ M) M) (peval dgeom τ M)))
      (Qsub (peval dgeom τ (M * M)) (peval dgeom τ M)) := by
    rw [Qabs_Qsub_comm]; exact hED
  have hbound1 : Qle (mul (Qabs (Qsub (expSum (peval (fun i => mul ⟨2, 1⟩ (acoef i)) τ M) M)
        (peval dgeom τ M))) (Qsub ⟨1, 1⟩ τ)) (mul ⟨2, 1⟩ (qpow τ (M + 1))) := by
    refine Qle_trans (Qmul_den_pos (Qsub_den_pos hDMMd hDd) hWd) (Qmul_le_mul_right hW0 hED') ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qsub_den_pos hPd (qpow_den_pos hτd (M * M + 1))))
      (Qeq_le (peval_dgeom_tail_cleared τ hτd M (M * M))) ?_
    exact Qmul_le_mul_left (by decide) (Qsub_le_self (qpow_nonneg hτ0 (M * M + 1)))
  refine Qle_trans (Qmul_den_pos (add_den_pos (Qabs_den_pos (Qsub_den_pos hEd hDd))
      (Qabs_den_pos (Qsub_den_pos hDd hgd))) hWd)
    (Qmul_le_mul_right hW0 (Qabs_sub_triangle hEd hDd hgd)) ?_
  refine Qle_trans (add_den_pos (Qmul_den_pos (Qabs_den_pos (Qsub_den_pos hEd hDd)) hWd)
      (Qmul_den_pos (Qabs_den_pos (Qsub_den_pos hDd hgd)) hWd))
    (Qeq_le (Qmul_add_right (Qabs (Qsub (expSum (peval (fun i => mul ⟨2, 1⟩ (acoef i)) τ M) M)
      (peval dgeom τ M))) (Qabs (Qsub (peval dgeom τ M) g)) (Qsub ⟨1, 1⟩ τ))) ?_
  refine Qle_trans (add_den_pos (Qmul_den_pos Nat.one_pos hPd) (Qmul_den_pos Nat.one_pos hPd))
    (Qadd_le_add hbound1 (dgeom_geom_gap_le τ g hτd hτ0 hτ1 hgd hg M)) ?_
  apply Qeq_le; simp only [Qeq, mul, add]; push_cast; ring_uor

end UOR.Bridge.F1Square.Analysis
