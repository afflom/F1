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

end UOR.Bridge.F1Square.Analysis
