/-
F1 square — **real powers** `nᶜ = exp(c·log n)` (the v0.15.2 commit 1: the natural-exponent core).

The v0.15.1 ζ-convergence gate `exp(log n) = n` (`Rexp_log_nat_Rlog`) makes `log n` a genuine
constructive real with `exp(log n) ≈ n`. This file lifts that to **powers**: for a natural exponent
`k`, `exp(k·log n) ≈ nᵏ`. The mechanism is the exponential homomorphism `RexpReal_add`
(`exp(x+y) ≈ exp x · exp y`) iterated `k` times — i.e. `exp(k·x) ≈ (exp x)ᵏ` — composed with the gate.

`k·x` is the iterated real sum `Rnsmul k x = x + x + ⋯ + x` (`k` copies), so the homomorphism is a
clean induction: `exp((k+1)·x) = exp(x + k·x) ≈ exp x · exp(k·x) ≈ exp x · (exp x)ᵏ = (exp x)^{k+1}`.

This is the analytic content behind the `ζ` tail bound `|n^{-s}| = n^{-Re s}` for `Re s > 1`: the
real exponent of `n` is `exp(Re s · log n)`, and grounding it against the integer powers `nᵏ` (here)
and the exp monotonicity (next commit) is what makes `Σ n^{-s}` summable.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.ExpLog
import F1Square.Analysis.Pow
import F1Square.Analysis.GammaAccel
import F1Square.Analysis.CosSinBound

namespace UOR.Bridge.F1Square.Analysis

/-- **The natural scalar multiple** `k·x` of a real, as the iterated sum `x + x + ⋯ + x` (`k` copies).
    `0·x = 0` and `(k+1)·x = x + k·x`. This is the additive analogue of `Rpow` (iterated `Rmul`); it
    is what feeds the exponential homomorphism to produce `exp(k·x) = (exp x)ᵏ`. -/
def Rnsmul : Nat → Real → Real
  | 0, _ => zero
  | (k + 1), x => Radd x (Rnsmul k x)

theorem Rnsmul_zero (x : Real) : Rnsmul 0 x = zero := rfl

theorem Rnsmul_succ (k : Nat) (x : Real) : Rnsmul (k + 1) x = Radd x (Rnsmul k x) := rfl

/-- **The natural-power exponential homomorphism**: `exp(k·x) ≈ (exp x)ᵏ`. The diagonal lift of
    `exp((k+1)·x) = exp(x + k·x) ≈ exp x · exp(k·x)` (`RexpReal_add`), folded `k` times against
    `Rpow` (`(exp x)^{k+1} = exp x · (exp x)ᵏ`). The base `k = 0` is `exp 0 ≈ 1` (`RexpReal_zero`). -/
theorem RexpReal_nsmul (x : Real) : ∀ k, Req (RexpReal (Rnsmul k x)) (Rpow (RexpReal x) k)
  | 0 => RexpReal_zero
  | (k + 1) =>
      Req_trans (RexpReal_add x (Rnsmul k x))
        (Rmul_congr (Req_refl (RexpReal x)) (RexpReal_nsmul x k))

-- ===========================================================================
-- `Rnonneg` is closed under `Rmul` — the foundational real-multiplication sign fact that the
-- exponential monotonicity (next) rests on. The `Rmul` reindex `I+1 = 2K(n+1)` is tuned exactly for
-- it: a product of two samples each `≥ −1/(I+1)` and `≤ K` (in absolute value) is `≥ −K/(I+1) =
-- −1/(2(n+1)) ≥ −1/(n+1)`. The nonlinear integer core is isolated (`ring_uor` chokes on `.num` casts).
-- ===========================================================================

/-- The integer core of `Rnonneg_Rmul`: a bilinear lower bound on a box. Given `−dA ≤ A·(2Km)`,
    `−dB ≤ B·(2Km)`, `A ≤ K·dA`, `B ≤ K·dB` (with `dA,dB,K,m > 0`), the product satisfies
    `−(dA·dB) ≤ A·B·m`. The minimum of `A·B` over the box `[−1/(2Km),K]²` sits at a corner; the proof
    cases on the signs of `A,B` and, in each mixed case, multiplies the active `≥ −d` bound by the
    non-negative factor and divides out `K`. -/
private theorem mul_lo_core {A B dA dB K m : Int}
    (hdA : 0 < dA) (hdB : 0 < dB) (hK : 0 < K) (_hm : 0 < m)
    (h1 : -dA ≤ A * (2 * K * m)) (h2 : -dB ≤ B * (2 * K * m))
    (h3 : A ≤ K * dA) (h4 : B ≤ K * dB) : -(dA * dB) ≤ A * B * m := by
  -- The shared "one factor non-negative" argument: if `0 ≤ G`, `−dF ≤ F·(2Km)`, `G ≤ K·dG`, then
  -- `−(dF·dG) ≤ F·G·m`. (Used with `(F,G,dF,dG) = (A,B,dA,dB)` and `= (B,A,dB,dA)`.)
  have posarg : ∀ F G dF dG : Int, 0 ≤ G → 0 ≤ dF → 0 < dG →
      -dF ≤ F * (2 * K * m) → G ≤ K * dG → -(dF * dG) ≤ F * G * m := by
    intro F G dF dG hG hdF hdG hbnd hGle
    have s1 := Int.mul_le_mul_of_nonneg_right hbnd hG
    have s2 := Int.mul_le_mul_of_nonneg_left hGle hdF
    have e1 : F * (2 * K * m) * G = 2 * K * (F * G * m) := by ring_uor
    have e2 : (-dF) * G = -(dF * G) := by ring_uor
    have e3 : dF * (K * dG) = K * (dF * dG) := by ring_uor
    rw [e1, e2] at s1
    rw [e3] at s2
    have s3 : -(K * (dF * dG)) ≤ -(dF * G) := by omega
    have s4 := Int.le_trans s3 s1
    have e4 : -(K * (dF * dG)) = K * (-(dF * dG)) := by ring_uor
    have e5 : 2 * K * (F * G * m) = K * (2 * (F * G * m)) := by ring_uor
    rw [e4, e5] at s4
    have hfin : -(dF * dG) ≤ 2 * (F * G * m) := Int.le_of_mul_le_mul_left s4 hK
    have hY : 0 ≤ dF * dG := Int.mul_nonneg hdF (Int.le_of_lt hdG)
    omega
  by_cases hB : 0 ≤ B
  · exact posarg A B dA dB hB (Int.le_of_lt hdA) hdB h1 h4
  · by_cases hA : 0 ≤ A
    · have hsymm := posarg B A dB dA hA (Int.le_of_lt hdB) hdA h2 h3
      have e : B * A * m = A * B * m := by ring_uor
      have e' : dB * dA = dA * dB := by ring_uor
      rw [e, e'] at hsymm; exact hsymm
    · -- both negative ⇒ `A·B ≥ 0`
      have hAB : 0 ≤ A * B := by
        have h := Int.mul_nonneg (by omega : 0 ≤ -A) (by omega : 0 ≤ -B)
        have e : (-A) * (-B) = A * B := by ring_uor
        rw [e] at h; exact h
      have hABm : 0 ≤ A * B * m := Int.mul_nonneg hAB (Int.le_of_lt _hm)
      have hY : 0 ≤ dA * dB := Int.mul_nonneg (Int.le_of_lt hdA) (Int.le_of_lt hdB)
      omega

/-- **`Rnonneg` is closed under `Rmul`**: the product of two non-negative reals is non-negative. The
    `Rmul` reindex `I = Ridx x y n` satisfies `I+1 = 2K(n+1)` (`K = max(xBound x, xBound y)`), so the
    sample product `(x_I)·(y_I)` — with each factor `≥ −1/(I+1)` and `|·| ≤ K` — is `≥ −1/(n+1)`
    (`mul_lo_core`). This unblocks the exponential monotonicity. -/
theorem Rnonneg_Rmul {x y : Real} (hx : Rnonneg x) (hy : Rnonneg y) : Rnonneg (Rmul x y) := by
  intro n
  show Qle (neg (Qbound n)) (mul (x.seq (Ridx x y n)) (y.seq (Ridx x y n)))
  -- abbreviations (no `set`: Mathlib-only)
  have hIeq : (Ridx x y n + 1 : Nat) = 2 * RmulK x y * (n + 1) := Ridx_succ x y n
  -- the four integer bounds at index `I = Ridx x y n`
  have h1 : -((x.seq (Ridx x y n)).den : Int)
      ≤ (x.seq (Ridx x y n)).num * (2 * (RmulK x y : Int) * ((n + 1 : Nat) : Int)) := by
    have hh := hx (Ridx x y n)
    simp only [Qle, neg, Qbound] at hh
    rw [hIeq] at hh
    push_cast at hh ⊢
    omega
  have h2 : -((y.seq (Ridx x y n)).den : Int)
      ≤ (y.seq (Ridx x y n)).num * (2 * (RmulK x y : Int) * ((n + 1 : Nat) : Int)) := by
    have hh := hy (Ridx x y n)
    simp only [Qle, neg, Qbound] at hh
    rw [hIeq] at hh
    push_cast at hh ⊢
    omega
  have h3 : (x.seq (Ridx x y n)).num ≤ (RmulK x y : Int) * (x.seq (Ridx x y n)).den := by
    have hh : Qle (x.seq (Ridx x y n)) ⟨(RmulK x y : Int), 1⟩ :=
      Qle_trans (Qabs_den_pos (x.den_pos _)) (Qle_self_Qabs _)
        (canon_bound_le (Nat.le_max_left _ _) _)
    simp only [Qle] at hh
    push_cast at hh ⊢
    omega
  have h4 : (y.seq (Ridx x y n)).num ≤ (RmulK x y : Int) * (y.seq (Ridx x y n)).den := by
    have hh : Qle (y.seq (Ridx x y n)) ⟨(RmulK x y : Int), 1⟩ :=
      Qle_trans (Qabs_den_pos (y.den_pos _)) (Qle_self_Qabs _)
        (canon_bound_le (Nat.le_max_right _ _) _)
    simp only [Qle] at hh
    push_cast at hh ⊢
    omega
  have hcore := mul_lo_core (A := (x.seq (Ridx x y n)).num) (B := (y.seq (Ridx x y n)).num)
    (dA := ((x.seq (Ridx x y n)).den : Int)) (dB := ((y.seq (Ridx x y n)).den : Int))
    (K := (RmulK x y : Int)) (m := ((n + 1 : Nat) : Int))
    (by exact_mod_cast x.den_pos _) (by exact_mod_cast y.den_pos _)
    (by exact_mod_cast RmulK_pos x y) (by exact_mod_cast Nat.succ_pos n) h1 h2 h3 h4
  simp only [Qle, neg, Qbound, mul]
  push_cast at hcore ⊢
  omega

-- ===========================================================================
-- Order ⇄ Bishop-non-negativity bridge. `Rle zero x` (the order `0 ≤ x`, slack `2/(n+1)`) and
-- `Rnonneg x` (the tight Bishop `−1/(n+1) ≤ xₙ`) are the same fact, but `Rnonneg` does not transfer
-- across `≈` pointwise (the slack would inflate `−1/(n+1)` to `−3/(n+1)`). The bridge recovers the
-- tight bound by a one-index Archimedean reindex (`Qarch_gen`), exactly as `Rle_trans` does.
-- ===========================================================================

/-- **`0 ≤ x` (order) ⟹ `x ≥ 0` (Bishop)** — the tight non-negativity is recovered from the order by
    an Archimedean reindex: for each target index `n`, `xₙ ≥ −1/(n+1) − 3/(m+1)` for *every* `m`
    (regularity `x` at `n,m` + the order bound `xₘ ≥ −2/(m+1)`), and `Qarch_gen` kills the `3/(m+1)`. -/
theorem Rnonneg_of_Rle_zero {x : Real} (h : Rle zero x) : Rnonneg x := by
  intro n
  refine Qarch_gen (C := 3) (neg_den_pos (Qbound_den_pos n)) (x.den_pos n) (fun m => ?_)
  have hs2 : Qle (⟨0, 1⟩ : Q) (add (x.seq m) ⟨2, m + 1⟩) := h m
  have hs1 : Qle (x.seq m) (add (x.seq n) (add (Qbound m) (Qbound n))) :=
    Qle_add_of_Qabs_sub (x.den_pos m) (x.den_pos n)
      (add_den_pos (Qbound_den_pos m) (Qbound_den_pos n)) (x.reg m n)
  have hcomb : Qle (⟨0, 1⟩ : Q)
      (add (add (x.seq n) (add (Qbound m) (Qbound n))) ⟨2, m + 1⟩) :=
    Qle_trans (add_den_pos (x.den_pos m) (Nat.succ_pos _)) hs2 (Qadd_le_add hs1 (Qle_refl _))
  have hfinal := Qadd_le_add hcomb (Qle_refl (neg (Qbound n)))
  have hLHSeq : Qeq (neg (Qbound n)) (add (⟨0, 1⟩ : Q) (neg (Qbound n))) := by
    simp only [Qeq, add, neg, Qbound]; push_cast; ring_uor
  have hRHSeq : Qeq (add (add (add (x.seq n) (add (Qbound m) (Qbound n))) ⟨2, m + 1⟩)
      (neg (Qbound n))) (add (x.seq n) ⟨3, m + 1⟩) := by
    simp only [Qeq, add, neg, Qbound]; push_cast; ring_uor
  refine Qle_trans (add_den_pos (by decide) (neg_den_pos (Qbound_den_pos n))) (Qeq_le hLHSeq) ?_
  refine Qle_trans (add_den_pos (add_den_pos (add_den_pos (x.den_pos n)
      (add_den_pos (Qbound_den_pos m) (Qbound_den_pos n))) (Nat.succ_pos _))
      (neg_den_pos (Qbound_den_pos n))) hfinal (Qeq_le hRHSeq)

/-- **`Rnonneg` respects `≈`** — via the order bridge (`Rle` transfers across `≈` cleanly). -/
theorem Rnonneg_congr {x y : Real} (h : Req x y) (hx : Rnonneg x) : Rnonneg y :=
  Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg hx) (Rle_of_Req h))

-- ===========================================================================
-- `exp c ≥ 1` for `c ≥ 0` (in the tight form `exp c − 1 ≥ 0`), proven directly at the diagonal:
-- the sample `q = c_{R}` is `≥ −1/(N+1)` (`N = RexpReal_R c (2j+1)`). If `q ≥ 0` the partial sums
-- increase from `expSum q 0 = 1`; if `q < 0` then `|q| ≤ 1/(N+1) ≤ 1` and the quadratic remainder
-- `expSum_quad` plus the constant bound `expSumM 1 N ≤ 3` give `expSum q N ≥ 1 − 4/(N+1)`. The reindex
-- `N ≥ 8(j+1)` makes `4/(N+1) ≤ 1/(j+1)`, i.e. the tight Bishop bound.
-- ===========================================================================

/-- The ℚ-level core of `exp c − 1 ≥ 0`: for a sample `q ≥ −1/(N+1)` with `N ≥ 1` and the depth
    `4(j+1) ≤ N+1`, the partial sum satisfies `expSum q N − 1 ≥ −1/(j+1)`. If `q ≥ 0` the partial
    sums increase from `1`; if `q < 0` then `|q| ≤ 1/(N+1)` and the quadratic remainder `expSum_quad`
    with `expSumM 1 N ≤ 3` gives `expSum q N ≥ 1 − 4/(N+1) ≥ 1 − 1/(j+1)`. -/
private theorem exp_sub_one_lo (q : Q) (N j : Nat) (hqd : 0 < q.den)
    (hqlo : Qle (neg (Qbound N)) q) (hNj : 4 * (j + 1) ≤ N + 1) (hN1 : 1 ≤ N) :
    Qle (neg (Qbound j)) (add (expSum q N) (neg ⟨1, 1⟩)) := by
  by_cases hq0 : 0 ≤ q.num
  · have h1 : Qle (⟨1, 1⟩ : Q) (expSum q N) := expSum_le hq0 hqd (Nat.zero_le _)
    refine Qle_trans (b := add (⟨1, 1⟩ : Q) (neg ⟨1, 1⟩))
      (add_den_pos (by decide) (neg_den_pos (by decide))) ?_ (Qadd_le_add h1 (Qle_refl _))
    simp only [Qle, neg, Qbound, add]; push_cast; omega
  · have hqneg : q.num < 0 := by omega
    have hlo' : -(q.den : Int) ≤ q.num * ((N + 1 : Nat) : Int) := by
      have := hqlo; simp only [Qle, neg, Qbound] at this; push_cast at this ⊢; omega
    have hqN : Qle (Qabs q) (Qbound N) := by
      have hkey : (q.num.natAbs : Int) * ((N + 1 : Nat) : Int) ≤ 1 * (q.den : Int) := by
        have habs : ((q.num.natAbs : Int)) = -q.num := by omega
        rw [habs, Int.neg_mul]; omega
      simpa only [Qle, Qabs, Qbound] using hkey
    have hqabs : Qle (Qabs q) (⟨1, 1⟩ : Q) :=
      Qle_trans (Qbound_den_pos N) hqN (by simp only [Qle, Qbound]; push_cast; omega)
    have hNsucc : N - 1 + 1 = N := by omega
    have hquad := expSum_quad hqd hqabs (N - 1)
    rw [hNsucc] at hquad
    have hEbound : Qle (expSumM 1 N) (⟨3, 1⟩ : Q) :=
      Qle_trans (expM_U_den_pos 1 2) (expSumM_le_U 1 N) (by decide)
    have hnn_q : 0 ≤ (Qabs q).num := Qabs_num_nonneg q
    -- B := |q|²·expSumM 1 N ≤ 3/(N+1)
    have hBbound : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (⟨3, N + 1⟩ : Q) := by
      have step1 : Qle (mul (Qabs q) (Qabs q)) (mul (Qbound N) (⟨1, 1⟩ : Q)) :=
        Qmul_le_mul (Qabs_den_pos hqd) (Qbound_den_pos N) (Qabs_den_pos hqd) hnn_q hnn_q hqN hqabs
      have step2 : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))
          (mul (mul (Qbound N) (⟨1, 1⟩ : Q)) (⟨3, 1⟩ : Q)) :=
        Qmul_le_mul (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd))
          (Qmul_den_pos (Qbound_den_pos N) (by decide)) (expSumM_den_pos 1 N)
          (Int.mul_nonneg hnn_q hnn_q) (expSumM_num_nonneg 1 N) step1 hEbound
      refine Qle_trans (Qmul_den_pos (Qmul_den_pos (Qbound_den_pos N) (by decide)) (by decide))
        step2 (Qeq_le ?_)
      simp only [Qeq, mul, Qbound]; push_cast; ring_uor
    -- 1+q ≤ expSum q N + B
    have hCAB : Qle (add (⟨1, 1⟩ : Q) q)
        (add (expSum q N) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))) := by
      apply Qle_add_of_Qabs_sub (add_den_pos (by decide) hqd) (expSum_den_pos hqd N)
        (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (expSumM_den_pos 1 N))
      rw [Qabs_Qsub_comm]; exact hquad
    -- 1 − 1/(N+1) ≤ 1+q ≤ expSum q N + B ≤ expSum q N + 3/(N+1)
    have hq_lift : Qle (add (⟨1, 1⟩ : Q) (neg (Qbound N))) (add (⟨1, 1⟩ : Q) q) :=
      Qadd_le_add (Qle_refl _) hqlo
    have hfin : Qle (add (⟨1, 1⟩ : Q) (neg (Qbound N))) (add (expSum q N) (⟨3, N + 1⟩ : Q)) :=
      Qle_trans (add_den_pos (by decide) hqd) hq_lift
        (Qle_trans (add_den_pos (expSum_den_pos hqd N)
          (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (expSumM_den_pos 1 N)))
          hCAB (Qadd_le_add (Qle_refl _) hBbound))
    -- shift both sides by (−1) + (−3/(N+1)) to read off expSum q N − 1 ≥ −4/(N+1)
    have hd1 : 0 < (⟨1, 1⟩ : Q).den := Nat.one_pos
    have hd3 : 0 < (⟨3, N + 1⟩ : Q).den := Nat.succ_pos N
    have hd4 : 0 < (⟨4, N + 1⟩ : Q).den := Nat.succ_pos N
    have hstep := Qadd_le_add hfin (Qle_refl (add (neg (⟨1, 1⟩ : Q)) (neg (⟨3, N + 1⟩ : Q))))
    have hLHS : Qeq (add (add (⟨1, 1⟩ : Q) (neg (Qbound N))) (add (neg (⟨1, 1⟩ : Q)) (neg ⟨3, N + 1⟩)))
        (neg ⟨4, N + 1⟩) := by simp only [Qeq, add, neg, Qbound]; push_cast; ring_uor
    have hRHS : Qeq (add (add (expSum q N) (⟨3, N + 1⟩ : Q)) (add (neg (⟨1, 1⟩ : Q)) (neg ⟨3, N + 1⟩)))
        (add (expSum q N) (neg ⟨1, 1⟩)) := by
      simp only [Qeq, add, neg]; push_cast; ring_uor
    have hdLHS : 0 < (add (add (⟨1, 1⟩ : Q) (neg (Qbound N)))
        (add (neg (⟨1, 1⟩ : Q)) (neg ⟨3, N + 1⟩))).den :=
      add_den_pos (add_den_pos hd1 (neg_den_pos (Qbound_den_pos N)))
        (add_den_pos (neg_den_pos hd1) (neg_den_pos hd3))
    have hdRHS : 0 < (add (add (expSum q N) (⟨3, N + 1⟩ : Q))
        (add (neg (⟨1, 1⟩ : Q)) (neg ⟨3, N + 1⟩))).den :=
      add_den_pos (add_den_pos (expSum_den_pos hqd N) hd3)
        (add_den_pos (neg_den_pos hd1) (neg_den_pos hd3))
    have hstep2 : Qle (neg (⟨4, N + 1⟩ : Q)) (add (expSum q N) (neg ⟨1, 1⟩)) :=
      Qle_trans hdLHS (Qeq_le (Qeq_symm hLHS)) (Qle_trans hdRHS hstep (Qeq_le hRHS))
    refine Qle_trans (neg_den_pos hd4) ?_ hstep2
    simp only [Qle, neg, Qbound]; push_cast; omega

/-- **`exp c − 1 ≥ 0`** (i.e. `exp c ≥ 1`) for `c ≥ 0`. The diagonal sample is `q = c_{R}` with
    `N = RexpReal_R c (2j+1) ≥ 8(j+1)`, so `4(j+1) ≤ N+1`; `exp_sub_one_lo` finishes. This is the
    multiplicand that makes the exponential monotone. -/
theorem RexpReal_sub_one_nonneg {c : Real} (hc : Rnonneg c) : Rnonneg (Rsub (RexpReal c) one) := by
  intro j
  show Qle (neg (Qbound j)) (add (expSum (c.seq (RexpReal_R c (2 * j + 1))) (RexpReal_R c (2 * j + 1)))
    (neg ⟨1, 1⟩))
  have hNlb : 8 * (j + 1) ≤ RexpReal_R c (2 * j + 1) := by
    have hK : 1 ≤ RexpReal_K c := by unfold RexpReal_K; omega
    have hmul : 8 * (j + 1) * 1 ≤ 4 * (2 * j + 1 + 1) * RexpReal_K c := by
      have e : 4 * (2 * j + 1 + 1) = 8 * (j + 1) := by omega
      rw [e]; exact Nat.mul_le_mul_left (8 * (j + 1)) hK
    unfold RexpReal_R; omega
  exact exp_sub_one_lo (c.seq (RexpReal_R c (2 * j + 1))) (RexpReal_R c (2 * j + 1)) j
    (c.den_pos _) (hc (RexpReal_R c (2 * j + 1))) (by omega) (by omega)


/-- **`t/2 + t/2 ≈ t`** (`Rhalf`, the no-reindex halving): the two halves sum (exactly, in ℚ) to the
    deep sample `t₍₂ₙ₊₁₎`, which is within `3/(2(n+1)) ≤ 2/(n+1)` of `tₙ` by regularity. -/
theorem Rhalf_double (t : Real) : Req (Radd (Rhalf t) (Rhalf t)) t := by
  intro n
  show Qle (Qabs (Qsub (add (mul (⟨1, 2⟩ : Q) (t.seq (2 * n + 1))) (mul ⟨1, 2⟩ (t.seq (2 * n + 1))))
      (t.seq n))) ⟨2, n + 1⟩
  have heq : Qeq (Qsub (add (mul (⟨1, 2⟩ : Q) (t.seq (2 * n + 1))) (mul ⟨1, 2⟩ (t.seq (2 * n + 1))))
      (t.seq n)) (Qsub (t.seq (2 * n + 1)) (t.seq n)) := by
    simp only [Qeq, Qsub, add, mul, neg]; push_cast; ring_uor
  refine Qle_congr_left (Qabs_den_pos (Qsub_den_pos (t.den_pos (2 * n + 1)) (t.den_pos n)))
    (Qeq_symm (Qabs_Qeq heq)) ?_
  have hbb : Qle (Qbound (2 * n + 1)) (Qbound n) := by simp only [Qle, Qbound]; push_cast; omega
  have hb : Qle (add (Qbound (2 * n + 1)) (Qbound n)) (⟨2, n + 1⟩ : Q) :=
    Qle_trans (add_den_pos (Qbound_den_pos n) (Qbound_den_pos n))
      (Qadd_le_add hbb (Qle_refl (Qbound n)))
      (Qeq_le (by simp only [Qeq, add, Qbound]; push_cast; ring_uor))
  exact Qle_trans (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)) (t.reg (2 * n + 1) n) hb

/-- **`exp` is non-negative**: `exp t ≥ 0` for every real `t`, because `exp t ≈ (exp(t/2))²` and a
    square is non-negative (`Rnonneg_Rmul_self`). Holds for all `t` (no sign hypothesis). -/
theorem RexpReal_nonneg (t : Real) : Rnonneg (RexpReal t) := by
  have hsq : Req (RexpReal t) (Rmul (RexpReal (Rhalf t)) (RexpReal (Rhalf t))) :=
    Req_trans (RexpReal_congr (Req_symm (Rhalf_double t))) (RexpReal_add (Rhalf t) (Rhalf t))
  exact Rnonneg_congr (Req_symm hsq) (Rnonneg_Rmul_self (RexpReal (Rhalf t)))

-- ===========================================================================
-- **The exponential is monotone**: `a ≤ b ⟹ exp a ≤ exp b`. Via `exp b ≈ exp a + exp a·(exp(b−a)−1)`
-- with the increment `≥ 0` (`exp a ≥ 0`, `exp(b−a) ≥ 1` since `b−a ≥ 0`).
-- ===========================================================================

/-- `b − a ≥ 0` (Bishop) from `a ≤ b` (order) — tight, read off at the `Radd` reindex `2n+1`. -/
theorem Rnonneg_Rsub_of_Rle {a b : Real} (h : Rle a b) : Rnonneg (Rsub b a) := by
  intro n
  show Qle (neg (Qbound n)) (add (b.seq (2 * n + 1)) (neg (a.seq (2 * n + 1))))
  have hab : Qle (a.seq (2 * n + 1)) (add (b.seq (2 * n + 1)) ⟨2, (2 * n + 1) + 1⟩) := h (2 * n + 1)
  have hsub : Qle (Qsub (a.seq (2 * n + 1)) (b.seq (2 * n + 1))) (⟨2, (2 * n + 1) + 1⟩ : Q) :=
    Qsub_le_of_le_add (b.den_pos _) (Nat.succ_pos _) hab
  have heq1 : Qeq (neg (Qbound n)) (neg (⟨2, (2 * n + 1) + 1⟩ : Q)) := by
    simp only [Qeq, neg, Qbound]; push_cast; ring_uor
  have heq2 : Qeq (neg (Qsub (a.seq (2 * n + 1)) (b.seq (2 * n + 1))))
      (add (b.seq (2 * n + 1)) (neg (a.seq (2 * n + 1)))) := by
    simp only [Qeq, neg, Qsub, add]; push_cast; ring_uor
  exact Qle_trans (neg_den_pos (Nat.succ_pos _)) (Qeq_le heq1)
    (Qle_trans (neg_den_pos (Qsub_den_pos (a.den_pos _) (b.den_pos _))) (Qneg_le_neg hsub)
      (Qeq_le heq2))

/-- **`a ≤ b` (order) from `b − a ≥ 0` (Bishop)** — the converse of `Rnonneg_Rsub_of_Rle`, by an
    Archimedean reindex (`Qarch_gen`): `aₙ ≤ bₙ + 2/(n+1) + 6/(m+1)` for every `m` (regularity at
    `n, 2m+1` for both `a, b`, and `b−a ≥ −1/(m+1)` at index `m`). The standard `a ≤ b ⟺ 0 ≤ b−a`. -/
theorem Rle_of_Rnonneg_Rsub {a b : Real} (h : Rnonneg (Rsub b a)) : Rle a b := by
  intro n
  refine Qarch_gen (C := 2) (a.den_pos n) (add_den_pos (b.den_pos n) (Nat.succ_pos _)) (fun m => ?_)
  -- a.seq(2m+1) ≤ b.seq(2m+1) + 1/(m+1)
  have hh : Qle (neg (Qbound m)) (add (b.seq (2 * m + 1)) (neg (a.seq (2 * m + 1)))) := h m
  have hba : Qle (a.seq (2 * m + 1)) (add (b.seq (2 * m + 1)) (Qbound m)) := by
    have h1 := Qadd_le_add (Qle_refl (a.seq (2 * m + 1))) hh
    have heL : Qeq (add (a.seq (2 * m + 1)) (neg (Qbound m)))
        (add (a.seq (2 * m + 1)) (neg (Qbound m))) := Qeq_refl _
    have heR : Qeq (add (a.seq (2 * m + 1)) (add (b.seq (2 * m + 1)) (neg (a.seq (2 * m + 1)))))
        (b.seq (2 * m + 1)) := by simp only [Qeq, add, neg]; push_cast; ring_uor
    have h2 : Qle (add (a.seq (2 * m + 1)) (neg (Qbound m))) (b.seq (2 * m + 1)) :=
      Qle_congr_right (add_den_pos (a.den_pos _)
        (add_den_pos (b.den_pos _) (neg_den_pos (a.den_pos _)))) heR h1
    have h3 := Qadd_le_add h2 (Qle_refl (Qbound m))
    refine Qle_trans (add_den_pos (add_den_pos (a.den_pos _) (neg_den_pos (Qbound_den_pos m)))
      (Qbound_den_pos m)) (Qeq_le ?_) h3
    simp only [Qeq, add, neg, Qbound]; push_cast; ring_uor
  have hregA : Qle (a.seq n) (add (a.seq (2 * m + 1)) (add (Qbound n) (Qbound (2 * m + 1)))) :=
    Qle_add_of_Qabs_sub (a.den_pos n) (a.den_pos _)
      (add_den_pos (Qbound_den_pos n) (Qbound_den_pos _)) (a.reg n (2 * m + 1))
  have hregB : Qle (b.seq (2 * m + 1)) (add (b.seq n) (add (Qbound (2 * m + 1)) (Qbound n))) :=
    Qle_add_of_Qabs_sub (b.den_pos _) (b.den_pos n)
      (add_den_pos (Qbound_den_pos _) (Qbound_den_pos n)) (b.reg (2 * m + 1) n)
  -- chain a.seq n ≤ a(2m+1)+ (1/(n+1)+1/(2m+2)) ≤ (b(2m+1)+1/(m+1)) + … ≤ b.seq n + 2/(n+1) + 2/(m+1)
  have c1 : Qle (a.seq n) (add (add (b.seq (2 * m + 1)) (Qbound m)) (add (Qbound n) (Qbound (2 * m + 1)))) :=
    Qle_trans (add_den_pos (a.den_pos _) (add_den_pos (Qbound_den_pos n) (Qbound_den_pos _)))
      hregA (Qadd_le_add hba (Qle_refl _))
  have c2 : Qle (a.seq n)
      (add (add (add (b.seq n) (add (Qbound (2 * m + 1)) (Qbound n))) (Qbound m))
        (add (Qbound n) (Qbound (2 * m + 1)))) :=
    Qle_trans (add_den_pos (add_den_pos (b.den_pos _) (Qbound_den_pos m))
        (add_den_pos (Qbound_den_pos n) (Qbound_den_pos _)))
      c1 (Qadd_le_add (Qadd_le_add hregB (Qle_refl _)) (Qle_refl _))
  refine Qle_trans (add_den_pos (add_den_pos (add_den_pos (b.den_pos n)
      (add_den_pos (Qbound_den_pos _) (Qbound_den_pos n))) (Qbound_den_pos m))
      (add_den_pos (Qbound_den_pos n) (Qbound_den_pos _))) c2 (Qeq_le ?_)
  simp only [Qeq, add, Qbound]; push_cast; ring_uor

/-- **`a + (x − a) ≈ x`** — the additive cancellation used to read `exp b` off the difference form. -/
theorem Radd_Rsub_self (a x : Real) : Req (Radd a (Rsub x a)) x :=
  Req_trans (Req_symm (Radd_assoc a x (Rneg a)))
    (Req_trans (Radd_congr (Radd_comm a x) (Req_refl (Rneg a)))
      (Req_trans (Radd_assoc x a (Rneg a))
        (Req_trans (Radd_congr (Req_refl x) (Radd_neg a)) (Radd_zero x))))

/-- **The exponential is monotone**: `a ≤ b ⟹ exp a ≤ exp b`. The increment `exp a·(exp(b−a)−1)` is
    `≥ 0` (`RexpReal_nonneg`, `RexpReal_sub_one_nonneg`, `Rnonneg_Rmul`), and `exp a` plus it is `exp b`
    (`RexpReal_add` + `Radd_Rsub_self`). -/
theorem RexpReal_le_of_Rle {a b : Real} (h : Rle a b) : Rle (RexpReal a) (RexpReal b) := by
  have hD : Rnonneg (Rmul (RexpReal a) (Rsub (RexpReal (Rsub b a)) one)) :=
    Rnonneg_Rmul (RexpReal_nonneg a) (RexpReal_sub_one_nonneg (Rnonneg_Rsub_of_Rle h))
  have hRmul : Req (Rmul (RexpReal a) (Rsub (RexpReal (Rsub b a)) one))
      (Rsub (Rmul (RexpReal a) (RexpReal (Rsub b a))) (RexpReal a)) :=
    Req_trans (Rmul_sub_distrib (RexpReal a) (RexpReal (Rsub b a)) one)
      (Rsub_congr (Req_refl _) (Rmul_one (RexpReal a)))
  have hmulexp : Req (Rmul (RexpReal a) (RexpReal (Rsub b a))) (RexpReal b) :=
    Req_trans (Req_symm (RexpReal_add a (Rsub b a))) (RexpReal_congr (Radd_Rsub_self a b))
  have halg : Req (Radd (RexpReal a) (Rmul (RexpReal a) (Rsub (RexpReal (Rsub b a)) one)))
      (RexpReal b) :=
    Req_trans (Radd_congr (Req_refl _) hRmul)
      (Req_trans (Radd_Rsub_self (RexpReal a) (Rmul (RexpReal a) (RexpReal (Rsub b a)))) hmulexp)
  exact Rle_trans (Rle_self_Radd_right hD) (Rle_of_Req halg)

/-- **Real powers, abstract form**: if `exp L ≈ N` then `exp(k·L) ≈ Nᵏ`. With `L = log n` and
    `N = n` (the v0.15.1 gate `Rexp_log_nat_Rlog`), this is `exp(k·log n) ≈ nᵏ`. Decoupled from the
    `Rlog` plumbing so that any logarithm witness `exp L ≈ N` produces its powers — the established
    abstract-reconciliation pattern (cf. `Rexp_two_artanh_via`). -/
theorem RexpReal_nsmul_eq {L N : Real} (h : Req (RexpReal L) N) (k : Nat) :
    Req (RexpReal (Rnsmul k L)) (Rpow N k) :=
  Req_trans (RexpReal_nsmul L k) (Rpow_congr h k)

-- ===========================================================================
-- `exp(−log n) = 1/n` — the reciprocal of the gate, the basis of the `|n⁻ˢ| ≤ 1/n²` tail.
-- ===========================================================================

/-- The product of two constant reals is the constant of the product (no reindex content). -/
theorem Rmul_ofQ_ofQ {a b : Q} (ha : 0 < a.den) (hb : 0 < b.den) :
    Req (Rmul (ofQ a ha) (ofQ b hb)) (ofQ (mul a b) (Qmul_den_pos ha hb)) :=
  Req_of_seq_Qeq (fun _ => Qeq_refl _)

/-- **`exp(−L) ≈ 1/n`** given `exp L ≈ n` (abstract form). From the reciprocal law
    `exp(−L)·exp L ≈ 1` (`RexpReal_mul_neg`): `exp(−L) ≈ exp(−L)·(n·(1/n)) ≈ (exp(−L)·n)·(1/n) ≈
    1·(1/n) ≈ 1/n`. With `L = log n` (`Rexp_log_nat_Rlog`) this is `exp(−log n) = 1/n`. -/
theorem RexpReal_neg_eq_recip (n : Nat) (hn : 0 < n) {L : Real}
    (h : Req (RexpReal L) (ofQ ⟨(n : Int), 1⟩ Nat.one_pos)) :
    Req (RexpReal (Rneg L)) (ofQ ⟨1, n⟩ hn) := by
  have hnr : Req (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) (ofQ (⟨1, n⟩ : Q) hn)) one :=
    Req_trans (Rmul_ofQ_ofQ Nat.one_pos hn)
      (ofQ_respects (Qmul_den_pos Nat.one_pos hn) (by decide)
        (by simp only [Qeq, mul]; push_cast; ring_uor))
  have hsub : Req (Rmul (RexpReal (Rneg L)) (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)) one :=
    Req_trans (Rmul_congr (Req_refl (RexpReal (Rneg L))) (Req_symm h)) (RexpReal_mul_neg L)
  exact Req_trans (Req_symm (Rmul_one (RexpReal (Rneg L))))
    (Req_trans (Rmul_congr (Req_refl (RexpReal (Rneg L))) (Req_symm hnr))
      (Req_trans (Req_symm (Rmul_assoc (RexpReal (Rneg L))
          (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) (ofQ (⟨1, n⟩ : Q) hn)))
        (Req_trans (Rmul_congr hsub (Req_refl (ofQ (⟨1, n⟩ : Q) hn)))
          (Req_trans (Rmul_comm one (ofQ (⟨1, n⟩ : Q) hn)) (Rmul_one (ofQ (⟨1, n⟩ : Q) hn))))))

-- ===========================================================================
-- `log n ≥ 0` for `n ≥ 1` — the sign fact behind the exponent comparison `−σ·log n ≤ −2·log n`.
-- ===========================================================================

/-- The artanh partial sums are non-negative for a non-negative base (`artSum t N ≥ t ≥ 0`). -/
theorem artSum_nonneg {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) (N : Nat) :
    0 ≤ (artSum t N).num := by
  have h := artSum_ge_arg ht0 htd N
  have hdI : (0 : Int) ≤ ((artSum t N).den : Int) := Int.ofNat_nonneg _
  have htdI : (0 : Int) < (t.den : Int) := by exact_mod_cast htd
  unfold Qle at h
  have h1 : (0 : Int) ≤ t.num * ((artSum t N).den : Int) := Int.mul_nonneg ht0 hdI
  have h3 : (0 : Int) * (t.den : Int) ≤ (artSum t N).num * (t.den : Int) := by
    have := Int.le_trans h1 h; simpa using this
  exact Int.le_of_mul_le_mul_right h3 htdI

/-- **`log n ≥ 0`** for `n ≥ 1` (Bishop), where `Rlog (ofQ n) …` is the constructive logarithm. Since
    `Rlog x M = 2·artanh((x−1)/(x+1))` and the argument is the constant `tmap n ≥ 0`, the artanh diagonal
    is `artSum (tmap n) (·) ≥ 0`, and `2·(≥0) ≥ 0` (`Rnonneg_Rmul`). -/
theorem Rlog_nonneg (x : Real) (M : Q) (hMd : 0 < M.den) (hMge : Qle (⟨1, 1⟩ : Q) M)
    (hxpos : ∀ n, 0 < (x.seq n).num) (hhi : ∀ n, Qle (x.seq n) M)
    (hlo : ∀ n, Qle (⟨1, 1⟩ : Q) (mul (x.seq n) M))
    (htmap : ∀ n, 0 ≤ (x.seq n).num → 0 ≤ (Rlog_seq x n).num) :
    Rnonneg (Rlog x M hMd hMge hxpos hhi hlo) := by
  have hden : ∀ n, 0 < (Rlog_seq x n).den := by
    intro n
    refine Qmul_den_pos (Qsub_den_pos (x.den_pos _) Nat.one_pos) (Qinv_den_pos ?_)
    have h2 := hxpos (Rlog_R n)
    show 0 < (x.seq (Rlog_R n)).num * 1 + 1 * ((x.seq (Rlog_R n)).den : Int)
    have h := Int.ofNat_nonneg (x.seq (Rlog_R n)).den; omega
  have hMge' : (1 : Int) * (M.den : Int) ≤ M.num * 1 := hMge
  have hMn : 0 ≤ M.num := by omega
  have hρ0 : 0 ≤ (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q).num := by
    show 0 ≤ M.num - (M.den : Int); omega
  have hρd : 0 < (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q).den := by
    show 0 < M.num.toNat + M.den; omega
  have hlt : (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q).num.toNat
      < (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q).den := by
    show (M.num - (M.den : Int)).toNat < M.num.toNat + M.den
    have h1 : ((M.num.toNat : Nat) : Int) = M.num := Int.toNat_of_nonneg hMn
    have h2 : ((M.num - (M.den : Int)).toNat : Int) = M.num - (M.den : Int) :=
      Int.toNat_of_nonneg (by omega)
    have : ((M.num - (M.den : Int)).toNat : Int) < ((M.num.toNat + M.den : Nat) : Int) := by
      push_cast [h1, h2]; omega
    exact_mod_cast this
  have hb : ∀ n, Qle (Qabs ((⟨Rlog_seq x, Rlog_regular x hxpos, hden⟩ : Real).seq n))
      (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q) := by
    intro n
    have hca : 0 < (add (x.seq (Rlog_R n)) ⟨1, 1⟩).num := by
      have h := Int.ofNat_nonneg (x.seq (Rlog_R n)).den; have := hxpos (Rlog_R n)
      show 0 < (x.seq (Rlog_R n)).num * 1 + 1 * ((x.seq (Rlog_R n)).den : Int); omega
    exact Qle_trans (show 0 < (tmap M).den from
        Qmul_den_pos (Qsub_den_pos hMd Nat.one_pos) (Qinv_den_pos (by
          show 0 < M.num * 1 + 1 * (M.den : Int); omega)))
      (tmap_abs_le (x.den_pos _) hMd hca (by show 0 < M.num * 1 + 1 * (M.den : Int); omega)
        (hhi (Rlog_R n)) (hlo (Rlog_R n)))
      (Qeq_le (tmap_M_eq hMd hMn))
  rw [Rlog_eq_Rmul x M hMd hMge hxpos hhi hlo hden hρ0 hρd hlt hb]
  refine Rnonneg_Rmul (fun n => by show Qle (neg (Qbound n)) ⟨2, 1⟩; simp only [Qle, neg, Qbound]; push_cast; omega) ?_
  intro j
  show Qle (neg (Qbound j)) (Rartanh_seq ⟨Rlog_seq x, Rlog_regular x hxpos, hden⟩
    (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q) j)
  have hnn : 0 ≤ (Rartanh_seq ⟨Rlog_seq x, Rlog_regular x hxpos, hden⟩
      (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q) j).num :=
    artSum_nonneg
      (htmap (Rartanh_R (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q) j)
        (Int.le_of_lt (hxpos (Rartanh_R (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q) j))))
      (hden (Rartanh_R (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q) j))
      (Rartanh_R (⟨M.num - (M.den : Int), M.num.toNat + M.den⟩ : Q) j)
  refine Qle_trans (b := (⟨0, 1⟩ : Q)) (by decide) (by simp only [Qle, neg, Qbound]; push_cast; omega) ?_
  show Qle (⟨0, 1⟩ : Q) _
  simp only [Qle]; push_cast; omega

-- ===========================================================================
-- The ζ-term decay bound `|n⁻ˢ| = exp(−σ·log n) ≤ 1/n²` for `σ = Re s ≥ 2` — the analytic content
-- of the v0.15.2 tail bound. Via the *positive* comparison `2·log n ≤ σ·log n` (clean `Rnonneg_Rmul`),
-- `Rneg` reversing `≤`, exp monotonicity, and `exp(−2 log n) = (1/n)² = 1/n²`.
-- ===========================================================================

/-- `−(x + y) ≈ (−x) + (−y)`. -/
theorem Rneg_Radd (x y : Real) : Req (Rneg (Radd x y)) (Radd (Rneg x) (Rneg y)) :=
  Req_of_seq_Qeq (fun n => by
    show Qeq (neg (add (x.seq (2 * n + 1)) (y.seq (2 * n + 1))))
      (add (neg (x.seq (2 * n + 1))) (neg (y.seq (2 * n + 1))))
    simp only [Qeq, neg, add]; push_cast; ring_uor)

/-- `1·x ≈ x`. -/
theorem Rone_mul (x : Real) : Req (Rmul one x) x := Req_trans (Rmul_comm one x) (Rmul_one x)

/-- `2·x ≈ x + x`. -/
theorem Rmul_two_eq_add (x : Real) : Req (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) x) (Radd x x) :=
  Req_trans
    (Rmul_congr (Req_of_seq_Qeq (fun _ => by
      show Qeq (⟨2, 1⟩ : Q) (add (⟨1, 1⟩ : Q) ⟨1, 1⟩); decide)) (Req_refl x))
    (Req_trans (Rmul_distrib_right one one x) (Radd_congr (Rone_mul x) (Rone_mul x)))

/-- The positive exponent comparison `2·L ≤ σ·L` for `L ≥ 0`, `σ ≥ 2` — the difference `(σ−2)·L` is
    `≥ 0` (`Rnonneg_Rmul`), so `Rle_of_Rnonneg_Rsub` gives the order. -/
theorem Rmul_two_le_Rmul {L σ : Real} (hL : Rnonneg L)
    (hσ : Rle (ofQ (⟨2, 1⟩ : Q) (by decide)) σ) :
    Rle (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) L) (Rmul σ L) :=
  Rle_of_Rnonneg_Rsub
    (Rnonneg_congr (Rmul_sub_distrib_right σ (ofQ (⟨2, 1⟩ : Q) (by decide)) L)
      (Rnonneg_Rmul (Rnonneg_Rsub_of_Rle hσ) hL))

/-- **`exp(−2L) ≈ 1/n²`** given `exp(−L) ≈ 1/n`: `exp(−L−L) ≈ exp(−L)·exp(−L) ≈ (1/n)·(1/n)`. -/
theorem RexpReal_neg_two_eq {n : Nat} (hn : 0 < n) {L : Real}
    (hrec : Req (RexpReal (Rneg L)) (ofQ (⟨1, n⟩ : Q) hn)) :
    Req (RexpReal (Radd (Rneg L) (Rneg L))) (ofQ (⟨1, n * n⟩ : Q) (Nat.mul_pos hn hn)) :=
  Req_trans (RexpReal_add (Rneg L) (Rneg L))
    (Req_trans (Rmul_congr hrec hrec)
      (Req_trans (Rmul_ofQ_ofQ hn hn)
        (ofQ_respects (Qmul_den_pos hn hn) (Nat.mul_pos hn hn)
          (by simp only [Qeq, mul]; push_cast; ring_uor))))

/-- **The ζ-term decay bound**: `exp(−σ·L) ≤ 1/n²` for `σ ≥ 2`, given `exp L ≈ n` and `L ≥ 0`. With
    `L = log n` and `σ = Re s` this is `|n⁻ˢ| ≤ 1/n²`, the summable tail bound for `Czeta` at `Re s ≥ 2`.
    Route: `−σL ≤ −2L` (`Rneg_le` of the positive `2L ≤ σL`), `exp` monotone, and `exp(−2L) = 1/n²`. -/
theorem RexpReal_neg_sigma_le {n : Nat} (hn : 0 < n) {L σ : Real}
    (hexpL : Req (RexpReal L) (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)) (hLnn : Rnonneg L)
    (hσ : Rle (ofQ (⟨2, 1⟩ : Q) (by decide)) σ) :
    Rle (RexpReal (Rneg (Rmul σ L))) (ofQ (⟨1, n * n⟩ : Q) (Nat.mul_pos hn hn)) := by
  have hrec : Req (RexpReal (Rneg L)) (ofQ (⟨1, n⟩ : Q) hn) := RexpReal_neg_eq_recip n hn hexpL
  have hmono : Rle (RexpReal (Rneg (Rmul σ L)))
      (RexpReal (Rneg (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) L))) :=
    RexpReal_le_of_Rle (Rle_Rneg (Rmul_two_le_Rmul hLnn hσ))
  have halg : Req (RexpReal (Rneg (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) L)))
      (RexpReal (Radd (Rneg L) (Rneg L))) :=
    RexpReal_congr (Req_trans (Rneg_congr (Rmul_two_eq_add L)) (Rneg_Radd L L))
  exact Rle_trans hmono (Rle_of_Req (Req_trans halg (RexpReal_neg_two_eq hn hrec)))

end UOR.Bridge.F1Square.Analysis
