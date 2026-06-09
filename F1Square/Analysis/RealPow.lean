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

-- ===========================================================================
-- Toward `Re s ∈ (1,2)`: the exp-convexity tower. First the geometric upper bound `exp t ≤ 1/(1−t)`
-- (`0 ≤ t < 1`), whose rational core is the termwise domination `qⁱ/i! ≤ qⁱ`, i.e. `expSum q N ≤ Σqⁱ`.
-- ===========================================================================

/-- **`expSum q N ≤ Σ_{i≤N} qⁱ`** for `q ≥ 0` — termwise, since `qⁱ/i! ≤ qⁱ` (`i! ≥ 1`). The rational
    seed of the geometric upper bound `exp t ≤ 1/(1−t)`. -/
theorem expSum_le_gPow {q : Q} (hq0 : 0 ≤ q.num) (hqd : 0 < q.den) :
    ∀ N, Qle (expSum q N) (gPow q N)
  | 0 => Qle_refl _
  | (N + 1) => by
      show Qle (add (expSum q N) (expTerm q (N + 1))) (add (gPow q N) (qpow q (N + 1)))
      have hterm : Qle (expTerm q (N + 1)) (qpow q (N + 1)) := by
        show Qle (mul (qpow q (N + 1)) ⟨1, fct (N + 1)⟩) (qpow q (N + 1))
        have hfle : Qle (⟨1, fct (N + 1)⟩ : Q) ⟨1, 1⟩ := by
          have hf : 1 ≤ fct (N + 1) := fct_pos (N + 1)
          show (1 : Int) * 1 ≤ 1 * ((fct (N + 1) : Nat) : Int)
          have : (1 : Int) ≤ ((fct (N + 1) : Nat) : Int) := by exact_mod_cast hf
          omega
        refine Qle_trans (Qmul_den_pos (qpow_den_pos hqd _) (by decide))
          (Qmul_le_mul_left (qpow_nonneg hq0 _) hfle) (Qeq_le ?_)
        simp only [Qeq, mul]; push_cast; ring_uor
      exact Qadd_le_add (expSum_le_gPow hq0 hqd N) hterm

/-- **`expSum q N · (1 − q) ≤ 1`** for `0 ≤ q ≤ 1` — the partial-sum form of `exp q ≤ 1/(1−q)`. Via
    `expSum ≤ Σqⁱ` and the geometric closed form `(Σqⁱ)(1−q) = 1 − q^{N+1} ≤ 1`. -/
theorem expSum_mul_one_sub_le {q : Q} (hq0 : 0 ≤ q.num) (hqd : 0 < q.den) (hq1 : Qle q ⟨1, 1⟩)
    (N : Nat) : Qle (mul (expSum q N) (Qsub ⟨1, 1⟩ q)) ⟨1, 1⟩ := by
  have hsub0 : 0 ≤ (Qsub (⟨1, 1⟩ : Q) q).num := by
    have h := hq1; simp only [Qle] at h; simp only [Qsub, add, neg]; push_cast at h ⊢; omega
  have h1 : Qle (mul (expSum q N) (Qsub ⟨1, 1⟩ q)) (mul (gPow q N) (Qsub ⟨1, 1⟩ q)) :=
    Qmul_le_mul_right hsub0 (expSum_le_gPow hq0 hqd N)
  have h3 : Qle (Qsub (⟨1, 1⟩ : Q) (qpow q (N + 1))) ⟨1, 1⟩ := by
    have hqp : 0 ≤ (qpow q (N + 1)).num := qpow_nonneg hq0 (N + 1)
    simp only [Qle, Qsub, add, neg]; push_cast; omega
  exact Qle_trans (Qmul_den_pos (gPow_den_pos hqd N) (Qsub_den_pos (by decide) hqd)) h1
    (Qle_trans (Qsub_den_pos (by decide) (qpow_den_pos hqd (N + 1))) (Qeq_le (gPow_telescope hqd N)) h3)

-- ===========================================================================
-- **Division by a positive real** (the cancellation linchpin): `Rnonneg (x·c) ∧ Pos c ⟹ Rnonneg x`.
-- The standard Bishop division — at a deep product index `c ≥ RL > 0` (`Inv.lean`'s witnessed floor),
-- so `x_I ≥ −1/((m+1)·RL)`; an Archimedean reindex (`Qarch_gen`) then recovers the tight `x ≥ −1/(p+1)`.
-- ===========================================================================

/-- The integer core of the division step: from `−dA·dc ≤ A·C·mp` (the product `≥ −1/mp`) and
    `RLn·dc ≤ C·RLd` (`c ≥ RL`), with all of `dA, dc, RLn, RLd, mp > 0`, conclude `−RLd·dA ≤ A·mp·RLn`
    (i.e. `x_I ≥ −1/(mp·RL)`). Cases on the sign of `A`; the `A<0` case divides out `dc`. -/
private theorem div_int_core {A C dA dc RLn RLd mp : Int}
    (hdA : 0 < dA) (hdc : 0 < dc) (hRLn : 0 < RLn) (hRLd : 0 < RLd) (_hmp : 0 < mp)
    (h1 : -(dA * dc) ≤ A * C * mp) (h2 : RLn * dc ≤ C * RLd) :
    -(RLd * dA) ≤ A * mp * RLn := by
  by_cases hA : 0 ≤ A
  · have h3 : 0 ≤ A * mp * RLn := Int.mul_nonneg (Int.mul_nonneg hA (by omega)) (by omega)
    have h4 : 0 ≤ RLd * dA := Int.mul_nonneg (by omega) (by omega)
    omega
  · have ha' : 0 ≤ -A := by omega
    have h1' : (-A) * C * mp ≤ dA * dc := by
      have e : (-A) * C * mp = -(A * C * mp) := by ring_uor
      rw [e]; omega
    have c1 : (-A) * mp * (RLn * dc) ≤ (-A) * mp * (C * RLd) :=
      Int.mul_le_mul_of_nonneg_left h2 (Int.mul_nonneg ha' (by omega))
    have c2 : ((-A) * C * mp) * RLd ≤ (dA * dc) * RLd :=
      Int.mul_le_mul_of_nonneg_right h1' (by omega)
    have e2 : (-A) * mp * (C * RLd) = ((-A) * C * mp) * RLd := by ring_uor
    have e3 : (-A) * mp * (RLn * dc) = ((-A) * mp * RLn) * dc := by ring_uor
    have e4 : (dA * dc) * RLd = (RLd * dA) * dc := by ring_uor
    have c3 : ((-A) * mp * RLn) * dc ≤ (RLd * dA) * dc := by
      rw [e2] at c1; rw [← e3, ← e4]; exact Int.le_trans c1 c2
    have c4 : (-A) * mp * RLn ≤ RLd * dA := Int.le_of_mul_le_mul_right c3 hdc
    have e5 : A * mp * RLn = -((-A) * mp * RLn) := by ring_uor
    rw [e5]; omega

/-- The `ℚ` division step: `−1/m ≤ xI·cI` and `L ≤ cI` (`L > 0`) give `−1/(m·L) ≤ xI`. -/
private theorem div_lo_core (xI cI L : Q) (m : Nat) (hxd : 0 < xI.den) (hcd : 0 < cI.den)
    (hLn : 0 < L.num) (hLd : 0 < L.den) (h1 : Qle (neg (Qbound m)) (mul xI cI)) (h2 : Qle L cI) :
    Qle (neg (mul (Qbound m) (Qinv L))) xI := by
  have H1 : -((xI.den : Int) * (cI.den : Int)) ≤ xI.num * cI.num * ((m : Int) + 1) := by
    have h := h1; simp only [Qle, neg, Qbound, mul] at h; push_cast at h; omega
  have H2 : L.num * (cI.den : Int) ≤ cI.num * (L.den : Int) := by
    have h := h2; simp only [Qle] at h; push_cast at h; omega
  have hcore := div_int_core (A := xI.num) (C := cI.num) (dA := (xI.den : Int))
    (dc := (cI.den : Int)) (RLn := L.num) (RLd := (L.den : Int)) (mp := (m : Int) + 1)
    (by exact_mod_cast hxd) (by exact_mod_cast hcd) hLn (by exact_mod_cast hLd) (by omega) H1 H2
  simp only [Qle, neg, mul, Qbound, Qinv]
  push_cast [Int.toNat_of_nonneg (Int.le_of_lt hLn)]
  have e2 : -((1 : Int) * (L.den : Int)) * (xI.den : Int) = -((L.den : Int) * (xI.den : Int)) := by
    ring_uor
  have e : xI.num * (((m : Int) + 1) * L.num) = xI.num * ((m : Int) + 1) * L.num := by ring_uor
  rw [e2, e]; exact hcore

/-- `1/((m+1)·L) ≤ L.den/(aux+1)` when `aux ≤ m` and `L > 0` (the first tail piece of the cancellation). -/
private theorem qbound_qinv_le {L : Q} (hLn : 0 < L.num) (m aux : Nat) (h : aux ≤ m) :
    Qle (mul (Qbound m) (Qinv L)) (⟨(L.den : Int), aux + 1⟩ : Q) := by
  simp only [Qle, mul, Qbound, Qinv]
  push_cast [Int.toNat_of_nonneg (Int.le_of_lt hLn)]
  have ha : (aux : Int) + 1 ≤ (m : Int) + 1 := by exact_mod_cast Nat.succ_le_succ h
  have hc : ((aux : Int) + 1) * 1 ≤ ((m : Int) + 1) * L.num :=
    Int.mul_le_mul ha (by omega) (by omega) (by omega)
  have hd : (0 : Int) ≤ (L.den : Int) := Int.ofNat_nonneg _
  have key : (1 : Int) * (L.den : Int) * ((aux : Int) + 1)
      ≤ (L.den : Int) * (((m : Int) + 1) * L.num) := by
    calc (1 : Int) * (L.den : Int) * ((aux : Int) + 1)
        = (L.den : Int) * (((aux : Int) + 1) * 1) := by ring_uor
      _ ≤ (L.den : Int) * (((m : Int) + 1) * L.num) := Int.mul_le_mul_of_nonneg_left hc hd
  exact key

/-- **Division by a positive real**: `Rnonneg (x·c)` and `Pos c` give `Rnonneg x`. The Bishop quotient:
    at a deep product index `c ≥ RL > 0` (`Rinv_lb`), `div_lo_core` gives `x_I ≥ −1/((m+1)·RL)`, and a
    `Qarch_gen` reindex (with `C = (RL c k).den + 1`) recovers the tight `x ≥ −1/(p+1)`. -/
theorem Rnonneg_of_Rmul_Pos {x c : Real} (hc : Pos c) (hxc : Rnonneg (Rmul x c)) : Rnonneg x := by
  obtain ⟨k, hk⟩ := hc
  intro p
  refine Qarch_gen (C := (RL c k).den + 1) (neg_den_pos (Qbound_den_pos p)) (x.den_pos p) (fun aux => ?_)
  -- m := aux + 2·δ.den, I := Ridx x c m
  have hmge : aux ≤ aux + 2 * (Rdelta c k).den := by omega
  have hIge : aux ≤ Ridx x c (aux + 2 * (Rdelta c k).den) :=
    Nat.le_trans hmge (Ridx_ge x c _)
  have hIdeep : 2 * (Rdelta c k).den ≤ Ridx x c (aux + 2 * (Rdelta c k).den) :=
    Nat.le_trans (by omega) (Ridx_ge x c _)
  have hprod : Qle (neg (Qbound (aux + 2 * (Rdelta c k).den)))
      (mul (x.seq (Ridx x c (aux + 2 * (Rdelta c k).den)))
        (c.seq (Ridx x c (aux + 2 * (Rdelta c k).den)))) :=
    hxc (aux + 2 * (Rdelta c k).den)
  have hclb : Qle (RL c k) (c.seq (Ridx x c (aux + 2 * (Rdelta c k).den))) := Rinv_lb hk hIdeep
  have hxI : Qle (neg (mul (Qbound (aux + 2 * (Rdelta c k).den)) (Qinv (RL c k))))
      (x.seq (Ridx x c (aux + 2 * (Rdelta c k).den))) :=
    div_lo_core _ _ _ _ (x.den_pos _) (c.den_pos _) (RL_num_pos hk) RL_den_pos hprod hclb
  have hreg : Qle (x.seq (Ridx x c (aux + 2 * (Rdelta c k).den)))
      (add (x.seq p) (add (Qbound (Ridx x c (aux + 2 * (Rdelta c k).den))) (Qbound p))) :=
    Qle_add_of_Qabs_sub (x.den_pos _) (x.den_pos p)
      (add_den_pos (Qbound_den_pos _) (Qbound_den_pos p))
      (x.reg (Ridx x c (aux + 2 * (Rdelta c k).den)) p)
  -- the key rational tail bound: X + Qbound I ≤ ⟨den+1, aux+1⟩
  have hkey : Qle (add (mul (Qbound (aux + 2 * (Rdelta c k).den)) (Qinv (RL c k)))
      (Qbound (Ridx x c (aux + 2 * (Rdelta c k).den)))) (⟨((RL c k).den : Int) + 1, aux + 1⟩ : Q) := by
    have hk2 : Qle (Qbound (Ridx x c (aux + 2 * (Rdelta c k).den))) (⟨1, aux + 1⟩ : Q) := by
      have hIge' := hIge
      simp only [Qle, Qbound]; push_cast; omega
    refine Qle_trans (add_den_pos (Nat.succ_pos aux) (Nat.succ_pos aux))
      (Qadd_le_add (qbound_qinv_le (RL_num_pos hk) _ aux hmge) hk2) (Qeq_le ?_)
    simp only [Qeq, add]; push_cast; ring_uor
  have hcomb : Qle (neg (mul (Qbound (aux + 2 * (Rdelta c k).den)) (Qinv (RL c k))))
      (add (x.seq p) (add (Qbound (Ridx x c (aux + 2 * (Rdelta c k).den))) (Qbound p))) :=
    Qle_trans (x.den_pos _) hxI hreg
  -- (−X) − (Qbound I + Qbound p) ≤ x.seq p
  have hxp_lb : Qle (add (neg (mul (Qbound (aux + 2 * (Rdelta c k).den)) (Qinv (RL c k))))
      (neg (add (Qbound (Ridx x c (aux + 2 * (Rdelta c k).den))) (Qbound p)))) (x.seq p) := by
    refine Qle_trans (add_den_pos (add_den_pos (x.den_pos p) (add_den_pos (Qbound_den_pos _)
      (Qbound_den_pos p))) (neg_den_pos (add_den_pos (Qbound_den_pos _) (Qbound_den_pos p))))
      (Qadd_le_add hcomb (Qle_refl _)) (Qeq_le ?_)
    simp only [Qeq, add, neg]; push_cast; ring_uor
  -- 0 ≤ (BD − (X + Qbound I)).num   (from hkey)
  have hnn : 0 ≤ (Qsub (⟨((RL c k).den + 1 : Nat), aux + 1⟩ : Q)
      (add (mul (Qbound (aux + 2 * (Rdelta c k).den)) (Qinv (RL c k)))
        (Qbound (Ridx x c (aux + 2 * (Rdelta c k).den))))).num :=
    Qsub_num_nonneg hkey
  -- neg(Qbound p) ≤ M := (−X − (Qbound I + Qbound p)) + BD
  have h_a : Qle (neg (Qbound p))
      (add (add (neg (mul (Qbound (aux + 2 * (Rdelta c k).den)) (Qinv (RL c k))))
        (neg (add (Qbound (Ridx x c (aux + 2 * (Rdelta c k).den))) (Qbound p))))
        (⟨((RL c k).den + 1 : Nat), aux + 1⟩ : Q)) := by
    refine Qle_trans (add_den_pos (neg_den_pos (Qbound_den_pos p)) (Qsub_den_pos (Nat.succ_pos _)
      (add_den_pos (Qmul_den_pos (Qbound_den_pos _) (Qinv_den_pos (RL_num_pos hk)))
        (Qbound_den_pos _)))) (Qle_self_add hnn) (Qeq_le ?_)
    simp only [Qeq, add, neg, Qsub]; push_cast; ring_uor
  exact Qle_trans (add_den_pos (add_den_pos (neg_den_pos (Qmul_den_pos (Qbound_den_pos _)
    (Qinv_den_pos (RL_num_pos hk)))) (neg_den_pos (add_den_pos (Qbound_den_pos _) (Qbound_den_pos p))))
    (Nat.succ_pos _)) h_a (Qadd_le_add hxp_lb (Qle_refl _))

/-- **`x ≥ 1 ⟹ x > 0`** (positivity from the order, witness `m = 3`: `x₃ ≥ 1 − 2/4 = 1/2 > 1/4`). -/
theorem Pos_of_Rle_one {x : Real} (h : Rle one x) : Pos x := by
  refine ⟨3, ?_⟩
  have h3 := h 3
  have hxd : 0 < (x.seq 3).den := x.den_pos 3
  show Qlt (Qbound 3) (x.seq 3)
  simp only [Qlt, Qbound]
  simp only [Qle, one, ofQ, add] at h3
  push_cast at h3 ⊢
  omega

/-- **`expSum q (N+1) ≥ 1 + q`** for `q ≥ 0` — the linear lower bound `exp q ≥ 1+q` at the partial-sum
    level: `expSum q 1 = 1 + q`, and the partial sums increase (`expSum_le`). -/
theorem expSum_ge_one_add {q : Q} (hq0 : 0 ≤ q.num) (hqd : 0 < q.den) (N : Nat) :
    Qle (add (⟨1, 1⟩ : Q) q) (expSum q (N + 1)) := by
  have h1 : Qeq (add (⟨1, 1⟩ : Q) q) (expSum q 1) := by
    show Qeq (add (⟨1, 1⟩ : Q) q) (add (expSum q 0) (expTerm q 1))
    simp only [expSum, expTerm, qpow, fct, Qeq, add, mul]; push_cast; ring_uor
  exact Qle_trans (expSum_den_pos hqd 1) (Qeq_le h1) (expSum_le hq0 hqd (by omega))

/-- `|q| ≤ 1/(N+1)` from `q ≥ −1/(N+1)` and `q < 0`. -/
private theorem qabs_le_qbound {q : Q} {N : Nat} (hqlo : Qle (neg (Qbound N)) q)
    (hqneg : q.num < 0) : Qle (Qabs q) (Qbound N) := by
  have hlo' : -(q.den : Int) ≤ q.num * ((N + 1 : Nat) : Int) := by
    have := hqlo; simp only [Qle, neg, Qbound] at this; push_cast at this ⊢; omega
  have hkey : (q.num.natAbs : Int) * ((N + 1 : Nat) : Int) ≤ 1 * (q.den : Int) := by
    have habs : ((q.num.natAbs : Int)) = -q.num := by omega
    rw [habs, Int.neg_mul]; omega
  simpa only [Qle, Qabs, Qbound] using hkey

/-- **`exp q ≥ 1 + q − 3/(N+1)`** (partial-sum form) for `q < 0` with `|q| ≤ 1/(N+1)` — the quadratic
    remainder `expSum_quad` with the constant bound `expSumM 1 N ≤ 3`. -/
private theorem exp_lower_quad {q : Q} (hqd : 0 < q.den) {N : Nat} (hN1 : 1 ≤ N)
    (hqabs : Qle (Qabs q) (Qbound N)) :
    Qle (add (⟨1, 1⟩ : Q) q) (add (expSum q N) (⟨3, N + 1⟩ : Q)) := by
  have hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q) :=
    Qle_trans (Qbound_den_pos N) hqabs (by simp only [Qle, Qbound]; push_cast; omega)
  have hNsucc : N - 1 + 1 = N := by omega
  have hquad := expSum_quad hqd hq1 (N - 1)
  rw [hNsucc] at hquad
  have hEbound : Qle (expSumM 1 N) (⟨3, 1⟩ : Q) :=
    Qle_trans (expM_U_den_pos 1 2) (expSumM_le_U 1 N) (by decide)
  have hnn_q : 0 ≤ (Qabs q).num := Qabs_num_nonneg q
  have hBbound : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (⟨3, N + 1⟩ : Q) := by
    have step1 : Qle (mul (Qabs q) (Qabs q)) (mul (Qbound N) (⟨1, 1⟩ : Q)) :=
      Qmul_le_mul (Qabs_den_pos hqd) (Qbound_den_pos N) (Qabs_den_pos hqd) hnn_q hnn_q hqabs hq1
    have step2 : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))
        (mul (mul (Qbound N) (⟨1, 1⟩ : Q)) (⟨3, 1⟩ : Q)) :=
      Qmul_le_mul (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd))
        (Qmul_den_pos (Qbound_den_pos N) (by decide)) (expSumM_den_pos 1 N)
        (Int.mul_nonneg hnn_q hnn_q) (expSumM_num_nonneg 1 N) step1 hEbound
    refine Qle_trans (Qmul_den_pos (Qmul_den_pos (Qbound_den_pos N) (by decide)) (by decide))
      step2 (Qeq_le ?_)
    simp only [Qeq, mul, Qbound]; push_cast; ring_uor
  have hCAB : Qle (add (⟨1, 1⟩ : Q) q)
      (add (expSum q N) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))) := by
    apply Qle_add_of_Qabs_sub (add_den_pos (by decide) hqd) (expSum_den_pos hqd N)
      (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (expSumM_den_pos 1 N))
    rw [Qabs_Qsub_comm]; exact hquad
  exact Qle_trans (add_den_pos (expSum_den_pos hqd N)
    (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (expSumM_den_pos 1 N)))
    hCAB (Qadd_le_add (Qle_refl _) hBbound)

/-- **`1 + t ≤ exp t`** for `t ≥ 0` (the `Rle` form). At the diagonal the sample `q = t_{R j}` gives
    `expSum q N ≥ 1 + q` (`expSum_ge_one_add`, or the quad lower bound if `q` dips negative), and the
    `+t` term at index `2j+1` is reconciled by regularity; the reindex `N ≥ 4(j+1)` closes the budget. -/
theorem RexpReal_ge_one_add_nonneg {t : Real} (ht : Rnonneg t) : Rle (Radd one t) (RexpReal t) := by
  intro j
  show Qle (add (⟨1, 1⟩ : Q) (t.seq (2 * j + 1)))
    (add (expSum (t.seq (RexpReal_R t j)) (RexpReal_R t j)) ⟨2, j + 1⟩)
  have hNlb : 4 * (j + 1) ≤ RexpReal_R t j := by
    have hK : 1 ≤ RexpReal_K t := by unfold RexpReal_K; omega
    have hmul : 4 * (j + 1) * 1 ≤ 4 * (j + 1) * RexpReal_K t := Nat.mul_le_mul_left _ hK
    unfold RexpReal_R; omega
  have hqd : 0 < (t.seq (RexpReal_R t j)).den := t.den_pos _
  have ht1 : Qle (t.seq (2 * j + 1)) (add (t.seq (RexpReal_R t j)) ⟨2, 2 * j + 1 + 1⟩) :=
    Qle_add_of_Qabs_sub (t.den_pos _) (t.den_pos _) (Nat.succ_pos _)
      (xreg_n_le t (Nat.le_refl (2 * j + 1)) (by omega : 2 * j + 1 ≤ RexpReal_R t j))
  -- the `1 + q` lower bound (uniform `3/(N+1)` slack covering both signs of `q`)
  have hlb : Qle (add (⟨1, 1⟩ : Q) (t.seq (RexpReal_R t j)))
      (add (expSum (t.seq (RexpReal_R t j)) (RexpReal_R t j)) ⟨3, RexpReal_R t j + 1⟩) := by
    by_cases hq0 : 0 ≤ (t.seq (RexpReal_R t j)).num
    · have h := expSum_ge_one_add hq0 hqd (RexpReal_R t j - 1)
      rw [(by omega : RexpReal_R t j - 1 + 1 = RexpReal_R t j)] at h
      exact Qle_trans (expSum_den_pos hqd _) h (Qle_self_add (by show (0 : Int) ≤ 3; decide))
    · exact exp_lower_quad hqd (by omega) (qabs_le_qbound (ht (RexpReal_R t j)) (by omega))
  have hassoc1 : Qeq (add (⟨1, 1⟩ : Q) (add (t.seq (RexpReal_R t j)) ⟨2, 2 * j + 1 + 1⟩))
      (add (add (⟨1, 1⟩ : Q) (t.seq (RexpReal_R t j))) ⟨2, 2 * j + 1 + 1⟩) := by
    simp only [Qeq, add]; push_cast; ring_uor
  have hmain : Qle (add (⟨1, 1⟩ : Q) (t.seq (2 * j + 1)))
      (add (add (expSum (t.seq (RexpReal_R t j)) (RexpReal_R t j)) ⟨3, RexpReal_R t j + 1⟩)
        ⟨2, 2 * j + 1 + 1⟩) := by
    refine Qle_trans (b := add (add (⟨1, 1⟩ : Q) (t.seq (RexpReal_R t j))) ⟨2, 2 * j + 1 + 1⟩)
      (add_den_pos (add_den_pos (by decide) (t.den_pos _)) (Nat.succ_pos _)) ?_
      (Qadd_le_add hlb (Qle_refl _))
    exact Qle_trans (add_den_pos (by decide) (add_den_pos (t.den_pos _) (Nat.succ_pos _)))
      (Qadd_le_add (Qle_refl _) ht1) (Qeq_le hassoc1)
  -- the slack reduction `3/(N+1) + 1/(j+1) ≤ 2/(j+1)`
  have h31 : Qle (⟨3, RexpReal_R t j + 1⟩ : Q) (⟨1, j + 1⟩ : Q) := by
    simp only [Qle]; push_cast; omega
  have hBC : Qle (add (⟨3, RexpReal_R t j + 1⟩ : Q) ⟨2, 2 * j + 1 + 1⟩) (⟨2, j + 1⟩ : Q) :=
    Qle_trans (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Qadd_le_add h31 (Qle_refl _))
      (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor))
  refine Qle_trans (b := add (add (expSum (t.seq (RexpReal_R t j)) (RexpReal_R t j))
    ⟨3, RexpReal_R t j + 1⟩) ⟨2, 2 * j + 1 + 1⟩)
    (add_den_pos (add_den_pos (expSum_den_pos hqd _) (Nat.succ_pos _)) (Nat.succ_pos _)) hmain ?_
  refine Qle_trans (b := add (expSum (t.seq (RexpReal_R t j)) (RexpReal_R t j))
    (add ⟨3, RexpReal_R t j + 1⟩ ⟨2, 2 * j + 1 + 1⟩))
    (add_den_pos (expSum_den_pos hqd _) (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
    (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor)) (Qadd_le_add (Qle_refl _) hBC)

-- ===========================================================================
-- Toward `Re s ∈ (1,2)` via the artanh ADDITION formula (the only reflection-free route to
-- log-multiplicativity). STEP 1 — the rational connector `tmap(2b) = g(tmap b)`, `g(w)=(1+3w)/(3+w)`,
-- the inner of `artanh(⅓)+artanh(w)=artanh(g(w))`. Mirrors `uval`/`uval_rel`/`tmap_sq_uval`.
-- ===========================================================================

/-- Fresh-`Int`-var core for `gval_rel` (dodges `ring_uor`'s cast-reifier issue, cf. `tmap_uval_core`). -/
private theorem gval_rel_core (wn d : Int) :
    (3 * d + wn * 1) * (d + 3 * wn) * (1 * (1 * d))
      = (1 * (1 * d) + 3 * wn * 1) * (1 * d * (3 * d + wn)) := by ring_uor

/-- Fresh-`Int`-var core for `tmap_two_law`'s cleared cross-relation. -/
private theorem tmap_two_law_core (B d : Int) :
    (3 * (d * 1 * (B * 1 + 1 * d)) + (B * 1 + -1 * d) * (d * 1) * 1) *
        ((2 * B * 1 + -1 * (1 * d)) * (1 * d * 1)) *
      (1 * (1 * (d * 1 * (B * 1 + 1 * d)))) =
    (1 * (1 * (d * 1 * (B * 1 + 1 * d))) + 3 * ((B * 1 + -1 * d) * (d * 1)) * 1) *
      (1 * (d * 1 * (B * 1 + 1 * d)) * (1 * d * 1 * (2 * B * 1 + 1 * (1 * d)))) := by ring_uor

/-- `g(w) = (1+3w)/(3+w)` as a rational (the addition-with-`tmap 2 = ⅓` inner map), for `w ≥ 0`. -/
def gval (w : Q) : Q := ⟨(w.den : Int) + 3 * w.num, (3 * (w.den : Int) + w.num).natAbs⟩

theorem gval_den_pos (w : Q) (hwd : 0 < w.den) (hwn : 0 ≤ w.num) : 0 < (gval w).den := by
  show 0 < (3 * (w.den : Int) + w.num).natAbs
  have hd : (0 : Int) < (w.den : Int) := by exact_mod_cast hwd
  omega

/-- The defining relation `(3+w)·g(w) = 1+3w` (for `w ≥ 0`). -/
theorem gval_rel (w : Q) (hwd : 0 < w.den) (hwn : 0 ≤ w.num) :
    Qeq (mul (add ⟨3, 1⟩ w) (gval w)) (add ⟨1, 1⟩ (mul ⟨3, 1⟩ w)) := by
  have h : (0 : Int) ≤ 3 * (w.den : Int) + w.num := by
    have : (0 : Int) ≤ (w.den : Int) := Int.ofNat_nonneg _; omega
  simp only [Qeq, mul, add, gval]; push_cast [Int.natAbs_of_nonneg h]
  exact gval_rel_core w.num (w.den : Int)

/-- **The `tmap` addition connector**: `tmap(2b) = g(tmap b)` for `b ≥ 1` — i.e. the inner map of the
    artanh addition with `tmap 2 = ⅓`. Both sides `= (2b−1)/(2b+1)`. Via the cleared cross-relation
    `(3+tmap b)·tmap(2b) = 1+3·tmap b` and `gval_rel`, then `Qmul_cancel_left` (cf. `tmap_sq_uval`). -/
theorem tmap_two_law (b : Q) (hbd : 0 < b.den) (hb1 : 0 < (add b ⟨1, 1⟩).num)
    (hb2 : 0 < (add (mul ⟨2, 1⟩ b) ⟨1, 1⟩).num) (htn : 0 ≤ (tmap b).num) :
    Qeq (tmap (mul ⟨2, 1⟩ b)) (gval (tmap b)) := by
  have htd : 0 < (tmap b).den := Qmul_den_pos (Qsub_den_pos hbd Nat.one_pos) (Qinv_den_pos hb1)
  have hcn : 0 < (add ⟨3, 1⟩ (tmap b)).num := by
    show 0 < 3 * ((tmap b).den : Int) + (tmap b).num * 1
    have hd : (0 : Int) < ((tmap b).den : Int) := by exact_mod_cast htd
    omega
  have hcd : 0 < (add ⟨3, 1⟩ (tmap b)).den := add_den_pos Nat.one_pos htd
  have rel1 : Qeq (mul (add ⟨3, 1⟩ (tmap b)) (tmap (mul ⟨2, 1⟩ b)))
      (add ⟨1, 1⟩ (mul ⟨3, 1⟩ (tmap b))) := by
    have hb1c := hb1; have hb2c := hb2
    simp only [mul, add] at hb1c hb2c
    push_cast at hb1c hb2c
    simp only [tmap, mul, add, Qsub, neg, Qinv, Qeq]
    push_cast [Int.toNat_of_nonneg (Int.le_of_lt hb1c), Int.toNat_of_nonneg (Int.le_of_lt hb2c)]
    exact tmap_two_law_core b.num (b.den : Int)
  exact Qmul_cancel_left hcn hcd
    (Qeq_trans (add_den_pos Nat.one_pos (Qmul_den_pos (by decide) htd)) rel1
      (Qeq_symm (gval_rel (tmap b) htd htn)))

-- ===========================================================================
-- STEP 2a — the **δ-series** `δ(w) = g(w) − ⅓ = 8w/(9+3w)` (the vanishing inner of the artanh
-- addition: `δ(0)=0`, `δₖ = (8/9)(−1/3)^{k−1}` for `k≥1`) and its cleared defining relation
-- `(9+3w)·δ = 8w`. Mirrors `kdbl`/`kdbl_rel` (using scaled monomials `fsmono`).
-- ===========================================================================

/-- The δ-series `δ(w) = 8w/(9+3w)`: `δ₀=0`, `δ_{k+1} = (8/9)(−1/3)ᵏ`. Vanishes at `0`. -/
def dcoef : Nat → Q
  | 0 => ⟨0, 1⟩
  | (k + 1) => mul ⟨8, 9⟩ (qpow ⟨-1, 3⟩ k)

theorem dcoef_den : ∀ k, 0 < (dcoef k).den
  | 0 => Nat.one_pos
  | (k + 1) => Qmul_den_pos (by decide) (qpow_den_pos (by decide) k)

theorem dcoef_zero : Qeq (dcoef 0) ⟨0, 1⟩ := Qeq_refl _

/-- The `(9+3w)` series (the cleared denominator of `δ`). -/
def nine3w (k : Nat) : Q := ⟨(if k = 0 then 9 else if k = 1 then 3 else 0 : Int), 1⟩
theorem nine3w_den (k : Nat) : 0 < (nine3w k).den := Nat.one_pos

/-- The `8w` series. -/
def eightT (k : Nat) : Q := ⟨(if k = 1 then 8 else 0 : Int), 1⟩
theorem eightT_den (k : Nat) : 0 < (eightT k).den := Nat.one_pos

/-- `(9+3w) = 9·t⁰ + 3·t¹` as scaled monomials. -/
theorem nine3w_split (k : Nat) :
    Qeq (nine3w k) (add (fsmono ⟨9, 1⟩ 0 k) (fsmono ⟨3, 1⟩ 1 k)) := by
  unfold nine3w fsmono
  by_cases h0 : k = 0
  · subst h0; decide
  · by_cases h1 : k = 1
    · subst h1; decide
    · simp only [if_neg h0, if_neg h1]; decide

/-- The scalar cancellation `9·(8/9)(−1/3)·P + 3·(8/9)·P = 0` (the `(−1/3)`-ratio collapse). -/
theorem dcoef_cancel_scalar (P : Q) :
    Qeq (add (mul ⟨9, 1⟩ (mul ⟨8, 9⟩ (mul ⟨-1, 3⟩ P))) (mul ⟨3, 1⟩ (mul ⟨8, 9⟩ P))) ⟨0, 1⟩ := by
  simp only [Qeq, mul, add]; push_cast; ring_uor

/-- The two-term sign cancellation `9·δ_{m+2} + 3·δ_{m+1} = 0` (`(−1/3)` ratio). -/
theorem dcoef_shift_cancel (m : Nat) :
    Qeq (add (mul ⟨9, 1⟩ (dcoef (m + 2))) (mul ⟨3, 1⟩ (dcoef (m + 1)))) ⟨0, 1⟩ := by
  show Qeq (add (mul ⟨9, 1⟩ (mul ⟨8, 9⟩ (qpow ⟨-1, 3⟩ (m + 1))))
      (mul ⟨3, 1⟩ (mul ⟨8, 9⟩ (qpow ⟨-1, 3⟩ m)))) ⟨0, 1⟩
  rw [qpow_succ]
  exact dcoef_cancel_scalar (qpow ⟨-1, 3⟩ m)

/-- The per-degree split `((9+3w)·δ)_k = 9δ_k + 3δ_{k−1} = (8w)_k`. -/
theorem dcoef_main : ∀ k,
    Qeq (add (fmul (fsmono ⟨9, 1⟩ 0) dcoef k) (fmul (fsmono ⟨3, 1⟩ 1) dcoef k)) (eightT k)
  | 0 => by
      have h0 : Qeq (fmul (fsmono ⟨9, 1⟩ 0) dcoef 0) (mul ⟨9, 1⟩ (dcoef 0)) :=
        fmul_fsmono (by decide) dcoef dcoef_den 0 (by omega)
      have h1 : Qeq (fmul (fsmono ⟨3, 1⟩ 1) dcoef 0) ⟨0, 1⟩ :=
        fmul_fsmono_zero (by decide) dcoef dcoef_den 1 (by omega)
      exact Qeq_trans (add_den_pos (Qmul_den_pos (by decide) (dcoef_den 0)) Nat.one_pos)
        (Qadd_congr h0 h1) (by decide)
  | 1 => by
      have h0 : Qeq (fmul (fsmono ⟨9, 1⟩ 0) dcoef 1) (mul ⟨9, 1⟩ (dcoef 1)) :=
        fmul_fsmono (by decide) dcoef dcoef_den 0 (by omega)
      have h1 : Qeq (fmul (fsmono ⟨3, 1⟩ 1) dcoef 1) (mul ⟨3, 1⟩ (dcoef 0)) :=
        fmul_fsmono (by decide) dcoef dcoef_den 1 (by omega)
      exact Qeq_trans (add_den_pos (Qmul_den_pos (by decide) (dcoef_den 1))
        (Qmul_den_pos (by decide) (dcoef_den 0))) (Qadd_congr h0 h1) (by decide)
  | (m + 2) => by
      have h0 : Qeq (fmul (fsmono ⟨9, 1⟩ 0) dcoef (m + 2)) (mul ⟨9, 1⟩ (dcoef (m + 2))) :=
        fmul_fsmono (by decide) dcoef dcoef_den 0 (by omega)
      have h1 : Qeq (fmul (fsmono ⟨3, 1⟩ 1) dcoef (m + 2)) (mul ⟨3, 1⟩ (dcoef (m + 1))) :=
        fmul_fsmono (by decide) dcoef dcoef_den 1 (by omega)
      refine Qeq_trans (add_den_pos (Qmul_den_pos (by decide) (dcoef_den (m + 2)))
        (Qmul_den_pos (by decide) (dcoef_den (m + 1)))) (Qadd_congr h0 h1) ?_
      have ht : Qeq (⟨0, 1⟩ : Q) (eightT (m + 2)) := by
        unfold eightT; rw [if_neg (by omega)]; exact Qeq_refl _
      exact Qeq_trans Nat.one_pos (dcoef_shift_cancel m) ht

/-- **The δ defining relation** `(9+3w)·δ = 8w`. -/
theorem dcoef_rel (k : Nat) : Qeq (fmul nine3w dcoef k) (eightT k) := by
  have hsplit_den : ∀ i, 0 < (add (fsmono ⟨9, 1⟩ 0 i) (fsmono ⟨3, 1⟩ 1 i)).den :=
    fun i => add_den_pos (fsmono_den (by decide) 0 i) (fsmono_den (by decide) 1 i)
  have e1 : Qeq (fmul nine3w dcoef k)
      (add (fmul (fsmono ⟨9, 1⟩ 0) dcoef k) (fmul (fsmono ⟨3, 1⟩ 1) dcoef k)) :=
    Qeq_trans (fmul_den_pos hsplit_den dcoef_den k)
      (fmul_congr_left nine3w_split k)
      (fmul_add_left (fsmono_den (by decide) 0) (fsmono_den (by decide) 1) dcoef_den k)
  exact Qeq_trans (add_den_pos (fmul_den_pos (fsmono_den (by decide) 0) dcoef_den k)
    (fmul_den_pos (fsmono_den (by decide) 1) dcoef_den k)) e1 (dcoef_main k)

-- ===========================================================================
-- STEP 2b — the **differentiated δ relation** `3δ + (9+3w)·δ' = 8` (Leibniz on `dcoef_rel`, since
-- `d/dw(9+3w)=3` and `d/dw(8w)=8`). Mirrors `kdbl_deriv_rel`. With `dcoef_rel` this pins `δ` and `δ'`.
-- ===========================================================================

/-- The constant `3` series `= d/dw(9+3w)`. -/
def threeFone (k : Nat) : Q := ⟨(if k = 0 then 3 else 0 : Int), 1⟩
theorem threeFone_den (k : Nat) : 0 < (threeFone k).den := Nat.one_pos

/-- The constant `8` series `= d/dw(8w)`. -/
def eightFone (k : Nat) : Q := ⟨(if k = 0 then 8 else 0 : Int), 1⟩
theorem eightFone_den (k : Nat) : 0 < (eightFone k).den := Nat.one_pos

/-- `d/dw(9+3w) = 3`. -/
theorem fderiv_nine3w : ∀ k, Qeq (fderiv nine3w k) (threeFone k)
  | 0 => by decide
  | (k + 1) => by
      show Qeq (mul ⟨(k + 1 + 1 : Int), 1⟩ (nine3w (k + 1 + 1))) (threeFone (k + 1))
      have hn : nine3w (k + 1 + 1) = ⟨0, 1⟩ := by
        unfold nine3w; rw [if_neg (by omega), if_neg (by omega)]
      have ht : threeFone (k + 1) = ⟨0, 1⟩ := by unfold threeFone; rw [if_neg (by omega)]
      rw [hn, ht]; simp [Qeq, mul]

/-- `d/dw(8w) = 8`. -/
theorem fderiv_eightT : ∀ k, Qeq (fderiv eightT k) (eightFone k)
  | 0 => by decide
  | (k + 1) => by
      show Qeq (mul ⟨(k + 1 + 1 : Int), 1⟩ (eightT (k + 1 + 1))) (eightFone (k + 1))
      have he : eightT (k + 1 + 1) = ⟨0, 1⟩ := by unfold eightT; rw [if_neg (by omega)]
      have hf : eightFone (k + 1) = ⟨0, 1⟩ := by unfold eightFone; rw [if_neg (by omega)]
      rw [he, hf]; simp [Qeq, mul]

/-- **The differentiated relation** `3·δ + (9+3w)·δ' = 8` (Leibniz `fderiv_fmul` on `dcoef_rel`). -/
theorem dcoef_deriv_rel (k : Nat) :
    Qeq (add (fmul threeFone dcoef k) (fmul nine3w (fderiv dcoef) k)) (eightFone k) := by
  have e1 : Qeq (fderiv (fmul nine3w dcoef) k)
      (add (fmul (fderiv nine3w) dcoef k) (fmul nine3w (fderiv dcoef) k)) :=
    fderiv_fmul nine3w dcoef nine3w_den dcoef_den k
  have e4 : Qeq (fmul (fderiv nine3w) dcoef k) (fmul threeFone dcoef k) :=
    fmul_congr_left fderiv_nine3w k
  have step1 : Qeq (fderiv (fmul nine3w dcoef) k)
      (add (fmul threeFone dcoef k) (fmul nine3w (fderiv dcoef) k)) :=
    Qeq_trans (add_den_pos (fmul_den_pos (fun i => fderiv_den_pos nine3w_den i) dcoef_den k)
        (fmul_den_pos nine3w_den (fun i => fderiv_den_pos dcoef_den i) k)) e1
      (Qadd_congr e4 (Qeq_refl _))
  have step2 : Qeq (fderiv (fmul nine3w dcoef) k) (eightFone k) :=
    Qeq_trans (fderiv_den_pos eightT_den k) (fderiv_congr dcoef_rel k) (fderiv_eightT k)
  exact Qeq_trans (fderiv_den_pos (fun i => fmul_den_pos nine3w_den dcoef_den i) k)
    (Qeq_symm step1) step2

-- ===========================================================================
-- STEP 2c-pre — **`(9+3w)` is a unit**: `fmul nine3w` is injective (cancellation). The defining
-- denominator of `δ` and `g`; needed to clear `A=(9+3w)` in the formal δ-ODE identity (STEP 2c).
-- First-order recurrence `9·Z_k + 3·Z_{k−1} = 0`, `Z₀=0 ⇒ Z≡0`. Mirrors `fmul_oneplusSq_cancel`.
-- ===========================================================================

/-- `9·X ≈ 0 ⇒ X ≈ 0`. -/
theorem mul9_eq_zero {X : Q} (h : Qeq (mul ⟨9, 1⟩ X) ⟨0, 1⟩) : Qeq X ⟨0, 1⟩ := by
  simp only [Qeq, mul] at h ⊢; push_cast at h ⊢; omega

/-- `((9+3w)·X)_0 = 9·X_0`. -/
theorem nine3w_eval0 (X : Nat → Q) (hX : ∀ i, 0 < (X i).den) :
    Qeq (fmul nine3w X 0) (mul ⟨9, 1⟩ (X 0)) := by
  have e0 : Qeq (fmul nine3w X 0)
      (add (fmul (fsmono ⟨9, 1⟩ 0) X 0) (fmul (fsmono ⟨3, 1⟩ 1) X 0)) :=
    Qeq_trans (fmul_den_pos (fun i => add_den_pos (fsmono_den (by decide) 0 i)
        (fsmono_den (by decide) 1 i)) hX 0) (fmul_congr_left nine3w_split 0)
      (fmul_add_left (fsmono_den (by decide) 0) (fsmono_den (by decide) 1) hX 0)
  have h9 : Qeq (fmul (fsmono ⟨9, 1⟩ 0) X 0) (mul ⟨9, 1⟩ (X 0)) :=
    fmul_fsmono (by decide) X hX 0 (by omega)
  have h3 : Qeq (fmul (fsmono ⟨3, 1⟩ 1) X 0) ⟨0, 1⟩ := fmul_fsmono_zero (by decide) X hX 1 (by omega)
  refine Qeq_trans (add_den_pos (fmul_den_pos (fsmono_den (by decide) 0) hX 0)
    (fmul_den_pos (fsmono_den (by decide) 1) hX 0)) e0 ?_
  exact Qeq_trans (add_den_pos (Qmul_den_pos (by decide) (hX 0)) Nat.one_pos)
    (Qadd_congr h9 h3) (Qadd_zero_right _)

/-- `((9+3w)·X)_{n+1} = 9·X_{n+1} + 3·X_n`. -/
theorem nine3w_eval_succ (X : Nat → Q) (hX : ∀ i, 0 < (X i).den) (n : Nat) :
    Qeq (fmul nine3w X (n + 1)) (add (mul ⟨9, 1⟩ (X (n + 1))) (mul ⟨3, 1⟩ (X n))) := by
  have e0 : Qeq (fmul nine3w X (n + 1))
      (add (fmul (fsmono ⟨9, 1⟩ 0) X (n + 1)) (fmul (fsmono ⟨3, 1⟩ 1) X (n + 1))) :=
    Qeq_trans (fmul_den_pos (fun i => add_den_pos (fsmono_den (by decide) 0 i)
        (fsmono_den (by decide) 1 i)) hX (n + 1)) (fmul_congr_left nine3w_split (n + 1))
      (fmul_add_left (fsmono_den (by decide) 0) (fsmono_den (by decide) 1) hX (n + 1))
  have h9 : Qeq (fmul (fsmono ⟨9, 1⟩ 0) X (n + 1)) (mul ⟨9, 1⟩ (X (n + 1))) := by
    have hh := fmul_fsmono (c := ⟨9, 1⟩) (by decide) X hX 0 (show 0 ≤ n + 1 by omega)
    rwa [Nat.sub_zero] at hh
  have h3 : Qeq (fmul (fsmono ⟨3, 1⟩ 1) X (n + 1)) (mul ⟨3, 1⟩ (X n)) := by
    have hh := fmul_fsmono (c := ⟨3, 1⟩) (by decide) X hX 1 (show 1 ≤ n + 1 by omega)
    rwa [show n + 1 - 1 = n from by omega] at hh
  refine Qeq_trans (add_den_pos (fmul_den_pos (fsmono_den (by decide) 0) hX (n + 1))
    (fmul_den_pos (fsmono_den (by decide) 1) hX (n + 1))) e0 ?_
  exact Qadd_congr h9 h3

/-- `(9+3w)·Z = 0 ⇒ Z = 0`. -/
theorem nine3w_zero_cancel {Z : Nat → Q} (hZ : ∀ i, 0 < (Z i).den)
    (h : ∀ k, Qeq (fmul nine3w Z k) ⟨0, 1⟩) : ∀ k, Qeq (Z k) ⟨0, 1⟩ := by
  intro k
  induction k with
  | zero => exact mul9_eq_zero (Qeq_trans (fmul_den_pos nine3w_den hZ 0)
      (Qeq_symm (nine3w_eval0 Z hZ)) (h 0))
  | succ n ih =>
      have hev : Qeq (add (mul ⟨9, 1⟩ (Z (n + 1))) (mul ⟨3, 1⟩ (Z n))) ⟨0, 1⟩ :=
        Qeq_trans (fmul_den_pos nine3w_den hZ (n + 1))
          (Qeq_symm (nine3w_eval_succ Z hZ n)) (h (n + 1))
      have h9z : Qeq (mul ⟨9, 1⟩ (Z (n + 1))) ⟨0, 1⟩ := by
        have hrw : Qeq (mul ⟨9, 1⟩ (Z (n + 1)))
            (Qsub (add (mul ⟨9, 1⟩ (Z (n + 1))) (mul ⟨3, 1⟩ (Z n))) (mul ⟨3, 1⟩ (Z n))) := by
          simp only [Qeq, add, Qsub, neg, mul]; push_cast; ring_uor
        have h3z : Qeq (mul ⟨3, 1⟩ (Z n)) ⟨0, 1⟩ := by
          have hin := ih; simp only [Qeq, mul] at hin ⊢; push_cast at hin ⊢; omega
        exact Qeq_trans (Qsub_den_pos (add_den_pos (Qmul_den_pos (by decide) (hZ (n + 1)))
            (Qmul_den_pos (by decide) (hZ n))) (Qmul_den_pos (by decide) (hZ n))) hrw
          (Qeq_trans (Qsub_den_pos Nat.one_pos Nat.one_pos) (Qsub_congr hev h3z)
            (by simp [Qeq, Qsub, add, neg]))
      exact mul9_eq_zero h9z

/-- **`fmul nine3w` is injective**: the `(9+3w)`-cancellation. -/
theorem fmul_nine3w_cancel {X Y : Nat → Q} (hX : ∀ i, 0 < (X i).den) (hY : ∀ i, 0 < (Y i).den)
    (h : ∀ k, Qeq (fmul nine3w X k) (fmul nine3w Y k)) (k : Nat) : Qeq (X k) (Y k) := by
  have hZ : ∀ i, 0 < (Qsub (X i) (Y i)).den := fun i => Qsub_den_pos (hX i) (hY i)
  have hzero : ∀ m, Qeq (fmul nine3w (fun i => Qsub (X i) (Y i)) m) ⟨0, 1⟩ := by
    intro m
    have hXc : Qeq (fmul (fun i => Qsub (X i) (Y i)) nine3w m)
        (Qsub (fmul X nine3w m) (fmul Y nine3w m)) := fmul_sub_left hX hY nine3w_den m
    refine Qeq_trans (fmul_den_pos hZ nine3w_den m)
      (fmul_comm nine3w (fun i => Qsub (X i) (Y i)) nine3w_den hZ m) ?_
    refine Qeq_trans (Qsub_den_pos (fmul_den_pos hX nine3w_den m) (fmul_den_pos hY nine3w_den m))
      hXc ?_
    refine Qeq_trans (Qsub_den_pos (fmul_den_pos nine3w_den hX m) (fmul_den_pos nine3w_den hY m))
      (Qsub_congr (fmul_comm X nine3w hX nine3w_den m) (fmul_comm Y nine3w hY nine3w_den m)) ?_
    exact Qeq_trans (Qsub_den_pos (fmul_den_pos nine3w_den hX m) (fmul_den_pos nine3w_den hX m))
      (Qsub_congr (Qeq_refl _) (Qeq_symm (h m))) (by simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor)
  exact Qeq_of_Qsub_zero (nine3w_zero_cancel hZ hzero k)

-- ===========================================================================
-- STEP 2c — the **key δ-ODE identity** `9·(1−w²)·δ' = 8 − 6δ − 9δ²` (i.e. `9(1−g²)`). This is where
-- the geometry `g'(1−w²)=1−g²` lives. Proved by clearing `A²=(9+3w)²` (two `fmul_nine3w_cancel`s):
-- after clearing, both sides collapse (via `dcoef_rel`/`dcoef_deriv_rel`) to the δ-free `648(1−w²)`.
-- ===========================================================================

/-- `threeFone = 3·t⁰` as a scaled monomial. -/
theorem threeFone_eq_fsmono (k : Nat) : Qeq (threeFone k) (fsmono ⟨3, 1⟩ 0 k) := by
  unfold threeFone fsmono; by_cases h : k = 0 <;> simp only [if_pos, if_neg, h] <;> decide

/-- The rearranged differentiated relation: `(9+3w)·δ' = 8 − 3δ`. -/
theorem nine3w_dderiv (k : Nat) :
    Qeq (fmul nine3w (fderiv dcoef) k) (Qsub (eightFone k) (mul ⟨3, 1⟩ (dcoef k))) := by
  have h3 : Qeq (fmul threeFone dcoef k) (mul ⟨3, 1⟩ (dcoef k)) := by
    refine Qeq_trans (fmul_den_pos (fun i => fsmono_den (by decide) 0 i) dcoef_den k)
      (fmul_congr_left threeFone_eq_fsmono k) ?_
    have hh := fmul_fsmono (c := ⟨3, 1⟩) (by decide) dcoef dcoef_den 0 (Nat.zero_le k)
    rwa [Nat.sub_zero] at hh
  have hrw : Qeq (fmul nine3w (fderiv dcoef) k)
      (Qsub (add (fmul threeFone dcoef k) (fmul nine3w (fderiv dcoef) k))
        (fmul threeFone dcoef k)) := by simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
  refine Qeq_trans (Qsub_den_pos (add_den_pos (fmul_den_pos (fun i => threeFone_den i) dcoef_den k)
      (fmul_den_pos nine3w_den (fun i => fderiv_den_pos dcoef_den i) k))
      (fmul_den_pos (fun i => threeFone_den i) dcoef_den k)) hrw ?_
  exact Qsub_congr (dcoef_deriv_rel k) h3

/-- `(9+3w)·δ² = δ·8w` (`nine3w·δ² = δ·eightT`, via `fmul_swap_left` + `dcoef_rel`). -/
theorem nine3w_dsq (k : Nat) :
    Qeq (fmul nine3w (fmul dcoef dcoef) k) (fmul dcoef eightT k) := by
  refine Qeq_trans (fmul_den_pos dcoef_den (fun i => fmul_den_pos nine3w_den dcoef_den i) k)
    (fmul_swap_left nine3w dcoef dcoef nine3w_den dcoef_den dcoef_den k) ?_
  exact fmul_congr_right (fun i => dcoef_rel i) k

/-- `8w = 8·t¹` as a scaled monomial. -/
theorem eightT_eq_fsmono (k : Nat) : Qeq (eightT k) (fsmono ⟨8, 1⟩ 1 k) := by
  unfold eightT fsmono; by_cases h : k = 1 <;> simp only [if_pos, if_neg, h] <;> decide

-- The three δ-free polynomial products feeding the collapse `648(1−w²)` (STEP 2c, post-`A²`-clearing).

/-- `(8w)² = 64w²`. -/
theorem eightT_sq_val (j : Nat) : Qeq (fmul eightT eightT j) ⟨(if j = 2 then 64 else 0 : Int), 1⟩ := by
  have e1 : Qeq (fmul eightT eightT j) (fmul (fsmono ⟨8, 1⟩ 1) eightT j) :=
    fmul_congr_left eightT_eq_fsmono j
  refine Qeq_trans (fmul_den_pos (fun i => fsmono_den (by decide) 1 i) eightT_den j) e1 ?_
  match j with
  | 0 => exact Qeq_trans Nat.one_pos (fmul_fsmono_zero (by decide) eightT eightT_den 1 (by omega)) (by decide)
  | (n + 1) =>
      refine Qeq_trans (Qmul_den_pos (by decide) (eightT_den n))
        (fmul_fsmono (c := ⟨8, 1⟩) (by decide) eightT eightT_den 1 (by omega)) ?_
      match n with
      | 1 => decide
      | 0 => decide
      | (m + 2) =>
          have he : eightT (m + 2) = ⟨0, 1⟩ := by unfold eightT; rw [if_neg (by omega)]
          rw [he]; simp only [Qeq, mul]; split <;> omega

/-- `(9+3w)² = 81 + 54w + 9w²`. -/
theorem nine3w_sq_val (j : Nat) :
    Qeq (fmul nine3w nine3w j) ⟨(if j = 0 then 81 else if j = 1 then 54 else if j = 2 then 9 else 0 : Int), 1⟩ := by
  match j with
  | 0 => exact Qeq_trans (Qmul_den_pos (by decide) (nine3w_den 0)) (nine3w_eval0 nine3w nine3w_den) (by decide)
  | (n + 1) =>
      refine Qeq_trans (add_den_pos (Qmul_den_pos (by decide) (nine3w_den (n + 1)))
        (Qmul_den_pos (by decide) (nine3w_den n))) (nine3w_eval_succ nine3w nine3w_den n) ?_
      match n with
      | 0 => decide
      | 1 => decide
      | (m + 2) =>
          have h1 : nine3w (m + 2 + 1) = ⟨0, 1⟩ := by
            unfold nine3w; rw [if_neg (by omega), if_neg (by omega)]
          have h2 : nine3w (m + 2) = ⟨0, 1⟩ := by
            unfold nine3w; rw [if_neg (by omega), if_neg (by omega)]
          rw [h1, h2]; simp only [Qeq, add, mul]; split <;> omega

/-- `(9+3w)·8w = 72w + 24w²`. -/
theorem nine3w_eightT_val (j : Nat) :
    Qeq (fmul nine3w eightT j) ⟨(if j = 1 then 72 else if j = 2 then 24 else 0 : Int), 1⟩ := by
  match j with
  | 0 => exact Qeq_trans (Qmul_den_pos (by decide) (eightT_den 0)) (nine3w_eval0 eightT eightT_den) (by decide)
  | (n + 1) =>
      refine Qeq_trans (add_den_pos (Qmul_den_pos (by decide) (eightT_den (n + 1)))
        (Qmul_den_pos (by decide) (eightT_den n))) (nine3w_eval_succ eightT eightT_den n) ?_
      match n with
      | 0 => decide
      | 1 => decide
      | (m + 2) =>
          have h1 : eightT (m + 2 + 1) = ⟨0, 1⟩ := by unfold eightT; rw [if_neg (by omega)]
          have h2 : eightT (m + 2) = ⟨0, 1⟩ := by unfold eightT; rw [if_neg (by omega)]
          rw [h1, h2]; simp only [Qeq, add, mul]; split <;> omega

/-- **The δ-free collapse** `648(1−w²) = 8(9+3w)² − 6(9+3w)·8w − 9·(8w)²` (both `= 648 − 648w²`).
    This is `9(1−w²)δ' = 8−6δ−9δ²` after clearing `A²=(9+3w)²` (STEP 2c). -/
theorem g2_final (j : Nat) :
    Qeq (mul ⟨648, 1⟩ (oneMinusSq j))
      (Qsub (Qsub (mul ⟨8, 1⟩ (fmul nine3w nine3w j)) (mul ⟨6, 1⟩ (fmul nine3w eightT j)))
        (mul ⟨9, 1⟩ (fmul eightT eightT j))) := by
  have hR : Qeq
      (Qsub (Qsub (mul ⟨8, 1⟩ ⟨(if j = 0 then 81 else if j = 1 then 54 else if j = 2 then 9 else 0 : Int), 1⟩)
                  (mul ⟨6, 1⟩ ⟨(if j = 1 then 72 else if j = 2 then 24 else 0 : Int), 1⟩))
            (mul ⟨9, 1⟩ ⟨(if j = 2 then 64 else 0 : Int), 1⟩))
      (Qsub (Qsub (mul ⟨8, 1⟩ (fmul nine3w nine3w j)) (mul ⟨6, 1⟩ (fmul nine3w eightT j)))
        (mul ⟨9, 1⟩ (fmul eightT eightT j))) :=
    Qsub_congr (Qsub_congr (Qmul_congr (Qeq_refl _) (Qeq_symm (nine3w_sq_val j)))
        (Qmul_congr (Qeq_refl _) (Qeq_symm (nine3w_eightT_val j))))
      (Qmul_congr (Qeq_refl _) (Qeq_symm (eightT_sq_val j)))
  refine Qeq_trans (Qsub_den_pos (Qsub_den_pos (Qmul_den_pos Nat.one_pos Nat.one_pos)
    (Qmul_den_pos Nat.one_pos Nat.one_pos)) (Qmul_den_pos Nat.one_pos Nat.one_pos)) ?_ hR
  match j with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | (m + 3) =>
      have ho : oneMinusSq (m + 3) = ⟨0, 1⟩ := by
        unfold oneMinusSq fsmono; rw [if_neg (by omega), if_neg (by omega)]; decide
      rw [ho, if_neg (show ¬(m + 3 = 0) by omega), if_neg (show ¬(m + 3 = 1) by omega),
        if_neg (show ¬(m + 3 = 2) by omega), if_neg (show ¬(m + 3 = 1) by omega),
        if_neg (show ¬(m + 3 = 2) by omega), if_neg (show ¬(m + 3 = 2) by omega)]
      decide

/-- `a·(b−c) = a·b − a·c` (right sub-distribution, via `fmul_comm` + `fmul_sub_left`). -/
theorem fmul_sub_right {a b c : Nat → Q} (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den)
    (hc : ∀ i, 0 < (c i).den) (k : Nat) :
    Qeq (fmul a (fun i => Qsub (b i) (c i)) k) (Qsub (fmul a b k) (fmul a c k)) := by
  refine Qeq_trans (fmul_den_pos (fun i => Qsub_den_pos (hb i) (hc i)) ha k)
    (fmul_comm a (fun i => Qsub (b i) (c i)) ha (fun i => Qsub_den_pos (hb i) (hc i)) k) ?_
  refine Qeq_trans (Qsub_den_pos (fmul_den_pos hb ha k) (fmul_den_pos hc ha k))
    (fmul_sub_left hb hc ha k) ?_
  exact Qsub_congr (fmul_comm b a hb ha k) (fmul_comm c a hc ha k)

/-- `eightFone = 8·t⁰` as a scaled series. -/
theorem eightFone_eq_fsmul (k : Nat) : Qeq (eightFone k) (fsmul ⟨8, 1⟩ fone k) := by
  unfold eightFone fsmul fone; by_cases h : k = 0 <;> simp only [if_pos, if_neg, h] <;> decide

/-- `8·(9+3w) − 3·8w = 72` (δ-free, both `= 72`). -/
theorem eight_n_three_e (k : Nat) :
    Qeq (Qsub (mul ⟨8, 1⟩ (nine3w k)) (mul ⟨3, 1⟩ (eightT k))) (mul ⟨72, 1⟩ (fone k)) := by
  match k with
  | 0 => decide
  | 1 => decide
  | (m + 2) =>
      have hn : nine3w (m + 2) = ⟨0, 1⟩ := by unfold nine3w; rw [if_neg (by omega), if_neg (by omega)]
      have he : eightT (m + 2) = ⟨0, 1⟩ := by unfold eightT; rw [if_neg (by omega)]
      have hf : fone (m + 2) = ⟨0, 1⟩ := by unfold fone; rw [if_neg (by omega)]
      rw [hn, he, hf]; decide

/-- **H1**: `(9+3w)·(8 − 3δ) = 72` — the δ-cancelling collapse (`δ` killed by `dcoef_rel`). -/
theorem nine3w_8m3d (k : Nat) :
    Qeq (fmul nine3w (fun i => Qsub (eightFone i) (mul ⟨3, 1⟩ (dcoef i))) k) (mul ⟨72, 1⟩ (fone k)) := by
  have hb : ∀ i, 0 < (eightFone i).den := eightFone_den
  have hc : ∀ i, 0 < (mul ⟨3, 1⟩ (dcoef i)).den := fun i => Qmul_den_pos (by decide) (dcoef_den i)
  -- (9+3w)·(8fone − 3δ) = (9+3w)·8fone − (9+3w)·3δ
  refine Qeq_trans (Qsub_den_pos (fmul_den_pos nine3w_den hb k)
    (fmul_den_pos nine3w_den hc k)) (fmul_sub_right nine3w_den hb hc k) ?_
  -- (9+3w)·8fone ≈ 8·(9+3w); (9+3w)·3δ ≈ 3·8w
  have e1 : Qeq (fmul nine3w eightFone k) (mul ⟨8, 1⟩ (nine3w k)) := by
    refine Qeq_trans (fmul_den_pos nine3w_den (fun i => fsmul_den (by decide) (fun _ => fone_den_pos _) i) k)
      (fmul_congr_right eightFone_eq_fsmul k) ?_
    exact Qeq_trans (Qmul_den_pos (by decide) (fmul_den_pos nine3w_den (fun _ => fone_den_pos _) k))
      (fmul_smul_right nine3w fone ⟨8, 1⟩ (by decide) nine3w_den (fun _ => fone_den_pos _) k)
      (Qmul_congr (Qeq_refl _) (fmul_one nine3w nine3w_den k))
  have e2 : Qeq (fmul nine3w (fun i => mul ⟨3, 1⟩ (dcoef i)) k) (mul ⟨3, 1⟩ (eightT k)) := by
    refine Qeq_trans (Qmul_den_pos (by decide) (fmul_den_pos nine3w_den dcoef_den k))
      (fmul_smul_right nine3w dcoef ⟨3, 1⟩ (by decide) nine3w_den dcoef_den k) ?_
    exact Qmul_congr (Qeq_refl _) (dcoef_rel k)
  exact Qeq_trans (Qsub_den_pos (Qmul_den_pos (by decide) (nine3w_den k))
    (Qmul_den_pos (by decide) (eightT_den k))) (Qsub_congr e1 e2) (eight_n_three_e k)

/-- **H3** (LHS of the double-cleared key identity): `(9+3w)²·((1−w²)·δ') = 72·(1−w²)`. -/
theorem nine3w_M2 (k : Nat) :
    Qeq (fmul nine3w (fmul nine3w (fmul oneMinusSq (fderiv dcoef))) k) (mul ⟨72, 1⟩ (oneMinusSq k)) := by
  have hdd : ∀ i, 0 < (fderiv dcoef i).den := fun i => fderiv_den_pos dcoef_den i
  have hDRd : ∀ i, 0 < (Qsub (eightFone i) (mul ⟨3, 1⟩ (dcoef i))).den :=
    fun i => Qsub_den_pos (eightFone_den i) (Qmul_den_pos (by decide) (dcoef_den i))
  have inner1 : ∀ i, Qeq (fmul nine3w (fmul oneMinusSq (fderiv dcoef)) i)
      (fmul oneMinusSq (fun j => Qsub (eightFone j) (mul ⟨3, 1⟩ (dcoef j))) i) := by
    intro i
    refine Qeq_trans (fmul_den_pos (fun j => oneMinusSq_den j)
      (fun j => fmul_den_pos nine3w_den hdd j) i)
      (fmul_swap_left nine3w oneMinusSq (fderiv dcoef) nine3w_den (fun j => oneMinusSq_den j) hdd i) ?_
    exact fmul_congr_right (fun j => nine3w_dderiv j) i
  refine Qeq_trans (fmul_den_pos nine3w_den
    (fun i => fmul_den_pos (fun j => oneMinusSq_den j) hDRd i) k) (fmul_congr_right inner1 k) ?_
  refine Qeq_trans (fmul_den_pos (fun j => oneMinusSq_den j)
    (fun i => fmul_den_pos nine3w_den hDRd i) k)
    (fmul_swap_left nine3w oneMinusSq (fun j => Qsub (eightFone j) (mul ⟨3, 1⟩ (dcoef j)))
      nine3w_den (fun j => oneMinusSq_den j) hDRd k) ?_
  refine Qeq_trans (fmul_den_pos (fun j => oneMinusSq_den j)
    (fun i => Qmul_den_pos (by decide) (fone_den_pos i)) k)
    (fmul_congr_right (fun i => nine3w_8m3d i) k) ?_
  refine Qeq_trans (Qmul_den_pos (by decide)
    (fmul_den_pos (fun j => oneMinusSq_den j) (fun _ => fone_den_pos _) k))
    (fmul_smul_right oneMinusSq fone ⟨72, 1⟩ (by decide) (fun j => oneMinusSq_den j)
      (fun _ => fone_den_pos _) k) ?_
  exact Qmul_congr (Qeq_refl _) (fmul_one oneMinusSq (fun j => oneMinusSq_den j) k)

/-- The composed-quadratic series `Qcomp = 8 − 6δ − 9δ²` (= eval of `8−6u−9u²` at δ = `9(1−g²)`). -/
def qcomp (k : Nat) : Q :=
  Qsub (Qsub (mul ⟨8, 1⟩ (fone k)) (mul ⟨6, 1⟩ (dcoef k))) (mul ⟨9, 1⟩ (fmul dcoef dcoef k))

theorem qcomp_den (k : Nat) : 0 < (qcomp k).den :=
  Qsub_den_pos (Qsub_den_pos (Qmul_den_pos (by decide) (fone_den_pos k))
    (Qmul_den_pos (by decide) (dcoef_den k))) (Qmul_den_pos (by decide) (fmul_den_pos dcoef_den dcoef_den k))

/-- `(9+3w)·(δ·8w) = (8w)²` (commute, swap `nine3w` onto `δ`, then `dcoef_rel`). -/
theorem nine3w_de (k : Nat) :
    Qeq (fmul nine3w (fmul dcoef eightT) k) (fmul eightT eightT k) := by
  refine Qeq_trans (fmul_den_pos nine3w_den (fun i => fmul_den_pos eightT_den dcoef_den i) k)
    (fmul_congr_right (fun i => fmul_comm dcoef eightT dcoef_den eightT_den i) k) ?_
  refine Qeq_trans (fmul_den_pos eightT_den (fun i => fmul_den_pos nine3w_den dcoef_den i) k)
    (fmul_swap_left nine3w eightT dcoef nine3w_den eightT_den dcoef_den k) ?_
  exact fmul_congr_right (fun i => dcoef_rel i) k

/-- **H2** (1st level): `(9+3w)·Qcomp = 8(9+3w) − 6·8w − 9·(δ·8w)`. -/
theorem nine3w_qcomp1 (k : Nat) :
    Qeq (fmul nine3w qcomp k)
      (Qsub (Qsub (mul ⟨8, 1⟩ (nine3w k)) (mul ⟨6, 1⟩ (eightT k))) (mul ⟨9, 1⟩ (fmul dcoef eightT k))) := by
  have hAd : ∀ i, 0 < (Qsub (mul ⟨8, 1⟩ (fone i)) (mul ⟨6, 1⟩ (dcoef i))).den :=
    fun i => Qsub_den_pos (Qmul_den_pos (by decide) (fone_den_pos i)) (Qmul_den_pos (by decide) (dcoef_den i))
  have hBd : ∀ i, 0 < (mul ⟨9, 1⟩ (fmul dcoef dcoef i)).den :=
    fun i => Qmul_den_pos (by decide) (fmul_den_pos dcoef_den dcoef_den i)
  -- fmul nine3w (Qsub A B) = Qsub (fmul nine3w A) (fmul nine3w B)
  refine Qeq_trans (Qsub_den_pos (fmul_den_pos nine3w_den hAd k) (fmul_den_pos nine3w_den hBd k))
    (fmul_sub_right nine3w_den hAd hBd k) ?_
  refine Qsub_congr ?_ ?_
  · -- fmul nine3w (Qsub 8fone 6δ) = Qsub (8 nine3w) (6 eightT)
    refine Qeq_trans (Qsub_den_pos (fmul_den_pos nine3w_den (fun i => Qmul_den_pos (by decide) (fone_den_pos i)) k)
        (fmul_den_pos nine3w_den (fun i => Qmul_den_pos (by decide) (dcoef_den i)) k))
      (fmul_sub_right nine3w_den (fun i => Qmul_den_pos (by decide) (fone_den_pos i))
        (fun i => Qmul_den_pos (by decide) (dcoef_den i)) k) ?_
    refine Qsub_congr ?_ ?_
    · exact Qeq_trans (Qmul_den_pos (by decide) (fmul_den_pos nine3w_den (fun _ => fone_den_pos _) k))
        (fmul_smul_right nine3w fone ⟨8, 1⟩ (by decide) nine3w_den (fun _ => fone_den_pos _) k)
        (Qmul_congr (Qeq_refl _) (fmul_one nine3w nine3w_den k))
    · exact Qeq_trans (Qmul_den_pos (by decide) (fmul_den_pos nine3w_den dcoef_den k))
        (fmul_smul_right nine3w dcoef ⟨6, 1⟩ (by decide) nine3w_den dcoef_den k)
        (Qmul_congr (Qeq_refl _) (dcoef_rel k))
  · -- fmul nine3w (9 δ²) = 9 (δ·8w)
    exact Qeq_trans (Qmul_den_pos (by decide) (fmul_den_pos nine3w_den (fun i => fmul_den_pos dcoef_den dcoef_den i) k))
      (fmul_smul_right nine3w (fmul dcoef dcoef) ⟨9, 1⟩ (by decide) nine3w_den
        (fun i => fmul_den_pos dcoef_den dcoef_den i) k)
      (Qmul_congr (Qeq_refl _) (nine3w_dsq k))

/-- **H2** (2nd level, RHS of the double-cleared key identity): `(9+3w)²·Qcomp = 8N² − 6N·8w − 9(8w)²`. -/
theorem nine3w_qcomp2 (k : Nat) :
    Qeq (fmul nine3w (fmul nine3w qcomp) k)
      (Qsub (Qsub (mul ⟨8, 1⟩ (fmul nine3w nine3w k)) (mul ⟨6, 1⟩ (fmul nine3w eightT k)))
        (mul ⟨9, 1⟩ (fmul eightT eightT k))) := by
  have hQ1d : ∀ i, 0 < (Qsub (Qsub (mul ⟨8, 1⟩ (nine3w i)) (mul ⟨6, 1⟩ (eightT i)))
      (mul ⟨9, 1⟩ (fmul dcoef eightT i))).den :=
    fun i => Qsub_den_pos (Qsub_den_pos (Qmul_den_pos (by decide) (nine3w_den i))
      (Qmul_den_pos (by decide) (eightT_den i))) (Qmul_den_pos (by decide) (fmul_den_pos dcoef_den eightT_den i))
  have hAd : ∀ i, 0 < (Qsub (mul ⟨8, 1⟩ (nine3w i)) (mul ⟨6, 1⟩ (eightT i))).den :=
    fun i => Qsub_den_pos (Qmul_den_pos (by decide) (nine3w_den i)) (Qmul_den_pos (by decide) (eightT_den i))
  have hBd : ∀ i, 0 < (mul ⟨9, 1⟩ (fmul dcoef eightT i)).den :=
    fun i => Qmul_den_pos (by decide) (fmul_den_pos dcoef_den eightT_den i)
  refine Qeq_trans (fmul_den_pos nine3w_den hQ1d k) (fmul_congr_right (fun i => nine3w_qcomp1 i) k) ?_
  refine Qeq_trans (Qsub_den_pos (fmul_den_pos nine3w_den hAd k) (fmul_den_pos nine3w_den hBd k))
    (fmul_sub_right nine3w_den hAd hBd k) ?_
  refine Qsub_congr ?_ ?_
  · refine Qeq_trans (Qsub_den_pos (fmul_den_pos nine3w_den (fun i => Qmul_den_pos (by decide) (nine3w_den i)) k)
        (fmul_den_pos nine3w_den (fun i => Qmul_den_pos (by decide) (eightT_den i)) k))
      (fmul_sub_right nine3w_den (fun i => Qmul_den_pos (by decide) (nine3w_den i))
        (fun i => Qmul_den_pos (by decide) (eightT_den i)) k) ?_
    refine Qsub_congr ?_ ?_
    · exact Qeq_trans (Qmul_den_pos (by decide) (fmul_den_pos nine3w_den nine3w_den k))
        (fmul_smul_right nine3w nine3w ⟨8, 1⟩ (by decide) nine3w_den nine3w_den k) (Qeq_refl _)
    · exact Qeq_trans (Qmul_den_pos (by decide) (fmul_den_pos nine3w_den eightT_den k))
        (fmul_smul_right nine3w eightT ⟨6, 1⟩ (by decide) nine3w_den eightT_den k) (Qeq_refl _)
  · exact Qeq_trans (Qmul_den_pos (by decide) (fmul_den_pos nine3w_den (fun i => fmul_den_pos dcoef_den eightT_den i) k))
      (fmul_smul_right nine3w (fmul dcoef eightT) ⟨9, 1⟩ (by decide) nine3w_den
        (fun i => fmul_den_pos dcoef_den eightT_den i) k)
      (Qmul_congr (Qeq_refl _) (nine3w_de k))

/-- **★ THE KEY δ-ODE IDENTITY (STEP 2c)** `9·(1−w²)·δ' = 8 − 6δ − 9δ²` (`= 9(1−g²)`). Both sides,
    cleared by `A²=(9+3w)²`, collapse to `648(1−w²)` (`nine3w_M2` / `nine3w_qcomp2` + `g2_final`); the
    identity then follows by two `fmul_nine3w_cancel`s. This is the formal `g'(1−w²)=1−g²` geometry. -/
theorem dcoef_ode (k : Nat) :
    Qeq (mul ⟨9, 1⟩ (fmul oneMinusSq (fderiv dcoef) k)) (qcomp k) := by
  have hMd : ∀ i, 0 < (fmul oneMinusSq (fderiv dcoef) i).den :=
    fun i => fmul_den_pos (fun j => oneMinusSq_den j) (fun j => fderiv_den_pos dcoef_den j) i
  have hLd : ∀ i, 0 < (mul ⟨9, 1⟩ (fmul oneMinusSq (fderiv dcoef) i)).den :=
    fun i => Qmul_den_pos (by decide) (hMd i)
  refine fmul_nine3w_cancel (X := fun i => mul ⟨9, 1⟩ (fmul oneMinusSq (fderiv dcoef) i))
    (Y := qcomp) hLd qcomp_den (fun m => ?_) k
  refine fmul_nine3w_cancel
    (X := fmul nine3w (fun i => mul ⟨9, 1⟩ (fmul oneMinusSq (fderiv dcoef) i)))
    (Y := fmul nine3w qcomp) (fun i => fmul_den_pos nine3w_den hLd i)
    (fun i => fmul_den_pos nine3w_den qcomp_den i) (fun j => ?_) m
  -- goal: fmul nine3w (fmul nine3w L) j ≈ fmul nine3w (fmul nine3w qcomp) j
  have hLHS : Qeq (fmul nine3w (fmul nine3w (fun i => mul ⟨9, 1⟩ (fmul oneMinusSq (fderiv dcoef) i))) j)
      (mul ⟨648, 1⟩ (oneMinusSq j)) := by
    refine Qeq_trans (fmul_den_pos nine3w_den
      (fun i => Qmul_den_pos (by decide) (fmul_den_pos nine3w_den hMd i)) j)
      (fmul_congr_right (fun i => fmul_smul_right nine3w (fmul oneMinusSq (fderiv dcoef)) ⟨9, 1⟩
        (by decide) nine3w_den hMd i) j) ?_
    refine Qeq_trans (Qmul_den_pos (by decide)
      (fmul_den_pos nine3w_den (fun i => fmul_den_pos nine3w_den hMd i) j))
      (fmul_smul_right nine3w (fmul nine3w (fmul oneMinusSq (fderiv dcoef))) ⟨9, 1⟩ (by decide)
        nine3w_den (fun i => fmul_den_pos nine3w_den hMd i) j) ?_
    refine Qeq_trans (Qmul_den_pos (by decide) (Qmul_den_pos (by decide) (oneMinusSq_den j)))
      (Qmul_congr (Qeq_refl _) (nine3w_M2 j)) ?_
    simp only [Qeq, mul]; push_cast; ring_uor
  exact Qeq_trans (Qmul_den_pos (by decide) (oneMinusSq_den j)) hLHS
    (Qeq_trans (Qsub_den_pos (Qsub_den_pos (Qmul_den_pos (by decide) (fmul_den_pos nine3w_den nine3w_den j))
        (Qmul_den_pos (by decide) (fmul_den_pos nine3w_den eightT_den j)))
        (Qmul_den_pos (by decide) (fmul_den_pos eightT_den eightT_den j)))
      (g2_final j) (Qeq_symm (nine3w_qcomp2 j)))

-- ===========================================================================
-- STEP 2d — the **shifted-artanh derivative** `sacD = sacoef' = artanh'(⅓+u) = 9/(8−6u−9u²)` (RATIONAL,
-- the reciprocal of the quadratic `8−6u−9u²`), via its 3-term recurrence `8 sacDₖ = 6 sacD_{k−1} + 9 sacD_{k−2}`.
-- Its ODE `(8−6u−9u²)·sacD = 9` is the defining relation, composed with δ in STEP 2e.
-- ===========================================================================

/-- Pair-recursion carrying `(sacD_k, sacD_{k−1})` for the 3-term recurrence. -/
def sacDpair : Nat → Q × Q
  | 0 => (⟨9, 8⟩, ⟨0, 1⟩)
  | (k + 1) => let p := sacDpair k; (mul ⟨1, 8⟩ (add (mul ⟨6, 1⟩ p.1) (mul ⟨9, 1⟩ p.2)), p.1)

/-- `sacD = sacoef' = 9/(8−6u−9u²)`. -/
def sacD (k : Nat) : Q := (sacDpair k).1

theorem sacDpair_den : ∀ k, 0 < (sacDpair k).1.den ∧ 0 < (sacDpair k).2.den
  | 0 => ⟨by decide, by decide⟩
  | (k + 1) => ⟨Qmul_den_pos (by decide)
      (add_den_pos (Qmul_den_pos (by decide) (sacDpair_den k).1)
        (Qmul_den_pos (by decide) (sacDpair_den k).2)), (sacDpair_den k).1⟩

theorem sacD_den (k : Nat) : 0 < (sacD k).den := (sacDpair_den k).1

/-- The recurrence `sacD_{m+2} = (6 sacD_{m+1} + 9 sacD_m)/8`. -/
theorem sacD_succ_succ (m : Nat) :
    sacD (m + 2) = mul ⟨1, 8⟩ (add (mul ⟨6, 1⟩ (sacD (m + 1))) (mul ⟨9, 1⟩ (sacD m))) := rfl

/-- The quadratic `8 − 6u − 9u²` coefficient series. -/
def p2 (k : Nat) : Q := ⟨(if k = 0 then 8 else if k = 1 then -6 else if k = 2 then -9 else 0 : Int), 1⟩
theorem p2_den (k : Nat) : 0 < (p2 k).den := Nat.one_pos

theorem p2_split (k : Nat) :
    Qeq (p2 k) (add (add (fsmono ⟨8, 1⟩ 0 k) (fsmono ⟨-6, 1⟩ 1 k)) (fsmono ⟨-9, 1⟩ 2 k)) := by
  unfold p2 fsmono
  by_cases h0 : k = 0
  · subst h0; decide
  · by_cases h1 : k = 1
    · subst h1; decide
    · by_cases h2 : k = 2
      · subst h2; decide
      · simp only [if_neg h0, if_neg h1, if_neg h2]; decide

/-- The 3-term recurrence cancellation `8·((6a+9b)/8) − 6a − 9b = 0`. -/
theorem sacD_cancel (a b : Q) :
    Qeq (add (add (mul ⟨8, 1⟩ (mul ⟨1, 8⟩ (add (mul ⟨6, 1⟩ a) (mul ⟨9, 1⟩ b))))
      (mul ⟨-6, 1⟩ a)) (mul ⟨-9, 1⟩ b)) ⟨0, 1⟩ := by
  simp only [Qeq, add, mul]; push_cast; ring_uor

/-- **The sacD ODE** `(8−6u−9u²)·sacD = 9` (the defining reciprocal relation, `sacD = sacoef'`). -/
theorem sacD_ode (k : Nat) : Qeq (fmul p2 sacD k) (mul ⟨9, 1⟩ (fone k)) := by
  have hsd : ∀ i, 0 < (add (add (fsmono ⟨8, 1⟩ 0 i) (fsmono ⟨-6, 1⟩ 1 i)) (fsmono ⟨-9, 1⟩ 2 i)).den :=
    fun i => add_den_pos (add_den_pos (fsmono_den (by decide) 0 i) (fsmono_den (by decide) 1 i))
      (fsmono_den (by decide) 2 i)
  have hid : ∀ i, 0 < (add (fsmono ⟨8, 1⟩ 0 i) (fsmono ⟨-6, 1⟩ 1 i)).den :=
    fun i => add_den_pos (fsmono_den (by decide) 0 i) (fsmono_den (by decide) 1 i)
  have e0 : Qeq (fmul p2 sacD k)
      (add (add (fmul (fsmono ⟨8, 1⟩ 0) sacD k) (fmul (fsmono ⟨-6, 1⟩ 1) sacD k))
        (fmul (fsmono ⟨-9, 1⟩ 2) sacD k)) := by
    refine Qeq_trans (fmul_den_pos hsd sacD_den k) (fmul_congr_left p2_split k) ?_
    refine Qeq_trans (add_den_pos (fmul_den_pos hid sacD_den k)
      (fmul_den_pos (fsmono_den (by decide) 2) sacD_den k))
      (fmul_add_left hid (fsmono_den (by decide) 2) sacD_den k) ?_
    exact Qadd_congr (fmul_add_left (fsmono_den (by decide) 0) (fsmono_den (by decide) 1) sacD_den k)
      (Qeq_refl _)
  have hd3 : ∀ i, 0 < (fmul (fsmono ⟨9, 1⟩ 0) sacD i).den := fun i => fmul_den_pos (fsmono_den (by decide) 0) sacD_den i
  match k with
  | 0 =>
      have h8 : Qeq (fmul (fsmono ⟨8, 1⟩ 0) sacD 0) (mul ⟨8, 1⟩ (sacD 0)) := fmul_fsmono (by decide) sacD sacD_den 0 (by omega)
      have h6 : Qeq (fmul (fsmono ⟨-6, 1⟩ 1) sacD 0) ⟨0, 1⟩ := fmul_fsmono_zero (by decide) sacD sacD_den 1 (by omega)
      have h9 : Qeq (fmul (fsmono ⟨-9, 1⟩ 2) sacD 0) ⟨0, 1⟩ := fmul_fsmono_zero (by decide) sacD sacD_den 2 (by omega)
      refine Qeq_trans (add_den_pos (add_den_pos (fmul_den_pos (fsmono_den (by decide) 0) sacD_den 0)
        (fmul_den_pos (fsmono_den (by decide) 1) sacD_den 0)) (fmul_den_pos (fsmono_den (by decide) 2) sacD_den 0)) e0 ?_
      exact Qeq_trans (add_den_pos (add_den_pos (Qmul_den_pos (by decide) (sacD_den 0)) Nat.one_pos) Nat.one_pos)
        (Qadd_congr (Qadd_congr h8 h6) h9) (by decide)
  | 1 =>
      have h8 : Qeq (fmul (fsmono ⟨8, 1⟩ 0) sacD 1) (mul ⟨8, 1⟩ (sacD 1)) := by
        have hh := fmul_fsmono (c := ⟨8, 1⟩) (by decide) sacD sacD_den 0 (show 0 ≤ 1 by omega); rwa [Nat.sub_zero] at hh
      have h6 : Qeq (fmul (fsmono ⟨-6, 1⟩ 1) sacD 1) (mul ⟨-6, 1⟩ (sacD 0)) := fmul_fsmono (by decide) sacD sacD_den 1 (by omega)
      have h9 : Qeq (fmul (fsmono ⟨-9, 1⟩ 2) sacD 1) ⟨0, 1⟩ := fmul_fsmono_zero (by decide) sacD sacD_den 2 (by omega)
      refine Qeq_trans (add_den_pos (add_den_pos (fmul_den_pos (fsmono_den (by decide) 0) sacD_den 1)
        (fmul_den_pos (fsmono_den (by decide) 1) sacD_den 1)) (fmul_den_pos (fsmono_den (by decide) 2) sacD_den 1)) e0 ?_
      exact Qeq_trans (add_den_pos (add_den_pos (Qmul_den_pos (by decide) (sacD_den 1))
        (Qmul_den_pos (by decide) (sacD_den 0))) Nat.one_pos) (Qadd_congr (Qadd_congr h8 h6) h9) (by decide)
  | (m + 2) =>
      have h8 : Qeq (fmul (fsmono ⟨8, 1⟩ 0) sacD (m + 2)) (mul ⟨8, 1⟩ (sacD (m + 2))) := by
        have hh := fmul_fsmono (c := ⟨8, 1⟩) (by decide) sacD sacD_den 0 (show 0 ≤ m + 2 by omega); rwa [Nat.sub_zero] at hh
      have h6 : Qeq (fmul (fsmono ⟨-6, 1⟩ 1) sacD (m + 2)) (mul ⟨-6, 1⟩ (sacD (m + 1))) := by
        have hh := fmul_fsmono (c := ⟨-6, 1⟩) (by decide) sacD sacD_den 1 (show 1 ≤ m + 2 by omega)
        rwa [show m + 2 - 1 = m + 1 from by omega] at hh
      have h9 : Qeq (fmul (fsmono ⟨-9, 1⟩ 2) sacD (m + 2)) (mul ⟨-9, 1⟩ (sacD m)) := by
        have hh := fmul_fsmono (c := ⟨-9, 1⟩) (by decide) sacD sacD_den 2 (show 2 ≤ m + 2 by omega)
        rwa [show m + 2 - 2 = m from by omega] at hh
      refine Qeq_trans (add_den_pos (add_den_pos (fmul_den_pos (fsmono_den (by decide) 0) sacD_den (m + 2))
        (fmul_den_pos (fsmono_den (by decide) 1) sacD_den (m + 2))) (fmul_den_pos (fsmono_den (by decide) 2) sacD_den (m + 2))) e0 ?_
      refine Qeq_trans (add_den_pos (add_den_pos (Qmul_den_pos (by decide) (sacD_den (m + 2)))
        (Qmul_den_pos (by decide) (sacD_den (m + 1)))) (Qmul_den_pos (by decide) (sacD_den m)))
        (Qadd_congr (Qadd_congr h8 h6) h9) ?_
      rw [sacD_succ_succ m]
      have hf : fone (m + 2) = ⟨0, 1⟩ := by unfold fone; rw [if_neg (by omega)]
      rw [hf]
      exact Qeq_trans Nat.one_pos (sacD_cancel (sacD (m + 1)) (sacD m)) (by decide)

/-- **The shifted-artanh series `sacoef`** (formal antiderivative of `sacD`), with the IRRATIONAL constant
    `sacoef₀=artanh(⅓)` REPLACED by `0` — legitimate since neither `fderiv` nor `fcomp` (degree ≥1) reads
    the constant; the true constant is restored only at the real-eval level (STEP 3). -/
def sacoef (k : Nat) : Q := if k = 0 then ⟨0, 1⟩ else mul ⟨1, k⟩ (sacD (k - 1))

theorem sacoef_zero : sacoef 0 = ⟨0, 1⟩ := rfl

theorem sacoef_den (k : Nat) : 0 < (sacoef k).den := by
  unfold sacoef; split
  · exact Nat.one_pos
  · next h => exact Qmul_den_pos (Nat.pos_of_ne_zero h) (sacD_den (k - 1))

/-- Fresh-`Int`-var core for `fderiv_sacoef` (dodges `ring_uor`'s cast-reifier issue). -/
private theorem fderiv_sacoef_core (K sn sd : Int) :
    (K + 1) * (1 * sn) * sd = sn * (1 * ((K + 1) * sd)) := by ring_uor

/-- **`fderiv sacoef = sacD`** — `sacoef` integrates `sacoef' = sacD` (the `(k+1)` and `1/(k+1)` cancel). -/
theorem fderiv_sacoef (k : Nat) : Qeq (fderiv sacoef k) (sacD k) := by
  show Qeq (mul ⟨(k + 1 : Int), 1⟩ (sacoef (k + 1))) (sacD k)
  have hs : sacoef (k + 1) = mul ⟨1, k + 1⟩ (sacD k) := by
    show (if k + 1 = 0 then (⟨0, 1⟩ : Q) else mul ⟨1, k + 1⟩ (sacD (k + 1 - 1))) = mul ⟨1, k + 1⟩ (sacD k)
    rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
  rw [hs]; simp only [Qeq, mul]; push_cast
  exact fderiv_sacoef_core (k : Int) (sacD k).num ((sacD k).den : Int)

-- ===========================================================================
-- STEP 2e — the **monomial-shift composition law** `fcomp (tᵈ·b) c = cᵈ·(fcomp b c)` (`c(0)=0`).
-- The `d=1` case via the `fcomp_chain` double-sum (extend → `Fsum_mul_left` → `Fsum_swap`); general `d`
-- by iteration. The enabler for the composed ODE `qcomp·(sacD∘δ)=9` (avoids general `fcomp_fmul`).
-- ===========================================================================

/-- **`fcomp (t·b) c = c·(fcomp b c)`** (`c(0)=0`), the degree-1 monomial-shift composition law. -/
theorem fcomp_shift1 (b c : Nat → Q) (hb : ∀ i, 0 < (b i).den) (hc : ∀ i, 0 < (c i).den)
    (hc0 : Qeq (c 0) ⟨0, 1⟩) (k : Nat) :
    Qeq (fcomp (fmul (fmono 1) b) c k) (fmul c (fcomp b c) k) := by
  have hbc : ∀ i, 0 < (fcomp b c i).den := fun i => fcomp_den_pos hb hc i
  have hfp : ∀ m i, 0 < (fpow c m i).den := fun m i => fpow_den_pos hc m i
  have hFb : ∀ i, 0 < (fmul (fmono 1) b i).den := fun i => fmul_den_pos (fun j => fmono_den 1 j) hb i
  -- RHS = middle = Σ_m b_m (c^{m+1})_k
  have hRHS : Qeq (fmul c (fcomp b c) k) (Fsum (fun m => mul (b m) (fpow c (m + 1) k)) k) := by
    show Qeq (Fsum (fun i => mul (c i) (fcomp b c (k - i))) k)
      (Fsum (fun m => mul (b m) (fpow c (m + 1) k)) k)
    have stepA : Qeq (Fsum (fun i => mul (c i) (fcomp b c (k - i))) k)
        (Fsum (fun i => Fsum (fun m => mul (c i) (mul (b m) (fpow c m (k - i)))) k) k) := by
      refine Fsum_congr_le (k := k) (fun i hi => ?_)
      have hext : Qeq (fcomp b c (k - i)) (Fsum (fun m => mul (b m) (fpow c m (k - i))) k) :=
        Fsum_extend_zero (fun m => Qmul_den_pos (hb m) (hfp m (k - i))) (by omega)
          (fun m hm1 _ => Qeq_trans (Qmul_den_pos (hb m) Nat.one_pos)
            (Qmul_congr (Qeq_refl _) (fpow_vanish hc hc0 m (k - i) hm1)) (by simp [Qeq, mul]))
      refine Qeq_trans (Qmul_den_pos (hc i) (Fsum_den_pos (fun m => Qmul_den_pos (hb m) (hfp m (k - i))) k))
        (Qmul_congr (Qeq_refl _) hext) ?_
      exact Qeq_symm (Fsum_mul_left (hc i) (fun m => Qmul_den_pos (hb m) (hfp m (k - i))) k)
    have stepB : Qeq (Fsum (fun i => Fsum (fun m => mul (c i) (mul (b m) (fpow c m (k - i)))) k) k)
        (Fsum (fun m => Fsum (fun i => mul (c i) (mul (b m) (fpow c m (k - i)))) k) k) :=
      Fsum_swap (fun i m => Qmul_den_pos (hc i) (Qmul_den_pos (hb m) (hfp m (k - i)))) k k
    have stepC : Qeq (Fsum (fun m => Fsum (fun i => mul (c i) (mul (b m) (fpow c m (k - i)))) k) k)
        (Fsum (fun m => mul (b m) (fpow c (m + 1) k)) k) := by
      refine Fsum_congr (fun m => ?_) k
      have hrw : Qeq (Fsum (fun i => mul (c i) (mul (b m) (fpow c m (k - i)))) k)
          (Fsum (fun i => mul (b m) (mul (c i) (fpow c m (k - i)))) k) :=
        Fsum_congr (fun i => by simp only [Qeq, mul]; push_cast; ring_uor) k
      refine Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos (hb m) (Qmul_den_pos (hc i) (hfp m (k - i)))) k) hrw ?_
      exact Fsum_mul_left (hb m) (fun i => Qmul_den_pos (hc i) (hfp m (k - i))) k
    exact Qeq_trans (Fsum_den_pos (fun i => Fsum_den_pos
        (fun m => Qmul_den_pos (hc i) (Qmul_den_pos (hb m) (hfp m (k - i)))) k) k) stepA
      (Qeq_trans (Fsum_den_pos (fun m => Fsum_den_pos
        (fun i => Qmul_den_pos (hc i) (Qmul_den_pos (hb m) (hfp m (k - i)))) k) k) stepB stepC)
  -- LHS = middle
  have hGF : ∀ m, Qeq (mul (b m) (fpow c (m + 1) k))
      (mul (fmul (fmono 1) b (m + 1)) (fpow c (m + 1) k)) :=
    fun m => Qmul_congr (Qeq_symm (by
      have h := fmul_fmono (c := b) hb 1 (show 1 ≤ m + 1 by omega)
      rwa [show m + 1 - 1 = m from by omega] at h)) (Qeq_refl _)
  have hF0 : Qeq (mul (fmul (fmono 1) b 0) (fpow c 0 k)) ⟨0, 1⟩ :=
    Qeq_trans (Qmul_den_pos Nat.one_pos (hfp 0 k))
      (Qmul_congr (fmul_fmono_zero hb (show (0 : Nat) < 1 by omega)) (Qeq_refl _)) (by simp [Qeq, mul])
  have hFk1 : Qeq (mul (fmul (fmono 1) b (k + 1)) (fpow c (k + 1) k)) ⟨0, 1⟩ :=
    Qeq_trans (Qmul_den_pos (hFb (k + 1)) Nat.one_pos)
      (Qmul_congr (Qeq_refl _) (fpow_vanish hc hc0 (k + 1) k (by omega))) (by simp [Qeq, mul])
  have hLHS : Qeq (Fsum (fun m => mul (b m) (fpow c (m + 1) k)) k)
      (fcomp (fmul (fmono 1) b) c k) := by
    show Qeq (Fsum (fun m => mul (b m) (fpow c (m + 1) k)) k)
      (Fsum (fun m => mul (fmul (fmono 1) b m) (fpow c m k)) k)
    refine Qeq_trans (Fsum_den_pos (fun m => Qmul_den_pos (hFb (m + 1)) (hfp (m + 1) k)) k)
      (Fsum_congr hGF k) ?_
    refine Qeq_trans (Qsub_den_pos (Fsum_den_pos (fun m => Qmul_den_pos (hFb m) (hfp m k)) (k + 1))
      (Qmul_den_pos (hFb 0) (hfp 0 k)))
      (Fsum_shift (fun m => Qmul_den_pos (hFb m) (hfp m k)) k) ?_
    -- Qsub (Fsum F (k+1)) (F 0) ≈ Fsum F (k+1) ≈ Fsum F k
    refine Qeq_trans (Fsum_den_pos (fun m => Qmul_den_pos (hFb m) (hfp m k)) (k + 1))
      (Qeq_trans (Qsub_den_pos (Fsum_den_pos (fun m => Qmul_den_pos (hFb m) (hfp m k)) (k + 1)) Nat.one_pos)
        (Qsub_congr (Qeq_refl _) hF0) (by simp [Qeq, Qsub, add, neg])) ?_
    show Qeq (add (Fsum (fun m => mul (fmul (fmono 1) b m) (fpow c m k)) k)
        (mul (fmul (fmono 1) b (k + 1)) (fpow c (k + 1) k)))
      (Fsum (fun m => mul (fmul (fmono 1) b m) (fpow c m k)) k)
    exact Qeq_trans (add_den_pos (Fsum_den_pos (fun m => Qmul_den_pos (hFb m) (hfp m k)) k) Nat.one_pos)
      (Qadd_congr (Qeq_refl _) hFk1) (Qadd_zero_right _)
  exact Qeq_trans (Fsum_den_pos (fun m => Qmul_den_pos (hb m) (hfp (m + 1) k)) k)
    (Qeq_symm hLHS) (Qeq_symm hRHS)

/-- `t·t = t²` (`fmono 1 · fmono 1 = fmono 2`). -/
theorem fmono1_sq : ∀ k, Qeq (fmul (fmono 1) (fmono 1) k) (fmono 2 k)
  | 0 => Qeq_trans Nat.one_pos (fmul_fmono_zero (fun i => fmono_den 1 i) (show (0 : Nat) < 1 by omega)) (by decide)
  | (m + 1) => by
      refine Qeq_trans (fmono_den 1 (m + 1 - 1))
        (fmul_fmono (fun i => fmono_den 1 i) 1 (show 1 ≤ m + 1 by omega)) ?_
      rw [show m + 1 - 1 = m from by omega]
      unfold fmono
      by_cases h : m = 1
      · subst h; decide
      · rw [if_neg h, if_neg (show ¬(m + 1 = 2) by omega)]; exact Qeq_refl _

/-- **`fcomp (t²·b) c = c²·(fcomp b c)`** (`c(0)=0`), the degree-2 shift, via `fcomp_shift1` twice. -/
theorem fcomp_shift2 (b c : Nat → Q) (hb : ∀ i, 0 < (b i).den) (hc : ∀ i, 0 < (c i).den)
    (hc0 : Qeq (c 0) ⟨0, 1⟩) (k : Nat) :
    Qeq (fcomp (fmul (fmono 2) b) c k) (fmul c (fmul c (fcomp b c)) k) := by
  have h1b : ∀ i, 0 < (fmul (fmono 1) b i).den := fun i => fmul_den_pos (fun j => fmono_den 1 j) hb i
  -- fmul (fmono 2) b ≈ fmul (fmono 1) (fmul (fmono 1) b)
  have hassoc : ∀ i, Qeq (fmul (fmono 2) b i) (fmul (fmono 1) (fmul (fmono 1) b) i) := by
    intro i
    refine Qeq_trans (fmul_den_pos (fun j => fmul_den_pos (fun l => fmono_den 1 l)
        (fun l => fmono_den 1 l) j) hb i)
      (fmul_congr_left (fun j => Qeq_symm (fmono1_sq j)) i) ?_
    exact fmul_assoc (fmono 1) (fmono 1) b (fun j => fmono_den 1 j) (fun j => fmono_den 1 j) hb i
  refine Qeq_trans (fcomp_den_pos (fun j => fmul_den_pos (fun l => fmono_den 1 l) h1b j) hc k)
    (fcomp_congr_left hassoc k) ?_
  refine Qeq_trans (fmul_den_pos hc (fun j => fcomp_den_pos h1b hc j) k)
    (fcomp_shift1 (fmul (fmono 1) b) c h1b hc hc0 k) ?_
  exact fmul_congr_right (fun j => fcomp_shift1 b c hb hc hc0 j) k

/-- `(c·a)·b = c·(a·b)` (scalar on the left factor of `fmul`). -/
theorem fmul_smul_left (a b : Nat → Q) (c : Q) (hc : 0 < c.den) (ha : ∀ i, 0 < (a i).den)
    (hb : ∀ i, 0 < (b i).den) (k : Nat) : Qeq (fmul (fsmul c a) b k) (mul c (fmul a b k)) := by
  refine Qeq_trans (fmul_den_pos hb (fun i => fsmul_den hc ha i) k)
    (fmul_comm (fsmul c a) b (fun i => fsmul_den hc ha i) hb k) ?_
  refine Qeq_trans (Qmul_den_pos hc (fmul_den_pos hb ha k))
    (fmul_smul_right b a c hc hb ha k) ?_
  exact Qmul_congr (Qeq_refl _) (fmul_comm b a hb ha k)

/-- `fcomp` pulls out a scalar: `(c·a)∘b = c·(a∘b)`. -/
theorem fcomp_smul (c : Q) (a b : Nat → Q) (hc : 0 < c.den) (ha : ∀ i, 0 < (a i).den)
    (hb : ∀ i, 0 < (b i).den) (k : Nat) : Qeq (fcomp (fsmul c a) b k) (mul c (fcomp a b k)) := by
  show Qeq (Fsum (fun m => mul (fsmul c a m) (fpow b m k)) k)
    (mul c (Fsum (fun m => mul (a m) (fpow b m k)) k))
  refine Qeq_trans (Fsum_den_pos (fun m => Qmul_den_pos hc (Qmul_den_pos (ha m) (fpow_den_pos hb m k))) k)
    (Fsum_congr (fun m => Qmul_assoc c (a m) (fpow b m k)) k) ?_
  exact Fsum_mul_left hc (fun m => Qmul_den_pos (ha m) (fpow_den_pos hb m k)) k

/-- `fcomp` distributes over subtraction (outer argument). -/
theorem fcomp_sub {a b c : Nat → Q} (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den)
    (hc : ∀ i, 0 < (c i).den) (k : Nat) :
    Qeq (fcomp (fun i => Qsub (a i) (b i)) c k) (Qsub (fcomp a c k) (fcomp b c k)) := by
  show Qeq (Fsum (fun m => mul (Qsub (a m) (b m)) (fpow c m k)) k)
    (Qsub (Fsum (fun m => mul (a m) (fpow c m k)) k) (Fsum (fun m => mul (b m) (fpow c m k)) k))
  refine Qeq_trans (Fsum_den_pos (fun m => Qsub_den_pos (Qmul_den_pos (ha m) (fpow_den_pos hc m k))
      (Qmul_den_pos (hb m) (fpow_den_pos hc m k))) k)
    (Fsum_congr (fun m => Qmul_sub_right (a m) (b m) (fpow c m k)) k)
    (Fsum_sub (fun m => Qmul_den_pos (ha m) (fpow_den_pos hc m k))
      (fun m => Qmul_den_pos (hb m) (fpow_den_pos hc m k)) k)

/-- `(c·tᵈ)·e = c·(tᵈ·e)` (scaled monomial = scalar times monomial shift). -/
theorem fmul_fsmono_smul (c : Q) (d : Nat) (e : Nat → Q) (hc : 0 < c.den) (he : ∀ i, 0 < (e i).den)
    (k : Nat) : Qeq (fmul (fsmono c d) e k) (mul c (fmul (fmono d) e k)) := by
  by_cases h : d ≤ k
  · refine Qeq_trans (Qmul_den_pos hc (he (k - d))) (fmul_fsmono hc e he d h) ?_
    exact Qmul_congr (Qeq_refl _) (Qeq_symm (fmul_fmono he d h))
  · refine Qeq_trans Nat.one_pos (fmul_fsmono_zero hc e he d (by omega)) ?_
    refine Qeq_trans (Qmul_den_pos hc Nat.one_pos) ?_
      (Qeq_symm (Qmul_congr (Qeq_refl c) (fmul_fmono_zero he (show k < d by omega))))
    simp [Qeq, mul]

/-- The decomposition `(8−6u−9u²)·sacD = 8·sacD − 6·(t·sacD) − 9·(t²·sacD)` (`p2_split` + `fsmono`-smul). -/
theorem p2_sacD (k : Nat) :
    Qeq (fmul p2 sacD k)
      (add (add (mul ⟨8, 1⟩ (sacD k)) (mul ⟨-6, 1⟩ (fmul (fmono 1) sacD k)))
        (mul ⟨-9, 1⟩ (fmul (fmono 2) sacD k))) := by
  have hf8 : ∀ i, 0 < (fsmono ⟨8, 1⟩ 0 i).den := fun i => fsmono_den (by decide) 0 i
  have hf6 : ∀ i, 0 < (fsmono ⟨-6, 1⟩ 1 i).den := fun i => fsmono_den (by decide) 1 i
  have hf9 : ∀ i, 0 < (fsmono ⟨-9, 1⟩ 2 i).den := fun i => fsmono_den (by decide) 2 i
  have hinner : ∀ i, 0 < (add (fsmono ⟨8, 1⟩ 0 i) (fsmono ⟨-6, 1⟩ 1 i)).den :=
    fun i => add_den_pos (hf8 i) (hf6 i)
  have e0 : Qeq (fmul p2 sacD k)
      (add (add (fmul (fsmono ⟨8, 1⟩ 0) sacD k) (fmul (fsmono ⟨-6, 1⟩ 1) sacD k))
        (fmul (fsmono ⟨-9, 1⟩ 2) sacD k)) := by
    refine Qeq_trans (fmul_den_pos (fun i => add_den_pos (hinner i) (hf9 i)) sacD_den k)
      (fmul_congr_left p2_split k) ?_
    refine Qeq_trans (add_den_pos (fmul_den_pos hinner sacD_den k) (fmul_den_pos hf9 sacD_den k))
      (fmul_add_left hinner hf9 sacD_den k) ?_
    exact Qadd_congr (fmul_add_left hf8 hf6 sacD_den k) (Qeq_refl _)
  have h8 : Qeq (fmul (fsmono ⟨8, 1⟩ 0) sacD k) (mul ⟨8, 1⟩ (sacD k)) :=
    Qeq_trans (Qmul_den_pos (by decide) (fmul_den_pos (fun i => fmono_den 0 i) sacD_den k))
      (fmul_fsmono_smul ⟨8, 1⟩ 0 sacD (by decide) sacD_den k)
      (Qmul_congr (Qeq_refl _) (by
        have h := fmul_fmono sacD_den 0 (Nat.zero_le k); rwa [Nat.sub_zero] at h))
  have h6 : Qeq (fmul (fsmono ⟨-6, 1⟩ 1) sacD k) (mul ⟨-6, 1⟩ (fmul (fmono 1) sacD k)) :=
    fmul_fsmono_smul ⟨-6, 1⟩ 1 sacD (by decide) sacD_den k
  have h9 : Qeq (fmul (fsmono ⟨-9, 1⟩ 2) sacD k) (mul ⟨-9, 1⟩ (fmul (fmono 2) sacD k)) :=
    fmul_fsmono_smul ⟨-9, 1⟩ 2 sacD (by decide) sacD_den k
  refine Qeq_trans (add_den_pos (add_den_pos (fmul_den_pos hf8 sacD_den k) (fmul_den_pos hf6 sacD_den k))
    (fmul_den_pos hf9 sacD_den k)) e0 ?_
  exact Qadd_congr (Qadd_congr h8 h6) h9

/-- `qcomp` in additive (negative-coefficient) form. -/
theorem qcomp_add (k : Nat) :
    Qeq (qcomp k) (add (add (mul ⟨8, 1⟩ (fone k)) (mul ⟨-6, 1⟩ (dcoef k)))
      (mul ⟨-9, 1⟩ (fmul dcoef dcoef k))) := by
  unfold qcomp; simp only [Qeq, Qsub, add, neg, mul]; push_cast; ring_uor

/-- **★ THE COMPOSED ODE** `qcomp·(sacD∘δ) = 9` — `sacD`'s ODE composed with `δ`, via the monomial-shift
    laws (`fcomp_shift1/2`) and `fcomp`/`fmul` linearity (avoids general `fcomp_fmul`). With `dcoef_ode`
    this gives `(1−w²)·fderiv(fcomp sacoef δ)=1`, hence `fderiv(fcomp sacoef δ)=gcoef`. -/
theorem composed_ode (k : Nat) :
    Qeq (fmul qcomp (fcomp sacD dcoef) k) (mul ⟨9, 1⟩ (fone k)) := by
  have hP : ∀ i, 0 < (fcomp sacD dcoef i).den := fun i => fcomp_den_pos sacD_den dcoef_den i
  have hm1 : ∀ i, 0 < (fmul (fmono 1) sacD i).den := fun i => fmul_den_pos (fun j => fmono_den 1 j) sacD_den i
  have hm2 : ∀ i, 0 < (fmul (fmono 2) sacD i).den := fun i => fmul_den_pos (fun j => fmono_den 2 j) sacD_den i
  -- MID = 8P − 6(δ·P) − 9(δ·(δ·P))
  -- hLM : fmul qcomp P ≈ MID
  have hLM : Qeq (fmul qcomp (fcomp sacD dcoef) k)
      (add (add (mul ⟨8, 1⟩ (fcomp sacD dcoef k))
        (mul ⟨-6, 1⟩ (fmul dcoef (fcomp sacD dcoef) k)))
        (mul ⟨-9, 1⟩ (fmul dcoef (fmul dcoef (fcomp sacD dcoef)) k))) := by
    have hAd : ∀ i, 0 < (add (mul ⟨8, 1⟩ (fone i)) (mul ⟨-6, 1⟩ (dcoef i))).den :=
      fun i => add_den_pos (Qmul_den_pos (by decide) (fone_den_pos i)) (Qmul_den_pos (by decide) (dcoef_den i))
    have hBd : ∀ i, 0 < (mul ⟨-9, 1⟩ (fmul dcoef dcoef i)).den :=
      fun i => Qmul_den_pos (by decide) (fmul_den_pos dcoef_den dcoef_den i)
    refine Qeq_trans (fmul_den_pos (fun i => add_den_pos (hAd i) (hBd i)) hP k)
      (fmul_congr_left qcomp_add k) ?_
    refine Qeq_trans (add_den_pos (fmul_den_pos hAd hP k) (fmul_den_pos hBd hP k))
      (fmul_add_left hAd hBd hP k) ?_
    refine Qadd_congr ?_ ?_
    · refine Qeq_trans (add_den_pos (fmul_den_pos (fun i => Qmul_den_pos (by decide) (fone_den_pos i)) hP k)
        (fmul_den_pos (fun i => Qmul_den_pos (by decide) (dcoef_den i)) hP k))
        (fmul_add_left (fun i => Qmul_den_pos (by decide) (fone_den_pos i))
          (fun i => Qmul_den_pos (by decide) (dcoef_den i)) hP k) ?_
      refine Qadd_congr ?_ ?_
      · -- fmul (8·fone) P = 8·(fmul fone P) = 8·P
        refine Qeq_trans (Qmul_den_pos (by decide) (fmul_den_pos (fun _ => fone_den_pos _) hP k))
          (fmul_smul_left fone (fcomp sacD dcoef) ⟨8, 1⟩ (by decide) (fun _ => fone_den_pos _) hP k) ?_
        refine Qmul_congr (Qeq_refl _) ?_
        exact Qeq_trans (fmul_den_pos hP (fun _ => fone_den_pos _) k)
          (fmul_comm fone (fcomp sacD dcoef) (fun _ => fone_den_pos _) hP k)
          (fmul_one (fcomp sacD dcoef) hP k)
      · exact fmul_smul_left dcoef (fcomp sacD dcoef) ⟨-6, 1⟩ (by decide) dcoef_den hP k
    · -- fmul (−9·δ²) P = −9·(δ·(δ·P))
      refine Qeq_trans (Qmul_den_pos (by decide) (fmul_den_pos (fun i => fmul_den_pos dcoef_den dcoef_den i) hP k))
        (fmul_smul_left (fmul dcoef dcoef) (fcomp sacD dcoef) ⟨-9, 1⟩ (by decide)
          (fun i => fmul_den_pos dcoef_den dcoef_den i) hP k) ?_
      exact Qmul_congr (Qeq_refl _) (fmul_assoc dcoef dcoef (fcomp sacD dcoef) dcoef_den dcoef_den hP k)
  -- hFM : fcomp (fmul p2 sacD) δ ≈ MID  (forward linearity into MID)
  have hAd' : ∀ i, 0 < (add (mul ⟨8, 1⟩ (sacD i)) (mul ⟨-6, 1⟩ (fmul (fmono 1) sacD i))).den :=
    fun i => add_den_pos (Qmul_den_pos (by decide) (sacD_den i)) (Qmul_den_pos (by decide) (hm1 i))
  have hBd' : ∀ i, 0 < (mul ⟨-9, 1⟩ (fmul (fmono 2) sacD i)).den :=
    fun i => Qmul_den_pos (by decide) (hm2 i)
  have hFM : Qeq (fcomp (fmul p2 sacD) dcoef k)
      (add (add (mul ⟨8, 1⟩ (fcomp sacD dcoef k))
        (mul ⟨-6, 1⟩ (fmul dcoef (fcomp sacD dcoef) k)))
        (mul ⟨-9, 1⟩ (fmul dcoef (fmul dcoef (fcomp sacD dcoef)) k))) := by
    refine Qeq_trans (fcomp_den_pos (fun i => add_den_pos (hAd' i) (hBd' i)) dcoef_den k)
      (fcomp_congr_left (fun i => p2_sacD i) k) ?_
    refine Qeq_trans (add_den_pos (fcomp_den_pos hAd' dcoef_den k) (fcomp_den_pos hBd' dcoef_den k))
      (fcomp_add hAd' hBd' dcoef_den k) ?_
    refine Qadd_congr ?_ ?_
    · refine Qeq_trans (add_den_pos
        (fcomp_den_pos (fun i => Qmul_den_pos (by decide) (sacD_den i)) dcoef_den k)
        (fcomp_den_pos (fun i => Qmul_den_pos (by decide) (hm1 i)) dcoef_den k))
        (fcomp_add (fun i => Qmul_den_pos (by decide) (sacD_den i))
          (fun i => Qmul_den_pos (by decide) (hm1 i)) dcoef_den k) ?_
      refine Qadd_congr ?_ ?_
      · exact fcomp_smul ⟨8, 1⟩ sacD dcoef (by decide) sacD_den dcoef_den k
      · refine Qeq_trans (Qmul_den_pos (by decide) (fcomp_den_pos hm1 dcoef_den k))
          (fcomp_smul ⟨-6, 1⟩ (fmul (fmono 1) sacD) dcoef (by decide) hm1 dcoef_den k) ?_
        exact Qmul_congr (Qeq_refl _) (fcomp_shift1 sacD dcoef sacD_den dcoef_den dcoef_zero k)
    · refine Qeq_trans (Qmul_den_pos (by decide) (fcomp_den_pos hm2 dcoef_den k))
        (fcomp_smul ⟨-9, 1⟩ (fmul (fmono 2) sacD) dcoef (by decide) hm2 dcoef_den k) ?_
      exact Qmul_congr (Qeq_refl _) (fcomp_shift2 sacD dcoef sacD_den dcoef_den dcoef_zero k)
  -- hode : fcomp (fmul p2 sacD) δ ≈ 9·fone  (sacD_ode + fcomp linearity)
  have hode : Qeq (fcomp (fmul p2 sacD) dcoef k) (mul ⟨9, 1⟩ (fone k)) := by
    refine Qeq_trans (fcomp_den_pos (fun i => Qmul_den_pos (by decide) (fone_den_pos i)) dcoef_den k)
      (fcomp_congr_left (fun i => sacD_ode i) k) ?_
    refine Qeq_trans (Qmul_den_pos (by decide) (fcomp_den_pos (fun _ => fone_den_pos _) dcoef_den k))
      (fcomp_smul ⟨9, 1⟩ fone dcoef (by decide) (fun _ => fone_den_pos _) dcoef_den k) ?_
    exact Qmul_congr (Qeq_refl _) (fcomp_fone dcoef_den k)
  have hMIDden : 0 < (add (add (mul ⟨8, 1⟩ (fcomp sacD dcoef k))
      (mul ⟨-6, 1⟩ (fmul dcoef (fcomp sacD dcoef) k)))
      (mul ⟨-9, 1⟩ (fmul dcoef (fmul dcoef (fcomp sacD dcoef)) k))).den :=
    add_den_pos (add_den_pos (Qmul_den_pos (by decide) (hP k))
      (Qmul_den_pos (by decide) (fmul_den_pos dcoef_den hP k)))
      (Qmul_den_pos (by decide) (fmul_den_pos dcoef_den (fun i => fmul_den_pos dcoef_den hP i) k))
  exact Qeq_trans hMIDden hLM
    (Qeq_trans (fcomp_den_pos (fun i => fmul_den_pos p2_den sacD_den i) dcoef_den k)
      (Qeq_symm hFM) hode)

private theorem mul9_cancel_core (xn yn : Int) (xd yd : Nat)
    (h : 9 * xn * ((1 * yd : Nat) : Int) = 9 * yn * ((1 * xd : Nat) : Int)) :
    xn * (yd : Int) = yn * (xd : Int) := by
  refine Int.eq_of_mul_eq_mul_left (a := 9) (by decide) ?_
  have e1 : 9 * xn * ((1 * yd : Nat) : Int) = 9 * (xn * (yd : Int)) := by push_cast; ring_uor
  have e2 : 9 * yn * ((1 * xd : Nat) : Int) = 9 * (yn * (xd : Int)) := by push_cast; ring_uor
  rw [e1, e2] at h; exact h

/-- Scalar `9` cancellation: `9·X = 9·Y ⇒ X = Y`. -/
theorem mul9_cancel {X Y : Q} (h : Qeq (mul ⟨9, 1⟩ X) (mul ⟨9, 1⟩ Y)) : Qeq X Y :=
  mul9_cancel_core X.num Y.num X.den Y.den h

-- ===========================================================================
-- STEP 2e/2f finale — `fderiv(fcomp sacoef δ)=gcoef` (chain rule + dcoef_ode + composed_ode, via the
-- `(1−w²)`-cancellation) and then `fcomp sacoef δ = acoef` (`fderiv_inj`, both 0 at the origin).
-- ===========================================================================

/-- **`fderiv(fcomp sacoef δ) = gcoef`** = `artanh'`: `H=artanh(g(w))` and `artanh(w)` have equal
    derivatives. Chain rule gives `H' = (sacD∘δ)·δ'`; then `(1−w²)·H' = 1` via `dcoef_ode` + `composed_ode`
    + the `9`-scalar cancel, matching `artanh_ode`, so `H' = gcoef` by `fmul_oneMinusSq_cancel`. -/
theorem fderiv_fcomp_sacoef (l : Nat) : Qeq (fderiv (fcomp sacoef dcoef) l) (gcoef l) := by
  have hHd : ∀ i, 0 < (fcomp sacoef dcoef i).den := fun i => fcomp_den_pos sacoef_den dcoef_den i
  have hP : ∀ i, 0 < (fcomp sacD dcoef i).den := fun i => fcomp_den_pos sacD_den dcoef_den i
  have hd' : ∀ i, 0 < (fderiv dcoef i).den := fun i => fderiv_den_pos dcoef_den i
  have hOMd' : ∀ i, 0 < (fmul oneMinusSq (fderiv dcoef) i).den :=
    fun i => fmul_den_pos (fun j => oneMinusSq_den j) hd' i
  have hchain : ∀ m, Qeq (fderiv (fcomp sacoef dcoef) m) (fmul (fcomp sacD dcoef) (fderiv dcoef) m) := by
    intro m
    refine Qeq_trans (fmul_den_pos
      (fun i => fcomp_den_pos (fun j => fderiv_den_pos sacoef_den j) dcoef_den i) hd' m)
      (fcomp_chain sacoef dcoef sacoef_den dcoef_den dcoef_zero m) ?_
    exact fmul_congr_left (fun i => fcomp_congr_left (fun j => fderiv_sacoef j) i) m
  have hode_H : ∀ m, Qeq (fmul oneMinusSq (fderiv (fcomp sacoef dcoef)) m) (fone m) := by
    intro m
    apply mul9_cancel
    have s12 : Qeq (fmul oneMinusSq (fderiv (fcomp sacoef dcoef)) m)
        (fmul (fcomp sacD dcoef) (fmul oneMinusSq (fderiv dcoef)) m) :=
      Qeq_trans (fmul_den_pos (fun j => oneMinusSq_den j) (fun i => fmul_den_pos hP hd' i) m)
        (fmul_congr_right (fun i => hchain i) m)
        (fmul_swap_left oneMinusSq (fcomp sacD dcoef) (fderiv dcoef)
          (fun j => oneMinusSq_den j) hP hd' m)
    refine Qeq_trans (Qmul_den_pos (by decide)
      (fmul_den_pos hP (fun i => fmul_den_pos (fun j => oneMinusSq_den j) hd' i) m))
      (Qmul_congr (Qeq_refl _) s12) ?_
    refine Qeq_trans (fmul_den_pos hP (fun i => fsmul_den (by decide) hOMd' i) m)
      (Qeq_symm (fmul_smul_right (fcomp sacD dcoef) (fmul oneMinusSq (fderiv dcoef)) ⟨9, 1⟩
        (by decide) hP hOMd' m)) ?_
    refine Qeq_trans (fmul_den_pos hP qcomp_den m) (fmul_congr_right (fun i => dcoef_ode i) m) ?_
    exact Qeq_trans (fmul_den_pos qcomp_den hP m)
      (fmul_comm (fcomp sacD dcoef) qcomp hP qcomp_den m) (composed_ode m)
  exact fmul_oneMinusSq_cancel (fun i => fderiv_den_pos hHd i) (fun i => gcoef_den i)
    (fun m => Qeq_trans (fone_den_pos m) (hode_H m) (Qeq_symm (artanh_ode m))) l

/-- **★ THE FORMAL ARTANH ADDITION** `fcomp sacoef δ = acoef` (as coefficient sequences): `artanh(g(w))`
    (re-centered, constant dropped) and `artanh(w)` agree, since both solve `(1−w²)y'=1` with `y(0)=0`
    (`fderiv_inj` + `fderiv_fcomp_sacoef`). The formal backbone of `artanh(g(w))=artanh(⅓)+artanh(w)`. -/
theorem fcomp_sacoef_eq_acoef (k : Nat) : Qeq (fcomp sacoef dcoef k) (acoef k) := by
  refine fderiv_inj (y := fcomp sacoef dcoef) (z := acoef) (fun m => ?_) ?_ k
  · exact Qeq_trans (gcoef_den m) (fderiv_fcomp_sacoef m) (Qeq_symm (fderiv_acoef m))
  · refine Qeq_trans (Qmul_den_pos (sacoef_den 0) (fpow_den_pos dcoef_den 0 0))
      (fcomp_const sacoef dcoef) ?_
    rw [sacoef_zero]; decide

-- ===========================================================================
-- STEP 3 — the EVAL BRIDGE. `peval` of the formal addition `fcomp sacoef δ = acoef` connects it to the
-- real `artanh` partial sum `artSum`. (The "acoef side"; the composition-eval estimate mirrors the
-- doubling's `Dterm_recip`/`DN_recip`.)
-- ===========================================================================

/-- **The formal addition, evaluated**: `peval(fcomp sacoef δ)(w, 2N+1) = artSum(w, N)` (the artanh
    partial sum), via `fcomp_sacoef_eq_acoef` + `peval_acoef_artSum`. -/
theorem peval_fcomp_sacoef_artSum (w : Q) (hwd : 0 < w.den) (N : Nat) :
    Qeq (peval (fcomp sacoef dcoef) w (2 * N + 1)) (artSum w N) :=
  Qeq_trans (peval_den_pos (fun k => acoef_den k) hwd _)
    (peval_congr (fun k => fcomp_sacoef_eq_acoef k) w (2 * N + 1))
    (peval_acoef_artSum w hwd N)

-- The **generic composition-eval error machinery** (parametric in the inner series `b` and rational inner
-- `u`), generalizing the doubling's `kcorner`/`per_m_step`/`per_m_bound`. Bounds `|peval(bᵐ,w,M) − uᵐ|`.

/-- The truncation corner of `peval(bᵐ⁺¹) = q·peval(bᵐ) − corner` (generic; `= peval_fpow_succ`'s corner). -/
def gcorner (b : Nat → Q) (w : Q) (m M : Nat) : Q :=
  Fsum (fun i => Qsub
    (Fsum (fun j => mul (mul (b i) (qpow w i)) (mul (fpow b m j) (qpow w j))) M)
    (Fsum (fun j => mul (mul (b i) (qpow w i)) (mul (fpow b m j) (qpow w j))) (M - i))) M

theorem gcorner_den (b : Nat → Q) (hb : ∀ i, 0 < (b i).den) (w : Q) (hwd : 0 < w.den) (m M : Nat) :
    0 < (gcorner b w m M).den :=
  Fsum_den_pos (fun i => Qsub_den_pos
    (Fsum_den_pos (fun j => Qmul_den_pos (Qmul_den_pos (hb i) (qpow_den_pos hwd i))
      (Qmul_den_pos (fpow_den_pos hb m j) (qpow_den_pos hwd j))) M)
    (Fsum_den_pos (fun j => Qmul_den_pos (Qmul_den_pos (hb i) (qpow_den_pos hwd i))
      (Qmul_den_pos (fpow_den_pos hb m j) (qpow_den_pos hwd j))) (M - i))) M

/-- **Generic per-`m` error recursion step**: `|e_{m+1}| ≤ |q|·|e_m| + |q−u|·|uᵐ| + |corner_m|`. -/
theorem per_m_step_gen (b : Nat → Q) (hb : ∀ i, 0 < (b i).den) (w : Q) (hwd : 0 < w.den)
    (u : Q) (hud : 0 < u.den) (m M : Nat) :
    Qle (Qabs (Qsub (peval (fpow b (m + 1)) w M) (qpow u (m + 1))))
      (add (mul (Qabs (peval b w M)) (Qabs (Qsub (peval (fpow b m) w M) (qpow u m))))
        (add (mul (Qabs (Qsub (peval b w M) u)) (Qabs (qpow u m)))
          (Qabs (gcorner b w m M)))) := by
  have hq : 0 < (peval b w M).den := peval_den_pos hb hwd M
  have hpm : 0 < (peval (fpow b m) w M).den := peval_den_pos (fpow_den_pos hb m) hwd M
  have hum : 0 < (qpow u m).den := qpow_den_pos hud m
  have hem : 0 < (Qsub (peval (fpow b m) w M) (qpow u m)).den := Qsub_den_pos hpm hum
  have hqu : 0 < (Qsub (peval b w M) u).den := Qsub_den_pos hq hud
  have hcor : 0 < (gcorner b w m M).den := gcorner_den b hb w hwd m M
  have hid : Qeq (Qsub (peval (fpow b (m + 1)) w M) (qpow u (m + 1)))
      (add (mul (peval b w M) (Qsub (peval (fpow b m) w M) (qpow u m)))
        (Qsub (mul (Qsub (peval b w M) u) (qpow u m)) (gcorner b w m M))) :=
    Qeq_trans (Qsub_den_pos (Qsub_den_pos (Qmul_den_pos hq hpm) hcor) (qpow_den_pos hud (m + 1)))
      (Qsub_congr (peval_fpow_succ b hb w hwd m M) (Qeq_refl _))
      (e_rec_alg (peval b w M) (peval (fpow b m) w M) (qpow u m) u (gcorner b w m M))
  refine Qle_trans (Qabs_den_pos (add_den_pos (Qmul_den_pos hq hem)
      (Qsub_den_pos (Qmul_den_pos hqu hum) hcor))) (Qeq_le (Qabs_Qeq hid)) ?_
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qmul_den_pos hq hem))
      (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos hqu hum) hcor))) (Qabs_add_le _ _) ?_
  refine Qadd_le_add (Qeq_le (by rw [Qabs_mul]; exact Qeq_refl _ :
    Qeq (Qabs (mul (peval b w M) (Qsub (peval (fpow b m) w M) (qpow u m))))
      (mul (Qabs (peval b w M)) (Qabs (Qsub (peval (fpow b m) w M) (qpow u m)))))) ?_
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qmul_den_pos hqu hum)) (Qabs_den_pos hcor))
    (Qabs_sub_le_add _ _) ?_
  exact Qadd_le_add (Qeq_le (by rw [Qabs_mul]; exact Qeq_refl _ :
    Qeq (Qabs (mul (Qsub (peval b w M) u) (qpow u m)))
      (mul (Qabs (Qsub (peval b w M) u)) (Qabs (qpow u m))))) (Qle_refl _)

/-- **Generic per-`m` error bound**: `|peval(bᵐ⁺¹,w,M) − uᵐ⁺¹| ≤ Σ_{j≤m} (|q−u| + |corner_j|)`,
    given `|q| ≤ 1`, `|u| ≤ 1`. By induction via `per_m_step_gen`. -/
theorem per_m_bound_gen (b : Nat → Q) (hb : ∀ i, 0 < (b i).den) (w : Q) (M : Nat) (hwd : 0 < w.den)
    (u : Q) (hud : 0 < u.den) (hq1 : Qle (Qabs (peval b w M)) ⟨1, 1⟩)
    (hu1 : Qle (Qabs u) ⟨1, 1⟩) (m : Nat) :
    Qle (Qabs (Qsub (peval (fpow b (m + 1)) w M) (qpow u (m + 1))))
      (Fsum (fun j => add (Qabs (Qsub (peval b w M) u)) (Qabs (gcorner b w j M))) m) := by
  have hqd : 0 < (peval b w M).den := peval_den_pos hb hwd M
  have hqud : 0 < (Qsub (peval b w M) u).den := Qsub_den_pos hqd hud
  have hpd : ∀ k, 0 < (peval (fpow b k) w M).den :=
    fun k => peval_den_pos (fpow_den_pos hb k) hwd M
  have hum1 : ∀ k, Qle (Qabs (qpow u k)) ⟨1, 1⟩ := by
    intro k
    induction k with
    | zero => show Qle (Qabs (⟨1, 1⟩ : Q)) ⟨1, 1⟩; decide
    | succ k ih =>
        show Qle (Qabs (mul u (qpow u k))) ⟨1, 1⟩
        refine Qle_trans (Qmul_den_pos (Qabs_den_pos hud) (Qabs_den_pos (qpow_den_pos hud k)))
          (Qeq_le (by rw [Qabs_mul]; exact Qeq_refl _ :
            Qeq (Qabs (mul u (qpow u k))) (mul (Qabs u) (Qabs (qpow u k))))) ?_
        exact Qle_trans (Qmul_den_pos Nat.one_pos Nat.one_pos)
          (Qmul_le_mul (Qabs_den_pos hud) Nat.one_pos (Qabs_den_pos (qpow_den_pos hud k))
            (Qabs_num_nonneg _) (Qabs_num_nonneg _) hu1 ih)
          (by decide : Qle (mul (⟨1, 1⟩ : Q) ⟨1, 1⟩) ⟨1, 1⟩)
  have bound1 : ∀ {e : Q}, 0 < e.den → Qle (mul (Qabs (peval b w M)) (Qabs e)) (Qabs e) :=
    fun {e} he => Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos he))
      (Qmul_le_mul_right (Qabs_num_nonneg _) hq1) (Qeq_le (Qone_mul _))
  induction m with
  | zero =>
      have hz : Qeq (Qsub (peval (fpow b 0) w M) (qpow u 0)) ⟨0, 1⟩ := by
        show Qeq (Qsub (peval fone w M) ⟨1, 1⟩) ⟨0, 1⟩
        refine Qeq_trans (Qsub_den_pos Nat.one_pos Nat.one_pos)
          (Qsub_congr (peval_fone w hwd M) (Qeq_refl _)) ?_
        simp [Qeq, Qsub, add, neg]
      have he0 : Qle (Qabs (Qsub (peval (fpow b 0) w M) (qpow u 0))) ⟨0, 1⟩ :=
        Qeq_le (Qeq_trans Nat.one_pos (Qabs_Qeq hz) (by decide : Qeq (Qabs (⟨0, 1⟩ : Q)) ⟨0, 1⟩))
      show Qle (Qabs (Qsub (peval (fpow b 1) w M) (qpow u 1)))
        (add (Qabs (Qsub (peval b w M) u)) (Qabs (gcorner b w 0 M)))
      refine Qle_trans (add_den_pos (Qmul_den_pos (Qabs_den_pos hqd)
          (Qabs_den_pos (Qsub_den_pos (hpd 0) (qpow_den_pos hud 0))))
          (add_den_pos (Qmul_den_pos (Qabs_den_pos hqud) (Qabs_den_pos (qpow_den_pos hud 0)))
            (Qabs_den_pos (gcorner_den b hb w hwd 0 M))))
        (per_m_step_gen b hb w hwd u hud 0 M) ?_
      refine Qle_trans (add_den_pos Nat.one_pos
          (add_den_pos (Qabs_den_pos hqud) (Qabs_den_pos (gcorner_den b hb w hwd 0 M))))
        (Qadd_le_add (Qle_trans (Qabs_den_pos (Qsub_den_pos (hpd 0) (qpow_den_pos hud 0)))
            (bound1 (Qsub_den_pos (hpd 0) (qpow_den_pos hud 0))) he0)
          (Qadd_le_add (Qle_trans (Qmul_den_pos (Qabs_den_pos hqud) Nat.one_pos)
            (Qmul_le_mul_left (Qabs_num_nonneg _) (hum1 0)) (Qeq_le (mul_one _))) (Qle_refl _))) ?_
      exact Qeq_le (Qzero_add _)
  | succ m ih =>
      refine Qle_trans (add_den_pos (Qmul_den_pos (Qabs_den_pos hqd)
          (Qabs_den_pos (Qsub_den_pos (hpd (m + 1)) (qpow_den_pos hud (m + 1)))))
          (add_den_pos (Qmul_den_pos (Qabs_den_pos hqud) (Qabs_den_pos (qpow_den_pos hud (m + 1))))
            (Qabs_den_pos (gcorner_den b hb w hwd (m + 1) M))))
        (per_m_step_gen b hb w hwd u hud (m + 1) M) ?_
      refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (hpd (m + 1)) (qpow_den_pos hud (m + 1))))
          (add_den_pos (Qabs_den_pos hqud) (Qabs_den_pos (gcorner_den b hb w hwd (m + 1) M))))
        (Qadd_le_add (bound1 (Qsub_den_pos (hpd (m + 1)) (qpow_den_pos hud (m + 1))))
          (Qadd_le_add (Qle_trans (Qmul_den_pos (Qabs_den_pos hqud) Nat.one_pos)
            (Qmul_le_mul_left (Qabs_num_nonneg _) (hum1 (m + 1))) (Qeq_le (mul_one _))) (Qle_refl _))) ?_
      exact Qadd_le_add ih (Qle_refl _)

/-- `|(−1/3)ᵏ| ≤ 1` (the δ-series geometric ratio is `≤ 1`). -/
theorem qpow_third_abs_le_one : ∀ k, Qle (Qabs (qpow ⟨-1, 3⟩ k)) ⟨1, 1⟩
  | 0 => by decide
  | (k + 1) => by
      show Qle (Qabs (mul ⟨-1, 3⟩ (qpow ⟨-1, 3⟩ k))) ⟨1, 1⟩
      refine Qle_trans (Qmul_den_pos (Qabs_den_pos (by decide))
          (Qabs_den_pos (qpow_den_pos (by decide) k)))
        (Qeq_le (by rw [Qabs_mul]; exact Qeq_refl _ :
          Qeq (Qabs (mul ⟨-1, 3⟩ (qpow ⟨-1, 3⟩ k)))
            (mul (Qabs (⟨-1, 3⟩ : Q)) (Qabs (qpow ⟨-1, 3⟩ k))))) ?_
      refine Qle_trans (Qmul_den_pos (Qabs_den_pos (by decide)) Nat.one_pos)
        (Qmul_le_mul_left (Qabs_num_nonneg _) (qpow_third_abs_le_one k)) ?_
      exact (by decide : Qle (mul (Qabs (⟨-1, 3⟩ : Q)) ⟨1, 1⟩) ⟨1, 1⟩)

/-- **`|δₖ| ≤ 1`** (the δ-series coefficients are bounded — the analog of the doubling's `|kdblₖ| ≤ 2`). -/
theorem dcoef_abs_le_one : ∀ k, Qle (Qabs (dcoef k)) ⟨1, 1⟩
  | 0 => by decide
  | (k + 1) => by
      show Qle (Qabs (mul ⟨8, 9⟩ (qpow ⟨-1, 3⟩ k))) ⟨1, 1⟩
      refine Qle_trans (Qmul_den_pos (Qabs_den_pos (by decide))
          (Qabs_den_pos (qpow_den_pos (by decide) k)))
        (Qeq_le (by rw [Qabs_mul]; exact Qeq_refl _ :
          Qeq (Qabs (mul ⟨8, 9⟩ (qpow ⟨-1, 3⟩ k)))
            (mul (Qabs (⟨8, 9⟩ : Q)) (Qabs (qpow ⟨-1, 3⟩ k))))) ?_
      refine Qle_trans (Qmul_den_pos (Qabs_den_pos (by decide)) Nat.one_pos)
        (Qmul_le_mul_left (Qabs_num_nonneg _) (qpow_third_abs_le_one k)) ?_
      exact (by decide : Qle (mul (Qabs (⟨8, 9⟩ : Q)) ⟨1, 1⟩) ⟨1, 1⟩)

/-- The **exact rational inner** `δ_rat(w) = 8w/(9+3w) = gval(w)−⅓` (the sum of the δ-series), a direct
    rational (like `uval`). The composition-eval's inner `u`. -/
def drat (w : Q) : Q := ⟨8 * w.num, (9 * (w.den : Int) + 3 * w.num).natAbs⟩

theorem drat_den (w : Q) (hwd : 0 < w.den) (hwn : 0 ≤ w.num) : 0 < (drat w).den := by
  show 0 < (9 * (w.den : Int) + 3 * w.num).natAbs
  have : (0 : Int) < (w.den : Int) := by exact_mod_cast hwd
  omega

/-- Fresh-`Int`-var core for `drat_rel` (dodges `ring_uor`'s cast-reifier issue). -/
private theorem drat_rel_core (wn d : Int) :
    (9 * (1 * d) + 3 * wn * 1) * (8 * wn) * (1 * d)
      = 8 * wn * (1 * (1 * d) * (9 * d + 3 * wn)) := by ring_uor

/-- The defining relation `(9+3w)·δ_rat = 8w` (for `w ≥ 0`). -/
theorem drat_rel (w : Q) (hwd : 0 < w.den) (hwn : 0 ≤ w.num) :
    Qeq (mul (add ⟨9, 1⟩ (mul ⟨3, 1⟩ w)) (drat w)) (mul ⟨8, 1⟩ w) := by
  have h : (0 : Int) ≤ 9 * (w.den : Int) + 3 * w.num := by
    have : (0 : Int) ≤ (w.den : Int) := Int.ofNat_nonneg _; omega
  simp only [Qeq, mul, add, drat]; push_cast [Int.natAbs_of_nonneg h]
  exact drat_rel_core w.num (w.den : Int)

/-- `peval(9+3w)(w, M) = 9 + 3w` for `M ≥ 1` (the low-degree polynomial evaluates exactly). -/
theorem peval_nine3w (w : Q) (hwd : 0 < w.den) :
    ∀ m, Qeq (peval nine3w w (m + 1)) (add ⟨9, 1⟩ (mul ⟨3, 1⟩ w))
  | 0 => by
      show Qeq (add (mul (nine3w 0) (qpow w 0)) (mul (nine3w 1) (qpow w 1)))
        (add ⟨9, 1⟩ (mul ⟨3, 1⟩ w))
      have e0 : Qeq (mul (nine3w 0) (qpow w 0)) ⟨9, 1⟩ := by
        show Qeq (mul ⟨9, 1⟩ ⟨1, 1⟩) ⟨9, 1⟩; decide
      have e1 : Qeq (mul (nine3w 1) (qpow w 1)) (mul ⟨3, 1⟩ w) := by
        show Qeq (mul ⟨3, 1⟩ (mul w (qpow w 0))) (mul ⟨3, 1⟩ w)
        refine Qmul_congr (Qeq_refl _) ?_
        show Qeq (mul w ⟨1, 1⟩) w; simp [Qeq, mul]
      exact Qeq_trans (add_den_pos Nat.one_pos (Qmul_den_pos (by decide) hwd))
        (Qadd_congr e0 e1) (Qeq_refl _)
  | (m + 1) => by
      show Qeq (add (peval nine3w w (m + 1)) (mul (nine3w (m + 1 + 1)) (qpow w (m + 1 + 1))))
        (add ⟨9, 1⟩ (mul ⟨3, 1⟩ w))
      have hz : Qeq (mul (nine3w (m + 1 + 1)) (qpow w (m + 1 + 1))) ⟨0, 1⟩ := by
        have hn : nine3w (m + 1 + 1) = ⟨0, 1⟩ := by
          unfold nine3w; rw [if_neg (by omega), if_neg (by omega)]
        rw [hn]; simp [Qeq, mul]
      refine Qeq_trans (add_den_pos (add_den_pos Nat.one_pos (Qmul_den_pos (by decide) hwd))
        Nat.one_pos) (Qadd_congr (peval_nine3w w hwd m) hz) (Qadd_zero_right _)

/-- `peval(8w)(w, M) = 8w` for `M ≥ 1`. -/
theorem peval_eightT (w : Q) (hwd : 0 < w.den) :
    ∀ m, Qeq (peval eightT w (m + 1)) (mul ⟨8, 1⟩ w)
  | 0 => by
      show Qeq (add (mul (eightT 0) (qpow w 0)) (mul (eightT 1) (qpow w 1))) (mul ⟨8, 1⟩ w)
      have e0 : Qeq (mul (eightT 0) (qpow w 0)) ⟨0, 1⟩ := by
        show Qeq (mul ⟨0, 1⟩ (qpow w 0)) ⟨0, 1⟩; simp [Qeq, mul]
      have e1 : Qeq (mul (eightT 1) (qpow w 1)) (mul ⟨8, 1⟩ w) := by
        show Qeq (mul ⟨8, 1⟩ (mul w (qpow w 0))) (mul ⟨8, 1⟩ w)
        refine Qmul_congr (Qeq_refl _) ?_
        show Qeq (mul w ⟨1, 1⟩) w; simp [Qeq, mul]
      exact Qeq_trans (add_den_pos Nat.one_pos (Qmul_den_pos (by decide) hwd))
        (Qadd_congr e0 e1) (Qzero_add _)
  | (m + 1) => by
      show Qeq (add (peval eightT w (m + 1)) (mul (eightT (m + 1 + 1)) (qpow w (m + 1 + 1))))
        (mul ⟨8, 1⟩ w)
      have hz : Qeq (mul (eightT (m + 1 + 1)) (qpow w (m + 1 + 1))) ⟨0, 1⟩ := by
        have he : eightT (m + 1 + 1) = ⟨0, 1⟩ := by unfold eightT; rw [if_neg (by omega)]
        rw [he]; simp [Qeq, mul]
      refine Qeq_trans (add_den_pos (Qmul_den_pos (by decide) hwd) Nat.one_pos)
        (Qadd_congr (peval_eightT w hwd m) hz) (Qadd_zero_right _)

/-- Difference-ring core for the base of `nine3w_peval_dcoef`: `(9+3w)(d₁w) − (8w + 3d₁w²) = (9d₁−8)w`. -/
private theorem inner_base_core (d1 wv : Q) :
    Qeq (Qsub (mul (add ⟨9, 1⟩ (mul ⟨3, 1⟩ wv)) (mul d1 wv))
          (add (mul ⟨8, 1⟩ wv) (mul (mul ⟨3, 1⟩ d1) (mul wv wv))))
        (mul (Qsub (mul ⟨9, 1⟩ d1) ⟨8, 1⟩) wv) := by
  simp only [Qeq, Qsub, add, mul, neg]; push_cast; ring_uor

/-- Difference-ring core for the step: collapses to `(9d₂+3d₁)·P`. -/
private theorem inner_step_core (eightw d1 d2 P wv : Q) :
    Qeq (Qsub (add (add eightw (mul (mul ⟨3, 1⟩ d1) P)) (mul (add ⟨9, 1⟩ (mul ⟨3, 1⟩ wv)) (mul d2 P)))
          (add eightw (mul (mul ⟨3, 1⟩ d2) (mul wv P))))
        (mul (add (mul ⟨9, 1⟩ d2) (mul ⟨3, 1⟩ d1)) P) := by
  simp only [Qeq, Qsub, add, mul, neg]; push_cast; ring_uor

/-- `mul (≈0) P ≈ 0`. -/
private theorem mul_zero_of_zero {z : Q} (hz : Qeq z ⟨0, 1⟩) (P : Q) (hPd : 0 < P.den) :
    Qeq (mul z P) ⟨0, 1⟩ := by
  refine Qeq_trans (Qmul_den_pos Nat.one_pos hPd) (Qmul_congr hz (Qeq_refl _)) ?_
  simp [Qeq, mul]

/-- **The inner eval relation** `(9+3w)·peval(δ,w,M) = 8w + 3·δ_M·w^{M+1}` (M≥1). The corner is a SINGLE
    term (since the cleared denominator `9+3w` has degree 1); the middle collapses by the δ-recurrence. -/
theorem nine3w_peval_dcoef (w : Q) (hwd : 0 < w.den) :
    ∀ m, Qeq (mul (add ⟨9, 1⟩ (mul ⟨3, 1⟩ w)) (peval dcoef w (m + 1)))
      (add (mul ⟨8, 1⟩ w) (mul (mul ⟨3, 1⟩ (dcoef (m + 1))) (qpow w (m + 1 + 1))))
  | 0 => by
      have h9d1 : Qeq (mul ⟨9, 1⟩ (dcoef 1)) ⟨8, 1⟩ := by
        show Qeq (mul ⟨9, 1⟩ (mul ⟨8, 9⟩ (qpow ⟨-1, 3⟩ 0))) ⟨8, 1⟩; decide
      have hp1 : Qeq (peval dcoef w 1) (mul (dcoef 1) w) := by
        show Qeq (add (mul (dcoef 0) (qpow w 0)) (mul (dcoef 1) (qpow w 1))) (mul (dcoef 1) w)
        have h0 : Qeq (mul (dcoef 0) (qpow w 0)) ⟨0, 1⟩ := by
          show Qeq (mul ⟨0, 1⟩ (qpow w 0)) ⟨0, 1⟩; simp [Qeq, mul]
        have h1 : Qeq (mul (dcoef 1) (qpow w 1)) (mul (dcoef 1) w) :=
          Qmul_congr (Qeq_refl _) (by show Qeq (mul w ⟨1, 1⟩) w; simp [Qeq, mul])
        exact Qeq_trans (add_den_pos Nat.one_pos (Qmul_den_pos (dcoef_den 1) hwd))
          (Qadd_congr h0 h1) (Qzero_add _)
      -- (9+3w)·peval ≈ (9+3w)(d₁w), then base_core + 9d₁=8 ⇒ 8w + 3d₁w², then qpow w 2 ≈ w²
      refine Qeq_trans (Qmul_den_pos (add_den_pos Nat.one_pos (Qmul_den_pos (by decide) hwd))
        (Qmul_den_pos (dcoef_den 1) hwd)) (Qmul_congr (Qeq_refl _) hp1) ?_
      have hqp2 : Qeq (qpow w (0 + 1 + 1)) (mul w w) := by
        show Qeq (mul w (mul w (qpow w 0))) (mul w w)
        exact Qmul_congr (Qeq_refl _) (by show Qeq (mul w ⟨1, 1⟩) w; simp [Qeq, mul])
      have hbase : Qeq (mul (add ⟨9, 1⟩ (mul ⟨3, 1⟩ w)) (mul (dcoef 1) w))
          (add (mul ⟨8, 1⟩ w) (mul (mul ⟨3, 1⟩ (dcoef 1)) (mul w w))) := by
        refine Qeq_of_Qsub_zero (Qeq_trans (Qmul_den_pos (Qsub_den_pos (Qmul_den_pos (by decide)
          (dcoef_den 1)) Nat.one_pos) hwd) (inner_base_core (dcoef 1) w) ?_)
        exact mul_zero_of_zero (Qeq_trans (Qsub_den_pos Nat.one_pos Nat.one_pos)
          (Qsub_congr h9d1 (Qeq_refl _)) (by simp [Qeq, Qsub, add, neg])) w hwd
      exact Qeq_trans (add_den_pos (Qmul_den_pos (by decide) hwd)
        (Qmul_den_pos (Qmul_den_pos (by decide) (dcoef_den 1)) (Qmul_den_pos hwd hwd))) hbase
        (Qadd_congr (Qeq_refl _) (Qmul_congr (Qeq_refl _) (Qeq_symm hqp2)))
  | (m + 1) => by
      have hP : 0 < (qpow w (m + 1 + 1)).den := qpow_den_pos hwd (m + 1 + 1)
      have hpd : ∀ k, 0 < (peval dcoef w k).den := fun k => peval_den_pos dcoef_den hwd k
      -- peval dcoef w (m+2) = add (peval dcoef w (m+1)) (dcoef_{m+2} · w^{m+2})
      -- distribute (9+3w), apply IH, then step_core + cancellation
      refine Qeq_trans (Qmul_den_pos (add_den_pos Nat.one_pos (Qmul_den_pos (by decide) hwd))
        (hpd (m + 1 + 1))) (Qmul_congr (Qeq_refl _) (show Qeq (peval dcoef w (m + 1 + 1))
          (add (peval dcoef w (m + 1)) (mul (dcoef (m + 1 + 1)) (qpow w (m + 1 + 1)))) from Qeq_refl _)) ?_
      refine Qeq_trans (add_den_pos (Qmul_den_pos (add_den_pos Nat.one_pos (Qmul_den_pos (by decide) hwd))
        (hpd (m + 1))) (Qmul_den_pos (add_den_pos Nat.one_pos (Qmul_den_pos (by decide) hwd))
          (Qmul_den_pos (dcoef_den (m + 1 + 1)) hP)))
        (mul_add (add ⟨9, 1⟩ (mul ⟨3, 1⟩ w)) (peval dcoef w (m + 1))
          (mul (dcoef (m + 1 + 1)) (qpow w (m + 1 + 1)))) ?_
      -- now: add ((9+3w)·peval(m+1)) ((9+3w)·(d_{m+2}·P)) ≈ RHS
      have hIH := nine3w_peval_dcoef w hwd m
      have h93 : 0 < (add ⟨9, 1⟩ (mul ⟨3, 1⟩ w)).den := add_den_pos Nat.one_pos (Qmul_den_pos (by decide) hwd)
      have hB : 0 < (mul (add ⟨9, 1⟩ (mul ⟨3, 1⟩ w)) (mul (dcoef (m + 1 + 1)) (qpow w (m + 1 + 1)))).den :=
        Qmul_den_pos h93 (Qmul_den_pos (dcoef_den (m + 1 + 1)) hP)
      have hrw_a : 0 < (add (add (mul ⟨8, 1⟩ w) (mul (mul ⟨3, 1⟩ (dcoef (m + 1))) (qpow w (m + 1 + 1))))
          (mul (add ⟨9, 1⟩ (mul ⟨3, 1⟩ w)) (mul (dcoef (m + 1 + 1)) (qpow w (m + 1 + 1))))).den :=
        add_den_pos (add_den_pos (Qmul_den_pos (by decide) hwd)
          (Qmul_den_pos (Qmul_den_pos (by decide) (dcoef_den (m + 1))) hP)) hB
      have hrw_b : 0 < (add (mul ⟨8, 1⟩ w)
          (mul (mul ⟨3, 1⟩ (dcoef (m + 1 + 1))) (mul w (qpow w (m + 1 + 1))))).den :=
        add_den_pos (Qmul_den_pos (by decide) hwd)
          (Qmul_den_pos (Qmul_den_pos (by decide) (dcoef_den (m + 1 + 1))) (Qmul_den_pos hwd hP))
      have hcanc : 0 < (mul (add (mul ⟨9, 1⟩ (dcoef (m + 1 + 1))) (mul ⟨3, 1⟩ (dcoef (m + 1))))
          (qpow w (m + 1 + 1))).den :=
        Qmul_den_pos (add_den_pos (Qmul_den_pos (by decide) (dcoef_den (m + 1 + 1)))
          (Qmul_den_pos (by decide) (dcoef_den (m + 1)))) hP
      refine Qeq_of_Qsub_zero (Qeq_trans (Qsub_den_pos hrw_a hrw_b)
        (Qsub_congr (Qadd_congr hIH (Qeq_refl _))
          (Qadd_congr (Qeq_refl _) (Qmul_congr (Qeq_refl _)
            (show Qeq (qpow w (m + 1 + 1 + 1)) (mul w (qpow w (m + 1 + 1))) from Qeq_refl _))))
        (Qeq_trans hcanc (inner_step_core (mul ⟨8, 1⟩ w) (dcoef (m + 1)) (dcoef (m + 1 + 1))
          (qpow w (m + 1 + 1)) w) (mul_zero_of_zero (dcoef_shift_cancel m) (qpow w (m + 1 + 1)) hP)))

/-- **`(9+3w)·(peval δ − δ_rat) = 3·δ_M·w^{M+1}`** (the inner error cleared of its denominator). -/
theorem nine3w_peval_dcoef_sub (w : Q) (hwd : 0 < w.den) (hwn : 0 ≤ w.num) (m : Nat) :
    Qeq (mul (add ⟨9, 1⟩ (mul ⟨3, 1⟩ w)) (Qsub (peval dcoef w (m + 1)) (drat w)))
      (mul (mul ⟨3, 1⟩ (dcoef (m + 1))) (qpow w (m + 1 + 1))) := by
  have h93 : 0 < (add ⟨9, 1⟩ (mul ⟨3, 1⟩ w)).den := add_den_pos Nat.one_pos (Qmul_den_pos (by decide) hwd)
  refine Qeq_trans (Qsub_den_pos (Qmul_den_pos h93 (peval_den_pos dcoef_den hwd (m + 1)))
      (Qmul_den_pos h93 (drat_den w hwd hwn))) (Qmul_sub_left _ _ _) ?_
  refine Qeq_trans (Qsub_den_pos (add_den_pos (Qmul_den_pos (by decide) hwd)
      (Qmul_den_pos (Qmul_den_pos (by decide) (dcoef_den (m + 1))) (qpow_den_pos hwd (m + 1 + 1))))
      (Qmul_den_pos (by decide) hwd))
    (Qsub_congr (nine3w_peval_dcoef w hwd m) (drat_rel w hwd hwn)) ?_
  exact Qsub_add_left_cancel (mul ⟨8, 1⟩ w) (mul (mul ⟨3, 1⟩ (dcoef (m + 1))) (qpow w (m + 1 + 1)))

/-- **The inner eval bound** `|peval(δ,w,M) − δ_rat(w)| ≤ (1/9)·|3·δ_M·w^{M+1}|` (`w ≥ 0`): divide the
    cleared error by `9+3w ≥ 9`. The `q−u` term feeding `per_m_bound_gen` with `u = δ_rat`. -/
theorem inner_eval_bound (w : Q) (hwd : 0 < w.den) (hwn : 0 ≤ w.num) (m : Nat) :
    Qle (Qabs (Qsub (peval dcoef w (m + 1)) (drat w)))
      (mul ⟨1, 9⟩ (Qabs (mul (mul ⟨3, 1⟩ (dcoef (m + 1))) (qpow w (m + 1 + 1))))) := by
  have h93 : 0 < (add ⟨9, 1⟩ (mul ⟨3, 1⟩ w)).den := add_den_pos Nat.one_pos (Qmul_den_pos (by decide) hwd)
  have hXd : 0 < (Qsub (peval dcoef w (m + 1)) (drat w)).den :=
    Qsub_den_pos (peval_den_pos dcoef_den hwd (m + 1)) (drat_den w hwd hwn)
  have h93num : (0 : Int) ≤ (add ⟨9, 1⟩ (mul ⟨3, 1⟩ w)).num := by
    have hd : (0 : Int) ≤ (w.den : Int) := Int.ofNat_nonneg _
    simp only [add, mul]; push_cast; omega
  have h9le : Qle (⟨9, 1⟩ : Q) (Qabs (add ⟨9, 1⟩ (mul ⟨3, 1⟩ w))) := by
    refine Qle_trans h93 ?_ (Qeq_le (Qeq_symm (Qabs_of_nonneg h93num)))
    show Qle (⟨9, 1⟩ : Q) (add ⟨9, 1⟩ (mul ⟨3, 1⟩ w))
    have hd : (0 : Int) ≤ (w.den : Int) := Int.ofNat_nonneg _
    simp only [Qle, add, mul]; push_cast; omega
  -- 9·|X| ≤ |9+3w|·|X| = |(9+3w)·X| = |Y|
  have h9X : Qle (mul ⟨9, 1⟩ (Qabs (Qsub (peval dcoef w (m + 1)) (drat w))))
      (Qabs (mul (mul ⟨3, 1⟩ (dcoef (m + 1))) (qpow w (m + 1 + 1)))) := by
    refine Qle_trans (Qmul_den_pos (Qabs_den_pos h93) (Qabs_den_pos hXd))
      (Qmul_le_mul_right (Qabs_num_nonneg _) h9le) ?_
    rw [← Qabs_mul]
    exact Qeq_le (Qabs_Qeq (nine3w_peval_dcoef_sub w hwd hwn m))
  -- divide by 9
  have hXeq : Qeq (Qabs (Qsub (peval dcoef w (m + 1)) (drat w)))
      (mul ⟨1, 9⟩ (mul ⟨9, 1⟩ (Qabs (Qsub (peval dcoef w (m + 1)) (drat w))))) := by
    simp only [Qeq, mul]; push_cast; ring_uor
  exact Qle_trans (Qmul_den_pos (by decide) (Qmul_den_pos (by decide) (Qabs_den_pos hXd)))
    (Qeq_le hXeq) (Qmul_le_mul_left (by decide) h9X)

/-- **The geometric term bound** `|3·δ_M·w^{M+1}| ≤ 3·ρ^{M+1}` for `|w| ≤ ρ` (`|δ|≤1` + `qpow` monotone). -/
theorem dcoef_term_geo (w ρ : Q) (hwd : 0 < w.den) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num)
    (hw : Qle (Qabs w) ρ) (m : Nat) :
    Qle (Qabs (mul (mul ⟨3, 1⟩ (dcoef (m + 1))) (qpow w (m + 1 + 1))))
      (mul ⟨3, 1⟩ (qpow ρ (m + 1 + 1))) := by
  have hQ3 : Qle (Qabs (mul ⟨3, 1⟩ (dcoef (m + 1)))) ⟨3, 1⟩ := by
    rw [Qabs_mul]
    refine Qle_trans (Qmul_den_pos (Qabs_den_pos (by decide)) Nat.one_pos)
      (Qmul_le_mul_left (Qabs_num_nonneg _) (dcoef_abs_le_one (m + 1))) ?_
    exact (by decide : Qle (mul (Qabs (⟨3, 1⟩ : Q)) ⟨1, 1⟩) ⟨3, 1⟩)
  rw [Qabs_mul]
  refine Qmul_le_mul (Qabs_den_pos (Qmul_den_pos (by decide) (dcoef_den (m + 1)))) (by decide)
    (Qabs_den_pos (qpow_den_pos hwd (m + 1 + 1))) (Qabs_num_nonneg _) (Qabs_num_nonneg _) hQ3 ?_
  exact Qle_trans (qpow_den_pos (Qabs_den_pos hwd) (m + 1 + 1)) (Qeq_le (qpow_abs w (m + 1 + 1)))
    (qpow_base_mono (Qabs_den_pos hwd) hρd (Qabs_num_nonneg w) hw (m + 1 + 1))

/-- **The geometric inner bound** `|peval(δ,w,M) − δ_rat(w)| ≤ (1/3)·ρ^{M+1}` (`0 ≤ w`, `|w| ≤ ρ`). -/
theorem inner_eval_geo (w ρ : Q) (hwd : 0 < w.den) (hwn : 0 ≤ w.num) (hρd : 0 < ρ.den)
    (hρ0 : 0 ≤ ρ.num) (hw : Qle (Qabs w) ρ) (m : Nat) :
    Qle (Qabs (Qsub (peval dcoef w (m + 1)) (drat w))) (mul ⟨1, 3⟩ (qpow ρ (m + 1 + 1))) := by
  refine Qle_trans (Qmul_den_pos (by decide) (Qabs_den_pos (Qmul_den_pos
    (Qmul_den_pos (by decide) (dcoef_den (m + 1))) (qpow_den_pos hwd (m + 1 + 1)))))
    (inner_eval_bound w hwd hwn m) ?_
  refine Qle_trans (Qmul_den_pos (by decide) (Qmul_den_pos (by decide) (qpow_den_pos hρd (m + 1 + 1))))
    (Qmul_le_mul_left (by decide) (dcoef_term_geo w ρ hwd hρd hρ0 hw m)) ?_
  refine Qeq_le (Qeq_trans (Qmul_den_pos (by decide) (qpow_den_pos hρd (m + 1 + 1)))
    (Qmul_assoc3 ⟨1, 9⟩ ⟨3, 1⟩ (qpow ρ (m + 1 + 1)))
    (Qmul_congr (by decide : Qeq (mul (⟨1, 9⟩ : Q) ⟨3, 1⟩) ⟨1, 3⟩) (Qeq_refl _)))

-- The **`gcorner` term bound** for `dcoef` (the corner Cauchy estimate): since `δ₀=0` and `|δᵢ|≤1`, the
-- power coefficients satisfy `fpow(fabs δ) m k ≤ 2ᵏ` (m-INDEPENDENT — cleaner than the doubling's `4ᵐ`).

/-- `Σ_{i=0}^k (i=0 ? 0 : 2^{k−i}) ≤ 2^k` (the `δ₀=0` saving: drop the `i=0` term, `Σ_{i=1}^k 2^{k−i}=2^k−1`). -/
private theorem geoTail_le : ∀ k,
    Qle (Fsum (fun i => if i = 0 then (⟨0, 1⟩ : Q) else ⟨(2 : Int) ^ (k - i), 1⟩) k) ⟨(2 : Int) ^ k, 1⟩
  | 0 => by decide
  | (k + 1) => by
      have hgvd : ∀ i, 0 < (if i = 0 then (⟨0, 1⟩ : Q) else ⟨(2 : Int) ^ (k + 1 - i), 1⟩).den := by
        intro i; split <;> exact Nat.one_pos
      have hhd : ∀ i, 0 < (if i = k + 1 then (⟨0, 1⟩ : Q) else ⟨(2 : Int) ^ i, 1⟩).den := by
        intro i; split <;> exact Nat.one_pos
      have hstep1 : Qeq (Fsum (fun i => if i = 0 then (⟨0, 1⟩ : Q) else ⟨(2 : Int) ^ (k + 1 - i), 1⟩) (k + 1))
          (Fsum (fun i => if i = k + 1 then (⟨0, 1⟩ : Q) else ⟨(2 : Int) ^ i, 1⟩) (k + 1)) := by
        refine Qeq_trans (Fsum_den_pos (fun i => by split <;> exact Nat.one_pos) (k + 1))
          (Fsum_reverse hgvd (k + 1)) ?_
        exact Fsum_congr_le (fun i _ => by
          by_cases h : i = k + 1
          · subst h; rw [Nat.sub_self, if_pos rfl, if_pos rfl]; exact Qeq_refl _
          · rw [if_neg (show k + 1 - i ≠ 0 by omega), if_neg h,
              show k + 1 - (k + 1 - i) = i from by omega]; exact Qeq_refl _)
      have hk : Qeq (Fsum (fun i => if i = k + 1 then (⟨0, 1⟩ : Q) else ⟨(2 : Int) ^ i, 1⟩) k)
          (⟨(2 : Int) ^ (k + 1) - 1, 1⟩ : Q) :=
        Qeq_trans (Fsum_den_pos (fun _ => Nat.one_pos) k)
          (Fsum_congr_le (fun i _ => by rw [if_neg (show i ≠ k + 1 by omega)]; exact Qeq_refl _))
          (pow2_sum k)
      have hstep2 : Qeq (Fsum (fun i => if i = k + 1 then (⟨0, 1⟩ : Q) else ⟨(2 : Int) ^ i, 1⟩) (k + 1))
          (⟨(2 : Int) ^ (k + 1) - 1, 1⟩ : Q) := by
        show Qeq (add (Fsum (fun i => if i = k + 1 then (⟨0, 1⟩ : Q) else ⟨(2 : Int) ^ i, 1⟩) k)
          (if k + 1 = k + 1 then (⟨0, 1⟩ : Q) else ⟨(2 : Int) ^ (k + 1), 1⟩)) ⟨(2 : Int) ^ (k + 1) - 1, 1⟩
        rw [if_pos rfl]
        exact Qeq_trans (add_den_pos Nat.one_pos Nat.one_pos)
          (Qadd_congr hk (Qeq_refl _)) (by simp [Qeq, add])
      refine Qle_trans Nat.one_pos (Qeq_le (Qeq_trans (Fsum_den_pos hhd (k + 1)) hstep1 hstep2)) ?_
      show Qle (⟨(2 : Int) ^ (k + 1) - 1, 1⟩ : Q) ⟨(2 : Int) ^ (k + 1), 1⟩
      simp only [Qle]; push_cast; omega

/-- **The `δ`-power term bound**: `fpow(fabs δ) m k ≤ 2ᵏ` (m-INDEPENDENT, via `δ₀=0` + `|δᵢ|≤1`). -/
theorem fpow_fabs_dcoef_bound : ∀ m k, Qle (fpow (fabs dcoef) m k) ⟨(2 : Int) ^ k, 1⟩
  | 0, k => by
      show Qle (fone k) ⟨(2 : Int) ^ k, 1⟩
      by_cases h : k = 0
      · subst h; rw [show fone 0 = (⟨1, 1⟩ : Q) from by simp [fone]]; decide
      · rw [show fone k = (⟨0, 1⟩ : Q) from by simp [fone, h]]
        show (0 : Int) * 1 ≤ (2 : Int) ^ k * 1
        have : (0 : Int) ≤ (2 : Int) ^ k := by exact_mod_cast Nat.zero_le (2 ^ k)
        omega
  | (m + 1), k => by
      show Qle (Fsum (fun i => mul (fabs dcoef i) (fpow (fabs dcoef) m (k - i))) k) ⟨(2 : Int) ^ k, 1⟩
      have hterm : ∀ i, Qle (mul (fabs dcoef i) (fpow (fabs dcoef) m (k - i)))
          (if i = 0 then (⟨0, 1⟩ : Q) else ⟨(2 : Int) ^ (k - i), 1⟩) := by
        intro i
        by_cases h : i = 0
        · subst h; rw [if_pos rfl]
          refine Qeq_le (Qeq_trans (Qmul_den_pos Nat.one_pos
            (fpow_den_pos (fun j => fabs_den_pos dcoef_den j) m (k - 0)))
            (Qmul_congr (show Qeq (fabs dcoef 0) ⟨0, 1⟩ from by decide) (Qeq_refl _))
            (by simp [Qeq, mul]))
        · rw [if_neg h]
          refine Qle_trans (Qmul_den_pos Nat.one_pos Nat.one_pos)
            (Qmul_le_mul (fabs_den_pos dcoef_den i) Nat.one_pos
              (fpow_den_pos (fun j => fabs_den_pos dcoef_den j) m (k - i))
              (fabs_nonneg dcoef i) (fpow_num_nonneg (fun j => fabs_nonneg dcoef j) m (k - i))
              (dcoef_abs_le_one i) (fpow_fabs_dcoef_bound m (k - i))) (Qeq_le (Qone_mul _))
      exact Qle_trans (Fsum_den_pos (fun i => by split <;> exact Nat.one_pos) k)
        (Fsum_le_Fsum hterm k) (geoTail_le k)

end UOR.Bridge.F1Square.Analysis
