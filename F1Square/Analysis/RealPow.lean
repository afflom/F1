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

/-- **Real powers, abstract form**: if `exp L ≈ N` then `exp(k·L) ≈ Nᵏ`. With `L = log n` and
    `N = n` (the v0.15.1 gate `Rexp_log_nat_Rlog`), this is `exp(k·log n) ≈ nᵏ`. Decoupled from the
    `Rlog` plumbing so that any logarithm witness `exp L ≈ N` produces its powers — the established
    abstract-reconciliation pattern (cf. `Rexp_two_artanh_via`). -/
theorem RexpReal_nsmul_eq {L N : Real} (h : Req (RexpReal L) N) (k : Nat) :
    Req (RexpReal (Rnsmul k L)) (Rpow N k) :=
  Req_trans (RexpReal_nsmul L k) (Rpow_congr h k)

end UOR.Bridge.F1Square.Analysis
