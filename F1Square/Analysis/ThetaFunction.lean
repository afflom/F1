/-
F1 square — Track 1, item 3 substrate: **the Jacobi theta function** `ψ(t) = Σ_{n≥1} e^{−πn²t}`,
as a genuine constructive real on its natural domain `t ≥ 1`.

This is the object the document names as the constructive substrate for the functional-equation seam
`CompletedZetaFE` (item 3): the Riemann FE is the Mellin transform of the theta modular transformation
`θ(1/t) = √t·θ(t)`. Here we build the function and its **convergence** from first principles, following
the established UOR precedent (term sequence → `RReg` regularity via a rational term bound → `Rlim`),
exactly as `Ceta`/`Czeta`/`CDigamma` were built.

The convergence is geometric and sidesteps the `Rpi²` `whnf` barrier entirely: for `t ≥ 1` the `m`-th
term `e^{−(m+1)²πt}` has exponent `(m+1)²·π·t ≥ (m+1)·m` (since `π·t ≥ 1`), so the exp-decay bound
`e^{−θ} ≤ 1/(1+τ)` (`Rexp_neg_le_ratio`, with `τ = (m+1)m`) gives `e^{−(m+1)²πt} ≤ 1/((m+1)m+1) ≤
1/((m+1)m)` — a *rational* `K/((m+1)m)` bound (`K = 1`) that feeds the generic convergence engine
`genSum_RReg`. `π` enters only as an opaque atom through `π·t ≥ 1` (`Rpi_lower_three`); no `Rpi²`.

The modular transformation itself (Poisson summation) remains the labelled classical seam.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.RealPow
import F1Square.Analysis.Pi
import F1Square.Analysis.ComplexDigamma
import F1Square.Analysis.ExpRealMono

namespace UOR.Bridge.F1Square.Analysis

/-- The exponent `(m+1)²·π·t` of the `m`-th theta term (so the sum ranges over `n = m+1 ≥ 1`). -/
def thetaArg (t : Real) (m : Nat) : Real :=
  Rmul (RofNat ((m + 1) * (m + 1))) (Rmul Rpi t)

/-- **The `m`-th Jacobi theta term** `e^{−(m+1)²πt}` (the `n = m+1` term of `Σ_{n≥1} e^{−πn²t}`). -/
def thetaTerm (t : Real) (m : Nat) : Real := RexpReal (Rneg (thetaArg t m))

/-- `π·t ≥ 1` for `t ≥ 1` (`π ≥ 3` is `Rpi_lower_three`, `t ≥ 1` is the hypothesis). -/
theorem one_le_pi_mul (t : Real) (ht : Rle one t) : Rle one (Rmul Rpi t) := by
  have hpi3 : Rle (ofQ (⟨3, 1⟩ : Q) (by decide)) Rpi := Rpi_lower_three
  have hpi_nn : Rnonneg Rpi :=
    Rnonneg_congr (Rsub_zero Rpi)
      (Rnonneg_Rsub_of_Rle (Rle_trans (Rle_ofQ_ofQ (by decide) (by decide) (by decide)) hpi3))
  have h1 : Rle Rpi (Rmul Rpi t) :=
    Rle_trans (Rle_of_Req (Req_symm (Rmul_one Rpi))) (Rmul_le_Rmul_left hpi_nn ht)
  exact Rle_trans (Rle_trans (Rle_ofQ_ofQ (by decide) (by decide) (by decide)) hpi3) h1

/-- **The exponent lower bound** `(m+1)²·π·t ≥ (m+1)·m` (for `t ≥ 1`): drop `π·t ≥ 1`, then
    `(m+1)² ≥ (m+1)m`. The `τ` for the exp-decay bound. -/
theorem thetaArg_lower (t : Real) (ht : Rle one t) (m : Nat) :
    Rle (ofQ (⟨((m + 1) * m : Nat), 1⟩ : Q) Nat.one_pos) (thetaArg t m) := by
  have hstep : Rle (RofNat ((m + 1) * (m + 1))) (thetaArg t m) :=
    Rle_trans (Rle_of_Req (Req_symm (Rmul_one (RofNat ((m + 1) * (m + 1))))))
      (Rmul_le_Rmul_left (Rnonneg_ofQ Nat.one_pos (Int.ofNat_nonneg _)) (one_le_pi_mul t ht))
  refine Rle_trans ?_ hstep
  refine Rle_ofQ_ofQ Nat.one_pos Nat.one_pos ?_
  have hI : (↑((m + 1) * m) : Int) ≤ ↑((m + 1) * (m + 1)) := by
    exact_mod_cast Nat.mul_le_mul (Nat.le_refl (m + 1)) (Nat.le_succ m)
  exact Int.mul_le_mul_of_nonneg_right hI (by exact_mod_cast Nat.zero_le 1)

/-- **The rational term bound** `e^{−(m+1)²πt} ≤ 1/((m+1)m)` (for `t ≥ 1`, `m ≥ 1`), in the exact form
    `genSum_RReg` consumes (`K = 1`). From `Rexp_neg_le_ratio` with `τ = (m+1)m`:
    `e^{−θ} ≤ 1/(1+(m+1)m) ≤ 1/((m+1)m)`. -/
theorem thetaTerm_le (t : Real) (ht : Rle one t) (m : Nat) (hm : 1 ≤ m) :
    Rle (thetaTerm t m)
      (ofQ (mul (⟨1, 1⟩ : Q) (⟨1, (m + 1) * m⟩ : Q))
        (Qmul_den_pos (by decide) (digamma_succ_mul_pos hm))) := by
  have hmulpos : 0 < ((m + 1) * m : Nat) := Nat.mul_pos (Nat.succ_pos m) (by omega)
  have hτn : 0 < (⟨((m + 1) * m : Nat), 1⟩ : Q).num := by
    show (0 : Int) < ((m + 1) * m : Nat); exact_mod_cast hmulpos
  have hp : (0 : Int) ≤ ((m + 1) * m : Nat) := Int.ofNat_nonneg _
  have hd : 0 < (add (⟨1, 1⟩ : Q) (⟨((m + 1) * m : Nat), 1⟩ : Q)).num := by
    show (0 : Int) < 1 * ((1 : Nat) : Int) + ((m + 1) * m : Nat) * ((1 : Nat) : Int)
    omega
  refine Rle_trans (Rexp_neg_le_ratio hτn Nat.one_pos (thetaArg_lower t ht m)) ?_
  refine Rle_ofQ_ofQ (Qinv_den_pos hd) (Qmul_den_pos (by decide) (digamma_succ_mul_pos hm)) ?_
  simp only [Qle, Qinv, add, mul]
  omega

/-- **The theta terms are regular**: the `K`-reindexed partial sums of `thetaTerm t` form a regular
    sequence (for `t ≥ 1`), via `genSum_RReg` with the rational bound `thetaTerm_le` (`K = 1`). The
    lower bound `−1/((m+1)m) ≤ e^{−…}` is trivial since the term is `≥ 0`. -/
theorem thetaTerm_RReg (t : Real) (ht : Rle one t) :
    RReg (fun j => genSum (thetaTerm t) (digammaMidx (⟨1, 1⟩ : Q) j)) :=
  genSum_RReg (thetaTerm t) (by decide) (by decide) (fun m hm =>
    ⟨Rle_trans
        (Rle_trans (Rle_Rneg (Rle_zero_of_Rnonneg
          (Rnonneg_ofQ (Qmul_den_pos (by decide) (digamma_succ_mul_pos hm))
            (show (0 : Int) ≤ 1 * 1 by decide))))
          (Rle_of_Req Rneg_zero))
        (Rle_zero_of_Rnonneg (RexpReal_nonneg _)),
      thetaTerm_le t ht m hm⟩)

/-- **The Jacobi theta function** `ψ(t) = Σ_{n≥1} e^{−πn²t}` on `t ≥ 1`, a genuine constructive real:
    the limit of the regular reindexed partial sums (`thetaTerm_RReg`). -/
def thetaFn (t : Real) (ht : Rle one t) : Real :=
  Rlim (fun j => genSum (thetaTerm t) (digammaMidx (⟨1, 1⟩ : Q) j)) (thetaTerm_RReg t ht)

/-- Non-negativity passes to a Bishop limit (local copy of `BLPipeline.Rnonneg_Rlim`, to avoid the
    `Analysis → Square` import). -/
theorem Rnonneg_Rlim_theta {X : Nat → Real} (h : RReg X) (hX : ∀ k, Rnonneg (X k)) :
    Rnonneg (Rlim X h) := by
  intro n
  have hbc := hX (4 * n + 3) (4 * n + 3)
  have hbd : 0 < (neg (Qbound (4 * n + 3))).den := by show 0 < 4 * n + 3 + 1; omega
  have hab : Qle (neg (Qbound n)) (neg (Qbound (4 * n + 3))) := by
    simp only [Qle, neg, Qbound]; push_cast; omega
  rw [Rlim_seq]
  exact Qle_trans hbd hab hbc

/-- The partial sum `Σ_{n<N} T n` of pointwise-non-negative terms is non-negative. -/
theorem genSum_nonneg {T : Nat → Real} (hT : ∀ n, Rnonneg (T n)) : ∀ N, Rnonneg (genSum T N)
  | 0 => Rnonneg_zero
  | (N + 1) => Rnonneg_Radd (genSum_nonneg hT N) (hT N)

/-- **The Jacobi theta function is non-negative** — a sum of the non-negative terms `e^{−(m+1)²πt}`,
    taken to its convergent limit. -/
theorem thetaFn_nonneg (t : Real) (ht : Rle one t) : Rnonneg (thetaFn t ht) :=
  Rnonneg_Rlim_theta (thetaTerm_RReg t ht)
    (fun j => genSum_nonneg (fun _ => RexpReal_nonneg _) (digammaMidx (⟨1, 1⟩ : Q) j))

/-- **Monotonicity passes to Bishop limits**: pointwise `X k ≤ Y k` gives `lim X ≤ lim Y` (a general
    reusable companion to `Rnonneg_Rlim`, previously absent). -/
theorem Rlim_le_Rlim {X Y : Nat → Real} (hX : RReg X) (hY : RReg Y) (h : ∀ k, Rle (X k) (Y k)) :
    Rle (Rlim X hX) (Rlim Y hY) := by
  intro n
  rw [Rlim_seq, Rlim_seq]
  have hk := h (4 * n + 3) (4 * n + 3)
  have hmid : 0 < (add ((Y (4 * n + 3)).seq (4 * n + 3)) (⟨2, 4 * n + 3 + 1⟩ : Q)).den :=
    add_den_pos ((Y (4 * n + 3)).den_pos (4 * n + 3)) (by show 0 < 4 * n + 3 + 1; omega)
  refine Qle_trans hmid hk (Qadd_le_add (Qle_refl _) ?_)
  simp only [Qle]; push_cast; omega

/-- The partial sum `Σ_{n<N} T n` is monotone under pointwise `≤` of the summands. -/
theorem genSum_le {T U : Nat → Real} (h : ∀ m, Rle (T m) (U m)) :
    ∀ N, Rle (genSum T N) (genSum U N)
  | 0 => Rle_refl zero
  | (N + 1) => Radd_le_add (genSum_le h N) (h N)

/-- **The theta exponent is monotone in `t`**: `(m+1)²πt₁ ≤ (m+1)²πt₂` for `t₁ ≤ t₂`. -/
theorem thetaArg_mono {t₁ t₂ : Real} (h : Rle t₁ t₂) (m : Nat) :
    Rle (thetaArg t₁ m) (thetaArg t₂ m) := by
  have hpi_nn : Rnonneg Rpi :=
    Rnonneg_congr (Rsub_zero Rpi)
      (Rnonneg_Rsub_of_Rle (Rle_trans (Rle_ofQ_ofQ (by decide) (by decide) (by decide))
        Rpi_lower_three))
  exact Rmul_le_Rmul_left (Rnonneg_ofQ Nat.one_pos (Int.ofNat_nonneg _))
    (Rmul_le_Rmul_left hpi_nn h)

/-- **The theta term is antitone in `t`**: `e^{−(m+1)²πt₂} ≤ e^{−(m+1)²πt₁}` for `t₁ ≤ t₂`. -/
theorem thetaTerm_antitone {t₁ t₂ : Real} (h : Rle t₁ t₂) (m : Nat) :
    Rle (thetaTerm t₂ m) (thetaTerm t₁ m) :=
  RexpReal_le_of_le (Rle_Rneg (thetaArg_mono h m))

/-- **The Jacobi theta function is antitone in `t`** (`t ≥ 1`): `ψ(t₂) ≤ ψ(t₁)` for `t₁ ≤ t₂` — more
    decay at larger `t`. -/
theorem thetaFn_antitone {t₁ t₂ : Real} (ht₁ : Rle one t₁) (ht₂ : Rle one t₂) (h : Rle t₁ t₂) :
    Rle (thetaFn t₂ ht₂) (thetaFn t₁ ht₁) :=
  Rlim_le_Rlim (thetaTerm_RReg t₂ ht₂) (thetaTerm_RReg t₁ ht₁)
    (fun j => genSum_le (fun m => thetaTerm_antitone h m) (digammaMidx (⟨1, 1⟩ : Q) j))

end UOR.Bridge.F1Square.Analysis
