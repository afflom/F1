/-
F1 square — v0.22.0 Track 1, brick (special-function substrate): **the formal arctan ODE**
`arctan′(t) = 1/(1+t²)` at the level of formal power-series coefficients.

This is the alternating sibling of `dgeom_ode` (ExpLog.lean), which proved that the `(1+w)/(1−w)`
coefficients satisfy `E′ = (2/(1−w²))·E` — the engine behind the *exact rational* artanh exp identity.

The arctan series `A(t) = Σ (−1)ⁿ t^{2n+1}/(2n+1)` has formal derivative `A′(t) = Σ (−1)ⁿ t^{2n} =
1/(1+t²)` (`arctan_fderiv`), and `(1+t²)·A′(t) = 1` (`onePlusSq_geomAlt`). Unlike the geometric
series, the arctan series is *not* rational-summable, so this formal identity does not collapse to an
exact rational value identity (as the artanh one did): the value-level inverse-function fact
`tan(arctan t) = t` — the remaining gap for the argument-addition `arg(zw) = arg z + arg w` (the
imaginary half of `Clog` additivity) — requires a formal-PS → value (fundamental-theorem-of-calculus)
bridge on top of this ODE. This brick is the constructive seed of that bridge.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.ExpLog
import F1Square.Analysis.Arctan

namespace UOR.Bridge.F1Square.Analysis

/-- The **arctan coefficient sequence**: coefficient of `tᵏ` in `Σ (−1)ⁿ t^{2n+1}/(2n+1)`. Nonzero only
    at odd degree `k = 2n+1`, where it is `(−1)ⁿ/(2n+1) = (−1)^{k/2}/k`. -/
def arctanCoeff (k : Nat) : Q :=
  if k % 2 = 1 then mul (qpow (⟨-1, 1⟩ : Q) (k / 2)) ⟨1, k⟩ else ⟨0, 1⟩

/-- The **`1/(1+t²)` coefficient sequence**: `Σ (−1)ⁿ t^{2n}`. Nonzero only at even degree `k = 2n`,
    where it is `(−1)ⁿ = (−1)^{k/2}`. -/
def geomAlt (k : Nat) : Q :=
  if k % 2 = 0 then qpow (⟨-1, 1⟩ : Q) (k / 2) else ⟨0, 1⟩

theorem arctanCoeff_den_pos (k : Nat) : 0 < (arctanCoeff k).den := by
  unfold arctanCoeff; split
  · rename_i h
    refine Qmul_den_pos (qpow_den_pos (by decide) (k / 2)) ?_
    show 0 < k; omega
  · exact Nat.one_pos

theorem geomAlt_den_pos (k : Nat) : 0 < (geomAlt k).den := by
  unfold geomAlt; split
  · exact qpow_den_pos (by decide) _
  · exact Nat.one_pos

/-- **The formal arctan ODE**: `fderiv arctanCoeff = geomAlt`, i.e. `A′(t) = 1/(1+t²)`. At even degree
    `k = 2n` the derivative `(k+1)·arctanCoeff(k+1) = (2n+1)·(−1)ⁿ/(2n+1) = (−1)ⁿ` matches `geomAlt(2n)`;
    at odd degree the next arctan coefficient vanishes, matching `geomAlt(odd) = 0`. -/
theorem arctan_fderiv (k : Nat) : Qeq (fderiv arctanCoeff k) (geomAlt k) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · -- k even: k = 2n; k+1 = 2n+1 odd, (2n+1)/2 = n, (2n)/2 = n
    obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    show Qeq (mul ⟨(2 * n + 1 : Int), 1⟩ (arctanCoeff (2 * n + 1))) (geomAlt (2 * n))
    unfold arctanCoeff geomAlt
    rw [if_pos (by omega : (2 * n + 1) % 2 = 1), if_pos (by omega : (2 * n) % 2 = 0),
      show (2 * n + 1) / 2 = n from by omega, show (2 * n) / 2 = n from by omega]
    -- (2n+1)·((−1)ⁿ·(1/(2n+1))) ≈ (−1)ⁿ
    simp only [Qeq, mul]; push_cast; ring_uor
  · -- k odd: k = 2n+1; k+1 = 2n+2 even, arctanCoeff(2n+2) = 0; geomAlt(2n+1) = 0
    obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    show Qeq (mul ⟨(2 * n + 1 + 1 : Int), 1⟩ (arctanCoeff (2 * n + 1 + 1))) (geomAlt (2 * n + 1))
    unfold arctanCoeff geomAlt
    rw [if_neg (by omega : ¬ (2 * n + 1 + 1) % 2 = 1), if_neg (by omega : ¬ (2 * n + 1) % 2 = 0)]
    -- (2n+2)·0 ≈ 0
    show Qeq (mul ⟨(2 * n + 1 + 1 : Int), 1⟩ ⟨0, 1⟩) ⟨0, 1⟩
    simp only [Qeq, mul]; omega

/-- **The `(1+t²)·A′ = 1` annihilation, homogeneous part**: the derivative coefficients `geomAlt`
    satisfy `geomAlt(k+2) + geomAlt(k) ≈ 0` — i.e. multiplication by `1+t²` kills every degree `≥ 2`.
    The parity recurrence `(−1)^{n+1} + (−1)ⁿ = 0` (`qpow_succ` of `⟨−1,1⟩`). -/
theorem geomAlt_recurrence (k : Nat) : Qeq (add (geomAlt (k + 2)) (geomAlt k)) ⟨0, 1⟩ := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    unfold geomAlt
    rw [if_pos (by omega : (2 * n + 2) % 2 = 0), if_pos (by omega : (2 * n) % 2 = 0),
      show (2 * n + 2) / 2 = n + 1 from by omega, show (2 * n) / 2 = n from by omega, qpow_succ]
    -- (−1)ⁿ·(−1) + (−1)ⁿ ≈ 0
    simp only [Qeq, add, mul]; push_cast; ring_uor
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    unfold geomAlt
    rw [if_neg (by omega : ¬ (2 * n + 1 + 2) % 2 = 0), if_neg (by omega : ¬ (2 * n + 1) % 2 = 0)]
    show Qeq (add (⟨0, 1⟩ : Q) ⟨0, 1⟩) ⟨0, 1⟩
    decide

/-- Boundary value: `A′(0) = 1` (`geomAlt 0 = 1`), the normalization `arctan′(0) = 1/(1+0²) = 1`. -/
theorem geomAlt_zero : geomAlt 0 = ⟨1, 1⟩ := by decide

/-- Boundary value: the degree-1 coefficient of `A′` vanishes (`geomAlt 1 = 0`). -/
theorem geomAlt_one : geomAlt 1 = ⟨0, 1⟩ := by decide

-- ===========================================================================
-- The formal sin/cos ODE  sin′ = cos,  cos′ = −sin  (degree-indexed coefficients).
-- Toward the value identity tan(arctan t) = t via the formal composition sin∘arctan.
-- ===========================================================================

/-- The **`sin` coefficient sequence**: coefficient of `tᵏ` in `Σ (−1)ⁿ t^{2n+1}/(2n+1)!`. Nonzero only
    at odd degree `k = 2n+1`, where it is `(−1)ⁿ/k! = (−1)^{k/2}/k!`. -/
def sinCoeff (k : Nat) : Q :=
  if k % 2 = 1 then mul (qpow (⟨-1, 1⟩ : Q) (k / 2)) ⟨1, fct k⟩ else ⟨0, 1⟩

/-- The **`cos` coefficient sequence**: coefficient of `tᵏ` in `Σ (−1)ⁿ t^{2n}/(2n)!`. Nonzero only at
    even degree `k = 2n`, where it is `(−1)ⁿ/k! = (−1)^{k/2}/k!`. -/
def cosCoeff (k : Nat) : Q :=
  if k % 2 = 0 then mul (qpow (⟨-1, 1⟩ : Q) (k / 2)) ⟨1, fct k⟩ else ⟨0, 1⟩

/-- Pure-`Int` core of the factorial-telescope step in `sin_fderiv` / the matching `cos` even-branch:
    `(2m+1)·(P·1)·(D·F) = (P·1)·(1·(D·((2m+1)·F)))`. Extracted because `ring_uor` reifies cleanly only
    over bare `Int` atoms (the in-place goal carries the opaque cast `↑(fct …)`). -/
private theorem sincos_fct_poly (m P D F : Int) :
    (2 * m + 1) * (P * 1) * (D * F) = P * 1 * (1 * (D * ((2 * m + 1) * F))) := by ring_uor

/-- Pure-`Int` core of the factorial-telescope step in `cos_fderiv` (odd branch), with the sign advance
    `(−1)^{n+1} = −(−1)ⁿ` already pulled out: `(2m+2)·(−P·1)·(D·F) = −(P·1)·(1·(1·D·((2m+2)·F)))`. -/
private theorem cos_fct_poly (m P D F : Int) :
    (2 * m + 1 + 1) * (-1 * P * 1) * (D * F) = -(P * 1) * (1 * (1 * D * ((2 * m + 1 + 1) * F))) := by
  ring_uor

theorem sinCoeff_den_pos (k : Nat) : 0 < (sinCoeff k).den := by
  unfold sinCoeff; split
  · exact Qmul_den_pos (qpow_den_pos (by decide) (k / 2)) (fct_pos k)
  · exact Nat.one_pos

theorem cosCoeff_den_pos (k : Nat) : 0 < (cosCoeff k).den := by
  unfold cosCoeff; split
  · exact Qmul_den_pos (qpow_den_pos (by decide) (k / 2)) (fct_pos k)
  · exact Nat.one_pos

/-- **The formal `sin` ODE**: `fderiv sinCoeff = cosCoeff` (`sin′ = cos`). At even degree `k = 2n` the
    factorial telescopes `(2n+1)·(1/(2n+1)!) = 1/(2n)!` with the same sign `(−1)ⁿ`; at odd degree the
    next `sin` coefficient vanishes, matching `cosCoeff(odd) = 0`. -/
theorem sin_fderiv (k : Nat) : Qeq (fderiv sinCoeff k) (cosCoeff k) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    show Qeq (mul ⟨(2 * n + 1 : Int), 1⟩ (sinCoeff (2 * n + 1))) (cosCoeff (2 * n))
    unfold sinCoeff cosCoeff
    rw [if_pos (by omega : (2 * n + 1) % 2 = 1), if_pos (by omega : (2 * n) % 2 = 0),
      show (2 * n + 1) / 2 = n from by omega, show (2 * n) / 2 = n from by omega]
    have hfZ : (fct (2 * n + 1) : Int) = (2 * n + 1) * fct (2 * n) := by
      exact_mod_cast fct_succ (2 * n)
    simp only [Qeq, mul]; push_cast [hfZ]
    exact sincos_fct_poly (n : Int) ((qpow (⟨-1, 1⟩ : Q) n).num)
      ((qpow (⟨-1, 1⟩ : Q) n).den : Int) ((fct (2 * n) : Nat) : Int)
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    show Qeq (mul ⟨(2 * n + 1 + 1 : Int), 1⟩ (sinCoeff (2 * n + 1 + 1))) (cosCoeff (2 * n + 1))
    unfold sinCoeff cosCoeff
    rw [if_neg (by omega : ¬ (2 * n + 1 + 1) % 2 = 1), if_neg (by omega : ¬ (2 * n + 1) % 2 = 0)]
    show Qeq (mul ⟨(2 * n + 1 + 1 : Int), 1⟩ ⟨0, 1⟩) ⟨0, 1⟩
    simp only [Qeq, mul]; omega

/-- **The formal `cos` ODE**: `fderiv cosCoeff = −sinCoeff` (`cos′ = −sin`). At odd degree `k = 2n+1`
    the factorial telescopes `(2n+2)·(1/(2n+2)!) = 1/(2n+1)!`, and the sign advances one step
    (`(−1)^{n+1} = −(−1)ⁿ`, via `qpow_succ`), matching `−sinCoeff(2n+1)`; at even degree both vanish. -/
theorem cos_fderiv (k : Nat) : Qeq (fderiv cosCoeff k) (neg (sinCoeff k)) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    show Qeq (mul ⟨(2 * n + 1 : Int), 1⟩ (cosCoeff (2 * n + 1))) (neg (sinCoeff (2 * n)))
    unfold cosCoeff sinCoeff
    rw [if_neg (by omega : ¬ (2 * n + 1) % 2 = 0), if_neg (by omega : ¬ (2 * n) % 2 = 1)]
    show Qeq (mul ⟨(2 * n + 1 : Int), 1⟩ ⟨0, 1⟩) (neg ⟨0, 1⟩)
    simp only [Qeq, mul, neg]; omega
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    show Qeq (mul ⟨(2 * n + 1 + 1 : Int), 1⟩ (cosCoeff (2 * n + 1 + 1))) (neg (sinCoeff (2 * n + 1)))
    unfold cosCoeff sinCoeff
    rw [if_pos (by omega : (2 * n + 1 + 1) % 2 = 0), if_pos (by omega : (2 * n + 1) % 2 = 1),
      show (2 * n + 1 + 1) / 2 = n + 1 from by omega, show (2 * n + 1) / 2 = n from by omega,
      qpow_succ]
    have hfZ : (fct (2 * n + 1 + 1) : Int) = (2 * n + 1 + 1) * fct (2 * n + 1) := by
      exact_mod_cast fct_succ (2 * n + 1)
    simp only [Qeq, mul, neg]; push_cast [hfZ]
    exact cos_fct_poly (n : Int) ((qpow (⟨-1, 1⟩ : Q) n).num)
      ((qpow (⟨-1, 1⟩ : Q) n).den : Int) ((fct (2 * n + 1) : Nat) : Int)

-- ===========================================================================
-- Formal composition  sin∘arctan, cos∘arctan: the chain-rule ODE relations
--   (sin∘arctan)′ = (cos∘arctan)·A′,   (cos∘arctan)′ = −(sin∘arctan)·A′.
-- ===========================================================================

/-- Negation distributes over the formal `add`: `(−A) + (−B) ≈ −(A + B)`. -/
theorem Qadd_neg_distrib (A B : Q) : Qeq (add (neg A) (neg B)) (neg (add A B)) := by
  simp only [Qeq, add, neg]; push_cast; ring_uor

/-- A finite sum of negations is the negation of the sum: `Σ (−fᵢ) ≈ −(Σ fᵢ)`. -/
theorem Fsum_neg (f : Nat → Q) (hf : ∀ i, 0 < (f i).den) (k : Nat) :
    Qeq (Fsum (fun i => neg (f i)) k) (neg (Fsum f k)) := by
  induction k with
  | zero => exact Qeq_refl _
  | succ n ih =>
      show Qeq (add (Fsum (fun i => neg (f i)) n) (neg (f (n + 1)))) (neg (add (Fsum f n) (f (n + 1))))
      exact Qeq_trans (add_den_pos (neg_den_pos (Fsum_den_pos hf n)) (neg_den_pos (hf (n + 1))))
        (Qadd_congr ih (Qeq_refl _)) (Qadd_neg_distrib (Fsum f n) (f (n + 1)))

/-- The formal composition is left-linear over negation: `(−a)∘b ≈ −(a∘b)`. Pull the sign through the
    composition sum so the `cos` chain rule `(cos∘arctan)′ = −(sin∘arctan)·A′` lands in clean form. -/
theorem fcomp_neg_left (a b : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den) (k : Nat) :
    Qeq (fcomp (fun m => neg (a m)) b k) (neg (fcomp a b k)) := by
  show Qeq (Fsum (fun m => mul (neg (a m)) (fpow b m k)) k) (neg (Fsum (fun m => mul (a m) (fpow b m k)) k))
  refine Qeq_trans (Fsum_den_pos (fun m => neg_den_pos (Qmul_den_pos (ha m) (fpow_den_pos hb m k))) k)
    (Fsum_congr (fun m => Qmul_neg_left (a m) (fpow b m k)) k)
    (Fsum_neg (fun m => mul (a m) (fpow b m k)) (fun m => Qmul_den_pos (ha m) (fpow_den_pos hb m k)) k)

/-- The formal Cauchy product is left-linear over negation: `(−a)·b ≈ −(a·b)`. -/
theorem fmul_neg_left (a b : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den) (k : Nat) :
    Qeq (fmul (fun i => neg (a i)) b k) (neg (fmul a b k)) := by
  show Qeq (Fsum (fun i => mul (neg (a i)) (b (k - i))) k) (neg (Fsum (fun i => mul (a i) (b (k - i))) k))
  refine Qeq_trans (Fsum_den_pos (fun i => neg_den_pos (Qmul_den_pos (ha i) (hb (k - i)))) k)
    (Fsum_congr (fun i => Qmul_neg_left (a i) (b (k - i))) k)
    (Fsum_neg (fun i => mul (a i) (b (k - i))) (fun i => Qmul_den_pos (ha i) (hb (k - i))) k)

/-- `arctanCoeff 0 = 0` — the composition prerequisite `b(0) = 0` for `fcomp_chain`. -/
theorem arctanCoeff_zero : Qeq (arctanCoeff 0) ⟨0, 1⟩ := by decide

/-- **The `sin∘arctan` chain-rule ODE**: `(sin∘arctan)′ = (cos∘arctan)·A′`, with `A′ = geomAlt`.
    `fcomp_chain` + `sin_fderiv` (sin′=cos, via `fcomp_congr_left`) + `arctan_fderiv` (A′=geomAlt). -/
theorem sinComp_deriv (k : Nat) :
    Qeq (fderiv (fcomp sinCoeff arctanCoeff) k) (fmul (fcomp cosCoeff arctanCoeff) geomAlt k) := by
  refine Qeq_trans
    (fmul_den_pos (fun i => fcomp_den_pos (fun j => fderiv_den_pos sinCoeff_den_pos j) arctanCoeff_den_pos i)
      (fun i => fderiv_den_pos arctanCoeff_den_pos i) k)
    (fcomp_chain sinCoeff arctanCoeff sinCoeff_den_pos arctanCoeff_den_pos arctanCoeff_zero k) ?_
  refine Qeq_trans
    (fmul_den_pos (fun i => fcomp_den_pos cosCoeff_den_pos arctanCoeff_den_pos i)
      (fun i => fderiv_den_pos arctanCoeff_den_pos i) k)
    (fmul_congr_left (fun i => fcomp_congr_left (b := arctanCoeff) sin_fderiv i) k)
    (fmul_congr_right (fun i => arctan_fderiv i) k)

/-- **The `cos∘arctan` chain-rule ODE**: `(cos∘arctan)′ = −(sin∘arctan)·A′`.
    `fcomp_chain` + `cos_fderiv` (cos′=−sin) + `fcomp_neg_left` (pull the sign out) + `arctan_fderiv`. -/
theorem cosComp_deriv (k : Nat) :
    Qeq (fderiv (fcomp cosCoeff arctanCoeff) k) (neg (fmul (fcomp sinCoeff arctanCoeff) geomAlt k)) := by
  refine Qeq_trans
    (fmul_den_pos (fun i => fcomp_den_pos (fun j => fderiv_den_pos cosCoeff_den_pos j) arctanCoeff_den_pos i)
      (fun i => fderiv_den_pos arctanCoeff_den_pos i) k)
    (fcomp_chain cosCoeff arctanCoeff cosCoeff_den_pos arctanCoeff_den_pos arctanCoeff_zero k) ?_
  -- fcomp (fderiv cosCoeff) arctanCoeff ≈ fcomp (neg sinCoeff) arctanCoeff ≈ neg (fcomp sinCoeff arctanCoeff)
  have hcomp : ∀ i, Qeq (fcomp (fderiv cosCoeff) arctanCoeff i) (neg (fcomp sinCoeff arctanCoeff i)) := by
    intro i
    refine Qeq_trans
      (fcomp_den_pos (fun j => neg_den_pos (sinCoeff_den_pos j)) arctanCoeff_den_pos i)
      (fcomp_congr_left (b := arctanCoeff) (fun j => cos_fderiv j) i)
      (fcomp_neg_left sinCoeff arctanCoeff sinCoeff_den_pos arctanCoeff_den_pos i)
  refine Qeq_trans
    (fmul_den_pos (fun i => neg_den_pos (fcomp_den_pos sinCoeff_den_pos arctanCoeff_den_pos i))
      (fun i => fderiv_den_pos arctanCoeff_den_pos i) k)
    (fmul_congr_left hcomp k) ?_
  -- fmul (neg (fcomp sin arctan)) (fderiv arctan) ≈ neg (fmul (fcomp sin arctan) geomAlt)
  refine Qeq_trans
    (fmul_den_pos (fun i => neg_den_pos (fcomp_den_pos sinCoeff_den_pos arctanCoeff_den_pos i))
      geomAlt_den_pos k)
    (fmul_congr_right (fun i => arctan_fderiv i) k) ?_
  exact fmul_neg_left (fcomp sinCoeff arctanCoeff) geomAlt
    (fun i => fcomp_den_pos sinCoeff_den_pos arctanCoeff_den_pos i) geomAlt_den_pos k

-- ===========================================================================
-- Sparse-convolution evaluation: extracting fmul against the identity series
-- (using the existing `Fsum_single` from ExpLog.lean).
-- ===========================================================================

/-- The **identity series** `X(t) = t`: coefficient `1` at degree `1`, else `0`. Multiplying by it
    shifts a series up one degree: `(X·H)(k+1) = H(k)`. -/
def Xident (k : Nat) : Q := if k = 1 then ⟨1, 1⟩ else ⟨0, 1⟩

theorem Xident_den_pos (k : Nat) : 0 < (Xident k).den := by unfold Xident; split <;> exact Nat.one_pos

/-- `(X·H)(0) ≈ 0`. -/
theorem fmul_Xident_zero (H : Nat → Q) : Qeq (fmul Xident H 0) ⟨0, 1⟩ := by
  show Qeq (mul (Xident 0) (H 0)) ⟨0, 1⟩
  unfold Xident; rw [if_neg (by omega)]; simp only [Qeq, mul]; omega

/-- **Shift law**: `(X·H)(k+1) ≈ H(k)` — multiplication by the identity series `X(t)=t`. Single nonzero
    convolution term at `i = 1` (via `Fsum_single`). -/
theorem fmul_Xident (H : Nat → Q) (hH : ∀ i, 0 < (H i).den) (k : Nat) :
    Qeq (fmul Xident H (k + 1)) (H k) := by
  show Qeq (Fsum (fun i => mul (Xident i) (H (k + 1 - i))) (k + 1)) (H k)
  refine Qeq_trans (Qmul_den_pos (Xident_den_pos 1) (hH (k + 1 - 1)))
    (Fsum_single (f := fun i => mul (Xident i) (H (k + 1 - i)))
      (fun i => Qmul_den_pos (Xident_den_pos i) (hH _)) (j := 1) ?_ (k := k + 1) (by omega)) ?_
  · intro i hi1
    show Qeq (mul (Xident i) (H (k + 1 - i))) ⟨0, 1⟩
    unfold Xident; rw [if_neg hi1]; simp only [Qeq, mul]; omega
  · show Qeq (mul (Xident 1) (H (k + 1 - 1))) (H k)
    rw [show k + 1 - 1 = k from by omega]
    unfold Xident; rw [if_pos rfl]
    simp only [Qeq, mul]; push_cast; ring_uor

/-- The **`1 + t²` series**: coefficient `1` at degrees `0` and `2`, else `0`. -/
def onePlusSq (k : Nat) : Q := if k = 0 then ⟨1, 1⟩ else if k = 2 then ⟨1, 1⟩ else ⟨0, 1⟩

/-- The **`t²` series**: coefficient `1` at degree `2`, else `0`. -/
def sq2 (k : Nat) : Q := if k = 2 then ⟨1, 1⟩ else ⟨0, 1⟩

theorem onePlusSq_den_pos (k : Nat) : 0 < (onePlusSq k).den := by
  unfold onePlusSq; split
  · exact Nat.one_pos
  · split <;> exact Nat.one_pos

theorem sq2_den_pos (k : Nat) : 0 < (sq2 k).den := by unfold sq2; split <;> exact Nat.one_pos

/-- Left unit for the formal Cauchy product: `fone · H ≈ H` (via `fmul_comm` + `fmul_one`). -/
theorem fmul_fone_left (H : Nat → Q) (hH : ∀ i, 0 < (H i).den) (k : Nat) :
    Qeq (fmul fone H k) (H k) :=
  Qeq_trans (fmul_den_pos hH (fun i => fone_den_pos i) k)
    (fmul_comm fone H (fun i => fone_den_pos i) hH k) (fmul_one H hH k)

/-- **Shift-by-two law**: `(t²·H)(k+2) ≈ H(k)`. Single nonzero convolution term at `i = 2`. -/
theorem fmul_sq2 (H : Nat → Q) (hH : ∀ i, 0 < (H i).den) (k : Nat) :
    Qeq (fmul sq2 H (k + 2)) (H k) := by
  show Qeq (Fsum (fun i => mul (sq2 i) (H (k + 2 - i))) (k + 2)) (H k)
  refine Qeq_trans (Qmul_den_pos (sq2_den_pos 2) (hH (k + 2 - 2)))
    (Fsum_single (f := fun i => mul (sq2 i) (H (k + 2 - i)))
      (fun i => Qmul_den_pos (sq2_den_pos i) (hH _)) (j := 2) ?_ (k := k + 2) (by omega)) ?_
  · intro i hi2
    show Qeq (mul (sq2 i) (H (k + 2 - i))) ⟨0, 1⟩
    unfold sq2; rw [if_neg hi2]; simp only [Qeq, mul]; omega
  · show Qeq (mul (sq2 2) (H (k + 2 - 2))) (H k)
    rw [show k + 2 - 2 = k from by omega]
    unfold sq2; rw [if_pos rfl]; simp only [Qeq, mul]; push_cast; ring_uor

/-- `onePlusSq ≈ fone + sq2` (pointwise) — the decomposition that splits its convolution. -/
theorem onePlusSq_decomp (i : Nat) : Qeq (onePlusSq i) (add (fone i) (sq2 i)) := by
  by_cases h0 : i = 0
  · subst h0; unfold onePlusSq fone sq2; decide
  · by_cases h2 : i = 2
    · subst h2; unfold onePlusSq fone sq2; decide
    · unfold onePlusSq fone sq2; simp only [if_neg h0, if_neg h2]; decide

/-- **The `(1+t²)·H` annihilation form**: `((1+t²)·H)(k+2) ≈ H(k+2) + H(k)`. Two nonzero convolution
    terms (`i = 0, 2`), extracted via the `fone + t²` decomposition. -/
theorem fmul_onePlusSq (H : Nat → Q) (hH : ∀ i, 0 < (H i).den) (k : Nat) :
    Qeq (fmul onePlusSq H (k + 2)) (add (H (k + 2)) (H k)) := by
  refine Qeq_trans
    (fmul_den_pos (fun i => add_den_pos (fone_den_pos i) (sq2_den_pos i)) hH (k + 2))
    (fmul_congr_left (fun i => onePlusSq_decomp i) (k + 2)) ?_
  refine Qeq_trans (add_den_pos (fmul_den_pos (fun i => fone_den_pos i) hH (k + 2))
      (fmul_den_pos (fun i => sq2_den_pos i) hH (k + 2)))
    (fmul_add_left (fun i => fone_den_pos i) (fun i => sq2_den_pos i) hH (k + 2)) ?_
  exact Qadd_congr (fmul_fone_left H hH (k + 2)) (fmul_sq2 H hH k)

/-- `((1+t²)·H)(0) ≈ H(0)`. -/
theorem fmul_onePlusSq_zero (H : Nat → Q) :
    Qeq (fmul onePlusSq H 0) (H 0) := by
  show Qeq (mul (onePlusSq 0) (H 0)) (H 0)
  unfold onePlusSq; rw [if_pos rfl]; simp only [Qeq, mul]; push_cast; ring_uor

/-- `((1+t²)·H)(1) ≈ H(1)`. -/
theorem fmul_onePlusSq_one (H : Nat → Q) (hH : ∀ i, 0 < (H i).den) :
    Qeq (fmul onePlusSq H 1) (H 1) := by
  show Qeq (add (mul (onePlusSq 0) (H 1)) (mul (onePlusSq 1) (H 0))) (H 1)
  have h0 : Qeq (mul (onePlusSq 0) (H 1)) (H 1) := by
    unfold onePlusSq; rw [if_pos rfl]; simp only [Qeq, mul]; push_cast; ring_uor
  have h1 : Qeq (mul (onePlusSq 1) (H 0)) ⟨0, 1⟩ := by
    unfold onePlusSq; rw [if_neg (by omega), if_neg (by omega)]; simp only [Qeq, mul]; omega
  exact Qeq_trans (add_den_pos (hH 1) (by decide))
    (Qadd_congr h0 h1) (Qadd_zero_right (H 1))

-- ===========================================================================
-- Formal ODE uniqueness:  (1+t²)·H′ = t·H  and  H(0)=0  imply  H = 0.
-- ===========================================================================

/-- **Strip a positive integer coefficient**: `c·x ≈ 0` with `c > 0` forces `x ≈ 0`. -/
theorem Qmul_pos_strip (c : Int) (hc : 0 < c) (x : Q) (h : Qeq (mul ⟨c, 1⟩ x) ⟨0, 1⟩) :
    Qeq x ⟨0, 1⟩ := by
  have hcx : c * x.num = 0 := by
    have hh : (c * x.num) * ((1 : Nat) : Int) = (0 : Int) * (((1 : Nat) * x.den : Nat) : Int) := h
    simpa using hh
  have hx0 : x.num = 0 := by
    rcases Int.mul_eq_zero.mp hcx with h1 | h1
    · omega
    · exact h1
  show x.num * ((1 : Nat) : Int) = 0 * ((x.den : Nat) : Int)
  rw [hx0]; simp

/-- `c·0 ≈ 0` for the formal scalar `⟨c,1⟩`. -/
theorem Qmul_const_zero (c : Int) (x : Q) (hx : Qeq x ⟨0, 1⟩) : Qeq (mul ⟨c, 1⟩ x) ⟨0, 1⟩ := by
  refine Qeq_trans (Qmul_den_pos Nat.one_pos Nat.one_pos) (Qmul_congr (Qeq_refl _) hx) ?_
  show Qeq (mul (⟨c, 1⟩ : Q) ⟨0, 1⟩) ⟨0, 1⟩
  simp only [Qeq, mul]; ring_uor

/-- From `a + b ≈ 0` and `b ≈ 0` conclude `a ≈ 0`. -/
theorem Qadd_right_zero_cancel (a b : Q) (ha : 0 < a.den) (hbd : 0 < b.den)
    (hab : Qeq (add a b) ⟨0, 1⟩) (hb : Qeq b ⟨0, 1⟩) : Qeq a ⟨0, 1⟩ := by
  have s1 : Qeq a (add a ⟨0, 1⟩) := Qeq_symm (Qadd_zero_right a)
  have s2 : Qeq (add a ⟨0, 1⟩) (add a b) := Qadd_congr (Qeq_refl a) (Qeq_symm hb)
  exact Qeq_trans (add_den_pos ha Nat.one_pos) s1
    (Qeq_trans (add_den_pos ha hbd) s2 hab)

/-- `fderiv H k ≈ 0` forces `H(k+1) ≈ 0` (strip the coefficient `k+1 > 0`). -/
theorem fderiv_strip (H : Nat → Q) (k : Nat) (h : Qeq (fderiv H k) ⟨0, 1⟩) :
    Qeq (H (k + 1)) ⟨0, 1⟩ :=
  Qmul_pos_strip ((k : Int) + 1) (by omega) (H (k + 1)) h

/-- **Formal ODE uniqueness**: if `H` satisfies the homogeneous ODE `(1+t²)·H′ ≈ t·H` (coefficientwise,
    `fmul onePlusSq (fderiv H) ≈ fmul Xident H`) and `H(0) ≈ 0`, then `H ≈ 0`. The coefficient recurrence
    `(k+3)·H(k+3) ≈ −k·H(k+1)` (with seeds `H(0)=H(1)=H(2)=0` from the low-degree relation) forces every
    coefficient to vanish — a triple-invariant induction. The discrete analog of `H′ = a·H, H(0)=0 ⟹ H=0`. -/
theorem ode_unique (H : Nat → Q) (hH : ∀ i, 0 < (H i).den) (hH0 : Qeq (H 0) ⟨0, 1⟩)
    (hrel : ∀ k, Qeq (fmul onePlusSq (fderiv H) k) (fmul Xident H k)) :
    ∀ k, Qeq (H k) ⟨0, 1⟩ := by
  have hfd : ∀ i, 0 < (fderiv H i).den := fun i => fderiv_den_pos hH i
  -- seed H 1: from the relation at 0
  have hfd0 : Qeq (fderiv H 0) ⟨0, 1⟩ :=
    Qeq_trans (fmul_den_pos onePlusSq_den_pos hfd 0)
      (Qeq_symm (fmul_onePlusSq_zero (fderiv H)))
      (Qeq_trans (fmul_den_pos Xident_den_pos hH 0) (hrel 0) (fmul_Xident_zero H))
  have hH1 : Qeq (H 1) ⟨0, 1⟩ := fderiv_strip H 0 hfd0
  -- seed H 2: from the relation at 1
  have hfd1 : Qeq (fderiv H 1) ⟨0, 1⟩ :=
    Qeq_trans (fmul_den_pos onePlusSq_den_pos hfd 1)
      (Qeq_symm (fmul_onePlusSq_one (fderiv H) hfd))
      (Qeq_trans (fmul_den_pos Xident_den_pos hH 1) (hrel 1)
        (Qeq_trans (hH 0) (fmul_Xident H hH 0) hH0))
  have hH2 : Qeq (H 2) ⟨0, 1⟩ := fderiv_strip H 1 hfd1
  -- recurrence: H(m+1) ≈ 0 ⟹ H(m+3) ≈ 0
  have hrec : ∀ m, Qeq (H (m + 1)) ⟨0, 1⟩ → Qeq (H (m + 3)) ⟨0, 1⟩ := by
    intro m hm1
    have hsum : Qeq (add (fderiv H (m + 2)) (fderiv H m)) ⟨0, 1⟩ :=
      Qeq_trans (fmul_den_pos onePlusSq_den_pos hfd (m + 2))
        (Qeq_symm (fmul_onePlusSq (fderiv H) hfd m))
        (Qeq_trans (fmul_den_pos Xident_den_pos hH (m + 2)) (hrel (m + 2))
          (Qeq_trans (hH (m + 1)) (fmul_Xident H hH (m + 1)) hm1))
    have hfdm : Qeq (fderiv H m) ⟨0, 1⟩ := Qmul_const_zero ((m : Int) + 1) (H (m + 1)) hm1
    have hfd2 : Qeq (fderiv H (m + 2)) ⟨0, 1⟩ :=
      Qadd_right_zero_cancel (fderiv H (m + 2)) (fderiv H m) (hfd (m + 2)) (hfd m) hsum hfdm
    exact fderiv_strip H (m + 2) hfd2
  -- triple-invariant induction
  have key : ∀ k, Qeq (H k) ⟨0, 1⟩ ∧ Qeq (H (k + 1)) ⟨0, 1⟩ ∧ Qeq (H (k + 2)) ⟨0, 1⟩ := by
    intro k
    induction k with
    | zero => exact ⟨hH0, hH1, hH2⟩
    | succ n ih => exact ⟨ih.2.1, ih.2.2, hrec n ih.2.1⟩
  intro k; exact (key k).1

/-- The formal Cauchy product is right-linear over negation: `a·(−b) ≈ −(a·b)`. -/
theorem fmul_neg_right (a b : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den) (k : Nat) :
    Qeq (fmul a (fun i => neg (b i)) k) (neg (fmul a b k)) := by
  refine Qeq_trans (fmul_den_pos (fun i => neg_den_pos (hb i)) ha k)
    (fmul_comm a (fun i => neg (b i)) ha (fun i => neg_den_pos (hb i)) k) ?_
  refine Qeq_trans (neg_den_pos (fmul_den_pos hb ha k)) (fmul_neg_left b a hb ha k) ?_
  exact Qneg_congr (fmul_comm b a hb ha k)

/-- `X² ≈ t²` (`fmul Xident Xident ≈ sq2`): both are `1` at degree `2`, else `0`. -/
theorem X_sq_eq_sq2 (k : Nat) : Qeq (fmul Xident Xident k) (sq2 k) := by
  by_cases h2 : k = 2
  · subst h2
    refine Qeq_trans (Qmul_den_pos (Xident_den_pos 1) (Xident_den_pos (2 - 1)))
      (Fsum_single (f := fun i => mul (Xident i) (Xident (2 - i)))
        (fun i => Qmul_den_pos (Xident_den_pos i) (Xident_den_pos _)) (j := 1) ?_ (k := 2) (by omega)) ?_
    · intro i hi1
      show Qeq (mul (Xident i) (Xident (2 - i))) ⟨0, 1⟩
      unfold Xident; rw [if_neg hi1]; simp only [Qeq, mul]; omega
    · show Qeq (mul (Xident 1) (Xident (2 - 1))) (sq2 2)
      unfold Xident sq2; rw [if_pos rfl, if_pos rfl]; decide
  · show Qeq (Fsum (fun i => mul (Xident i) (Xident (k - i))) k) (sq2 k)
    have hterm : ∀ i, i ≤ k → Qeq (mul (Xident i) (Xident (k - i))) ⟨0, 1⟩ := by
      intro i _
      by_cases hi1 : i = 1
      · subst hi1
        have hz : Xident (k - 1) = ⟨0, 1⟩ := by unfold Xident; rw [if_neg (by omega)]
        rw [hz]; simp only [Qeq, mul]; omega
      · unfold Xident; rw [if_neg hi1]; simp only [Qeq, mul]; omega
    have hzeros : Qeq (Fsum (fun i => mul (Xident i) (Xident (k - i))) k) ⟨0, 1⟩ :=
      Qeq_trans (Fsum_den_pos (fun _ => Nat.one_pos) k)
        (Fsum_congr_le (g := fun _ => (⟨0, 1⟩ : Q)) hterm) (Fsum_zeros k)
    have hsq2 : sq2 k = ⟨0, 1⟩ := by unfold sq2; rw [if_neg h2]
    rw [hsq2]; exact hzeros

/-- Formal derivative of a pointwise difference: `(S − T)′ = S′ − T′`. -/
theorem fderiv_sub (S T : Nat → Q) (k : Nat) :
    Qeq (fderiv (fun j => Qsub (S j) (T j)) k) (Qsub (fderiv S k) (fderiv T k)) :=
  Qmul_sub_distrib ⟨(k : Int) + 1, 1⟩ (S (k + 1)) (T (k + 1))

/-- Right distributivity of the formal Cauchy product over difference: `a·(b−c) ≈ a·b − a·c`
    (local, via `fmul_comm` + `fmul_sub_left`). -/
theorem fmul_subR (a b c : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den)
    (hc : ∀ i, 0 < (c i).den) (k : Nat) :
    Qeq (fmul a (fun i => Qsub (b i) (c i)) k) (Qsub (fmul a b k) (fmul a c k)) := by
  refine Qeq_trans (fmul_den_pos (fun i => Qsub_den_pos (hb i) (hc i)) ha k)
    (fmul_comm a (fun i => Qsub (b i) (c i)) ha (fun i => Qsub_den_pos (hb i) (hc i)) k) ?_
  refine Qeq_trans (Qsub_den_pos (fmul_den_pos hb ha k) (fmul_den_pos hc ha k))
    (fmul_sub_left hb hc ha k) ?_
  exact QsubCongr (fmul_comm b a hb ha k) (fmul_comm c a hc ha k)

/-- The Q-algebra rearrangement at the heart of the ODE relation: `a − ((a + b) − c) ≈ c − b`. -/
theorem Qalg1 (a b c : Q) : Qeq (Qsub a (add (add a b) (neg c))) (Qsub c b) := by
  simp only [Qeq, Qsub, add, neg, mul]; push_cast; ring_uor

/-- The identity series is its own antiderivative's derivative: `X′ = 1` (`fderiv Xident ≈ fone`). -/
theorem Xident_fderiv (k : Nat) : Qeq (fderiv Xident k) (fone k) := by
  by_cases h0 : k = 0
  · subst h0
    show Qeq (mul ⟨(0 : Int) + 1, 1⟩ (Xident 1)) (fone 0)
    unfold Xident fone; rw [if_pos rfl, if_pos rfl]; decide
  · show Qeq (mul ⟨(k : Int) + 1, 1⟩ (Xident (k + 1))) (fone k)
    unfold Xident fone; rw [if_neg (by omega : ¬ k + 1 = 1), if_neg h0]
    simp only [Qeq, mul]; push_cast; ring_uor

/-- **`(1+t²)·A′ = 1`**: `fmul onePlusSq geomAlt ≈ fone` — the formal statement that `geomAlt` is the
    reciprocal `1/(1+t²)`. From `geomAlt_recurrence` (degree `≥ 2`) and the boundary values. -/
theorem onePlusSq_geomAlt : ∀ k, Qeq (fmul onePlusSq geomAlt k) (fone k)
  | 0 => by
      have h := fmul_onePlusSq_zero geomAlt
      rw [geomAlt_zero] at h; exact h
  | 1 => by
      have h := fmul_onePlusSq_one geomAlt geomAlt_den_pos
      rw [geomAlt_one] at h; exact h
  | (m + 2) => by
      have h := fmul_onePlusSq geomAlt geomAlt_den_pos m
      exact Qeq_trans (add_den_pos (geomAlt_den_pos (m + 2)) (geomAlt_den_pos m)) h
        (geomAlt_recurrence m)

/-- **Absorption**: `(1+t²)·(P·A′) ≈ P` — since `(1+t²)·A′ = 1` (`onePlusSq_geomAlt`). The key
    simplification in the `G`-ODE derivation: `(1+t²)·(C·geomAlt) = C`, etc. -/
theorem absorb_onePlusSq_geomAlt (P : Nat → Q) (hP : ∀ i, 0 < (P i).den) (k : Nat) :
    Qeq (fmul onePlusSq (fmul P geomAlt) k) (P k) := by
  refine Qeq_trans (fmul_den_pos (fun i => fmul_den_pos hP geomAlt_den_pos i) onePlusSq_den_pos k)
    (fmul_comm onePlusSq (fmul P geomAlt) onePlusSq_den_pos
      (fun i => fmul_den_pos hP geomAlt_den_pos i) k) ?_
  refine Qeq_trans (fmul_den_pos hP (fun i => fmul_den_pos geomAlt_den_pos onePlusSq_den_pos i) k)
    (fmul_assoc P geomAlt onePlusSq hP geomAlt_den_pos onePlusSq_den_pos k) ?_
  refine Qeq_trans (fmul_den_pos hP (fun i => fone_den_pos i) k)
    (fmul_congr_right (b := fmul geomAlt onePlusSq) (b' := fone)
      (fun i => Qeq_trans (fmul_den_pos onePlusSq_den_pos geomAlt_den_pos i)
        (fmul_comm geomAlt onePlusSq geomAlt_den_pos onePlusSq_den_pos i) (onePlusSq_geomAlt i)) k) ?_
  exact fmul_one P hP k

-- ===========================================================================
-- The formal identity  sin∘arctan = t·(cos∘arctan)  via ode_unique on G = S − t·C.
-- ===========================================================================

/-- **Derivative of `t·(cos∘arctan)`**: `(X·C)′ ≈ C + (−((X·S)·A′))` — product rule `(X·C)′ = X′·C + X·C′`
    with `X′ = 1`, `C′ = −(S·A′)` (`cosComp_deriv`), and the associativity `X·(S·A′) = (X·S)·A′`. -/
theorem Gseq_fderivT (i : Nat) :
    Qeq (fderiv (fmul Xident (fcomp cosCoeff arctanCoeff)) i)
      (add (fcomp cosCoeff arctanCoeff i)
        (neg (fmul (fmul Xident (fcomp sinCoeff arctanCoeff)) geomAlt i))) := by
  have hS : ∀ j, 0 < (fcomp sinCoeff arctanCoeff j).den :=
    fun j => fcomp_den_pos sinCoeff_den_pos arctanCoeff_den_pos j
  have hC : ∀ j, 0 < (fcomp cosCoeff arctanCoeff j).den :=
    fun j => fcomp_den_pos cosCoeff_den_pos arctanCoeff_den_pos j
  have hSg : ∀ j, 0 < (fmul (fcomp sinCoeff arctanCoeff) geomAlt j).den :=
    fun j => fmul_den_pos hS geomAlt_den_pos j
  have part1 : Qeq (fmul (fderiv Xident) (fcomp cosCoeff arctanCoeff) i) (fcomp cosCoeff arctanCoeff i) :=
    Qeq_trans (fmul_den_pos (fun j => fone_den_pos j) hC i)
      (fmul_congr_left (fun j => Xident_fderiv j) i) (fmul_fone_left (fcomp cosCoeff arctanCoeff) hC i)
  have part2 : Qeq (fmul Xident (fderiv (fcomp cosCoeff arctanCoeff)) i)
      (neg (fmul (fmul Xident (fcomp sinCoeff arctanCoeff)) geomAlt i)) :=
    Qeq_trans (fmul_den_pos Xident_den_pos (fun j => neg_den_pos (hSg j)) i)
      (fmul_congr_right (fun j => cosComp_deriv j) i)
      (Qeq_trans (neg_den_pos (fmul_den_pos Xident_den_pos hSg i))
        (fmul_neg_right Xident (fmul (fcomp sinCoeff arctanCoeff) geomAlt) Xident_den_pos hSg i)
        (Qneg_congr (Qeq_symm
          (fmul_assoc Xident (fcomp sinCoeff arctanCoeff) geomAlt Xident_den_pos hS geomAlt_den_pos i))))
  exact Qeq_trans
    (add_den_pos (fmul_den_pos (fun j => fderiv_den_pos Xident_den_pos j) hC i)
      (fmul_den_pos Xident_den_pos (fun j => fderiv_den_pos hC j) i))
    (fderiv_fmul Xident (fcomp cosCoeff arctanCoeff) Xident_den_pos hC i)
    (Qadd_congr part1 part2)

/-- `G = sin∘arctan − t·(cos∘arctan)` — the difference whose vanishing is the formal identity. -/
def Gseq (j : Nat) : Q :=
  Qsub (fcomp sinCoeff arctanCoeff j) (fmul Xident (fcomp cosCoeff arctanCoeff) j)

theorem Gseq_den_pos (i : Nat) : 0 < (Gseq i).den :=
  Qsub_den_pos (fcomp_den_pos sinCoeff_den_pos arctanCoeff_den_pos i)
    (fmul_den_pos Xident_den_pos (fun j => fcomp_den_pos cosCoeff_den_pos arctanCoeff_den_pos j) i)

/-- `G(0) ≈ 0`: `sin∘arctan` and `t·(cos∘arctan)` both vanish at degree 0. -/
theorem Gseq_zero : Qeq (Gseq 0) ⟨0, 1⟩ := by
  have hA : Qeq (fcomp sinCoeff arctanCoeff 0) ⟨0, 1⟩ :=
    Qeq_trans (sinCoeff_den_pos 0) (fcomp_const sinCoeff arctanCoeff) (by decide)
  have hB : Qeq (fmul Xident (fcomp cosCoeff arctanCoeff) 0) ⟨0, 1⟩ :=
    fmul_Xident_zero (fcomp cosCoeff arctanCoeff)
  exact Qeq_trans (Qsub_den_pos (by decide) (by decide)) (QsubCongr hA hB) (by decide)

/-- **The `G`-ODE relation**: `(1+t²)·G′ ≈ t·G`. Both sides reduce to `X·S − t²·C`: the RHS by
    distributing `X` and `X² = t²`; the LHS by the chain-rule derivatives, the absorption
    `(1+t²)·(P·A′) = P`, and the algebra `a − ((a+b)−c) = c − b`. -/
theorem Gseq_ode (k : Nat) : Qeq (fmul onePlusSq (fderiv Gseq) k) (fmul Xident Gseq k) := by
  show Qeq (fmul onePlusSq
      (fderiv (fun j => Qsub (fcomp sinCoeff arctanCoeff j)
        (fmul Xident (fcomp cosCoeff arctanCoeff) j))) k)
    (fmul Xident (fun j => Qsub (fcomp sinCoeff arctanCoeff j)
      (fmul Xident (fcomp cosCoeff arctanCoeff) j)) k)
  have hS : ∀ j, 0 < (fcomp sinCoeff arctanCoeff j).den :=
    fun j => fcomp_den_pos sinCoeff_den_pos arctanCoeff_den_pos j
  have hC : ∀ j, 0 < (fcomp cosCoeff arctanCoeff j).den :=
    fun j => fcomp_den_pos cosCoeff_den_pos arctanCoeff_den_pos j
  have hT : ∀ j, 0 < (fmul Xident (fcomp cosCoeff arctanCoeff) j).den :=
    fun j => fmul_den_pos Xident_den_pos hC j
  have hXS : ∀ j, 0 < (fmul Xident (fcomp sinCoeff arctanCoeff) j).den :=
    fun j => fmul_den_pos Xident_den_pos hS j
  have hsq2C : ∀ j, 0 < (fmul sq2 (fcomp cosCoeff arctanCoeff) j).den :=
    fun j => fmul_den_pos sq2_den_pos hC j
  have hfdS : ∀ j, 0 < (fderiv (fcomp sinCoeff arctanCoeff) j).den := fun j => fderiv_den_pos hS j
  have hfdT : ∀ j, 0 < (fderiv (fmul Xident (fcomp cosCoeff arctanCoeff)) j).den :=
    fun j => fderiv_den_pos hT j
  have hCg : ∀ j, 0 < (fmul (fcomp cosCoeff arctanCoeff) geomAlt j).den :=
    fun j => fmul_den_pos hC geomAlt_den_pos j
  have hXSg : ∀ j, 0 < (fmul (fmul Xident (fcomp sinCoeff arctanCoeff)) geomAlt j).den :=
    fun j => fmul_den_pos hXS geomAlt_den_pos j
  -- abbreviation: the common middle form M = X·S − t²·C
  -- RHS : fmul Xident Gseq k ≈ M
  have hRHS : Qeq (fmul Xident (fun j => Qsub (fcomp sinCoeff arctanCoeff j)
        (fmul Xident (fcomp cosCoeff arctanCoeff) j)) k)
      (Qsub (fmul Xident (fcomp sinCoeff arctanCoeff) k) (fmul sq2 (fcomp cosCoeff arctanCoeff) k)) := by
    have hTeq : Qeq (fmul Xident (fmul Xident (fcomp cosCoeff arctanCoeff)) k)
        (fmul sq2 (fcomp cosCoeff arctanCoeff) k) :=
      Qeq_trans (fmul_den_pos (fun j => fmul_den_pos Xident_den_pos Xident_den_pos j) hC k)
        (Qeq_symm (fmul_assoc Xident Xident (fcomp cosCoeff arctanCoeff) Xident_den_pos Xident_den_pos hC k))
        (fmul_congr_left (fun j => X_sq_eq_sq2 j) k)
    refine Qeq_trans (Qsub_den_pos (hXS k) (fmul_den_pos Xident_den_pos hT k))
      (fmul_subR Xident (fcomp sinCoeff arctanCoeff) (fmul Xident (fcomp cosCoeff arctanCoeff))
        Xident_den_pos hS hT k) ?_
    exact QsubCongr (Qeq_refl _) hTeq
  -- LHS : fmul onePlusSq (fderiv Gseq) k ≈ M
  have hLHS : Qeq (fmul onePlusSq
        (fderiv (fun j => Qsub (fcomp sinCoeff arctanCoeff j)
          (fmul Xident (fcomp cosCoeff arctanCoeff) j))) k)
      (Qsub (fmul Xident (fcomp sinCoeff arctanCoeff) k) (fmul sq2 (fcomp cosCoeff arctanCoeff) k)) := by
    -- fderiv Gseq ≈ Qsub (fderiv S)(fderiv T)
    have hLd : Qeq (fmul onePlusSq
          (fderiv (fun j => Qsub (fcomp sinCoeff arctanCoeff j)
            (fmul Xident (fcomp cosCoeff arctanCoeff) j))) k)
        (Qsub (fmul onePlusSq (fderiv (fcomp sinCoeff arctanCoeff)) k)
          (fmul onePlusSq (fderiv (fmul Xident (fcomp cosCoeff arctanCoeff))) k)) := by
      refine Qeq_trans (fmul_den_pos onePlusSq_den_pos
          (fun j => Qsub_den_pos (hfdS j) (hfdT j)) k)
        (fmul_congr_right
          (b := fderiv (fun j => Qsub (fcomp sinCoeff arctanCoeff j)
            (fmul Xident (fcomp cosCoeff arctanCoeff) j)))
          (b' := fun j => Qsub (fderiv (fcomp sinCoeff arctanCoeff) j)
            (fderiv (fmul Xident (fcomp cosCoeff arctanCoeff)) j))
          (fun j => fderiv_sub (fcomp sinCoeff arctanCoeff)
            (fmul Xident (fcomp cosCoeff arctanCoeff)) j) k) ?_
      exact fmul_subR onePlusSq (fderiv (fcomp sinCoeff arctanCoeff))
        (fderiv (fmul Xident (fcomp cosCoeff arctanCoeff))) onePlusSq_den_pos hfdS hfdT k
    -- term1 : (1+t²)·S′ ≈ C
    have hT1 : Qeq (fmul onePlusSq (fderiv (fcomp sinCoeff arctanCoeff)) k) (fcomp cosCoeff arctanCoeff k) :=
      Qeq_trans (fmul_den_pos onePlusSq_den_pos hCg k)
        (fmul_congr_right (fun j => sinComp_deriv j) k)
        (absorb_onePlusSq_geomAlt (fcomp cosCoeff arctanCoeff) hC k)
    -- term2 : (1+t²)·T′ ≈ (C + t²·C) − X·S
    have hT2 : Qeq (fmul onePlusSq (fderiv (fmul Xident (fcomp cosCoeff arctanCoeff))) k)
        (add (add (fcomp cosCoeff arctanCoeff k) (fmul sq2 (fcomp cosCoeff arctanCoeff) k))
          (neg (fmul Xident (fcomp sinCoeff arctanCoeff) k))) := by
      -- (1+t²)·T′ ≈ (1+t²)·(C + (−((X·S)·A′)))
      refine Qeq_trans (fmul_den_pos onePlusSq_den_pos
          (fun j => add_den_pos (hC j) (neg_den_pos (hXSg j))) k)
        (fmul_congr_right (fun j => Gseq_fderivT j) k) ?_
      -- distribute over add
      refine Qeq_trans (add_den_pos (fmul_den_pos onePlusSq_den_pos hC k)
          (fmul_den_pos onePlusSq_den_pos (fun j => neg_den_pos (hXSg j)) k))
        (fmul_add_right onePlusSq_den_pos hC (fun j => neg_den_pos (hXSg j)) k) ?_
      refine Qadd_congr ?_ ?_
      · -- (1+t²)·C ≈ C + t²·C
        refine Qeq_trans (add_den_pos (fmul_den_pos (fun j => fone_den_pos j) hC k)
            (fmul_den_pos sq2_den_pos hC k))
          (Qeq_trans (fmul_den_pos (fun j => add_den_pos (fone_den_pos j) (sq2_den_pos j)) hC k)
            (fmul_congr_left (fun j => onePlusSq_decomp j) k)
            (fmul_add_left (fun j => fone_den_pos j) (fun j => sq2_den_pos j) hC k)) ?_
        exact Qadd_congr (fmul_fone_left (fcomp cosCoeff arctanCoeff) hC k) (Qeq_refl _)
      · -- (1+t²)·(−((X·S)·A′)) ≈ −(X·S)
        refine Qeq_trans (neg_den_pos (fmul_den_pos onePlusSq_den_pos
            (fun j => fmul_den_pos hXS geomAlt_den_pos j) k))
          (fmul_neg_right onePlusSq (fmul (fmul Xident (fcomp sinCoeff arctanCoeff)) geomAlt)
            onePlusSq_den_pos hXSg k) ?_
        exact Qneg_congr (absorb_onePlusSq_geomAlt (fmul Xident (fcomp sinCoeff arctanCoeff)) hXS k)
    -- combine: Qsub C ((C+t²C) − X·S) ≈ X·S − t²·C  via Qalg1
    refine Qeq_trans (Qsub_den_pos (hC k)
        (add_den_pos (add_den_pos (hC k) (hsq2C k)) (neg_den_pos (hXS k))))
      (Qeq_trans (Qsub_den_pos (fmul_den_pos onePlusSq_den_pos hfdS k)
          (fmul_den_pos onePlusSq_den_pos hfdT k))
        hLd (QsubCongr hT1 hT2)) ?_
    exact Qalg1 (fcomp cosCoeff arctanCoeff k) (fmul sq2 (fcomp cosCoeff arctanCoeff) k)
      (fmul Xident (fcomp sinCoeff arctanCoeff) k)
  exact Qeq_trans (Qsub_den_pos (hXS k) (hsq2C k)) hLHS (Qeq_symm hRHS)

/-- **★ The formal identity `sin∘arctan = t·(cos∘arctan)`**: `fcomp sinCoeff arctanCoeff ≈
    fmul Xident (fcomp cosCoeff arctanCoeff)`. The formal-power-series shadow of `tan(arctan t) = t`,
    obtained by `ode_unique` on `G = S − t·C` (which satisfies `(1+t²)G′ = t·G`, `G(0)=0`). -/
theorem sin_arctan_eq (k : Nat) :
    Qeq (fcomp sinCoeff arctanCoeff k) (fmul Xident (fcomp cosCoeff arctanCoeff) k) :=
  Qeq_of_Qsub_zero (ode_unique Gseq Gseq_den_pos Gseq_zero Gseq_ode k)

-- ===========================================================================
-- Value-bridge entry points: the formal identity at the `peval` (evaluation) level,
-- and the composition swaps `peval (sin∘arctan) = Σₘ sinₘ·peval(arctanᵐ)`. The remaining
-- step toward `Rsin(arctan t) = t·Rcos(arctan t)` is the composition-series convergence
-- (`peval (fpow arctanCoeff m) t M → (arctan-value)ᵐ`, summed against `sinCoeff`), for which
-- ExpLog provides the general infrastructure: `peval_fcomp_swap`, `peval_fpow_abs_bound`,
-- `peval_mul`/`peval_fpow_succ`, and the `per_m_step` error-recursion pattern.
-- ===========================================================================

/-- **Value-level form of the formal identity**: the composed series `sin∘arctan` and
    `t·(cos∘arctan)`, evaluated at any rational `t` and truncated at `M`, agree (`peval_congr` on
    `sin_arctan_eq`). The entry point of the formal-PS → value bridge. -/
theorem peval_sin_arctan_eq (t : Q) (M : Nat) :
    Qeq (peval (fcomp sinCoeff arctanCoeff) t M)
      (peval (fmul Xident (fcomp cosCoeff arctanCoeff)) t M) :=
  peval_congr (fun k => sin_arctan_eq k) t M

/-- **Composition swap for `sin∘arctan`**: `peval(sin∘arctan, t, M) = Σ_{m≤M} sinₘ·peval(arctanᵐ, t, M)`
    — the finite rearrangement (`peval_fcomp_swap`) expressing the composed series as the `sin` series
    evaluated at the `arctan` powers. -/
theorem peval_sinComp_swap (t : Q) (htd : 0 < t.den) (M : Nat) :
    Qeq (peval (fcomp sinCoeff arctanCoeff) t M)
      (Fsum (fun m => mul (sinCoeff m) (peval (fpow arctanCoeff m) t M)) M) :=
  peval_fcomp_swap sinCoeff arctanCoeff sinCoeff_den_pos arctanCoeff_den_pos arctanCoeff_zero t htd M

/-- **Composition swap for `cos∘arctan`**: `peval(cos∘arctan, t, M) = Σ_{m≤M} cosₘ·peval(arctanᵐ, t, M)`. -/
theorem peval_cosComp_swap (t : Q) (htd : 0 < t.den) (M : Nat) :
    Qeq (peval (fcomp cosCoeff arctanCoeff) t M)
      (Fsum (fun m => mul (cosCoeff m) (peval (fpow arctanCoeff m) t M)) M) :=
  peval_fcomp_swap cosCoeff arctanCoeff cosCoeff_den_pos arctanCoeff_den_pos arctanCoeff_zero t htd M

/-- `|(−1)ⁿ| = 1`: the alternating sign series has unit absolute value at every power. -/
theorem qpow_neg_one_abs (n : Nat) : Qabs (qpow (⟨-1, 1⟩ : Q) n) = ⟨1, 1⟩ := by
  induction n with
  | zero => rfl
  | succ m ih => rw [qpow_succ, Qabs_mul, ih]; rfl

-- ===========================================================================
-- General per-m convergence: |peval(bᵐ,w,M) − (peval b w M)ᵐ| ≤ Σ |cornerⱼ|.
-- (Compares the truncated power-of-series to the power of the truncated series — the
-- partial-sum comparison that the NON-rational arctan series needs, vs the doubling's
-- rational-limit `uval`. The recursion eₘ₊₁ = q·eₘ − cornerₘ has no q−u term.)
-- ===========================================================================

/-- The general truncation corner of `peval (fpow b (m+1))` (the `peval_fpow_succ` defect; `kcorner`
    with `b` in place of `kdbl`). -/
def gcornerB (b : Nat → Q) (w : Q) (m M : Nat) : Q :=
  Fsum (fun i => Qsub
    (Fsum (fun j => mul (mul (b i) (qpow w i)) (mul (fpow b m j) (qpow w j))) M)
    (Fsum (fun j => mul (mul (b i) (qpow w i)) (mul (fpow b m j) (qpow w j))) (M - i))) M

theorem gcornerB_den (b : Nat → Q) (hb : ∀ i, 0 < (b i).den) (w : Q) (hwd : 0 < w.den) (m M : Nat) :
    0 < (gcornerB b w m M).den :=
  Fsum_den_pos (fun i => Qsub_den_pos
    (Fsum_den_pos (fun j => Qmul_den_pos (Qmul_den_pos (hb i) (qpow_den_pos hwd i))
      (Qmul_den_pos (fpow_den_pos hb m j) (qpow_den_pos hwd j))) M)
    (Fsum_den_pos (fun j => Qmul_den_pos (Qmul_den_pos (hb i) (qpow_den_pos hwd i))
      (Qmul_den_pos (fpow_den_pos hb m j) (qpow_den_pos hwd j))) (M - i))) M

/-- The error-recursion algebra: `(q·p − c) − q·r = q·(p − r) − c`. -/
theorem e_rec_alg2 (q p r c : Q) :
    Qeq (Qsub (Qsub (mul q p) c) (mul q r)) (Qsub (mul q (Qsub p r)) c) := by
  simp only [Qeq, Qsub, add, neg, mul]; push_cast; ring_uor

/-- **Per-`m` error step**: `|eₘ₊₁| ≤ |q|·|eₘ| + |cornerₘ|`, where `eₖ = peval(bᵏ,w,M) − qᵏ`,
    `q = peval b w M`. From `peval_fpow_succ` (= `q·peval(bᵐ) − corner`) and `e_rec_alg2`. -/
theorem gen_per_m_step (b : Nat → Q) (hb : ∀ i, 0 < (b i).den) (w : Q) (hwd : 0 < w.den) (m M : Nat) :
    Qle (Qabs (Qsub (peval (fpow b (m + 1)) w M) (qpow (peval b w M) (m + 1))))
      (add (mul (Qabs (peval b w M))
              (Qabs (Qsub (peval (fpow b m) w M) (qpow (peval b w M) m))))
        (Qabs (gcornerB b w m M))) := by
  have hq : 0 < (peval b w M).den := peval_den_pos hb hwd M
  have hpm : 0 < (peval (fpow b m) w M).den := peval_den_pos (fpow_den_pos hb m) hwd M
  have hqm : 0 < (qpow (peval b w M) m).den := qpow_den_pos hq m
  have hem : 0 < (Qsub (peval (fpow b m) w M) (qpow (peval b w M) m)).den := Qsub_den_pos hpm hqm
  have hcor : 0 < (gcornerB b w m M).den := gcornerB_den b hb w hwd m M
  have hid : Qeq (Qsub (peval (fpow b (m + 1)) w M) (qpow (peval b w M) (m + 1)))
      (Qsub (mul (peval b w M) (Qsub (peval (fpow b m) w M) (qpow (peval b w M) m)))
        (gcornerB b w m M)) := by
    rw [qpow_succ]
    exact Qeq_trans
      (Qsub_den_pos (Qsub_den_pos (Qmul_den_pos hq hpm) hcor) (Qmul_den_pos hq hqm))
      (Qsub_congr (peval_fpow_succ b hb w hwd m M) (Qeq_refl _))
      (e_rec_alg2 (peval b w M) (peval (fpow b m) w M) (qpow (peval b w M) m) (gcornerB b w m M))
  refine Qle_trans (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos hq hem) hcor))
    (Qeq_le (Qabs_Qeq hid)) ?_
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qmul_den_pos hq hem)) (Qabs_den_pos hcor))
    (Qabs_sub_le_add _ _) ?_
  exact Qadd_le_add (Qeq_le (by rw [Qabs_mul]; exact Qeq_refl _ :
    Qeq (Qabs (mul (peval b w M) (Qsub (peval (fpow b m) w M) (qpow (peval b w M) m))))
      (mul (Qabs (peval b w M)) (Qabs (Qsub (peval (fpow b m) w M) (qpow (peval b w M) m))))))
    (Qle_refl _)

/-- **Per-`m` error bound**: `|peval(bᵐ⁺¹,w,M) − qᵐ⁺¹| ≤ Σ_{j≤m} |cornerⱼ|` for `q = peval b w M` with
    `|q| ≤ 1`. By induction via `gen_per_m_step` (the `|q|·|eₘ| ≤ |eₘ|` contraction). -/
theorem gen_per_m_bound (b : Nat → Q) (hb : ∀ i, 0 < (b i).den) (w : Q) (hwd : 0 < w.den) (M : Nat)
    (hq1 : Qle (Qabs (peval b w M)) ⟨1, 1⟩) (m : Nat) :
    Qle (Qabs (Qsub (peval (fpow b (m + 1)) w M) (qpow (peval b w M) (m + 1))))
      (Fsum (fun j => Qabs (gcornerB b w j M)) m) := by
  have hq : 0 < (peval b w M).den := peval_den_pos hb hwd M
  have hpd : ∀ k, 0 < (peval (fpow b k) w M).den :=
    fun k => peval_den_pos (fpow_den_pos hb k) hwd M
  have hqm : ∀ k, 0 < (qpow (peval b w M) k).den := fun k => qpow_den_pos hq k
  have bound1 : ∀ {e : Q}, 0 < e.den → Qle (mul (Qabs (peval b w M)) (Qabs e)) (Qabs e) :=
    fun {e} he => Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos he))
      (Qmul_le_mul_right (Qabs_num_nonneg _) hq1) (Qeq_le (Qone_mul _))
  induction m with
  | zero =>
      have hz : Qeq (Qsub (peval (fpow b 0) w M) (qpow (peval b w M) 0)) ⟨0, 1⟩ := by
        show Qeq (Qsub (peval fone w M) ⟨1, 1⟩) ⟨0, 1⟩
        refine Qeq_trans (Qsub_den_pos Nat.one_pos Nat.one_pos)
          (Qsub_congr (peval_fone w hwd M) (Qeq_refl _)) ?_
        simp [Qeq, Qsub, add, neg]
      have he0 : Qle (Qabs (Qsub (peval (fpow b 0) w M) (qpow (peval b w M) 0))) ⟨0, 1⟩ :=
        Qeq_le (Qeq_trans Nat.one_pos (Qabs_Qeq hz) (by decide : Qeq (Qabs (⟨0, 1⟩ : Q)) ⟨0, 1⟩))
      show Qle (Qabs (Qsub (peval (fpow b 1) w M) (qpow (peval b w M) 1)))
        (Qabs (gcornerB b w 0 M))
      refine Qle_trans (add_den_pos (Qmul_den_pos (Qabs_den_pos hq)
          (Qabs_den_pos (Qsub_den_pos (hpd 0) (hqm 0)))) (Qabs_den_pos (gcornerB_den b hb w hwd 0 M)))
        (gen_per_m_step b hb w hwd 0 M) ?_
      refine Qle_trans (add_den_pos Nat.one_pos (Qabs_den_pos (gcornerB_den b hb w hwd 0 M)))
        (Qadd_le_add (Qle_trans (Qabs_den_pos (Qsub_den_pos (hpd 0) (hqm 0)))
          (bound1 (Qsub_den_pos (hpd 0) (hqm 0))) he0) (Qle_refl _)) ?_
      exact Qeq_le (Qzero_add _)
  | succ m ih =>
      refine Qle_trans (add_den_pos (Qmul_den_pos (Qabs_den_pos hq)
          (Qabs_den_pos (Qsub_den_pos (hpd (m + 1)) (hqm (m + 1)))))
          (Qabs_den_pos (gcornerB_den b hb w hwd (m + 1) M)))
        (gen_per_m_step b hb w hwd (m + 1) M) ?_
      refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (hpd (m + 1)) (hqm (m + 1))))
          (Qabs_den_pos (gcornerB_den b hb w hwd (m + 1) M)))
        (Qadd_le_add (bound1 (Qsub_den_pos (hpd (m + 1)) (hqm (m + 1)))) (Qle_refl _)) ?_
      exact Qadd_le_add ih (Qle_refl _)

-- ===========================================================================
-- Bridge to the existing arctan real: peval arctanCoeff = arctanSum (hence RarctanR).
-- ===========================================================================

/-- The odd-degree term of `peval arctanCoeff` is the `arctan` series term: `arctanCoeff_{2n+1}·t^{2n+1}
    ≈ arctanTerm t n` (both `(−1)ⁿ·t^{2n+1}/(2n+1)`). -/
theorem arctanCoeff_term_odd (t : Q) (n : Nat) :
    Qeq (mul (arctanCoeff (2 * n + 1)) (qpow t (2 * n + 1))) (arctanTerm t n) := by
  unfold arctanCoeff arctanTerm artTerm
  rw [if_pos (by omega : (2 * n + 1) % 2 = 1), show (2 * n + 1) / 2 = n from by omega]
  simp only [Qeq, mul]; push_cast; ring_uor

/-- The even-degree term of `peval arctanCoeff` vanishes: `arctanCoeff_{2n+2}·t^{2n+2} ≈ 0`. -/
theorem arctanCoeff_term_even (t : Q) (n : Nat) :
    Qeq (mul (arctanCoeff (2 * n + 2)) (qpow t (2 * n + 2))) ⟨0, 1⟩ := by
  unfold arctanCoeff
  rw [if_neg (by omega : ¬ (2 * n + 2) % 2 = 1)]
  show Qeq (mul (⟨0, 1⟩ : Q) (qpow t (2 * n + 2))) ⟨0, 1⟩
  simp only [Qeq, mul]; omega

/-- **Bridge to `arctanSum`**: `peval arctanCoeff t (2N+1) ≈ arctanSum t N` — the degree-indexed
    power-series evaluation of the `arctan` coefficients IS the `n`-indexed `arctan` partial sum (even
    terms vanish, odd terms `= arctanTerm`). Connects the formal-PS machinery to `RarctanR`. -/
theorem peval_arctanCoeff_eq_arctanSum (t : Q) (htd : 0 < t.den) (N : Nat) :
    Qeq (peval arctanCoeff t (2 * N + 1)) (arctanSum t N) := by
  have hg : ∀ k, 0 < (mul (arctanCoeff k) (qpow t k)).den :=
    fun k => Qmul_den_pos (arctanCoeff_den_pos k) (qpow_den_pos htd k)
  induction N with
  | zero =>
    show Qeq (add (mul (arctanCoeff 0) (qpow t 0)) (mul (arctanCoeff 1) (qpow t 1))) (arctanTerm t 0)
    have he : Qeq (mul (arctanCoeff 0) (qpow t 0)) ⟨0, 1⟩ := by
      have h0 : arctanCoeff 0 = ⟨0, 1⟩ := by unfold arctanCoeff; rw [if_neg (by decide)]
      rw [h0]; simp only [Qeq, mul]; omega
    exact Qeq_trans (add_den_pos Nat.one_pos (arctanTerm_den_pos htd 0))
      (Qadd_congr he (arctanCoeff_term_odd t 0)) (Qzero_add (arctanTerm t 0))
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 from by omega]
    show Qeq (add (add (peval arctanCoeff t (2 * n + 1)) (mul (arctanCoeff (2 * n + 2)) (qpow t (2 * n + 2))))
        (mul (arctanCoeff (2 * n + 3)) (qpow t (2 * n + 3))))
      (add (arctanSum t n) (arctanTerm t (n + 1)))
    have ho : Qeq (mul (arctanCoeff (2 * n + 3)) (qpow t (2 * n + 3))) (arctanTerm t (n + 1)) := by
      have h := arctanCoeff_term_odd t (n + 1)
      rwa [show 2 * (n + 1) + 1 = 2 * n + 3 from by omega] at h
    refine Qeq_trans (add_den_pos (add_den_pos (arctanSum_den_pos htd n) Nat.one_pos)
        (arctanTerm_den_pos htd (n + 1)))
      (Qadd_congr (Qadd_congr ih (arctanCoeff_term_even t n)) ho) ?_
    exact Qadd_congr (Qadd_zero_right (arctanSum t n)) (Qeq_refl _)

/-- `|sinCoeffₖ| ≤ 1` for every `k` (`(−1)^{k/2}/k!` at odd `k`, else `0`; `k! ≥ 1`). The outer-series
    coefficient bound for the `DN`-sum of the `sin∘arctan` composition bridge. -/
theorem sinCoeff_abs_le_one (k : Nat) : Qle (Qabs (sinCoeff k)) ⟨1, 1⟩ := by
  unfold sinCoeff
  by_cases h : k % 2 = 1
  · rw [if_pos h, Qabs_mul, qpow_neg_one_abs]
    have hk1 : 1 ≤ fct k := fct_pos k
    simp only [Qabs, Qle, mul]; push_cast; omega
  · rw [if_neg h]; simp only [Qabs, Qle]; push_cast

/-- `|cosCoeffₖ| ≤ 1` for every `k`. -/
theorem cosCoeff_abs_le_one (k : Nat) : Qle (Qabs (cosCoeff k)) ⟨1, 1⟩ := by
  unfold cosCoeff
  by_cases h : k % 2 = 0
  · rw [if_pos h, Qabs_mul, qpow_neg_one_abs]
    have hk1 : 1 ≤ fct k := fct_pos k
    simp only [Qabs, Qle, mul]; push_cast; omega
  · rw [if_neg h]; simp only [Qabs, Qle]; push_cast

/-- **Absolute bound on the arctan partial sum**: `|arctanSum t N| ≤ geoSum ρ N` for `|t| ≤ ρ`
    (per-term `arctanTerm_abs_le` + triangle). With `geoSum ρ N ≤ 1` (small `ρ`) this gives the
    `|peval arctanCoeff t M| ≤ 1` hypothesis that `gen_per_m_bound` needs. -/
theorem arctanSum_abs_le {t ρ : Q} (htd : 0 < t.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (htρ : Qle (Qabs t) ρ) : ∀ N, Qle (Qabs (arctanSum t N)) (geoSum ρ N)
  | 0 => arctanTerm_abs_le htd hρ0 hρd htρ 0
  | (N + 1) => by
      show Qle (Qabs (add (arctanSum t N) (arctanTerm t (N + 1)))) (add (geoSum ρ N) (geoTerm ρ (N + 1)))
      refine Qle_trans (add_den_pos (Qabs_den_pos (arctanSum_den_pos htd N))
          (Qabs_den_pos (arctanTerm_den_pos htd (N + 1)))) (Qabs_add_le _ _) ?_
      exact Qadd_le_add (arctanSum_abs_le htd hρ0 hρd htρ N) (arctanTerm_abs_le htd hρ0 hρd htρ (N + 1))

-- ===========================================================================
-- The DN-sum: composition error = Σₘ sinₘ·(per-m error), bounded by Σₘ Σⱼ |cornerⱼ|.
-- ===========================================================================

/-- **`DN` identity**: `peval(sin∘arctan,t,M) − peval(sin, q, M) = Σ_{m≤M} sinₘ·(peval(arctanᵐ,t,M) − qᵐ)`
    where `q = peval arctanCoeff t M`. (`peval_fcomp_swap` + `Fsum_sub` + `Qmul_sub_left_loc`.) -/
theorem DN_sin_eq (t : Q) (htd : 0 < t.den) (M : Nat) :
    Qeq (Qsub (peval (fcomp sinCoeff arctanCoeff) t M)
          (peval sinCoeff (peval arctanCoeff t M) M))
      (Fsum (fun m => mul (sinCoeff m)
        (Qsub (peval (fpow arctanCoeff m) t M) (qpow (peval arctanCoeff t M) m))) M) := by
  have hq : 0 < (peval arctanCoeff t M).den := peval_den_pos arctanCoeff_den_pos htd M
  have hF : ∀ m, 0 < (mul (sinCoeff m) (peval (fpow arctanCoeff m) t M)).den :=
    fun m => Qmul_den_pos (sinCoeff_den_pos m) (peval_den_pos (fpow_den_pos arctanCoeff_den_pos m) htd M)
  have hG : ∀ m, 0 < (mul (sinCoeff m) (qpow (peval arctanCoeff t M) m)).den :=
    fun m => Qmul_den_pos (sinCoeff_den_pos m) (qpow_den_pos hq m)
  refine Qeq_trans (Qsub_den_pos (Fsum_den_pos hF M) (peval_den_pos sinCoeff_den_pos hq M))
    (QsubCongr (peval_fcomp_swap sinCoeff arctanCoeff sinCoeff_den_pos arctanCoeff_den_pos
      arctanCoeff_zero t htd M) (Qeq_refl _)) ?_
  refine Qeq_trans (Fsum_den_pos (fun m => Qsub_den_pos (hF m) (hG m)) M)
    (Qeq_symm (Fsum_sub hF hG M)) ?_
  exact Fsum_congr (fun m => Qeq_symm (Qmul_sub_left_loc (sinCoeff m)
    (peval (fpow arctanCoeff m) t M) (qpow (peval arctanCoeff t M) m))) M

/-- **Per-`m` error ≤ corner sum**: `|peval(arctanᵐ,t,M) − qᵐ| ≤ Σ_{j≤M}|cornerⱼ|` for `m ≤ M`
    (`q = peval arctanCoeff t M`, `|q| ≤ 1`). `m = 0` is `0`; `m = k+1` is `gen_per_m_bound` extended
    by `Fsum_mono_len`. -/
theorem e_le_T_arctan (t : Q) (htd : 0 < t.den) (M : Nat)
    (hq1 : Qle (Qabs (peval arctanCoeff t M)) ⟨1, 1⟩) (m : Nat) (hm : m ≤ M) :
    Qle (Qabs (Qsub (peval (fpow arctanCoeff m) t M) (qpow (peval arctanCoeff t M) m)))
      (Fsum (fun j => Qabs (gcornerB arctanCoeff t j M)) M) := by
  have hgd : ∀ j, 0 < (Qabs (gcornerB arctanCoeff t j M)).den :=
    fun j => Qabs_den_pos (gcornerB_den arctanCoeff arctanCoeff_den_pos t htd j M)
  have hg0 : ∀ j, 0 ≤ (Qabs (gcornerB arctanCoeff t j M)).num := fun j => Qabs_num_nonneg _
  cases m with
  | zero =>
    have hsub : Qeq (Qsub (peval (fpow arctanCoeff 0) t M) (qpow (peval arctanCoeff t M) 0)) ⟨0, 1⟩ := by
      show Qeq (Qsub (peval fone t M) ⟨1, 1⟩) ⟨0, 1⟩
      refine Qeq_trans (Qsub_den_pos Nat.one_pos Nat.one_pos)
        (Qsub_congr (peval_fone t htd M) (Qeq_refl _)) (by decide)
    have he0 : Qeq (Qabs (Qsub (peval (fpow arctanCoeff 0) t M) (qpow (peval arctanCoeff t M) 0))) ⟨0, 1⟩ :=
      Qeq_trans (by decide) (Qabs_Qeq hsub) (by decide)
    exact Qle_trans Nat.one_pos (Qeq_le he0) (Qzero_le_loc (Fsum_num_nonneg hg0 M))
  | succ k =>
    refine Qle_trans (Fsum_den_pos hgd k)
      (gen_per_m_bound arctanCoeff arctanCoeff_den_pos t htd M hq1 k) ?_
    exact Fsum_mono_len hg0 hgd (by omega : k ≤ M)

/-- **The `DN` bound**: `|peval(sin∘arctan,t,M) − peval(sin,q,M)| ≤ Σ_{m≤M} Σ_{j≤M}|cornerⱼ|`
    (`= (M+1)·(corner sum)`), `q = peval arctanCoeff t M`. The `sin∘arctan` value convergence is now
    reduced to the corner decay `Σⱼ|gcornerB arctanCoeff t j M| → 0`. -/
theorem DN_sin_abs_le (t : Q) (htd : 0 < t.den) (M : Nat)
    (hq1 : Qle (Qabs (peval arctanCoeff t M)) ⟨1, 1⟩) :
    Qle (Qabs (Qsub (peval (fcomp sinCoeff arctanCoeff) t M)
          (peval sinCoeff (peval arctanCoeff t M) M)))
      (Fsum (fun _ => Fsum (fun j => Qabs (gcornerB arctanCoeff t j M)) M) M) := by
  have herr : ∀ m, 0 < (Qsub (peval (fpow arctanCoeff m) t M) (qpow (peval arctanCoeff t M) m)).den :=
    fun m => Qsub_den_pos (peval_den_pos (fpow_den_pos arctanCoeff_den_pos m) htd M)
      (qpow_den_pos (peval_den_pos arctanCoeff_den_pos htd M) m)
  have hSE : ∀ m, 0 < (mul (sinCoeff m)
      (Qsub (peval (fpow arctanCoeff m) t M) (qpow (peval arctanCoeff t M) m))).den :=
    fun m => Qmul_den_pos (sinCoeff_den_pos m) (herr m)
  refine Qle_trans (Qabs_den_pos (Fsum_den_pos hSE M)) (Qeq_le (Qabs_Qeq (DN_sin_eq t htd M))) ?_
  refine Qle_trans (Fsum_den_pos (fun m => Qabs_den_pos (hSE m)) M) (Fsum_abs_le hSE M) ?_
  refine Fsum_le_congr (fun m hm => ?_)
  refine Qle_trans (Qmul_den_pos (Qabs_den_pos (sinCoeff_den_pos m)) (Qabs_den_pos (herr m)))
    (Qeq_le (by rw [Qabs_mul]; exact Qeq_refl _ :
      Qeq (Qabs (mul (sinCoeff m) (Qsub (peval (fpow arctanCoeff m) t M) (qpow (peval arctanCoeff t M) m))))
        (mul (Qabs (sinCoeff m)) (Qabs (Qsub (peval (fpow arctanCoeff m) t M) (qpow (peval arctanCoeff t M) m)))))) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (herr m)))
    (Qmul_le_mul_right (Qabs_num_nonneg _) (sinCoeff_abs_le_one m)) ?_
  exact Qle_trans (Qabs_den_pos (herr m)) (Qeq_le (Qone_mul _)) (e_le_T_arctan t htd M hq1 m hm)

/-- **Geometric domination of the arctan coefficients**: `|arctanCoeffₖ| ≤ 1` for every `k` (the
    coefficient is `(−1)^{k/2}/k` at odd `k`, else `0`). The convergence input for the composition
    value bridge: combined with `peval_mono` it bounds `peval (fabs arctanCoeff) ρ M` by a geometric
    sum, giving the absolute convergence of the `arctan` powers inside the radius. -/
theorem arctanCoeff_fabs_le_one (k : Nat) : Qle (fabs arctanCoeff k) ⟨1, 1⟩ := by
  show Qle (Qabs (arctanCoeff k)) ⟨1, 1⟩
  unfold arctanCoeff
  by_cases h : k % 2 = 1
  · rw [if_pos h, Qabs_mul, qpow_neg_one_abs]
    have hk1 : 1 ≤ k := by omega
    simp only [Qabs, Qle, mul]; push_cast; omega
  · rw [if_neg h]; simp only [Qabs, Qle]; push_cast

-- ===========================================================================
-- Corner decay for arctanCoeff (the sin∘arctan value-bridge wall): mirrors the
-- kdbl machinery with arctan constants (2ᵐ not 4ᵐ, since |arctanCoeffₖ| ≤ 1).
-- ===========================================================================

/-- **Per-coefficient power bound**: `(|arctanCoeff|ᵐ)ₖ ≤ 2ᵐ·2ᵏ` (the `arctan` analog of
    `fpow_fabs_kdbl_bound`; cleaner since `|arctanCoeffₖ| ≤ 1`, not `2`). -/
theorem fpow_fabs_arctan_bound (m k : Nat) :
    Qle (fpow (fabs arctanCoeff) m k) ⟨(2 : Int) ^ m * 2 ^ k, 1⟩ := by
  induction m generalizing k with
  | zero =>
      show Qle (fone k) ⟨(2 : Int) ^ 0 * 2 ^ k, 1⟩
      by_cases h : k = 0
      · subst h; rw [show fone 0 = (⟨1, 1⟩ : Q) from by simp [fone]]; decide
      · rw [show fone k = (⟨0, 1⟩ : Q) from by simp [fone, h]]
        show (0 : Int) * 1 ≤ ((2 : Int) ^ 0 * 2 ^ k) * 1
        have h2 : (0 : Int) ≤ (2 : Int) ^ 0 * 2 ^ k := by exact_mod_cast Nat.zero_le (2 ^ 0 * 2 ^ k)
        omega
  | succ m ih =>
      have hterm : ∀ i, Qle (mul (fabs arctanCoeff i) (fpow (fabs arctanCoeff) m (k - i)))
          (mul (⟨(2 : Int) ^ m, 1⟩ : Q) ⟨2 ^ (k - i), 1⟩) := by
        intro i
        refine Qle_trans (Qmul_den_pos Nat.one_pos Nat.one_pos)
          (Qmul_le_mul (fabs_den_pos (fun j => arctanCoeff_den_pos j) i) Nat.one_pos
            (fpow_den_pos (fun j => fabs_den_pos (fun l => arctanCoeff_den_pos l) j) m (k - i))
            (fabs_nonneg arctanCoeff i) (fpow_num_nonneg (fun j => fabs_nonneg arctanCoeff j) m (k - i))
            (arctanCoeff_fabs_le_one i) (ih (k - i)))
          (Qeq_le (by simp only [Qeq, mul]; push_cast; ring_uor))
      show Qle (Fsum (fun i => mul (fabs arctanCoeff i) (fpow (fabs arctanCoeff) m (k - i))) k)
        ⟨(2 : Int) ^ (m + 1) * 2 ^ k, 1⟩
      refine Qle_trans (Fsum_den_pos (fun i => Qmul_den_pos Nat.one_pos Nat.one_pos) k)
        (Fsum_le_Fsum hterm k) ?_
      refine Qle_trans (Qmul_den_pos Nat.one_pos (Fsum_den_pos (fun _ => Nat.one_pos) k))
        (Qeq_le (Fsum_mul_left Nat.one_pos (fun _ => Nat.one_pos) k)) ?_
      refine Qle_trans (Qmul_den_pos Nat.one_pos Nat.one_pos)
        (Qeq_le (Qmul_congr (Qeq_refl _) (Qeq_trans (Fsum_den_pos (fun _ => Nat.one_pos) k)
          (Qeq_symm (Fsum_reverse (f := fun j => (⟨(2 : Int) ^ j, 1⟩ : Q)) (fun _ => Nat.one_pos) k))
          (pow2_sum k)))) ?_
      show ((2 : Int) ^ m * (2 ^ (k + 1) - 1)) * 1 ≤ ((2 : Int) ^ (m + 1) * 2 ^ k) * 1
      rw [show (2 : Int) ^ (m + 1) = 2 ^ m * 2 from by rw [Int.pow_succ],
          show (2 : Int) ^ (k + 1) = 2 ^ k * 2 from by rw [Int.pow_succ]]
      have hgen : ∀ A B : Int, 0 ≤ A → (A * (B * 2 - 1)) * 1 ≤ (A * 2 * B) * 1 := by
        intro A B hA
        have key : (A * 2 * B) * 1 - (A * (B * 2 - 1)) * 1 = A := by ring_uor
        omega
      exact hgen ((2 : Int) ^ m) ((2 : Int) ^ k) (by exact_mod_cast Nat.zero_le (2 ^ m))

/-- **Per-term geometric domination**: the `k`-th `|arctanCoeff|ᵐ` evaluation term is `≤ 2ᵐ·(2ρ)ᵏ`. -/
theorem fpow_arctan_term_bound (ρ : Q) (hρd : 0 < ρ.den) (hρ0 : 0 ≤ ρ.num) (m k : Nat) :
    Qle (mul (fpow (fabs arctanCoeff) m k) (qpow ρ k))
      (mul (⟨(2 : Int) ^ m, 1⟩ : Q) (qpow (mul ⟨2, 1⟩ ρ) k)) := by
  refine Qle_trans (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd k))
    (Qmul_le_mul_right (qpow_nonneg hρ0 k) (fpow_fabs_arctan_bound m k)) ?_
  refine Qeq_le (Qeq_trans (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd k)))
    (Qeq_trans (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd k))
      (by simp only [Qeq, mul] : Qeq (mul (⟨(2 : Int) ^ m * 2 ^ k, 1⟩ : Q) (qpow ρ k))
        (mul (mul (⟨(2 : Int) ^ m, 1⟩ : Q) ⟨(2 : Int) ^ k, 1⟩) (qpow ρ k)))
      (Qmul_assoc ⟨(2 : Int) ^ m, 1⟩ ⟨(2 : Int) ^ k, 1⟩ (qpow ρ k)))
    (Qmul_congr (Qeq_refl _) (Qeq_trans (Qmul_den_pos (qpow_den_pos (by decide) k) (qpow_den_pos hρd k))
      (Qmul_congr (Qeq_symm (qpow_two_nat k)) (Qeq_refl _)) (Qeq_symm (qpow_mul ⟨2, 1⟩ ρ (by decide) hρd k)))))

end UOR.Bridge.F1Square.Analysis
