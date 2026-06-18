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

end UOR.Bridge.F1Square.Analysis
