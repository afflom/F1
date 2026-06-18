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

/-- Formal derivative of a pointwise difference: `(S − T)′ = S′ − T′`. -/
theorem fderiv_sub (S T : Nat → Q) (k : Nat) :
    Qeq (fderiv (fun j => Qsub (S j) (T j)) k) (Qsub (fderiv S k) (fderiv T k)) :=
  Qmul_sub_distrib ⟨(k : Int) + 1, 1⟩ (S (k + 1)) (T (k + 1))

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

end UOR.Bridge.F1Square.Analysis
