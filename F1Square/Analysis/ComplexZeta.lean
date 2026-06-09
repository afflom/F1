/-
F1 square — the complex Riemann zeta function `ζ(s) = Σ_{n≥1} n⁻ˢ` for `Re s > 1`, built on the
dyadic-geometric tail. The per-term modulus `|n⁻ˢ| = exp(−Re s · log n)` decays geometrically across
dyadic blocks `B_k = [2ᵏ, 2ᵏ⁺¹)`, giving a rational regularity modulus for each (real, imaginary)
component — the honest route for *real* `σ = Re s > 1` (the integer-`s` telescoping of `Zeta.lean`
fails for `1 < σ < 2`). This brick: the per-term component bounds `−exp(Re z) ≤ Re/Im(eᶻ) ≤ exp(Re z)`.
-/
import F1Square.Analysis.RealPow
import F1Square.Analysis.ComplexPow

namespace UOR.Bridge.F1Square.Analysis

/-- `Re(eᶻ) ≤ exp(Re z)` (`Re(eᶻ) = exp(Re z)·cos(Im z)` and `cos ≤ 1`, `exp ≥ 0`). -/
theorem Cexp_re_le (z : Complex) : Rle ((Cexp z).re) (RexpReal z.re) :=
  Rle_trans (Rmul_le_Rmul_left (RexpReal_nonneg z.re) (Rcos_le_one z.im))
    (Rle_of_Req (Rmul_one (RexpReal z.re)))

/-- `−exp(Re z) ≤ Re(eᶻ)` (`cos ≥ −1`). -/
theorem Cexp_re_ge (z : Complex) : Rle (Rneg (RexpReal z.re)) ((Cexp z).re) :=
  Rle_trans (Rle_of_Req (Req_symm (Req_trans (Rmul_neg_right (RexpReal z.re) one)
      (Rneg_congr (Rmul_one (RexpReal z.re))))))
    (Rmul_le_Rmul_left (RexpReal_nonneg z.re) (Rneg_one_le_Rcos z.im))

/-- `Im(eᶻ) ≤ exp(Re z)` (`Im(eᶻ) = exp(Re z)·sin(Im z)` and `sin ≤ 1`). -/
theorem Cexp_im_le (z : Complex) : Rle ((Cexp z).im) (RexpReal z.re) :=
  Rle_trans (Rmul_le_Rmul_left (RexpReal_nonneg z.re) (Rsin_le_one z.im))
    (Rle_of_Req (Rmul_one (RexpReal z.re)))

/-- `−exp(Re z) ≤ Im(eᶻ)` (`sin ≥ −1`). -/
theorem Cexp_im_ge (z : Complex) : Rle (Rneg (RexpReal z.re)) ((Cexp z).im) :=
  Rle_trans (Rle_of_Req (Req_symm (Req_trans (Rmul_neg_right (RexpReal z.re) one)
      (Rneg_congr (Rmul_one (RexpReal z.re))))))
    (Rmul_le_Rmul_left (RexpReal_nonneg z.re) (Rneg_one_le_Rsin z.im))

/-- **The `n`-th term `n⁻ˢ = exp(−s·log n)`** of `ζ(s)`, for `n ≥ 1` (`log 1 = 0`, so `1⁻ˢ = e⁰ = 1`).
    Built on `logN` (the natural-log of `ComplexZeta`/`RealPow`) so the dyadic bounds apply directly. -/
def czetaTerm (s : Complex) (n : Nat) (hn : 1 ≤ n) : Complex :=
  Cexp ⟨Rmul (Rneg s.re) (logN n hn), Rmul (Rneg s.im) (logN n hn)⟩

/-- The term's modulus exponent `−Re s · log n` (`= Re` of the `Cexp` argument). -/
def czetaExpArg (s : Complex) (n : Nat) (hn : 1 ≤ n) : Real := Rmul (Rneg s.re) (logN n hn)

theorem czetaTerm_re_le (s : Complex) (n : Nat) (hn : 1 ≤ n) :
    Rle ((czetaTerm s n hn).re) (RexpReal (czetaExpArg s n hn)) := Cexp_re_le _

theorem czetaTerm_re_ge (s : Complex) (n : Nat) (hn : 1 ≤ n) :
    Rle (Rneg (RexpReal (czetaExpArg s n hn))) ((czetaTerm s n hn).re) := Cexp_re_ge _

theorem czetaTerm_im_le (s : Complex) (n : Nat) (hn : 1 ≤ n) :
    Rle ((czetaTerm s n hn).im) (RexpReal (czetaExpArg s n hn)) := Cexp_im_le _

theorem czetaTerm_im_ge (s : Complex) (n : Nat) (hn : 1 ≤ n) :
    Rle (Rneg (RexpReal (czetaExpArg s n hn))) ((czetaTerm s n hn).im) := Cexp_im_ge _

/-- The real partial sum `Σ_{n=1}^N Re(n⁻ˢ)`. -/
def czetaReSum (s : Complex) : Nat → Real
  | 0 => zero
  | (n + 1) => Radd (czetaReSum s n) ((czetaTerm s (n + 1) (by omega)).re)

/-- The imaginary partial sum `Σ_{n=1}^N Im(n⁻ˢ)`. -/
def czetaImSum (s : Complex) : Nat → Real
  | 0 => zero
  | (n + 1) => Radd (czetaImSum s n) ((czetaTerm s (n + 1) (by omega)).im)

/-- The modulus partial sum `Σ_{n=1}^N exp(−Re s · log n)` (dominates both components' increments). -/
def czetaExpSum (s : Complex) : Nat → Real
  | 0 => zero
  | (n + 1) => Radd (czetaExpSum s n) (RexpReal (czetaExpArg s (n + 1) (by omega)))

/-- `(a+t) − b ≈ (a−b) + t`. -/
theorem Rsub_Radd_left (a t b : Real) : Req (Rsub (Radd a t) b) (Radd (Rsub a b) t) :=
  Req_trans (Radd_assoc a t (Rneg b))
    (Req_trans (Radd_congr (Req_refl a) (Radd_comm t (Rneg b)))
      (Req_symm (Radd_assoc a (Rneg b) t)))

/-- `−0 ≈ 0`. -/
theorem Rneg_zero : Req (Rneg zero) zero :=
  Req_of_seq_Qeq (fun _ => by show Qeq (neg (⟨0, 1⟩ : Q)) ⟨0, 1⟩; decide)

/-- **Upper tail bound (real part)**, `d`-form: `S_re(N+d) − S_re(N) ≤ E(N+d) − E(N)`. -/
theorem czeta_re_diff_le_aux (s : Complex) (N : Nat) : ∀ d,
    Rle (Rsub (czetaReSum s (N + d)) (czetaReSum s N))
        (Rsub (czetaExpSum s (N + d)) (czetaExpSum s N))
  | 0 => Rle_of_Req (Req_trans (Radd_neg _) (Req_symm (Radd_neg _)))
  | (d + 1) =>
      Rle_trans (Rle_of_Req (Rsub_Radd_left (czetaReSum s (N + d)) _ (czetaReSum s N)))
        (Rle_trans (Radd_le_add (czeta_re_diff_le_aux s N d) (czetaTerm_re_le s (N + d + 1) (by omega)))
          (Rle_of_Req (Req_symm (Rsub_Radd_left (czetaExpSum s (N + d)) _ (czetaExpSum s N)))))

/-- **Upper tail bound (real part)**: for `N ≤ M`, `S_re(M) − S_re(N) ≤ E(M) − E(N)`. -/
theorem czeta_re_diff_le (s : Complex) {N M : Nat} (hNM : N ≤ M) :
    Rle (Rsub (czetaReSum s M) (czetaReSum s N)) (Rsub (czetaExpSum s M) (czetaExpSum s N)) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hNM; exact czeta_re_diff_le_aux s N d

/-- **Lower tail bound (real part)**, `d`-form: `−(E(N+d) − E(N)) ≤ S_re(N+d) − S_re(N)`. -/
theorem czeta_re_diff_ge_aux (s : Complex) (N : Nat) : ∀ d,
    Rle (Rneg (Rsub (czetaExpSum s (N + d)) (czetaExpSum s N)))
        (Rsub (czetaReSum s (N + d)) (czetaReSum s N))
  | 0 => Rle_of_Req (Req_trans (Rneg_congr (Radd_neg _)) (Req_trans Rneg_zero (Req_symm (Radd_neg _))))
  | (d + 1) =>
      Rle_trans (Rle_of_Req (Req_trans
          (Rneg_congr (Rsub_Radd_left (czetaExpSum s (N + d)) _ (czetaExpSum s N)))
          (Rneg_Radd (Rsub (czetaExpSum s (N + d)) (czetaExpSum s N)) _)))
        (Rle_trans (Radd_le_add (czeta_re_diff_ge_aux s N d) (czetaTerm_re_ge s (N + d + 1) (by omega)))
          (Rle_of_Req (Req_symm (Rsub_Radd_left (czetaReSum s (N + d)) _ (czetaReSum s N)))))

/-- **Lower tail bound (real part)**: for `N ≤ M`, `−(E(M) − E(N)) ≤ S_re(M) − S_re(N)`. -/
theorem czeta_re_diff_ge (s : Complex) {N M : Nat} (hNM : N ≤ M) :
    Rle (Rneg (Rsub (czetaExpSum s M) (czetaExpSum s N))) (Rsub (czetaReSum s M) (czetaReSum s N)) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hNM; exact czeta_re_diff_ge_aux s N d

/-- **Upper tail bound (imaginary part)**, `d`-form. -/
theorem czeta_im_diff_le_aux (s : Complex) (N : Nat) : ∀ d,
    Rle (Rsub (czetaImSum s (N + d)) (czetaImSum s N))
        (Rsub (czetaExpSum s (N + d)) (czetaExpSum s N))
  | 0 => Rle_of_Req (Req_trans (Radd_neg _) (Req_symm (Radd_neg _)))
  | (d + 1) =>
      Rle_trans (Rle_of_Req (Rsub_Radd_left (czetaImSum s (N + d)) _ (czetaImSum s N)))
        (Rle_trans (Radd_le_add (czeta_im_diff_le_aux s N d) (czetaTerm_im_le s (N + d + 1) (by omega)))
          (Rle_of_Req (Req_symm (Rsub_Radd_left (czetaExpSum s (N + d)) _ (czetaExpSum s N)))))

theorem czeta_im_diff_le (s : Complex) {N M : Nat} (hNM : N ≤ M) :
    Rle (Rsub (czetaImSum s M) (czetaImSum s N)) (Rsub (czetaExpSum s M) (czetaExpSum s N)) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hNM; exact czeta_im_diff_le_aux s N d

/-- **Lower tail bound (imaginary part)**, `d`-form. -/
theorem czeta_im_diff_ge_aux (s : Complex) (N : Nat) : ∀ d,
    Rle (Rneg (Rsub (czetaExpSum s (N + d)) (czetaExpSum s N)))
        (Rsub (czetaImSum s (N + d)) (czetaImSum s N))
  | 0 => Rle_of_Req (Req_trans (Rneg_congr (Radd_neg _)) (Req_trans Rneg_zero (Req_symm (Radd_neg _))))
  | (d + 1) =>
      Rle_trans (Rle_of_Req (Req_trans
          (Rneg_congr (Rsub_Radd_left (czetaExpSum s (N + d)) _ (czetaExpSum s N)))
          (Rneg_Radd (Rsub (czetaExpSum s (N + d)) (czetaExpSum s N)) _)))
        (Rle_trans (Radd_le_add (czeta_im_diff_ge_aux s N d) (czetaTerm_im_ge s (N + d + 1) (by omega)))
          (Rle_of_Req (Req_symm (Rsub_Radd_left (czetaImSum s (N + d)) _ (czetaImSum s N)))))

theorem czeta_im_diff_ge (s : Complex) {N M : Nat} (hNM : N ≤ M) :
    Rle (Rneg (Rsub (czetaExpSum s M) (czetaExpSum s N))) (Rsub (czetaImSum s M) (czetaImSum s N)) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hNM; exact czeta_im_diff_ge_aux s N d

/-- **Block-sum bound**: if each of the `d` modulus terms over `(N, N+d]` is `≤ B`, then
    `E(N+d) − E(N) ≤ d·B` (the dyadic block's `2ᵏ` terms each `≤ exp(−σ·k·log 2)`). -/
theorem czetaExp_block_le (s : Complex) (N : Nat) (B : Real) : ∀ d,
    (∀ i, i < d → Rle (RexpReal (czetaExpArg s (N + i + 1) (by omega))) B) →
    Rle (Rsub (czetaExpSum s (N + d)) (czetaExpSum s N)) (Rnsmul d B)
  | 0 => fun _ => Rle_of_Req (Radd_neg _)
  | (d + 1) => fun h =>
      Rle_trans (Rle_of_Req (Rsub_Radd_left (czetaExpSum s (N + d)) _ (czetaExpSum s N)))
        (Rle_trans (Radd_le_add (czetaExp_block_le s N B d (fun i hi => h i (by omega)))
            (h d (by omega)))
          (Rle_of_Req (Radd_comm (Rnsmul d B) B)))

/-- **Per-term block bound**: for `n ≥ 2ᵏ` (and `Re s ≥ 0`), the `n`-th modulus term
    `exp(−Re s · log n) ≤ exp(−Re s · k · log 2)`. The bound `B` feeding `czetaExp_block_le`. -/
theorem czetaExp_term_le (s : Complex) (hσ : Rnonneg s.re) (k n : Nat) (hn : 1 ≤ n) (hkn : 2 ^ k ≤ n) :
    Rle (RexpReal (czetaExpArg s n hn))
        (RexpReal (Rneg (Rmul s.re (Rnsmul k (logN 2 (by omega)))))) :=
  Rle_trans (Rle_of_Req (RexpReal_congr (Rmul_neg_left s.re (logN n hn)))) (exp_block_bound hσ hkn)

/-- **The dyadic block bound**: `E(2ᵏ⁺¹) − E(2ᵏ) ≤ 2ᵏ · exp(−Re s · k · log 2)` (`2ᵏ` terms, each
    `≤ exp(−Re s · k · log 2)`). The `k`-th block of the modulus sum. -/
theorem czetaExp_block (s : Complex) (hσ : Rnonneg s.re) (k : Nat) :
    Rle (Rsub (czetaExpSum s (2 ^ (k + 1))) (czetaExpSum s (2 ^ k)))
        (Rnsmul (2 ^ k) (RexpReal (Rneg (Rmul s.re (Rnsmul k (logN 2 (by omega))))))) := by
  have he : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  rw [← he]
  exact czetaExp_block_le s (2 ^ k) _ (2 ^ k)
    (fun i _ => czetaExp_term_le s hσ k (2 ^ k + i + 1) (by omega) (by omega))

/-- The single-step modulus ratio `u = exp(−Re s · log 2)` (so `block(k) ≤ (2u)ᵏ`). -/
def czetaU (s : Complex) : Real := RexpReal (Rneg (Rmul s.re (logN 2 (by omega))))

/-- `exp(−Re s · k · log 2) ≈ uᵏ`. -/
theorem czetaExpB_eq_pow (s : Complex) (k : Nat) :
    Req (RexpReal (Rneg (Rmul s.re (Rnsmul k (logN 2 (by omega)))))) (Rpow (czetaU s) k) :=
  Req_trans (RexpReal_congr (Req_trans (Rneg_congr (Rmul_Rnsmul s.re (logN 2 (by omega)) k))
      (Rneg_Rnsmul (Rmul s.re (logN 2 (by omega))) k)))
    (RexpReal_nsmul (Rneg (Rmul s.re (logN 2 (by omega)))) k)

/-- **The dyadic block as a geometric power**: `E(2ᵏ⁺¹) − E(2ᵏ) ≤ (2u)ᵏ`, `u = exp(−Re s · log 2)`. -/
theorem czetaExp_block_pow (s : Complex) (hσ : Rnonneg s.re) (k : Nat) :
    Rle (Rsub (czetaExpSum s (2 ^ (k + 1))) (czetaExpSum s (2 ^ k)))
        (Rpow (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (czetaU s)) k) := by
  refine Rle_trans (czetaExp_block s hσ k) (Rle_of_Req ?_)
  -- Rnsmul(2^k) B ≈ Rmul(ofQ 2^k) B ≈ Rmul(Rpow(ofQ 2) k)(Rpow u k) ≈ Rpow(2u) k
  refine Req_trans (Rnsmul_eq_Rmul_ofQ _ (2 ^ k)) ?_
  refine Req_trans (Rmul_congr ?_ (czetaExpB_eq_pow s k)) (Req_symm (Rpow_mul_dist _ _ k))
  -- ofQ ⟨2^k,1⟩ ≈ Rpow(ofQ 2) k
  exact Req_symm (Req_trans (Rpow_ofQ (by decide) k)
    (ofQ_congr (qpow_den_pos (by decide) k) Nat.one_pos
      (Qeq_trans Nat.one_pos (qpow_two_eq k) (by simp only [Qeq]; push_cast; ring_uor))))

set_option maxHeartbeats 1000000 in
/-- `log2 − Re s · log2 ≈ −(Re s − 1)·log2` (the exponent of `2u = exp(−θ)`). -/
theorem czeta_theta_arg_eq (s : Complex) :
    Req (Radd (logN 2 (by omega)) (Rneg (Rmul s.re (logN 2 (by omega)))))
        (Rneg (Rmul (Rsub s.re one) (logN 2 (by omega)))) := by
  have hL : Req (Radd (logN 2 (by omega)) (Rneg (Rmul s.re (logN 2 (by omega)))))
      (Rmul (Rsub one s.re) (logN 2 (by omega))) :=
    Req_trans (Radd_congr (Req_symm (Rone_mul (logN 2 (by omega))))
        (Req_symm (Rmul_neg_left s.re (logN 2 (by omega)))))
      (Req_symm (Rmul_distrib_right one (Rneg s.re) (logN 2 (by omega))))
  have hR : Req (Rneg (Rmul (Rsub s.re one) (logN 2 (by omega))))
      (Rmul (Rsub one s.re) (logN 2 (by omega))) :=
    Req_trans (Req_symm (Rmul_neg_left (Rsub s.re one) (logN 2 (by omega))))
      (Rmul_congr (Rneg_Rsub s.re one) (Req_refl _))
  exact Req_trans hL (Req_symm hR)

/-- **`2u = exp(−θ)`** where `θ = (Re s − 1)·log 2`: the dyadic ratio as a single exp. -/
theorem czetaU_2u_eq (s : Complex) :
    Req (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (czetaU s))
        (RexpReal (Rneg (Rmul (Rsub s.re one) (logN 2 (by omega))))) :=
  Req_trans (Rmul_congr (Req_symm (Rexp_logN 2 (by omega))) (Req_refl _))
    (Req_trans (Req_symm (RexpReal_add (logN 2 (by omega)) (Rneg (Rmul s.re (logN 2 (by omega))))))
      (RexpReal_congr (czeta_theta_arg_eq s)))

/-- **`2u ≤ 1/(1+τ) < 1`** whenever `θ = (Re s−1)·log2 ≥ ofQ τ` (`τ > 0`): the dyadic ratio bound. -/
theorem czetaU_2u_le_of_theta (s : Complex) {τ : Q} (hτn : 0 < τ.num) (hτd : 0 < τ.den)
    (hθ : Rle (ofQ τ hτd) (Rmul (Rsub s.re one) (logN 2 (by omega)))) :
    Rle (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (czetaU s))
        (ofQ (Qinv (add ⟨1, 1⟩ τ)) (Qinv_den_pos (by simp only [add]; push_cast; omega))) :=
  Rle_trans (Rle_of_Req (czetaU_2u_eq s)) (Rexp_neg_le_ratio hτn hτd hθ)

/-- **`θ ≥ ofQ(ε/2)`** from `Re s > 1` (`Pos(s.re−1)`): extracts the positive rational lower bound on the
    dyadic exponent (`σ−1 ≥ ε` via `Pos_imp_ofQ_le`, `log2 ≥ ½`). -/
theorem czeta_theta_ge (s : Complex) (hs : Pos (Rsub s.re one)) :
    ∃ (τ : Q) (hτd : 0 < τ.den), 0 < τ.num ∧
      Rle (ofQ τ hτd) (Rmul (Rsub s.re one) (logN 2 (by omega))) := by
  obtain ⟨ε, hεd, hεn, hε⟩ := Pos_imp_ofQ_le hs
  refine ⟨mul ε ⟨1, 2⟩, Qmul_den_pos hεd (by decide), by simp only [mul]; omega, ?_⟩
  refine Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ hεd (by decide)))) ?_
  exact Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ hεd (Int.le_of_lt hεn)) logN_2_ge_half)
    (Rmul_le_Rmul_right (Rnonneg_logN 2 (by omega)) hε)

/-- **The dyadic block as a rational geometric term**: `E(2ᵏ⁺¹) − E(2ᵏ) ≤ ofQ(rᵏ)`, `r = 1/(1+τ) < 1`,
    for `θ = (Re s−1)·log2 ≥ ofQ τ` (`τ > 0`) and `Re s ≥ 0`. -/
theorem czetaExp_block_geo (s : Complex) (hσ : Rnonneg s.re) {τ : Q} (hτn : 0 < τ.num) (hτd : 0 < τ.den)
    (hθ : Rle (ofQ τ hτd) (Rmul (Rsub s.re one) (logN 2 (by omega)))) (k : Nat) :
    Rle (Rsub (czetaExpSum s (2 ^ (k + 1))) (czetaExpSum s (2 ^ k)))
        (ofQ (qpow (Qinv (add ⟨1, 1⟩ τ)) k)
          (qpow_den_pos (Qinv_den_pos (by simp only [add]; push_cast; omega)) k)) := by
  have hrd : 0 < (Qinv (add (⟨1, 1⟩ : Q) τ)).den := Qinv_den_pos (by simp only [add]; push_cast; omega)
  have hrn : 0 ≤ (Qinv (add (⟨1, 1⟩ : Q) τ)).num := by
    show (0 : Int) ≤ ((add (⟨1, 1⟩ : Q) τ).den : Int); exact_mod_cast Nat.zero_le _
  refine Rle_trans (czetaExp_block_pow s hσ k) ?_
  refine Rle_trans (Rpow_mono
      (Rnonneg_Rmul (Rnonneg_ofQ (by decide) (by decide)) (RexpReal_nonneg _))
      (Rnonneg_ofQ hrd hrn) (czetaU_2u_le_of_theta s hτn hτd hθ) k) ?_
  exact Rle_of_Req (Rpow_ofQ hrd k)

/-- The rational geometric partial sum `Σ_{k=j}^{j+d−1} rᵏ` (block-first ordering). -/
def geoFrom (r : Q) (j : Nat) : Nat → Q
  | 0 => ⟨0, 1⟩
  | (d + 1) => add (qpow r (j + d)) (geoFrom r j d)

theorem geoFrom_den_pos (r : Q) (hrd : 0 < r.den) (j : Nat) : ∀ d, 0 < (geoFrom r j d).den
  | 0 => Nat.one_pos
  | (d + 1) => add_den_pos (qpow_den_pos hrd (j + d)) (geoFrom_den_pos r hrd j d)

private theorem geo_step_id (X Y r : Q) :
    Qeq (add (mul X (Qsub ⟨1, 1⟩ r)) (Qsub Y X)) (Qsub Y (mul r X)) := by
  simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor

/-- **Geometric telescoping**: `(Σ_{k=j}^{j+d−1} rᵏ)·(1−r) = rʲ − r^{j+d}`. -/
theorem geoFrom_telescope (r : Q) (hrd : 0 < r.den) (j d : Nat) :
    Qeq (mul (geoFrom r j d) (Qsub ⟨1, 1⟩ r)) (Qsub (qpow r j) (qpow r (j + d))) := by
  induction d with
  | zero => simp only [geoFrom, Nat.add_zero, Qeq, mul, Qsub, add, neg]; push_cast; ring_uor
  | succ d ih =>
      have e1 : Qeq (mul (geoFrom r j (d + 1)) (Qsub ⟨1, 1⟩ r))
          (add (mul (qpow r (j + d)) (Qsub ⟨1, 1⟩ r)) (mul (geoFrom r j d) (Qsub ⟨1, 1⟩ r))) :=
        Qmul_add_right _ _ _
      refine Qeq_trans (add_den_pos (Qmul_den_pos (qpow_den_pos hrd _) (Qsub_den_pos Nat.one_pos hrd))
          (Qmul_den_pos (geoFrom_den_pos r hrd j d) (Qsub_den_pos Nat.one_pos hrd))) e1 ?_
      refine Qeq_trans (add_den_pos (Qmul_den_pos (qpow_den_pos hrd _) (Qsub_den_pos Nat.one_pos hrd))
          (Qsub_den_pos (qpow_den_pos hrd j) (qpow_den_pos hrd (j + d))))
        (Qadd_congr (Qeq_refl _) ih) ?_
      have hjd : j + (d + 1) = (j + d) + 1 := by omega
      rw [hjd]
      exact geo_step_id (qpow r (j + d)) (qpow r j) r

/-- **The tail is bounded by a vanishing geometric**: `Σ_{k=j}^{j+d−1} rᵏ ≤ rʲ/(1−r)` (for `0 ≤ r`, `r < 1`). -/
theorem geoFrom_le (r : Q) (hrd : 0 < r.den) (hr0 : 0 ≤ r.num) (hr1 : 0 < (Qsub (⟨1, 1⟩ : Q) r).num)
    (j d : Nat) :
    Qle (geoFrom r j d) (mul (qpow r j) (Qinv (Qsub ⟨1, 1⟩ r))) := by
  have hwd : 0 < (Qsub (⟨1, 1⟩ : Q) r).den := Qsub_den_pos Nat.one_pos hrd
  refine Qmul_le_cancel_right hr1 hwd ?_
  refine Qle_trans (Qsub_den_pos (qpow_den_pos hrd j) (qpow_den_pos hrd (j + d)))
    (Qeq_le (geoFrom_telescope r hrd j d)) ?_
  -- r^j − r^{j+d} ≤ (r^j/(1−r))·(1−r) = r^j
  have hcancel : Qeq (mul (mul (qpow r j) (Qinv (Qsub ⟨1, 1⟩ r))) (Qsub ⟨1, 1⟩ r)) (qpow r j) :=
    Qeq_trans (Qmul_den_pos (qpow_den_pos hrd j) (Qmul_den_pos (Qinv_den_pos hr1) hwd))
      (Qmul_assoc (qpow r j) (Qinv (Qsub ⟨1, 1⟩ r)) (Qsub ⟨1, 1⟩ r))
      (Qeq_trans (Qmul_den_pos (qpow_den_pos hrd j) Nat.one_pos)
        (Qmul_congr (Qeq_refl _) (Qinv_mul hwd hr1)) (mul_one (qpow r j)))
  refine Qle_trans (qpow_den_pos hrd j) ?_ (Qeq_le (Qeq_symm hcancel))
  show Qle (Qsub (qpow r j) (qpow r (j + d))) (qpow r j)
  have hnn : 0 ≤ (qpow r (j + d)).num := qpow_nonneg hr0 (j + d)
  exact Qsub_le_of_le_add (qpow_den_pos hrd (j + d)) (qpow_den_pos hrd j)
    (Qle_trans (add_den_pos (qpow_den_pos hrd j) (qpow_den_pos hrd (j + d)))
      (Qle_self_add hnn) (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor)))

/-- **The dyadic tail telescopes to a geometric partial sum**: `E(2^{j+d}) − E(2ʲ) ≤ ofQ(Σ_{k=j}^{j+d−1} rᵏ)`. -/
theorem czetaExp_tail (s : Complex) (hσ : Rnonneg s.re) {τ : Q} (hτn : 0 < τ.num) (hτd : 0 < τ.den)
    (hθ : Rle (ofQ τ hτd) (Rmul (Rsub s.re one) (logN 2 (by omega)))) (j : Nat) : ∀ d,
    Rle (Rsub (czetaExpSum s (2 ^ (j + d))) (czetaExpSum s (2 ^ j)))
        (ofQ (geoFrom (Qinv (add ⟨1, 1⟩ τ)) j d)
          (geoFrom_den_pos _ (Qinv_den_pos (by simp only [add]; push_cast; omega)) j d))
  | 0 => Rle_of_Req (Radd_neg _)
  | (d + 1) => by
      refine Rle_trans (Rle_of_Req (Req_symm
          (Rsub_telescope (czetaExpSum s (2 ^ (j + d + 1))) (czetaExpSum s (2 ^ (j + d)))
            (czetaExpSum s (2 ^ j))))) ?_
      refine Rle_trans (Radd_le_add (czetaExp_block_geo s hσ hτn hτd hθ (j + d))
          (czetaExp_tail s hσ hτn hτd hθ j d)) ?_
      exact Rle_of_Req (Radd_ofQ_ofQ _ _)

/-- **From a real upper bound to a same-index rational bound** (the completeness bridge): if `a − b ≤ c`
    as reals (`c` a rational), then `aₙ − bₙ ≤ c + 2/(n+1)` for every index `n`. Regularity moves the
    comparison index `2m+1` back to `n`; the generalized Archimedean lemma kills the `3/(m+1)` tail. -/
theorem seq_diff_le (a b : Real) (c : Q) (hcd : 0 < c.den)
    (h : Rle (Rsub a b) (ofQ c hcd)) (n : Nat) :
    Qle (Qsub (a.seq n) (b.seq n)) (add c ⟨2, n + 1⟩) := by
  apply Qarch_gen (C := 3) (Qsub_den_pos (a.den_pos n) (b.den_pos n))
    (add_den_pos hcd (Nat.succ_pos _))
  intro m
  have hmid : Qle (Qsub (a.seq (2 * m + 1)) (b.seq (2 * m + 1))) (add c ⟨2, m + 1⟩) := h m
  have s1 : Qle (a.seq n) (add (a.seq (2 * m + 1)) (add (Qbound n) (Qbound (2 * m + 1)))) :=
    Qle_add_of_Qabs_sub (a.den_pos n) (a.den_pos _)
      (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)) (a.reg n (2 * m + 1))
  have s2 : Qle (neg (b.seq n)) (add (neg (b.seq (2 * m + 1))) (add (Qbound n) (Qbound (2 * m + 1)))) :=
    Qle_add_of_Qabs_sub (neg_den_pos (b.den_pos n)) (neg_den_pos (b.den_pos _))
      (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))
      (by rw [Qabs_Qsub_neg]; exact b.reg n (2 * m + 1))
  have hp1 : Qle (Qsub (a.seq n) (b.seq n))
      (add (add (a.seq (2 * m + 1)) (add (Qbound n) (Qbound (2 * m + 1))))
           (add (neg (b.seq (2 * m + 1))) (add (Qbound n) (Qbound (2 * m + 1))))) :=
    Qadd_le_add s1 s2
  have hreg : Qeq
      (add (add (a.seq (2 * m + 1)) (add (Qbound n) (Qbound (2 * m + 1))))
           (add (neg (b.seq (2 * m + 1))) (add (Qbound n) (Qbound (2 * m + 1)))))
      (add (Qsub (a.seq (2 * m + 1)) (b.seq (2 * m + 1)))
           (add (add (Qbound n) (Qbound (2 * m + 1))) (add (Qbound n) (Qbound (2 * m + 1))))) := by
    simp only [Qeq, Qsub, add, neg, Qbound]; push_cast; ring_uor
  refine Qle_trans
    (add_den_pos (add_den_pos (a.den_pos _) (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)))
      (add_den_pos (neg_den_pos (b.den_pos _)) (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))))
    hp1 ?_
  refine Qle_trans
    (add_den_pos (Qsub_den_pos (a.den_pos _) (b.den_pos _))
      (add_den_pos (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))
        (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))))
    (Qeq_le hreg) ?_
  exact Qle_trans
    (add_den_pos (add_den_pos hcd (Nat.succ_pos _))
      (add_den_pos (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))
        (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))))
    (Qadd_le_add hmid (Qle_refl _))
    (Qeq_le (by simp only [Qeq, add, Qbound]; push_cast; ring_uor))

/-- **The completeness bridge to `RReg`**: a family `X : ℕ → ℝ` whose pairwise real differences are
    bounded by rationals `c j k ≤ 1/(j+1) + 1/(k+1)` is a regular sequence of reals. -/
theorem RReg_of_real_bound (X : Nat → Real) (c : Nat → Nat → Q) (hcd : ∀ j k, 0 < (c j k).den)
    (hcb : ∀ j k, Qle (c j k) (add ⟨1, j + 1⟩ ⟨1, k + 1⟩))
    (hX : ∀ j k, Rle (Rsub (X j) (X k)) (ofQ (c j k) (hcd j k))) : RReg X := by
  intro j k n
  have hjk : Qle (Qsub ((X j).seq n) ((X k).seq n)) (add (c j k) ⟨2, n + 1⟩) :=
    seq_diff_le (X j) (X k) (c j k) (hcd j k) (hX j k) n
  have hkj : Qle (Qsub ((X k).seq n) ((X j).seq n)) (add (c k j) ⟨2, n + 1⟩) :=
    seq_diff_le (X k) (X j) (c k j) (hcd k j) (hX k j) n
  have hcb' : Qle (c k j) (add ⟨1, j + 1⟩ ⟨1, k + 1⟩) :=
    Qle_trans (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (hcb k j)
      (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor))
  refine Qabs_le_of_both ?_ ?_
  · exact Qle_trans (add_den_pos (hcd j k) (Nat.succ_pos _)) hjk
      (Qadd_le_add (hcb j k) (Qle_refl _))
  · have hcomm : Qeq (Qsub ((X k).seq n) ((X j).seq n))
        (neg (Qsub ((X j).seq n) ((X k).seq n))) := by
      simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
    refine Qle_congr_left (Qsub_den_pos ((X k).den_pos n) ((X j).den_pos n)) hcomm ?_
    exact Qle_trans (add_den_pos (hcd k j) (Nat.succ_pos _)) hkj
      (Qadd_le_add hcb' (Qle_refl _))

end UOR.Bridge.F1Square.Analysis
