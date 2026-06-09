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

end UOR.Bridge.F1Square.Analysis
