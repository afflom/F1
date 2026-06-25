/-
F1 square — the certified **half-line integral** `∫₁^∞ f`, built as the Bishop limit of the
unit-interval integrals `∫_n^{n+1} f` summed by the UOR convergence engine `genSum_RReg`.

`∫₁^∞ f = Σ_{n≥1} ∫_n^{n+1} f`, the limit of the partial integrals `∫_1^{N+1} f = Σ_{i<N} ∫_{i+1}^{i+2} f`.
Each term `T i = ∫_{i+1}^{i+2} f` is a width-1 interval integral (`riemannIntegralI`); convergence is
the genuine analytic content and is carried as the decay hypothesis `|T m| ≤ K/((m+1)m)` (`m ≥ 1`),
exactly the `genSum_RReg` input. This is the improper range the Mellin link to the completed ζ needs
(its split at `x = 1`), and the half-line domain of Track-2's Weil integrals.

The decay bound is the honest seam: it is where convergence lives, so a concrete integrand discharges
it from its own decay structure, mirroring how the program carries every analytic input as an explicit
audit-visible hypothesis rather than an axiom.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.IntervalIntegral
import F1Square.Analysis.ThetaFunction

namespace UOR.Bridge.F1Square.Analysis

/-- The `m`-th unit-interval term `T m = ∫_{m+1}^{m+2} f` (width `1`, left endpoint `m+1`), so the
    partial sum `Σ_{i<N} T i` is the proper integral `∫_1^{N+1} f`. -/
def integralTerm {f : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y)) (m : Nat) : Real :=
  riemannIntegralI hLd hLn hlip hfc (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q)
    Nat.one_pos (by decide) (by decide)

/-- **The certified half-line integral `∫₁^∞ f`** — the Bishop limit of the partial integrals
    `∫_1^{N+1} f`, regular by `genSum_RReg` from the term decay bound `|∫_n^{n+1} f| ≤ K/((n+1)n)`. -/
def improperIntegral1 {f : Real → Real} {L K : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y)) (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hb : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hLd hLn hlip hfc m)
      ∧ Rle (integralTerm hLd hLn hlip hfc m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm)))) : Real :=
  Rlim (fun j => genSum (integralTerm hLd hLn hlip hfc) (digammaMidx K j))
    (genSum_RReg (integralTerm hLd hLn hlip hfc) hKd hK0 hb)

/-- **`∫₁^∞ f ≥ 0` for `f ≥ 0`** — every unit-interval term is non-negative (`riemannIntegralI_nonneg`),
    so every partial sum is (`genSum_nonneg`), and the limit inherits it (`Rnonneg_Rlim_seq`). -/
theorem improperIntegral1_nonneg {f : Real → Real} {L K : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y)) (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hb : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hLd hLn hlip hfc m)
      ∧ Rle (integralTerm hLd hLn hlip hfc m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
    (hfnn : ∀ x, Rnonneg (f x)) :
    Rnonneg (improperIntegral1 hLd hLn hlip hfc hKd hK0 hb) :=
  Rnonneg_Rlim_seq _ (fun j =>
    genSum_nonneg (fun _m => riemannIntegralI_nonneg hLd hLn hlip hfc hfnn _ _ _ _ _)
      (digammaMidx K j))

/-- Termwise monotonicity of `genSum`: `Tf ≤ Tg` pointwise gives `Σ Tf ≤ Σ Tg`. -/
theorem genSum_le_genSum {Tf Tg : Nat → Real} (h : ∀ n, Rle (Tf n) (Tg n)) :
    ∀ N, Rle (genSum Tf N) (genSum Tg N)
  | 0 => Rle_of_Req (Req_refl _)
  | (N + 1) => Radd_le_add (genSum_le_genSum h N) (h N)

/-- **`∫₁^∞ f ≤ ∫₁^∞ g` for `f ≤ g`** (shared Lipschitz modulus `L` and decay constant `K`, so both
    limits sample the same schedule) — termwise `riemannIntegralI_le`, lifted through `genSum` and the
    Bishop limit (`Rlim_le_seq`). -/
theorem improperIntegral1_le {f g : Real → Real} {L K : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlipf : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcf : ∀ x y, Req x y → Req (f x) (f y))
    (hlipg : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcg : ∀ x y, Req x y → Req (g x) (g y)) (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hbf : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hLd hLn hlipf hfcf m)
      ∧ Rle (integralTerm hLd hLn hlipf hfcf m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
    (hbg : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hLd hLn hlipg hfcg m)
      ∧ Rle (integralTerm hLd hLn hlipg hfcg m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
    (hfg : ∀ x, Rle (f x) (g x)) :
    Rle (improperIntegral1 hLd hLn hlipf hfcf hKd hK0 hbf)
        (improperIntegral1 hLd hLn hlipg hfcg hKd hK0 hbg) :=
  Rlim_le_seq _ _ (fun j =>
    genSum_le_genSum
      (fun _m => riemannIntegralI_le hLd hLn hlipf hfcf hlipg hfcg hfg _ _ _ _ _)
      (digammaMidx K j))

/-- **The certified full half-line integral `∫₀^∞ f = ∫₀¹ f + ∫₁^∞ f`** — the Mellin domain, split
    at `x = 1` into the `[0,1]` gateway (`riemannIntegral`) and the convergent half-line tail
    (`improperIntegral1`). -/
def halfLineIntegral {f : Real → Real} {L K : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y)) (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hb : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hLd hLn hlip hfc m)
      ∧ Rle (integralTerm hLd hLn hlip hfc m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm)))) : Real :=
  Radd (riemannIntegral hLd hLn hlip hfc) (improperIntegral1 hLd hLn hlip hfc hKd hK0 hb)

/-- **`∫₀^∞ f ≥ 0` for `f ≥ 0`** — both halves are non-negative. -/
theorem halfLineIntegral_nonneg {f : Real → Real} {L K : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y)) (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hb : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hLd hLn hlip hfc m)
      ∧ Rle (integralTerm hLd hLn hlip hfc m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
    (hfnn : ∀ x, Rnonneg (f x)) :
    Rnonneg (halfLineIntegral hLd hLn hlip hfc hKd hK0 hb) :=
  Rnonneg_Radd (riemannIntegral_nonneg hLd hLn hlip hfc hfnn)
    (improperIntegral1_nonneg hLd hLn hlip hfc hKd hK0 hb hfnn)

/-- **`∫₀^∞ f ≤ ∫₀^∞ g` for `f ≤ g`** (shared `L`, `K`) — both halves are monotone. -/
theorem halfLineIntegral_le {f g : Real → Real} {L K : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlipf : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcf : ∀ x y, Req x y → Req (f x) (f y))
    (hlipg : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcg : ∀ x y, Req x y → Req (g x) (g y)) (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hbf : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hLd hLn hlipf hfcf m)
      ∧ Rle (integralTerm hLd hLn hlipf hfcf m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
    (hbg : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hLd hLn hlipg hfcg m)
      ∧ Rle (integralTerm hLd hLn hlipg hfcg m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
    (hfg : ∀ x, Rle (f x) (g x)) :
    Rle (halfLineIntegral hLd hLn hlipf hfcf hKd hK0 hbf)
        (halfLineIntegral hLd hLn hlipg hfcg hKd hK0 hbg) :=
  Radd_le_add (riemannIntegral_le hLd hLn hlipf hfcf hlipg hfcg hfg)
    (improperIntegral1_le hLd hLn hlipf hfcf hlipg hfcg hKd hK0 hbf hbg hfg)

/-- **`∫₁^∞ f ≈ ∫₁^∞ g` for `f ≈ g` pointwise** (shared Lipschitz modulus `L` and decay `K`, so both
    sample the same schedule). The integral respects `≈` of integrands — the capability needed to
    rewrite an integrand under a pointwise identity (e.g. the theta modular relation) inside the Mellin
    bridge. Antisymmetry of `improperIntegral1_le` applied both ways. -/
theorem improperIntegral1_congr {f g : Real → Real} {L K : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlipf : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcf : ∀ x y, Req x y → Req (f x) (f y))
    (hlipg : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcg : ∀ x y, Req x y → Req (g x) (g y)) (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hbf : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hLd hLn hlipf hfcf m)
      ∧ Rle (integralTerm hLd hLn hlipf hfcf m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
    (hbg : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hLd hLn hlipg hfcg m)
      ∧ Rle (integralTerm hLd hLn hlipg hfcg m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
    (hfg : ∀ x, Req (f x) (g x)) :
    Req (improperIntegral1 hLd hLn hlipf hfcf hKd hK0 hbf)
        (improperIntegral1 hLd hLn hlipg hfcg hKd hK0 hbg) :=
  Rle_antisymm
    (improperIntegral1_le hLd hLn hlipf hfcf hlipg hfcg hKd hK0 hbf hbg (fun x => Rle_of_Req (hfg x)))
    (improperIntegral1_le hLd hLn hlipg hfcg hlipf hfcf hKd hK0 hbg hbf
      (fun x => Rle_of_Req (Req_symm (hfg x))))

/-- **`∫₀^∞ f ≈ ∫₀^∞ g` for `f ≈ g` pointwise** (shared `L`, `K`) — the integral respects `≈` on the
    whole Mellin domain. -/
theorem halfLineIntegral_congr {f g : Real → Real} {L K : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlipf : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcf : ∀ x y, Req x y → Req (f x) (f y))
    (hlipg : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcg : ∀ x y, Req x y → Req (g x) (g y)) (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hbf : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hLd hLn hlipf hfcf m)
      ∧ Rle (integralTerm hLd hLn hlipf hfcf m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
    (hbg : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hLd hLn hlipg hfcg m)
      ∧ Rle (integralTerm hLd hLn hlipg hfcg m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
    (hfg : ∀ x, Req (f x) (g x)) :
    Req (halfLineIntegral hLd hLn hlipf hfcf hKd hK0 hbf)
        (halfLineIntegral hLd hLn hlipg hfcg hKd hK0 hbg) :=
  Rle_antisymm
    (halfLineIntegral_le hLd hLn hlipf hfcf hlipg hfcg hKd hK0 hbf hbg (fun x => Rle_of_Req (hfg x)))
    (halfLineIntegral_le hLd hLn hlipg hfcg hlipf hfcf hKd hK0 hbg hbf
      (fun x => Rle_of_Req (Req_symm (hfg x))))

end UOR.Bridge.F1Square.Analysis
