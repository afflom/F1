/-
F1 square — Track 1, item 5: **the Hadamard product of the completed ξ**,
`ξ(s) = ξ(0)·∏_ρ (1 − s/ρ)`, as a constructive labelled-seam interface (parallel to `BLZeroSum`),
together with the genuine algebraic bridge connecting its factors to the Li/Bombieri–Lagarias
Cayley factors that drive the explicit-formula seam `bl`.

`ξ` is entire of order 1 (item 4), so it has a Hadamard product over its nontrivial zeros `ρ`, paired
`(ρ, 1−ρ)` for convergence. The two pieces of genuine analytic content are:

  * **convergence** of the partial products `∏_{j<M}(1 − s/ρⱼ)` — the *Riemann–von Mangoldt
    zero-counting* `N(T) ~ (T/2π)log(T/2π)`; and
  * the **factorization equality** `ξ(s) = ξ(0)·∏(1 − s/ρ)` itself — the *Hadamard factorization
    theorem* for an order-1 entire function.

Neither is constructible in this core (no complex differentiation / entire-function theory, no real
square root). We package them as the named seams `conv` and `factored` of `HadamardXi`, exactly as
item-3 carries the completed-zeta functional equation and item-5's classical input is the document's
single labelled seam.

The genuine constructive content here is **`hadFactor_one_eq_liRatio`**: the Hadamard factor `1 − s/ρ`
*evaluated at `s = 1`* is exactly the Li/Keiper Cayley factor `liRatio ρ = (ρ−1)·(1/ρ) = 1 − 1/ρ`
(`CayleyMap.lean`) — the `zeroCayley` whose unit modulus on the critical line drives `witnessSum`
positivity and the `bl` zero-sum. So the *same* zero enumeration feeds both the analytic Hadamard
product (item 5) and the arithmetic Li witness sum (the `bl`/`reg` pipeline) — the structural link
between the product side and the explicit formula.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.CayleyMap
import F1Square.Analysis.ComplexSeries
import F1Square.Analysis.ComplexXi
import F1Square.Analysis.EulerMaclaurin
import F1Square.Analysis.LiLinearize
import F1Square.Analysis.RHWitness

namespace UOR.Bridge.F1Square.Analysis

/-- **The Hadamard factor `1 − s/ρ`** of a single nontrivial zero `ρ` (with a positivity witness `k`
    for `|ρ|²`, so `1/ρ = Cinv ρ` exists). The infinite product of these over the zeros is `ξ(s)/ξ(0)`. -/
def hadFactor (s ρ : Complex) (k : Nat) (hk : Qlt (Qbound k) ((CnormSq ρ).seq k)) : Complex :=
  Csub Cone (Cmul s (Cinv ρ k hk))

/-- **The bridge to the Li/Cayley factor**: `hadFactor 1 ρ ≈ liRatio ρ`, i.e. the Hadamard factor at
    `s = 1` is exactly the Cayley factor `1 − 1/ρ` of the Bombieri–Lagarias pipeline.

    `(ρ − 1)·(1/ρ) = ρ·(1/ρ) − 1·(1/ρ) = 1 − 1/ρ = 1 − 1·(1/ρ)` — proven constructively through the
    inverse law `ρ·(1/ρ) = 1` (`Cmul_Cinv`) and the ℂ-ring toolkit. This is what ties item 5's
    product to the `zeroCayley`/`witnessSum`/`bl` machinery: one zero enumeration, two faces. -/
theorem hadFactor_one_eq_liRatio (ρ : Complex) (k : Nat)
    (hk : Qlt (Qbound k) ((CnormSq ρ).seq k)) :
    Ceq (hadFactor Cone ρ k hk) (liRatio ρ k hk) := by
  -- both sides reduce to `1 + (−(1/ρ))`
  have hh : Ceq (hadFactor Cone ρ k hk) (Cadd Cone (Cneg (Cinv ρ k hk))) :=
    Cadd_congr (Ceq_refl Cone)
      (Cneg_congr (Ceq_trans (Cmul_comm Cone (Cinv ρ k hk)) (Cmul_one (Cinv ρ k hk))))
  have hl : Ceq (liRatio ρ k hk) (Cadd Cone (Cneg (Cinv ρ k hk))) :=
    Ceq_trans (Cmul_comm (Cadd ρ (Cneg Cone)) (Cinv ρ k hk))
      (Ceq_trans (Cmul_distrib (Cinv ρ k hk) ρ (Cneg Cone))
        (Cadd_congr
          (Ceq_trans (Cmul_comm (Cinv ρ k hk) ρ) (Cmul_Cinv ρ k hk))
          (Ceq_trans (cmul_cneg (Cinv ρ k hk) Cone) (Cneg_congr (Cmul_one (Cinv ρ k hk))))))
  exact Ceq_trans hh (Ceq_symm hl)

/-- **The Hadamard product representation of ξ** — a constructive labelled-seam interface (parallel to
    `BLZeroSum`). It packages an enumeration `ρ` of the nontrivial zeros, per-zero positivity
    witnesses `hwit`, the value `xi0 = ξ(0)`, and the two analytic seams:

      * `conv`     — the partial Hadamard products converge (Riemann–von Mangoldt zero-counting);
      * `factored` — `ξ(s) = ξ(0)·∏(1 − s/ρ)` (the order-1 Hadamard factorization).

    A `HadamardXi` (any `s`) provides the analytic product side; `hadamard_factor_one_is_cayley` then
    identifies its `s = 1` factors with the `liRatio` Cayley factors of `bl`. -/
structure HadamardXi (s gs zs : Complex) where
  ρ : Nat → Complex
  kwit : Nat → Nat
  hwit : ∀ j, Qlt (Qbound (kwit j)) ((CnormSq (ρ j)).seq (kwit j))
  xi0 : Complex
  conv : CprodConv (fun j => hadFactor s (ρ j) (kwit j) (hwit j))
  factored :
    Ceq (Cxi s gs zs)
      (Cmul xi0 (CprodInf (fun j => hadFactor s (ρ j) (kwit j) (hwit j)) conv))

/-- **The Hadamard factors at `s = 1` are the Li/Cayley factors of `bl`** — for every enumerated zero
    `ρⱼ`, the `j`-th factor of the `s = 1` Hadamard product equals `liRatio ρⱼ`. The explicit
    structural link between the analytic product (item 5) and the arithmetic Li witness sum
    (`zeroCayley`/`witnessSum`/`bl`). -/
theorem hadamard_factor_one_is_cayley {gs zs : Complex} (H : HadamardXi Cone gs zs) (j : Nat) :
    Ceq (hadFactor Cone (H.ρ j) (H.kwit j) (H.hwit j)) (liRatio (H.ρ j) (H.kwit j) (H.hwit j)) :=
  hadFactor_one_eq_liRatio (H.ρ j) (H.kwit j) (H.hwit j)

-- ===========================================================================
-- Item 6 (algebraic link): the Hadamard product's `s = 1` factors feed the
-- `bl` witness sum. `Σ(1 − Re(wⁿ))` is congruent under `≈` of the factors, so
-- the Li witness sum over the `zeroCayley` factors equals the witness sum over
-- the Hadamard factors at `s = 1`. (The zero-FORM of `λₙ` is thus algebraic and
-- built; the remaining `bl` content is only the explicit-formula equality to the
-- arithmetic η-form, which the Hadamard product cannot supply.)
-- ===========================================================================

/-- `Cnpow` is `≈`-congruent in its base: `z ≈ z' ⟹ zⁿ ≈ z'ⁿ`. -/
theorem Cnpow_congr {z z' : Complex} (h : Ceq z z') : ∀ n, Ceq (Cnpow z n) (Cnpow z' n)
  | 0 => Ceq_refl Cone
  | (k + 1) => Cmul_congr h (Cnpow_congr h k)

/-- The per-zero Li witness term `1 − Re(wⁿ)` is `≈`-congruent in `w`. -/
theorem witnessTerm_congr {w w' : Complex} (h : Ceq w w') (n : Nat) :
    Req (Rsub one (Cnpow w n).re) (Rsub one (Cnpow w' n).re) :=
  Rsub_congr (Req_refl one) (Cnpow_congr h n).1

/-- **The witness sum is congruent under pointwise `≈` of mapped factors**: for any index list `is`
    and factor functions `f ≈ g`, `witnessSum (is.map f) n = witnessSum (is.map g) n`. -/
theorem witnessSum_mapidx_congr (f g : Nat → Complex) (h : ∀ k, Ceq (f k) (g k)) (n : Nat) :
    ∀ (is : List Nat), Req (witnessSum (is.map f) n) (witnessSum (is.map g) n)
  | [] => Req_refl _
  | (i :: rest) =>
      Radd_congr (witnessTerm_congr (h i) n) (witnessSum_mapidx_congr f g h n rest)

/-- **The `bl` witness sum is the witness sum of the Hadamard product's `s = 1` factors**: for every
    partial range `M`, the Li witness sum over the Cayley factors `liRatio ρⱼ` (the `zeroCayley` of
    `bl`) equals the witness sum over the Hadamard factors `hadFactor 1 ρⱼ`. With the seam `factored`,
    this is the algebraic shape of item 6 — the analytic product (item 5) and the arithmetic zero-sum
    (`bl`) are the same object, factor by factor. The only content left in `bl` is the explicit-formula
    equality of this zero-form to the η-form `genuineLamSeq`. -/
theorem witnessSum_hadFactor_eq_liRatio {gs zs : Complex} (H : HadamardXi Cone gs zs) (M n : Nat) :
    Req (witnessSum ((List.range M).map
            (fun j => hadFactor Cone (H.ρ j) (H.kwit j) (H.hwit j))) n)
        (witnessSum ((List.range M).map
            (fun j => liRatio (H.ρ j) (H.kwit j) (H.hwit j))) n) :=
  witnessSum_mapidx_congr _ _
    (fun j => hadFactor_one_eq_liRatio (H.ρ j) (H.kwit j) (H.hwit j)) n (List.range M)

end UOR.Bridge.F1Square.Analysis
