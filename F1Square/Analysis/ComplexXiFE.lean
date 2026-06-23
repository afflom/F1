/-
F1 square — Track 1, item 3: **the functional equation `ξ(s) = ξ(1−s)`** of the completed Riemann
ξ, assembled from its constructive part plus the single labelled classical seam.

`ξ(s) = ½·s·(s−1) · π^{−s/2} · Γ(s/2) · ζ(s)` (`ComplexXi.Cxi`).  The functional equation factors
cleanly into two pieces:

  * the **polynomial prefactor symmetry** `½·s·(s−1) ≈ ½·(1−s)·((1−s)−1)` — this is *purely algebraic*
    (`(1−s)·(−s) = (s−1)·s = s·(s−1)`), and is **proven here constructively** (`CxiPoly_symm`) using
    the ℂ-commutative-ring-up-to-`≈` toolkit; and

  * the **completed-zeta functional equation** `π^{−s/2}·Γ(s/2)·ζ(s) ≈ π^{−(1−s)/2}·Γ((1−s)/2)·ζ(1−s)`
    (`Z(s) = Z(1−s)`) — this is the genuine *Poisson-summation / theta-modularity* content of the
    Riemann functional equation. Its constructive discharge requires the Jacobi theta function, its
    modular transform `θ(1/t) = √t·θ(t)`, a Mellin/integral representation, and a real square root —
    none of which exist in this core. We therefore carry it as the **single labelled classical seam**
    `CompletedZetaFE`, exactly as item 5 carries Riemann–von Mangoldt zero-counting and as `bl`/`reg`
    carry the explicit formula. (Honesty = the seam is *named and verifier-checked*, not smuggled.)

Given the seam, `Cxi_functional_equation` derives `ξ(s) ≈ ξ(1−s)` for the *built* ξ — for **arbitrary**
factor values `gammaHalf`, `zeta` (and their `1−s` counterparts), so the result is independent of the
Γ/ζ realization (item 1) and reusable by any future discharge of the seam.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.ComplexXi
import F1Square.Analysis.EulerMaclaurin
import F1Square.Analysis.EtaVariation
import F1Square.Analysis.LiLinearize
import F1Square.Analysis.ComplexArgLeftAdd

namespace UOR.Bridge.F1Square.Analysis

/-- **`1 − s`** as a complex number (`= Cone − s`). The reflection argument of the functional equation. -/
def oneSub (s : Complex) : Complex := Csub Cone s

-- ===========================================================================
-- Small ℂ-ring helpers (double negation; product of two negations).
-- ===========================================================================

/-- **Double negation in ℂ**: `−(−z) ≈ z`. -/
theorem Cneg_Cneg (z : Complex) : Ceq (Cneg (Cneg z)) z :=
  ⟨Rneg_neg z.re, Rneg_neg z.im⟩

/-- **Product of two negations**: `(−a)·(−b) ≈ a·b`. -/
theorem cmul_cneg_cneg (a b : Complex) : Ceq (Cmul (Cneg a) (Cneg b)) (Cmul a b) :=
  Ceq_trans (cmul_cneg (Cneg a) b)
    (Ceq_trans (Cneg_congr (Ceq_symm (Cneg_Cmul_left a b)))
      (Cneg_Cneg (Cmul a b)))

-- ===========================================================================
-- The two affine identities `1 − s ≈ −(s − 1)` and `(1 − s) − 1 ≈ −s`.
-- ===========================================================================

/-- **`1 − s ≈ −(s − 1)`** (componentwise affine identity). -/
theorem oneSub_eq_neg_sub (s : Complex) :
    Ceq (oneSub s) (Cneg (Cadd s (Cneg Cone))) := by
  refine ⟨?_, ?_⟩
  · -- re:  1 + (−s.re)  ≈  −(s.re + (−1))
    exact Req_symm
      (Req_trans (Rneg_Radd s.re (Rneg one))
        (Req_trans (Radd_congr (Req_refl (Rneg s.re)) (Rneg_neg one))
          (Radd_comm (Rneg s.re) one)))
  · -- im:  0 + (−s.im)  ≈  −(s.im + (−0))
    refine Req_trans (Req_trans (Radd_comm zero (Rneg s.im)) (Radd_zero (Rneg s.im))) ?_
    exact Req_symm
      (Req_trans (Rneg_Radd s.im (Rneg zero))
        (Req_trans (Radd_congr (Req_refl (Rneg s.im)) (Rneg_neg zero))
          (Radd_zero (Rneg s.im))))

/-- **`(1 − s) − 1 ≈ −s`** (componentwise affine identity). -/
theorem oneSub_sub_one (s : Complex) :
    Ceq (Cadd (oneSub s) (Cneg Cone)) (Cneg s) := by
  refine ⟨?_, ?_⟩
  · -- re:  (1 + (−s.re)) + (−1)  ≈  −s.re
    refine Req_trans (Radd_congr (Radd_comm one (Rneg s.re)) (Req_refl (Rneg one))) ?_
    refine Req_trans (Radd_assoc (Rneg s.re) one (Rneg one)) ?_
    exact Req_trans (Radd_congr (Req_refl (Rneg s.re)) (Radd_neg one)) (Radd_zero (Rneg s.re))
  · -- im:  (0 + (−s.im)) + (−0)  ≈  −s.im
    refine Req_trans (Radd_congr (Req_refl (Radd zero (Rneg s.im))) Rneg_zero) ?_
    refine Req_trans (Radd_zero (Radd zero (Rneg s.im))) ?_
    exact Req_trans (Radd_comm zero (Rneg s.im)) (Radd_zero (Rneg s.im))

-- ===========================================================================
-- The polynomial-prefactor symmetry (the constructive half of item 3).
-- ===========================================================================

/-- **The polynomial prefactor of ξ is reflection-symmetric**:
    `½·s·(s−1) ≈ ½·(1−s)·((1−s)−1)`, i.e. `CxiPoly s ≈ CxiPoly (1−s)`.

    Algebraically `(1−s)·((1−s)−1) = (1−s)·(−s) = (−(s−1))·(−s) = (s−1)·s = s·(s−1)` — proven here
    constructively with `oneSub_eq_neg_sub`, `oneSub_sub_one`, `cmul_cneg_cneg`, and `Cmul_comm`. -/
theorem CxiPoly_symm (s : Complex) : Ceq (CxiPoly s) (CxiPoly (oneSub s)) := by
  refine Cmul_congr (Ceq_refl _) ?_
  -- Goal:  s·(s−1)  ≈  (1−s)·((1−s)−1)
  refine Ceq_symm ?_
  -- Goal:  (1−s)·((1−s)−1)  ≈  s·(s−1)
  refine Ceq_trans (Cmul_congr (oneSub_eq_neg_sub s) (oneSub_sub_one s)) ?_
  -- Goal:  (−(s−1))·(−s)  ≈  s·(s−1)
  exact Ceq_trans (cmul_cneg_cneg (Cadd s (Cneg Cone)) s) (Cmul_comm (Cadd s (Cneg Cone)) s)

-- ===========================================================================
-- The completed-zeta factor, its regrouping, and the functional equation.
-- ===========================================================================

/-- **The completed-zeta factor** `Z(s) = π^{−s/2}·Γ(s/2)·ζ(s)` of ξ (`Γ(s/2)`, `ζ(s)` supplied as the
    already-built complex values `g`, `z`). The functional equation is `Z(s) = Z(1−s)`. -/
def completedZeta (s g z : Complex) : Complex := Cmul (Cmul (CpiPow s) g) z

/-- **ξ regroups as polynomial × completed-zeta**: `ξ(s) ≈ CxiPoly s · Z(s)` — a pure reassociation of
    the four-factor product `((½s(s−1)·π^{−s/2})·Γ)·ζ`. -/
theorem Cxi_eq_poly_completed (s g z : Complex) :
    Ceq (Cxi s g z) (Cmul (CxiPoly s) (completedZeta s g z)) :=
  Ceq_trans (Cmul_congr (Cmul_assoc (CxiPoly s) (CpiPow s) g) (Ceq_refl z))
    (Cmul_assoc (CxiPoly s) (Cmul (CpiPow s) g) z)

/-- **The completed-zeta functional equation seam** `Z(s) = Z(1−s)` — the genuine Poisson-summation /
    theta-modularity content of the Riemann functional equation, carried as the single labelled
    classical input (its constructive discharge needs the Jacobi theta function, its modular
    transform, a Mellin representation, and a real square root). `gs = Γ(s/2)`, `zs = ζ(s)`,
    `g₁ = Γ((1−s)/2)`, `z₁ = ζ(1−s)`. -/
def CompletedZetaFE (s gs zs g₁ z₁ : Complex) : Prop :=
  Ceq (completedZeta s gs zs) (completedZeta (oneSub s) g₁ z₁)

/-- **The functional equation `ξ(s) = ξ(1−s)`** — assembled from the constructively-proven polynomial
    symmetry (`CxiPoly_symm`) and the single labelled completed-zeta seam (`CompletedZetaFE`). Stated
    for arbitrary factor values, hence independent of the Γ/ζ realization and reusable by any future
    discharge of the seam. -/
theorem Cxi_functional_equation (s gs zs g₁ z₁ : Complex)
    (hfe : CompletedZetaFE s gs zs g₁ z₁) :
    Ceq (Cxi s gs zs) (Cxi (oneSub s) g₁ z₁) :=
  Ceq_trans (Cxi_eq_poly_completed s gs zs)
    (Ceq_trans (Cmul_congr (CxiPoly_symm s) hfe)
      (Ceq_symm (Cxi_eq_poly_completed (oneSub s) g₁ z₁)))

end UOR.Bridge.F1Square.Analysis
