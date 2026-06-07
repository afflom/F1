/-
π as a constructive real, via Machin's formula  π = 16·arctan(1/5) − 4·arctan(1/239).

This is the standard constructive *definition* of π: the Machin combination of two arctangents at
rational arguments (Arctan.lean), each with |t| ≤ 1/2 < 1 so the geometric-tail diagonal applies.
Pure Lean 4, no Mathlib, no `sorry`.

`Rpi` is the real; the rational brackets `S₁ ≤ arctanSum ≤ S₀` that pin its value (and give `Pos Rpi`,
needed for `log π`) are developed next.
-/
import F1Square.Analysis.Arctan

namespace UOR.Bridge.F1Square.Analysis

/-- `arctan(1/5)` (radius 1/2). -/
def Ratan5 : Real :=
  Rarctan (⟨1, 5⟩ : Q) (by decide) (ρ := ⟨1, 2⟩) (by decide) (by decide) (by decide) (by decide)

/-- `arctan(1/239)` (radius 1/2). -/
def Ratan239 : Real :=
  Rarctan (⟨1, 239⟩ : Q) (by decide) (ρ := ⟨1, 2⟩) (by decide) (by decide) (by decide) (by decide)

/-- **π**, via Machin: `π = 16·arctan(1/5) − 4·arctan(1/239)`. -/
def Rpi : Real :=
  Rsub (Rmul (ofQ (⟨16, 1⟩ : Q) (by decide)) Ratan5)
    (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) Ratan239)

end UOR.Bridge.F1Square.Analysis
