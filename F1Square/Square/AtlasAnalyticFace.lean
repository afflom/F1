/-
F1 square — **the analytic face of the Atlas crux, integrated**: the Bombieri–Lagarias / witness /
Voros pipeline (`BLPipeline.lean`) joined to the Atlas's geometric crux, so the Atlas formalization
incorporates the analytic side of the prime–archimedean coupling, both directions.

The Atlas reduced closing the crux to the sign of the prime–archimedean coupling
(`genuine_crux_arch_coupling`: `SpectralCrux ⟺ ∀n>0, arith(n)+arch(n) > 0` — the geometric/Lefschetz
face). `BLPipeline.lean` then built the ANALYTIC face constructively: `li_criterion`
(`LiNonneg (genuineLamSeq) ⟺ AllZerosOnLine`), with the constructive witness the forward content and
the Voros dichotomy the reverse, and the off-line geometric seed proven
(`offLine_left_not_inClosedDisk`). This brick records the two faces together.

THE TWO FACES MEET AT RH. The geometric crux is strict positivity of the coupling (`λₙ > 0 ∀n`); the
analytic face is non-negativity tied to the zeros (`λₙ ≥ 0 ∀n ⟺ zeros on line`). Both are equivalent
to RH (Keiper–Li: `λₙ > 0 ∀n ⟺ RH`, and `λₙ ≥ 0 ∀n ⟺ RH`); we state them side by side rather than
chaining strict to non-strict (which would itself pass through RH). The classical inputs
(Bombieri–Lagarias, Voros) are the explicit hypotheses of `LiBridge`, audit-visible; the single open
input is `AllZerosOnLine` = RH. The crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Square.BLPipeline
import F1Square.Square.LefschetzCoupling
import F1Square.Square.Forced

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open UOR.Bridge.F1Square.Li

/-- **THE ATLAS CRUX WITH ITS ANALYTIC FACE WIRED**: for the genuine square, the geometric crux is the
    prime–archimedean coupling sign (`genuine_crux_arch_coupling`), and — given the classical
    `LiBridge` (Bombieri–Lagarias + Voros, explicit hypotheses) — the analytic face is the full
    equivalence `LiNonneg (genuineLamSeq) ⟺ AllZerosOnLine` (`li_criterion`). Both faces are equivalent
    to RH; the single open input is `AllZerosOnLine`. Axiom-clean; crux fields `none`. -/
theorem atlas_coupling_analytic_face (E : StieltjesEta) (L : LiBridge E) :
    (SpectralCrux (genuineSpectralSquare E)
        ↔ ∀ n, 0 < n → Pos (Radd (genuineArithSeq E.eta n) (genuineArchSeq n)))
    ∧ (LiNonneg (genuineLamSeq E.eta) ↔ AllZerosOnLine L.isZero) :=
  ⟨genuine_crux_arch_coupling E, li_criterion E L⟩

/-- **THE ARITHMETIC HODGE INDEX ⟺ RH** — the statement the whole F1-square program aims at, now a
    single connected equivalence. The geometric **Hodge-index non-negativity** of the genuine square
    (`SpectralHodgeNeg`, `−⟨Cₙ,Cₙ⟩ ≥ 0 ∀n`) equals **Li non-negativity** (`genuine_hodgeNeg_iff`,
    the v0.17.0/v0.18.0 bridge), which — given the classical `LiBridge` (Bombieri–Lagarias + Voros) —
    equals **all zeros on the critical line** (`li_criterion`). So the arithmetic Hodge index on
    `𝕊 = Spec ℤ ×_𝔽₁ Spec ℤ` holds **iff RH**, the chain running geometry → Li coefficients → zeros,
    both directions, through the constructive witness. The classical inputs are the explicit `LiBridge`
    hypotheses (audit-visible); the single open input is `AllZerosOnLine` = RH. Axiom-clean; the crux
    fields stay `none`. -/
theorem hodgeIndex_iff_RH (E : StieltjesEta) (L : LiBridge E) :
    SpectralHodgeNeg (genuineSpectralSquare E) ↔ AllZerosOnLine L.isZero :=
  Iff.trans (genuine_hodgeNeg_iff E) (li_criterion E L)

end UOR.Bridge.F1Square.Square
