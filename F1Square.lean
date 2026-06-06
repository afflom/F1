-- F1 square intersection theory — UOR Foundation individual constants.
--
-- Formalization of `Spec ℤ ×_𝔽₁ Spec ℤ` (the arithmetic square `F ⊗_𝔹 F`) and its
-- intersection theory, in the UOR ontology idiom. Companion to the development in
-- `f1_square_intersection_theory.md`.
--
-- EPISTEMIC CONVENTION (matching this library, e.g. Bridge.Homology.boundarySquaredZero):
--   `universallyValid := some true`  ⇒ asserted established (verified / classical theorem)
--   `universallyValid := none`       ⇒ NOT asserted proven in this encoding (open / conditional)
-- The open crux (Hodge index = RH) is encoded with `none`, never `some true`. Results we
-- verified in the runtime (template signature, ample class, parallel-pencil structure) carry
-- their established status; the crux does not. No field asserts an unproven claim as true.

import UOR.Structures
import UOR.Individuals.Op
import UOR.Individuals.Schema
import UOR.Individuals.Convergence
import UOR.Individuals.Division
import UOR.Individuals.Homology

-- The genuine Lean proof layer (real theorems, no Mathlib, no `sorry`): proves the
-- [VERIFIED] / [CLASSICAL] boundary facts of the program. The crux (= RH) is never proved there.
import F1Square.Mechanism
import F1Square.Template
import F1Square.CharOne
import F1Square.Bridge
import F1Square.CycleCounts
import F1Square.Crux
import F1Square.Tropical.Closure
import F1Square.Tropical.Signature
import F1Square.Tropical.Spectrum
import F1Square.Tropical.Siblings
import F1Square.Analysis.Rat
import F1Square.Analysis.RingNF
import F1Square.Analysis.RingTac
import F1Square.Analysis.QOrder
import F1Square.Analysis.Real

open UOR.Primitives

namespace UOR.Bridge.F1Square

-- ===========================================================================
-- §0/§9. The base and the curve (boundary conditions — established/classical).
-- The square's 1-dimensional factor is the Connes–Consani arithmetic-site curve,
-- whose convergence-tower foundation (R→C→H→O) is already in the library
-- (UOR.Kernel.Convergence). The base semiring is characteristic-1 (idempotent).
-- These are carried as references, not re-asserted here.
-- ===========================================================================

-- §2.2 / T3. The intersection-pairing TEMPLATE (product-of-curves form).
-- Established as a CLASSICAL theorem (Hodge index for a projective surface) and
-- verified in the runtime on the sourced form {E₁,E₂,E₃}, E₃²=−2, signature (1,ρ−1).
-- Status: established as a TEMPLATE the concrete square must match (universally valid
-- as a statement about product surfaces over a field).
def intersectionTemplate : UOR.Kernel.Op.Identity UOR.Prims.Standard := {
  lhs := none
  rhs := none
  forAll := none
  verificationDomain := #[.algebraic, .topological]
  verifiedAtLevel := #[]
  universallyValid := some (true)   -- Hodge index IS a theorem for product surfaces over a field
  validityKind := some (.universal)
  validKMin := none
  validKMax := none
}

-- §1.4. The AMPLE class (projectivity/Kähler precondition).
-- Resolved on the template (runtime-verified, gated): H = E₁+E₂ has H²=2>0, positive
-- cone has two components, form negative-definite on H^⊥. NON-automatic per the tropical
-- literature, hence a genuine result — but established ON THE TEMPLATE, not on the concrete
-- square. Status: established on the template (geometric/algebraic).
def ampleClassOnTemplate : UOR.Kernel.Op.Identity UOR.Prims.Standard := {
  lhs := none
  rhs := none
  forAll := none
  verificationDomain := #[.algebraic, .geometric]
  verifiedAtLevel := #[]
  universallyValid := some (true)   -- verified: a class of positive self-intersection exists on the template
  validityKind := some (.universal)
  validKMin := none
  validKMax := none
}

-- §2.3. The concrete square F ⊗_𝔹 F: the parallel-pencil structural finding.
-- In the tropical (log) coordinate the scaling Frobenius Fr_n : x ↦ x + log n is an affine
-- shift, so its graph is PARALLEL to the diagonal: Δ · Γ_n = |det((1,1),(1,1))| = 0. The
-- arithmetic content relocates to the shift length log p. This is a structural property of
-- the concrete bi-tropical model (a candidate realization), derived from the stable-
-- intersection rule. Status: established for the candidate model (topological/geometric);
-- NOT asserted as the canonical F ⊗_𝔹 F (which is still under construction, arXiv 1703.10521).
def parallelPencilStructure : UOR.Kernel.Op.Identity UOR.Prims.Standard := {
  lhs := none
  rhs := none
  forAll := none
  verificationDomain := #[.topological, .geometric]
  verifiedAtLevel := #[]
  universallyValid := none           -- candidate model; not asserted canonical
  validityKind := none
  validKMin := none
  validKMax := none
}

-- §2.3 / §1.5. The shift-length positivity, and its identification with RH.
-- The Weil-type Gram on the pencil, W_ij = Σ_zeros cos(γ·(log p_i − log p_j)), is PSD — but
-- a control shows this PSD-ness holds for ANY real spectral parameters γ, so the positivity
-- is EQUIVALENT to the γ being real (zeros on the critical line) = RH. Hence the shift-length
-- positivity is RH, reached from the tropical direction — NOT a route around it.
-- Status: the positivity is RH. OPEN. Encoded with `none` (the crux), never `some true`.
def shiftLengthPositivity : UOR.Kernel.Op.Identity UOR.Prims.Standard := {
  lhs := none
  rhs := none
  forAll := none
  verificationDomain := #[.analytical, .topological]
  verifiedAtLevel := #[]
  universallyValid := none           -- this positivity IS RH — OPEN, not asserted
  validityKind := none
  validKMin := none
  validKMax := none
}

-- §1.5 / T5. THE CRUX: the Hodge index theorem for 𝕊 (signature (1, ρ−1) on the concrete
-- square), whose negative-definiteness on the primitive complement forces the zeros onto
-- Re(s)=1/2. This is the Riemann Hypothesis. It is established locally/semilocally (Weil
-- positivity at the archimedean place, Connes–Consani) but NOT globally.
-- Status: OPEN — this is RH. universallyValid := none, validityKind := none. Never asserted.
-- (Mirrors the library's own convention: Bridge.Homology.indexBridge carries none.)
def hodgeIndexCrux : UOR.Kernel.Op.Identity UOR.Prims.Standard := {
  lhs := none
  rhs := none
  forAll := none
  verificationDomain := #[.algebraic, .topological, .analytical]
  verifiedAtLevel := #[]
  universallyValid := none           -- = RH. OPEN. The crux is never asserted true.
  validityKind := none
  validKMin := none
  validKMax := none
}

-- ===========================================================================
-- The convergence-tower link: the square's curve factor sits at the F₁/tropical
-- base below the division-algebra tower. The tower TERMINATES at O (dim 8); the
-- next Cayley–Dickson step (sedenions, dim 16) is where division fails — the
-- "no normed division algebra of dim 16" boundary (Op.DA_4). Our sedenion
-- zero-divisor generator (XOR-class, e_8 exempt) characterizes exactly that
-- residual. These library objects are referenced, not re-asserted:
--   UOR.Kernel.Convergence.L3_Self        (O, dim 8 — top of the tower)
--   UOR.Kernel.Division.cayleyDickson_H_to_O  (the last division-preserving doubling)
--   UOR.Kernel.Op.DA_4                    (Adams/Hurwitz: no dim-16 division algebra)
-- ===========================================================================

-- A roll-up record of the construction's status, for the unproven-manifest layer.
-- Every field reflects the HONEST verified status; the crux fields are `none`.
structure F1SquareStatus where
  surfaceConstructed        : Option Bool   -- §1.1: candidate (bi-tropical) — not canonical
  classGroupFinitelyGen     : Option Bool   -- §1.2 / T2: partial (true on template)
  intersectionTemplateValid : Option Bool   -- §2.2 / T3: true (classical, on template)
  ampleClassExists          : Option Bool   -- §1.4: true (verified on template)
  parallelPencilFinding     : Option Bool   -- §2.3: candidate-model structural finding
  hodgeIndexHolds           : Option Bool   -- §1.5 / T5: NONE — this is RH
  deriving Repr

def f1SquareStatus : F1SquareStatus := {
  surfaceConstructed        := none          -- candidate only; canonical F ⊗_𝔹 F open
  classGroupFinitelyGen     := some true      -- on the template
  intersectionTemplateValid := some true      -- classical Hodge index for product surfaces
  ampleClassExists          := some true      -- verified on the template
  parallelPencilFinding     := none           -- candidate model, not asserted canonical
  hodgeIndexHolds           := none           -- = RH, OPEN, never asserted
}

-- ===========================================================================
-- Proof-layer backing (P1–P6). The established (`some true`) fields above are discharged by
-- GENUINE Lean theorems in the proof layer (`F1Square/*.lean`), each audited axiom-clean
-- (no `sorry` / `native_decide` / stray axiom) by `scripts/honesty_audit.sh`:
--   intersectionTemplateValid ← Template.{E1_dot_E2, E3_sq, pair_symm}                 (P1, §2.2)
--   ampleClassExists          ← Template.{H_sq_pos, Hperp_neg_semidef, Hperp_definite} (P1, §1.4)
--   the Hodge/Hasse flip      ← Mechanism.{hodgeType_iff, hasse_q4/q9/q25_*}           (P1, §0.3/§9.1)
--   tropical positivity (R13) ← Mechanism.{tropMult_nonneg, bezout_line_line/conic}    (P2)
--   characteristic 1 (R1,R12) ← CharOne.{tAdd_idem, cycle_reversal_invariant}          (P2)
--   trace counts (R6)         ← CycleCounts.{N1 … N8}  (exact `Bᵐ`)                    (P3b)
--   mechanism + §2.3 control  ← Bridge.{hodge_implies_spectral_bound, control_psd}     (P3)
-- v0.2.0 (finite tropical stack + first analysis brick):
--   tropical Kleene/κ/spectrum ← Tropical.{R2_kleene_idempotent, R3_kappa_perm_invariant,
--                                R4_cycle_spectrum, R9_same_kappa, R10_diff_spectrum, R11_kappa_fiber}
--   sibling carriers (R14–R16) ← Tropical.{R14_kappaBool_perm_invariant, R15_faceted_address,
--                                R16_boolean_facet_degenerate}
--   tropical Hodge signatures ← Tropical.Signature.{parallel_pencil, fan_degenerate, fan_kernel,
--                                bh_two_positive_dirs}
--   exact ℚ analysis brick    ← Analysis.{reduce_6_8, reduce_idem, same_address_iff_eq}
-- v0.3.0 (the analysis substrate: a ℤ ring normalizer + constructive ℝ):
--   ℤ ring normalizer (the    ← Analysis.RingNF.{norm_sound, nf_eq, sq_add, mul_diff, sq_add3} —
--     no-`ring` ceiling lifted)  a reflective canonical polynomial form; soundness ⇒ general identities
--   general ℚ field laws       ← Analysis.{add_comm, mul_comm, mul_assoc, add_assoc, mul_add, add_neg}
--                                (now for ALL rationals, via the normalizer — not just v0.2.0 numerals)
--   constructive ℝ (Bishop)    ← Analysis.{const_regular, Req_refl, Req_symm, ofQ_respects, Pos_half}
-- v0.4.0 (a from-scratch `ring` tactic; ℚ ordered field; ℝ as an ordered additive group):
--   ring_uor (the no-Mathlib    ← Analysis.RingNF.{ring_uor_sq, ring_uor_cube, ring_uor_telescope} —
--     `ring`, built on nf_eq)     a reflective decision procedure: reify → nf_eq → decide
--   ℚ ordered field            ← Analysis.{Qle_trans, Qadd_le_add, Qabs_add_le, Qabs_sub_add4, Qeq_le}
--   ℝ arithmetic (regular)     ← Analysis.{Rneg, Radd} (negation + Bishop addition, regularity proved)
-- The crux is NOT backed and stays `none`:
--   hodgeIndexHolds (= RH)    ← Crux.CruxFor 𝕊 — OPEN. Crux.template_hodgeIndex proves the
--                               property only on the product-of-curves TEMPLATE, never on 𝕊.
-- No arbitrary ceiling: if a genuine, audited, faithful proof of the crux ever lands, this field
-- flips `none → some true` because that is then the truth (program stance, never a defect).
-- ===========================================================================

/-- Elaboration-checked witness that the manifest's established fields rest on real theorems
    (not just annotations): a sample of the proof layer, referenced from the manifest itself. -/
example :
    Template.pair (1, 1, 0) (1, 1, 0) = 2
    ∧ Mechanism.hodgeType 25 10
    ∧ (0 ≤ Bridge.controlForm 3 5 7 11 2 4)
    ∧ CycleCounts.trace (CycleCounts.powM CycleCounts.B 8) = 34
    ∧ Crux.HodgeIndex Crux.templatePolarized :=
  ⟨Template.H_sq, Mechanism.hasse_q25_a10, Bridge.control_psd 3 5 7 11 2 4,
   CycleCounts.N8, Crux.template_hodgeIndex⟩

/-- Elaboration-checked witness binding the v0.2.0 finite tropical stack and the ℚ brick to the
    manifest: Kleene idempotence (R2), κ⊥spectrum (R9/R10), the parallel pencil (§2.3), and the
    canonical ℚ form. -/
example :
    Tropical.mulN 4 (Tropical.starN 4 Tropical.W) (Tropical.starN 4 Tropical.W)
        = Tropical.starN 4 Tropical.W
    ∧ Tropical.kappa 2 Tropical.WA = Tropical.kappa 2 Tropical.WB
    ∧ Tropical.spectrum Tropical.WA Tropical.cyc2 ≠ Tropical.spectrum Tropical.WB Tropical.cyc2
    ∧ Tropical.Signature.det2 1 1 1 1 = 0
    ∧ Analysis.reduce ⟨6, 8⟩ = ⟨3, 4⟩ :=
  ⟨Tropical.R2_kleene_idempotent, Tropical.R9_same_kappa, Tropical.R10_diff_spectrum,
   Tropical.Signature.parallel_pencil, Analysis.reduce_6_8⟩

/-- Elaboration-checked witness binding the v0.3.0 analysis substrate to the manifest: the ℤ ring
    normalizer proves a *general* binomial identity (`(a+b)² = a²+2ab+b²`, here at a sample point),
    the general ℚ commutativity law holds, and the constructive real `½` is positive. -/
example :
    ((3 : Int) + 5) * (3 + 5) = 3 * 3 + 2 * (3 * 5) + 5 * 5
    ∧ Analysis.Qeq (Analysis.mul ⟨2, 3⟩ ⟨4, 5⟩) (Analysis.mul ⟨4, 5⟩ ⟨2, 3⟩)
    ∧ Analysis.Pos Analysis.half :=
  ⟨Analysis.RingNF.sq_add 3 5, Analysis.mul_comm ⟨2, 3⟩ ⟨4, 5⟩, Analysis.Pos_half⟩

/-- Elaboration-checked witness binding the v0.4.0 layer: the from-scratch `ring_uor` proves a general
    integer identity, ℚ addition is monotone (ordered field), and ℝ negation is a pointwise
    involution (ℝ arithmetic). -/
example :
    ((2 : Int) + 3) * (2 + 3) = 2 * 2 + 2 * (2 * 3) + 3 * 3
    ∧ (∀ a b c d : Analysis.Q, Analysis.Qle a b → Analysis.Qle c d →
        Analysis.Qle (Analysis.add a c) (Analysis.add b d))
    ∧ ((Analysis.Rneg (Analysis.Rneg Analysis.half)).seq 0).num = (Analysis.half.seq 0).num :=
  ⟨Analysis.RingNF.ring_uor_sq 2 3, fun _ _ _ _ hab hcd => Analysis.Qadd_le_add hab hcd,
   Analysis.Rneg_Rneg_seq Analysis.half 0⟩

end UOR.Bridge.F1Square
