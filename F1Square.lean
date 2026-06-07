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
import F1Square.Analysis.Complex
import F1Square.Analysis.Complete
import F1Square.Analysis.Exp
import F1Square.Analysis.ExpGen
import F1Square.Analysis.ExactBounded
import F1Square.Analysis.Zeta
import F1Square.Analysis.ROrder
import F1Square.Analysis.Pow
import F1Square.Analysis.Inv
import F1Square.Analysis.ExpReal
import F1Square.Analysis.CosSin
import F1Square.Analysis.Log
import F1Square.Li

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
  hodgeIndexHolds           : Option Bool   -- §1.5 / T5: NONE — this is RH (geometric face)
  liPositivityHolds         : Option Bool   -- Li's criterion: NONE — this is RH (analytic face)
  deriving Repr

def f1SquareStatus : F1SquareStatus := {
  surfaceConstructed        := none          -- candidate only; canonical F ⊗_𝔹 F open
  classGroupFinitelyGen     := some true      -- on the template
  intersectionTemplateValid := some true      -- classical Hodge index for product surfaces
  ampleClassExists          := some true      -- verified on the template
  parallelPencilFinding     := none           -- candidate model, not asserted canonical
  hodgeIndexHolds           := none           -- = RH (geometric face), OPEN, never asserted
  liPositivityHolds         := none           -- = RH (analytic face: λₙ > 0 ∀n, Li 1997), OPEN, never asserted
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
-- v0.5.0 (ℝ's Bishop equality is an equivalence; ℝ multiplication; ℂ = ℝ×ℝ with all four operations):
--   ℚ Archimedean + ≈-trans    ← Analysis.{Qarch, Qabs_sub_triangle, Req_trans} (the limiting argument)
--   ℚ multiplication/order     ← Analysis.{Qabs_mul, Qmul_le_mul, Qabs_mul_diff} (consumed by Rmul)
--   ℝ field arithmetic         ← Analysis.{Radd_comm, Radd_neg, Rmul, Rmul_comm} (add/neg/mul, regular)
--   ≈-congruence (well-defined)← Analysis.{Rneg_congr, Radd_congr, Rsub_congr} (operations respect ≈)
--   ℂ = ℝ×ℝ (comm. mult.)      ← Analysis.{Ceq_trans, Cadd_comm, Cadd_neg, Cmul, Cmul_comm}
-- v0.6.0 (ℝ and ℂ are commutative rings up to ≈; ℝ multiplication well-defined on the setoid):
--   Archimedean engine         ← Analysis.{Qarch_gen, Req_of_lin_bound} (linear bound C/(n+1) ⟹ ≈)
--   product-gap engine         ← Analysis.{Rmul_gap, Rgap_le, Rcross_le, canon_bound_mul}
--   ℝ multiplication well-def.  ← Analysis.Rmul_congr (the v0.5.0-deferred congruence, now proved)
--   ℝ commutative ring         ← Analysis.{Rmul_assoc, Rmul_distrib, Rmul_one, Radd_assoc, Rmul_zero}
--   ℂ commutative ring         ← Analysis.{Cadd_assoc, Cmul_one, Cmul_distrib, Cmul_assoc}
-- v0.7.0 (Cauchy completeness of ℝ — every regular sequence of reals converges):
--   limit construction         ← Analysis.{RReg, Rlim, RlimSeq_regular} (Bishop diagonal, reindex 4n+3)
--   convergence with rate      ← Analysis.Rlim_tendsTo (X k → lim X within 1/(k+1))
--   uniqueness of limits       ← Analysis.RTendsTo_unique (Archimedean + linear-bound criterion)
-- v0.8.0 (the first transcendental: Euler's number e via the exponential series):
--   factorial + partial sums   ← Analysis.{fct, eSum} (Σ 1/i!, from scratch — core has no factorial)
--   rigorous error bound       ← Analysis.ediff_bound (telescoping: U(n)=S(n)+2/(n+1)! decreasing)
--   e as a constructive real   ← Analysis.{e, eSeq_regular, e_pos} (the series value; positive)
-- v0.9.0 (the general exponential exp(q) on the rational interval [0,1]):
--   rational powers from scratch ← Analysis.{qpow, qpow_le_one} (qⁱ; for q∈[0,1] every qⁱ ≤ 1)
--   termwise domination bridge   ← Analysis.{expTerm_le, expdiff_dom} (qⁱ/i! ≤ 1/i!, gap dominated)
--   rigorous error bound (reused) ← Analysis.expdiff_bound (same 2/(a+1)! tail as e, by domination)
--   exp(q) as a constructive real ← Analysis.{Rexp, expSeq_regular}; anchors Rexp_zero (exp 0 ≈ 1),
--                                   Rexp_one_pos (exp 1 > 0), Rexp_one_eq_e (exp 1 ≈ e — ties to v0.8.0)
-- v0.10.0 (the λₙ / RH PROOF BOUNDARY — locked faithfully before ζ is built):
--   Bishop ℝ ≥ 0 / > 0         ← Li.{Rnonneg, Rnonneg_zero, Rnonneg_one, Pos_one}
--   Li-positivity property     ← Li.{LiPositive (strict, ζ-specific Li 1997), LiNonneg (BL 1999 form)};
--                                template_liPositive proves it for the constant-1 sequence (genuine)
--   the finite-check guard     ← Li.liPositive_iff_all_upTo (LiPositive = ∀N, LiPositiveUpTo; no
--                                finite N / `decide` reaches the universal — the first ~10⁵ λₙ are
--                                numerically positive yet that is NOT a proof)
--   ζ-layer substrate (interfaces, never asserted for the genuine λ) ← Li.{LiDecomposition (BL),
--                                ExplicitFormulaTrace (Weil 1952/Connes 1999), LiAgreesWith}
--   ζ(s) as an exact-bounded object ← Analysis.{zeta (Σ1/iˢ, integer s≥2), zeta_pos, zetadiff_bound
--                                (the rigorous rational tail certificate)}; λₙ typed as
--                                Nat → ExactBoundedReal (Analysis.ExactBounded). HONEST SCOPE: ζ here
--                                is the convergent regime Re(s)>1 (no zeros, not the critical strip);
--                                the genuine λₙ values need analytic continuation + log (deferred).
-- v0.11.0 (the order ≤ on ℝ — the foundation for the transcendentals):
--   Bishop order ≤            ← Analysis.{Rle (xₙ ≤ yₙ + 2/(n+1)), Rle_refl, Rle_of_Req, Rle_antisymm,
--                               Rle_trans (Archimedean), Rle_zero_of_Rnonneg}; Rnonneg canonicalized here
--   ℚ signed-bound helpers    ← Analysis.{Qle_self_Qabs, Qabs_le_of_both, Qle_add_of_Qabs_sub,
--                               Qsub_le_of_le_add}
-- v0.12.0 (ℝ as a constructive field with powers, and `exp` on all of ℝ):
--   real field/powers          ← Analysis.{Rpow (iterated Rmul), Rpow_one, Rpow_congr; Rinv (1/x via
--                               a positivity witness, full Bishop regularity), Rdiv}
--   exp on ℝ (diagonal)        ← Analysis.{RexpReal = ⟨S_{x_{Rj}}(Rj)⟩ₙ, RexpReal_regular}, built from the
--                               rational bounds expSum_trunc_bound (geometric tail), expSum_Lip_le +
--                               LipS_le_U (Lipschitz), fct_ge_geom (factorial growth) — all axiom-clean
-- v0.13.0 (the transcendentals on ℝ: cos, sin, and log on all positive reals):
--   cos / sin on ℝ             ← Analysis.{Rcos = RaltReal x 0, Rsin = Rmul x (RaltReal x 1)}, the
--                               alternating series with base −q² dominated by exp(M²) (altSum_trunc_bound,
--                               altSum_Lip_le, fct_mono)
--   log on positive reals      ← Analysis.{Rlog x M = 2·artanh((x−1)/(x+1)) for 1/M ≤ x ≤ M}, built on the
--                               complete artanh diagonal Rartanh (artanh on every [−ρ,ρ], ρ<1), via the
--                               geometric tail (artSum_trunc), artanh Lipschitz (artSum_Lip_le), the general
--                               Bernoulli reindex (qpow_geom_bound), and the t-map q↦(q−1)/(q+1) with its
--                               cleared difference identity (tmap_diff_cleared), Lipschitz (tmap_lipschitz),
--                               and range bound (tmap_abs_le) — all axiom-clean, no `sorry`
-- The crux is NOT backed and stays `none` (BOTH faces, same RH):
--   hodgeIndexHolds (= RH, geometric) ← Crux.CruxFor 𝕊 — OPEN. Crux.template_hodgeIndex proves the
--                               property only on the product-of-curves TEMPLATE, never on 𝕊.
--   liPositivityHolds (= RH, analytic) ← Li.LiCrux λ for the unconstructed genuine Li sequence λ —
--                               OPEN. Li.template_liPositive proves the property only for a constant
--                               sequence, never for λ; LiPositive λ ⟺ RH is [CLASSICAL] (Li 1997).
-- No arbitrary ceiling: if a genuine, audited, faithful proof of the crux ever lands, these fields
-- flip `none → some true` because that is then the truth (program stance, never a defect).
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

/-- Elaboration-checked witness binding the v0.5.0 layer: Bishop equality on ℝ is transitive (an
    equivalence), ℝ multiplication is commutative up to `≈`, and ℂ multiplication is commutative
    up to `≈` (via the operation-congruences). -/
example :
    (∀ x y z : Analysis.Real, Analysis.Req x y → Analysis.Req y z → Analysis.Req x z)
    ∧ (∀ x y : Analysis.Real, Analysis.Req (Analysis.Rmul x y) (Analysis.Rmul y x))
    ∧ (∀ z w : Analysis.Complex, Analysis.Ceq (Analysis.Cmul z w) (Analysis.Cmul w z)) :=
  ⟨fun _ _ _ => Analysis.Req_trans, Analysis.Rmul_comm, Analysis.Cmul_comm⟩

/-- Elaboration-checked witness binding the v0.6.0 layer: ℝ multiplication is well-defined on the
    `≈`-setoid (the v0.5.0-deferred congruence), ℝ multiplication is associative up to `≈`, and ℂ
    multiplication is both associative and distributive up to `≈` — so ℂ is a commutative ring. -/
example :
    (∀ x x' y y' : Analysis.Real, Analysis.Req x x' → Analysis.Req y y' →
        Analysis.Req (Analysis.Rmul x y) (Analysis.Rmul x' y'))
    ∧ (∀ x y z : Analysis.Real,
        Analysis.Req (Analysis.Rmul (Analysis.Rmul x y) z) (Analysis.Rmul x (Analysis.Rmul y z)))
    ∧ (∀ z w v : Analysis.Complex,
        Analysis.Ceq (Analysis.Cmul (Analysis.Cmul z w) v) (Analysis.Cmul z (Analysis.Cmul w v)))
    ∧ (∀ z w v : Analysis.Complex,
        Analysis.Ceq (Analysis.Cmul z (Analysis.Cadd w v))
                     (Analysis.Cadd (Analysis.Cmul z w) (Analysis.Cmul z v))) :=
  ⟨fun _ _ _ _ => Analysis.Rmul_congr, Analysis.Rmul_assoc, Analysis.Cmul_assoc, Analysis.Cmul_distrib⟩

/-- Elaboration-checked witness binding the v0.7.0 layer: ℝ is Cauchy complete — every regular
    sequence of reals converges to its diagonal limit (with an explicit rate), and limits are unique
    up to `≈`. -/
example :
    (∀ (X : Nat → Analysis.Real) (h : Analysis.RReg X), Analysis.RTendsTo X (Analysis.Rlim X h))
    ∧ (∀ (X : Nat → Analysis.Real) (L L' : Analysis.Real),
        Analysis.RTendsTo X L → Analysis.RTendsTo X L' → Analysis.Req L L') :=
  ⟨Analysis.Rlim_tendsTo, fun _ _ _ => Analysis.RTendsTo_unique⟩

/-- Elaboration-checked witness binding the v0.8.0 layer: Euler's number `e` is a genuine constructive
    real (positive), and the exponential series carries a rigorous rational error bound on its partial
    sums (`S(b) − S(a) ≤ 2/(a+1)!` for `a ≤ b`) — the convergent-series-with-error-bound pattern. -/
example :
    Analysis.Pos Analysis.e
    ∧ (∀ a b : Nat, a ≤ b →
        Analysis.Qle (Analysis.Qsub (Analysis.eSum b) (Analysis.eSum a)) ⟨2, Analysis.fct (a + 1)⟩) :=
  ⟨Analysis.e_pos, fun _ _ h => Analysis.ediff_bound h⟩

/-- Elaboration-checked witness binding the v0.9.0 layer: the general exponential `exp(q)` on the
    rational interval `[0,1]` is a genuine constructive real — it agrees with `1` at `q = 0`
    (`exp 0 ≈ 1`), is positive at `q = 1` (`exp 1 > 0`), and its partial sums carry the *same*
    rigorous rational error bound as `e` via termwise domination (`qⁱ/i! ≤ 1/i!` for `q ∈ [0,1]`). -/
example :
    Analysis.Req (Analysis.Rexp ⟨0, 1⟩ (by decide) (by decide) (by decide)) Analysis.one
    ∧ Analysis.Req (Analysis.Rexp ⟨1, 1⟩ (by decide) (by decide) (by decide)) Analysis.e
    ∧ Analysis.Pos (Analysis.Rexp ⟨1, 1⟩ (by decide) (by decide) (by decide))
    ∧ (∀ (q : Analysis.Q) (hq0 : 0 ≤ q.num) (hqd : 0 < q.den) (hq1 : Analysis.Qle q ⟨1, 1⟩)
        (a b : Nat), a ≤ b →
        Analysis.Qle (Analysis.Qsub (Analysis.expSum q b) (Analysis.expSum q a))
          ⟨2, Analysis.fct (a + 1)⟩) :=
  ⟨Analysis.Rexp_zero, Analysis.Rexp_one_eq_e, Analysis.Rexp_one_pos,
   fun _ hq0 hqd hq1 _ _ h => Analysis.expdiff_bound hq0 hqd hq1 h⟩

/-- Elaboration-checked witness binding the v0.10.0 layer — the λₙ / RH proof boundary, locked
    faithfully. The Li-positivity PROPERTY is genuine (the constant-`1` sequence satisfies it), it is
    *exactly* the conjunction of all finite truncations (so no finite check is a proof), and the
    Bombieri–Lagarias decomposition is a genuine interface — while the CRUX, `LiCrux` for the
    unconstructed genuine Li sequence of ζ, is never asserted (`liPositivityHolds = none`, = RH). -/
example :
    Li.LiPositive (fun _ => Analysis.one)
    ∧ (∀ lam : Nat → Analysis.ExactBoundedReal, Li.LiPositive lam ↔ ∀ N, Li.LiPositiveUpTo lam N)
    ∧ (∀ lam : Nat → Analysis.ExactBoundedReal, Li.LiDecomposition lam lam (fun _ => Analysis.zero))
    ∧ f1SquareStatus.liPositivityHolds = none :=
  ⟨Li.template_liPositive, Li.liPositive_iff_all_upTo, Li.liDecomposition_genuine, rfl⟩

/-- Elaboration-checked witness that ζ ships as a genuine **exact-bounded object**: for every integer
    `s ≥ 2`, `ζ(s) = Σ 1/iˢ` is a constructive real that is positive (`zeta_pos`) and whose partial
    sums carry the rigorous rational error bound `S(b) − S(a) ≤ 1/(a+1)` (`zetadiff_bound`) — its
    precision certificate. (This is ζ in the convergent regime `Re(s) > 1`, where it has no zeros; the
    analytic continuation to the critical strip — where RH lives — is not built.) -/
example :
    (∀ (s : Nat) (hs : 2 ≤ s), Analysis.Pos (Analysis.zeta s hs))
    ∧ (∀ (s : Nat) (_hs : 2 ≤ s) (a b : Nat), a ≤ b →
        Analysis.Qle (Analysis.Qsub (Analysis.zetaSum s b) (Analysis.zetaSum s a)) ⟨1, a + 1⟩)
    ∧ (∀ (x : Analysis.ExactBoundedReal) (n : Nat),
        Analysis.Qeq (Analysis.Qsub (Analysis.upperB x n) (Analysis.lowerB x n)) ⟨2, n + 1⟩) :=
  ⟨Analysis.zeta_pos, fun s hs _ _ h => Analysis.zetadiff_bound s hs h, Analysis.enclosure_width⟩

/-- Elaboration-checked witness binding the v0.11.0 layer: the order `≤` on ℝ is a genuine order —
    reflexive, antisymmetric up to `≈` (`x ≤ y` and `y ≤ x` give `x ≈ y`), transitive (the genuine
    Archimedean limiting step), and refined by `≈`; and Bishop non-negativity `x ≥ 0` entails `0 ≤ x`.
    This is the foundation the transcendentals (`exp`, `cos`/`sin`, `log`) build on. -/
example :
    (∀ x : Analysis.Real, Analysis.Rle x x)
    ∧ (∀ x y : Analysis.Real, Analysis.Rle x y → Analysis.Rle y x → Analysis.Req x y)
    ∧ (∀ x y z : Analysis.Real, Analysis.Rle x y → Analysis.Rle y z → Analysis.Rle x z)
    ∧ (∀ x : Analysis.Real, Analysis.Rnonneg x → Analysis.Rle Analysis.zero x) :=
  ⟨Analysis.Rle_refl, fun _ _ => Analysis.Rle_antisymm, fun _ _ _ => Analysis.Rle_trans,
   fun _ => Analysis.Rle_zero_of_Rnonneg⟩

/-- Elaboration-checked witness binding the v0.12.0 layer: real powers satisfy `x¹ ≈ x`, and the
    everywhere-defined `exp` on ℝ is a genuinely constructed real — its diagonal sequence is
    Bishop-regular, with the explicit rigorous gap bound `|expₓ(j) − expₓ(k)| ≤ 1/(j+1)` for `j ≤ k`
    (truncation + Lipschitz, both axiom-clean). -/
example :
    (∀ x : Analysis.Real, Analysis.Req (Analysis.Rpow x 1) x)
    ∧ (∀ x : Analysis.Real, Analysis.IsRegular (Analysis.RexpReal_seq x))
    ∧ (∀ x : Analysis.Real, ∀ j k : Nat, j ≤ k →
        Analysis.Qle (Analysis.Qabs (Analysis.Qsub (Analysis.RexpReal_seq x j)
          (Analysis.RexpReal_seq x k))) (Analysis.Qbound j)) :=
  ⟨Analysis.Rpow_one, Analysis.RexpReal_regular, fun _ _ _ h => Analysis.RexpReal_diag_le _ h⟩

/-- Elaboration-checked witness binding the v0.13.0 transcendentals: `cos` and `sin` (the alternating
    diagonal `RaltReal x off`) are genuinely constructed reals — their diagonal sequences are
    Bishop-regular; and `log` on every positive, `[1/M, M]`-bounded real (`Rlog x M`) is a genuinely
    constructed real, its diagonal `t.seq n = (x_{2(n+1)}−1)/(x_{2(n+1)}+1)` Bishop-regular. All
    axiom-clean, no `sorry`; the t-map range bound keeps the artanh argument inside `[−ρ,ρ]`, `ρ<1`. -/
example :
    (∀ x : Analysis.Real, ∀ off : Nat, Analysis.IsRegular (Analysis.RaltReal_seq x off))
    ∧ (∀ x : Analysis.Real, (∀ n, 0 < (x.seq n).num) → Analysis.IsRegular (Analysis.Rlog_seq x)) :=
  ⟨Analysis.RaltReal_regular, Analysis.Rlog_regular⟩

end UOR.Bridge.F1Square
