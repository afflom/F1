/-
F1 square — **the functional-equation reflection, formalized at the Li growth-ratio level**: the
mirror symmetry `ρ ↔ 1−ρ` of the Riemann ξ-zeros, realized as an exact identity on the squared
moduli that govern the Li coefficients — and its consequence for the witness's closed-disk condition.

The completed ζ (the ξ-function) has its zeros symmetric under `s ↦ 1−s`: if `ρ` is a zero, so is
`1−ρ`. THIS FILE turns that symmetry into constructive algebra on the two squared moduli of
`ZeroGeometry` — `cnormSq ρ = |ρ|²` and `csubOneNormSq ρ = |ρ−1|²`, whose ratio `r(ρ) = |ρ−1|²/|ρ|²`
is the squared modulus of the zero's Cayley factor `1−1/ρ` (the per-zero Li growth factor). The exact
reflection identities (no `sqrt`, pure `Real` algebra via `Rneg_sq`/`Rneg_Rsub`):

    cnormSq (1−ρ)        =  csubOneNormSq ρ          (|1−ρ|²   = |ρ−1|²)
    csubOneNormSq (1−ρ)  =  cnormSq ρ                (|(1−ρ)−1|² = |ρ|²),

so the two mirror ratios are RECIPROCAL: `r(ρ)·r(1−ρ) = 1`. THE CONSEQUENCE (`mirror_both_in_disk_iff`):
a zero AND its mirror BOTH lie in the closed unit disk of Cayley factors (`|w|² ≤ 1`, i.e.
`csubOneNormSq ≤ cnormSq`, the witness's per-zero hypothesis in `RHWitness`) **iff** `|ρ−1|² = |ρ|²` —
the Cayley factor of UNIT modulus, which is exactly the on-the-line condition (`liRatio_on_line`).

WHY THIS MATTERS (and what it does NOT do). This is the THEOREM behind the remark in
`rh_witness_onLine`: the reciprocal-ratio constraint means the half-plane witness hypothesis
(`|w|² ≤ 1`) cannot be met by BOTH members of an off-line mirror pair — one factor is forced strictly
OUTSIDE the disk. So the closed-disk witness applied to the full (reflection-closed) zero set forces
every zero onto the line; it does not secretly weaken RH. It also does NOT prove the zeros are in the
disk — WHERE the zeros sit is RH, untouched. The crux fields stay `none`. This is the
functional-equation facet of the Atlas connected to the witness, formalized; novelty: the reflection
identity for the Li growth ratio.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.ZeroGeometry

namespace UOR.Bridge.F1Square.Analysis

/-- The functional-equation **reflection** `ρ ↦ 1−ρ` (real part `1−Re ρ`, imaginary part `−Im ρ`). -/
def Creflect (z : Complex) : Complex := ⟨Rsub one z.re, Rneg z.im⟩

/-- **Reflection identity I**: `|1−ρ|² = |ρ−1|²` — the reflected point's squared modulus is the
    original's `csubOneNormSq`. (`(1−r)² = (r−1)²` by `Rneg_Rsub`+`Rneg_sq`; `(−i)² = i²` by `Rneg_sq`.) -/
theorem cnormSq_Creflect (z : Complex) : Req (cnormSq (Creflect z)) (csubOneNormSq z) := by
  show Req (Radd (Rmul (Rsub one z.re) (Rsub one z.re)) (Rmul (Rneg z.im) (Rneg z.im)))
           (Radd (Rmul (Rsub z.re one) (Rsub z.re one)) (Rmul z.im z.im))
  refine Radd_congr ?_ (Rneg_sq z.im)
  have hneg : Req (Rsub one z.re) (Rneg (Rsub z.re one)) := Req_symm (Rneg_Rsub z.re one)
  exact Req_trans (Rmul_congr hneg hneg) (Rneg_sq (Rsub z.re one))

/-- **Reflection identity II**: `|(1−ρ)−1|² = |ρ|²` — the reflected point's `csubOneNormSq` is the
    original's squared modulus. (`(1−r)−1 = −r`, then `(−r)² = r²` by `Rneg_sq`.) -/
theorem csubOneNormSq_Creflect (z : Complex) : Req (csubOneNormSq (Creflect z)) (cnormSq z) := by
  show Req (Radd (Rmul (Rsub (Rsub one z.re) one) (Rsub (Rsub one z.re) one)) (Rmul (Rneg z.im) (Rneg z.im)))
           (Radd (Rmul z.re z.re) (Rmul z.im z.im))
  refine Radd_congr ?_ (Rneg_sq z.im)
  have e1 : Req (Rsub (Rsub one z.re) one) (Rneg z.re) := by
    show Req (Radd (Radd one (Rneg z.re)) (Rneg one)) (Rneg z.re)
    refine Req_trans (Radd_congr (Radd_comm one (Rneg z.re)) (Req_refl (Rneg one))) ?_
    refine Req_trans (Radd_assoc (Rneg z.re) one (Rneg one)) ?_
    exact Req_trans (Radd_congr (Req_refl (Rneg z.re)) (Radd_neg one)) (Radd_zero (Rneg z.re))
  exact Req_trans (Rmul_congr e1 e1) (Rneg_sq z.re)

/-- A zero is **in the closed Cayley disk** when its growth ratio is `≤ 1`: `|ρ−1|² ≤ |ρ|²` — i.e. its
    Cayley factor `1−1/ρ` has `|w|² ≤ 1` (the per-zero hypothesis of the `RHWitness` half-plane
    witness, in division-free form). By `liRatio_right_of_line`/`liRatio_on_line` this is `Re ρ ≥ ½`. -/
def InClosedDisk (z : Complex) : Prop := Rle (csubOneNormSq z) (cnormSq z)

/-- **THE MIRROR CONSTRAINT (the reflection facet meets the witness).** A zero and its
    functional-equation mirror BOTH lie in the closed Cayley disk **iff** the squared moduli are equal
    — `|ρ−1|² = |ρ|²`, the Cayley factor of UNIT modulus (the on-line condition, `liRatio_on_line`).
    The reciprocal-ratio identities force it: `InClosedDisk (1−ρ)` says `|ρ|² ≤ |ρ−1|²`, the reverse
    inequality, so both together pin equality (`Rle_antisymm`). Hence an OFF-line mirror pair can never
    both satisfy the witness hypothesis — exactly why the half-plane witness, on the
    reflection-closed zero set, forces the line. It does not prove the zeros are there; the crux
    fields stay `none`. -/
theorem mirror_both_in_disk_iff (z : Complex) :
    (InClosedDisk z ∧ InClosedDisk (Creflect z)) ↔ Req (csubOneNormSq z) (cnormSq z) := by
  constructor
  · intro h
    have hrev : Rle (cnormSq z) (csubOneNormSq z) :=
      Rle_trans (Rle_of_Req (Req_symm (csubOneNormSq_Creflect z)))
        (Rle_trans h.2 (Rle_of_Req (cnormSq_Creflect z)))
    exact Rle_antisymm h.1 hrev
  · intro heq
    refine ⟨Rle_of_Req heq, ?_⟩
    exact Rle_trans (Rle_of_Req (csubOneNormSq_Creflect z))
      (Rle_trans (Rle_of_Req (Req_symm heq)) (Rle_of_Req (Req_symm (cnormSq_Creflect z))))

/-- **On the line ⟹ the whole mirror pair is in the disk.** If `Re ρ = ½`, both `ρ` and `1−ρ` have
    Cayley factors in the closed disk (unit modulus). This is the forward content the witness consumes;
    the converse (in-disk ⟹ on line for the pair) is the squared-modulus equality `mirror_both_in_disk_iff`,
    whose discharge for the actual zero set is RH. -/
theorem onLine_mirror_in_disk (z : Complex) (h : OnCriticalLine z) :
    InClosedDisk z ∧ InClosedDisk (Creflect z) :=
  (mirror_both_in_disk_iff z).mpr (liRatio_on_line z h)

end UOR.Bridge.F1Square.Analysis
