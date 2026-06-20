/-
F1 square — v0.22.0 Track 1, brick (argument axis): **the real-argument value identity**
`sin(arctan t) = t·cos(arctan t)` for a REAL argument `t` (`|t.seq n| ≤ ρ < 1/16`).

The rational-argument value identity `Rsin_arctan_value_eq` (`ArctanODE.lean`) is the heart of
`tan(arctan t₀) = t₀`, but only for a FIXED rational `t₀` (its nested-composition `peval` is at one
point). The complex argument `Carg z = arctan(Im z / Re z)` and its reciprocal extension need the
identity at a REAL ratio. This file lifts it: `RarctanR_value_eq`.

The lift is NOT a naive approximation (that blows up the Lipschitz constant via the approximants'
denominators). Instead it clones the nested-diagonal bridge directly for the real arctan
`RarctanR t`: at each diagonal index the argument is sampled at one deep index `q = t.seq(...)`, and
the nested-composition lemmas (`cos_nested_general` / `sin_nested_general`, already `t₀`-parametric
with `|t₀| ≤ ρ`) apply at that sample. All bounds stay `ρ.den`-based (constant). The diagonal
bridges `Rcos_seq_eq_peval` / `RsinAux_seq_eq_peval` are already `X`-general; the only new work is the
final factor reconciliation `q` (the sin-shift factor) vs `t` (the `Rmul` factor), discharged by
`t`'s regularity.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/
import F1Square.Analysis.ArctanTan

namespace UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 1600000 in
/-- **cos nested-diagonal bound, real argument**: `|(Rcos (RarctanR t)).seq j − peval(cos∘arctan) q
    (2D)| ≤ (U·4ρ.den + 2ρ.den)/(j+1)` where `D = RaltReal_R (RarctanR t) j` and `q = t.seq(Rartanh_R ρ
    D)` is the deep sample. The real-argument clone of `Rcos_arctan_nested`: the diagonal of
    `Rcos (RarctanR t)` samples `t` at the single deep index `Rartanh_R ρ D`, and `cos_nested_general`
    applies at that sample `q` (`|q| ≤ ρ`). -/
theorem Rcos_RarctanR_nested (t : Real) (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (hbt : ∀ n, Qle (Qabs (t.seq n)) ρ)
    (hlt16 : (mul ⟨16, 1⟩ ρ).num.toNat < (mul ⟨16, 1⟩ ρ).den)
    (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hhalf : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ))) (hρ4 : Qle (mul ⟨4, 1⟩ ρ) ⟨1, 1⟩)
    (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (hρ8 : Qle (mul ⟨2, 1⟩ ρ) ⟨1, 1⟩) (j : Nat) :
    Qle (Qabs (Qsub ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).seq j)
        (peval (fcomp cosCoeff arctanCoeff)
          (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt) j)))
          (2 * RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt) j))))
      (⟨((expM_U 1 2).num.toNat : Int) * (4 * (ρ.den : Int)) + 2 * (ρ.den : Int), j + 1⟩ : Q) := by
  have hK1 : 1 ≤ RaltReal_K (RarctanR t ρ hρ0 hρd hlt hbt) := by unfold RaltReal_K; omega
  have hDj : j + 1 ≤ RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt) j := by
    have h4 : 4 * (j + 1) * 1 ≤ 4 * (j + 1) * RaltReal_K (RarctanR t ρ hρ0 hρd hlt hbt) :=
      Nat.mul_le_mul (Nat.le_refl _) hK1
    have hge : 4 * (j + 1) * RaltReal_K (RarctanR t ρ hρ0 hρd hlt hbt)
        ≤ RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt) j := by unfold RaltReal_R; omega
    omega
  obtain ⟨E, hE⟩ : ∃ E, RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt) j = E + 1 :=
    ⟨RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt) j - 1, by omega⟩
  have hrw : Qeq (Qabs (Qsub ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).seq j)
        (peval (fcomp cosCoeff arctanCoeff)
          (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt) j)))
          (2 * RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt) j))))
      (Qabs (Qsub (peval cosCoeff
          ((RarctanR t ρ hρ0 hρd hlt hbt).seq (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt) j))
          (2 * RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt) j))
        (peval (fcomp cosCoeff arctanCoeff)
          (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt) j)))
          (2 * RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt) j)))) :=
    Qabs_Qeq (Qsub_congr (Rcos_seq_eq_peval (RarctanR t ρ hρ0 hρd hlt hbt) j) (Qeq_refl _))
  refine Qle_congr_left
    (Qabs_den_pos (Qsub_den_pos
      (peval_den_pos cosCoeff_den_pos ((RarctanR t ρ hρ0 hρd hlt hbt).den_pos _) _)
      (peval_den_pos (fun k => fcomp_den_pos cosCoeff_den_pos arctanCoeff_den_pos k)
        (t.den_pos _) _)))
    (Qeq_symm hrw) ?_
  rw [hE]
  have hRge : ∀ m, m + 1 ≤ Rartanh_R ρ m := by
    intro m; unfold Rartanh_R
    have hk : 1 ≤ ρ.den * ρ.den + 4 * ρ.den :=
      Nat.le_trans (by omega : 1 ≤ 4 * ρ.den) (Nat.le_add_left _ _)
    calc m + 1 = 1 * (m + 1) := by omega
      _ ≤ (ρ.den * ρ.den + 4 * ρ.den) * (m + 1) := Nat.mul_le_mul_right _ hk
  have hbE : E ≤ Rartanh_R ρ (E + 1) := by have := hRge (E + 1); omega
  exact cos_nested_general (t.seq (Rartanh_R ρ (E + 1))) ρ (t.den_pos _) hρ0 hρd hlt16 (hbt _)
    h2ρ hhalf hρ4 hρ2 hρ8 hlt E (Rartanh_R ρ (E + 1)) j hbE (by omega) (by omega)

set_option maxHeartbeats 2400000 in
/-- **sin nested-diagonal bound, real argument**: `|(Rsin (RarctanR t)).seq n − peval(sin∘arctan) q
    (2D+1)| ≤ C/(n+1)`, `D = RaltReal_R (RarctanR t) (Ridx ... n)`, `q = t.seq(Rartanh_R ρ D)`. The
    real-argument clone of `Rsin_arctan_nested`: the `Rmul` reconciliation (`Rsin = X·RsinAux`, `X`
    sampled at the outer reindex vs `RsinAux` internally at `D`) is `X`-regularity (argument-agnostic);
    the composition core is `sin_nested_general` at the deep sample `q` (`(RarctanR t).seq D` is
    definitionally `arctanSum q (Rartanh_R ρ D)`). -/
theorem Rsin_RarctanR_nested (t : Real) (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (hbt : ∀ n, Qle (Qabs (t.seq n)) ρ)
    (hlt16 : (mul ⟨16, 1⟩ ρ).num.toNat < (mul ⟨16, 1⟩ ρ).den)
    (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hhalf : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ))) (hρ4 : Qle (mul ⟨4, 1⟩ ρ) ⟨1, 1⟩)
    (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (hρ8 : Qle (mul ⟨2, 1⟩ ρ) ⟨1, 1⟩) (n : Nat) :
    Qle (Qabs (Qsub ((Rsin (RarctanR t ρ hρ0 hρd hlt hbt)).seq n)
        (peval (fcomp sinCoeff arctanCoeff)
          (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
          (2 * RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n) + 1))))
      (⟨((expM_U 1 2).num.toNat : Int) * 2
        + (((expM_U 1 2).num.toNat : Int) * (6 * (ρ.den : Int)) + 2 * (ρ.den : Int)), n + 1⟩ : Q) := by
  -- abbreviations (written out): A = RarctanR t, R = Ridx A (RsinAux A) n, D = RaltReal_R A R
  have hRn : n ≤ Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n :=
    Ridx_ge _ _ n
  have hDRge : Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n + 1
      ≤ RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
          (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n) :=
    RaltReal_R_ge _ _
  have hDRn : n ≤ RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
      (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n) := by omega
  -- |RsinAux.seq R| ≤ U  (RsinAux at the outer reindex, inner depth D)
  have hRsinAuxU : Qle (Qabs ((RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)).seq
        (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))
      (⟨((expM_U 1 2).num.toNat : Int), 1⟩ : Q) := by
    rw [RsinAux_seq_eq_altSum]
    exact altSum_arctan_abs_le_U (t.den_pos _) hρ0 hρd
      (hbt (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
        (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
      hρ2 hρ8
      (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
        (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))
      (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
        (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))
  -- |X.seq R − X.seq D| ≤ ⟨2,n+1⟩  (X regularity)
  have hXreg2 : Qle (Qabs (Qsub ((RarctanR t ρ hρ0 hρd hlt hbt).seq
          (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))
        ((RarctanR t ρ hρ0 hρd hlt hbt).seq
          (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))))
      (⟨2, n + 1⟩ : Q) := by
    refine Qle_trans (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))
      ((RarctanR t ρ hρ0 hρd hlt hbt).reg _ _) ?_
    have hb1 : Qle (Qbound (Ridx (RarctanR t ρ hρ0 hρd hlt hbt)
        (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)) (Qbound n) := by
      show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((_ + 1 : Nat) : Int)
      rw [Int.one_mul, Int.one_mul]; exact_mod_cast (Nat.succ_le_succ hRn)
    have hb2 : Qle (Qbound (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
        (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))
        (Qbound n) := by
      show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((_ + 1 : Nat) : Int)
      rw [Int.one_mul, Int.one_mul]; exact_mod_cast (Nat.succ_le_succ hDRn)
    refine Qle_trans (add_den_pos (Qbound_den_pos n) (Qbound_den_pos n)) (Qadd_le_add hb1 hb2) ?_
    apply Qeq_le; simp only [Qeq, add, Qbound]; push_cast; ring_uor
  -- reconciliation leg
  have hrec : Qle (Qabs (Qsub
        (mul ((RarctanR t ρ hρ0 hρd hlt hbt).seq
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))
          ((RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)).seq
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))
        (mul ((RarctanR t ρ hρ0 hρd hlt hbt).seq
            (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
              (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))
          ((RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)).seq
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))))
      (⟨((expM_U 1 2).num.toNat : Int) * 2, n + 1⟩ : Q) := by
    refine Qle_congr_left (Qmul_den_pos
        (Qabs_den_pos (Qsub_den_pos ((RarctanR t ρ hρ0 hρd hlt hbt).den_pos _)
          ((RarctanR t ρ hρ0 hρd hlt hbt).den_pos _)))
        (Qabs_den_pos ((RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _)))
      (Qeq_symm (Qabs_sub_mul_right_eq _ _ _)) ?_
    refine Qle_trans (Qmul_den_pos (Nat.succ_pos n) Nat.one_pos)
      (Qmul_le_mul (Qabs_den_pos (Qsub_den_pos ((RarctanR t ρ hρ0 hρd hlt hbt).den_pos _)
          ((RarctanR t ρ hρ0 hρd hlt hbt).den_pos _))) (Nat.succ_pos n)
        (Qabs_den_pos ((RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _))
        (Qabs_num_nonneg _) (Qabs_num_nonneg _) hXreg2 hRsinAuxU) ?_
    apply Qeq_le; simp only [Qeq, mul]; push_cast; ring_uor
  -- composition leg
  have hsinLeg : Qle (Qabs (Qsub
        (mul ((RarctanR t ρ hρ0 hρd hlt hbt).seq
            (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
              (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))
          ((RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)).seq
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))
        (peval (fcomp sinCoeff arctanCoeff)
          (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
          (2 * RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n) + 1))))
      (⟨((expM_U 1 2).num.toNat : Int) * (6 * (ρ.den : Int)) + 2 * (ρ.den : Int), n + 1⟩ : Q) := by
    refine Qle_congr_left (Qabs_den_pos (Qsub_den_pos
        (peval_den_pos sinCoeff_den_pos ((RarctanR t ρ hρ0 hρd hlt hbt).den_pos _) _)
        (peval_den_pos (fun k => fcomp_den_pos sinCoeff_den_pos arctanCoeff_den_pos k)
          (t.den_pos _) _)))
      (Qabs_Qeq (Qsub_congr (Qeq_symm (RsinAux_seq_eq_peval (RarctanR t ρ hρ0 hρd hlt hbt) _))
        (Qeq_refl _))) ?_
    exact sin_nested_general
      (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
        (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
      ρ (t.den_pos _) hρ0 hρd hlt16 (hbt _) h2ρ hhalf hρ4 hρ2 hρ8 hlt
      (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
        (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))
      (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
        (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))) n
      (by have := Rartanh_R_ge ρ hρd (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)); omega)
      (by omega) (by omega)
  -- triangle through the midpoint mul (X.seq D)(RsinAux.seq R)
  refine Qle_trans (add_den_pos
      (Qabs_den_pos (Qsub_den_pos
        (Qmul_den_pos ((RarctanR t ρ hρ0 hρd hlt hbt).den_pos _)
          ((RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _))
        (Qmul_den_pos ((RarctanR t ρ hρ0 hρd hlt hbt).den_pos _)
          ((RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _))))
      (Qabs_den_pos (Qsub_den_pos
        (Qmul_den_pos ((RarctanR t ρ hρ0 hρd hlt hbt).den_pos _)
          ((RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _))
        (peval_den_pos (fun k => fcomp_den_pos sinCoeff_den_pos arctanCoeff_den_pos k)
          (t.den_pos _) _))))
    (Qabs_sub_triangle (b := mul ((RarctanR t ρ hρ0 hρd hlt hbt).seq
          (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))
        ((RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)).seq
          (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))
      (Qmul_den_pos ((RarctanR t ρ hρ0 hρd hlt hbt).den_pos _)
        ((RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _))
      (Qmul_den_pos ((RarctanR t ρ hρ0 hρd hlt hbt).den_pos _)
        ((RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _))
      (peval_den_pos (fun k => fcomp_den_pos sinCoeff_den_pos arctanCoeff_den_pos k)
        (t.den_pos _) _)) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n)) (Qadd_le_add hrec hsinLeg) ?_
  apply Qeq_le; simp only [Qeq, add]; push_cast; ring_uor

set_option maxHeartbeats 4000000 in
/-- **★ `sin(arctan t) = t·cos(arctan t)` at the value level, REAL argument** `t` (`|t.seq n| ≤ ρ <
    1/16`). The lift of the rational `Rsin_arctan_value_eq` to a real ratio. Triangle through the deep
    sample `q = t.seq(Rartanh_R ρ D)` (`D = RaltReal_R (RarctanR t) (Ridx ... n)`):
    `Rsin(arctan t).seq n →[Rsin_RarctanR_nested] peval(sin∘arctan) q (2D+1) →[shift, exact]
    q·peval(cos∘arctan) q (2D) →[Rcos_RarctanR_nested] q·(Rcos(arctan t)).seq R →[reg] t·cos`. The new
    leg over the rational case is the factor reconciliation `q ↦ t` (the sin-shift factor `q` vs the
    `Rmul` factor `t`), discharged by `t`-regularity and the `|Rcos| ≤ expM_U 1 2` bound. The
    sqrt-free, real-argument `tan∘arctan = id` — the substrate of the reciprocal `Carg`/`Clog` lift. -/
theorem RarctanR_value_eq (t : Real) (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hlt : ρ.num.toNat < ρ.den) (hbt : ∀ n, Qle (Qabs (t.seq n)) ρ)
    (hlt16 : (mul ⟨16, 1⟩ ρ).num.toNat < (mul ⟨16, 1⟩ ρ).den)
    (h2ρ : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ⟨2, 1⟩ ρ)).num)
    (hhalf : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨2, 1⟩ ρ))) (hρ4 : Qle (mul ⟨4, 1⟩ ρ) ⟨1, 1⟩)
    (hρ2 : Qle (⟨1, 2⟩ : Q) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (hρ8 : Qle (mul ⟨2, 1⟩ ρ) ⟨1, 1⟩)
    (hρ1 : Qle ρ ⟨1, 1⟩) :
    Req (Rsin (RarctanR t ρ hρ0 hρd hlt hbt))
      (Rmul t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt))) := by
  refine Req_of_lin_bound
    (C := (expM_U 1 2).num.toNat * 2 + ((expM_U 1 2).num.toNat * (6 * ρ.den) + 2 * ρ.den)
      + ((expM_U 1 2).num.toNat * (4 * ρ.den) + 2 * ρ.den) + (2 + 2 * (expM_U 1 2).num.toNat)) ?_
  intro n
  -- the deep indices (written out): A, R, D, SI = Rartanh_R ρ D, Rc
  have hRn : n ≤ Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n :=
    Ridx_ge _ _ n
  have hDge : Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n + 1
      ≤ RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
          (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n) :=
    RaltReal_R_ge _ _
  have hRcn : n ≤ Ridx t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt)) n := Ridx_ge _ _ n
  have hSIge : ∀ m, m ≤ Rartanh_R ρ m := by
    intro m; have := Rartanh_R_ge ρ hρd m; omega
  -- |q| ≤ 1  (sample bound)
  have hq1 : Qle (Qabs (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
      (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))))
      (⟨1, 1⟩ : Q) := Qle_trans hρd (hbt _) hρ1
  -- L1∘L2: |a0 − a2| ≤ C1/(n+1), a2 = q·peval(cos∘arctan) q (2D)  (Rsin nested + exact shift)
  have hL1 := Rsin_RarctanR_nested t ρ hρ0 hρd hlt hbt hlt16 h2ρ hhalf hρ4 hρ2 hρ8 n
  have hshift := peval_sin_arctan_shift
    (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
      (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
    (t.den_pos _)
    (2 * RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
      (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))
  have hL12 : Qle (Qabs (Qsub ((Rsin (RarctanR t ρ hρ0 hρd hlt hbt)).seq n)
        (mul (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
          (peval (fcomp cosCoeff arctanCoeff)
            (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
              (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
            (2 * RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
              (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))))
      (⟨((expM_U 1 2).num.toNat : Int) * 2
        + (((expM_U 1 2).num.toNat : Int) * (6 * (ρ.den : Int)) + 2 * (ρ.den : Int)), n + 1⟩ : Q) :=
    Qle_congr_left
      (Qabs_den_pos (Qsub_den_pos ((Rsin (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos n)
        (peval_den_pos (fun k => fcomp_den_pos sinCoeff_den_pos arctanCoeff_den_pos k)
          (t.den_pos _) _)))
      (Qabs_Qeq (Qsub_congr (Qeq_refl _) hshift)) hL1
  -- L3: |a2 − a3| ≤ Ccos/(n+1), a3 = q·(Rcos A).seq R   (Rcos nested at j = R, factor |q| ≤ 1)
  have hcosgap := Rcos_RarctanR_nested t ρ hρ0 hρd hlt hbt hlt16 h2ρ hhalf hρ4 hρ2 hρ8
    (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)
  have hL3 : Qle (Qabs (Qsub
        (mul (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
          (peval (fcomp cosCoeff arctanCoeff)
            (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
              (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
            (2 * RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
              (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
        (mul (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
          ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).seq
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))))
      (⟨((expM_U 1 2).num.toNat : Int) * (4 * (ρ.den : Int)) + 2 * (ρ.den : Int), n + 1⟩ : Q) := by
    refine Qle_congr_left
      (Qmul_den_pos (Qabs_den_pos (t.den_pos _)) (Qabs_den_pos (Qsub_den_pos
        (peval_den_pos (fun k => fcomp_den_pos cosCoeff_den_pos arctanCoeff_den_pos k) (t.den_pos _) _)
        ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _))))
      (Qeq_symm (Qabs_sub_mul_left_eq _ _ _)) ?_
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos n))
      (Qmul_le_mul (Qabs_den_pos (t.den_pos _)) Nat.one_pos
        (Qabs_den_pos (Qsub_den_pos
          (peval_den_pos (fun k => fcomp_den_pos cosCoeff_den_pos arctanCoeff_den_pos k) (t.den_pos _) _)
          ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _)))
        (Qabs_num_nonneg _) (Qabs_num_nonneg _) hq1
        (Qle_trans (Nat.succ_pos _) (by rw [Qabs_Qsub_comm]; exact hcosgap)
          (Qrecip_anti (Int.add_nonneg
            (Int.mul_nonneg (Int.ofNat_nonneg _) (Int.mul_nonneg (by decide) (Int.ofNat_nonneg _)))
            (Int.mul_nonneg (by decide) (Int.ofNat_nonneg _))) hRn))) ?_
    apply Qeq_le; simp only [Qeq, mul]; push_cast; ring_uor
  -- L4: |a3 − a4| ≤ (2 + 2U)/(n+1), a4 = (Rmul t (Rcos A)).seq n   (factor + cos reconciliation)
  have hc2bd : Qle (Qabs ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).seq
      (Ridx t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt)) n)))
      (⟨((expM_U 1 2).num.toNat : Int), 1⟩ : Q) := by
    have hb : Qle (Qabs ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).seq
        (Ridx t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt)) n))) (expM_U 1 2) := by
      show Qle (Qabs (altSum ((RarctanR t ρ hρ0 hρd hlt hbt).seq
          (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt)) n))) 0
          (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt)) n)))) (expM_U 1 2)
      exact altSum_abs_le_U (M := 1) ((RarctanR t ρ hρ0 hρd hlt hbt).den_pos _)
        (arctanSum_abs_le_one (t.den_pos _) hρ0 hρd (hbt _) hρ2 hρ8 _) 0 _
    exact Qle_trans (expM_U_den_pos _ _) hb
      (Qle_toNat (expM_U_num_nonneg _ _) (expM_U_den_pos _ _))
  -- regularity of the two reindices used by a3 and a4
  have hcosreg : Qle (Qabs (Qsub ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).seq
        (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))
      ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).seq (Ridx t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
      (⟨2, n + 1⟩ : Q) := by
    refine Qle_trans (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))
      ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).reg _ _) ?_
    have hb1 : Qle (Qbound (Ridx (RarctanR t ρ hρ0 hρd hlt hbt)
        (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)) (Qbound n) := by
      show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((_ + 1 : Nat) : Int)
      rw [Int.one_mul, Int.one_mul]; exact_mod_cast (Nat.succ_le_succ hRn)
    have hb2 : Qle (Qbound (Ridx t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt)) n)) (Qbound n) := by
      show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((_ + 1 : Nat) : Int)
      rw [Int.one_mul, Int.one_mul]; exact_mod_cast (Nat.succ_le_succ hRcn)
    refine Qle_trans (add_den_pos (Qbound_den_pos n) (Qbound_den_pos n)) (Qadd_le_add hb1 hb2) ?_
    apply Qeq_le; simp only [Qeq, add, Qbound]; push_cast; ring_uor
  have hfacreg : Qle (Qabs (Qsub
        (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
          (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
        (t.seq (Ridx t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
      (⟨2, n + 1⟩ : Q) := by
    refine Qle_trans (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)) (t.reg _ _) ?_
    have hb1 : Qle (Qbound (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
        (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
        (Qbound n) := by
      show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((_ + 1 : Nat) : Int)
      rw [Int.one_mul, Int.one_mul]
      have : n ≤ Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
          (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)) :=
        Nat.le_trans (by omega) (hSIge _)
      exact_mod_cast Nat.succ_le_succ this
    have hb2 : Qle (Qbound (Ridx t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt)) n)) (Qbound n) := by
      show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((_ + 1 : Nat) : Int)
      rw [Int.one_mul, Int.one_mul]; exact_mod_cast (Nat.succ_le_succ hRcn)
    refine Qle_trans (add_den_pos (Qbound_den_pos n) (Qbound_den_pos n)) (Qadd_le_add hb1 hb2) ?_
    apply Qeq_le; simp only [Qeq, add, Qbound]; push_cast; ring_uor
  -- L4 product reconciliation: |q·c1 − t'·c2| ≤ |q||c1−c2| + |c2||q−t'| ≤ 2/(n+1) + 2U/(n+1)
  have hL4 : Qle (Qabs (Qsub
        (mul (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
          ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).seq
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))
        ((Rmul t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt))).seq n)))
      (⟨2 + 2 * (expM_U 1 2).num.toNat, n + 1⟩ : Q) := by
    -- a4 = mul (t.seq Rc) ((Rcos A).seq Rc) definitionally
    show Qle (Qabs (Qsub
        (mul (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
          ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).seq
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))
        (mul (t.seq (Ridx t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt)) n))
          ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).seq
            (Ridx t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt)) n))))) _
    -- triangle through mul q c2
    refine Qle_trans (add_den_pos
        (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos (t.den_pos _)
          ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _))
          (Qmul_den_pos (t.den_pos _) ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _))))
        (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos (t.den_pos _)
          ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _))
          (Qmul_den_pos (t.den_pos _) ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _)))))
      (Qabs_sub_triangle
        (b := mul (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
          ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).seq (Ridx t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt)) n)))
        (Qmul_den_pos (t.den_pos _) ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _))
        (Qmul_den_pos (t.den_pos _) ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _))
        (Qmul_den_pos (t.den_pos _) ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _))) ?_
    -- leg A: |q·c1 − q·c2| = |q|·|c1−c2| ≤ 1·(2/(n+1)) ; leg B: |q·c2 − t'·c2| = |q−t'|·|c2| ≤ (2/(n+1))·U
    have hlegA : Qle (Qabs (Qsub
          (mul (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
              (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
            ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).seq
              (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))
          (mul (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
              (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
            ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).seq
              (Ridx t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt)) n)))))
        (⟨2, n + 1⟩ : Q) := by
      refine Qle_congr_left (Qmul_den_pos (Qabs_den_pos (t.den_pos _))
          (Qabs_den_pos (Qsub_den_pos ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _)
            ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _))))
        (Qeq_symm (Qabs_sub_mul_left_eq _ _ _)) ?_
      refine Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos n))
        (Qmul_le_mul (Qabs_den_pos (t.den_pos _)) Nat.one_pos
          (Qabs_den_pos (Qsub_den_pos ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _)
            ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _)))
          (Qabs_num_nonneg _) (Qabs_num_nonneg _) hq1 hcosreg) ?_
      apply Qeq_le; simp only [Qeq, mul]; push_cast; ring_uor
    have hlegB : Qle (Qabs (Qsub
          (mul (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
              (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
            ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).seq
              (Ridx t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt)) n)))
          (mul (t.seq (Ridx t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt)) n))
            ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).seq
              (Ridx t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt)) n)))))
        (⟨2 * (expM_U 1 2).num.toNat, n + 1⟩ : Q) := by
      refine Qle_congr_left (Qmul_den_pos
          (Qabs_den_pos (Qsub_den_pos (t.den_pos _) (t.den_pos _)))
          (Qabs_den_pos ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _)))
        (Qeq_symm (Qabs_sub_mul_right_eq _ _ _)) ?_
      refine Qle_trans (Qmul_den_pos (Nat.succ_pos n) Nat.one_pos)
        (Qmul_le_mul (Qabs_den_pos (Qsub_den_pos (t.den_pos _) (t.den_pos _))) (Nat.succ_pos n)
          (Qabs_den_pos ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _))
          (Qabs_num_nonneg _) (Qabs_num_nonneg _) hfacreg hc2bd) ?_
      apply Qeq_le; simp only [Qeq, mul]; push_cast; ring_uor
    refine Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n)) (Qadd_le_add hlegA hlegB) ?_
    apply Qeq_le; simp only [Qeq, add]; push_cast; ring_uor
  -- assemble: a0 →(L12) a2 →(L3) a3 →(L4) a4   (nested telescoping triangles)
  have ha0d : 0 < ((Rsin (RarctanR t ρ hρ0 hρd hlt hbt)).seq n).den :=
    (Rsin (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos n
  have ha2d : 0 < (mul (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
        (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
      (peval (fcomp cosCoeff arctanCoeff)
        (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
          (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
        (2 * RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
          (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))).den :=
    Qmul_den_pos (t.den_pos _)
      (peval_den_pos (fun k => fcomp_den_pos cosCoeff_den_pos arctanCoeff_den_pos k) (t.den_pos _) _)
  have ha3d : 0 < (mul (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
        (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
      ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).seq
        (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))).den :=
    Qmul_den_pos (t.den_pos _) ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).den_pos _)
  have ha4d : 0 < ((Rmul t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt))).seq n).den :=
    (Rmul t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt))).den_pos n
  have htri2 : Qle (Qabs (Qsub
        (mul (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
          (peval (fcomp cosCoeff arctanCoeff)
            (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
              (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
            (2 * RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
              (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
        ((Rmul t (Rcos (RarctanR t ρ hρ0 hρd hlt hbt))).seq n)))
      (⟨(((expM_U 1 2).num.toNat : Int) * (4 * (ρ.den : Int)) + 2 * (ρ.den : Int))
        + (2 + 2 * (expM_U 1 2).num.toNat), n + 1⟩ : Q) := by
    refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos ha2d ha3d))
        (Qabs_den_pos (Qsub_den_pos ha3d ha4d)))
      (Qabs_sub_triangle (b := mul (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
          ((Rcos (RarctanR t ρ hρ0 hρd hlt hbt)).seq
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n)))
        ha2d ha3d ha4d) ?_
    refine Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n)) (Qadd_le_add hL3 hL4) ?_
    apply Qeq_le; simp only [Qeq, add]; push_cast; ring_uor
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos ha0d ha2d))
      (Qabs_den_pos (Qsub_den_pos ha2d ha4d)))
    (Qabs_sub_triangle (b := mul (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
          (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
        (peval (fcomp cosCoeff arctanCoeff)
          (t.seq (Rartanh_R ρ (RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
          (2 * RaltReal_R (RarctanR t ρ hρ0 hρd hlt hbt)
            (Ridx (RarctanR t ρ hρ0 hρd hlt hbt) (RsinAux (RarctanR t ρ hρ0 hρd hlt hbt)) n))))
      ha0d ha2d ha4d) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n)) (Qadd_le_add hL12 htri2) ?_
  apply Qeq_le; simp only [Qeq, add]; push_cast; ring_uor

end UOR.Bridge.F1Square.Analysis
