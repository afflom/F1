/-
F1 square — v0.22.0 Track 1, brick (complex lift): toward **complex argument additivity**
`arg(zw) = arg z + arg w` (`Carg`), the imaginary half of `Clog` additivity.

Built on the real-argument arctan addition `RarctanR_add_real_via` (`ArctanTan.lean`) and the real
arctan map `vvalReal` (`ArtanhAdd.lean`). The route: the complex-division **ratio identity**
`Im(zw)/Re(zw) ≈ vvalReal(Im z/Re z, Im w/Re w)` (the tangent-addition identity at the value level),
then `RarctanR_congr` + the real addition law. This file collects the cancellation infrastructure and
the `vvalReal` real defining relation that the ratio identity needs.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.ArctanTan
import F1Square.Analysis.RArctanCongr

namespace UOR.Bridge.F1Square.Analysis

/-- **Right cancellation for `Rmul`**: if `a·c ≈ b·c` and `c` is apart from `0` (a positive lower
    bound at index `k`), then `a ≈ b`. Via `(a−b)·c ≈ a·c − b·c ≈ 0` and `Rmul_eq_zero_cancel`. -/
theorem Rmul_right_cancel {a b c : Real} {k : Nat} (hk : Qlt (Qbound k) (c.seq k))
    (h : Req (Rmul a c) (Rmul b c)) : Req a b := by
  have hz : Req (Rmul (Rsub a b) c) zero :=
    Req_trans (Rmul_sub_distrib_right a b c)
      (Req_trans (Rsub_congr h (Req_refl (Rmul b c))) (Radd_neg (Rmul b c)))
  exact Req_of_Rsub_zero_loc (Rmul_eq_zero_cancel hk hz)

/-- **`(a/b)·b ≈ a`** (the division defining relation), for `b` apart from `0`: `Rdiv a b = a·(1/b)`,
    reassociate and cancel `b·(1/b) ≈ 1` (`Rmul_Rinv_self`). -/
theorem Rdiv_mul_cancel {a b : Real} {k : Nat} (hk : Qlt (Qbound k) (b.seq k)) :
    Req (Rmul (Rdiv a b k hk) b) a := by
  show Req (Rmul (Rmul a (Rinv b k hk)) b) a
  refine Req_trans (Rmul_assoc a (Rinv b k hk) b) ?_
  refine Req_trans (Rmul_congr (Req_refl a)
    (Req_trans (Rmul_comm (Rinv b k hk) b) (Rmul_Rinv_self hk))) ?_
  exact Rmul_one a

/-- The pure-`Q` algebra behind `vvalReal_rel`: `A·(1−U) − A·(1−W) = A·(W−U)`. -/
theorem vvalrel_alg (A U W : Q) :
    Qeq (Qsub (mul A (Qsub ⟨1, 1⟩ U)) (mul A (Qsub ⟨1, 1⟩ W))) (mul A (Qsub W U)) := by
  simp only [Qeq, Qsub, mul, add, neg]; push_cast; ring_uor

set_option maxHeartbeats 1200000 in
/-- **The `vvalReal` defining relation (abstract diagonal)**: for a real `V` whose `n`-th approximant
    is `vval(s.seq (f n), t.seq (f n))` (any reindex `f` with `n ≤ f n`), `V·(1 − s·t) ≈ s + t`, given
    `|s.seq m|, |t.seq m|, |vval(s.seq m, t.seq m)| ≤ ρ` (`ρ ≤ 1`, `ρ² ≤ ½`). The rational `vval_rel`
    (`a+b = vval a b·(1−ab)`) holds exactly at each diagonal index; the index mismatch between `V`'s
    argument depth and the `(1−st)` factor's depth is absorbed by regularity (`xreg_n_le`). The
    `vvalReal`-side input to the `arg(zw) = arg z + arg w` ratio identity. -/
theorem vvalReal_rel_via (s t V : Real) (ρ : Q) (f : Nat → Nat) (hf : ∀ n, n ≤ f n)
    (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρ1 : Qle ρ ⟨1, 1⟩) (hρ2 : Qle (mul ρ ρ) ⟨1, 2⟩)
    (hbs : ∀ m, Qle (Qabs (s.seq m)) ρ) (hbt : ∀ m, Qle (Qabs (t.seq m)) ρ)
    (hbw : ∀ m, Qle (Qabs (vval (s.seq m) (t.seq m))) ρ)
    (hVseq : ∀ n, V.seq n = vval (s.seq (f n)) (t.seq (f n))) :
    Req (Rmul V (Rsub one (Rmul s t))) (Radd s t) := by
  refine Req_of_lin_bound (C := 8) ?_
  intro n
  have hJn : n ≤ Ridx V (Rsub one (Rmul s t)) n := Ridx_ge _ _ n
  have hPn : n ≤ f (Ridx V (Rsub one (Rmul s t)) n) := Nat.le_trans hJn (hf _)
  have hLn : n ≤ Ridx s t (2 * Ridx V (Rsub one (Rmul s t)) n + 1) :=
    Nat.le_trans hJn (Nat.le_trans (by omega) (Ridx_ge s t _))
  have hae : (Rmul V (Rsub one (Rmul s t))).seq n
      = mul (vval (s.seq (f (Ridx V (Rsub one (Rmul s t)) n)))
                  (t.seq (f (Ridx V (Rsub one (Rmul s t)) n))))
          (Qsub ⟨1, 1⟩ (mul (s.seq (Ridx s t (2 * Ridx V (Rsub one (Rmul s t)) n + 1)))
                            (t.seq (Ridx s t (2 * Ridx V (Rsub one (Rmul s t)) n + 1))))) := by
    show mul (V.seq (Ridx V (Rsub one (Rmul s t)) n))
        ((Rsub one (Rmul s t)).seq (Ridx V (Rsub one (Rmul s t)) n)) = _
    rw [hVseq]; rfl
  rw [hae, show (Radd s t).seq n = add (s.seq (2 * n + 1)) (t.seq (2 * n + 1)) from rfl]
  generalize hPdef : f (Ridx V (Rsub one (Rmul s t)) n) = P at hPn ⊢
  generalize hLdef : Ridx s t (2 * Ridx V (Rsub one (Rmul s t)) n + 1) = L at hLn ⊢
  -- now: |A·(1 − s_L t_L) − (s_{2n+1} + t_{2n+1})| ≤ 8/(n+1), A = vval(s_P, t_P)
  have hposP : 0 < (s.seq P).den * (t.seq P).den - (s.seq P).num * (t.seq P).num :=
    vval_inner_pos ρ (s.seq P) (t.seq P) hρd hρ0 (s.den_pos P) (t.den_pos P) (hbs P) (hbt P) hρ2
  have hAd : 0 < (vval (s.seq P) (t.seq P)).den := vval_den_pos _ _ hposP
  have hmLd : 0 < (mul (s.seq L) (t.seq L)).den := Qmul_den_pos (s.den_pos L) (t.den_pos L)
  have hmPd : 0 < (mul (s.seq P) (t.seq P)).den := Qmul_den_pos (s.den_pos P) (t.den_pos P)
  have hLd : 0 < (mul (vval (s.seq P) (t.seq P)) (Qsub ⟨1, 1⟩ (mul (s.seq L) (t.seq L)))).den :=
    Qmul_den_pos hAd (Qsub_den_pos (by decide) hmLd)
  have hmid : 0 < (add (s.seq P) (t.seq P)).den := add_den_pos (s.den_pos P) (t.den_pos P)
  have hRd : 0 < (add (s.seq (2 * n + 1)) (t.seq (2 * n + 1))).den :=
    add_den_pos (s.den_pos _) (t.den_pos _)
  -- abbreviation bounds
  have hAle1 : Qle (Qabs (vval (s.seq P) (t.seq P))) (⟨1, 1⟩ : Q) := Qle_trans hρd (hbw P) hρ1
  have hsP1 : Qle (Qabs (s.seq P)) (⟨1, 1⟩ : Q) := Qle_trans hρd (hbs P) hρ1
  have htL1 : Qle (Qabs (t.seq L)) (⟨1, 1⟩ : Q) := Qle_trans hρd (hbt L) hρ1
  -- vval_rel: s_P + t_P = A·(1 − s_P t_P)
  have hvr : Qeq (add (s.seq P) (t.seq P))
      (mul (vval (s.seq P) (t.seq P)) (Qsub ⟨1, 1⟩ (mul (s.seq P) (t.seq P)))) :=
    vval_rel (s.seq P) (t.seq P) hposP
  -- term1: |LHS − (s_P + t_P)| ≤ 4/(n+1)
  have hkey : Qeq (Qsub (mul (vval (s.seq P) (t.seq P)) (Qsub ⟨1, 1⟩ (mul (s.seq L) (t.seq L))))
        (add (s.seq P) (t.seq P)))
      (mul (vval (s.seq P) (t.seq P)) (Qsub (mul (s.seq P) (t.seq P)) (mul (s.seq L) (t.seq L)))) :=
    Qeq_trans (Qsub_den_pos (Qmul_den_pos hAd (Qsub_den_pos (by decide) hmLd))
        (Qmul_den_pos hAd (Qsub_den_pos (by decide) hmPd)))
      (Qsub_congr (Qeq_refl _) hvr)
      (vvalrel_alg (vval (s.seq P) (t.seq P)) (mul (s.seq L) (t.seq L)) (mul (s.seq P) (t.seq P)))
  have hYbound : Qle (Qabs (Qsub (mul (s.seq P) (t.seq P)) (mul (s.seq L) (t.seq L)))) (⟨4, n + 1⟩ : Q) := by
    refine Qle_trans (add_den_pos (Qmul_den_pos (Qabs_den_pos (s.den_pos P))
        (Qabs_den_pos (Qsub_den_pos (t.den_pos P) (t.den_pos L))))
        (Qmul_den_pos (Qabs_den_pos (t.den_pos L)) (Qabs_den_pos (Qsub_den_pos (s.den_pos P) (s.den_pos L)))))
      (Qabs_mul_diff (s.den_pos P) (t.den_pos P) (s.den_pos L) (t.den_pos L)) ?_
    refine Qle_trans (add_den_pos (Qmul_den_pos Nat.one_pos (Nat.succ_pos n))
        (Qmul_den_pos Nat.one_pos (Nat.succ_pos n)))
      (Qadd_le_add
        (Qmul_le_mul (Qabs_den_pos (s.den_pos P)) (by decide)
          (Qabs_den_pos (Qsub_den_pos (t.den_pos P) (t.den_pos L))) (Qabs_num_nonneg _)
          (Qabs_num_nonneg _) hsP1 (xreg_n_le t hPn hLn))
        (Qmul_le_mul (Qabs_den_pos (t.den_pos L)) (by decide)
          (Qabs_den_pos (Qsub_den_pos (s.den_pos P) (s.den_pos L))) (Qabs_num_nonneg _)
          (Qabs_num_nonneg _) htL1 (xreg_n_le s hPn hLn))) ?_
    apply Qeq_le
    show Qeq (add (mul ⟨1, 1⟩ ⟨2, n + 1⟩) (mul ⟨1, 1⟩ ⟨2, n + 1⟩)) (⟨4, n + 1⟩ : Q)
    simp only [Qeq, mul, add]; push_cast; ring_uor
  have hterm1 : Qle (Qabs (Qsub (mul (vval (s.seq P) (t.seq P)) (Qsub ⟨1, 1⟩ (mul (s.seq L) (t.seq L))))
        (add (s.seq P) (t.seq P)))) (⟨4, n + 1⟩ : Q) := by
    refine Qle_trans (Qabs_den_pos (Qmul_den_pos hAd (Qsub_den_pos hmPd hmLd)))
      (Qeq_le (Qabs_Qeq hkey)) ?_
    rw [Qabs_mul]
    refine Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos hmPd hmLd)))
      (Qmul_le_mul_right (Qabs_num_nonneg _) hAle1) ?_
    exact Qle_trans (Qabs_den_pos (Qsub_den_pos hmPd hmLd))
      (Qeq_le (Qone_mul _)) hYbound
  -- term2: |(s_P + t_P) − (s_{2n+1} + t_{2n+1})| ≤ 4/(n+1)
  have hterm2 : Qle (Qabs (Qsub (add (s.seq P) (t.seq P))
        (add (s.seq (2 * n + 1)) (t.seq (2 * n + 1))))) (⟨4, n + 1⟩ : Q) := by
    have h2n : n ≤ 2 * n + 1 := by omega
    refine Qle_trans (add_den_pos
        (Qabs_den_pos (Qsub_den_pos (s.den_pos P) (s.den_pos (2 * n + 1))))
        (Qabs_den_pos (Qsub_den_pos (t.den_pos P) (t.den_pos (2 * n + 1)))))
      (Qabs_sub_add4 (s.den_pos P) (t.den_pos P) (s.den_pos (2 * n + 1)) (t.den_pos (2 * n + 1))) ?_
    refine Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n))
      (Qadd_le_add (xreg_n_le s (i := P) (j := 2 * n + 1) hPn h2n)
        (xreg_n_le t (i := P) (j := 2 * n + 1) hPn h2n)) ?_
    apply Qeq_le; exact Qadd_same_den_loc 2 2 (n + 1)
  -- triangle through (s_P + t_P)
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hLd hmid))
      (Qabs_den_pos (Qsub_den_pos hmid hRd)))
    (Qabs_sub_triangle hLd hmid hRd) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n)) (Qadd_le_add hterm1 hterm2) ?_
  apply Qeq_le; exact Qadd_same_den_loc 4 4 (n + 1)

end UOR.Bridge.F1Square.Analysis
