/-
F1 square — Track 1, item 0 substrate: the **real-level artanh bracket** `v ≤ artanh(v) ≤ v/(1−v²)`
for a constant rational argument `v ∈ [0, 1)`.

The constructive `Rartanh` (`Log.lean`) at a constant rational `v` (`RartanhAtQ`, `ExpLog.lean`) has the
fixed-rational diagonal `artSum v (Rartanh_R ρ j)` (`RartanhAtQ_seq`). Both rational endpoints already
exist at the partial-sum level — the lower bound `v ≤ artSum v N` (`artSum_ge_arg`) and the cleared
geometric upper bound `artSum v N · (1−v²) ≤ v` (`artSum_le_geo`, since `1/(2k+1) ≤ 1`). This lifts them
to the Bishop real, giving the two-sided bound directly on `RartanhAtQ`. The upper endpoint cancels the
positive factor `1−v²` with `Qmul_le_cancel_right`, exactly the `two_artSum_le` pattern but for an
arbitrary rational `v`.

This is the substrate for the one-sided log bound `log u ≤ u−1` (`= 2·artanh(tmap u) ≤ u−1`), the
modulus the `RrpowPos` Lipschitz / general `t^{σ−1}` Mellin integrand needs.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.RealPow
import F1Square.Analysis.RexpLogRat

namespace UOR.Bridge.F1Square.Analysis

/-- **Real artanh lower bound** `v ≤ artanh(v)` for a constant rational `v ≥ 0`. Each diagonal
    `artSum v N ≥ v` (`artSum_ge_arg`), lifted to the Bishop `Rle` (the `⟨2,n+1⟩` slack is `≥ 0`). -/
theorem RartanhAtQ_ge (v : Q) (hvd : 0 < v.den) (hv0 : 0 ≤ v.num) (ρ : Q)
    (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hlt : ρ.num.toNat < ρ.den) (hb : Qle (Qabs v) ρ) :
    Rle (ofQ v hvd) (RartanhAtQ v hvd ρ hρ0 hρd hlt hb) := by
  intro n
  show Qle v (add (artSum v (Rartanh_R ρ n)) ⟨2, n + 1⟩)
  exact Qle_trans (artSum_den_pos hvd _) (artSum_ge_arg hv0 hvd _)
    (Qle_self_add (by show (0 : Int) ≤ 2; decide))

/-- **Real artanh upper bound** `artanh(v) ≤ v/(1−v²)` for a constant rational `v ∈ [0,1)` (encoded by
    `0 < (1−v²).num`). Each diagonal `artSum v N ≤ v·(1−v²)⁻¹` from the cleared bound `artSum v N·(1−v²) ≤ v`
    (`artSum_le_geo`) cancelling the positive `1−v²` (`Qmul_le_cancel_right`); lifted to the Bishop `Rle`. -/
theorem RartanhAtQ_le (v : Q) (hvd : 0 < v.den) (hv0 : 0 ≤ v.num) (ρ : Q)
    (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hlt : ρ.num.toNat < ρ.den) (hb : Qle (Qabs v) ρ)
    (hWn : 0 < (Qsub (⟨1, 1⟩ : Q) (mul v v)).num) :
    Rle (RartanhAtQ v hvd ρ hρ0 hρd hlt hb)
      (ofQ (mul v (Qinv (Qsub (⟨1, 1⟩ : Q) (mul v v))))
        (Qmul_den_pos hvd (Qinv_den_pos hWn))) := by
  -- abbreviations
  have hWd : 0 < (Qsub (⟨1, 1⟩ : Q) (mul v v)).den := Qsub_den_pos Nat.one_pos (Qmul_den_pos hvd hvd)
  -- the cleared closed form `v·W⁻¹·W = v` (general `W` with `0 < W.num`, so `W` stays opaque)
  have hcancel : ∀ (W : Q), 0 < W.num → Qeq v (mul (mul v (Qinv W)) W) := by
    intro W hWn'
    have ht : ((W.num.toNat : Nat) : Int) = W.num := Int.toNat_of_nonneg (Int.le_of_lt hWn')
    show v.num * (((v.den * W.num.toNat) * W.den : Nat) : Int)
        = ((v.num * (W.den : Int)) * W.num) * (v.den : Int)
    push_cast [ht]
    ring_uor
  -- per-index `artSum v N ≤ v·(1−v²)⁻¹`
  have key : ∀ N, Qle (artSum v N) (mul v (Qinv (Qsub (⟨1, 1⟩ : Q) (mul v v)))) := by
    intro N
    have hgeo := artSum_le_geo hv0 hvd (Int.le_of_lt hWn) N
    refine Qmul_le_cancel_right hWn hWd ?_
    exact Qle_trans hvd hgeo (Qeq_le (hcancel (Qsub (⟨1, 1⟩ : Q) (mul v v)) hWn))
  intro n
  show Qle (artSum v (Rartanh_R ρ n))
    (add (mul v (Qinv (Qsub (⟨1, 1⟩ : Q) (mul v v)))) ⟨2, n + 1⟩)
  exact Qle_trans (Qmul_den_pos hvd (Qinv_den_pos hWn)) (key (Rartanh_R ρ n))
    (Qle_self_add (by show (0 : Int) ≤ 2; decide))

/-- The rational Qinv cancellation `c·(v·W⁻¹)·W = c·v` for `0 < W.num` (`W` opaque). -/
private theorem mul_Qinv_mul_cancel (c v W : Q) (hWn : 0 < W.num) :
    Qeq (mul (mul c (mul v (Qinv W))) W) (mul c v) := by
  have htW : ((W.num.toNat : Nat) : Int) = W.num := Int.toNat_of_nonneg (Int.le_of_lt hWn)
  show (c.num * (v.num * (W.den : Int))) * W.num * ((c.den * v.den : Nat) : Int)
      = (c.num * v.num) * (((c.den * (v.den * W.num.toNat)) * W.den : Nat) : Int)
  push_cast [htW]; ring_uor

set_option maxHeartbeats 1000000 in
/-- **The one-sided log bound** `log q ≤ q − 1` for a rational `q ≥ 1` — the constructive Bishop form of
    `log u ≤ u−1`, the convexity modulus the `RrpowPos` Lipschitz / general `t^{σ−1}` Mellin integrand needs.
    Since `log q = 2·artanh(tmap q)` (`Rlog`'s definition, where `tmap q = (q−1)/(q+1)`), the bracket
    `RartanhAtQ_le` gives `artanh(tmap q) ≤ tmap q/(1−tmap q²)`, so `2·tmap q/(1−tmap q²) = (q²−1)/(2q) ≤ q−1`.
    The final rational inequality cancels the positive `1−tmap q²` (`mul_Qinv_mul_cancel`) and reduces to
    `q.den ≤ q.num` (i.e. `q ≥ 1`), the residual `(q−1)²·… ≥ 0`. -/
theorem Rlog_le_sub_one (q : Q) (hqd : 0 < q.den) (hqge : Qle (⟨1, 1⟩ : Q) q)
    (hqn : 0 < q.num) (hqq : Qle (⟨1, 1⟩ : Q) (mul q q)) :
    Rle (Rlog (ofQ q hqd) q hqd hqge (fun _ => hqn) (fun _ => Qle_refl q) (fun _ => hqq))
        (ofQ (Qsub q (⟨1, 1⟩ : Q)) (Qsub_den_pos hqd Nat.one_pos)) := by
  have had : (q.den : Int) ≤ q.num := by have h := hqge; simp only [Qle] at h; omega
  have hdp : (0 : Int) < (q.den : Int) := by exact_mod_cast hqd
  have htn : ((q.num + (q.den : Int)).toNat : Int) = q.num + (q.den : Int) :=
    Int.toNat_of_nonneg (by omega)
  obtain ⟨hMn, hM1, hρ0, hρd, hρlt, hρ1⟩ := Rlog_radius_facts q hqd hqge
  have hτd : 0 < (tmap q).den := by rw [tmap_rat_den]; exact Nat.mul_pos hqd (by omega)
  have hv0 : 0 ≤ (tmap q).num := by rw [tmap_rat_num]; exact Int.mul_nonneg (by omega) (by omega)
  have hb : Qle (Qabs (tmap q)) (⟨q.num - (q.den : Int), q.num.toNat + q.den⟩ : Q) :=
    Rlog_tbound (ofQ q hqd) q hqd hMn hM1 (fun _ => Qle_refl q) (fun _ => hqq) (fun _ => hqn) 0
  have hWnum : (Qsub (⟨1, 1⟩ : Q) (mul (tmap q) (tmap q))).num
      = 4 * q.num * ((q.den : Int) * (q.den : Int) * (q.den : Int)) := by
    show (add (⟨1, 1⟩ : Q) (neg (mul (tmap q) (tmap q)))).num = _
    simp only [add, neg, mul]; rw [tmap_rat_num, tmap_rat_den]; push_cast [htn]; ring_uor
  have hWn : 0 < (Qsub (⟨1, 1⟩ : Q) (mul (tmap q) (tmap q))).num := by
    rw [hWnum]
    exact Int.mul_pos (Int.mul_pos (by decide) hqn) (Int.mul_pos (Int.mul_pos hdp hdp) hdp)
  have hWd : 0 < (Qsub (⟨1, 1⟩ : Q) (mul (tmap q) (tmap q))).den :=
    Qsub_den_pos Nat.one_pos (Qmul_den_pos hτd hτd)
  have hbridge : Rlog (ofQ q hqd) q hqd hqge (fun _ => hqn) (fun _ => Qle_refl q) (fun _ => hqq)
      = TwoArtanhConst (tmap q) (⟨q.num - (q.den : Int), q.num.toNat + q.den⟩ : Q)
          hτd hρ0 hρd hρlt hb := rfl
  rw [hbridge]
  have hbracket := RartanhAtQ_le (tmap q) hτd hv0
    (⟨q.num - (q.den : Int), q.num.toNat + q.den⟩ : Q) hρ0 hρd hρlt hb hWn
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) hbracket) ?_
  refine Rle_trans (Rle_of_Req (Rmul_ofQ_ofQ (by decide)
    (Qmul_den_pos hτd (Qinv_den_pos hWn)))) ?_
  refine Rle_ofQ_ofQ (Qmul_den_pos (by decide) (Qmul_den_pos hτd (Qinv_den_pos hWn)))
    (Qsub_den_pos hqd Nat.one_pos) ?_
  refine Qmul_le_cancel_right hWn hWd ?_
  refine Qle_trans (Qmul_den_pos (by decide) hτd)
    (Qeq_le (mul_Qinv_mul_cancel (⟨2, 1⟩ : Q) (tmap q)
      (Qsub (⟨1, 1⟩ : Q) (mul (tmap q) (tmap q))) hWn)) ?_
  simp only [Qle, mul, Qsub, add, neg]
  rw [tmap_rat_num, tmap_rat_den]
  push_cast [htn]
  have hsq : (0 : Int) ≤ (q.num - (q.den : Int)) * (q.num - (q.den : Int)) := by
    rw [← Int.natAbs_mul_self]; exact Int.ofNat_nonneg _
  have hap : (0 : Int) ≤ q.num + (q.den : Int) := by omega
  have hnn : (0 : Int) ≤ 2 * ((q.num - (q.den : Int)) * (q.num - (q.den : Int)))
      * ((q.den : Int) * (q.den : Int) * (q.den : Int) * (q.den : Int)) * (q.num + (q.den : Int)) :=
    Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (by decide) hsq)
      (Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (Int.le_of_lt hdp) (Int.le_of_lt hdp))
        (Int.le_of_lt hdp)) (Int.le_of_lt hdp))) hap
  have hfac : (q.num * 1 + -1 * (q.den : Int)) *
        (1 * ((q.den : Int) * (q.num + (q.den : Int)) * ((q.den : Int) * (q.num + (q.den : Int)))) +
          -((q.num - (q.den : Int)) * (q.den : Int) * ((q.num - (q.den : Int)) * (q.den : Int))) * 1) *
      (1 * ((q.den : Int) * (q.num + (q.den : Int))))
      = 2 * ((q.num - (q.den : Int)) * (q.den : Int))
          * ((q.den : Int) * 1 * (1 * ((q.den : Int) * (q.num + (q.den : Int))
              * ((q.den : Int) * (q.num + (q.den : Int))))))
        + 2 * ((q.num - (q.den : Int)) * (q.num - (q.den : Int)))
          * ((q.den : Int) * (q.den : Int) * (q.den : Int) * (q.den : Int)) * (q.num + (q.den : Int)) := by
    ring_uor
  omega

set_option maxHeartbeats 1000000 in
/-- **The companion lower log bound** `2(q−1)/(q+1) ≤ log q` for rational `q ≥ 1`. From the artanh lower
    bound `tmap q ≤ artanh(tmap q)` (`RartanhAtQ_ge`), doubled: `log q = 2·artanh(tmap q) ≥ 2·tmap q`. No
    `Qinv` cancellation needed. Together with `Rlog_le_sub_one` this brackets `log q ∈ [2(q−1)/(q+1), q−1]`. -/
theorem Rlog_ge_two_tmap (q : Q) (hqd : 0 < q.den) (hqge : Qle (⟨1, 1⟩ : Q) q)
    (hqn : 0 < q.num) (hqq : Qle (⟨1, 1⟩ : Q) (mul q q)) :
    Rle (ofQ (mul (⟨2, 1⟩ : Q) (tmap q)) (Qmul_den_pos (by decide)
          (by rw [tmap_rat_den]; exact Nat.mul_pos hqd (by omega))))
        (Rlog (ofQ q hqd) q hqd hqge (fun _ => hqn) (fun _ => Qle_refl q) (fun _ => hqq)) := by
  obtain ⟨hMn, hM1, hρ0, hρd, hρlt, hρ1⟩ := Rlog_radius_facts q hqd hqge
  have hτd : 0 < (tmap q).den := by rw [tmap_rat_den]; exact Nat.mul_pos hqd (by omega)
  have hv0 : 0 ≤ (tmap q).num := by
    rw [tmap_rat_num]
    have had : (q.den : Int) ≤ q.num := by have h := hqge; simp only [Qle] at h; omega
    exact Int.mul_nonneg (by omega) (by omega)
  have hb : Qle (Qabs (tmap q)) (⟨q.num - (q.den : Int), q.num.toNat + q.den⟩ : Q) :=
    Rlog_tbound (ofQ q hqd) q hqd hMn hM1 (fun _ => Qle_refl q) (fun _ => hqq) (fun _ => hqn) 0
  have hbridge : Rlog (ofQ q hqd) q hqd hqge (fun _ => hqn) (fun _ => Qle_refl q) (fun _ => hqq)
      = TwoArtanhConst (tmap q) (⟨q.num - (q.den : Int), q.num.toNat + q.den⟩ : Q)
          hτd hρ0 hρd hρlt hb := rfl
  rw [hbridge]
  have hge := RartanhAtQ_ge (tmap q) hτd hv0
    (⟨q.num - (q.den : Int), q.num.toNat + q.den⟩ : Q) hρ0 hρd hρlt hb
  refine Rle_trans ?_ (Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) hge)
  exact Rle_of_Req (Req_symm (Rmul_ofQ_ofQ (by decide) hτd))
/-! ### Uniform rational per-index bound `2·artSum(tmap q)(N) ≤ q−1` for all `q > 0`

These lift the artanh upper bound to a *uniform* (sign-robust) rational statement: the per-index bound
holds for every `q > 0`, not only `q ≥ 1`. For `q ≥ 1` it is the geometric route (`artSum_le_geo`);
for `q < 1` (`tmap q < 0`) the artanh partial sum sits *below* its negative argument
(`artSum_le_arg_of_nonpos`), and `2·tmap q ≤ q−1` holds for all `q > 0` (`two_tmap_le_sub`, residual
`(q.num−q.den)²·q.den ≥ 0`). This is the rational core of the GENERAL-REAL `log u ≤ u−1`: a real `u ≥ 1`
has approximants that dip below `1`, so the per-index bound must hold without the sign hypothesis. -/

/-- `x + y ≤ x` when `y ≤ 0`. -/
theorem Qadd_le_self_of_nonpos {x y : Q} (hy : y.num ≤ 0) : Qle (add x y) x := by
  show (x.num * (y.den : Int) + y.num * (x.den : Int)) * (x.den : Int)
      ≤ x.num * ((x.den * y.den : Nat) : Int)
  have hd : x.num * ((x.den * y.den : Nat) : Int)
        - (x.num * (y.den : Int) + y.num * (x.den : Int)) * (x.den : Int)
      = (-(y.num)) * ((x.den : Int) * (x.den : Int)) := by push_cast; ring_uor
  have hnn : 0 ≤ (-(y.num)) * ((x.den : Int) * (x.den : Int)) :=
    Int.mul_nonneg (by omega) (Int.mul_nonneg (Int.ofNat_nonneg _) (Int.ofNat_nonneg _))
  omega

/-- An even power has non-negative numerator (`qⁱ = (qʲ)²` at `i = 2j`). -/
theorem qpow_two_mul_nonneg (t : Q) (hd : 0 < t.den) (j : Nat) : 0 ≤ (qpow t (2 * j)).num := by
  have heq : Qeq (qpow t (2 * j)) (mul (qpow t j) (qpow t j)) := by
    rw [show 2 * j = j + j from by omega]; exact qpow_add t hd j j
  have hmul : 0 ≤ (mul (qpow t j) (qpow t j)).num := by
    show 0 ≤ (qpow t j).num * (qpow t j).num
    rw [← Int.natAbs_mul_self]; exact Int.ofNat_nonneg _
  exact num_nonneg_of_Qzero_le (Qle_trans (Qmul_den_pos (qpow_den_pos hd j) (qpow_den_pos hd j))
    (Qzero_le hmul) (Qeq_le (Qeq_symm heq)))

/-- An odd power of a non-positive rational has non-positive numerator. -/
theorem qpow_odd_nonpos (t : Q) (hd : 0 < t.den) (ht : t.num ≤ 0) (j : Nat) :
    (qpow t (2 * j + 1)).num ≤ 0 := by
  rw [qpow_succ t (2 * j)]
  show t.num * (qpow t (2 * j)).num ≤ 0
  have h1 := Int.mul_nonneg (by omega : (0 : Int) ≤ -t.num) (qpow_two_mul_nonneg t hd j)
  rw [Int.neg_mul] at h1; omega

/-- The artanh term `t^{2j+1}/(2j+1)` is non-positive for `t ≤ 0`. -/
theorem artTerm_nonpos (t : Q) (hd : 0 < t.den) (ht : t.num ≤ 0) (j : Nat) :
    (artTerm t j).num ≤ 0 := by
  show (qpow t (2 * j + 1)).num * 1 ≤ 0
  have := qpow_odd_nonpos t hd ht j; omega

/-- **`artSum t N ≤ t` for `t ≤ 0`** — the artanh partial sum sits below its (negative) argument,
    since every term past the first is non-positive. The mirror of `artSum_ge_arg` (`t ≥ 0`). -/
theorem artSum_le_arg_of_nonpos (t : Q) (hd : 0 < t.den) (ht : t.num ≤ 0) :
    ∀ N, Qle (artSum t N) t
  | 0 => Qeq_le (artSum_zero_eq t)
  | (N + 1) => by
    show Qle (add (artSum t N) (artTerm t (N + 1))) t
    exact Qle_trans (artSum_den_pos hd N) (Qadd_le_self_of_nonpos (artTerm_nonpos t hd ht (N + 1)))
      (artSum_le_arg_of_nonpos t hd ht N)

/-- `2·tmap q ≤ q−1` for all `q > 0` (residual `(q.num−q.den)²·q.den ≥ 0`). -/
theorem two_tmap_le_sub (q : Q) (hqd : 0 < q.den) (hqn : 0 < q.num) :
    Qle (mul (⟨2, 1⟩ : Q) (tmap q)) (Qsub q (⟨1, 1⟩ : Q)) := by
  have hdp : (0 : Int) < (q.den : Int) := by exact_mod_cast hqd
  have htn : ((q.num + (q.den : Int)).toNat : Int) = q.num + (q.den : Int) := Int.toNat_of_nonneg (by omega)
  simp only [Qle, mul, Qsub, add, neg]
  rw [tmap_rat_num, tmap_rat_den]; push_cast [htn]
  have hsq : (0 : Int) ≤ (q.num - (q.den : Int)) * (q.num - (q.den : Int)) := by
    rw [← Int.natAbs_mul_self]; exact Int.ofNat_nonneg _
  have hnn : (0 : Int) ≤ (q.num - (q.den : Int)) * (q.num - (q.den : Int)) * (q.den : Int) :=
    Int.mul_nonneg hsq (Int.le_of_lt hdp)
  have hfac : (q.num * 1 + -1 * (q.den : Int)) * (1 * ((q.den : Int) * (q.num + (q.den : Int))))
      = 2 * ((q.num - (q.den : Int)) * (q.den : Int)) * ((q.den : Int) * 1)
        + (q.num - (q.den : Int)) * (q.num - (q.den : Int)) * (q.den : Int) := by ring_uor
  omega

/-- `2·tmap q ≤ (q−1)·(1−tmap q²)` for all `q > 0` (the `W`-cleared form of `two_tmap_le_sub`). -/
theorem two_tmap_le_sub_mul_W (q : Q) (hqd : 0 < q.den) (hqn : 0 < q.num) :
    Qle (mul (⟨2, 1⟩ : Q) (tmap q))
        (mul (Qsub q (⟨1, 1⟩ : Q)) (Qsub (⟨1, 1⟩ : Q) (mul (tmap q) (tmap q)))) := by
  have hdp : (0 : Int) < (q.den : Int) := by exact_mod_cast hqd
  have htn : ((q.num + (q.den : Int)).toNat : Int) = q.num + (q.den : Int) := Int.toNat_of_nonneg (by omega)
  simp only [Qle, mul, Qsub, add, neg]
  rw [tmap_rat_num, tmap_rat_den]; push_cast [htn]
  have hsq : (0 : Int) ≤ (q.num - (q.den : Int)) * (q.num - (q.den : Int)) := by
    rw [← Int.natAbs_mul_self]; exact Int.ofNat_nonneg _
  have hap : (0 : Int) ≤ q.num + (q.den : Int) := by omega
  have hnn : (0 : Int) ≤ 2 * ((q.num - (q.den : Int)) * (q.num - (q.den : Int)))
      * ((q.den : Int) * (q.den : Int) * (q.den : Int) * (q.den : Int)) * (q.num + (q.den : Int)) :=
    Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (by decide) hsq)
      (Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg (Int.le_of_lt hdp) (Int.le_of_lt hdp))
        (Int.le_of_lt hdp)) (Int.le_of_lt hdp))) hap
  have hfac : (q.num * 1 + -1 * (q.den : Int)) *
        (1 * ((q.den : Int) * (q.num + (q.den : Int)) * ((q.den : Int) * (q.num + (q.den : Int)))) +
          -((q.num - (q.den : Int)) * (q.den : Int) * ((q.num - (q.den : Int)) * (q.den : Int))) * 1) *
      (1 * ((q.den : Int) * (q.num + (q.den : Int))))
      = 2 * ((q.num - (q.den : Int)) * (q.den : Int))
          * ((q.den : Int) * 1 * (1 * ((q.den : Int) * (q.num + (q.den : Int))
              * ((q.den : Int) * (q.num + (q.den : Int))))))
        + 2 * ((q.num - (q.den : Int)) * (q.num - (q.den : Int)))
          * ((q.den : Int) * (q.den : Int) * (q.den : Int) * (q.den : Int)) * (q.num + (q.den : Int)) := by
    ring_uor
  omega

set_option maxHeartbeats 1000000 in
/-- **The uniform rational per-index bound** `2·artSum(tmap q)(N) ≤ q−1`, for every rational `q > 0`
    and every depth `N`. The sign-robust core of the general-real `log u ≤ u−1`: `q ≥ 1` via the
    geometric upper bound (cancel `1−tmap q²`); `q < 1` via `artSum ≤ tmap q ≤ 0` then `2·tmap q ≤ q−1`. -/
theorem artSum_tmap_double_le (q : Q) (hqd : 0 < q.den) (hqn : 0 < q.num) (N : Nat) :
    Qle (mul (⟨2, 1⟩ : Q) (artSum (tmap q) N)) (Qsub q (⟨1, 1⟩ : Q)) := by
  have hdp : (0 : Int) < (q.den : Int) := by exact_mod_cast hqd
  have htn : ((q.num + (q.den : Int)).toNat : Int) = q.num + (q.den : Int) := Int.toNat_of_nonneg (by omega)
  have hτd : 0 < (tmap q).den := by rw [tmap_rat_den]; exact Nat.mul_pos hqd (by omega)
  by_cases hq1 : Qle (⟨1, 1⟩ : Q) q
  · have hv0 : 0 ≤ (tmap q).num := tmap_num_nonneg hq1
    have hWnum : (Qsub (⟨1, 1⟩ : Q) (mul (tmap q) (tmap q))).num
        = 4 * q.num * ((q.den : Int) * (q.den : Int) * (q.den : Int)) := by
      show (add (⟨1, 1⟩ : Q) (neg (mul (tmap q) (tmap q)))).num = _
      simp only [add, neg, mul]; rw [tmap_rat_num, tmap_rat_den]; push_cast [htn]; ring_uor
    have hWn : 0 < (Qsub (⟨1, 1⟩ : Q) (mul (tmap q) (tmap q))).num := by
      rw [hWnum]; exact Int.mul_pos (Int.mul_pos (by decide) hqn) (Int.mul_pos (Int.mul_pos hdp hdp) hdp)
    have hWd : 0 < (Qsub (⟨1, 1⟩ : Q) (mul (tmap q) (tmap q))).den :=
      Qsub_den_pos Nat.one_pos (Qmul_den_pos hτd hτd)
    refine Qmul_le_cancel_right hWn hWd ?_
    refine Qle_trans (Qmul_den_pos (by decide) (Qmul_den_pos (artSum_den_pos hτd N) hWd))
      (Qeq_le (Qmul_assoc (⟨2, 1⟩ : Q) (artSum (tmap q) N)
        (Qsub (⟨1, 1⟩ : Q) (mul (tmap q) (tmap q))))) ?_
    refine Qle_trans (Qmul_den_pos (by decide) hτd)
      (Qmul_le_mul_left (by decide) (artSum_le_geo hv0 hτd (Int.le_of_lt hWn) N)) ?_
    exact two_tmap_le_sub_mul_W q hqd hqn
  · have hqlt : Qlt q (⟨1, 1⟩ : Q) := by
      rcases Qle_or_Qlt (⟨1, 1⟩ : Q) q with h | h
      · exact absurd h hq1
      · exact h
    have htneg : (tmap q).num ≤ 0 := by
      rw [tmap_rat_num]
      have hlt : q.num < (q.den : Int) := by have h := hqlt; simp only [Qlt] at h; omega
      have h1 := Int.mul_nonneg (by omega : (0 : Int) ≤ -(q.num - (q.den : Int))) (Int.ofNat_nonneg q.den)
      rw [Int.neg_mul] at h1; omega
    refine Qle_trans (Qmul_den_pos (by decide) hτd)
      (Qmul_le_mul_left (by decide) (artSum_le_arg_of_nonpos (tmap q) hτd htneg N))
      (two_tmap_le_sub q hqd hqn)

end UOR.Bridge.F1Square.Analysis
