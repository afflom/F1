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

end UOR.Bridge.F1Square.Analysis
