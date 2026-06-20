import F1Square.Analysis.ClogAddBounded
import F1Square.Analysis.Gamma

/-!
# Signed-τ artanh/exp substrate — toward general-modulus `Rlog`/`Clog` additivity

The bounded-modulus discharge (`RlogMulPos`, `ClogAddBounded`) requires squared moduli `≥ 1`
(so the `tmap` arguments are `≥ 0`). Extending to the symmetric band `[1/B, B]` (moduli near 1,
above *and* below) needs the artanh/exp identities for **signed** arguments.

The key observation that sidesteps re-deriving the `t≥0` corner bounds: `exp(2·artanh τ) =
(1+τ)/(1−τ)` for `τ < 0` follows from the nonnegative case by **oddness**
(`artanh(−σ) = −artanh σ`, `Rartanh_neg`) and **exp-of-negation** (`exp(−x)·exp(x) = 1`,
`RexpReal_add`), with the addition law lifted through `RexpReal_inj_gen` (no nonneg restriction).

This file builds that substrate bottom-up.
-/

namespace UOR.Bridge.F1Square.Analysis

/-- **`artanh` is odd**: `Rartanh(−t) = −Rartanh t`. Per diagonal index the partial sum negates
    (`artSum_neg`), since the artanh series has only odd-degree terms. The bound for `−t` follows
    from the bound for `t` (`Qabs_neg`). -/
theorem Rartanh_neg (t : Real) (ρ : Q) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hlt : ρ.num.toNat < ρ.den)
    (hb : ∀ n, Qle (Qabs (t.seq n)) ρ)
    (hb' : ∀ n, Qle (Qabs ((Rneg t).seq n)) ρ) :
    Req (Rartanh (Rneg t) ρ hρ0 hρd hlt hb') (Rneg (Rartanh t ρ hρ0 hρd hlt hb)) := by
  refine Req_of_seq_Qeq (fun j => ?_)
  show Qeq (artSum ((Rneg t).seq (Rartanh_R ρ j)) (Rartanh_R ρ j))
        (neg (artSum (t.seq (Rartanh_R ρ j)) (Rartanh_R ρ j)))
  exact artSum_neg (t.den_pos _) (Rartanh_R ρ j)

end UOR.Bridge.F1Square.Analysis
