import RischTragerBronstein.Mixed.NKInfRExp
import RischTragerBronstein.Mixed.NKInfRExample
import RischTragerBronstein.Mixed.NKInf2UnitExpExample

/-!
# Example: three places at infinity over `eˣ`

Tower `x`, `t = eˣ`, and the rational cubic `θ³ + t θ² − t = 0` of `NKInfREx` (three places at
infinity, units `1 ∓ θ`, a single place above `t = 0`). By `nk_iffETInf`, `∫ θ dx` is elementary iff
`θ − τ(θ)/3 − c₁ u₁′/u₁ − c₂ u₂′/u₂` is exact for some constants and `∫ τ(θ)/3 = ∫ −eˣ/3` is
elementary; `exactTL` (exponential solver, basis normal at infinity) answers `some true` (`#guard`;
the hypothesis `hres`): **`∫ θ dx` is elementary** (with `θ = 1/s`, `eˣ = 1/(s³ − s)`, the integrand
is `−(3s² − 1)/(s²(s² − 1)) ds`, whose logarithms are those of the units `1 ∓ θ`). Over `t = log x`
the same integrand is not elementary (`NKInfREx.not_elementary`).
-/

namespace Curves.MT.NKInfREEx

open Curves Curves.LT Curves.MT CPoly Sup Tower.Sys Curves.MT.NKExEE Polynomial Differential GTors

abbrev Fq : BPoly ℚ := NKInfREx.Fq

def Pp : List (GPoly (LC 0)) := liftCurve Fc ks 0 3 Fq
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
def tC' : LC 1 := (([[], one0] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
def t2 : LC 1 := (([[], [], one0] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
/-- Power sums `s₀ = 3`, `s₁ = −t`, `s₂ = t²`. -/
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 3, (MOr Fc ks 1).neg tC', t2]
abbrev Us := NKInfREx.Us
abbrev Vs := NKInfREx.Vs
/-- `uᵢ′/uᵢ` (now `t′ = t`). -/
def gls : List (GPoly (LC 1)) :=
  [[([[], [([3 / 4], [1])], [([-1 / 2], [1])]], [[([-27 / 4], [1])], [], [([1], [1])]]),
    ([[([9 / 4], [1])], [([3 / 4], [1])], [([-1 / 2], [1])]], [[([-27 / 4], [1])], [], [([1], [1])]]),
    ([[([9 / 4], [1])], [([-1 / 2], [1])]], [[([-27 / 4], [1])], [], [([1], [1])]])],
   [([[], [([-3 / 4], [1])], [([-1 / 2], [1])]], [[([-27 / 4], [1])], [], [([1], [1])]]),
    ([[([-9 / 4], [1])], [([3 / 4], [1])], [([1 / 2], [1])]], [[([-27 / 4], [1])], [], [([1], [1])]]),
    ([[([9 / 4], [1])], [([1 / 2], [1])]], [[([-27 / 4], [1])], [], [([1], [1])]])]]
/-- `θ′` and `1/P_θ`. -/
def dθW : GPoly (LC 1) :=
  [([[], [([3 / 2], [1])]], [[([-27 / 4], [1])], [], [([1], [1])]]),
   ([[([-9 / 4], [1])]], [[([-27 / 4], [1])], [], [([1], [1])]]),
   ([[], [([-1], [1])]], [[([-27 / 4], [1])], [], [([1], [1])]])]
abbrev wθW := NKInfREx.wθW
/-- The inverse of the `(θ, θ²)`-minor of the coordinates of `u₁′/u₁, u₂′/u₂`. -/
def Hm : List (List (LC 1)) :=
  [[([[([-3 / 2], [1])], [([-1 / 3], [1])]], [[([1], [1])]]),
    ([[([3 / 2], [1])], [([-1 / 3], [1])]], [[([1], [1])]])],
   [([[([-3 / 2], [1])], [([1 / 2], [1])], [([1 / 3], [1])]], [[([1], [1])]]),
    ([[([-3 / 2], [1])], [([-1 / 2], [1])], [([1 / 3], [1])]], [[([1], [1])]])]]
/-- `f = θ`. -/
def fp : List (GPoly (LC 0)) := [[], [one0]]
def q : LC 1 := nkTau Fc ks 0 3 (nkFl Fc ks 0 fp) sC
def rest : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fp) q

-- `θ − τ(θ)/3 − c₁ u₁′/u₁ − c₂ u₂′/u₂` is exact for some `cᵢ`
#guard exactTL Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC (nkTc Fc ks 0 Pp)
  (nkTi Fc ks 0 Pp) rest gls = some true

set_option maxRecDepth 200000 in
lemma hcertC : certC Fc ks lv 1 = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hsh0 : nkShape0 Fc ks 0 Pp = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hs : traceW Fc ks 0 Pp dθW wθW sC = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hU : unitsC Fc ks 0 Pp Us Vs gls dθW wθW sC = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hJH : indepC Fc ks 0 gls [1, 2] Hm = true := by decide +kernel

set_option maxRecDepth 200000 in
/-- `τ(θ)/3 = −t/3` is its own derivative. -/
lemma hqd : (MOr Fc ks 1).isZero ((MOr Fc ks 1).add q ((MOr Fc ks 1).neg ((MOr Fc ks 1).deriv q))) =
    true := by decide +kernel

lemma hmonF : (toB Fc).Monic ∧ (toB Fc).natDegree = cvN Fc := by
  have e : toB Fc = X + Polynomial.C (-X) := by
    simp [toB, CPoly.toPoly, add_comm]
  rw [e]
  exact ⟨monic_X_add_C _, by rw [natDegree_X_add_C]; rfl⟩

lemma hlen : Pp.length = 3 := by simp [Pp, liftCurve]

lemma ha0Q : (toB Fq).coeff 0 ≠ 0 := by
  rw [NKInfREx.Fq_eq]
  simp

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L] [IsAlgClosed Cc]

/-- **`∫ θ dx` is elementary** for `θ³ + θ² eˣ − eˣ = 0`, given the `exactTL` answer (`#guard`
above). -/
theorem elementary (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 3 + ∑ i ∈ Finset.range 3, T.evP 0 (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (hres : exactTL Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC (nkTc Fc ks 0 Pp)
      (nkTi Fc ks 0 Pp) rest gls = some true) :
    HasElementaryIntegral (∑ j ∈ Finset.range 3, T.evP 0 (fp.getD j []) * θ ^ j) := by
  have hTr : T.Tr 1 := (T.mspecs hmonF.1 hmonF.2 lv 1 (by omega) hcertC).hyp.tr
  have hiff := T.nk_iffETInf hmonF.1 hmonF.2 0 hn hcertC rfl Pp Fq (by rw [hlen]; rfl)
    NKInfREx.Fq_mon (by rw [NKInfREx.Fq_deg, hlen]) (by rw [hlen]; norm_num) NKInfREx.hgeo hsh0
    ha0Q θ (IsAlgClosed.lift (R := ℚ) (S := NKInfREx.KK) (M := Cc)).toRingHom 1 3 NKInfREx.hinv
    NKInfREx.Fq'_mon (by show (toB NKInfREx.Fq').natDegree = _; rw [NKInfREx.Fq'_deg, hlen])
    Us Vs gls NKInfREx.hpd dθW wθW sC hU [1, 2] Hm hJH (by rw [hlen]; exact hθ) hgen hs
    fp (nkTc Fc ks 0 Pp) (nkTi Fc ks 0 Pp) true (by rw [hlen]; exact hres)
  rw [hlen] at hiff
  refine hiff.mpr ⟨rfl, ?_⟩
  have h0 : T.ev 1 q = (T.ev 1 q)′ := by
    have := ((T.MPr 1 hTr).isZero_iff _).mp hqd
    rw [(T.MPr 1 hTr).sem_add, (T.MPr 1 hTr).sem_neg, (T.MPr 1 hTr).sem_deriv,
      add_neg_eq_zero] at this
    calc T.ev 1 q = ((T.MPr 1 hTr).sem q : L) := (T.coe_sem_MPr 1 hTr q).symm
      _ = (((T.MPr 1 hTr).sem q)′ : T.F 1) := congrArg Subtype.val this
      _ = (T.ev 1 q)′ := by rw [MTower.coe_deriv, T.coe_sem_MPr]
  change HasElementaryIntegral (T.ev 1 q)
  rw [h0]
  exact hasElementaryIntegral_of_deriv _

end Curves.MT.NKInfREEx
