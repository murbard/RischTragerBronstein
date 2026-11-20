import RischTragerBronstein.Mixed.NKInfRLog
import RischTragerBronstein.Mixed.NKInf2UnitExample

/-!
# Example: three places at infinity

Tower `x`, `t = log x`, and the rational cubic `θ³ + t θ² − t = 0` (`θ = 1/s`, `t = 1/(s³ − s)`;
Eisenstein at `t = 0`). Its three places at infinity (`s = 0, ±1`) are the three branches
`y′ = −1, ±x′` of the inverted curve `y′³ + y′² − x′² = 0` above `x′ = 0` (`RPlaceDataP`, checked),
and `u₁ = 1 − θ`, `u₂ = 1 + θ` are units (inverses `θ² + (1 + t) θ + 1 + t` and
`θ² − (1 − t) θ + 1 − t`; norms `±1`, so `τ(uᵢ′/uᵢ) = 0`), multiplicatively independent modulo
`ℚ(x, t)` (`indepC`: the `(θ, θ²)`-coordinates of `uᵢ′/uᵢ` form an invertible matrix). By
`nk_iffInf`, `∫ θ dx` is elementary iff `θ − τ(θ)/3 − c₁ u₁′/u₁ − c₂ u₂′/u₂` is exact for some
constants; `exactTL` answers `some false` (`#guard`; the hypothesis `hres`):
**`∫ θ dx` is not elementary**.
-/

namespace Curves.MT.NKInfREx

open Curves Curves.LT Curves.MT CPoly Sup Tower.Sys Curves.MT.NKExEx Polynomial Differential GTors

/-- `θ³ + t θ² − t`. -/
def Fq : BPoly ℚ := [[0, -1], [], [0, 1], [1]]

def Pp : List (GPoly (LC 0)) := liftCurve Fc ks 0 3 Fq
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
def t2 : LC 1 := (([[], [], one0] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
/-- Power sums `s₀ = 3`, `s₁ = −t`, `s₂ = t²`. -/
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 3, (MOr Fc ks 1).neg tC, t2]
def cq (q : ℚ) : LC 0 := [([q], [1])]
/-- `u₁ = 1 − θ`, `u₂ = 1 + θ` and their inverses. -/
def Us : List (List (GPoly (LC 0))) := [[[cq 1], [cq (-1)]], [[cq 1], [cq 1]]]
def Vs : List (List (GPoly (LC 0))) :=
  [[[cq 1, cq 1], [cq 1, cq 1], [cq 1]], [[cq 1, cq (-1)], [cq (-1), cq 1], [cq 1]]]
/-- `uᵢ′/uᵢ`. -/
def gls : List (GPoly (LC 1)) :=
  [[([[([3 / 4], [0, 1])], [([-1 / 2], [0, 1])]], [[([-27 / 4], [1])], [], [([1], [1])]]),
    ([[([9 / 4], [0, 1])], [([3 / 4], [0, 1])], [([-1 / 2], [0, 1])]],
      [[], [([-27 / 4], [1])], [], [([1], [1])]]),
    ([[([9 / 4], [0, 1])], [([-1 / 2], [0, 1])]], [[], [([-27 / 4], [1])], [], [([1], [1])]])],
   [([[([-3 / 4], [0, 1])], [([-1 / 2], [0, 1])]], [[([-27 / 4], [1])], [], [([1], [1])]]),
    ([[([-9 / 4], [0, 1])], [([3 / 4], [0, 1])], [([1 / 2], [0, 1])]],
      [[], [([-27 / 4], [1])], [], [([1], [1])]]),
    ([[([9 / 4], [0, 1])], [([1 / 2], [0, 1])]], [[], [([-27 / 4], [1])], [], [([1], [1])]])]]
/-- `θ′` and `1/P_θ`. -/
def dθW : GPoly (LC 1) :=
  [([[([3 / 2], [0, 1])]], [[([-27 / 4], [1])], [], [([1], [1])]]),
   ([[([-9 / 4], [0, 1])]], [[], [([-27 / 4], [1])], [], [([1], [1])]]),
   ([[([-1], [0, 1])]], [[([-27 / 4], [1])], [], [([1], [1])]])]
def wθW : GPoly (LC 1) :=
  [([[([-3 / 4], [1])]], [[([-27 / 4], [1])], [], [([1], [1])]]),
   ([[([-9 / 4], [1])], [], [([1 / 2], [1])]], [[], [([-27 / 4], [1])], [], [([1], [1])]]),
   ([[([1 / 2], [1])]], [[([-27 / 4], [1])], [], [([1], [1])]])]
/-- The inverse of the `(θ, θ²)`-minor of the coordinates of `u₁′/u₁, u₂′/u₂`. -/
def Hm : List (List (LC 1)) :=
  [[([[], [([0, -3 / 2], [1])], [([0, -1 / 3], [1])]], [[([1], [1])]]),
    ([[], [([0, 3 / 2], [1])], [([0, -1 / 3], [1])]], [[([1], [1])]])],
   [([[], [([0, -3 / 2], [1])], [([0, 1 / 2], [1])], [([0, 1 / 3], [1])]], [[([1], [1])]]),
    ([[], [([0, -3 / 2], [1])], [([0, -1 / 2], [1])], [([0, 1 / 3], [1])]], [[([1], [1])]])]]
/-- `f = θ`. -/
def fp : List (GPoly (LC 0)) := [[], [one0]]
def rest : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fp) (nkTau Fc ks 0 3 (nkFl Fc ks 0 fp) sC)
def Id3 : List (List (LC 1)) := [[onec, zer, zer], [zer, onec, zer], [zer, zer, onec]]

-- `θ − τ(θ)/3 − c₁ u₁′/u₁ − c₂ u₂′/u₂` is never exact (about 2 min)
#guard exactTL Fc ks 0 (primSysC Fc ks 0 ic (paramLimC Fc ks lv 0)) PC Id3 Id3 rest gls = some false

lemma hcertC : certC Fc ks lv 1 = true := NKNonTorsEx.hcert

set_option maxRecDepth 200000 in
lemma hs : traceW Fc ks 0 Pp dθW wθW sC = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hU : unitsC Fc ks 0 Pp Us Vs gls dθW wθW sC = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hJH : indepC Fc ks 0 gls [1, 2] Hm = true := by decide +kernel

lemma Fq_eq : toB Fq = X ^ 3 + C X * X ^ 2 + C (-X) := by
  simp [Fq, toB_cons, toB_nil, toPoly_cons, toPoly_nil]
  ring

lemma Fq_mon : (toB Fq).Monic := by rw [Fq_eq]; monicity!

lemma Fq_deg : (toB Fq).natDegree = 3 := by rw [Fq_eq]; compute_degree!

def Fq' : BPoly ℚ := invB (shiftB Fq 0) 1 3

lemma Fq'_lit : Fq' = [[0, 0, -1, 0], [0, 0, 0], [1, 0], [1]] := by decide +kernel

lemma Fq'_eq : toB Fq' = X ^ 3 + X ^ 2 + C (toPoly [0, 0, -1, 0]) := by
  rw [Fq'_lit]
  simp only [toB_cons, toB_nil, toPoly_nil, map_zero, toPoly_cons, map_one, mul_zero, add_zero,
    mul_one, zero_add]
  ring

lemma Fq'_mon : (toB Fq').Monic := by rw [Fq'_eq]; monicity!

lemma Fq'_deg : (toB Fq').natDegree = 3 := by rw [Fq'_eq]; compute_degree!

lemma hinv : InvOK 1 3 0 (shiftB Fq 0) := invOKb_spec (by decide +kernel)

universe u

lemma hgeo : GeomIrr.{u} Fq :=
  geomIrr_of_eis Fq Fq_mon (by rw [Fq_deg]; rfl) (by rw [Fq_deg]; norm_num) 0 (by decide +kernel)

/-- The coefficient field `ℚ` (as `ℚ[γ]/(γ)`). -/
def MM : CPoly ℚ := [0, 1]

instance : Fact (Irreducible (toPoly MM)) := ⟨Kron.irredQ_sound MM irredQ_X⟩

abbrev KK := NFC.NF MM

/-- The place data of `y′³ + y′² − x′² = 0` above `x′ = 0` (three places `y′ = −1, ±x′`). -/
def PcW : PlaceCert KK := ⟨[((NFC.mk MM []), 1)], [(0, (1, ([(NFC.mk MM [(-1)]), (NFC.mk MM []), (NFC.mk MM [1]), (NFC.mk MM []), (NFC.mk MM [2]), (NFC.mk MM []), (NFC.mk MM [7]), (NFC.mk MM [])], 7))), (0, (1, ([(NFC.mk MM []), (NFC.mk MM [1]), (NFC.mk MM [(-1/2)]), (NFC.mk MM [(5/8)]), (NFC.mk MM [(-1)]), (NFC.mk MM [(231/128)]), (NFC.mk MM [(-7/2)]), (NFC.mk MM [(7293/1024)])], 7))), (0, (1, ([(NFC.mk MM []), (NFC.mk MM [(-1)]), (NFC.mk MM [(-1/2)]), (NFC.mk MM [(-5/8)]), (NFC.mk MM [(-1)]), (NFC.mk MM [(-231/128)]), (NFC.mk MM [(-7/2)]), (NFC.mk MM [(-7293/1024)])], 7)))], [[(0, (1, (NFC.mk MM [1]))), (1, (1, (NFC.mk MM [1]))), (2, (1, (NFC.mk MM [1])))]], [1, 1, 1], [1], [3], 1, [4]⟩

def FcK : BPoly KK := Fq'.map (·.map (algebraMap ℚ KK))

lemma FcK_deg : (toB FcK).natDegree = 3 := by
  rw [FcK, toB_mapL, natDegree_map_eq_of_injective (map_injective _ (algebraMap ℚ KK).injective),
    Fq'_deg]

set_option maxRecDepth 200000 in
lemma okPc : PcW.check FcK (toB FcK).natDegree = true := by
  rw [FcK_deg]
  decide +kernel

lemma hpd : RPlaceDataP KK (invB (shiftB Fq 0) 1 3) (gls.length + 1) :=
  ⟨FcK, PcW, by rw [FcK, toB_mapL]; rfl, okPc, rfl, rfl, by decide +kernel⟩

lemma hmonF : (toB Fc).Monic ∧ (toB Fc).natDegree = cvN Fc := by
  have e : toB Fc = X + Polynomial.C (-X) := by
    simp [toB, CPoly.toPoly, add_comm]
  rw [e]
  exact ⟨monic_X_add_C _, by rw [natDegree_X_add_C]; rfl⟩

lemma hlen : Pp.length = 3 := by simp [Pp, liftCurve]

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L] [IsAlgClosed Cc]

/-- **`∫ θ dx` is not elementary** for `θ³ + θ² log x − log x = 0` (three places at infinity, two
independent units), given the `exactTL` answer (`#guard` above). -/
theorem not_elementary (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 3 + ∑ i ∈ Finset.range 3, T.evP 0 (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (hres : exactTL Fc ks 0 (primSysC Fc ks 0 ic (paramLimC Fc ks lv 0)) PC Id3 Id3 rest gls =
      some false) :
    ¬ HasElementaryIntegral (∑ j ∈ Finset.range 3, T.evP 0 (fp.getD j []) * θ ^ j) := by
  intro h
  have hiff := T.nk_iffInf hmonF.1 hmonF.2 0 hn hcertC rfl Pp Fq (by rw [hlen]; rfl) Fq_mon
    (by rw [Fq_deg, hlen]) (by rw [hlen]; norm_num) hgeo θ
    (IsAlgClosed.lift (R := ℚ) (S := KK) (M := Cc)).toRingHom 1 3 hinv Fq'_mon
    (by show (toB Fq').natDegree = _; rw [Fq'_deg, hlen]) Us Vs gls hpd dθW wθW sC
    hU [1, 2] Hm hJH (by rw [hlen]; exact hθ) hgen hs
    fp Id3 Id3 false (by rw [hlen]; exact hres)
  rw [hlen] at hiff
  exact absurd (hiff.mp h).1 (by decide)

end Curves.MT.NKInfREx
