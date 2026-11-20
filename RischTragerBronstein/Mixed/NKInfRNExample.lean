import RischTragerBronstein.Mixed.NKInfRN
import RischTragerBronstein.Mixed.NKInf2NExample

/-!
# Example: three places at infinity, two of them conjugate

Tower `x`, `t = log x`, and the rational cubic `θ³ − t θ² − t = 0` (`θ = 1/s`,
`t = 1/(s³ + s)`; Eisenstein at `t = 0`). Its places at infinity are `s = 0` and the conjugate
pair `s = ±i` (the branches `y′ = 1, ±i x′` of `y′³ − y′² − x′² = 0`). The rational units have
rank `1` only (`1 + θ²`), but `u₁ = 1 − iθ`, `u₂ = 1 + iθ` (inverses `(1 ± iθ)(1 + tθ − θ²)`)
are independent units over `ℚ(i)` (`unitsRNC`, `indepCN`). By `nk_iffRN`, `∫ θ dx` is
elementary iff `θ − τ(θ)/3 − ∑ cᵢₖ gᵢₖ` is exact for some constants and `∫ τ(θ)/3 = ∫ (log x)/3`
is elementary; `exactTL` answers `some false` (`#guard`; the hypothesis `hres`):
**`∫ θ dx` is not elementary**.
-/

namespace Curves.MT.NKInfRNEx

open Curves Curves.LT Curves.MT CPoly Sup Tower.Sys Curves.MT.NKExEx Polynomial Differential GTors

/-- `θ³ − t θ² − t`. -/
def Fq : BPoly ℚ := [[0, -1], [], [0, -1], [1]]

def Pp : List (GPoly (LC 0)) := liftCurve Fc ks 0 3 Fq
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
def tC2 : LC 1 := (([[], [], one0] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
/-- Power sums `s₀ = 3`, `s₁ = t`, `s₂ = t²`. -/
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 3, tC, tC2]
def cq (q : ℚ) : LC 0 := [([q], [1])]
abbrev μ : List ℤ := NKInf2NEx.μ
/-- `w = 1/(1 + θ²) = 1 + tθ − θ²`. -/
def wP : List (GPoly (LC 0)) := [[cq 1], [[], cq 1], [cq (-1)]]
/-- `u₁ = 1 − αθ`, `u₂ = 1 + αθ` and their inverses `w ± α(θ − t)`. -/
def Ass : List (List (List (GPoly (LC 0)))) := [[[[cq 1]], [[], [cq (-1)]]], [[[cq 1]], [[], [cq 1]]]]
def Bss : List (List (List (GPoly (LC 0)))) :=
  [[wP, [[[], cq (-1)], [cq 1]]], [wP, [[[], cq 1], [cq (-1)]]]]
def den2 : GPoly (LC 0) := [[([27 / 4], [1])], [], [([1], [1])]]
def den3 : GPoly (LC 0) := [[], [([27 / 4], [1])], [], [([1], [1])]]
def g10 : GPoly (LC 1) :=
  [([[], [([-1 / 2], [0, 1])]], den2), ([[([-3 / 4], [0, 1])]], den2), ([[([9 / 4], [0, 1])]], den3)]
def g11 : GPoly (LC 1) :=
  [([[([3 / 4], [0, 1])]], den2), ([[([-9 / 4], [0, 1])], [], [([-1 / 2], [0, 1])]], den3),
   ([[([1 / 2], [0, 1])]], den2)]
def g21 : GPoly (LC 1) :=
  [([[([-3 / 4], [0, 1])]], den2), ([[([9 / 4], [0, 1])], [], [([1 / 2], [0, 1])]], den3),
   ([[([-1 / 2], [0, 1])]], den2)]
/-- `uᵢ′/uᵢ = gᵢ₀ + α gᵢ₁`. -/
def gss : List (List (GPoly (LC 1))) := [[g10, g11], [g10, g21]]
/-- `θ′` and `1/P_θ`. -/
def dθW : GPoly (LC 1) :=
  [([[([3 / 2], [0, 1])]], den2), ([[([9 / 4], [0, 1])]], den3), ([[([1], [0, 1])]], den2)]
def wθW : GPoly (LC 1) :=
  [([[([-3 / 4], [1])]], den2), ([[([9 / 4], [1])], [], [([1 / 2], [1])]], den3),
   ([[([-1 / 2], [1])]], den2)]
/-- The inverse over `ℚ(α)` of the `(θ, θ²)`-minor of the coordinates of `u₁′/u₁, u₂′/u₂`. -/
def Hm : List (List (List (LC 1))) :=
  [[[([[], [], [([0, 1 / 3], [1])]], [[([1], [1])]]), ([[], [([0, 3 / 2], [1])]], [[([1], [1])]])],
    [([[], [], [([0, 1 / 3], [1])]], [[([1], [1])]]), ([[], [([0, -3 / 2], [1])]], [[([1], [1])]])]],
   [[([[], [([0, 3 / 2], [1])], [], [([0, 1 / 3], [1])]], [[([1], [1])]]),
      ([[], [], [([0, 1 / 2], [1])]], [[([1], [1])]])],
    [([[], [([0, 3 / 2], [1])], [], [([0, 1 / 3], [1])]], [[([1], [1])]]),
      ([[], [], [([0, -1 / 2], [1])]], [[([1], [1])]])]]]
/-- `f = θ`. -/
def fp : List (GPoly (LC 0)) := [[], [one0]]
def rest : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fp) (nkTau Fc ks 0 3 (nkFl Fc ks 0 fp) sC)
def Id3 : List (List (LC 1)) := [[onec, zer, zer], [zer, onec, zer], [zer, zer, onec]]

-- `θ − τ(θ)/3 − ∑ cᵢₖ gᵢₖ` is never exact (about 2 min)
#guard exactTL Fc ks 0 (primSysC Fc ks 0 ic (paramLimC Fc ks lv 0)) PC Id3 Id3 rest gss.flatten =
  some false

lemma hcertC : certC Fc ks lv 1 = true := NKNonTorsEx.hcert

set_option maxRecDepth 200000 in
lemma hs : traceW Fc ks 0 Pp dθW wθW sC = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hU : unitsRNC Fc ks 0 Pp μ Ass Bss gss dθW wθW sC = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hJH : indepCN Fc ks 0 μ gss [1, 2] Hm = true := by decide +kernel

lemma Fq_eq : toB Fq = X ^ 3 + C (-X) * X ^ 2 + C (-X) := by
  simp [Fq, toB_cons, toB_nil, toPoly_cons, toPoly_nil]
  ring

lemma Fq_mon : (toB Fq).Monic := by rw [Fq_eq]; monicity!

lemma Fq_deg : (toB Fq).natDegree = 3 := by rw [Fq_eq]; compute_degree!

def Fq' : BPoly ℚ := invB (shiftB Fq 0) 1 3

lemma Fq'_lit : Fq' = [[0, 0, -1, 0], [0, 0, 0], [-1, 0], [1]] := by decide +kernel

lemma Fq'_eq : toB Fq' = X ^ 3 - X ^ 2 + C (-X ^ 2) := by
  rw [Fq'_lit]
  simp [toB_cons, toB_nil, toPoly_cons, toPoly_nil]
  ring

lemma Fq'_mon : (toB Fq').Monic := by rw [Fq'_eq]; monicity!

lemma Fq'_deg : (toB Fq').natDegree = 3 := by rw [Fq'_eq]; compute_degree!

lemma hinv : InvOK 1 3 0 (shiftB Fq 0) := invOKb_spec (by decide +kernel)

universe u

lemma hgeo : GeomIrr.{u} Fq :=
  geomIrr_of_eis Fq Fq_mon (by rw [Fq_deg]; rfl) (by rw [Fq_deg]; norm_num) 0 (by decide +kernel)

abbrev MM := NKInf2NEx.MM

abbrev KK := NKInf2NEx.KK

/-- The place data of `y′³ − y′² − x′² = 0` above `x′ = 0` (`y′ = 1, ±i x′`). -/
def PcW : PlaceCert KK := ⟨[((NFC.mk MM []), 1)], [(0, (1, ([(NFC.mk MM []), (NFC.mk MM [0, 1]), (NFC.mk MM [(-1/2)]), (NFC.mk MM [0, (-5/8)]), (NFC.mk MM [1]), (NFC.mk MM [0, (231/128)]), (NFC.mk MM [(-7/2)]), (NFC.mk MM [0, (-7293/1024)])], 7))), (0, (1, ([(NFC.mk MM []), (NFC.mk MM [0, (-1)]), (NFC.mk MM [(-1/2)]), (NFC.mk MM [0, (5/8)]), (NFC.mk MM [1]), (NFC.mk MM [0, (-231/128)]), (NFC.mk MM [(-7/2)]), (NFC.mk MM [0, (7293/1024)])], 7))), (0, (1, ([(NFC.mk MM [1]), (NFC.mk MM []), (NFC.mk MM [1]), (NFC.mk MM []), (NFC.mk MM [(-2)]), (NFC.mk MM []), (NFC.mk MM [7]), (NFC.mk MM [])], 7)))], [[(0, (1, (NFC.mk MM [1]))), (1, (1, (NFC.mk MM [1]))), (2, (1, (NFC.mk MM [1])))]], [1, 1, 1], [1], [3], 1, [4]⟩

def FcK : BPoly KK := Fq'.map (·.map (algebraMap ℚ KK))

lemma FcK_deg : (toB FcK).natDegree = 3 := by
  rw [FcK, toB_mapL, natDegree_map_eq_of_injective (map_injective _ (algebraMap ℚ KK).injective),
    Fq'_deg]

set_option maxRecDepth 200000 in
lemma okPc : PcW.check FcK (toB FcK).natDegree = true := by
  rw [FcK_deg]
  decide +kernel

lemma hpd : RPlaceDataP KK (invB (shiftB Fq 0) 1 3) (gss.length + 1) :=
  ⟨FcK, PcW, by rw [FcK, toB_mapL]; rfl, okPc, rfl, rfl, by decide +kernel⟩

lemma hmonF : (toB Fc).Monic ∧ (toB Fc).natDegree = cvN Fc := by
  have e : toB Fc = X + Polynomial.C (-X) := by
    simp [toB, CPoly.toPoly, add_comm]
  rw [e]
  exact ⟨monic_X_add_C _, by rw [natDegree_X_add_C]; rfl⟩

lemma hlen : Pp.length = 3 := by simp [Pp, liftCurve]

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L] [IsAlgClosed Cc]

/-- **`∫ θ dx` is not elementary** for `θ³ − θ² log x − log x = 0`, given the `exactTL` answer
(`#guard` above). -/
theorem not_elementary (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 3 + ∑ i ∈ Finset.range 3, T.evP 0 (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (hres : exactTL Fc ks 0 (primSysC Fc ks 0 ic (paramLimC Fc ks lv 0)) PC Id3 Id3 rest
      gss.flatten = some false) :
    ¬ HasElementaryIntegral (∑ j ∈ Finset.range 3, T.evP 0 (fp.getD j []) * θ ^ j) := by
  intro h
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Cc) (n := 2) (by norm_num)
  have hi0 : i ≠ 0 := fun h ↦ by rw [h] at hi; norm_num at hi
  set αs : Fin μ.length → Cc := ![i, -i] with hαs
  have hne : i ≠ -i := fun h ↦ hi0 (by linear_combination h / 2)
  have hinj : Function.Injective αs := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> first | rfl | exact absurd hab hne | exact absurd hab hne.symm
  have hαμ : ∀ k, αs k ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : Cc) * αs k ^ l = 0 := by
    intro k
    fin_cases k <;> simp [hαs, μ, NKInf2NEx.μ, Finset.sum_range_succ, hi]
  have hiff := T.nk_iffRN hmonF.1 hmonF.2 0 hn hcertC rfl Pp Fq (by rw [hlen]; rfl) Fq_mon
    (by rw [Fq_deg, hlen]) (by rw [hlen]; norm_num) hgeo θ
    (IsAlgClosed.lift (R := ℚ) (S := KK) (M := Cc)).toRingHom 1 3 hinv Fq'_mon
    (by show (toB Fq').natDegree = _; rw [Fq'_deg, hlen]) μ Ass Bss gss hpd dθW wθW sC hU
    [1, 2] Hm hJH (by rw [hlen]; exact hθ) hgen αs hinj hαμ hs fp Id3 Id3 false
    (by rw [hlen]; exact hres)
  rw [hlen] at hiff
  exact absurd (hiff.mp h).1 (by decide)

end Curves.MT.NKInfRNEx
