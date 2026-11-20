import RischTragerBronstein.Mixed.NKInf2NExp
import RischTragerBronstein.Mixed.NKInf2NExample
import RischTragerBronstein.Mixed.NKInf2UnitExpExample

/-!
# Example: conjugate places at infinity over `eˣ`

Tower `x`, `t = eˣ`, and `θ² = t − t²` (places at infinity `θ ≈ ±i t`, conjugate; a single
ramified place above `t = 0`). The unit `u = 1 − 2t + 2iθ` (inverse `1 − 2t − 2iθ`) has
`u′/u = i θ/(1 − t)`. By `nk_iffET2N`, `∫ θ dx` is elementary iff `θ − c₀ g₀ − c₁ g₁` is exact
for some constants (`τ(θ) = 0`); `exactTL` (exponential solver, basis normal at infinity) answers
`some true` (`#guard`; the hypothesis `hres`): **`∫ √(eˣ − e²ˣ) dx` is elementary**
(an arcsine: `√(eˣ − e²ˣ) − arcsin(1 − 2eˣ)/2`).
-/

namespace Curves.MT.NKInf2NEEx

open Curves Curves.LT Curves.MT CPoly Sup Tower.Sys Curves.MT.NKExEE Polynomial Differential GTors

/-- `θ² + t² − t`. -/
def Fq : BPoly ℚ := [[0, -1, 1], [], [1]]

def Pp : List (GPoly (LC 0)) := liftCurve Fc ks 0 2 Fq
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
def cq (q : ℚ) : LC 0 := [([q], [1])]
def zer1 : LC 1 := (([] : GPoly (LC 0)), ([one0] : GPoly (LC 0)))
/-- Power sums `s₀ = 2`, `s₁ = 0`. -/
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 2, zer1]
abbrev μ : List ℤ := NKInf2NEx.μ
/-- `u = 1 − 2t + 2αθ` and `u⁻¹ = 1 − 2t − 2αθ`. -/
def As : List (List (GPoly (LC 0))) := [[[cq 1, cq (-2)]], [[], [cq 2]]]
def Bs : List (List (GPoly (LC 0))) := [[[cq 1, cq (-2)]], [[], [cq (-2)]]]
def den : GPoly (LC 0) := [cq 1, cq (-1)]
/-- `u′/u = α g₁`, `g₁ = θ/(1 − t)`. -/
def gs : List (GPoly (LC 1)) := [[], [zer1, ([one0], den)]]
/-- `θ′` and `1/(2θ)`. -/
def dθW : GPoly (LC 1) :=
  [([], [[([1], [1])]]), ([[([-1 / 2], [1])], [([1], [1])]], [[([-1], [1])], [([1], [1])]])]
def wθW : GPoly (LC 1) := [([], [[([1], [1])]]), ([[([-1 / 2], [1])]], [[], [([-1], [1])], [([1], [1])]])]
/-- The inverse `−α (1 − t)` of the `θ`-coordinate `α/(1 − t)` of `u′/u`. -/
def Hn : List (LC 1) := [zer1, ([cq (-1), cq 1], [one0])]
/-- `f = θ`. -/
def fp : List (GPoly (LC 0)) := [[], [one0]]
def rest : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fp) (nkTau Fc ks 0 2 (nkFl Fc ks 0 fp) sC)

-- `θ − c₀ g₀ − c₁ g₁` is exact for some constants
#guard exactTL Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC (nkTc Fc ks 0 Pp) (nkTi Fc ks 0 Pp)
  rest gs = some true

set_option maxRecDepth 200000 in
lemma hcertC : certC Fc ks lv 1 = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hsh0 : nkShape0 Fc ks 0 Pp = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hs : traceW Fc ks 0 Pp dθW wθW sC = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hU : unitsNC Fc ks 0 Pp μ As Bs gs dθW wθW sC 1 Hn = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hτf : (MOr Fc ks 1).isZero (nkTau Fc ks 0 2 (nkFl Fc ks 0 fp) sC) = true := by
  decide +kernel

lemma Fq_eq : toB Fq = X ^ 2 + C (X ^ 2 - X) := by
  simp [Fq, toB_cons, toB_nil, toPoly_cons, toPoly_nil]
  ring

lemma Fq_mon : (toB Fq).Monic := by rw [Fq_eq]; monicity!

lemma Fq_deg : (toB Fq).natDegree = 2 := by rw [Fq_eq]; compute_degree!

lemma ha0Q : (toB Fq).coeff 0 ≠ 0 := by
  rw [Fq_eq]
  simp only [coeff_add, coeff_X_pow, coeff_C_zero]
  norm_num
  intro h
  have := congrArg (fun p : ℚ[X] ↦ p.coeff 1) h
  simp at this

def Fq' : BPoly ℚ := invB (shiftB Fq 0) 1 2

lemma Fq'_lit : Fq' = [[1, -1, 0], [0, 0], [1]] := by decide +kernel

lemma Fq'_eq : toB Fq' = X ^ 2 + C (1 - X) := by
  rw [Fq'_lit]
  simp [toB_cons, toB_nil, toPoly_cons, toPoly_nil]
  ring

lemma Fq'_mon : (toB Fq').Monic := by rw [Fq'_eq]; monicity!

lemma Fq'_deg : (toB Fq').natDegree = 2 := by rw [Fq'_eq]; compute_degree!

lemma hinv : InvOK 1 2 0 (shiftB Fq 0) := invOKb_spec (by decide +kernel)

universe u

lemma hgeo : GeomIrr.{u} Fq :=
  geomIrr_of_eis Fq Fq_mon (by rw [Fq_deg]; rfl) (by rw [Fq_deg]; norm_num) 0 (by decide +kernel)

abbrev MM := NKInf2NEx.MM

abbrev KK := NKInf2NEx.KK

/-- The place data of `y′² + 1 − x′ = 0` above `x′ = 0` (two places `y′ = ±i`). -/
def PcW : PlaceCert KK := ⟨[((NFC.mk MM []), 1)], [(0, (1, ([(NFC.mk MM [0, 1]), (NFC.mk MM [0, (-1/2)]), (NFC.mk MM [0, (-1/8)]), (NFC.mk MM [0, (-1/16)]), (NFC.mk MM [0, (-5/128)]), (NFC.mk MM [0, (-7/256)]), (NFC.mk MM [0, (-21/1024)]), (NFC.mk MM [0, (-33/2048)])], 7))), (0, (1, ([(NFC.mk MM [0, (-1)]), (NFC.mk MM [0, (1/2)]), (NFC.mk MM [0, (1/8)]), (NFC.mk MM [0, (1/16)]), (NFC.mk MM [0, (5/128)]), (NFC.mk MM [0, (7/256)]), (NFC.mk MM [0, (21/1024)]), (NFC.mk MM [0, (33/2048)])], 7)))], [[(0, (1, (NFC.mk MM [1]))), (1, (1, (NFC.mk MM [1])))]], [1, 1], [1], [2], 1, [4]⟩

def FcK : BPoly KK := Fq'.map (·.map (algebraMap ℚ KK))

lemma FcK_deg : (toB FcK).natDegree = 2 := by
  rw [FcK, toB_mapL, natDegree_map_eq_of_injective (map_injective _ (algebraMap ℚ KK).injective),
    Fq'_deg]

set_option maxRecDepth 200000 in
lemma okPc : PcW.check FcK (toB FcK).natDegree = true := by
  rw [FcK_deg]
  decide +kernel

lemma hpd : TwoPlaceDataP KK (invB (shiftB Fq 0) 1 2) :=
  ⟨FcK, PcW, by rw [FcK, toB_mapL]; rfl, okPc, rfl, rfl, by decide +kernel⟩

lemma hmonF : (toB Fc).Monic ∧ (toB Fc).natDegree = cvN Fc := by
  have e : toB Fc = X + Polynomial.C (-X) := by
    simp [toB, CPoly.toPoly, add_comm]
  rw [e]
  exact ⟨monic_X_add_C _, by rw [natDegree_X_add_C]; rfl⟩

lemma hlen : Pp.length = 2 := by simp [Pp, liftCurve]

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L] [IsAlgClosed Cc]

/-- **`∫ θ dx` is elementary** for `θ² = eˣ − e²ˣ`, given the `exactTL` answer (`#guard` above). -/
theorem elementary (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 2 + ∑ i ∈ Finset.range 2, T.evP 0 (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (hres : exactTL Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC (nkTc Fc ks 0 Pp)
      (nkTi Fc ks 0 Pp) rest gs = some true) :
    HasElementaryIntegral (∑ j ∈ Finset.range 2, T.evP 0 (fp.getD j []) * θ ^ j) := by
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
  have hTr : T.Tr 1 := (T.mspecs hmonF.1 hmonF.2 lv 1 (by omega) hcertC).hyp.tr
  have hiff := T.nk_iffET2N hmonF.1 hmonF.2 0 hn hcertC rfl Pp Fq (by rw [hlen]; rfl) Fq_mon
    (by rw [Fq_deg, hlen]) (by rw [hlen]; norm_num) hgeo hsh0 ha0Q θ
    (IsAlgClosed.lift (R := ℚ) (S := KK) (M := Cc)).toRingHom 1 2 hinv Fq'_mon
    (by show (toB Fq').natDegree = _; rw [Fq'_deg, hlen]) hpd μ As Bs gs dθW wθW sC 1 Hn hU
    αs hinj hαμ (by rw [hlen]; exact hθ) hgen hs fp (nkTc Fc ks 0 Pp) (nkTi Fc ks 0 Pp) true
    (by rw [hlen]; exact hres)
  rw [hlen] at hiff
  refine hiff.mpr ⟨rfl, ?_⟩
  have h0 : T.ev 1 (nkTau Fc ks 0 2 (nkFl Fc ks 0 fp) sC) = 0 := by
    rw [← T.coe_sem_MPr 1 hTr, ((T.MPr 1 hTr).isZero_iff _).mp hτf]
    rfl
  rw [h0, show (0 : L) = (0 : L)′ from (Derivation.map_zero _).symm]
  exact hasElementaryIntegral_of_deriv _

end Curves.MT.NKInf2NEEx
