import RischTragerBronstein.Mixed.NKInf2UnitDecide
import RischTragerBronstein.Mixed.NKExactExamples
import RischTragerBronstein.Torsion.Front
import RischTragerBronstein.Mixed.NKNonTorsExample

/-!
# Example: two places at infinity with a torsion difference

Tower `x`, `t = log x`, and the conic `θ² = t² + t` (genus `0`: the two places at infinity differ by
a principal divisor). The unit `u₀ = θ + t + 1/2` has inverse `4(t + 1/2 − θ)` (`unitC`), its
logarithmic derivative is `θ/(x (t² + t))` (certified: `logDerChk`) with trace `0`, and the inverted curve
`y′² = 1 + x′` has its two places above `x′ = 0` (`TwoPlaceDataP`, checked). By `nk_iff2U`,
`∫ θ dx` is elementary iff `θ − c u₀′/u₀` is exact for some constant `c` (`τ(θ) = 0`); `exactC2`
answers `some false` (`#guard`; it enters `not_elementary` as the hypothesis `hres`):
**`∫ √(log²x + log x) dx` is not elementary**.
-/

namespace Curves.MT.NKInf2UEx

open Curves Curves.LT Curves.MT CPoly Sup Tower.Sys Curves.MT.NKExEx Polynomial Differential GTors

/-- `θ² − (t + t²)`. -/
def Fq : BPoly ℚ := [[0, -1, -1], [], [1]]

def Pp : List (GPoly (LC 0)) := liftCurve Fc ks 0 2 Fq
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
/-- Power sums `s₀ = 2`, `s₁ = 0`. -/
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 2, zer]
def cq (q : ℚ) : LC 0 := [([q], [1])]
/-- `u₀ = θ + t + 1/2` and its inverse `4 (t + 1/2) − 4 θ`. -/
def U : List (GPoly (LC 0)) := [[cq (1/2), cq 1], [cq 1]]
def V : List (GPoly (LC 0)) := [[cq 2, cq 4], [cq (-4)]]
/-- `u₀′/u₀ = θ / (x (t + t²))`. -/
def gl : GPoly (LC 1) :=
  [([], [[([1], [1])]]), ([[([1], [0, 1])]], [[], [([1], [1])], [([1], [1])]])]

/-- `θ′ = θ (t + 1/2)/(x (t + t²))` and the inverse `θ/(2 (t + t²))` of `P_θ = 2θ`. -/
def dθW : GPoly (LC 1) :=
  [([], [[([1], [1])]]), ([[([1 / 2], [0, 1])], [([1], [0, 1])]], [[], [([1], [1])], [([1], [1])]])]
def wθW : GPoly (LC 1) := [([], [[([1], [1])]]), ([[([1 / 2], [1])]], [[], [([1], [1])], [([1], [1])]])]
/-- `f = θ`. -/
def fp : List (GPoly (LC 0)) := [[], [one0]]
def rest : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fp) (nkTau Fc ks 0 2 (nkFl Fc ks 0 fp) sC)

#guard nkShape Fc ks 0 Pp = false
-- `θ − c u₀′/u₀` is never exact
#guard exactC2 Fc ks 0 ic (paramLimC Fc ks lv 0) PC rest gl = some false

lemma hcertC : certC Fc ks lv 1 = true := NKNonTorsEx.hcert

set_option maxRecDepth 200000 in
lemma hs : traceC Fc ks 0 PC sC = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma huv : unitC Fc ks 0 Pp U V = true := by decide +kernel

set_option maxRecDepth 200000 in
set_option maxRecDepth 200000 in
lemma hgl : logDerChk Fc ks 0 Pp U V gl dθW wθW = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hτg : (MOr Fc ks 1).isZero (nkTau Fc ks 0 2 gl sC) = true := by decide +kernel

lemma hU1 : GPoly.trim (MO Fc ks 0) (U.getD 1 []) ≠ [] :=
  List.ne_nil_of_length_pos (by decide +kernel)

lemma Fq_eq : toB Fq = X ^ 2 + C (toPoly [0, -1, -1]) := by
  simp only [Fq, toB_cons, toB_nil, toPoly_nil, map_zero, toPoly_cons, map_one, mul_zero,
    add_zero, mul_one]; ring

lemma Fq_mon : (toB Fq).Monic := by rw [Fq_eq]; monicity!

lemma Fq_deg : (toB Fq).natDegree = 2 := by rw [Fq_eq]; compute_degree!

def Fq' : BPoly ℚ := invB (shiftB Fq 0) 1 2

lemma Fq'_lit : Fq' = [[-1, -1, 0], [0, 0], [1]] := by decide +kernel

lemma Fq'_eq : toB Fq' = X ^ 2 + C (toPoly [-1, -1, 0]) := by
  rw [Fq'_lit]
  simp only [toB_cons, toB_nil, toPoly_nil, map_zero, toPoly_cons, map_one, mul_zero, add_zero,
    mul_one]; ring

lemma Fq'_mon : (toB Fq').Monic := by rw [Fq'_eq]; monicity!

lemma Fq'_deg : (toB Fq').natDegree = 2 := by rw [Fq'_eq]; compute_degree!

lemma hinv : InvOK 1 2 0 (shiftB Fq 0) := invOKb_spec (by decide +kernel)

universe u

lemma hgeo : GeomIrr.{u} Fq :=
  geomIrr_of_eis Fq Fq_mon (by rw [Fq_deg]; rfl) (by rw [Fq_deg]; norm_num) 0 (by decide +kernel)

/-- The coefficient field `ℚ` (as `ℚ[γ]/(γ)`). -/
def MM : CPoly ℚ := [0, 1]

instance : Fact (Irreducible (toPoly MM)) := ⟨Kron.irredQ_sound MM irredQ_X⟩

abbrev KK := NFC.NF MM

/-- The place data of `y′² = 1 + x′` above `x′ = 0` (two places `y′ = ±1`). -/
def PcW : PlaceCert KK := ⟨[((NFC.mk MM []), 1)], [(0, (1, ([(NFC.mk MM [1]), (NFC.mk MM [(1/2)]),
  (NFC.mk MM [(-1/8)]), (NFC.mk MM [(1/16)]), (NFC.mk MM [(-5/128)]), (NFC.mk MM [(7/256)]),
  (NFC.mk MM [(-21/1024)]), (NFC.mk MM [(33/2048)]), (NFC.mk MM [(-429/32768)]),
  (NFC.mk MM [(715/65536)])], 9))), (0, (1, ([(NFC.mk MM [(-1)]), (NFC.mk MM [(-1/2)]),
  (NFC.mk MM [(1/8)]), (NFC.mk MM [(-1/16)]), (NFC.mk MM [(5/128)]), (NFC.mk MM [(-7/256)]),
  (NFC.mk MM [(21/1024)]), (NFC.mk MM [(-33/2048)]), (NFC.mk MM [(429/32768)]),
  (NFC.mk MM [(-715/65536)])], 9)))], [[(0, (1, (NFC.mk MM [1]))), (1, (1, (NFC.mk MM [1])))]],
  [2, 0], [2], [2], 1, [6]⟩

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

/-- **`∫ θ dx` is not elementary** for `θ² = t² + t`, `t = log x` (two places at infinity, a
non-constant unit), given the `exactC2` answer (`#guard` above). -/
theorem not_elementary (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 2 + ∑ i ∈ Finset.range 2, T.evP 0 (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (hres : exactC2 Fc ks 0 ic (paramLimC Fc ks lv 0) PC rest gl = some false) :
    ¬ HasElementaryIntegral (∑ j ∈ Finset.range 2, T.evP 0 (fp.getD j []) * θ ^ j) := by
  intro h
  have hiff := T.nk_iff2U hmonF.1 hmonF.2 0 hn hcertC rfl Pp Fq (by rw [hlen]; rfl) Fq_mon
    (by rw [Fq_deg, hlen]) (by rw [hlen]; norm_num) hgeo θ
    (IsAlgClosed.lift (R := ℚ) (S := KK) (M := Cc)).toRingHom 1 2 hinv Fq'_mon
    (by show (toB Fq').natDegree = _; rw [Fq'_deg, hlen]) hpd U V (by rw [hlen]; decide) huv 1
    (by rw [hlen]; norm_num) hU1 gl dθW wθW hgl (by rw [hlen]; decide) (by rw [hlen]; exact hθ) hgen sC hs
    fp false (by rw [hlen]; exact hτg) (by rw [hlen]; exact hres)
  rw [hlen] at hiff
  exact absurd (hiff.mp h).1 (by decide)

end Curves.MT.NKInf2UEx
