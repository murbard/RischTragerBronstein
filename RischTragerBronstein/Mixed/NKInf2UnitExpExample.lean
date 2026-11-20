import RischTragerBronstein.Mixed.NKInf2UnitExpDecide
import RischTragerBronstein.Mixed.NKExpExamples
import RischTragerBronstein.Mixed.NKInf2UnitExample

/-!
# Example: an elementary integral over `eˣ` with two places at infinity

Tower `x`, `t = eˣ`, and `θ² = t² + t` (two places at infinity, a single place above `t = 0`), with
the non-constant unit `u₀ = θ + t + 1/2` (`u₀′/u₀ = θ/(t + 1)`, certified by `logDerChk`, trace
`0`). By `nk_iffET2U`, `∫ θ dx` is elementary iff `θ − c u₀′/u₀` is exact for some constant `c`
(`τ(θ) = 0`), and `exactT2` (exponential solver, basis normal at infinity) answers `some true`
(`#guard`; the hypothesis `hres` of `elementary`): **`∫ √(e²ˣ + eˣ) dx` is elementary**
(`= √(e²ˣ + eˣ) + ½ log(2eˣ + 1 + 2√(e²ˣ + eˣ))`). The single-place theory does not apply
(`nkShape` fails), and the logarithm is the unit `u₀`.
-/

namespace Curves.MT.NKInf2UEEx

open Curves Curves.LT Curves.MT CPoly Sup Tower.Sys Curves.MT.NKExEE Polynomial Differential GTors

/-- `θ² − (t + t²)` (the curve of `NKInf2UEx`). -/
abbrev Fq : BPoly ℚ := NKInf2UEx.Fq

def Pp : List (GPoly (LC 0)) := liftCurve Fc ks 0 2 Fq
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
/-- Power sums `s₀ = 2`, `s₁ = 0`. -/
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 2, zer]
def cq (q : ℚ) : LC 0 := [([q], [1])]
/-- `u₀ = θ + t + 1/2` and its inverse `4 (t + 1/2) − 4 θ`. -/
def U : List (GPoly (LC 0)) := [[cq (1/2), cq 1], [cq 1]]
def V : List (GPoly (LC 0)) := [[cq 2, cq 4], [cq (-4)]]
/-- `u₀′/u₀ = θ/(t + 1)`, `θ′ = θ (t + 1/2)/(t + 1)`, `1/P_θ = θ/(2(t + t²))`. -/
def gl : GPoly (LC 1) := [([], [[([1], [1])]]), ([[([1], [1])]], [[([1], [1])], [([1], [1])]])]
def dθW : GPoly (LC 1) :=
  [([], [[([1], [1])]]), ([[([1 / 2], [1])], [([1], [1])]], [[([1], [1])], [([1], [1])]])]
def wθW : GPoly (LC 1) := [([], [[([1], [1])]]), ([[([1 / 2], [1])]], [[], [([1], [1])], [([1], [1])]])]
/-- `f = θ`. -/
def fp : List (GPoly (LC 0)) := [[], [one0]]
def rest : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fp) (nkTau Fc ks 0 2 (nkFl Fc ks 0 fp) sC)

#guard nkShape Fc ks 0 Pp = false
-- `θ − c u₀′/u₀` is exact for some `c`
#guard exactT2 Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC (nkTc Fc ks 0 Pp) (nkTi Fc ks 0 Pp)
  rest gl = some true

set_option maxRecDepth 200000 in
lemma hcertC : certC Fc ks lv 1 = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hsh0 : nkShape0 Fc ks 0 Pp = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hs : traceC Fc ks 0 PC sC = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma huv : unitC Fc ks 0 Pp U V = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hgl : logDerChk Fc ks 0 Pp U V gl dθW wθW = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hτg : (MOr Fc ks 1).isZero (nkTau Fc ks 0 2 gl sC) = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hτf : (MOr Fc ks 1).isZero (nkTau Fc ks 0 2 (nkFl Fc ks 0 fp) sC) = true := by
  decide +kernel

lemma hU1 : GPoly.trim (MO Fc ks 0) (U.getD 1 []) ≠ [] :=
  List.ne_nil_of_length_pos (by decide +kernel)

lemma hmonF : (toB Fc).Monic ∧ (toB Fc).natDegree = cvN Fc := by
  have e : toB Fc = X + Polynomial.C (-X) := by
    simp [toB, CPoly.toPoly, add_comm]
  rw [e]
  exact ⟨monic_X_add_C _, by rw [natDegree_X_add_C]; rfl⟩

lemma hlen : Pp.length = 2 := by simp [Pp, liftCurve]

lemma ha0Q : (toB Fq).coeff 0 ≠ 0 := by
  rw [coeff_toB]
  intro h
  have := congrArg (fun p : ℚ[X] ↦ p.coeff 1) h
  simp [NKInf2UEx.Fq] at this

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L] [IsAlgClosed Cc]

/-- **`∫ θ dx` is elementary** for `θ² = t² + t`, `t = eˣ`, given the `exactT2` answer (`#guard`
above). -/
theorem elementary (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 2 + ∑ i ∈ Finset.range 2, T.evP 0 (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (hres : exactT2 Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC (nkTc Fc ks 0 Pp)
      (nkTi Fc ks 0 Pp) rest gl = some true) :
    HasElementaryIntegral (∑ j ∈ Finset.range 2, T.evP 0 (fp.getD j []) * θ ^ j) := by
  have hTr : T.Tr 1 := (T.mspecs hmonF.1 hmonF.2 lv 1 (by omega) hcertC).hyp.tr
  have hiff := T.nk_iffET2U hmonF.1 hmonF.2 0 hn hcertC rfl Pp Fq (by rw [hlen]; rfl)
    NKInf2UEx.Fq_mon (by rw [NKInf2UEx.Fq_deg, hlen]) (by rw [hlen]; norm_num) NKInf2UEx.hgeo hsh0
    ha0Q (IsAlgClosed.lift (R := ℚ) (S := NKInf2UEx.KK) (M := Cc)).toRingHom 1 2 NKInf2UEx.hinv
    NKInf2UEx.Fq'_mon (by show (toB NKInf2UEx.Fq').natDegree = _; rw [NKInf2UEx.Fq'_deg, hlen])
    NKInf2UEx.hpd U V (by rw [hlen]; decide) huv 1 (by rw [hlen]; norm_num) hU1 gl dθW wθW hgl
    (by rw [hlen]; decide) θ (by rw [hlen]; exact hθ) hgen sC hs fp _ _ true
    (by rw [hlen]; exact hτg) (by rw [hlen]; exact hres)
  rw [hlen] at hiff
  refine hiff.mpr ⟨rfl, ?_⟩
  have h0 : T.ev 1 (nkTau Fc ks 0 2 (nkFl Fc ks 0 fp) sC) = 0 := by
    rw [← T.coe_sem_MPr 1 hTr, ((T.MPr 1 hTr).isZero_iff _).mp hτf]
    rfl
  rw [h0, show (0 : L) = (0 : L)′ from (Derivation.map_zero _).symm]
  exact hasElementaryIntegral_of_deriv _

end Curves.MT.NKInf2UEEx
