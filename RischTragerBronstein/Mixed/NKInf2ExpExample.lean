import RischTragerBronstein.Mixed.NKInf2ExpDecide
import RischTragerBronstein.Mixed.NKInf2Example

/-!
# Example: two places at infinity over `eˣ`

Tower `x`, `t = eˣ`, and the curve of `Mixed/NKInf2Example`, `θ² = t (1 + 25 t)(1 − 2 t)(1 − 50 t)`:
two places at infinity (their difference certified non-torsion: `NKInf2Ex.hcert2`, kernel-checked)
and a single place above `t = 0` (`nkShape0`: `ord₀ a₀ = 1`). By `nk_iffET2`, with the basis normal
at infinity (`nkTc`), `τ(θ) = 0` and `exactT` answering `some false` (`#guard`; it enters
`not_elementary` as the hypothesis `hres`): **`∫ √(eˣ (1 + 25eˣ)(1 − 2eˣ)(1 − 50eˣ)) dx` is not
elementary**.
-/

namespace Curves.MT.NKInf2ExpEx

open Curves Curves.LT Curves.MT CPoly Sup Tower.Sys Curves.MT.NKExEE Polynomial Differential

abbrev Fq : BPoly ℚ := NKInf2Ex.Fq

def Pp : List (GPoly (LC 0)) := liftCurve Fc ks 0 2 Fq
def PC : GPoly (LC 1) := nkPC Fc ks 0 Pp
/-- Power sums `s₀ = 2`, `s₁ = 0`. -/
def sC : List (LC 1) := [(MOr Fc ks 1).natCast 2, zer]
/-- `f = θ`. -/
def fp : List (GPoly (LC 0)) := [[], [one0]]
def rest : List (LC 1) := nkRest Fc ks 0 (nkFl Fc ks 0 fp) (nkTau Fc ks 0 2 (nkFl Fc ks 0 fp) sC)

#guard nkShape Fc ks 0 Pp = false
-- `θ` is not exact (in the basis normal at infinity)
#guard exactT Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC (nkTc Fc ks 0 Pp) (nkTi Fc ks 0 Pp)
  rest = some false

set_option maxRecDepth 200000 in
lemma hcertC : certC Fc ks lv 1 = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hsh0 : nkShape0 Fc ks 0 Pp = true := by decide +kernel

set_option maxRecDepth 200000 in
lemma hs : traceC Fc ks 0 PC sC = true := by decide +kernel

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
  simp [NKInf2Ex.Fq] at this

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L] [IsAlgClosed Cc]

/-- **`∫ θ dx` is not elementary** for `θ² = t (1 + 25 t)(1 − 2 t)(1 − 50 t)`, `t = eˣ`, given the
`exactT` answer (`#guard` above). -/
theorem not_elementary (T : MTower Fc ks Cc L) (hn : T.n = 1) (θ : L)
    (hθ : θ ^ 2 + ∑ i ∈ Finset.range 2, T.evP 0 (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (hres : exactT Fc ks 0 (expSysT Fc ks 0 xc (rdeE Fc ks lv 0)) PC (nkTc Fc ks 0 Pp)
      (nkTi Fc ks 0 Pp) rest = some false) :
    ¬ HasElementaryIntegral (∑ j ∈ Finset.range 2, T.evP 0 (fp.getD j []) * θ ^ j) := by
  intro h
  have hiff := T.nk_iffET2 hmonF.1 hmonF.2 0 hn hcertC rfl Pp Fq (by rw [hlen]; rfl)
    NKInf2Ex.Fq_mon (by rw [NKInf2Ex.Fq_deg, hlen]) (by rw [hlen]; norm_num) NKInf2Ex.hgeo hsh0 ha0Q
    (IsAlgClosed.lift (R := ℚ) (S := NKInf2Ex.KK) (M := Cc)).toRingHom 2 4 NKInf2Ex.hinv
    NKInf2Ex.Fq'_mon (by show (toB NKInf2Ex.Fq').natDegree = _; rw [NKInf2Ex.Fq'_deg, hlen])
    NKInf2Ex.hcert2 θ (by rw [hlen]; exact hθ) hgen sC hs fp _ _ false (by rw [hlen]; exact hres)
  rw [hlen] at hiff
  exact absurd (hiff.mp h).1 (by decide)

end Curves.MT.NKInf2ExpEx
