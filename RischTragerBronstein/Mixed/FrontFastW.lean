import RischTragerBronstein.Mixed.MTFastW
import RischTragerBronstein.Mixed.FrontFast
import RischTragerBronstein.Mixed.FrontIntegrate

/-!
# The expression front end with antiderivatives, fast over the line

`frontIntegrateF` is `frontIntegrate` with `elMWF` in place of `elMW`.
`frontIntegrateF_valid`: every returned antiderivative is valid; `frontIntegrateF_none`: the
answer "not elementary" is correct. `integrateShowF` prints the answer.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup EE

variable (Fc : BPoly ℚ)

/-- **The front end with the antiderivative, fast over the line.** -/
def frontIntegrateF (e : EE) (N : ℕ) : Option (Option (ADW e.nodesOf.length)) :=
  if curveShape Fc && certC Fc (ksOf Fc e) (lvOf Fc e) e.nodesOf.length then
    (comp Fc e.nodesOf (ksOf Fc e) e.nodesOf.length e).bind fun q ↦
      elMWF Fc (ksOf Fc e) (lvOf Fc e) e.nodesOf.length q N
  else none

/-- **Integrate and print**, fast over the line. -/
def integrateShowF (e : EE) (N : ℕ) : List String :=
  match frontIntegrateF Fc e N with
  | none => ["no answer at this bound"]
  | some none => ["not elementary"]
  | some (some w) => "elementary; tower:" :: nodesRender e ++
      "antiderivative = sum of the pieces:" :: ADW.render Fc (ksOf Fc e) N _ w

universe u

variable {Fc} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **Every antiderivative returned by `frontIntegrateF` is valid.** -/
theorem frontIntegrateF_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (e : EE) (N : ℕ) (w : ADW e.nodesOf.length) (h : frontIntegrateF Fc e N = some (some w))
    (T : MTower Fc (ksOf Fc e) Cc L) (hn : T.n = e.nodesOf.length)
    (hgen : ∀ z : L, z ∈ T.F e.nodesOf.length) :
    ∃ q, T.ev e.nodesOf.length q = evE Fc T e.nodesOf e ∧
      T.ValidW e.nodesOf.length q w := by
  unfold frontIntegrateF at h
  split_ifs at h with hcs
  simp only [Bool.and_eq_true] at hcs
  obtain ⟨hsh, hc⟩ := hcs
  obtain ⟨q, hq, hw⟩ := Option.bind_eq_some_iff.mp h
  have hTr : T.Tr e.nodesOf.length :=
    (T.mspecs hmon hdeg (lvOf Fc e) e.nodesOf.length (by omega) hc).hyp.tr
  exact ⟨q, comp_spec Fc T e.nodesOf e.nodesOf.length hTr e q hq,
    elMWF_valid hmon hdeg hsh T e.nodesOf.length hn hc hgen q N w hw⟩

/-- **The answer "not elementary" of `frontIntegrateF` is correct.** -/
theorem frontIntegrateF_none (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (e : EE) (N : ℕ) (h : frontIntegrateF Fc e N = some none)
    (T : MTower Fc (ksOf Fc e) Cc L) (hn : T.n = e.nodesOf.length)
    (hgen : ∀ z : L, z ∈ T.F e.nodesOf.length) :
    ¬HasElementaryIntegral (evE Fc T e.nodesOf e) := by
  unfold frontIntegrateF at h
  split_ifs at h with hcs
  simp only [Bool.and_eq_true] at hcs
  obtain ⟨hsh, hc⟩ := hcs
  obtain ⟨q, hq, hw⟩ := Option.bind_eq_some_iff.mp h
  have hTr : T.Tr e.nodesOf.length :=
    (T.mspecs hmon hdeg (lvOf Fc e) e.nodesOf.length (by omega) hc).hyp.tr
  rw [← comp_spec Fc T e.nodesOf e.nodesOf.length hTr e q hq]
  exact elMWF_none hmon hdeg hsh T e.nodesOf.length hn hc hgen q N hw

end Curves.MT.Front
