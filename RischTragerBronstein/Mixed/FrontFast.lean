import RischTragerBronstein.Mixed.MTFast
import RischTragerBronstein.Mixed.FrontExpr

/-!
# The expression front end with the fast path over the line

`frontDecideF` is `frontDecide` with `elMF` in place of `elM`: over the line `y = x` the base
integrand (a rational function of `x`) is not sent to the general-curve decision.
`frontF_sound`: every answer is correct.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup

variable (Fc : BPoly ℚ)

/-- **The expression front end, fast over the line.** -/
def frontDecideF (e : EE) (N : ℕ) : Option Bool :=
  let n := e.nodesOf.length
  if curveShape Fc && certC Fc (ksOf Fc e) (lvOf Fc e) n then
    (comp Fc e.nodesOf (ksOf Fc e) n e).bind fun q ↦ elMF Fc (ksOf Fc e) (lvOf Fc e) n q N
  else none

universe u

variable {Fc} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **Every answer of `frontDecideF` is correct.** -/
theorem frontF_sound (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (e : EE) (N : ℕ)
    (b : Bool) (h : frontDecideF Fc e N = some b) (T : MTower Fc (ksOf Fc e) Cc L)
    (hn : T.n = e.nodesOf.length) (hgen : ∀ z : L, z ∈ T.F e.nodesOf.length) :
    HasElementaryIntegral (evE Fc T e.nodesOf e) ↔ b = true := by
  unfold frontDecideF at h
  by_cases hcs : (curveShape Fc && certC Fc (ksOf Fc e) (lvOf Fc e) e.nodesOf.length) = true
  · rw [if_pos hcs] at h
    simp only [Bool.and_eq_true] at hcs
    obtain ⟨hsh, hc⟩ := hcs
    rcases hq : comp Fc e.nodesOf (ksOf Fc e) e.nodesOf.length e with _ | q
    · rw [hq] at h; cases h
    · rw [hq, Option.bind_some] at h
      have hTr : T.Tr e.nodesOf.length :=
        (T.mspecs hmon hdeg (lvOf Fc e) e.nodesOf.length (by omega) hc).hyp.tr
      rw [← comp_spec Fc T e.nodesOf e.nodesOf.length hTr e q hq]
      exact (elMF_sound hmon hdeg hsh T _ hn hc hgen q N b h).1
  · rw [if_neg hcs] at h; cases h

end Curves.MT.Front
