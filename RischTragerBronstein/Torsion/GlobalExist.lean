import RischTragerBronstein.Torsion.NonTorsExist2
import RischTragerBronstein.Torsion.IBExist8

/-!
# Global certificates exist

**`exists_globalCert`**: for a valid problem over `F` (characteristic `0`) with distinct special
points, whose curve is given over `F`, there is a global certificate without divisor data
(`αL = []`) for the curve of the problem passing `globalCheck`: the integral basis of
`exists_ibCert` certified at the special points of the problem and at infinity.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Global

variable {F E : Type*} [Field F] [CharZero F] [DecidableEq F] [Field E] [Algebra F E]

lemma shapeCheck_of_valid {P : CurveProb F} (h : P.valid = true) :
    shapeCheck P.Fc P.n P.k = true ∧ ∀ j < P.Fc.length, (P.Fc.getD j []).length ≤ P.k + 1 := by
  simp only [CurveProb.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := h
  refine ⟨?_, h7⟩
  simp only [shapeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Nat.zero_add]
  exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

/-- **Global certificates exist.** -/
theorem exists_globalCert (P : CurveProb F) (hvalid : P.valid = true) (hV : P.ValidFacts)
    (hnd : (P.pts.map Prod.fst).Nodup) (SF : CurveData F E) (hSF : SF.F = toB P.Fc) :
    ∃ T : GlobalCert F, T.globalCheck = true ∧ T.Fc = P.Fc ∧ T.n = P.n ∧ T.αL = [] ∧
      T.yL = [] ∧ T.I.pts.map Prod.fst = P.pts.map Prod.fst := by
  have hnS : SF.F.natDegree = P.n := by rw [hSF, hV.deg]
  have hsh := (shapeCheck_of_valid hvalid).1
  have hR0 : toPoly P.R0 ≠ 0 := by
    intro h0
    have := hV.R0l
    rw [(trim_eq_nil_iff P.R0).mpr h0] at this
    simp at this
  have hdisc0 : toPoly (discRC P.Fc P.n P.k) ≠ 0 := by
    intro h0
    apply hR0
    rw [CurveProb.R0, toPoly_trim, toPoly_mul, h0, zero_mul]
  have hdisc : coverCheck (discRC P.Fc P.n P.k) (P.pts.map Prod.fst) = true := by
    refine coverCheck_complete _ _ hdisc0 (algebraMap F (AlgebraicClosure F)) fun z hz ↦ ?_
    refine coverCheck_spec _ _ hV.cover (algebraMap F (AlgebraicClosure F)) z ?_
    rw [toPoly_mul, Polynomial.map_mul, eval_mul, hz, mul_zero]
  obtain ⟨I, hib, hnorm, hDl, hpts⟩ := SF.exists_ibCert P.Fc hSF P.k P.k (by rw [hnS]; exact hsh)
    P.pts (fun p hp ↦ by rw [hnS]; exact hV.certs p hp) hnd (by rw [hnS]; exact hdisc0)
    (by rw [hnS]; exact hdisc) P.inf (by rw [hnS]; exact hV.certInf)
  refine ⟨⟨P.Fc, P.n, P.k, P.k, I, 0, [], [], [], [], 0⟩, ?_, rfl, rfl, rfl, rfl, hpts⟩
  rw [hnS] at hib
  simp only [GlobalCert.globalCheck, GlobalCert.G, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨hib, by rw [hnS] at hnorm; exact hnorm⟩, hDl⟩, (shapeCheck_of_valid hvalid).2⟩, ?_⟩, rfl⟩, by simp⟩
  simp [GlobalCert.ptCheck]

end Global

end Curves
