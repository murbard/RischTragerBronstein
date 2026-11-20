import RischTragerBronstein.Torsion.RaisePrec
import RischTragerBronstein.Torsion.ValidBase

/-!
# Raising the precision of valid problems

**`raise_valid`**: a valid problem stays valid when the precision of all its branch data (at the
points and at infinity) is raised above any bound, over the same field and with the same points
and parametrizations (`raise_certCheck`).
-/

open Polynomial

namespace Curves

open CPoly Sup

section Raise

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Raising the precision of a valid problem.** -/
theorem raise_valid (P : CurveProb F) (hv : P.valid = true) (B : ℕ) :
    ∃ P' : CurveProb F, P'.Fc = P.Fc ∧ P'.n = P.n ∧ P'.k = P.k ∧ P'.A = P.A ∧ P'.D = P.D ∧
      P'.pts.map Prod.fst = P.pts.map Prod.fst ∧
      P'.pts.map (fun ac ↦ (ac.1, ac.2.N)) = P.pts.map (fun ac ↦ (ac.1, ac.2.N)) ∧
      (∀ ac ∈ P'.pts, B ≤ ac.2.prec) ∧
      B ≤ P'.inf.prec ∧ P'.inf.N = P.inf.N ∧ P'.valid = true := by
  classical
  obtain ⟨hN, hpts, hinf, hcov, hmu, hinfp⟩ := certs_of_valid P hv
  have hr : ∀ ac ∈ P.pts, ∃ c' : BranchCert F, c'.N = ac.2.N ∧ B ≤ c'.prec ∧ ac.2.prec ≤ c'.prec ∧
      certCheck P.Fc P.n ac.1 c' = true := fun ac hac ↦ by
    obtain ⟨c', h1, h2, h3, -, -, h4⟩ := raise_certCheck (hpts ac hac) B
    exact ⟨c', h1, h2, h3, h4⟩
  choose f hfN hfB hfp hfc using hr
  obtain ⟨ci, hciN, hciB, hcip, -, -, hcic⟩ := raise_certCheck hinf B
  set pts' := P.pts.attach.map fun ac ↦ (ac.1.1, f ac.1 ac.2) with hpts'
  set P' : CurveProb F := ⟨P.Fc, P.n, P.k, P.A, P.D, pts', ci⟩ with hP'
  have hfst : pts'.map Prod.fst = P.pts.map Prod.fst := by
    simp only [hpts', List.map_map, Function.comp_def]
    conv_rhs => rw [← List.attach_map_subtype_val P.pts, List.map_map]
    rfl
  have hpN : pts'.map (fun ac ↦ (ac.1, ac.2.N)) = P.pts.map (fun ac ↦ (ac.1, ac.2.N)) := by
    simp only [hpts', List.map_map, Function.comp_def, hfN]
    conv_rhs => rw [← List.attach_map_subtype_val P.pts, List.map_map]
    rfl
  refine ⟨P', rfl, rfl, rfl, rfl, rfl, hfst, hpN, fun ac hac ↦ ?_, hciB, hciN, ?_⟩
  · obtain ⟨⟨ac0, h0⟩, -, rfl⟩ := List.mem_map.mp hac
    exact hfB ac0 h0
  refine valid_of_shapeOK P' (shapeOK_of_valid P hv) (by rw [hciN]; exact hN) ?_ hcic ?_ ?_ ?_
  · intro ac hac
    obtain ⟨⟨ac0, h0⟩, -, rfl⟩ := List.mem_map.mp hac
    exact hfc ac0 h0
  · show coverCheck (mul P.D (discRC P.Fc P.n P.k)) (pts'.map Prod.fst) = true
    rw [hfst]; exact hcov
  · intro ac hac
    obtain ⟨⟨ac0, h0⟩, -, rfl⟩ := List.mem_map.mp hac
    obtain ⟨m1, m2, m3, m4⟩ := hmu ac0 h0
    have e1 : P'.muFin ac0.1 (f ac0 h0).N = P.muFin ac0.1 ac0.2.N := by rw [hfN]; rfl
    have e2 : P'.mufFin ac0.1 (f ac0 h0).N = P.mufFin ac0.1 ac0.2.N := by rw [hfN]; rfl
    have e3 : P'.QFin ac0.1 (f ac0 h0).N = P.QFin ac0.1 ac0.2.N := by rw [hfN]; rfl
    have e4 : P'.QfFin ac0.1 (f ac0 h0).N = P.QfFin ac0.1 ac0.2.N := by rw [hfN]; rfl
    have hp := hfp ac0 h0
    refine ⟨?_, ?_, ?_, ?_⟩
    · show P'.muFin ac0.1 (f ac0 h0).N < (f ac0 h0).prec
      rw [e1]; omega
    · show P'.mufFin ac0.1 (f ac0 h0).N < (f ac0 h0).prec + (f ac0 h0).N
      rw [e2, hfN]; omega
    · show P'.muFin ac0.1 (f ac0 h0).N < (P'.QFin ac0.1 (f ac0 h0).N).length
      rw [e1, e3]; exact m3
    · show P'.mufFin ac0.1 (f ac0 h0).N < (P'.QfFin ac0.1 (f ac0 h0).N).length
      rw [e2, e4]; exact m4
  · have e1 : P'.sbInf = P.sbInf := by
      simp only [CurveProb.sbInf, hP']; rw [hciN]; rfl
    have e2 : P'.sfInf = P.sfInf := by
      simp only [CurveProb.sfInf, hP']; rw [hciN]; rfl
    rw [e1, e2]
    show -P.sbInf ≤ (ci.prec : ℤ) ∧ (ci.N : ℤ) - P.sfInf < ci.prec
    rw [hciN]
    have : (P.inf.prec : ℤ) ≤ ci.prec := by exact_mod_cast hcip
    exact ⟨hinfp.1.trans this, lt_of_lt_of_le hinfp.2 this⟩

end Raise

end Curves
