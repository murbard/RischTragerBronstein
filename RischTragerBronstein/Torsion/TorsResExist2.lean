import RischTragerBronstein.Torsion.TorsResExist1
import RischTragerBronstein.Torsion.IBExist6

/-!
# Residue data at places from a valid problem (1): the fibres

For a valid problem `P` over `F` on a curve `S` over `C` (`S.F` the image of `P.Fc` under `ψ`):

* `fibreΦ`: the split fibre above a special point `ac ∈ P.pts` (the roots over `F` of `fin_roots_F`,
  mapped to `C`);
* `resFin_fibre`: the computed residue along the approximations of the local place data is the
  residue along the root; `resFin_fibre_rep`: it only depends on the place.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open CPoly Sup Differential LaurentSeries

section Fib

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [CharZero L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L) (P : CurveProb F) {ψ : F →+* C}
  (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) (hV : P.ValidFacts)

include hSF hV in
lemma exists_fibre (ac : F × BranchCert F) (hac : ac ∈ P.pts) :
    ∃ y : Fin S.F.natDegree → PowerSeries F, Function.Injective y ∧
      ((toB P.Fc).map (mapRingHom ψ)).map (branchSub (C := C) (K := C) ac.2.N (ψ ac.1)) =
        ∏ k, (X - Polynomial.C (ofPowerSeries ℤ C (PowerSeries.map ψ (y k)))) := by
  obtain ⟨y, hy, hs⟩ := S.fin_roots_F (K := C) P ψ hSF hV ac hac
  refine ⟨y, hy, ?_⟩
  rw [← hSF]
  simpa [Algebra.algebraMap_self] using hs

/-- **The split fibre above a special point.** -/
noncomputable def fibreΦ (ac : F × BranchCert F) (hac : ac ∈ P.pts) :
    SplitFibre (C := C) (K := C) ((toB P.Fc).map (mapRingHom ψ)) S.F.natDegree where
  a := ψ ac.1
  N := ac.2.N
  hN := N_pos_of_certCheck (hV.certs ac hac)
  y := fun k ↦ PowerSeries.map ψ (Classical.choose (S.exists_fibre P hSF hV ac hac) k)
  inj := fun k l h ↦ (Classical.choose_spec (S.exists_fibre P hSF hV ac hac)).1
    (PowerSeries.map_injective ψ ψ.injective h)
  split := (Classical.choose_spec (S.exists_fibre P hSF hV ac hac)).2

lemma fibreΦ_a (ac : F × BranchCert F) (hac : ac ∈ P.pts) : (S.fibreΦ P hSF hV ac hac).a = ψ ac.1 := rfl

lemma fibreΦ_N (ac : F × BranchCert F) (hac : ac ∈ P.pts) : (S.fibreΦ P hSF hV ac hac).N = ac.2.N := rfl

/-- The coefficients of the roots are images of elements of `F`. -/
lemma fibreΦ_coeff (ac : F × BranchCert F) (hac : ac ∈ P.pts) (k : Fin S.F.natDegree) (i : ℕ) :
    PowerSeries.coeff i ((S.fibreΦ P hSF hV ac hac).y k) ∈ Set.range ψ := by
  simp only [fibreΦ, PowerSeries.coeff_map]
  exact ⟨_, rfl⟩

end CurveData

end Fib

end Curves
