import RischTragerBronstein.Torsion.PlacePrimeExist5

/-!
# Structural facts on the place certificates `PcE tx`

* `PcE_pl_mem`: every place entry of `PcE tx` has precision `> tx` and at most the length of its
  approximation;
* `PcE_pp_gt`, `PcE_pp_le_len`, `PcE_tp_ge`: the corresponding statements by index.
-/

open Polynomial HahnSeries EllQuad.QCoords

namespace Curves

open CPoly Sup

section PcE

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [CharZero L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L) (P : CurveProb F) {ψ : F →+* C}
  (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) (hV : P.ValidFacts)
  (hζ : ∀ ac ∈ P.pts, ∃ ζF : F, IsPrimitiveRoot (ψ ζF) ac.2.N) (j₀ : Fin (dim F))

lemma PcE_pl_mem (tx : ℕ) : ∀ x ∈ (S.PcE P hSF hV hζ j₀ tx).pl,
    tx < x.2.2.2 ∧ x.2.2.2 ≤ x.2.2.1.length := by
  intro x hx
  simp only [PcE, assemble, List.mem_flatten, plBlocks, List.mem_map, List.mem_range] at hx
  obtain ⟨_, ⟨j, hj, rfl⟩, hx⟩ := hx
  rw [S.Ls_length P hSF hV hζ j₀ tx] at hj
  rw [S.Ls_getD P hSF hV hζ j₀ j hj tx] at hx
  simp only [LocPlaces.placeList, lpj, SplitFibre.locPlaces, List.map_map, List.mem_map,
    Function.comp_apply] at hx
  obtain ⟨π, -, rfl⟩ := hx
  simp only [SplitFibre.yF, SplitFibre.ppF, List.length_map, List.length_range]
  omega

lemma PcE_pp_facts (tx : ℕ) (π : ℕ) (hπ : π < (S.PcE P hSF hV hζ j₀ tx).pl.length) :
    tx < (S.PcE P hSF hV hζ j₀ tx).pp π ∧
      (S.PcE P hSF hV hζ j₀ tx).pp π ≤ ((S.PcE P hSF hV hζ j₀ tx).py π).length := by
  have h := S.PcE_pl_mem P hSF hV hζ j₀ tx _ (List.getElem_mem hπ)
  simp only [PlaceCert.pp, PlaceCert.py, List.getD_eq_getElem _ _ hπ]
  exact h

lemma PcE_tp_ge (tx : ℕ) (j : ℕ) (hj : j < P.pts.length) :
    tx ≤ (S.PcE P hSF hV hζ j₀ tx).tp.getD j 0 ∧
      (S.PcE P hSF hV hζ j₀).tp.getD j 0 ≤ (S.PcE P hSF hV hζ j₀ tx).tp.getD j 0 := by
  rw [S.PcE_tp P hSF hV hζ j₀ tx hj, S.PcE_tp P hSF hV hζ j₀ 0 hj]
  omega

end CurveData

end PcE

end Curves
