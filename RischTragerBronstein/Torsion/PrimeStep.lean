import RischTragerBronstein.Torsion.Gcd

/-!
# From a good prime to a bound on torsion (general curves)

Auxiliary lemmas relating the base-field data of a curve and its images under a field embedding
`φ : C → K₀`: `basisSer_map`, `basisSer_lowerBd`, `princTest_cast`, `split_map`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section Aux

variable {C C' : Type*} [Field C] [Field C']

lemma lmap_eval (φ : C →+* C') (W : C[X][X]) (N : ℕ) (a : C) (r : LaurentSeries C) :
    lmap φ ((W.map (branchSub (C := C) (K := C) N a)).eval r) =
      ((W.map (mapRingHom φ)).map (branchSub (C := C') (K := C') N (φ a))).eval (lmap φ r) := by
  rw [eval_map, eval_map, hom_eval₂, eval₂_map]
  congr 1
  refine RingHom.ext fun P ↦ ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, coe_mapRingHom, lmap_branchSub']

lemma basisSer_map (φ : C →+* C') {n : ℕ} (B : Fin n → C[X][X]) (D : C[X]) (N : ℕ) (a : C)
    (r : LaurentSeries C) (i : Fin n) :
    lmap φ (basisSer B D N a r i) =
      basisSer (fun i ↦ (B i).map (mapRingHom φ)) (D.map φ) N (φ a) (lmap φ r) i := by
  rw [basisSer, basisSer, map_mul, map_inv₀, lmap_eval, lmap_branchSub']

lemma princTest_cast {n n' : ℕ} (h : n' = n) (δ : Fin n → ℕ) (M : ℕ) {Q : Type*} (e : Q → ℕ)
    (a : Q → C) (σ : Q → Fin n → LaurentSeries C) (b : Q → ℕ) :
    princTest (fun i ↦ δ (Fin.cast h i)) M e a (fun q i ↦ σ q (Fin.cast h i)) b ↔
      princTest δ M e a σ b := by
  subst h
  simp only [Fin.cast_eq_self]

end Aux

end Curves
