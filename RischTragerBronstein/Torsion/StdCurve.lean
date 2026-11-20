import RischTragerBronstein.Torsion.HenselBranch
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The standard curve over any field

`stdCurve C F`: for `F ∈ C[x][Y]` monic of positive degree and irreducible over `C(x)`, the curve
`F(x, y) = 0` with function field inside the algebraic closure of `C(x)` (any characteristic).
-/

open Polynomial

namespace Curves

section Std

variable (C : Type*) [Field C]

/-- `C[x] → C(x) → (C(x))‾`. -/
noncomputable abbrev toAC : C[X] →+* AlgebraicClosure (RatFunc C) :=
  (algebraMap (RatFunc C) (AlgebraicClosure (RatFunc C))).comp (algebraMap C[X] (RatFunc C))

variable {C}

lemma toAC_injective : Function.Injective (toAC C) := fun a b h ↦
  IsFractionRing.injective C[X] (RatFunc C) ((algebraMap (RatFunc C) _).injective h)

lemma exists_root_std (F : C[X][X]) (hF : F.Monic) (hd : 0 < F.natDegree) :
    ∃ y : AlgebraicClosure (RatFunc C), (F.map (toAC C)).eval y = 0 := by
  have hdeg : (F.map (toAC C)).degree ≠ 0 := by
    rw [degree_map_eq_of_injective toAC_injective, degree_eq_natDegree hF.ne_zero]
    exact_mod_cast hd.ne'
  exact IsAlgClosed.exists_root _ hdeg

lemma aeval_X_std (P : C[X]) :
    aeval (algebraMap (RatFunc C) (AlgebraicClosure (RatFunc C)) RatFunc.X) P = toAC C P := by
  rw [aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap]
  rfl

lemma map_aeval_std (F : C[X][X]) :
    F.map (aeval (algebraMap (RatFunc C) (AlgebraicClosure (RatFunc C)) RatFunc.X)).toRingHom =
      F.map (toAC C) := by
  congr 1
  exact RingHom.ext fun P ↦ aeval_X_std P

/-- **The standard curve** `F(x, y) = 0` over any field. -/
noncomputable def stdCurve (F : C[X][X]) (hF : F.Monic) (hd : 0 < F.natDegree)
    (hirr : Irreducible (F.map (algebraMap C[X] (RatFunc C)))) :
    CurveData C (AlgebraicClosure (RatFunc C)) where
  x := algebraMap (RatFunc C) (AlgebraicClosure (RatFunc C)) RatFunc.X
  y := Classical.choose (exists_root_std F hF hd)
  F := F
  htr := (transcendental_algebraMap_iff (algebraMap (RatFunc C) _).injective).mpr
    RatFunc.transcendental_X
  monic := hF
  irr := by
    intro G hG hGy
    rw [map_aeval_std] at hGy
    set y := Classical.choose (exists_root_std F hF hd)
    have hy := Classical.choose_spec (exists_root_std F hF hd)
    -- `F` mapped to `C(x)` is the minimal polynomial of `y`
    set F' := F.map (algebraMap C[X] (RatFunc C)) with hF'
    have hF'm : F'.Monic := hF.map _
    have hint : IsIntegral (RatFunc C) y := ⟨F', hF'm, by
      rw [hF', Polynomial.eval₂_map, ← eval_map]; exact hy⟩
    have hmin : minpoly (RatFunc C) y = F' :=
      (minpoly.eq_of_irreducible_of_monic hirr (by
        rw [aeval_def, hF', eval₂_map, ← eval_map]; exact hy) hF'm).symm
    set G' := G.map (algebraMap C[X] (RatFunc C)) with hG'
    have hG'y : aeval y G' = 0 := by rw [aeval_def, hG', eval₂_map, ← eval_map]; exact hGy
    by_contra hG0
    have hG'0 : G' ≠ 0 := by
      rw [hG', Ne, Polynomial.map_eq_zero_iff (IsFractionRing.injective C[X] (RatFunc C))]
      exact hG0
    have := natDegree_le_natDegree (minpoly.degree_le_of_ne_zero (RatFunc C) y hG'0 hG'y)
    rw [hmin, hF', natDegree_map_eq_of_injective (IsFractionRing.injective C[X] (RatFunc C)),
      hG', natDegree_map_eq_of_injective (IsFractionRing.injective C[X] (RatFunc C))] at this
    omega
  root := by
    rw [map_aeval_std]
    exact Classical.choose_spec (exists_root_std F hF hd)

end Std

end Curves
