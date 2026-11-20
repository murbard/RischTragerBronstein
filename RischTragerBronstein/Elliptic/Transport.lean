import RischTragerBronstein.Elliptic.NLBound
import RischTragerBronstein.Elliptic.Abel

/-!
# Rational points in a field extension

`toK K : (EllNL.W a b c)(ℚ) →+ (EllAbel.W a b c)(K)`, injective, `(α, β) ↦ (α, β)`, for a field
`K` of characteristic zero. Finite order in `K` implies finite order over `ℚ`.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace EllNL

/-- Points of equal curves. -/
def ptEquiv {K : Type*} [Field K] [DecidableEq K] {W1 W2 : WeierstrassCurve K} (h : W1 = W2) :
    W1.toAffine.Point ≃+ W2.toAffine.Point := by
  subst h; exact AddEquiv.refl _

lemma ptEquiv_some {K : Type*} [Field K] [DecidableEq K] {W1 W2 : WeierstrassCurve K}
    (h : W1 = W2) {x y : K} (hx : W1.toAffine.Nonsingular x y) (hy : W2.toAffine.Nonsingular x y) :
    ptEquiv h (Point.some x y hx) = Point.some x y hy := by
  subst h; rfl

variable (a b c : ℤ) (K : Type*) [Field K] [CharZero K] [DecidableEq K]

lemma baseChange_Q : (W a b c).baseChange ℚ = W a b c := by
  simp [W, WeierstrassCurve.baseChange, WeierstrassCurve.map]

lemma baseChange_K : (W a b c).baseChange K = EllAbel.W (a : K) (b : K) (c : K) := by
  simp [W, EllAbel.W, WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- The embedding of rational points. -/
noncomputable def toK : (W a b c).toAffine.Point →+ (EllAbel.W (a : K) (b : K) (c : K)).toAffine.Point :=
  (ptEquiv (baseChange_K a b c K)).toAddMonoidHom.comp
    ((Point.map (W' := W a b c) (Algebra.ofId ℚ K)).comp
      (ptEquiv (baseChange_Q a b c).symm).toAddMonoidHom)

lemma toK_injective : Function.Injective (toK a b c K) := by
  intro P Q h
  simp only [toK, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply] at h
  exact (ptEquiv _).injective (Point.map_injective _ ((ptEquiv _).injective h))

lemma toK_some {x y : ℚ} (h : (W a b c).toAffine.Nonsingular x y)
    (h' : (EllAbel.W (a : K) (b : K) (c : K)).toAffine.Nonsingular (x : K) (y : K)) :
    toK a b c K (Point.some x y h) = Point.some (x : K) (y : K) h' := by
  simp only [toK, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply]
  have h1 : ((W a b c).baseChange ℚ).toAffine.Nonsingular x y := by rw [baseChange_Q]; exact h
  rw [ptEquiv_some _ h h1, Point.map_some]
  exact ptEquiv_some _ _ _

/-- Finite order in the extension gives finite order over `ℚ`. -/
lemma isOfFinAddOrder_of_toK {P : (W a b c).toAffine.Point} (h : IsOfFinAddOrder (toK a b c K P)) :
    IsOfFinAddOrder P := by
  obtain ⟨n, hn, hP⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp h
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, toK_injective a b c K ?_⟩
  rw [map_nsmul, hP, map_zero]

end EllNL
