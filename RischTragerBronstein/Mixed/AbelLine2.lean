import RischTragerBronstein.Algebraic.AbelLine
import RischTragerBronstein.Mixed.EllScale

/-!
# The divisor of a line through two points (Abel bridge, step B2)

On `y² = x³ + a x + b` (a superelliptic `S` with `n = 2`, `p = X³ + aX + b`), for points
`P₁ = (x₁, y₁)`, `P₂ = (x₂, y₂)` with `P₁ ≠ −P₂` and `ℓ` the slope of Mathlib's group law,
the line `y − (ℓx + ν)`, `ν = y₁ − ℓx₁`, satisfies
`(ℓX + ν)² − p = −(X − x₁)(X − x₂)(X − x₃)` (`line_poly`, from Mathlib's `addPolynomial_slope`),
`x₃ = addX`, so its order at a point `(α, β)` is the number of `i ∈ {1, 2, 3}` with
`(α, β) = (xᵢ, yᵢ)`, `y₃ = ℓx₃ + ν` (`ordAt_line_three`): its affine divisor is
`(P₁) + (P₂) + (−(P₁ + P₂))`.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Differential

namespace SuperData

open scoped Classical

variable {C L K : Type*} [Field C] [PerfectField C] [Field L] [Algebra C L] [Field K] [Algebra C K]
  [IsAlgClosed K]
variable (S : SuperData C L)

omit [PerfectField C] in
/-- The cubic of the line through two points of a short curve. -/
theorem line_poly (a b x1 y1 x2 y2 : C) (h1 : (FFHeight.shortF a b).toAffine.Equation x1 y1)
    (h2 : (FFHeight.shortF a b).toAffine.Equation x2 y2)
    (hxy : ¬(x1 = x2 ∧ y1 = (FFHeight.shortF a b).toAffine.negY x2 y2)) :
    (Polynomial.C ((FFHeight.shortF a b).toAffine.slope x1 x2 y1 y2) * X +
        Polynomial.C (y1 - (FFHeight.shortF a b).toAffine.slope x1 x2 y1 y2 * x1)) ^ 2 -
        (X ^ 3 + Polynomial.C a * X + Polynomial.C b) =
      -((X - Polynomial.C x1) * (X - Polynomial.C x2) *
        (X - Polynomial.C ((FFHeight.shortF a b).toAffine.addX x1 x2
          ((FFHeight.shortF a b).toAffine.slope x1 x2 y1 y2)))) := by
  rw [← addPolynomial_slope h1 h2 hxy]
  generalize (FFHeight.shortF a b).toAffine.slope x1 x2 y1 y2 = ℓ
  simp only [addPolynomial, linePolynomial, Affine.polynomial, FFHeight.shortF]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, map_zero, zero_mul, add_zero,
    sub_zero, map_sub, map_mul]
  ring

open Classical in
/-- B1 at every point: `ord_{(α,β)} ℓ = mult_α q` if `β = λα + ν`, else `0`. -/
theorem ordAt_line_all [CharZero K] (hn2 : S.n = 2) (lam nu : C)
    (hq : (Polynomial.C lam * X + Polynomial.C nu) ^ 2 - S.p ≠ 0) (α β : K)
    (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    S.ordAt K (S.lineF lam nu) α β =
      if β = algebraMap C K lam * α + algebraMap C K nu then
        ((((Polynomial.C lam * X + Polynomial.C nu) ^ 2 - S.p).map (algebraMap C K)).rootMultiplicity α : ℤ)
      else 0 := by
  by_cases hβ : β = 0
  · subst hβ
    have he : (S.p.map (algebraMap C K)).eval α = 0 := by rw [← hv, zero_pow S.hn.ne']
    exact S.ordAt_line_br hn2 lam nu α he
  · exact S.ordAt_line hn2 lam nu hq α β hβ hv

/-- **B2: the divisor of the line through `P₁, P₂`** is `(P₁) + (P₂) + (−(P₁ + P₂))`. -/
theorem ordAt_line_three [CharZero K] (hn2 : S.n = 2) (a b : C)
    (hpE : S.p = X ^ 3 + Polynomial.C a * X + Polynomial.C b) (x1 y1 x2 y2 : C)
    (h1 : (FFHeight.shortF a b).toAffine.Equation x1 y1)
    (h2 : (FFHeight.shortF a b).toAffine.Equation x2 y2)
    (hxy : ¬(x1 = x2 ∧ y1 = (FFHeight.shortF a b).toAffine.negY x2 y2)) (α β : K)
    (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    let ℓ := (FFHeight.shortF a b).toAffine.slope x1 x2 y1 y2
    let ν := y1 - ℓ * x1
    let x3 := (FFHeight.shortF a b).toAffine.addX x1 x2 ℓ
    S.ordAt K (S.lineF ℓ ν) α β =
      (if α = algebraMap C K x1 ∧ β = algebraMap C K y1 then 1 else 0) +
      (if α = algebraMap C K x2 ∧ β = algebraMap C K y2 then 1 else 0) +
      (if α = algebraMap C K x3 ∧ β = algebraMap C K (ℓ * x3 + ν) then 1 else 0) := by
  intro ℓ ν x3
  have hpoly := line_poly a b x1 y1 x2 y2 h1 h2 hxy
  have hqe : (Polynomial.C ℓ * X + Polynomial.C ν) ^ 2 - S.p =
      -((X - Polynomial.C x1) * (X - Polynomial.C x2) * (X - Polynomial.C x3)) := by
    rw [hpE]; exact hpoly
  have hq : (Polynomial.C ℓ * X + Polynomial.C ν) ^ 2 - S.p ≠ 0 := by
    rw [hqe, neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)
  rw [S.ordAt_line_all hn2 ℓ ν hq α β hv, hqe]
  -- `y₂ = ℓ x₂ + ν`
  have hy2 : y2 = ℓ * x2 + ν := by
    by_cases hx : x1 = x2
    · have hy : y1 ≠ (FFHeight.shortF a b).toAffine.negY x2 y2 := fun h ↦ hxy ⟨hx, h⟩
      have := Y_eq_of_Y_ne h1 h2 hx hy
      simp only [ν]; rw [← hx, ← this]; ring
    · have hd : x1 - x2 ≠ 0 := sub_ne_zero.mpr hx
      have hl : ℓ = (y1 - y2) / (x1 - x2) := slope_of_X_ne hx
      simp only [ν]; rw [hl]; field_simp; ring
  have hmul : ((-((X - Polynomial.C x1) * (X - Polynomial.C x2) * (X - Polynomial.C x3))).map
      (algebraMap C K)).rootMultiplicity α =
      (if α = algebraMap C K x1 then 1 else 0) + (if α = algebraMap C K x2 then 1 else 0) +
        (if α = algebraMap C K x3 then 1 else 0) := by
    simp only [Polynomial.map_neg, Polynomial.map_mul, Polynomial.map_sub, map_X, map_C]
    rw [show ∀ g : K[X], -g = Polynomial.C (-1) * g from fun g ↦ by simp,
      rootMultiplicity_mul (by
        exact mul_ne_zero (by simp) (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _)
          (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _))), rootMultiplicity_C, zero_add,
      rootMultiplicity_mul (by
        exact mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)),
      rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
      rootMultiplicity_X_sub_C, rootMultiplicity_X_sub_C, rootMultiplicity_X_sub_C]
  by_cases hon : β = algebraMap C K ℓ * α + algebraMap C K ν
  · rw [if_pos hon, hmul]
    have e1 : (α = algebraMap C K x1 ∧ β = algebraMap C K y1) ↔ α = algebraMap C K x1 := by
      constructor
      · exact fun h ↦ h.1
      · intro h; refine ⟨h, ?_⟩; rw [hon, h, ← map_mul, ← map_add]; congr 1; simp only [ν]; ring
    have e2 : (α = algebraMap C K x2 ∧ β = algebraMap C K y2) ↔ α = algebraMap C K x2 := by
      constructor
      · exact fun h ↦ h.1
      · intro h; refine ⟨h, ?_⟩; rw [hon, h, ← map_mul, ← map_add, hy2]
    have e3 : (α = algebraMap C K x3 ∧ β = algebraMap C K (ℓ * x3 + ν)) ↔ α = algebraMap C K x3 := by
      constructor
      · exact fun h ↦ h.1
      · intro h; refine ⟨h, ?_⟩; rw [hon, h, ← map_mul, ← map_add]
    simp only [e1, e2, e3]
    push_cast
    split_ifs <;> simp
  · rw [if_neg hon]
    have n1 : ¬(α = algebraMap C K x1 ∧ β = algebraMap C K y1) := by
      rintro ⟨h, h'⟩; apply hon; rw [h', h, ← map_mul, ← map_add]; congr 1; simp only [ν]; ring
    have n2 : ¬(α = algebraMap C K x2 ∧ β = algebraMap C K y2) := by
      rintro ⟨h, h'⟩; apply hon; rw [h', h, ← map_mul, ← map_add, hy2]
    have n3 : ¬(α = algebraMap C K x3 ∧ β = algebraMap C K (ℓ * x3 + ν)) := by
      rintro ⟨h, h'⟩; apply hon; rw [h', h, ← map_mul, ← map_add]
    have n3' : ¬(α = algebraMap C K x3 ∧
        β = algebraMap C K ℓ * algebraMap C K x3 + algebraMap C K ν) := by
      rintro ⟨h, h'⟩; apply hon; rw [h', h]
    simp only [map_add, map_mul] at n3 ⊢
    simp [n1, n2, n3']

end SuperData

end Differential
