import RischTragerBronstein.Mixed.EllIsoClassify
import RischTragerBronstein.Mixed.EllConstK

/-!
# Descent of the Mordell–Weil question for curves constant up to scaling

For `y² = x³ + A x + B` over `K(X)` with `A = u⁴ a`, `B = u⁶ b` (`a, b ∈ K`):
`ΦCS : E_{a,b}(K) →+ E_{A,B}(K(X))` (constant embedding, then scaling by `u`) is injective and
**surjective** (`mem_range_ΦCS`: every point is constant after scaling, `const_scale_descent`).
Hence `indep_iff_ΦCS`: independence of two points over `K(X)` is independence of their preimages
in `E_{a,b}(K)` — the Mordell–Weil question descends one level.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)
local notation "κ" => algebraMap K (RatFunc K)

lemma shortF_baseChangeK (a b : K) :
    ((shortF a b).toAffine⁄(RatFunc K)) = (shortF (κ a) (κ b)).toAffine := by
  simp [shortF, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- **The constant embedding** `E_{a,b}(K) → E_{a,b}(K(X))`. -/
noncomputable def ιK (a b : K) : (shortF a b).toAffine.Point →+ (shortF (κ a) (κ b)).toAffine.Point :=
  have hself : (shortF a b).toAffine = ((shortF a b).toAffine⁄K) := by
    simp [shortF, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  (castHom (shortF_baseChangeK a b)).comp
    ((Point.map (W' := (shortF a b).toAffine) (Algebra.ofId K (RatFunc K))).comp (castHom hself))

lemma ιK_injective (a b : K) : Function.Injective (ιK a b) :=
  (castHom_injective _).comp ((Point.map_injective _).comp (castHom_injective _))

lemma ιK_some (a b : K) (x y : K) (h : (shortF a b).toAffine.Nonsingular x y) :
    ∃ h', ιK a b (Point.some x y h) = Point.some (κ x) (κ y) h' := by
  unfold ιK
  simp only [AddMonoidHom.comp_apply]
  erw [castHom_some]
  refine ⟨?w, ?e⟩
  case e => rfl
  case w =>
    rw [← shortF_baseChangeK]
    exact (Affine.map_nonsingular (W := (shortF a b).toAffine) (algebraMap K (RatFunc K)).injective
      x y).mpr h

lemma shortW_eq_shortF (A B : K[X]) : (shortW A B).toAffine = (shortF (ι A) (ι B)).toAffine := rfl

variable {A B : K[X]} {u : RatFunc K} {a b : K}

/-- **The descent hom** `E_{a,b}(K) → E_{A,B}(K(X))`. -/
noncomputable def ΦCS (hu : u ≠ 0) (hA : ι A = u ^ 4 * κ a) (hB : ι B = u ^ 6 * κ b) :
    (shortF a b).toAffine.Point →+ (shortW A B).toAffine.Point :=
  (castHom (shortW_eq_shortF A B).symm).comp
    ((scaleHomEq (κ a) (κ b) (ι A) (ι B) u hu hA hB).comp (ιK a b))

lemma ΦCS_injective (hu : u ≠ 0) (hA : ι A = u ^ 4 * κ a) (hB : ι B = u ^ 6 * κ b) :
    Function.Injective (ΦCS hu hA hB) := by
  intro P Q h
  unfold ΦCS at h
  simp only [AddMonoidHom.comp_apply] at h
  exact ιK_injective a b (scaleHomEq_injective _ _ _ _ u hu hA hB
    (castHom_injective (shortW_eq_shortF A B).symm h))

/-- A rational function with constant square is constant. -/
theorem const_of_sq (w : RatFunc K) (d : K) (h : w ^ 2 = κ d) : ∃ e : K, w = κ e := by
  obtain ⟨q, hq⟩ := poly_of_pow 2 (by norm_num) w (C d) (by rw [h, RatFunc.algebraMap_C,
    RatFunc.algebraMap_eq_C])
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hq2 : q ^ 2 = C d := hinj (by rw [map_pow, ← hq, h, RatFunc.algebraMap_C,
    RatFunc.algebraMap_eq_C])
  have hdeg : q.natDegree = 0 := by
    have := congrArg natDegree hq2
    rw [natDegree_pow, natDegree_C] at this
    omega
  refine ⟨q.coeff 0, ?_⟩
  rw [hq, eq_C_of_natDegree_eq_zero hdeg, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C,
    coeff_C_zero]

/-- **Every point comes from the constant curve.** -/
theorem mem_range_ΦCS (hu : u ≠ 0) (hA : ι A = u ^ 4 * κ a) (hB : ι B = u ^ 6 * κ b)
    (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (P : (shortW A B).toAffine.Point) :
    ∃ P' : (shortF a b).toAffine.Point, ΦCS hu hA hB P' = P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨0, map_zero _⟩
  have heq := h.1
  rw [equation_iff] at heq
  simp only [shortW, zero_mul, add_zero] at heq
  obtain ⟨c, hc⟩ := const_scale_descent hu hA hB hΔ x y (by linear_combination heq)
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have hu3 : u ^ 3 ≠ 0 := pow_ne_zero 3 hu
  have hx : x = u ^ 2 * κ c := by rw [RatFunc.algebraMap_eq_C, ← hc]; field_simp
  have hy2 : (y / u ^ 3) ^ 2 = κ (c ^ 3 + a * c + b) := by
    rw [div_pow, ← pow_mul, heq, hx, hA, hB]
    simp only [map_add, map_mul, map_pow]; field_simp; ring
  obtain ⟨e, he⟩ := const_of_sq (y / u ^ 3) _ hy2
  have hy : y = u ^ 3 * κ e := by rw [← he]; field_simp
  have heqn : e ^ 2 = c ^ 3 + a * c + b := by
    apply (algebraMap K (RatFunc K)).injective
    rw [map_pow, ← he, hy2]
  have hΔW : (shortF a b).Δ ≠ 0 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, shortF]
    intro h0; apply hΔ; linear_combination (-1 / 16 : K) * h0
  have hns : (shortF a b).toAffine.Nonsingular c e := by
    refine (equation_iff_nonsingular_of_Δ_ne_zero hΔW).mp ?_
    rw [equation_iff]
    simp only [shortF]
    linear_combination heqn
  refine ⟨Point.some c e hns, ?_⟩
  obtain ⟨h1, e1⟩ := ιK_some a b c e hns
  unfold ΦCS
  simp only [AddMonoidHom.comp_apply]
  rw [e1]
  obtain ⟨h2, e2⟩ := scaleHomEq_some (κ a) (κ b) (ι A) (ι B) u hu hA hB h1
  rw [e2, castHom_some]
  simp only [Point.some.injEq]
  exact ⟨hx.symm, hy.symm⟩

/-- **The Mordell–Weil question descends.** -/
theorem indep_iff_ΦCS (hu : u ≠ 0) (hA : ι A = u ^ 4 * κ a) (hB : ι B = u ^ 6 * κ b)
    (P' Q' : (shortF a b).toAffine.Point) :
    (∀ m n : ℤ, m • ΦCS hu hA hB P' = n • ΦCS hu hA hB Q' → m = 0 ∧ n = 0) ↔
      (∀ m n : ℤ, m • P' = n • Q' → m = 0 ∧ n = 0) := by
  constructor
  · intro h m n hr; exact h m n (by rw [← map_zsmul, ← map_zsmul, hr])
  · intro h m n hr
    exact h m n (ΦCS_injective hu hA hB (by rw [map_zsmul, map_zsmul]; exact hr))

end FFHeight

