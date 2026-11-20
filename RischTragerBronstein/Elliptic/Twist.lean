import RischTragerBronstein.Elliptic.Scale
import RischTragerBronstein.Elliptic.Transport

/-!
# Quadratic twists

For `s² = d` (`d ∈ ℤ \ {0}`) in a field `K` of characteristic zero, the points of the twist
`E^d : Y² = X³ + adX² + bd²X + cd³` over `ℚ` embed into `E(K)`, `E : y² = x³ + ax² + bx + c`, by
`(dx, d²y) ↦ (x, y s)` (`twist_transport`: base change, then scaling by `u = 1/s`).
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace EllNL

variable (a b c : ℤ) {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- Rational nonsingular points stay nonsingular in `K`. -/
lemma nonsingular_cast {x y : ℚ} (h : (W a b c).toAffine.Nonsingular x y) :
    (EllAbel.W (a : K) (b : K) (c : K)).toAffine.Nonsingular (x : K) (y : K) := by
  have h' : (EllAbel.W (a : ℚ) (b : ℚ) (c : ℚ)).toAffine.Nonsingular x y := h
  rw [EllAbel.nonsingular_W'] at h' ⊢
  obtain ⟨he, hn⟩ := h'
  refine ⟨by exact_mod_cast he, ?_⟩
  rcases hn with hn | hn
  · left; exact_mod_cast hn
  · right; exact_mod_cast hn

/-- **The twist embedding.** -/
theorem twist_transport (d : ℤ) (hd : d ≠ 0) (s : K) (hs : s ^ 2 = d) :
    ∃ T : (W (a * d) (b * d ^ 2) (c * d ^ 3)).toAffine.Point →+
        (EllAbel.W (a : K) (b : K) (c : K)).toAffine.Point,
      Function.Injective T ∧ ∀ (x y : ℚ)
        (h : (W (a * d) (b * d ^ 2) (c * d ^ 3)).toAffine.Nonsingular (d * x) (d ^ 2 * y))
        (h' : (EllAbel.W (a : K) (b : K) (c : K)).toAffine.Nonsingular (x : K) ((y : K) * s)),
        T (Point.some _ _ h) = Point.some _ _ h' := by
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
  have hs0 : s ≠ 0 := by rintro rfl; apply hdK; rw [← hs]; ring
  have hu : s⁻¹ ≠ 0 := inv_ne_zero hs0
  have hu2 : s⁻¹ ^ 2 * (d : K) = 1 := by rw [inv_pow, hs, inv_mul_cancel₀ hdK]
  have h₂ : ((a : ℤ) : K) = s⁻¹ ^ 2 * (((a * d : ℤ)) : K) := by
    push_cast; linear_combination (-(a : K)) * hu2
  have h₄ : ((b : ℤ) : K) = s⁻¹ ^ 4 * (((b * d ^ 2 : ℤ)) : K) := by
    push_cast; linear_combination (-(b : K)) * (s⁻¹ ^ 2 * (d : K) + 1) * hu2
  have h₆ : ((c : ℤ) : K) = s⁻¹ ^ 6 * (((c * d ^ 3 : ℤ)) : K) := by
    push_cast
    linear_combination (-(c : K)) * ((s⁻¹ ^ 2 * (d : K)) ^ 2 + s⁻¹ ^ 2 * (d : K) + 1) * hu2
  refine ⟨(EllAbel.scaleHom h₂ h₄ h₆ hu).comp (toK (a * d) (b * d ^ 2) (c * d ^ 3) K),
    (EllAbel.scale_injective h₂ h₄ h₆ hu).comp (toK_injective _ _ _ K), ?_⟩
  intro x y h h'
  have hK := nonsingular_cast (K := K) _ _ _ h
  simp only [AddMonoidHom.coe_comp, Function.comp_apply]
  rw [toK_some _ _ _ K h hK]
  show EllAbel.scale h₂ h₄ h₆ hu (Point.some _ _ hK) = _
  rw [EllAbel.scale_some]
  simp only [Point.some.injEq]
  constructor
  · push_cast; linear_combination (x : K) * hu2
  · have hs3 : s⁻¹ ^ 3 * (d : K) ^ 2 = s := by rw [← hs]; field_simp
    push_cast
    linear_combination (y : K) * hs3

end EllNL
