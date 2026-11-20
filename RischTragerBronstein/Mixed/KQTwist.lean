import RischTragerBronstein.Mixed.KQBridge

/-!
# Twisting a superelliptic curve: `y ↦ μ y`

The points `(α, β)` of `yⁿ = f` and `(α, μβ)` of `yⁿ = μⁿ f` correspond, and so do the functions
`W(x, y)` and `W(x, y/μ)`:

* `vanishAtN_scale`: vanishing orders are preserved;
* `principalMulN_scale`: `ψ`-form principality is preserved.
-/

open Polynomial

namespace Sup

variable {R : Type*} [Field R]

lemma compRingHom_C (α a : R) : compRingHom (X + C α) (C a) = C a := by simp

/-- **Vanishing is preserved by the twist.** -/
theorem vanishAtN_scale {f : R[X]} {n : ℕ} {W : R[X][X]} {α β : R} {ℓ : ℕ} (μ : R) (hμ : μ ≠ 0)
    (h : VanishAtN f n W α β ℓ) :
    VanishAtN (C (μ ^ n) * f) n (W.comp (C (C μ⁻¹) * X)) α (μ * β) ℓ := by
  obtain ⟨V, ⟨hV0, hVd⟩, hj⟩ := h
  refine ⟨C μ * V, ⟨by rw [coeff_C_mul, hV0], ?_⟩, ?_⟩
  · rw [mul_comp, C_comp, mul_pow, ← C_pow, ← mul_sub]
    exact dvd_mul_of_dvd_right hVd _
  · have e : jetN (W.comp (C (C μ⁻¹) * X)) α (C μ * V) = jetN W α V := by
      unfold jetN
      rw [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
        compRingHom_C, eval_comp, eval_mul, eval_C, eval_X, ← mul_assoc, ← C_mul,
        inv_mul_cancel₀ hμ, C_1, one_mul]
    rw [e]; exact hj

/-- **`ψ`-form principality is preserved by the twist.** -/
theorem principalMulN_scale {f : R[X]} {n d r : ℕ} {α β : Fin r → R} {mq : Fin r → ℕ} {s : ℕ}
    (μ : R) (hμ : μ ≠ 0) (h : PrincipalMulN f n d α β mq s) :
    PrincipalMulN (C (μ ^ n) * f) n d α (fun q ↦ μ * β q) mq s := by
  obtain ⟨W, hW0, hWs, hWv⟩ := h
  have hC : C μ⁻¹ ∈ nonZeroDivisors R[X] :=
    mem_nonZeroDivisors_of_ne_zero (C_ne_zero.mpr (inv_ne_zero hμ))
  refine ⟨W.comp (C (C μ⁻¹) * X), fun h0 ↦ hW0 ((comp_C_mul_X_eq_zero_iff hC).mp h0),
    fun j a h ↦ hWs j a (fun h0 ↦ h ?_), fun q ↦ vanishAtN_scale μ hμ (hWv q)⟩
  rw [comp_C_mul_X_coeff, ← C_pow, coeff_mul_C, h0, zero_mul]

end Sup
