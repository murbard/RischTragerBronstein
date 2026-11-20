import RischTragerBronstein.Jacobian.PrincipalMul

/-!
# Rescaling the curve

For `t, e ≠ 0`, the map `(x, y) ↦ (t x, e y)` sends `y² = f(x)` to `Y² = F(X)` with
`F = e² f(X/t)` (`scaleF`), and a function `a(x) + b(x) y` to `a(X/t) + e⁻¹ b(X/t) Y`
(`scaleψ`). Vanishing orders and pole orders are preserved (`VanishAt.scale`, `PoleLE.scale`), so
`principalMul_scale`: `n Γ` is principal on the first curve iff `n Γ'` is on the second.
-/

open Polynomial

namespace Jac

variable {K : Type*} [Field K]

/-- `e² f(X/t)`. -/
noncomputable def scaleF (t e : K) (f : K[X]) : K[X] := C (e ^ 2) * f.comp (C t⁻¹ * X)

/-- `a(X/t) + e⁻¹ b(X/t) Y`. -/
noncomputable def scaleψ (t e : K) (ψ : K[X] × K[X]) : K[X] × K[X] :=
  (ψ.1.comp (C t⁻¹ * X), C e⁻¹ * ψ.2.comp (C t⁻¹ * X))

/-- The rescaled divisor. -/
def scaleΓ (t e : K) (Γ : EDiv K) : EDiv K := Γ.map fun q ↦ (t * q.1, e * q.2.1, q.2.2)

lemma X_pow_dvd_comp_smul {P : K[X]} {k : ℕ} (c : K) (h : X ^ k ∣ P) :
    X ^ k ∣ P.comp (C c * X) := by
  obtain ⟨Q, rfl⟩ := h
  rw [mul_comp, X_pow_comp, mul_pow, ← C_pow, mul_assoc, mul_left_comm]
  exact dvd_mul_right _ _

lemma comp_shift_scale (P : K[X]) {t : K} (ht : t ≠ 0) (α : K) :
    (P.comp (C t⁻¹ * X)).comp (X + C (t * α)) = (P.comp (X + C α)).comp (C t⁻¹ * X) := by
  rw [comp_assoc, comp_assoc]
  congr 1
  simp only [mul_comp, C_comp, X_comp, add_comp]
  rw [mul_add, ← Polynomial.C_mul, inv_mul_cancel_left₀ ht]

lemma VanishAt.scale {f a b : K[X]} {α β : K} {k : ℕ} {t e : K} (ht : t ≠ 0) (he : e ≠ 0)
    (h : VanishAt f a b α β k) :
    VanishAt (scaleF t e f) (scaleψ t e (a, b)).1 (scaleψ t e (a, b)).2 (t * α) (e * β) k := by
  obtain ⟨V, ⟨hV0, hV⟩, hj⟩ := h
  refine ⟨C e * V.comp (C t⁻¹ * X), ⟨?_, ?_⟩, ?_⟩
  · rw [coeff_C_mul, coeff_zero_eq_eval_zero, eval_comp]; simp [← coeff_zero_eq_eval_zero, hV0]
  · have := X_pow_dvd_comp_smul t⁻¹ hV
    have e1 : (C e * V.comp (C t⁻¹ * X)) ^ 2 - (scaleF t e f).comp (X + C (t * α)) =
        C (e ^ 2) * (V ^ 2 - f.comp (X + C α)).comp (C t⁻¹ * X) := by
      rw [scaleF, mul_comp, C_comp, comp_shift_scale f ht, sub_comp, pow_comp, C_pow]; ring
    rw [e1]; exact dvd_mul_of_dvd_right this _
  · have := X_pow_dvd_comp_smul t⁻¹ hj
    have e1 : jet (scaleψ t e (a, b)).1 (scaleψ t e (a, b)).2 (t * α)
        (C e * V.comp (C t⁻¹ * X)) = (jet a b α V).comp (C t⁻¹ * X) := by
      simp only [jet, scaleψ, mul_comp, C_comp, comp_shift_scale _ ht, add_comp]
      have : C e⁻¹ * C e = (1 : K[X]) := by rw [← Polynomial.C_mul, inv_mul_cancel₀ he, C_1]
      linear_combination ((b.comp (X + C α)).comp (C t⁻¹ * X) * V.comp (C t⁻¹ * X)) * this
    rw [e1]; exact this

lemma PoleLE.scale {g : ℕ} {ψ : K[X] × K[X]} {N : ℕ} {t e : K} (ht : t ≠ 0) (he : e ≠ 0)
    (h : PoleLE g ψ N) : PoleLE g (scaleψ t e ψ) N := by
  have hd : ∀ P : K[X], (P.comp (C t⁻¹ * X)).natDegree = P.natDegree := fun P ↦ by
    rw [natDegree_comp, natDegree_C_mul_X _ (inv_ne_zero ht), mul_one]
  refine ⟨by simp only [scaleψ]; rw [hd]; exact h.1, ?_⟩
  rcases h.2 with h0 | h1
  · left; simp [scaleψ, h0]
  · right
    simp only [scaleψ]
    rw [natDegree_C_mul (inv_ne_zero he), hd]; exact h1

lemma scaleψ_ne_zero {ψ : K[X] × K[X]} {t e : K} (ht : t ≠ 0) (he : e ≠ 0) (h : ψ ≠ (0, 0)) :
    scaleψ t e ψ ≠ (0, 0) := by
  intro h0
  apply h
  simp only [scaleψ, Prod.mk.injEq] at h0
  have hc : ∀ P : K[X], P.comp (C t⁻¹ * X) = 0 → P = 0 := fun P hP ↦ by
    have := congrArg natDegree hP
    by_contra hne
    have hl := congrArg leadingCoeff hP
    rw [leadingCoeff_comp (by rw [natDegree_C_mul_X _ (inv_ne_zero ht)]; exact one_ne_zero),
      leadingCoeff_zero] at hl
    simp [hne, ht] at hl
  refine Prod.ext (hc _ h0.1) (hc _ ?_)
  rcases mul_eq_zero.mp h0.2 with h | h
  · exact absurd (C_eq_zero.mp h) (inv_ne_zero he)
  · exact h

lemma edeg_scaleΓ (t e : K) (Γ : EDiv K) : edeg (scaleΓ t e Γ) = edeg Γ := by
  simp [edeg, scaleΓ, Function.comp_def]

lemma escale_scaleΓ (t e : K) (n : ℕ) (Γ : EDiv K) :
    escale n (scaleΓ t e Γ) = scaleΓ t e (escale n Γ) := by
  simp [escale, scaleΓ, Function.comp_def]

/-- **Principality is invariant under rescaling.** -/
theorem PrincipalMul.scale {f : K[X]} {g : ℕ} {Γ : EDiv K} {n : ℕ} {t e : K} (ht : t ≠ 0)
    (he : e ≠ 0) (h : PrincipalMul f g Γ n) : PrincipalMul (scaleF t e f) g (scaleΓ t e Γ) n := by
  obtain ⟨ψ, h0, hp, hv⟩ := h
  refine ⟨scaleψ t e ψ, scaleψ_ne_zero ht he h0, ?_, ?_⟩
  · rw [edeg_scaleΓ]; exact hp.scale ht he
  · intro q hq
    rw [escale_scaleΓ] at hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact (hv q' hq').scale ht he

lemma scaleF_scaleF (f : K[X]) {t e : K} (ht : t ≠ 0) (he : e ≠ 0) :
    scaleF t⁻¹ e⁻¹ (scaleF t e f) = f := by
  simp only [scaleF, mul_comp, C_comp, comp_assoc]
  rw [inv_inv, show C t⁻¹ * X.comp (C t * X) = X by
    rw [X_comp, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ ht, C_1, one_mul], comp_X,
    ← mul_assoc, ← Polynomial.C_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 he), C_1, one_mul]

lemma scaleΓ_scaleΓ (Γ : EDiv K) {t e : K} (ht : t ≠ 0) (he : e ≠ 0) :
    scaleΓ t⁻¹ e⁻¹ (scaleΓ t e Γ) = Γ := by
  simp [scaleΓ, Function.comp_def, ← mul_assoc, inv_mul_cancel₀ ht, inv_mul_cancel₀ he]

theorem principalMul_scale_iff {f : K[X]} {g : ℕ} {Γ : EDiv K} {n : ℕ} {t e : K} (ht : t ≠ 0)
    (he : e ≠ 0) : PrincipalMul (scaleF t e f) g (scaleΓ t e Γ) n ↔ PrincipalMul f g Γ n := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.scale ht he⟩
  have := h.scale (inv_ne_zero ht) (inv_ne_zero he)
  rwa [scaleF_scaleF f ht he, scaleΓ_scaleΓ Γ ht he] at this

end Jac
