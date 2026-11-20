import RischTragerBronstein.Algebraic.SupKernel

/-!
# Branch jets over a ring

Over any commutative ring, if `n βⁿ⁻¹` is a unit and `βⁿ = f(α)`, there are branch jets of every
order (`exists_branchN`, Newton's iteration). Vanishing is compatible with injective ring maps
(`vanishAtN_of_map`).
-/

open Polynomial

namespace Sup

variable {R : Type*} [CommRing R]

/-- **Branch jets exist** when `n βⁿ⁻¹` is a unit. -/
theorem exists_branchN (f : R[X]) {n : ℕ} (hn : 0 < n) {α β : R}
    (hu : IsUnit ((n : R) * β ^ (n - 1))) (hf : β ^ n = f.eval α) :
    ∀ ℓ, ∃ V, IsBranchN f n α β (ℓ + 1) V := by
  obtain ⟨u, hu'⟩ := hu
  intro ℓ
  induction ℓ with
  | zero =>
    refine ⟨C β, by simp, ?_⟩
    rw [zero_add, pow_one, X_dvd_iff]
    simp [coeff_zero_eq_eval_zero, eval_comp, hf]
  | succ k ih =>
    obtain ⟨V, hV0, G, hG⟩ := ih
    set c : R := (V ^ n - f.comp (X + C α)).coeff (k + 1) * ↑u⁻¹
    have hcoef : (V ^ n - f.comp (X + C α)).coeff (k + 1) = c * ((n : R) * β ^ (n - 1)) := by
      simp only [c, ← hu', mul_assoc, Units.inv_mul, mul_one]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨E, hE⟩ := add_pow_sq V (-(C c * X ^ (k + 1))) m
    refine ⟨V - C c * X ^ (k + 1), ?_, ?_⟩
    · rw [coeff_sub, coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero, sub_zero, hV0]
    · rw [show V - C c * X ^ (k + 1) = V + -(C c * X ^ (k + 1)) from sub_eq_add_neg _ _, hE]
      have e : V ^ (m + 1) + C ((m + 1 : ℕ) : R) * -(C c * X ^ (k + 1)) * V ^ m +
          (-(C c * X ^ (k + 1))) ^ 2 * E - f.comp (X + C α) =
          X ^ (k + 1) * (G - C ((m + 1 : ℕ) * c) * V ^ m) +
            X ^ (2 * (k + 1)) * (C (c ^ 2) * E) := by
        rw [show V ^ (m + 1) + C ((m + 1 : ℕ) : R) * -(C c * X ^ (k + 1)) * V ^ m +
          (-(C c * X ^ (k + 1))) ^ 2 * E - f.comp (X + C α) =
          (V ^ (m + 1) - f.comp (X + C α)) -
            C ((m + 1 : ℕ) * c) * X ^ (k + 1) * V ^ m + X ^ (2 * (k + 1)) * (C (c ^ 2) * E) by
          simp only [map_mul, map_pow, map_natCast]; ring, hG]
        ring
      rw [e]
      refine dvd_add ?_ ?_
      · rw [pow_succ]
        refine mul_dvd_mul_left _ ?_
        rw [X_dvd_iff, coeff_sub, coeff_C_mul]
        have hG1 : G.coeff 0 = (V ^ (m + 1) - f.comp (X + C α)).coeff (k + 1) := by
          rw [hG, coeff_X_pow_mul', if_pos (by omega), Nat.sub_self]
        have hVm : (V ^ m).coeff 0 = β ^ m := by
          rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, hV0]
        rw [hG1, hcoef, hVm]
        simp only [Nat.add_sub_cancel]
        push_cast; ring
      · exact Dvd.dvd.mul_right (pow_dvd_pow X (by omega)) _

/-- Vanishing descends along an injective ring map, given a branch over the source. -/
theorem vanishAtN_of_map {S : Type*} [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ)
    {f : R[X]} {n : ℕ} (hn : 0 < n) {W : R[X][X]} {α β : R} {ℓ : ℕ} {V : R[X]}
    (hV : IsBranchN f n α β ℓ V) (hu : IsUnit ((n : S) * φ β ^ (n - 1)))
    (h : VanishAtN (f.map φ) n (W.map (mapRingHom φ)) (φ α) (φ β) ℓ) :
    VanishAtN f n W α β ℓ := by
  obtain ⟨V', hV', hd⟩ := h
  refine ⟨V, hV, ?_⟩
  have hVm := IsBranchN.mapR φ hV
  have hcong := branchN_unique hn hu hVm hV'
  have h1 := dvd_add (jetN_congr (W.map (mapRingHom φ)) (φ α) hcong) hd
  rw [sub_add_cancel, ← jetN_map] at h1
  rw [Polynomial.X_pow_dvd_iff] at h1 ⊢
  intro t ht
  have := h1 t ht
  rw [coeff_map] at this
  exact hφ (by rw [this, map_zero])

end Sup
