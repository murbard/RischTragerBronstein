import RischTragerBronstein.Mixed.KXHeight
import RischTragerBronstein.Mixed.KXConj
import RischTragerBronstein.Mixed.ManinCompute

/-!
# The `kx` group condition from a Manin-map certificate

`hgrp_of_manCert` is `hgrp_of_cert` with the executable **Manin-map certificate**
(`Manin.manCert`, a non-zero Wronskian of the Manin images) in place of the height certificate:
certificate points over `k₀(X)` whose images under `mapE` (along `j : k₀ → k`) are the
`toShort`-images of the exception points `D, Z` give `2N D + 2μ Z ≠ 0` for all `N > 0`, `μ`.
This is the hypothesis of `kxe_norel_group` (no Liouville form), for non-constant curves.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Differential

namespace SuperData

open scoped Classical

variable {C : Type*} [Field C] [CharZero C]
variable {k : Type*} [Field k] [CharZero k] (φ : C ≃+* RatFunc k)

/-- **The group condition from a Manin certificate.** -/
theorem hgrp_of_manCert {k₀ : Type*} [Field k₀] [CharZero k₀] [DecidableEq k₀] (j : k₀ →+* k)
    (c3 c2 c1 c0 : C) (u : RatFunc k) (hu : u ≠ 0) (A₀ B₀ : k₀[X])
    (hA : algebraMap k[X] (RatFunc k) (A₀.map j) = u ^ 4 * (φ (c1 * c3) - φ c2 ^ 2 / 3))
    (hB : algebraMap k[X] (RatFunc k) (B₀.map j) =
      u ^ 6 * (φ (c0 * c3 ^ 2) - φ c2 * φ (c1 * c3) / 3 + 2 * φ c2 ^ 3 / 27))
    (D Z : (WG c3 c2 c1 c0).Point) (Ac Bc : CPoly k₀) (hAc : CPoly.toPoly Ac = A₀)
    (hBc : CPoly.toPoly Bc = B₀) (uD vD uZ vZ : FFHeight.Fr k₀)
    (hPD : (FFHeight.shortW A₀ B₀).toAffine.Nonsingular (FFHeight.Fr.val uD) (FFHeight.Fr.val vD))
    (hPZ : (FFHeight.shortW A₀ B₀).toAffine.Nonsingular (FFHeight.Fr.val uZ) (FFHeight.Fr.val vZ))
    (hmD : FFHeight.mapE j A₀ B₀ (Point.some _ _ hPD) =
      toShort φ c3 c2 c1 c0 u hu (A₀.map j) (B₀.map j) hA hB D)
    (hmZ : FFHeight.mapE j A₀ B₀ (Point.some _ _ hPZ) =
      toShort φ c3 c2 c1 c0 u hu (A₀.map j) (B₀.map j) hA hB Z)
    (hc : Manin.manCert Ac Bc uD vD uZ vZ = true) :
    ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • D + (2 * μ) • Z ≠ 0 :=
  hgrp_of_indep (toShort φ c3 c2 c1 c0 u hu (A₀.map j) (B₀.map j) hA hB)
    (toShort_injective φ c3 c2 c1 c0 u hu _ _ hA hB) D Z (fun m n h ↦ by
      rw [← hmD, ← hmZ, ← map_zsmul, ← map_zsmul] at h
      have h' := FFHeight.mapE_injective j A₀ B₀ h
      subst hAc hBc
      exact Manin.indep_of_manCert hc hPD hPZ m n 0 1 one_ne_zero (by simp)
        (by rw [add_zero]; exact h'))

/-- The Manin certificate on optional code points (fails on the origin). -/
def manCertP {k₀ : Type*} [Field k₀] [DecidableEq k₀] (Ac Bc : CPoly k₀) :
    FFHeight.PtC k₀ → FFHeight.PtC k₀ → Bool
  | some (uD, vD), some (uZ, vZ) => Manin.manCert Ac Bc uD vD uZ vZ
  | _, _ => false

/-- **Independence of represented points from a Manin certificate** (over `k₀(X)`). -/
theorem indep_of_manCertP {k₀ : Type*} [Field k₀] [CharZero k₀] [DecidableEq k₀]
    (Ac Bc : CPoly k₀) (oD oZ : FFHeight.PtC k₀)
    (PD PZ : (FFHeight.shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point)
    (hD : FFHeight.Rel _ _ oD PD) (hZ : FFHeight.Rel _ _ oZ PZ)
    (hc : manCertP Ac Bc oD oZ = true) : ∀ m n : ℤ, m • PD = n • PZ → m = 0 ∧ n = 0 := by
  intro m n h
  rcases oD with _ | ⟨uD, vD⟩ <;> rcases oZ with _ | ⟨uZ, vZ⟩ <;> simp only [manCertP] at hc <;>
    try exact absurd hc (by decide)
  rcases PD with _ | ⟨xD, yD, hPD⟩
  · exact absurd hD (by simp [FFHeight.Rel])
  rcases PZ with _ | ⟨xZ, yZ, hPZ⟩
  · exact absurd hZ (by simp [FFHeight.Rel])
  obtain ⟨-, -, rfl, rfl⟩ := hD
  obtain ⟨-, -, rfl, rfl⟩ := hZ
  exact Manin.indep_of_manCert hc hPD hPZ m n 0 1 one_ne_zero (by simp) (by rw [add_zero]; exact h)

/-- The constant-ratio Manin certificate on optional code points. -/
def manCertRP {k₀ : Type*} [Field k₀] [DecidableEq k₀] (Ac Bc : CPoly k₀) (isRat : k₀ → Bool) :
    FFHeight.PtC k₀ → FFHeight.PtC k₀ → Bool
  | some (uD, vD), some (uZ, vZ) => Manin.manCertR Ac Bc isRat uD vD uZ vZ
  | _, _ => false

/-- **Independence of represented points from the constant-ratio certificate.** -/
theorem indep_of_manCertRP {k₀ : Type*} [Field k₀] [CharZero k₀] [DecidableEq k₀]
    (Ac Bc : CPoly k₀) {isRat : k₀ → Bool} (hRat : ∀ q : ℚ, isRat (q : k₀) = true)
    (oD oZ : FFHeight.PtC k₀)
    (PD PZ : (FFHeight.shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point)
    (hD : FFHeight.Rel _ _ oD PD) (hZ : FFHeight.Rel _ _ oZ PZ)
    (hc : manCertRP Ac Bc isRat oD oZ = true) : ∀ m n : ℤ, m • PD = n • PZ → m = 0 ∧ n = 0 := by
  intro m n h
  rcases oD with _ | ⟨uD, vD⟩ <;> rcases oZ with _ | ⟨uZ, vZ⟩ <;> simp only [manCertRP] at hc <;>
    try exact absurd hc (by decide)
  rcases PD with _ | ⟨xD, yD, hPD⟩
  · exact absurd hD (by simp [FFHeight.Rel])
  rcases PZ with _ | ⟨xZ, yZ, hPZ⟩
  · exact absurd hZ (by simp [FFHeight.Rel])
  obtain ⟨-, -, rfl, rfl⟩ := hD
  obtain ⟨-, -, rfl, rfl⟩ := hZ
  exact Manin.indep_of_manCertR hRat hc hPD hPZ m n 0 1 one_ne_zero (by simp)
    (by rw [add_zero]; exact h)

/-- **The group condition from a Manin certificate on represented points.** -/
theorem hgrp_of_manCertP {k₀ : Type*} [Field k₀] [CharZero k₀] [DecidableEq k₀] (j : k₀ →+* k)
    (c3 c2 c1 c0 : C) (u : RatFunc k) (hu : u ≠ 0) (A₀ B₀ : k₀[X])
    (hA : algebraMap k[X] (RatFunc k) (A₀.map j) = u ^ 4 * (φ (c1 * c3) - φ c2 ^ 2 / 3))
    (hB : algebraMap k[X] (RatFunc k) (B₀.map j) =
      u ^ 6 * (φ (c0 * c3 ^ 2) - φ c2 * φ (c1 * c3) / 3 + 2 * φ c2 ^ 3 / 27))
    (D Z : (WG c3 c2 c1 c0).Point) (Ac Bc : CPoly k₀) (hAc : CPoly.toPoly Ac = A₀)
    (hBc : CPoly.toPoly Bc = B₀) (oD oZ : FFHeight.PtC k₀)
    (PD PZ : (FFHeight.shortW A₀ B₀).toAffine.Point)
    (hD : FFHeight.Rel A₀ B₀ oD PD) (hZ : FFHeight.Rel A₀ B₀ oZ PZ)
    (hmD : FFHeight.mapE j A₀ B₀ PD = toShort φ c3 c2 c1 c0 u hu (A₀.map j) (B₀.map j) hA hB D)
    (hmZ : FFHeight.mapE j A₀ B₀ PZ = toShort φ c3 c2 c1 c0 u hu (A₀.map j) (B₀.map j) hA hB Z)
    (hc : manCertP Ac Bc oD oZ = true) :
    ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • D + (2 * μ) • Z ≠ 0 := by
  rcases oD with _ | ⟨uD, vD⟩ <;> rcases oZ with _ | ⟨uZ, vZ⟩ <;> simp only [manCertP] at hc <;>
    try exact absurd hc (by decide)
  rcases PD with _ | ⟨xD, yD, hPD⟩
  · exact absurd hD (by simp [FFHeight.Rel])
  rcases PZ with _ | ⟨xZ, yZ, hPZ⟩
  · exact absurd hZ (by simp [FFHeight.Rel])
  obtain ⟨-, -, rfl, rfl⟩ := hD
  obtain ⟨-, -, rfl, rfl⟩ := hZ
  exact hgrp_of_manCert φ j c3 c2 c1 c0 u hu A₀ B₀ hA hB D Z Ac Bc hAc hBc uD vD uZ vZ hPD hPZ
    hmD hmZ hc

end SuperData

end Differential

