import RischTragerBronstein.Liouville.PoleOrder
import RischTragerBronstein.RDE.RationalCoeff

/-!
# Denominator bounds for `y′ + h′ y = g`

The coefficient of the Risch equations arising in nested towers is a derivative `f = h′`, which
has no simple pole at a normal prime. Hence (`rde_pole_bound`): if `g` has a pole of order at most
`E + 1` at a normal prime `p`, then `y` has a pole of order at most `E` there — whether `h` is
regular at `p` (then `y′` dominates) or not (then `h′ y` dominates, with a pole of order `≥ 2`
more than `y`).
-/

open Polynomial

namespace Differential

variable {A K : Type*} [CommRing A] [IsDomain A] [WfDvdMonoid A] [Field K] [Algebra A K]
variable [IsFractionRing A K] {p : A} (hp : Prime p)
variable [Differential A] [Differential K] [DifferentialAlgebra A K]

local notation "φ" => algebraMap A K

include hp in
/-- **The pole bound at a normal prime** for `y′ + h′ y = g`. -/
theorem rde_pole_bound (hnorm : ¬p ∣ p′) (hnat : ∀ k : ℕ, k ≠ 0 → ¬p ∣ (k : A)) (h y g : K)
    (E : ℕ) (hg : g * φ p ^ (E + 1) ∈ regularAt K p hp) (hrde : y′ + h′ * y = g) :
    y * φ p ^ E ∈ regularAt K p hp := by
  have hp0 : φ p ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A K)]; exact hp.ne_zero
  have hpm : φ p ∈ regularAt K p hp := algebraMap_mem_regularAt hp p
  by_cases hy0 : y = 0
  · rw [hy0, zero_mul]; exact zero_mem _
  obtain ⟨n, u, hu, rfl⟩ := exists_zpow_mul_isUnitAt hp hy0
  by_cases hn : -(E : ℤ) ≤ n
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, n + E = j := ⟨(n + E).toNat, by omega⟩
    have : φ p ^ n * u * φ p ^ E = φ p ^ j * u := by
      rw [← zpow_natCast, ← zpow_natCast, ← hj, zpow_add₀ hp0, zpow_natCast]; ring
    rw [this]; exact mul_mem (pow_mem hpm _) (hu.mem_regularAt hp)
  exfalso
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
  have hkE : E + 1 ≤ k := by omega
  have hyk : φ p ^ n * u = u / φ p ^ k := by rw [hk, zpow_neg, zpow_natCast]; field_simp
  rw [hyk] at hrde
  set U := (u / φ p ^ k)′ * φ p ^ (k + 1) with hU
  have hUu : IsUnitAt K p U := isUnitAt_deriv_pole hp hnorm hu k (hnat k (by omega))
  obtain ⟨r, hr⟩ : ∃ r, k = E + 1 + r := ⟨k - (E + 1), by omega⟩
  have hreg1 : g * φ p ^ (E + 1) * φ p ^ r ∈ regularAt K p hp := mul_mem hg (pow_mem hpm _)
  have hgk : g * φ p ^ (k + 1) = φ p * (g * φ p ^ (E + 1) * φ p ^ r) := by
    rw [hr]; ring
  by_cases hh : h ∈ regularAt K p hp
  · have hf := deriv_mem_regularAt hp hh
    have e : g * φ p ^ (k + 1) = U + φ p * (h′ * u) := by
      rw [← hrde, hU]
      field_simp
      ring
    refine hUu.ne_mul hp (f := g * φ p ^ (E + 1) * φ p ^ r - h′ * u)
      (sub_mem hreg1 (mul_mem hf (hu.mem_regularAt hp))) ?_
    linear_combination e.symm.trans hgk
  · have hh0 : h ≠ 0 := fun h0 ↦ hh (h0 ▸ zero_mem _)
    obtain ⟨n', v, hv, rfl⟩ := exists_zpow_mul_isUnitAt hp hh0
    have hn' : n' < 0 := by
      by_contra hn'
      obtain ⟨j, hj⟩ : ∃ j : ℕ, n' = j := ⟨n'.toNat, by omega⟩
      refine hh ?_
      rw [hj, zpow_natCast]
      exact mul_mem (pow_mem hpm _) (hv.mem_regularAt hp)
    obtain ⟨l, hl⟩ : ∃ l : ℕ, n' = -((l + 1 : ℕ) : ℤ) := ⟨(-n').toNat - 1, by omega⟩
    have hhv : φ p ^ n' * v = v / φ p ^ (l + 1) := by
      rw [hl, zpow_neg, zpow_natCast]; field_simp
    rw [hhv] at hrde
    set V := (v / φ p ^ (l + 1))′ * φ p ^ (l + 1 + 1) with hV
    have hVv : IsUnitAt K p V := isUnitAt_deriv_pole hp hnorm hv (l + 1) (hnat _ (by omega))
    have hY : u / φ p ^ k * φ p ^ k = u := div_mul_cancel₀ _ (pow_ne_zero _ hp0)
    have e : g * φ p ^ (k + 1) * φ p ^ (l + 1) = U * φ p ^ (l + 1) + V * u := by
      rw [← hrde, hU, hV]
      linear_combination ((v / φ p ^ (l + 1))′ * φ p ^ (l + 1 + 1)) * hY
    refine (hVv.mul' hp hu).ne_mul hp (f := g * φ p ^ (E + 1) * φ p ^ r * φ p ^ (l + 1) -
      U * φ p ^ l) (sub_mem (mul_mem hreg1 (pow_mem hpm _))
        (mul_mem (hUu.mem_regularAt hp) (pow_mem hpm _))) ?_
    rw [hgk] at e
    simp only [hU, hV] at e ⊢
    linear_combination -e
