import RischTragerBronstein.Liouville.PrimitivePoly
import RischTragerBronstein.Differential.Constants

/-!
# A primitive that is not a derivative introduces no new constant polynomials

If `η ∈ F` is not a derivative of an element of `F` (characteristic zero), then the only
`P ∈ F[t]`, `t′ = η`, with `P′ = 0` are the constants of `F`.
-/

open Polynomial

namespace Differential

variable {F : Type*} [Field F] [CharZero F] [Differential F] (η : F)

theorem const_of_implicitDeriv_eq_zero (hη : ∀ y : F, y′ ≠ η) {P : F[X]}
    (h : implicitDeriv (C η) P = 0) : ∃ e : F, P = C e := by
  by_contra hne
  have hdeg : P.natDegree ≠ 0 := fun h0 ↦ hne ⟨P.coeff 0, eq_C_of_natDegree_eq_zero h0⟩
  obtain ⟨n, hn⟩ : ∃ n, P.natDegree = n + 1 := ⟨P.natDegree - 1, by omega⟩
  have hcoeff : ∀ k, (P.coeff k)′ + η * (P.coeff (k + 1) * (k + 1)) = 0 := fun k ↦ by
    rw [← coeff_implicitDeriv_C, h, coeff_zero]
  set a := P.coeff (n + 1) with ha
  have ha0 : a ≠ 0 := by
    rw [ha, ← hn]
    exact leadingCoeff_ne_zero.mpr fun h0 ↦ by simp [h0] at hn
  have ha' : a′ = 0 := by
    have := hcoeff (n + 1)
    rwa [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < n + 1 + 1), zero_mul, mul_zero,
      add_zero] at this
  have hn1 : ((n : F) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  -- the constant `c = (a (n + 1))⁻¹`
  have hc : (a * ((n : F) + 1))⁻¹ ∈ constants F := by
    refine inv_mem (mul_mem (mem_constants.mpr ha') ?_)
    have : ((n : F) + 1) = ((n + 1 : ℕ) : F) := by push_cast; ring
    rw [this]
    exact natCast_mem _ _
  rw [mem_constants] at hc
  refine hη (-(P.coeff n) * (a * ((n : F) + 1))⁻¹) ?_
  have hk := hcoeff n
  rw [Derivation.leibniz, hc, map_neg]
  simp only [smul_eq_mul, mul_zero, zero_add]
  field_simp
  linear_combination -hk
end Differential
