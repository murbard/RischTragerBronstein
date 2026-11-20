import RischTragerBronstein.Computable.LimitedPrimCodes
import RischTragerBronstein.Computable.Prim2TimesPositive

/-!
# Limited integration inside `S(x)(t₁)`: the polynomial form of soundness

In a two-level model `K₁ = S(x) ⊆ K₂ ∋ t₁`, `t₁′ = η₁`, the codes returned by `limitedPrimCodes`
assemble to a polynomial `P = ∑ pⱼ t₁ ^ j ∈ K₂` with

  `P′ = A - c η₂`.

This is the step solver for the polynomial part at the next tower level (`t₂′ = η₂`).
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S[X]] [Field K₁] [Algebra S[X] K₁] [IsFractionRing S[X] K₁]
variable [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Field K₂] [Differential K₂] [Algebra K₁ K₂] [DifferentialAlgebra K₁ K₂]

local notation "φ" => algebraMap S[X] K₁

/-- The value in `K₂` of a polynomial in `t₁` given by fraction codes of its coefficients. -/
noncomputable def ev₂ (ι : R →+* S) (t₁ : K₂) (P : ℕ → CPoly R × CPoly R) (n : ℕ) : K₂ :=
  ∑ j ∈ Finset.range (n + 1), algebraMap K₁ K₂ (ev K₁ ι (P j)) * t₁ ^ j

theorem limitedPrimCodes_sound_poly (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {En Ed En₂ Ed₂ : CPoly R} {Iη₁ Iη₂ : RationalIntegral R}
    (hcη₁ : rationalCheck En Ed Iη₁ = true) (hcη₂ : rationalCheck En₂ Ed₂ Iη₂ = true)
    (hEd : toPoly Ed ≠ 0) (t₁ : K₂) (ht₁ : t₁′ = algebraMap K₁ K₂ (ev K₁ ι (En, Ed)))
    (A D : ℕ → CPoly R) (d : ℕ) (hD0 : ∀ j ≤ d, toPoly (D j) ≠ 0) {c : R}
    {P : ℕ → CPoly R × CPoly R}
    (h : limitedPrimCodes En Ed Iη₁ Iη₂ A D d = some (c, P)) :
    (∀ j ≤ d + 1, toPoly (P j).2 ≠ 0) ∧
      (ev₂ (K₁ := K₁) ι t₁ P (d + 1))′ = ev₂ (K₁ := K₁) ι t₁ (fun j ↦ (A j, D j)) d -
        algebraMap K₁ K₂ (φ (C (ι c)) * ev K₁ ι (En₂, Ed₂)) := by
  obtain ⟨hden, hpe, hp0, hpd⟩ := limitedPrimCodes_sound (K := K₁) ι hD hcη₁ hcη₂ hEd A D d hD0 h
  refine ⟨hden, ?_⟩
  set η₁ : K₂ := algebraMap K₁ K₂ (ev K₁ ι (En, Ed)) with hη₁
  let q : ℕ → K₂ := fun j ↦ algebraMap K₁ K₂ (ev K₁ ι (P j))
  have hqe : ∀ j, 1 ≤ j → j ≤ d → (q j)′ + ((j + 1 : ℕ) : K₂) * η₁ * q (j + 1) =
      algebraMap K₁ K₂ (ev K₁ ι (A j, D j)) := fun j h1 h2 ↦ by
    have := congrArg (algebraMap K₁ K₂) (hpe j h1 h2)
    simp only [map_add, map_mul, map_natCast] at this
    rw [← this, deriv_algebraMap]
  have hq0 : (q 0)′ + η₁ * q 1 = algebraMap K₁ K₂ (ev K₁ ι (A 0, D 0)) -
      algebraMap K₁ K₂ (φ (C (ι c)) * ev K₁ ι (En₂, Ed₂)) := by
    have := congrArg (algebraMap K₁ K₂) hp0
    simp only [map_add, map_mul, map_sub] at this
    rw [map_mul, ← this, deriv_algebraMap]
  have hqd : (q (d + 1))′ = 0 := by
    change (algebraMap K₁ K₂ _)′ = 0
    rw [deriv_algebraMap, hpd, map_zero]
  change (∑ j ∈ Finset.range (d + 1 + 1), q j * t₁ ^ j)′ = _
  rw [deriv_sum_mul_pow t₁ η₁ ht₁ q (d + 1), hqd, zero_mul, add_zero, ev₂,
    Finset.sum_range_succ' _ d, Finset.sum_range_succ' (fun j ↦
      algebraMap K₁ K₂ (ev K₁ ι (A j, D j)) * t₁ ^ j) d]
  have h1 : ∑ j ∈ Finset.range d, ((q (j + 1))′ + ((j + 1 + 1 : ℕ) : K₂) * η₁ * q (j + 1 + 1)) *
      t₁ ^ (j + 1) = ∑ j ∈ Finset.range d,
      algebraMap K₁ K₂ (ev K₁ ι (A (j + 1), D (j + 1))) * t₁ ^ (j + 1) :=
    Finset.sum_congr rfl fun j hj ↦ by
      rw [hqe (j + 1) (by omega) (by have := Finset.mem_range.mp hj; omega)]
  rw [h1]
  simp only [pow_zero, mul_one, Nat.cast_one, zero_add, one_mul]
  rw [hq0]
  ring

end CPoly
