import RischTragerBronstein.Elementary.Logarithm
import RischTragerBronstein.Elementary.Trans

/-!
# The constructive half of Liouville's theorem

If `f = v′ + ∑ cᵢ * uᵢ′ / uᵢ` with `v, uᵢ ∈ F`, `uᵢ ≠ 0`, and constants `cᵢ ∈ F`, then `f` has an
elementary integral over `F`, namely `v + ∑ cᵢ log uᵢ`. The logarithms are adjoined one at a time;
transitivity of elementary extensions glues the steps together.

This is the form in which every integration algorithm of this development returns its answer:
an algorithm's soundness proof ends by invoking `hasElementaryIntegral_of_liouville_form`.
-/

open Polynomial

namespace Differential

universe u

/-- `(a + c t)′ = a′ + c t′` for a constant `c`. Stated for an abstract differential ring so that
it can be applied to `RatFunc`, whose `ℤ`-algebra structure is not syntactically the canonical
one. -/
lemma deriv_add_const_mul {R : Type*} [CommRing R] [Differential R] (a c t : R) (hc : c′ = 0) :
    (a + c * t)′ = a′ + c * t′ := by
  simp [Derivation.leibniz, hc]

/-- `(a + b)′ = a′ + b′`, for use at types with a non-canonical `ℤ`-algebra structure. -/
lemma deriv_add_const_mul_one {R : Type*} [CommRing R] [Differential R] (a b : R) :
    (a + b)′ = a′ + b′ := map_add _ _ _

/-- Auxiliary form of `hasElementaryIntegral_of_liouville_form`, by induction on the number of
logarithms, quantifying over the field so that the induction hypothesis applies to `F(t)`. -/
private theorem liouville_form_aux (n : ℕ) :
    ∀ (F : Type u) [Field F] [Differential F] (l : List (F × F)) (v : F), l.length = n →
      (∀ p ∈ l, p.1′ = 0 ∧ p.2 ≠ 0) →
      HasElementaryIntegral (v′ + (l.map fun p ↦ p.1 * logDeriv p.2).sum) := by
  induction n with
  | zero =>
    intro F _ _ l v hl _
    rw [List.length_eq_zero_iff.mp hl]
    simpa using hasElementaryIntegral_of_deriv v
  | succ n ih =>
    intro F _ _ l v hl hcu
    obtain ⟨⟨c, u⟩, l', rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    obtain ⟨hc, hu⟩ := hcu (c, u) (List.mem_cons_self ..)
    -- adjoin `t = log u`
    let _ : Differential (RatFunc F) := ratFuncOfDeriv (C (logDeriv u))
    have hDA : DifferentialAlgebra F (RatFunc F) := differentialAlgebra_ratFuncOfDeriv _
    obtain ⟨hE, hX⟩ := isElementaryExtension_log u hu
    refine HasElementaryIntegral.of_extension hE ?_
    let φ : F →+* RatFunc F := algebraMap F (RatFunc F)
    have hφd : ∀ a : F, (φ a)′ = φ a′ := fun a ↦ deriv_algebraMap a
    have hφl : ∀ a : F, φ (logDeriv a) = logDeriv (φ a) := fun a ↦ (logDeriv_algebraMap a).symm
    have hsum : ∀ l : List (F × F), φ (l.map fun p ↦ p.1 * logDeriv p.2).sum =
        ((l.map (Prod.map φ φ)).map fun p ↦ p.1 * logDeriv p.2).sum := by
      intro l
      induction l with
      | nil => simp
      | cons p l ihl =>
        simp only [List.map_cons, List.sum_cons, map_add, map_mul, ihl, Prod.map_fst,
          Prod.map_snd, hφl]
    -- over `F(t)` the integrand has one logarithm less
    have key : φ (v′ + (((c, u) :: l').map fun p : F × F ↦ p.1 * logDeriv p.2).sum) =
        (φ v + φ c * RatFunc.X)′ +
          ((l'.map (Prod.map φ φ)).map fun p ↦ p.1 * logDeriv p.2).sum := by
      have hc' : (φ c)′ = 0 := by rw [hφd, hc, map_zero]
      rw [List.map_cons, List.sum_cons, map_add, map_add, map_mul, hsum,
        deriv_add_const_mul _ _ _ hc', hX, hφd, hφl]
      ring
    change HasElementaryIntegral (φ _)
    rw [key]
    refine ih (RatFunc F) _ _ (by simpa using hl) ?_
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hq1, hq2⟩ := hcu q (List.mem_cons_of_mem _ hq)
    refine ⟨?_, ?_⟩
    · change (φ q.1)′ = 0
      rw [hφd, hq1, map_zero]
    · change φ q.2 ≠ 0
      exact (map_ne_zero φ).mpr hq2

variable {F : Type u} [Field F] [Differential F]

/-- **Liouville's theorem, constructive direction.** `v′ + ∑ cᵢ uᵢ′ / uᵢ` with constant `cᵢ` and
nonzero `uᵢ` has an elementary integral. -/
theorem hasElementaryIntegral_of_liouville_form (v : F) (l : List (F × F))
    (h : ∀ p ∈ l, p.1′ = 0 ∧ p.2 ≠ 0) :
    HasElementaryIntegral (v′ + (l.map fun p ↦ p.1 * logDeriv p.2).sum) :=
  liouville_form_aux l.length F l v rfl h

end Differential
