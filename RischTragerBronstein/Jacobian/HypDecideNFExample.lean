import RischTragerBronstein.Jacobian.HypDecideNF

/-!
# The number-field pipeline, checked by the kernel

`hypDecideNF M f g A D B` runs in the kernel (`decide +kernel`); with `hypDecideNF_spec` its
answer becomes a theorem. Here over `NF [0, 1] = ℚ`: `∫ dx / (x √(x⁵ + 1))` is elementary.
-/

open Polynomial CPoly Differential Jac

namespace Jac.NFExample

instance : Fact (Irreducible (toPoly ([0, 1] : CPoly ℚ))) := ⟨Kron.irredQ_sound _ NFC.irredQ_X⟩

set_option maxRecDepth 100000 in
lemma run : hypDecideNF [0, 1] [1, 0, 0, 0, 0, 1] 2 [1] [0, 1] 20 = some true := by
  decide +kernel

lemma sq_f : Squarefree ((toPoly [1, 0, 0, 0, 0, 1]).map (Int.castRingHom ℚ)) := by
  have := squarefreeCheck_sound (s := ([1, 0, 0, 0, 0, 1] : List ℤ).map (Int.castRingHom ℚ))
    (by decide +kernel)
  rwa [toPoly_map_list] at this

lemma deg_f : ((toPoly [1, 0, 0, 0, 0, 1]).map (Int.castRingHom ℚ)).natDegree = 2 * 2 + 1 := by
  rw [natDegree_map_eq_of_injective (RingHom.injective_int _)]
  exact natDegree_of_list (by rfl) (by decide)

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ dx / (x √(x⁵ + 1))` is elementary**, decided by the number-field pipeline. -/
theorem x5_elementary [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 5 + 1) (hgen : ∀ z : E, InHyp Kc x y z) :
    HasElementaryIntegral (1 / (x * y)) := by
  let ι : NFC.NF [0, 1] →+* Kc :=
    (IsAlgClosed.lift (R := ℚ) (S := NFC.NF [0, 1]) (M := Kc)).toRingHom
  have hy' : y ^ 2 = aeval x ((toPoly [1, 0, 0, 0, 0, 1]).map (Int.castRingHom ℚ)) := by
    rw [hy]; simp [CPoly.toPoly]; ring
  have := (hypDecideNF_spec [0, 1] (by decide) hC hCall x y hx sq_f deg_f hy' hgen ι [1] [0, 1] 20
    true run).mp rfl
  convert this using 1
  simp [CPoly.toPoly]

end Jac.NFExample
