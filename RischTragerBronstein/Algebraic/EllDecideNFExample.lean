import RischTragerBronstein.Algebraic.EllDecideNF

/-!
# Automatic splitting data: two integrals over `ℚ(√2) = NF (x² − 2)`

`ellDecideNF` finds the roots `±√2` of `D = x² − 2` and square roots of `p(±√2) = 4` in
`ℚ(√2)` itself (Trager's norm method, `rootsIn`, run by the kernel), then decides:

* `∫ (2x² + 4) dx / ((x² − 2) √(x³ + 2x² − 2x))` is **elementary**;
* `∫ 8 dx / ((x² − 2) √(x³ + 2x² − 2x))` is **not elementary**.
-/

open Polynomial Differential EllQuad NFC CPoly EllDV

namespace NFExample4

/-- `x² − 2`. -/
abbrev f2 : CPoly ℚ := [-2, 0, 1]

instance : Fact (Irreducible (toPoly f2)) := ⟨Kron.irredQ_sound _ (by decide +kernel)⟩

lemma run1 : ellDecideNF f2 2 (-2) 0 [4, 0, 2] [-2, 0, 1] (redCount 7 2 (-2) 0 + 1) = some true := by
  decide +kernel

lemma run2 : ellDecideNF f2 2 (-2) 0 [8] [-2, 0, 1] (redCount 7 2 (-2) 0 + 1) = some false := by
  decide +kernel

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

lemma hsq : Squarefree (X ^ 3 + C ((2 : ℤ) : ℚ) * X ^ 2 + C ((-2 : ℤ) : ℚ) * X + C ((0 : ℤ) : ℚ)) := by
  have h := CPoly.squarefreeCheck_sound (s := EllAlgo.pOf 2 (-2) 0) (by decide +kernel)
  rwa [EllAlgo.toPoly_pOf] at h

lemma hgood : goodRedMod 7 2 (-2) 0 := by decide

lemma hN : Fintype.card (Option (RedPts 7 2 (-2) 0)) ≤ redCount 7 2 (-2) 0 + 1 := by
  rw [Fintype.card_option, card_RedPts]

lemma embed : Nonempty (NF f2 →ₐ[ℚ] ℚ_[7]) :=
  exists_embedNF f2 (X ^ 2 - C 2) (by simp [CPoly.toPoly, map_ofNat]; ring) (3 : ZMod 7)
    (by simp; decide) (by simp; decide)

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ (2x² + 4) dx / ((x² − 2)√(x³ + 2x² − 2x))` is elementary** (splitting data computed). -/
theorem auto_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 2 * x ^ 2 - 2 * x) (hgen : ∀ z : E, InHyp Kc x y z) (ι : NF f2 →+* Kc) :
    HasElementaryIntegral ((2 * x ^ 2 + 4) / ((x ^ 2 - 2) * y)) := by
  obtain ⟨φ⟩ := embed
  have h := ellDecideNF_spec f2 hC hCall x y hx 2 (-2) 0 hsq (by rw [hy]; push_cast; ring) hgen ι
    [4, 0, 2] [-2, 0, 1] 7 (by norm_num) hgood φ _ hN true run1
  have hA : aeval x (toPoly ([4, 0, 2] : CPoly ℚ)) = 2 * x ^ 2 + 4 := by simp [CPoly.toPoly]; ring
  have hD : aeval x (toPoly ([-2, 0, 1] : CPoly ℚ)) = x ^ 2 - 2 := by simp [CPoly.toPoly]; ring
  rw [hA, hD] at h
  exact h.mp rfl

/-- **`∫ 8 dx / ((x² − 2)√(x³ + 2x² − 2x))` is not elementary** (splitting data computed). -/
theorem auto_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 2 * x ^ 2 - 2 * x) (hgen : ∀ z : E, InHyp Kc x y z) (ι : NF f2 →+* Kc) :
    ¬HasElementaryIntegral (8 / ((x ^ 2 - 2) * y)) := by
  obtain ⟨φ⟩ := embed
  have h := ellDecideNF_spec f2 hC hCall x y hx 2 (-2) 0 hsq (by rw [hy]; push_cast; ring) hgen ι
    [8] [-2, 0, 1] 7 (by norm_num) hgood φ _ hN false run2
  have hA : aeval x (toPoly ([8] : CPoly ℚ)) = 8 := by simp [CPoly.toPoly]
  have hD : aeval x (toPoly ([-2, 0, 1] : CPoly ℚ)) = x ^ 2 - 2 := by simp [CPoly.toPoly]; ring
  rw [hA, hD] at h
  exact fun he ↦ Bool.false_ne_true (h.mpr he)

end NFExample4
