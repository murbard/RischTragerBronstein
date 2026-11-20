import RischTragerBronstein.Algebraic.NumField
import RischTragerBronstein.Algebraic.EllDecideADK

/-!
# Elliptic integrals over the non-normal cubic field `ℚ(∛12)`

`K = ℚ(θ)`, `θ³ = 12` (`NF [-12, 0, 0, 1]`), curve `y² = x³ − 3`, point `P = (θ, 3)` (of order 3).
`ellDecideK` runs in the kernel (torsion bound at `p = 5`, where `θ ≡ 3` is a simple root):

* `∫ 3 dx / ((x − θ) y)` is **not elementary** (the log part is torsion, but the holomorphic
  remainder `−θ²/6 · dx/y` survives);
* `∫ (θ²/6 + 3/(x − θ)) dx / y` is **elementary**.
-/

open Polynomial Differential EllQuad NFC CPoly EllDV

namespace NFExample

/-- `x³ − 12`. -/
abbrev f12 : CPoly ℚ := [-12, 0, 0, 1]

instance : Fact (Irreducible (toPoly f12)) := ⟨Kron.irredQ_sound _ (by decide +kernel)⟩

/-- `ℚ(∛12)`. -/
abbrev K3 := NF f12

/-- `θ = ∛12`. -/
def θ : K3 := mk f12 [0, 1]

/-- The pole at `P = (θ, 3)` with residue `1`. -/
def ptsC : List (K3 × K3 × K3) := [(θ, 3, 1)]

lemma run1 : ellDecideK (K := K3) 0 0 (-3) [] ptsC (redCount 5 0 0 (-3) + 1) = some false := by
  decide +kernel

lemma run2 : ellDecideK (K := K3) 0 0 (-3) [mk f12 [0, 0, 1 / 6]] ptsC
    (redCount 5 0 0 (-3) + 1) = some true := by
  decide +kernel

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

lemma hsq : Squarefree (X ^ 3 + C ((0 : ℤ) : ℚ) * X ^ 2 + C ((0 : ℤ) : ℚ) * X + C ((-3 : ℤ) : ℚ)) := by
  have h := CPoly.squarefreeCheck_sound (s := EllAlgo.pOf 0 0 (-3)) (by decide +kernel)
  rwa [EllAlgo.toPoly_pOf] at h

lemma hgood : goodRedMod 5 0 0 (-3) := by decide

lemma hN : Fintype.card (Option (RedPts 5 0 0 (-3))) ≤ redCount 5 0 0 (-3) + 1 := by
  rw [Fintype.card_option, card_RedPts]

lemma embed : Nonempty (K3 →ₐ[ℚ] ℚ_[5]) :=
  exists_embedNF f12 (X ^ 3 - C 12) (by simp [CPoly.toPoly, map_ofNat]; ring) (3 : ZMod 5)
    (by simp; decide) (by simp; decide)

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ 3 dx / ((x − ∛12) √(x³ − 3))` is not elementary.** -/
theorem cubic_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 - 3) (hgen : ∀ z : E, InHyp Kc x y z) (ι : K3 →+* Kc) :
    ¬HasElementaryIntegral ((evF ι x [] + (ptsC.map fun q ↦
      algebraMap Kc E (ι (q.2.2 * q.2.1)) / (x - algebraMap Kc E (ι q.1))).sum) / y) := by
  obtain ⟨φ⟩ := embed
  have h := ellDecideK_spec hC hCall x y hx 0 0 (-3) hsq (by rw [hy]; push_cast; ring) hgen ι []
    ptsC 5 (by norm_num) hgood φ _ hN false run1
  exact fun he ↦ Bool.false_ne_true (h.mpr he)

/-- **`∫ (θ²/6 + 3/(x − θ)) dx / √(x³ − 3)` is elementary** (`θ = ∛12`). -/
theorem cubic_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 - 3) (hgen : ∀ z : E, InHyp Kc x y z) (ι : K3 →+* Kc) :
    HasElementaryIntegral ((evF ι x [mk f12 [0, 0, 1 / 6]] + (ptsC.map fun q ↦
      algebraMap Kc E (ι (q.2.2 * q.2.1)) / (x - algebraMap Kc E (ι q.1))).sum) / y) := by
  obtain ⟨φ⟩ := embed
  have h := ellDecideK_spec hC hCall x y hx 0 0 (-3) hsq (by rw [hy]; push_cast; ring) hgen ι
    [mk f12 [0, 0, 1 / 6]] ptsC 5 (by norm_num) hgood φ _ hN true run2
  exact h.mp rfl

end NFExample

/-!
## A rational integrand whose poles have a cubic residue field

`D = x³ − 3x + 1` is irreducible over `ℚ` and splits over the cyclic cubic field `ℚ(θ)`,
`θ³ − 3θ + 1 = 0`, with roots `θ, θ² − 2, 2 − θ − θ²`. On `y² = x³ + x² − x + 2 = D + (x + 1)²` the
poles lie over the points `(α, α + 1)`. `ellDecideADK` checks the splitting and decides
`∫ dx / ((x³ − 3x + 1) y)` (torsion bound at `p = 17`, where `θ ≡ 7`).
-/

namespace NFExample2

open Polynomial Differential EllQuad NFC CPoly EllDV

/-- `x³ − 3x + 1`. -/
abbrev f9 : CPoly ℚ := [1, -3, 0, 1]

instance : Fact (Irreducible (toPoly f9)) := ⟨Kron.irredQ_sound _ (by decide +kernel)⟩

/-- The cyclic cubic field `ℚ(2 cos(2π/9))`. -/
abbrev K9 := NF f9

/-- `θ`. -/
def θ : K9 := mk f9 [0, 1]

/-- The splitting data: the roots `α` of `D` and the ordinates `α + 1`. -/
noncomputable def ptsA : List (K9 × K9) :=
  [θ, θ ^ 2 - 2, 2 - θ - θ ^ 2].map fun α ↦ (α, α + 1)

lemma run : ellDecideADK (K := K9) 1 (-1) 2 [1] [1, -3, 0, 1] ptsA (redCount 17 1 (-1) 2 + 1) =
    some false := by
  decide +kernel

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

lemma hsq : Squarefree (X ^ 3 + C ((1 : ℤ) : ℚ) * X ^ 2 + C ((-1 : ℤ) : ℚ) * X + C ((2 : ℤ) : ℚ)) := by
  have h := CPoly.squarefreeCheck_sound (s := EllAlgo.pOf 1 (-1) 2) (by decide +kernel)
  rwa [EllAlgo.toPoly_pOf] at h

lemma hgood : goodRedMod 17 1 (-1) 2 := by decide

lemma hN : Fintype.card (Option (RedPts 17 1 (-1) 2)) ≤ redCount 17 1 (-1) 2 + 1 := by
  rw [Fintype.card_option, card_RedPts]

lemma embed : Nonempty (K9 →ₐ[ℚ] ℚ_[17]) :=
  exists_embedNF f9 (X ^ 3 - C 3 * X + 1) (by simp [CPoly.toPoly, map_ofNat]; ring) (7 : ZMod 17)
    (by simp; decide) (by simp; decide)

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **`∫ dx / ((x³ − 3x + 1) √(x³ + x² − x + 2))` is not elementary** (constants containing the
cyclic cubic field). -/
theorem cyclic_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + x ^ 2 - x + 2) (hgen : ∀ z : E, InHyp Kc x y z) (ι : K9 →+* Kc) :
    ¬HasElementaryIntegral (1 / ((x ^ 3 - 3 * x + 1) * y)) := by
  obtain ⟨φ⟩ := embed
  have h := ellDecideADK_spec hC hCall x y hx 1 (-1) 2 hsq (by rw [hy]; push_cast; ring) hgen ι
    [1] [1, -3, 0, 1] ptsA 17 (by norm_num) hgood φ _ hN false run
  have hA : aeval x (toPoly ([1] : CPoly ℚ)) = 1 := by simp [CPoly.toPoly]
  have hD : aeval x (toPoly ([1, -3, 0, 1] : CPoly ℚ)) = x ^ 3 - 3 * x + 1 := by
    simp [CPoly.toPoly]; ring
  rw [hA, hD] at h
  exact fun he ↦ Bool.false_ne_true (h.mpr he)

end NFExample2

