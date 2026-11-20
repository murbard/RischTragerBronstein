import RischTragerBronstein.Algebraic.EllDecideAD
import RischTragerBronstein.Algebraic.EllIrrationalElemExample

/-!
# The automatic quadratic-orbit procedure on three integrands

`quadOrbitDecide` (with `d = 2`, reduction prime `7`, `√2 ≡ 3 mod 7`) is run by the kernel and its
answer is turned into a theorem by `quadOrbitDecide_spec`:

* `(4x + 4) / ((x² − 2)√(x³ + x² + 1))` — not elementary (`P − σP` has infinite order);
* `(2x² + 4) / ((x² − 2)√(x³ + 2x² − 2x))` — elementary;
* `8 / ((x² − 2)√(x³ + 2x² − 2x))` — not elementary (torsion holds, holomorphic remainder).
-/

open Polynomial Differential EllDV

namespace EllAlgo.QuadDecideExample

open CPoly EllQuad

instance : Fact (¬IsSquare (((2 : ℤ)) : ℚ)) :=
  ⟨by rw [Int.cast_ofNat]; exact Fact.out⟩

lemma hgood1 : goodRedMod 7 1 0 1 := by decide
lemma hgood2 : goodRedMod 7 2 (-2) 0 := by decide

lemma hrun1 : quadOrbitDecide (d := 2) 1 0 1 [4, 4] [-2, 0, 1] 7 = some false := by
  decide +kernel

lemma hrun2 : quadOrbitDecide (d := 2) 2 (-2) 0 [4, 0, 2] [-2, 0, 1] 7 = some true := by
  decide +kernel

lemma hrun3 : quadOrbitDecide (d := 2) 2 (-2) 0 [8] [-2, 0, 1] 7 = some false := by
  decide +kernel

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

lemma h3sq : (3 : ZMod 7) ^ 2 = ((2 : ℤ) : ZMod 7) := by decide
lemma h3ne : (2 : ZMod 7) * 3 ≠ 0 := by decide

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma sq_one : Squarefree (X ^ 3 + C ((1 : ℤ) : ℚ) * X ^ 2 + C ((0 : ℤ) : ℚ) * X + C ((1 : ℤ) : ℚ)) := by
  have h := CPoly.squarefreeCheck_sound (s := EllAlgo.pOf 1 0 1) (by decide +kernel)
  rwa [EllAlgo.toPoly_pOf] at h

lemma sq_two :
    Squarefree (X ^ 3 + C ((2 : ℤ) : ℚ) * X ^ 2 + C ((-2 : ℤ) : ℚ) * X + C ((0 : ℤ) : ℚ)) := by
  have h := CPoly.squarefreeCheck_sound (s := EllAlgo.pOf 2 (-2) 0) (by decide +kernel)
  rwa [EllAlgo.toPoly_pOf] at h

omit [Differential E] in
lemma evD (x : E) : aeval x (toPoly ([-2, 0, 1] : CPoly ℚ)) = x ^ 2 - 2 := by
  simp [CPoly.toPoly]; ring

/-- **Automatic**: `∫ (4x + 4) dx / ((x² − 2)√(x³ + x² + 1))` is not elementary. -/
theorem auto_not_elementary_nontorsion (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + x ^ 2 + 1) (hgen : ∀ z : E, InHyp Kc x y z)
    (s2 : Kc) (hs2 : s2 ^ 2 = 2) :
    ¬HasElementaryIntegral ((4 * x + 4) / ((x ^ 2 - 2) * y)) := by
  have h := quadOrbitDecide_spec (d := 2) hC hCall x y hx 1 0 1 sq_one
    (by rw [hy]; push_cast; ring) hgen s2 (by rw [hs2]; norm_num) [4, 4] [-2, 0, 1] 7
    (by norm_num) hgood1 3 h3sq h3ne false hrun1
  have hA : aeval x (toPoly ([4, 4] : CPoly ℚ)) = 4 * x + 4 := by simp [CPoly.toPoly]; ring
  rw [hA, evD] at h
  exact fun he ↦ Bool.false_ne_true (h.mpr he)

/-- **Automatic**: `∫ (2x² + 4) dx / ((x² − 2)√(x³ + 2x² − 2x))` is elementary. -/
theorem auto_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 2 * x ^ 2 - 2 * x) (hgen : ∀ z : E, InHyp Kc x y z)
    (s2 : Kc) (hs2 : s2 ^ 2 = 2) :
    HasElementaryIntegral ((2 * x ^ 2 + 4) / ((x ^ 2 - 2) * y)) := by
  have h := quadOrbitDecide_spec (d := 2) hC hCall x y hx 2 (-2) 0 sq_two
    (by rw [hy]; push_cast; ring) hgen s2 (by rw [hs2]; norm_num) [4, 0, 2] [-2, 0, 1] 7
    (by norm_num) hgood2 3 h3sq h3ne true hrun2
  have hA : aeval x (toPoly ([4, 0, 2] : CPoly ℚ)) = 2 * x ^ 2 + 4 := by
    simp [CPoly.toPoly]; ring
  rw [hA, evD] at h
  exact h.mp rfl

/-- **Automatic**: `∫ 8 dx / ((x² − 2)√(x³ + 2x² − 2x))` is not elementary. -/
theorem auto_not_elementary_remainder (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 2 * x ^ 2 - 2 * x) (hgen : ∀ z : E, InHyp Kc x y z)
    (s2 : Kc) (hs2 : s2 ^ 2 = 2) :
    ¬HasElementaryIntegral (8 / ((x ^ 2 - 2) * y)) := by
  have h := quadOrbitDecide_spec (d := 2) hC hCall x y hx 2 (-2) 0 sq_two
    (by rw [hy]; push_cast; ring) hgen s2 (by rw [hs2]; norm_num) [8] [-2, 0, 1] 7
    (by norm_num) hgood2 3 h3sq h3ne false hrun3
  have hA : aeval x (toPoly ([8] : CPoly ℚ)) = 8 := by simp [CPoly.toPoly]
  rw [hA, evD] at h
  exact fun he ↦ Bool.false_ne_true (h.mpr he)

/-! ### Mixed data: a conjugate pair and a rational point (`ellDecideF`) -/

/-- `ℚ(√2)` as `ellDecideF` sees it. -/
abbrev Q2' := QuadraticAlgebra ℚ ((2 : ℤ) : ℚ) 0

/-- Poles at `(√2, 2)`, `(−√2, 2)` (residues `±√2`) and at the rational point `(1, 1)` (residue 1). -/
def ptsM : List (Q2' × Q2' × Q2') := [(⟨0, 1⟩, 2, ⟨0, 1⟩), (⟨0, -1⟩, 2, ⟨0, -1⟩), (1, 1, 1)]

lemma hrunF : ellDecideF (d := 2) 2 (-2) 0 [2] ptsM 7 = some false := by
  decide +kernel

/-- **Automatic**: `∫ (2 + 2√2/(x − √2) + 2√2/(x + √2)·(−1) + 1/(x − 1)) dx / √(x³ + 2x² − 2x)`
is not elementary. -/
theorem auto_mixed_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 2 * x ^ 2 - 2 * x) (hgen : ∀ z : E, InHyp Kc x y z) (ι : Q2' →+* Kc) :
    ¬HasElementaryIntegral ((evF ι x [2] + (ptsM.map fun q ↦
      algebraMap Kc E (ι (q.2.2 * q.2.1)) / (x - algebraMap Kc E (ι q.1))).sum) / y) := by
  have h := ellDecideF_spec (d := 2) hC hCall x y hx 2 (-2) 0 sq_two
    (by rw [hy]; push_cast; ring) hgen ι [2] ptsM 7 (by norm_num) hgood2 3 h3sq h3ne false hrunF
  exact fun he ↦ Bool.false_ne_true (h.mpr he)

/-! ### From `A / (D y)` directly (`ellDecideAD`) -/

lemma hrunAD : ellDecideAD (d := 2) 2 (-2) 0 [1] [2, -2, -1, 1] 7 = some false := by
  decide +kernel

/-- **Automatic**: `∫ dx / ((x² − 2)(x − 1) √(x³ + 2x² − 2x))` is not elementary (`D` factored
over `ℚ(√2)`, partial fractions at `±√2` and `1`). -/
theorem auto_AD_not_elementary (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (hy : y ^ 2 = x ^ 3 + 2 * x ^ 2 - 2 * x) (hgen : ∀ z : E, InHyp Kc x y z) (ι : Q2' →+* Kc) :
    ¬HasElementaryIntegral (1 / ((x ^ 3 - x ^ 2 - 2 * x + 2) * y)) := by
  have h := ellDecideAD_spec (d := 2) hC hCall x y hx 2 (-2) 0 sq_two
    (by rw [hy]; push_cast; ring) hgen ι [1] [2, -2, -1, 1] 7 (by norm_num) hgood2 3 h3sq h3ne
    false hrunAD
  have hA : aeval x (toPoly ([1] : CPoly ℚ)) = 1 := by simp [CPoly.toPoly]
  have hD : aeval x (toPoly ([2, -2, -1, 1] : CPoly ℚ)) = x ^ 3 - x ^ 2 - 2 * x + 2 := by
    simp [CPoly.toPoly]; ring
  rw [hA, hD] at h
  exact fun he ↦ Bool.false_ne_true (h.mpr he)

end EllAlgo.QuadDecideExample
