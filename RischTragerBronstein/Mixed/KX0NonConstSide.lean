import RischTragerBronstein.Mixed.KXCertBridgeTRev
import RischTragerBronstein.Mixed.KXMWDecideT
import RischTragerBronstein.Mixed.PolyOfSpec

/-!
# The level-`0` search data for non-constant curves (part 1: the short model)

As at the levels `m + 1` (`KXNonConstSide`): the search scales the short model by `uF = mwU` (the
product of the reduced denominators of `c₀, …, c₃`); **`AFr_poly`, `BFr_poly`**: the scaled
coefficients have polynomial values, so the read-off `polyOf` is exact (`polyOf_eq_of_val`) for
arbitrary (non-constant) coefficients.
-/

open Polynomial

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
variable (c0f : CPoly ℚ) (A : GPoly (LC 0))

local notation "ι" => algebraMap ℚ[X] (RatFunc ℚ)

/-- The reduced denominator of `cᵢ`. -/
abbrev d0 (i : ℕ) : CPoly ℚ := (Fr.norm (cF Fc ks c0f A i)).2
/-- The reduced numerator of `cᵢ`. -/
abbrev n0 (i : ℕ) : CPoly ℚ := (Fr.norm (cF Fc ks c0f A i)).1

variable {Fc ks c0f A}

theorem mwU_eq : mwU Fc ks c0f A = Fr.mul (Fr.ofPoly (d0 Fc ks c0f A 0))
    (Fr.mul (Fr.ofPoly (d0 Fc ks c0f A 1)) (Fr.mul (Fr.ofPoly (d0 Fc ks c0f A 2))
      (Fr.mul (Fr.ofPoly (d0 Fc ks c0f A 3)) (Fr.ofPoly [1])))) := rfl

theorem val_mwU : Fr.val (mwU Fc ks c0f A) = ι (toPoly (d0 Fc ks c0f A 0)) *
    (ι (toPoly (d0 Fc ks c0f A 1)) * (ι (toPoly (d0 Fc ks c0f A 2)) *
      (ι (toPoly (d0 Fc ks c0f A 3)) * 1))) := by
  rw [mwU_eq]
  simp only [Fr.val_mul (Fr.ok_ofPoly _) (Fr.ok_mul (Fr.ok_ofPoly _) (Fr.ok_mul (Fr.ok_ofPoly _)
    (Fr.ok_mul (Fr.ok_ofPoly _) (Fr.ok_ofPoly _)))), Fr.val_mul (Fr.ok_ofPoly _) (Fr.ok_mul
    (Fr.ok_ofPoly _) (Fr.ok_mul (Fr.ok_ofPoly _) (Fr.ok_ofPoly _))), Fr.val_mul (Fr.ok_ofPoly _)
    (Fr.ok_mul (Fr.ok_ofPoly _) (Fr.ok_ofPoly _)), Fr.val_mul (Fr.ok_ofPoly _) (Fr.ok_ofPoly _),
    Fr.val_ofPoly]
  simp [CPoly.toPoly]

theorem ok_mwU : Fr.ok (mwU Fc ks c0f A) := by
  rw [mwU_eq]
  exact Fr.ok_mul (Fr.ok_ofPoly _) (Fr.ok_mul (Fr.ok_ofPoly _) (Fr.ok_mul (Fr.ok_ofPoly _)
    (Fr.ok_mul (Fr.ok_ofPoly _) (Fr.ok_ofPoly _))))

theorem val_cF (hok : ∀ i < 4, Fr.ok (cF Fc ks c0f A i)) (i : ℕ) (hi : i < 4) :
    Fr.val (cF Fc ks c0f A i) = ι (toPoly (n0 Fc ks c0f A i)) / ι (toPoly (d0 Fc ks c0f A i)) := by
  rw [← Fr.val_norm (hok i hi)]; rfl

theorem d0_ne (hok : ∀ i < 4, Fr.ok (cF Fc ks c0f A i)) (i : ℕ) (hi : i < 4) :
    ι (toPoly (d0 Fc ks c0f A i)) ≠ 0 :=
  Fr.ι_ne (Fr.ok_norm (hok i hi))

/-- **The scaled `A` coefficient is a polynomial.** -/
theorem AFr_poly (hok : ∀ i < 4, Fr.ok (cF Fc ks c0f A i)) (c : ℚ) :
    ∃ p : ℚ[X], Fr.val (Fr.smulC c (AFr Fc ks c0f A (mwU Fc ks c0f A))) = ι p := by
  set d := fun i ↦ toPoly (d0 Fc ks c0f A i)
  set n := fun i ↦ toPoly (n0 Fc ks c0f A i)
  refine ⟨C c * ((d 0 ^ 4 * d 1 ^ 3 * d 2 ^ 4 * d 3 ^ 3) * (n 1 * n 3) -
    C (1 / 3) * ((d 0 ^ 4 * d 1 ^ 4 * d 2 ^ 2 * d 3 ^ 4) * (n 2 * n 2))), ?_⟩
  have o := hok
  have ou := ok_mwU (Fc := Fc) (ks := ks) (c0f := c0f) (A := A)
  have h0 := d0_ne hok 0 (by norm_num)
  have h1 := d0_ne hok 1 (by norm_num)
  have h2 := d0_ne hok 2 (by norm_num)
  have h3 := d0_ne hok 3 (by norm_num)
  unfold AFr
  rw [Fr.val_smulC, Fr.val_mul (Fr.ok_mul (Fr.ok_mul ou ou) (Fr.ok_mul ou ou))
      (Fr.ok_sub (Fr.ok_mul (o 1 (by norm_num)) (o 3 (by norm_num)))
        (Fr.ok_smulC _ (Fr.ok_mul (o 2 (by norm_num)) (o 2 (by norm_num))))),
    Fr.val_mul (Fr.ok_mul ou ou) (Fr.ok_mul ou ou), Fr.val_mul ou ou,
    Fr.val_sub (Fr.ok_mul (o 1 (by norm_num)) (o 3 (by norm_num)))
      (Fr.ok_smulC _ (Fr.ok_mul (o 2 (by norm_num)) (o 2 (by norm_num)))),
    Fr.val_mul (o 1 (by norm_num)) (o 3 (by norm_num)), Fr.val_smulC,
    Fr.val_mul (o 2 (by norm_num)) (o 2 (by norm_num)), val_mwU,
    val_cF hok 1 (by norm_num), val_cF hok 2 (by norm_num), val_cF hok 3 (by norm_num)]
  simp only [map_mul, map_sub, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  field_simp
  ring

/-- **The scaled `B` coefficient is a polynomial.** -/
theorem BFr_poly (hok : ∀ i < 4, Fr.ok (cF Fc ks c0f A i)) (c : ℚ) :
    ∃ p : ℚ[X], Fr.val (Fr.smulC c (BFr Fc ks c0f A (mwU Fc ks c0f A))) = ι p := by
  set d := fun i ↦ toPoly (d0 Fc ks c0f A i)
  set n := fun i ↦ toPoly (n0 Fc ks c0f A i)
  refine ⟨C c * ((d 0 ^ 5 * d 1 ^ 6 * d 2 ^ 6 * d 3 ^ 4) * (n 0 * n 3 * n 3) -
    C (1 / 3) * ((d 0 ^ 6 * d 1 ^ 5 * d 2 ^ 5 * d 3 ^ 5) * (n 2 * n 1 * n 3)) +
    C (2 / 27) * ((d 0 ^ 6 * d 1 ^ 6 * d 2 ^ 3 * d 3 ^ 6) * (n 2 * n 2 * n 2))), ?_⟩
  have o := hok
  have ou := ok_mwU (Fc := Fc) (ks := ks) (c0f := c0f) (A := A)
  have h0 := d0_ne hok 0 (by norm_num)
  have h1 := d0_ne hok 1 (by norm_num)
  have h2 := d0_ne hok 2 (by norm_num)
  have h3 := d0_ne hok 3 (by norm_num)
  have o0 := o 0 (by norm_num)
  have o1 := o 1 (by norm_num)
  have o2 := o 2 (by norm_num)
  have o3 := o 3 (by norm_num)
  unfold BFr
  rw [Fr.val_smulC]
  simp (disch := okt) only [Fr.val_mul, Fr.val_add, Fr.val_sub, Fr.val_smulC]
  rw [val_mwU, val_cF hok 0 (by norm_num), val_cF hok 1 (by norm_num),
    val_cF hok 2 (by norm_num), val_cF hok 3 (by norm_num)]
  simp only [map_mul, map_sub, map_add, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  field_simp
  ring

/-- The exact short-model read-off. -/
theorem polyOf_eq_of_val (f : Fr ℚ) (hf : Fr.ok f) (p : ℚ[X]) (hv : Fr.val f = ι p) :
    Fr.val (Fr.ofPoly (polyOf f)) = Fr.val f := by
  rw [Fr.val_ofPoly, show polyOf f = polyOfG f from rfl, polyOfG_spec f hf p hv, hv]

end Curves.MT
