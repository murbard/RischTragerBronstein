import RischTragerBronstein.Mixed.PolyOfSpec

/-!
# The level-`m + 1` search data for non-constant curves (part 1: the short model)

The search scales the short model by `uF = mwUS` (the product of the reduced denominators of
`c₀, …, c₃`). **`AFrS_poly`, `BFrS_poly`**: the scaled coefficients `s² u⁴ (c₁c₃ − c₂²/3)` and
`s³ u⁶ (c₀c₃² − c₂c₁c₃/3 + 2c₂³/27)` have polynomial values, so by `polyOfG_spec` the read-off
`Ac`, `Bc` of `kxMWSearchS` are exact (`Ac_spec`, `Bc_spec`) — for arbitrary (non-constant)
coefficients.
-/

open Polynomial

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
variable (m : ℕ) (A : GPoly (LC (m + 1)))

local notation "ι" => algebraMap (KF Fc m)[X] (RatFunc (KF Fc m))

/-- The reduced denominator of `cᵢ`. -/
abbrev dS (i : ℕ) : CPoly (KF Fc m) := (Fr.norm (cFS Fc ks m A i)).2
/-- The reduced numerator of `cᵢ`. -/
abbrev nS (i : ℕ) : CPoly (KF Fc m) := (Fr.norm (cFS Fc ks m A i)).1

variable {Fc ks m A}

theorem mwUS_eq : mwUS Fc ks m A = Fr.mul (Fr.ofPoly (dS Fc ks m A 0)) (Fr.mul (Fr.ofPoly (dS Fc ks m A 1))
    (Fr.mul (Fr.ofPoly (dS Fc ks m A 2)) (Fr.mul (Fr.ofPoly (dS Fc ks m A 3)) (Fr.ofPoly [1])))) := rfl

theorem val_mwUS : Fr.val (mwUS Fc ks m A) = ι (toPoly (dS Fc ks m A 0)) * (ι (toPoly (dS Fc ks m A 1)) *
    (ι (toPoly (dS Fc ks m A 2)) * (ι (toPoly (dS Fc ks m A 3)) * 1))) := by
  rw [mwUS_eq]
  simp only [Fr.val_mul (Fr.ok_ofPoly _) (Fr.ok_mul (Fr.ok_ofPoly _) (Fr.ok_mul (Fr.ok_ofPoly _)
    (Fr.ok_mul (Fr.ok_ofPoly _) (Fr.ok_ofPoly _)))), Fr.val_mul (Fr.ok_ofPoly _) (Fr.ok_mul
    (Fr.ok_ofPoly _) (Fr.ok_mul (Fr.ok_ofPoly _) (Fr.ok_ofPoly _))), Fr.val_mul (Fr.ok_ofPoly _)
    (Fr.ok_mul (Fr.ok_ofPoly _) (Fr.ok_ofPoly _)), Fr.val_mul (Fr.ok_ofPoly _) (Fr.ok_ofPoly _),
    Fr.val_ofPoly]
  simp [CPoly.toPoly]

theorem ok_mwUS : Fr.ok (mwUS Fc ks m A) := by
  rw [mwUS_eq]
  exact Fr.ok_mul (Fr.ok_ofPoly _) (Fr.ok_mul (Fr.ok_ofPoly _) (Fr.ok_mul (Fr.ok_ofPoly _)
    (Fr.ok_mul (Fr.ok_ofPoly _) (Fr.ok_ofPoly _))))

theorem val_cFS (hok : ∀ i < 4, Fr.ok (cFS Fc ks m A i)) (i : ℕ) (hi : i < 4) :
    Fr.val (cFS Fc ks m A i) = ι (toPoly (nS Fc ks m A i)) / ι (toPoly (dS Fc ks m A i)) := by
  rw [← Fr.val_norm (hok i hi)]; rfl

theorem dS_ne (hok : ∀ i < 4, Fr.ok (cFS Fc ks m A i)) (i : ℕ) (hi : i < 4) :
    ι (toPoly (dS Fc ks m A i)) ≠ 0 :=
  Fr.ι_ne (Fr.ok_norm (hok i hi))

/-- **The scaled `A` coefficient is a polynomial.** -/
theorem AFrS_poly (hok : ∀ i < 4, Fr.ok (cFS Fc ks m A i)) (c : KF Fc m) :
    ∃ p : (KF Fc m)[X], Fr.val (Fr.smulC c (AFrS Fc ks m A (mwUS Fc ks m A))) = ι p := by
  set d := fun i ↦ toPoly (dS Fc ks m A i)
  set n := fun i ↦ toPoly (nS Fc ks m A i)
  refine ⟨C c * ((d 0 ^ 4 * d 1 ^ 3 * d 2 ^ 4 * d 3 ^ 3) * (n 1 * n 3) -
    C (1 / 3) * ((d 0 ^ 4 * d 1 ^ 4 * d 2 ^ 2 * d 3 ^ 4) * (n 2 * n 2))), ?_⟩
  have o := hok
  have ou := ok_mwUS (Fc := Fc) (ks := ks) (m := m) (A := A)
  have h0 := dS_ne hok 0 (by norm_num)
  have h1 := dS_ne hok 1 (by norm_num)
  have h2 := dS_ne hok 2 (by norm_num)
  have h3 := dS_ne hok 3 (by norm_num)
  unfold AFrS
  rw [Fr.val_smulC, Fr.val_mul (Fr.ok_mul (Fr.ok_mul ou ou) (Fr.ok_mul ou ou))
      (Fr.ok_sub (Fr.ok_mul (o 1 (by norm_num)) (o 3 (by norm_num)))
        (Fr.ok_smulC _ (Fr.ok_mul (o 2 (by norm_num)) (o 2 (by norm_num))))),
    Fr.val_mul (Fr.ok_mul ou ou) (Fr.ok_mul ou ou), Fr.val_mul ou ou,
    Fr.val_sub (Fr.ok_mul (o 1 (by norm_num)) (o 3 (by norm_num)))
      (Fr.ok_smulC _ (Fr.ok_mul (o 2 (by norm_num)) (o 2 (by norm_num)))),
    Fr.val_mul (o 1 (by norm_num)) (o 3 (by norm_num)), Fr.val_smulC,
    Fr.val_mul (o 2 (by norm_num)) (o 2 (by norm_num)), val_mwUS,
    val_cFS hok 1 (by norm_num), val_cFS hok 2 (by norm_num), val_cFS hok 3 (by norm_num)]
  simp only [map_mul, map_sub, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  field_simp
  ring

/-- **The scaled `B` coefficient is a polynomial.** -/
theorem BFrS_poly (hok : ∀ i < 4, Fr.ok (cFS Fc ks m A i)) (c : KF Fc m) :
    ∃ p : (KF Fc m)[X], Fr.val (Fr.smulC c (BFrS Fc ks m A (mwUS Fc ks m A))) = ι p := by
  set d := fun i ↦ toPoly (dS Fc ks m A i)
  set n := fun i ↦ toPoly (nS Fc ks m A i)
  refine ⟨C c * ((d 0 ^ 5 * d 1 ^ 6 * d 2 ^ 6 * d 3 ^ 4) * (n 0 * n 3 * n 3) -
    C (1 / 3) * ((d 0 ^ 6 * d 1 ^ 5 * d 2 ^ 5 * d 3 ^ 5) * (n 2 * n 1 * n 3)) +
    C (2 / 27) * ((d 0 ^ 6 * d 1 ^ 6 * d 2 ^ 3 * d 3 ^ 6) * (n 2 * n 2 * n 2))), ?_⟩
  have o := hok
  have ou := ok_mwUS (Fc := Fc) (ks := ks) (m := m) (A := A)
  have h0 := dS_ne hok 0 (by norm_num)
  have h1 := dS_ne hok 1 (by norm_num)
  have h2 := dS_ne hok 2 (by norm_num)
  have h3 := dS_ne hok 3 (by norm_num)
  have o0 := o 0 (by norm_num)
  have o1 := o 1 (by norm_num)
  have o2 := o 2 (by norm_num)
  have o3 := o 3 (by norm_num)
  unfold BFrS
  rw [Fr.val_smulC]
  simp (disch := okt) only [Fr.val_mul, Fr.val_add, Fr.val_sub, Fr.val_smulC]
  rw [val_mwUS, val_cFS hok 0 (by norm_num), val_cFS hok 1 (by norm_num),
    val_cFS hok 2 (by norm_num), val_cFS hok 3 (by norm_num)]
  simp only [map_mul, map_sub, map_add, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  field_simp
  ring

end Curves.MT

