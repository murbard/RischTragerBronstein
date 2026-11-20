import RischTragerBronstein.Torsion.PlaceExist2
import RischTragerBronstein.Curves.Reparam

/-!
# Places above a point exist (3): residues along a place

* `res_rot_branch`: the substitution `T ↦ ζT` (`ζᴺ = 1`) does not change residues at `x = a + Tᴺ`;
* **`res_conj_place`**: along the conjugate `rot ζ (lsub s ρ)` of a place series `ρ` (at
  `x = a + tᵉ`, `N = s e`), the residue of `f dx` is `s` times the residue along `ρ`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Res

variable {K : Type*} [Field K] [CharZero K]

lemma res_rot_branch (ζ : K) (hζ : ζ ≠ 0) (N : ℕ) (hN : 0 < N) (hζN : ζ ^ N = 1) (a : K)
    (u : LaurentSeries K) :
    LaurentSeries.res (rot ζ hζ u * LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) 1)) =
      LaurentSeries.res (u * LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) 1)) := by
  rw [SuperData.derivation_branchX N hN a, LaurentSeries.res, LaurentSeries.res,
    HahnSeries.coeff_mul_single, HahnSeries.coeff_mul_single, rot_coeff]
  have : ζ ^ ((-1 : ℤ) - ((N : ℤ) - 1)) = 1 := by
    rw [show (-1 : ℤ) - ((N : ℤ) - 1) = -(N : ℤ) by ring, zpow_neg, zpow_natCast, hζN, inv_one]
  rw [this, one_mul]

end Res

section Curve

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K] [CharZero K]

namespace CurveData

variable (S : CurveData C L)

/-- **Residues along a conjugate of a place series.** -/
theorem res_conj_place (ζ : K) (hζ : ζ ≠ 0) (s e : ℕ) (hs : 0 < s) (he : 0 < e)
    (hζN : ζ ^ (s * e) = 1) (a : K) (ρ : LaurentSeries K)
    (hρ : (S.F.map (branchSub e a)).eval ρ = 0)
    (hρ' : (S.F.map (branchSub (s * e) a)).eval (lsub s hs ρ) = 0)
    (hρ'' : (S.F.map (branchSub (s * e) a)).eval (rot ζ hζ (lsub s hs ρ)) = 0)
    (f : C⟮S.x⟯⟮S.y⟯) :
    LaurentSeries.res (S.embG (branchSub (s * e) a) (branchSub_injective _ (Nat.mul_pos hs he) a)
        (rot ζ hζ (lsub s hs ρ)) hρ'' f *
        LaurentSeries.derivation (HahnSeries.C a + single ((s * e : ℕ) : ℤ) 1)) =
      (s : K) * LaurentSeries.res (S.embG (branchSub e a) (branchSub_injective e he a) ρ hρ f *
        LaurentSeries.derivation (HahnSeries.C a + single (e : ℤ) 1)) := by
  have h1 := S.embG_rot ζ hζ (s * e) (Nat.mul_pos hs he) hζN a (lsub s hs ρ) hρ' f
  have h2 := S.embG_lsub_fin s hs e he a ρ hρ hρ' f
  rw [h1, res_rot_branch ζ hζ (s * e) (Nat.mul_pos hs he) hζN a, h2]
  have hX : HahnSeries.C a + single ((s * e : ℕ) : ℤ) (1 : K) =
      lsub s hs (HahnSeries.C a + single (e : ℤ) (1 : K)) := by
    rw [map_add, lsub_C, lsub_single]
    congr 2
  rw [hX, res_lsub]


end CurveData

end Curve

end Curves
