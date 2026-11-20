import RischTragerBronstein.Torsion.UnramPrime

/-!
# The principality test for divisors at unramified points

`principal_iff_test_unram`: over a curve with base field `C`, a divisor `Γ − c ∞ₓ` supported at
points `(α_j, y_{j,k})` of `C`-split unramified fibres is principal iff `princTest` holds for the
expansions of the integral basis along the Hensel branches over `C`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section UT

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

lemma DivGE_congr_lf {J : Type*} (α : J → C) (N : J → ℕ) (hN : ∀ j, 0 < N j)
    {lf lf' : J → List (LaurentSeries K)} (h : lf = lf')
    (hlf : ∀ j, S.F.map (branchSub (N j) (algebraMap C K (α j))) =
      ((lf j).map fun r ↦ X - Polynomial.C r).prod)
    (hlf' : ∀ j, S.F.map (branchSub (N j) (algebraMap C K (α j))) =
      ((lf' j).map fun r ↦ X - Polynomial.C r).prod)
    (Γ : J → LaurentSeries K → ℕ) (c : ℕ) (γ : C⟮S.x⟯⟮S.y⟯) :
    S.DivGE α N hN lf hlf Γ c γ ↔ S.DivGE α N hN lf' hlf' Γ c γ := by
  subst h; rfl

variable [IsAlgClosed K]

/-- **The unramified principality test.** -/
theorem principal_iff_test_unram {B : Fin S.F.natDegree → C[X][X]} {D : C[X]}
    {δ : Fin S.F.natDegree → ℕ} (hB : S.IsIntBasis K B D δ) {J : Type*} [Fintype J]
    (α : J → C) (yΓ : J → Fin S.F.natDegree → C) (Y0 : J → Fin S.F.natDegree → PowerSeries C)
    (hY0c : ∀ j k, PowerSeries.constantCoeff (Y0 j k) = yΓ j k)
    (hsp : ∀ j, S.F.map (branchSub (C := C) (K := C) 1 (α j)) =
      ∏ k, (X - Polynomial.C (ofPowerSeries ℤ C (Y0 j k))))
    (hyinj : ∀ j, Function.Injective (yΓ j)) (ΓC : J → Fin S.F.natDegree → ℕ) (c : ℕ) :
    (∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧ S.DivGEU (K := K) α yΓ ΓC c γ) ↔
      princTest δ c (fun _ : J × Fin S.F.natDegree ↦ 1) (fun q ↦ α q.1)
        (fun q i ↦ basisSer B D 1 (α q.1) (ofPowerSeries ℤ C (Y0 q.1 q.2)) i)
        (fun q ↦ ΓC q.1 q.2) := by
  classical
  set ι := algebraMap C K with hι
  set YK : J → Fin S.F.natDegree → PowerSeries K := fun j k ↦ PowerSeries.map ι (Y0 j k) with hYK
  have hlmap : ∀ j k, lmap ι (ofPowerSeries ℤ C (Y0 j k)) = ofPowerSeries ℤ K (YK j k) :=
    fun j k ↦ lmap_ofPS ι _
  have hspK : ∀ j, S.F.map (branchSub 1 (ι (α j))) =
      ∏ k, (X - Polynomial.C (ofPowerSeries ℤ K (YK j k))) := by
    intro j
    rw [S.split_lmap 1 (α j) _ (hsp j), List.map_ofFn, List.prod_ofFn]
    exact Finset.prod_congr rfl fun k _ ↦ by simp only [Function.comp_apply]; rw [hlmap]
  have hYKc : ∀ j k, PowerSeries.constantCoeff (YK j k) = ι (yΓ j k) := by
    intro j k
    rw [hYK, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hY0c]
  have hYKinj : ∀ j, Function.Injective fun k ↦ ofPowerSeries ℤ K (YK j k) := by
    intro j a b h
    have := congrArg (fun z : LaurentSeries K ↦ z.coeff 0) h
    simp only [coeff_ofPS, le_refl, if_true, Int.toNat_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      hYKc] at this
    exact hyinj j (ι.injective this)
  set ΓK : J → LaurentSeries K → ℕ :=
    fun j ↦ Function.extend (fun k ↦ ofPowerSeries ℤ K (YK j k)) (ΓC j) 0 with hΓK
  have hΓKv : ∀ j k, ΓK j (lmap ι (ofPowerSeries ℤ C (Y0 j k))) = ΓC j k := by
    intro j k
    rw [hlmap]
    exact (hYKinj j).extend_apply _ _ k
  have hlf : (fun j ↦ List.ofFn fun k ↦ lmap ι (ofPowerSeries ℤ C (Y0 j k))) =
      fun j ↦ List.ofFn fun k ↦ ofPowerSeries ℤ K (YK j k) := by
    funext j; congr 1; funext k; exact hlmap j k
  rw [← S.principal_iff_test hB α (fun _ ↦ 1) (fun _ ↦ one_pos) (fun j k ↦ ofPowerSeries ℤ C (Y0 j k))
    hsp ΓC ΓK hΓKv c]
  refine exists_congr fun γ ↦ and_congr_right fun _ ↦ ?_
  rw [S.divGEU_iff α yΓ YK hspK hYKc hyinj ΓC c γ]
  exact (S.DivGE_congr_lf α _ _ hlf _ _ ΓK c γ).symm

end CurveData

end UT

end Curves
