import RischTragerBronstein.Curves.Ansatz

/-!
# Abel's direction on an arbitrary curve

`curve_abel`: if `f = v′ + ∑ cᵢ uᵢ′/uᵢ` on `C⟮x⟯⟮y⟯` and `Λ : K → ℚ` is `ℚ`-linear, then for some
`m > 0` there is `w ≠ 0` whose order along *every* branch is `m · Λ(res f dx)` (the residue of the
expansion of `f dx` along that branch): the `Λ`-component of the residue divisor is torsion in
the divisor class group. The witness is `∏ uᵢ^{M Λ(cᵢ)}`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries Differential.SuperData

section Abel

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K]

omit [CharZero K] [Algebra C K] in
lemma order_inv_laurent (z : LaurentSeries K) (hz : z ≠ 0) : z⁻¹.order = -z.order := by
  have h := HahnSeries.order_mul hz (inv_ne_zero hz)
  rw [mul_inv_cancel₀ hz, HahnSeries.order_one] at h
  omega

namespace CurveData

variable (S : CurveData C L)

/-- The order of a product of integer powers along an embedding. -/
lemma order_prod_zpow (φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K) {ι : Type*} (s : Finset ι)
    (u : ι → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i ∈ s, u i ≠ 0) (e : ι → ℤ) :
    (φ (∏ i ∈ s, u i ^ e i)).order = ∑ i ∈ s, e i * (φ (u i)).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, map_mul, map_zpow₀]
    have hu0 : φ (u j) ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr (hu j (Finset.mem_insert_self _ _))
    have hp0 : φ (∏ i ∈ s, u i ^ e i) ≠ 0 := by
      rw [map_prod]
      exact Finset.prod_ne_zero_iff.mpr fun i hi ↦ by
        rw [map_zpow₀]
        exact zpow_ne_zero _ ((map_ne_zero_iff φ φ.injective).mpr
          (hu i (Finset.mem_insert_of_mem hi)))
    rw [HahnSeries.order_mul (zpow_ne_zero _ hu0) hp0, ih fun i hi ↦ hu i (Finset.mem_insert_of_mem hi)]
    congr 1
    rcases Int.eq_nat_or_neg (e j) with ⟨k, hk | hk⟩
    · rw [hk, zpow_natCast, HahnSeries.order_pow]; push_cast; ring
    · rw [hk, zpow_neg, zpow_natCast, order_inv_laurent _ (pow_ne_zero _ hu0),
        HahnSeries.order_pow]
      push_cast; ring

/-- **Abel's direction**: the `Λ`-component of the residue divisor of a Liouville form is torsion,
witnessed along every branch. -/
theorem curve_abel (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (f v : L) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (hv : v ∈ C⟮S.x⟯⟮S.y⟯) {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → C) (u : ι → L)
    (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0)
    (heq : f = v′ + ∑ i ∈ s, algebraMap C L (c i) * ((u i)′ / u i)) (Λ : K →ₗ[ℚ] ℚ) :
    ∃ m : ℕ, 0 < m ∧ ∃ w : C⟮S.x⟯⟮S.y⟯, w ≠ 0 ∧
      ∀ (Xh : LaurentSeries K) (hX : LaurentSeries.derivation Xh ≠ 0)
        (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
        (hgX : ∀ P, g P = substHom Xh P) (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0),
        ((S.embG g hg Y hY w).order : ℚ) =
          m * Λ (LaurentSeries.res (S.embG g hg Y hY ⟨f, hf⟩ * LaurentSeries.derivation Xh)) := by
  classical
  set q : ι → ℚ := fun i ↦ Λ (algebraMap C K (c i)) with hq
  set M : ℕ := ∏ i ∈ s, (q i).den with hM
  have hMpos : 0 < M := Finset.prod_pos fun i _ ↦ (q i).den_pos
  have he : ∀ i ∈ s, ∃ k : ℤ, q i * M = k := fun i hi ↦
    exists_int_of_den_dvd (q i) M (Finset.dvd_prod_of_mem _ hi)
  choose! e he' using he
  refine ⟨M, hMpos, ∏ i ∈ s, (⟨u i, hu i⟩ : C⟮S.x⟯⟮S.y⟯) ^ e i,
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ fun h ↦ hu0 i (congrArg Subtype.val h),
    fun Xh hX g hg hgX Y hY ↦ ?_⟩
  rw [S.order_prod_zpow _ s _ (fun i _ h ↦ hu0 i (congrArg Subtype.val h)),
    S.res_liouvilleG Xh hX g hg hgX hC hx Y hY s c u hu hu0 v f hv hf heq, map_sum,
    Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hΛ : Λ (algebraMap C K (c i) * ((S.embG g hg Y hY ⟨u i, hu i⟩).order : K)) =
      ((S.embG g hg Y hY ⟨u i, hu i⟩).order : ℚ) * q i := by
    rw [mul_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
  rw [hΛ, ← he' i hi]
  ring

end CurveData

end Abel

end Curves
