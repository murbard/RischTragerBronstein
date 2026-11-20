import RischTragerBronstein.Curves.SecondKind

/-!
# Pole bounds along branches

`LowerBd z m`: the Laurent series `z` has no coefficient below `Tᵐ` (i.e. `ord z ≥ m`); closure
under sums, products, derivatives (`m ↦ m − 1`), logarithmic derivatives (`≥ −1`).

`liouville_local`: along any branch of a curve, if `f = v′ + ∑ cᵢ uᵢ′/uᵢ` then
* `(f − v′) dx` has at most a simple pole, and
* if `f dx` has a pole of order `≤ e + 1` then `v` has a pole of order `≤ e`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section LowerBd

variable {K : Type*} [Field K]

/-- No coefficient below `Tᵐ`. -/
def LowerBd (z : LaurentSeries K) (m : ℤ) : Prop := ∀ k < m, z.coeff k = 0

lemma LowerBd.mono {z : LaurentSeries K} {m m' : ℤ} (h : LowerBd z m) (hm : m' ≤ m) :
    LowerBd z m' := fun k hk ↦ h k (lt_of_lt_of_le hk hm)

lemma lowerBd_zero (m : ℤ) : LowerBd (0 : LaurentSeries K) m := fun k _ ↦ by simp

lemma LowerBd.add {x y : LaurentSeries K} {m : ℤ} (hx : LowerBd x m) (hy : LowerBd y m) :
    LowerBd (x + y) m := fun k hk ↦ by rw [HahnSeries.coeff_add, hx k hk, hy k hk, add_zero]

lemma LowerBd.neg {x : LaurentSeries K} {m : ℤ} (hx : LowerBd x m) : LowerBd (-x) m :=
  fun k hk ↦ by rw [HahnSeries.coeff_neg, hx k hk, neg_zero]

lemma LowerBd.sub {x y : LaurentSeries K} {m : ℤ} (hx : LowerBd x m) (hy : LowerBd y m) :
    LowerBd (x - y) m := by rw [sub_eq_add_neg]; exact hx.add hy.neg

lemma lowerBd_sum {ι : Type*} (s : Finset ι) (x : ι → LaurentSeries K) {m : ℤ}
    (h : ∀ i ∈ s, LowerBd (x i) m) : LowerBd (∑ i ∈ s, x i) m := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact lowerBd_zero m
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

lemma lowerBd_ofPS (t : PowerSeries K) : LowerBd (ofPowerSeries ℤ K t) 0 := fun k hk ↦
  coeff_ofPS_neg t hk

lemma lowerBd_iff (z : LaurentSeries K) (m : ℤ) :
    LowerBd z m ↔ ∃ t : PowerSeries K, z = single m (1 : K) * ofPowerSeries ℤ K t := by
  constructor
  · intro h
    have h0 : 0 ≤ (single (-m) (1 : K) * z).order := by
      by_cases hz : single (-m) (1 : K) * z = 0
      · rw [hz, HahnSeries.order_zero]
      by_contra hneg
      push Not at hneg
      apply (HahnSeries.coeff_order_eq_zero.not.mpr hz)
      rw [LaurentSeries.coeff_single_mul]
      exact h _ (by omega)
    obtain ⟨t, ht⟩ := exists_ofPS_of_order_nonneg _ h0
    refine ⟨t, ?_⟩
    rw [← ht, ← mul_assoc, single_mul_single, add_neg_cancel, mul_one]
    exact (one_mul z).symm
  · rintro ⟨t, rfl⟩ k hk
    rw [LaurentSeries.coeff_single_mul]
    exact coeff_ofPS_neg t (by omega)

lemma LowerBd.mul {x y : LaurentSeries K} {m m' : ℤ} (hx : LowerBd x m) (hy : LowerBd y m') :
    LowerBd (x * y) (m + m') := by
  obtain ⟨t, rfl⟩ := (lowerBd_iff x m).mp hx
  obtain ⟨t', rfl⟩ := (lowerBd_iff y m').mp hy
  refine (lowerBd_iff _ _).mpr ⟨t * t', ?_⟩
  rw [map_mul, show single (m + m') (1 : K) = single m 1 * single m' 1 by
    rw [single_mul_single, one_mul]]
  ring

lemma lowerBd_single (a : ℤ) (r : K) : LowerBd (single a r) a := fun k hk ↦ by
  rw [coeff_single_of_ne (by omega)]

lemma lowerBd_C (c : K) : LowerBd (HahnSeries.C c : LaurentSeries K) 0 := by
  rw [HahnSeries.C_apply]; exact lowerBd_single 0 c

lemma LowerBd.pow {x : LaurentSeries K} {m : ℤ} (hx : LowerBd x m) (n : ℕ) :
    LowerBd (x ^ n) (n * m) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, ← HahnSeries.C_one]
    exact lowerBd_C 1
  | succ n ih =>
    rw [pow_succ]
    convert ih.mul hx using 1
    push_cast; ring

lemma LowerBd.derivative {z : LaurentSeries K} {m : ℤ} (hz : LowerBd z m) :
    LowerBd (LaurentSeries.derivative K z) (m - 1) := fun k hk ↦ by
  rw [derivative_coeff, hz (k + 1) (by omega), mul_zero]

variable [CharZero K]

/-- The coefficient of `T^{m−1}` in `z′` when `z` starts at `Tᵐ`. -/
lemma derivative_coeff_order (z : LaurentSeries K) (m : ℤ) (hz : LowerBd z m) :
    (LaurentSeries.derivative K z).coeff (m - 1) = (m : K) * z.coeff m := by
  rw [derivative_coeff, sub_add_cancel]

/-- **Logarithmic derivatives have at most a simple pole.** -/
lemma lowerBd_logDeriv (u : LaurentSeries K) (hu : u ≠ 0) :
    LowerBd (LaurentSeries.derivative K u / u) (-1) := by
  have h := res_logDeriv u hu
  set a := u.order
  set F := u.powerSeriesPart
  have hF0 : PowerSeries.constantCoeff F ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, powerSeriesPart_coeff]
    simpa [a] using (not_congr HahnSeries.coeff_order_eq_zero).mpr hu
  have hu' : u = single a (1 : K) * ofPowerSeries ℤ K F :=
    (single_order_mul_powerSeriesPart u).symm
  set Fi := F⁻¹
  have hFFi : F * Fi = 1 := PowerSeries.mul_inv_cancel F hF0
  have hmul : u * (single (-a) (1 : K) * ofPowerSeries ℤ K Fi) = 1 := by
    rw [hu']
    calc single a (1 : K) * ofPowerSeries ℤ K F * (single (-a) (1 : K) * ofPowerSeries ℤ K Fi)
        = (single a (1 : K) * single (-a) (1 : K)) * ofPowerSeries ℤ K (F * Fi) := by
          rw [map_mul]; ring
      _ = 1 := by rw [single_mul_single, add_neg_cancel, mul_one, hFFi]; simp
  have hinv : u⁻¹ = single (-a) (1 : K) * ofPowerSeries ℤ K Fi :=
    (eq_inv_of_mul_eq_one_right hmul).symm
  rw [div_eq_mul_inv, hinv]
  conv_lhs => rw [hu']
  rw [derivative_single_mul_ofPS]
  have e1 : (single a (1 : K) * ofPowerSeries ℤ K (PowerSeries.derivative F) +
      (a : K) • (single (a - 1) (1 : K) * ofPowerSeries ℤ K F)) *
      (single (-a) (1 : K) * ofPowerSeries ℤ K Fi) =
      ofPowerSeries ℤ K (PowerSeries.derivative F * Fi) +
        (a : K) • single (-1) (1 : K) := by
    have s1 : single a (1 : K) * single (-a) 1 = 1 := by
      rw [single_mul_single, add_neg_cancel, one_mul]; rfl
    have s2 : single (a - 1) (1 : K) * single (-a) 1 = single (-1) 1 := by
      rw [single_mul_single, one_mul]; ring_nf
    have hP : ofPowerSeries ℤ K F * ofPowerSeries ℤ K Fi = 1 := by rw [← map_mul, hFFi, map_one]
    have hC : ∀ z : K⸨X⸩, (a : K) • z = HahnSeries.C (a : K) * z := fun z ↦
      (HahnSeries.C_mul_eq_smul).symm
    rw [hC, hC, map_mul]
    linear_combination (ofPowerSeries ℤ K (PowerSeries.derivative F) * ofPowerSeries ℤ K Fi) * s1 +
      (HahnSeries.C (a : K) * ofPowerSeries ℤ K F * ofPowerSeries ℤ K Fi) * s2 +
      (HahnSeries.C (a : K) * single (-1) (1 : K)) * hP
  rw [e1]
  refine ((lowerBd_ofPS _).mono (by norm_num)).add ?_
  intro k hk
  rw [HahnSeries.coeff_smul, coeff_single_of_ne (by omega), smul_zero]

end LowerBd

section Local

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

variable (Xh : LaurentSeries K) (hX : LaurentSeries.derivation Xh ≠ 0)
  (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (hgX : ∀ P, g P = substHom Xh P)

include hX hgX in
/-- `φ(f) dX̂/dT = (φ v)′ + ∑ cᵢ (φ uᵢ)′/φ uᵢ` along a branch. -/
lemma expand_liouville (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (Y : LaurentSeries K)
    (hY : (S.F.map g).eval Y = 0) {ι : Type*} (s : Finset ι) (c : ι → C)
    (u : ι → L) (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, algebraMap C L (c i) * ((u i)′ / u i)) :
    S.embG g hg Y hY ⟨f, hf⟩ * LaurentSeries.derivation Xh =
      LaurentSeries.derivation (S.embG g hg Y hY ⟨v, hv⟩) + ∑ i ∈ s,
        HahnSeries.C (algebraMap C K (c i)) *
          (LaurentSeries.derivation (S.embG g hg Y hY ⟨u i, hu i⟩) /
            S.embG g hg Y hY ⟨u i, hu i⟩) := by
  set T := C⟮S.x⟯⟮S.y⟯
  set φ := S.embG g hg Y hY
  have hdc := S.derivClosedXY hC hx
  have hT : (⟨f, hf⟩ : T) = ⟨v′, hdc v hv⟩ + ∑ i ∈ s,
      (⟨algebraMap C L (c i), S.const_mem (c i)⟩ : T) *
        ((⟨(u i)′, hdc _ (hu i)⟩ : T) / ⟨u i, hu i⟩) :=
    Subtype.ext (by simp [heq])
  have hcst : ∀ i, φ ⟨algebraMap C L (c i), S.const_mem (c i)⟩ =
      HahnSeries.C (algebraMap C K (c i)) := fun i ↦ by
    letI := algebraAdjoinSimple (F := C) S.x
    have e : (⟨algebraMap C L (c i), S.const_mem (c i)⟩ : T) =
        algebraMap C⟮S.x⟯ T (algebraMap C[X] C⟮S.x⟯ (Polynomial.C (c i))) :=
      Subtype.ext (by
        show algebraMap C L (c i) = ((algebraMap C[X] C⟮S.x⟯ (Polynomial.C (c i)) : C⟮S.x⟯) : L)
        rw [algebraMap_adjoinSimple, aeval_C])
    rw [e, S.embG_algebraMap, S.embXG_algebraMap, hgX, substHom_apply, Polynomial.map_C, aeval_C,
      HahnSeries.algebraMap_apply']
    exact ofPowerSeries_C _
  have hδ : ∀ F : LaurentSeries K, SuperData.deltaX Xh F * LaurentSeries.derivation Xh =
      LaurentSeries.derivation F := fun F ↦ by
    rw [SuperData.deltaX_apply]; field_simp
  rw [hT, map_add, map_sum, S.embG_derivG Xh hX g hg hgX hC hx Y hY v hv, add_mul, hδ,
    Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_div₀, S.embG_derivG Xh hX g hg hgX hC hx Y hY (u i) (hu i), hcst,
    ← hδ (S.embG g hg Y hY ⟨u i, hu i⟩)]
  ring

include hX hgX in
/-- **Local pole bounds for a Liouville form.** -/
theorem liouville_local (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (Y : LaurentSeries K)
    (hY : (S.F.map g).eval Y = 0) {ι : Type*} (s : Finset ι) (c : ι → C)
    (u : ι → L) (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0)
    (v f : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, algebraMap C L (c i) * ((u i)′ / u i)) :
    LowerBd (S.embG g hg Y hY ⟨f, hf⟩ * LaurentSeries.derivation Xh -
        LaurentSeries.derivation (S.embG g hg Y hY ⟨v, hv⟩)) (-1) ∧
      ∀ e : ℕ, LowerBd (S.embG g hg Y hY ⟨f, hf⟩ * LaurentSeries.derivation Xh) (-(e + 1)) →
        LowerBd (S.embG g hg Y hY ⟨v, hv⟩) (-e) := by
  set φ := S.embG g hg Y hY
  have hexp := S.expand_liouville Xh hX g hg hgX hC hx Y hY s c u hu hu0 v f hv hf heq
  have hlog : LowerBd (∑ i ∈ s, HahnSeries.C (algebraMap C K (c i)) *
      (LaurentSeries.derivation (φ ⟨u i, hu i⟩) / φ ⟨u i, hu i⟩)) (-1) := by
    refine lowerBd_sum _ _ fun i _ ↦ ?_
    have h0 : φ ⟨u i, hu i⟩ ≠ 0 :=
      (map_ne_zero_iff φ φ.injective).mpr (fun h ↦ hu0 i (congrArg Subtype.val h))
    have := (lowerBd_C (algebraMap C K (c i))).mul (lowerBd_logDeriv _ h0)
    rwa [zero_add] at this
  refine ⟨by rw [hexp, add_sub_cancel_left]; exact hlog, fun e he ↦ ?_⟩
  intro k hk
  by_contra hne
  set z := φ ⟨v, hv⟩
  have hz0 : z ≠ 0 := fun h ↦ hne (by rw [h, HahnSeries.coeff_zero])
  have hord : z.order ≤ k := HahnSeries.order_le_of_coeff_ne_zero hne
  have hlz : LowerBd z z.order := fun j hj ↦ HahnSeries.coeff_eq_zero_of_lt_order hj
  have hc0 : z.coeff z.order ≠ 0 := HahnSeries.coeff_order_eq_zero.not.mpr hz0
  have h1 := he (z.order - 1) (by omega)
  rw [hexp, HahnSeries.coeff_add, LaurentSeries.derivation_apply,
    derivative_coeff_order z _ hlz, hlog _ (by omega), add_zero] at h1
  have hzo : (z.order : K) ≠ 0 := by exact_mod_cast (show z.order ≠ 0 by omega)
  exact (mul_ne_zero hzo hc0) h1

end CurveData

end Local

end Curves
