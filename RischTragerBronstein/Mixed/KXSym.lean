import RischTragerBronstein.Mixed.KXPrep

/-!
# The two points over `x = 0` when `√p(0)` is not in `C`

`S : SuperData C L` with `n = 2`, `p(0) = β₀² ≠ 0`. If `β₀ ∉ C`, every nonzero `z ∈ C(x, y)` has the
same order at `(0, β₀)` and `(0, −β₀)` (`ordAt_pm`): writing `z = a₀ + a₁ y`, the expansions are
`A₀ ± A₁ Y` with `A₀, A₁` the expansions of `a₀, a₁ ∈ C(x)` at `0` (whose leading coefficients lie in
`C`) and `Y(0) = β₀`; no cancellation can occur, so both orders are `min(ord A₀, ord A₁)`.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries Classical

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L)

omit [CharZero C] [CharZero L] [CharZero K] [Differential K] [IsAlgClosed K] in
/-- The coefficients of the expansion of a polynomial at `0` lie in `C`. -/
lemma coeff_shiftHom_zero (P : C[X]) (k : ℤ) :
    (shiftHom (C := C) (0 : K) P).coeff k ∈ Set.range (algebraMap C K) := by
  rw [shiftHom_apply, PowerSeries.coeff_coe]
  split_ifs
  · exact ⟨0, map_zero _⟩
  · rw [Polynomial.coeff_coe, map_zero, add_zero, comp_X, coeff_map]
    exact ⟨_, rfl⟩

omit [CharZero C] [CharZero L] [Differential K] [IsAlgClosed K] in
/-- **The leading coefficient of the expansion of `a ∈ C(x)` at `0` lies in `C`.** -/
lemma leadingCoeff_embX (a : C⟮S.x⟯) :
    (embX S.x S.htr (0 : K) a).leadingCoeff ∈ Set.range (algebraMap C K) := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  obtain ⟨P, Q, hQ, rfl⟩ := IsFractionRing.div_surjective (A := C[X]) a
  have hQ0 : Q ≠ 0 := nonZeroDivisors.ne_zero hQ
  rw [map_div₀, S.embX_algebraMap, S.embX_algebraMap]
  set A := shiftHom (C := C) (0 : K) P
  set B := shiftHom (C := C) (0 : K) Q
  have hB0 : B ≠ 0 := (map_ne_zero_iff _ (shiftHom_injective 0)).mpr hQ0
  have hlc : ∀ F : LaurentSeries K, (∀ k, F.coeff k ∈ Set.range (algebraMap C K)) →
      F.leadingCoeff ∈ Set.range (algebraMap C K) := fun F hF ↦ by
    by_cases h : F = 0
    · rw [h, HahnSeries.leadingCoeff_zero]; exact ⟨0, map_zero _⟩
    · rw [HahnSeries.leadingCoeff_eq]; exact hF _
  obtain ⟨u, hu⟩ := hlc A (coeff_shiftHom_zero P)
  obtain ⟨v, hv⟩ := hlc B (coeff_shiftHom_zero Q)
  have hvB : B.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr hB0
  have hmul : (A / B).leadingCoeff * B.leadingCoeff = A.leadingCoeff := by
    rw [← HahnSeries.leadingCoeff_mul, div_mul_cancel₀ _ hB0]
  refine ⟨u / v, ?_⟩
  rw [map_div₀, hu, hv, div_eq_iff hvB, hmul]

omit [CharZero C] [CharZero L] [IsAlgClosed K] in
/-- **No cancellation**: `ord (A₀ + A₁ Y) = min (ord A₀) (ord A₁)` when the leading coefficients of
`A₀, A₁` lie in `C`, `Y` has order `0` and `Y(0) ∉ C`. -/
lemma order_no_cancel (A0 A1 Y : LaurentSeries K) (h0 : A0 ≠ 0) (h1 : A1 ≠ 0)
    (hl0 : A0.leadingCoeff ∈ Set.range (algebraMap C K))
    (hl1 : A1.leadingCoeff ∈ Set.range (algebraMap C K))
    (hY : ∀ k < 0, Y.coeff k = 0) (hY0 : ∀ c : C, algebraMap C K c * Y.coeff 0 ∉
      Set.range (algebraMap C K) ∨ c = 0) :
    (A0 + A1 * Y).order = min A0.order A1.order := by
  have hYc : Y.coeff 0 ≠ 0 := fun h ↦ by
    rcases hY0 1 with h' | h'
    · apply h'; rw [h, mul_zero]; exact ⟨0, map_zero _⟩
    · exact one_ne_zero h'
  have hYne : Y ≠ 0 := fun h ↦ hYc (by rw [h]; rfl)
  have hYo : Y.order = 0 := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hYc) ?_
    by_contra hlt; push Not at hlt
    exact (not_congr HahnSeries.coeff_order_eq_zero).mpr hYne (hY _ hlt)
  set B := A1 * Y with hB
  have hB0 : B ≠ 0 := mul_ne_zero h1 hYne
  have hBo : B.order = A1.order := by rw [hB, HahnSeries.order_mul h1 hYne, hYo, add_zero]
  have hBc : B.coeff A1.order = A1.leadingCoeff * Y.coeff 0 := by
    have := coeff_mul_add (x := A1) (y := Y) (a := A1.order) (b := 0) (coeff_lt_order_eq_zero A1) hY
    rw [add_zero] at this
    rw [hB, this, HahnSeries.leadingCoeff_eq]
  set k := min A0.order A1.order
  have hbelow : ∀ j < k, (A0 + B).coeff j = 0 := fun j hj ↦ by
    rw [HahnSeries.coeff_add, HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hj (min_le_left _ _)),
      HahnSeries.coeff_eq_zero_of_lt_order (by rw [hBo]; exact lt_of_lt_of_le hj (min_le_right _ _)),
      add_zero]
  have hk : (A0 + B).coeff k ≠ 0 := by
    rw [HahnSeries.coeff_add]
    rcases lt_trichotomy A0.order A1.order with hlt | heq | hgt
    · have hkk : k = A0.order := min_eq_left hlt.le
      rw [hkk, HahnSeries.coeff_eq_zero_of_lt_order (x := B) (by rw [hBo]; exact hlt), add_zero]
      exact (not_congr HahnSeries.coeff_order_eq_zero).mpr h0
    · have hkk : k = A0.order := by simp [k, heq]
      rw [hkk, heq, hBc, ← heq, ← HahnSeries.leadingCoeff_eq]
      obtain ⟨u, hu⟩ := hl0
      obtain ⟨v, hv⟩ := hl1
      intro hsum
      have hv0 : v ≠ 0 := fun h ↦ HahnSeries.leadingCoeff_ne_zero.mpr h1 (by rw [← hv, h, map_zero])
      rcases hY0 v with h' | h'
      · apply h'; rw [hv]; exact ⟨-u, by rw [map_neg, hu]; linear_combination -hsum⟩
      · exact hv0 h'
    · have hkk : k = A1.order := min_eq_right hgt.le
      rw [hkk, HahnSeries.coeff_eq_zero_of_lt_order hgt, zero_add, hBc]
      exact mul_ne_zero (HahnSeries.leadingCoeff_ne_zero.mpr h1) hYc
  have hne : A0 + B ≠ 0 := fun h ↦ hk (by rw [h]; rfl)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hk) ?_
  by_contra hlt; push Not at hlt
  exact (not_congr HahnSeries.coeff_order_eq_zero).mpr hne (hbelow _ hlt)

lemma sum_two {M : Type*} [AddCommMonoid M] (hn2 : S.n = 2) (f : Fin S.n → M) :
    ∑ i, f i = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ := by
  rw [Fintype.sum_equiv (finCongr hn2) f (fun j ↦ f ((finCongr hn2).symm j)) (fun i ↦ by simp),
    Fin.sum_univ_two]
  rfl

/-- **Equal orders over `x = 0`** when `√p(0) ∉ C`. -/
theorem ordAt_pm (hn2 : S.n = 2) (β₀ : K) (hβ₀ : β₀ ≠ 0)
    (hv : β₀ ^ S.n = (S.p.map (algebraMap C K)).eval 0) (hns : ∀ c : C, algebraMap C K c ≠ β₀)
    (z : C⟮S.x⟯⟮S.y⟯) (hz : z ≠ 0) : S.ordAt K z 0 β₀ = S.ordAt K z 0 (-β₀) := by
  obtain ⟨a, ha⟩ := S.power_repr z
  rw [S.sum_two hn2] at ha
  simp only [pow_zero, mul_one, pow_one] at ha
  set a0 := a ⟨0, by omega⟩
  set a1 := a ⟨1, by omega⟩
  have hvM : (-β₀) ^ S.n = (S.p.map (algebraMap C K)).eval 0 := by
    rw [hn2, neg_sq, ← hn2]; exact hv
  have hnb : -β₀ ≠ 0 := neg_ne_zero.mpr hβ₀
  -- the expansion at `(0, β)`
  have hexp : ∀ (β : K) (hβ : β ≠ 0) (hβv : β ^ S.n = (S.p.map (algebraMap C K)).eval 0),
      S.embXY 0 β hβ hβv z = embX S.x S.htr (0 : K) a0 + embX S.x S.htr (0 : K) a1 *
        ofPowerSeries ℤ K (branchY S.n S.hn (S.hnK K) S.p 0 β hβ hβv) := fun β hβ hβv ↦ by
    rw [ha, map_add, map_mul, S.embXY_algebraMap, S.embXY_algebraMap, S.embXY_gen]
  have hYn : ∀ (β : K) (hβ : β ≠ 0) (hβv : β ^ S.n = (S.p.map (algebraMap C K)).eval 0),
      ∀ k < 0, (ofPowerSeries ℤ K (branchY S.n S.hn (S.hnK K) S.p 0 β hβ hβv)).coeff k = 0 :=
    fun β hβ hβv k hk ↦ by rw [PowerSeries.coeff_coe, ite_eq_left hk]
  have hY0 : ∀ (β : K) (hβ : β ≠ 0) (hβv : β ^ S.n = (S.p.map (algebraMap C K)).eval 0),
      (ofPowerSeries ℤ K (branchY S.n S.hn (S.hnK K) S.p 0 β hβ hβv)).coeff 0 = β :=
    fun β hβ hβv ↦ by
      rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, coeff_coe_powerSeries,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, branchY_const]
  have hns' : ∀ β, (β = β₀ ∨ β = -β₀) → ∀ c : C, algebraMap C K c * β ∉ Set.range (algebraMap C K) ∨
      c = 0 := by
    intro β hβ c
    by_cases hc : c = 0
    · exact Or.inr hc
    · left
      rintro ⟨d, hd⟩
      have hcK : algebraMap C K c ≠ 0 := (_root_.map_ne_zero _).mpr hc
      rcases hβ with rfl | rfl
      · apply hns (d / c)
        rw [map_div₀, hd]; field_simp
      · apply hns (-(d / c))
        rw [map_neg, map_div₀, hd]; field_simp
  have hord : ∀ (β : K) (hβ : β ≠ 0) (hβv : β ^ S.n = (S.p.map (algebraMap C K)).eval 0),
      (β = β₀ ∨ β = -β₀) → S.ordAt K z 0 β =
        if a1 = 0 then (embX S.x S.htr (0 : K) a0).order
        else if a0 = 0 then (embX S.x S.htr (0 : K) a1).order
        else min (embX S.x S.htr (0 : K) a0).order (embX S.x S.htr (0 : K) a1).order := by
    intro β hβ hβv hββ
    rw [S.ordAt_nb _ 0 β hβ hβv, hexp β hβ hβv]
    set Y := ofPowerSeries ℤ K (branchY S.n S.hn (S.hnK K) S.p 0 β hβ hβv)
    have hYne : Y ≠ 0 := fun h ↦ hβ (by rw [← hY0 β hβ hβv]; show Y.coeff 0 = 0; rw [h]; rfl)
    have hYo : Y.order = 0 := by
      refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [hY0 β hβ hβv]; exact hβ)) ?_
      by_contra hlt; push Not at hlt
      exact (not_congr HahnSeries.coeff_order_eq_zero).mpr hYne (hYn β hβ hβv _ hlt)
    split_ifs with h1 h0
    · rw [h1, map_zero, zero_mul, add_zero]
    · rw [h0, map_zero, zero_add, HahnSeries.order_mul
        ((map_ne_zero_iff _ (embX S.x S.htr (0 : K)).injective).mpr h1) hYne, hYo, add_zero]
    · exact order_no_cancel _ _ Y ((map_ne_zero_iff _ (embX S.x S.htr (0 : K)).injective).mpr h0)
        ((map_ne_zero_iff _ (embX S.x S.htr (0 : K)).injective).mpr h1) (S.leadingCoeff_embX a0)
        (S.leadingCoeff_embX a1) (hYn β hβ hβv) (by rw [hY0 β hβ hβv]; exact hns' β hββ)
  rw [hord β₀ hβ₀ hv (Or.inl rfl), hord (-β₀) hnb hvM (Or.inr rfl)]

end SuperData

end Differential
