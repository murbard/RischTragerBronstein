import RischTragerBronstein.Torsion.PlaceExist1

/-!
# Places above a point exist (2): orbits

The orbits of the conjugation permutation are the places. `rep k` is the least root in the orbit of
`k`; every root is `σⁱ(rep k)` with `i < e` (`rep_spec`), so it is the conjugate
`y_π((ζⁱ T)^{N/e})` of the place series of its representative (`y_eq_conj_rep`). The orbit of a
place has `e_π` elements, hence **`sum_period_reps`**: `∑_π e_π = n`.
-/

open Polynomial HahnSeries

namespace Curves

open Differential LaurentSeries

section Orbits

variable {C K : Type*} [Field C] [Field K] [Algebra C K] {G : C[X][X]} {n : ℕ}

namespace SplitFibre

variable (Φ : SplitFibre (K := K) G n) {ζ : K} (hζ : IsPrimitiveRoot ζ Φ.N)
include hζ

lemma exists_iter_lt (l k : Fin n) (h : ∃ i, (Φ.conjPerm hζ)^[i] l = k) :
    ∃ i < Φ.period hζ l, (Φ.conjPerm hζ)^[i] l = k := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i % Φ.period hζ l, Nat.mod_lt _ (Φ.period_pos hζ l), ?_⟩
  rw [← hi]
  exact Function.iterate_mod_minimalPeriod_eq

open Classical in
/-- The representative (least element) of the orbit of `k`. -/
noncomputable def rep (k : Fin n) : Fin n :=
  (Finset.univ.filter fun l ↦ ∃ i, (Φ.conjPerm hζ)^[i] l = k).min' ⟨k, by simp; exact ⟨0, rfl⟩⟩

lemma rep_mem (k : Fin n) : ∃ i, (Φ.conjPerm hζ)^[i] (Φ.rep hζ k) = k := by
  classical
  have := Finset.min'_mem (Finset.univ.filter fun l ↦ ∃ i, (Φ.conjPerm hζ)^[i] l = k)
    ⟨k, by simp; exact ⟨0, rfl⟩⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this

lemma rep_spec (k : Fin n) :
    ∃ i < Φ.period hζ (Φ.rep hζ k), (Φ.conjPerm hζ)^[i] (Φ.rep hζ k) = k :=
  Φ.exists_iter_lt hζ _ _ (Φ.rep_mem hζ k)

lemma rep_le (k l : Fin n) (h : ∃ i, (Φ.conjPerm hζ)^[i] l = k) : Φ.rep hζ k ≤ l := by
  classical
  exact Finset.min'_le _ _ (by simpa using h)

/-- Same orbit, symmetric form. -/
lemma orbit_symm (l k : Fin n) (h : ∃ i, (Φ.conjPerm hζ)^[i] l = k) :
    ∃ i, (Φ.conjPerm hζ)^[i] k = l := by
  obtain ⟨i, hi1, hi2⟩ := Φ.exists_iter_lt hζ l k h
  refine ⟨Φ.period hζ l - i, ?_⟩
  rw [← hi2, ← Function.iterate_add_apply, Nat.sub_add_cancel hi1.le]
  exact Function.iterate_minimalPeriod

lemma orbit_trans (a b c : Fin n) (h1 : ∃ i, (Φ.conjPerm hζ)^[i] a = b)
    (h2 : ∃ i, (Φ.conjPerm hζ)^[i] b = c) : ∃ i, (Φ.conjPerm hζ)^[i] a = c := by
  obtain ⟨i, rfl⟩ := h1
  obtain ⟨j, rfl⟩ := h2
  exact ⟨j + i, Function.iterate_add_apply _ _ _ _⟩

/-- The representative only depends on the orbit. -/
lemma rep_eq_of_orbit (k l : Fin n) (h : ∃ i, (Φ.conjPerm hζ)^[i] k = l) :
    Φ.rep hζ l = Φ.rep hζ k := by
  refine le_antisymm (Φ.rep_le hζ l _ (Φ.orbit_trans hζ _ _ _ (Φ.rep_mem hζ k) h)) ?_
  exact Φ.rep_le hζ k _ (Φ.orbit_trans hζ _ _ _ (Φ.rep_mem hζ l) (Φ.orbit_symm hζ _ _ h))

lemma rep_rep (k : Fin n) : Φ.rep hζ (Φ.rep hζ k) = Φ.rep hζ k :=
  (Φ.rep_eq_of_orbit hζ (Φ.rep hζ k) k (Φ.rep_mem hζ k)).symm

lemma period_rep (k : Fin n) : Φ.period hζ (Φ.rep hζ k) = Φ.period hζ k := by
  obtain ⟨i, hi⟩ := Φ.rep_mem hζ k
  have := Function.minimalPeriod_apply_iterate (Φ.mem_periodicPts hζ (Φ.rep hζ k)) i
  rw [hi] at this
  exact this.symm

/-- **Every root is a conjugate of the place series of its representative.** -/
lemma y_eq_conj_rep (k : Fin n) : ∃ i : ℕ, Φ.y k =
    conjPS (ζ ^ i) (Φ.sIdx hζ (Φ.rep hζ k)) (Φ.placeSer hζ (Φ.rep hζ k)) := by
  obtain ⟨i, hi⟩ := Φ.rep_mem hζ k
  refine ⟨i, HahnSeries.ofPowerSeries_injective (Γ := ℤ) ?_⟩
  have h := Φ.conjPerm_iterate hζ i (Φ.rep hζ k)
  rw [hi] at h
  rw [h, Φ.ofPS_y_eq_lsub hζ (Φ.rep hζ k), ofPS_conjPS _ (pow_ne_zero _ (Φ.ζ_ne_zero hζ)) _
    (Φ.sIdx_pos hζ _)]

/-- The orbit of a place has `e_π` elements. -/
lemma card_orbit (π : Fin n) (hπ : Φ.rep hζ π = π) :
    (Finset.univ.filter fun k ↦ Φ.rep hζ k = π).card = Φ.period hζ π := by
  classical
  have himg : (Finset.univ.filter fun k ↦ Φ.rep hζ k = π) =
      (Finset.range (Φ.period hζ π)).image fun i ↦ (Φ.conjPerm hζ)^[i] π := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro rfl
      obtain ⟨i, hi, h⟩ := Φ.rep_spec hζ k
      exact ⟨i, hi, h⟩
    · rintro ⟨i, -, rfl⟩
      rw [Φ.rep_eq_of_orbit hζ π _ ⟨i, rfl⟩, hπ]
  rw [himg, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  exact Function.iterate_injOn_Iio_minimalPeriod (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij

/-- **The ramification indices of the places add up to `n`.** -/
theorem sum_period_reps :
    ∑ π ∈ Finset.univ.filter (fun π ↦ Φ.rep hζ π = π), Φ.period hζ π = n := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := Φ.rep hζ) (s := Finset.univ)
    (t := Finset.univ.filter fun π ↦ Φ.rep hζ π = π)
    (fun k _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, Φ.rep_rep hζ k⟩)
  rw [Finset.card_univ, Fintype.card_fin] at h
  refine Eq.trans (Finset.sum_congr rfl fun π hπ ↦ ?_) h.symm
  have hπ' := (Finset.mem_filter.mp hπ).2
  rw [← Φ.card_orbit hζ π hπ']

end SplitFibre

end Orbits

end Curves
