import RischTragerBronstein.Torsion.PlaceLocal1

/-!
# Local place data (2): the places of a split fibre

For a split fibre `Φ` (distinct roots `yₖ` of `G(a + Tᴺ, Y)`, `G` the image of `Fc` under `ψ : F → K`)
and a primitive `N`-th root of unity `ζ = ψ ζ_F`, `Φ.locPlaces` lists the places (the orbits of
`T ↦ ζ T`, sorted representatives) with truncated place series pulled back to `F`, and the roots as
conjugates of place series. **`locPlaces_OK`**: it satisfies the local conditions `LocPlaces.OK`, given
pull-backs of the finitely many coefficients used (below `Φ.bnd`, independent of `F`).
-/

open Polynomial HahnSeries

namespace Curves

open CPoly Sup LaurentSeries Differential

variable {F : Type*} [Field F] [DecidableEq F] {K : Type*} [Field K] {ψ : F →+* K}
variable {Fc : BPoly F} {n : ℕ}
variable (Φ : SplitFibre (C := K) (K := K) ((toB Fc).map (mapRingHom ψ)) n) {ζ : K}
  (hζ : IsPrimitiveRoot ζ Φ.N) {α : F} (hα : ψ α = Φ.a)

namespace SplitFibre

lemma sum_sort_map {M : Type*} [AddCommMonoid M] (s : Finset (Fin n)) (f : Fin n → M) :
    ((s.sort (· ≤ ·)).map f).sum = ∑ π ∈ s, f π := by
  conv_rhs => rw [← Finset.sort_toFinset s (· ≤ ·)]
  rw [List.sum_toFinset _ (Finset.sort_nodup _ _)]

/-- The representatives of the places, sorted. -/
noncomputable def repL : List (Fin n) :=
  (Finset.univ.filter fun π ↦ Φ.rep hζ π = π).sort (· ≤ ·)

lemma mem_repL (π : Fin n) : π ∈ Φ.repL hζ ↔ Φ.rep hζ π = π := by
  simp [repL]

lemma repL_nodup : (Φ.repL hζ).Nodup := Finset.sort_nodup _ _

include hα in
lemma rootCheck_exists (π : Fin n) :
    ∃ d, ∀ prec, d < prec → ∀ pre : K → F,
      (∀ i < d + prec, ψ (pre (PowerSeries.coeff i (Φ.placeSer hζ π))) =
        PowerSeries.coeff i (Φ.placeSer hζ π)) →
      rootCheck Fc α (Φ.period hζ π) prec ((List.range (d + prec)).map fun i ↦
        pre (PowerSeries.coeff i (Φ.placeSer hζ π))) = true := by
  refine rootCheck_trunc ψ Fc α _ _ ?_ ?_
  · rw [hα]; exact Φ.placeSer_root hζ π
  · rw [hα]; exact placeSer_deriv_ne_zero Φ hζ π

/-- The order of `∂_Y G` along the place series (a bound for the root check). -/
noncomputable def dOrd (π : Fin n) : ℕ := Classical.choose (Φ.rootCheck_exists hζ hα π)

lemma exists_sep (k l : Fin n) (hkl : k ≠ l) :
    ∃ i, PowerSeries.coeff i (Φ.y k) ≠ PowerSeries.coeff i (Φ.y l) := by
  by_contra h
  push Not at h
  exact hkl (Φ.inj (PowerSeries.ext h))

/-- The first coefficient separating two roots. -/
noncomputable def sepIdx (k l : Fin n) : ℕ :=
  if h : k ≠ l then Classical.choose (Φ.exists_sep k l h) else 0

/-- The test precision: above all separating coefficients. -/
noncomputable def tpF : ℕ := 1 + ∑ k, ∑ l, Φ.sepIdx k l

lemma sepIdx_lt (k l : Fin n) : Φ.sepIdx k l < Φ.tpF := by
  have : Φ.sepIdx k l ≤ ∑ k, ∑ l, Φ.sepIdx k l :=
    (Finset.single_le_sum (f := fun l ↦ Φ.sepIdx k l) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ l)).trans (Finset.single_le_sum (f := fun k ↦ ∑ l, Φ.sepIdx k l)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ k))
  rw [tpF]; omega

lemma sepIdx_spec (k l : Fin n) (hkl : k ≠ l) :
    PowerSeries.coeff (Φ.sepIdx k l) (Φ.y k) ≠ PowerSeries.coeff (Φ.sepIdx k l) (Φ.y l) := by
  rw [sepIdx, dif_pos hkl]; exact Classical.choose_spec (Φ.exists_sep k l hkl)

variable (tx : ℕ)

/-- The place precision (`tx`: slack for the test precision `tpF + tx`). -/
noncomputable def ppF (π : Fin n) : ℕ := Φ.dOrd hζ hα π + (Φ.tpF + tx) + 1

/-- The number of coefficients of the place series used. -/
noncomputable def bnd : ℕ := ∑ π, (Φ.dOrd hζ hα π + Φ.ppF hζ hα tx π)

lemma lt_bnd (π : Fin n) (i : ℕ) (hi : i < Φ.dOrd hζ hα π + Φ.ppF hζ hα tx π) : i < Φ.bnd hζ hα tx :=
  lt_of_lt_of_le hi (Finset.single_le_sum (f := fun π ↦ Φ.dOrd hζ hα π + Φ.ppF hζ hα tx π)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ π))

/-- The exponents of the conjugations. -/
noncomputable def cExp (k : Fin n) : ℕ := Classical.choose (Φ.y_eq_conj_rep hζ k)

lemma cExp_spec (k : Fin n) : Φ.y k =
    conjPS (ζ ^ Φ.cExp hζ k) (Φ.sIdx hζ (Φ.rep hζ k)) (Φ.placeSer hζ (Φ.rep hζ k)) :=
  Classical.choose_spec (Φ.y_eq_conj_rep hζ k)

variable (pre : K → F) (ζF : F) (Γf : Fin n → ℕ)

/-- The truncated place series over `F`. -/
noncomputable def yF (π : Fin n) : CPoly F :=
  (List.range (Φ.dOrd hζ hα π + Φ.ppF hζ hα tx π)).map fun i ↦
    pre (PowerSeries.coeff i (Φ.placeSer hζ π))

/-- **The local place data of the fibre.** -/
noncomputable def locPlaces : LocPlaces F where
  α := α
  N := Φ.N
  pls := (Φ.repL hζ).map fun π ↦ (Φ.period hζ π, Φ.yF hζ hα tx pre π, Φ.ppF hζ hα tx π)
  rts := (List.finRange n).map fun k ↦
    ((Φ.repL hζ).idxOf (Φ.rep hζ k), Φ.sIdx hζ (Φ.rep hζ k), ζF ^ Φ.cExp hζ k)
  Γ := (Φ.repL hζ).map Γf
  cf := ((Φ.repL hζ).map Γf).sum
  tp := Φ.tpF + tx

end SplitFibre

end Curves
