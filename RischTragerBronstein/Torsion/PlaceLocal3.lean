import RischTragerBronstein.Torsion.PlaceLocal2

/-!
# Local place data (3): the local conditions

**`locPlaces_OK`**: the place data `Φ.locPlaces` of a split fibre satisfy `LocPlaces.OK`, given
pull-backs of the place-series coefficients below `Φ.bnd` and of `ζ`.
-/

open Polynomial HahnSeries

namespace Curves

open CPoly Sup LaurentSeries Differential

variable {F : Type*} [Field F] [DecidableEq F] {K : Type*} [Field K] {ψ : F →+* K}
variable {Fc : BPoly F} {n : ℕ}
variable (Φ : SplitFibre (C := K) (K := K) ((toB Fc).map (mapRingHom ψ)) n) {ζ : K}
  (hζ : IsPrimitiveRoot ζ Φ.N) {α : F} (hα : ψ α = Φ.a)
variable (tx : ℕ) (pre : K → F) (ζF : F) (Γf : Fin n → ℕ)

namespace SplitFibre

section Access

lemma lp_pls_length : (Φ.locPlaces hζ hα tx pre ζF Γf).pls.length = (Φ.repL hζ).length := by
  simp [locPlaces]

lemma lp_getD_pls (t : ℕ) (ht : t < (Φ.repL hζ).length) :
    (Φ.locPlaces hζ hα tx pre ζF Γf).pls.getD t (1, [], 0) =
      (Φ.period hζ (Φ.repL hζ)[t], Φ.yF hζ hα tx pre (Φ.repL hζ)[t], Φ.ppF hζ hα tx (Φ.repL hζ)[t]) := by
  simp only [locPlaces]
  rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map]

lemma lp_e (t : ℕ) (ht : t < (Φ.repL hζ).length) :
    (Φ.locPlaces hζ hα tx pre ζF Γf).e t = Φ.period hζ (Φ.repL hζ)[t] := by
  rw [LocPlaces.e, lp_getD_pls Φ hζ hα tx pre ζF Γf t ht]

lemma lp_y (t : ℕ) (ht : t < (Φ.repL hζ).length) :
    (Φ.locPlaces hζ hα tx pre ζF Γf).y t = Φ.yF hζ hα tx pre (Φ.repL hζ)[t] := by
  rw [LocPlaces.y, lp_getD_pls Φ hζ hα tx pre ζF Γf t ht]

lemma lp_pp (t : ℕ) (ht : t < (Φ.repL hζ).length) :
    (Φ.locPlaces hζ hα tx pre ζF Γf).pp t = Φ.ppF hζ hα tx (Φ.repL hζ)[t] := by
  rw [LocPlaces.pp, lp_getD_pls Φ hζ hα tx pre ζF Γf t ht]

lemma lp_getD_rts (k : ℕ) (hk : k < n) :
    (Φ.locPlaces hζ hα tx pre ζF Γf).rts.getD k (0, 1, 1) =
      ((Φ.repL hζ).idxOf (Φ.rep hζ ⟨k, hk⟩), Φ.sIdx hζ (Φ.rep hζ ⟨k, hk⟩),
        ζF ^ Φ.cExp hζ ⟨k, hk⟩) := by
  simp only [locPlaces]
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_finRange]
  rfl

lemma lp_idx (k : ℕ) (hk : k < n) :
    (Φ.locPlaces hζ hα tx pre ζF Γf).idx k = (Φ.repL hζ).idxOf (Φ.rep hζ ⟨k, hk⟩) := by
  rw [LocPlaces.idx, lp_getD_rts Φ hζ hα tx pre ζF Γf k hk]

lemma lp_s (k : ℕ) (hk : k < n) :
    (Φ.locPlaces hζ hα tx pre ζF Γf).s k = Φ.sIdx hζ (Φ.rep hζ ⟨k, hk⟩) := by
  rw [LocPlaces.s, lp_getD_rts Φ hζ hα tx pre ζF Γf k hk]

lemma lp_ζ (k : ℕ) (hk : k < n) :
    (Φ.locPlaces hζ hα tx pre ζF Γf).ζ k = ζF ^ Φ.cExp hζ ⟨k, hk⟩ := by
  rw [LocPlaces.ζ, lp_getD_rts Φ hζ hα tx pre ζF Γf k hk]

lemma lp_Γ (t : ℕ) (ht : t < (Φ.repL hζ).length) :
    (Φ.locPlaces hζ hα tx pre ζF Γf).Γ.getD t 0 = Γf (Φ.repL hζ)[t] := by
  simp only [locPlaces]
  rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map]

lemma rep_mem_repL (k : Fin n) : Φ.rep hζ k ∈ Φ.repL hζ :=
  (Φ.mem_repL hζ _).mpr (Φ.rep_rep hζ k)

lemma idxOf_lt (k : Fin n) : (Φ.repL hζ).idxOf (Φ.rep hζ k) < (Φ.repL hζ).length :=
  List.idxOf_lt_length_of_mem (Φ.rep_mem_repL hζ k)

lemma getElem_idxOf (k : Fin n) :
    (Φ.repL hζ)[(Φ.repL hζ).idxOf (Φ.rep hζ k)]'(Φ.idxOf_lt hζ k) = Φ.rep hζ k :=
  List.getElem_idxOf _

end Access

variable {pre ζF} in
/-- **The approximations reproduce the roots below the test precision.** -/
lemma lp_coeff (hζF : ψ ζF = ζ)
    (hpre : ∀ π : Fin n, ∀ i < Φ.bnd hζ hα tx, ψ (pre (PowerSeries.coeff i (Φ.placeSer hζ π))) =
      PowerSeries.coeff i (Φ.placeSer hζ π)) (m : Fin n) (i : ℕ) (hi : i < Φ.tpF + tx) :
    ψ ((conjC ((Φ.locPlaces hζ hα tx pre ζF Γf).ζ m) ((Φ.locPlaces hζ hα tx pre ζF Γf).s m)
      ((Φ.locPlaces hζ hα tx pre ζF Γf).y ((Φ.locPlaces hζ hα tx pre ζF Γf).idx m))).getD i 0) =
        PowerSeries.coeff i (Φ.y m) := by
  have hlt := Φ.idxOf_lt hζ m
  have hs := Φ.sIdx_pos hζ (Φ.rep hζ m)
  rw [lp_ζ Φ hζ hα tx pre ζF Γf m m.2, lp_s Φ hζ hα tx pre ζF Γf m m.2,
    lp_idx Φ hζ hα tx pre ζF Γf m m.2, lp_y Φ hζ hα tx pre ζF Γf _ hlt]
  simp only [Fin.eta, Φ.getElem_idxOf hζ]
  rw [getD_conjC _ hs, Φ.cExp_spec hζ m, coeff_conjPS]
  split_ifs with hdvd
  · have hi' : i / Φ.sIdx hζ (Φ.rep hζ m) < Φ.dOrd hζ hα (Φ.rep hζ m) + Φ.ppF hζ hα tx (Φ.rep hζ m) := by
      have := Nat.div_le_self i (Φ.sIdx hζ (Φ.rep hζ m))
      rw [ppF]; omega
    rw [map_mul, map_pow, map_pow, hζF, yF, List.getD_eq_getElem _ _ (by simpa using hi'),
      List.getElem_map, List.getElem_range, hpre _ _ (Φ.lt_bnd hζ hα tx _ _ hi')]
  · rw [map_zero]

variable {pre ζF} in
/-- The approximation of the root `m` to the test precision. -/
lemma lp_approx (hζF : ψ ζF = ζ)
    (hpre : ∀ π : Fin n, ∀ i < Φ.bnd hζ hα tx, ψ (pre (PowerSeries.coeff i (Φ.placeSer hζ π))) =
      PowerSeries.coeff i (Φ.placeSer hζ π)) (m : Fin n) :
    (PowerSeries.X : PowerSeries K) ^ (Φ.tpF + tx) ∣ Φ.y m - thetaT ψ (toPoly
      (conjC ((Φ.locPlaces hζ hα tx pre ζF Γf).ζ m) ((Φ.locPlaces hζ hα tx pre ζF Γf).s m)
        ((Φ.locPlaces hζ hα tx pre ζF Γf).y ((Φ.locPlaces hζ hα tx pre ζF Γf).idx m)))) := by
  refine PowerSeries.X_pow_dvd_iff.mpr fun i hi ↦ ?_
  rw [map_sub, coeff_thetaT, lp_coeff Φ hζ hα tx Γf hζF hpre m i hi, sub_self]

/-- **The local conditions hold.** -/
theorem locPlaces_OK (hψ : Function.Injective ψ) (hζF : ψ ζF = ζ)
    (hpre : ∀ π : Fin n, ∀ i < Φ.bnd hζ hα tx, ψ (pre (PowerSeries.coeff i (Φ.placeSer hζ π))) =
      PowerSeries.coeff i (Φ.placeSer hζ π)) :
    (Φ.locPlaces hζ hα tx pre ζF Γf).OK Fc n := by
  classical
  set L := Φ.locPlaces hζ hα tx pre ζF Γf with hL
  set R := Φ.repL hζ with hR
  have hRe : ∀ t (ht : t < R.length), Φ.rep hζ R[t] = R[t] := fun t ht ↦
    (Φ.mem_repL hζ _).mp (List.getElem_mem ht)
  constructor
  · -- the root checks
    intro t ht
    rw [lp_pls_length] at ht
    rw [lp_e Φ hζ hα tx pre ζF Γf t ht, lp_pp Φ hζ hα tx pre ζF Γf t ht, lp_y Φ hζ hα tx pre ζF Γf t ht]
    refine ⟨Φ.period_pos hζ _, ?_⟩
    have h := Classical.choose_spec (Φ.rootCheck_exists hζ hα R[t])
    refine h _ (by rw [ppF]; unfold dOrd; omega) pre fun i hi ↦ hpre R[t] i (Φ.lt_bnd hζ hα tx R[t] i ?_)
    unfold dOrd at hi ⊢; exact hi
  · simp [hL, locPlaces]
  · simp [hL, locPlaces]
  · -- the roots
    intro k hk
    have hlt := Φ.idxOf_lt hζ ⟨k, hk⟩
    rw [lp_idx Φ hζ hα tx pre ζF Γf k hk, lp_s Φ hζ hα tx pre ζF Γf k hk, lp_ζ Φ hζ hα tx pre ζF Γf k hk,
      lp_e Φ hζ hα tx pre ζF Γf _ hlt, lp_pp Φ hζ hα tx pre ζF Γf _ hlt, Φ.getElem_idxOf hζ]
    refine ⟨by rw [lp_pls_length]; exact hlt, Φ.sIdx_pos hζ _, ?_, ?_, ?_⟩
    · show Φ.N = _
      rw [Φ.sIdx_mul hζ]
    · apply hψ
      rw [map_pow, map_pow, hζF, map_one, ← pow_mul, mul_comm, pow_mul]
      show (ζ ^ Φ.N) ^ _ = 1
      rw [hζ.pow_eq_one, one_pow]
    · show Φ.tpF + tx ≤ _
      have h1 := Φ.sIdx_pos hζ (Φ.rep hζ ⟨k, hk⟩)
      calc Φ.tpF + tx ≤ Φ.ppF hζ hα tx (Φ.rep hζ ⟨k, hk⟩) := by rw [ppF]; omega
        _ ≤ _ := Nat.le_mul_of_pos_left _ h1
  · -- separation
    intro k hk l hl hkl
    set kk : Fin n := ⟨k, hk⟩
    set ll : Fin n := ⟨l, hl⟩
    have hne : kk ≠ ll := fun h ↦ hkl (congrArg Fin.val h)
    refine ⟨Φ.sepIdx kk ll, lt_of_lt_of_le (Φ.sepIdx_lt kk ll) (Nat.le_add_right _ _), fun h ↦ Φ.sepIdx_spec kk ll hne ?_⟩
    -- the approximations reproduce the roots below the test precision
    have happ := lp_coeff Φ hζ hα tx Γf hζF hpre
    rw [← happ kk _ (lt_of_lt_of_le (Φ.sepIdx_lt kk ll) (Nat.le_add_right _ _)),
      ← happ ll _ (lt_of_lt_of_le (Φ.sepIdx_lt kk ll) (Nat.le_add_right _ _))]
    exact congrArg ψ h
  · -- the bounds
    intro t ht
    rw [lp_pls_length] at ht
    rw [lp_Γ Φ hζ hα tx pre ζF Γf t ht, lp_e Φ hζ hα tx pre ζF Γf t ht]
    have h1 : Γf R[t] ≤ (R.map Γf).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨_, List.getElem_mem ht, rfl⟩)
    have h2 := Φ.period_pos hζ R[t]
    calc Γf R[t] ≤ (R.map Γf).sum := h1
      _ ≤ (R.map Γf).sum * Φ.period hζ R[t] := Nat.le_mul_of_pos_right _ h2
  · -- the degree
    have hΓsum : L.Γ.sum = ∑ π ∈ Finset.univ.filter (fun π ↦ Φ.rep hζ π = π), Γf π := by
      simp only [hL, locPlaces]; exact sum_sort_map _ _
    rw [hΓsum, Finset.mul_sum]
    have e1 : ∀ k ∈ Finset.range n, L.s k * L.Γ.getD (L.idx k) 0 =
        (fun k : ℕ ↦ if hk : k < n then Φ.sIdx hζ (Φ.rep hζ ⟨k, hk⟩) * Γf (Φ.rep hζ ⟨k, hk⟩)
          else 0) k := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hlt := Φ.idxOf_lt hζ ⟨k, hk'⟩
      simp only [dif_pos hk']
      rw [lp_s Φ hζ hα tx pre ζF Γf k hk', lp_idx Φ hζ hα tx pre ζF Γf k hk',
        lp_Γ Φ hζ hα tx pre ζF Γf _ hlt, Φ.getElem_idxOf hζ]
    rw [Finset.sum_congr rfl e1, ← Fin.sum_univ_eq_sum_range]
    simp only [Fin.is_lt, dif_pos, Fin.eta]
    rw [← Finset.sum_fiberwise_of_maps_to (g := Φ.rep hζ)
      (t := Finset.univ.filter fun π ↦ Φ.rep hζ π = π)
      (fun k _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, Φ.rep_rep hζ k⟩)]
    refine Finset.sum_congr rfl fun π hπ ↦ ?_
    have hπ' := (Finset.mem_filter.mp hπ).2
    rw [Finset.sum_congr rfl fun k hk ↦ by rw [(Finset.mem_filter.mp hk).2], Finset.sum_const,
      smul_eq_mul]
    have hc : (Finset.univ.filter fun k ↦ Φ.rep hζ k = π).card = Φ.period hζ π :=
      Φ.card_orbit hζ π hπ'
    rw [hc, ← mul_assoc, mul_comm (Φ.period hζ π), Φ.sIdx_mul hζ]
    rfl
  · -- `dΓ ≤ n cf`
    show L.Γ.sum ≤ n * L.Γ.sum
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : R = [] := by
        rw [hR, repL]; simp
      simp [hL, locPlaces, ← hR, this]
    · exact Nat.le_mul_of_pos_left _ hn
  · -- the ramification indices add up to `n`
    have e1 : ∑ t ∈ Finset.range L.pls.length, L.e t = (L.pls.map (·.1)).sum := by
      rw [← sum_range_list]
      congr 1
      conv_rhs => rw [← map_getD_range L.pls (1, [], 0), List.map_map]
      rfl
    rw [e1]
    simp only [hL, locPlaces, List.map_map, Function.comp_def]
    rw [repL, sum_sort_map]
    exact Φ.sum_period_reps hζ
  · -- every place carries a root
    intro t ht
    rw [lp_pls_length] at ht
    refine ⟨R[t], R[t].2, ?_⟩
    rw [lp_idx Φ hζ hα tx pre ζF Γf _ R[t].2]
    simp only [Fin.eta, hRe t ht]
    exact (Φ.repL_nodup hζ).idxOf_getElem t ht

end SplitFibre

end Curves
