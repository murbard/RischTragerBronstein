import RischTragerBronstein.Torsion.Residual

/-!
# Bridges between jets, orders and norms (general curves)

* `vanishAtG_of_map`: jet vanishing descends along injective ring maps (unit `F_Y`);
* `le_rootMultiplicity_normW`: lower bounds for the orders along a complete branch system above
  `b` bound the multiplicity of `b` in the norm from below;
* `dvd_of_rootMultiplicity_le`: over an algebraically closed field, divisibility from
  multiplicities;
* `base_vanishG`: if `(x − x₀)ⁿ` divides the norm of `W` and `W` does not vanish to order `2` at the
  points `(x₀, y_k)`, `k ≠ k₀`, of an unramified fibre, then `W(x₀, y_{k₀}) = 0`.
-/

open Polynomial HahnSeries

namespace GTors

lemma vanishAtG_of_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) {F W : R[X][X]} {a b : R} {ℓ : ℕ} {V : R[X]}
    (hV : IsBranchG F a b ℓ V)
    (hu : IsUnit (Sup.evalW (derivative (F.map (mapRingHom φ))) (φ a) (φ b)))
    (h : VanishAtG (F.map (mapRingHom φ)) (W.map (mapRingHom φ)) (φ a) (φ b) ℓ) :
    VanishAtG F W a b ℓ := by
  have hV' := hV.mapR φ
  have h1 := (vanishAtG_iff hu hV').mp h
  rw [← Sup.jetN_map] at h1
  refine ⟨V, hV, ?_⟩
  rw [X_pow_dvd_iff] at h1 ⊢
  intro d hd
  have := h1 d hd
  rw [coeff_map] at this
  exact (map_eq_zero_iff φ hφ).mp this

lemma VanishAtG.map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {F W : R[X][X]}
    {a b : R} {ℓ : ℕ} (h : VanishAtG F W a b ℓ) :
    VanishAtG (F.map (mapRingHom φ)) (W.map (mapRingHom φ)) (φ a) (φ b) ℓ := by
  obtain ⟨V, hV, hd⟩ := h
  refine ⟨V.map φ, hV.mapR φ, ?_⟩
  rw [← Sup.jetN_map]
  simpa using Polynomial.map_dvd φ hd

lemma VanishAtG.C_mul {R : Type*} [CommRing R] {F W : R[X][X]} {a b : R} {ℓ : ℕ}
    (h : VanishAtG F W a b ℓ) (c : R) :
    VanishAtG F (Polynomial.C (Polynomial.C c) * W) a b ℓ := by
  obtain ⟨V, hV, hd⟩ := h
  refine ⟨V, hV, ?_⟩
  rw [Sup.jetN_C_poly_mul, C_comp]
  exact dvd_mul_of_dvd_right hd _

lemma not_vanish2_of_unit {R : Type*} [CommRing R] [Nontrivial R] {F W : R[X][X]} {a b : R}
    {V : R[X]} (hV : IsBranchG F a b 2 V) (hu : IsUnit (Sup.evalW (derivative F) a b))
    (h1 : IsUnit ((Sup.jetN W a V).coeff 1)) : ¬ VanishAtG F W a b 2 := by
  intro h
  have := (vanishAtG_iff hu hV).mp h
  rw [X_pow_dvd_iff] at this
  exact h1.ne_zero (this 1 (by norm_num))

end GTors

namespace Curves

open Differential LaurentSeries GTors

lemma dvd_of_rootMultiplicity_le {K : Type*} [Field K] [IsAlgClosed K] (P Q : K[X]) (hP : P ≠ 0)
    (hQ : Q ≠ 0) (h : ∀ b, P.rootMultiplicity b ≤ Q.rootMultiplicity b) : P ∣ Q := by
  classical
  have hle : P.roots ≤ Q.roots := Multiset.le_iff_count.mpr fun b ↦ by
    rw [count_roots, count_roots]; exact h b
  have h1 : (P.roots.map fun a ↦ X - Polynomial.C a).prod ∣ (Q.roots.map fun a ↦ X - Polynomial.C a).prod :=
    Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle)
  have hPe := C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (k := K) (p := P))
  rw [← hPe, IsUnit.mul_left_dvd (isUnit_C.mpr (leadingCoeff_ne_zero.mpr hP).isUnit)]
  exact h1.trans (prod_multiset_X_sub_C_dvd Q)

section Bridge

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **Multiplicities in the norm from lower bounds.** -/
lemma le_rootMultiplicity_normW (W : C[X][X]) (m : ℕ) (hWm : W.natDegree ≤ m)
    (hW : S.evXY W ≠ 0) (N : ℕ) (hN : 0 < N) (b : K) (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (z : LaurentSeries K → ℤ) (hz : ∀ r ∈ l, z r ≤ ((W.map (branchSub N b)).eval r).order)
    (k : ℤ) (hk : (l.map z).sum = N * k) :
    k ≤ (((S.normW W m).map (algebraMap C K)).rootMultiplicity b : ℤ) := by
  have h1 := S.sum_order_fin W m hWm hW N hN b l hl
  have h2 : (l.map z).sum ≤ (l.map fun r ↦ ((W.map (branchSub N b)).eval r).order).sum :=
    List.sum_le_sum fun r hr ↦ hz r hr
  rw [hk, h1] at h2
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  exact le_of_mul_le_mul_left h2 hN'

/-- **Vanishing at the base point from the norm.** -/
theorem base_vanishG (W : C[X][X]) (m : ℕ) (hWm : W.natDegree ≤ m) (hW : S.evXY W ≠ 0)
    (x₀ : C) (y : Fin S.F.natDegree → C) (Y : Fin S.F.natDegree → PowerSeries K)
    (hY : ∀ k, (fibrePS S.F (algebraMap C K x₀)).eval (Y k) = 0)
    (hYc : ∀ k, PowerSeries.constantCoeff (Y k) = algebraMap C K (y k))
    (hs : S.F.map (branchSub 1 (algebraMap C K x₀)) =
      ∏ k, (X - Polynomial.C (ofPowerSeries ℤ K (Y k))))
    (hFY : ∀ k, (fibreAt (derivative S.F) (algebraMap C K x₀)).eval (algebraMap C K (y k)) ≠ 0)
    (hmult : S.F.natDegree ≤ ((S.normW W m).map (algebraMap C K)).rootMultiplicity
      (algebraMap C K x₀))
    (k0 : Fin S.F.natDegree)
    (hsim : ∀ k, k ≠ k0 → ¬ VanishAtG (S.F.map (mapRingHom (algebraMap C K)))
      (W.map (mapRingHom (algebraMap C K))) (algebraMap C K x₀) (algebraMap C K (y k)) 2) :
    Sup.evalW W x₀ (y k0) = 0 := by
  classical
  set ι := algebraMap C K with hι
  set l := List.ofFn fun k ↦ ofPowerSeries ℤ K (Y k) with hl_def
  have hl : S.F.map (branchSub 1 (ι x₀)) = (l.map fun r ↦ X - Polynomial.C r).prod := by
    rw [hs, hl_def, List.map_ofFn, List.prod_ofFn]; rfl
  have hsum := S.sum_order_fin W m hWm hW 1 one_pos (ι x₀) l hl
  rw [hl_def, List.map_ofFn, List.sum_ofFn] at hsum
  set o : Fin S.F.natDegree → ℤ := fun k ↦
    ((W.map (branchSub 1 (ι x₀))).eval (ofPowerSeries ℤ K (Y k))).order with ho
  have ho' : ∀ k, o k = (ofPowerSeries ℤ K ((W.map (psSub 1 (ι x₀))).eval (Y k))).order :=
    fun k ↦ by rw [ho]; simp only; rw [eval_branchSub_ofPS]
  have hne : ∀ k, ofPowerSeries ℤ K ((W.map (psSub 1 (ι x₀))).eval (Y k)) ≠ 0 := by
    intro k
    have := S.branch_values_ne_zero W hW _ (branchSub_injective 1 one_pos (ι x₀)) l hl
      _ (List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨k, rfl⟩, rfl⟩)
    rwa [eval_branchSub_ofPS] at this
  have hnn : ∀ k, 0 ≤ o k := fun k ↦ by
    rw [ho']; exact order_nonneg_of_lowerBd' _ (fun j hj ↦ LaurentSeries.coeff_ofPS_neg _ hj)
  have hle1 : ∀ k, k ≠ k0 → o k ≤ 1 := by
    intro k hk
    by_contra hlt
    push Not at hlt
    apply hsim k hk
    rw [← lowerBd_iff_vanishAtG S.F (ι x₀) (ι (y k)) (Y k) (hY k) (hYc k) (hFY k) W 2]
    have := lowerBd_of_le_order _ 2 (by rw [← ho']; exact_mod_cast hlt)
    exact_mod_cast this
  have hk0 : 1 ≤ o k0 := by
    have hsplit : ∑ k, o k = o k0 + ∑ k ∈ Finset.univ.erase k0, o k :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ k0)).symm
    have hbound : ∑ k ∈ Finset.univ.erase k0, o k ≤ ∑ k ∈ Finset.univ.erase k0, (1 : ℤ) :=
      Finset.sum_le_sum fun k hk ↦ hle1 k (Finset.ne_of_mem_erase hk)
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at hbound
    have hs' : (∑ k, o k : ℤ) = ((((S.normW W m).map ι).rootMultiplicity (ι x₀) : ℕ) : ℤ) := by
      have : ∑ k, o k = ((1 : ℕ) : ℤ) * (((S.normW W m).map (algebraMap C K)).rootMultiplicity
          (ι x₀) : ℤ) := hsum
      rw [this]; push_cast; ring
    have hm' : ((S.F.natDegree : ℕ) : ℤ) ≤ ((((S.normW W m).map ι).rootMultiplicity (ι x₀) : ℕ) : ℤ) := by
      exact_mod_cast hmult
    have hn1 : ((S.F.natDegree - 1 : ℕ) : ℤ) = S.F.natDegree - 1 := by
      have := Nat.pos_of_ne_zero S.natDegree_F_ne_zero
      push_cast [Nat.cast_sub (show 1 ≤ S.F.natDegree by omega)]; ring
    rw [hn1] at hbound
    linarith
  -- the constant coefficient vanishes
  rw [ho'] at hk0
  have hl1 := lowerBd_of_le_order _ 1 hk0
  have hdvd := (lowerBd_ofPS_iff _ 1).mp (by exact_mod_cast hl1)
  rw [pow_one, PowerSeries.X_dvd_iff, constantCoeff_eval_psSub, hYc, evalW_mapG] at hdvd
  exact (map_eq_zero_iff _ ι.injective).mp hdvd

end CurveData

end Bridge

end Curves
