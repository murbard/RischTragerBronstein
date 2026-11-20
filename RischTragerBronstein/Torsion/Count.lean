import RischTragerBronstein.Torsion.LSpace

/-!
# Counting conditions: functions with prescribed zeros exist

* `exists_coords_ker`: a linear map from coordinate vectors `c : Fin n → C[X]` with
  `deg cⱼ + δⱼ ≤ M` to a space of dimension `< ∑ⱼ (M + 1 − δⱼ)` kills a non-zero vector;
* `lmap`: the coefficient map `C⸨T⸩ → K⸨T⸩` of a ring map `C → K`, with `lmap_branchSub`;
* `exists_coords_vanishing`: given series `σᵢⱼ ∈ C⟦T⟧` (the expansions of the basis functions
  along branches) and orders `mᵢ` with `∑ mᵢ < ∑ⱼ (M + 1 − δⱼ)`, some non-zero `c` makes every
  `∑ⱼ cⱼ(aᵢ + T^{eᵢ}) σᵢⱼ` vanish to order `mᵢ`.
-/

open Polynomial HahnSeries Module

namespace Curves

open Differential LaurentSeries

section Count

variable {C : Type*} [Field C]

/-- The coefficient vector of a polynomial of degree `< k`. -/
noncomputable def polyOfFin {k : ℕ} (v : Fin k → C) : C[X] := ∑ e : Fin k, Polynomial.C (v e) * X ^ (e : ℕ)

lemma polyOfFin_coeff {k : ℕ} (v : Fin k → C) (e : Fin k) : (polyOfFin v).coeff e = v e := by
  classical
  rw [polyOfFin, finset_sum_coeff, Finset.sum_eq_single e]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro b _ hb
    rw [coeff_C_mul_X_pow, if_neg]
    exact fun h ↦ hb (Fin.ext h.symm)
  · intro h; exact absurd (Finset.mem_univ e) h

lemma polyOfFin_natDegree {k : ℕ} (v : Fin k → C) (hk : 0 < k) :
    (polyOfFin v).natDegree ≤ k - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun e _ ↦ (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := e.isLt; omega

/-- The linear map from coefficient arrays to coordinate vectors. -/
noncomputable def coordsOf {n : ℕ} (k : Fin n → ℕ) :
    ((j : Fin n) → Fin (k j) → C) →ₗ[C] (Fin n → C[X]) where
  toFun a j := polyOfFin (a j)
  map_add' a b := by
    ext1 j
    simp only [polyOfFin, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' r a := by
    ext1 j
    simp only [polyOfFin, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Finset.mul_sum,
      Polynomial.smul_eq_C_mul]
    exact Finset.sum_congr rfl fun e _ ↦ by ring

/-- **Existence by counting.** -/
theorem exists_coords_ker {n : ℕ} (δ : Fin n → ℕ) (M : ℕ) {V : Type*} [AddCommGroup V]
    [Module C V] [FiniteDimensional C V] (Φ : (Fin n → C[X]) →ₗ[C] V)
    (hcount : finrank C V < ∑ j, (M + 1 - δ j)) :
    ∃ c : Fin n → C[X], c ≠ 0 ∧ (∀ j, c j ≠ 0 → (c j).natDegree + δ j ≤ M) ∧ Φ c = 0 := by
  classical
  set k : Fin n → ℕ := fun j ↦ M + 1 - δ j with hk
  have hdim : finrank C ((j : Fin n) → Fin (k j) → C) = ∑ j, (M + 1 - δ j) := by
    rw [Module.finrank_pi_fintype]
    simp [hk]
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := Φ.comp (coordsOf k)) (by rw [hdim]; exact hcount)
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨coordsOf k a, fun h0 ↦ ha0 ?_, fun j hj ↦ ?_, ha⟩
  · funext j e
    have := congrArg (fun c : Fin n → C[X] ↦ (c j).coeff e) h0
    simp only [coordsOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, Polynomial.coeff_zero] at this
    rw [polyOfFin_coeff] at this
    exact this
  · have hkpos : 0 < k j := by
      by_contra h0
      push_neg at h0
      apply hj
      simp only [coordsOf, LinearMap.coe_mk, AddHom.coe_mk, polyOfFin]
      have : k j = 0 := by omega
      exact Finset.sum_eq_zero fun e _ ↦ absurd e.isLt (by omega)
    have := polyOfFin_natDegree (a j) hkpos
    simp only [coordsOf, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [hk] at this hkpos
    omega

/-- The coefficient map of Laurent series. -/
noncomputable def lmap {K : Type*} [Field K] (ι : C →+* K) : LaurentSeries C →+* LaurentSeries K where
  toFun z := z.map ι
  map_one' := by ext k; simp [HahnSeries.coeff_one]
  map_mul' x y := HahnSeries.map_mul ι.toNonUnitalRingHom
  map_zero' := by ext; simp
  map_add' x y := HahnSeries.map_add ι.toAddMonoidHom

variable {K : Type*} [Field K]

@[simp] lemma lmap_coeff (ι : C →+* K) (z : LaurentSeries C) (k : ℤ) :
    (lmap ι z).coeff k = ι (z.coeff k) := rfl

lemma lowerBd_lmap_iff (ι : C →+* K) (z : LaurentSeries C) (m : ℤ) :
    LowerBd (lmap ι z) m ↔ LowerBd z m := by
  refine ⟨fun h k hk ↦ ?_, fun h k hk ↦ ?_⟩
  · have := h k hk
    rw [lmap_coeff] at this
    exact (map_eq_zero_iff ι ι.injective).mp this
  · rw [lmap_coeff, h k hk, map_zero]

lemma lmap_injective (ι : C →+* K) : Function.Injective (lmap ι) := by
  intro x y h
  ext k
  have := congrArg (fun z : LaurentSeries K ↦ z.coeff k) h
  simp only [lmap_coeff] at this
  exact ι.injective this

lemma lmap_branchSub [Algebra C K] (N : ℕ) (a : C) (P : C[X]) :
    lmap (algebraMap C K) (branchSub (K := C) N a P) = branchSub (K := K) N (algebraMap C K a) P := by
  have e : (P.map (algebraMap C K)).comp (Polynomial.C (algebraMap C K a) + X ^ N) =
      ((P.map (algebraMap C C)).comp (Polynomial.C a + X ^ N)).map (algebraMap C K) := by
    rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, Algebra.algebraMap_self, Polynomial.map_id]
  ext k
  rw [lmap_coeff, branchSub_apply, branchSub_apply, e, coeff_ofPS, coeff_ofPS]
  split_ifs
  · rw [Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_map]
  · exact map_zero _

/-- **Functions with prescribed zeros along branches exist** when there are fewer conditions than
coordinates. -/
theorem exists_coords_vanishing {n : ℕ} (δ : Fin n → ℕ) (M : ℕ) {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (a : ι → C) (σ : ι → Fin n → LaurentSeries C)
    (hσ : ∀ i j, LowerBd (σ i j) 0) (m : ι → ℕ)
    (hcount : ∑ i, m i < ∑ j, (M + 1 - δ j)) :
    ∃ c : Fin n → C[X], c ≠ 0 ∧ (∀ j, c j ≠ 0 → (c j).natDegree + δ j ≤ M) ∧
      ∀ i, LowerBd (∑ j, branchSub (K := C) (e i) (a i) (c j) * σ i j) (m i) := by
  classical
  let Φ : (Fin n → C[X]) →ₗ[C] ((i : ι) → Fin (m i) → C) :=
    { toFun := fun c i k ↦ (∑ j, branchSub (K := C) (e i) (a i) (c j) * σ i j).coeff k
      map_add' := fun c c' ↦ by
        ext i k
        simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, HahnSeries.coeff_add]
      map_smul' := fun r c ↦ by
        ext i k
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Polynomial.smul_eq_C_mul, map_mul]
        have : branchSub (K := C) (e i) (a i) (Polynomial.C r) = HahnSeries.C r := by
          rw [branchSub_apply]; simp [Polynomial.map_C, C_comp]
        simp only [this, mul_assoc, ← Finset.mul_sum]
        rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul] }
  have hdim : finrank C ((i : ι) → Fin (m i) → C) = ∑ i, m i := by
    rw [Module.finrank_pi_fintype]; simp
  obtain ⟨c, hc0, hdeg, hΦ⟩ := exists_coords_ker δ M Φ (by rw [hdim]; exact hcount)
  refine ⟨c, hc0, hdeg, fun i k hk ↦ ?_⟩
  by_cases hk0 : k < 0
  · have hb : LowerBd (∑ j, branchSub (K := C) (e i) (a i) (c j) * σ i j) 0 := by
      refine lowerBd_sum _ _ fun j _ ↦ ?_
      have hb : LowerBd (branchSub (K := C) (e i) (a i) (c j)) 0 := by
        rw [branchSub_apply]; intro k hk; exact LaurentSeries.coeff_ofPS_neg _ hk
      simpa using hb.mul (hσ i j)
    exact hb k hk0
  · push_neg at hk0
    have := congrFun (congrFun hΦ i) ⟨k.toNat, by omega⟩
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    rwa [Int.toNat_of_nonneg hk0] at this

end Count

end Curves
