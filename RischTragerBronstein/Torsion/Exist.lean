import RischTragerBronstein.Torsion.EllPower

/-!
# Existence of the auxiliary function (general curves)

* `evalW_PsiC`: values of `Ψ(c)` are linear in the coordinates;
* `exists_psi`: over any field, some non-zero coordinate vector with `deg cⱼ + δⱼ ≤ M` satisfies
  `mₚ` series conditions at each place representative and vanishes at the points
  `(xᵢ, y_{i,k})`, `k ≠ 0`, when there are fewer conditions than coordinates;
* `embG_lmap`: expansions along roots with coefficients in the base field are the coefficient maps
  of the base-field computations.
-/

open Polynomial HahnSeries IntermediateField Module

namespace Curves

open Differential LaurentSeries GTors

section Exist

variable {C : Type*} [Field C]

lemma evalW_PsiC {n : ℕ} (B : Fin n → C[X][X]) (c : Fin n → C[X]) (x y : C) :
    Sup.evalW (PsiC B c) x y = ∑ j, (c j).eval x * Sup.evalW (B j) x y := by
  simp only [Sup.evalW, PsiC, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    eval_finsetSum, eval_mul, eval_C, coe_evalRingHom]

/-- **Existence of the auxiliary function.** -/
theorem exists_psi {n : ℕ} (hn : 0 < n) (B : Fin n → C[X][X]) (δ : Fin n → ℕ) (M : ℕ)
    {P : Type*} [Fintype P] (e : P → ℕ) (a : P → C) (σ : P → Fin n → LaurentSeries C)
    (hσ : ∀ π j, LowerBd (σ π j) 0) (m : P → ℕ)
    {g : ℕ} (x : Fin g → C) (y : Fin g → Fin n → C)
    (hcount : ∑ π, m π + g * (n - 1) < ∑ j, (M + 1 - δ j)) :
    ∃ c : Fin n → C[X], c ≠ 0 ∧ (∀ j, c j ≠ 0 → (c j).natDegree + δ j ≤ M) ∧
      (∀ π, LowerBd (∑ j, branchSub (K := C) (e π) (a π) (c j) * σ π j) (m π)) ∧
      ∀ i (k : Fin n), (k : ℕ) ≠ 0 → Sup.evalW (PsiC B c) (x i) (y i k) = 0 := by
  classical
  let Φ1 : (Fin n → C[X]) →ₗ[C] ((π : P) → Fin (m π) → C) :=
    { toFun := fun c π t ↦ (∑ j, branchSub (K := C) (e π) (a π) (c j) * σ π j).coeff t
      map_add' := fun c c' ↦ by
        ext π t
        simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, HahnSeries.coeff_add]
      map_smul' := fun r c ↦ by
        ext π t
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Polynomial.smul_eq_C_mul, map_mul]
        have : branchSub (K := C) (e π) (a π) (Polynomial.C r) = HahnSeries.C r := by
          rw [branchSub_apply]; simp [Polynomial.map_C, C_comp]
        simp only [this, mul_assoc, ← Finset.mul_sum]
        rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul] }
  let Φ2 : (Fin n → C[X]) →ₗ[C] ((i : Fin g) → {k : Fin n // (k : ℕ) ≠ 0} → C) :=
    { toFun := fun c i k ↦ Sup.evalW (PsiC B c) (x i) (y i k)
      map_add' := fun c c' ↦ by
        ext i k
        simp only [evalW_PsiC, Pi.add_apply, eval_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c ↦ by
        ext i k
        simp only [evalW_PsiC, Pi.smul_apply, smul_eq_mul, Polynomial.smul_eq_C_mul, eval_mul,
          eval_C, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hcard : Fintype.card {k : Fin n // (k : ℕ) ≠ 0} = n - 1 := by
    have : Fintype.card {k : Fin n // (k : ℕ) ≠ 0} = Fintype.card {k : Fin n // k ≠ ⟨0, hn⟩} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun k ↦ by
        rw [Ne, Ne, Fin.ext_iff])
    rw [this, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  have hdim : finrank C (((π : P) → Fin (m π) → C) × ((i : Fin g) → {k : Fin n // (k : ℕ) ≠ 0} → C)) =
      ∑ π, m π + g * (n - 1) := by
    rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype]
    simp [hcard]
  obtain ⟨c, hc0, hdeg, hΦ⟩ := exists_coords_ker δ M (Φ1.prod Φ2) (by rw [hdim]; exact hcount)
  have h1 : Φ1 c = 0 := congrArg Prod.fst hΦ
  have h2 : Φ2 c = 0 := congrArg Prod.snd hΦ
  refine ⟨c, hc0, hdeg, fun π t ht ↦ ?_, fun i k hk ↦ ?_⟩
  · by_cases ht0 : t < 0
    · have hb : LowerBd (∑ j, branchSub (K := C) (e π) (a π) (c j) * σ π j) 0 := by
        refine lowerBd_sum _ _ fun j _ ↦ ?_
        have hb : LowerBd (branchSub (K := C) (e π) (a π) (c j)) 0 := by
          rw [branchSub_apply]; intro k hk; exact LaurentSeries.coeff_ofPS_neg _ hk
        simpa using hb.mul (hσ π j)
      exact hb t ht0
    · push_neg at ht0
      have := congrFun (congrFun h1 π) ⟨t.toNat, by omega⟩
      simp only [Φ1, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
      rwa [Int.toNat_of_nonneg ht0] at this
  · exact congrFun (congrFun h2 i) ⟨k, hk⟩

end Exist

section Lmap

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

lemma lmap_root (e : ℕ) (a : C) (ρ : LaurentSeries C)
    (hρ : (S.F.map (branchSub (K := C) e a)).eval ρ = 0) :
    (S.F.map (branchSub (K := K) e (algebraMap C K a))).eval (lmap (algebraMap C K) ρ) = 0 := by
  have h : branchSub (C := C) (K := K) e (algebraMap C K a) =
      (lmap (algebraMap C K)).comp (branchSub (K := C) e a) :=
    RingHom.ext fun P ↦ (lmap_branchSub e a P).symm
  rw [h, ← Polynomial.map_map, eval_map, eval₂_at_apply, hρ, map_zero]

/-- **Expansions along base-field roots.** -/
lemma embG_lmap_fnWQ (e : ℕ) (he : 0 < e) (a : C) (ρ : LaurentSeries C)
    (hρ : (S.F.map (branchSub (K := C) e a)).eval ρ = 0) (W : C[X][X]) (D : C[X]) :
    S.embG (branchSub e (algebraMap C K a)) (branchSub_injective e he _) (lmap (algebraMap C K) ρ)
      (S.lmap_root e a ρ hρ) (S.fnWQ W D) =
      lmap (algebraMap C K) ((W.map (branchSub (K := C) e a)).eval ρ *
        (branchSub (K := C) e a D)⁻¹) := by
  have h : branchSub (C := C) (K := K) e (algebraMap C K a) =
      (lmap (algebraMap C K)).comp (branchSub (K := C) e a) :=
    RingHom.ext fun P ↦ (lmap_branchSub e a P).symm
  rw [S.embG_fnWQ, map_mul, map_inv₀, ← lmap_branchSub]
  congr 1
  rw [h, ← Polynomial.map_map, eval_map, eval₂_at_apply]

end CurveData

end Lmap

end Curves
