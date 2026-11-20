import RischTragerBronstein.Torsion.IBExist2
import RischTragerBronstein.Curves.PoleBounds

/-!
# Integral bases exist (3): bases locally integral and independent at finitely many points

**`exists_finite_basis`**: for finitely many branch systems `σ` above distinct points of `C`
(coefficients in `C`), there is a basis `wⱼ = Bⱼ/D` (`w₀ = 1`, `deg_y Bⱼ < n`, `det [Bⱼ,ᵢ] ≠ 0`,
`D` and `det` vanishing only at the given points) which is regular along every `σ` and whose
reductions modulo `x − a` along every `σ` are independent (`IndepAt`). The proof improves the power
basis (`stepB`) while some reduction is dependent; the total local index
`∑_σ mult_a (discⁿ det B) − n mult_a D` (a natural number by `index_bound`) drops by one each time.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Loop

variable {C L : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]

namespace CurveData

variable {S : CurveData C L}

lemma lowerBd_mul_inv_single {z : LaurentSeries C} {N : ℕ} (hz : LowerBd z N) :
    LowerBd (z * (single (N : ℤ) (1 : C))⁻¹) 0 := by
  have hs : single (N : ℤ) (1 : C) ≠ 0 := single_ne_zero one_ne_zero
  have h := hz.mul (lowerBd_inv _ hs)
  rw [order_single one_ne_zero] at h
  simpa using h

lemma order_unit_X (d : C) (hd : d ≠ 0) (N : ℕ) (hN : 0 < N) :
    (HahnSeries.C d + single (N : ℤ) (1 : C)).order = 0 := by
  have h0 : (HahnSeries.C d + single (N : ℤ) (1 : C)).coeff 0 = d := by
    rw [HahnSeries.coeff_add, HahnSeries.C_apply, coeff_single, coeff_single, if_pos rfl,
      if_neg (by omega), add_zero]
  have hne : HahnSeries.C d + single (N : ℤ) (1 : C) ≠ 0 := fun h ↦ hd (by rw [← h0, h]; rfl)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [h0]; exact hd)) ?_
  exact le_order_of_lowerBd _ hne 0 ((lowerBd_C d).add ((lowerBd_single _ _).mono (by omega)))

lemma ev_polyF_C (σ : S.LocSys) (k : Fin S.F.natDegree) (c : C) :
    σ.ev k (S.polyF (Polynomial.C c)) = HahnSeries.C c := by
  rw [LocSys.ev, S.embG_polyF, bs_C]; rfl

lemma ev_stepB_eq (τ : S.LocSys) (k : Fin S.F.natDegree) (B : Fin S.F.natDegree → C[X][X])
    (D : C[X]) (a : C) (c : Fin S.F.natDegree → C) (j₀ : Fin S.F.natDegree) :
    τ.ev k (S.fnWQ (stepB B a c j₀ j₀) (stepD D a)) =
      (∑ l, (HahnSeries.C (c l) : LaurentSeries C) * τ.ev k (S.fnWQ (B l) D)) *
        (τ.ev k (S.polyF (X - Polynomial.C a)))⁻¹ := by
  rw [fnWQ_stepB_eq]
  unfold LocSys.ev
  rw [map_mul, map_inv₀, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_mul, S.embG_polyF, bs_C]
  rfl

/-- **Regularity of the new element along the improving system.** -/
lemma regAt_step_self (σ : S.LocSys) (B : Fin S.F.natDegree → C[X][X]) (D : C[X])
    (hreg : RegAt σ B D) (c : Fin S.F.natDegree → C) (j₀ : Fin S.F.natDegree)
    (hdep : ∀ k, LowerBd (∑ j, HahnSeries.C (c j) * σ.ev k (S.fnWQ (B j) D)) σ.N) :
    RegAt σ (stepB B σ.a c j₀) (stepD D σ.a) := by
  intro j k
  by_cases hj : j = j₀
  · subst hj
    rw [ev_stepB_eq, polyF_X_sub, sub_self, map_zero, zero_add]
    exact lowerBd_mul_inv_single (hdep k)
  · rw [fnWQ_stepB_ne B D σ.a c j₀ j hj]; exact hreg j k

/-- **Regularity along systems above other points.** -/
lemma regAt_step_other (σ τ : S.LocSys) (hστ : τ.a ≠ σ.a) (B : Fin S.F.natDegree → C[X][X])
    (D : C[X]) (hreg : RegAt τ B D) (c : Fin S.F.natDegree → C) (j₀ : Fin S.F.natDegree) :
    RegAt τ (stepB B σ.a c j₀) (stepD D σ.a) := by
  intro j k
  by_cases hj : j = j₀
  · subst hj
    rw [ev_stepB_eq, polyF_X_sub]
    have hd : τ.a - σ.a ≠ 0 := sub_ne_zero.mpr hστ
    have ho := order_unit_X _ hd τ.N τ.hN
    have hu : HahnSeries.C (τ.a - σ.a) + single (τ.N : ℤ) (1 : C) ≠ 0 := by
      intro h
      have h0 : (HahnSeries.C (τ.a - σ.a) + single (τ.N : ℤ) (1 : C)).coeff 0 = τ.a - σ.a := by
        rw [HahnSeries.coeff_add, HahnSeries.C_apply, coeff_single, coeff_single, if_pos rfl,
          if_neg (by have := τ.hN; omega), add_zero]
      rw [h] at h0
      exact hd (by rw [← h0]; rfl)
    have hinv := lowerBd_inv _ hu
    rw [ho, neg_zero] at hinv
    have hsum : LowerBd (∑ l, HahnSeries.C (c l) * τ.ev k (S.fnWQ (B l) D)) 0 :=
      lowerBd_sum _ _ fun l _ ↦ ((lowerBd_C (c l)).mul (hreg l k)).mono (by simp)
    exact (hsum.mul hinv).mono (by simp)
  · rw [fnWQ_stepB_ne B D σ.a c j₀ j hj]; exact hreg j k

/-- The local index at `σ`. -/
noncomputable def idx (σ : S.LocSys) (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) : ℕ :=
  (S.discR ^ S.F.natDegree * (coeffMat B).det).rootMultiplicity σ.a -
    S.F.natDegree * D.rootMultiplicity σ.a

open Classical in
lemma mult_stepB (B : Fin S.F.natDegree → C[X][X]) (hdet : (coeffMat B).det ≠ 0) (a : C)
    (c : Fin S.F.natDegree → C) (j₀ : Fin S.F.natDegree) (hc : c j₀ ≠ 0) (b : C) :
    (S.discR ^ S.F.natDegree * (coeffMat (stepB B a c j₀)).det).rootMultiplicity b =
      (S.discR ^ S.F.natDegree * (coeffMat B).det).rootMultiplicity b +
        if b = a then S.F.natDegree - 1 else 0 := by
  classical
  have hd : S.discR ^ S.F.natDegree ≠ 0 := pow_ne_zero _ S.discR_ne_zero
  have hC : Polynomial.C (c j₀) ≠ 0 := Polynomial.C_ne_zero.mpr hc
  rw [det_stepB, show S.discR ^ S.F.natDegree * ((X - Polynomial.C a) ^ (S.F.natDegree - 1) *
      (Polynomial.C (c j₀) * (coeffMat B).det)) = (X - Polynomial.C a) ^ (S.F.natDegree - 1) *
      (Polynomial.C (c j₀) * (S.discR ^ S.F.natDegree * (coeffMat B).det)) by ring,
    rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero a))
      (mul_ne_zero hC (mul_ne_zero hd hdet))),
    rootMultiplicity_mul (mul_ne_zero hC (mul_ne_zero hd hdet)), rootMultiplicity_C, zero_add]
  by_cases h : b = a
  · subst h; rw [rootMultiplicity_X_sub_C_pow, if_pos rfl]; omega
  · rw [if_neg h, rootMultiplicity_eq_zero (by simp [IsRoot, eval_pow, sub_eq_zero, h])]
    omega

open Classical in
lemma mult_stepD (D : C[X]) (hD : D ≠ 0) (a b : C) :
    (stepD D a).rootMultiplicity b = D.rootMultiplicity b + if b = a then 1 else 0 := by
  classical
  rw [stepD, rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero a) hD), rootMultiplicity_X_sub_C]
  split_ifs <;> subst_vars <;> simp_all <;> omega

/-- The invariants kept by the improvement. -/
structure FinGood (A : List S.LocSys) (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) : Prop where
  deg : ∀ j, (B j).natDegree < S.F.natDegree
  det : (coeffMat B).det ≠ 0
  hD : D ≠ 0
  reg : ∀ σ ∈ A, RegAt σ B D
  one : ∀ h : 0 < S.F.natDegree, B ⟨0, h⟩ = Polynomial.C D
  roots : ∀ b, (D * (coeffMat B).det).IsRoot b → ∃ σ ∈ A, σ.a = b
  split : Multiset.card D.roots = D.natDegree
  monic : D.Monic
  detsplit : Multiset.card (coeffMat B).det.roots = (coeffMat B).det.natDegree

lemma list_sum_lt {α : Type*} (l : List α) (f g : α → ℕ) (hle : ∀ x ∈ l, g x ≤ f x) (x₀ : α)
    (hx₀ : x₀ ∈ l) (hlt : g x₀ < f x₀) : (l.map g).sum < (l.map f).sum := by
  induction l with
  | nil => simp at hx₀
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hl : (l.map g).sum ≤ (l.map f).sum :=
      List.sum_le_sum fun x hx ↦ hle x (List.mem_cons_of_mem _ hx)
    rcases List.mem_cons.mp hx₀ with rfl | h
    · have := hle x₀ List.mem_cons_self; omega
    · have := ih (fun x hx ↦ hle x (List.mem_cons_of_mem _ hx)) h
      have := hle a List.mem_cons_self; omega

lemma ev_one (σ : S.LocSys) (k : Fin S.F.natDegree) (D : C[X]) (hD : D ≠ 0) :
    σ.ev k (S.fnWQ (Polynomial.C D) D) = 1 := by
  rw [LocSys.ev, S.embG_fnWQ, Polynomial.map_C, eval_C]
  exact mul_inv_cancel₀ ((map_ne_zero_iff _ (branchSub_injective _ σ.hN _)).mpr hD)

lemma coeffMat_pow : coeffMat (fun j : Fin S.F.natDegree ↦ (X : C[X][X]) ^ (j : ℕ)) = 1 := by
  refine Matrix.ext fun i j ↦ ?_
  simp only [coeffMat, Matrix.of_apply, coeff_X_pow, Matrix.one_apply, Fin.ext_iff]

/-- The power basis `1, y, …, yⁿ⁻¹`. -/
lemma finGood_pow (A : List S.LocSys) :
    FinGood A (fun j : Fin S.F.natDegree ↦ (X : C[X][X]) ^ (j : ℕ)) 1 := by
  refine ⟨fun j ↦ ?_, by rw [coeffMat_pow, Matrix.det_one]; exact one_ne_zero, one_ne_zero,
    fun σ _ j k ↦ ?_, fun h ↦ by simp, fun b hb ↦ ?_, by simp, monic_one,
    by rw [coeffMat_pow, Matrix.det_one]; simp⟩
  · rw [natDegree_X_pow]; exact j.2
  · rw [LocSys.ev, S.embG_fnWQ, Polynomial.map_pow, Polynomial.map_X, eval_pow, eval_X, map_one,
      inv_one, mul_one]
    simpa using (σ.hr k).pow (j : ℕ)
  · rw [coeffMat_pow, Matrix.det_one, one_mul] at hb
    exact absurd hb (by simp)

/-- **Integral bases at finitely many points.** -/
theorem exists_finite_basis (A : List S.LocSys) (hA : (A.map LocSys.a).Nodup) :
    ∃ (B : Fin S.F.natDegree → C[X][X]) (D : C[X]), FinGood A B D ∧ ∀ σ ∈ A, IndepAt σ B D := by
  classical
  have hn : 0 < S.F.natDegree := Nat.pos_of_ne_zero S.natDegree_F_ne_zero
  suffices key : ∀ m (B : Fin S.F.natDegree → C[X][X]) (D : C[X]), FinGood A B D →
      (A.map fun σ ↦ idx σ B D).sum = m →
      ∃ (B : Fin S.F.natDegree → C[X][X]) (D : C[X]), FinGood A B D ∧ ∀ σ ∈ A, IndepAt σ B D from
    key _ _ _ (finGood_pow A) rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro B D hG hm
  by_cases hall : ∀ σ ∈ A, IndepAt σ B D
  · exact ⟨B, D, hG, hall⟩
  push Not at hall
  obtain ⟨σ, hσ, hnot⟩ := hall
  simp only [IndepAt, not_forall] at hnot
  obtain ⟨c, hdep, hc⟩ := hnot
  -- an index `j₀ ≠ 0` with `c j₀ ≠ 0`
  obtain ⟨j₀, hj₀0, hcj₀⟩ : ∃ j₀ : Fin S.F.natDegree, (j₀ : ℕ) ≠ 0 ∧ c j₀ ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hc
    have h0 : c ⟨0, hn⟩ = 0 := by
      have hk := hdep ⟨0, hn⟩
      rw [Finset.sum_eq_single ⟨0, hn⟩ (fun j _ hj ↦ by
        rw [hno j (fun h ↦ hj (Fin.ext h)), map_zero, zero_mul]) (by simp),
        hG.one hn, ev_one σ _ D hG.hD, mul_one] at hk
      have := hk 0 (by exact_mod_cast σ.hN)
      rwa [HahnSeries.C_apply, coeff_single, if_pos rfl] at this
    funext j
    by_cases hj : (j : ℕ) = 0
    · have : j = ⟨0, hn⟩ := Fin.ext hj
      rw [this, h0]; rfl
    · exact hno j hj
  set B' := stepB B σ.a c j₀ with hB'
  set D' := stepD D σ.a with hD'
  have hdet' : (coeffMat B').det ≠ 0 := by
    rw [hB', det_stepB]
    exact mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _))
      (mul_ne_zero (Polynomial.C_ne_zero.mpr hcj₀) hG.det)
  have hreg' : ∀ τ ∈ A, RegAt τ B' D' := by
    intro τ hτ
    by_cases hτσ : τ.a = σ.a
    · have : τ = σ := List.inj_on_of_nodup_map hA hτ hσ hτσ
      subst this
      exact regAt_step_self τ B D (hG.reg τ hτ) c j₀ hdep
    · exact regAt_step_other σ τ hτσ B D (hG.reg τ hτ) c j₀
  have hG' : FinGood A B' D' := by
    refine ⟨stepB_deg hG.deg σ.a c j₀, hdet', stepD_ne_zero hG.hD σ.a, hreg', fun h ↦ ?_,
      fun b hb ↦ ?_, ?_, (monic_X_sub_C _).mul hG.monic, ?_⟩
    · have hne : (⟨0, h⟩ : Fin S.F.natDegree) ≠ j₀ := fun e ↦ hj₀0 (by rw [← e])
      rw [hB', stepB, if_neg hne, hG.one h, hD', stepD, Polynomial.C_mul]
    · rw [hB', det_stepB, hD', stepD] at hb
      by_cases hba : b = σ.a
      · exact ⟨σ, hσ, hba.symm⟩
      · refine hG.roots b ?_
        simp only [IsRoot, eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hb ⊢
        have hb0 : b - σ.a ≠ 0 := sub_ne_zero.mpr hba
        have e : eval b D * eval b (coeffMat B).det *
            ((b - σ.a) * (b - σ.a) ^ (S.F.natDegree - 1) * c j₀) = 0 := by
          rw [← hb]; ring
        exact (mul_eq_zero.mp e).resolve_right
          (mul_ne_zero (mul_ne_zero hb0 (pow_ne_zero _ hb0)) hcj₀)
    · rw [hD', stepD, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) hG.hD), roots_X_sub_C,
        Multiset.card_add, Multiset.card_singleton, hG.split,
        natDegree_mul (X_sub_C_ne_zero _) hG.hD, natDegree_X_sub_C, add_comm]
    · have hC : Polynomial.C (c j₀) ≠ 0 := Polynomial.C_ne_zero.mpr hcj₀
      have hp : (X - Polynomial.C σ.a) ^ (S.F.natDegree - 1) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero _)
      rw [hB', det_stepB, roots_mul (mul_ne_zero hp (mul_ne_zero hC hG.det)),
        roots_mul (mul_ne_zero hC hG.det), roots_C, roots_pow, roots_X_sub_C, Multiset.card_add,
        Multiset.card_add, Multiset.card_nsmul, Multiset.card_singleton, Multiset.card_zero,
        hG.detsplit, natDegree_mul hp (mul_ne_zero hC hG.det), natDegree_mul hC hG.det,
        natDegree_C, natDegree_pow, natDegree_X_sub_C]
  -- the index drops at `σ` and nowhere else
  have hchange : ∀ τ ∈ A, idx τ B' D' + (if τ.a = σ.a then 1 else 0) = idx τ B D := by
    intro τ hτ
    have h1 := mult_stepB B hG.det σ.a c j₀ hcj₀ τ.a
    have h2 := mult_stepD D hG.hD σ.a τ.a
    simp only [idx]
    simp only [← hB', ← hD'] at h1 h2
    rw [h1, h2]
    by_cases hτσ : τ.a = σ.a
    · simp only [if_pos hτσ]
      have hb := S.index_bound B' (stepB_deg hG.deg σ.a c j₀) hdet' D' (stepD_ne_zero hG.hD _)
        τ.a τ.N τ.hN τ.r τ.hs τ.hr (fun j k ↦ hreg' τ hτ j k)
      rw [show (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (B' j).coeff i) = coeffMat B' from rfl,
        h1, h2] at hb
      simp only [if_pos hτσ] at hb
      have : 0 < S.F.natDegree := hn
      rw [Nat.mul_add, Nat.mul_one] at hb ⊢
      omega
    · simp only [if_neg hτσ]; simp
  have hlt : (A.map fun τ ↦ idx τ B' D').sum < m := by
    rw [← hm]
    refine list_sum_lt A _ _ (fun τ hτ ↦ by have := hchange τ hτ; omega) σ hσ ?_
    have := hchange σ hσ
    rw [if_pos rfl] at this
    omega
  exact ih _ hlt B' D' hG' rfl

end CurveData

end Loop

end Curves
