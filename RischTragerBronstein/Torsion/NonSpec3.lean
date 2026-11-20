import RischTragerBronstein.Torsion.NonSpec2

/-!
# Non-special base points exist (3): points impose independent conditions in large degree

For `r` admissible fibres with distinct abscissae and `m ≥ r − 1 + δⱼ` for all `j`, evaluation at
the non-chosen points is onto (`evQ_surjective`: Lagrange interpolation in `x` times interpolation
on each fibre), hence **`finrank_kerSp`**: `dim kerSp m = ∑ⱼ (m + 1 − δⱼ) − r (n − 1)`.
-/

open Polynomial Module

namespace Curves

open CPoly Sup GTors

section Surj

variable {K : Type*} [Field K] {n : ℕ} {B : Fin n → K[X][X]} (δ : Fin n → ℕ)

/-- The Lagrange polynomial of `l` for the abscissae of `f`. -/
noncomputable def lagr {r : ℕ} (f : Fin r → AdmFib B) (l : Fin r) : K[X] :=
  Polynomial.C (∏ l' ∈ Finset.univ.erase l, ((f l).x - (f l').x))⁻¹ *
    ∏ l' ∈ Finset.univ.erase l, (X - Polynomial.C (f l').x)

variable {r : ℕ} (f : Fin r → AdmFib B) (hx : Function.Injective fun l ↦ (f l).x)
include hx

lemma lagr_eval_self (l : Fin r) : (lagr f l).eval (f l).x = 1 := by
  rw [lagr, eval_mul, eval_C, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  exact inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun l' hl' ↦
    sub_ne_zero.mpr fun h ↦ (Finset.ne_of_mem_erase hl') (hx h).symm)

lemma lagr_eval_ne (l l' : Fin r) (h : l' ≠ l) : (lagr f l).eval (f l').x = 0 := by
  rw [lagr, eval_mul, eval_prod]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h, Finset.mem_univ l'⟩) ?_)
  simp

omit hx in
lemma natDegree_lagr_le (l : Fin r) : (lagr f l).natDegree ≤ r - 1 := by
  rw [lagr]
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_prod _ _ fun l' _ ↦ X_sub_C_ne_zero _]
  simp [Finset.card_erase_of_mem]

omit hx in
/-- The index set of the non-chosen points. -/
abbrev QIdx (j₀ : Fin r → Fin n) := {q : Fin r × Fin n // q.2 ≠ j₀ q.1}

omit hx in
/-- Evaluation at the non-chosen points. -/
noncomputable def evQ (m : ℕ) (j₀ : Fin r → Fin n) : Vsp K δ m →ₗ[K] (QIdx j₀ → K) :=
  (LinearMap.pi fun q : QIdx j₀ ↦ evPt B (f q.1.1).x ((f q.1.1).ys q.1.2)) ∘ₗ (Vsp K δ m).subtype

/-- **Points impose independent conditions in large degree.** -/
theorem evQ_surjective (m : ℕ) (hm : ∀ j, r - 1 + δ j ≤ m) (j₀ : Fin r → Fin n) :
    Function.Surjective (evQ δ f m j₀) := by
  classical
  intro v
  -- values on each fibre
  have hu := fun l ↦ (f l).exists_vals (fun k ↦ if h : k ≠ j₀ l then v ⟨(l, k), h⟩ else 0)
  choose u hu using hu
  set c : Fin n → K[X] := fun j ↦ ∑ l, Polynomial.C (u l j) * lagr f l with hc
  have hcV : c ∈ Vsp K δ m := by
    rw [mem_Vsp]
    intro j
    rw [mem_degreeLT]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun l _ ↦ ?_
    refine lt_of_le_of_lt degree_le_natDegree ?_
    have := (natDegree_C_mul_le (u l j) (lagr f l)).trans (natDegree_lagr_le f l)
    have := hm j
    exact_mod_cast (by omega : (Polynomial.C (u l j) * lagr f l).natDegree < m + 1 - δ j)
  refine ⟨⟨c, hcV⟩, funext fun q ↦ ?_⟩
  obtain ⟨⟨l0, k⟩, hk⟩ := q
  simp only [evQ, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.pi_apply, evPt_apply]
  have hcl : ∀ j, (c j).eval (f l0).x = u l0 j := fun j ↦ by
    rw [hc, eval_finset_sum, Finset.sum_eq_single l0 (fun l _ hl ↦ by
      rw [eval_mul, eval_C, lagr_eval_ne f hx l l0 (Ne.symm hl), mul_zero]) (by simp),
      eval_mul, eval_C, lagr_eval_self f hx, mul_one]
  simp only [hcl]
  rw [hu l0 k, dif_pos hk]

/-- **The dimension of the kernel space in large degree.** -/
theorem finrank_kerSp (m : ℕ) (hm : ∀ j, r - 1 + δ j ≤ m) (j₀ : Fin r → Fin n) :
    finrank K (kerSp δ m r f j₀) + r * (n - 1) = ∑ j, (m + 1 - δ j) := by
  classical
  have h1 := LinearMap.finrank_range_add_finrank_ker (evQ δ f m j₀)
  rw [LinearMap.range_eq_top.mpr (evQ_surjective δ f hx m hm j₀), finrank_top,
    Module.finrank_fintype_fun_eq_card, finrank_Vsp] at h1
  have hcard : Fintype.card (QIdx j₀) = r * (n - 1) := by
    rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun l k ↦ k ≠ j₀ l),
      Fintype.card_sigma]
    simp [Fintype.card_subtype_compl]
  have hker : finrank K (LinearMap.ker (evQ δ f m j₀)) = finrank K (kerSp δ m r f j₀) := by
    have he : LinearMap.ker (evQ δ f m j₀) =
        Submodule.comap (Vsp K δ m).subtype (kerSp δ m r f j₀) := by
      ext c
      simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, mem_kerSp]
      constructor
      · intro h
        refine ⟨c.2, fun l k hk ↦ ?_⟩
        have := congrFun h ⟨(l, k), hk⟩
        simpa [evQ] using this
      · rintro ⟨-, h⟩
        funext q
        simpa [evQ] using h q.1.1 q.1.2 q.2
    rw [he]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_left)
  omega

end Surj

end Curves
