import RischTragerBronstein.Curves.Infinity
import RischTragerBronstein.Algebraic.QIndep

/-!
# Residue-free Liouville forms on an arbitrary curve are exact

* `deriv_eq_zero_of_aeval`: an element algebraic over the constants is a constant;
* `deriv_eq_zero_of_regular`: a function without poles along all branches (finite and infinite)
  is a constant;
* `curve_second_kind`: if `f = v′ + ∑ cᵢ uᵢ′/uᵢ` on `C⟮x⟯⟮y⟯` and `f dx` has no residue along any
  branch (above every finite point and above infinity), then `f = v′`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential

section SK

variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]

/-- An element algebraic over the constants is a constant. -/
lemma deriv_eq_zero_of_aeval (hC : ∀ c : C, c′ = 0) (u : L) (M0 : C[X]) (hM0 : M0.Monic)
    (h : aeval u M0 = 0) : u′ = 0 := by
  have hint : IsIntegral C u := ⟨M0, hM0, by rwa [← aeval_def]⟩
  set m := minpoly C u with hm
  have hsep : m.Separable := (minpoly.irreducible hint).separable
  have hd := hsep.aeval_derivative_ne_zero (minpoly.aeval C u)
  have h1 := derivation_eval (Differential.deriv (R := L)).toLinearMap.toAddMonoidHom
    (isLeibniz_derivation _) (m.map (algebraMap C L)) u (m.natDegree + 1)
    (natDegree_map_le.trans_lt (Nat.lt_succ_self _))
  have h2 : ((Differential.deriv (R := L)).toLinearMap.toAddMonoidHom
      ((m.map (algebraMap C L)).eval u)) = 0 := by
    show ((m.map (algebraMap C L)).eval u)′ = 0
    rw [eval_map, ← aeval_def, minpoly.aeval, map_zero]
  have h3 : ∀ i, (Differential.deriv (R := L)).toLinearMap.toAddMonoidHom
      ((m.map (algebraMap C L)).coeff i) = 0 := fun i ↦ by
    show ((m.map (algebraMap C L)).coeff i)′ = 0
    rw [coeff_map, deriv_algebraMap, hC, map_zero]
  simp only [h3, zero_mul, Finset.sum_const_zero, zero_add, h2] at h1
  rw [derivative_map, eval_map, ← aeval_def] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_left hd

variable {K : Type*} [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]

namespace CurveData

variable (S : CurveData C L)

/-- **A function without poles is a constant.** -/
lemma deriv_eq_zero_of_regular (hC : ∀ c : C, c′ = 0) (u : C⟮S.x⟯⟮S.y⟯)
    (hfin : S.RegularFinite K u) (hinf : S.RegularInf K u) : (u : L)′ = 0 := by
  obtain ⟨M0, hM0, h⟩ := S.algebraic_of_regular (K := K) u hfin hinf
  exact deriv_eq_zero_of_aeval hC _ M0 hM0 h

/-- **Residue-free Liouville forms are exact.** -/
theorem curve_second_kind (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L)) (f v : L)
    (hf : f ∈ C⟮S.x⟯⟮S.y⟯) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c u : ι → L) (hc : ∀ i ∈ s, (c i)′ = 0) (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, c i * logDeriv (u i))
    (hresF : ∀ (a : K) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      LaurentSeries.res (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a)
        r (S.root_of_mem hl hr) ⟨f, hf⟩ *
          LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) (1 : K))) = 0)
    (hresI : ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      LaurentSeries.res (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN))
        r (S.root_of_mem hl hr) ⟨f, hf⟩ *
          LaurentSeries.derivation (single (-(N : ℤ)) (1 : K))) = 0) :
    f = v′ := by
  obtain ⟨k, d, w, ⟨hd, hw, hind⟩, hsum⟩ := logSum_qindep (C⟮S.x⟯⟮S.y⟯).toSubfield s c u hc
    (fun i hi ↦ ⟨(hu i hi).1, (hu i hi).2⟩)
  have hdC : ∀ j, ∃ dc : C, j < k → d j = algebraMap C L dc := fun j ↦ by
    by_cases hj : j < k
    · obtain ⟨dc, hdc⟩ := hconst (d j) (hd j hj)
      exact ⟨dc, fun _ ↦ hdc.symm⟩
    · exact ⟨0, fun h ↦ absurd h hj⟩
  choose dc hdc using hdC
  set w' : ℕ → L := fun j ↦ if j < k then w j else 1
  have hw' : ∀ j, w' j ≠ 0 ∧ w' j ∈ C⟮S.x⟯⟮S.y⟯ := fun j ↦ by
    by_cases hj : j < k
    · simp only [w', if_pos hj]; exact hw j hj
    · simp only [w', if_neg hj]; exact ⟨one_ne_zero, one_mem _⟩
  have heq' : f = v′ + ∑ j ∈ Finset.range k, algebraMap C L (dc j) * ((w' j)′ / w' j) := by
    rw [heq, hsum]
    congr 1
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' := Finset.mem_range.mp hj
    simp only [w', if_pos hj', hdc j hj']
    rfl
  have key : ∀ (ordj : ℕ → ℤ), ∑ j ∈ Finset.range k, algebraMap C K (dc j) * (ordj j : K) = 0 →
      ∀ j < k, ordj j = 0 := by
    intro ordj h j hj
    have h1 : algebraMap C K (∑ j ∈ Finset.range k, dc j * (ordj j : C)) = 0 := by
      rw [map_sum]; simpa using h
    have h2 : ∑ j ∈ Finset.range k, ((ordj j : ℚ) : L) * d j = 0 := by
      have h3 := congrArg (algebraMap C L)
        ((map_eq_zero_iff _ (algebraMap C K).injective).mp h1)
      rw [map_sum, map_zero] at h3
      rw [← h3]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      rw [hdc j (Finset.mem_range.mp hj), map_mul, map_intCast]
      push_cast; ring
    exact_mod_cast hind (fun j ↦ (ordj j : ℚ)) h2 j hj
  -- every `wⱼ` has order `0` along every branch
  have hzF : ∀ j < k, S.RegularFinite K ⟨w' j, (hw' j).2⟩ := by
    intro j hj a N hN l hl r hr
    have hX : LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) (1 : K)) ≠ 0 := by
      rw [SuperData.derivation_branchX N (Nat.pos_of_ne_zero hN) a]
      exact HahnSeries.single_ne_zero (by exact_mod_cast hN)
    have hres := S.res_liouvilleG _ hX (branchSub N a)
      (branchSub_injective N (Nat.pos_of_ne_zero hN) a) (fun P ↦ by rw [SuperData.branchSub_eq_subst]) hC hx
      r (S.root_of_mem hl hr) (Finset.range k) dc w' (fun j ↦ (hw' j).2) (fun j ↦ (hw' j).1)
      v f hv hf heq'
    rw [hresF a N hN l hl r hr, eq_comm] at hres
    exact (key _ hres j hj).ge
  have hzI : ∀ j < k, S.RegularInf K ⟨w' j, (hw' j).2⟩ := by
    intro j hj N hN l hl r hr
    have hX : LaurentSeries.derivation (single (-(N : ℤ)) (1 : K)) ≠ 0 := by
      rw [SuperData.derivation_infX N]
      refine HahnSeries.single_ne_zero ?_
      simp only [ne_eq, neg_eq_zero, Nat.cast_eq_zero]
      exact hN
    have hres := S.res_liouvilleG _ hX (infSub N)
      (infSub_injective N (Nat.pos_of_ne_zero hN)) (fun P ↦ by rw [SuperData.infSub_eq_subst]) hC hx
      r (S.root_of_mem hl hr) (Finset.range k) dc w' (fun j ↦ (hw' j).2) (fun j ↦ (hw' j).1)
      v f hv hf heq'
    rw [hresI N hN l hl r hr, eq_comm] at hres
    exact (key _ hres j hj).ge
  -- hence every `wⱼ` is a constant and the logarithmic part vanishes
  rw [heq', add_eq_left]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  have hj' := Finset.mem_range.mp hj
  have h0 := S.deriv_eq_zero_of_regular (K := K) hC ⟨w' j, (hw' j).2⟩ (hzF j hj') (hzI j hj')
  simp only at h0
  rw [h0, zero_div, mul_zero]

end CurveData

end SK

end Curves
