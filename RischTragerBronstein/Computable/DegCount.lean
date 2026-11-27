import RischTragerBronstein.Computable.Kronecker
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Algebra.Squarefree.Basic

/-!
# Degrees of the factors of a squarefree polynomial

Let `f ≠ 0` be squarefree over a field and suppose that for each `d ∈ [1, n]` (`n ≥ deg f`) a
polynomial `h_d ≠ 0` is divisible by every irreducible factor of `f` of degree `d`. Then every
divisor `g` of `f` has degree `∑_{d=1}^{n} d c_d` with `d c_d ≤ deg h_d` (`natDegree_of_dvd_sq`).
-/

open Polynomial UniqueFactorizationMonoid

namespace DegCount

variable {K : Type*} [Field K]

open scoped Classical in
theorem natDegree_of_dvd_sq {f g : K[X]} (hf : f ≠ 0) (hsq : Squarefree f) (hg : g ∣ f) (n : ℕ)
    (hn : f.natDegree ≤ n) (m : ℕ → ℕ)
    (hm : ∀ d, 1 ≤ d → d ≤ n → ∃ h : K[X], h ≠ 0 ∧ h.natDegree = m d ∧
      ∀ π : K[X], Irreducible π → π ∣ f → π.natDegree = d → π ∣ h) :
    ∃ c : ℕ → ℕ, (∀ d, 1 ≤ d → d ≤ n → d * c d ≤ m d) ∧
      g.natDegree = ∑ d ∈ Finset.Icc 1 n, d * c d := by
  have hg0 : g ≠ 0 := ne_zero_of_dvd_ne_zero hf hg
  have hgsq : Squarefree g := hsq.squarefree_of_dvd hg
  set S : Finset K[X] := (normalizedFactors g).toFinset with hS
  have hnd : (normalizedFactors g).Nodup := (squarefree_iff_nodup_normalizedFactors hg0).mp hgsq
  have hirr : ∀ π ∈ S, Irreducible π := fun π hπ ↦
    irreducible_of_normalized_factor π (Multiset.mem_toFinset.mp hπ)
  have hdvdg : ∀ π ∈ S, π ∣ g := fun π hπ ↦
    dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hπ)
  have hdeg : ∀ π ∈ S, π.natDegree ∈ Finset.Icc 1 n := fun π hπ ↦ by
    rw [Finset.mem_Icc]
    refine ⟨(hirr π hπ).natDegree_pos, le_trans ?_ hn⟩
    exact natDegree_le_of_dvd ((hdvdg π hπ).trans hg) hf
  have hprod : (∏ π ∈ S, π) = (normalizedFactors g).prod := by
    rw [Finset.prod_eq_multiset_prod, hS, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd,
      Multiset.map_id']
  have hne : ∀ π ∈ S, π ≠ 0 := fun π hπ ↦ (hirr π hπ).ne_zero
  have hgdeg : g.natDegree = ∑ π ∈ S, π.natDegree := by
    have hass : Associated ((∏ π ∈ S, π)) g := by rw [hprod]; exact prod_normalizedFactors hg0
    rw [← natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hass),
      natDegree_prod _ _ (fun π hπ ↦ hne π hπ)]
  refine ⟨fun d ↦ (S.filter fun π ↦ π.natDegree = d).card, fun d hd1 hdn ↦ ?_, ?_⟩
  · obtain ⟨h, hh0, hhm, hh⟩ := hm d hd1 hdn
    set T := S.filter fun π ↦ π.natDegree = d with hT
    have hTd : ∀ π ∈ T, π.natDegree = d := fun π hπ ↦ (Finset.mem_filter.mp hπ).2
    have hTS : ∀ π ∈ T, π ∈ S := fun π hπ ↦ (Finset.mem_filter.mp hπ).1
    have hcop : (T : Set K[X]).Pairwise (Function.onFun IsCoprime id) := by
      intro a ha b hb hab
      have ha' := hTS a ha
      have hb' := hTS b hb
      refine ((hirr a ha').coprime_iff_not_dvd).mpr fun hdvd ↦ hab ?_
      have hass : Associated a b := (hirr a ha').associated_of_dvd (hirr b hb') hdvd
      have ea := normalize_normalized_factor a (Multiset.mem_toFinset.mp ha')
      have eb := normalize_normalized_factor b (Multiset.mem_toFinset.mp hb')
      rw [← ea, ← eb]
      exact normalize_eq_normalize hass.dvd hass.symm.dvd
    have hdv : (∏ π ∈ T, π) ∣ h := Finset.prod_dvd_of_coprime hcop fun π hπ ↦
      hh π (hirr π (hTS π hπ)) ((hdvdg π (hTS π hπ)).trans hg) (hTd π hπ)
    have hle := natDegree_le_of_dvd hdv hh0
    rw [natDegree_prod _ _ (fun π hπ ↦ hne π (hTS π hπ)), hhm] at hle
    have : ∑ π ∈ T, π.natDegree = d * T.card := by
      rw [Finset.sum_congr rfl (fun π hπ ↦ hTd π hπ), Finset.sum_const, smul_eq_mul, mul_comm]
    rw [this] at hle
    exact hle
  · rw [hgdeg, ← Finset.sum_fiberwise_of_maps_to hdeg]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [Finset.sum_congr rfl (fun π hπ ↦ (Finset.mem_filter.mp hπ).2), Finset.sum_const,
      smul_eq_mul, mul_comm]

end DegCount
