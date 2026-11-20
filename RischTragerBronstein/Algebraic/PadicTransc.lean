import RischTragerBronstein.Computable.RatFuncC
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.MetricSpace.Perfect

/-!
# Transcendental `p`-adic integers with a prescribed residue

`ℤ_p` is uncountable (a nonempty perfect set in a complete metric space contains a Cantor set), so
for a countable field `K` embedded in `ℚ_p` by `φ`, every class `c + pℤ_p` contains an element
transcendental over `φ(K)` (`exists_transc`): the roots of the nonzero polynomials over `K` form a
countable set.

This is how function fields `K(t)` are embedded in `ℚ_p` with a prescribed reduction of `t`.
-/

open Polynomial

namespace Sup

variable {p : ℕ} [hp : Fact p.Prime]

lemma padicInt_perfect : Perfect (Set.univ : Set ℤ_[p]) := by
  refine ⟨isClosed_univ, ?_⟩
  rw [preperfect_iff_nhds]
  intro x _ U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp1)
  refine ⟨x + (p : ℤ_[p]) ^ n, ⟨hball ?_, Set.mem_univ _⟩, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, PadicInt.norm_p_pow]
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact hn
  · intro h
    have h0 : (p : ℤ_[p]) ^ n = 0 := by
      have := congrArg (fun z ↦ z - x) h
      simpa using this
    exact pow_ne_zero n (by exact_mod_cast hp.out.ne_zero : (p : ℤ_[p]) ≠ 0) h0

lemma not_countable_nat_bool : ¬ Countable (ℕ → Bool) := by
  classical
  intro h
  have : Countable (Set ℕ) := Function.Injective.countable
    (f := fun s : Set ℕ ↦ fun n ↦ decide (n ∈ s)) (by
      intro s t hst
      ext n
      have := congrFun hst n
      simpa using this)
  obtain ⟨f, hf⟩ := exists_surjective_nat (Set ℕ)
  exact Function.cantor_surjective f hf

lemma padicInt_not_countable : ¬ Countable ℤ_[p] := by
  intro hc
  obtain ⟨f, -, -, hf⟩ := padicInt_perfect.exists_nat_bool_injection ⟨(0 : ℤ_[p]), Set.mem_univ _⟩
  exact not_countable_nat_bool hf.countable

/-- **A transcendental element in every residue class** `c + pℤ_p`, over a countable field. -/
theorem exists_transc {K : Type*} [Field K] [Countable K] (φ : K →+* ℚ_[p]) (c : ℤ_[p]) :
    ∃ y : ℤ_[p], RFC.Transc φ ((c + (p : ℤ_[p]) * y : ℤ_[p]) : ℚ_[p]) := by
  classical
  -- the bad set: roots of nonzero polynomials, indexed by coefficient lists
  set B : Set ℚ_[p] := ⋃ l : List K,
    {z | CPoly.toPoly l ≠ 0 ∧ (CPoly.toPoly l).eval₂ φ z = 0} with hB
  have hBc : B.Countable := by
    refine Set.countable_iUnion fun l ↦ ?_
    by_cases hl : CPoly.toPoly l = 0
    · simp [hl]
    · refine (Set.Finite.countable ?_)
      refine ((CPoly.toPoly l).map φ).roots.toFinset.finite_toSet.subset fun z hz ↦ ?_
      obtain ⟨-, hz⟩ := hz
      have hm : (CPoly.toPoly l).map φ ≠ 0 := (Polynomial.map_ne_zero_iff φ.injective).mpr hl
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      rw [mem_roots hm, IsRoot, eval_map]
      exact hz
  by_contra hne
  push Not at hne
  apply padicInt_not_countable (p := p)
  -- `y ↦ c + p y` maps `ℤ_p` injectively into `B`
  have hinj : Function.Injective fun y : ℤ_[p] ↦ ((c + (p : ℤ_[p]) * y : ℤ_[p]) : ℚ_[p]) := by
    intro y y' h
    have h1 : (c + (p : ℤ_[p]) * y : ℤ_[p]) = c + p * y' := Subtype.ext h
    have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    exact mul_left_cancel₀ hp0 (add_left_cancel h1)
  have hmem : ∀ y : ℤ_[p], ((c + (p : ℤ_[p]) * y : ℤ_[p]) : ℚ_[p]) ∈ B := fun y ↦ by
    have h := hne y
    unfold RFC.Transc at h
    push Not at h
    obtain ⟨P, hP, hP0⟩ := h
    refine Set.mem_iUnion.mpr ⟨(List.range (P.natDegree + 1)).map P.coeff, ?_⟩
    have hPl : CPoly.toPoly ((List.range (P.natDegree + 1)).map P.coeff) = P := by
      ext i
      rw [CPoly.coeff_toPoly]
      by_cases hi : i < P.natDegree + 1
      · simp [List.getD_eq_getElem?_getD, hi]
      · rw [List.getD_eq_default _ _ (by simp; omega)]
        exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
    exact ⟨by rw [hPl]; exact hP, by rw [hPl]; exact hP0⟩
  have := hBc.to_subtype
  exact Function.Injective.countable (f := fun y ↦ (⟨_, hmem y⟩ : B))
    (by
      intro a b h
      have h2 : ((c + (p : ℤ_[p]) * a : ℤ_[p]) : ℚ_[p]) = ((c + (p : ℤ_[p]) * b : ℤ_[p]) : ℚ_[p]) :=
        congrArg (fun w : B ↦ (w : ℚ_[p])) h
      exact hinj h2)

end Sup
