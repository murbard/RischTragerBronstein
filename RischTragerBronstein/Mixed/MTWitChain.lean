import RischTragerBronstein.Mixed.MTWit

/-!
# The witnesses of the chain and of the Risch equations

* `mchainW_sound`: the list returned by `mchainW` is a solution `P₀ = 0, P₁, …, Pⱼ₊₁` of the
  recurrence `Pᵢ′ + (i + 1) η Pᵢ₊₁ = aᵢ`, `Pⱼ₊₁` the starting value up to a rational, `P₁ = Q₁`;
* `rdeSolM_sound`: a returned `y` solves `y′ + h′ y = f`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable (m : ℕ) (h : T.Tr m) (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h) (paramLimC Fc ks lv m))
include hlim

/-- **Soundness of one step** with its constant. -/
lemma mchainStepW_sound (η a Q : LC m) (j : ℕ) (Q' : LC m) (γ : ℚ)
    (hs : mchainStepW Fc ks lv m η a Q j = some (Q', γ)) :
    ((T.MP m h).sem Q')′ + (γ : T.F m) * (T.MP m h).sem η =
      (T.MP m h).sem (mchainRHS Fc ks m η a Q j) := by
  set M := T.MP m h
  obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp hs
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hr0 := List.find?_some hr
  simp only [decide_eq_true_eq] at hr0
  have hmem := List.mem_of_find?_eq_some hr
  have hsd := hlim.sound _ r hmem
  rw [sQ] at hsd
  simp only [List.length_cons, List.length_nil, zero_add, Finset.sum_range_succ,
    Finset.range_one, Finset.sum_singleton, List.getD_cons_zero, List.getD_cons_succ] at hsd
  set r0 := r.1.getD 0 0
  set r1 := r.1.getD 1 0
  have hq : (r0 : T.F m) ≠ 0 := by exact_mod_cast hr0
  rw [M.sem_mul, T.sem_mcst, Derivation.leibniz, T.deriv_ratCast, hsd]
  simp only [smul_eq_mul, mul_zero, add_zero]
  push_cast
  field_simp
  ring

/-- **Soundness of the chain, with the solution.** -/
theorem mchainW_sound (η : LC m) (Λ : GPoly (LC m)) :
    ∀ (j : ℕ) (Q R : LC m) (Pl : GPoly (LC m)), mchainW Fc ks lv m η Λ j Q = some (R, Pl) →
      Pl.length = j + 2 ∧
      (∀ i, 1 ≤ i → i ≤ j → ((T.MP m h).sem (Pl.getD i (MO Fc ks m).zero))′ +
          ((i + 1 : ℕ) : T.F m) * (T.MP m h).sem η *
            (T.MP m h).sem (Pl.getD (i + 1) (MO Fc ks m).zero) =
          (T.MP m h).sem (Λ.getD i (MO Fc ks m).zero)) ∧
      (∃ q : ℚ, (T.MP m h).sem (Pl.getD (j + 1) (MO Fc ks m).zero) = (T.MP m h).sem Q + q) ∧
      (T.MP m h).sem (Pl.getD 1 (MO Fc ks m).zero) = (T.MP m h).sem R ∧
      (T.MP m h).sem (Pl.getD 0 (MO Fc ks m).zero) = 0 := by
  set M := T.MP m h
  set z := (MO Fc ks m).zero
  intro j
  induction j with
  | zero =>
    intro Q R Pl hc
    simp only [mchainW, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    refine ⟨rfl, fun i h1 h2 ↦ by omega, ⟨0, by simp⟩, rfl, M.sem_zero⟩
  | succ j ih =>
    intro Q R Pl hc
    simp only [mchainW] at hc
    obtain ⟨p, hp, hR⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨⟨R0, Pl0⟩, hR0, he⟩ := Option.map_eq_some_iff.mp hR
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hlen, hrec, ⟨q, hq⟩, hP1, hP0⟩ := ih p.1 R0 Pl0 hR0
    have hγ := T.mchainStepW_sound m h hlim η _ Q (j + 1) p.1 p.2 hp
    rw [T.sem_mchainRHS] at hγ
    have hlt : ∀ i, i < j + 2 → (Pl0 ++ [(MO Fc ks m).add Q (mcst Fc ks m (p.2 / (j + 2 : ℕ)))]).getD
        i z = Pl0.getD i z := fun i hi ↦ by
      rw [List.getD_append _ _ _ _ (by omega)]
    have htop : (Pl0 ++ [(MO Fc ks m).add Q (mcst Fc ks m (p.2 / (j + 2 : ℕ)))]).getD (j + 2) z =
        (MO Fc ks m).add Q (mcst Fc ks m (p.2 / (j + 2 : ℕ))) := by
      rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
      rfl
    have htopv : M.sem ((MO Fc ks m).add Q (mcst Fc ks m (p.2 / (j + 2 : ℕ)))) =
        M.sem Q + ((p.2 / (j + 2 : ℕ) : ℚ) : T.F m) := by
      rw [M.sem_add, T.sem_mcst]
    refine ⟨by simp [hlen], fun i h1 h2 ↦ ?_, ⟨p.2 / (j + 2 : ℕ), by rw [htop, htopv]⟩,
      by rw [hlt 1 (by omega)]; exact hP1, by rw [hlt 0 (by omega)]; exact hP0⟩
    by_cases hij : i ≤ j
    · rw [hlt i (by omega), hlt (i + 1) (by omega)]
      exact hrec i h1 hij
    · have hi : i = j + 1 := by omega
      subst hi
      rw [hlt (j + 1) (by omega), htop, htopv, hq, Derivation.map_add, T.deriv_ratCast, add_zero]
      have hj2 : ((j + 2 : ℕ) : T.F m) ≠ 0 := by exact_mod_cast (by omega : j + 2 ≠ 0)
      have hγ' : (M.sem p.1)′ = M.sem (Λ.getD (j + 1) z) -
          ((j + 1 + 1 : ℕ) : T.F m) * M.sem η * M.sem Q - (p.2 : T.F m) * M.sem η := by
        rw [← hγ]; ring
      rw [hγ']
      push_cast at hj2 ⊢
      field_simp
      ring

omit hlim in
/-- **Soundness of a Risch-equation solution.** -/
lemma rdeSolM_sound
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h) ((T.MP m h).sem (fCode (MO Fc ks m) fr))
        (prdeC Fc ks lv m fr))
    (hc f y : LC m) (hy : rdeSolM Fc ks lv m hc f = some y) :
    ((T.MP m h).sem y)′ + ((T.MP m h).sem hc)′ * (T.MP m h).sem y = (T.MP m h).sem f := by
  classical
  set M := T.MP m h
  have hs : RdeSpecK (algebraMap Cc (T.F m)) M (M.sem hc)′ (prdeC Fc ks lv m ⟨hc, []⟩) := by
    have := hrde ⟨hc, []⟩ (fun cw hcw ↦ by simp at hcw)
    rwa [sem_fCode, logSumV, List.map_nil, List.sum_nil, add_zero] at this
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hy
  have hr0 := List.find?_some hr
  simp only [decide_eq_true_eq] at hr0
  have hsd := hs.sound [f] r (List.mem_of_find?_eq_some hr)
  rw [sQ] at hsd
  simp only [List.length_cons, List.length_nil, zero_add, Finset.range_one,
    Finset.sum_singleton, List.getD_cons_zero] at hsd
  have hq : ((r.1.getD 0 0 : ℚ) : T.F m) ≠ 0 := by exact_mod_cast hr0
  rw [M.sem_mul, T.sem_mcst, Derivation.leibniz, T.deriv_ratCast]
  simp only [smul_eq_mul, mul_zero, add_zero]
  rw [Rat.cast_inv]
  field_simp
  linear_combination hsd

end MTower

end Curves.MT
