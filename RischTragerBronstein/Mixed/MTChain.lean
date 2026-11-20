import RischTragerBronstein.Mixed.MTTransfer

/-!
# Mixed towers over a curve: the limited-integration chain below a logarithm

The polynomial part `∑ aⱼ tₘʲ` of an integrand at a logarithmic level `m + 1` (`tₘ′ = η`) is
handled top down: `Qⱼ′ + γ η = aⱼ − (j + 1) η Qⱼ₊₁` (`Q_{d+1} = 0`), each step solved by
parametric limited integration `paramLimC m` on `[aⱼ − (j + 1) η Qⱼ₊₁, η]` (a returned solution
with non-zero first parameter). The port of `LTChain` to mixed towers.

* `mchain_sound`: given the specification of `paramLimC m`;
* `mchain_complete`: given moreover that `η` has no antiderivative at level `m`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- `a − (j + 1) η Q` at level `m`. -/
def mchainRHS (m : ℕ) (η a Q : LC m) (j : ℕ) : LC m :=
  (MO Fc ks m).add a ((MO Fc ks m).neg
    ((MO Fc ks m).mul ((MO Fc ks m).mul ((MO Fc ks m).natCast (j + 1)) η) Q))

/-- One step of the chain: a solution `Q'` of `Q'′ + γ η = a − (j + 1) η Q`. -/
def mchainStep (m : ℕ) (η a Q : LC m) (j : ℕ) : Option (LC m) :=
  ((paramLimC Fc ks lv m [mchainRHS Fc ks m η a Q j, η]).find?
    fun r ↦ decide (r.1.getD 0 0 ≠ 0)).map
    fun r ↦ (MO Fc ks m).mul (mcst Fc ks m (r.1.getD 0 0)⁻¹) r.2

/-- The chain from index `j` down to `1`, starting from `Qⱼ₊₁ = Q`; returns `Q₁`. -/
def mchain (m : ℕ) (η : LC m) (Λ : GPoly (LC m)) : ℕ → LC m → Option (LC m)
  | 0, Q => some Q
  | j + 1, Q => (mchainStep Fc ks lv m η (Λ.getD (j + 1) (MO Fc ks m).zero) Q (j + 1)).bind
      (mchain m η Λ j)

/-- The constant term `a₀ − η Q₁`. -/
def mconst (m : ℕ) (η : LC m) (Λ : GPoly (LC m)) (Q1 : LC m) : LC m :=
  (MO Fc ks m).add (Λ.getD 0 (MO Fc ks m).zero) ((MO Fc ks m).neg ((MO Fc ks m).mul η Q1))

universe u

variable {Fc ks lv} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma sem_mchainRHS (m : ℕ) (h : T.Tr m) (η a Q : LC m) (j : ℕ) :
    (T.MP m h).sem (mchainRHS Fc ks m η a Q j) = (T.MP m h).sem a -
      ((j + 1 : ℕ) : T.F m) * (T.MP m h).sem η * (T.MP m h).sem Q := by
  rw [mchainRHS, CField.sem_add, CField.sem_neg, CField.sem_mul, CField.sem_mul,
    CField.sem_natCast, sub_eq_add_neg]

lemma sem_mconst (m : ℕ) (h : T.Tr m) (η : LC m) (Λ : GPoly (LC m)) (Q1 : LC m) :
    (T.MP m h).sem (mconst Fc ks m η Λ Q1) =
      (T.MP m h).sem (Λ.getD 0 (MO Fc ks m).zero) - (T.MP m h).sem η * (T.MP m h).sem Q1 := by
  rw [mconst, CField.sem_add, CField.sem_neg, CField.sem_mul, sub_eq_add_neg]

variable (m : ℕ) (h : T.Tr m) (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h) (paramLimC Fc ks lv m))
include hlim

/-- **Soundness of one step.** -/
lemma mchainStep_sound (η a Q Q' : LC m) (j : ℕ) (hs : mchainStep Fc ks lv m η a Q j = some Q') :
    ∃ γ : ℚ, ((T.MP m h).sem Q')′ + (γ : T.F m) * (T.MP m h).sem η =
      (T.MP m h).sem (mchainRHS Fc ks m η a Q j) := by
  set M := T.MP m h
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hs
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
  refine ⟨-(r1 / r0), ?_⟩
  rw [M.sem_mul, T.sem_mcst, Derivation.leibniz, T.deriv_ratCast, hsd]
  simp only [smul_eq_mul, mul_zero, add_zero]
  push_cast
  field_simp
  ring

/-- **Soundness of the chain.** -/
theorem mchain_sound (η : LC m) (Λ : GPoly (LC m)) :
    ∀ (j : ℕ) (Q R : LC m), mchain Fc ks lv m η Λ j Q = some R →
      ∃ P : ℕ → T.F m,
        (∀ i, 1 ≤ i → i ≤ j → (P i)′ + ((i + 1 : ℕ) : T.F m) * (T.MP m h).sem η * P (i + 1) =
          (T.MP m h).sem (Λ.getD i (MO Fc ks m).zero)) ∧
        (∃ q : ℚ, P (j + 1) = (T.MP m h).sem Q + q) ∧ P 1 = (T.MP m h).sem R := by
  set M := T.MP m h
  intro j
  induction j with
  | zero =>
    intro Q R hc
    simp only [mchain, Option.some.injEq] at hc
    subst hc
    exact ⟨fun _ ↦ M.sem Q, fun i h1 h2 ↦ by omega, ⟨0, by simp⟩, rfl⟩
  | succ j ih =>
    intro Q R hc
    simp only [mchain] at hc
    obtain ⟨Q', hQ', hR⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨P, hPrec, ⟨q, hq⟩, hP1⟩ := ih Q' R hR
    obtain ⟨γ, hγ⟩ := T.mchainStep_sound m h hlim η _ Q Q' (j + 1) hQ'
    rw [T.sem_mchainRHS] at hγ
    set P' := Function.update P (j + 2) (M.sem Q + ((γ / (j + 2) : ℚ) : T.F m)) with hP'
    have hP'lt : ∀ i, i < j + 2 → P' i = P i := fun i hi ↦
      Function.update_of_ne (by omega) _ _
    refine ⟨P', fun i h1 h2 ↦ ?_, ⟨γ / (j + 2), ?_⟩, ?_⟩
    · rw [hP'lt i (by omega)]
      by_cases hij : i ≤ j
      · rw [hP'lt (i + 1) (by omega)]; exact hPrec i h1 hij
      · have hi : i = j + 1 := by omega
        subst hi
        rw [hP', Function.update_self, hq, Derivation.map_add, T.deriv_ratCast, add_zero]
        have hj2 : (j : T.F m) + 2 ≠ 0 := by exact_mod_cast (by omega : j + 2 ≠ 0)
        have h2 : (((j + 1 + 1 : ℕ) : T.F m)) = ((j + 2 : ℕ) : T.F m) := by push_cast; ring
        have hγ' : (M.sem Q')′ = M.sem (Λ.getD (j + 1) (MO Fc ks m).zero) -
            ((j + 1 + 1 : ℕ) : T.F m) * M.sem η * M.sem Q - (γ : T.F m) * M.sem η := by
          rw [← hγ]; ring
        rw [hγ', h2]
        push_cast
        field_simp
        ring
    · rw [hP', Function.update_self]
    · rw [hP'lt 1 (by omega), hP1]

/-- **Completeness of the chain**: a solution `p` of the recurrence (with `p_{j+1} − Q`
constant) makes the chain succeed, with `p₁ − Q₁` constant. -/
theorem mchain_complete (η : LC m) (hnd : ∀ y : T.F m, y′ ≠ (T.MP m h).sem η)
    (Λ : GPoly (LC m)) (p : ℕ → T.F m) :
    ∀ (j : ℕ), (∀ i, 1 ≤ i → i ≤ j → (p i)′ + ((i + 1 : ℕ) : T.F m) * (T.MP m h).sem η * p (i + 1) =
          (T.MP m h).sem (Λ.getD i (MO Fc ks m).zero)) →
      ∀ Q : LC m, (p (j + 1) - (T.MP m h).sem Q)′ = 0 →
      ∃ R, mchain Fc ks lv m η Λ j Q = some R ∧ (p 1 - (T.MP m h).sem R)′ = 0 := by
  classical
  set M := T.MP m h
  intro j
  induction j with
  | zero =>
    intro _ Q hQ
    exact ⟨Q, rfl, hQ⟩
  | succ j ih =>
    intro hrec Q hQ
    obtain ⟨κ, hκ⟩ := T.const_F _ hQ
    set f := mchainRHS Fc ks m η (Λ.getD (j + 1) (MO Fc ks m).zero) Q (j + 1) with hf
    set sols := paramLimC Fc ks lv m [f, η] with hsols
    -- `p (j + 1)` solves the parametric problem
    have hpj : (p (j + 1))′ = sC (algebraMap Cc (T.F m)) M [1, -(((j + 2 : ℕ) : Cc)) * κ] [f, η] := by
      rw [sC]
      simp only [List.length_cons, List.length_nil, zero_add, Finset.sum_range_succ,
        Finset.range_one, Finset.sum_singleton, List.getD_cons_zero, List.getD_cons_succ]
      rw [hf, T.sem_mchainRHS]
      have := hrec (j + 1) (by omega) le_rfl
      have hp2 : p (j + 1 + 1) = M.sem Q + algebraMap Cc (T.F m) κ := by
        rw [← hκ]; ring
      rw [hp2] at this
      simp only [map_one, one_mul, map_mul, map_neg, map_natCast]
      rw [show ((j + 1 + 1 : ℕ) : T.F m) = ((j + 2 : ℕ) : T.F m) by push_cast; ring] at this ⊢
      linear_combination this
    obtain ⟨β, hβ1, -⟩ := hlim.complete [f, η]
      [1, -(((j + 2 : ℕ) : Cc)) * κ] (fun i hi ↦ by
        rcases i with _ | _ | i
        · simp at hi
        · simp at hi
        · rfl) (p (j + 1)) hpj
    have h1 := hβ1 0
    simp only [List.getD_cons_zero] at h1
    have hex : ∃ r ∈ sols, r.1.getD 0 0 ≠ 0 := by
      by_contra hall
      push Not at hall
      rw [Finset.sum_eq_zero fun l hl ↦ by
        have : (sols.getD l ([], (MO Fc ks m).zero)).1.getD 0 0 = 0 := hall _ (by
          rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hl)]; exact List.getElem_mem _)
        rw [this, map_zero, mul_zero]] at h1
      exact one_ne_zero h1
    obtain ⟨r, hr⟩ : ∃ r, sols.find? (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) = some r := by
      obtain ⟨r, hrm, hr0⟩ := hex
      exact Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨r, hrm, by simpa using hr0⟩)
    set Q' := (MO Fc ks m).mul (mcst Fc ks m (r.1.getD 0 0)⁻¹) r.2 with hQ'
    have hstep : mchainStep Fc ks lv m η (Λ.getD (j + 1) (MO Fc ks m).zero) Q (j + 1) = some Q' := by
      simp only [mchainStep, ← hf, ← hsols, hr, Option.map_some]
      rfl
    obtain ⟨γ, hγ⟩ := T.mchainStep_sound m h hlim η _ Q Q' (j + 1) hstep
    -- `p (j + 1) − Q'` is constant
    have hd : (p (j + 1) - M.sem Q')′ =
        (algebraMap Cc (T.F m) (-(((j + 2 : ℕ) : Cc)) * κ) + (γ : T.F m)) * M.sem η := by
      have e1 : (p (j + 1))′ = M.sem f +
          algebraMap Cc (T.F m) (-(((j + 2 : ℕ) : Cc)) * κ) * M.sem η := by
        rw [hpj, sC]
        simp only [List.length_cons, List.length_nil, zero_add, Finset.sum_range_succ,
          Finset.range_one, Finset.sum_singleton, List.getD_cons_zero, List.getD_cons_succ,
          map_one, one_mul]
      rw [Derivation.map_sub, e1, ← hγ]
      ring
    set cc := algebraMap Cc (T.F m) (-(((j + 2 : ℕ) : Cc)) * κ) + (γ : T.F m) with hcc
    by_cases h0 : cc = 0
    · rw [h0, zero_mul] at hd
      obtain ⟨R, hR, hR1⟩ := ih (fun i h1 h2 ↦ hrec i h1 (by omega)) Q' hd
      refine ⟨R, ?_, hR1⟩
      simp only [mchain, hstep, Option.bind_some]
      exact hR
    · exfalso
      apply hnd ((p (j + 1) - M.sem Q') / cc)
      have hc' : cc′ = 0 := by
        rw [hcc, Derivation.map_add, T.deriv_algebraMap_Cc, T.deriv_ratCast, add_zero]
      rw [Derivation.leibniz_div, hc', hd]
      simp only [smul_eq_mul, mul_zero, sub_zero]
      field_simp

end MTower

end Curves.MT
