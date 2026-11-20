import RischTragerBronstein.Mixed.LTTransfer

/-!
# Towers of logarithms over a curve: the limited-integration chain at level `m`

The polynomial part `∑ aⱼ tₘʲ` of an integrand at level `m + 1` is handled top down:
`Qⱼ′ + γ η = aⱼ − (j + 1) η Qⱼ₊₁` (`Q_{d+1} = 0`), each step solved with `lex m` on the
right-hand sides `[aⱼ − (j + 1) η Qⱼ₊₁, η]` (a returned solution with non-zero first parameter).
This is `primChain` of `LogCurveDecide` with the Risch solver of the curve replaced by the
parametric exact solver of level `m`.

* `lchain_sound`: in a realization with the generators below `m` transcendental;
* `lchain_complete`: in a realization with the generators below `m + 1` transcendental.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.LT

open CPoly Sup

variable (Fc : BPoly ℚ) (us : (m : ℕ) → LC m)

/-- `a − (j + 1) η Q` at level `m`. -/
def lchainRHS (m : ℕ) (a Q : LC m) (j : ℕ) : LC m :=
  (LO Fc us m).add a ((LO Fc us m).neg
    ((LO Fc us m).mul ((LO Fc us m).mul ((LO Fc us m).natCast (j + 1)) (etaC Fc us m)) Q))

/-- One step of the chain: a solution `Q'` of `Q'′ + γ η = a − (j + 1) η Q`. -/
def lchainStep (m : ℕ) (a Q : LC m) (j : ℕ) : Option (LC m) :=
  ((lex Fc us m [lchainRHS Fc us m a Q j, etaC Fc us m]).find?
    fun r ↦ decide (r.1.getD 0 0 ≠ 0)).map
    fun r ↦ (LO Fc us m).mul (lcst Fc us m (r.1.getD 0 0)⁻¹) r.2

/-- The chain from index `j` down to `1`, starting from `Qⱼ₊₁ = Q`; returns `Q₁`. -/
def lchain (m : ℕ) (Λ : GPoly (LC m)) : ℕ → LC m → Option (LC m)
  | 0, Q => some Q
  | j + 1, Q => (lchainStep Fc us m (Λ.getD (j + 1) (LO Fc us m).zero) Q (j + 1)).bind
      (lchain m Λ j)

/-- The constant term `a₀ − η Q₁`. -/
def lconst (m : ℕ) (Λ : GPoly (LC m)) (Q1 : LC m) : LC m :=
  (LO Fc us m).add (Λ.getD 0 (LO Fc us m).zero)
    ((LO Fc us m).neg ((LO Fc us m).mul (etaC Fc us m) Q1))

universe u

variable {Fc us} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace LTower

variable (T : LTower Fc us Cc L)

lemma sem_lchainRHS (m : ℕ) (h : T.Tr m) (a Q : LC m) (j : ℕ) :
    (T.MP m h).sem (lchainRHS Fc us m a Q j) = (T.MP m h).sem a -
      ((j + 1 : ℕ) : T.F m) * T.eta m * (T.MP m h).sem Q := by
  rw [lchainRHS, CField.sem_add, CField.sem_neg, CField.sem_mul, CField.sem_mul,
    CField.sem_natCast, T.sem_eta, sub_eq_add_neg]

lemma sem_lconst (m : ℕ) (h : T.Tr m) (Λ : GPoly (LC m)) (Q1 : LC m) :
    (T.MP m h).sem (lconst Fc us m Λ Q1) =
      (T.MP m h).sem (Λ.getD 0 (LO Fc us m).zero) - T.eta m * (T.MP m h).sem Q1 := by
  rw [lconst, CField.sem_add, CField.sem_neg, CField.sem_mul, T.sem_eta, sub_eq_add_neg]

/-- **Soundness of one step.** -/
lemma lchainStep_sound (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (h : T.Tr m) (a Q Q' : LC m) (j : ℕ) (hs : lchainStep Fc us m a Q j = some Q') :
    ∃ γ : ℚ, ((T.MP m h).sem Q')′ + (γ : T.F m) * T.eta m =
      (T.MP m h).sem (lchainRHS Fc us m a Q j) := by
  set M := T.MP m h
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hs
  have hr0 := List.find?_some hr
  simp only [decide_eq_true_eq] at hr0
  have hmem := List.mem_of_find?_eq_some hr
  have hsd := (T.lex_spec hmon hdeg m h _).1 r hmem
  rw [sumQ] at hsd
  simp only [List.length_cons, List.length_nil, zero_add, Finset.sum_range_succ,
    Finset.range_one, Finset.sum_singleton, List.getD_cons_zero, List.getD_cons_succ] at hsd
  rw [T.sem_eta] at hsd
  set r0 := r.1.getD 0 0
  set r1 := r.1.getD 1 0
  have hq : (r0 : T.F m) ≠ 0 := by exact_mod_cast hr0
  refine ⟨-(r1 / r0), ?_⟩
  rw [M.sem_mul, T.sem_lcst, Derivation.leibniz, T.deriv_ratCast, hsd]
  simp only [smul_eq_mul, mul_zero, add_zero]
  push_cast
  field_simp
  ring

/-- **Soundness of the chain.** -/
theorem lchain_sound (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (h : T.Tr m) (Λ : GPoly (LC m)) :
    ∀ (j : ℕ) (Q R : LC m), lchain Fc us m Λ j Q = some R →
      ∃ P : ℕ → T.F m,
        (∀ i, 1 ≤ i → i ≤ j → (P i)′ + ((i + 1 : ℕ) : T.F m) * T.eta m * P (i + 1) =
          (T.MP m h).sem (Λ.getD i (LO Fc us m).zero)) ∧
        (∃ q : ℚ, P (j + 1) = (T.MP m h).sem Q + q) ∧ P 1 = (T.MP m h).sem R := by
  set M := T.MP m h
  intro j
  induction j with
  | zero =>
    intro Q R hc
    simp only [lchain, Option.some.injEq] at hc
    subst hc
    exact ⟨fun _ ↦ M.sem Q, fun i h1 h2 ↦ by omega, ⟨0, by simp⟩, rfl⟩
  | succ j ih =>
    intro Q R hc
    simp only [lchain] at hc
    obtain ⟨Q', hQ', hR⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨P, hPrec, ⟨q, hq⟩, hP1⟩ := ih Q' R hR
    obtain ⟨γ, hγ⟩ := T.lchainStep_sound hmon hdeg m h _ Q Q' (j + 1) hQ'
    rw [T.sem_lchainRHS] at hγ
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
        have hγ' : (M.sem Q')′ = M.sem (Λ.getD (j + 1) (LO Fc us m).zero) -
            ((j + 1 + 1 : ℕ) : T.F m) * T.eta m * M.sem Q - (γ : T.F m) * T.eta m := by
          rw [← hγ]; ring
        rw [hγ', h2]
        push_cast
        field_simp
        ring
    · rw [hP', Function.update_self]
    · rw [hP'lt 1 (by omega), hP1]

/-- **Completeness of the chain**: a solution `p` of the recurrence (with `p_{j+1} − Q`
constant) makes the chain succeed, with `p₁ − Q₁` constant. -/
theorem lchain_complete (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (h : T.Tr (m + 1)) (Λ : GPoly (LC m)) (p : ℕ → T.F m) :
    ∀ (j : ℕ), (∀ i, 1 ≤ i → i ≤ j → (p i)′ + ((i + 1 : ℕ) : T.F m) * T.eta m * p (i + 1) =
          (T.MP m h.of_succ).sem (Λ.getD i (LO Fc us m).zero)) →
      ∀ Q : LC m, (p (j + 1) - (T.MP m h.of_succ).sem Q)′ = 0 →
      ∃ R, lchain Fc us m Λ j Q = some R ∧ (p 1 - (T.MP m h.of_succ).sem R)′ = 0 := by
  classical
  set hm : T.Tr m := h.of_succ
  set M := T.MP m hm
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  intro j
  induction j with
  | zero =>
    intro _ Q hQ
    exact ⟨Q, rfl, hQ⟩
  | succ j ih =>
    intro hrec Q hQ
    obtain ⟨κ, hκ⟩ := T.const_F _ hQ
    set f := lchainRHS Fc us m (Λ.getD (j + 1) (LO Fc us m).zero) Q (j + 1) with hf
    set sols := lex Fc us m [f, etaC Fc us m] with hsols
    -- `p (j + 1)` solves the parametric problem
    have hpj : (p (j + 1))′ = T.sumK m hm [1, -(((j + 2 : ℕ) : Cc)) * κ] [f, etaC Fc us m] := by
      rw [sumK]
      simp only [List.length_cons, List.length_nil, zero_add, Finset.sum_range_succ,
        Finset.range_one, Finset.sum_singleton, List.getD_cons_zero, List.getD_cons_succ]
      rw [hf, T.sem_lchainRHS, T.sem_eta]
      have := hrec (j + 1) (by omega) le_rfl
      have hp2 : p (j + 1 + 1) = M.sem Q + algebraMap Cc (T.F m) κ := by
        rw [← hκ]; ring
      rw [hp2] at this
      simp only [map_one, one_mul, map_mul, map_neg, map_natCast]
      rw [show ((j + 1 + 1 : ℕ) : T.F m) = ((j + 2 : ℕ) : T.F m) by push_cast; ring] at this ⊢
      linear_combination this
    obtain ⟨β, hβ1, -⟩ := (T.lex_spec hmon hdeg m hm [f, etaC Fc us m]).2
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
        have : (sols.getD l ([], zc Fc us m)).1.getD 0 0 = 0 := hall _ (by
          rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hl)]; exact List.getElem_mem _)
        rw [this, map_zero, mul_zero]] at h1
      exact one_ne_zero h1
    obtain ⟨r, hr⟩ : ∃ r, sols.find? (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) = some r := by
      obtain ⟨r, hrm, hr0⟩ := hex
      exact Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨r, hrm, by simpa using hr0⟩)
    set Q' := (LO Fc us m).mul (lcst Fc us m (r.1.getD 0 0)⁻¹) r.2 with hQ'
    have hstep : lchainStep Fc us m (Λ.getD (j + 1) (LO Fc us m).zero) Q (j + 1) = some Q' := by
      simp only [lchainStep, ← hf, ← hsols, hr, Option.map_some]
      rfl
    obtain ⟨γ, hγ⟩ := T.lchainStep_sound hmon hdeg m hm _ Q Q' (j + 1) hstep
    -- `p (j + 1) − Q'` is constant
    have hd : (p (j + 1) - M.sem Q')′ =
        (algebraMap Cc (T.F m) (-(((j + 2 : ℕ) : Cc)) * κ) + (γ : T.F m)) * T.eta m := by
      have e1 : (p (j + 1))′ = M.sem f +
          algebraMap Cc (T.F m) (-(((j + 2 : ℕ) : Cc)) * κ) * T.eta m := by
        rw [hpj, sumK]
        simp only [List.length_cons, List.length_nil, zero_add, Finset.sum_range_succ,
          Finset.range_one, Finset.sum_singleton, List.getD_cons_zero, List.getD_cons_succ,
          map_one, one_mul, T.sem_eta]
        rfl
      rw [Derivation.map_sub, e1, ← hγ]
      ring
    set cc := algebraMap Cc (T.F m) (-(((j + 2 : ℕ) : Cc)) * κ) + (γ : T.F m) with hcc
    by_cases h0 : cc = 0
    · rw [h0, zero_mul] at hd
      obtain ⟨R, hR, hR1⟩ := ih (fun i h1 h2 ↦ hrec i h1 (by omega)) Q' hd
      refine ⟨R, ?_, hR1⟩
      simp only [lchain, hstep, Option.bind_some]
      exact hR
    · exfalso
      apply T.eta_not_deriv m htr ((p (j + 1) - M.sem Q') / cc)
      have hc' : cc′ = 0 := by
        rw [hcc, Derivation.map_add, T.deriv_algebraMap_Cc, T.deriv_ratCast, add_zero]
      rw [Derivation.leibniz_div, hc', hd]
      simp only [smul_eq_mul, mul_zero, sub_zero]
      field_simp

end LTower

end Curves.LT
