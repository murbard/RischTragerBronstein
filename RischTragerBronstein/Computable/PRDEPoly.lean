import RischTragerBronstein.Computable.ODEPolyGen
import RischTragerBronstein.Computable.LinSolve

/-!
# The parametric polynomial ODE `P₁ Y′ + P₀ Y = A₀ - c A₁`

One unknown constant `c`. The elimination loop `odeLoopGen` is run twice (right-hand sides `A₀`,
`A₁`); by linearity the residual of `A₀ - c A₁` is `Rm₀ - c Rm₁`, and the final condition
(together with the homogeneous track, if any) is a linear system in `(c, λ)` solved by `linSolve`.

* `prdeSolveGen_sound`: a returned `(c, Y)` solves the equation;
* `prdeSolveGen_complete_map`: if a solution `(c, Ys)` exists over an extension `S` of the
  constants, the solver succeeds (and then returns some solution).
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R]

/-- Decide `P₁ Y′ + P₀ Y = A₀ - c A₁` for a constant `c`. -/
def prdeSolveGen (P₁ P₀ A₀ A₁ : CPoly R) (dg : ℕ) (piv : ℕ → R) (N : ℕ) :
    Option (R × CPoly R) :=
  let st₀ := odeLoopGen P₁ P₀ dg piv N ⟨[], A₀, none⟩
  let st₁ := odeLoopGen P₁ P₀ dg piv N ⟨[], A₁, none⟩
  match st₀.hom with
  | none =>
    match linSolve [st₁.Rm] st₀.Rm with
    | some [c] => some (c, trim (sub st₀.Y (smul c st₁.Y)))
    | _ => none
  | some yh =>
    match linSolve [st₁.Rm, neg yh.2] st₀.Rm with
    | some [c, l] => some (c, trim (add (sub st₀.Y (smul c st₁.Y)) (smul l yh.1)))
    | _ => none

/-- **Soundness.** -/
theorem prdeSolveGen_sound {P₁ P₀ A₀ A₁ : CPoly R} {dg : ℕ} {piv : ℕ → R} {N : ℕ} {c : R}
    {Y : CPoly R} (h : prdeSolveGen P₁ P₀ A₀ A₁ dg piv N = some (c, Y)) :
    toPoly P₁ * derivative (toPoly Y) + toPoly P₀ * toPoly Y = toPoly A₀ - C c * toPoly A₁ := by
  have hinv₀ := odeLoopGen_inv P₁ P₀ A₀ dg piv N ⟨[], A₀, none⟩
    ⟨by simp [odeOp], fun yh hyh ↦ by simp at hyh⟩
  have hinv₁ := odeLoopGen_inv P₁ P₀ A₁ dg piv N ⟨[], A₁, none⟩
    ⟨by simp [odeOp], fun yh hyh ↦ by simp at hyh⟩
  simp only [prdeSolveGen] at h
  set st₀ := odeLoopGen P₁ P₀ dg piv N ⟨[], A₀, none⟩
  set st₁ := odeLoopGen P₁ P₀ dg piv N ⟨[], A₁, none⟩
  obtain ⟨h0, h0h⟩ := hinv₀
  obtain ⟨h1, -⟩ := hinv₁
  rw [toPoly_odeOp] at h0 h1
  cases hh : st₀.hom with
  | none =>
    rw [hh] at h
    simp only at h
    revert h
    cases hls : linSolve [st₁.Rm] st₀.Rm with
    | none => intro h; exact absurd h (by simp)
    | some cs =>
      obtain ⟨-, hc⟩ := linSolve_sound _ _ _ hls
      intro h
      match cs, hc, h with
      | [c'], hc, h =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [lcomb, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons,
          List.sum_nil, add_zero] at hc
        rw [toPoly_trim, toPoly_sub, toPoly_smul, derivative_sub, derivative_mul, derivative_C,
          zero_mul, zero_add]
        linear_combination h0 - C c' * h1 + hc
  | some yh =>
    rw [hh] at h
    simp only at h
    revert h
    cases hls : linSolve [st₁.Rm, neg yh.2] st₀.Rm with
    | none => intro h; exact absurd h (by simp)
    | some cs =>
      obtain ⟨-, hc⟩ := linSolve_sound _ _ _ hls
      have hyh := h0h yh hh
      rw [toPoly_odeOp] at hyh
      intro h
      match cs, hc, h with
      | [c', l], hc, h =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [lcomb, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons,
          List.sum_nil, add_zero, toPoly_neg] at hc
        rw [toPoly_trim, toPoly_add, toPoly_sub, toPoly_smul, toPoly_smul, derivative_add,
          derivative_sub, derivative_mul, derivative_mul, derivative_C, derivative_C, zero_mul,
          zero_mul, zero_add, zero_add]
        linear_combination h0 - C c' * h1 + hc + C l * hyh

end CPoly

namespace CPoly

variable {R S : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [DecidableEq S]
  [CharZero S] (ι : R →+* S)

lemma toPoly_listMap (l : CPoly R) : toPoly (l.map ι) = (toPoly l).map ι := by
  induction l with
  | nil => simp
  | cons a l ih => simp [toPoly, ih]

/-- The relation between the run over `S` on `A₀ - c A₁` and the two runs over `R`. -/
def PRel (c : S) (stS : OdeState S) (st₀ st₁ : OdeState R) : Prop :=
  toPoly stS.Y = (toPoly st₀.Y).map ι - C c * (toPoly st₁.Y).map ι ∧
  toPoly stS.Rm = (toPoly st₀.Rm).map ι - C c * (toPoly st₁.Rm).map ι ∧
  (stS.hom = none ↔ st₀.hom = none) ∧
  ∀ yhS yh, stS.hom = some yhS → st₀.hom = some yh →
    toPoly yhS.1 = (toPoly yh.1).map ι ∧ toPoly yhS.2 = (toPoly yh.2).map ι

lemma opS_eq (P₁ P₀ : CPoly R) (Y : CPoly S) :
    toPoly (odeOp (P₁.map ι) (P₀.map ι) Y) = opS ι P₁ P₀ (toPoly Y) := by
  rw [toPoly_odeOp, opS, toPoly_listMap, toPoly_listMap]

lemma odeStepGen_prel (P₁ P₀ : CPoly R) (dg k : ℕ) (pv : R) (c : S)
    (stS : OdeState S) (st₀ st₁ : OdeState R) (h : PRel ι c stS st₀ st₁) :
    PRel ι c (odeStepGen (P₁.map ι) (P₀.map ι) dg k (ι pv) stS)
      (odeStepGen P₁ P₀ dg k pv st₀) (odeStepGen P₁ P₀ dg k pv st₁) := by
  obtain ⟨hY, hR, hn, hs⟩ := h
  have hmap : ∀ Q : CPoly R, toPoly (odeOp (P₁.map ι) (P₀.map ι) (Q.map ι)) =
      (toPoly (odeOp P₁ P₀ Q)).map ι := fun Q ↦ by
    rw [opS_eq, toPoly_listMap, opS_map]
  by_cases hpv : pv = 0
  · subst hpv
    simp only [odeStepGen, map_zero, eq_self_iff_true, if_true]
    cases hh : stS.hom with
    | none =>
      have hh0 : st₀.hom = none := hn.mp hh
      rw [hh0]
      cases st₁.hom <;>
      · refine ⟨hY, hR, by simp, fun yhS yh h1 h2 ↦ ?_⟩
        simp only [Option.some.injEq] at h1 h2
        subst h1; subst h2
        have hm : (monomial k (1 : S)) = (monomial k (1 : R)).map ι := by
          simp [monomial, List.map_replicate]
        refine ⟨?_, ?_⟩
        · rw [hm, toPoly_listMap]
        · simp only [neg]
          rw [toPoly_smul, toPoly_smul, Polynomial.map_mul, map_C, hm, hmap]
          congr 1
          rw [map_neg, map_one]
          simp
    | some yhS =>
      have hh0 : ∃ yh, st₀.hom = some yh := by
        cases hh0 : st₀.hom with
        | none => exact absurd (hn.mpr hh0) (by rw [hh]; simp)
        | some yh => exact ⟨yh, rfl⟩
      obtain ⟨yh, hh0⟩ := hh0
      rw [hh0]
      cases st₁.hom <;>
      · refine ⟨hY, hR, by simp [hh, hh0], fun yhS' yh' h1 h2 ↦ ?_⟩
        simp only at h1 h2
        exact hs _ _ h1 h2
  · have hpv' : ι pv ≠ 0 := fun h ↦ hpv ((map_eq_zero ι).mp h)
    simp only [odeStepGen, hpv, hpv', if_false]
    have hcoeff : stS.Rm.getD (k + dg) 0 =
        ι (st₀.Rm.getD (k + dg) 0) - c * ι (st₁.Rm.getD (k + dg) 0) := by
      rw [← coeff_toPoly, hR, coeff_sub, coeff_C_mul, coeff_map, coeff_map, coeff_toPoly,
        coeff_toPoly]
    have hm : toPoly (monomial k (stS.Rm.getD (k + dg) 0 / ι pv)) =
        (toPoly (monomial k (st₀.Rm.getD (k + dg) 0 / pv))).map ι -
          C c * (toPoly (monomial k (st₁.Rm.getD (k + dg) 0 / pv))).map ι := by
      rw [toPoly_monomial, toPoly_monomial, toPoly_monomial, Polynomial.map_mul, map_C,
        Polynomial.map_pow, map_X, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, hcoeff,
        map_div₀ ι, map_div₀ ι]
      have hd : (ι (st₀.Rm.getD (k + dg) 0) - c * ι (st₁.Rm.getD (k + dg) 0)) / ι pv =
          ι (st₀.Rm.getD (k + dg) 0) / ι pv - c * (ι (st₁.Rm.getD (k + dg) 0) / ι pv) := by
        field_simp
      rw [hd, C_sub, C_mul]
      ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [toPoly_add, hY, hm, Polynomial.map_add]
      ring
    · simp only [toPoly_sub, hR, ← toPoly_odeOp, opS_eq, Polynomial.map_sub]
      rw [hm, opS_sub, opS_C_mul, ← opS_map, ← opS_map]
      ring
    · simp only [Option.map_eq_none_iff]
      exact hn
    · intro yhS' yh' h1 h2
      simp only [Option.map_eq_some_iff] at h1 h2
      obtain ⟨yhS, hyhS, rfl⟩ := h1
      obtain ⟨yh, hyh, rfl⟩ := h2
      obtain ⟨e1, e2⟩ := hs yhS yh hyhS hyh
      have hcoeff' : yhS.2.getD (k + dg) 0 = ι (yh.2.getD (k + dg) 0) := by
        rw [← coeff_toPoly, e2, coeff_map, coeff_toPoly]
      have hmh : monomial k (yhS.2.getD (k + dg) 0 / ι pv) =
          (monomial k (yh.2.getD (k + dg) 0 / pv)).map ι := by
        simp only [monomial, List.map_append, List.map_replicate, List.map_cons, List.map_nil,
          map_zero, map_div₀]
        rw [hcoeff']
      refine ⟨?_, ?_⟩
      · simp only [toPoly_add, e1, hmh, toPoly_listMap, Polynomial.map_add]
      · simp only [toPoly_sub, e2, hmh, hmap, Polynomial.map_sub]

lemma odeLoopGen_prel (P₁ P₀ : CPoly R) (dg : ℕ) (piv : ℕ → R) (c : S) (N : ℕ)
    (stS : OdeState S) (st₀ st₁ : OdeState R) (h : PRel ι c stS st₀ st₁) :
    PRel ι c (odeLoopGen (P₁.map ι) (P₀.map ι) dg (fun k ↦ ι (piv k)) N stS)
      (odeLoopGen P₁ P₀ dg piv N st₀) (odeLoopGen P₁ P₀ dg piv N st₁) := by
  induction N generalizing stS st₀ st₁ with
  | zero => exact h
  | succ N ih => exact ih _ _ _ (odeStepGen_prel ι P₁ P₀ dg N (piv N) c stS st₀ st₁ h)

/-- **Completeness.** If `P₁ Y′ + P₀ Y = A₀ - c A₁` has a polynomial solution of degree `< N`
over an extension `S` of the coefficient field (with `c ∈ S`), the solver succeeds. -/
theorem prdeSolveGen_complete_map {P₁ P₀ A₀ A₁ : CPoly R} {dg : ℕ} {piv : ℕ → R} {N : ℕ}
    (h1 : (toPoly P₁).natDegree ≤ dg + 1) (h0 : (toPoly P₀).natDegree ≤ dg)
    (hpiv : ∀ k, piv k = (k : R) * (toPoly P₁).coeff (dg + 1) + (toPoly P₀).coeff dg)
    (huniq : ∀ k k', piv k = 0 → piv k' = 0 → k = k')
    (c : S) (Ys : S[X]) (hYs : opS ι P₁ P₀ Ys = (toPoly A₀).map ι - C c * (toPoly A₁).map ι)
    (hN : Ys.natDegree < N) :
    prdeSolveGen P₁ P₀ A₀ A₁ dg piv N ≠ none := by
  -- the run over `S` on `A₀ - c A₁`
  set AS : CPoly S := sub (A₀.map ι) (smul c (A₁.map ι)) with hAS
  have hAS' : toPoly AS = (toPoly A₀).map ι - C c * (toPoly A₁).map ι := by
    rw [hAS, toPoly_sub, toPoly_smul, toPoly_listMap, toPoly_listMap]
  have hrel := odeLoopGen_prel ι P₁ P₀ dg piv c N ⟨[], AS, none⟩ ⟨[], A₀, none⟩ ⟨[], A₁, none⟩
    ⟨by simp, by simp [hAS'], by simp, fun _ _ h _ ↦ by simp at h⟩
  have hS := odeSolveGen_complete_map (RingHom.id S) (P₁ := P₁.map ι) (P₀ := P₀.map ι) (A := AS)
    (dg := dg) (piv := fun k ↦ ι (piv k)) (N := N)
    (by rw [toPoly_listMap]; exact natDegree_map_le.trans h1)
    (by rw [toPoly_listMap]; exact natDegree_map_le.trans h0)
    (fun k ↦ by rw [hpiv, map_add, map_mul, map_natCast, toPoly_listMap, toPoly_listMap, coeff_map,
      coeff_map])
    (fun k k' hk hk' ↦ huniq k k' ((map_eq_zero ι).mp hk) ((map_eq_zero ι).mp hk')) Ys
    (by
      simp only [opS, toPoly_listMap, Polynomial.map_id, hAS']
      exact hYs) hN
  simp only [odeSolveGen] at hS
  simp only [prdeSolveGen]
  set stS := odeLoopGen (P₁.map ι) (P₀.map ι) dg (fun k ↦ ι (piv k)) N ⟨[], AS, none⟩ with hstS
  set st₀ := odeLoopGen P₁ P₀ dg piv N ⟨[], A₀, none⟩ with hst₀
  set st₁ := odeLoopGen P₁ P₀ dg piv N ⟨[], A₁, none⟩ with hst₁
  obtain ⟨-, hR, hn, hs⟩ := hrel
  cases hh : st₀.hom with
  | none =>
    have hhS : stS.hom = none := hn.mpr hh
    rw [hhS] at hS
    simp only at hS
    split_ifs at hS with hz
    swap
    · exact absurd rfl hS
    have hz' := (isZero_iff _).mp hz
    rw [hR] at hz'
    have hne := linSolve_complete_map ι [st₁.Rm] st₀.Rm [c] rfl (by
      simp only [lcombS, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons,
        List.sum_nil, add_zero]
      linear_combination -hz')
    obtain ⟨cs, hcs⟩ := Option.ne_none_iff_exists'.mp hne
    obtain ⟨hlen, -⟩ := linSolve_sound _ _ _ hcs
    obtain ⟨c', rfl⟩ := List.length_eq_one_iff.mp hlen
    simp only [hcs]
    exact Option.some_ne_none _
  | some yh =>
    have hhS : ∃ yhS, stS.hom = some yhS := by
      cases hhS : stS.hom with
      | none => exact absurd (hn.mp hhS) (by rw [hh]; simp)
      | some yhS => exact ⟨yhS, rfl⟩
    obtain ⟨yhS, hhS⟩ := hhS
    obtain ⟨-, e2⟩ := hs yhS yh hhS hh
    rw [hhS] at hS
    simp only at hS
    revert hS
    cases hcrit : limitedCrit stS.Rm [1] (neg yhS.2) [1] with
    | none => intro hS; exact absurd rfl hS
    | some l =>
      intro _
      have hl := limitedCrit_sound hcrit
      simp only [toPoly_cons, toPoly_nil, mul_zero, add_zero, C_1, mul_one, toPoly_neg] at hl
      rw [hR, e2] at hl
      have hne := linSolve_complete_map ι [st₁.Rm, neg yh.2] st₀.Rm [c, l] rfl (by
        simp only [lcombS, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons,
          List.sum_nil, add_zero, toPoly_neg, Polynomial.map_neg]
        linear_combination -hl)
      obtain ⟨cs, hcs⟩ := Option.ne_none_iff_exists'.mp hne
      obtain ⟨hlen, -⟩ := linSolve_sound _ _ _ hcs
      match cs, hlen, hcs with
      | [c', l'], _, hcs =>
        simp only [hcs]
        exact Option.some_ne_none _

/-- Degree bound with an arbitrary right-hand side over `S`. -/
theorem natDegree_le_of_opS' {P₁ P₀ : CPoly R} {dg : ℕ} {piv : ℕ → R}
    (h1 : (toPoly P₁).natDegree ≤ dg + 1) (h0 : (toPoly P₀).natDegree ≤ dg)
    (hpiv : ∀ k, piv k = (k : R) * (toPoly P₁).coeff (dg + 1) + (toPoly P₀).coeff dg)
    {kb : ℕ} (hkb : ∀ k, kb < k → piv k ≠ 0) (Ys B : S[X])
    (hYs : opS ι P₁ P₀ Ys = B) :
    Ys.natDegree ≤ max (B.natDegree - dg) kb := by
  by_contra hlt
  rw [not_le, max_lt_iff] at hlt
  obtain ⟨hA, hk⟩ := hlt
  have hY0 : Ys ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hk; omega
  have hco := coeff_opS ι h1 h0 (Z := Ys) (k := Ys.natDegree)
    fun m hm ↦ coeff_eq_zero_of_natDegree_lt hm
  rw [hYs, ← hpiv, coeff_eq_zero_of_natDegree_lt (by omega)] at hco
  rcases mul_eq_zero.mp hco.symm with h | h
  · exact hkb _ hk ((map_eq_zero ι).mp h)
  · exact hY0 (leadingCoeff_eq_zero.mp h)

/-- The packaged parametric solver: `P₁ Y′ + P₀ Y = A₀ - c A₁` (`P₀ ≠ 0`), `kb` bounding the
zero of the pivot. -/
def prdeSolveFull (P₁ P₀ A₀ A₁ : CPoly R) (kb : ℕ) : Option (R × CPoly R) :=
  prdeSolveGen P₁ P₀ A₀ A₁ (odeDg P₁ P₀) (odePiv P₁ P₀)
    (max (max ((trim A₀).length - 1) ((trim A₁).length - 1) - odeDg P₁ P₀) kb + 1)

theorem prdeSolveFull_sound {P₁ P₀ A₀ A₁ : CPoly R} {kb : ℕ} {c : R} {Y : CPoly R}
    (h : prdeSolveFull P₁ P₀ A₀ A₁ kb = some (c, Y)) :
    toPoly P₁ * derivative (toPoly Y) + toPoly P₀ * toPoly Y = toPoly A₀ - C c * toPoly A₁ :=
  prdeSolveGen_sound h

/-- **Completeness of the packaged parametric solver.** -/
theorem prdeSolveFull_complete_map {P₁ P₀ A₀ A₁ : CPoly R} {kb : ℕ} (hP₀ : trim P₀ ≠ [])
    (hkb : ∀ k, odePiv P₁ P₀ k = 0 → k ≤ kb) (h : prdeSolveFull P₁ P₀ A₀ A₁ kb = none) :
    ¬∃ (c : S) (Ys : S[X]), (toPoly P₁).map ι * derivative Ys + (toPoly P₀).map ι * Ys =
      (toPoly A₀).map ι - C c * (toPoly A₁).map ι := by
  rintro ⟨c, Ys, hYs⟩
  set dg := odeDg P₁ P₀ with hdg
  have h1 : (toPoly P₁).natDegree ≤ dg + 1 := by
    have := natDegree_toPoly_le P₁
    have : (trim P₁).length - 2 ≤ dg := le_max_left _ _
    omega
  have h0 : (toPoly P₀).natDegree ≤ dg := (natDegree_toPoly_le P₀).trans (le_max_right _ _)
  have hpiv : ∀ k, odePiv P₁ P₀ k =
      (k : R) * (toPoly P₁).coeff (dg + 1) + (toPoly P₀).coeff dg := fun k ↦ by
    rw [odePiv, coeff_toPoly, coeff_toPoly]
  obtain ⟨hd₀, hlc₀, hlc₀0⟩ := natDegree_toPoly_of_trim_ne_nil hP₀
  have hab : (toPoly P₁).coeff (dg + 1) ≠ 0 ∨ (toPoly P₀).coeff dg ≠ 0 := by
    by_cases hcase : (trim P₁).length - 2 ≤ (trim P₀).length - 1
    · right
      rw [hdg, odeDg, max_eq_right hcase, hlc₀]
      exact hlc₀0
    · left
      have hP₁ : trim P₁ ≠ [] := fun h0' ↦ by rw [h0'] at hcase; simp at hcase
      obtain ⟨-, hlc₁, hlc₁0⟩ := natDegree_toPoly_of_trim_ne_nil hP₁
      have : dg + 1 = (trim P₁).length - 1 := by
        rw [hdg, odeDg, max_eq_left (by omega)]
        omega
      rw [this, hlc₁]
      exact hlc₁0
  have huniq : ∀ k k', odePiv P₁ P₀ k = 0 → odePiv P₁ P₀ k' = 0 → k = k' := by
    intro k k' hk hk'
    rw [hpiv] at hk hk'
    by_cases ha : (toPoly P₁).coeff (dg + 1) = 0
    · rw [ha, mul_zero, zero_add] at hk
      exact absurd hk (hab.resolve_left (not_not.mpr ha))
    · have : ((k : R) - k') * (toPoly P₁).coeff (dg + 1) = 0 := by linear_combination hk - hk'
      have := (mul_eq_zero.mp this).resolve_right ha
      exact_mod_cast sub_eq_zero.mp this
  have hYs' : opS ι P₁ P₀ Ys = (toPoly A₀).map ι - C c * (toPoly A₁).map ι := hYs
  have hbound := natDegree_le_of_opS' ι h1 h0 hpiv (kb := kb)
    (fun k hk hz ↦ absurd (hkb k hz) (by omega)) Ys _ hYs'
  have hA₀ := natDegree_toPoly_le A₀
  have hA₁ := natDegree_toPoly_le A₁
  have hB : ((toPoly A₀).map ι - C c * (toPoly A₁).map ι).natDegree ≤
      max ((trim A₀).length - 1) ((trim A₁).length - 1) := by
    refine (natDegree_sub_le _ _).trans (max_le_max ?_ ?_)
    · exact natDegree_map_le.trans hA₀
    · exact (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans hA₁)
  refine prdeSolveGen_complete_map ι h1 h0 hpiv huniq c Ys hYs' ?_ h
  have : max (((toPoly A₀).map ι - C c * (toPoly A₁).map ι).natDegree - dg) kb ≤
      max (max ((trim A₀).length - 1) ((trim A₁).length - 1) - dg) kb :=
    max_le_max (by omega) le_rfl
  omega

end CPoly
