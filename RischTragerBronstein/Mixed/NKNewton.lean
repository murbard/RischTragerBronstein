import RischTragerBronstein.Mixed.NKResOrdC

/-!
# Correctness of the Newton lifting codes

`nlStep`: `Θ ↦ Θ + a Tⁱ` with `a = −d [Tⁱ] Q(T, Θ)`. If `β` is a simple root of `Q(0, ·)` and
`d ∂Q(0, β) = 1`, the iterates starting from `β` are roots of `Q(T, ·)` modulo `Tᴹ`
(`nlIter_trunc`). Hence the generators `henselC` and `segHenselC` always pass the truncation
checks (`segHenselC_truncOK`): the Newton lifts used by the zero-residue and residue-matching
certificates exist.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Curves

section Newton

variable {F : Type*} [Field F]

/-- One Newton step at precision `i`. -/
noncomputable def nlStep (Q : F[X][X]) (d : F) (Θ : F[X]) (i : ℕ) : F[X] :=
  Θ + Polynomial.C (-(d * (Q.eval Θ).coeff i)) * X ^ i

lemma coeff_zero_eval (p : F[X][X]) (Θ : F[X]) :
    (p.eval Θ).coeff 0 = (p.map Polynomial.constantCoeff).eval (Θ.coeff 0) := by
  rw [eval_map, ← Polynomial.constantCoeff_apply, Polynomial.eval, Polynomial.hom_eval₂]
  rfl

/-- **One Newton step gains one order.** -/
lemma nlStep_spec (Q : F[X][X]) (d : F) (Θ : F[X]) (i : ℕ) (hi : 1 ≤ i)
    (hd : d * ((derivative Q).eval Θ).coeff 0 = 1)
    (hΘ : ∀ k < i, (Q.eval Θ).coeff k = 0) :
    (∀ k < i + 1, (Q.eval (nlStep Q d Θ i)).coeff k = 0) ∧ (nlStep Q d Θ i).coeff 0 = Θ.coeff 0 := by
  set a := -(d * (Q.eval Θ).coeff i) with ha
  set y : F[X] := Polynomial.C a * X ^ i with hy
  obtain ⟨kk, hkk⟩ := Q.binomExpansion Θ y
  have hy0 : y.coeff 0 = 0 := by
    rw [hy, coeff_C_mul_X_pow, if_neg (by omega)]
  refine ⟨fun k hk ↦ ?_, ?_⟩
  · rw [nlStep, ← ha, ← hy, hkk, coeff_add, coeff_add]
    have h2 : (kk * y ^ 2).coeff k = 0 := by
      have : kk * y ^ 2 = (kk * Polynomial.C (a ^ 2)) * X ^ (2 * i) := by
        rw [hy, C_pow]; ring
      rw [this, coeff_mul_X_pow', if_neg (by omega)]
    rw [h2, add_zero, hy, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hΘ k hk, if_neg (by omega), zero_add]
    · rw [if_pos le_rfl, Nat.sub_self, ha]
      linear_combination -((Q.eval Θ).coeff k) * hd
  · rw [nlStep, coeff_add, coeff_C_mul_X_pow, if_neg (by omega), add_zero]

/-- The iterates `Θ ↦ nlStep … i` for `i = 1, …, M − 1`, starting from `β`. -/
noncomputable def nlIter (Q : F[X][X]) (d : F) (β : F) (M : ℕ) : F[X] :=
  ((List.range M).drop 1).foldl (nlStep Q d) (Polynomial.C β)

lemma nlIter_foldl (Q : F[X][X]) (d β : F)
    (hβ : (Q.map Polynomial.constantCoeff).eval β = 0)
    (hd : d * ((derivative Q).map Polynomial.constantCoeff).eval β = 1) :
    ∀ n : ℕ, (∀ k < n + 1, (Q.eval ((List.range' 1 n).foldl (nlStep Q d) (Polynomial.C β))).coeff k
      = 0) ∧ ((List.range' 1 n).foldl (nlStep Q d) (Polynomial.C β)).coeff 0 = β
  | 0 => by
    refine ⟨fun k hk ↦ ?_, by simp⟩
    have : k = 0 := by omega
    subst this
    simp only [List.range'_zero, List.foldl_nil]
    rw [coeff_zero_eval, coeff_C_zero, hβ]
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := nlIter_foldl Q d β hβ hd n
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, one_mul]
    have hd' : d * ((derivative Q).eval
        ((List.range' 1 n).foldl (nlStep Q d) (Polynomial.C β))).coeff 0 = 1 := by
      rw [coeff_zero_eval, ih2]; exact hd
    obtain ⟨h1, h2⟩ := nlStep_spec Q d _ (1 + n) (by omega) hd' (fun k hk ↦ ih1 k (by omega))
    exact ⟨fun k hk ↦ h1 k (by omega), by rw [h2, ih2]⟩

/-- **The Newton iterates are roots modulo `Tᴹ`.** -/
theorem nlIter_trunc (Q : F[X][X]) (d β : F)
    (hβ : (Q.map Polynomial.constantCoeff).eval β = 0)
    (hd : d * ((derivative Q).map Polynomial.constantCoeff).eval β = 1) (M : ℕ) :
    ∀ k < M, (Q.eval (nlIter Q d β M)).coeff k = 0 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · intro k hk; omega
  have e : (List.range M).drop 1 = List.range' 1 (M - 1) := by
    rw [List.range_eq_range', List.drop_range']
  have := (nlIter_foldl Q d β hβ hd (M - 1)).1
  intro k hk
  rw [nlIter, e]
  exact this k (by omega)

end Newton

end Curves

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Tower.PrimN GTors Differential

section Codes

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {m : ℕ} {F : Type*} [Field F] [Differential F] (M : CField (LC m) F (MO Fc ks m))

/-- The semantic polynomial `∑ Qcᵢ Zⁱ` of a list of codes. -/
noncomputable def qSem (Qc : List (GPoly (LC m))) : F[X][X] :=
  ∑ i ∈ Finset.range Qc.length, Polynomial.C (GPoly.toPoly M (Qc.getD i [])) * X ^ i

lemma toPoly_evalPolyC_qSem (Qc : List (GPoly (LC m))) (Θ : GPoly (LC m)) :
    GPoly.toPoly M (evalPolyC Fc ks m Qc Θ) = (qSem M Qc).eval (GPoly.toPoly M Θ) := by
  rw [toPoly_evalPolyC, qSem, eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [eval_mul, eval_C, eval_pow, eval_X]

/-- The code step of the Newton lifting. -/
def nlStepC (Qc : List (GPoly (LC m))) (d : LC m) (Θ : GPoly (LC m)) (i : ℕ) : GPoly (LC m) :=
  Θ ++ [(MO Fc ks m).neg ((MO Fc ks m).mul d ((evalPolyC Fc ks m Qc Θ).getD i (MO Fc ks m).zero))]

lemma toPoly_nlStepC (Qc : List (GPoly (LC m))) (d : LC m) (Θ : GPoly (LC m)) :
    GPoly.toPoly M (nlStepC (Fc := Fc) (ks := ks) Qc d Θ Θ.length) =
      nlStep (qSem M Qc) (M.sem d) (GPoly.toPoly M Θ) Θ.length := by
  rw [nlStepC, GPoly.toPoly_append, nlStep]
  simp only [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, M.sem_neg, M.sem_mul]
  rw [← coeff_toPoly_sem, toPoly_evalPolyC_qSem]
  ring

lemma toPoly_nlFold (Qc : List (GPoly (LC m))) (d : LC m) :
    ∀ (n : ℕ) (Θ : GPoly (LC m)),
      GPoly.toPoly M ((List.range' Θ.length n).foldl (nlStepC (Fc := Fc) (ks := ks) Qc d) Θ) =
        (List.range' Θ.length n).foldl (nlStep (qSem M Qc) (M.sem d)) (GPoly.toPoly M Θ)
  | 0, Θ => by simp
  | n + 1, Θ => by
    rw [List.range'_succ, List.foldl_cons, List.foldl_cons]
    have hl : (nlStepC (Fc := Fc) (ks := ks) Qc d Θ Θ.length).length = Θ.length + 1 := by
      simp [nlStepC]
    have := toPoly_nlFold Qc d n (nlStepC (Fc := Fc) (ks := ks) Qc d Θ Θ.length)
    rw [hl] at this
    rw [this, toPoly_nlStepC]

lemma toPoly_qSem_map (Qc : List (GPoly (LC m))) :
    GPoly.toPoly M (Qc.map fun p ↦ p.getD 0 (MO Fc ks m).zero) =
      (qSem M Qc).map Polynomial.constantCoeff := by
  ext i
  rw [coeff_toPoly_sem, Polynomial.coeff_map, qSem, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  by_cases hi : i < Qc.length
  · rw [if_pos (Finset.mem_range.mpr hi), Polynomial.constantCoeff_apply, coeff_toPoly_sem]
    have hg := List.getD_map (fun p : GPoly (LC m) ↦ p.getD 0 (MO Fc ks m).zero)
      (l := Qc) (n := i) (d := [])
    simp only [List.getD_nil] at hg
    rw [hg]
  · rw [if_neg (by simpa using hi), map_zero, List.getD_eq_default _ _ (by simpa using hi),
      M.sem_zero]

include M in
/-- **The Newton lifting codes pass the truncation check.** -/
theorem newton_truncOK (Qc : List (GPoly (LC m))) (β : LC m) (Mn : ℕ)
    (hroot : (MO Fc ks m).isZero
      (evalLC Fc ks m (Qc.map fun p ↦ p.getD 0 (MO Fc ks m).zero) β) = true)
    (hder : (MO Fc ks m).isZero (evalLC Fc ks m (GPoly.derivX (MO Fc ks m)
      (Qc.map fun p ↦ p.getD 0 (MO Fc ks m).zero)) β) = false) :
    truncOKC Fc ks m Mn (evalPolyC Fc ks m Qc (((List.range Mn).drop 1).foldl
      (nlStepC (Fc := Fc) (ks := ks) Qc ((MO Fc ks m).inv (evalLC Fc ks m (GPoly.derivX (MO Fc ks m)
        (Qc.map fun p ↦ p.getD 0 (MO Fc ks m).zero)) β))) [β])) = true := by
  set R := Qc.map fun p ↦ p.getD 0 (MO Fc ks m).zero with hR
  set d := (MO Fc ks m).inv (evalLC Fc ks m (GPoly.derivX (MO Fc ks m) R) β) with hd
  have hβ : ((qSem M Qc).map Polynomial.constantCoeff).eval (M.sem β) = 0 := by
    rw [← toPoly_qSem_map, ← sem_evalLC]
    exact (M.isZero_iff _).mp hroot
  have hd1 : M.sem d * ((derivative (qSem M Qc)).map Polynomial.constantCoeff).eval (M.sem β) = 1 := by
    rw [← Polynomial.derivative_map, ← toPoly_qSem_map, ← GPoly.toPoly_derivX, ← sem_evalLC, hd,
      M.sem_inv]
    refine inv_mul_cancel₀ fun h0 ↦ ?_
    rw [← M.isZero_iff] at h0
    rw [h0] at hder
    exact absurd hder (by simp)
  have htr := nlIter_trunc (qSem M Qc) (M.sem d) (M.sem β) hβ hd1 Mn
  have hfold : GPoly.toPoly M (((List.range Mn).drop 1).foldl
      (nlStepC (Fc := Fc) (ks := ks) Qc d) [β]) = nlIter (qSem M Qc) (M.sem d) (M.sem β) Mn := by
    rcases Nat.eq_zero_or_pos Mn with h0 | hpos
    · subst h0; simp [nlIter, GPoly.toPoly_cons, GPoly.toPoly_nil]
    have e : (List.range Mn).drop 1 = List.range' ([β] : GPoly (LC m)).length (Mn - 1) := by
      rw [List.range_eq_range', List.drop_range']; simp
    rw [e, toPoly_nlFold, nlIter, show ([β] : GPoly (LC m)).length = 1 from rfl]
    rw [List.range_eq_range', List.drop_range']
    simp [GPoly.toPoly_cons, GPoly.toPoly_nil]
  unfold truncOKC
  rw [List.all_eq_true]
  intro k hk
  rw [M.isZero_iff, ← coeff_toPoly_sem, toPoly_evalPolyC_qSem, hfold]
  exact htr k (List.mem_range.mp hk)

end Codes

section Seg

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {m : ℕ} {F : Type*} [Field F] [Differential F] (M : CField (LC m) F (MO Fc ks m))

lemma segHenselC_eq (e : ℕ) (s K0 : ℤ) (Pp : List (GPoly (LC m))) (Mn : ℕ) (β : LC m) :
    segHenselC Fc ks m e s K0 Pp Mn β = ((List.range Mn).drop 1).foldl
      (nlStepC (Fc := Fc) (ks := ks) (segPolyC Fc ks m e s K0 Pp)
        ((MO Fc ks m).inv (evalLC Fc ks m (GPoly.derivX (MO Fc ks m)
          (segResidC Fc ks m e s K0 Pp)) β))) [β] := rfl

lemma nlFold_head (Qc : List (GPoly (LC m))) (d β : LC m) :
    ∀ l : List ℕ, (l.foldl (nlStepC (Fc := Fc) (ks := ks) Qc d) [β]).getD 0 (MO Fc ks m).zero = β := by
  intro l
  suffices h : ∀ (l : List ℕ) (Θ : GPoly (LC m)), Θ ≠ [] →
      (l.foldl (nlStepC (Fc := Fc) (ks := ks) Qc d) Θ).getD 0 (MO Fc ks m).zero =
        Θ.getD 0 (MO Fc ks m).zero from h l [β] (by simp)
  intro l
  induction l with
  | nil => intro Θ _; rfl
  | cons i l ih =>
    intro Θ hΘ
    rw [List.foldl_cons, ih _ (by simp [nlStepC])]
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hΘ
    simp [nlStepC]

include M in
/-- **The segment Newton lifts pass the truncation check.** -/
theorem segHenselC_truncOK (e : ℕ) (s K0 : ℤ) (Pp : List (GPoly (LC m))) (Mn : ℕ) (β : LC m)
    (hroot : (MO Fc ks m).isZero (evalLC Fc ks m (segResidC Fc ks m e s K0 Pp) β) = true)
    (hder : (MO Fc ks m).isZero (evalLC Fc ks m (GPoly.derivX (MO Fc ks m)
      (segResidC Fc ks m e s K0 Pp)) β) = false) :
    truncOKC Fc ks m Mn (segEvalC Fc ks m e s K0 Pp (segHenselC Fc ks m e s K0 Pp Mn β)) = true := by
  rw [segHenselC_eq, segEvalC]
  exact newton_truncOK M _ β Mn hroot hder

lemma segHenselC_head (e : ℕ) (s K0 : ℤ) (Pp : List (GPoly (LC m))) (Mn : ℕ) (β : LC m) :
    (segHenselC Fc ks m e s K0 Pp Mn β).getD 0 (MO Fc ks m).zero = β := by
  rw [segHenselC_eq]; exact nlFold_head _ _ _ _

end Seg

section DerivComplete

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m} {m : ℕ}
variable {Cs F : Type*} [Field Cs] [CharZero Cs] [Field F] [Differential F] [CharZero F] (ι : Cs →+* F)
  (M : CField (LC m) F (MO Fc ks m))

/-- **Completeness of the derivative test.** -/
lemma derivTestC_complete
    (hrde : RdeSpecK ι M (M.sem (fCode (MO Fc ks m) ⟨(MO Fc ks m).one, []⟩))
      (prdeC Fc ks lv m ⟨(MO Fc ks m).one, []⟩))
    (c : LC m) (h : ∃ z : F, z′ = M.sem c) : derivTestC Fc ks lv m c = true := by
  obtain ⟨z, hz⟩ := h
  have hf0 : M.sem (fCode (MO Fc ks m) ⟨(MO Fc ks m).one, []⟩) = 0 := by
    rw [sem_fCode]
    simp [logSumV, M.sem_one]
  obtain ⟨βs, hβs, -⟩ := hrde.complete [c] [1] (fun i hi ↦ by
    simp only [List.length_cons, List.length_nil] at hi
    rw [List.getD_eq_default _ _ (by simpa using hi)]) z (by
      rw [hf0, zero_mul, add_zero, hz, sC]
      simp)
  have h0 := hβs 0
  simp only [List.getD_cons_zero] at h0
  unfold derivTestC
  rw [List.any_eq_true]
  by_contra hno
  push_neg at hno
  rw [Finset.sum_eq_zero (fun kk hkk ↦ by
    have hmem : (prdeC Fc ks lv m ⟨(MO Fc ks m).one, []⟩ [c]).getD kk ([], (MO Fc ks m).zero) ∈
        prdeC Fc ks lv m ⟨(MO Fc ks m).one, []⟩ [c] := by
      rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hkk)]
      exact List.getElem_mem _
    have := hno _ hmem
    simp only [bne_iff_ne, ne_eq, Bool.not_eq_true, decide_eq_false_iff_not, not_not] at this
    rw [show ((prdeC Fc ks lv m ⟨(MO Fc ks m).one, []⟩ [c]).getD kk ([], (MO Fc ks m).zero)).1.getD 0 0
      = 0 by simpa using this, map_zero, mul_zero])] at h0
  exact one_ne_zero h0

end DerivComplete

end Curves.MT
