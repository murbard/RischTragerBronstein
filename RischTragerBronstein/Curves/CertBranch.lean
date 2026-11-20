import RischTragerBronstein.Curves.HenselQ
import RischTragerBronstein.Computable.ResidueAnnihilator
import RischTragerBronstein.Algebraic.SupBivar

/-!
# Certified truncated branches

Computable bivariate evaluation `bivEval W s Y = W(s(T), Y(T))` on coefficient lists, the
`Y`-derivative `derivYB`, the order `ordC`, and a certificate check `certCheck` for a branch
system above `x = a`: `N` and approximate roots `ỹₖ ∈ F[T]` with, for each `k`,
`ord F_Y(a + Tᴺ, ỹₖ) = Bₖ < prec` and `ord F(a + Tᴺ, ỹₖ) ≥ Bₖ + prec`, pairwise distinct below
`T^prec`. `certCheck_spec`: then over any field `K ⊇ F`, `F(a + Tᴺ, Y) = ∏ₖ (Y − yₖ)` with true
roots `yₖ ≡ ỹₖ (mod T^prec)` (quantitative Hensel, `split_of_approx`).
-/

open Polynomial

namespace Curves

open CPoly Sup Differential

section Defs

variable {F : Type*} [Field F] [DecidableEq F]

/-- `Tᴺ`. -/
def xPowC (N : ℕ) : CPoly F := List.replicate N 0 ++ [1]

/-- `a + Tᴺ`. -/
def shiftC (a : F) (N : ℕ) : CPoly F := add [a] (xPowC N)

/-- `W(s, Y)` (Horner in `Y`). -/
def bivEval (W : BPoly F) (s Y : CPoly F) : CPoly F :=
  W.foldr (fun c acc ↦ add (compC c s) (mul Y acc)) []

/-- The `Y`-derivative. -/
def derivYB : BPoly F → BPoly F
  | [] => []
  | _ :: W => addB W ([] :: derivYB W)

/-- The index of the first non-zero coefficient (the length if there is none). -/
def ordC (P : CPoly F) : ℕ := P.findIdx (· ≠ 0)

/-- A branch certificate above a point. -/
structure BranchCert (F : Type*) where
  N : ℕ
  ys : List (CPoly F)
  prec : ℕ

/-- The check for one approximate root, with exact evaluations (the semantics of `rootCheck`). -/
def rootCheckFull (Fc : BPoly F) (a : F) (N prec : ℕ) (y : CPoly F) : Bool :=
  let D := bivEval (derivYB Fc) (shiftC a N) y
  let H := bivEval Fc (shiftC a N) y
  decide (ordC D < prec) && decide (ordC D < D.length) &&
    (List.range (ordC D + prec)).all fun i ↦ decide (H.getD i 0 = 0)

/-- `W(s, Y)` modulo `Tᴷ` (Horner, truncated at every step). -/
def bivEvalT (W : BPoly F) (s Y : CPoly F) (K : ℕ) : CPoly F :=
  W.foldr (fun c acc ↦ (add (compC c s) (mul Y acc)).take K) []

/-- **The check for one approximate root** (truncated evaluations; `rootCheck_facts`: it implies
the exact check). -/
def rootCheck (Fc : BPoly F) (a : F) (N prec : ℕ) (y : CPoly F) : Bool :=
  let D := bivEvalT (derivYB Fc) (shiftC a N) y prec
  let H := bivEvalT Fc (shiftC a N) y (ordC D + prec)
  decide (ordC D < prec) && decide (ordC D < D.length) &&
    (List.range (ordC D + prec)).all fun i ↦ decide (H.getD i 0 = 0)

/-- Pairwise separation below `T^prec`. -/
def sepCheck (ys : List (CPoly F)) (prec : ℕ) : Bool :=
  (List.range ys.length).all fun k ↦ (List.range ys.length).all fun l ↦
    decide (k = l) || (List.range prec).any fun i ↦
      decide ((ys.getD k []).getD i 0 ≠ (ys.getD l []).getD i 0)

/-- **The certificate check.** -/
def certCheck (Fc : BPoly F) (n : ℕ) (a : F) (c : BranchCert F) : Bool :=
  decide (0 < c.N) && decide (c.ys.length = n) &&
    c.ys.all (rootCheck Fc a c.N c.prec) && sepCheck c.ys c.prec

end Defs

section Sem

variable {F : Type*} [Field F] [DecidableEq F]

lemma toPoly_xPowC (N : ℕ) : toPoly (xPowC N : CPoly F) = X ^ N := by
  induction N with
  | zero => simp [xPowC]
  | succ N ih =>
    simp only [xPowC, List.replicate_succ, List.cons_append, toPoly_cons, map_zero, zero_add] at ih ⊢
    rw [ih, pow_succ, mul_comm]

lemma toPoly_shiftC (a : F) (N : ℕ) : toPoly (shiftC a N) = Polynomial.C a + X ^ N := by
  rw [shiftC, toPoly_add, toPoly_xPowC]; simp

lemma toPoly_bivEval (W : BPoly F) (s Y : CPoly F) :
    toPoly (bivEval W s Y) = ((toB W).map (compRingHom (toPoly s))).eval (toPoly Y) := by
  induction W with
  | nil => simp [bivEval]
  | cons c W ih =>
    simp only [bivEval, List.foldr_cons] at ih ⊢
    rw [toPoly_add, toPoly_compC, toPoly_mul, ih, toB_cons, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_add, eval_mul, eval_C, eval_X]
    rfl

lemma toB_derivYB (W : BPoly F) : toB (derivYB W) = derivative (toB W) := by
  induction W with
  | nil => simp [derivYB]
  | cons a W ih =>
    simp only [derivYB, toB_addB, toB_cons, toPoly_nil, map_zero, zero_add, ih, derivative_add,
      derivative_C, derivative_mul, derivative_X, one_mul]

lemma getD_lt_ordC (P : CPoly F) (i : ℕ) (hi : i < ordC P) : P.getD i 0 = 0 := by
  by_cases hl : i < P.length
  · rw [List.getD_eq_getElem _ _ hl]
    have := List.not_of_lt_findIdx hi
    simpa using this
  · rw [List.getD_eq_default _ _ (not_lt.mp hl)]

lemma getD_ordC (P : CPoly F) (h : ordC P < P.length) : P.getD (ordC P) 0 ≠ 0 := by
  rw [List.getD_eq_getElem _ _ h]
  have := List.findIdx_getElem (w := h)
  simpa [ordC] using this

lemma toPoly_sub_take_dvd (L : CPoly F) (K : ℕ) : X ^ K ∣ toPoly L - toPoly (L.take K) := by
  have h := toPoly_append (L.take K) (L.drop K)
  rw [List.take_append_drop] at h
  rw [h, add_sub_cancel_left]
  by_cases hK : K ≤ L.length
  · rw [List.length_take, min_eq_left hK]; exact dvd_mul_right _ _
  · rw [List.drop_eq_nil_of_le (by omega), toPoly_nil, mul_zero]; exact dvd_zero _

lemma bivEvalT_dvd (W : BPoly F) (s Y : CPoly F) (K : ℕ) :
    X ^ K ∣ toPoly (bivEval W s Y) - toPoly (bivEvalT W s Y K) := by
  induction W with
  | nil => simp [bivEval, bivEvalT]
  | cons c W ih =>
    simp only [bivEval, bivEvalT, List.foldr_cons] at ih ⊢
    set E := W.foldr (fun c acc ↦ add (compC c s) (mul Y acc)) [] with hE
    set ET := W.foldr (fun c acc ↦ (add (compC c s) (mul Y acc)).take K) [] with hET
    have e : toPoly (add (compC c s) (mul Y E)) - toPoly ((add (compC c s) (mul Y ET)).take K) =
        toPoly Y * (toPoly E - toPoly ET) + (toPoly (add (compC c s) (mul Y ET)) -
          toPoly ((add (compC c s) (mul Y ET)).take K)) := by
      simp only [toPoly_add, toPoly_mul]; ring
    rw [e]
    exact dvd_add (Dvd.dvd.mul_left ih _) (toPoly_sub_take_dvd _ _)

lemma getD_eq_of_X_pow_dvd {P Q : CPoly F} {K : ℕ} (h : X ^ K ∣ toPoly P - toPoly Q) (i : ℕ)
    (hi : i < K) : P.getD i 0 = Q.getD i 0 := by
  obtain ⟨r, hr⟩ := h
  have := congrArg (·.coeff i) hr
  simp only [coeff_sub, coeff_toPoly, coeff_X_pow_mul', if_neg (not_le.mpr hi)] at this
  exact sub_eq_zero.mp this

lemma ordC_eq_of {P : CPoly F} {o : ℕ} (h0 : ∀ i < o, P.getD i 0 = 0) (h1 : P.getD o 0 ≠ 0) :
    ordC P = o := by
  rcases lt_trichotomy (ordC P) o with h | h | h
  · by_cases hl : ordC P < P.length
    · exact absurd (h0 _ h) (getD_ordC P hl)
    · exact absurd (List.getD_eq_default _ _ (by omega)) h1
  · exact h
  · exact absurd (getD_lt_ordC P o h) h1

/-- **The truncated check implies the exact one.** -/
theorem rootCheck_facts {Fc : BPoly F} {a : F} {N prec : ℕ} {y : CPoly F}
    (h : rootCheck Fc a N prec y = true) :
    ordC (bivEval (derivYB Fc) (shiftC a N) y) < prec ∧
      ordC (bivEval (derivYB Fc) (shiftC a N) y) < (bivEval (derivYB Fc) (shiftC a N) y).length ∧
      ∀ i < ordC (bivEval (derivYB Fc) (shiftC a N) y) + prec,
        (bivEval Fc (shiftC a N) y).getD i 0 = 0 := by
  simp only [rootCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  set DT := bivEvalT (derivYB Fc) (shiftC a N) y prec with hDT
  set D := bivEval (derivYB Fc) (shiftC a N) y with hD
  have hag : ∀ i < prec, D.getD i 0 = DT.getD i 0 :=
    getD_eq_of_X_pow_dvd (bivEvalT_dvd _ _ _ _)
  have ho : ordC D = ordC DT := ordC_eq_of
    (fun i hi ↦ by rw [hag i (by omega)]; exact getD_lt_ordC DT i hi)
    (by rw [hag _ h1]; exact getD_ordC DT h2)
  have hne : D.getD (ordC DT) 0 ≠ 0 := by rw [hag _ h1]; exact getD_ordC DT h2
  refine ⟨by rw [ho]; exact h1, ?_, fun i hi ↦ ?_⟩
  · rw [ho]
    by_contra hl
    exact hne (List.getD_eq_default _ _ (by omega))
  · rw [ho] at hi
    rw [getD_eq_of_X_pow_dvd (bivEvalT_dvd Fc (shiftC a N) y (ordC DT + prec)) i hi]
    exact h3 i hi

end Sem

section Spec

variable {F : Type*} [Field F] [DecidableEq F]
variable {C K : Type*} [Field C] [Field K] [Algebra C K]

/-- `P ↦ P(T)` into `K⟦T⟧` (coefficients through `ψ`). -/
noncomputable def thetaT (ψ : F →+* K) : F[X] →+* PowerSeries K :=
  (Polynomial.coeToPowerSeries.ringHom (R := K)).comp (mapRingHom ψ)

/-- `P ↦ P(a + Tᴺ)` into `K⟦T⟧`. -/
noncomputable def thetaN (ψ : F →+* K) (a : F) (N : ℕ) : F[X] →+* PowerSeries K :=
  (thetaT ψ).comp (compRingHom (Polynomial.C a + X ^ N))

lemma thetaT_apply (ψ : F →+* K) (P : F[X]) :
    thetaT ψ P = ((P.map ψ : K[X]) : PowerSeries K) := rfl

lemma coeff_thetaT (ψ : F →+* K) (P : CPoly F) (i : ℕ) :
    PowerSeries.coeff i (thetaT ψ (toPoly P)) = ψ (P.getD i 0) := by
  rw [thetaT_apply, Polynomial.coeff_coe, coeff_map, coeff_toPoly]

lemma ofPS_thetaN (ψ₀ : F →+* C) (a : F) (N : ℕ) (P : F[X]) :
    HahnSeries.ofPowerSeries ℤ K (thetaN ((algebraMap C K).comp ψ₀) a N P) =
      branchSub N (algebraMap C K (ψ₀ a)) (P.map ψ₀) := by
  rw [branchSub_apply, thetaN, RingHom.comp_apply, thetaT_apply, Polynomial.map_map]
  congr 2
  rw [coe_compRingHom_apply, Polynomial.map_comp]
  simp [add_comm]

lemma X_pow_dvd_thetaT (ψ : F →+* K) (P : CPoly F) (A : ℕ) (h : ∀ i < A, P.getD i 0 = 0) :
    (PowerSeries.X : PowerSeries K) ^ A ∣ thetaT ψ (toPoly P) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro i hi
  rw [coeff_thetaT, h i hi, map_zero]

lemma thetaT_ordC (ψ : F →+* K) (P : CPoly F) (h : ordC P < P.length) :
    thetaT ψ (toPoly P) = PowerSeries.X ^ ordC P * thetaT ψ (toPoly (P.drop (ordC P))) ∧
      PowerSeries.constantCoeff (thetaT ψ (toPoly (P.drop (ordC P)))) ≠ 0 := by
  constructor
  · have htake : toPoly (P.take (ordC P)) = 0 := by
      ext i
      rw [coeff_toPoly, Polynomial.coeff_zero]
      by_cases hi : i < ordC P
      · rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, ← List.getD_eq_getElem?_getD,
          getD_lt_ordC P i hi]
      · rw [List.getD_eq_default _ _ (by rw [List.length_take]; omega)]
    conv_lhs => rw [← List.take_append_drop (ordC P) P]
    rw [toPoly_append, htake, zero_add, List.length_take, min_eq_left h.le, map_mul, map_pow]
    congr 1
    rw [thetaT_apply]
    simp
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_thetaT, List.getD_eq_getElem?_getD,
      List.getElem?_drop, add_zero, ← List.getD_eq_getElem?_getD]
    exact (map_ne_zero_iff ψ ψ.injective).mpr (getD_ordC P h)

lemma thetaT_bivEval (ψ : F →+* K) (W : BPoly F) (a : F) (N : ℕ) (Y : CPoly F) :
    thetaT ψ (toPoly (bivEval W (shiftC a N) Y)) =
      ((toB W).map (thetaN ψ a N)).eval (thetaT ψ (toPoly Y)) := by
  rw [toPoly_bivEval, toPoly_shiftC, eval_map, hom_eval₂, eval_map]
  rfl

/-- **Certified branches**: a passing certificate yields the full splitting of `F(a + Tᴺ, Y)` over
`K⟦T⟧` with roots congruent to the approximations modulo `T^prec`. -/
theorem certCheck_spec (Fc : BPoly F) (n : ℕ) (hmon : (toB Fc).Monic)
    (hn : (toB Fc).natDegree = n) (a : F) (c : BranchCert F) (h : certCheck Fc n a c = true)
    (ψ₀ : F →+* C) :
    ∃ y : Fin n → PowerSeries K,
      (∀ k : Fin n, (PowerSeries.X : PowerSeries K) ^ c.prec ∣
        y k - thetaT ((algebraMap C K).comp ψ₀) (toPoly (c.ys.getD k []))) ∧
      Function.Injective y ∧ ((toB Fc).map (mapRingHom ψ₀)).map (branchSub c.N (algebraMap C K (ψ₀ a))) =
        ∏ k, (X - Polynomial.C (HahnSeries.ofPowerSeries ℤ K (y k))) := by
  classical
  simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hN, hlen⟩, hroots⟩, hsep⟩ := h
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  set H := (toB Fc).map (thetaN ψ a c.N) with hH
  have hHm : H.Monic := hmon.map _
  have hHn : H.natDegree = n := by rw [hH, hmon.natDegree_map, hn]
  set yk : Fin n → CPoly F := fun k ↦ c.ys.getD k [] with hyk
  have hmem : ∀ k : Fin n, yk k ∈ c.ys := fun k ↦ by
    simp only [hyk]
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact k.2)]
    exact List.getElem_mem _
  set Dk := fun k : Fin n ↦ bivEval (derivYB Fc) (shiftC a c.N) (yk k) with hDk
  set Hk := fun k : Fin n ↦ bivEval Fc (shiftC a c.N) (yk k) with hHk
  have hrc : ∀ k, ordC (Dk k) < c.prec ∧ ordC (Dk k) < (Dk k).length ∧
      ∀ i < ordC (Dk k) + c.prec, (Hk k).getD i 0 = 0 := by
    intro k
    exact rootCheck_facts (hroots (yk k) (hmem k))
  obtain ⟨y, hy, hyinj, hsplit⟩ := split_of_approx H hHm hHn (fun k ↦ thetaT ψ (toPoly (yk k)))
    (fun k ↦ ordC (Dk k) + c.prec) (fun k ↦ ordC (Dk k))
    (fun k ↦ thetaT ψ (toPoly ((Dk k).drop (ordC (Dk k)))))
    (fun k ↦ by
      rw [hH, ← thetaT_bivEval]
      exact X_pow_dvd_thetaT ψ _ _ (hrc k).2.2)
    (fun k ↦ by
      rw [hH, Polynomial.derivative_map, ← toB_derivYB, ← thetaT_bivEval]
      exact (thetaT_ordC ψ _ (hrc k).2.1).1)
    (fun k ↦ (thetaT_ordC ψ _ (hrc k).2.1).2)
    (fun k ↦ by have := (hrc k).1; omega)
    (fun k l hkl ↦ by
      rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, min_self, PowerSeries.X_pow_dvd_iff]
      intro hall
      simp only [sepCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
        List.any_eq_true] at hsep
      rcases hsep k (by rw [hlen]; exact k.2) l (by rw [hlen]; exact l.2) with h1 | ⟨i, hi, hne⟩
      · exact hkl (Fin.ext h1)
      · have := hall i hi
        rw [map_sub, coeff_thetaT, coeff_thetaT, sub_eq_zero] at this
        exact hne (ψ.injective this))
  refine ⟨y, fun k ↦ by have := hy k; rwa [Nat.add_sub_cancel_left] at this, hyinj, ?_⟩
  rw [← hsplit, hH, Polynomial.map_map, Polynomial.map_map]
  congr 1
  exact RingHom.ext fun P ↦ (ofPS_thetaN ψ₀ a c.N P).symm

end Spec

end Curves
