import RischTragerBronstein.Curves.InfEval
import RischTragerBronstein.Computable.ResultantC
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Computing `discR = Res_Y(F, F_Y)`

* `resultant_deriv_map_split`: along a split fibre, `g(Res(F, F_Y)) = ∏ⱼ F_Y(rⱼ)`;
* `natDegree_disc_le`: `deg Res(F, F_Y) ≤ n(n − 1)k` (from the branches above infinity);
* `discAt Fc c = Res(F(c, Y), F_Y(c, Y))` computed by `resC` (`discAt_eq`);
* `discRC`: Lagrange interpolation of `discAt` at `0, 1, …, n(n − 1)k` (`toPoly_discRC`).
-/

open Polynomial HahnSeries

namespace Curves

open CPoly Sup Differential

section Split

variable {C : Type*} [Field C]

lemma resultant_deriv_map_split {L' : Type*} [Field L'] (Fp : C[X][X]) (hF : Fp.Monic)
    (g : C[X] →+* L') (r : Fin Fp.natDegree → L')
    (hsplit : Fp.map g = ∏ k, (X - Polynomial.C (r k))) :
    g (resultant Fp (derivative Fp) Fp.natDegree (Fp.natDegree - 1)) =
      ∏ j, (derivative (∏ k, (X - Polynomial.C (r k)))).eval (r j) := by
  have hlist : ∏ k, (X - Polynomial.C (r k)) =
      ((List.ofFn r).map fun a ↦ X - Polynomial.C a).prod := by
    rw [List.map_ofFn, List.prod_ofFn]; rfl
  have hdeg : (derivative (((List.ofFn r).map fun a ↦ X - Polynomial.C a).prod)).natDegree ≤
      Fp.natDegree - 1 :=
    (natDegree_derivative_le _).trans (by rw [← hlist, ← hsplit, hF.natDegree_map])
  have h := resultant_list_prod (List.ofFn r) _ _ hdeg
  rw [List.length_ofFn] at h
  rw [← resultant_map_map, ← Polynomial.derivative_map, hsplit, hlist, h, List.map_ofFn,
    List.prod_ofFn]
  rfl

variable [CharZero C]

/-- **Degree bound for the discriminant.** -/
theorem natDegree_disc_le (Fp : C[X][X]) (hF : Fp.Monic) (k : ℕ)
    (hk : ∀ i, (Fp.coeff i).natDegree ≤ k) :
    (resultant Fp (derivative Fp) Fp.natDegree (Fp.natDegree - 1)).natDegree ≤
      Fp.natDegree * (Fp.natDegree - 1) * k := by
  classical
  set K := AlgebraicClosure C
  set R := resultant Fp (derivative Fp) Fp.natDegree (Fp.natDegree - 1) with hR
  by_cases hR0 : R = 0
  · rw [hR0, natDegree_zero]; exact Nat.zero_le _
  obtain ⟨N, hN, l, hl, hsplitl, hroots⟩ := split_inf (K := K) Fp hF k hk
  obtain ⟨r, hrl, hsplit⟩ := split_fin Fp (infSub N) l hl hsplitl
  have hN0 : 0 < N := Nat.pos_of_ne_zero hN
  have hr : ∀ j, LowerBd (r j) (-((k * N : ℕ) : ℤ)) := fun j ↦ by
    obtain ⟨w, hw⟩ := hroots (r j) (hrl j)
    rw [hw]
    have := (lowerBd_ofPS w).mul (lowerBd_single (-(k * N : ℤ)) (1 : K))
    rw [zero_add] at this
    push_cast; exact this
  have hmap := resultant_deriv_map_split Fp hF (infSub (K := K) N) r hsplit
  have hbd : LowerBd (infSub (K := K) N R)
      (-((Fp.natDegree * ((Fp.natDegree - 1) * (k * N)) : ℕ) : ℤ)) := by
    rw [hR, hmap]
    have := polyLB_prod (K := K) Finset.univ
      (fun j ↦ Polynomial.C ((derivative (∏ k, (X - Polynomial.C (r k)))).eval (r j)))
      (b := -(((Fp.natDegree - 1) * (k * N) : ℕ) : ℤ)) (fun j _ ↦ by
        refine polyLB_C ?_
        rw [eval_derivative_prod]
        have := polyLB_prod (K := K) (Finset.univ.erase j)
          (fun i ↦ Polynomial.C (r j - r i)) (b := -((k * N : ℕ) : ℤ))
          (fun i _ ↦ polyLB_C ((hr j).sub (hr i))) 0
        rw [← map_prod, coeff_C_zero, Finset.card_erase_of_mem (Finset.mem_univ j),
          Finset.card_univ, Fintype.card_fin] at this
        convert this using 1
        push_cast [Nat.cast_sub (Fin.pos j)]
        ring) 0
    rw [← map_prod, coeff_C_zero, Finset.card_univ, Fintype.card_fin] at this
    convert this using 1
    push_cast; ring
  have hne : infSub (C := C) (K := K) N R ≠ 0 := infSub_ne_zero N hN0 R hR0
  have hord := order_infSub (C := C) (K := K) N hN0 R hR0
  have hle : ¬ (infSub (K := K) N R).order <
      -((Fp.natDegree * ((Fp.natDegree - 1) * (k * N)) : ℕ) : ℤ) := fun hlt ↦
    HahnSeries.coeff_order_eq_zero.not.mpr hne (hbd _ hlt)
  rw [hord] at hle
  push Not at hle
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN0
  have : (N : ℤ) * R.natDegree ≤ N * (Fp.natDegree * (Fp.natDegree - 1) * k : ℕ) := by
    push_cast at hle ⊢; nlinarith
  exact_mod_cast le_of_mul_le_mul_left this hN'

end Split

section Comp

variable {F : Type*} [Field F] [DecidableEq F]

/-- `F(c, Y)`. -/
def evalFibre (Fc : BPoly F) (c : F) : CPoly F := Fc.map fun q ↦ Kron.evalC q c

/-- `Res(F(c, Y), F_Y(c, Y))`. -/
def discAt (Fc : BPoly F) (c : F) : F := resC (evalFibre Fc c) (evalFibre (derivYB Fc) c)

/-- `∏_{j ∈ js, j ≠ i} (X − xⱼ)`. -/
def prodNumL (xs : List F) (i : ℕ) : List ℕ → CPoly F
  | [] => [1]
  | j :: js => if j = i then prodNumL xs i js else mul [-(xs.getD j 0), 1] (prodNumL xs i js)

/-- `∏_{j ∈ js, j ≠ i} (xᵢ − xⱼ)`. -/
def prodDenL (xs : List F) (i : ℕ) : List ℕ → F
  | [] => 1
  | j :: js => if j = i then prodDenL xs i js else (xs.getD i 0 - xs.getD j 0) * prodDenL xs i js

/-- `∑_{i ∈ is} vᵢ/denᵢ ∏_{j ≠ i} (X − xⱼ)`. -/
def interpL (xs vs : List F) (js : List ℕ) : List ℕ → CPoly F
  | [] => []
  | i :: is => add (smul (vs.getD i 0 / prodDenL xs i js) (prodNumL xs i js)) (interpL xs vs js is)

/-- **Lagrange interpolation.** -/
def interpC (xs vs : List F) : CPoly F :=
  interpL xs vs (List.range xs.length) (List.range xs.length)

/-- The sample points `0, 1, …, d`. -/
def natPts (d : ℕ) : List F := (List.range (d + 1)).map fun i : ℕ ↦ (i : F)

/-- **`Res_Y(F, F_Y)` by interpolation.** -/
def discRC (Fc : BPoly F) (n k : ℕ) : CPoly F :=
  interpC (natPts (n * (n - 1) * k)) ((natPts (n * (n - 1) * k)).map (discAt Fc))

end Comp

section CompSem

variable {F : Type*} [Field F] [DecidableEq F]

lemma toPoly_evalFibre (Fc : BPoly F) (c : F) :
    toPoly (evalFibre Fc c) = (toB Fc).map (evalRingHom c) := by
  induction Fc with
  | nil => simp [evalFibre]
  | cons q W ih =>
    simp only [evalFibre, List.map_cons, toPoly_cons] at ih ⊢
    rw [ih, toB_cons, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Kron.evalC_eq, coe_evalRingHom]

lemma toPoly_prodNumL (xs : List F) (i : ℕ) (js : List ℕ) (hjs : js.Nodup) :
    toPoly (prodNumL xs i js) = ∏ j ∈ js.toFinset.erase i, (X - Polynomial.C (xs.getD j 0)) := by
  classical
  induction js with
  | nil => simp [prodNumL]
  | cons j js ih =>
    have hj : j ∉ js := (List.nodup_cons.mp hjs).1
    have hjs' := (List.nodup_cons.mp hjs).2
    rw [List.toFinset_cons]
    by_cases hji : j = i
    · subst hji
      rw [prodNumL, if_pos rfl, ih hjs', Finset.erase_insert (by simpa using hj),
        Finset.erase_eq_of_notMem (by simpa using hj)]
    · rw [prodNumL, if_neg hji, toPoly_mul, ih hjs', Finset.erase_insert_of_ne hji,
        Finset.prod_insert (by simp [hj])]
      simp [sub_eq_add_neg, add_comm]

lemma prodDenL_eq (xs : List F) (i : ℕ) (js : List ℕ) (hjs : js.Nodup) :
    prodDenL xs i js = ∏ j ∈ js.toFinset.erase i, (xs.getD i 0 - xs.getD j 0) := by
  classical
  induction js with
  | nil => simp [prodDenL]
  | cons j js ih =>
    have hj : j ∉ js := (List.nodup_cons.mp hjs).1
    have hjs' := (List.nodup_cons.mp hjs).2
    rw [List.toFinset_cons]
    by_cases hji : j = i
    · subst hji
      rw [prodDenL, if_pos rfl, ih hjs', Finset.erase_insert (by simpa using hj),
        Finset.erase_eq_of_notMem (by simpa using hj)]
    · rw [prodDenL, if_neg hji, ih hjs', Finset.erase_insert_of_ne hji,
        Finset.prod_insert (by simp [hj])]

lemma toPoly_interpL (xs vs : List F) (js is : List ℕ) :
    toPoly (interpL xs vs js is) = (is.map fun i ↦ Polynomial.C (vs.getD i 0 / prodDenL xs i js) *
      toPoly (prodNumL xs i js)).sum := by
  induction is with
  | nil => simp [interpL]
  | cons i is ih => simp [interpL, ih]

lemma toPoly_interpC (xs vs : List F) : toPoly (interpC xs vs) =
    ∑ i ∈ Finset.range xs.length, Polynomial.C (vs.getD i 0 /
      ∏ j ∈ (Finset.range xs.length).erase i, (xs.getD i 0 - xs.getD j 0)) *
      ∏ j ∈ (Finset.range xs.length).erase i, (X - Polynomial.C (xs.getD j 0)) := by
  classical
  rw [interpC, toPoly_interpL, ← List.sum_toFinset _ (List.nodup_range), List.toFinset_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [prodDenL_eq _ _ _ List.nodup_range, toPoly_prodNumL _ _ _ List.nodup_range,
    List.toFinset_range]

/-- Evaluation of the interpolant at a node. -/
lemma eval_interpC (xs vs : List F) (hnd : xs.Nodup) (l : ℕ) (hl : l < xs.length) :
    (toPoly (interpC xs vs)).eval (xs.getD l 0) = vs.getD l 0 := by
  classical
  have hxinj : ∀ i j, i < xs.length → j < xs.length → xs.getD i 0 = xs.getD j 0 → i = j := by
    intro i j hi hj h
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
    exact (List.Nodup.getElem_inj_iff hnd).mp h
  rw [toPoly_interpC, eval_finsetSum, Finset.sum_eq_single l]
  · rw [eval_mul, eval_C, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    have hden : ∏ j ∈ (Finset.range xs.length).erase l, (xs.getD l 0 - xs.getD j 0) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j hj ↦ by
        obtain ⟨hjl, hj'⟩ := Finset.mem_erase.mp hj
        exact sub_ne_zero.mpr fun h ↦ hjl (hxinj j l (Finset.mem_range.mp hj') hl h.symm)
    field_simp
  · intro i hi hil
    rw [eval_mul, eval_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := l) (Finset.mem_erase.mpr
      ⟨Ne.symm hil, Finset.mem_range.mpr hl⟩) (by simp))
  · intro h; exact absurd (Finset.mem_range.mpr hl) h

lemma natDegree_interpC_lt (xs vs : List F) (hxs : 0 < xs.length) :
    (toPoly (interpC xs vs)).natDegree < xs.length := by
  rw [toPoly_interpC]
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := xs.length - 1) fun i hi ↦ ?_)
    (by omega)
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  refine (Finset.sum_le_sum fun j _ ↦ natDegree_X_sub_C_le _).trans ?_
  simp [Finset.card_erase_of_mem hi]

end CompSem

section DiscSpec

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

lemma discAt_eq (Fc : BPoly F) (n : ℕ) (hmon : (toB Fc).Monic) (hn : (toB Fc).natDegree = n)
    (c : F) : discAt Fc c = (resultant (toB Fc) (derivative (toB Fc)) n (n - 1)).eval c := by
  rw [discAt, resC_eq, toPoly_evalFibre, toPoly_evalFibre, toB_derivYB]
  have h1 : ((toB Fc).map (evalRingHom c)).natDegree = n := by rw [hmon.natDegree_map, hn]
  have h2 : ((derivative (toB Fc)).map (evalRingHom c)).natDegree = n - 1 := by
    rw [← Polynomial.derivative_map, natDegree_derivative, h1]
  rw [h1, h2, resultant_map_map, coe_evalRingHom]

lemma natPts_length (d : ℕ) : (natPts d : List F).length = d + 1 := by simp [natPts]

lemma natPts_getD (d i : ℕ) (hi : i < d + 1) : (natPts d : List F).getD i 0 = (i : F) := by
  rw [natPts, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

lemma natPts_nodup (d : ℕ) : (natPts d : List F).Nodup :=
  List.nodup_range.map fun a b h ↦ by exact_mod_cast h

/-- **`discRC` is the discriminant.** -/
theorem toPoly_discRC (Fc : BPoly F) (n k : ℕ) (hmon : (toB Fc).Monic)
    (hn : (toB Fc).natDegree = n) (hk : ∀ i, ((toB Fc).coeff i).natDegree ≤ k) :
    toPoly (discRC Fc n k) = resultant (toB Fc) (derivative (toB Fc)) n (n - 1) := by
  set d := n * (n - 1) * k with hd
  refine eq_of_natDegree_lt_card_of_eval_eq _ _ (ι := Fin (d + 1)) (f := fun i ↦ ((i : ℕ) : F))
    (fun a b h ↦ Fin.ext (by simpa using h)) (fun i ↦ ?_) ?_
  · have hi : (i : ℕ) < d + 1 := i.2
    have hl : (i : ℕ) < (natPts d : List F).length := by rw [natPts_length]; exact hi
    rw [discRC, ← natPts_getD d i hi, eval_interpC _ _ (natPts_nodup d) i hl,
      List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
      ← List.getD_eq_getElem _ 0 hl, natPts_getD d i hi, discAt_eq Fc n hmon hn]
  · rw [Fintype.card_fin]
    refine max_lt ?_ ?_
    · have := natDegree_interpC_lt (natPts d : List F)
        ((natPts d).map (discAt Fc)) (by rw [natPts_length]; omega)
      rwa [natPts_length] at this
    · have := natDegree_disc_le (toB Fc) hmon k hk
      rw [hn] at this; omega

end DiscSpec

end Curves
