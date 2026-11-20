import RischTragerBronstein.Algebraic.EllDecideK
import RischTragerBronstein.Algebraic.EllDecideAD

/-!
# `∫ A dx / (D y)` over a number field of constants, from checked splitting data

`ellDecideADK` takes rational `A, D` and a list of pairs `(αᵢ, βᵢ)` in a computable field `K`
(e.g. `NF f`). It checks by computation that `D = lc ∏ (X − αᵢ)` over `K` (`splitCheck`), computes
the residues `A(αᵢ) / (D′(αᵢ) βᵢ)`, and runs `ellDecideK` (which checks `βᵢ² = p(αᵢ)`, `βᵢ ≠ 0`,
distinct `αᵢ`). `ellDecideADK_spec`: every answer is correct. `ellDecideADK_ne_none`: correct
splitting data is always accepted and decided.
-/

open Polynomial Differential

namespace EllQuad

open CPoly EllDV

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- Evaluation of a rational polynomial at a point of `K`. -/
def evalQK (q : CPoly ℚ) (z : K) : K := q.foldr (fun (t : ℚ) (acc : K) ↦ (t : K) + z * acc) 0

/-- A rational polynomial over `K`. -/
def liftK (q : CPoly ℚ) : CPoly K := q.map fun (t : ℚ) ↦ (t : K)

/-- `∏ (X − rᵢ)`. -/
def prodLin : List K → CPoly K
  | [] => [1]
  | r :: t => mul [-r, 1] (prodLin t)

/-- **The splitting check** `D = lc ∏ (X − αᵢ)` over `K`. -/
def splitCheck (D : CPoly ℚ) (rs : List K) : Bool :=
  beq (liftK D) (smul ((lead (trim D) : ℚ) : K) (prodLin rs))

lemma evalQK_eq (q : CPoly ℚ) (z : K) : evalQK q z = aeval z (toPoly q) := by
  induction q with
  | nil => simp [evalQK, CPoly.toPoly]
  | cons t q ih =>
    simp only [evalQK, List.foldr_cons] at ih ⊢
    rw [ih, toPoly_cons, map_add, map_mul, aeval_C, aeval_X]
    simp [Algebra.algebraMap_eq_smul_one]

lemma toPoly_liftK (q : CPoly ℚ) : toPoly (liftK (K := K) q) = (toPoly q).map (algebraMap ℚ K) := by
  induction q with
  | nil => simp [liftK, CPoly.toPoly]
  | cons t q ih =>
    simp only [liftK, List.map_cons, toPoly_cons, Polynomial.map_add, Polynomial.map_mul, map_C,
      Polynomial.map_X] at ih ⊢
    rw [ih]; rfl

lemma toPoly_prodLin : ∀ rs : List K, toPoly (prodLin rs) = (rs.map fun r ↦ X - C r).prod
  | [] => by simp [prodLin, CPoly.toPoly]
  | r :: t => by
    rw [prodLin, toPoly_mul, toPoly_prodLin t, List.map_cons, List.prod_cons]
    congr 1
    simp [CPoly.toPoly]; ring

lemma lead_trim_ne_zero {D : CPoly ℚ} (hD : toPoly D ≠ 0) : lead (trim D) ≠ 0 := by
  have htr : trim D ≠ [] := fun h ↦ hD ((trim_eq_nil_iff D).mp h)
  have hl := length_trim htr
  have : lead (trim D) = (toPoly D).leadingCoeff := by
    rw [leadingCoeff, ← toPoly_trim, coeff_toPoly, lead, List.getLastD_eq_getLast? ]
    rw [List.getLast?_eq_getElem?, hl]
    simp [List.getD_eq_getElem?_getD]
  rw [this]; exact leadingCoeff_ne_zero.mpr hD

lemma splitCheck_iff (D : CPoly ℚ) (hD : toPoly D ≠ 0) (rs : List K) :
    splitCheck D rs = true ↔ (toPoly D).map (algebraMap ℚ K) =
      C ((lead (trim D) : ℚ) : K) * (rs.map fun r ↦ X - C r).prod := by
  rw [splitCheck, beq_iff, toPoly_liftK, toPoly_smul, toPoly_prodLin]

lemma evF_liftK {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [CharZero Kc] [CharZero E]
    (ι : K →+* Kc) (x : E) (q : CPoly ℚ) : evF ι x (liftK q) = aeval x (toPoly q) := by
  rw [evF, toPoly_liftK, Polynomial.map_map]
  rw [show (ι.comp (algebraMap ℚ K)) = algebraMap ℚ Kc from RingHom.ext_rat _ _,
    aeval_map_algebraMap]

variable [QCoords K]

/-- **The procedure** (`none`: `D = 0`, the splitting data is wrong, or the points are invalid). -/
def ellDecideADK (a b c : ℤ) (A D : CPoly ℚ) (pts : List (K × K)) (N : ℕ) : Option Bool :=
  if (!isZero D && splitCheck D (pts.map Prod.fst)) = true then
    ellDecideK a b c (liftK (divMod A D).1)
      (pts.map fun q ↦ (q.1, q.2, evalQK A q.1 / (evalQK (CPoly.deriv D) q.1 * q.2))) N
  else none

omit [QCoords K] in
lemma validK_of_some' {a b c : ℤ} {B : CPoly K} {pts : List (K × K × K)} {N : ℕ} [QCoords K]
    {ans : Bool} (h : ellDecideK a b c B pts N = some ans) : validK a b c pts = true := by
  by_contra hv
  rw [ellDecideK, if_neg hv] at h
  cases h

section Spec

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 3200000 in
/-- **The integrand as partial fractions over the roots.** -/
lemma integrand_pfK (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (ι : K →+* Kc)
    (A D : CPoly ℚ) (hD0 : toPoly D ≠ 0) (rs : List K) (hnd : rs.Nodup) (lc : K) (hlc : lc ≠ 0)
    (hsplit : (toPoly D).map (algebraMap ℚ K) = C lc * (rs.map fun r ↦ X - C r).prod) :
    aeval x (toPoly A) / (aeval x (toPoly D) * y) =
      (evF ι x (liftK (divMod A D).1) + (rs.map fun α ↦ algebraMap Kc E
        (ι (evalQK A α / evalQK (CPoly.deriv D) α)) / (x - algebraMap Kc E (ι α))).sum) / y := by
  classical
  set ιE : K →+* E := (algebraMap Kc E).comp ι with hιE
  have hmapE : ∀ P : ℚ[X], (P.map (algebraMap ℚ K)).map ιE = P.map (algebraMap ℚ E) := by
    intro P; rw [Polynomial.map_map]; congr 1; exact RingHom.ext_rat _ _
  have haev : ∀ P : ℚ[X], aeval x P = (P.map (algebraMap ℚ E)).eval x := fun P ↦ by
    rw [eval_map_algebraMap]
  have haevF : ∀ (P : ℚ[X]) (z : K), ιE (aeval z P) = (P.map (algebraMap ℚ E)).eval (ιE z) := by
    intro P z
    rw [eval_map_algebraMap]
    exact (aeval_algHom_apply ιE.toRatAlgHom z P).symm
  set n := rs.length
  set v : Fin n → E := fun i ↦ ιE rs[i]
  have hv : Set.InjOn v ↑(Finset.univ : Finset (Fin n)) := by
    intro i _ j _ hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp (ιE.injective hij))
  set DE := (toPoly D).map (algebraMap ℚ E)
  have hDE : DE = C (ιE lc) * ∏ i : Fin n, (X - C (v i)) := by
    show (toPoly D).map (algebraMap ℚ E) = _
    rw [← hmapE, hsplit, Polynomial.map_mul, map_C, EllAlgo.prod_map_eq_fin, Polynomial.map_prod]
    simp [v]
    left; rfl
  -- the division
  set q := (divMod A D).1
  set R := (divMod A D).2
  have hAR : toPoly A = toPoly q * toPoly D + toPoly R := divMod_spec A D
  have hRdeg := divMod_degree_lt A D hD0
  have hDn : (toPoly D).natDegree = n := by
    have h1 : DE.natDegree = (toPoly D).natDegree :=
      natDegree_map_eq_of_injective (algebraMap ℚ E).injective _
    have h2 : DE.natDegree = n := by
      rw [hDE, natDegree_C_mul ((map_ne_zero_iff _ ιE.injective).mpr hlc),
        natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C _]
      simp
    omega
  set RE := (toPoly R).map (algebraMap ℚ E)
  have hRE : RE.degree < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin, degree_map]
    calc (toPoly R).degree < (toPoly D).degree := hRdeg
      _ = n := by rw [degree_eq_natDegree hD0, hDn]
  have hxv : ∀ i ∈ (Finset.univ : Finset (Fin n)), x ≠ v i := fun i _ ↦
    sub_ne_zero.mp (x_sub_const_ne hC x hx (ι rs[i]))
  have hpf := partial_frac Finset.univ v hv (ιE lc) ((map_ne_zero_iff _ ιE.injective).mpr hlc) DE RE
    hDE hRE x hxv
  -- evaluate
  have hDx : aeval x (toPoly D) ≠ 0 := by
    rw [haev]
    change DE.eval x ≠ 0
    rw [hDE, eval_mul, eval_C, eval_prod]
    refine mul_ne_zero ((map_ne_zero_iff _ ιE.injective).mpr hlc)
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_)
    simp only [eval_sub, eval_X, eval_C]; exact sub_ne_zero.mpr (hxv i (Finset.mem_univ _))
  rw [evF_liftK, EllAlgo.sum_map_eq_fin]
  have hA : aeval x (toPoly A) / aeval x (toPoly D) = aeval x (toPoly q) +
      RE.eval x / DE.eval x := by
    rw [hAR, map_add, map_mul, add_div, mul_div_cancel_right₀ _ hDx, haev (toPoly R),
      haev (toPoly D)]
  rw [← div_div, hA, hpf]
  congr 2
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hroot : (toPoly D).eval₂ (algebraMap ℚ K) rs[i] = 0 := by
    rw [← eval_map, hsplit, eval_mul, eval_list_prod]
    apply mul_eq_zero_of_right
    apply List.prod_eq_zero
    simp only [List.map_map, List.mem_map, Function.comp_apply, eval_sub, eval_X, eval_C]
    exact ⟨rs[i], List.getElem_mem _, sub_self _⟩
  have hRi : RE.eval (v i) = ιE (evalQK A rs[i]) := by
    rw [evalQK_eq, haevF, hAR]
    simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, RE]
    rw [← haevF (toPoly D), aeval_def, hroot, map_zero, mul_zero, zero_add]
  have hDi : (derivative DE).eval (v i) = ιE (evalQK (CPoly.deriv D) rs[i]) := by
    rw [evalQK_eq, haevF, toPoly_deriv, derivative_map]
  rw [hRi, hDi]
  simp only [ιE, RingHom.comp_apply, map_div₀, v]
  field_simp


set_option maxHeartbeats 1600000 in
/-- **Correctness of `ellDecideADK`**. -/
theorem ellDecideADK_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (ι : K →+* Kc) (A D : CPoly ℚ) (pts : List (K × K)) (p0 : ℕ) [Fact p0.Prime]
    (hp02 : p0 ≠ 2) (hgood : goodRedMod p0 a b c) (φ : K →ₐ[ℚ] ℚ_[p0]) (N : ℕ)
    (hN : Fintype.card (Option (RedPts p0 a b c)) ≤ N)
    (ans : Bool) (h : ellDecideADK a b c A D pts N = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold ellDecideADK at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨hz, hsp⟩ := hc
  have hD0 : toPoly D ≠ 0 := fun h0 ↦ by rw [(isZero_iff _).mpr h0] at hz; exact Bool.noConfusion hz
  have hsplit := (splitCheck_iff D hD0 _).mp hsp
  have hv := validK_of_some' h
  simp only [validK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv
  obtain ⟨hon, hnd⟩ := hv
  have hnd' : (pts.map Prod.fst).Nodup := by simpa [List.map_map, Function.comp_def] using hnd
  have hlc : ((lead (trim D) : ℚ) : K) ≠ 0 := by exact_mod_cast lead_trim_ne_zero hD0
  have hsum : ((pts.map fun q ↦ (q.1, q.2, evalQK A q.1 / (evalQK (CPoly.deriv D) q.1 * q.2))).map
      fun q ↦ algebraMap Kc E (ι (q.2.2 * q.2.1)) / (x - algebraMap Kc E (ι q.1))).sum =
      ((pts.map Prod.fst).map fun α ↦ algebraMap Kc E
        (ι (evalQK A α / evalQK (CPoly.deriv D) α)) / (x - algebraMap Kc E (ι α))).sum := by
    rw [List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun q hq ↦ ?_
    have hβ := (hon _ (List.mem_map_of_mem hq)).2
    simp only [Function.comp_apply] at hβ ⊢
    congr 3
    field_simp
  rw [ellDecideK_spec hC hCall x y hx a b c hsq hy hgen ι _ _ p0 hp02 hgood φ N hN ans h,
    integrand_pfK hC x y hx ι A D hD0 _ hnd' _ hlc hsplit, hsum]

/-- **Completeness of `ellDecideADK`**: correct splitting data with valid points is decided. -/
theorem ellDecideADK_ne_none (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (A D : CPoly ℚ) (hD0 : toPoly D ≠ 0) (pts : List (K × K))
    (hsplit : (toPoly D).map (algebraMap ℚ K) =
      C ((lead (trim D) : ℚ) : K) * ((pts.map Prod.fst).map fun r ↦ X - C r).prod)
    (hon : ∀ q ∈ pts, q.2 * q.2 = q.1 ^ 3 + (a : K) * q.1 ^ 2 + (b : K) * q.1 + (c : K) ∧ q.2 ≠ 0)
    (hnd : (pts.map Prod.fst).Nodup) (N : ℕ) :
    ellDecideADK a b c A D pts N ≠ none := by
  unfold ellDecideADK
  rw [if_pos (by
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨by rcases h : isZero D with _ | _
              · rfl
              · exact absurd ((isZero_iff _).mp h) hD0, (splitCheck_iff D hD0 _).mpr hsplit⟩)]
  refine ellDecideK_ne_none a b c hsq _ _ N ?_
  simp only [validK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.map_map]
  refine ⟨fun q hq ↦ ?_, by simpa [Function.comp_def] using hnd⟩
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  exact hon q0 hq0

end Spec

end EllQuad
