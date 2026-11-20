import RischTragerBronstein.Algebraic.SupLogSem

/-!
# The identity behind the exactness test

`logMT_eval`: in any differential field with `x′ = 1`, `yⁿ = f(x)`,
`T(x, y) = M(x, y) f(x) (h − ∑ⱼ cⱼ (uⱼ/Dⱼ)′/(uⱼ/Dⱼ))` for the integrand
`h = B + B₁/f + ∑ Gᵢ/(x − aᵢ)`, `uⱼ = Wⱼ(x, y)` and `Dⱼ = ∏ (x − aᵢ)^{Nⱼ negᵢ}`.
-/

open Polynomial CPoly Differential

namespace Sup

section Ident

variable {F : Type*} [Field F] [DecidableEq F]
variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
  [DifferentialAlgebra Kc E] [CharZero E]

/-- `c(x)` for a list polynomial. -/
noncomputable def exC (ι : F →+* Kc) (x : E) (c : CPoly F) : E := aeval x ((toPoly c).map ι)

variable (ι : F →+* Kc) (x y : E)

lemma evalE_smulB (c : CPoly F) (W : BPoly F) :
    evalE ι x y (toB (smulB c W)) = exC ι x c * evalE ι x y (toB W) := by
  rw [toB_smulB, map_mul, evalE_C]; rfl

lemma evalE_mulB (V W : BPoly F) :
    evalE ι x y (toB (mulB V W)) = evalE ι x y (toB V) * evalE ι x y (toB W) := by
  rw [toB_mulB, map_mul]

lemma evalE_addB (V W : BPoly F) :
    evalE ι x y (toB (addB V W)) = evalE ι x y (toB V) + evalE ι x y (toB W) := by
  rw [toB_addB, map_add]

lemma evalE_single (q : CPoly F) : evalE ι x y (toB [q]) = exC ι x q := by
  rw [evalE_cons, toB_nil, map_zero, mul_zero, add_zero]; rfl

lemma evalE_sumB (l : List (BPoly F)) :
    evalE ι x y (toB (sumB l)) = (l.map fun W ↦ evalE ι x y (toB W)).sum := by
  rw [toB_sumB, map_list_sum, List.map_map]; rfl

lemma evalE_prodB (l : List (BPoly F)) :
    evalE ι x y (toB (prodB l)) = (l.map fun W ↦ evalE ι x y (toB W)).prod := by
  rw [toB_prodB, map_list_prod, List.map_map]; rfl

lemma exC_smul (c : F) (P : CPoly F) : exC ι x (smul c P) = algebraMap Kc E (ι c) * exC ι x P := by
  simp [exC, toPoly_smul, Polynomial.map_mul, map_mul, aeval_C]

lemma exC_mul (P Q : CPoly F) : exC ι x (CPoly.mul P Q) = exC ι x P * exC ι x Q := by
  simp [exC, toPoly_mul, Polynomial.map_mul, map_mul]

lemma exC_prodP {m : ℕ} (a : Fin m → F) :
    exC ι x (prodC ((List.finRange m).map fun i ↦ linC (a i))) =
      ∏ i, (x - algebraMap Kc E (ι (a i))) := by
  rw [exC, toPoly_prodP, Polynomial.map_prod, map_prod]
  simp [aeval_C]

lemma exC_prodExc {m : ℕ} (a : Fin m → F) (i : Fin m) :
    ∏ i', (x - algebraMap Kc E (ι (a i'))) = (x - algebraMap Kc E (ι (a i))) * exC ι x (prodExc a i) := by
  have := congrArg (fun P : F[X] ↦ aeval x (P.map ι)) (prodP_eq a i)
  simp only [Polynomial.map_prod, map_prod, Polynomial.map_mul, map_mul, Polynomial.map_sub,
    map_sub, Polynomial.map_X, aeval_X, Polynomial.map_C, aeval_C] at this
  exact this

lemma exC_neg_one : exC ι x ([-1] : CPoly F) = -1 := by
  simp [exC, CPoly.toPoly]

lemma sum_finRange {M : Type*} [AddCommMonoid M] {k : ℕ} (g : Fin k → M) :
    ((List.finRange k).map g).sum = ∑ i, g i := (Fin.sum_univ_def g).symm

lemma prod_finRange {M : Type*} [CommMonoid M] {k : ℕ} (g : Fin k → M) :
    ((List.finRange k).map g).prod = ∏ i, g i := (Fin.prod_univ_def g).symm

end Ident

section Main

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
  [DifferentialAlgebra Kc E] [CharZero E]

open EllQuad.QCoords

lemma logDeriv_x_sub (hC : ∀ c : Kc, c′ = 0) (x : E) (hx : x′ = 1) (c : Kc) :
    logDeriv (x - algebraMap Kc E c) = 1 / (x - algebraMap Kc E c) := by
  rw [Differential.logDeriv, map_sub, hx, deriv_algebraMap, hC, map_zero, sub_zero]

omit [DecidableEq F] [CharZero F] [EllQuad.QCoords F] in
/-- The field identity behind `logMT_eval`. -/
lemma log_identity {M : Type*} [Field M] {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (Px U fx Bv B1v : M) (G Pe xa : ιA → M) (c u u' Uj : ιB → M) (e : ιB → ιA → ℕ)
    (hPe : ∀ i, Px = xa i * Pe i) (hUj : ∀ j, U = u j * Uj j) (hxa : ∀ i, xa i ≠ 0)
    (hu : ∀ j, u j ≠ 0) (hf : fx ≠ 0) :
    U * (fx * (Px * Bv + ∑ i, (Pe i * G i + (∑ j, c j * ((e j i : ℕ) : M)) * Pe i)) + Px * B1v) +
      -1 * ∑ j, c j * Px * (fx * u' j * Uj j) =
    Px * U * fx * (Bv + B1v / fx + ∑ i, G i / xa i -
      ∑ j, c j * (u' j / u j - ∑ i, (e j i : M) * (1 / xa i))) := by
  have h1 : Px * ∑ i, G i / xa i = ∑ i, Pe i * G i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hPe i]; field_simp [hxa i]
  have h2 : U * ∑ j, c j * (u' j / u j) = ∑ j, c j * (u' j * Uj j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hUj j]; field_simp [hu j]
  have h3 : Px * ∑ j, c j * ∑ i, (e j i : M) * (1 / xa i) =
      ∑ i, (∑ j, c j * ((e j i : ℕ) : M)) * Pe i := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hPe i]; field_simp [hxa i]
  have h4 : fx * (B1v / fx) = B1v := by field_simp
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_add_distrib]
  have e2 : ∑ j, c j * Px * (fx * u' j * Uj j) = Px * fx * ∑ j, c j * (u' j * Uj j) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
  have e3 : ∑ i, (∑ j, c j * ((e j i : ℕ) : M)) * Pe i = Px * ∑ j, c j * ∑ i, (e j i : M) * (1 / xa i) :=
    h3.symm
  have e1 : ∑ i, Pe i * G i = Px * ∑ i, G i / xa i := h1.symm
  have e2' : ∑ j, c j * (u' j * Uj j) = U * ∑ j, c j * (u' j / u j) := h2.symm
  rw [e2, e3, e1, e2']
  have e5 : ∑ j, c j * (u' j / u j) - ∑ j, c j * ∑ i, (e j i : M) * (1 / xa i) =
      ∑ j, (c j * (u' j / u j) - c j * ∑ i, (e j i : M) * (1 / xa i)) := by
    rw [Finset.sum_sub_distrib]
  linear_combination (-(Px * U)) * h4

set_option maxHeartbeats 1000000 in
/-- **The identity behind the exactness test.** -/
theorem logMT_eval (hC : ∀ c : Kc, c′ = 0) (ι : F →+* Kc) (x y : E) (hx : x′ = 1)
    (f : CPoly F) {n : ℕ} (hn : 0 < n) (hy0 : y ≠ 0) (hy : y ^ n = aeval x ((toPoly f).map ι))
    {m : ℕ} (ζ : F) (a b : Fin m → F) (G : Fin m → BPoly F) (B B₁ : BPoly F)
    (NW : Fin (dim F) → ℕ × BPoly F)
    (hu : ∀ j, evalE ι x y (toB (NW j).2) ≠ 0)
    (hxa : ∀ i, x - algebraMap Kc E (ι (a i)) ≠ 0) (hf : exC ι x f ≠ 0) :
    evalE ι x y (toB (logMT f n ζ a b G B B₁ NW).2) =
      evalE ι x y (toB (logMT f n ζ a b G B B₁ NW).1) * exC ι x f *
        (evalE ι x y (toB B) + evalE ι x y (toB B₁) / exC ι x f +
          ∑ i, evalE ι x y (toB (G i)) / (x - algebraMap Kc E (ι (a i))) -
          ∑ j, algebraMap Kc E (ι (cJ n ζ a b G j (NW j).1)) *
            logDeriv (evalE ι x y (toB (NW j).2) /
              ∏ i, (x - algebraMap Kc E (ι (a i))) ^ ((NW j).1 * negJ n ζ a b G j i))) := by
  set ι' : F → E := fun c ↦ algebraMap Kc E (ι c) with hι'
  set u : Fin (dim F) → E := fun j ↦ evalE ι x y (toB (NW j).2) with hu_def
  set Px : E := ∏ i, (x - ι' (a i)) with hPx
  set Pe : Fin m → E := fun i ↦ exC ι x (prodExc a i) with hPe_def
  set U : E := ∏ j, u j with hU_def
  set Uj : Fin (dim F) → E := fun j ↦ ∏ k, if k = j then 1 else u k with hUj_def
  set fx := exC ι x f with hfx
  set e : Fin (dim F) → Fin m → ℕ := fun j i ↦ (NW j).1 * negJ n ζ a b G j i with he_def
  set c : Fin (dim F) → F := fun j ↦ cJ n ζ a b G j (NW j).1 with hc_def
  have hPe : ∀ i, Px = (x - ι' (a i)) * Pe i := fun i ↦ exC_prodExc ι x a i
  have hUj : ∀ j, U = u j * Uj j := by
    intro j
    simp only [hU_def, hUj_def]
    rw [← Finset.mul_prod_erase Finset.univ u (Finset.mem_univ j),
      ← Finset.mul_prod_erase Finset.univ (fun k ↦ if k = j then (1 : E) else u k)
        (Finset.mem_univ j), if_pos rfl, one_mul]
    congr 1
    exact Finset.prod_congr rfl fun k hk ↦ by rw [if_neg (Finset.ne_of_mem_erase hk)]
  have hD0 : ∀ j, ∏ i, (x - ι' (a i)) ^ e j i ≠ 0 := fun j ↦
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (hxa i)
  -- the logarithmic derivatives
  have hlog : ∀ j, logDeriv (u j / ∏ i, (x - ι' (a i)) ^ e j i) =
      (u j)′ / u j - ∑ i, (e j i : E) * (1 / (x - ι' (a i))) := by
    intro j
    rw [Differential.logDeriv_div _ _ (hu j) (hD0 j), Differential.logDeriv_prod _ _ _ fun i _ ↦ pow_ne_zero _ (hxa i)]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Differential.logDeriv_pow, logDeriv_x_sub hC x hx]
  -- evaluate the two sides
  have hM : evalE ι x y (toB (logMT f n ζ a b G B B₁ NW).1) = Px * U := by
    simp only [logMT, evalE_smulB, evalE_prodB, List.map_map, prod_finRange, exC_prodP]
    rfl
  have hite : ∀ j k, evalE ι x y (toB (if k = j then ([[1]] : BPoly F) else (NW k).2)) =
      if k = j then 1 else u k := by
    intro j k
    split_ifs
    · rw [evalE_single]; simp [exC, CPoly.toPoly]
    · rfl
  have hT : evalE ι x y (toB (logMT f n ζ a b G B B₁ NW).2) =
      U * (fx * (Px * evalE ι x y (toB B) + ∑ i, (Pe i * evalE ι x y (toB (G i)) +
        (∑ j, ι' (c j) * ((e j i : ℕ) : E)) * Pe i)) + Px * evalE ι x y (toB B₁)) +
      -1 * ∑ j, ι' (c j) * Px * (fx * (u j)′ * Uj j) := by
    simp only [logMT, evalE_addB, evalE_mulB, evalE_smulB, evalE_sumB, evalE_prodB, List.map_cons,
      List.sum_cons, List.map_map, sum_finRange, prod_finRange, exC_prodP, evalE_single,
      exC_neg_one, exC_smul, Function.comp_def]
    simp only [map_sum, map_mul, map_natCast, evalE_derivB hC x y hx ι f hn hy0 hy, hite]
    rfl
  rw [hT, hM, log_identity Px U fx _ _ (fun i ↦ evalE ι x y (toB (G i))) Pe
    (fun i ↦ x - ι' (a i)) (fun j ↦ ι' (c j)) u (fun j ↦ (u j)′) Uj e hPe hUj hxa hu hf]
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  show ι' (c j) * _ = ι' (c j) * logDeriv (u j / ∏ i, (x - ι' (a i)) ^ e j i)
  rw [hlog j]

end Main

end Sup
