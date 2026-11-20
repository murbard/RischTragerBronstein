import RischTragerBronstein.Mixed.KQDecide
import RischTragerBronstein.Mixed.KESem

/-!
# Square roots over a logarithmic level with poles: the values of the codes of `kqDecide`

Horner evaluation (`sem_evalGC`), products of linear factors (`toPoly_prodLinG`,
`prodLin_eraseIdx`), powers (`sem_powC`) and the rational square root (`qsqrt_spec`).
-/

open Polynomial Differential CPoly

set_option linter.unusedSectionVars false

namespace Curves.MT

lemma qsqrt_spec {x y : ℚ} (h : qsqrt x = some y) : y ^ 2 = x ∧ 0 ≤ y := by
  unfold qsqrt at h
  split_ifs at h with h0 h1
  obtain rfl := Option.some.inj h
  have hx : 0 ≤ x := not_lt.mp h0
  have hnum : (x.num.toNat : ℤ) = x.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hx)
  refine ⟨?_, by positivity⟩
  have e1 : ((Nat.sqrt x.num.toNat : ℚ)) ^ 2 = x.num := by
    rw [sq, ← Nat.cast_mul, h1.1]; exact_mod_cast hnum
  have e2 : ((Nat.sqrt x.den : ℚ)) ^ 2 = x.den := by
    rw [sq, ← Nat.cast_mul, h1.2]
  rw [div_pow, e1, e2]
  exact Rat.num_div_den x

section Gen

variable {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

lemma sem_powC (a : α) (k : ℕ) : M.sem (powC O a k) = M.sem a ^ k := by
  induction k with
  | zero => simp [powC, M.sem_one]
  | succ k ih => rw [powC, M.sem_mul, ih, pow_succ, mul_comm]

end Gen

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable (m : ℕ) (h : T.Tr m)

lemma sem_evalGC (P : GPoly (LC m)) (c : LC m) :
    (T.MP m h).sem (evalGC Fc ks m P c) =
      (GPoly.toPoly (T.MP m h) P).eval ((T.MP m h).sem c) := by
  induction P with
  | nil => simp [evalGC, (T.MP m h).sem_zero]
  | cons a P ih =>
    simp only [evalGC, List.foldr_cons] at ih ⊢
    rw [(T.MP m h).sem_add, (T.MP m h).sem_mul, ih, GPoly.toPoly_cons, eval_add, eval_mul, eval_C,
      eval_X]

lemma toPoly_linG (c : LC m) :
    GPoly.toPoly (T.MP m h) (linG Fc ks m c) = X - Polynomial.C ((T.MP m h).sem c) := by
  simp only [linG, GPoly.toPoly_cons, GPoly.toPoly_nil, (T.MP m h).sem_neg, (T.MP m h).sem_one,
    map_neg, map_one, mul_zero, add_zero, mul_one]
  ring

lemma toPoly_prodLinG (cs : List (LC m)) :
    GPoly.toPoly (T.MP m h) (prodLinG Fc ks m cs) =
      (cs.map fun c ↦ X - Polynomial.C ((T.MP m h).sem c)).prod := by
  induction cs with
  | nil => simp [prodLinG, (T.MP m h).sem_one]
  | cons c cs ih =>
    simp only [prodLinG, List.foldr_cons] at ih ⊢
    rw [GPoly.toPoly_mul, ih, T.toPoly_linG m h, List.map_cons, List.prod_cons]

lemma prodLin_eraseIdx (cs : List (LC m)) (q : ℕ) (hq : q < cs.length) :
    GPoly.toPoly (T.MP m h) (prodLinG Fc ks m cs) =
      (X - Polynomial.C ((T.MP m h).sem (kqC Fc ks m cs q))) *
        GPoly.toPoly (T.MP m h) (prodLinG Fc ks m (cs.eraseIdx q)) := by
  rw [T.toPoly_prodLinG m h, T.toPoly_prodLinG m h, ← List.eraseIdx_map]
  have hq' : q < (cs.map fun c ↦ X - Polynomial.C ((T.MP m h).sem c)).length := by simpa using hq
  rw [← List.CommMonoid.mul_prod_eraseIdx hq', List.getElem_map, kqC,
    List.getD_eq_getElem _ _ hq]

lemma eval_prodLin_ne (cs : List (LC m)) {K : Type*} [Field K] [Algebra (T.F m) K] (α : K)
    (hα : ∀ c ∈ cs, α ≠ algebraMap (T.F m) K ((T.MP m h).sem c)) :
    ((GPoly.toPoly (T.MP m h) (prodLinG Fc ks m cs)).map (algebraMap (T.F m) K)).eval α ≠ 0 := by
  rw [T.toPoly_prodLinG m h, Polynomial.map_list_prod, eval_list_prod, List.map_map, List.map_map]
  refine List.prod_ne_zero ?_
  intro h0
  obtain ⟨c, hc, hc0⟩ := List.mem_map.mp h0
  simp only [Function.comp_apply, Polynomial.map_sub, map_X, Polynomial.map_C, eval_sub, eval_X,
    eval_C] at hc0
  exact hα c hc (sub_eq_zero.mp hc0)

lemma eval_prodLin_erase_ne (cs : List (LC m)) (q : ℕ) (hq : q < cs.length)
    (h0 : (MO Fc ks m).isZero (evalGC Fc ks m (prodLinG Fc ks m (cs.eraseIdx q))
      (kqC Fc ks m cs q)) = false) :
    ∀ q' (hq' : q' < cs.length), q' ≠ q →
      (T.MP m h).sem (cs[q']'hq') ≠ (T.MP m h).sem (kqC Fc ks m cs q) := by
  intro q' hq' hne heq
  have hv : (T.MP m h).sem (evalGC Fc ks m (prodLinG Fc ks m (cs.eraseIdx q)) (kqC Fc ks m cs q))
      = 0 := by
    rw [T.sem_evalGC m h, T.toPoly_prodLinG m h, eval_list_prod]
    refine List.prod_eq_zero ?_
    refine List.mem_map.mpr ⟨X - Polynomial.C ((T.MP m h).sem (cs[q']'hq')),
      List.mem_map.mpr ⟨cs[q']'hq', ?_, rfl⟩, ?_⟩
    · exact List.mem_eraseIdx_iff_getElem.mpr ⟨q', hq', hne, rfl⟩
    · simp [heq]
  rw [← (T.MP m h).isZero_iff] at hv
  rw [hv] at h0
  exact Bool.noConfusion h0

end MTower

end Curves.MT
