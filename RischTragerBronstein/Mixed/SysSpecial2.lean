import RischTragerBronstein.Mixed.SysSpecial

/-!
# Coupled Risch systems: a complete bound on the special degrees

`specBound` combined the annihilator rows with fixed weights, so its pencil determinant could vanish
identically. Here the special degrees are bounded through the Gram matrix of the pencil
`M(X) = X Uₐ + U_c` (all annihilator rows): `G(X) = M(X)ᵀ M(X)`, `P = det G ∈ ℚ[X]`. A special
degree `D` gives a constant vector `κ ≠ 0` with `M(D) κ = 0`, hence `G(D) κ = 0` and `P(D) = 0`
(`specBound2_spec`).
-/

open Polynomial CPoly Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP

/-- The entry `(i, j)` of the Gram matrix `Σᵤ (X aᵤᵢ + cᵤᵢ)(X aᵤⱼ + cᵤⱼ)`. -/
def gramEntry (U : List (CPoly ℚ)) (n : ℕ) (i j : Fin n) : CPoly ℚ :=
  [(U.map fun u ↦ u.getD (n + i) 0 * u.getD (n + j) 0).sum,
   (U.map fun u ↦ u.getD i 0 * u.getD (n + j) 0 + u.getD (n + i) 0 * u.getD j 0).sum,
   (U.map fun u ↦ u.getD i 0 * u.getD j 0).sum]

lemma gram_kill {Cc : Type*} [Field Cc] [CharZero Cc] (n : ℕ) (D : ℚ) (κ : Fin n → Cc) (i : Fin n) :
    ∀ U : List (CPoly ℚ), (∀ u ∈ U, ∑ j : Fin n, (((u.getD j 0 : ℚ) : Cc) * ((D : Cc) * κ j) +
      ((u.getD (n + j) 0 : ℚ) : Cc) * κ j) = 0) →
    ∑ j : Fin n, (((U.map fun u ↦ (D * u.getD i 0 + u.getD (n + i) 0) *
      (D * u.getD j 0 + u.getD (n + j) 0)).sum : ℚ) : Cc) * κ j = 0
  | [], _ => by simp
  | u :: U, h => by
    have ih := gram_kill n D κ i U fun v hv ↦ h v (List.mem_cons_of_mem _ hv)
    have hu := h u List.mem_cons_self
    set f : CPoly ℚ → Fin n → ℚ := fun v j ↦ (D * v.getD i 0 + v.getD (n + i) 0) *
      (D * v.getD j 0 + v.getD (n + j) 0) with hf
    have hsplit : ∑ j : Fin n, ((((u :: U).map fun v ↦ f v j).sum : ℚ) : Cc) * κ j =
        ∑ j : Fin n, ((f u j : ℚ) : Cc) * κ j +
          ∑ j : Fin n, (((U.map fun v ↦ f v j).sum : ℚ) : Cc) * κ j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [List.map_cons, List.sum_cons, Rat.cast_add, add_mul]
    change ∑ j : Fin n, ((((u :: U).map fun v ↦ f v j).sum : ℚ) : Cc) * κ j = 0
    rw [hsplit, show ∑ j : Fin n, (((U.map fun v ↦ f v j).sum : ℚ) : Cc) * κ j = 0 from ih,
      add_zero]
    have e : ∑ j : Fin n, ((f u j : ℚ) : Cc) * κ j = (((D * u.getD i 0 + u.getD (n + i) 0) : ℚ) : Cc) *
        ∑ j : Fin n, (((u.getD j 0 : ℚ) : Cc) * ((D : Cc) * κ j) +
          ((u.getD (n + j) 0 : ℚ) : Cc) * κ j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hf]; push_cast; ring
    rw [e, hu, mul_zero]

/-- The Gram determinant. -/
def gramPoly (U : List (CPoly ℚ)) (n : ℕ) : CPoly ℚ :=
  detF [] [1] CPoly.add CPoly.mul CPoly.neg n (gramEntry U n)

lemma eval_gramPoly (U : List (CPoly ℚ)) (n : ℕ) (x : ℚ) :
    (toPoly (gramPoly U n)).eval x = (Matrix.of fun i j : Fin n ↦ (U.map fun u ↦
      (x * u.getD i 0 + u.getD (n + i) 0) * (x * u.getD j 0 + u.getD (n + j) 0)).sum).det := by
  rw [gramPoly, detF_spec [] [1] CPoly.add CPoly.mul CPoly.neg (fun p ↦ (toPoly p).eval x)
    (by simp) (by simp) (by simp) (by simp) (by simp)]
  congr 1
  ext i j
  simp only [Matrix.of_apply, gramEntry, toPoly_cons, toPoly_nil]
  simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, add_zero]
  induction U with
  | nil => simp
  | cons u U ih =>
    simp only [List.map_cons, List.sum_cons]
    linear_combination ih

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The complete bound on the special degrees.** -/
def specBound2 (m n : ℕ) (lim : List (LC m) → List (List ℚ × LC m)) (η : LC m)
    (β : Fin n → Fin n → LC m) : Option ℕ :=
  let P := gramPoly (specAnn Fc ks m n lim η β) n
  if CPoly.isZero P then none else some (maxRootLE P ⌈rootBoundL P⌉₊)

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Every special degree is bounded by `specBound2`.** -/
theorem specBound2_spec (m : ℕ) (h : T.Tr m) (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h) lim) (n : ℕ) (η : LC m)
    (β : Fin n → Fin n → LC m) (Bs : ℕ) (hB : specBound2 Fc ks m n lim η β = some Bs) (D : ℕ)
    (hD : SpecialDeg ((T.MP m h).sem η) (fun i j ↦ (T.MP m h).sem (β i j)) D) : D ≤ Bs := by
  classical
  obtain ⟨c, hc0, hc', y, hy⟩ := hD
  choose κ hκ using fun j ↦ T.const_F (c j) (hc' j)
  set ι := algebraMap Cc (T.F m) with hι
  set M := T.MP m h with hM
  set U := specAnn Fc ks m n lim η β with hU
  -- every annihilator row kills `(D κ, κ)`
  have hUκ : ∀ u ∈ U, ∑ j : Fin n, (((u.getD j 0 : ℚ) : Cc) * ((D : Cc) * κ j) +
      ((u.getD (n + j) 0 : ℚ) : Cc) * κ j) = 0 := by
    intro u hu
    obtain ⟨i, -, hu⟩ := List.mem_flatMap.mp hu
    set ws := specWs Fc ks m n η β i with hws
    set cl : List Cc := (List.range (2 * n)).map fun l ↦
      if hl : l < n then (D : Cc) * κ ⟨l, hl⟩ else if h' : l - n < n then κ ⟨l - n, h'⟩ else 0
      with hcl
    have hlen : ws.length = 2 * n := by simp [hws, specWs]
    have hwsl : ∀ j : Fin n, ws.getD j (MO Fc ks m).zero = if (j : ℕ) = i then η else (MO Fc ks m).zero :=
      fun j ↦ by
        rw [hws, specWs, NestTower.getD_range_map _ _ (by omega), if_pos j.2]
    have hwsr : ∀ j : Fin n, ws.getD (n + j) (MO Fc ks m).zero = β i j := fun j ↦ by
      rw [hws, specWs, NestTower.getD_range_map _ _ (by omega), if_neg (by omega),
        dif_pos (by omega)]
      congr 1; exact Fin.ext (by simp)
    have hcll : ∀ j : Fin n, cl.getD j 0 = (D : Cc) * κ j := fun j ↦ by
      rw [hcl, NestTower.getD_range_map _ _ (by omega), dif_pos j.2]
    have hclr : ∀ j : Fin n, cl.getD (n + j) 0 = κ j := fun j ↦ by
      rw [hcl, NestTower.getD_range_map _ _ (by omega), dif_neg (by omega), dif_pos (by omega)]
      congr 1; exact Fin.ext (by simp)
    set z := -y i with hzdef
    have hz : z′ = sC ι M cl ws := by
      rw [sC, hlen, sum_range_two]
      simp only [hwsl, hwsr, hcll, hclr]
      rw [hzdef, map_neg, hy i, neg_neg]
      simp only [apply_ite M.sem, M.sem_zero, mul_ite, mul_zero]
      simp only [Fin.val_inj, Finset.sum_ite_eq', Finset.mem_univ, if_true, hκ, map_mul,
        map_natCast]
      ring_nf
      simp only [mul_comm]
    have hclen : ∀ l, ws.length ≤ l → cl.getD l 0 = 0 := fun l hl ↦
      List.getD_eq_default _ _ (by simp [hcl]; omega)
    obtain ⟨γ, hγ, -⟩ := hlim.complete ws cl hclen z hz
    have hVk : ∀ k, ((lim ws).map Prod.fst).getD k [] = ((lim ws).getD k ([], (MO Fc ks m).zero)).1 :=
      fun k ↦ by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (lim ws)[k]? <;> rfl
    have hsum : ∑ l ∈ Finset.range (2 * n), ((u.getD l 0 : ℚ) : Cc) * cl.getD l 0 = 0 := by
      have e1 : ∀ l ∈ Finset.range (2 * n), ((u.getD l 0 : ℚ) : Cc) * cl.getD l 0 =
          ∑ k ∈ Finset.range (lim ws).length, γ.getD k 0 * ((u.getD l 0 *
            ((lim ws).getD k ([], (MO Fc ks m).zero)).1.getD l 0 : ℚ) : Cc) := fun l _ ↦ by
        rw [hγ l, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [eq_ratCast]; push_cast; ring
      rw [Finset.sum_congr rfl e1, Finset.sum_comm]
      refine Finset.sum_eq_zero fun k hk ↦ ?_
      have ho := ann_orth ((lim ws).map Prod.fst) (2 * n) u hu k
        (by simpa using Finset.mem_range.mp hk)
      rw [hVk] at ho
      rw [← Finset.mul_sum, ← Rat.cast_sum, ho, Rat.cast_zero, mul_zero]
    rw [sum_range_two] at hsum
    simp only [hcll, hclr, ← Finset.sum_add_distrib] at hsum
    exact hsum
  -- the Gram matrix kills `κ`
  have hκ0 : κ ≠ 0 := fun h0 ↦ hc0 (funext fun j ↦ by
    rw [hκ j, h0, Pi.zero_apply, map_zero, Pi.zero_apply])
  set Gq : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j : Fin n ↦ (U.map fun u ↦
      ((D : ℚ) * u.getD i 0 + u.getD (n + i) 0) * ((D : ℚ) * u.getD j 0 + u.getD (n + j) 0)).sum
    with hGq
  have hGκ : ∀ i : Fin n, ∑ j, ((Gq i j : ℚ) : Cc) * κ j = 0 := fun i ↦
    gram_kill n (D : ℚ) κ i U (fun u hu ↦ by simpa using hUκ u hu)
  have hdetC : ((algebraMap ℚ Cc).mapMatrix Gq).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨κ, hκ0, funext fun i ↦ by
      simpa [Matrix.mulVec, dotProduct, eq_ratCast] using hGκ i⟩
  rw [← RingHom.map_det] at hdetC
  have hdet : Gq.det = 0 := (algebraMap ℚ Cc).injective (by rw [hdetC, map_zero])
  have hroot : (toPoly (gramPoly U n)).IsRoot (D : ℚ) := by
    rw [IsRoot.def, eval_gramPoly]; exact hdet
  unfold specBound2 at hB
  simp only at hB
  split_ifs at hB with hz
  obtain rfl := Option.some.inj hB
  have hP0 : toPoly (gramPoly U n) ≠ 0 := fun h0 ↦ hz ((CPoly.isZero_iff _).mpr h0)
  have hb := abs_le_rootBound _ hP0 _ hroot
  rw [← rootBoundL_eq _ hP0, abs_of_nonneg (by positivity)] at hb
  exact le_maxRootLE _ _ D (by exact_mod_cast hb.trans (Nat.le_ceil _)) hroot

end MTower

end Curves.MT
