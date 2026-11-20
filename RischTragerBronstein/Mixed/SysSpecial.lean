import RischTragerBronstein.Computable.SysDeg
import RischTragerBronstein.Mixed.SysIndM

/-!
# Coupled Risch systems: bounding the special degrees at a primitive level

`D` is a special degree for `(η, β)` over `Fₘ` if some nonzero constant vector `c` makes
`(D η + β) c` a derivative (`SpecialDeg`). For each component `i` the family
`(η eᵢ, βᵢ₁, …, βᵢₙ)` is handed to parametric integration (`lim`, with `LimSpec`); every relation
`(D c, c)` lies in the span of the returned rational vectors, so it is orthogonal to their
annihilator `U` (`nullBasis`). Hence `(D Uₐ + U_c) c = 0`; after a fixed rational combination of
the rows, `D` is a root of the pencil determinant `det(X Pₐ + P_c) ∈ ℚ[X]`, bounded by `rootBound`
(`specBound_spec`; `none` if that determinant vanishes identically).
-/

open Polynomial CPoly Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP

/-- Vectors from `nullBasis` of the transpose are orthogonal to the rows. -/
lemma ann_orth (V : List (CPoly ℚ)) (L : ℕ) (w : CPoly ℚ)
    (hw : w ∈ CPoly.nullBasis (transposeL V L)) (k : ℕ) (hk : k < V.length) :
    ∑ j ∈ Finset.range L, w.getD j 0 * (V.getD k []).getD j 0 = 0 := by
  have horth := CPoly.nullBasis_sound (transposeL V L) w hw
  have hcol : ∀ j < L, ((transposeL V L).getD j []).getD k 0 = (V.getD k []).getD j 0 :=
    fun j hj ↦ by
      rw [transposeL, Tower.NestP.NestTower.getD_range_map _ _ hj,
        Tower.NestP.NestTower.getD_map' _ _ [] 0 hk]
  have := congrArg (fun P : ℚ[X] ↦ P.coeff k) horth
  simp only [CPoly.lcomb, coeff_zero] at this
  rw [Tower.NestP.zipWith_sum_getD (fun (c : ℚ) (v : CPoly ℚ) ↦ Polynomial.C c * toPoly v) 0 []
    (fun v ↦ by simp), finset_sum_coeff] at this
  rw [show (transposeL V L).length = L by simp [transposeL]] at this
  refine (Finset.sum_congr rfl fun j hj ↦ ?_).trans this
  rw [coeff_C_mul, coeff_toPoly, hcol j (Finset.mem_range.mp hj)]

lemma sum_range_two {R : Type*} [AddCommMonoid R] (n : ℕ) (f : ℕ → R) :
    ∑ l ∈ Finset.range (2 * n), f l = ∑ j : Fin n, f j + ∑ j : Fin n, f (n + j) := by
  rw [two_mul, Finset.sum_range_add, Fin.sum_univ_eq_sum_range,
    Fin.sum_univ_eq_sum_range (fun j ↦ f (n + j))]

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The family of component `i`: `η eᵢ` (first `n` entries), then the row `βᵢ`. -/
def specWs (m n : ℕ) (η : LC m) (β : Fin n → Fin n → LC m) (i : Fin n) : List (LC m) :=
  (List.range (2 * n)).map fun l ↦
    if l < n then (if l = (i : ℕ) then η else (MO Fc ks m).zero)
    else if h : l - n < n then β i ⟨l - n, h⟩ else (MO Fc ks m).zero

/-- The annihilator rows of all the relation spaces. -/
def specAnn (m n : ℕ) (lim : List (LC m) → List (List ℚ × LC m)) (η : LC m)
    (β : Fin n → Fin n → LC m) : List (CPoly ℚ) :=
  (List.finRange n).flatMap fun i ↦
    CPoly.nullBasis (transposeL ((lim (specWs Fc ks m n η β i)).map Prod.fst) (2 * n))

/-- Row `i` of the combination (weights `(l + 1)ⁱ`) of the first halves. -/
def specPa (U : List (CPoly ℚ)) (n : ℕ) (i j : Fin n) : ℚ :=
  ∑ l ∈ Finset.range U.length, ((l + 1 : ℕ) : ℚ) ^ (i : ℕ) * (U.getD l []).getD j 0

/-- Row `i` of the combination of the second halves. -/
def specPc (U : List (CPoly ℚ)) (n : ℕ) (i j : Fin n) : ℚ :=
  ∑ l ∈ Finset.range U.length, ((l + 1 : ℕ) : ℚ) ^ (i : ℕ) * (U.getD l []).getD (n + j) 0

/-- The pencil determinant `det(X Pₐ + P_c)`. -/
def pencilPoly (U : List (CPoly ℚ)) (n : ℕ) : CPoly ℚ :=
  detF [] [1] CPoly.add CPoly.mul CPoly.neg n fun i j ↦ [specPc U n i j, specPa U n i j]

/-- **The bound on the special degrees.** -/
def specBound (m n : ℕ) (lim : List (LC m) → List (List ℚ × LC m)) (η : LC m)
    (β : Fin n → Fin n → LC m) : Option ℕ :=
  let P := pencilPoly (specAnn Fc ks m n lim η β) n
  if CPoly.isZero P then none else some (maxRootLE P ⌈rootBoundL P⌉₊)

lemma eval_pencilPoly (U : List (CPoly ℚ)) (n : ℕ) (x : ℚ) :
    (toPoly (pencilPoly U n)).eval x =
      (Matrix.of fun i j ↦ x * specPa U n i j + specPc U n i j).det := by
  rw [pencilPoly, detF_spec [] [1] CPoly.add CPoly.mul CPoly.neg (fun p ↦ (toPoly p).eval x)
    (by simp) (by simp) (by simp) (by simp) (by simp)]
  congr 1
  ext i j
  simp only [Matrix.of_apply, toPoly_cons, toPoly_nil]
  simp; ring

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Every special degree is bounded by `specBound`.** -/
theorem specBound_spec (m : ℕ) (h : T.Tr m) (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h) lim) (n : ℕ) (η : LC m)
    (β : Fin n → Fin n → LC m) (Bs : ℕ) (hB : specBound Fc ks m n lim η β = some Bs) (D : ℕ)
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
  -- the pencil kills `κ`
  have hPκ : ∀ i : Fin n, ∑ j, (((D : ℚ) * specPa U n i j + specPc U n i j : ℚ) : Cc) * κ j = 0 := by
    intro i
    have e : ∀ j, (((D : ℚ) * specPa U n i j + specPc U n i j : ℚ) : Cc) * κ j =
        ∑ l ∈ Finset.range U.length, ((((l + 1 : ℕ) : ℚ) ^ (i : ℕ) : ℚ) : Cc) *
          ((((U.getD l []).getD j 0 : ℚ) : Cc) * ((D : Cc) * κ j) +
            (((U.getD l []).getD (n + j) 0 : ℚ) : Cc) * κ j) := fun j ↦ by
      simp only [specPa, specPc]
      push_cast
      simp only [add_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ ↦ by ring
    rw [Finset.sum_congr rfl fun j _ ↦ e j, Finset.sum_comm]
    refine Finset.sum_eq_zero fun l hl ↦ ?_
    rw [← Finset.mul_sum, hUκ _ (getD_memC _ _ (Finset.mem_range.mp hl)), mul_zero]
  have hκ0 : κ ≠ 0 := fun h0 ↦ hc0 (funext fun j ↦ by
    rw [hκ j, h0, Pi.zero_apply, map_zero, Pi.zero_apply])
  set Mq : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j ↦ (D : ℚ) * specPa U n i j + specPc U n i j
    with hMq
  have hdetC : ((algebraMap ℚ Cc).mapMatrix Mq).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨κ, hκ0, funext fun i ↦ by
      simpa [Matrix.mulVec, dotProduct, hMq, eq_ratCast] using hPκ i⟩
  rw [← RingHom.map_det] at hdetC
  have hdet : Mq.det = 0 := (algebraMap ℚ Cc).injective (by rw [hdetC, map_zero])
  have hroot : (toPoly (pencilPoly U n)).IsRoot (D : ℚ) := by
    rw [IsRoot.def, eval_pencilPoly]; exact hdet
  unfold specBound at hB
  simp only at hB
  split_ifs at hB with hz
  obtain rfl := Option.some.inj hB
  have hP0 : toPoly (pencilPoly U n) ≠ 0 := fun h0 ↦ hz ((CPoly.isZero_iff _).mpr h0)
  have hb := abs_le_rootBound _ hP0 _ hroot
  rw [← rootBoundL_eq _ hP0, abs_of_nonneg (by positivity)] at hb
  exact le_maxRootLE _ _ D (by exact_mod_cast hb.trans (Nat.le_ceil _)) hroot

end MTower

end Curves.MT
