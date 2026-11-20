import RischTragerBronstein.Mixed.SysSpecial2
import RischTragerBronstein.Computable.SysDegL
import RischTragerBronstein.Computable.SysLoopC
import RischTragerBronstein.Computable.SysRel
import RischTragerBronstein.Computable.RatProj

/-!
# Special degrees with a limit matrix, through a solver one level down

At a primitive level with a limit matrix `Λ ≠ 0` at infinity, a special degree `D` (`SpecialDegL`)
is a nonzero solution `c` of `c′ + Λ c = 0` with `−(D w0 + β) c` in the image of `y ↦ y′ + Λ y`.
`specBoundL` computes, with any parametric solver `low` for `y′ + Λ y = ∑ cₗ wₗ` (`SysSpecAt`):
a basis `V` of the homogeneous solutions (`low []`), the relations of the family
`(w0 v)_{v ∈ V}, (β v)_{v ∈ V}`, their annihilator `U`, and the Gram determinant of the pencil
`X U₁ + U₂`; a special degree `D` makes it vanish at `D` (`specBoundL_spec`).
-/

open Polynomial CPoly Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP

section Codes

variable {α : Type} (O : COps α) {n : ℕ}

/-- The family `(w0 v)_{v ∈ V}, (β v)_{v ∈ V}`. -/
def specWsL (η : α) (β : Fin n → Fin n → α) (V : List (Fin n → α)) : List (Fin n → α) :=
  (List.range (2 * V.length)).map fun l ↦
    if l < V.length then (fun i ↦ O.mul η ((V.getD l fun _ ↦ O.zero) i))
    else mvC O β (V.getD (l - V.length) fun _ ↦ O.zero)

/-- The values of coordinate `x` of the vectors `V`. -/
def vecCoordsL (V : List (Fin n → α)) (x : ℕ) : List α :=
  if h : x < n then V.map fun v ↦ v ⟨x, h⟩ else V.map fun _ ↦ O.zero

/-- The entry `∑ₖ kᵢ kⱼ` of the Gram matrix of the relations. -/
def hEntry (K0 : List (List ℚ)) (i j : ℕ) : ℚ := (K0.map fun k ↦ k.getD i 0 * k.getD j 0).sum

/-- The Gram entry of the pencil plus the relation term. -/
def gramEntryH (U K0 : List (CPoly ℚ)) (r : ℕ) (i j : Fin r) : CPoly ℚ :=
  [(U.map fun u ↦ u.getD (r + i) 0 * u.getD (r + j) 0).sum + hEntry K0 i j,
   (U.map fun u ↦ u.getD i 0 * u.getD (r + j) 0 + u.getD (r + i) 0 * u.getD j 0).sum,
   (U.map fun u ↦ u.getD i 0 * u.getD j 0).sum]

/-- The determinant of `G(X) + H`. -/
def gramPolyH (U K0 : List (CPoly ℚ)) (r : ℕ) : CPoly ℚ :=
  detF [] [1] CPoly.add CPoly.mul CPoly.neg r (gramEntryH U K0 r)

/-- **The bound on the special degrees with a limit matrix.** -/
def specBoundL (cst : ℚ → α) (rel : List α → List (List ℚ))
    (low : List (Fin n → α) → List (List ℚ × (Fin n → α))) (η : α)
    (β : Fin n → Fin n → α) : Option ℕ :=
  let V := (low []).map Prod.snd
  let K0 := relRun O cst rel V.length (vecCoordsL O V) n
  let U := CPoly.nullBasis (transposeL ((low (specWsL O η β V)).map Prod.fst) (2 * V.length))
  let P := gramPolyH U K0 V.length
  if CPoly.isZero P then none else some (maxRootLE P ⌈rootBoundL P⌉₊)

lemma eval_gramPolyH (U K0 : List (CPoly ℚ)) (r : ℕ) (x : ℚ) :
    (toPoly (gramPolyH U K0 r)).eval x = (Matrix.of fun i j : Fin r ↦ (U.map fun u ↦
      (x * u.getD i 0 + u.getD (r + i) 0) * (x * u.getD j 0 + u.getD (r + j) 0)).sum +
        hEntry K0 i j).det := by
  rw [gramPolyH, detF_spec [] [1] CPoly.add CPoly.mul CPoly.neg (fun p ↦ (toPoly p).eval x)
    (by simp) (by simp) (by simp) (by simp) (by simp)]
  congr 1
  ext i j
  simp only [Matrix.of_apply, gramEntryH, toPoly_cons, toPoly_nil]
  simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, add_zero]
  have hU : ∀ U : List (CPoly ℚ), (U.map fun u ↦
      (x * u.getD i 0 + u.getD (r + i) 0) * (x * u.getD j 0 + u.getD (r + j) 0)).sum =
      (U.map fun u ↦ u.getD (r + i) 0 * u.getD (r + j) 0).sum +
        x * ((U.map fun u ↦ u.getD i 0 * u.getD (r + j) 0 + u.getD (r + i) 0 * u.getD j 0).sum +
          x * (U.map fun u ↦ u.getD i 0 * u.getD j 0).sum) := by
    intro U
    induction U with
    | nil => simp
    | cons u U ih =>
      simp only [List.map_cons, List.sum_cons]
      linear_combination ih
  rw [hU]
  ring

end Codes

section Sem

variable {α : Type} {K Cs : Type*} [Field K] [Differential K] [CharZero K] [Field Cs] [CharZero Cs]
  (ι : Cs →+* K) {O : COps α} (M : CField α K O) {n : ℕ}

/-- **Every special degree is bounded by `specBoundL`.** -/
theorem specBoundL_spec (cst : ℚ → α) (hcst : ∀ q, M.sem (cst q) = q)
    (rel : List α → List (List ℚ)) (hrel : RelSpec ι M rel) (F : Fin n → Fin n → K)
    (low : List (Fin n → α) → List (List ℚ × (Fin n → α)))
    (hlow : ∀ ws, SysSpecAt ι F (ws.map (semVa M)) (semR M (low ws)))
    (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K))
    (η : α) (β : Fin n → Fin n → α) (Bs : ℕ) (hB : specBoundL O cst rel low η β = some Bs) (D : ℕ)
    (hD : SpecialDegL (M.sem η) (Matrix.of F) (Matrix.of fun i j ↦ M.sem (β i j)) D) :
    D ≤ Bs := by
  classical
  obtain ⟨c, hc0, hc, y, hy⟩ := hD
  set R0 := low [] with hR0
  set V := R0.map Prod.snd with hV
  set r := V.length with hr
  have hrR : R0.length = r := by simp [hr, hV]
  -- the semantic basis vectors
  set Vs : ℕ → Fin n → K := fun k i ↦ M.sem ((V.getD k fun _ ↦ O.zero) i) with hVs
  have hsemR0 : ∀ k < r, ((semR M R0).getD k ([], 0)).2 = Vs k := by
    intro k hk
    funext i
    have hk' : k < R0.length := by omega
    simp only [semR, hVs, hV]
    rw [List.getD_eq_getElem _ _ (by simpa using hk'), List.getD_eq_getElem _ _ (by simpa using hk')]
    simp
  -- `c` is a combination of `V`
  obtain ⟨γ, -, hcγ⟩ := (hlow []).2 [] (fun _ _ ↦ by simp) c (fun i ↦ by
    have := hc i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply] at this
    simpa [mv] using this)
  have hlenR0 : (semR M R0).length = r := by simp [semR, hrR]
  have hc' : ∀ i, c i = ∑ k ∈ Finset.range r, ι (γ.getD k 0) * Vs k i := fun i ↦ by
    rw [hcγ i, hlenR0]
    exact Finset.sum_congr rfl fun k hk ↦ by rw [hsemR0 k (Finset.mem_range.mp hk)]
  -- the relations among `V`
  set K0 := relRun O cst rel r (vecCoordsL O V) n with hK0
  have hvl : ∀ x, (vecCoordsL O V x).length = r := fun x ↦ by
    unfold vecCoordsL; split_ifs <;> simp [hr]
  obtain ⟨hK0s, -⟩ := relRun_inv ι M cst hcst rel r (vecCoordsL O V) hrel hvl hιrat n
  have hvc : ∀ (i : Fin n) (b : ℕ), b < r → M.sem ((vecCoordsL O V i).getD b O.zero) = Vs b i := by
    intro i b hb
    simp only [vecCoordsL, i.2, ↓reduceDIte, hVs]
    rw [List.getD_eq_getElem _ _ (by simpa using hb), List.getD_eq_getElem _ _ (by simpa using hb)]
    simp
  have hK0V : ∀ k ∈ K0, ∀ i : Fin n, ∑ b ∈ Finset.range r, ((k.getD b 0 : ℚ) : K) * Vs b i = 0 :=
    fun k hk i ↦ by
      rw [← hK0s k hk i i.2]
      exact Finset.sum_congr rfl fun b hb ↦ by rw [hvc i b (Finset.mem_range.mp hb)]
  -- the family
  set ws := specWsL O η β V with hws
  have hwslen : ws.length = 2 * r := by simp [hws, specWsL, hr]
  have hwsg : ∀ l < 2 * r, (ws.map (semVa M)).getD l 0 = semVa M (if l < r then
      (fun i ↦ O.mul η ((V.getD l fun _ ↦ O.zero) i))
      else mvC O β (V.getD (l - r) fun _ ↦ O.zero)) := by
    intro l hl
    rw [List.getD_eq_getElem _ _ (by simp [hwslen]; omega), List.getElem_map]
    congr 1
    rw [← List.getD_eq_getElem ws (fun _ ↦ O.zero) (by simp [hwslen]; omega), hws, specWsL,
      NestTower.getD_range_map _ _ hl]
  have hwsL : ∀ k < r, (ws.map (semVa M)).getD k 0 = fun i ↦ M.sem η * Vs k i := by
    intro k hk
    rw [hwsg k (by omega)]
    funext i
    simp only [hk, ↓reduceIte, semVa, M.sem_mul, hVs]
  have hwsR : ∀ k < r, (ws.map (semVa M)).getD (r + k) 0 =
      mv (fun i j ↦ M.sem (β i j)) (Vs k) := by
    intro k hk
    rw [hwsg (r + k) (by omega)]
    funext i
    simp only [show ¬ (r + k < r) by omega, ↓reduceIte, semVa, sem_mvC,
      show r + k - r = k by omega, hVs]
  -- the right-hand side for coefficients `(D a, a)`
  have hrhs : ∀ (a : ℕ → Cs) (i : Fin n), ∑ l ∈ Finset.range (2 * r),
      ι ((if l < r then (D : Cs) * a l else a (l - r))) * ((ws.map (semVa M)).getD l 0) i =
      (D : K) * M.sem η * (∑ k ∈ Finset.range r, ι (a k) * Vs k i) +
        ∑ j, M.sem (β i j) * ∑ k ∈ Finset.range r, ι (a k) * Vs k j := by
    intro a i
    rw [sum_range_two]
    have hL : ∀ j : Fin r, ι (if (j : ℕ) < r then (D : Cs) * a j else a (j - r)) *
        ((ws.map (semVa M)).getD j 0) i = (D : K) * M.sem η * (ι (a j) * Vs j i) := fun j ↦ by
      rw [if_pos j.2, hwsL j j.2]; simp only [map_mul, map_natCast]; ring
    have hR : ∀ j : Fin r, ι (if r + (j : ℕ) < r then (D : Cs) * a (r + j) else a (r + j - r)) *
        ((ws.map (semVa M)).getD (r + j) 0) i =
        ι (a j) * mv (fun i j ↦ M.sem (β i j)) (Vs j) i := fun j ↦ by
      rw [if_neg (by omega), hwsR j j.2, show r + (j : ℕ) - r = j by omega]
    simp only [hL, hR, ← Finset.mul_sum]
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range (fun k ↦ ι (a k) * Vs k i)]
    · simp only [mv, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← Fin.sum_univ_eq_sum_range (fun k ↦ M.sem (β i j) * (ι (a k) * Vs k j)) r]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
  -- relations solvable one level down are killed by the annihilator rows
  set U := CPoly.nullBasis (transposeL ((low ws).map Prod.fst) (2 * r)) with hU
  have hann : ∀ a : ℕ → Cs, (∃ z : Fin n → K, ∀ i, (z i)′ + mv F z i = ∑ l ∈ Finset.range (2 * r),
      ι ((if l < r then (D : Cs) * a l else a (l - r))) * ((ws.map (semVa M)).getD l 0) i) →
      ∀ u ∈ U, ∑ j : Fin r, (((u.getD j 0 : ℚ) : Cs) * ((D : Cs) * a j) +
        ((u.getD (r + j) 0 : ℚ) : Cs) * a j) = 0 := by
    intro a ⟨z, hz⟩ u hu
    set cl : List Cs := (List.range (2 * r)).map fun l ↦ if l < r then (D : Cs) * a l else a (l - r)
      with hcl
    have hcll : ∀ l < 2 * r, cl.getD l 0 = if l < r then (D : Cs) * a l else a (l - r) :=
      fun l hl ↦ by rw [hcl, NestTower.getD_range_map _ _ hl]
    have hclen : ∀ l, (ws.map (semVa M)).length ≤ l → cl.getD l 0 = 0 := fun l hl ↦
      List.getD_eq_default _ _ (by simp [hcl]; simp [hwslen] at hl; omega)
    obtain ⟨γ', hγ', -⟩ := (hlow ws).2 cl hclen z (fun i ↦ by
      rw [hz i, List.length_map, hwslen]
      exact Finset.sum_congr rfl fun l hl ↦ by rw [hcll l (Finset.mem_range.mp hl)])
    have hVk : ∀ k, ((low ws).map Prod.fst).getD k [] = ((semR M (low ws)).getD k ([], 0)).1 :=
      fun k ↦ by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, semR,
          List.getElem?_map]
        cases (low ws)[k]? <;> rfl
    have hsum : ∑ l ∈ Finset.range (2 * r), ((u.getD l 0 : ℚ) : Cs) * cl.getD l 0 = 0 := by
      have e1 : ∀ l ∈ Finset.range (2 * r), ((u.getD l 0 : ℚ) : Cs) * cl.getD l 0 =
          ∑ k ∈ Finset.range (semR M (low ws)).length, γ'.getD k 0 * ((u.getD l 0 *
            ((semR M (low ws)).getD k ([], 0)).1.getD l 0 : ℚ) : Cs) := fun l _ ↦ by
        rw [hγ' l, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [eq_ratCast]; push_cast; ring
      rw [Finset.sum_congr rfl e1, Finset.sum_comm]
      refine Finset.sum_eq_zero fun k hk ↦ ?_
      have ho := ann_orth ((low ws).map Prod.fst) (2 * r) u hu k
        (by simpa [semR] using Finset.mem_range.mp hk)
      rw [hVk] at ho
      rw [← Finset.mul_sum, ← Rat.cast_sum, ho, Rat.cast_zero, mul_zero]
    rw [sum_range_two] at hsum
    have e1 : ∀ j : Fin r, cl.getD j 0 = (D : Cs) * a j := fun j ↦ by
      rw [hcll j (by omega), if_pos j.2]
    have e2 : ∀ j : Fin r, cl.getD (r + j) 0 = a j := fun j ↦ by
      rw [hcll (r + j) (by omega), if_neg (by omega), show r + (j : ℕ) - r = j by omega]
    simp only [e1, e2, ← Finset.sum_add_distrib] at hsum
    exact hsum
  -- `κ = −γ` satisfies the pencil equations
  set κ : Fin r → Cs := fun j ↦ -γ.getD j 0 with hκ
  have hUκ := hann (fun k ↦ -γ.getD k 0) ⟨y, fun i ↦ by
    have h1 := hy i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply] at h1
    rw [show mv F y i = ∑ j, F i j * y j from rfl, h1, hrhs]
    simp only [map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib, hc']
    ring⟩
  -- the relations satisfy the pencil equations
  have hK0p : ∀ k ∈ K0, ∀ u ∈ U, ∑ j : Fin r, (((u.getD j 0 : ℚ) : Cs) * ((D : Cs) *
      ((k.getD j 0 : ℚ) : Cs)) + ((u.getD (r + j) 0 : ℚ) : Cs) * ((k.getD j 0 : ℚ) : Cs)) = 0 := by
    intro k hk
    refine hann (fun b ↦ ((k.getD b 0 : ℚ) : Cs)) ⟨0, fun i ↦ ?_⟩
    rw [hrhs]
    have h0 : ∀ i, ∑ b ∈ Finset.range r, ι (((k.getD b 0 : ℚ) : Cs)) * Vs b i = 0 := fun i ↦ by
      rw [← hK0V k hk i]
      exact Finset.sum_congr rfl fun b _ ↦ by rw [map_ratCast]
    simp only [h0, mul_zero, zero_add, Finset.sum_const_zero]
    simp [mv]
  -- project `κ` orthogonally to the relations
  choose a q hdec horth using fun s : Fin r ↦ rat_proj K0 r (fun j ↦ if j = s then 1 else 0)
  set κ' : Fin r → Cs := fun j ↦ ∑ s, κ s * ((q s j : ℚ) : Cs) with hκ'
  have hκdec : ∀ j : Fin r, κ j = κ' j + ∑ t ∈ Finset.range K0.length,
      (∑ s, κ s * ((a s t : ℚ) : Cs)) * (((K0.getD t []).getD j 0 : ℚ) : Cs) := by
    intro j
    have hdec' : ∀ s : Fin r, (if j = s then (1 : ℚ) else 0) = q s j + ∑ t ∈ Finset.range K0.length,
        a s t * (K0.getD t []).getD j 0 := fun s ↦ hdec s j
    have e : κ j = ∑ s, κ s * (((if j = s then 1 else 0 : ℚ)) : Cs) := by
      rw [Finset.sum_eq_single j (fun s _ hs ↦ by rw [if_neg (Ne.symm hs)]; simp) (by simp)]
      simp
    rw [e, hκ']
    simp only [hdec', Rat.cast_add, Rat.cast_sum, Rat.cast_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun s _ ↦ by ring
  have hK0κ' : ∀ t < K0.length, ∑ j : Fin r, (((K0.getD t []).getD j 0 : ℚ) : Cs) * κ' j = 0 := by
    intro t ht
    simp only [hκ', Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun s _ ↦ ?_
    have := horth s t ht
    have e : ∑ j : Fin r, (((K0.getD t []).getD j 0 : ℚ) : Cs) * (κ s * ((q s j : ℚ) : Cs)) =
        κ s * (((∑ j : Fin r, (K0.getD t []).getD j 0 * q s j : ℚ)) : Cs) := by
      push_cast; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [e, this, Rat.cast_zero, mul_zero]
  -- `κ′` satisfies the pencil equations
  set bt : ℕ → Cs := fun t ↦ ∑ s, κ s * ((a s t : ℚ) : Cs) with hbt
  have hUκ' : ∀ u ∈ U, ∑ j : Fin r, (((u.getD j 0 : ℚ) : Cs) * ((D : Cs) * κ' j) +
      ((u.getD (r + j) 0 : ℚ) : Cs) * κ' j) = 0 := by
    intro u hu
    have h1 : ∑ j : Fin r, (((u.getD j 0 : ℚ) : Cs) * ((D : Cs) * κ j) +
        ((u.getD (r + j) 0 : ℚ) : Cs) * κ j) = 0 := hUκ u hu
    have hP : ∀ t ∈ Finset.range K0.length, ∑ j : Fin r, (((u.getD j 0 : ℚ) : Cs) * ((D : Cs) *
        (((K0.getD t []).getD j 0 : ℚ) : Cs)) + ((u.getD (r + j) 0 : ℚ) : Cs) *
          (((K0.getD t []).getD j 0 : ℚ) : Cs)) = 0 := by
      intro t ht
      have hkt : K0.getD t [] ∈ K0 := by
        rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp ht)]; exact List.getElem_mem _
      exact hK0p _ hkt u hu
    set wj : Fin r → Cs := fun j ↦ ((u.getD j 0 : ℚ) : Cs) * (D : Cs) + ((u.getD (r + j) 0 : ℚ) : Cs)
      with hwj
    have hw : ∀ x : Fin r → Cs, ∑ j : Fin r, (((u.getD j 0 : ℚ) : Cs) * ((D : Cs) * x j) +
        ((u.getD (r + j) 0 : ℚ) : Cs) * x j) = ∑ j, wj j * x j := fun x ↦
      Finset.sum_congr rfl fun j _ ↦ by simp only [hwj]; ring
    rw [hw] at h1 ⊢
    have hP' : ∀ t ∈ Finset.range K0.length, ∑ j : Fin r, wj j * (((K0.getD t []).getD j 0 : ℚ) : Cs)
        = 0 := fun t ht ↦ by rw [← hw]; exact hP t ht
    have E : ∑ j, wj j * κ j = ∑ j, wj j * κ' j + ∑ t ∈ Finset.range K0.length, bt t *
        ∑ j : Fin r, wj j * (((K0.getD t []).getD j 0 : ℚ) : Cs) := by
      rw [Finset.sum_congr rfl fun j _ ↦ congrArg (wj j * ·) (hκdec j)]
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun j _ ↦ by simp only [hbt]; ring
    rw [Finset.sum_eq_zero (s := Finset.range K0.length) (fun t ht ↦ by rw [hP' t ht, mul_zero]),
      add_zero, h1] at E
    exact E.symm
  -- the relation term vanishes on `κ′`
  have hHκ' : ∀ i : Fin r, ∑ j : Fin r, ((hEntry K0 i j : ℚ) : Cs) * κ' j = 0 := by
    intro i
    have : ∀ j : Fin r, ((hEntry K0 i j : ℚ) : Cs) = ∑ t ∈ Finset.range K0.length,
        (((K0.getD t []).getD i 0 : ℚ) : Cs) * (((K0.getD t []).getD j 0 : ℚ) : Cs) := by
      intro j
      rw [hEntry, ← Fin.sum_univ_eq_sum_range (fun t ↦ (((K0.getD t []).getD i 0 : ℚ) : Cs) *
        (((K0.getD t []).getD j 0 : ℚ) : Cs)), ← List.sum_ofFn]
      push_cast
      congr 1
      apply List.ext_getElem (by simp)
      intro t h1 h2
      simp [List.getD_eq_getElem?_getD]
    simp only [this, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun t ht ↦ ?_
    have e : ∑ j : Fin r, (((K0.getD t []).getD i 0 : ℚ) : Cs) * (((K0.getD t []).getD j 0 : ℚ) : Cs) *
        κ' j = (((K0.getD t []).getD i 0 : ℚ) : Cs) *
          ∑ j : Fin r, (((K0.getD t []).getD j 0 : ℚ) : Cs) * κ' j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [e, hK0κ' t (Finset.mem_range.mp ht), mul_zero]
  -- `κ′ ≠ 0`
  have hκ'0 : κ' ≠ 0 := by
    intro h0
    apply hc0
    have hκz : ∀ j : Fin r, κ j = ∑ t ∈ Finset.range K0.length, bt t *
        (((K0.getD t []).getD j 0 : ℚ) : Cs) := fun j ↦ by
      rw [hκdec j, h0, Pi.zero_apply, zero_add]
    funext i
    rw [hc' i, Pi.zero_apply, ← Fin.sum_univ_eq_sum_range (fun k ↦ ι (γ.getD k 0) * Vs k i)]
    have hγκ : ∀ k : Fin r, ι (γ.getD k 0) = -ι (κ k) := fun k ↦ by simp [hκ]
    rw [Finset.sum_congr rfl fun k _ ↦ by rw [hγκ k, hκz k]]
    simp only [map_sum, map_mul, map_ratCast, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul,
      neg_eq_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun t ht ↦ ?_
    have hkt : K0.getD t [] ∈ K0 := by
      rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp ht)]; exact List.getElem_mem _
    have h1 := hK0V _ hkt i
    rw [← Fin.sum_univ_eq_sum_range (fun b ↦ (((K0.getD t []).getD b 0 : ℚ) : K) * Vs b i)] at h1
    have e : ∑ k : Fin r, ι (bt t) * (((K0.getD t []).getD k 0 : ℚ) : K) * Vs k i =
        ι (bt t) * ∑ k : Fin r, (((K0.getD t []).getD k 0 : ℚ) : K) * Vs k i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [e, h1, mul_zero]
  -- the determinant of `G(D) + H` vanishes
  set Gq : Matrix (Fin r) (Fin r) ℚ := Matrix.of fun i j : Fin r ↦ (U.map fun u ↦
      ((D : ℚ) * u.getD i 0 + u.getD (r + i) 0) * ((D : ℚ) * u.getD j 0 + u.getD (r + j) 0)).sum +
        hEntry K0 i j with hGq
  have hGκ : ∀ i : Fin r, ∑ j, ((Gq i j : ℚ) : Cs) * κ' j = 0 := fun i ↦ by
    have h1 := gram_kill r (D : ℚ) κ' i U (fun u hu ↦ by simpa using hUκ' u hu)
    have h2 := hHκ' i
    have e : ∀ j : Fin r, ((Gq i j : ℚ) : Cs) * κ' j = (((U.map fun u ↦
        ((D : ℚ) * u.getD i 0 + u.getD (r + i) 0) * ((D : ℚ) * u.getD j 0 + u.getD (r + j) 0)).sum :
          ℚ) : Cs) * κ' j + ((hEntry K0 i j : ℚ) : Cs) * κ' j := fun j ↦ by
      simp only [hGq, Matrix.of_apply, Rat.cast_add]; ring
    rw [Finset.sum_congr rfl fun j _ ↦ e j, Finset.sum_add_distrib, h2, add_zero]
    exact h1
  have hdetC : ((algebraMap ℚ Cs).mapMatrix Gq).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨κ', hκ'0, funext fun i ↦ by
      simpa [Matrix.mulVec, dotProduct, eq_ratCast] using hGκ i⟩
  rw [← RingHom.map_det] at hdetC
  have hdet : Gq.det = 0 := (algebraMap ℚ Cs).injective (by rw [hdetC, map_zero])
  have hroot : (toPoly (gramPolyH U K0 r)).IsRoot (D : ℚ) := by
    rw [IsRoot.def, eval_gramPolyH]; exact hdet
  unfold specBoundL at hB
  simp only at hB
  split_ifs at hB with hz
  obtain rfl := Option.some.inj hB
  have hP0 : toPoly (gramPolyH U K0 r) ≠ 0 := fun h0 ↦ hz ((CPoly.isZero_iff _).mpr h0)
  have hb := abs_le_rootBound _ hP0 _ hroot
  rw [← rootBoundL_eq _ hP0, abs_of_nonneg (by positivity)] at hb
  exact le_maxRootLE _ _ D (by exact_mod_cast hb.trans (Nat.le_ceil _)) hroot

end Sem


end Curves.MT
