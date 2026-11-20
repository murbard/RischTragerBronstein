import RischTragerBronstein.Computable.NestPBasics

/-!
# Parametric limited integration in towers with nested primitives: soundness and completeness

`paramLim_sound`: every returned `(e, y)` has `y′ = ∑ eᵢ wᵢ`.
`paramLim_complete`: every `(c, z)` with constants `cᵢ` and `z′ = ∑ cᵢ wᵢ` is, up to a constant in
`z`, a combination with constant coefficients of the returned pairs.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestP

open Tower.PrimN

section Generic

variable {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)
  (cst : ℚ → α) (hcst : ∀ q, M.sem (cst q) = (q : K))

include hcst in
lemma sem_lcombCode : ∀ (e : List ℚ) (as : List α),
    M.sem (lcombCode O cst e as) = (List.zipWith (fun (q : ℚ) a ↦ (q : K) * M.sem a) e as).sum
  | [], _ => by simp [lcombCode, M.sem_zero]
  | _ :: _, [] => by simp [lcombCode, M.sem_zero]
  | q :: e, a :: as => by
    have ih := sem_lcombCode e as
    simp only [lcombCode, List.zipWith_cons_cons, List.foldr_cons] at ih ⊢
    rw [M.sem_add, M.sem_mul, hcst, ih, List.sum_cons]

include hcst in
lemma toPoly_lcombGP : ∀ (e : List ℚ) (ps : List (GPoly α)),
    GPoly.toPoly M (lcombGP O cst e ps) =
      (List.zipWith (fun (q : ℚ) p ↦ C (q : K) * GPoly.toPoly M p) e ps).sum
  | [], _ => by simp [lcombGP]
  | _ :: _, [] => by simp [lcombGP]
  | q :: e, p :: ps => by
    have ih := toPoly_lcombGP e ps
    simp only [lcombGP, List.zipWith_cons_cons, List.foldr_cons] at ih ⊢
    rw [GPoly.toPoly_add, GPoly.toPoly_smul, hcst, ih, List.sum_cons]

end Generic

namespace NestTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ηs : (m : ℕ) → Code (m + 1)}
variable (T : NestTower Kc E ηs)

lemma zipWith_sum_range {α β γ : Type*} [AddCommMonoid γ] (f : α → β → γ) (d₁ : α) (d₂ : β) :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
      (List.zipWith f l₁ l₂).sum = ∑ i ∈ Finset.range l₁.length, f (l₁.getD i d₁) (l₂.getD i d₂)
  | [], [], _ => by simp
  | a :: l₁, b :: l₂, h => by
    rw [List.zipWith_cons_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ',
      zipWith_sum_range f d₁ d₂ l₁ l₂ (by simpa using h), add_comm]
    simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The zero code of level `m`. -/
def zc (ηs : (m : ℕ) → Code (m + 1)) (m : ℕ) : Code (m + 1) := (opsQ ηs m).zero

/-- `∑ cᵢ wᵢ` with constant coefficients. -/
noncomputable def sumK (m : ℕ) (h : T.Tr m) (c : List Kc) (W : List (Code (m + 1))) : T.F m :=
  ∑ i ∈ Finset.range W.length,
    algebraMap Kc (T.F m) (c.getD i 0) * (T.MP m h).sem (W.getD i (zc ηs m))

/-- `∑ eᵢ wᵢ` with rational coefficients. -/
noncomputable def sumQ (m : ℕ) (h : T.Tr m) (e : List ℚ) (W : List (Code (m + 1))) : T.F m :=
  ∑ i ∈ Finset.range W.length, ((e.getD i 0 : ℚ) : T.F m) * (T.MP m h).sem (W.getD i (zc ηs m))

/-- The soundness statement of a parametric solution list. -/
def PLSound (m : ℕ) (h : T.Tr m) (W : List (Code (m + 1)))
    (out : List (List ℚ × Code (m + 1))) : Prop :=
  ∀ r ∈ out, ((T.MP m h).sem r.2)′ = T.sumQ m h r.1 W

/-- The completeness statement of a parametric solution list. -/
def PLComplete (m : ℕ) (h : T.Tr m) (W : List (Code (m + 1)))
    (out : List (List ℚ × Code (m + 1))) : Prop :=
  ∀ c : List Kc, (∀ i, W.length ≤ i → c.getD i 0 = 0) → ∀ z : T.F m, z′ = T.sumK m h c W →
    ∃ β : List Kc,
      (∀ i, c.getD i 0 = ∑ k ∈ Finset.range out.length,
        β.getD k 0 * algebraMap ℚ Kc ((out.getD k ([], zc ηs m)).1.getD i 0)) ∧
      (z - ∑ k ∈ Finset.range out.length,
        algebraMap Kc (T.F m) (β.getD k 0) * (T.MP m h).sem (out.getD k ([], zc ηs m)).2)′ = 0

lemma algebraMap_ratCast {m : ℕ} (q : ℚ) :
    algebraMap Kc (T.F m) (algebraMap ℚ Kc q) = (q : T.F m) := by
  rw [eq_ratCast (algebraMap ℚ Kc) q, map_ratCast]

lemma list_sum_map_range {γ : Type*} [AddCommMonoid γ] (f : ℕ → γ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma deriv_sum_ratCast {m : ℕ} (n : ℕ) (q : ℕ → ℚ) (a : ℕ → T.F m) :
    (∑ i ∈ Finset.range n, (q i : T.F m) * a i)′ = ∑ i ∈ Finset.range n, (q i : T.F m) * (a i)′ := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Derivation.leibniz, T.deriv_ratCast, smul_eq_mul, smul_eq_mul, mul_zero, add_zero, mul_comm]

lemma deriv_sum_Kc {m : ℕ} (n : ℕ) (q : ℕ → Kc) (a : ℕ → T.F m) :
    (∑ i ∈ Finset.range n, algebraMap Kc (T.F m) (q i) * a i)′ =
      ∑ i ∈ Finset.range n, algebraMap Kc (T.F m) (q i) * (a i)′ := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Derivation.leibniz, T.deriv_algebraMap_Kc, smul_eq_mul, smul_eq_mul, mul_zero, add_zero,
    mul_comm]

/-- The value of `paramLim` at the base, for one basis vector. -/
lemma sem_y0 (h : T.Tr 0) (W : List (Code 1)) (e : List ℚ) (he : e.length = W.length) :
    (T.MP 0 h).sem (lcombCode (opsQ ηs 0) (cstN 0) e (W.map fun w ↦ ratPart (ratInt w))) =
      ∑ i ∈ Finset.range W.length,
        ((e.getD i 0 : ℚ) : T.F 0) * (T.MP 0 h).sem (ratPart (ratInt (W.getD i (zc ηs 0)))) := by
  rw [sem_lcombCode (T.MP 0 h) (cstN 0) (T.sem_cstN 0 h),
    zipWith_sum_range _ 0 (zc ηs 0) _ _ (by rw [List.length_map, he]), he]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i < W.length := Finset.mem_range.mp hi
  congr 2
  rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map,
    List.getD_eq_getElem _ _ hi']

/-- The decomposition `w = (ratPart)′ + logPart` at the base. -/
lemma sem0_split (h : T.Tr 0) (w : Code 1) :
    (T.MP 0 h).sem w = ((T.MP 0 h).sem (ratPart (ratInt w)))′ + (T.MP 0 h).sem (logPart w) := by
  refine (T.ratInt_spec w).1.trans ?_
  congr 1
  exact (T.model0_sem_eq (logPart w)).symm

lemma getD_range_map {γ : Type*} (f : ℕ → γ) (d : γ) {n i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

lemma getD_map' {γ δ : Type*} (f : γ → δ) (l : List γ) (d : γ) (d' : δ) {i : ℕ}
    (hi : i < l.length) : (l.map f).getD i d' = f (l.getD i d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getD_eq_getElem _ _ hi]

/-- The basis vector as a list of length `n`. -/
def vecOf (n : ℕ) (u : CPoly ℚ) : List ℚ := (List.range n).map fun i ↦ u.getD i 0

lemma getD_vecOf (n : ℕ) (u : CPoly ℚ) (i : ℕ) :
    (vecOf n u).getD i 0 = if i < n then u.getD i 0 else 0 := by
  unfold vecOf
  split_ifs with hi
  · exact getD_range_map _ _ hi
  · exact List.getD_eq_default _ _ (by simpa using hi)

/-- **Parametric limited integration at the base**: soundness and completeness. -/
theorem paramLim_zero (h : T.Tr 0) (W : List (Code 1)) :
    T.PLSound 0 h W (paramLim ηs 0 W) ∧ T.PLComplete 0 h W (paramLim ηs 0 W) := by
  have hout : paramLim ηs 0 W = (consys ηs 0 (W.map logPart)).map fun u ↦
      (vecOf W.length u, lcombCode (opsQ ηs 0) (cstN 0) (vecOf W.length u)
          (W.map fun w ↦ ratPart (ratInt w))) := rfl
  -- the relation given by a basis vector
  have hrel : ∀ u ∈ consys ηs 0 (W.map logPart), ∑ i ∈ Finset.range W.length,
      ((u.getD i 0 : ℚ) : T.F 0) * (T.MP 0 h).sem (logPart (W.getD i (zc ηs 0))) = 0 := by
    intro u hu
    have := T.consys_sound 0 h (W.map logPart) u hu
    rw [zipWith_sum_range _ 0 (zc ηs 0) _ _ (by simp)] at this
    simp only [List.length_map, List.length_range] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i < W.length := Finset.mem_range.mp hi
    rw [getD_range_map (fun j ↦ algebraMap ℚ Kc (u.getD j 0)) 0 hi', T.algebraMap_ratCast,
      getD_map' logPart W (zc ηs 0) (zc ηs 0) hi']
  -- the derivative of a returned solution
  have hder : ∀ u ∈ consys ηs 0 (W.map logPart),
      ((T.MP 0 h).sem (lcombCode (opsQ ηs 0) (cstN 0) (vecOf W.length u)
        (W.map fun w ↦ ratPart (ratInt w))))′ = T.sumQ 0 h (vecOf W.length u) W := by
    intro u hu
    rw [T.sem_y0 h W _ (by simp [vecOf]), T.deriv_sum_ratCast, sumQ]
    have e : ∀ i ∈ Finset.range W.length,
        (((vecOf W.length u).getD i 0 : ℚ) : T.F 0) *
          ((T.MP 0 h).sem (ratPart (ratInt (W.getD i (zc ηs 0)))))′ =
        (((vecOf W.length u).getD i 0 : ℚ) : T.F 0) * (T.MP 0 h).sem (W.getD i (zc ηs 0)) -
          ((u.getD i 0 : ℚ) : T.F 0) * (T.MP 0 h).sem (logPart (W.getD i (zc ηs 0))) := by
      intro i hi
      rw [T.sem0_split h (W.getD i (zc ηs 0)), getD_vecOf, if_pos (Finset.mem_range.mp hi)]
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, hrel u hu, sub_zero]
  have hsound : T.PLSound 0 h W (paramLim ηs 0 W) := fun r hr ↦ by
    rw [hout] at hr
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
    exact hder u hu
  refine ⟨hsound, fun c hc z hz ↦ ?_⟩
  -- completeness
  letI : Differential Kc[X] := polynomialOfDeriv 1
  haveI : DifferentialAlgebra Kc[X] (T.F 0) := ⟨T.deriv_phi0⟩
  have hD : ∀ P : Kc[X], P′ = derivative P := implicitDeriv_one_of_trivial T.hC
  have hnorm : ∀ p : Kc[X], Irreducible p → ¬p ∣ p′ := fun p hp ↦ by
    rw [hD]; exact Differential.not_dvd_derivative_self hp
  have hL : ∀ i, (T.MP 0 h).sem (logPart (W.getD i (zc ηs 0))) =
      algebraMap Kc[X] (T.F 0) ((CPoly.toPoly (ratInt (W.getD i (zc ηs 0))).r).map
        (algebraMap ℚ Kc)) / algebraMap Kc[X] (T.F 0)
        ((CPoly.toPoly (ratInt (W.getD i (zc ηs 0))).s).map (algebraMap ℚ Kc)) := fun i ↦
    T.model0_sem_eq _
  set l := (List.range W.length).map fun i ↦
    (C (c.getD i 0) * (CPoly.toPoly (ratInt (W.getD i (zc ηs 0))).r).map (algebraMap ℚ Kc),
      (CPoly.toPoly (ratInt (W.getD i (zc ηs 0))).s).map (algebraMap ℚ Kc)) with hl
  set Z := z - ∑ i ∈ Finset.range W.length, algebraMap Kc (T.F 0) (c.getD i 0) *
    (T.MP 0 h).sem (ratPart (ratInt (W.getD i (zc ηs 0)))) with hZ
  have hlsum : (l.map fun p ↦ algebraMap Kc[X] (T.F 0) p.1 / algebraMap Kc[X] (T.F 0) p.2).sum =
      ∑ i ∈ Finset.range W.length, algebraMap Kc (T.F 0) (c.getD i 0) *
        (T.MP 0 h).sem (logPart (W.getD i (zc ηs 0))) := by
    rw [hl, List.map_map, list_sum_map_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Function.comp_apply]
    rw [hL, map_mul, show algebraMap Kc[X] (T.F 0) (C (c.getD i 0)) =
      algebraMap Kc (T.F 0) (c.getD i 0) from T.phi0_C _]
    ring
  have hZd : Z′ = algebraMap Kc[X] (T.F 0) 0 +
      (l.map fun p ↦ algebraMap Kc[X] (T.F 0) p.1 / algebraMap Kc[X] (T.F 0) p.2).sum := by
    rw [hlsum, map_zero, zero_add, hZ, map_sub, hz, T.deriv_sum_Kc, sumK,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [T.sem0_split h (W.getD i (zc ηs 0))]
    ring
  obtain ⟨hsum0, -⟩ := Differential.deriv_eq_poly_add_sum_proper (K := T.F 0) hnorm 0 l
    (fun p hp ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      exact (T.ratInt_spec _).2.1)
    (fun p hp ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      exact lt_of_le_of_lt (by rw [← smul_eq_C_mul]; exact degree_smul_le _ _)
        (T.ratInt_spec _).2.2)
    Z hZd
  rw [hlsum] at hsum0
  -- the constant system
  have h0 : (List.zipWith (fun c v ↦ algebraMap Kc (T.F 0) c * (T.MP 0 h).sem v)
      ((List.range W.length).map fun i ↦ c.getD i 0) (W.map logPart)).sum = 0 := by
    rw [zipWith_sum_range _ 0 (zc ηs 0) _ _ (by simp), ← hsum0]
    simp only [List.length_map, List.length_range]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i < W.length := Finset.mem_range.mp hi
    rw [getD_range_map (fun j ↦ c.getD j 0) 0 hi', getD_map' logPart W (zc ηs 0) (zc ηs 0) hi']
  obtain ⟨β, hβl, hβ⟩ := T.consys_complete 0 h (W.map logPart) _ (by simp) h0
  have hlen : (paramLim ηs 0 W).length = (consys ηs 0 (W.map logPart)).length := by
    rw [hout, List.length_map]
  have hgetD : ∀ k < (consys ηs 0 (W.map logPart)).length,
      (paramLim ηs 0 W).getD k ([], zc ηs 0) =
        (vecOf W.length ((consys ηs 0 (W.map logPart)).getD k []),
          lcombCode (opsQ ηs 0) (cstN 0) (vecOf W.length ((consys ηs 0 (W.map logPart)).getD k []))
            (W.map fun w ↦ ratPart (ratInt w))) := fun k hk ↦ by
    rw [hout, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
      List.getD_eq_getElem _ _ hk]
  have hcoef : ∀ i, c.getD i 0 = ∑ k ∈ Finset.range (paramLim ηs 0 W).length,
      β.getD k 0 * algebraMap ℚ Kc (((paramLim ηs 0 W).getD k ([], zc ηs 0)).1.getD i 0) := by
    intro i
    rw [hlen]
    by_cases hi : i < W.length
    · have := hβ i
      rw [getD_range_map (fun j ↦ c.getD j 0) 0 hi,
        zipWith_sum_range _ 0 [] _ _ hβl, hβl] at this
      rw [this]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [hgetD k (Finset.mem_range.mp hk), getD_vecOf, if_pos hi]
    · rw [hc i (by omega)]
      symm
      refine Finset.sum_eq_zero fun k hk ↦ ?_
      rw [hgetD k (Finset.mem_range.mp hk), getD_vecOf, if_neg hi, map_zero, mul_zero]
  refine ⟨β, hcoef, ?_⟩
  rw [map_sub, hz, T.deriv_sum_Kc, sub_eq_zero]
  have e1 : ∀ k ∈ Finset.range (paramLim ηs 0 W).length,
      algebraMap Kc (T.F 0) (β.getD k 0) *
        ((T.MP 0 h).sem ((paramLim ηs 0 W).getD k ([], zc ηs 0)).2)′ =
      ∑ i ∈ Finset.range W.length, algebraMap Kc (T.F 0) (β.getD k 0 *
        algebraMap ℚ Kc (((paramLim ηs 0 W).getD k ([], zc ηs 0)).1.getD i 0)) *
          (T.MP 0 h).sem (W.getD i (zc ηs 0)) := by
    intro k hk
    have hmem : (paramLim ηs 0 W).getD k ([], zc ηs 0) ∈ paramLim ηs 0 W := by
      rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]; exact List.getElem_mem _
    rw [hsound _ hmem, sumQ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, T.algebraMap_ratCast]
    ring
  rw [Finset.sum_congr rfl e1, Finset.sum_comm, sumK]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_mul, ← map_sum, ← hcoef i]

end NestTower

end Tower.NestP
