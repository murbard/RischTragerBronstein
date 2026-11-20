import RischTragerBronstein.Computable.NestMLim
import RischTragerBronstein.Computable.NestPElem
import RischTragerBronstein.Computable.NestPDecide

/-!
# Parametric elementary integration at exponential levels

At `t = exp a` a combination `∑ cᵢ wᵢ = G′ + N / S + P / tˢ` has an elementary integral iff the
residue test passes for `N / S` (a constant system at level `m + 1`) and every Laurent coefficient
of `P / tˢ` is admissible: `Pⱼ` for `j ≠ S` is `y′ + (j - S) a′ y` for some `y` (a Risch equation
one level down), and `P_S` has an elementary integral one level down. The admissible combinations
are computed coefficient by coefficient (`elemLoop`): each admissible set is a linear subspace.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP CPoly

/-! ### The coefficient loop, generically -/

section ElemLoop

variable {α : Type} {K Cs : Type*} [Field K] [Differential K] [CharZero K] [Field Cs] [CharZero Cs]
variable (ι : Cs →+* K) {O : COps α} (M : CField α K O) (cst : ℚ → α)
variable (Pu : List (GPoly α))

/-- The coefficient `i` of `∑ βᵤ Pᵤ`, rational coefficients. -/
noncomputable def cvalQ (i : ℕ) (β : List ℚ) : K :=
  ∑ u ∈ Finset.range Pu.length, ((β.getD u 0 : ℚ) : K) * (GPoly.toPoly M (Pu.getD u [])).coeff i

/-- The coefficient `i` of `∑ cᵤ Pᵤ`, constant coefficients. -/
noncomputable def cvalC (i : ℕ) (c : List Cs) : K :=
  ∑ u ∈ Finset.range Pu.length, ι (c.getD u 0) * (GPoly.toPoly M (Pu.getD u [])).coeff i

variable (O) in
/-- The codes of the coefficient `i` of the vectors of a basis. -/
def coefCodes (i : ℕ) (Bs : List (List ℚ)) : List α :=
  Bs.map fun β ↦ lcombCode O cst β (Pu.map fun L ↦ L.getD i O.zero)

/-- The specification of a coefficient solver with admissibility predicates `Adm` (rational
combinations) and `AdmC` (constant combinations). -/
structure ElemSolSpec (Adm AdmC : K → Prop) (sol : List α → List (List ℚ)) : Prop where
  sound : ∀ ws, ∀ β ∈ sol ws, Adm (sQ M β ws)
  complete : ∀ ws (c : List Cs), (∀ i, ws.length ≤ i → c.getD i 0 = 0) → AdmC (sC ι M c ws) →
    ∃ γ : List Cs, ∀ k, c.getD k 0 = ∑ l ∈ Finset.range (sol ws).length,
      γ.getD l 0 * algebraMap ℚ Cs (((sol ws).getD l []).getD k 0)

lemma sem_getD (p : GPoly α) (i : ℕ) : M.sem (p.getD i O.zero) = (p.map M.sem).getD i 0 := by
  by_cases hi : i < p.length
  · rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega), M.sem_zero]

/-- Stage `j` of the loop, soundness: every basis vector is admissible at the coefficients `≥ j`. -/
def ESound (Adm : ℕ → K → Prop) (j : ℕ) (Bs : List (List ℚ)) : Prop :=
  ∀ β ∈ Bs, ∀ i, j ≤ i → Adm i (cvalQ M Pu i β)

/-- Stage `j` of the loop, completeness. -/
def EComplete (AdmC : ℕ → K → Prop) (n j : ℕ) (Bs : List (List ℚ)) : Prop :=
  ∀ c : List Cs, (∀ u, n ≤ u → c.getD u 0 = 0) → (∀ i, j ≤ i → AdmC i (cvalC ι M Pu i c)) →
    ∃ γ : List Cs, ∀ u, c.getD u 0 = ∑ k ∈ Finset.range Bs.length,
      γ.getD k 0 * algebraMap ℚ Cs ((Bs.getD k []).getD u 0)

variable {M cst}
variable (hcst : ∀ q, M.sem (cst q) = (q : K))

include hcst in
lemma sem_coefCode (i : ℕ) (β : List ℚ) :
    M.sem (lcombCode O cst β (Pu.map fun L ↦ L.getD i O.zero)) = cvalQ M Pu i β := by
  rw [sem_lcombCode M cst hcst, zipWith_sum_getD (fun (q : ℚ) a ↦ (q : K) * M.sem a) 0 O.zero
    (by simp), List.length_map, cvalQ]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  rw [NestTower.getD_map' _ Pu [] O.zero (Finset.mem_range.mp hu), GPoly.coeff_toPoly, sem_getD]

include hcst in
lemma sQ_coefCodes (i : ℕ) (Bs : List (List ℚ)) (β : List ℚ) :
    sQ M β (coefCodes O cst Pu i Bs) =
      ∑ k ∈ Finset.range Bs.length, ((β.getD k 0 : ℚ) : K) * cvalQ M Pu i (Bs.getD k []) := by
  rw [sQ, coefCodes, List.length_map]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [NestTower.getD_map' _ Bs [] O.zero (Finset.mem_range.mp hk), sem_coefCode Pu hcst]

include hcst in
lemma sC_coefCodes (i : ℕ) (Bs : List (List ℚ)) (γ : List Cs) :
    sC ι M γ (coefCodes O cst Pu i Bs) =
      ∑ k ∈ Finset.range Bs.length, ι (γ.getD k 0) * cvalQ M Pu i (Bs.getD k []) := by
  rw [sC, coefCodes, List.length_map]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [NestTower.getD_map' _ Bs [] O.zero (Finset.mem_range.mp hk), sem_coefCode Pu hcst]

lemma cvalQ_vcomb (n : ℕ) (hn : Pu.length = n) (i : ℕ) (β : List ℚ) (Bs : List (List ℚ)) :
    cvalQ M Pu i (vcomb n β Bs) =
      ∑ k ∈ Finset.range Bs.length, ((β.getD k 0 : ℚ) : K) * cvalQ M Pu i (Bs.getD k []) := by
  simp only [cvalQ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  rw [getD_vcomb, if_pos (by rw [← hn]; exact Finset.mem_range.mp hu)]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ ↦ by ring

lemma cvalC_comb (n : ℕ) (hn : Pu.length = n) (i : ℕ) (c γ : List Cs) (Bs : List (List ℚ))
    (hc : ∀ u < n, c.getD u 0 = ∑ k ∈ Finset.range Bs.length,
      γ.getD k 0 * algebraMap ℚ Cs ((Bs.getD k []).getD u 0))
    (hιq : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K)) :
    cvalC ι M Pu i c = ∑ k ∈ Finset.range Bs.length, ι (γ.getD k 0) * cvalQ M Pu i (Bs.getD k []) := by
  simp only [cvalC, cvalQ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  rw [hc u (by rw [← hn]; exact Finset.mem_range.mp hu), map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_mul, hιq]
  ring

variable (Adm AdmC : ℕ → K → Prop) (sol : ℕ → List α → List (List ℚ))
  (hspec : ∀ i, ElemSolSpec ι M (Adm i) (AdmC i) (sol i))
  (hlin : ∀ i (s : Finset ℕ) (q : ℕ → ℚ) (v : ℕ → K), (∀ k ∈ s, Adm i (v k)) →
    Adm i (∑ k ∈ s, ((q k : ℚ) : K) * v k))
  (hιq : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K))

include hcst hspec hlin hιq in
/-- **The coefficient loop is sound and complete.** -/
theorem elemLoop_stage (n : ℕ) (hn : Pu.length = n) :
    ∀ (j : ℕ) (Bs : List (List ℚ)), ESound M Pu Adm j Bs → EComplete ι M Pu AdmC n j Bs →
      ESound M Pu Adm 0 (elemLoop n (fun i Bs ↦ sol i (coefCodes O cst Pu i Bs)) j Bs) ∧
        EComplete ι M Pu AdmC n 0 (elemLoop n (fun i Bs ↦ sol i (coefCodes O cst Pu i Bs)) j Bs)
  | 0, Bs, hs, hc => ⟨hs, hc⟩
  | j + 1, Bs, hs, hc => by
    refine elemLoop_stage n hn j _ ?_ ?_
    · -- soundness of the step
      intro β' hβ' i hi
      obtain ⟨β, hβ, rfl⟩ := List.mem_map.mp hβ'
      rw [cvalQ_vcomb Pu n hn]
      rcases Nat.lt_or_ge j i with hlt | hle
      · refine hlin i _ _ _ fun k hk ↦ hs _ ?_ i (by omega)
        rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]; exact List.getElem_mem _
      · obtain rfl : i = j := le_antisymm hle hi
        have := (hspec i).sound _ β hβ
        rwa [sQ_coefCodes Pu hcst] at this
    · -- completeness of the step
      intro c hcn hadm
      obtain ⟨γ, hγ⟩ := hc c hcn fun i hi ↦ hadm i (by omega)
      set γt := (List.range Bs.length).map fun k ↦ γ.getD k 0 with hγt
      have hγtD : ∀ k < Bs.length, γt.getD k 0 = γ.getD k 0 := fun k hk ↦
        NestTower.getD_range_map _ _ hk
      have hval : cvalC ι M Pu j c = sC ι M γt (coefCodes O cst Pu j Bs) := by
        rw [sC_coefCodes ι Pu hcst, cvalC_comb ι Pu n hn j c γ Bs (fun u _ ↦ hγ u) hιq]
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        rw [hγtD k (Finset.mem_range.mp hk)]
      obtain ⟨γ', hγ'⟩ := (hspec j).complete _ γt (fun i hi ↦ List.getD_eq_default _ _ (by
        simp only [coefCodes, List.length_map] at hi; simpa [hγt] using hi))
        (hval ▸ hadm j le_rfl)
      refine ⟨γ', fun u ↦ ?_⟩
      rw [List.length_map]
      by_cases hu : u < n
      · have := recombine n Bs.length (sol j (coefCodes O cst Pu j Bs)).length
          (fun k u ↦ (Bs.getD k []).getD u 0)
          (fun l k ↦ ((sol j (coefCodes O cst Pu j Bs)).getD l []).getD k 0)
          (fun u ↦ c.getD u 0) (fun k ↦ γt.getD k 0) (fun l ↦ γ'.getD l 0)
          (fun u _ ↦ by
            rw [hγ u]
            refine Finset.sum_congr rfl fun k hk ↦ ?_
            rw [hγtD k (Finset.mem_range.mp hk)])
          (fun k hk ↦ by
            have := hγ' k
            simp only [coefCodes, List.length_map] at this ⊢
            exact this) u hu
        rw [this]
        refine Finset.sum_congr rfl fun l hl ↦ ?_
        rw [NestTower.getD_map' _ _ [] [] (Finset.mem_range.mp hl), getD_vcomb, if_pos hu]
      · rw [hcn u (by omega)]
        symm
        refine Finset.sum_eq_zero fun l hl ↦ ?_
        rw [NestTower.getD_map' _ _ [] [] (Finset.mem_range.mp hl), getD_vcomb, if_neg hu,
          map_zero, mul_zero]

omit [Differential K] [CharZero K] in
/-- The unit vectors span everything. -/
lemma unit_span (n : ℕ) (c : List Cs) (hc : ∀ u, n ≤ u → c.getD u 0 = 0) (u : ℕ) :
    c.getD u 0 = ∑ k ∈ Finset.range ((List.range n).map (unitV n)).length,
      ((List.range n).map fun i ↦ c.getD i 0).getD k 0 *
        algebraMap ℚ Cs ((((List.range n).map (unitV n)).getD k []).getD u 0) := by
  simp only [List.length_map, List.length_range]
  have e : ∀ k ∈ Finset.range n, ((List.range n).map fun i ↦ c.getD i 0).getD k 0 *
      algebraMap ℚ Cs ((((List.range n).map (unitV n)).getD k []).getD u 0) =
      if u = k then (if u < n then c.getD u 0 else 0) else 0 := fun k hk ↦ by
    have hk' := Finset.mem_range.mp hk
    rw [NestTower.getD_range_map _ _ hk', NestTower.getD_range_map _ _ hk', getD_unitV]
    by_cases huk : u = k
    · subst huk; simp [hk']
    · simp [huk]
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq]
  by_cases hu : u < n
  · simp [hu]
  · simp only [Finset.mem_range, hu, if_false]
    exact hc u (by omega)

lemma cvalQ_eq_zero (top : ℕ) (htop : ∀ u < Pu.length, (Pu.getD u []).length ≤ top) (i : ℕ)
    (hi : top ≤ i) (β : List ℚ) : cvalQ M Pu i β = 0 := by
  refine Finset.sum_eq_zero fun u hu ↦ ?_
  rw [GPoly.coeff_toPoly, List.getD_eq_default ((Pu.getD u []).map M.sem) 0 (by
    rw [List.length_map]; exact (htop u (Finset.mem_range.mp hu)).trans hi), mul_zero]

end ElemLoop

/-! ### The data of the exponential step -/

section ExpData

variable (as : (m : ℕ) → Code (m + 1)) (m : ℕ)

/-- The derivation polynomial `[0, a′]`. -/
abbrev wkM : GPoly (Code (m + 1)) := [(opsM (expK as) m).zero, (opsM (expK as) m).deriv (as m)]

/-- The common squarefree denominator of the simple parts. -/
def lcmSM (W : List (Code (m + 2))) : GPoly (Code (m + 1)) :=
  lcmList (opsM (expK as) m) ((W.map (eSp as m)).map ExpSplit.s)

/-- The numerators of the simple parts over `lcmSM`. -/
def numLM (W : List (Code (m + 2))) : List (GPoly (Code (m + 1))) :=
  (W.map (eSp as m)).map fun e ↦ GPoly.mul (opsM (expK as) m) e.r
    (GPoly.divMod (opsM (expK as) m) (lcmSM as m W) e.s).1

/-- The reduced residue test polynomial of `Nᵢ / S`. -/
def ttCodeM (W : List (Code (m + 2))) (Ni : GPoly (Code (m + 1))) : GPoly (Code (m + 1)) :=
  (GPoly.divMod (opsM (expK as) m) (residueTestCode (opsM (expK as) m)
    (GPoly.residuePoly (opsM (expK as) m) (wkM as m) Ni (lcmSM as m W)) (lcmSM as m W))
    (lcmSM as m W)).2

/-- The residue test polynomials as codes of level `m + 1`. -/
def resCodesM (W : List (Code (m + 2))) : List (Code (m + 2)) :=
  ((numLM as m W).map (ttCodeM as m W)).map fun T ↦ ((T, [(opsM (expK as) m).one]) : Code (m + 2))

/-- The basis of the residue condition. -/
def E1M (W : List (Code (m + 2))) : List (List ℚ) :=
  (consys (expK as) (m + 1) (resCodesM as m W)).map fun u ↦
    (List.range W.length).map fun i ↦ u.getD i 0

/-- The check on the common denominator. -/
def lcmCheckM (W : List (Code (m + 2))) : Bool :=
  GPoly.squarefreeCheck (opsM (expK as) m) (lcmSM as m W) &&
    (W.map (eSp as m)).all
      (fun e ↦ GPoly.isZero (opsM (expK as) m) (GPoly.divMod (opsM (expK as) m) (lcmSM as m W) e.s).2)

/-- The common order at `t = 0` of the Laurent parts. -/
def SM (W : List (Code (m + 2))) : ℕ := laurentS (W.map (eSp as m))

/-- The Laurent parts of the basis of the residue condition. -/
def PuM (W : List (Code (m + 2))) : List (GPoly (Code (m + 1))) :=
  (E1M as m W).map fun e ↦ lcombGP (opsM (expK as) m) (cstN m) e
    ((W.map (eSp as m)).map (shiftedL (opsM (expK as) m) (SM as m W)))

/-- The coefficient solvers. -/
def solM (elem : List (Code (m + 1)) → List (List ℚ)) (W : List (Code (m + 2))) :
    ℕ → List (Code (m + 1)) → List (List ℚ) := fun i ws ↦
  if i = SM as m W then elem ws
  else (prde (expK as) m ((opsM (expK as) m).mul (cstN m ((i : ℚ) - SM as m W)) (as m)) ws).map
    Prod.fst

/-- The top degree of the Laurent parts. -/
def topM (W : List (Code (m + 2))) : ℕ := ((PuM as m W).map List.length).foldr max 0

lemma expElemStep_eq (elem : List (Code (m + 1)) → List (List ℚ)) (W : List (Code (m + 2))) :
    expElemStep (expK as) m (as m) elem W =
      if lcmCheckM as m W then
        (elemLoop (E1M as m W).length
          (fun i Bs ↦ solM as m elem W i (coefCodes (opsM (expK as) m) (cstN m) (PuM as m W) i Bs))
          (topM as m W) ((List.range (E1M as m W).length).map (unitV (E1M as m W).length))).map
          fun δ ↦ vcomb W.length δ (E1M as m W)
      else [] := rfl

end ExpData

/-! ### Common multiples divide products -/

section LcmProd

variable {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

lemma lcmG_dvd_mul (a b : GPoly α) (hb : GPoly.toPoly M b ≠ 0) :
    GPoly.toPoly M (lcmG O a b) ∣ GPoly.toPoly M a * GPoly.toPoly M b := by
  obtain ⟨-, hgb⟩ := GPoly.egcd_dvd M a b
  have hg0 : GPoly.toPoly M (GPoly.egcd O a b).1 ≠ 0 := fun h0 ↦ hb (zero_dvd_iff.mp (h0 ▸ hgb))
  have hbq := GPoly.div_mul_of_dvd M b _ hg0 hgb
  rw [lcmG, GPoly.toPoly_mul]
  exact mul_dvd_mul_left _ ⟨_, hbq⟩

lemma lcmList_dvd_prod : ∀ l : List (GPoly α), (∀ p ∈ l, GPoly.toPoly M p ≠ 0) →
    GPoly.toPoly M (lcmList O l) ∣ (l.map (GPoly.toPoly M)).prod
  | [], _ => by simp [lcmList, M.sem_one]
  | p :: l, h0 => by
    have ih := lcmList_dvd_prod l fun q hq ↦ h0 q (List.mem_cons_of_mem _ hq)
    have hne := (GPolyLcm.lcmList_spec M l fun q hq ↦ h0 q (List.mem_cons_of_mem _ hq)).2.1
    rw [List.map_cons, List.prod_cons]
    exact (lcmG_dvd_mul M p (lcmList O l) hne).trans (mul_dvd_mul_left _ ih)

end LcmProd

namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {as : (m : ℕ) → Code (m + 1)}
variable (T : NestMTower Kc E (expK as))

section Data

variable (m : ℕ) (h : T.Tr (m + 1))

/-- **The common denominator**: squarefree, prime to `t`, and every weight is
`gᵢ′ + Nᵢ / S + Lᵢ / tˢ` with `deg Nᵢ < deg S`. -/
lemma lcm_dataM (W : List (Code (m + 2))) (hchk : lcmCheckM as m W = true) :
    Squarefree (GPoly.toPoly (T.Mm m h) (lcmSM as m W)) ∧
    ¬X ∣ GPoly.toPoly (T.Mm m h) (lcmSM as m W) ∧
    ∀ i < W.length, (T.MP (m + 1) h).sem (W.getD i (opsM (expK as) (m + 1)).zero) =
      ((T.M1 m h).sem ((eSp as m (W.getD i (opsM (expK as) (m + 1)).zero)).gn,
        (eSp as m (W.getD i (opsM (expK as) (m + 1)).zero)).gd))′ +
      T.phi m (GPoly.toPoly (T.Mm m h) ((numLM as m W).getD i [])) /
        T.phi m (GPoly.toPoly (T.Mm m h) (lcmSM as m W)) +
      T.σ1 m h (shiftedL (opsM (expK as) m) (SM as m W)
        (eSp as m (W.getD i (opsM (expK as) (m + 1)).zero))) / T.phi m (X ^ SM as m W) ∧
      (GPoly.toPoly (T.Mm m h) ((numLM as m W).getD i [])).degree <
        (GPoly.toPoly (T.Mm m h) (lcmSM as m W)).degree := by
  have hinj := T.phi_injective' m h
  simp only [lcmCheckM, Bool.and_eq_true] at hchk
  obtain ⟨hsqc, hall⟩ := hchk
  have hsq : Squarefree (GPoly.toPoly (T.Mm m h) (lcmSM as m W)) :=
    GPoly.squarefreeCheck_sound (T.Mm m h) hsqc
  have hs : ∀ p ∈ (W.map (eSp as m)).map ExpSplit.s, GPoly.toPoly (T.Mm m h) p ≠ 0 ∧
      ¬X ∣ GPoly.toPoly (T.Mm m h) p := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp he
    exact ⟨(T.exp_weight_decomp m h w).2.1.ne_zero, (T.exp_weight_decomp m h w).2.2.1⟩
  have hX : ¬X ∣ GPoly.toPoly (T.Mm m h) (lcmSM as m W) := by
    intro hXd
    have := hXd.trans (lcmList_dvd_prod (T.Mm m h) _ fun p hp ↦ (hs p hp).1)
    obtain ⟨q, hq, hXq⟩ := (Prime.dvd_prod_iff prime_X).mp this
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact (hs p hp).2 hXq
  refine ⟨hsq, hX, fun i hi ↦ ?_⟩
  obtain ⟨w, hw⟩ : ∃ w, w = W.getD i (opsM (expK as) (m + 1)).zero := ⟨_, rfl⟩
  rw [← hw]
  have hwm : w ∈ W := by rw [hw, List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  have hS : ∀ e ∈ W.map (eSp as m), e.k ≤ SM as m W := fun e he ↦ k_le_laurentS m _ e he
  have hval := T.sem_weight m h W (SM as m W) hS i hi
  rw [← hw] at hval
  obtain ⟨-, hsqs, -, hdeg⟩ := T.exp_weight_decomp m h w
  have hz := List.all_eq_true.mp hall (eSp as m w) (List.mem_map.mpr ⟨w, hwm, rfl⟩)
  have hr0 := (GPoly.isZero_iff (T.Mm m h) _).mp hz
  have hdm := GPoly.divMod_spec (T.Mm m h) (lcmSM as m W) (eSp as m w).s
  rw [hr0, add_zero] at hdm
  set d := GPoly.toPoly (T.Mm m h) (GPoly.divMod (opsM (expK as) m) (lcmSM as m W) (eSp as m w).s).1
    with hd
  have hd0 : d ≠ 0 := fun h0 ↦ hsq.ne_zero (by rw [hdm, h0, zero_mul])
  have hN : GPoly.toPoly (T.Mm m h) ((numLM as m W).getD i []) =
      GPoly.toPoly (T.Mm m h) (eSp as m w).r * d := by
    rw [numLM, NestTower.getD_map_map (eSp as m) _ W (opsM (expK as) (m + 1)).zero [] hi, ← hw,
      GPoly.toPoly_mul]
  refine ⟨?_, ?_⟩
  · have hφd : T.phi m d ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd0
    have hφs : T.phi m (GPoly.toPoly (T.Mm m h) (eSp as m w).s) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr hsqs.ne_zero
    have hmid : T.σ1 m h (eSp as m w).r / T.σ1 m h (eSp as m w).s =
        T.phi m (GPoly.toPoly (T.Mm m h) (eSp as m w).r * d) /
          T.phi m (GPoly.toPoly (T.Mm m h) (lcmSM as m W)) := by
      simp only [σ1]
      rw [hdm, map_mul, map_mul]
      field_simp
    rw [hval, hN, hmid]
  · rw [hN, hdm, degree_mul, degree_mul, add_comm]
    exact WithBot.add_lt_add_left (degree_ne_bot.mpr hd0) hdeg

/-- **The residue data**: the residue polynomial of `Nᵢ / S` and its reduced test polynomial. -/
lemma res_dataM (W : List (Code (m + 2)))
    (hS : Squarefree (GPoly.toPoly (T.Mm m h) (lcmSM as m W)))
    (hX : ¬X ∣ GPoly.toPoly (T.Mm m h) (lcmSM as m W)) (Ni : GPoly (Code (m + 1))) :
    GPoly.toPoly (T.Mm m h) (lcmSM as m W) ∣
      GPoly.toPoly (T.Mm m h) (GPoly.residuePoly (opsM (expK as) m) (wkM as m) Ni (lcmSM as m W)) *
        (mapCoeffs (GPoly.toPoly (T.Mm m h) (lcmSM as m W)) +
          C (T.bE m h) * X * derivative (GPoly.toPoly (T.Mm m h) (lcmSM as m W))) -
        GPoly.toPoly (T.Mm m h) Ni ∧
    GPoly.toPoly (T.Mm m h) (lcmSM as m W) ∣
      residueTest (GPoly.toPoly (T.Mm m h)
        (GPoly.residuePoly (opsM (expK as) m) (wkM as m) Ni (lcmSM as m W)))
        (GPoly.toPoly (T.Mm m h) (lcmSM as m W)) -
        GPoly.toPoly (T.Mm m h) (ttCodeM as m W Ni) ∧
    (GPoly.toPoly (T.Mm m h) (ttCodeM as m W Ni)).degree <
      (GPoly.toPoly (T.Mm m h) (lcmSM as m W)).degree := by
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hwk : GPoly.toPoly (T.Mm m h) (wkM as m) = C (T.bE m h) * X := T.toPoly_peW m h
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly (T.Mm m h) (wkM as m))
      (GPoly.toPoly (T.Mm m h) (lcmSM as m W))) (GPoly.toPoly (T.Mm m h) (lcmSM as m W)) := by
    rw [hwk, ← T.wPoly_eq_bE m h]
    let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
    exact isCoprime_deriv_of_squarefree hS (fun p hp hpS ↦
      T.normal_exp m htr rfl p hp (fun hXp ↦ hX (hXp.trans hpS)))
  have hrs := GPoly.residuePoly_spec (T.Mm m h) (wkM as m) Ni _ hS.ne_zero hcop
  have himp : implicitDeriv (GPoly.toPoly (T.Mm m h) (wkM as m)) (GPoly.toPoly (T.Mm m h) (lcmSM as m W)) =
      mapCoeffs (GPoly.toPoly (T.Mm m h) (lcmSM as m W)) +
        C (T.bE m h) * X * derivative (GPoly.toPoly (T.Mm m h) (lcmSM as m W)) := by
    rw [hwk]; simp [implicitDeriv]
  rw [himp] at hrs
  refine ⟨hrs, ?_, GPoly.divMod_degree_lt (T.Mm m h) _ _ hS.ne_zero⟩
  have hdm := GPoly.divMod_spec (T.Mm m h) (residueTestCode (opsM (expK as) m)
    (GPoly.residuePoly (opsM (expK as) m) (wkM as m) Ni (lcmSM as m W)) (lcmSM as m W))
    (lcmSM as m W)
  rw [NestTower.toPoly_residueTestCode] at hdm
  rw [ttCodeM, hdm]
  exact ⟨_, by ring⟩

lemma length_resCodesM (W : List (Code (m + 2))) : (resCodesM as m W).length = W.length := by
  unfold resCodesM numLM
  exact (List.length_map _).trans ((List.length_map _).trans ((List.length_map _).trans
    (List.length_map _)))

lemma getD_resCodesM (W : List (Code (m + 2))) {i : ℕ} (hi : i < W.length) :
    (resCodesM as m W).getD i (opsM (expK as) (m + 1)).zero =
      ((ttCodeM as m W ((numLM as m W).getD i []), [(opsM (expK as) m).one]) : Code (m + 2)) :=
  NestTower.getD_map_map _ _ _ [] _ (by unfold numLM; simpa using hi)

/-- The relation given by a basis vector of the residue system. -/
lemma rel_resM (W : List (Code (m + 2))) (u : CPoly ℚ)
    (hu : u ∈ consys (expK as) (m + 1) (resCodesM as m W)) :
    ∑ i ∈ Finset.range W.length, C ((u.getD i 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.Mm m h) (ttCodeM as m W ((numLM as m W).getD i [])) = 0 := by
  have := T.consys_sound (m + 1) h (resCodesM as m W) u hu
  rw [NestTower.zipWith_sum_range _ 0 (opsM (expK as) (m + 1)).zero _ _ (by simp)] at this
  apply T.phi_injective' m h
  rw [map_zero, ← this, map_sum]
  refine Finset.sum_congr (by rw [List.length_map, List.length_range, length_resCodesM]) fun i hi ↦ ?_
  have hi' : i < W.length := by
    have := Finset.mem_range.mp hi
    rwa [List.length_map, List.length_range, length_resCodesM] at this
  rw [NestTower.getD_range_map (fun j ↦ algebraMap ℚ Kc (u.getD j 0)) 0
    (by rw [length_resCodesM]; exact hi'), T.algebraMap_ratCastM, getD_resCodesM m W hi',
    map_mul, T.phi_C_ratCastM]
  congr 1
  change _ = T.σ1 m h _ / T.σ1 m h [(opsM (expK as) m).one]
  rw [T.σ1_one, div_one]

lemma length_E1M (W : List (Code (m + 2))) :
    (E1M as m W).length = (consys (expK as) (m + 1) (resCodesM as m W)).length := by
  simp [E1M]

/-- The test polynomials, recombined, vanish. -/
lemma sum_Tv_eq_zeroM (W : List (Code (m + 2))) (δ : List ℚ) :
    ∑ i ∈ Finset.range W.length, C (((vcomb W.length δ (E1M as m W)).getD i 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.Mm m h) (ttCodeM as m W ((numLM as m W).getD i [])) = 0 := by
  set U := consys (expK as) (m + 1) (resCodesM as m W) with hU
  have e : ∀ i ∈ Finset.range W.length,
      C (((vcomb W.length δ (E1M as m W)).getD i 0 : ℚ) : T.F m) *
        GPoly.toPoly (T.Mm m h) (ttCodeM as m W ((numLM as m W).getD i [])) =
      ∑ k ∈ Finset.range U.length, C ((δ.getD k 0 : ℚ) : T.F m) *
        (C (((U.getD k []).getD i 0 : ℚ) : T.F m) *
          GPoly.toPoly (T.Mm m h) (ttCodeM as m W ((numLM as m W).getD i []))) :=
    fun i hi ↦ by
      have hi' := Finset.mem_range.mp hi
      rw [getD_vcomb, if_pos hi', length_E1M, ← hU]
      push_cast
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [E1M, ← hU, NestTower.getD_map' _ U [] [] (Finset.mem_range.mp hk),
        NestTower.getD_range_map _ _ hi', C_mul]
      ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  rw [← Finset.mul_sum, T.rel_resM m h W _ (NestTower.getD_mem_of_lt U [] (Finset.mem_range.mp hk)), mul_zero]

include T h in
/-- **The lcm check always passes.** -/
lemma lcmCheck_trueM (W : List (Code (m + 2))) : lcmCheckM as m W = true := by
  have hs : ∀ p ∈ (W.map (eSp as m)).map ExpSplit.s,
      GPoly.toPoly (T.Mm m h) p ≠ 0 ∧ Squarefree (GPoly.toPoly (T.Mm m h) p) := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp he
    have := (T.exp_weight_decomp m h w).2.1
    exact ⟨this.ne_zero, this⟩
  obtain ⟨hdvd, -, hsqf⟩ := GPolyLcm.lcmList_spec (T.Mm m h) _ (fun p hp ↦ (hs p hp).1)
  simp only [lcmCheckM, Bool.and_eq_true]
  refine ⟨GPoly.squarefreeCheck_complete (T.Mm m h) (hsqf fun p hp ↦ (hs p hp).2),
    List.all_eq_true.mpr fun e he ↦ ?_⟩
  refine (GPoly.isZero_iff (T.Mm m h) _).mpr (GPoly.divMod_exact (T.Mm m h) _ _ ?_
    (hdvd _ (List.mem_map.mpr ⟨e, he, rfl⟩)))
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp he
  exact (T.exp_weight_decomp m h w).2.1.ne_zero

end Data

section Split

variable (m : ℕ) (h : T.Tr (m + 1))

lemma const_memM (z : E) (hz : z′ = 0) : z ∈ T.F m := by
  obtain ⟨κ, rfl⟩ := T.hCall z hz
  exact (T.F m).algebraMap_mem κ

variable (hc2 : ∀ u ∈ consys (expK as) m ((opsM (expK as) m).deriv (as m) :: dExps as m),
  u.getD 0 0 = 0)

include hc2 in
set_option maxHeartbeats 1600000 in
/-- **The Liouville analysis of an exponential step**: if `G′ + N / S + P / tˢ` (`N / S` a normal
simple part with residue data `R`) has a Liouville form over `F (m + 1)`, then the residue test
passes, every Laurent coefficient `j ≠ S` of `P` is `y′ + (j - S) a′ y`, and `P_S` has a Liouville
form over `F m`. -/
theorem exp_liouville_split (G : T.F (m + 1)) (Nc Sd R P : (T.F m)[X]) (S : ℕ)
    (hsq : Squarefree Sd) (hX : ¬X ∣ Sd) (hdeg : Nc.degree < Sd.degree)
    (hr : Sd ∣ R * (mapCoeffs Sd + C (T.bE m h) * X * derivative Sd) - Nc)
    (hL : LiouvilleIn (T.F (m + 1))
      (((G′ + T.phi m Nc / T.phi m Sd + T.phi m P / T.phi m (X ^ S) : T.F (m + 1))) : E)) :
    Sd ∣ residueTest R Sd ∧
      (∀ j, j ≠ S → ∃ y : T.F m, y′ + (((j : ℤ) - S : ℤ) : T.F m) * T.bE m h * y = P.coeff j) ∧
      LiouvilleIn (T.F m) (((P.coeff S : T.F m)) : E) := by
  classical
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hinj := T.phi_injective' m h
  obtain ⟨ι, s, cc, u, v, hdata, hv, heq⟩ := hL
  set t := T.ts m with ht
  have htd : t′ = algebraMap (T.F m) E (T.bE m h) * t := by
    rw [ht, T.deriv_ts_aeval m, T.wPoly_eq_bE m h, map_mul, aeval_C, aeval_X]
  have hconst : ∀ z ∈ (T.F m)⟮t⟯, z′ = 0 → z ∈ Set.range (algebraMap (T.F m) E) :=
    fun z _ hz0 ↦ by
      obtain ⟨κ, rfl⟩ := T.hCall z hz0
      exact ⟨algebraMap Kc (T.F m) κ, rfl⟩
  -- the constants as elements of `F m`
  set c' : ι → T.F m := fun i ↦ if hc : (cc i)′ = 0 then ⟨cc i, T.const_memM m _ hc⟩ else 0
    with hc'
  have hc'E : ∀ i ∈ s, ((c' i : T.F m) : E) = cc i := fun i hi ↦ by
    simp only [hc']
    rw [dif_pos (hdata i hi).1]
  have hc'd : ∀ i ∈ s, (c' i)′ = 0 := fun i hi ↦
    Subtype.ext (by rw [coe_deriv, hc'E i hi, (hdata i hi).1]; rfl)
  have hvg : v - (G : E) ∈ (T.F m)⟮t⟯ := (T.mem_F_succ).mp (sub_mem hv G.2)
  have hsumc : ∑ i ∈ s, cc i * logDeriv (u i) =
      ∑ i ∈ s, algebraMap (T.F m) E (c' i) * logDeriv (u i) :=
    Finset.sum_congr rfl fun i hi ↦ by rw [← hc'E i hi]; rfl
  have hSd0 : aeval t Sd ≠ 0 := by
    rw [ht, ← T.coe_phi]
    exact fun h0 ↦ hsq.ne_zero (hinj ((Subtype.ext h0).trans (map_zero _).symm))
  have htS : (t : E) ^ S ≠ 0 := by
    have : aeval t (X ^ S : (T.F m)[X]) ≠ 0 := by
      rw [ht, ← T.coe_phi]
      exact fun h0 ↦ (pow_ne_zero S X_ne_zero) (hinj ((Subtype.ext h0).trans (map_zero _).symm))
    simpa using this
  have hval : (((G′ + T.phi m Nc / T.phi m Sd + T.phi m P / T.phi m (X ^ S) : T.F (m + 1))) : E) =
      (G : E)′ + aeval t Nc / aeval t Sd + aeval t P / t ^ S := by
    rw [IntermediateField.coe_add, IntermediateField.coe_add, IntermediateField.coe_div,
      IntermediateField.coe_div, coe_deriv, T.coe_phi, T.coe_phi, T.coe_phi, T.coe_phi, map_pow,
      aeval_X]
  rw [hval] at heq
  -- the residue test
  have hT : Sd ∣ residueTest R Sd := by
    refine residueTest_step_exponential (F := T.F m) t htr (T.bE m h) htd hconst s c' u
      (fun i hi ↦ ⟨(T.mem_F_succ).mp (hdata i hi).2.1, (hdata i hi).2.2⟩) hc'd (v - (G : E)) hvg
      (Nc * X ^ S + P * Sd) Nc Sd R S hsq hX ⟨P, by ring⟩ hr ?_
    rw [← hsumc, map_sub, ← add_sub_assoc, ← heq, map_add, map_mul, map_mul, map_pow, aeval_X]
    field_simp
    ring
  refine ⟨hT, ?_⟩
  -- the Laurent part, in `K = F m (t)`
  have hw := T.deriv_ts_aeval m
  let _ := algebraAdjoinSimple (F := T.F m) t
  let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  let _ : Differential (T.F m)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮t⟯ := isFractionRing_adjoin_simple _ htr
  have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮t⟯ := differentialAlgebra_adjoin_simple _ _ hw
  have hcoe : ∀ Q, ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ Q : (T.F m)⟮t⟯) : E) = aeval t Q :=
    algebraMap_adjoinSimple _
  have hDe : ∀ Q : (T.F m)[X], Q′ = implicitDeriv (C (T.bE m h) * X) Q := fun Q ↦ by
    change implicitDeriv (T.wPoly m) Q = _
    rw [T.wPoly_eq_bE m h]
  have hdK : ∀ y : (T.F m)⟮t⟯, ((y′ : (T.F m)⟮t⟯) : E) = (y : E)′ := fun y ↦ rfl
  have hcoeLog : ∀ y : (T.F m)⟮t⟯, ((logDeriv y : (T.F m)⟮t⟯) : E) = logDeriv (y : E) := by
    intro y
    unfold logDeriv
    rw [IntermediateField.coe_div]
    rfl
  set u'' : ι → (T.F m)⟮t⟯ := fun i ↦ if hu : u i ∈ (T.F m)⟮t⟯ then ⟨u i, hu⟩ else 1 with hu''d
  have hu'' : ∀ i ∈ s, ((u'' i : (T.F m)⟮t⟯) : E) = u i := fun i hi ↦ by
    simp only [hu''d]
    rw [dif_pos ((T.mem_F_succ).mp (hdata i hi).2.1)]
  obtain ⟨e, n, V, kv, he, hPV⟩ := laurent_part_liouville (K := (T.F m)⟮t⟯) hDe s c' u''
    (fun i hi h0 ↦ (hdata i hi).2.2 (by rw [← hu'' i hi, h0]; rfl)) ⟨v - (G : E), hvg⟩ P S
    (algebraMap (T.F m)[X] (T.F m)⟮t⟯ Nc / algebraMap (T.F m)[X] (T.F m)⟮t⟯ Sd)
    ⟨Nc, Sd, hsq.ne_zero, hX, hdeg, rfl⟩ (Subtype.ext (by
      rw [IntermediateField.coe_add, IntermediateField.coe_div, IntermediateField.coe_div, hcoe,
        hcoe, hcoe, hcoe, IntermediateField.coe_add, AddSubmonoidClass.coe_finset_sum, hdK,
        map_pow, aeval_X]
      have h1 : aeval t P / t ^ S + aeval t Nc / aeval t Sd =
          ∑ i ∈ s, algebraMap (T.F m) E (c' i) * logDeriv (u i) + (v - (G : E))′ := by
        rw [← hsumc, map_sub, ← add_sub_assoc, ← heq]
        ring
      rw [h1]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [IntermediateField.coe_mul, hcoe, aeval_C, hcoeLog, hu'' i hi]))
  obtain ⟨hj, hS⟩ := laurent_coeff_eqs (T.bE m h) P V _ kv S hPV
  refine ⟨hj, ?_⟩
  -- `P_S` has a Liouville form over `F m`
  set α := (T.Mm m h).sem (as m) with hα
  have hbα : T.bE m h = α′ := rfl
  set q : T.F m := ∑ i ∈ s, c' i * (n i : T.F m) with hq
  have hqd : q′ = 0 := by
    rw [hq, map_sum]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rw [Derivation.leibniz, hc'd i hi, show ((n i : T.F m))′ = 0 by
      simpa using deriv_ratCastK (K := T.F m) (n i : ℚ)]
    simp
  have e1 : ∑ i ∈ s, c' i * (logDeriv (e i) + (n i : T.F m) * T.bE m h) =
      ∑ i ∈ s, c' i * logDeriv (e i) + q * T.bE m h := by
    rw [hq, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hPS : P.coeff S = ∑ i ∈ s, c' i * logDeriv (e i) + (V.coeff kv + q * α)′ := by
    rw [hS, e1, map_add, Derivation.leibniz, hqd, ← hbα]
    simp only [smul_eq_mul, mul_zero, add_zero]
    ring
  refine ⟨ι, s, cc, fun i ↦ ((e i : T.F m) : E), ((V.coeff kv + q * α : T.F m) : E),
    fun i hi ↦ ⟨(hdata i hi).1, (e i).2, fun h0 ↦ he i hi (Subtype.ext h0)⟩,
    (V.coeff kv + q * α).2, ?_⟩
  rw [hPS, IntermediateField.coe_add, AddSubmonoidClass.coe_finset_sum, coe_deriv]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [IntermediateField.coe_mul, hc'E i hi, T.coe_logDeriv_F]

end Split

section Adm

variable (m : ℕ) (h : T.Tr (m + 1))

/-- Admissibility of the Laurent coefficient `i` (exponent `i - S`), rational combinations. -/
def AdmM (S i : ℕ) (v : T.F m) : Prop :=
  if i = S then HasElementaryIntegralIn (v : E)
  else ∃ y : T.F m, y′ + (((i : ℤ) - S : ℤ) : T.F m) * T.bE m h * y = v

/-- Admissibility of the Laurent coefficient `i`, constant combinations. -/
def AdmCM (S i : ℕ) (v : T.F m) : Prop :=
  if i = S then LiouvilleIn (T.F m) (v : E)
  else ∃ y : T.F m, y′ + (((i : ℤ) - S : ℤ) : T.F m) * T.bE m h * y = v

lemma admM_zero (S i : ℕ) : T.AdmM m h S i 0 := by
  unfold AdmM
  split_ifs
  · have := hasElementaryIntegralIn_deriv (0 : E)
    rwa [Derivation.map_zero] at this
  · exact ⟨0, by simp⟩

/-- Admissibility is a `ℚ`-linear condition. -/
lemma admM_lin (S i : ℕ) (s : Finset ℕ) (q : ℕ → ℚ) (v : ℕ → T.F m)
    (hv : ∀ k ∈ s, T.AdmM m h S i (v k)) : T.AdmM m h S i (∑ k ∈ s, ((q k : ℚ) : T.F m) * v k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using T.admM_zero m h S i
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    have h1 := hv k (Finset.mem_insert_self k s)
    have h2 := ih fun j hj ↦ hv j (Finset.mem_insert_of_mem hj)
    unfold AdmM at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ with hi
    · rw [IntermediateField.coe_add, IntermediateField.coe_mul]
      refine HasElementaryIntegralIn.add (h1.const_mul _ ?_) h2
      rw [NestMTower.coe_ratCast]
      exact T.deriv_ratCast_E _
    · obtain ⟨y1, hy1⟩ := h1
      obtain ⟨y2, hy2⟩ := h2
      refine ⟨((q k : ℚ) : T.F m) * y1 + y2, ?_⟩
      rw [← hy1, ← hy2, map_add, Derivation.leibniz, T.deriv_ratCast]
      simp only [smul_eq_mul, mul_zero, add_zero]
      ring

variable (hc2 : ∀ u ∈ consys (expK as) m ((opsM (expK as) m).deriv (as m) :: dExps as m),
  u.getD 0 0 = 0)

/-- **The coefficient solvers meet their specification.** -/
lemma solM_spec (elem : List (Code (m + 1)) → List (List ℚ))
    (hel : ElemSolSpec (algebraMap Kc (T.F m)) (T.Mm m h) (fun v ↦ HasElementaryIntegralIn (v : E))
      (fun v ↦ LiouvilleIn (T.F m) (v : E)) elem)
    (hprde : ∀ f : Code (m + 1),
      RdeSpecK (algebraMap Kc (T.F m)) (T.Mm m h) ((T.Mm m h).sem f)′ (prde (expK as) m f))
    (W : List (Code (m + 2))) (i : ℕ) :
    ElemSolSpec (algebraMap Kc (T.F m)) (T.Mm m h) (T.AdmM m h (SM as m W) i)
      (T.AdmCM m h (SM as m W) i) (solM as m elem W i) := by
  by_cases hi : i = SM as m W
  · have e1 : solM as m elem W i = elem := funext fun ws ↦ if_pos hi
    have e2 : T.AdmM m h (SM as m W) i = fun v : T.F m ↦ HasElementaryIntegralIn (v : E) :=
      funext fun v ↦ if_pos hi
    have e3 : T.AdmCM m h (SM as m W) i = fun v : T.F m ↦ LiouvilleIn (T.F m) (v : E) :=
      funext fun v ↦ if_pos hi
    rw [e1, e2, e3]
    exact hel
  · set f := (opsM (expK as) m).mul (cstN m ((i : ℚ) - SM as m W)) (as m) with hf
    have hfd : ((T.Mm m h).sem f)′ = (((i : ℤ) - SM as m W : ℤ) : T.F m) * T.bE m h := by
      rw [hf, (T.Mm m h).sem_mul, T.sem_cstN m _, Derivation.leibniz, deriv_ratCastK, bE]
      simp only [smul_eq_mul, mul_zero, add_zero]
      push_cast
      ring
    have e1 : solM as m elem W i = fun ws ↦ (prde (expK as) m f ws).map Prod.fst :=
      funext fun ws ↦ if_neg hi
    have e2 : T.AdmM m h (SM as m W) i = fun v ↦
        ∃ y : T.F m, y′ + (((i : ℤ) - SM as m W : ℤ) : T.F m) * T.bE m h * y = v :=
      funext fun v ↦ if_neg hi
    have e3 : T.AdmCM m h (SM as m W) i = fun v ↦
        ∃ y : T.F m, y′ + (((i : ℤ) - SM as m W : ℤ) : T.F m) * T.bE m h * y = v :=
      funext fun v ↦ if_neg hi
    rw [e1, e2, e3]
    refine ⟨fun ws β hβ ↦ ?_, fun ws c hc hadm ↦ ?_⟩
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hβ
      refine ⟨(T.Mm m h).sem r.2, ?_⟩
      rw [← (hprde f).sound ws r hr, hfd]
    · obtain ⟨y, hy⟩ := hadm
      obtain ⟨β, hβc, -⟩ := (hprde f).complete ws c hc y (by rw [hfd]; exact hy)
      refine ⟨β, fun k ↦ ?_⟩
      rw [hβc k, List.length_map]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      rw [NestTower.getD_map' _ _ ([], (opsM (expK as) m).zero) [] (Finset.mem_range.mp hl)]

/-- **Admissible Laurent coefficients give an elementary integral.** -/
lemma laurent_elem (P : (T.F m)[X]) (S : ℕ) (hadm : ∀ i, T.AdmM m h S i (P.coeff i)) :
    HasElementaryIntegralIn (((T.phi m P / T.phi m (X ^ S) : T.F (m + 1))) : E) := by
  classical
  have hinj := T.phi_injective' m h
  have hXS : T.phi m (X ^ S) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  rw [P.as_sum_range_C_mul_X_pow, map_sum, Finset.sum_div, AddSubmonoidClass.coe_finset_sum]
  refine Finset.sum_induction _ (fun x : E ↦ HasElementaryIntegralIn x) (fun a b ha hb ↦ ha.add hb)
    (by have := hasElementaryIntegralIn_deriv (0 : E); rwa [Derivation.map_zero] at this)
    (fun i _ ↦ ?_)
  have hi := hadm i
  unfold AdmM at hi
  split_ifs at hi with hiS
  · subst hiS
    rw [map_mul, mul_div_assoc, div_self hXS, mul_one, T.phi_C]
    exact hi
  · obtain ⟨y, hy⟩ := hi
    have e : T.phi m (C (P.coeff i) * X ^ i) / T.phi m (X ^ S) =
        (T.phi m (C y * X ^ i) / T.phi m (X ^ S))′ := by
      rw [T.deriv_laurent_tower m h, ← hy]
      congr 2
      rw [Derivation.leibniz, implicitDeriv_C, deriv_X_pow]
      simp only [smul_eq_mul, C_add, C_mul, C_sub]
      push_cast
      simp only [C_add, C_mul, C_sub, C_neg]
      ring
    rw [e, coe_deriv]
    exact hasElementaryIntegralIn_deriv _

end Adm

section PuFacts

variable (m : ℕ) (h : T.Tr (m + 1))

lemma toPoly_PuM (W : List (Code (m + 2))) {u : ℕ} (hu : u < (E1M as m W).length) :
    GPoly.toPoly (T.Mm m h) ((PuM as m W).getD u []) = ∑ i ∈ Finset.range W.length,
      C ((((E1M as m W).getD u []).getD i 0 : ℚ) : T.F m) * GPoly.toPoly (T.Mm m h)
        (shiftedL (opsM (expK as) m) (SM as m W) (eSp as m (W.getD i (opsM (expK as) (m + 1)).zero))) := by
  rw [PuM, NestTower.getD_map' _ _ [] [] hu, toPoly_lcombGP (T.Mm m h) (cstN m) (T.sem_cstN m _),
    zipWith_sum_getD (fun (q : ℚ) (p : GPoly (Code (m + 1))) ↦
      C (q : T.F m) * GPoly.toPoly (T.Mm m h) p) 0 [] (by simp)]
  rw [show ((W.map (eSp as m)).map (shiftedL (opsM (expK as) m) (SM as m W))).length = W.length by simp]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [NestTower.getD_map_map (eSp as m) _ W (opsM (expK as) (m + 1)).zero [] (Finset.mem_range.mp hi)]

lemma length_PuM (W : List (Code (m + 2))) : (PuM as m W).length = (E1M as m W).length := by
  simp [PuM]

lemma getD_E1M (W : List (Code (m + 2))) {u i : ℕ} (hu : u < (E1M as m W).length)
    (hi : i < W.length) : ((E1M as m W).getD u []).getD i 0 =
      ((consys (expK as) (m + 1) (resCodesM as m W)).getD u []).getD i 0 := by
  rw [E1M, NestTower.getD_map' _ _ [] [] (by simpa [E1M] using hu), NestTower.getD_range_map _ _ hi]

/-- The Laurent part of a rational combination. -/
lemma sum_PuM_Q (W : List (Code (m + 2))) (δ : List ℚ) :
    ∑ u ∈ Finset.range (PuM as m W).length, C ((δ.getD u 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.Mm m h) ((PuM as m W).getD u []) =
    ∑ i ∈ Finset.range W.length, C (((vcomb W.length δ (E1M as m W)).getD i 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.Mm m h) (shiftedL (opsM (expK as) m) (SM as m W)
        (eSp as m (W.getD i (opsM (expK as) (m + 1)).zero))) := by
  have e : ∀ u ∈ Finset.range (PuM as m W).length, C ((δ.getD u 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.Mm m h) ((PuM as m W).getD u []) = ∑ i ∈ Finset.range W.length,
        C (((δ.getD u 0 * ((E1M as m W).getD u []).getD i 0 : ℚ)) : T.F m) *
          GPoly.toPoly (T.Mm m h) (shiftedL (opsM (expK as) m) (SM as m W)
            (eSp as m (W.getD i (opsM (expK as) (m + 1)).zero))) := fun u hu ↦ by
    have hu' : u < (E1M as m W).length := by rw [← length_PuM]; exact Finset.mem_range.mp hu
    rw [T.toPoly_PuM m h W hu', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    push_cast
    rw [C_mul]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm, length_PuM]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [getD_vcomb, if_pos (Finset.mem_range.mp hi), ← Finset.sum_mul]
  push_cast
  rw [map_sum]

/-- The Laurent part of a constant combination. -/
lemma sum_PuM_K (W : List (Code (m + 2))) (β0 c : List Kc)
    (hc : ∀ i < W.length, c.getD i 0 = ∑ u ∈ Finset.range (E1M as m W).length,
      β0.getD u 0 * algebraMap ℚ Kc (((E1M as m W).getD u []).getD i 0)) :
    ∑ u ∈ Finset.range (PuM as m W).length, C (algebraMap Kc (T.F m) (β0.getD u 0)) *
      GPoly.toPoly (T.Mm m h) ((PuM as m W).getD u []) =
    ∑ i ∈ Finset.range W.length, C (algebraMap Kc (T.F m) (c.getD i 0)) *
      GPoly.toPoly (T.Mm m h) (shiftedL (opsM (expK as) m) (SM as m W)
        (eSp as m (W.getD i (opsM (expK as) (m + 1)).zero))) := by
  have e : ∀ u ∈ Finset.range (PuM as m W).length, C (algebraMap Kc (T.F m) (β0.getD u 0)) *
      GPoly.toPoly (T.Mm m h) ((PuM as m W).getD u []) = ∑ i ∈ Finset.range W.length,
        C (algebraMap Kc (T.F m) (β0.getD u 0 * algebraMap ℚ Kc (((E1M as m W).getD u []).getD i 0))) *
          GPoly.toPoly (T.Mm m h) (shiftedL (opsM (expK as) m) (SM as m W)
            (eSp as m (W.getD i (opsM (expK as) (m + 1)).zero))) := fun u hu ↦ by
    have hu' : u < (E1M as m W).length := by rw [← length_PuM]; exact Finset.mem_range.mp hu
    rw [T.toPoly_PuM m h W hu', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, T.algebraMap_ratCastM, C_mul]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm, length_PuM]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [hc i (Finset.mem_range.mp hi), ← Finset.sum_mul, ← map_sum, ← map_sum]

end PuFacts

section StepSpec

variable (m : ℕ) (h : T.Tr (m + 1))
variable (hc2 : ∀ u ∈ consys (expK as) m ((opsM (expK as) m).deriv (as m) :: dExps as m),
  u.getD 0 0 = 0)

include hc2 in
set_option maxHeartbeats 3200000 in
/-- **Parametric elementary integration over an exponential level is sound and complete.** -/
theorem expElemStep_spec (elem : List (Code (m + 1)) → List (List ℚ))
    (hel : ElemSolSpec (algebraMap Kc (T.F m)) (T.Mm m h) (fun v ↦ HasElementaryIntegralIn (v : E))
      (fun v ↦ LiouvilleIn (T.F m) (v : E)) elem)
    (hprde : ∀ f : Code (m + 1),
      RdeSpecK (algebraMap Kc (T.F m)) (T.Mm m h) ((T.Mm m h).sem f)′ (prde (expK as) m f)) :
    ElemSolSpec (algebraMap Kc (T.F (m + 1))) (T.MP (m + 1) h)
      (fun v ↦ HasElementaryIntegralIn (v : E)) (fun v ↦ LiouvilleIn (T.F (m + 1)) (v : E))
      (expElemStep (expK as) m (as m) elem) := by
  classical
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
  have hinj := T.phi_injective' m h
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  -- the loop, for any `W`
  have hloop : ∀ W : List (Code (m + 2)),
      ESound (T.Mm m h) (PuM as m W) (T.AdmM m h (SM as m W)) 0
        (elemLoop (E1M as m W).length (fun i Bs ↦ solM as m elem W i
          (coefCodes (opsM (expK as) m) (cstN m) (PuM as m W) i Bs)) (topM as m W)
          ((List.range (E1M as m W).length).map (unitV (E1M as m W).length))) ∧
      EComplete (algebraMap Kc (T.F m)) (T.Mm m h) (PuM as m W) (T.AdmCM m h (SM as m W))
        (E1M as m W).length 0
        (elemLoop (E1M as m W).length (fun i Bs ↦ solM as m elem W i
          (coefCodes (opsM (expK as) m) (cstN m) (PuM as m W) i Bs)) (topM as m W)
          ((List.range (E1M as m W).length).map (unitV (E1M as m W).length))) := by
    intro W
    have htop : ∀ u < (PuM as m W).length, ((PuM as m W).getD u []).length ≤ topM as m W :=
      fun u hu ↦ le_foldr_max _ _ (List.mem_map.mpr ⟨_, NestTower.getD_mem_of_lt _ _ hu, rfl⟩)
    refine elemLoop_stage (algebraMap Kc (T.F m)) (M := T.Mm m h) (cst := cstN m) (PuM as m W)
      (T.sem_cstN m _) (T.AdmM m h (SM as m W)) (T.AdmCM m h (SM as m W)) (solM as m elem W)
      (fun i ↦ T.solM_spec m h elem hel hprde W i)
      (fun i s q v hv ↦ T.admM_lin m h (SM as m W) i s q v hv) (fun q ↦ T.algebraMap_ratCastM q)
      (E1M as m W).length (length_PuM m W) _ _ ?_ ?_
    · intro β _ i hi
      rw [cvalQ_eq_zero (PuM as m W) (topM as m W) htop i hi]
      exact T.admM_zero m h _ i
    · intro c hc _
      exact ⟨(List.range (E1M as m W).length).map fun i ↦ c.getD i 0,
        unit_span (E1M as m W).length c hc⟩
  refine ⟨fun W β hβ ↦ ?_, fun W c hc hL ↦ ?_⟩
  · -- soundness
    rw [expElemStep_eq] at hβ
    split_ifs at hβ with hchk
    swap
    · simp at hβ
    obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hβ
    obtain ⟨hsq, hXS, hdat⟩ := T.lcm_dataM m h W hchk
    have hadm : ∀ i, T.AdmM m h (SM as m W) i (cvalQ (T.Mm m h) (PuM as m W) i δ) :=
      fun i ↦ (hloop W).1 δ hδ i (Nat.zero_le _)
    set n := W.length with hn
    set S := SM as m W with hS
    set Sv := GPoly.toPoly (T.Mm m h) (lcmSM as m W) with hSv
    set vq : ℕ → ℚ := fun i ↦ (vcomb n δ (E1M as m W)).getD i 0 with hvq
    set Nq := ∑ i ∈ Finset.range n, C ((vq i : ℚ) : T.F m) *
      GPoly.toPoly (T.Mm m h) ((numLM as m W).getD i []) with hNq
    set Rq := ∑ i ∈ Finset.range n, C ((vq i : ℚ) : T.F m) *
      GPoly.toPoly (T.Mm m h) (GPoly.residuePoly (opsM (expK as) m) (wkM as m)
        ((numLM as m W).getD i []) (lcmSM as m W)) with hRq
    set Pq := ∑ u ∈ Finset.range (PuM as m W).length, C ((δ.getD u 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.Mm m h) ((PuM as m W).getD u []) with hPq
    set G := ∑ i ∈ Finset.range n, ((vq i : ℚ) : T.F (m + 1)) *
      (T.M1 m h).sem ((eSp as m (W.getD i (opsM (expK as) (m + 1)).zero)).gn,
        (eSp as m (W.getD i (opsM (expK as) (m + 1)).zero)).gd) with hG
    have hφS : T.phi m Sv ≠ 0 := (map_ne_zero_iff _ hinj).mpr hsq.ne_zero
    have hXSφ : T.phi m (X ^ S) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
    -- the value
    have hA : sQ (T.MP (m + 1) h) (vcomb n δ (E1M as m W)) W =
        G′ + T.phi m Nq / T.phi m Sv + T.phi m Pq / T.phi m (X ^ S) := by
      rw [hPq, T.sum_PuM_Q m h W δ, hG, T.deriv_sum_ratCastM, hNq, map_sum, map_sum, Finset.sum_div,
        Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, sQ]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [(hdat i (Finset.mem_range.mp hi)).1, map_mul, map_mul, T.phi_C_ratCastM]
      simp only [hvq, σ1]
      ring
    have hAE : ((sQ (T.MP (m + 1) h) (vcomb n δ (E1M as m W)) W : T.F (m + 1)) : E) =
        (G : E)′ + ((T.phi m Nq / T.phi m Sv : T.F (m + 1)) : E) +
          ((T.phi m Pq / T.phi m (X ^ S) : T.F (m + 1)) : E) := by
      rw [hA, IntermediateField.coe_add, IntermediateField.coe_add, coe_deriv]
    -- the logarithmic part
    have hlog : HasElementaryIntegralIn ((T.phi m Nq / T.phi m Sv : T.F (m + 1)) : E) := by
      have hst : aeval (T.ts m) Sv ≠ 0 := by
        rw [← T.coe_phi]
        exact fun h0 ↦ hφS (Subtype.ext h0)
      have hdeg : Nq.degree < Sv.degree :=
        NestTower.degree_sum_C_mul_lt n _ _ Sv hsq.ne_zero fun i hi ↦ (hdat i hi).2
      have hr : Sv ∣ Rq * (mapCoeffs Sv + (C 0 + C (T.bE m h) * X) * derivative Sv) - Nq := by
        rw [C_0, zero_add, hRq, hNq, Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.dvd_sum fun i _ ↦ ?_
        have := (T.res_dataM m h W hsq hXS ((numLM as m W).getD i [])).1
        rw [show ∀ a b c d : (T.F m)[X], a * b * c - a * d = a * (b * c - d) from
          fun _ _ _ _ ↦ by ring]
        exact dvd_mul_of_dvd_right this _
      have hT : Sv ∣ residueTest Rq Sv := by
        rw [hRq, residueTest_sum n _ (fun i ↦ T.deriv_ratCast _)]
        have h0 := T.sum_Tv_eq_zeroM m h W δ
        rw [← sub_zero (∑ i ∈ Finset.range n, _), ← h0, ← Finset.sum_sub_distrib]
        refine Finset.dvd_sum fun i _ ↦ ?_
        rw [← mul_sub]
        exact dvd_mul_of_dvd_right (T.res_dataM m h W hsq hXS _).2.1 _
      have ht' : (T.ts m)′ = algebraMap (T.F m) E 0 + algebraMap (T.F m) E (T.bE m h) * T.ts m := by
        rw [map_zero, zero_add, T.deriv_ts_aeval m, T.wPoly_eq_bE m h, map_mul, aeval_C, aeval_X]
      have hts0 : T.ts m ≠ 0 := T.hts0 m (as m) rfl
      have hθ : logDeriv (T.ts m) = algebraMap (T.F m) E (T.bE m h) := by
        unfold logDeriv
        rw [ht', map_zero, zero_add]
        field_simp
      rw [IntermediateField.coe_div, T.coe_phi, T.coe_phi]
      exact hasElementaryIntegralIn_of_residueTest (F := T.F m) (T.ts m) 0 (T.bE m h) ht' (T.ts m)
        hts0 hθ Sv Nq Rq (PerfectField.separable_iff_squarefree.mpr hsq) hst hdeg hr hT
    -- the Laurent part
    have hlau : HasElementaryIntegralIn ((T.phi m Pq / T.phi m (X ^ S) : T.F (m + 1)) : E) := by
      refine T.laurent_elem m h Pq S fun i ↦ ?_
      have hc : Pq.coeff i = cvalQ (T.Mm m h) (PuM as m W) i δ := by
        rw [hPq, finset_sum_coeff, cvalQ]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [coeff_C_mul]
      rw [hc]
      exact hadm i
    rw [hAE]
    exact ((hasElementaryIntegralIn_deriv _).add hlog).add hlau
  · -- completeness
    have hchk := T.lcmCheck_trueM m h W
    rw [expElemStep_eq, if_pos hchk]
    obtain ⟨hsq, hXS, hdat⟩ := T.lcm_dataM m h W hchk
    set n := W.length with hn
    set S := SM as m W with hS
    set Sv := GPoly.toPoly (T.Mm m h) (lcmSM as m W) with hSv
    set ac : ℕ → T.F m := fun i ↦ algebraMap Kc (T.F m) (c.getD i 0) with hac
    have hac' : ∀ i, (ac i)′ = 0 := fun i ↦ T.deriv_algebraMap_Kc _
    set Nv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly (T.Mm m h) ((numLM as m W).getD i []) with hNv
    set Rv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly (T.Mm m h) (GPoly.residuePoly (opsM (expK as) m)
      (wkM as m) ((numLM as m W).getD i []) (lcmSM as m W)) with hRv
    set Tv : ℕ → (T.F m)[X] := fun i ↦
      GPoly.toPoly (T.Mm m h) (ttCodeM as m W ((numLM as m W).getD i [])) with hTv
    set Nc := ∑ i ∈ Finset.range n, C (ac i) * Nv i with hNc
    set Rc := ∑ i ∈ Finset.range n, C (ac i) * Rv i with hRc
    set Pc := ∑ i ∈ Finset.range n, C (ac i) * GPoly.toPoly (T.Mm m h)
      (shiftedL (opsM (expK as) m) S (eSp as m (W.getD i (opsM (expK as) (m + 1)).zero))) with hPc
    set G : T.F (m + 1) := ∑ i ∈ Finset.range n, algebraMap Kc (T.F (m + 1)) (c.getD i 0) *
      (T.M1 m h).sem ((eSp as m (W.getD i (opsM (expK as) (m + 1)).zero)).gn,
        (eSp as m (W.getD i (opsM (expK as) (m + 1)).zero)).gd) with hG
    -- the value
    have hsum : sC (algebraMap Kc (T.F (m + 1))) (T.MP (m + 1) h) c W =
        G′ + T.phi m Nc / T.phi m Sv + T.phi m Pc / T.phi m (X ^ S) := by
      rw [hG, T.deriv_sum_KcM, hNc, hPc, map_sum, map_sum, Finset.sum_div, Finset.sum_div,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, sC]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [(hdat i (Finset.mem_range.mp hi)).1, map_mul, map_mul, T.algebraMap_succ]
      simp only [hac, hNv, σ1]
      ring
    have hdegN : Nc.degree < Sv.degree :=
      NestTower.degree_sum_C_mul_lt n _ _ Sv hsq.ne_zero fun i hi ↦ (hdat i hi).2
    have hr : Sv ∣ Rc * (mapCoeffs Sv + C (T.bE m h) * X * derivative Sv) - Nc := by
      rw [hRc, hNc, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.dvd_sum fun i _ ↦ ?_
      have := (T.res_dataM m h W hsq hXS ((numLM as m W).getD i [])).1
      rw [show ∀ a b c d : (T.F m)[X], a * b * c - a * d = a * (b * c - d) from
        fun _ _ _ _ ↦ by ring]
      exact dvd_mul_of_dvd_right this _
    rw [hsum] at hL
    obtain ⟨hT, hj, hPS⟩ := T.exp_liouville_split m h hc2 G Nc Sv Rc Pc S hsq hXS hdegN hr hL
    -- the residue condition
    have hT0 : ∑ i ∈ Finset.range n, C (ac i) * Tv i = 0 := by
      refine eq_zero_of_dvd_of_degree_lt ?_ (NestTower.degree_sum_C_mul_lt n _ _ Sv hsq.ne_zero
        fun i _ ↦ (T.res_dataM m h W hsq hXS _).2.2)
      have e : ∑ i ∈ Finset.range n, C (ac i) * Tv i = residueTest Rc Sv -
          ∑ i ∈ Finset.range n, C (ac i) * (residueTest (Rv i) Sv - Tv i) := by
        rw [hRc, residueTest_sum n ac hac', ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        ring
      rw [e]
      exact dvd_sub hT (Finset.dvd_sum fun i _ ↦
        dvd_mul_of_dvd_right (T.res_dataM m h W hsq hXS _).2.1 _)
    -- the constant system at level `m + 1`
    set U := consys (expK as) (m + 1) (resCodesM as m W) with hU
    have h0 : (List.zipWith (fun c v ↦ algebraMap Kc (T.F (m + 1)) c * (T.MP (m + 1) h).sem v)
        ((List.range (resCodesM as m W).length).map fun i ↦ c.getD i 0)
        (resCodesM as m W)).sum = 0 := by
      rw [NestTower.zipWith_sum_range _ 0 (opsM (expK as) (m + 1)).zero _ _ (by simp)]
      have e : ∀ i ∈ Finset.range ((List.range (resCodesM as m W).length).map
          fun i ↦ c.getD i 0).length,
          algebraMap Kc (T.F (m + 1)) (((List.range (resCodesM as m W).length).map
            fun i ↦ c.getD i 0).getD i 0) *
            (T.MP (m + 1) h).sem ((resCodesM as m W).getD i (opsM (expK as) (m + 1)).zero) =
          T.phi m (C (ac i) * Tv i) := fun i hi ↦ by
        have hi' : i < n := by
          have := Finset.mem_range.mp hi
          rwa [List.length_map, List.length_range, length_resCodesM] at this
        rw [NestTower.getD_range_map (fun j ↦ c.getD j 0) 0 (by rw [length_resCodesM]; exact hi'),
          getD_resCodesM m W hi', map_mul, T.algebraMap_succ]
        congr 1
        change T.σ1 m h _ / T.σ1 m h [(opsM (expK as) m).one] = _
        rw [T.σ1_one, div_one]
      rw [Finset.sum_congr rfl e, List.length_map, List.length_range, length_resCodesM, ← map_sum,
        hT0, map_zero]
    obtain ⟨β, hβl, hβ⟩ := T.consys_complete (m + 1) h (resCodesM as m W) _ (by simp) h0
    rw [← hU] at hβl hβ
    have hlE : (E1M as m W).length = U.length := length_E1M m W
    have hβc : ∀ i < n, c.getD i 0 = ∑ u ∈ Finset.range (E1M as m W).length,
        β.getD u 0 * algebraMap ℚ Kc (((E1M as m W).getD u []).getD i 0) := fun i hi ↦ by
      have := hβ i
      rw [NestTower.getD_range_map (fun j ↦ c.getD j 0) 0 (by rw [length_resCodesM]; exact hi),
        NestTower.zipWith_sum_range _ 0 [] _ _ hβl, hβl] at this
      rw [this, hlE]
      refine Finset.sum_congr rfl fun u hu ↦ ?_
      rw [getD_E1M m W (by rw [hlE]; exact Finset.mem_range.mp hu) hi]
    -- the Laurent part in terms of the basis
    have hPcb : Pc = ∑ u ∈ Finset.range (PuM as m W).length,
        C (algebraMap Kc (T.F m) (β.getD u 0)) * GPoly.toPoly (T.Mm m h) ((PuM as m W).getD u []) :=
      (T.sum_PuM_K m h W β c hβc).symm
    have hadm : ∀ i, 0 ≤ i → T.AdmCM m h S i
        (cvalC (algebraMap Kc (T.F m)) (T.Mm m h) (PuM as m W) i β) := by
      intro i _
      have hcv : cvalC (algebraMap Kc (T.F m)) (T.Mm m h) (PuM as m W) i β = Pc.coeff i := by
        rw [hPcb, finset_sum_coeff, cvalC]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [coeff_C_mul]
      rw [hcv]
      unfold AdmCM
      split_ifs with hiS
      · subst hiS; exact hPS
      · exact hj i hiS
    obtain ⟨γ, hγ⟩ := (hloop W).2 β (fun u hu ↦ List.getD_eq_default _ _ (by rw [hβl, ← hlE]; exact hu))
      hadm
    -- recombine
    set pe := elemLoop (E1M as m W).length (fun i Bs ↦ solM as m elem W i
      (coefCodes (opsM (expK as) m) (cstN m) (PuM as m W) i Bs)) (topM as m W)
      ((List.range (E1M as m W).length).map (unitV (E1M as m W).length)) with hpe
    refine ⟨γ, fun i ↦ ?_⟩
    rw [List.length_map]
    have e : ∀ k ∈ Finset.range pe.length, γ.getD k 0 * algebraMap ℚ Kc
        (((pe.map fun δ ↦ vcomb n δ (E1M as m W)).getD k []).getD i 0) =
        γ.getD k 0 * algebraMap ℚ Kc ((vcomb n (pe.getD k []) (E1M as m W)).getD i 0) :=
      fun k hk ↦ by rw [NestTower.getD_map' _ _ [] [] (Finset.mem_range.mp hk)]
    rw [Finset.sum_congr rfl e]
    by_cases hi : i < n
    · have := recombine n (E1M as m W).length pe.length
        (fun u i ↦ ((E1M as m W).getD u []).getD i 0) (fun j u ↦ (pe.getD j []).getD u 0)
        (fun i ↦ c.getD i 0) (fun u ↦ β.getD u 0) (fun j ↦ γ.getD j 0) hβc
        (fun u _ ↦ hγ u) i hi
      rw [this]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [getD_vcomb, if_pos hi]
    · rw [hc i (by omega)]
      symm
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [getD_vcomb, if_neg hi, map_zero, mul_zero]

end StepSpec

section Induction

/-- Every element of `Kc(x)` given by a rational code has an elementary integral. -/
theorem rational_inM (q : GFrac ℚ) : HasElementaryIntegralIn (PrimN.evx Kc T.x q) := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
  by_cases hq : (CPoly.toPoly q.2).map (algebraMap ℚ Kc) = 0
  · have : PrimN.evx Kc T.x q = (0 : E)′ := by simp [PrimN.evx, hq]
    rw [this]
    exact hasElementaryIntegralIn_deriv 0
  intro E' _ _ _ _ _
  let _ : Algebra Kc E' := ((algebraMap E E').comp (algebraMap Kc E)).toAlgebra
  have hDA : DifferentialAlgebra Kc E' :=
    ⟨fun a ↦ by
      change (algebraMap E E' (algebraMap Kc E a))′ = algebraMap E E' (algebraMap Kc E a′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  have hx : (algebraMap E E' T.x)′ = 1 := by rw [deriv_algebraMap, T.hx, map_one]
  have haev : ∀ P : Kc[X], algebraMap E E' (aeval T.x P) = aeval (algebraMap E E' T.x) P :=
    fun P ↦ by
      rw [aeval_def, aeval_def, hom_eval₂]
      rfl
  have := hasElementaryIntegral_rational_in T.hC (algebraMap E E' T.x) hx
    ((CPoly.toPoly q.1).map (algebraMap ℚ Kc)) _ hq 0
  rw [map_zero, zero_add] at this
  rw [PrimN.evx, map_div₀, haev, haev]
  exact this

/-- **The base `Kc(x)`**: everything is elementary. -/
theorem paramElem0_spec (h : T.Tr 0) :
    ElemSolSpec (algebraMap Kc (T.F 0)) (T.MP 0 h) (fun v ↦ HasElementaryIntegralIn (v : E))
      (fun v ↦ LiouvilleIn (T.F 0) (v : E)) (paramElemM (expK as) 0) := by
  refine ⟨fun W β _ ↦ ?_, fun W c hc _ ↦ ?_⟩
  · have e : sQ (T.MP 0 h) β W = (T.MP 0 h).sem (lcombCode (opsM (expK as) 0) (cstN 0) β W) := by
      rw [sem_lcombCode (T.MP 0 h) (cstN 0) (T.sem_cstN 0 h),
        zipWith_sum_getD (fun (q : ℚ) (a : Code 1) ↦ ((q : ℚ) : T.F 0) * (T.MP 0 h).sem a) 0
          (opsM (expK as) 0).zero (by simp)]
      rfl
    rw [e, T.sem_MP]
    exact T.rational_inM _
  · exact ⟨(List.range W.length).map fun i ↦ c.getD i 0, unit_span W.length c hc⟩

/-- **Parametric elementary integration at every level of a certified exponential tower.** -/
theorem paramElemM_spec : ∀ (n : ℕ), expCertM (expK as) n = true → ∀ (h : T.Tr n),
    ElemSolSpec (algebraMap Kc (T.F n)) (T.MP n h) (fun v ↦ HasElementaryIntegralIn (v : E))
      (fun v ↦ LiouvilleIn (T.F n) (v : E)) (paramElemM (expK as) n)
  | 0, _, h => T.paramElem0_spec h
  | n + 1, hcert, h => by
    obtain ⟨hc1, hc2⟩ := expCert_succ hcert
    have hn : T.Tr n := fun i hi ↦ h i (by omega)
    have IH := paramElemM_spec n hc1 hn
    exact T.expElemStep_spec n h hc2 (paramElemM (expK as) n) IH (fun f ↦ T.prde_spec n hc1 hn f)

end Induction

end NestMTower

end Tower.NestM
