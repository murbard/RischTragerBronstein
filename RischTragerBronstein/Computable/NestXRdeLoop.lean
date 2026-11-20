import RischTragerBronstein.Computable.NestMRdeLoop
import RischTragerBronstein.Liouville.PrimitivePoly
import RischTragerBronstein.Computable.NestPElemPoly
import RischTragerBronstein.Liouville.ExponentialPoly
import RischTragerBronstein.Liouville.ExponentialLaurentPart

/-!
# The coefficient loop of the Risch equation over an exponential: soundness and completeness

Generic in a differential field `K` with a model `M`, an exponential monomial (`t′ = DS t`, the
derivation of `K[t]` being `DzX = implicitDeriv (DS.W)`), the polynomial equation
`A Y′ + B Y = ∑ cᵢ Cᵢ` (`deg A, deg B ≤ δ`) and a one-level-down solver `lower k` of the scalar
Risch equations `z′ + fₖ z = ∑ βⱼ wⱼ`. The loop `rdeLoop` treats the equations of degree
`k + δ`, `k = N, …, 0`; stage `j` invariants: the basis elements vanish below `j` and satisfy
the equations of degree `≥ j + δ`, and span (over the constants) all solutions of those equations
on the coefficients of degree `≥ j`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.NestX

open Tower.NestP Tower.NestM

/-- The shape of a monomial derivation `implicitDeriv W` of `K[t]`: it does not raise degrees, and
the coefficient `k` of `D Z` for `deg Z ≤ k` is `Zₖ′ + sh k Zₖ` (`sh k = k b` for `t′ = b t`,
`sh k = 0` for a primitive). -/
structure DShape (K : Type*) [Field K] [Differential K] where
  W : K[X]
  sh : ℕ → K
  deg : ∀ (Z : K[X]) (k : ℕ), Z.natDegree ≤ k → (implicitDeriv W Z).natDegree ≤ k
  top : ∀ (Z : K[X]) (k : ℕ), Z.natDegree ≤ k →
    (implicitDeriv W Z).coeff k = (Z.coeff k)′ + sh k * Z.coeff k

/-- The exponential shape `t′ = b t`. -/
noncomputable def expShape {K : Type*} [Field K] [Differential K] (b : K) : DShape K where
  W := C b * X
  sh k := k * b
  deg Z k hZ := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    have hi' : Z.natDegree < i := lt_of_le_of_lt hZ (by exact_mod_cast hi)
    rw [coeff_implicitDeriv_C_mul_X, coeff_eq_zero_of_natDegree_lt hi']
    simp
  top Z k _ := by rw [coeff_implicitDeriv_C_mul_X]; ring

/-- The primitive shape `t′ = η`. -/
noncomputable def primShape {K : Type*} [Field K] [Differential K] (η : K) : DShape K where
  W := C η
  sh _ := 0
  deg Z k hZ := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    have hi' : Z.natDegree < i := lt_of_le_of_lt hZ (by exact_mod_cast hi)
    rw [coeff_implicitDeriv_C, coeff_eq_zero_of_natDegree_lt hi',
      coeff_eq_zero_of_natDegree_lt (by omega)]
    simp
  top Z k hZ := by
    rw [coeff_implicitDeriv_C, coeff_eq_zero_of_natDegree_lt (by omega : Z.natDegree < k + 1)]
    ring


section Generic

variable {α : Type} {K Cs : Type*} [Field K] [Differential K] [CharZero K] [Field Cs] [CharZero Cs]
variable (ι : Cs →+* K) {O : COps α} (M : CField α K O) (cst : ℚ → α)
variable (DS : DShape K) (A B : GPoly α) (Cl : List (GPoly α)) (δ : ℕ)

/-- The derivation of `K[t]`, `t′ = DS t`. -/
noncomputable abbrev DzX (P : K[X]) : K[X] := implicitDeriv DS.W P

/-- The residual `A Y′ + B Y - ∑ cᵢ Cᵢ`, constant coefficients. -/
noncomputable def resCX (c : List Cs) (Y : K[X]) : K[X] :=
  GPoly.toPoly M A * DzX DS Y + GPoly.toPoly M B * Y -
    ∑ i ∈ Finset.range Cl.length, C (ι (c.getD i 0)) * GPoly.toPoly M (Cl.getD i [])

/-- The residual `A Y′ + B Y - ∑ eᵢ Cᵢ`, rational coefficients. -/
noncomputable def resQX (e : List ℚ) (Y : K[X]) : K[X] :=
  GPoly.toPoly M A * DzX DS Y + GPoly.toPoly M B * Y -
    ∑ i ∈ Finset.range Cl.length, C ((e.getD i 0 : ℚ) : K) * GPoly.toPoly M (Cl.getD i [])

/-- Stage `j`, soundness. -/
def RStageSoundX (j : ℕ) (Bs : List (List ℚ × GPoly α)) : Prop :=
  ∀ bb ∈ Bs, bb.1.length = Cl.length ∧ (∀ i < j, (GPoly.toPoly M bb.2).coeff i = 0) ∧
    ∀ d, j + δ ≤ d → (resQX M DS A B Cl bb.1 (GPoly.toPoly M bb.2)).coeff d = 0

/-- Stage `j`, completeness. -/
def RStageCompleteX (N j : ℕ) (Bs : List (List ℚ × GPoly α)) : Prop :=
  ∀ c : List Cs, (∀ i, Cl.length ≤ i → c.getD i 0 = 0) → ∀ Y : K[X], Y.natDegree ≤ N →
    (∀ d, j + δ ≤ d → (resCX ι M DS A B Cl c Y).coeff d = 0) →
    ∃ β : List Cs,
      (∀ i, c.getD i 0 = ∑ k ∈ Finset.range Bs.length,
        β.getD k 0 * algebraMap ℚ Cs ((Bs.getD k ([], [])).1.getD i 0)) ∧
      ∀ i, j ≤ i → Y.coeff i = ∑ l ∈ Finset.range Bs.length,
        ι (β.getD l 0) * (GPoly.toPoly M (Bs.getD l ([], [])).2).coeff i

/-- The operator part `A Y′ + B Y`. -/
noncomputable def LopX (Y : K[X]) : K[X] := GPoly.toPoly M A * DzX DS Y + GPoly.toPoly M B * Y

/-- The right-hand side `∑ eᵢ Cᵢ`. -/
noncomputable def SqX (e : List ℚ) : K[X] :=
  ∑ i ∈ Finset.range Cl.length, C ((e.getD i 0 : ℚ) : K) * GPoly.toPoly M (Cl.getD i [])

variable {M cst}

/-! ### The residual -/

omit [CharZero Cs] in
lemma Dz_C_mulX (q : ℚ) (P : K[X]) : DzX DS (C ((q : ℚ) : K) * P) = C ((q : ℚ) : K) * DzX DS P := by
  rw [DzX, Derivation.leibniz, implicitDeriv_C, deriv_ratCastK q]
  simp

omit [CharZero Cs] in
lemma Dz_sumX (N : ℕ) (q : ℕ → ℚ) (P : ℕ → K[X]) :
    DzX DS (∑ l ∈ Finset.range N, C ((q l : ℚ) : K) * P l) =
      ∑ l ∈ Finset.range N, C ((q l : ℚ) : K) * DzX DS (P l) := by
  unfold DzX
  rw [map_sum]
  exact Finset.sum_congr rfl fun l _ ↦ Dz_C_mulX DS (q l) (P l)

variable (hcst : ∀ q, M.sem (cst q) = (q : K))

include hcst in
lemma toPoly_residEX (w : GPoly α) (hw : GPoly.toPoly M w = DS.W) (bb : List ℚ × GPoly α) :
    GPoly.toPoly M (residE O cst w A B Cl bb) = resQX M DS A B Cl bb.1 (GPoly.toPoly M bb.2) := by
  rw [residE, GPoly.toPoly_sub, GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_mul,
    GPoly.toPoly_derivT, hw, toPoly_lcombGP M cst hcst,
    zipWith_sum_getD (fun (q : ℚ) (p : GPoly α) ↦ C (q : K) * GPoly.toPoly M p) 0 [] (by simp),
    resQX]

lemma resQ_eqX (e : List ℚ) (Y : K[X]) : resQX M DS A B Cl e Y = LopX M DS A B Y - SqX M Cl e := rfl

omit [CharZero Cs] in
lemma Lop_addX (Y Z : K[X]) : LopX M DS A B (Y + Z) = LopX M DS A B Y + LopX M DS A B Z := by
  simp only [LopX, DzX, map_add]; ring

omit [CharZero Cs] in
lemma Lop_sumX (N : ℕ) (q : ℕ → ℚ) (P : ℕ → K[X]) :
    LopX M DS A B (∑ l ∈ Finset.range N, C ((q l : ℚ) : K) * P l) =
      ∑ l ∈ Finset.range N, C ((q l : ℚ) : K) * LopX M DS A B (P l) := by
  simp only [LopX, Dz_sumX, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  ring

lemma Sq_vcombX (Bs : List (List ℚ)) (r : List ℚ) :
    SqX M Cl (vcomb Cl.length r Bs) =
      ∑ l ∈ Finset.range Bs.length, C ((r.getD l 0 : ℚ) : K) * SqX M Cl (Bs.getD l []) := by
  simp only [SqX, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [getD_vcomb, if_pos (Finset.mem_range.mp hi)]
  push_cast
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [C_mul]
  ring

omit [CharZero Cs] in
/-- The residual of a combination. -/
lemma resQ_combX (Bs : List (List ℚ × GPoly α)) (r : List ℚ) (Z : K[X]) :
    resQX M DS A B Cl (vcomb Cl.length r (Bs.map Prod.fst))
      (∑ l ∈ Finset.range Bs.length, C ((r.getD l 0 : ℚ) : K) * GPoly.toPoly M (Bs.getD l ([], [])).2
        + Z) =
      ∑ l ∈ Finset.range Bs.length, C ((r.getD l 0 : ℚ) : K) *
        resQX M DS A B Cl (Bs.getD l ([], [])).1 (GPoly.toPoly M (Bs.getD l ([], [])).2) +
      LopX M DS A B Z := by
  rw [resQ_eqX, Lop_addX, Lop_sumX, Sq_vcombX, List.length_map]
  simp only [resQ_eqX, mul_sub, Finset.sum_sub_distrib]
  have e : ∀ l ∈ Finset.range Bs.length, C ((r.getD l 0 : ℚ) : K) *
      SqX M Cl ((Bs.map Prod.fst).getD l []) = C ((r.getD l 0 : ℚ) : K) *
      SqX M Cl (Bs.getD l ([], [])).1 := fun l hl ↦ by
    rw [NestTower.getD_map' _ _ ([], []) [] (Finset.mem_range.mp hl)]
  rw [Finset.sum_congr rfl e]
  ring

omit [CharZero Cs] in
lemma resQ_addX (e : List ℚ) (Y Z : K[X]) :
    resQX M DS A B Cl e (Y + Z) = resQX M DS A B Cl e Y + LopX M DS A B Z := by
  rw [resQ_eqX, resQ_eqX, Lop_addX]; ring

omit [CharZero Cs] in
lemma natDegree_Dz_leX (Z : K[X]) (k : ℕ) (hZ : Z.natDegree ≤ k) : (DzX DS Z).natDegree ≤ k :=
  DS.deg Z k hZ

omit [CharZero Cs] in
/-- The coefficient of degree `k + δ` of `A Z′ + B Z` for `deg Z ≤ k`. -/
lemma coeff_Lop_topX (hA : (GPoly.toPoly M A).natDegree ≤ δ) (hB : (GPoly.toPoly M B).natDegree ≤ δ)
    (Z : K[X]) (k : ℕ) (hZ : Z.natDegree ≤ k) :
    (LopX M DS A B Z).coeff (k + δ) = (GPoly.toPoly M A).coeff δ * ((Z.coeff k)′ + DS.sh k * Z.coeff k) +
      (GPoly.toPoly M B).coeff δ * Z.coeff k := by
  rw [LopX, coeff_add, add_comm k δ, coeff_mul_add_eq_of_natDegree_le hA (natDegree_Dz_leX DS Z k hZ),
    coeff_mul_add_eq_of_natDegree_le hB hZ, DzX, DS.top Z k hZ]

omit [CharZero Cs] in
lemma coeff_Lop_highX (hA : (GPoly.toPoly M A).natDegree ≤ δ) (hB : (GPoly.toPoly M B).natDegree ≤ δ)
    (Z : K[X]) (k : ℕ) (hZ : Z.natDegree ≤ k) (d : ℕ) (hd : k + δ < d) :
    (LopX M DS A B Z).coeff d = 0 := by
  rw [LopX, coeff_add]
  have h1 : (GPoly.toPoly M A * DzX DS Z).natDegree < d :=
    lt_of_le_of_lt (natDegree_mul_le.trans (add_le_add hA (natDegree_Dz_leX DS Z k hZ))) (by omega)
  have h2 : (GPoly.toPoly M B * Z).natDegree < d :=
    lt_of_le_of_lt (natDegree_mul_le.trans (add_le_add hB hZ)) (by omega)
  rw [coeff_eq_zero_of_natDegree_lt h1, coeff_eq_zero_of_natDegree_lt h2, add_zero]

lemma natDegree_C_mul_X_pow_le'X (z : K) (k : ℕ) : (C z * X ^ k).natDegree ≤ k :=
  natDegree_C_mul_X_pow_le z k

/-! ### The steps -/

variable (w : GPoly α) (hw : GPoly.toPoly M w = DS.W)

include hcst hw in
lemma sem_rkX (bb : List ℚ × GPoly α) (d : ℕ) :
    M.sem (O.neg ((residE O cst w A B Cl bb).getD d O.zero)) =
      -(resQX M DS A B Cl bb.1 (GPoly.toPoly M bb.2)).coeff d := by
  rw [M.sem_neg, ← coeff_toPoly_getD', toPoly_residEX DS A B Cl hcst w hw]

lemma getD_mem_BX (Bs : List (List ℚ × GPoly α)) {l : ℕ} (hl : l < Bs.length) :
    Bs.getD l ([], []) ∈ Bs := by
  rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem _

include hcst hw in
/-- **The algebraic step is sound.** -/
lemma rdeStep_sound_algX (hA : (GPoly.toPoly M A).natDegree ≤ δ)
    (hB : (GPoly.toPoly M B).natDegree ≤ δ) (hAδ : (GPoly.toPoly M A).coeff δ = 0)
    (lcA lcB : α) (hlcB : M.sem lcB = (GPoly.toPoly M B).coeff δ) (hB0 : M.sem lcB ≠ 0)
    (lower : ℕ → List α → List (List ℚ × α)) (k : ℕ) (Bs : List (List ℚ × GPoly α))
    (hBs : RStageSoundX M DS A B Cl δ (k + 1) Bs) :
    RStageSoundX M DS A B Cl δ k (rdeStep O cst w A B Cl Cl.length δ true lcA lcB lower k Bs) := by
  intro bb hbb
  simp only [rdeStep, if_true] at hbb
  obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hbb
  obtain ⟨hl, hlow, hres⟩ := hBs b0 hb0
  set q := M.sem (O.mul (O.neg ((residE O cst w A B Cl b0).getD (k + δ) O.zero)) (O.inv lcB))
    with hq
  have hY : GPoly.toPoly M (GPoly.add O b0.2 (GPoly.monomial O k
      (O.mul (O.neg ((residE O cst w A B Cl b0).getD (k + δ) O.zero)) (O.inv lcB)))) =
      GPoly.toPoly M b0.2 + C q * X ^ k := by
    rw [GPoly.toPoly_add, GPoly.toPoly_monomial]
  refine ⟨hl, fun i hi ↦ ?_, fun d hd ↦ ?_⟩
  · rw [hY, coeff_add, hlow i (by omega), coeff_C_mul_X_pow, if_neg (by omega), add_zero]
  · simp only [hY, resQ_addX, coeff_add]
    rcases Nat.eq_or_lt_of_le hd with rfl | hlt
    · rw [coeff_Lop_topX DS A B δ hA hB _ k (natDegree_C_mul_X_pow_le q k), hAδ, zero_mul, zero_add,
        coeff_C_mul_X_pow, if_pos rfl, hq, M.sem_mul, M.sem_inv, sem_rkX DS A B Cl hcst w hw, ← hlcB]
      field_simp
      ring
    · rw [hres d (by omega), coeff_Lop_highX DS A B δ hA hB _ k (natDegree_C_mul_X_pow_le q k) d hlt,
        add_zero]

include hcst hw in
/-- **The differential step is sound.** -/
lemma rdeStep_sound_diffX (hA : (GPoly.toPoly M A).natDegree ≤ δ)
    (hB : (GPoly.toPoly M B).natDegree ≤ δ)
    (lcA lcB : α) (hlcA : M.sem lcA = (GPoly.toPoly M A).coeff δ) (hA0 : M.sem lcA ≠ 0)
    (lower : ℕ → List α → List (List ℚ × α)) (k : ℕ) (f : K)
    (hf : ∀ z : K, (GPoly.toPoly M A).coeff δ * (z′ + DS.sh k * z) + (GPoly.toPoly M B).coeff δ * z =
      (GPoly.toPoly M A).coeff δ * (z′ + f * z))
    (hsound : ∀ ws, ∀ r ∈ lower k ws, (M.sem r.2)′ + f * M.sem r.2 = sQ M r.1 ws)
    (Bs : List (List ℚ × GPoly α)) (hBs : RStageSoundX M DS A B Cl δ (k + 1) Bs) :
    RStageSoundX M DS A B Cl δ k (rdeStep O cst w A B Cl Cl.length δ false lcA lcB lower k Bs) := by
  intro bb hbb
  simp only [rdeStep, Bool.false_eq_true, if_false] at hbb
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hbb
  have hy := hsound _ r hr
  set z := M.sem r.2 with hz
  have hY := toPoly_newElem hcst r.1 Bs k r.2
  refine ⟨length_vcomb _ _ _, fun i hi ↦ ?_, fun d hd ↦ ?_⟩
  · simp only
    rw [hY, coeff_add, finset_sum_coeff, coeff_C_mul_X_pow, if_neg (by omega), add_zero]
    refine Finset.sum_eq_zero fun l hl ↦ ?_
    rw [coeff_C_mul, (hBs _ (getD_mem_BX Bs (Finset.mem_range.mp hl))).2.1 i (by omega), mul_zero]
  · simp only
    rw [hY, resQ_combX, coeff_add, finset_sum_coeff]
    rcases Nat.eq_or_lt_of_le hd with rfl | hlt
    · rw [coeff_Lop_topX DS A B δ hA hB _ k (natDegree_C_mul_X_pow_le z k), coeff_C_mul_X_pow,
        if_pos rfl, hf, hy, sQ, List.length_map, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun l hl ↦ ?_
      rw [NestTower.getD_map' _ _ ([], []) O.zero (Finset.mem_range.mp hl), M.sem_mul, M.sem_inv,
        sem_rkX DS A B Cl hcst w hw, hlcA, coeff_C_mul]
      have hA0' : (GPoly.toPoly M A).coeff δ ≠ 0 := by rw [← hlcA]; exact hA0
      field_simp
      ring
    · rw [coeff_Lop_highX DS A B δ hA hB _ k (natDegree_C_mul_X_pow_le z k) d hlt, add_zero]
      refine Finset.sum_eq_zero fun l hl ↦ ?_
      rw [coeff_C_mul, (hBs _ (getD_mem_BX Bs (Finset.mem_range.mp hl))).2.2 d (by omega), mul_zero]

/-! ### Completeness of the steps -/

variable (hιd : ∀ κ : Cs, (ι κ)′ = 0) (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K))

include hιd in
omit [CharZero Cs] in
lemma Lop_sumKX (N : ℕ) (β : ℕ → Cs) (P : ℕ → K[X]) :
    LopX M DS A B (∑ l ∈ Finset.range N, C (ι (β l)) * P l) =
      ∑ l ∈ Finset.range N, C (ι (β l)) * LopX M DS A B (P l) := by
  simp only [LopX, DzX, map_sum, Derivation.leibniz, implicitDeriv_C, hιd, map_zero, smul_zero,
    add_zero, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  ring

include hιd hιrat in
/-- The constant residual of a combination of basis elements. -/
lemma resC_combX (Bs : List (List ℚ × GPoly α)) (c β : List Cs)
    (hβc : ∀ i, c.getD i 0 = ∑ k ∈ Finset.range Bs.length,
      β.getD k 0 * algebraMap ℚ Cs ((Bs.getD k ([], [])).1.getD i 0)) (Z : K[X]) :
    resCX ι M DS A B Cl c (∑ l ∈ Finset.range Bs.length, C (ι (β.getD l 0)) *
      GPoly.toPoly M (Bs.getD l ([], [])).2 + Z) =
      ∑ l ∈ Finset.range Bs.length, C (ι (β.getD l 0)) *
        resQX M DS A B Cl (Bs.getD l ([], [])).1 (GPoly.toPoly M (Bs.getD l ([], [])).2) +
      LopX M DS A B Z := by
  have hS : ∑ i ∈ Finset.range Cl.length, C (ι (c.getD i 0)) * GPoly.toPoly M (Cl.getD i []) =
      ∑ l ∈ Finset.range Bs.length, C (ι (β.getD l 0)) * SqX M Cl (Bs.getD l ([], [])).1 := by
    simp only [SqX, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hβc i, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_mul, hιrat, C_mul]
    ring
  rw [resCX, show GPoly.toPoly M A * DzX DS (∑ l ∈ Finset.range Bs.length, C (ι (β.getD l 0)) *
      GPoly.toPoly M (Bs.getD l ([], [])).2 + Z) + GPoly.toPoly M B * (∑ l ∈ Finset.range Bs.length,
        C (ι (β.getD l 0)) * GPoly.toPoly M (Bs.getD l ([], [])).2 + Z) =
      LopX M DS A B (∑ l ∈ Finset.range Bs.length, C (ι (β.getD l 0)) *
        GPoly.toPoly M (Bs.getD l ([], [])).2 + Z) from rfl, Lop_addX,
    Lop_sumKX ι DS A B hιd, hS]
  simp only [resQ_eqX, mul_sub, Finset.sum_sub_distrib]
  ring

include hcst hw hιd hιrat in
/-- **The differential step is complete.** -/
lemma rdeStep_complete_diffX (hA : (GPoly.toPoly M A).natDegree ≤ δ)
    (hB : (GPoly.toPoly M B).natDegree ≤ δ)
    (lcA lcB : α) (hlcA : M.sem lcA = (GPoly.toPoly M A).coeff δ) (hA0 : M.sem lcA ≠ 0)
    (lower : ℕ → List α → List (List ℚ × α)) (k : ℕ) (f : K)
    (hf : ∀ z : K, (GPoly.toPoly M A).coeff δ * (z′ + DS.sh k * z) + (GPoly.toPoly M B).coeff δ * z =
      (GPoly.toPoly M A).coeff δ * (z′ + f * z))
    (hspec : RdeSpecK ι M f (lower k)) (N : ℕ) (Bs : List (List ℚ × GPoly α))
    (hBs : RStageSoundX M DS A B Cl δ (k + 1) Bs) (hBc : RStageCompleteX ι M DS A B Cl δ N (k + 1) Bs) :
    RStageCompleteX ι M DS A B Cl δ N k
      (rdeStep O cst w A B Cl Cl.length δ false lcA lcB lower k Bs) := by
  intro c hc Y hYdeg heq
  obtain ⟨β, hβc, hβY⟩ := hBc c hc Y hYdeg (fun d hd ↦ heq d (by omega))
  have hA0' : (GPoly.toPoly M A).coeff δ ≠ 0 := by rw [← hlcA]; exact hA0
  set ws := Bs.map fun bb ↦ O.mul (O.neg ((residE O cst w A B Cl bb).getD (k + δ) O.zero))
    (O.inv lcA) with hws
  set R := lower k ws with hR
  set βt := (List.range Bs.length).map fun l ↦ β.getD l 0 with hβt
  have hβtD : ∀ l < Bs.length, βt.getD l 0 = β.getD l 0 := fun l hl ↦
    NestTower.getD_range_map _ _ hl
  set Z := Y - ∑ l ∈ Finset.range Bs.length, C (ι (β.getD l 0)) *
    GPoly.toPoly M (Bs.getD l ([], [])).2 with hZ
  have hZdeg : Z.natDegree ≤ k := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    have hi' : k + 1 ≤ i := by exact_mod_cast hi
    rw [hZ, coeff_sub, finset_sum_coeff, hβY i hi']
    simp only [coeff_C_mul, sub_self]
  have hYZ : Y = ∑ l ∈ Finset.range Bs.length, C (ι (β.getD l 0)) *
      GPoly.toPoly M (Bs.getD l ([], [])).2 + Z := by rw [hZ]; ring
  -- the equation of degree `k + δ`
  have hz : (Z.coeff k)′ + f * Z.coeff k = sC ι M βt ws := by
    have h1 := heq (k + δ) le_rfl
    rw [hYZ, resC_combX ι DS A B Cl hιd hιrat Bs c β hβc Z, coeff_add,
      coeff_Lop_topX DS A B δ hA hB Z k hZdeg, hf, finset_sum_coeff] at h1
    rw [sC, List.length_map]
    have e : ∀ l ∈ Finset.range Bs.length, ι (βt.getD l 0) * M.sem (ws.getD l O.zero) =
        -(ι (β.getD l 0) * (resQX M DS A B Cl (Bs.getD l ([], [])).1
          (GPoly.toPoly M (Bs.getD l ([], [])).2)).coeff (k + δ)) / (GPoly.toPoly M A).coeff δ := by
      intro l hl
      have hl' := Finset.mem_range.mp hl
      rw [hβtD l hl', hws, NestTower.getD_map' _ _ ([], []) O.zero hl', M.sem_mul, M.sem_inv,
        sem_rkX DS A B Cl hcst w hw, hlcA]
      ring
    rw [Finset.sum_congr rfl e, ← Finset.sum_div, Finset.sum_neg_distrib]
    simp only [coeff_C_mul] at h1
    field_simp
    linear_combination h1
  obtain ⟨γ, hγβ, hγz⟩ := hspec.complete ws βt (fun i hi ↦ by
    rw [List.length_map] at hi
    exact List.getD_eq_default _ _ (by rw [hβt, List.length_map, List.length_range]; exact hi))
    (Z.coeff k) hz
  have hβγ : ∀ l < Bs.length, β.getD l 0 = ∑ j ∈ Finset.range R.length,
      γ.getD j 0 * algebraMap ℚ Cs ((R.getD j ([], O.zero)).1.getD l 0) := fun l hl ↦ by
    rw [← hβtD l hl, hγβ l]
  have hlen : (rdeStep O cst w A B Cl Cl.length δ false lcA lcB lower k Bs).length = R.length := by
    simp [rdeStep, hR, hws]
  have hget : ∀ j < R.length, (rdeStep O cst w A B Cl Cl.length δ false lcA lcB lower k Bs).getD j
      ([], []) = (vcomb Cl.length (R.getD j ([], O.zero)).1 (Bs.map Prod.fst),
        GPoly.add O (lcombGP O cst (R.getD j ([], O.zero)).1 (Bs.map Prod.snd))
          (GPoly.monomial O k (R.getD j ([], O.zero)).2)) := fun j hj ↦ by
    simp only [rdeStep, Bool.false_eq_true, if_false]
    exact NestTower.getD_map' _ _ ([], O.zero) _ hj
  refine ⟨γ, fun i ↦ ?_, fun i hi ↦ ?_⟩
  · rw [hlen]
    have e : ∀ j ∈ Finset.range R.length, γ.getD j 0 * algebraMap ℚ Cs
        (((rdeStep O cst w A B Cl Cl.length δ false lcA lcB lower k Bs).getD j ([], [])).1.getD i 0) =
        γ.getD j 0 * algebraMap ℚ Cs ((vcomb Cl.length (R.getD j ([], O.zero)).1
          (Bs.map Prod.fst)).getD i 0) := fun j hj ↦ by rw [hget j (Finset.mem_range.mp hj)]
    rw [Finset.sum_congr rfl e]
    by_cases hi : i < Cl.length
    · rw [recombine Cl.length Bs.length R.length (fun l i ↦ (Bs.getD l ([], [])).1.getD i 0)
        (fun j l ↦ (R.getD j ([], O.zero)).1.getD l 0) (fun i ↦ c.getD i 0) (fun l ↦ β.getD l 0)
        (fun j ↦ γ.getD j 0) (fun i _ ↦ hβc i) hβγ i hi]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [getD_vcomb, if_pos hi, List.length_map]
      congr 2
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      rw [NestTower.getD_map' _ _ ([], []) [] (Finset.mem_range.mp hl)]
    · rw [hc i (by omega)]
      symm
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [getD_vcomb, if_neg hi, map_zero, mul_zero]
  · rw [hlen]
    have e : ∀ j ∈ Finset.range R.length, ι (γ.getD j 0) * (GPoly.toPoly M
        ((rdeStep O cst w A B Cl Cl.length δ false lcA lcB lower k Bs).getD j ([], [])).2).coeff i =
        ι (γ.getD j 0) * (∑ l ∈ Finset.range Bs.length, (((R.getD j ([], O.zero)).1.getD l 0 : ℚ) : K) *
          (GPoly.toPoly M (Bs.getD l ([], [])).2).coeff i +
            if i = k then M.sem (R.getD j ([], O.zero)).2 else 0) := fun j hj ↦ by
      rw [hget j (Finset.mem_range.mp hj)]
      simp only
      rw [toPoly_newElem hcst, coeff_add, finset_sum_coeff, coeff_C_mul_X_pow]
      simp only [coeff_C_mul]
    rw [Finset.sum_congr rfl e]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    have e2 : ∑ l ∈ Finset.range Bs.length, ∑ j ∈ Finset.range R.length, ι (γ.getD j 0) *
        ((((R.getD j ([], O.zero)).1.getD l 0 : ℚ) : K) * (GPoly.toPoly M (Bs.getD l ([], [])).2).coeff i) =
        ∑ l ∈ Finset.range Bs.length, ι (β.getD l 0) * (GPoly.toPoly M (Bs.getD l ([], [])).2).coeff i := by
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      rw [hβγ l (Finset.mem_range.mp hl), map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_mul, hιrat]
      ring
    rw [e2]
    have hYi : Y.coeff i = ∑ l ∈ Finset.range Bs.length, ι (β.getD l 0) *
        (GPoly.toPoly M (Bs.getD l ([], [])).2).coeff i + Z.coeff i := by
      rw [hYZ, coeff_add, finset_sum_coeff]
      simp only [coeff_C_mul]
    rw [hYi]
    congr 1
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · simp only [if_true, mul_one]
      rw [hγz]
    · simp only [if_neg (show ¬(i = k) by omega), mul_zero, Finset.sum_const_zero]
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hZdeg hlt)

include hcst hw hιd hιrat in
/-- **The algebraic step is complete.** -/
lemma rdeStep_complete_algX (hA : (GPoly.toPoly M A).natDegree ≤ δ)
    (hB : (GPoly.toPoly M B).natDegree ≤ δ) (hAδ : (GPoly.toPoly M A).coeff δ = 0)
    (lcA lcB : α) (hlcB : M.sem lcB = (GPoly.toPoly M B).coeff δ) (hB0 : M.sem lcB ≠ 0)
    (lower : ℕ → List α → List (List ℚ × α)) (k N : ℕ) (Bs : List (List ℚ × GPoly α))
    (hBs : RStageSoundX M DS A B Cl δ (k + 1) Bs) (hBc : RStageCompleteX ι M DS A B Cl δ N (k + 1) Bs) :
    RStageCompleteX ι M DS A B Cl δ N k
      (rdeStep O cst w A B Cl Cl.length δ true lcA lcB lower k Bs) := by
  intro c hc Y hYdeg heq
  obtain ⟨β, hβc, hβY⟩ := hBc c hc Y hYdeg (fun d hd ↦ heq d (by omega))
  have hB0' : (GPoly.toPoly M B).coeff δ ≠ 0 := by rw [← hlcB]; exact hB0
  set Z := Y - ∑ l ∈ Finset.range Bs.length, C (ι (β.getD l 0)) *
    GPoly.toPoly M (Bs.getD l ([], [])).2 with hZ
  have hZdeg : Z.natDegree ≤ k := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    have hi' : k + 1 ≤ i := by exact_mod_cast hi
    rw [hZ, coeff_sub, finset_sum_coeff, hβY i hi']
    simp only [coeff_C_mul, sub_self]
  have hYZ : Y = ∑ l ∈ Finset.range Bs.length, C (ι (β.getD l 0)) *
      GPoly.toPoly M (Bs.getD l ([], [])).2 + Z := by rw [hZ]; ring
  have hZk : Z.coeff k = -(∑ l ∈ Finset.range Bs.length, ι (β.getD l 0) *
      (resQX M DS A B Cl (Bs.getD l ([], [])).1 (GPoly.toPoly M (Bs.getD l ([], [])).2)).coeff (k + δ)) /
        (GPoly.toPoly M B).coeff δ := by
    have h1 := heq (k + δ) le_rfl
    rw [hYZ, resC_combX ι DS A B Cl hιd hιrat Bs c β hβc Z, coeff_add,
      coeff_Lop_topX DS A B δ hA hB Z k hZdeg, hAδ, zero_mul, zero_add, finset_sum_coeff] at h1
    simp only [coeff_C_mul] at h1
    field_simp
    linear_combination h1
  have hlen : (rdeStep O cst w A B Cl Cl.length δ true lcA lcB lower k Bs).length = Bs.length := by
    simp [rdeStep]
  have hget : ∀ l < Bs.length, (rdeStep O cst w A B Cl Cl.length δ true lcA lcB lower k Bs).getD l
      ([], []) = ((Bs.getD l ([], [])).1, GPoly.add O (Bs.getD l ([], [])).2 (GPoly.monomial O k
        (O.mul (O.neg ((residE O cst w A B Cl (Bs.getD l ([], []))).getD (k + δ) O.zero))
          (O.inv lcB)))) := fun l hl ↦ by
    simp only [rdeStep, if_true]
    exact NestTower.getD_map' _ _ ([], []) _ hl
  refine ⟨β, fun i ↦ ?_, fun i hi ↦ ?_⟩
  · rw [hlen, hβc i]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [hget l (Finset.mem_range.mp hl)]
  · rw [hlen]
    have e : ∀ l ∈ Finset.range Bs.length, ι (β.getD l 0) * (GPoly.toPoly M
        ((rdeStep O cst w A B Cl Cl.length δ true lcA lcB lower k Bs).getD l ([], [])).2).coeff i =
        ι (β.getD l 0) * (GPoly.toPoly M (Bs.getD l ([], [])).2).coeff i +
          if i = k then ι (β.getD l 0) * -((resQX M DS A B Cl (Bs.getD l ([], [])).1
            (GPoly.toPoly M (Bs.getD l ([], [])).2)).coeff (k + δ) / (GPoly.toPoly M B).coeff δ)
          else 0 := fun l hl ↦ by
      rw [hget l (Finset.mem_range.mp hl)]
      simp only
      rw [GPoly.toPoly_add, GPoly.toPoly_monomial, coeff_add, coeff_C_mul_X_pow, M.sem_mul,
        M.sem_inv, sem_rkX DS A B Cl hcst w hw, hlcB]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib]
    have hYi : Y.coeff i = ∑ l ∈ Finset.range Bs.length, ι (β.getD l 0) *
        (GPoly.toPoly M (Bs.getD l ([], [])).2).coeff i + Z.coeff i := by
      rw [hYZ, coeff_add, finset_sum_coeff]
      simp only [coeff_C_mul]
    rw [hYi]
    congr 1
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · simp only [if_true]
      rw [hZk, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      ring
    · simp only [if_neg (show ¬(i = k) by omega), Finset.sum_const_zero]
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hZdeg hlt)

/-! ### The initial stage and the loop -/

omit [CharZero Cs] in
lemma rdeInit_soundX (N : ℕ) (hC : ∀ i < Cl.length, (GPoly.toPoly M (Cl.getD i [])).natDegree ≤ N + δ) :
    RStageSoundX M DS A B Cl δ (N + 1) (rdeInit (α := α) Cl.length) := by
  intro bb hbb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hbb
  have hi' := List.mem_range.mp hi
  refine ⟨by simp [unitV], fun j _ ↦ by simp, fun d hd ↦ ?_⟩
  rw [resQ_eqX, coeff_sub, GPoly.toPoly_nil, show LopX M DS A B 0 = 0 by simp [LopX, DzX], coeff_zero,
    zero_sub, SqX, finset_sum_coeff, neg_eq_zero]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  rw [coeff_C_mul, getD_unitV]
  split_ifs with h
  · obtain ⟨-, rfl⟩ := h
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hC j (Finset.mem_range.mp hj)) (by omega)),
      mul_zero]
  · simp

lemma rdeInit_completeX (N : ℕ) : RStageCompleteX ι M DS A B Cl δ N (N + 1) (rdeInit (α := α) Cl.length) := by
  intro c hc Y hYdeg _
  refine ⟨(List.range Cl.length).map fun i ↦ c.getD i 0, fun i ↦ ?_, fun i hi ↦ ?_⟩
  · simp only [rdeInit, List.length_map, List.length_range]
    have e : ∀ k ∈ Finset.range Cl.length, ((List.range Cl.length).map fun i ↦ c.getD i 0).getD k 0 *
        algebraMap ℚ Cs ((((List.range Cl.length).map fun i ↦ ((unitV Cl.length i, []) :
          List ℚ × GPoly α)).getD k ([], [])).1.getD i 0) =
        if i = k then (if i < Cl.length then c.getD i 0 else 0) else 0 := fun k hk ↦ by
      have hk' := Finset.mem_range.mp hk
      rw [NestTower.getD_range_map _ _ hk', NestTower.getD_range_map _ _ hk', getD_unitV]
      by_cases hik : i = k
      · subst hik; simp [hk']
      · simp [hik]
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq]
    by_cases hi : i < Cl.length
    · simp [hi]
    · simp only [Finset.mem_range, hi, if_false]
      exact hc i (by omega)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    symm
    refine Finset.sum_eq_zero fun l hl ↦ ?_
    have hl' : l < Cl.length := by simpa [rdeInit] using hl
    rw [show (rdeInit (α := α) Cl.length).getD l ([], []) = (unitV Cl.length l, []) from
      NestTower.getD_range_map _ _ hl']
    simp

include hcst hw hιd hιrat in
/-- **The loop**: from stage `j` to stage `0`. -/
lemma rdeLoop_stageX (hA : (GPoly.toPoly M A).natDegree ≤ δ)
    (hB : (GPoly.toPoly M B).natDegree ≤ δ) (alg : Bool) (lcA lcB : α)
    (lower : ℕ → List α → List (List ℚ × α))
    (halg : alg = true → (GPoly.toPoly M A).coeff δ = 0 ∧
      M.sem lcB = (GPoly.toPoly M B).coeff δ ∧ M.sem lcB ≠ 0)
    (hdiff : alg = false → M.sem lcA = (GPoly.toPoly M A).coeff δ ∧ M.sem lcA ≠ 0 ∧
      ∀ k : ℕ, ∃ f : K, (∀ z : K, (GPoly.toPoly M A).coeff δ * (z′ + DS.sh k * z) +
        (GPoly.toPoly M B).coeff δ * z = (GPoly.toPoly M A).coeff δ * (z′ + f * z)) ∧
        RdeSpecK ι M f (lower k))
    (N : ℕ) : ∀ (j : ℕ) (Bs : List (List ℚ × GPoly α)), RStageSoundX M DS A B Cl δ j Bs →
      RStageCompleteX ι M DS A B Cl δ N j Bs →
      RStageSoundX M DS A B Cl δ 0 (rdeLoop O cst w A B Cl Cl.length δ alg lcA lcB lower j Bs) ∧
        RStageCompleteX ι M DS A B Cl δ N 0
          (rdeLoop O cst w A B Cl Cl.length δ alg lcA lcB lower j Bs)
  | 0, Bs, hs, hc => ⟨hs, hc⟩
  | j + 1, Bs, hs, hc => by
    cases alg with
    | true =>
      obtain ⟨hAδ, hlcB, hB0⟩ := halg rfl
      exact rdeLoop_stageX hA hB true lcA lcB lower halg hdiff N j _
        (rdeStep_sound_algX DS A B Cl δ hcst w hw hA hB hAδ lcA lcB hlcB hB0 lower j Bs hs)
        (rdeStep_complete_algX ι DS A B Cl δ hcst w hw hιd hιrat hA hB hAδ lcA lcB hlcB hB0 lower
          j N Bs hs hc)
    | false =>
      obtain ⟨hlcA, hA0, hf⟩ := hdiff rfl
      obtain ⟨f, hff, hspec⟩ := hf j
      exact rdeLoop_stageX hA hB false lcA lcB lower halg hdiff N j _
        (rdeStep_sound_diffX DS A B Cl δ hcst w hw hA hB lcA lcB hlcA hA0 lower j f hff hspec.sound
          Bs hs)
        (rdeStep_complete_diffX ι DS A B Cl δ hcst w hw hιd hιrat hA hB lcA lcB hlcA hA0 lower j f hff
          hspec N Bs hs hc)

end Generic

end Tower.NestX
