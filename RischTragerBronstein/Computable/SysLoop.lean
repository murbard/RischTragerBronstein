import RischTragerBronstein.Computable.NestMRdeLoop

/-!
# Coupled Risch systems: the operator `A Y′ + B Y` on vectors of polynomials

For a differential field `K`, an exponential monomial (`t′ = b t`, derivation `Dz` of `K[t]`), and
polynomial matrices `A B : Fin n → Fin n → K[t]`, the operator `LopV A B Y = A Y′ + B Y` on
`Y : Fin n → K[t]`. For `deg A, deg B ≤ δ` and `deg Y ≤ k`, its coefficient of degree `k + δ` is
`lc(A) (Yₖ′ + k b Yₖ) + lc(B) Yₖ` (`coeff_LopV_top`), and it has no higher coefficients
(`coeff_LopV_high`): the basis of the coefficient loop for systems.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

open Tower.NestM Tower.NestP

variable {K : Type*} [Field K] [Differential K] [CharZero K]
variable (w0 b : K) {n : ℕ} (A B : Fin n → Fin n → K[X])

/-- The derivation of `K[t]` with `t′ = w0 + b t` (logarithm: `b = 0`; exponential: `w0 = 0`). -/
noncomputable abbrev DzL (P : K[X]) : K[X] := implicitDeriv (C w0 + C b * X) P

lemma coeff_DzL (P : K[X]) (k : ℕ) :
    (DzL w0 b P).coeff k = (P.coeff k)′ + k * b * P.coeff k + w0 * ((k + 1 : ℕ) * P.coeff (k + 1)) := by
  have h1 : (C b * X * derivative P).coeff k = b * (k * P.coeff k) := by
    rw [mul_assoc, coeff_C_mul]
    cases k with
    | zero => simp
    | succ j => rw [coeff_X_mul, coeff_derivative]; push_cast; ring
  have h2 : (C w0 * derivative P).coeff k = w0 * ((k + 1 : ℕ) * P.coeff (k + 1)) := by
    rw [coeff_C_mul, coeff_derivative]; push_cast; ring
  simp only [DzL, implicitDeriv, Derivation.coe_add, Derivation.coe_smul, Pi.add_apply,
    Pi.smul_apply, Derivation.restrictScalars_apply, derivative'_apply, smul_eq_mul, coeff_add,
    coeff_mapCoeffs, add_mul, coeff_add, h1, h2]
  ring

lemma natDegree_DzL_le (Z : K[X]) (k : ℕ) (hZ : Z.natDegree ≤ k) : (DzL w0 b Z).natDegree ≤ k := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  have hi' : Z.natDegree < i := lt_of_le_of_lt hZ (by exact_mod_cast hi)
  rw [coeff_DzL, coeff_eq_zero_of_natDegree_lt hi',
    coeff_eq_zero_of_natDegree_lt (show Z.natDegree < i + 1 by omega)]
  simp

lemma coeff_DzL_top (Z : K[X]) (k : ℕ) (hZ : Z.natDegree ≤ k) :
    (DzL w0 b Z).coeff k = (Z.coeff k)′ + k * b * Z.coeff k := by
  rw [coeff_DzL, coeff_eq_zero_of_natDegree_lt (show Z.natDegree < k + 1 by omega)]
  simp

/-- **The operator** `A Y′ + B Y` on vectors. -/
noncomputable def LopV (Y : Fin n → K[X]) : Fin n → K[X] :=
  fun i ↦ ∑ j, (A i j * DzL w0 b (Y j) + B i j * Y j)

lemma LopV_add (Y Z : Fin n → K[X]) : LopV w0 b A B (Y + Z) = LopV w0 b A B Y + LopV w0 b A B Z := by
  funext i
  simp only [LopV, Pi.add_apply, map_add, mul_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- The coefficient of degree `k + δ` of `A Y′ + B Y` for `deg Y ≤ k`. -/
lemma coeff_LopV_top (δ : ℕ) (hA : ∀ i j, (A i j).natDegree ≤ δ) (hB : ∀ i j, (B i j).natDegree ≤ δ)
    (Y : Fin n → K[X]) (k : ℕ) (hY : ∀ j, (Y j).natDegree ≤ k) (i : Fin n) :
    (LopV w0 b A B Y i).coeff (k + δ) = ∑ j, ((A i j).coeff δ * (((Y j).coeff k)′ + k * b * (Y j).coeff k) +
      (B i j).coeff δ * (Y j).coeff k) := by
  rw [LopV, finset_sum_coeff]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [coeff_add, add_comm k δ, coeff_mul_add_eq_of_natDegree_le (hA i j)
    (natDegree_DzL_le w0 b (Y j) k (hY j)), coeff_mul_add_eq_of_natDegree_le (hB i j) (hY j),
    coeff_DzL_top w0 b (Y j) k (hY j)]

/-- No coefficients above `k + δ`. -/
lemma coeff_LopV_high (δ : ℕ) (hA : ∀ i j, (A i j).natDegree ≤ δ) (hB : ∀ i j, (B i j).natDegree ≤ δ)
    (Y : Fin n → K[X]) (k : ℕ) (hY : ∀ j, (Y j).natDegree ≤ k) (i : Fin n) (d : ℕ) (hd : k + δ < d) :
    (LopV w0 b A B Y i).coeff d = 0 := by
  rw [LopV, finset_sum_coeff]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [coeff_add]
  have h1 : (A i j * DzL w0 b (Y j)).natDegree < d :=
    lt_of_le_of_lt (natDegree_mul_le.trans (add_le_add (hA i j) (natDegree_DzL_le w0 b (Y j) k (hY j))))
      (by omega)
  have h2 : (B i j * Y j).natDegree < d :=
    lt_of_le_of_lt (natDegree_mul_le.trans (add_le_add (hB i j) (hY j))) (by omega)
  rw [coeff_eq_zero_of_natDegree_lt h1, coeff_eq_zero_of_natDegree_lt h2, add_zero]

/-! ### The right-hand sides and the residual -/

variable (Cl : List (Fin n → K[X]))

/-- `∑ eₗ Cₗ` for rational `e`. -/
noncomputable def SqV (e : List ℚ) : Fin n → K[X] :=
  fun i ↦ ∑ l ∈ Finset.range Cl.length, C ((e.getD l 0 : ℚ) : K) * (Cl.getD l 0) i

/-- The residual `A Y′ + B Y − ∑ eₗ Cₗ`. -/
noncomputable def resQV (e : List ℚ) (Y : Fin n → K[X]) : Fin n → K[X] :=
  LopV w0 b A B Y - SqV Cl e

lemma resQV_add (e : List ℚ) (Y Z : Fin n → K[X]) :
    resQV w0 b A B Cl e (Y + Z) = resQV w0 b A B Cl e Y + LopV w0 b A B Z := by
  rw [resQV, resQV, LopV_add]; abel

lemma Dz_C_rat (q : ℚ) (P : K[X]) : DzL w0 b (C ((q : ℚ) : K) * P) = C ((q : ℚ) : K) * DzL w0 b P := by
  rw [DzL, Derivation.leibniz, implicitDeriv_C, Tower.NestP.deriv_ratCastK q]
  simp

lemma LopV_smul_rat (q : ℚ) (Y : Fin n → K[X]) :
    LopV w0 b A B (fun i ↦ C ((q : ℚ) : K) * Y i) = fun i ↦ C ((q : ℚ) : K) * LopV w0 b A B Y i := by
  funext i
  simp only [LopV, Dz_C_rat, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

lemma LopV_sum (N : ℕ) (q : ℕ → ℚ) (P : ℕ → Fin n → K[X]) :
    LopV w0 b A B (fun i ↦ ∑ l ∈ Finset.range N, C ((q l : ℚ) : K) * P l i) =
      fun i ↦ ∑ l ∈ Finset.range N, C ((q l : ℚ) : K) * LopV w0 b A B (P l) i := by
  induction N with
  | zero =>
    funext i
    simp [LopV]
  | succ N ih =>
    have e : (fun i ↦ ∑ l ∈ Finset.range (N + 1), C ((q l : ℚ) : K) * P l i) =
        (fun i ↦ ∑ l ∈ Finset.range N, C ((q l : ℚ) : K) * P l i) +
          fun i ↦ C ((q N : ℚ) : K) * P N i := by
      funext i; simp [Finset.sum_range_succ]
    rw [e, LopV_add, ih, LopV_smul_rat]
    funext i
    simp [Finset.sum_range_succ]

lemma SqV_vcomb (Bs : List (List ℚ)) (r : List ℚ) :
    SqV Cl (vcomb Cl.length r Bs) =
      fun i ↦ ∑ l ∈ Finset.range Bs.length, C ((r.getD l 0 : ℚ) : K) * SqV Cl (Bs.getD l []) i := by
  funext i
  simp only [SqV, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ll hll ↦ ?_
  rw [getD_vcomb, if_pos (Finset.mem_range.mp hll)]
  push_cast
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [C_mul]
  ring

/-- **The residual of a combination.** -/
lemma resQV_comb (Bs : List (List ℚ × (Fin n → K[X]))) (r : List ℚ) (Z : Fin n → K[X]) :
    resQV w0 b A B Cl (vcomb Cl.length r (Bs.map Prod.fst))
      ((fun i ↦ ∑ l ∈ Finset.range Bs.length, C ((r.getD l 0 : ℚ) : K) * (Bs.getD l ([], 0)).2 i)
        + Z) =
      (fun i ↦ ∑ l ∈ Finset.range Bs.length, C ((r.getD l 0 : ℚ) : K) *
        resQV w0 b A B Cl (Bs.getD l ([], 0)).1 (Bs.getD l ([], 0)).2 i) + LopV w0 b A B Z := by
  rw [resQV, LopV_add, LopV_sum w0 b A B Bs.length (fun l ↦ r.getD l 0) (fun l ↦ (Bs.getD l ([], 0)).2),
    SqV_vcomb, List.length_map]
  funext i
  simp only [resQV, Pi.add_apply, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have e : ∀ l ∈ Finset.range Bs.length, C ((r.getD l 0 : ℚ) : K) *
      SqV Cl ((Bs.map Prod.fst).getD l []) i = C ((r.getD l 0 : ℚ) : K) *
      SqV Cl (Bs.getD l ([], 0)).1 i := fun l hl ↦ by
    rw [NestTower.getD_map' _ _ ([], 0) [] (Finset.mem_range.mp hl)]
  rw [Finset.sum_congr rfl e]
  ring

/-! ### The coefficient loop -/

/-- Matrix times vector over `K`. -/
def mv (P : Fin n → Fin n → K) (v : Fin n → K) : Fin n → K := fun i ↦ ∑ j, P i j * v j

variable (δ : ℕ)

/-- Stage `j`, soundness: the basis vanishes below `j` and satisfies the equations of degree
`≥ j + δ`. -/
def SStageSound (j : ℕ) (Bs : List (List ℚ × (Fin n → K[X]))) : Prop :=
  ∀ bb ∈ Bs, bb.1.length = Cl.length ∧ (∀ i, ∀ m < j, (bb.2 i).coeff m = 0) ∧
    ∀ d, j + δ ≤ d → ∀ i, (resQV w0 b A B Cl bb.1 bb.2 i).coeff d = 0

/-- The new unknowns' right-hand side at degree `k + δ`. -/
noncomputable def rkV (k : ℕ) (bb : List ℚ × (Fin n → K[X])) : Fin n → K :=
  fun i ↦ -(resQV w0 b A B Cl bb.1 bb.2 i).coeff (k + δ)

/-- The new basis from the solutions `R` of the system one level down. -/
noncomputable def sStepR (k : ℕ) (R : List (List ℚ × (Fin n → K)))
    (Bs : List (List ℚ × (Fin n → K[X]))) : List (List ℚ × (Fin n → K[X])) :=
  R.map fun r ↦
    (vcomb Cl.length r.1 (Bs.map Prod.fst),
      (fun i ↦ ∑ l ∈ Finset.range Bs.length, C ((r.1.getD l 0 : ℚ) : K) * (Bs.getD l ([], 0)).2 i) +
        fun i ↦ C (r.2 i) * X ^ k)

/-- **One step** at degree `k + δ`: algebraic (`Yₖ = lc(B)⁻¹ r`) or a system one level down. -/
noncomputable def sStep (alg : Bool) (PA PB : Fin n → Fin n → K)
    (lower : ℕ → List (Fin n → K) → List (List ℚ × (Fin n → K))) (k : ℕ)
    (Bs : List (List ℚ × (Fin n → K[X]))) : List (List ℚ × (Fin n → K[X])) :=
  if alg then
    Bs.map fun bb ↦ (bb.1, bb.2 + fun i ↦ C (mv PB (rkV w0 b A B Cl δ k bb) i) * X ^ k)
  else
    sStepR Cl k (lower k (Bs.map fun bb ↦ mv PA (rkV w0 b A B Cl δ k bb))) Bs

lemma getD_mem_BV (Bs : List (List ℚ × (Fin n → K[X]))) {l : ℕ} (hl : l < Bs.length) :
    Bs.getD l ([], 0) ∈ Bs := by
  rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem _

/-- **The algebraic step is sound.** -/
lemma sStep_sound_alg (hA : ∀ i j, (A i j).natDegree ≤ δ) (hB : ∀ i j, (B i j).natDegree ≤ δ)
    (hAδ : ∀ i j, (A i j).coeff δ = 0) (PA PB : Fin n → Fin n → K)
    (hPB : ∀ v, mv (fun i j ↦ (B i j).coeff δ) (mv PB v) = v)
    (lower : ℕ → List (Fin n → K) → List (List ℚ × (Fin n → K))) (k : ℕ)
    (Bs : List (List ℚ × (Fin n → K[X]))) (hBs : SStageSound w0 b A B Cl δ (k + 1) Bs) :
    SStageSound w0 b A B Cl δ k (sStep w0 b A B Cl δ true PA PB lower k Bs) := by
  intro bb hbb
  simp only [sStep, if_true] at hbb
  obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hbb
  obtain ⟨hl, hlow, hres⟩ := hBs b0 hb0
  set q := mv PB (rkV w0 b A B Cl δ k b0) with hq
  have hZ : ∀ j, (C (q j) * X ^ k : K[X]).natDegree ≤ k := fun j ↦ natDegree_C_mul_X_pow_le _ _
  refine ⟨hl, fun i m hm ↦ ?_, fun d hd i ↦ ?_⟩
  · simp only [Pi.add_apply, coeff_add, hlow i m (by omega), coeff_C_mul_X_pow]
    rw [if_neg (by omega)]; simp
  · rw [resQV_add, Pi.add_apply, coeff_add]
    rcases Nat.eq_or_lt_of_le hd with rfl | hlt
    · rw [coeff_LopV_top w0 b A B δ hA hB _ k hZ i]
      simp only [coeff_C_mul_X_pow, if_true, hAδ, zero_mul, zero_add]
      have h1 := congrFun (hPB (rkV w0 b A B Cl δ k b0)) i
      simp only [mv] at h1
      rw [show (∑ j, (B i j).coeff δ * q j) = rkV w0 b A B Cl δ k b0 i from h1]
      simp [rkV]
    · rw [hres d (by omega), coeff_LopV_high w0 b A B δ hA hB _ k hZ i d hlt, add_zero]

/-- **The differential step is sound** (for any list `R` of solutions one level down). -/
lemma sStepR_sound_diff (hA : ∀ i j, (A i j).natDegree ≤ δ) (hB : ∀ i j, (B i j).natDegree ≤ δ)
    (PA : Fin n → Fin n → K) (hPA : ∀ v, mv (fun i j ↦ (A i j).coeff δ) (mv PA v) = v)
    (k : ℕ) (F : Fin n → Fin n → K)
    (hf : ∀ z : Fin n → K, ∀ i, ∑ j, ((A i j).coeff δ * ((z j)′ + k * b * z j) + (B i j).coeff δ * z j) =
      ∑ j, (A i j).coeff δ * ((z j)′ + mv F z j))
    (Bs : List (List ℚ × (Fin n → K[X]))) (R : List (List ℚ × (Fin n → K)))
    (hsoundR : ∀ r ∈ R, ∀ i, (r.2 i)′ + mv F r.2 i =
      ∑ l ∈ Finset.range (Bs.map fun bb ↦ mv PA (rkV w0 b A B Cl δ k bb)).length,
        ((r.1.getD l 0 : ℚ) : K) * ((Bs.map fun bb ↦ mv PA (rkV w0 b A B Cl δ k bb)).getD l 0) i)
    (hBs : SStageSound w0 b A B Cl δ (k + 1) Bs) :
    SStageSound w0 b A B Cl δ k (sStepR Cl k R Bs) := by
  intro bb hbb
  simp only [sStepR] at hbb
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hbb
  have hy := hsoundR r hr
  set z := r.2 with hz
  have hZ : ∀ j, (C (z j) * X ^ k : K[X]).natDegree ≤ k := fun j ↦ natDegree_C_mul_X_pow_le _ _
  refine ⟨length_vcomb _ _ _, fun i m hm ↦ ?_, fun d hd i ↦ ?_⟩
  · simp only [Pi.add_apply, coeff_add, finset_sum_coeff, coeff_C_mul_X_pow]
    rw [if_neg (by omega), add_zero]
    refine Finset.sum_eq_zero fun l hl ↦ ?_
    rw [coeff_C_mul, (hBs _ (getD_mem_BV Bs (Finset.mem_range.mp hl))).2.1 i m (by omega), mul_zero]
  · rw [resQV_comb, Pi.add_apply, coeff_add, finset_sum_coeff]
    rcases Nat.eq_or_lt_of_le hd with rfl | hlt
    · rw [coeff_LopV_top w0 b A B δ hA hB _ k hZ i]
      simp only [coeff_C_mul_X_pow, if_true]
      rw [hf z i]
      simp only [hy, List.length_map]
      -- `lc(A) (∑ r_l PA rk_l) = ∑ r_l rk_l`
      have hlin : ∀ i, ∑ j, (A i j).coeff δ * ∑ l ∈ Finset.range Bs.length,
          ((r.1.getD l 0 : ℚ) : K) * ((Bs.map fun bb ↦ mv PA (rkV w0 b A B Cl δ k bb)).getD l 0) j =
          ∑ l ∈ Finset.range Bs.length, ((r.1.getD l 0 : ℚ) : K) *
            rkV w0 b A B Cl δ k (Bs.getD l ([], 0)) i := by
        intro i
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l hl ↦ ?_
        rw [NestTower.getD_map' _ _ ([], 0) 0 (Finset.mem_range.mp hl)]
        have h1 := congrFun (hPA (rkV w0 b A B Cl δ k (Bs.getD l ([], 0)))) i
        simp only [mv] at h1
        rw [← h1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ by simp only [mv]; ring
      rw [hlin i]
      simp only [coeff_C_mul, rkV]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun l _ ↦ ?_
      push_cast
      ring
    · rw [coeff_LopV_high w0 b A B δ hA hB _ k hZ i d hlt, add_zero]
      refine Finset.sum_eq_zero fun l hl ↦ ?_
      rw [coeff_C_mul, (hBs _ (getD_mem_BV Bs (Finset.mem_range.mp hl))).2.2 d (by omega) i,
        mul_zero]

/-- **The differential step is sound.** -/
lemma sStep_sound_diff (hA : ∀ i j, (A i j).natDegree ≤ δ) (hB : ∀ i j, (B i j).natDegree ≤ δ)
    (PA PB : Fin n → Fin n → K) (hPA : ∀ v, mv (fun i j ↦ (A i j).coeff δ) (mv PA v) = v)
    (lower : ℕ → List (Fin n → K) → List (List ℚ × (Fin n → K))) (k : ℕ) (F : Fin n → Fin n → K)
    (hf : ∀ z : Fin n → K, ∀ i, ∑ j, ((A i j).coeff δ * ((z j)′ + k * b * z j) + (B i j).coeff δ * z j) =
      ∑ j, (A i j).coeff δ * ((z j)′ + mv F z j))
    (hsound : ∀ ws, ∀ r ∈ lower k ws, ∀ i, (r.2 i)′ + mv F r.2 i =
      ∑ l ∈ Finset.range ws.length, ((r.1.getD l 0 : ℚ) : K) * (ws.getD l 0) i)
    (Bs : List (List ℚ × (Fin n → K[X]))) (hBs : SStageSound w0 b A B Cl δ (k + 1) Bs) :
    SStageSound w0 b A B Cl δ k (sStep w0 b A B Cl δ false PA PB lower k Bs) :=
  sStepR_sound_diff w0 b A B Cl δ hA hB PA hPA k F hf Bs _ (fun r hr ↦ hsound _ r hr) hBs

/-! ### Completeness -/

section Complete

variable {Cs : Type*} [Field Cs] [CharZero Cs] (ι : Cs →+* K)

/-- The residual with constant coefficients `c`. -/
noncomputable def resCV (c : List Cs) (Y : Fin n → K[X]) : Fin n → K[X] :=
  LopV w0 b A B Y - fun i ↦ ∑ l ∈ Finset.range Cl.length, C (ι (c.getD l 0)) * (Cl.getD l 0) i

/-- Stage `j`, completeness: the basis spans (over the constants) all solutions of the equations
of degree `≥ j + δ` on the coefficients of degree `≥ j`. -/
def SStageComplete (N j : ℕ) (Bs : List (List ℚ × (Fin n → K[X]))) : Prop :=
  ∀ c : List Cs, (∀ l, Cl.length ≤ l → c.getD l 0 = 0) → ∀ Y : Fin n → K[X],
    (∀ i, (Y i).natDegree ≤ N) → (∀ d, j + δ ≤ d → ∀ i, (resCV w0 b A B Cl ι c Y i).coeff d = 0) →
    ∃ β : List Cs,
      (∀ l, c.getD l 0 = ∑ k ∈ Finset.range Bs.length,
        β.getD k 0 * algebraMap ℚ Cs ((Bs.getD k ([], 0)).1.getD l 0)) ∧
      ∀ i, ∀ m, j ≤ m → (Y i).coeff m = ∑ l ∈ Finset.range Bs.length,
        ι (β.getD l 0) * ((Bs.getD l ([], 0)).2 i).coeff m

/-- **The specification of a system solver** `z′ + F z = ∑ βₗ wₗ` one level down. -/
structure SysSpecK (F : Fin n → Fin n → K) (lowerk : List (Fin n → K) → List (List ℚ × (Fin n → K))) :
    Prop where
  sound : ∀ ws, ∀ r ∈ lowerk ws, ∀ i, (r.2 i)′ + mv F r.2 i =
    ∑ l ∈ Finset.range ws.length, ((r.1.getD l 0 : ℚ) : K) * (ws.getD l 0) i
  complete : ∀ ws (c : List Cs), (∀ l, ws.length ≤ l → c.getD l 0 = 0) → ∀ z : Fin n → K,
    (∀ i, (z i)′ + mv F z i = ∑ l ∈ Finset.range ws.length, ι (c.getD l 0) * (ws.getD l 0) i) →
    ∃ β : List Cs,
      (∀ l, c.getD l 0 = ∑ k ∈ Finset.range (lowerk ws).length,
        β.getD k 0 * algebraMap ℚ Cs (((lowerk ws).getD k ([], 0)).1.getD l 0)) ∧
      ∀ i, z i = ∑ k ∈ Finset.range (lowerk ws).length,
        ι (β.getD k 0) * ((lowerk ws).getD k ([], 0)).2 i

variable (hιd : ∀ κ : Cs, (ι κ)′ = 0) (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K))

include hιd in
lemma LopV_sumK (N : ℕ) (β : ℕ → Cs) (P : ℕ → Fin n → K[X]) :
    LopV w0 b A B (fun i ↦ ∑ l ∈ Finset.range N, C (ι (β l)) * P l i) =
      fun i ↦ ∑ l ∈ Finset.range N, C (ι (β l)) * LopV w0 b A B (P l) i := by
  funext i
  simp only [LopV, DzL, map_sum, Derivation.leibniz, implicitDeriv_C, hιd, map_zero, smul_zero,
    add_zero, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  ring

include hιd hιrat in
/-- The constant residual of a combination of basis elements. -/
lemma resCV_comb (Bs : List (List ℚ × (Fin n → K[X]))) (c β : List Cs)
    (hβc : ∀ l, c.getD l 0 = ∑ k ∈ Finset.range Bs.length,
      β.getD k 0 * algebraMap ℚ Cs ((Bs.getD k ([], 0)).1.getD l 0)) (Z : Fin n → K[X]) :
    resCV w0 b A B Cl ι c ((fun i ↦ ∑ l ∈ Finset.range Bs.length, C (ι (β.getD l 0)) *
      (Bs.getD l ([], 0)).2 i) + Z) =
      (fun i ↦ ∑ l ∈ Finset.range Bs.length, C (ι (β.getD l 0)) *
        resQV w0 b A B Cl (Bs.getD l ([], 0)).1 (Bs.getD l ([], 0)).2 i) + LopV w0 b A B Z := by
  have hS : ∀ i, ∑ l ∈ Finset.range Cl.length, C (ι (c.getD l 0)) * (Cl.getD l 0) i =
      ∑ k ∈ Finset.range Bs.length, C (ι (β.getD k 0)) * SqV Cl (Bs.getD k ([], 0)).1 i := by
    intro i
    simp only [SqV, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [hβc l, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, hιrat, C_mul]
    ring
  rw [resCV, LopV_add, LopV_sumK w0 b A B ι hιd]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, hS, resQV, mul_sub, Finset.sum_sub_distrib]
  ring

lemma mv_sum (P : Fin n → Fin n → K) (N : ℕ) (a : ℕ → K) (v : ℕ → Fin n → K) :
    mv P (fun i ↦ ∑ l ∈ Finset.range N, a l * v l i) = fun i ↦ ∑ l ∈ Finset.range N, a l * mv P (v l) i := by
  funext i
  simp only [mv, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

include hιd hιrat in
/-- **The algebraic step is complete.** -/
lemma sStep_complete_alg (hA : ∀ i j, (A i j).natDegree ≤ δ) (hB : ∀ i j, (B i j).natDegree ≤ δ)
    (hAδ : ∀ i j, (A i j).coeff δ = 0) (PA PB : Fin n → Fin n → K)
    (hPBl : ∀ v, mv PB (mv (fun i j ↦ (B i j).coeff δ) v) = v)
    (lower : ℕ → List (Fin n → K) → List (List ℚ × (Fin n → K))) (k N : ℕ)
    (Bs : List (List ℚ × (Fin n → K[X]))) (hBc : SStageComplete w0 b A B Cl δ ι N (k + 1) Bs) :
    SStageComplete w0 b A B Cl δ ι N k (sStep w0 b A B Cl δ true PA PB lower k Bs) := by
  intro c hc Y hYdeg heq
  obtain ⟨β, hβc, hβY⟩ := hBc c hc Y hYdeg (fun d hd i ↦ heq d (by omega) i)
  set S : Fin n → K[X] := fun i ↦ ∑ l ∈ Finset.range Bs.length, C (ι (β.getD l 0)) *
    (Bs.getD l ([], 0)).2 i with hS
  set Z : Fin n → K[X] := Y - S with hZ
  have hZdeg : ∀ i, (Z i).natDegree ≤ k := fun i ↦ by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    have hm' : k + 1 ≤ m := by exact_mod_cast hm
    simp only [hZ, hS, Pi.sub_apply, coeff_sub, finset_sum_coeff, coeff_C_mul]
    rw [hβY i m hm', sub_self]
  have hYZ : Y = S + Z := by rw [hZ]; abel
  -- the top equations
  have hzk : ∀ i, ∑ j, (B i j).coeff δ * (Z j).coeff k =
      ∑ l ∈ Finset.range Bs.length, ι (β.getD l 0) * rkV w0 b A B Cl δ k (Bs.getD l ([], 0)) i := by
    intro i
    have h1 := heq (k + δ) le_rfl i
    rw [hYZ, resCV_comb w0 b A B Cl ι hιd hιrat Bs c β hβc Z, Pi.add_apply, coeff_add,
      coeff_LopV_top w0 b A B δ hA hB Z k hZdeg i, finset_sum_coeff] at h1
    simp only [hAδ, zero_mul, zero_add, coeff_C_mul] at h1
    simp only [rkV, mul_neg, Finset.sum_neg_distrib]
    linear_combination h1
  have hzv : (fun j ↦ (Z j).coeff k) = fun i ↦ ∑ l ∈ Finset.range Bs.length, ι (β.getD l 0) *
      mv PB (rkV w0 b A B Cl δ k (Bs.getD l ([], 0))) i := by
    rw [← mv_sum, ← hPBl (fun j ↦ (Z j).coeff k)]
    congr 1
    funext i
    exact hzk i
  have hlen : (sStep w0 b A B Cl δ true PA PB lower k Bs).length = Bs.length := by simp [sStep]
  have hget : ∀ l < Bs.length, (sStep w0 b A B Cl δ true PA PB lower k Bs).getD l ([], 0) =
      ((Bs.getD l ([], 0)).1, (Bs.getD l ([], 0)).2 +
        fun i ↦ C (mv PB (rkV w0 b A B Cl δ k (Bs.getD l ([], 0))) i) * X ^ k) := fun l hl ↦ by
    simp only [sStep, if_true]
    exact NestTower.getD_map' _ _ ([], 0) _ hl
  refine ⟨β, fun l ↦ ?_, fun i m hm ↦ ?_⟩
  · rw [hlen, hβc l]
    refine Finset.sum_congr rfl fun k' hk' ↦ ?_
    rw [hget k' (Finset.mem_range.mp hk')]
  · rw [hlen]
    have e : ∀ l ∈ Finset.range Bs.length, ι (β.getD l 0) *
        (((sStep w0 b A B Cl δ true PA PB lower k Bs).getD l ([], 0)).2 i).coeff m =
        ι (β.getD l 0) * ((Bs.getD l ([], 0)).2 i).coeff m +
          if m = k then ι (β.getD l 0) * mv PB (rkV w0 b A B Cl δ k (Bs.getD l ([], 0))) i else 0 :=
      fun l hl ↦ by
        rw [hget l (Finset.mem_range.mp hl)]
        simp only [Pi.add_apply, coeff_add, coeff_C_mul_X_pow]
        split_ifs <;> ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib]
    have hYi : (Y i).coeff m = ∑ l ∈ Finset.range Bs.length, ι (β.getD l 0) *
        ((Bs.getD l ([], 0)).2 i).coeff m + (Z i).coeff m := by
      rw [hYZ, Pi.add_apply, coeff_add, hS, finset_sum_coeff]
      simp only [coeff_C_mul]
    rw [hYi]
    congr 1
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · simp only [if_true]
      exact congrFun hzv i
    · simp only [if_neg (show ¬(m = k) by omega), Finset.sum_const_zero]
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hZdeg i) hlt)

include hιd hιrat in
/-- **The differential step is complete** (for any list `R` complete one level down). -/
lemma sStepR_complete_diff (hA : ∀ i j, (A i j).natDegree ≤ δ) (hB : ∀ i j, (B i j).natDegree ≤ δ)
    (PA : Fin n → Fin n → K) (hPAl : ∀ v, mv PA (mv (fun i j ↦ (A i j).coeff δ) v) = v)
    (k : ℕ) (F : Fin n → Fin n → K)
    (hf : ∀ z : Fin n → K, ∀ i, ∑ j, ((A i j).coeff δ * ((z j)′ + k * b * z j) + (B i j).coeff δ * z j) =
      ∑ j, (A i j).coeff δ * ((z j)′ + mv F z j))
    (N : ℕ) (Bs : List (List ℚ × (Fin n → K[X]))) (R : List (List ℚ × (Fin n → K)))
    (hcompR : ∀ c : List Cs,
      (∀ l, (Bs.map fun bb ↦ mv PA (rkV w0 b A B Cl δ k bb)).length ≤ l → c.getD l 0 = 0) →
      ∀ z : Fin n → K, (∀ i, (z i)′ + mv F z i =
        ∑ l ∈ Finset.range (Bs.map fun bb ↦ mv PA (rkV w0 b A B Cl δ k bb)).length,
          ι (c.getD l 0) * ((Bs.map fun bb ↦ mv PA (rkV w0 b A B Cl δ k bb)).getD l 0) i) →
      ∃ β : List Cs,
        (∀ l, c.getD l 0 = ∑ k ∈ Finset.range R.length,
          β.getD k 0 * algebraMap ℚ Cs ((R.getD k ([], 0)).1.getD l 0)) ∧
        ∀ i, z i = ∑ k ∈ Finset.range R.length, ι (β.getD k 0) * (R.getD k ([], 0)).2 i)
    (hBc : SStageComplete w0 b A B Cl δ ι N (k + 1) Bs) :
    SStageComplete w0 b A B Cl δ ι N k (sStepR Cl k R Bs) := by
  intro c hc Y hYdeg heq
  obtain ⟨β, hβc, hβY⟩ := hBc c hc Y hYdeg (fun d hd i ↦ heq d (by omega) i)
  set S : Fin n → K[X] := fun i ↦ ∑ l ∈ Finset.range Bs.length, C (ι (β.getD l 0)) *
    (Bs.getD l ([], 0)).2 i with hS
  set Z : Fin n → K[X] := Y - S with hZ
  have hZdeg : ∀ i, (Z i).natDegree ≤ k := fun i ↦ by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    have hm' : k + 1 ≤ m := by exact_mod_cast hm
    simp only [hZ, hS, Pi.sub_apply, coeff_sub, finset_sum_coeff, coeff_C_mul]
    rw [hβY i m hm', sub_self]
  have hYZ : Y = S + Z := by rw [hZ]; abel
  set ws := Bs.map fun bb ↦ mv PA (rkV w0 b A B Cl δ k bb) with hws
  set βt := (List.range Bs.length).map fun l ↦ β.getD l 0 with hβt
  have hβtD : ∀ l < Bs.length, βt.getD l 0 = β.getD l 0 := fun l hl ↦
    NestTower.getD_range_map _ _ hl
  set zk : Fin n → K := fun j ↦ (Z j).coeff k with hzk
  -- the top equations
  have hlcA : ∀ i, ∑ j, (A i j).coeff δ * ((zk j)′ + mv F zk j) =
      ∑ l ∈ Finset.range Bs.length, ι (β.getD l 0) * rkV w0 b A B Cl δ k (Bs.getD l ([], 0)) i := by
    intro i
    have h1 := heq (k + δ) le_rfl i
    rw [hYZ, resCV_comb w0 b A B Cl ι hιd hιrat Bs c β hβc Z, Pi.add_apply, coeff_add,
      coeff_LopV_top w0 b A B δ hA hB Z k hZdeg i, finset_sum_coeff, hf zk i] at h1
    simp only [coeff_C_mul] at h1
    simp only [rkV, mul_neg, Finset.sum_neg_distrib]
    linear_combination h1
  have hz : ∀ i, (zk i)′ + mv F zk i =
      ∑ l ∈ Finset.range ws.length, ι (βt.getD l 0) * (ws.getD l 0) i := by
    have hu := hPAl (fun j ↦ (zk j)′ + mv F zk j)
    have e1 : mv (fun i j ↦ (A i j).coeff δ) (fun j ↦ (zk j)′ + mv F zk j) =
        fun i ↦ ∑ l ∈ Finset.range Bs.length, ι (β.getD l 0) *
          rkV w0 b A B Cl δ k (Bs.getD l ([], 0)) i := funext hlcA
    rw [e1, mv_sum] at hu
    intro i
    have := congrFun hu i
    rw [← this, List.length_map]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [hβtD l (Finset.mem_range.mp hl), hws, NestTower.getD_map' _ _ ([], 0) 0 (Finset.mem_range.mp hl)]
  obtain ⟨γ, hγβ, hγz⟩ := hcompR βt (fun l hl ↦ by
    rw [List.length_map] at hl
    exact List.getD_eq_default _ _ (by rw [hβt, List.length_map, List.length_range]; exact hl))
    zk hz
  have hβγ : ∀ l < Bs.length, β.getD l 0 = ∑ j ∈ Finset.range R.length,
      γ.getD j 0 * algebraMap ℚ Cs ((R.getD j ([], 0)).1.getD l 0) := fun l hl ↦ by
    rw [← hβtD l hl, hγβ l]
  have hlen : (sStepR Cl k R Bs).length = R.length := by
    simp [sStepR]
  have hget : ∀ j < R.length, (sStepR Cl k R Bs).getD j ([], 0) =
      (vcomb Cl.length (R.getD j ([], 0)).1 (Bs.map Prod.fst),
        (fun i ↦ ∑ l ∈ Finset.range Bs.length, C (((R.getD j ([], 0)).1.getD l 0 : ℚ) : K) *
          (Bs.getD l ([], 0)).2 i) + fun i ↦ C ((R.getD j ([], 0)).2 i) * X ^ k) := fun j hj ↦ by
    simp only [sStepR]
    exact NestTower.getD_map' _ _ ([], 0) _ hj
  refine ⟨γ, fun l ↦ ?_, fun i m hm ↦ ?_⟩
  · rw [hlen]
    have e : ∀ j ∈ Finset.range R.length, γ.getD j 0 * algebraMap ℚ Cs
        (((sStepR Cl k R Bs).getD j ([], 0)).1.getD l 0) =
        γ.getD j 0 * algebraMap ℚ Cs ((vcomb Cl.length (R.getD j ([], 0)).1
          (Bs.map Prod.fst)).getD l 0) := fun j hj ↦ by rw [hget j (Finset.mem_range.mp hj)]
    rw [Finset.sum_congr rfl e]
    by_cases hl : l < Cl.length
    · rw [recombine Cl.length Bs.length R.length (fun l i ↦ (Bs.getD l ([], 0)).1.getD i 0)
        (fun j l ↦ (R.getD j ([], 0)).1.getD l 0) (fun i ↦ c.getD i 0) (fun l ↦ β.getD l 0)
        (fun j ↦ γ.getD j 0) (fun i _ ↦ hβc i) hβγ l hl]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [getD_vcomb, if_pos hl, List.length_map]
      congr 2
      refine Finset.sum_congr rfl fun l' hl' ↦ ?_
      rw [NestTower.getD_map' _ _ ([], 0) [] (Finset.mem_range.mp hl')]
    · rw [hc l (by omega)]
      symm
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [getD_vcomb, if_neg hl, map_zero, mul_zero]
  · rw [hlen]
    have e : ∀ j ∈ Finset.range R.length, ι (γ.getD j 0) *
        (((sStepR Cl k R Bs).getD j ([], 0)).2 i).coeff m =
        ι (γ.getD j 0) * (∑ l ∈ Finset.range Bs.length, (((R.getD j ([], 0)).1.getD l 0 : ℚ) : K) *
          ((Bs.getD l ([], 0)).2 i).coeff m + if m = k then (R.getD j ([], 0)).2 i else 0) :=
      fun j hj ↦ by
        rw [hget j (Finset.mem_range.mp hj)]
        simp only [Pi.add_apply, coeff_add, finset_sum_coeff, coeff_C_mul, coeff_X_pow]
        split_ifs <;> ring
    rw [Finset.sum_congr rfl e]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    have e2 : ∑ l ∈ Finset.range Bs.length, ∑ j ∈ Finset.range R.length, ι (γ.getD j 0) *
        ((((R.getD j ([], 0)).1.getD l 0 : ℚ) : K) * ((Bs.getD l ([], 0)).2 i).coeff m) =
        ∑ l ∈ Finset.range Bs.length, ι (β.getD l 0) * ((Bs.getD l ([], 0)).2 i).coeff m := by
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      rw [hβγ l (Finset.mem_range.mp hl), map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_mul, hιrat]
      ring
    rw [e2]
    have hYi : (Y i).coeff m = ∑ l ∈ Finset.range Bs.length, ι (β.getD l 0) *
        ((Bs.getD l ([], 0)).2 i).coeff m + (Z i).coeff m := by
      rw [hYZ, Pi.add_apply, coeff_add, hS, finset_sum_coeff]
      simp only [coeff_C_mul]
    rw [hYi]
    congr 1
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · simp only [if_true, mul_one]
      exact hγz i
    · simp only [if_neg (show ¬(m = k) by omega), mul_zero, Finset.sum_const_zero]
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hZdeg i) hlt)

include hιd hιrat in
/-- **The differential step is complete.** -/
lemma sStep_complete_diff (hA : ∀ i j, (A i j).natDegree ≤ δ) (hB : ∀ i j, (B i j).natDegree ≤ δ)
    (PA PB : Fin n → Fin n → K) (hPAl : ∀ v, mv PA (mv (fun i j ↦ (A i j).coeff δ) v) = v)
    (lower : ℕ → List (Fin n → K) → List (List ℚ × (Fin n → K))) (k : ℕ) (F : Fin n → Fin n → K)
    (hf : ∀ z : Fin n → K, ∀ i, ∑ j, ((A i j).coeff δ * ((z j)′ + k * b * z j) + (B i j).coeff δ * z j) =
      ∑ j, (A i j).coeff δ * ((z j)′ + mv F z j))
    (hspec : SysSpecK ι F (lower k)) (N : ℕ) (Bs : List (List ℚ × (Fin n → K[X])))
    (hBc : SStageComplete w0 b A B Cl δ ι N (k + 1) Bs) :
    SStageComplete w0 b A B Cl δ ι N k (sStep w0 b A B Cl δ false PA PB lower k Bs) :=
  sStepR_complete_diff w0 b A B Cl δ ι hιd hιrat hA hB PA hPAl k F hf N Bs _
    (fun c hc z hz ↦ hspec.complete _ c hc z hz) hBc

end Complete

/-! ### The initial stage and the loop -/

/-- The initial basis `(eₗ, 0)`. -/
noncomputable def sInit (L : ℕ) : List (List ℚ × (Fin n → K[X])) :=
  (List.range L).map fun l ↦ (unitV L l, 0)

lemma sInit_sound (N : ℕ) (hC : ∀ l < Cl.length, ∀ i, ((Cl.getD l 0) i).natDegree ≤ N + δ) :
    SStageSound w0 b A B Cl δ (N + 1) (sInit Cl.length) := by
  intro bb hbb
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hbb
  have hl' := List.mem_range.mp hl
  refine ⟨by simp [unitV], fun i m _ ↦ by simp, fun d hd i ↦ ?_⟩
  have h0 : LopV w0 b A B (0 : Fin n → K[X]) = 0 := by funext i; simp [LopV, DzL]
  simp only [resQV, h0, zero_sub, Pi.neg_apply, coeff_neg, SqV, finset_sum_coeff, neg_eq_zero]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  rw [coeff_C_mul, getD_unitV]
  split_ifs with h
  · obtain ⟨-, rfl⟩ := h
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hC j (Finset.mem_range.mp hj) i) (by omega)),
      mul_zero]
  · simp

lemma sInit_complete {Cs : Type*} [Field Cs] [CharZero Cs] (ι : Cs →+* K) (N : ℕ) :
    SStageComplete w0 b A B Cl δ ι N (N + 1) (sInit Cl.length) := by
  intro c hc Y hYdeg _
  refine ⟨(List.range Cl.length).map fun i ↦ c.getD i 0, fun i ↦ ?_, fun i m hm ↦ ?_⟩
  · simp only [sInit, List.length_map, List.length_range]
    have e : ∀ k ∈ Finset.range Cl.length, ((List.range Cl.length).map fun i ↦ c.getD i 0).getD k 0 *
        algebraMap ℚ Cs ((((List.range Cl.length).map fun i ↦ ((unitV Cl.length i, 0) :
          List ℚ × (Fin n → K[X]))).getD k ([], 0)).1.getD i 0) =
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
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hYdeg i) (by omega))]
    symm
    refine Finset.sum_eq_zero fun l hl ↦ ?_
    have hl' : l < Cl.length := by simpa [sInit] using hl
    rw [show (sInit (n := n) (K := K) Cl.length).getD l ([], 0) = (unitV Cl.length l, 0) from
      NestTower.getD_range_map _ _ hl']
    simp

/-- **The coefficient loop** for systems, `k = N, …, 0`. -/
noncomputable def sLoop (alg : Bool) (PA PB : Fin n → Fin n → K)
    (lower : ℕ → List (Fin n → K) → List (List ℚ × (Fin n → K))) :
    ℕ → List (List ℚ × (Fin n → K[X])) → List (List ℚ × (Fin n → K[X]))
  | 0, Bs => Bs
  | k + 1, Bs => sLoop alg PA PB lower k (sStep w0 b A B Cl δ alg PA PB lower k Bs)

section LoopThm

variable {Cs : Type*} [Field Cs] [CharZero Cs] (ι : Cs →+* K)
  (hιd : ∀ κ : Cs, (ι κ)′ = 0) (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K))

include hιd hιrat in
/-- **The loop for systems**: from stage `j` to stage `0`, when the leading matrices are
invertible (`PB` two-sided inverse of `lc B` in the algebraic case, `PA` of `lc A` otherwise). -/
lemma sLoop_stage (hA : ∀ i j, (A i j).natDegree ≤ δ) (hB : ∀ i j, (B i j).natDegree ≤ δ)
    (alg : Bool) (PA PB : Fin n → Fin n → K)
    (lower : ℕ → List (Fin n → K) → List (List ℚ × (Fin n → K)))
    (halg : alg = true → (∀ i j, (A i j).coeff δ = 0) ∧
      (∀ v, mv (fun i j ↦ (B i j).coeff δ) (mv PB v) = v) ∧
      (∀ v, mv PB (mv (fun i j ↦ (B i j).coeff δ) v) = v))
    (hdiff : alg = false → (∀ v, mv (fun i j ↦ (A i j).coeff δ) (mv PA v) = v) ∧
      (∀ v, mv PA (mv (fun i j ↦ (A i j).coeff δ) v) = v) ∧
      ∀ k : ℕ, ∃ F : Fin n → Fin n → K, (∀ z : Fin n → K, ∀ i,
        ∑ j, ((A i j).coeff δ * ((z j)′ + k * b * z j) + (B i j).coeff δ * z j) =
          ∑ j, (A i j).coeff δ * ((z j)′ + mv F z j)) ∧ SysSpecK ι F (lower k))
    (N : ℕ) : ∀ (j : ℕ) (Bs : List (List ℚ × (Fin n → K[X]))), SStageSound w0 b A B Cl δ j Bs →
      SStageComplete w0 b A B Cl δ ι N j Bs →
      SStageSound w0 b A B Cl δ 0 (sLoop w0 b A B Cl δ alg PA PB lower j Bs) ∧
        SStageComplete w0 b A B Cl δ ι N 0 (sLoop w0 b A B Cl δ alg PA PB lower j Bs)
  | 0, Bs, hs, hc => ⟨hs, hc⟩
  | j + 1, Bs, hs, hc => by
    cases alg with
    | true =>
      obtain ⟨hAδ, hPB, hPBl⟩ := halg rfl
      exact sLoop_stage hA hB true PA PB lower halg hdiff N j _
        (sStep_sound_alg w0 b A B Cl δ hA hB hAδ PA PB hPB lower j Bs hs)
        (sStep_complete_alg w0 b A B Cl δ ι hιd hιrat hA hB hAδ PA PB hPBl lower j N Bs hc)
    | false =>
      obtain ⟨hPA, hPAl, hf⟩ := hdiff rfl
      obtain ⟨F, hff, hspec⟩ := hf j
      exact sLoop_stage hA hB false PA PB lower halg hdiff N j _
        (sStep_sound_diff w0 b A B Cl δ hA hB PA PB hPA lower j F hff hspec.sound Bs hs)
        (sStep_complete_diff w0 b A B Cl δ ι hιd hιrat hA hB PA PB hPAl lower j F hff hspec N Bs hc)

end LoopThm

end Tower.Sys
