import RischTragerBronstein.Torsion.BaseChange
import RischTragerBronstein.Curves.CoverComplete

/-!
# Validity of a problem after base change

`CurveProb.valid` mixes conditions on the problem (shape of `F`, of the integrand, `D ≠ 0`,
`disc · D ≠ 0`) with conditions on the certificates (branch data, cover, precisions).
`CurveProb.shapeOK` collects the first kind. **`shapeOK_baseChange`**: they survive every base
change `φ : F → F'`; **`valid_of_shapeOK`**: with the certificate conditions they give `valid`.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Shape

variable {F : Type*} [Field F] [DecidableEq F]

/-- The conditions of `valid` on the problem itself. -/
def CurveProb.shapeOK (P : CurveProb F) : Bool :=
  decide (0 < P.n) && decide (P.Fc.length = P.n + 1) && decide (P.Fc.getD P.n [] = [1]) &&
  decide ((invB P.Fc P.k (P.k * P.n)).length = P.n + 1) &&
  decide ((invB P.Fc P.k (P.k * P.n)).getD P.n [] = [1]) &&
  (List.range P.Fc.length).all (fun j ↦ decide ((P.Fc.getD j []).length + P.k * j ≤ P.k * P.n + 1)) &&
  (List.range P.Fc.length).all (fun j ↦ decide ((P.Fc.getD j []).length ≤ P.k + 1)) &&
  !isZero P.D && decide (0 < (trim P.R0).length) && decide (0 < (trim P.D).length) &&
  (List.range P.A.length).all (fun j ↦ decide ((P.A.getD j []).length + P.k * j ≤ P.DA + 1))

/-- **`valid` from the shape and the certificate conditions.** -/
theorem valid_of_shapeOK (P : CurveProb F) (hS : P.shapeOK = true) (hinfN : 0 < P.inf.N)
    (hpts : ∀ ac ∈ P.pts, certCheck P.Fc P.n ac.1 ac.2 = true)
    (hinf : certCheck (invB P.Fc P.k (P.k * P.n)) P.n 0 P.inf = true)
    (hcov : coverCheck (mul P.D (discRC P.Fc P.n P.k)) (P.pts.map Prod.fst) = true)
    (hmu : ∀ ac ∈ P.pts, P.muFin ac.1 ac.2.N < ac.2.prec ∧ P.mufFin ac.1 ac.2.N < ac.2.prec + ac.2.N ∧
      P.muFin ac.1 ac.2.N < (P.QFin ac.1 ac.2.N).length ∧
      P.mufFin ac.1 ac.2.N < (P.QfFin ac.1 ac.2.N).length)
    (hinfp : -P.sbInf ≤ P.inf.prec ∧ (P.inf.N : ℤ) - P.sfInf < P.inf.prec) :
    P.valid = true := by
  simp only [CurveProb.shapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hS
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := hS
  simp only [CurveProb.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩,
    hinfN⟩, hpts⟩, hinf⟩, h8⟩, hcov⟩, fun ac hac ↦ ?_⟩, hinfp.1⟩, hinfp.2⟩, h9⟩, h10⟩, h11⟩
  obtain ⟨m1, m2, m3, m4⟩ := hmu ac hac
  exact ⟨⟨⟨m1, m2⟩, m3⟩, m4⟩

/-- `valid` contains the shape conditions. -/
lemma shapeOK_of_valid (P : CurveProb F) (h : P.valid = true) : P.shapeOK = true := by
  simp only [CurveProb.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, -⟩, -⟩, -⟩, h8⟩, -⟩, -⟩, -⟩, -⟩, h9⟩, h10⟩,
    h11⟩ := h
  simp only [CurveProb.shapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩

/-- The certificate conditions of `valid`. -/
lemma certs_of_valid (P : CurveProb F) (h : P.valid = true) :
    0 < P.inf.N ∧ (∀ ac ∈ P.pts, certCheck P.Fc P.n ac.1 ac.2 = true) ∧
    certCheck (invB P.Fc P.k (P.k * P.n)) P.n 0 P.inf = true ∧
    coverCheck (mul P.D (discRC P.Fc P.n P.k)) (P.pts.map Prod.fst) = true ∧
    (∀ ac ∈ P.pts, P.muFin ac.1 ac.2.N < ac.2.prec ∧ P.mufFin ac.1 ac.2.N < ac.2.prec + ac.2.N ∧
      P.muFin ac.1 ac.2.N < (P.QFin ac.1 ac.2.N).length ∧
      P.mufFin ac.1 ac.2.N < (P.QfFin ac.1 ac.2.N).length) ∧
    (-P.sbInf ≤ P.inf.prec ∧ (P.inf.N : ℤ) - P.sfInf < P.inf.prec) := by
  simp only [CurveProb.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hN⟩, hpts⟩, hinf⟩, -⟩, hcov⟩, hmu⟩, hi1⟩, hi2⟩,
    -⟩, -⟩, -⟩ := h
  refine ⟨hN, hpts, hinf, hcov, fun ac hac ↦ ?_, hi1, hi2⟩
  have := hmu ac hac
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

end Shape

section Map

variable {F : Type*} [Field F] [DecidableEq F] {F' : Type*} [Field F'] [DecidableEq F']
  (φ : F →+* F')

lemma reflectC_map (M : ℕ) (P : CPoly F) : reflectC M (P.map φ) = (reflectC M P).map φ := by
  simp only [reflectC, List.map_ofFn]
  congr 1
  funext j
  simp only [Function.comp_apply]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases P[M - (j : ℕ)]? <;> simp

lemma invBAux_map (k D : ℕ) : ∀ (i : ℕ) (W : BPoly F),
    invBAux k D i (W.map (·.map φ)) = (invBAux k D i W).map (·.map φ)
  | _, [] => rfl
  | i, c :: W => by
    simp only [List.map_cons, invBAux, reflectC_map, invBAux_map k D (i + 1) W]

lemma invB_map (W : BPoly F) (k D : ℕ) :
    invB (W.map (·.map φ)) k D = (invB W k D).map (·.map φ) := invBAux_map φ k D 0 W

lemma isZero_map (P : CPoly F) : isZero (P.map φ) = isZero P := by
  rw [Bool.eq_iff_iff, isZero_iff, isZero_iff, toPoly_mapHom,
    Polynomial.map_eq_zero_iff φ.injective]

lemma trim_length_pos_map (P : CPoly F) :
    0 < (trim (P.map φ)).length ↔ 0 < (trim P).length := by
  rw [List.length_pos_iff, List.length_pos_iff, ne_eq, ne_eq, trim_eq_nil_iff, trim_eq_nil_iff,
    toPoly_mapHom, Polynomial.map_eq_zero_iff φ.injective]

lemma degT_map (P : CPoly F) : degT (P.map φ) = degT P := by
  rw [degT_eq, degT_eq, toPoly_mapHom, natDegree_map_eq_of_injective φ.injective]

lemma getD_map_list {α β : Type*} (f : α → β) (l : List α) (d : α) (j : ℕ) :
    (l.map f).getD j (f d) = f (l.getD j d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> rfl

lemma getD_mapL (W : BPoly F) (j : ℕ) : (W.map (·.map φ)).getD j [] = (W.getD j []).map φ :=
  getD_map_list (·.map φ) W [] j

/-- The shape of `F` gives the hypotheses of `toPoly_discRC`. -/
lemma shape_monic (Fc : BPoly F) (n k : ℕ) (hl : Fc.length = n + 1) (hlead : Fc.getD n [] = [1])
    (hk : ∀ j < Fc.length, (Fc.getD j []).length ≤ k + 1) :
    (toB Fc).Monic ∧ (toB Fc).natDegree = n ∧ ∀ i, ((toB Fc).coeff i).natDegree ≤ k := by
  have hcn : (toB Fc).coeff n = 1 := by rw [coeff_toB, hlead]; simp
  have hdeg : (toB Fc).natDegree = n := by
    refine natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [hcn]; exact one_ne_zero)
    refine natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ ?_
    rw [coeff_toB, List.getD_eq_default _ _ (by have : n < i := (by exact_mod_cast hi); omega)]
    simp
  refine ⟨?_, hdeg, fun i ↦ ?_⟩
  · rw [Monic, leadingCoeff, hdeg, hcn]
  · rw [coeff_toB]
    by_cases hi : i < Fc.length
    · have := natDegree_toPoly_lt_length (Fc.getD i []) 
      by_cases h0 : toPoly (Fc.getD i []) = 0
      · rw [h0, natDegree_zero]; exact Nat.zero_le _
      · have := this h0; have := hk i hi; omega
    · rw [List.getD_eq_default _ _ (by omega)]; simp

/-- `discRC` commutes with base change (through its meaning, the discriminant). -/
lemma toPoly_discRC_map [CharZero F] [CharZero F'] (Fc : BPoly F) (n k : ℕ) (hmon : (toB Fc).Monic)
    (hn : (toB Fc).natDegree = n) (hk : ∀ i, ((toB Fc).coeff i).natDegree ≤ k) :
    toPoly (discRC (Fc.map (·.map φ)) n k) = (toPoly (discRC Fc n k)).map φ := by
  have hB : toB (Fc.map (·.map φ)) = (toB Fc).map (mapRingHom φ) := toB_mapL φ Fc
  have hmon' : (toB (Fc.map (·.map φ))).Monic := by rw [hB]; exact hmon.map _
  have hn' : (toB (Fc.map (·.map φ))).natDegree = n := by rw [hB, hmon.natDegree_map, hn]
  have hk' : ∀ i, ((toB (Fc.map (·.map φ))).coeff i).natDegree ≤ k := fun i ↦ by
    rw [hB, coeff_map, coe_mapRingHom]
    exact (natDegree_map_le).trans (hk i)
  rw [toPoly_discRC _ n k hmon' hn' hk', toPoly_discRC _ n k hmon hn hk, hB,
    Polynomial.derivative_map, resultant_map_map, coe_mapRingHom]

/-- **The shape survives base change.** -/
theorem shapeOK_baseChange [CharZero F] [CharZero F'] (P0 : CurveProb F) (hS : P0.shapeOK = true)
    (pts : List (F' × BranchCert F')) (inf : BranchCert F') :
    (P0.baseChange φ P0.k pts inf).shapeOK = true := by
  have hS' := hS
  simp only [CurveProb.shapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true'] at hS'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := hS'
  obtain ⟨hmon, hn, hk⟩ := shape_monic P0.Fc P0.n P0.k h2 h3 h7
  have hR0 : toPoly (P0.baseChange φ P0.k pts inf).R0 = (toPoly P0.R0).map φ := by
    simp only [CurveProb.R0, CurveProb.baseChange, toPoly_trim, CPoly.toPoly_mul, Polynomial.map_mul,
      toPoly_mapHom, toPoly_discRC_map φ P0.Fc P0.n P0.k hmon hn hk]
  have hDA : (P0.baseChange φ P0.k pts inf).DA = P0.DA := by
    simp only [CurveProb.DA, CurveProb.baseChange, List.length_map, getD_mapL, degT_map]
  simp only [CurveProb.shapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, ?_⟩, ?_⟩, ?_⟩, ?_⟩, fun j hj ↦ ?_⟩, fun j hj ↦ ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    fun j hj ↦ ?_⟩
  · simp [CurveProb.baseChange, h2]
  · simp only [CurveProb.baseChange]; rw [getD_mapL, h3]; simp
  · simp only [CurveProb.baseChange]; rw [invB_map, List.length_map, h4]
  · simp only [CurveProb.baseChange]; rw [invB_map, getD_mapL, h5]; simp
  · simp only [CurveProb.baseChange, List.length_map] at hj ⊢
    rw [getD_mapL, List.length_map]; exact h6 j hj
  · simp only [CurveProb.baseChange, List.length_map] at hj ⊢
    rw [getD_mapL, List.length_map]; exact h7 j hj
  · simp only [CurveProb.baseChange]; rw [isZero_map]; exact h8
  · rw [List.length_pos_iff, ne_eq, trim_eq_nil_iff, hR0, Polynomial.map_eq_zero_iff φ.injective,
      ← trim_eq_nil_iff, ← ne_eq, ← List.length_pos_iff]
    exact h9
  · simp only [CurveProb.baseChange]; rw [trim_length_pos_map]; exact h10
  · rw [hDA]
    simp only [CurveProb.baseChange, List.length_map] at hj ⊢
    rw [getD_mapL, List.length_map]; exact h11 j hj

/-- `R0` after base change. -/
lemma toPoly_R0_baseChange [CharZero F] [CharZero F'] (P0 : CurveProb F) (hS : P0.shapeOK = true)
    (pts : List (F' × BranchCert F')) (inf : BranchCert F') :
    toPoly (P0.baseChange φ P0.k pts inf).R0 = (toPoly P0.R0).map φ := by
  simp only [CurveProb.shapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true'] at hS
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, h2⟩, h3⟩, -⟩, -⟩, -⟩, h7⟩, -⟩, -⟩, -⟩, -⟩ := hS
  obtain ⟨hmon, hn, hk⟩ := shape_monic P0.Fc P0.n P0.k h2 h3 h7
  simp only [CurveProb.R0, CurveProb.baseChange, toPoly_trim, CPoly.toPoly_mul, Polynomial.map_mul,
    toPoly_mapHom, toPoly_discRC_map φ P0.Fc P0.n P0.k hmon hn hk]

end Map

section Ord

variable {F : Type*} [Field F] [DecidableEq F]

/-- `ordC` is the order of vanishing at `0`. -/
lemma ordC_eq_natTrailingDegree (P : CPoly F) (h : toPoly P ≠ 0) :
    ordC P = (toPoly P).natTrailingDegree := by
  refine ordC_eq_of (fun i hi ↦ ?_) ?_
  · rw [← coeff_toPoly]; exact coeff_eq_zero_of_lt_natTrailingDegree hi
  · rw [← coeff_toPoly]; exact trailingCoeff_nonzero_iff_nonzero.mpr h

lemma ordC_lt_length (P : CPoly F) (h : toPoly P ≠ 0) : ordC P < P.length := by
  by_contra hle
  push Not at hle
  apply h
  refine Polynomial.ext fun i ↦ ?_
  rw [coeff_toPoly, coeff_zero]
  by_cases hi : i < ordC P
  · exact getD_lt_ordC P i hi
  · exact List.getD_eq_default _ _ (by omega)

lemma toPoly_compC_shiftC (R : CPoly F) (a : F) (N : ℕ) :
    toPoly (compC R (shiftC a N)) = (toPoly R).comp (Polynomial.C a + X ^ N) := by
  rw [toPoly_compC, toPoly_shiftC]

end Ord

end Curves
