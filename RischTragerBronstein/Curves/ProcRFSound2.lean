import RischTragerBronstein.Curves.ProcRFSound1

/-!
# What the validity check guarantees

`ValidFacts P` collects the semantic consequences of `P.valid = true` (`valid_spec`): the curve
equation is monic of degree `n` (also after inversion), the coefficient degree bounds, the branch
certificates, the covering of the special points, and the precision conditions.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Facts

variable {F : Type*} [Field F] [DecidableEq F]

lemma natDegree_toPoly_le_length (c : CPoly F) : (toPoly c).natDegree ≤ c.length - 1 :=
  natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ by
    have : c.length - 1 < i := by exact_mod_cast hi
    rw [coeff_toPoly, List.getD_eq_default _ _ (by omega)]

/-- A list of coefficients with length `n + 1` and last entry `[1]` is monic of degree `n`. -/
lemma monic_toB_of (W : BPoly F) (n : ℕ) (hl : W.length = n + 1) (hlast : W.getD n [] = [1]) :
    (toB W).Monic ∧ (toB W).natDegree = n := by
  have hc : (toB W).coeff n = 1 := by
    rw [coeff_toB, hlast]; simp [toPoly]
  have hle : (toB W).natDegree ≤ n := natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ by
    have : n < i := by exact_mod_cast hi
    rw [coeff_toB, List.getD_eq_default _ _ (by omega), toPoly_nil]
  have hdeg : (toB W).natDegree = n :=
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hc]; exact one_ne_zero))
  exact ⟨by rw [Monic, leadingCoeff, hdeg, hc], hdeg⟩

namespace CurveProb

variable (P : CurveProb F)

/-- The semantic content of `P.valid`. -/
structure ValidFacts : Prop where
  n_pos : 0 < P.n
  mon : (toB P.Fc).Monic
  deg : (toB P.Fc).natDegree = P.n
  mon' : (toB (invB P.Fc P.k (P.k * P.n))).Monic
  deg' : (toB (invB P.Fc P.k (P.k * P.n))).natDegree = P.n
  okF : InvOK P.k (P.k * P.n) 0 P.Fc
  kF : ∀ j, (toPoly (P.Fc.getD j [])).natDegree ≤ P.k
  infN : 0 < P.inf.N
  certs : ∀ ac ∈ P.pts, certCheck P.Fc P.n ac.1 ac.2 = true
  certInf : certCheck (invB P.Fc P.k (P.k * P.n)) P.n 0 P.inf = true
  D0 : toPoly P.D ≠ 0
  cover : coverCheck (mul P.D (discRC P.Fc P.n P.k)) (P.pts.map Prod.fst) = true
  prec : ∀ ac ∈ P.pts, P.muFin ac.1 ac.2.N < ac.2.prec ∧
    P.mufFin ac.1 ac.2.N < ac.2.prec + ac.2.N ∧
    P.muFin ac.1 ac.2.N < (P.QFin ac.1 ac.2.N).length ∧
    P.mufFin ac.1 ac.2.N < (P.QfFin ac.1 ac.2.N).length
  sb : -P.sbInf ≤ P.inf.prec
  sf : (P.inf.N : ℤ) - P.sfInf < P.inf.prec
  R0l : 0 < (trim P.R0).length
  Dl : 0 < (trim P.D).length
  okA : InvOK P.k P.DA 0 P.A
  len : P.Fc.length = P.n + 1
  last : P.Fc.getD P.n [] = [1]

lemma mem_basisIdx {ie : ℕ × ℕ} (h : ie ∈ P.basisIdx) : ie.1 < P.n ∧ ie.2 ≤ P.E := by
  simp only [basisIdx, List.mem_flatMap, List.mem_range, List.mem_map] at h
  obtain ⟨i, hi, e, he, rfl⟩ := h
  exact ⟨hi, by omega⟩

lemma okB (hn : 0 < P.n) (b : ℕ) (hb : b < P.basisIdx.length) :
    InvOK P.k P.DWb 0 (basisB (F := F) (P.basisIdx.getD b (0, 0)).1 (P.basisIdx.getD b (0, 0)).2) := by
  have hm := P.mem_basisIdx (ie := P.basisIdx.getD b (0, 0))
    (by rw [List.getD_eq_getElem _ _ hb]; exact List.getElem_mem hb)
  set i := (P.basisIdx.getD b (0, 0)).1
  set e := (P.basisIdx.getD b (0, 0)).2
  intro j hj
  simp only [basisB, List.length_append, List.length_replicate, List.length_singleton] at hj
  have hk : P.k * j ≤ P.k * (P.n - 1) := Nat.mul_le_mul_left _ (by omega)
  simp only [DWb, zero_add]
  by_cases hji : j < i
  · rw [basisB, List.getD_append _ _ _ _ (by simpa using hji), List.getD_replicate]
    · simp; omega
    · simpa using hji
  · have hj' : j = i := by omega
    subst hj'
    rw [basisB, List.getD_append_right _ _ _ _ (by simp), List.length_replicate, Nat.sub_self]
    simp only [List.getD_cons_zero, xPowC, List.length_append, List.length_replicate,
      List.length_singleton]
    omega

/-- **The validity check is sound.** -/
theorem valid_spec (h : P.valid = true) : P.ValidFacts := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true', Bool.eq_false_iff, and_assoc] at h
  obtain ⟨hn, hl, hlast, hl', hlast', hok, hkF, hN, hcerts, hcinf, hD, hcov, hprec, hsb, hsf, hR0,
    hD0, hA⟩ := h
  obtain ⟨hmon, hdeg⟩ := monic_toB_of P.Fc P.n hl hlast
  obtain ⟨hmon', hdeg'⟩ := monic_toB_of _ P.n hl' hlast'
  refine ⟨hn, hmon, hdeg, hmon', hdeg', fun j hj ↦ by simpa using hok j hj, fun j ↦ ?_, hN,
    hcerts, hcinf, fun h0 ↦ hD ((isZero_iff _).mpr h0), hcov, fun ac hac ↦ ?_, hsb, hsf, hR0,
    hD0, fun j hj ↦ by simpa using hA j hj, hl, hlast⟩
  · refine (natDegree_toPoly_le_length _).trans ?_
    by_cases hj : j < P.Fc.length
    · have := hkF j hj; omega
    · rw [List.getD_eq_default _ _ (by omega)]; simp
  · exact hprec ac hac

end CurveProb

end Facts

end Curves
