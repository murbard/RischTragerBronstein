import RischTragerBronstein.Mixed.KX0NonConstSide
import RischTragerBronstein.Mixed.KXConstComplete

/-!
# The level-`0` structural checks pass on non-constant data

`kxChkT0_true_nc` / `kxChkC0_true_nc`: with the data of the level-`0` searches (scaling
`uF = mwU`, short model read off by `polyOf`), the structural checks `kxChkT0` / `kxChkC0` pass for
arbitrary (non-constant) coefficients, given the side conditions (codes well formed, poles not on
`B = 0`, the `z`-equation, `mG ≠ 0`) and the non-vanishing discriminant in `F₀`.
-/

open Polynomial Differential IntermediateField

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

namespace MTower

universe u

variable {Fc : BPoly ℚ} [Fact (Irreducible (toPoly (fKc Fc)))] {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

/-- The discriminant of the short model does not vanish (from the discriminant in `F₀`). -/
theorem disc0_nc (c0 : CPoly ℚ) (hFc : Fc = [c0, [1]]) (h0 : T.Tr 0) (A : GPoly (LC 0))
    (hA4 : ∀ i < 4, codeOKb (aC Fc ks A i) = true) (s : ℚ) (hs : s ≠ 0)
    (hdisc : let cc := fun i ↦ T.val 0 (aC Fc ks A i)
      4 * (cc 1 * cc 3 - cc 2 ^ 2 / 3) ^ 3 +
        27 * (cc 0 * cc 3 ^ 2 - cc 2 * cc 1 * cc 3 / 3 + 2 * cc 2 ^ 3 / 27) ^ 2 ≠ 0) :
    (!CPoly.isZero (discC (polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0 A (mwU Fc ks c0 A))))
      (polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0 A (mwU Fc ks c0 A)))))) = true := by
  set uF := mwU Fc ks c0 A with huF
  set φ := T.phi0 c0 hFc with hφ
  set j := algebraMap ℚ Cc with hj
  have hyok : Fr.ok (yL c0) := by simp [Fr.ok, CPoly.toPoly]
  have oc : ∀ i < 4, Fr.ok (cF Fc ks c0 A i) := fun i hi ↦
    codeFr_ok _ hyok _ (codeOK_of (hA4 i hi))
  have ou : Fr.ok uF := ok_mwU
  have o0 := oc 0 (by norm_num)
  have o1 := oc 1 (by norm_num)
  have o2 := oc 2 (by norm_num)
  have o3 := oc 3 (by norm_num)
  have oA : Fr.ok (Fr.smulC (s ^ 2) (AFr Fc ks c0 A uF)) := by unfold AFr; okt
  have oB : Fr.ok (Fr.smulC (s ^ 3) (BFr Fc ks c0 A uF)) := by unfold BFr; okt
  obtain ⟨pA, hpA⟩ := AFr_poly oc (s ^ 2)
  obtain ⟨pB, hpB⟩ := BFr_poly oc (s ^ 3)
  have hu0 : Fr.val uF ≠ 0 := by
    rw [huF, val_mwU]
    exact mul_ne_zero (d0_ne oc 0 (by norm_num)) (mul_ne_zero (d0_ne oc 1 (by norm_num))
      (mul_ne_zero (d0_ne oc 2 (by norm_num)) (mul_ne_zero (d0_ne oc 3 (by norm_num)) one_ne_zero)))
  rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CPoly.isZero_iff]
  intro h0'
  apply hdisc
  have hA' := polyOf_eq_of_val _ oA pA hpA
  have hB' := polyOf_eq_of_val _ oB pB hpB
  rw [Fr.val_ofPoly] at hA' hB'
  have e0 := congrArg (algebraMap ℚ[X] (RatFunc ℚ)) h0'
  simp only [discC, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_mul, map_add, map_mul,
    map_zero, hA', hB', RatFunc.algebraMap_C] at e0
  have e1 := congrArg (ratMap j) e0
  unfold AFr BFr at e1
  simp (disch := okt) only [Fr.val_smulC, Fr.val_mul, Fr.val_sub, Fr.val_add] at e1
  have hv : ∀ i < 4, ratMap j (Fr.val (cF Fc ks c0 A i)) = φ (T.val 0 (aC Fc ks A i)) := fun i hi ↦ by
    rw [hφ, T.phi0_val c0 hFc _ (codeOK_of (hA4 i hi))]; rfl
  simp only [map_add, map_mul, map_sub, map_zero, hv 0 (by norm_num), hv 1 (by norm_num),
    hv 2 (by norm_num), hv 3 (by norm_num)] at e1
  beta_reduce
  have hU : ratMap j (Fr.val uF) ≠ 0 := (map_ne_zero_iff _ (ratMap j).injective).mpr hu0
  apply φ.injective
  rw [map_zero]
  have hs' : (s : RatFunc Cc) ≠ 0 := by exact_mod_cast hs
  simp only [map_add, map_mul, map_sub, map_pow, map_div₀, map_ofNat]
  have key : (s : RatFunc Cc) ^ 6 * ratMap j (Fr.val uF) ^ 12 *
      (4 * (φ (T.val 0 (aC Fc ks A 1)) * φ (T.val 0 (aC Fc ks A 3)) -
          φ (T.val 0 (aC Fc ks A 2)) ^ 2 / 3) ^ 3 +
        27 * (φ (T.val 0 (aC Fc ks A 0)) * φ (T.val 0 (aC Fc ks A 3)) ^ 2 -
          φ (T.val 0 (aC Fc ks A 2)) * φ (T.val 0 (aC Fc ks A 1)) * φ (T.val 0 (aC Fc ks A 3)) / 3 +
            2 * φ (T.val 0 (aC Fc ks A 2)) ^ 3 / 27) ^ 2) = 0 := by
    rw [← e1]
    simp only [map_ratCast, map_pow, map_div₀, map_one, map_ofNat, eq_ratCast, Rat.cast_pow,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    ring
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (mul_ne_zero (pow_ne_zero _ hs') (pow_ne_zero _ hU))
  · exact h

set_option maxHeartbeats 8000000 in
/-- **The twisted level-`0` check passes on non-constant data.** -/
theorem kxChkT0_true_nc (c0 : CPoly ℚ)
    (hFc : Fc = [c0, [1]]) (h0 : T.Tr 0) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ)
    (cs : List (LC 0)) (z : LC 0) (c : ℚ) (kc : ℕ)
    (hA4 : ∀ i < 4, codeOKb (aC Fc ks A i) = true) (hBok : ∀ b ∈ B, codeOKb b = true)
    (hcs : ∀ q < cs.length, codeOKb (kqC Fc ks 0 cs q) = true)
    (hD : ∀ q < cs.length, codeOKb (kxD Fc ks 0 g cs q) = true) (hz : codeOKb z = true)
    (hBq : ∀ q < cs.length,
      (GPoly.toPoly (T.MP 0 h0) B).eval (T.val 0 (kqC Fc ks 0 cs q)) ≠ 0)
    (hκ : c ≠ 0) (hs : sT Fc ks g A B kt l cs kc ≠ 0)
    (hzκ : T.val 0 z ^ 2 * T.val 0 (aC Fc ks A 0) = ((sT Fc ks g A B kt l cs kc * c * c : ℚ) : T.F 0))
    (hmG : mG Fc ks g A B kt l cs kc ≠ 0)
    (hdisc : let cc := fun i ↦ T.val 0 (aC Fc ks A i)
      4 * (cc 1 * cc 3 - cc 2 ^ 2 / 3) ^ 3 +
        27 * (cc 0 * cc 3 ^ 2 - cc 2 * cc 1 * cc 3 / 3 + 2 * cc 2 ^ 3 / 27) ^ 2 ≠ 0) :
    kxChkT0 Fc ks c0 g A B kt l cs z c (mwU Fc ks c0 A)
      (polyOf (Fr.smulC (sT Fc ks g A B kt l cs kc ^ 2) (AFr Fc ks c0 A (mwU Fc ks c0 A))))
      (polyOf (Fr.smulC (sT Fc ks g A B kt l cs kc ^ 3) (BFr Fc ks c0 A (mwU Fc ks c0 A)))) kc = true := by
  set s := sT Fc ks g A B kt l cs kc with hsdef
  set uF := mwU Fc ks c0 A with huF
  have hyok : Fr.ok (yL c0) := by simp [Fr.ok, CPoly.toPoly]
  have oc : ∀ i < 4, Fr.ok (cF Fc ks c0 A i) := fun i hi ↦
    codeFr_ok _ hyok _ (codeOK_of (hA4 i hi))
  have ou : Fr.ok uF := ok_mwU
  have o0 := oc 0 (by norm_num)
  have o1 := oc 1 (by norm_num)
  have o2 := oc 2 (by norm_num)
  have o3 := oc 3 (by norm_num)
  have oA : Fr.ok (Fr.smulC (s ^ 2) (AFr Fc ks c0 A uF)) := by unfold AFr; okt
  have oB : Fr.ok (Fr.smulC (s ^ 3) (BFr Fc ks c0 A uF)) := by unfold BFr; okt
  obtain ⟨pA, hpA⟩ := AFr_poly oc (s ^ 2)
  obtain ⟨pB, hpB⟩ := BFr_poly oc (s ^ 3)
  have h1 : (List.range 4).all (fun i ↦ codeOKb (aC Fc ks A i)) = true :=
    List.all_eq_true.mpr fun i hi ↦ hA4 i (List.mem_range.mp hi)
  have h2 : B.all codeOKb = true := List.all_eq_true.mpr hBok
  have h3 : (List.range cs.length).all (fun q ↦ codeOKb (kqC Fc ks 0 cs q) &&
      codeOKb (kxD Fc ks 0 g cs q) && codeOKb (kxR Fc ks 0 A kt l cs q) &&
      !Fr.isZ (MTower.hornerFr (yL c0) (codeFr (yL c0) (kqC Fc ks 0 cs q)) B)) = true := by
    refine List.all_eq_true.mpr fun q hq ↦ ?_
    have hq' := List.mem_range.mp hq
    have kq := codeOK_of (hcs q hq')
    have oq := codeFr_ok _ hyok _ kq
    have hBc' : ∀ b ∈ B, codeOK b := fun b hb ↦ codeOK_of (hBok b hb)
    have oH := hornerFr_ok _ _ hyok oq B hBc'
    have hHs := T.hornerFr_spec c0 hFc h0 _ oq (T.val 0 (kqC Fc ks 0 cs q))
      (T.phi0_val c0 hFc _ kq) B hBc'
    have hH : Fr.isZ (MTower.hornerFr (yL c0) (codeFr (yL c0) (kqC Fc ks 0 cs q)) B) = false := by
      rw [Bool.eq_false_iff, Ne, Fr.isZ_iff oH]
      intro h0'
      apply hBq q hq'
      have := hHs; rw [h0', map_zero] at this
      exact (map_eq_zero_iff _ (T.phi0 c0 hFc).injective).mp this.symm
    simp only [hcs q hq', hD q hq', hH, Bool.true_and, Bool.not_false, Bool.and_true]
    exact codeOKb_normC Fc _
  have hu0 : Fr.val uF ≠ 0 := by
    rw [huF, val_mwU]
    exact mul_ne_zero (d0_ne oc 0 (by norm_num)) (mul_ne_zero (d0_ne oc 1 (by norm_num))
      (mul_ne_zero (d0_ne oc 2 (by norm_num)) (mul_ne_zero (d0_ne oc 3 (by norm_num)) one_ne_zero)))
  have h5 : (!CPoly.isZero uF.2) = true := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CPoly.isZero_iff]; exact ou
  have h6 : (!Fr.isZ uF) = true := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, Fr.isZ_iff ou]; exact hu0
  have h7 : Fr.eqb (Fr.ofPoly (polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0 A uF))))
      (Fr.smulC (s ^ 2) (AFr Fc ks c0 A uF)) = true := by
    rw [Fr.eqb_iff (Fr.ok_ofPoly _) oA, polyOf_eq_of_val _ oA pA hpA]
  have h8 : Fr.eqb (Fr.ofPoly (polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0 A uF))))
      (Fr.smulC (s ^ 3) (BFr Fc ks c0 A uF)) = true := by
    rw [Fr.eqb_iff (Fr.ok_ofPoly _) oB, polyOf_eq_of_val _ oB pB hpB]
  have h9 := T.disc0_nc c0 hFc h0 A hA4 s hs hdisc
  rw [← huF] at h9
  have h12 : Fr.eqb (Fr.mul (Fr.mul (codeFr (yL c0) z) (codeFr (yL c0) z)) (cF Fc ks c0 A 0))
      (Fr.ofPoly [s * c * c]) = true := by
    have oz := codeFr_ok _ hyok _ (codeOK_of hz)
    rw [Fr.eqb_iff (Fr.ok_mul (Fr.ok_mul oz oz) o0) (Fr.ok_ofPoly _)]
    apply (ratMap (algebraMap ℚ Cc)).injective
    rw [Fr.val_mul (Fr.ok_mul oz oz) o0, Fr.val_mul oz oz, map_mul, map_mul,
      show cF Fc ks c0 A 0 = codeFr (CPoly.neg c0, [1]) (aC Fc ks A 0) from rfl,
      show yL c0 = (CPoly.neg c0, [1]) from rfl, ← T.phi0_val c0 hFc z (codeOK_of hz),
      ← T.phi0_val c0 hFc _ (codeOK_of (hA4 0 (by norm_num))), ← map_mul, ← map_mul, ← sq, hzκ,
      map_ratCast, (constFr_ofPoly (s * c * c)).2, eq_ratCast (algebraMap ℚ (RatFunc ℚ)), map_ratCast]
  unfold kxChkT0
  simp only [← hsdef]
  simp only [h1, h2, h3, h5, h6, h7, h8, h9, h12, hz, Bool.true_and, Bool.and_true,
    bne_iff_ne, ne_eq, hκ, hs, hmG, not_false_eq_true, decide_true]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨⟨hκ, hs⟩, hmG⟩

set_option maxHeartbeats 8000000 in
/-- **The conjugation level-`0` check passes on non-constant data.** -/
theorem kxChkC0_true_nc (c0 : CPoly ℚ)
    (hFc : Fc = [c0, [1]]) (h0 : T.Tr 0) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ)
    (cs : List (LC 0)) (z : LC 0) (κ : ℚ) (kc : ℕ)
    (hA4 : ∀ i < 4, codeOKb (aC Fc ks A i) = true) (hBok : ∀ b ∈ B, codeOKb b = true)
    (hcs : ∀ q < cs.length, codeOKb (kqC Fc ks 0 cs q) = true)
    (hD : ∀ q < cs.length, codeOKb (kxD Fc ks 0 g cs q) = true) (hz : codeOKb z = true)
    (hBq : ∀ q < cs.length,
      (GPoly.toPoly (T.MP 0 h0) B).eval (T.val 0 (kqC Fc ks 0 cs q)) ≠ 0)
    (hκ : κ ≠ 0) (hs : sT Fc ks g A B kt l cs kc ≠ 0)
    (hzκ : T.val 0 z ^ 2 * T.val 0 (aC Fc ks A 0) = ((κ : ℚ) : T.F 0))
    (hmG : mG Fc ks g A B kt l cs kc ≠ 0)
    (hdisc : let cc := fun i ↦ T.val 0 (aC Fc ks A i)
      4 * (cc 1 * cc 3 - cc 2 ^ 2 / 3) ^ 3 +
        27 * (cc 0 * cc 3 ^ 2 - cc 2 * cc 1 * cc 3 / 3 + 2 * cc 2 ^ 3 / 27) ^ 2 ≠ 0) :
    kxChkC0 Fc ks c0 g A B kt l cs z κ (mwU Fc ks c0 A)
      (polyOf (Fr.smulC (sT Fc ks g A B kt l cs kc ^ 2) (AFr Fc ks c0 A (mwU Fc ks c0 A))))
      (polyOf (Fr.smulC (sT Fc ks g A B kt l cs kc ^ 3) (BFr Fc ks c0 A (mwU Fc ks c0 A)))) kc = true := by
  set s := sT Fc ks g A B kt l cs kc with hsdef
  set uF := mwU Fc ks c0 A with huF
  have hyok : Fr.ok (yL c0) := by simp [Fr.ok, CPoly.toPoly]
  have oc : ∀ i < 4, Fr.ok (cF Fc ks c0 A i) := fun i hi ↦
    codeFr_ok _ hyok _ (codeOK_of (hA4 i hi))
  have ou : Fr.ok uF := ok_mwU
  have o0 := oc 0 (by norm_num)
  have o1 := oc 1 (by norm_num)
  have o2 := oc 2 (by norm_num)
  have o3 := oc 3 (by norm_num)
  have oA : Fr.ok (Fr.smulC (s ^ 2) (AFr Fc ks c0 A uF)) := by unfold AFr; okt
  have oB : Fr.ok (Fr.smulC (s ^ 3) (BFr Fc ks c0 A uF)) := by unfold BFr; okt
  obtain ⟨pA, hpA⟩ := AFr_poly oc (s ^ 2)
  obtain ⟨pB, hpB⟩ := BFr_poly oc (s ^ 3)
  have h1 : (List.range 4).all (fun i ↦ codeOKb (aC Fc ks A i)) = true :=
    List.all_eq_true.mpr fun i hi ↦ hA4 i (List.mem_range.mp hi)
  have h2 : B.all codeOKb = true := List.all_eq_true.mpr hBok
  have h3 : (List.range cs.length).all (fun q ↦ codeOKb (kqC Fc ks 0 cs q) &&
      codeOKb (kxD Fc ks 0 g cs q) && codeOKb (kxR Fc ks 0 A kt l cs q) &&
      !Fr.isZ (MTower.hornerFr (yL c0) (codeFr (yL c0) (kqC Fc ks 0 cs q)) B)) = true := by
    refine List.all_eq_true.mpr fun q hq ↦ ?_
    have hq' := List.mem_range.mp hq
    have kq := codeOK_of (hcs q hq')
    have oq := codeFr_ok _ hyok _ kq
    have hBc' : ∀ b ∈ B, codeOK b := fun b hb ↦ codeOK_of (hBok b hb)
    have oH := hornerFr_ok _ _ hyok oq B hBc'
    have hHs := T.hornerFr_spec c0 hFc h0 _ oq (T.val 0 (kqC Fc ks 0 cs q))
      (T.phi0_val c0 hFc _ kq) B hBc'
    have hH : Fr.isZ (MTower.hornerFr (yL c0) (codeFr (yL c0) (kqC Fc ks 0 cs q)) B) = false := by
      rw [Bool.eq_false_iff, Ne, Fr.isZ_iff oH]
      intro h0'
      apply hBq q hq'
      have := hHs; rw [h0', map_zero] at this
      exact (map_eq_zero_iff _ (T.phi0 c0 hFc).injective).mp this.symm
    simp only [hcs q hq', hD q hq', hH, Bool.true_and, Bool.not_false, Bool.and_true]
    exact codeOKb_normC Fc _
  have hu0 : Fr.val uF ≠ 0 := by
    rw [huF, val_mwU]
    exact mul_ne_zero (d0_ne oc 0 (by norm_num)) (mul_ne_zero (d0_ne oc 1 (by norm_num))
      (mul_ne_zero (d0_ne oc 2 (by norm_num)) (mul_ne_zero (d0_ne oc 3 (by norm_num)) one_ne_zero)))
  have h5 : (!CPoly.isZero uF.2) = true := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CPoly.isZero_iff]; exact ou
  have h6 : (!Fr.isZ uF) = true := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, Fr.isZ_iff ou]; exact hu0
  have h7 : Fr.eqb (Fr.ofPoly (polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0 A uF))))
      (Fr.smulC (s ^ 2) (AFr Fc ks c0 A uF)) = true := by
    rw [Fr.eqb_iff (Fr.ok_ofPoly _) oA, polyOf_eq_of_val _ oA pA hpA]
  have h8 : Fr.eqb (Fr.ofPoly (polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0 A uF))))
      (Fr.smulC (s ^ 3) (BFr Fc ks c0 A uF)) = true := by
    rw [Fr.eqb_iff (Fr.ok_ofPoly _) oB, polyOf_eq_of_val _ oB pB hpB]
  have h9 := T.disc0_nc c0 hFc h0 A hA4 s hs hdisc
  rw [← huF] at h9
  have h12 : Fr.eqb (Fr.mul (Fr.mul (codeFr (yL c0) z) (codeFr (yL c0) z)) (cF Fc ks c0 A 0))
      (Fr.ofPoly [κ]) = true := by
    have oz := codeFr_ok _ hyok _ (codeOK_of hz)
    rw [Fr.eqb_iff (Fr.ok_mul (Fr.ok_mul oz oz) o0) (Fr.ok_ofPoly _)]
    apply (ratMap (algebraMap ℚ Cc)).injective
    rw [Fr.val_mul (Fr.ok_mul oz oz) o0, Fr.val_mul oz oz, map_mul, map_mul,
      show cF Fc ks c0 A 0 = codeFr (CPoly.neg c0, [1]) (aC Fc ks A 0) from rfl,
      show yL c0 = (CPoly.neg c0, [1]) from rfl, ← T.phi0_val c0 hFc z (codeOK_of hz),
      ← T.phi0_val c0 hFc _ (codeOK_of (hA4 0 (by norm_num))), ← map_mul, ← map_mul, ← sq, hzκ,
      map_ratCast, (constFr_ofPoly (κ)).2, eq_ratCast (algebraMap ℚ (RatFunc ℚ)), map_ratCast]
  unfold kxChkC0
  simp only [← hsdef]
  simp only [h1, h2, h3, h5, h6, h7, h8, h9, h12, hz, Bool.true_and, Bool.and_true,
    bne_iff_ne, ne_eq, hκ, hs, hmG, not_false_eq_true, decide_true]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨⟨hκ, hs⟩, hmG⟩

end MTower

end Curves.MT
