import RischTragerBronstein.Mixed.KXNonConstSide2

/-!
# The level-`m + 1` twisted check passes on non-constant data

`kxChkT0S_true_nc`: with the data computed by `kxMWSearchS` (scaling `uF = mwUS`, short model read
off by `polyOfS`), the structural check `kxChkT0S` passes for arbitrary (non-constant)
coefficients, given the side conditions (`nonconst_sideS`), `κ / s = c²` and the `z`-equation.
The short model is exact by `AFrS_poly`/`BFrS_poly` + `polyOfG_spec`; the discriminant check
follows from the non-vanishing of the discriminant in `Kₘ₊₁` through the embedding `phiS`.
-/

open Polynomial Differential IntermediateField

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

namespace MTower

universe u

variable {Fc : BPoly ℚ} [Fact (Irreducible (toPoly (fKc Fc)))] {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L) (m : ℕ) (A : GPoly (LC (m + 1)))

/-- The exact short-model read-off. -/
theorem polyOfS_eq_of_val (f : Fr (KF Fc m)) (hf : Fr.ok f) (p : (KF Fc m)[X])
    (hv : Fr.val f = algebraMap (KF Fc m)[X] (RatFunc (KF Fc m)) p) :
    Fr.val (Fr.ofPoly (polyOfS Fc m f)) = Fr.val f := by
  rw [Fr.val_ofPoly, polyOfS_eq_polyOfG, polyOfG_spec f hf p hv, hv]

set_option maxHeartbeats 8000000 in
/-- **The structural level-`m + 1` check passes on non-constant data.** -/
theorem kxChkT0S_true_nc (h0 : T.Tr (m + 1)) (g : LC (m + 1)) (B : GPoly (LC (m + 1))) (kt l : ℕ)
    (cs : List (LC (m + 1))) (z : LC (m + 1)) (c : ℚ) (kc : ℕ)
    (hA4 : ∀ i < 4, okS (Fc := Fc) m (aCS Fc ks m A i) = true)
    (hBok : ∀ b ∈ B, okS (Fc := Fc) m b = true)
    (hcs : ∀ q < cs.length, okS (Fc := Fc) m (kqC Fc ks (m + 1) cs q) = true)
    (hD : ∀ q < cs.length, okS (Fc := Fc) m (kxD Fc ks (m + 1) g cs q) = true)
    (hz : okS (Fc := Fc) m z = true)
    (hBq : ∀ q < cs.length,
      (GPoly.toPoly (T.MP (m + 1) h0) B).eval (T.val (m + 1) (kqC Fc ks (m + 1) cs q)) ≠ 0)
    (hκ : c ≠ 0) (hs : sTS Fc ks m g A B kt l cs kc ≠ 0)
    (hzκ : T.val (m + 1) z ^ 2 * T.val (m + 1) (aCS Fc ks m A 0) =
      ((sTS Fc ks m g A B kt l cs kc * c * c : ℚ) : T.F (m + 1)))
    (hmG : mGS Fc ks m g A B kt l cs kc ≠ 0)
    (hdisc : let cc := fun i ↦ T.val (m + 1) (aCS Fc ks m A i)
      4 * (cc 1 * cc 3 - cc 2 ^ 2 / 3) ^ 3 +
        27 * (cc 0 * cc 3 ^ 2 - cc 2 * cc 1 * cc 3 / 3 + 2 * cc 2 ^ 3 / 27) ^ 2 ≠ 0) :
    kxChkT0S Fc ks m g A B kt l cs z c (mwUS Fc ks m A)
      (polyOfS Fc m (Fr.smulC (Rat.cast (sTS Fc ks m g A B kt l cs kc ^ 2) : KF Fc m)
        (AFrS Fc ks m A (mwUS Fc ks m A))))
      (polyOfS Fc m (Fr.smulC (Rat.cast (sTS Fc ks m g A B kt l cs kc ^ 3) : KF Fc m)
        (BFrS Fc ks m A (mwUS Fc ks m A)))) kc = true := by
  set s := sTS Fc ks m g A B kt l cs kc with hsdef
  set uF := mwUS Fc ks m A with huF
  set φ := T.phiS m h0 with hφ
  set jQ := T.psiF m h0.of_succ with hjQ
  have oc : ∀ i < 4, Fr.ok (cFS Fc ks m A i) := fun i hi ↦ okS_spec (Fc := Fc) (hA4 i hi)
  have ou : Fr.ok uF := ok_mwUS
  have o0 := oc 0 (by norm_num)
  have o1 := oc 1 (by norm_num)
  have o2 := oc 2 (by norm_num)
  have o3 := oc 3 (by norm_num)
  have oA : Fr.ok (Fr.smulC (Rat.cast (s ^ 2) : KF Fc m) (AFrS Fc ks m A uF)) := by
    unfold AFrS; okt
  have oB : Fr.ok (Fr.smulC (Rat.cast (s ^ 3) : KF Fc m) (BFrS Fc ks m A uF)) := by
    unfold BFrS; okt
  obtain ⟨pA, hpA⟩ := AFrS_poly oc (Rat.cast (s ^ 2) : KF Fc m)
  obtain ⟨pB, hpB⟩ := BFrS_poly oc (Rat.cast (s ^ 3) : KF Fc m)
  -- the conjuncts
  have h1 : (List.range 4).all (fun i ↦ okS (Fc := Fc) m (aCS Fc ks m A i)) = true :=
    List.all_eq_true.mpr fun i hi ↦ hA4 i (List.mem_range.mp hi)
  have h2 : B.all (okS (Fc := Fc) m) = true := List.all_eq_true.mpr hBok
  have h3 : (List.range cs.length).all (fun q ↦ okS (Fc := Fc) m (kqC Fc ks (m + 1) cs q) &&
      okS (Fc := Fc) m (kxD Fc ks (m + 1) g cs q) && okS (Fc := Fc) m (kxR Fc ks (m + 1) A kt l cs q) &&
      !Fr.isZ (hornerFrS (Fc := Fc) m (trFr (Fc := Fc) m (kqC Fc ks (m + 1) cs q)) B)) = true := by
    refine List.all_eq_true.mpr fun q hq ↦ ?_
    have hq' := List.mem_range.mp hq
    have oq := okS_spec (Fc := Fc) (hcs q hq')
    have oH := hornerFrS_ok (Fc := Fc) m _ oq B hBok
    have hHs := T.hornerFrS_spec m h0 _ oq (T.val (m + 1) (kqC Fc ks (m + 1) cs q))
      (T.phiS_val m h0 _) B hBok
    have hH : Fr.isZ (hornerFrS (Fc := Fc) m (trFr (Fc := Fc) m (kqC Fc ks (m + 1) cs q)) B) =
        false := by
      rw [Bool.eq_false_iff, Ne, Fr.isZ_iff oH]
      intro h0'
      apply hBq q hq'
      have := hHs; rw [h0', map_zero] at this
      exact (map_eq_zero_iff _ (T.phiS m h0).injective).mp this.symm
    have hR : okS (Fc := Fc) m (kxR Fc ks (m + 1) A kt l cs q) = true := by
      unfold kxR; exact T.okS_normC m h0.of_succ _
    simp only [hcs q hq', hD q hq', hH, hR, Bool.true_and, Bool.not_false]
  have hu0 : Fr.val uF ≠ 0 := by
    rw [huF, val_mwUS]
    exact mul_ne_zero (dS_ne oc 0 (by norm_num)) (mul_ne_zero (dS_ne oc 1 (by norm_num))
      (mul_ne_zero (dS_ne oc 2 (by norm_num)) (mul_ne_zero (dS_ne oc 3 (by norm_num)) one_ne_zero)))
  have h5 : (!CPoly.isZero uF.2) = true := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CPoly.isZero_iff]; exact ou
  have h6 : (!Fr.isZ uF) = true := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, Fr.isZ_iff ou]; exact hu0
  have h7 : Fr.eqb (Fr.ofPoly (polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 2) : KF Fc m)
      (AFrS Fc ks m A uF)))) (Fr.smulC (Rat.cast (s ^ 2) : KF Fc m) (AFrS Fc ks m A uF)) = true := by
    rw [Fr.eqb_iff (Fr.ok_ofPoly _) oA, polyOfS_eq_of_val m _ oA pA hpA]
  have h8 : Fr.eqb (Fr.ofPoly (polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 3) : KF Fc m)
      (BFrS Fc ks m A uF)))) (Fr.smulC (Rat.cast (s ^ 3) : KF Fc m) (BFrS Fc ks m A uF)) = true := by
    rw [Fr.eqb_iff (Fr.ok_ofPoly _) oB, polyOfS_eq_of_val m _ oB pB hpB]
  have h9 : (!CPoly.isZero (discCS Fc m
      (polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 2) : KF Fc m) (AFrS Fc ks m A uF)))
      (polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 3) : KF Fc m) (BFrS Fc ks m A uF))))) = true := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CPoly.isZero_iff]
    intro h0'
    apply hdisc
    have hA' := polyOfS_eq_of_val m _ oA pA hpA
    have hB' := polyOfS_eq_of_val m _ oB pB hpB
    rw [Fr.val_ofPoly] at hA' hB'
    have e0 := congrArg (algebraMap (KF Fc m)[X] (RatFunc (KF Fc m))) h0'
    simp only [discCS, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_mul, map_add, map_mul,
      map_zero, hA', hB', RatFunc.algebraMap_C] at e0
    have e1 := congrArg (ratMap jQ) e0
    unfold AFrS BFrS at e1
    simp (disch := okt) only [Fr.val_smulC, Fr.val_mul, Fr.val_sub, Fr.val_add] at e1
    simp only [map_add, map_mul, map_sub, map_zero, show ∀ i, cFS Fc ks m A i = trFr (Fc := Fc) m
      (aCS Fc ks m A i) from fun _ ↦ rfl, ← T.phiS_val m h0] at e1
    beta_reduce
    have hU : ratMap jQ (Fr.val uF) ≠ 0 := (map_ne_zero_iff _ (ratMap jQ).injective).mpr hu0
    apply φ.injective
    rw [map_zero]
    have hs' : (s : RatFunc (T.F m)) ≠ 0 := by exact_mod_cast hs
    simp only [map_add, map_mul, map_sub, map_pow, map_div₀, map_ofNat]
    have key : (s : RatFunc (T.F m)) ^ 6 * ratMap jQ (Fr.val uF) ^ 12 *
        (4 * (φ (T.val (m + 1) (aCS Fc ks m A 1)) * φ (T.val (m + 1) (aCS Fc ks m A 3)) - φ (T.val (m + 1) (aCS Fc ks m A 2)) ^ 2 / 3) ^ 3 +
          27 * (φ (T.val (m + 1) (aCS Fc ks m A 0)) * φ (T.val (m + 1) (aCS Fc ks m A 3)) ^ 2 - φ (T.val (m + 1) (aCS Fc ks m A 2)) * φ (T.val (m + 1) (aCS Fc ks m A 1)) * φ (T.val (m + 1) (aCS Fc ks m A 3)) / 3 +
            2 * φ (T.val (m + 1) (aCS Fc ks m A 2)) ^ 3 / 27) ^ 2) = 0 := by
      rw [← e1]
      simp only [hφ, hjQ, T.phiS_val m h0, map_ratCast, map_pow, map_div₀, map_one, map_ofNat,
        eq_ratCast, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
      ring
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (mul_ne_zero (pow_ne_zero _ hs') (pow_ne_zero _ hU))
    · exact h
  have h12 : Fr.eqb (Fr.mul (Fr.mul (trFr (Fc := Fc) m z) (trFr (Fc := Fc) m z)) (cFS Fc ks m A 0))
      (Fr.ofPoly [(Rat.cast (s * c * c) : KF Fc m)]) = true := by
    have oz := okS_spec (Fc := Fc) hz
    rw [Fr.eqb_iff (Fr.ok_mul (Fr.ok_mul oz oz) o0) (Fr.ok_ofPoly _)]
    apply (ratMap jQ).injective
    rw [Fr.val_mul (Fr.ok_mul oz oz) o0, Fr.val_mul oz oz, map_mul, map_mul,
      show cFS Fc ks m A 0 = trFr (Fc := Fc) m (aCS Fc ks m A 0) from rfl,
      ← T.phiS_val m h0 z, ← T.phiS_val m h0, ← map_mul, ← map_mul, ← sq, hzκ,
      map_ratCast, (constFrS_ofPoly (s * c * c)).2, eq_ratCast (algebraMap ℚ _), map_ratCast]
  have h13 := T.okS_zCS m h0
  unfold kxChkT0S
  simp only [← hsdef, ← huF]
  simp only [h1, h2, h3, h5, h6, h7, h8, h9, h12, h13, hz, Bool.true_and, Bool.and_true,
    bne_iff_ne, ne_eq, hκ, hs, hmG, not_false_eq_true, decide_true]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨⟨hκ, hs⟩, hmG⟩

end MTower

end Curves.MT

