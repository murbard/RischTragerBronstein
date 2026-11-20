import RischTragerBronstein.Mixed.KXCertBridgeCS
import RischTragerBronstein.Mixed.KXRepS

/-!
# Represented point of the level-`m + 1` conjugation check

`rep_of_chkC0S` (first half of `grp_of_chkC0S`): when `kxChkC0S` passes, the code point `ptDTS`
represents (through the descent maps) the `toShort`-image of `D'` with `D = mG D'`; torsion of a
represented point gives torsion of `D'`. The bridge for the completeness of the conjugation branch.
-/

open Polynomial Differential IntermediateField WeierstrassCurve WeierstrassCurve.Affine

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight NFEmbed

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L) (m : ℕ)
variable (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
  (z : LC (m + 1)) (κ : ℚ) (uF : Fr (KF Fc m)) (Ac Bc : CPoly (KF Fc m))

set_option maxHeartbeats 16000000 in
open Classical in
theorem rep_of_chkC0S (h0 : T.Tr (m + 1))
    (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length)
    [Fact (¬ IsSquare (Rat.cast (sTS Fc ks m g A B kt l cs k * κ) : KF Fc m))]
    (hchk : kxChkC0S Fc ks m g A B kt l cs z κ uF Ac Bc k = true)
    (rtsF : List (T.F (m + 1))) (hrl : rtsF.length = (kxGens Fc ks (m + 1) g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks (m + 1) g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks (m + 1) g A B kt l cs)[i] : T.F (m + 1)))
    (b₀ : T.F (m + 1)) (hb₀ : b₀ ^ 2 = (T.MP (m + 1) h0).sem (A.getD 0 (MO Fc ks (m + 1)).zero)) :
    let cC : ℕ → T.F (m + 1) := (fun i ↦ (GPoly.toPoly (T.MP (m + 1) h0) A).coeff i)
    let xC : Fin cs.length → T.F (m + 1) := (fun q ↦ (T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))
    let βC : Fin cs.length → T.F (m + 1) := (fun q ↦
      ((kxRep Fc ks (m + 1) g A B kt l cs q).2 : T.F (m + 1)) *
        SqrtIndep.prodRoots rtsF (kxRep Fc ks (m + 1) g A B kt l cs q).1 *
        ((T.MP (m + 1) h0).sem (kxD Fc ks (m + 1) g cs q) * (T.MP (m + 1) h0).sem (kxR Fc ks (m + 1) A kt l cs q) /
          (GPoly.toPoly (T.MP (m + 1) h0) B).eval ((T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))))
    ∀ (hns : ∀ q, (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * xC q) (cC 3 * βC q))
      (hns0 : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * 0) (cC 3 * b₀)),
      ∃ D' : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Point,
        (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks (m + 1) g A B kt l cs q)
          (kxCl (m + 1) g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) =
          (mGS Fc ks m g A B kt l cs k : ℤ) • D' ∧
        (∃ PD : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point,
          Rel _ _ (ptDTS Fc ks m g A B kt l cs uF Ac k) PD) ∧
        ∀ PD : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point,
          Rel _ _ (ptDTS Fc ks m g A B kt l cs uF Ac k) PD → ∀ n : ℤ, n • PD = 0 → n • D' = 0 := by
  intro cC xC βC hns hns0
  simp only [kxChkC0S, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    bne_iff_ne, ne_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hA4, hBok⟩, hcs⟩, hzok⟩, hzC⟩, hu2⟩, huZ⟩, hAe⟩, hBe⟩, hdisc⟩, hκ⟩, hs0⟩, hze⟩,
    hmG⟩ := hchk
  set s := sTS Fc ks m g A B kt l cs k with hsdef
  set T₀ := clsTS Fc ks m g A B kt l cs k with hT₀
  set φ := T.phiS m h0 with hφ
  set jQ := T.psiF m h0.of_succ with hjQ
  have hφc : ∀ c : Cc, φ (algebraMap Cc (T.F (m + 1)) c) =
      algebraMap (T.F m) (RatFunc (T.F m)) (algebraMap Cc (T.F m) c) :=
    fun c ↦ T.phiS_base m h0 (algebraMap Cc (T.F m) c)
  have hval : ∀ b : LC (m + 1), φ (T.val (m + 1) b) = ratMap jQ (Fr.val (trFr (Fc := Fc) m b)) :=
    fun b ↦ T.phiS_val m h0 b
  have hsem : ∀ b : LC (m + 1), (T.MP (m + 1) h0).sem b = T.val (m + 1) b := fun b ↦ T.sem_MP_F (m + 1) h0 b
  have hcC : ∀ i, cC i = T.val (m + 1) (aCS Fc ks m A i) := fun i ↦ by
    simp only [cC, aCS]
    rw [Tower.PrimN.coeff_toPoly_getD]
    exact hsem _
  have hok : ∀ i < 4, okS (Fc := Fc) m (aCS Fc ks m A i) = true := fun i hi ↦ (hA4 i hi)
  have oc : ∀ i < 4, Fr.ok (cFS Fc ks m A i) := fun i hi ↦ okS_spec (Fc := Fc) (hok i hi)
  have hcF : ∀ i < 4, φ (cC i) = ratMap jQ (Fr.val (cFS Fc ks m A i)) := fun i hi ↦ by
    rw [hcC]; exact hval _
  have ouF : Fr.ok uF := fun h ↦ by
    rw [← CPoly.isZero_iff] at h; rw [h] at hu2; exact absurd hu2 (by decide)
  set u₀ := ratMap jQ (Fr.val uF) with hu₀def
  have hu₀ : u₀ ≠ 0 := by
    rw [hu₀def, map_ne_zero_iff _ (ratMap jQ).injective]
    intro h; rw [← Fr.isZ_iff ouF] at h; rw [h] at huZ; exact absurd huZ (by decide)
  -- the constants: roots of the generators, `r = ∏_T rᵢ`
  have hg0 := (kxGens_spec (Fc := Fc) (ks := ks) (m + 1) g A B kt l cs).2
  have hcF0 : ∀ x ∈ rtsF, ∃ c : Cc, algebraMap Cc (T.F (m + 1)) c = x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact T.const_of_sqN (m + 1) _ _ (hg0 _ (List.getElem_mem (by omega))) (hrs i hi (by omega))
  obtain ⟨rs, hrsm⟩ := T.consts_of_listN (m + 1) rtsF hcF0
  subst hrsm
  have hrsl : rs.length = (kxGens Fc ks (m + 1) g A B kt l cs).length := by
    rw [← hrl, List.length_map]
  have hrs2 : ∀ i (hi : i < rs.length) (hi' : i < (kxGens Fc ks (m + 1) g A B kt l cs).length),
      rs[i] ^ 2 = ((kxGens Fc ks (m + 1) g A B kt l cs)[i] : Cc) := fun i hi hi' ↦ by
    apply (algebraMap Cc (T.F (m + 1))).injective
    have := hrs i (by simpa using hi) hi'
    simp only [List.getElem_map] at this
    rw [map_pow, this, map_ratCast]
  set r := SqrtIndep.prodRoots rs T₀ with hrdef
  have hr2 : r ^ 2 = (s : Cc) := SqrtIndep.prodRoots_sq _ rs hrsl hrs2 T₀
  have hr0 : r ≠ 0 := fun h ↦ by
    rw [h, zero_pow two_ne_zero] at hr2
    exact hs0 (by exact_mod_cast hr2.symm)
  set ρ := algebraMap (T.F m) (RatFunc (T.F m)) (algebraMap Cc (T.F m) r) with hρ
  have hρ2 : ρ ^ 2 = (s : RatFunc (T.F m)) := by
    rw [hρ, ← map_pow, ← map_pow, hr2, map_ratCast, map_ratCast]
  have hρ0 : ρ ≠ 0 := (map_ne_zero_iff _ (algebraMap (T.F m) (RatFunc (T.F m))).injective).mpr
    ((map_ne_zero_iff _ (algebraMap Cc (T.F m)).injective).mpr hr0)
  set u := u₀ * ρ with hudef
  have hu : u ≠ 0 := mul_ne_zero hu₀ hρ0
  have o0 := oc 0 (by norm_num)
  have o1 := oc 1 (by norm_num)
  have o2 := oc 2 (by norm_num)
  have o3 := oc 3 (by norm_num)
  have oAFr : Fr.ok (AFrS Fc ks m A uF) := by
    unfold AFrS; okt
  have oBFr : Fr.ok (BFrS Fc ks m A uF) := by
    unfold BFrS; okt
  have hA0 : ratMap jQ (Fr.val (AFrS Fc ks m A uF)) =
      u₀ ^ 4 * (φ (cC 1 * cC 3) - φ (cC 2) ^ 2 / 3) := by
    simp only [map_mul, map_pow]
    rw [hcF 1 (by norm_num), hcF 2 (by norm_num), hcF 3 (by norm_num)]
    unfold AFrS
    simp (disch := okt) only [Fr.val_mul, Fr.val_sub, Fr.val_smulC]
    simp only [map_mul, map_sub, map_add, eq_ratCast, map_ratCast, hu₀def, one_div, map_inv₀,
      map_ofNat, map_div₀]
    ring
  have hB0 : ratMap jQ (Fr.val (BFrS Fc ks m A uF)) =
      u₀ ^ 6 * (φ (cC 0 * cC 3 ^ 2) - φ (cC 2) * φ (cC 1 * cC 3) / 3 + 2 * φ (cC 2) ^ 3 / 27) := by
    simp only [map_mul, map_pow]
    rw [hcF 0 (by norm_num), hcF 1 (by norm_num), hcF 2 (by norm_num), hcF 3 (by norm_num)]
    unfold BFrS
    simp (disch := okt) only [Fr.val_mul, Fr.val_sub, Fr.val_add, Fr.val_smulC]
    simp only [map_mul, map_sub, map_add, eq_ratCast, map_ratCast, hu₀def, one_div, map_inv₀,
      map_ofNat, map_div₀]
    ring
  have hA : algebraMap (T.F m)[X] (RatFunc (T.F m)) ((CPoly.toPoly Ac).map jQ) =
      u ^ 4 * (φ (cC 1 * cC 3) - φ (cC 2) ^ 2 / 3) := by
    have e' := congrArg (ratMap jQ) ((Fr.eqb_iff (Fr.ok_ofPoly Ac) (Fr.ok_smulC _ oAFr)).mp hAe)
    rw [Fr.val_ofPoly, ratMap_alg] at e'
    rw [e', ratMap_smulCS, hA0, hudef, mul_pow, show ρ ^ 4 = (ρ ^ 2) ^ 2 by ring, hρ2]
    push_cast
    ring
  have hB : algebraMap (T.F m)[X] (RatFunc (T.F m)) ((CPoly.toPoly Bc).map jQ) =
      u ^ 6 * (φ (cC 0 * cC 3 ^ 2) - φ (cC 2) * φ (cC 1 * cC 3) / 3 + 2 * φ (cC 2) ^ 3 / 27) := by
    have e' := congrArg (ratMap jQ) ((Fr.eqb_iff (Fr.ok_ofPoly Bc) (Fr.ok_smulC _ oBFr)).mp hBe)
    rw [Fr.val_ofPoly, ratMap_alg] at e'
    rw [e', ratMap_smulCS, hB0, hudef, mul_pow, show ρ ^ 6 = (ρ ^ 2) ^ 3 by ring, hρ2]
    push_cast
    ring
  have hΔ : 4 * ((CPoly.toPoly Ac).map jQ) ^ 3 + 27 * ((CPoly.toPoly Bc).map jQ) ^ 2 ≠ 0 := by
    have h1 : CPoly.toPoly (discCS Fc m Ac Bc) ≠ 0 := fun h ↦ by
      rw [← CPoly.isZero_iff] at h; rw [h] at hdisc; exact absurd hdisc (by decide)
    have h2 : 4 * ((CPoly.toPoly Ac).map jQ) ^ 3 + 27 * ((CPoly.toPoly Bc).map jQ) ^ 2 =
        (CPoly.toPoly (discCS Fc m Ac Bc)).map jQ := by
      simp only [discCS, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_mul, Polynomial.map_add,
        Polynomial.map_mul, Polynomial.map_C]
      simp only [map_ofNat]
      ring
    rw [h2]
    exact (Polynomial.map_ne_zero_iff jQ.injective).mpr h1
  have hBc : ∀ b ∈ B, okS (Fc := Fc) m b = true := fun b hb ↦ (hBok b hb)
  have hq : ∀ q : Fin cs.length, inClsS Fc ks m g A B kt l cs k q = true →
      ∃ Pk : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point,
      Rel _ _ (ptQTS Fc ks m g A B kt l cs uF k q) Pk ∧
      mapE jQ _ _ Pk = Differential.SuperData.toShort φ (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _ hA hB
        (Point.some _ _ (hns q)) := by
    intro q hin
    have hTq : (kxRep Fc ks (m + 1) g A B kt l cs q).1 = T₀ := by
      simpa [inClsS, hT₀] using hin
    obtain ⟨⟨⟨hq1, hq2⟩, hq3⟩, hq4⟩ := hcs q q.2
    have kq := hq1
    have kD := hq2
    have kR := hq3
    have oq := okS_spec (Fc := Fc) kq
    have oD := okS_spec (Fc := Fc) kD
    have oR := okS_spec (Fc := Fc) kR
    have o3' := okS_spec (Fc := Fc) (hok 3 (by norm_num))
    have o2' := okS_spec (Fc := Fc) (hok 2 (by norm_num))
    have oH := hornerFrS_ok (Fc := Fc) m _ oq B hBc
    have hH0 : Fr.val (hornerFrS (Fc := Fc) m (trFr (Fc := Fc) m (kqC Fc ks (m + 1) cs q)) B) ≠ 0 := fun h ↦ by
      rw [← Fr.isZ_iff oH] at h; rw [h] at hq4; exact absurd hq4 (by decide)
    have hHs := T.hornerFrS_spec m h0 _ oq (T.val (m + 1) (kqC Fc ks (m + 1) cs q)) (hval _) B hBc
    have hB0' : (GPoly.toPoly (T.MP (m + 1) h0) B).eval (T.val (m + 1) (kqC Fc ks (m + 1) cs q)) ≠ 0 := fun h ↦ by
      apply hH0
      rw [h, map_zero] at hHs
      exact (map_eq_zero_iff _ (ratMap jQ).injective).mp hHs
    have oY : Fr.ok (yBaseFrS (Fc := Fc) m uF (aCS Fc ks m A 3) (kxD Fc ks (m + 1) g cs q)
        (kxR Fc ks (m + 1) A kt l cs q) (kqC Fc ks (m + 1) cs q) B) := by
      unfold yBaseFrS
      have := Fr.ok_div (Fr.ok_mul oD oR) hH0
      okt
    have oX : Fr.ok (xFrS (Fc := Fc) m uF (aCS Fc ks m A 3) (aCS Fc ks m A 2) (kqC Fc ks (m + 1) cs q)) := by
      unfold xFrS; okt
    refine Differential.SuperData.cert_pt φ jQ (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _ hA hB _ _
      (hns q) _ _ (Fr.ok_smulC _ oX) (Fr.ok_mul oY (Fr.ok_ofPoly _)) ?_ ?_
    · rw [ratMap_smulCS, T.xFrS_spec m h0 uF ouF _ _ _ (hok 3 (by norm_num)) (hok 2 (by norm_num))
        kq, hcC, hcC, hudef, mul_pow, hρ2]
      simp only [xC, hsem]
      rw [← hu₀def]
      ring
    · rw [ratMap_mulCS m jQ _ oY, T.yBaseFrS_spec m h0 uF ouF _ _ _ _ B (hok 3 (by norm_num)) kD kR
        kq hBc hB0']
      simp only [βC, hTq, ← SqrtIndep.map_prodRoots, ← hrdef, hcC, hsem]
      simp only [map_mul, map_div₀, map_ratCast, hφc, ← hρ, hudef, ← hu₀def]
      have e4 : (u₀ * ρ) ^ 3 * ρ = u₀ ^ 3 * (s : RatFunc (T.F m)) ^ 2 := by
        rw [← hρ2]; ring
      rw [← hφ, ← hu₀def, ← hsdef]
      set X := φ (T.val (m + 1) (kxD Fc ks (m + 1) g cs ↑q)) * φ (T.val (m + 1) (kxR Fc ks (m + 1) A kt l cs ↑q)) /
        φ (eval (T.val (m + 1) (kqC Fc ks (m + 1) cs ↑q)) (GPoly.toPoly (T.MP (m + 1) h0) B))
      rw [show (u₀ * ρ) ^ 3 * (φ (T.val (m + 1) (aCS Fc ks m A 3)) *
          (((kxRep Fc ks (m + 1) g A B kt l cs ↑q).2 : RatFunc (T.F m)) * ρ * X)) =
          (u₀ * ρ) ^ 3 * ρ * (φ (T.val (m + 1) (aCS Fc ks m A 3)) *
          (((kxRep Fc ks (m + 1) g A B kt l cs ↑q).2 : RatFunc (T.F m)) * X)) by ring, e4]
      push_cast
      ring
  -- the field `k₀ = ℚ(√δ)`, `δ = s κ`, and its embedding `√δ ↦ r w`
  set δ := s * κ with hδ
  have kz := hzok
  have ozF := okS_spec (Fc := Fc) kz
  have hzeq := (Fr.eqb_iff (Fr.ok_mul (Fr.ok_mul ozF ozF) o0) (Fr.ok_ofPoly _)).mp hze
  rw [Fr.val_mul (Fr.ok_mul ozF ozF) o0, Fr.val_mul ozF ozF, Fr.val_ofPoly] at hzeq
  have hκr : algebraMap (KF Fc m)[X] (RatFunc (KF Fc m)) (CPoly.toPoly [(Rat.cast κ : KF Fc m)]) =
      ((κ : ℚ) : RatFunc (KF Fc m)) := by
    simp [CPoly.toPoly, RatFunc.algebraMap_C]
  rw [hκr] at hzeq
  have hφz : φ (T.val (m + 1) z) = ratMap jQ (Fr.val (trFr (Fc := Fc) m z)) := hval z
  have hw : (b₀ * T.val (m + 1) z) ^ 2 = ((κ : ℚ) : T.F (m + 1)) := by
    apply φ.injective
    have hb : φ b₀ ^ 2 = ratMap jQ (Fr.val (cFS Fc ks m A 0)) := by
      rw [← map_pow, hb₀, hsem, ← hcF 0 (by norm_num), hcC]; rfl
    have e2 := congrArg (ratMap jQ) hzeq
    simp only [map_mul, map_ratCast] at e2
    rw [mul_pow, map_mul, map_pow, map_pow, hb, hφz, map_ratCast]
    linear_combination e2
  have hvz : T.val (m + 1) z ≠ 0 := fun h ↦ by
    rw [h, mul_zero, zero_pow two_ne_zero] at hw
    exact hκ (by exact_mod_cast hw.symm)
  have hzne : Fr.val (trFr (Fc := Fc) m z) ≠ 0 := fun h ↦ by
    rw [h, map_zero] at hφz
    exact hvz ((map_eq_zero_iff _ φ.injective).mp hφz)
  obtain ⟨w, hwc⟩ := T.const_of_sqN (m + 1) _ _ hκ hw
  have hw2 : w ^ 2 = (κ : Cc) := by
    apply (algebraMap Cc (T.F (m + 1))).injective
    rw [map_pow, hwc, hw, map_ratCast]
  letI : Algebra (KF Fc m) (T.F m) := (T.psiF m h0.of_succ).toAlgebra
  set R : T.F m := algebraMap Cc (T.F m) (r * w) with hR
  have ht : R * R = algebraMap (KF Fc m) (T.F m) (Rat.cast δ) := by
    rw [RingHom.algebraMap_toAlgebra, map_ratCast, hR, ← map_mul,
      show (r * w) * (r * w) = r ^ 2 * w ^ 2 by ring, hr2, hw2, hδ, ← Rat.cast_mul, map_ratCast]
  set e := algebraMap (KF Fc m) (QuadraticAlgebra (KF Fc m) (Rat.cast δ) 0) with he
  set j : QuadraticAlgebra (KF Fc m) (Rat.cast δ) 0 →+* T.F m :=
    (qaEmbed (Rat.cast δ) R ht).toRingHom with hj
  have hjω : j ⟨0, 1⟩ = R := qaEmbed_omega (Rat.cast δ) R ht
  have hje : j.comp e = jQ := by
    rw [hj, he, hjQ]
    exact (qaEmbed (Rat.cast δ) R ht).comp_algebraMap
  have hA' : algebraMap (T.F m)[X] (RatFunc (T.F m)) (((CPoly.toPoly Ac).map e).map j) =
      u ^ 4 * (φ (cC 1 * cC 3) - φ (cC 2) ^ 2 / 3) := by rw [Polynomial.map_map, hje]; exact hA
  have hB' : algebraMap (T.F m)[X] (RatFunc (T.F m)) (((CPoly.toPoly Bc).map e).map j) =
      u ^ 6 * (φ (cC 0 * cC 3 ^ 2) - φ (cC 2) * φ (cC 1 * cC 3) / 3 + 2 * φ (cC 2) ^ 3 / 27) := by
    rw [Polynomial.map_map, hje]; exact hB
  -- transfer of the class points to `ℚ → k₀ → Cc`
  have transfer : ∀ (x y : T.F (m + 1)) (hxy : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1)
      (cC 0)).Nonsingular x y) (Pk : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point),
      mapE jQ _ _ Pk = Differential.SuperData.toShort φ (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _ hA hB
        (Point.some x y hxy) →
      mapE j _ _ (mapE e _ _ Pk) = Differential.SuperData.toShort φ (cC 3) (cC 2) (cC 1) (cC 0) u hu
        _ _ hA' hB' (Point.some x y hxy) := by
    intro x y hxy Pk hPk
    rcases Pk with _ | ⟨X, Y, hXY⟩
    · obtain ⟨h3, e3⟩ := Differential.SuperData.toShort_some φ (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _
        hA hB x y hxy
      rw [e3] at hPk
      rw [show (Point.zero : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point) = 0
        from rfl, map_zero] at hPk
      cases hPk
    obtain ⟨h1, e1⟩ := mapE_some jQ _ _ X Y hXY
    obtain ⟨h3, e3⟩ := Differential.SuperData.toShort_some φ (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _
      hA hB x y hxy
    rw [e1, e3] at hPk
    simp only [Point.some.injEq] at hPk
    obtain ⟨h4, e4⟩ := mapE_some e _ _ X Y hXY
    obtain ⟨h5, e5⟩ := mapE_some j _ _ _ _ h4
    obtain ⟨h6, e6⟩ := Differential.SuperData.toShort_some φ (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _
      hA' hB' x y hxy
    rw [e4, e5, e6]
    simp only [Point.some.injEq, ratMap_comp', hje]
    exact hPk
  -- the sum `D` over the class
  set fl := (List.finRange cs.length).filter fun q : Fin cs.length ↦
    inClsS Fc ks m g A B kt l cs k (q : ℕ) with hfl
  set lst : List (ℤ × PtC (KF Fc m) × (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Point) :=
    fl.map (fun q : Fin cs.length ↦ (mKcS Fc ks m g A B kt l cs k (q : ℕ) /
        (mGS Fc ks m g A B kt l cs k : ℤ), ptQTS Fc ks m g A B kt l cs uF k (q : ℕ),
          Point.some _ _ (hns q))) with hlst
  obtain ⟨PD, hRD, hmD⟩ := Differential.SuperData.cert_sumψG φ e j (cC 3) (cC 2) (cC 1) (cC 0) u hu
    _ _ hA' hB' Ac rfl lst (fun e' he' ↦ by
      rw [hlst, List.mem_map] at he'
      obtain ⟨q, hqm, rfl⟩ := he'
      have hqm' := hqm
      rw [hfl, List.mem_filter] at hqm'
      obtain ⟨Pk, hRk, hmk⟩ := hq q hqm'.2
      exact ⟨Pk, hRk, transfer _ _ _ Pk hmk⟩)
  have hl1 : lst.map (fun e ↦ (e.1, e.2.1)) = fl.map (fun q : Fin cs.length ↦
      (mKcS Fc ks m g A B kt l cs k (q : ℕ) / (mGS Fc ks m g A B kt l cs k : ℤ),
        ptQTS Fc ks m g A B kt l cs uF k (q : ℕ))) := by
    rw [hlst, List.map_map]; rfl
  rw [hl1] at hRD
  have hdvd : ∀ q : Fin cs.length, (mGS Fc ks m g A B kt l cs k : ℤ) ∣ mKcS Fc ks m g A B kt l cs k q :=
    fun q ↦ foldr_gcd_dvd _ _ (List.mem_map.mpr ⟨q, List.mem_range.mpr q.2, rfl⟩)
  have hz0 : ∀ q : Fin cs.length, inClsS Fc ks m g A B kt l cs k q = false →
      mKcS Fc ks m g A B kt l cs k q = 0 := fun q hq ↦ by
    unfold mKcS
    unfold inClsS clsTS at hq
    rw [List.getD_eq_getElem _ _ k.2] at hq ⊢
    simp [hq]
  have hD : ∑ q, ((Differential.SuperData.mK (fun q ↦ kxMNm Fc ks (m + 1) g A B kt l cs q)
      (kxCl (m + 1) g A B kt l cs) k q : ℕ) : ℤ) • Point.some _ _ (hns q) =
      (mGS Fc ks m g A B kt l cs k : ℤ) • (lst.map fun e ↦ e.1 • e.2.2).sum := by
    have e1 : ∑ q, ((Differential.SuperData.mK (fun q ↦ kxMNm Fc ks (m + 1) g A B kt l cs q)
        (kxCl (m + 1) g A B kt l cs) k q : ℕ) : ℤ) • Point.some _ _ (hns q) =
        ∑ q : Fin cs.length, ((mGS Fc ks m g A B kt l cs k : ℤ) * (mKcS Fc ks m g A B kt l cs k q /
          (mGS Fc ks m g A B kt l cs k : ℤ))) • Point.some _ _ (hns q) := by
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [Int.mul_ediv_cancel' (hdvd q), mK_eq_mKcS]
    rw [e1, Fin.sum_univ_def, sum_map_filter_of_zero
      (fun q : Fin cs.length ↦ inClsS Fc ks m g A B kt l cs k (q : ℕ)) _ _
      (fun q _ hq ↦ by rw [hz0 q hq, Int.zero_ediv, mul_zero, zero_smul]), ← hfl, hlst,
      List.map_map, List.smul_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q _
    simp only [Function.comp_apply, smul_smul]
  -- the point `P₊` over `k₀`
  set b₀s : T.F (m + 1) := algebraMap Cc (T.F (m + 1)) w / T.val (m + 1) z with hb₀s
  have hb₀e : b₀ = b₀s := by rw [hb₀s, hwc]; field_simp
  have o3' := okS_spec (Fc := Fc) (hok 3 (by norm_num))
  have o2' := okS_spec (Fc := Fc) (hok 2 (by norm_num))
  have kn := hzC
  have on := okS_spec (Fc := Fc) kn
  have oXZ : Fr.ok (xFrS (Fc := Fc) m uF (aCS Fc ks m A 3) (aCS Fc ks m A 2) (zCS Fc ks m)) := by unfold xFrS; okt
  have odiv := Fr.ok_div (Fr.ok_ofPoly [1]) hzne
  have oYZ : Fr.ok (yZS Fc ks m A z uF) := by unfold yZS; okt
  have hv0 : T.val (m + 1) (zCS Fc ks m) = 0 := Subtype.ext (zero_div _)
  have hratm : ∀ f : Fr (KF Fc m), ratMap j (Fr.val (frMap e f)) = ratMap jQ (Fr.val f) := fun f ↦ by
    rw [frMap_val, ratMap_comp', hje]
  set fx0 := frMap e (Fr.smulC (Rat.cast s : KF Fc m) (xFrS (Fc := Fc) m uF (aCS Fc ks m A 3) (aCS Fc ks m A 2) (zCS Fc ks m))) with hfx0
  set fy0 := Fr.mul (frMap e (Fr.mul (yZS Fc ks m A z uF) (Fr.ofPoly [(Rat.cast s : KF Fc m)])))
    (Fr.ofPoly [(⟨0, 1⟩ : QuadraticAlgebra (KF Fc m) (Rat.cast δ) 0)]) with hfy0
  have ofx0 : Fr.ok fx0 := frMap_ok e _ (Fr.ok_smulC _ oXZ)
  have ofy1 : Fr.ok (frMap e (Fr.mul (yZS Fc ks m A z uF) (Fr.ofPoly [(Rat.cast s : KF Fc m)]))) :=
    frMap_ok e _ (Fr.ok_mul oYZ (Fr.ok_ofPoly _))
  have ofy0 : Fr.ok fy0 := Fr.ok_mul ofy1 (Fr.ok_ofPoly _)
  obtain ⟨PZ, hRZ, hmZ⟩ := Differential.SuperData.cert_pt φ j (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _
    hA' hB' _ _ hns0 fx0 fy0 ofx0 ofy0 (by
      rw [hfx0, hratm, ratMap_smulCS, T.xFrS_spec m h0 uF ouF _ _ _ (hok 3 (by norm_num))
        (hok 2 (by norm_num)) kn, hcC, hcC, hv0, hudef, mul_pow, hρ2, ← hu₀def]
      ring) (by
      rw [hfy0, frMap_mulConst j _ ofy1, hratm, ratMap_mulCS m jQ _ oYZ, hjω, hb₀e]
      unfold yZS
      simp only [Fr.val_mul (Fr.ok_mul ouF (Fr.ok_mul ouF ouF)) (Fr.ok_mul o3 odiv),
        Fr.val_mul ouF (Fr.ok_mul ouF ouF), Fr.val_mul ouF ouF, Fr.val_mul o3 odiv,
        Fr.val_div (Fr.ok_ofPoly [1]) ozF hzne, Fr.val_ofPoly]
      simp only [map_mul, map_div₀, hb₀s, ← hcF 3 (by norm_num), ← hφz, hφc, ← hρ, hudef,
        ← hu₀def]
      have h1 : ratMap jQ (algebraMap (KF Fc m)[X] (RatFunc (KF Fc m)) (CPoly.toPoly [1])) = 1 := by
        simp [CPoly.toPoly]
      rw [h1]
      have e4 : (u₀ * ρ) ^ 3 * ρ = u₀ ^ 3 * (s : RatFunc (T.F m)) ^ 2 := by rw [← hρ2]; ring
      rw [show (u₀ * ρ) ^ 3 * (φ (cC 3) * (algebraMap (T.F m) (RatFunc (T.F m))
          (algebraMap Cc (T.F m) w) / φ (T.val (m + 1) z))) =
        u₀ ^ 3 * ρ ^ 3 * (φ (cC 3) * (algebraMap (T.F m) (RatFunc (T.F m))
          (algebraMap Cc (T.F m) w) / φ (T.val (m + 1) z))) by ring]
      rw [show ρ ^ 3 = (s : RatFunc (T.F m)) * ρ by rw [pow_succ, hρ2]]
      rw [hR, map_mul, map_mul, ← hρ]
      push_cast
      ring)
  -- conjugation
  set τ := starRingEnd (QuadraticAlgebra (KF Fc m) (Rat.cast δ) 0) with hτ
  have hτe : τ.comp e = e := RingHom.ext fun a ↦ by
    ext <;> simp [hτ, he, starRingEnd_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  have hAτ : (((CPoly.toPoly Ac).map e).map τ) = (CPoly.toPoly Ac).map e := by
    rw [Polynomial.map_map, hτe]
  have hBτ : (((CPoly.toPoly Bc).map e).map τ) = (CPoly.toPoly Bc).map e := by
    rw [Polynomial.map_map, hτe]
  have hτω : τ ⟨0, 1⟩ = -⟨0, 1⟩ := by
    ext <;> simp [hτ, starRingEnd_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  have hZτ : τE τ _ _ hAτ hBτ PZ = -PZ := by
    rcases PZ with _ | ⟨X, Y, hXY⟩
    · exact absurd hRZ (by simp [FFHeight.Rel])
    obtain ⟨-, -, hX, hY⟩ := hRZ
    obtain ⟨h2, e2⟩ := τE_some τ _ _ hAτ hBτ X Y hXY
    rw [e2, WeierstrassCurve.Affine.Point.neg_some]
    simp only [Point.some.injEq, negY_shortW]
    rw [← hX, ← hY, hfx0, hfy0, frMap_val, ratMap_comp', hτe, Fr.val_mul ofy1 (Fr.ok_ofPoly _),
      Fr.val_ofPoly, map_mul, frMap_val, ratMap_comp', hτe, ratMap_alg]
    simp only [CPoly.toPoly_cons, CPoly.toPoly_nil, mul_zero, add_zero, Polynomial.map_C, hτω,
      map_neg, RatFunc.algebraMap_C]
    refine ⟨trivial, ?_⟩
    ring
  -- non-torsion of `D′` over `ℚ`
  have hΔq : 4 * (CPoly.toPoly Ac) ^ 3 + 27 * (CPoly.toPoly Bc) ^ 2 ≠ 0 := by
    intro h0
    apply hΔ
    rw [show 4 * ((CPoly.toPoly Ac).map jQ) ^ 3 + 27 * ((CPoly.toPoly Bc).map jQ) ^ 2 =
      (4 * (CPoly.toPoly Ac) ^ 3 + 27 * (CPoly.toPoly Bc) ^ 2).map jQ by simp, h0,
      Polynomial.map_zero]
  refine ⟨(lst.map fun e ↦ e.1 • e.2.2).sum, hD, ⟨PD, hRD⟩, ?_⟩
  intro PD' hRD' n hn
  rw [Rel_unique hRD' hRD] at hn
  have h2 := congrArg (fun X ↦ mapE j _ _ (mapE e _ _ X)) hn
  simp only [map_zsmul, map_zero] at h2
  rw [hmD] at h2
  have h3 := Differential.SuperData.rel_of_toShort φ (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _ hA' hB'
    (lst.map fun e ↦ e.1 • e.2.2).sum (lst.map fun e ↦ e.1 • e.2.2).sum n 0
    (by rw [zero_zsmul]; convert h2 using 2 <;> (try congr!) <;> (try apply Subsingleton.elim))
  convert h3 using 1 <;>
    first
    | exact (zero_zsmul _).symm
    | rfl
    | (congr! <;> apply Subsingleton.elim)

end MTower

end Curves.MT


