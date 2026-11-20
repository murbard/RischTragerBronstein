import RischTragerBronstein.Mixed.KXCertBridgeT
import RischTragerBronstein.Mixed.KXCertBridgeC

/-!
# The converse of the twisted bridge check

`indep_of_grpT0`: under the structural checks of `kxChkT0`, the group condition on the curve (and
`P₊` of infinite order) makes the certificate points on the twist independent.
-/

open Polynomial Differential IntermediateField WeierstrassCurve WeierstrassCurve.Affine NFEmbed

namespace Differential.SuperData

open scoped Classical

/-- A relation between images under `toShort` is a relation on the curve. -/
theorem rel_of_toShort {C : Type*} [Field C] [CharZero C] {k : Type*} [Field k] [CharZero k]
    (φ : C ≃+* RatFunc k) (c3 c2 c1 c0 : C) (u : RatFunc k) (hu : u ≠ 0) (A B : k[X])
    (hA : algebraMap k[X] (RatFunc k) A = u ^ 4 * (φ (c1 * c3) - φ c2 ^ 2 / 3))
    (hB : algebraMap k[X] (RatFunc k) B =
      u ^ 6 * (φ (c0 * c3 ^ 2) - φ c2 * φ (c1 * c3) / 3 + 2 * φ c2 ^ 3 / 27))
    (D Z : (WG c3 c2 c1 c0).Point) (m n : ℤ)
    (h : m • toShort φ c3 c2 c1 c0 u hu A B hA hB D = n • toShort φ c3 c2 c1 c0 u hu A B hA hB Z) :
    m • D = n • Z := by
  apply toShort_injective φ c3 c2 c1 c0 u hu A B hA hB
  rw [map_zsmul, map_zsmul, h]

/-- `toShort` has trivial kernel. -/
theorem zero_of_toShort {C : Type*} [Field C] [CharZero C] {k : Type*} [Field k] [CharZero k]
    (φ : C ≃+* RatFunc k) (c3 c2 c1 c0 : C) (u : RatFunc k) (hu : u ≠ 0) (A B : k[X])
    (hA : algebraMap k[X] (RatFunc k) A = u ^ 4 * (φ (c1 * c3) - φ c2 ^ 2 / 3))
    (hB : algebraMap k[X] (RatFunc k) B =
      u ^ 6 * (φ (c0 * c3 ^ 2) - φ c2 * φ (c1 * c3) / 3 + 2 * φ c2 ^ 3 / 27))
    (D : (WG c3 c2 c1 c0).Point) (n : ℤ) (h : n • toShort φ c3 c2 c1 c0 u hu A B hA hB D = 0) :
    n • D = 0 := by
  apply toShort_injective φ c3 c2 c1 c0 u hu A B hA hB
  rw [map_zsmul, h, map_zero]

end Differential.SuperData

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

lemma rel_unique {K : Type*} [Field K] [DecidableEq K] {A B : K[X]} {p : PtC K}
    {P Q : (shortW A B).toAffine.Point} (hP : Rel A B p P) (hQ : Rel A B p Q) : P = Q := by
  rcases p with _ | ⟨fx, fy⟩ <;> rcases P with _ | ⟨x, y, h⟩ <;> rcases Q with _ | ⟨x', y', h'⟩ <;>
    simp_all [FFHeight.Rel]

namespace MTower

variable [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
variable (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
  (z : LC 0) (c : ℚ) (uF : Fr ℚ) (Ac Bc : CPoly ℚ) (kk : ℕ)

set_option maxHeartbeats 8000000 in
open Classical in
/-- **The converse of `grp_of_chkT0`**: when the structural checks pass, the group condition on the
curve (with `P₊` of infinite order) makes the certificate points `D′`, `P₊′` on the twist
independent — so a two-point certificate for them exists (`certG_exists`). -/
theorem indep_of_grpT0 (hFc : Fc = [c0f, [1]]) (h0 : T.Tr 0)
    (k : Fin (kxCls Fc ks 0 g A B kt l cs).length)
    (hchk : kxChkT0 Fc ks c0f g A B kt l cs z c uF Ac Bc k = true)
    (rtsF : List (T.F 0)) (hrl : rtsF.length = (kxGens Fc ks 0 g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks 0 g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks 0 g A B kt l cs)[i] : T.F 0))
    (b₀ : T.F 0) (hb₀ : b₀ ^ 2 = (T.MP 0 h0).sem (A.getD 0 (MO Fc ks 0).zero)) :
    let cC : ℕ → T.F 0 := (fun i ↦ (GPoly.toPoly (T.MP 0 h0) A).coeff i)
    let xC : Fin cs.length → T.F 0 := (fun q ↦ (T.MP 0 h0).sem (kqC Fc ks 0 cs q))
    let βC : Fin cs.length → T.F 0 := (fun q ↦
      ((kxRep Fc ks 0 g A B kt l cs q).2 : T.F 0) *
        SqrtIndep.prodRoots rtsF (kxRep Fc ks 0 g A B kt l cs q).1 *
        ((T.MP 0 h0).sem (kxD Fc ks 0 g cs q) * (T.MP 0 h0).sem (kxR Fc ks 0 A kt l cs q) /
          (GPoly.toPoly (T.MP 0 h0) B).eval ((T.MP 0 h0).sem (kqC Fc ks 0 cs q))))
    ∀ (hns : ∀ q, (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * xC q) (cC 3 * βC q))
      (hns0 : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * 0) (cC 3 * b₀)),
      (∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
          (kxCl 0 g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0) →
      (∀ n : ℤ, n • WeierstrassCurve.Affine.Point.some _ _ hns0 = 0 → n = 0) →
      (∃ PD : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point,
        Rel _ _ (ptDT Fc ks c0f g A B kt l cs uF Ac k) PD) ∧
      (∃ PZ : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point,
        Rel _ _ (ptZT Fc ks c0f g A B kt l cs z c uF k) PZ) ∧
      ∀ PD PZ : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point,
        Rel _ _ (ptDT Fc ks c0f g A B kt l cs uF Ac k) PD →
        Rel _ _ (ptZT Fc ks c0f g A B kt l cs z c uF k) PZ →
        ∀ m n : ℤ, m • PD = n • PZ → m = 0 ∧ n = 0 := by
  intro cC xC βC hns hns0 hgrp hP0
  simp only [kxChkT0, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    bne_iff_ne, ne_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hA4, hBok⟩, hcs⟩, hzok⟩, hu2⟩, huZ⟩, hAe⟩, hBe⟩, hdisc⟩, hc0⟩, hs0⟩, hze⟩,
    hmG⟩ := hchk
  set s := sT Fc ks g A B kt l cs k with hsdef
  set T₀ := clsT Fc ks g A B kt l cs k with hT₀
  set φ := T.phi0 c0f hFc with hφ
  set jQ := algebraMap ℚ Cc with hjQ
  have hφc : ∀ c : Cc, φ (algebraMap Cc (T.F 0) c) = algebraMap Cc (RatFunc Cc) c :=
    fun c ↦ T.phi0_const c0f hFc c
  have hyok : Fr.ok (yL c0f) := by simp [Fr.ok, CPoly.toPoly]
  have hval : ∀ b : LC 0, codeOK b → φ (T.val 0 b) = ratMap jQ (Fr.val (codeFr (yL c0f) b)) :=
    fun b hb ↦ T.phi0_val c0f hFc b hb
  have hsem : ∀ b : LC 0, (T.MP 0 h0).sem b = T.val 0 b := fun b ↦ T.sem_MP_F 0 h0 b
  have hcC : ∀ i, cC i = T.val 0 (aC Fc ks A i) := fun i ↦ by
    simp only [cC, aC]
    rw [Tower.PrimN.coeff_toPoly_getD]
    exact hsem _
  have hok : ∀ i < 4, codeOK (aC Fc ks A i) := fun i hi ↦ codeOK_of (hA4 i hi)
  have oc : ∀ i < 4, Fr.ok (cF Fc ks c0f A i) := fun i hi ↦ codeFr_ok _ hyok _ (hok i hi)
  have hcF : ∀ i < 4, φ (cC i) = ratMap jQ (Fr.val (cF Fc ks c0f A i)) := fun i hi ↦ by
    rw [hcC]; exact hval _ (hok i hi)
  have ouF : Fr.ok uF := fun h ↦ by
    rw [← CPoly.isZero_iff] at h; rw [h] at hu2; exact absurd hu2 (by decide)
  set u₀ := ratMap jQ (Fr.val uF) with hu₀def
  have hu₀ : u₀ ≠ 0 := by
    rw [hu₀def, map_ne_zero_iff _ (ratMap jQ).injective]
    intro h; rw [← Fr.isZ_iff ouF] at h; rw [h] at huZ; exact absurd huZ (by decide)
  -- the constants: roots of the generators, `r = ∏_T rᵢ`
  have hg0 := (kxGens_spec (Fc := Fc) (ks := ks) 0 g A B kt l cs).2
  have hcF0 : ∀ x ∈ rtsF, ∃ c : Cc, algebraMap Cc (T.F 0) c = x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact T.const_of_sq _ _ (hg0 _ (List.getElem_mem (by omega))) (hrs i hi (by omega))
  obtain ⟨rs, hrsm⟩ := T.consts_of_list rtsF hcF0
  subst hrsm
  have hrsl : rs.length = (kxGens Fc ks 0 g A B kt l cs).length := by
    rw [← hrl, List.length_map]
  have hrs2 : ∀ i (hi : i < rs.length) (hi' : i < (kxGens Fc ks 0 g A B kt l cs).length),
      rs[i] ^ 2 = ((kxGens Fc ks 0 g A B kt l cs)[i] : Cc) := fun i hi hi' ↦ by
    apply (algebraMap Cc (T.F 0)).injective
    have := hrs i (by simpa using hi) hi'
    simp only [List.getElem_map] at this
    rw [map_pow, this, map_ratCast]
  set r := SqrtIndep.prodRoots rs T₀ with hrdef
  have hr2 : r ^ 2 = (s : Cc) := SqrtIndep.prodRoots_sq _ rs hrsl hrs2 T₀
  have hr0 : r ≠ 0 := fun h ↦ by
    rw [h, zero_pow two_ne_zero] at hr2
    exact hs0 (by exact_mod_cast hr2.symm)
  set ρ := algebraMap Cc (RatFunc Cc) r with hρ
  have hρ2 : ρ ^ 2 = (s : RatFunc Cc) := by rw [hρ, ← map_pow, hr2, map_ratCast]
  have hρ0 : ρ ≠ 0 := (map_ne_zero_iff _ (algebraMap Cc (RatFunc Cc)).injective).mpr hr0
  set u := u₀ * ρ with hudef
  have hu : u ≠ 0 := mul_ne_zero hu₀ hρ0
  have o0 := oc 0 (by norm_num)
  have o1 := oc 1 (by norm_num)
  have o2 := oc 2 (by norm_num)
  have o3 := oc 3 (by norm_num)
  have oAFr : Fr.ok (AFr Fc ks c0f A uF) := by
    unfold AFr; okt
  have oBFr : Fr.ok (BFr Fc ks c0f A uF) := by
    unfold BFr; okt
  have hA0 : ratMap jQ (Fr.val (AFr Fc ks c0f A uF)) =
      u₀ ^ 4 * (φ (cC 1 * cC 3) - φ (cC 2) ^ 2 / 3) := by
    simp only [map_mul, map_pow]
    rw [hcF 1 (by norm_num), hcF 2 (by norm_num), hcF 3 (by norm_num)]
    unfold AFr
    simp (disch := okt) only [Fr.val_mul, Fr.val_sub, Fr.val_smulC]
    simp only [map_mul, map_sub, eq_ratCast, map_ratCast, hu₀def]
    ring
  have hB0 : ratMap jQ (Fr.val (BFr Fc ks c0f A uF)) =
      u₀ ^ 6 * (φ (cC 0 * cC 3 ^ 2) - φ (cC 2) * φ (cC 1 * cC 3) / 3 + 2 * φ (cC 2) ^ 3 / 27) := by
    simp only [map_mul, map_pow]
    rw [hcF 0 (by norm_num), hcF 1 (by norm_num), hcF 2 (by norm_num), hcF 3 (by norm_num)]
    unfold BFr
    simp (disch := okt) only [Fr.val_mul, Fr.val_sub, Fr.val_add, Fr.val_smulC]
    simp only [map_mul, map_sub, map_add, eq_ratCast, map_ratCast, hu₀def]
    ring
  have hA : algebraMap Cc[X] (RatFunc Cc) ((CPoly.toPoly Ac).map jQ) =
      u ^ 4 * (φ (cC 1 * cC 3) - φ (cC 2) ^ 2 / 3) := by
    have e' := congrArg (ratMap jQ) ((Fr.eqb_iff (Fr.ok_ofPoly Ac) (Fr.ok_smulC _ oAFr)).mp hAe)
    rw [Fr.val_ofPoly, ratMap_alg] at e'
    rw [e', ratMap_smulC, hA0, hudef, mul_pow, show ρ ^ 4 = (ρ ^ 2) ^ 2 by ring, hρ2]
    push_cast
    ring
  have hB : algebraMap Cc[X] (RatFunc Cc) ((CPoly.toPoly Bc).map jQ) =
      u ^ 6 * (φ (cC 0 * cC 3 ^ 2) - φ (cC 2) * φ (cC 1 * cC 3) / 3 + 2 * φ (cC 2) ^ 3 / 27) := by
    have e' := congrArg (ratMap jQ) ((Fr.eqb_iff (Fr.ok_ofPoly Bc) (Fr.ok_smulC _ oBFr)).mp hBe)
    rw [Fr.val_ofPoly, ratMap_alg] at e'
    rw [e', ratMap_smulC, hB0, hudef, mul_pow, show ρ ^ 6 = (ρ ^ 2) ^ 3 by ring, hρ2]
    push_cast
    ring
  have hΔ : 4 * ((CPoly.toPoly Ac).map jQ) ^ 3 + 27 * ((CPoly.toPoly Bc).map jQ) ^ 2 ≠ 0 := by
    have h1 : CPoly.toPoly (discC Ac Bc) ≠ 0 := fun h ↦ by
      rw [← CPoly.isZero_iff] at h; rw [h] at hdisc; exact absurd hdisc (by decide)
    have h2 : 4 * ((CPoly.toPoly Ac).map jQ) ^ 3 + 27 * ((CPoly.toPoly Bc).map jQ) ^ 2 =
        (CPoly.toPoly (discC Ac Bc)).map jQ := by
      simp only [discC, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_mul, Polynomial.map_add,
        Polynomial.map_mul, Polynomial.map_C]
      simp only [map_ofNat]
      ring
    rw [h2]
    exact (Polynomial.map_ne_zero_iff jQ.injective).mpr h1
  have hBc : ∀ b ∈ B, codeOK b := fun b hb ↦ codeOK_of (hBok b hb)
  have hq : ∀ q : Fin cs.length, inCls Fc ks g A B kt l cs k q = true →
      ∃ Pk : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point,
      Rel _ _ (ptQT Fc ks c0f g A B kt l cs uF k q) Pk ∧
      mapE jQ _ _ Pk = Differential.SuperData.toShort φ (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _ hA hB
        (Point.some _ _ (hns q)) := by
    intro q hin
    have hTq : (kxRep Fc ks 0 g A B kt l cs q).1 = T₀ := by
      simpa [inCls, hT₀] using hin
    obtain ⟨⟨⟨hq1, hq2⟩, hq3⟩, hq4⟩ := hcs q q.2
    have kq := codeOK_of hq1
    have kD := codeOK_of hq2
    have kR := codeOK_of hq3
    have oq := codeFr_ok _ hyok _ kq
    have oD := codeFr_ok _ hyok _ kD
    have oR := codeFr_ok _ hyok _ kR
    have o3' := codeFr_ok _ hyok _ (hok 3 (by norm_num))
    have o2' := codeFr_ok _ hyok _ (hok 2 (by norm_num))
    have oH := hornerFr_ok _ _ hyok oq B hBc
    have hH0 : Fr.val (hornerFr (yL c0f) (codeFr (yL c0f) (kqC Fc ks 0 cs q)) B) ≠ 0 := fun h ↦ by
      rw [← Fr.isZ_iff oH] at h; rw [h] at hq4; exact absurd hq4 (by decide)
    have hHs := T.hornerFr_spec c0f hFc h0 _ oq (T.val 0 (kqC Fc ks 0 cs q)) (hval _ kq) B hBc
    have hB0' : (GPoly.toPoly (T.MP 0 h0) B).eval (T.val 0 (kqC Fc ks 0 cs q)) ≠ 0 := fun h ↦ by
      apply hH0
      rw [h, map_zero] at hHs
      exact (map_eq_zero_iff _ (ratMap jQ).injective).mp hHs
    have oY : Fr.ok (yBaseFr (yL c0f) uF (aC Fc ks A 3) (kxD Fc ks 0 g cs q)
        (kxR Fc ks 0 A kt l cs q) (kqC Fc ks 0 cs q) B) := by
      unfold yBaseFr
      have := Fr.ok_div (Fr.ok_mul oD oR) hH0
      okt
    have oX : Fr.ok (xFr (yL c0f) uF (aC Fc ks A 3) (aC Fc ks A 2) (kqC Fc ks 0 cs q)) := by
      unfold xFr; okt
    refine Differential.SuperData.cert_pt φ jQ (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _ hA hB _ _
      (hns q) _ _ (Fr.ok_smulC _ oX) (Fr.ok_mul oY (Fr.ok_ofPoly _)) ?_ ?_
    · rw [ratMap_smulC, T.xFr_spec c0f hFc uF ouF _ _ _ (hok 3 (by norm_num)) (hok 2 (by norm_num))
        kq, hcC, hcC, hudef, mul_pow, hρ2]
      simp only [xC, hsem]
      rw [← hu₀def]
      ring
    · rw [ratMap_mulC jQ _ oY, T.yBaseFr_spec c0f hFc h0 uF ouF _ _ _ _ B (hok 3 (by norm_num)) kD kR
        kq hBc hB0']
      simp only [βC, hTq, ← SqrtIndep.map_prodRoots, ← hrdef, hcC, hsem]
      simp only [map_mul, map_div₀, map_ratCast, hφc, ← hρ, hudef, ← hu₀def]
      have e4 : (u₀ * ρ) ^ 3 * ρ = u₀ ^ 3 * (s : RatFunc Cc) ^ 2 := by
        rw [← hρ2]; ring
      rw [← hφ, ← hu₀def, ← hsdef]
      set X := φ (T.val 0 (kxD Fc ks 0 g cs ↑q)) * φ (T.val 0 (kxR Fc ks 0 A kt l cs ↑q)) /
        φ (eval (T.val 0 (kqC Fc ks 0 cs ↑q)) (GPoly.toPoly (T.MP 0 h0) B))
      rw [show (u₀ * ρ) ^ 3 * (φ (T.val 0 (aC Fc ks A 3)) *
          (((kxRep Fc ks 0 g A B kt l cs ↑q).2 : RatFunc Cc) * ρ * X)) =
          (u₀ * ρ) ^ 3 * ρ * (φ (T.val 0 (aC Fc ks A 3)) *
          (((kxRep Fc ks 0 g A B kt l cs ↑q).2 : RatFunc Cc) * X)) by ring, e4]
      push_cast
      ring
  -- the sum `D` over the class
  set fl := (List.finRange cs.length).filter fun q : Fin cs.length ↦
    inCls Fc ks g A B kt l cs k (q : ℕ) with hfl
  set lst : List (ℤ × PtC ℚ × (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Point) :=
    fl.map (fun q : Fin cs.length ↦ (mKc Fc ks g A B kt l cs k (q : ℕ) /
        (mG Fc ks g A B kt l cs k : ℤ), ptQT Fc ks c0f g A B kt l cs uF k (q : ℕ),
          Point.some _ _ (hns q))) with hlst
  obtain ⟨PD, hRD, hmD⟩ := Differential.SuperData.cert_sum φ jQ (cC 3) (cC 2) (cC 1) (cC 0) u hu
    _ _ hA hB Ac rfl lst (fun e' he' ↦ by
      rw [hlst, List.mem_map] at he'
      obtain ⟨q, hqm, rfl⟩ := he'
      have hqm' := hqm
      rw [hfl, List.mem_filter] at hqm'
      exact hq q hqm'.2)
  have hl1 : lst.map (fun e ↦ (e.1, e.2.1)) = fl.map (fun q : Fin cs.length ↦
      (mKc Fc ks g A B kt l cs k (q : ℕ) / (mG Fc ks g A B kt l cs k : ℤ),
        ptQT Fc ks c0f g A B kt l cs uF k (q : ℕ))) := by
    rw [hlst, List.map_map]; rfl
  rw [hl1] at hRD
  have hdvd : ∀ q : Fin cs.length, (mG Fc ks g A B kt l cs k : ℤ) ∣ mKc Fc ks g A B kt l cs k q :=
    fun q ↦ foldr_gcd_dvd _ _ (List.mem_map.mpr ⟨q, List.mem_range.mpr q.2, rfl⟩)
  have hz0 : ∀ q : Fin cs.length, inCls Fc ks g A B kt l cs k q = false →
      mKc Fc ks g A B kt l cs k q = 0 := fun q hq ↦ by
    unfold mKc
    unfold inCls clsT at hq
    rw [List.getD_eq_getElem _ _ k.2] at hq ⊢
    simp [hq]
  have hD : ∑ q, ((Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
      (kxCl 0 g A B kt l cs) k q : ℕ) : ℤ) • Point.some _ _ (hns q) =
      (mG Fc ks g A B kt l cs k : ℤ) • (lst.map fun e ↦ e.1 • e.2.2).sum := by
    have e1 : ∑ q, ((Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
        (kxCl 0 g A B kt l cs) k q : ℕ) : ℤ) • Point.some _ _ (hns q) =
        ∑ q : Fin cs.length, ((mG Fc ks g A B kt l cs k : ℤ) * (mKc Fc ks g A B kt l cs k q /
          (mG Fc ks g A B kt l cs k : ℤ))) • Point.some _ _ (hns q) := by
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [Int.mul_ediv_cancel' (hdvd q), mK_eq_mKc]
    rw [e1, Fin.sum_univ_def, sum_map_filter_of_zero
      (fun q : Fin cs.length ↦ inCls Fc ks g A B kt l cs k (q : ℕ)) _ _
      (fun q _ hq ↦ by rw [hz0 q hq, Int.zero_ediv, mul_zero, zero_smul]), ← hfl, hlst,
      List.map_map, List.smul_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q _
    simp only [Function.comp_apply, smul_smul]
  -- the point `P₊`
  have kz := codeOK_of hzok
  have ozF := codeFr_ok _ hyok _ kz
  have hzeq := (Fr.eqb_iff (Fr.ok_mul (Fr.ok_mul ozF ozF) o0) (Fr.ok_ofPoly _)).mp hze
  rw [Fr.val_mul (Fr.ok_mul ozF ozF) o0, Fr.val_mul ozF ozF, Fr.val_ofPoly] at hzeq
  have hκr : algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly [s * c * c]) = ((s * c * c : ℚ) : RatFunc ℚ) := by
    simp [CPoly.toPoly, RatFunc.algebraMap_C]
  rw [hκr] at hzeq
  have hφz : φ (T.val 0 z) = ratMap jQ (Fr.val (codeFr (yL c0f) z)) := hval z kz
  have hw : (b₀ * T.val 0 z) ^ 2 = ((s * c * c : ℚ) : T.F 0) := by
    apply φ.injective
    have hb : φ b₀ ^ 2 = ratMap jQ (Fr.val (cF Fc ks c0f A 0)) := by
      rw [← map_pow, hb₀, hsem, ← hcF 0 (by norm_num), hcC]; rfl
    have e2 := congrArg (ratMap jQ) hzeq
    simp only [map_mul, map_ratCast] at e2
    rw [mul_pow, map_mul, map_pow, map_pow, hb, hφz, map_ratCast]
    linear_combination e2
  have hκ0 : s * c * c ≠ 0 := mul_ne_zero (mul_ne_zero hs0 hc0) hc0
  have hvz : T.val 0 z ≠ 0 := fun h ↦ by
    rw [h, mul_zero, zero_pow two_ne_zero] at hw
    exact hκ0 (by exact_mod_cast hw.symm)
  have hzne : Fr.val (codeFr (yL c0f) z) ≠ 0 := fun h ↦ by
    rw [h, map_zero] at hφz
    exact hvz ((map_eq_zero_iff _ φ.injective).mp hφz)
  set b₀s : T.F 0 := algebraMap Cc (T.F 0) (r * c) / T.val 0 z with hb₀s
  have hsq : (b₀ * T.val 0 z) ^ 2 = (algebraMap Cc (T.F 0) (r * c)) ^ 2 := by
    rw [hw, ← map_pow, mul_pow, hr2]; push_cast; ring
  have hns0s : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
      (cC 3 * 0) (cC 3 * b₀s) ∧
      ∀ h' : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * 0) (cC 3 * b₀s),
        Point.some _ _ hns0 = Point.some _ _ h' ∨ Point.some _ _ hns0 = -Point.some _ _ h' := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · have hb : b₀ = b₀s := by rw [hb₀s]; field_simp; linear_combination h
      subst hb
      exact ⟨hns0, fun h' ↦ Or.inl rfl⟩
    · have hb : b₀ = -b₀s := by rw [hb₀s]; field_simp; linear_combination h
      have hneg := (nonsingular_neg (W' := Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0))
        _ _).mpr hns0
      have hy : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).negY (cC 3 * 0) (cC 3 * b₀) =
          cC 3 * b₀s := by
        simp [negY, FFHeight.longF, hb]
      refine ⟨hy ▸ hneg, fun h' ↦ Or.inr ?_⟩
      rw [WeierstrassCurve.Affine.Point.neg_some]
      simp only [Point.some.injEq, true_and]
      simp [negY, FFHeight.longF, hb]
  obtain ⟨hns0s', hsign⟩ := hns0s
  have o3' := codeFr_ok _ hyok _ (hok 3 (by norm_num))
  have o2' := codeFr_ok _ hyok _ (hok 2 (by norm_num))
  have kn : codeOK ([] : LC 0) := fun r hr ↦ absurd hr (List.not_mem_nil)
  have on := codeFr_ok _ hyok _ kn
  have oXZ : Fr.ok (xFr (yL c0f) uF (aC Fc ks A 3) (aC Fc ks A 2) []) := by unfold xFr; okt
  have odiv := Fr.ok_div (Fr.ok_ofPoly [1]) hzne
  have oYZ : Fr.ok (yZ Fc ks c0f A z uF) := by unfold yZ; okt
  have hv0 : T.val 0 ([] : LC 0) = 0 := by
    apply φ.injective
    rw [hval _ kn, map_zero]
    simp [codeFr, Fr.val_ofPoly, CPoly.toPoly]
  obtain ⟨PZ, hRZ, hmZ⟩ := Differential.SuperData.cert_pt φ jQ (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _
    hA hB _ _ hns0s' (Fr.smulC s (xFr (yL c0f) uF (aC Fc ks A 3) (aC Fc ks A 2) []))
    (Fr.mul (yZ Fc ks c0f A z uF) (Fr.ofPoly [s * s * c]))
    (Fr.ok_smulC _ oXZ) (Fr.ok_mul oYZ (Fr.ok_ofPoly _)) (by
      rw [ratMap_smulC, T.xFr_spec c0f hFc uF ouF _ _ _ (hok 3 (by norm_num)) (hok 2 (by norm_num))
        kn, hcC, hcC, hv0, hudef, mul_pow, hρ2, ← hu₀def]
      ring) (by
      rw [ratMap_mulC jQ _ oYZ]
      unfold yZ
      simp only [Fr.val_mul (Fr.ok_mul ouF (Fr.ok_mul ouF ouF)) (Fr.ok_mul o3 odiv),
        Fr.val_mul ouF (Fr.ok_mul ouF ouF), Fr.val_mul ouF ouF, Fr.val_mul o3 odiv,
        Fr.val_div (Fr.ok_ofPoly [1]) ozF hzne, Fr.val_ofPoly]
      simp only [map_mul, map_div₀, hb₀s, ← hcF 3 (by norm_num), ← hφz, hφc, ← hρ, hudef,
        ← hu₀def]
      have h1 : ratMap jQ (algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly [1])) = 1 := by
        simp [CPoly.toPoly]
      rw [h1]
      have e4 : (u₀ * ρ) ^ 3 * ρ = u₀ ^ 3 * (s : RatFunc Cc) ^ 2 := by rw [← hρ2]; ring
      have hcc : algebraMap Cc (RatFunc Cc) (c : Cc) = (c : RatFunc Cc) := map_ratCast _ _
      rw [hcc]
      rw [show (u₀ * ρ) ^ 3 * (φ (cC 3) * (ρ * (c : RatFunc Cc) / φ (T.val 0 z))) =
        (u₀ * ρ) ^ 3 * ρ * (φ (cC 3) * ((c : RatFunc Cc) / φ (T.val 0 z))) by ring, e4]
      push_cast
      ring)
  refine ⟨⟨PD, hRD⟩, ⟨PZ, hRZ⟩, ?_⟩
  intro PD' PZ' hRD' hRZ' m n hmn
  rw [rel_unique hRD' hRD, rel_unique hRZ' hRZ] at hmn
  set D' := (lst.map fun e ↦ e.1 • e.2.2).sum with hD'
  have e1 := congrArg (mapE jQ _ _) hmn
  rw [map_zsmul, map_zsmul, hmD, hmZ] at e1
  have hrel0 := Differential.SuperData.rel_of_toShort φ (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _ hA hB
    D' (Point.some _ _ hns0s') m n (by convert e1)
  have hrel : m • D' = n • Point.some _ _ hns0s' := by convert hrel0
  set Dfull := ∑ q, ((Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
    (kxCl 0 g A B kt l cs) k q : ℕ) : ℤ) • Point.some _ _ (hns q) with hDfull
  set G := (mG Fc ks g A B kt l cs k : ℤ) with hG
  have hG0 : G ≠ 0 := by simp only [hG]; exact_mod_cast hmG
  -- `Z′ = s P₊`, `s = ±1`
  obtain ⟨s, hs, hZ⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ Point.some _ _ hns0s' = s • Point.some _ _ hns0 := by
    rcases hsign hns0s' with h | h
    · exact ⟨1, Or.inl rfl, by rw [one_zsmul, h]⟩
    · exact ⟨-1, Or.inr rfl, by rw [neg_one_zsmul, h, neg_neg]⟩
  have hfull : m • Dfull = (G * n * s) • Point.some _ _ hns0 := by
    rw [hD, smul_smul, mul_comm m G, ← smul_smul, hrel, hZ, smul_smul, smul_smul]
  have hgrp' : ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • Dfull + (2 * μ) • Point.some _ _ hns0 ≠ 0 :=
    fun N hN μ ↦ by convert hgrp N hN μ using 3
  rcases lt_trichotomy m 0 with hm | hm | hm
  · exfalso
    apply hgrp' m.natAbs (by omega) (G * n * s)
    have hN : ((m.natAbs : ℕ) : ℤ) = -m := by omega
    rw [hN, show 2 * -m = -(2 * m) by ring, neg_smul, ← smul_smul, hfull, smul_smul]
    abel
  · subst hm
    rw [zero_smul] at hfull
    have := hP0 _ hfull.symm
    have hs0 : s ≠ 0 := by rcases hs with h | h <;> simp [h]
    refine ⟨rfl, ?_⟩
    rcases mul_eq_zero.mp this with h | h
    · exact (mul_eq_zero.mp h).resolve_left hG0
    · exact absurd h hs0
  · exfalso
    apply hgrp' m.natAbs (by omega) (-(G * n * s))
    have hN : ((m.natAbs : ℕ) : ℤ) = m := by omega
    rw [hN, ← smul_smul, hfull, smul_smul]
    rw [← add_smul]; ring_nf; simp

variable (κ : ℚ)

set_option maxHeartbeats 16000000 in
open Classical in
theorem indep_of_grpC0 (hFc : Fc = [c0f, [1]]) (h0 : T.Tr 0)
    (k : Fin (kxCls Fc ks 0 g A B kt l cs).length)
    [Fact (¬ IsSquare (sT Fc ks g A B kt l cs k * κ))]
    (hchk : kxChkC0 Fc ks c0f g A B kt l cs z κ uF Ac Bc k = true)
    (rtsF : List (T.F 0)) (hrl : rtsF.length = (kxGens Fc ks 0 g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks 0 g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks 0 g A B kt l cs)[i] : T.F 0))
    (b₀ : T.F 0) (hb₀ : b₀ ^ 2 = (T.MP 0 h0).sem (A.getD 0 (MO Fc ks 0).zero)) :
    let cC : ℕ → T.F 0 := (fun i ↦ (GPoly.toPoly (T.MP 0 h0) A).coeff i)
    let xC : Fin cs.length → T.F 0 := (fun q ↦ (T.MP 0 h0).sem (kqC Fc ks 0 cs q))
    let βC : Fin cs.length → T.F 0 := (fun q ↦
      ((kxRep Fc ks 0 g A B kt l cs q).2 : T.F 0) *
        SqrtIndep.prodRoots rtsF (kxRep Fc ks 0 g A B kt l cs q).1 *
        ((T.MP 0 h0).sem (kxD Fc ks 0 g cs q) * (T.MP 0 h0).sem (kxR Fc ks 0 A kt l cs q) /
          (GPoly.toPoly (T.MP 0 h0) B).eval ((T.MP 0 h0).sem (kqC Fc ks 0 cs q))))
    ∀ (hns : ∀ q, (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * xC q) (cC 3 * βC q))
      (hns0 : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * 0) (cC 3 * b₀)),
      (∀ n : ℤ, n • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
          (kxCl 0 g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) = 0 →
          n = 0) →
      (∃ PD : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point,
        Rel _ _ (ptDT Fc ks c0f g A B kt l cs uF Ac k) PD) ∧
      ∀ PD : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point,
        Rel _ _ (ptDT Fc ks c0f g A B kt l cs uF Ac k) PD → ∀ n : ℤ, n • PD = 0 → n = 0 := by
  intro cC xC βC hns hns0 hntF
  simp only [kxChkC0, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    bne_iff_ne, ne_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hA4, hBok⟩, hcs⟩, hzok⟩, hu2⟩, huZ⟩, hAe⟩, hBe⟩, hdisc⟩, hκ⟩, hs0⟩, hze⟩,
    hmG⟩ := hchk
  set s := sT Fc ks g A B kt l cs k with hsdef
  set T₀ := clsT Fc ks g A B kt l cs k with hT₀
  set φ := T.phi0 c0f hFc with hφ
  set jQ := algebraMap ℚ Cc with hjQ
  have hφc : ∀ c : Cc, φ (algebraMap Cc (T.F 0) c) = algebraMap Cc (RatFunc Cc) c :=
    fun c ↦ T.phi0_const c0f hFc c
  have hyok : Fr.ok (yL c0f) := by simp [Fr.ok, CPoly.toPoly]
  have hval : ∀ b : LC 0, codeOK b → φ (T.val 0 b) = ratMap jQ (Fr.val (codeFr (yL c0f) b)) :=
    fun b hb ↦ T.phi0_val c0f hFc b hb
  have hsem : ∀ b : LC 0, (T.MP 0 h0).sem b = T.val 0 b := fun b ↦ T.sem_MP_F 0 h0 b
  have hcC : ∀ i, cC i = T.val 0 (aC Fc ks A i) := fun i ↦ by
    simp only [cC, aC]
    rw [Tower.PrimN.coeff_toPoly_getD]
    exact hsem _
  have hok : ∀ i < 4, codeOK (aC Fc ks A i) := fun i hi ↦ codeOK_of (hA4 i hi)
  have oc : ∀ i < 4, Fr.ok (cF Fc ks c0f A i) := fun i hi ↦ codeFr_ok _ hyok _ (hok i hi)
  have hcF : ∀ i < 4, φ (cC i) = ratMap jQ (Fr.val (cF Fc ks c0f A i)) := fun i hi ↦ by
    rw [hcC]; exact hval _ (hok i hi)
  have ouF : Fr.ok uF := fun h ↦ by
    rw [← CPoly.isZero_iff] at h; rw [h] at hu2; exact absurd hu2 (by decide)
  set u₀ := ratMap jQ (Fr.val uF) with hu₀def
  have hu₀ : u₀ ≠ 0 := by
    rw [hu₀def, map_ne_zero_iff _ (ratMap jQ).injective]
    intro h; rw [← Fr.isZ_iff ouF] at h; rw [h] at huZ; exact absurd huZ (by decide)
  -- the constants: roots of the generators, `r = ∏_T rᵢ`
  have hg0 := (kxGens_spec (Fc := Fc) (ks := ks) 0 g A B kt l cs).2
  have hcF0 : ∀ x ∈ rtsF, ∃ c : Cc, algebraMap Cc (T.F 0) c = x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact T.const_of_sq _ _ (hg0 _ (List.getElem_mem (by omega))) (hrs i hi (by omega))
  obtain ⟨rs, hrsm⟩ := T.consts_of_list rtsF hcF0
  subst hrsm
  have hrsl : rs.length = (kxGens Fc ks 0 g A B kt l cs).length := by
    rw [← hrl, List.length_map]
  have hrs2 : ∀ i (hi : i < rs.length) (hi' : i < (kxGens Fc ks 0 g A B kt l cs).length),
      rs[i] ^ 2 = ((kxGens Fc ks 0 g A B kt l cs)[i] : Cc) := fun i hi hi' ↦ by
    apply (algebraMap Cc (T.F 0)).injective
    have := hrs i (by simpa using hi) hi'
    simp only [List.getElem_map] at this
    rw [map_pow, this, map_ratCast]
  set r := SqrtIndep.prodRoots rs T₀ with hrdef
  have hr2 : r ^ 2 = (s : Cc) := SqrtIndep.prodRoots_sq _ rs hrsl hrs2 T₀
  have hr0 : r ≠ 0 := fun h ↦ by
    rw [h, zero_pow two_ne_zero] at hr2
    exact hs0 (by exact_mod_cast hr2.symm)
  set ρ := algebraMap Cc (RatFunc Cc) r with hρ
  have hρ2 : ρ ^ 2 = (s : RatFunc Cc) := by rw [hρ, ← map_pow, hr2, map_ratCast]
  have hρ0 : ρ ≠ 0 := (map_ne_zero_iff _ (algebraMap Cc (RatFunc Cc)).injective).mpr hr0
  set u := u₀ * ρ with hudef
  have hu : u ≠ 0 := mul_ne_zero hu₀ hρ0
  have o0 := oc 0 (by norm_num)
  have o1 := oc 1 (by norm_num)
  have o2 := oc 2 (by norm_num)
  have o3 := oc 3 (by norm_num)
  have oAFr : Fr.ok (AFr Fc ks c0f A uF) := by
    unfold AFr; okt
  have oBFr : Fr.ok (BFr Fc ks c0f A uF) := by
    unfold BFr; okt
  have hA0 : ratMap jQ (Fr.val (AFr Fc ks c0f A uF)) =
      u₀ ^ 4 * (φ (cC 1 * cC 3) - φ (cC 2) ^ 2 / 3) := by
    simp only [map_mul, map_pow]
    rw [hcF 1 (by norm_num), hcF 2 (by norm_num), hcF 3 (by norm_num)]
    unfold AFr
    simp (disch := okt) only [Fr.val_mul, Fr.val_sub, Fr.val_smulC]
    simp only [map_mul, map_sub, eq_ratCast, map_ratCast, hu₀def]
    ring
  have hB0 : ratMap jQ (Fr.val (BFr Fc ks c0f A uF)) =
      u₀ ^ 6 * (φ (cC 0 * cC 3 ^ 2) - φ (cC 2) * φ (cC 1 * cC 3) / 3 + 2 * φ (cC 2) ^ 3 / 27) := by
    simp only [map_mul, map_pow]
    rw [hcF 0 (by norm_num), hcF 1 (by norm_num), hcF 2 (by norm_num), hcF 3 (by norm_num)]
    unfold BFr
    simp (disch := okt) only [Fr.val_mul, Fr.val_sub, Fr.val_add, Fr.val_smulC]
    simp only [map_mul, map_sub, map_add, eq_ratCast, map_ratCast, hu₀def]
    ring
  have hA : algebraMap Cc[X] (RatFunc Cc) ((CPoly.toPoly Ac).map jQ) =
      u ^ 4 * (φ (cC 1 * cC 3) - φ (cC 2) ^ 2 / 3) := by
    have e' := congrArg (ratMap jQ) ((Fr.eqb_iff (Fr.ok_ofPoly Ac) (Fr.ok_smulC _ oAFr)).mp hAe)
    rw [Fr.val_ofPoly, ratMap_alg] at e'
    rw [e', ratMap_smulC, hA0, hudef, mul_pow, show ρ ^ 4 = (ρ ^ 2) ^ 2 by ring, hρ2]
    push_cast
    ring
  have hB : algebraMap Cc[X] (RatFunc Cc) ((CPoly.toPoly Bc).map jQ) =
      u ^ 6 * (φ (cC 0 * cC 3 ^ 2) - φ (cC 2) * φ (cC 1 * cC 3) / 3 + 2 * φ (cC 2) ^ 3 / 27) := by
    have e' := congrArg (ratMap jQ) ((Fr.eqb_iff (Fr.ok_ofPoly Bc) (Fr.ok_smulC _ oBFr)).mp hBe)
    rw [Fr.val_ofPoly, ratMap_alg] at e'
    rw [e', ratMap_smulC, hB0, hudef, mul_pow, show ρ ^ 6 = (ρ ^ 2) ^ 3 by ring, hρ2]
    push_cast
    ring
  have hΔ : 4 * ((CPoly.toPoly Ac).map jQ) ^ 3 + 27 * ((CPoly.toPoly Bc).map jQ) ^ 2 ≠ 0 := by
    have h1 : CPoly.toPoly (discC Ac Bc) ≠ 0 := fun h ↦ by
      rw [← CPoly.isZero_iff] at h; rw [h] at hdisc; exact absurd hdisc (by decide)
    have h2 : 4 * ((CPoly.toPoly Ac).map jQ) ^ 3 + 27 * ((CPoly.toPoly Bc).map jQ) ^ 2 =
        (CPoly.toPoly (discC Ac Bc)).map jQ := by
      simp only [discC, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_mul, Polynomial.map_add,
        Polynomial.map_mul, Polynomial.map_C]
      simp only [map_ofNat]
      ring
    rw [h2]
    exact (Polynomial.map_ne_zero_iff jQ.injective).mpr h1
  have hBc : ∀ b ∈ B, codeOK b := fun b hb ↦ codeOK_of (hBok b hb)
  have hq : ∀ q : Fin cs.length, inCls Fc ks g A B kt l cs k q = true →
      ∃ Pk : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point,
      Rel _ _ (ptQT Fc ks c0f g A B kt l cs uF k q) Pk ∧
      mapE jQ _ _ Pk = Differential.SuperData.toShort φ (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _ hA hB
        (Point.some _ _ (hns q)) := by
    intro q hin
    have hTq : (kxRep Fc ks 0 g A B kt l cs q).1 = T₀ := by
      simpa [inCls, hT₀] using hin
    obtain ⟨⟨⟨hq1, hq2⟩, hq3⟩, hq4⟩ := hcs q q.2
    have kq := codeOK_of hq1
    have kD := codeOK_of hq2
    have kR := codeOK_of hq3
    have oq := codeFr_ok _ hyok _ kq
    have oD := codeFr_ok _ hyok _ kD
    have oR := codeFr_ok _ hyok _ kR
    have o3' := codeFr_ok _ hyok _ (hok 3 (by norm_num))
    have o2' := codeFr_ok _ hyok _ (hok 2 (by norm_num))
    have oH := hornerFr_ok _ _ hyok oq B hBc
    have hH0 : Fr.val (hornerFr (yL c0f) (codeFr (yL c0f) (kqC Fc ks 0 cs q)) B) ≠ 0 := fun h ↦ by
      rw [← Fr.isZ_iff oH] at h; rw [h] at hq4; exact absurd hq4 (by decide)
    have hHs := T.hornerFr_spec c0f hFc h0 _ oq (T.val 0 (kqC Fc ks 0 cs q)) (hval _ kq) B hBc
    have hB0' : (GPoly.toPoly (T.MP 0 h0) B).eval (T.val 0 (kqC Fc ks 0 cs q)) ≠ 0 := fun h ↦ by
      apply hH0
      rw [h, map_zero] at hHs
      exact (map_eq_zero_iff _ (ratMap jQ).injective).mp hHs
    have oY : Fr.ok (yBaseFr (yL c0f) uF (aC Fc ks A 3) (kxD Fc ks 0 g cs q)
        (kxR Fc ks 0 A kt l cs q) (kqC Fc ks 0 cs q) B) := by
      unfold yBaseFr
      have := Fr.ok_div (Fr.ok_mul oD oR) hH0
      okt
    have oX : Fr.ok (xFr (yL c0f) uF (aC Fc ks A 3) (aC Fc ks A 2) (kqC Fc ks 0 cs q)) := by
      unfold xFr; okt
    refine Differential.SuperData.cert_pt φ jQ (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _ hA hB _ _
      (hns q) _ _ (Fr.ok_smulC _ oX) (Fr.ok_mul oY (Fr.ok_ofPoly _)) ?_ ?_
    · rw [ratMap_smulC, T.xFr_spec c0f hFc uF ouF _ _ _ (hok 3 (by norm_num)) (hok 2 (by norm_num))
        kq, hcC, hcC, hudef, mul_pow, hρ2]
      simp only [xC, hsem]
      rw [← hu₀def]
      ring
    · rw [ratMap_mulC jQ _ oY, T.yBaseFr_spec c0f hFc h0 uF ouF _ _ _ _ B (hok 3 (by norm_num)) kD kR
        kq hBc hB0']
      simp only [βC, hTq, ← SqrtIndep.map_prodRoots, ← hrdef, hcC, hsem]
      simp only [map_mul, map_div₀, map_ratCast, hφc, ← hρ, hudef, ← hu₀def]
      have e4 : (u₀ * ρ) ^ 3 * ρ = u₀ ^ 3 * (s : RatFunc Cc) ^ 2 := by
        rw [← hρ2]; ring
      rw [← hφ, ← hu₀def, ← hsdef]
      set X := φ (T.val 0 (kxD Fc ks 0 g cs ↑q)) * φ (T.val 0 (kxR Fc ks 0 A kt l cs ↑q)) /
        φ (eval (T.val 0 (kqC Fc ks 0 cs ↑q)) (GPoly.toPoly (T.MP 0 h0) B))
      rw [show (u₀ * ρ) ^ 3 * (φ (T.val 0 (aC Fc ks A 3)) *
          (((kxRep Fc ks 0 g A B kt l cs ↑q).2 : RatFunc Cc) * ρ * X)) =
          (u₀ * ρ) ^ 3 * ρ * (φ (T.val 0 (aC Fc ks A 3)) *
          (((kxRep Fc ks 0 g A B kt l cs ↑q).2 : RatFunc Cc) * X)) by ring, e4]
      push_cast
      ring
  -- the field `k₀ = ℚ(√δ)`, `δ = s κ`, and its embedding `√δ ↦ r w`
  set δ := s * κ with hδ
  have kz := codeOK_of hzok
  have ozF := codeFr_ok _ hyok _ kz
  have hzeq := (Fr.eqb_iff (Fr.ok_mul (Fr.ok_mul ozF ozF) o0) (Fr.ok_ofPoly _)).mp hze
  rw [Fr.val_mul (Fr.ok_mul ozF ozF) o0, Fr.val_mul ozF ozF, Fr.val_ofPoly] at hzeq
  have hκr : algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly [κ]) = ((κ : ℚ) : RatFunc ℚ) := by
    simp [CPoly.toPoly, RatFunc.algebraMap_C]
  rw [hκr] at hzeq
  have hφz : φ (T.val 0 z) = ratMap jQ (Fr.val (codeFr (yL c0f) z)) := hval z kz
  have hw : (b₀ * T.val 0 z) ^ 2 = ((κ : ℚ) : T.F 0) := by
    apply φ.injective
    have hb : φ b₀ ^ 2 = ratMap jQ (Fr.val (cF Fc ks c0f A 0)) := by
      rw [← map_pow, hb₀, hsem, ← hcF 0 (by norm_num), hcC]; rfl
    have e2 := congrArg (ratMap jQ) hzeq
    simp only [map_mul, map_ratCast] at e2
    rw [mul_pow, map_mul, map_pow, map_pow, hb, hφz, map_ratCast]
    linear_combination e2
  have hvz : T.val 0 z ≠ 0 := fun h ↦ by
    rw [h, mul_zero, zero_pow two_ne_zero] at hw
    exact hκ (by exact_mod_cast hw.symm)
  have hzne : Fr.val (codeFr (yL c0f) z) ≠ 0 := fun h ↦ by
    rw [h, map_zero] at hφz
    exact hvz ((map_eq_zero_iff _ φ.injective).mp hφz)
  obtain ⟨w, hwc⟩ := T.const_of_sq _ _ hκ hw
  have hw2 : w ^ 2 = (κ : Cc) := by
    apply (algebraMap Cc (T.F 0)).injective
    rw [map_pow, hwc, hw, map_ratCast]
  have ht : (r * w) * (r * w) = algebraMap ℚ Cc δ := by
    rw [show (r * w) * (r * w) = r ^ 2 * w ^ 2 by ring, hr2, hw2, hδ, eq_ratCast]; push_cast; ring
  set e := algebraMap ℚ (QuadraticAlgebra ℚ δ 0) with he
  set j : QuadraticAlgebra ℚ δ 0 →+* Cc := (qaEmbed δ (r * w) ht).toRingHom with hj
  have hjω : j ⟨0, 1⟩ = r * w := qaEmbed_omega δ (r * w) ht
  have hje : j.comp e = jQ := RingHom.ext_rat _ _
  have hA' : algebraMap Cc[X] (RatFunc Cc) (((CPoly.toPoly Ac).map e).map j) =
      u ^ 4 * (φ (cC 1 * cC 3) - φ (cC 2) ^ 2 / 3) := by rw [Polynomial.map_map, hje]; exact hA
  have hB' : algebraMap Cc[X] (RatFunc Cc) (((CPoly.toPoly Bc).map e).map j) =
      u ^ 6 * (φ (cC 0 * cC 3 ^ 2) - φ (cC 2) * φ (cC 1 * cC 3) / 3 + 2 * φ (cC 2) ^ 3 / 27) := by
    rw [Polynomial.map_map, hje]; exact hB
  -- transfer of the class points to `ℚ → k₀ → Cc`
  have transfer : ∀ (x y : T.F 0) (hxy : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1)
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
    inCls Fc ks g A B kt l cs k (q : ℕ) with hfl
  set lst : List (ℤ × PtC ℚ × (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Point) :=
    fl.map (fun q : Fin cs.length ↦ (mKc Fc ks g A B kt l cs k (q : ℕ) /
        (mG Fc ks g A B kt l cs k : ℤ), ptQT Fc ks c0f g A B kt l cs uF k (q : ℕ),
          Point.some _ _ (hns q))) with hlst
  obtain ⟨PD, hRD, hmD⟩ := Differential.SuperData.cert_sumψ φ e j (cC 3) (cC 2) (cC 1) (cC 0) u hu
    _ _ hA' hB' Ac rfl lst (fun e' he' ↦ by
      rw [hlst, List.mem_map] at he'
      obtain ⟨q, hqm, rfl⟩ := he'
      have hqm' := hqm
      rw [hfl, List.mem_filter] at hqm'
      obtain ⟨Pk, hRk, hmk⟩ := hq q hqm'.2
      exact ⟨Pk, hRk, transfer _ _ _ Pk hmk⟩)
  have hl1 : lst.map (fun e ↦ (e.1, e.2.1)) = fl.map (fun q : Fin cs.length ↦
      (mKc Fc ks g A B kt l cs k (q : ℕ) / (mG Fc ks g A B kt l cs k : ℤ),
        ptQT Fc ks c0f g A B kt l cs uF k (q : ℕ))) := by
    rw [hlst, List.map_map]; rfl
  rw [hl1] at hRD
  have hdvd : ∀ q : Fin cs.length, (mG Fc ks g A B kt l cs k : ℤ) ∣ mKc Fc ks g A B kt l cs k q :=
    fun q ↦ foldr_gcd_dvd _ _ (List.mem_map.mpr ⟨q, List.mem_range.mpr q.2, rfl⟩)
  have hz0 : ∀ q : Fin cs.length, inCls Fc ks g A B kt l cs k q = false →
      mKc Fc ks g A B kt l cs k q = 0 := fun q hq ↦ by
    unfold mKc
    unfold inCls clsT at hq
    rw [List.getD_eq_getElem _ _ k.2] at hq ⊢
    simp [hq]
  have hD : ∑ q, ((Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
      (kxCl 0 g A B kt l cs) k q : ℕ) : ℤ) • Point.some _ _ (hns q) =
      (mG Fc ks g A B kt l cs k : ℤ) • (lst.map fun e ↦ e.1 • e.2.2).sum := by
    have e1 : ∑ q, ((Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
        (kxCl 0 g A B kt l cs) k q : ℕ) : ℤ) • Point.some _ _ (hns q) =
        ∑ q : Fin cs.length, ((mG Fc ks g A B kt l cs k : ℤ) * (mKc Fc ks g A B kt l cs k q /
          (mG Fc ks g A B kt l cs k : ℤ))) • Point.some _ _ (hns q) := by
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [Int.mul_ediv_cancel' (hdvd q), mK_eq_mKc]
    rw [e1, Fin.sum_univ_def, sum_map_filter_of_zero
      (fun q : Fin cs.length ↦ inCls Fc ks g A B kt l cs k (q : ℕ)) _ _
      (fun q _ hq ↦ by rw [hz0 q hq, Int.zero_ediv, mul_zero, zero_smul]), ← hfl, hlst,
      List.map_map, List.smul_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q _
    simp only [Function.comp_apply, smul_smul]
  -- the point `P₊` over `k₀`
  set b₀s : T.F 0 := algebraMap Cc (T.F 0) w / T.val 0 z with hb₀s
  have hb₀e : b₀ = b₀s := by rw [hb₀s, hwc]; field_simp
  have o3' := codeFr_ok _ hyok _ (hok 3 (by norm_num))
  have o2' := codeFr_ok _ hyok _ (hok 2 (by norm_num))
  have kn : codeOK ([] : LC 0) := fun r hr ↦ absurd hr (List.not_mem_nil)
  have on := codeFr_ok _ hyok _ kn
  have oXZ : Fr.ok (xFr (yL c0f) uF (aC Fc ks A 3) (aC Fc ks A 2) []) := by unfold xFr; okt
  have odiv := Fr.ok_div (Fr.ok_ofPoly [1]) hzne
  have oYZ : Fr.ok (yZ Fc ks c0f A z uF) := by unfold yZ; okt
  have hv0 : T.val 0 ([] : LC 0) = 0 := by
    apply φ.injective
    rw [hval _ kn, map_zero]
    simp [codeFr, Fr.val_ofPoly, CPoly.toPoly]
  have hratm : ∀ f : Fr ℚ, ratMap j (Fr.val (frMap e f)) = ratMap jQ (Fr.val f) := fun f ↦ by
    rw [frMap_val, ratMap_comp', hje]
  set fx0 := frMap e (Fr.smulC s (xFr (yL c0f) uF (aC Fc ks A 3) (aC Fc ks A 2) [])) with hfx0
  set fy0 := Fr.mul (frMap e (Fr.mul (yZ Fc ks c0f A z uF) (Fr.ofPoly [s])))
    (Fr.ofPoly [(⟨0, 1⟩ : QuadraticAlgebra ℚ δ 0)]) with hfy0
  have ofx0 : Fr.ok fx0 := frMap_ok e _ (Fr.ok_smulC _ oXZ)
  have ofy1 : Fr.ok (frMap e (Fr.mul (yZ Fc ks c0f A z uF) (Fr.ofPoly [s]))) :=
    frMap_ok e _ (Fr.ok_mul oYZ (Fr.ok_ofPoly _))
  have ofy0 : Fr.ok fy0 := Fr.ok_mul ofy1 (Fr.ok_ofPoly _)
  obtain ⟨PZ, hRZ, hmZ⟩ := Differential.SuperData.cert_pt φ j (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _
    hA' hB' _ _ hns0 fx0 fy0 ofx0 ofy0 (by
      rw [hfx0, hratm, ratMap_smulC, T.xFr_spec c0f hFc uF ouF _ _ _ (hok 3 (by norm_num))
        (hok 2 (by norm_num)) kn, hcC, hcC, hv0, hudef, mul_pow, hρ2, ← hu₀def]
      ring) (by
      rw [hfy0, frMap_mulConst j _ ofy1, hratm, ratMap_mulC jQ _ oYZ, hjω, hb₀e]
      unfold yZ
      simp only [Fr.val_mul (Fr.ok_mul ouF (Fr.ok_mul ouF ouF)) (Fr.ok_mul o3 odiv),
        Fr.val_mul ouF (Fr.ok_mul ouF ouF), Fr.val_mul ouF ouF, Fr.val_mul o3 odiv,
        Fr.val_div (Fr.ok_ofPoly [1]) ozF hzne, Fr.val_ofPoly]
      simp only [map_mul, map_div₀, hb₀s, ← hcF 3 (by norm_num), ← hφz, hφc, ← hρ, hudef,
        ← hu₀def]
      have h1 : ratMap jQ (algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly [1])) = 1 := by
        simp [CPoly.toPoly]
      rw [h1]
      have e4 : (u₀ * ρ) ^ 3 * ρ = u₀ ^ 3 * (s : RatFunc Cc) ^ 2 := by rw [← hρ2]; ring
      rw [show (u₀ * ρ) ^ 3 * (φ (cC 3) * (algebraMap Cc (RatFunc Cc) w / φ (T.val 0 z))) =
        u₀ ^ 3 * ρ ^ 3 * (φ (cC 3) * (algebraMap Cc (RatFunc Cc) w / φ (T.val 0 z))) by ring]
      rw [show ρ ^ 3 = (s : RatFunc Cc) * ρ by rw [pow_succ, hρ2]]
      push_cast
      ring)
  -- conjugation
  set τ := starRingEnd (QuadraticAlgebra ℚ δ 0) with hτ
  have hτe : τ.comp e = e := RingHom.ext_rat _ _
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
  refine ⟨⟨PD, hRD⟩, ?_⟩
  intro PD' hRD' n hn
  rw [rel_unique hRD' hRD] at hn
  have e1 := congrArg (fun P ↦ mapE j _ _ (mapE e _ _ P)) hn
  simp only [map_zsmul, map_zero] at e1
  rw [hmD] at e1
  have hrel0 := Differential.SuperData.zero_of_toShort φ (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _ hA' hB'
    (lst.map fun e ↦ e.1 • e.2.2).sum n (by convert e1)
  have hrel1 : n • (lst.map fun e ↦ e.1 • e.2.2).sum = 0 := by convert hrel0
  apply hntF n
  rw [hD, smul_smul, mul_comm, ← smul_smul]
  convert congrArg (fun P ↦ (mG Fc ks g A B kt l cs k : ℤ) • P) hrel1 using 1
  simp

end MTower

end Curves.MT
