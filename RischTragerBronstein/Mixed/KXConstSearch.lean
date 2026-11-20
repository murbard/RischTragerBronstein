import RischTragerBronstein.Mixed.KXConstCK

/-!
# The constant-curve searches answer (completeness of the searches)

`kxMWSearchCK_of` / `kxMWSearchTK_of`: for a curve with rational coefficients `r`, nonzero
discriminant, and the class divisor of infinite order (resp. independent of `P₊ − ∞`), the searches
`kxMWSearchCK` / `kxMWSearchTK` succeed for every large `kmax` — at the integral scaling
`lcm(den a₁, den b₁)` of `mwScales`.
-/

open Polynomial Differential IntermediateField

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- The integral scaling: the heads at scale `mm = lcm(den a₁, den b₁)` are integers. -/
lemma scale_int (a1 b1 X Y U s : ℚ) (hX : X = s ^ 2 * (U * U * (U * U)) * a1)
    (hY : Y = s ^ 3 * (U * U * (U * U * (U * U))) * b1) (a1' b1' : ℚ)
    (ha : a1' = s ^ 2 * (U * U * (U * U)) * a1) (hb : b1' = s ^ 3 * (U * U * (U * U * (U * U))) * b1)
    (mm : ℕ) (hmm : mm = Nat.lcm a1'.den b1'.den)
    (X' Y' : ℚ) (hX' : X' = s ^ 2 * ((U * mm) * (U * mm) * ((U * mm) * (U * mm))) * a1)
    (hY' : Y' = s ^ 3 * ((U * mm) * (U * mm) * ((U * mm) * (U * mm) * ((U * mm) * (U * mm)))) * b1) :
    (X'.num : ℚ) = X' ∧ (Y'.num : ℚ) = Y' := by
  have eX : X' = (mm : ℚ) ^ 4 * a1' := by rw [hX', ha]; ring
  have eY : Y' = (mm : ℚ) ^ 6 * b1' := by rw [hY', hb]; ring
  rw [eX, eY]
  exact ⟨pow_mul_int a1' mm (hmm ▸ Nat.dvd_lcm_left _ _) 4 (by norm_num),
    pow_mul_int b1' mm (hmm ▸ Nat.dvd_lcm_right _ _) 6 (by norm_num)⟩

lemma lcm_den_ne_zero (a b : ℚ) : ((Nat.lcm a.den b.den : ℕ) : ℚ) ≠ 0 := by
  exact_mod_cast Nat.lcm_ne_zero a.den_nz b.den_nz

/-- The discriminant of the scaled model. -/
lemma disc_scaled (r : ℕ → ℚ) (s u : ℚ) (hs : s ≠ 0) (hu : u ≠ 0)
    (hdisc : 4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
      27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2 ≠ 0) (a b : ℤ)
    (ha : (a : ℚ) = s ^ 2 * (u * u * (u * u) * (r 1 * r 3 - 1 / 3 * (r 2 * r 2))))
    (hb : (b : ℚ) = s ^ 3 * (u * u * (u * u * (u * u)) *
      (r 0 * (r 3 * r 3) - 1 / 3 * (r 2 * (r 1 * r 3)) + 2 / 27 * (r 2 * (r 2 * r 2))))) :
    4 * a ^ 3 + 27 * b ^ 2 ≠ 0 := by
  intro h
  have h' : (4 * (a : ℚ) ^ 3 + 27 * (b : ℚ) ^ 2) = 0 := by exact_mod_cast h
  have e : 4 * (a : ℚ) ^ 3 + 27 * (b : ℚ) ^ 2 = s ^ 6 * u ^ 12 * (4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
      27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2) := by
    rw [ha, hb]; ring
  rw [e] at h'
  exact hdisc ((mul_eq_zero.mp h').resolve_left (mul_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ hu)))

namespace MTower

variable [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The constant-curve search (different classes) succeeds** for large `kmax`. -/
theorem kxMWSearchCK_of (c0f : CPoly ℚ) (hFc : Fc = [c0f, [1]]) (h0 : T.Tr 0) (g : LC 0)
    (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (z : LC 0) (hz : kxZ Fc ks lv 0 A = some z)
    (k : Fin (kxCls Fc ks 0 g A B kt l cs).length)
    (hδ : ¬ IsSquare (sT Fc ks g A B kt l cs k * kxKap Fc ks 0 A z))
    (hA4 : ∀ i < 4, codeOKb (aC Fc ks A i) = true) (hBok : ∀ b ∈ B, codeOKb b = true)
    (hcs : ∀ q < cs.length, codeOKb (kqC Fc ks 0 cs q) = true)
    (hD : ∀ q < cs.length, codeOKb (kxD Fc ks 0 g cs q) = true)
    (r : ℕ → ℚ) (hr : ∀ i < 4, T.val 0 (aC Fc ks A i) = (r i : T.F 0))
    (hBq : ∀ q < cs.length,
      (GPoly.toPoly (T.MP 0 h0) B).eval (T.val 0 (kqC Fc ks 0 cs q)) ≠ 0)
    (hκ : kxKap Fc ks 0 A z ≠ 0) (hs : sT Fc ks g A B kt l cs k ≠ 0)
    (hzκ : T.val 0 z ^ 2 * T.val 0 (aC Fc ks A 0) = (kxKap Fc ks 0 A z : T.F 0))
    (hmG : mG Fc ks g A B kt l cs k ≠ 0)
    (hdisc : 4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
      27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2 ≠ 0)
    (rtsF : List (T.F 0)) (hrl : rtsF.length = (kxGens Fc ks 0 g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks 0 g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks 0 g A B kt l cs)[i] : T.F 0))
    (b₀ : T.F 0) (hb₀ : b₀ ^ 2 = (T.MP 0 h0).sem (A.getD 0 (MO Fc ks 0).zero))
    (hns : ∀ q : Fin cs.length, (Differential.SuperData.WG ((GPoly.toPoly (T.MP 0 h0) A).coeff 3)
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 2) ((GPoly.toPoly (T.MP 0 h0) A).coeff 1)
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 3 * (T.MP 0 h0).sem (kqC Fc ks 0 cs q))
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 3 * (((kxRep Fc ks 0 g A B kt l cs q).2 : T.F 0) *
          SqrtIndep.prodRoots rtsF (kxRep Fc ks 0 g A B kt l cs q).1 *
          ((T.MP 0 h0).sem (kxD Fc ks 0 g cs q) * (T.MP 0 h0).sem (kxR Fc ks 0 A kt l cs q) /
            (GPoly.toPoly (T.MP 0 h0) B).eval ((T.MP 0 h0).sem (kqC Fc ks 0 cs q))))))
    (hns0 : (Differential.SuperData.WG ((GPoly.toPoly (T.MP 0 h0) A).coeff 3)
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 2) ((GPoly.toPoly (T.MP 0 h0) A).coeff 1)
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 3 * 0) ((GPoly.toPoly (T.MP 0 h0) A).coeff 3 * b₀))
    (hntF : ∀ n : ℤ, n • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
        (kxCl 0 g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) = 0 →
        n = 0) :
    ∃ K0, ∀ kmax, K0 ≤ kmax → kxMWSearchCK Fc ks lv c0f g A B kt l cs kmax = true := by
  set κ := kxKap Fc ks 0 A z with hκdef
  set s := sT Fc ks g A B kt l cs k with hsdef
  set z' := normC Fc 0 z with hz'
  have hyok : Fr.ok (yL c0f) := by simp [Fr.ok, CPoly.toPoly]
  have hcF : ∀ i < 4, IsConstFr (cF Fc ks c0f A i) (r i) := fun i hi ↦
    ⟨codeFr_ok _ hyok _ (codeOK_of (hA4 i hi)), T.frval_of_rat c0f hFc _ (hA4 i hi) (r i) (hr i hi)⟩
  obtain ⟨U, hU0, hU⟩ := mwU_const Fc ks c0f A r hcF
  set a1 := (polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0f A (mwU Fc ks c0f A)))).headD 0 with ha1
  set b1 := (polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0f A (mwU Fc ks c0f A)))).headD 0 with hb1
  set mN := Nat.lcm a1.den b1.den with hmN
  set mm : ℚ := (mN : ℚ) with hmm
  have hmm0 : mm ≠ 0 := lcm_den_ne_zero a1 b1
  set uF := Fr.mul (mwU Fc ks c0f A) (Fr.ofPoly [mm]) with huF
  have hu : IsConstFr uF (U * mm) := constFr_mul hU (constFr_ofPoly mm)
  set aX := (polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0f A uF))).headD 0 with hX
  set bY := (polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0f A uF))).headD 0 with hY
  have hXv := Ac_head Fc ks c0f A r hcF s uF _ hu
  have hYv := Bc_head Fc ks c0f A r hcF s uF _ hu
  have ha1v := Ac_head Fc ks c0f A r hcF s _ _ hU
  have hb1v := Bc_head Fc ks c0f A r hcF s _ _ hU
  obtain ⟨hXi, hYi⟩ := scale_int (r 1 * r 3 - 1 / 3 * (r 2 * r 2))
    (r 0 * (r 3 * r 3) - 1 / 3 * (r 2 * (r 1 * r 3)) + 2 / 27 * (r 2 * (r 2 * r 2))) a1 b1 U s
    (ha1v.trans (by ring)) (hb1v.trans (by ring)) a1 b1 (ha1v.trans (by ring)) (hb1v.trans (by ring)) mN rfl
    aX bY (hXv.trans (by ring)) (hYv.trans (by ring))
  -- the structural part
  have hz'ok : codeOKb z' = true := codeOKb_normC Fc z
  have hz'v : T.val 0 z' = T.val 0 z := by
    rw [← T.sem_MP_F 0 h0, ← T.sem_MP_F 0 h0, hz', T.sem_normC 0 h0]
  have hchk0 := T.kxChkC0_true c0f hFc h0 g A B kt l cs z' κ k mm hA4 hBok hcs hD hz'ok r hr hBq
    hκ hs (by rw [hz'v]; exact hzκ) hmG hmm0 hdisc
  have hΔ : 4 * aX.num ^ 3 + 27 * bY.num ^ 2 ≠ 0 :=
    disc_scaled r s (U * mm) hs (mul_ne_zero hU0 hmm0) hdisc _ _ (hXi.trans hXv) (hYi.trans hYv)
  haveI : Fact (¬ IsSquare (sT Fc ks g A B kt l cs k * κ)) := ⟨hδ⟩
  obtain ⟨kk, hkk⟩ := T.kxChkCK_exists c0f g A B kt l cs z' κ uF [aX] [bY] aX.num bY.num hFc h0 k
    hchk0 (by rw [hXi]) (by rw [hYi]) hΔ rtsF hrl hrs b₀ hb₀ hns hns0 hntF
  refine ⟨kk + 1, fun kmax hkm ↦ ?_⟩
  unfold kxMWSearchCK
  rw [hz]
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne]
  refine ⟨k, k.2, ?_, mm, ?_, kk, by omega, ?_⟩
  · intro h
    exact hδ ⟨_, h.symm⟩
  · unfold mwScales
    simp only [List.mem_cons]
    right; right; right; right; left; rfl
  · convert hkk using 2 <;> rw [List.headD_cons]

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The constant-curve search (same class) succeeds** for large `kmax`. -/
theorem kxMWSearchTK_of (c0f : CPoly ℚ) (hFc : Fc = [c0f, [1]]) (h0 : T.Tr 0) (g : LC 0)
    (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (z : LC 0) (hz : kxZ Fc ks lv 0 A = some z)
    (k : Fin (kxCls Fc ks 0 g A B kt l cs).length)
    (hδ : IsSquare (kxKap Fc ks 0 A z / sT Fc ks g A B kt l cs k))
    (hA4 : ∀ i < 4, codeOKb (aC Fc ks A i) = true) (hBok : ∀ b ∈ B, codeOKb b = true)
    (hcs : ∀ q < cs.length, codeOKb (kqC Fc ks 0 cs q) = true)
    (hD : ∀ q < cs.length, codeOKb (kxD Fc ks 0 g cs q) = true)
    (r : ℕ → ℚ) (hr : ∀ i < 4, T.val 0 (aC Fc ks A i) = (r i : T.F 0))
    (hBq : ∀ q < cs.length,
      (GPoly.toPoly (T.MP 0 h0) B).eval (T.val 0 (kqC Fc ks 0 cs q)) ≠ 0)
    (hκ : kxKap Fc ks 0 A z ≠ 0) (hs : sT Fc ks g A B kt l cs k ≠ 0)
    (hzκ : T.val 0 z ^ 2 * T.val 0 (aC Fc ks A 0) = (kxKap Fc ks 0 A z : T.F 0))
    (hmG : mG Fc ks g A B kt l cs k ≠ 0)
    (hdisc : 4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
      27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2 ≠ 0)
    (rtsF : List (T.F 0)) (hrl : rtsF.length = (kxGens Fc ks 0 g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks 0 g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks 0 g A B kt l cs)[i] : T.F 0))
    (b₀ : T.F 0) (hb₀ : b₀ ^ 2 = (T.MP 0 h0).sem (A.getD 0 (MO Fc ks 0).zero))
    (hns : ∀ q : Fin cs.length, (Differential.SuperData.WG ((GPoly.toPoly (T.MP 0 h0) A).coeff 3)
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 2) ((GPoly.toPoly (T.MP 0 h0) A).coeff 1)
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 3 * (T.MP 0 h0).sem (kqC Fc ks 0 cs q))
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 3 * (((kxRep Fc ks 0 g A B kt l cs q).2 : T.F 0) *
          SqrtIndep.prodRoots rtsF (kxRep Fc ks 0 g A B kt l cs q).1 *
          ((T.MP 0 h0).sem (kxD Fc ks 0 g cs q) * (T.MP 0 h0).sem (kxR Fc ks 0 A kt l cs q) /
            (GPoly.toPoly (T.MP 0 h0) B).eval ((T.MP 0 h0).sem (kqC Fc ks 0 cs q))))))
    (hns0 : (Differential.SuperData.WG ((GPoly.toPoly (T.MP 0 h0) A).coeff 3)
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 2) ((GPoly.toPoly (T.MP 0 h0) A).coeff 1)
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP 0 h0) A).coeff 3 * 0) ((GPoly.toPoly (T.MP 0 h0) A).coeff 3 * b₀))
    (hgrp : ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
          (kxCl 0 g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0)
    (hP0 : ∀ n : ℤ, n • WeierstrassCurve.Affine.Point.some _ _ hns0 = 0 → n = 0) :
    ∃ K0, ∀ kmax, K0 ≤ kmax → kxMWSearchTK Fc ks lv c0f g A B kt l cs kmax = true := by
  set κ := kxKap Fc ks 0 A z with hκdef
  set s := sT Fc ks g A B kt l cs k with hsdef
  set z' := normC Fc 0 z with hz'
  have hyok : Fr.ok (yL c0f) := by simp [Fr.ok, CPoly.toPoly]
  have hcF : ∀ i < 4, IsConstFr (cF Fc ks c0f A i) (r i) := fun i hi ↦
    ⟨codeFr_ok _ hyok _ (codeOK_of (hA4 i hi)), T.frval_of_rat c0f hFc _ (hA4 i hi) (r i) (hr i hi)⟩
  obtain ⟨U, hU0, hU⟩ := mwU_const Fc ks c0f A r hcF
  set a1 := (polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0f A (mwU Fc ks c0f A)))).headD 0 with ha1
  set b1 := (polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0f A (mwU Fc ks c0f A)))).headD 0 with hb1
  set mN := Nat.lcm a1.den b1.den with hmN
  set mm : ℚ := (mN : ℚ) with hmm
  have hmm0 : mm ≠ 0 := lcm_den_ne_zero a1 b1
  set uF := Fr.mul (mwU Fc ks c0f A) (Fr.ofPoly [mm]) with huF
  have hu : IsConstFr uF (U * mm) := constFr_mul hU (constFr_ofPoly mm)
  set aX := (polyOf (Fr.smulC (s ^ 2) (AFr Fc ks c0f A uF))).headD 0 with hX
  set bY := (polyOf (Fr.smulC (s ^ 3) (BFr Fc ks c0f A uF))).headD 0 with hY
  have hXv := Ac_head Fc ks c0f A r hcF s uF _ hu
  have hYv := Bc_head Fc ks c0f A r hcF s uF _ hu
  have ha1v := Ac_head Fc ks c0f A r hcF s _ _ hU
  have hb1v := Bc_head Fc ks c0f A r hcF s _ _ hU
  obtain ⟨hXi, hYi⟩ := scale_int (r 1 * r 3 - 1 / 3 * (r 2 * r 2))
    (r 0 * (r 3 * r 3) - 1 / 3 * (r 2 * (r 1 * r 3)) + 2 / 27 * (r 2 * (r 2 * r 2))) a1 b1 U s
    (ha1v.trans (by ring)) (hb1v.trans (by ring)) a1 b1 (ha1v.trans (by ring)) (hb1v.trans (by ring)) mN rfl
    aX bY (hXv.trans (by ring)) (hYv.trans (by ring))
  -- the structural part
  have hz'ok : codeOKb z' = true := codeOKb_normC Fc z
  have hz'v : T.val 0 z' = T.val 0 z := by
    rw [← T.sem_MP_F 0 h0, ← T.sem_MP_F 0 h0, hz', T.sem_normC 0 h0]
  set c := Rat.sqrt (κ / s) with hcdef
  have hcc : c * c = κ / s := (Rat.exists_mul_self _).mp (by
    obtain ⟨q, hq⟩ := hδ; exact ⟨q, hq.symm⟩)
  have hc0 : c ≠ 0 := fun h ↦ by
    rw [h, zero_mul, eq_comm, div_eq_zero_iff] at hcc
    exact hcc.elim hκ hs
  have hscc : s * c * c = κ := by rw [mul_assoc, hcc]; field_simp
  have hchk0 := T.kxChkT0_true c0f hFc h0 g A B kt l cs z' c k mm hA4 hBok hcs hD hz'ok r hr hBq
    hc0 hs (by rw [hz'v, hzκ, hscc]) hmG hmm0 hdisc
  have hΔ : 4 * aX.num ^ 3 + 27 * bY.num ^ 2 ≠ 0 :=
    disc_scaled r s (U * mm) hs (mul_ne_zero hU0 hmm0) hdisc _ _ (hXi.trans hXv) (hYi.trans hYv)
  obtain ⟨kk, hkk⟩ := T.kxChkTK_exists c0f g A B kt l cs z' c uF [aX] [bY] aX.num bY.num hFc h0 k
    hchk0 (by rw [hXi]) (by rw [hYi]) hΔ rtsF hrl hrs b₀ hb₀ hns hns0 hgrp hP0
  refine ⟨kk + 1, fun kmax hkm ↦ ?_⟩
  unfold kxMWSearchTK
  rw [hz]
  simp only [List.any_eq_true, List.mem_range]
  refine ⟨k, k.2, mm, ?_, kk, by omega, ?_⟩
  · unfold mwScales
    simp only [List.mem_cons]
    right; right; right; right; left; rfl
  · convert hkk using 2 <;> rw [List.headD_cons]

end MTower

end Curves.MT
