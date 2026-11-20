import RischTragerBronstein.Mixed.KXCertBridgeK
import RischTragerBronstein.Mixed.KXConj

/-!
# The bridge check on the twist (any number of class generators, one square class)

`D = ∑ m_q P_q` only involves the poles of one class `T` (`m_q = 0` elsewhere), whose ordinates are
rational multiples of `r = ∏_T rᵢ` (`r² = s = ∏_T gᵢ`). When `κ = s c²` (the point `P₊` in the same
square class), scaling the model by `u = u₀ r` makes every coordinate rational:
`x ↦ s u₀² (…)`, `y_q ↦ s² c_q u₀³ (…)`, `y₀ ↦ s² c u₀³ c₃ / z`, `A ↦ s² u₀⁴(…)`, `B ↦ s³ u₀⁶(…)`.
So the certificate is computed over `ℚ` (`kxChkT`), for any number of generators, and gives the
group hypothesis (`grp_of_chkT`).
-/

open Polynomial Differential IntermediateField WeierstrassCurve WeierstrassCurve.Affine

namespace Differential.SuperData

open scoped Classical

/-- `hgrp_of_indep` for `toShort` (instances as in `KXHeight`). -/
theorem hgrp_of_toShort_indep {C : Type*} [Field C] [CharZero C] {k : Type*} [Field k] [CharZero k]
    (φ : C ≃+* RatFunc k) (c3 c2 c1 c0 : C) (u : RatFunc k) (hu : u ≠ 0) (A B : k[X])
    (hA : algebraMap k[X] (RatFunc k) A = u ^ 4 * (φ (c1 * c3) - φ c2 ^ 2 / 3))
    (hB : algebraMap k[X] (RatFunc k) B =
      u ^ 6 * (φ (c0 * c3 ^ 2) - φ c2 * φ (c1 * c3) / 3 + 2 * φ c2 ^ 3 / 27))
    (D Z : (WG c3 c2 c1 c0).Point)
    (hind : ∀ m n : ℤ, m • toShort φ c3 c2 c1 c0 u hu A B hA hB D =
      n • toShort φ c3 c2 c1 c0 u hu A B hA hB Z → m = 0 ∧ n = 0) :
    ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • D + (2 * μ) • Z ≠ 0 :=
  hgrp_of_indep _ (toShort_injective φ c3 c2 c1 c0 u hu A B hA hB) D Z hind

end Differential.SuperData


namespace Curves.MT

open CPoly Sup Curves.LT FFHeight

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

section ChkT

variable (Fc ks) [Fact (Irreducible (toPoly (fKc Fc)))]
variable (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
  (z : LC 0) (c : ℚ) (uF : Fr ℚ) (Ac Bc : CPoly ℚ) (kk kc : ℕ)

/-- The class `T`. -/
def clsT : List Bool := (kxCls Fc ks 0 g A B kt l cs).getD kc []

/-- Its value `s = ∏_T gᵢ`. -/
def sT : ℚ := prodSub (kxGens Fc ks 0 g A B kt l cs) (clsT Fc ks g A B kt l cs kc)

/-- Is `c_q` in the class? -/
def inCls (q : ℕ) : Bool := (kxRep Fc ks 0 g A B kt l cs q).1 == clsT Fc ks g A B kt l cs kc

/-- The point of the pole `c_q` on the twist. -/
def ptQT (q : ℕ) : PtC ℚ :=
  some (Fr.smulC (sT Fc ks g A B kt l cs kc)
      (MTower.xFr (yL c0f) uF (aC Fc ks A 3) (aC Fc ks A 2) (kqC Fc ks 0 cs q)),
    Fr.mul (MTower.yBaseFr (yL c0f) uF (aC Fc ks A 3) (kxD Fc ks 0 g cs q) (kxR Fc ks 0 A kt l cs q)
      (kqC Fc ks 0 cs q) B)
      (Fr.ofPoly [sT Fc ks g A B kt l cs kc * sT Fc ks g A B kt l cs kc *
        (kxRep Fc ks 0 g A B kt l cs q).2]))

/-- `D′` on the twist (poles of the class only). -/
def ptDT : PtC ℚ :=
  sumC Ac (((List.finRange cs.length).filter fun q : Fin cs.length ↦
    inCls Fc ks g A B kt l cs kc (q : ℕ)).map fun q : Fin cs.length ↦
    (mKc Fc ks g A B kt l cs kc (q : ℕ) / (mG Fc ks g A B kt l cs kc : ℤ),
      ptQT Fc ks c0f g A B kt l cs uF kc (q : ℕ)))

/-- `P₊` on the twist. -/
def ptZT : PtC ℚ :=
  some (Fr.smulC (sT Fc ks g A B kt l cs kc)
      (MTower.xFr (yL c0f) uF (aC Fc ks A 3) (aC Fc ks A 2) []),
    Fr.mul (yZ Fc ks c0f A z uF)
      (Fr.ofPoly [sT Fc ks g A B kt l cs kc * sT Fc ks g A B kt l cs kc * c]))

/-- **The check on the twist** without the independence certificate. -/
def kxChkT0 : Bool :=
  (List.range 4).all (fun i ↦ codeOKb (aC Fc ks A i)) && B.all codeOKb &&
  (List.range cs.length).all (fun q ↦ codeOKb (kqC Fc ks 0 cs q) &&
    codeOKb (kxD Fc ks 0 g cs q) && codeOKb (kxR Fc ks 0 A kt l cs q) &&
    !Fr.isZ (MTower.hornerFr (yL c0f) (codeFr (yL c0f) (kqC Fc ks 0 cs q)) B)) &&
  codeOKb z && !CPoly.isZero uF.2 && !Fr.isZ uF &&
  Fr.eqb (Fr.ofPoly Ac) (Fr.smulC (sT Fc ks g A B kt l cs kc ^ 2) (AFr Fc ks c0f A uF)) &&
  Fr.eqb (Fr.ofPoly Bc) (Fr.smulC (sT Fc ks g A B kt l cs kc ^ 3) (BFr Fc ks c0f A uF)) &&
  !CPoly.isZero (discC Ac Bc) && c != 0 && sT Fc ks g A B kt l cs kc != 0 &&
  Fr.eqb (Fr.mul (Fr.mul (codeFr (yL c0f) z) (codeFr (yL c0f) z)) (cF Fc ks c0f A 0))
    (Fr.ofPoly [sT Fc ks g A B kt l cs kc * c * c]) &&
  mG Fc ks g A B kt l cs kc != 0

/-- **The check on the twist** (function-field height certificate). -/
def kxChkT : Bool :=
  kxChkT0 Fc ks c0f g A B kt l cs z c uF Ac Bc kc &&
  certQ Ac (max (cdeg Ac) (cdeg Bc)) kk (ptDT Fc ks c0f g A B kt l cs uF Ac kc)
    (ptZT Fc ks c0f g A B kt l cs z c uF kc)

end ChkT

lemma sum_map_filter_of_zero {α M : Type*} [AddCommMonoid M] (p : α → Bool) (f : α → M) :
    ∀ l : List α, (∀ x ∈ l, p x = false → f x = 0) → (l.map f).sum = ((l.filter p).map f).sum
  | [], _ => rfl
  | x :: l, h => by
    have ih := sum_map_filter_of_zero p f l fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    by_cases hx : p x = true
    · simp [List.filter_cons, hx, ih]
    · have h0 := h x List.mem_cons_self (by simpa using hx)
      simp [List.filter_cons, hx, h0, ih]

namespace MTower

variable [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
variable (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
  (z : LC 0) (c : ℚ) (uF : Fr ℚ) (Ac Bc : CPoly ℚ) (kk : ℕ)

lemma ratMap_smulC (j : ℚ →+* Cc) (a : ℚ) (f : Fr ℚ) :
    ratMap j (Fr.val (Fr.smulC a f)) = (a : RatFunc Cc) * ratMap j (Fr.val f) := by
  rw [Fr.val_smulC, map_mul]
  congr 1
  rw [eq_ratCast, map_ratCast]

lemma ratMap_mulC (j : ℚ →+* Cc) (f : Fr ℚ) (hf : Fr.ok f) (a : ℚ) :
    ratMap j (Fr.val (Fr.mul f (Fr.ofPoly [a]))) = ratMap j (Fr.val f) * (a : RatFunc Cc) := by
  rw [frMap_mulConst j f hf a, eq_ratCast, map_ratCast]

set_option maxHeartbeats 8000000 in
open Classical in
/-- **The group condition from the check on the twist**, for every realization, every choice of
the roots of the generators and of `√A(0)`. -/
theorem grp_of_chkT0 (hFc : Fc = [c0f, [1]]) (h0 : T.Tr 0)
    (k : Fin (kxCls Fc ks 0 g A B kt l cs).length)
    (hchk : kxChkT0 Fc ks c0f g A B kt l cs z c uF Ac Bc k = true)
    (hind : ∀ PD PZ : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point,
      Rel _ _ (ptDT Fc ks c0f g A B kt l cs uF Ac k) PD →
      Rel _ _ (ptZT Fc ks c0f g A B kt l cs z c uF k) PZ →
      ∀ m n : ℤ, m • PD = n • PZ → m = 0 ∧ n = 0)
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
      ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
          (kxCl 0 g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0 := by
  intro cC xC βC hns hns0
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
  have hgr := Differential.SuperData.hgrp_of_toShort_indep φ (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _ hA
    hB (lst.map fun e ↦ e.1 • e.2.2).sum (Point.some _ _ hns0s') (fun m n h ↦ by
      refine hind PD PZ hRD hRZ m n (mapE_injective jQ _ _ ?_)
      rw [map_zsmul, map_zsmul, hmD, hmZ]
      convert h)
  have hgr' : ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • (lst.map fun e ↦ e.1 • e.2.2).sum +
      (2 * μ) • Point.some _ _ hns0s' ≠ 0 := by
    convert hgr
  have hfin := grp_of_div _ _ _ (Nat.pos_of_ne_zero hmG)
    (grp_signs _ _ _ _ (Or.inl rfl) (hsign hns0s') hgr')
  intro N hN μ
  convert hfin N hN μ using 3

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The group condition from the check on the twist** (function-field certificate). -/
theorem grp_of_chkT (hFc : Fc = [c0f, [1]]) (h0 : T.Tr 0)
    (k : Fin (kxCls Fc ks 0 g A B kt l cs).length)
    (hchk : kxChkT Fc ks c0f g A B kt l cs z c uF Ac Bc kk k = true)
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
      ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
          (kxCl 0 g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0 := by
  simp only [kxChkT, Bool.and_eq_true] at hchk
  obtain ⟨hchk0, hcert⟩ := hchk
  have hΔq : 4 * (CPoly.toPoly Ac) ^ 3 + 27 * (CPoly.toPoly Bc) ^ 2 ≠ 0 := by
    simp only [kxChkT0, Bool.and_eq_true, Bool.not_eq_true'] at hchk0
    have hdisc := hchk0.1.1.1.1.2
    intro h0
    rw [show 4 * (CPoly.toPoly Ac) ^ 3 + 27 * (CPoly.toPoly Bc) ^ 2 = CPoly.toPoly (discC Ac Bc) by
      simp only [discC, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_mul, map_ofNat,
        Polynomial.C_ofNat]; ring, ← CPoly.isZero_iff] at h0
    rw [h0] at hdisc; exact absurd hdisc (by decide)
  exact T.grp_of_chkT0 c0f g A B kt l cs z c uF Ac Bc hFc h0 k hchk0
    (fun PD PZ hRD hRZ m n h ↦ indep_of_certQ Ac Bc (CPoly.toPoly Ac) (CPoly.toPoly Bc) rfl hΔq kk
      _ _ PD PZ hRD hRZ (by rw [← cdeg_spec, ← cdeg_spec]; exact hcert) m n h) rtsF hrl hrs b₀ hb₀

end MTower

end Curves.MT
