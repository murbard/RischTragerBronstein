import RischTragerBronstein.Mixed.KXCertBridgeT
import RischTragerBronstein.Mixed.MTField

/-!
# The bridge checks at levels `m + 1` (any base curve)

At a level `m + 1 ≥ 1` the coefficient field of the exception's curve is `F(m+1) = Fₘ(tₘ)`
(`MTField.phiS`), and codes translate to executable fractions over the computable field `Kₘ`
(`trFr`). The twisted bridge (`KXCertBridgeT`) transfers verbatim: `kxChkT0S`, `grp_of_chkT0S`
(independence input), `kxChkTS` (function-field certificate over `Kₘ`), `grp_of_chkTS`. No
condition on the base curve is needed.
-/

open Polynomial Differential IntermediateField WeierstrassCurve WeierstrassCurve.Affine

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

section ChkS

variable (Fc ks) [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ)
variable (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
  (z : LC (m + 1)) (c : ℚ) (uF : Fr (KF Fc m)) (Ac Bc : CPoly (KF Fc m)) (kk kc : ℕ)

/-- The `i`-th coefficient code. -/
def aCS (i : ℕ) : LC (m + 1) := A.getD i (MO Fc ks (m + 1)).zero

/-- The zero code. -/
def zCS : LC (m + 1) := (([] : GPoly (LC m)), [(MO Fc ks m).one])

/-- `cᵢ` as fractions over `Kₘ`. -/
def cFS (i : ℕ) : Fr (KF Fc m) := MTower.trFr (Fc := Fc) m (aCS Fc ks m A i)

def AFrS : Fr (KF Fc m) :=
  Fr.mul (Fr.mul (Fr.mul uF uF) (Fr.mul uF uF))
    (Fr.sub (Fr.mul (cFS Fc ks m A 1) (cFS Fc ks m A 3))
      (Fr.smulC (1 / 3) (Fr.mul (cFS Fc ks m A 2) (cFS Fc ks m A 2))))

def BFrS : Fr (KF Fc m) :=
  Fr.mul (Fr.mul (Fr.mul uF uF) (Fr.mul (Fr.mul uF uF) (Fr.mul uF uF)))
    (Fr.add (Fr.sub (Fr.mul (cFS Fc ks m A 0) (Fr.mul (cFS Fc ks m A 3) (cFS Fc ks m A 3)))
      (Fr.smulC (1 / 3) (Fr.mul (cFS Fc ks m A 2) (Fr.mul (cFS Fc ks m A 1) (cFS Fc ks m A 3)))))
      (Fr.smulC (2 / 27) (Fr.mul (cFS Fc ks m A 2) (Fr.mul (cFS Fc ks m A 2) (cFS Fc ks m A 2)))))

def mKcS (q : ℕ) : ℤ :=
  if (kxRep Fc ks (m + 1) g A B kt l cs q).1 == (kxCls Fc ks (m + 1) g A B kt l cs).getD kc [] then
    (kxMNm Fc ks (m + 1) g A B kt l cs q : ℤ) else 0

def mGS : ℕ := ((List.range cs.length).map (mKcS Fc ks m g A B kt l cs kc)).foldr
  (fun a b ↦ Int.gcd a (b : ℤ)) 0

def clsTS : List Bool := (kxCls Fc ks (m + 1) g A B kt l cs).getD kc []

def sTS : ℚ := prodSub (kxGens Fc ks (m + 1) g A B kt l cs) (clsTS Fc ks m g A B kt l cs kc)

def inClsS (q : ℕ) : Bool :=
  (kxRep Fc ks (m + 1) g A B kt l cs q).1 == clsTS Fc ks m g A B kt l cs kc

def ptQTS (q : ℕ) : PtC (KF Fc m) :=
  some (Fr.smulC ((sTS Fc ks m g A B kt l cs kc : ℚ) : KF Fc m)
      (MTower.xFrS (Fc := Fc) m uF (aCS Fc ks m A 3) (aCS Fc ks m A 2) (kqC Fc ks (m + 1) cs q)),
    Fr.mul (MTower.yBaseFrS (Fc := Fc) m uF (aCS Fc ks m A 3) (kxD Fc ks (m + 1) g cs q)
      (kxR Fc ks (m + 1) A kt l cs q) (kqC Fc ks (m + 1) cs q) B)
      (Fr.ofPoly [(Rat.cast (sTS Fc ks m g A B kt l cs kc * sTS Fc ks m g A B kt l cs kc *
        (kxRep Fc ks (m + 1) g A B kt l cs q).2) : KF Fc m)]))

def ptDTS : PtC (KF Fc m) :=
  sumC Ac (((List.finRange cs.length).filter fun q : Fin cs.length ↦
    inClsS Fc ks m g A B kt l cs kc (q : ℕ)).map fun q : Fin cs.length ↦
    (mKcS Fc ks m g A B kt l cs kc (q : ℕ) / (mGS Fc ks m g A B kt l cs kc : ℤ),
      ptQTS Fc ks m g A B kt l cs uF kc (q : ℕ)))

def yZS : Fr (KF Fc m) :=
  Fr.mul (Fr.mul uF (Fr.mul uF uF)) (Fr.mul (cFS Fc ks m A 3)
    (Fr.div (Fr.ofPoly [1]) (MTower.trFr (Fc := Fc) m z)))

def ptZTS : PtC (KF Fc m) :=
  some (Fr.smulC ((sTS Fc ks m g A B kt l cs kc : ℚ) : KF Fc m)
      (MTower.xFrS (Fc := Fc) m uF (aCS Fc ks m A 3) (aCS Fc ks m A 2) (zCS Fc ks m)),
    Fr.mul (yZS Fc ks m A z uF)
      (Fr.ofPoly [(Rat.cast (sTS Fc ks m g A B kt l cs kc * sTS Fc ks m g A B kt l cs kc * c) :
        KF Fc m)]))

/-- The discriminant polynomial. -/
def discCS : CPoly (KF Fc m) := CPoly.add (CPoly.smul 4 (CPoly.mul Ac (CPoly.mul Ac Ac)))
  (CPoly.smul 27 (CPoly.mul Bc Bc))

/-- **The check on the twist at level `m + 1`** (without independence). -/
def kxChkT0S : Bool :=
  (List.range 4).all (fun i ↦ MTower.okS (Fc := Fc) m (aCS Fc ks m A i)) && B.all (MTower.okS (Fc := Fc) m) &&
  (List.range cs.length).all (fun q ↦ MTower.okS (Fc := Fc) m (kqC Fc ks (m + 1) cs q) &&
    MTower.okS (Fc := Fc) m (kxD Fc ks (m + 1) g cs q) && MTower.okS (Fc := Fc) m (kxR Fc ks (m + 1) A kt l cs q) &&
    !Fr.isZ (MTower.hornerFrS (Fc := Fc) m (MTower.trFr (Fc := Fc) m (kqC Fc ks (m + 1) cs q)) B)) &&
  MTower.okS (Fc := Fc) m z && MTower.okS (Fc := Fc) m (zCS Fc ks m) && !CPoly.isZero uF.2 && !Fr.isZ uF &&
  Fr.eqb (Fr.ofPoly Ac) (Fr.smulC (Rat.cast (sTS Fc ks m g A B kt l cs kc ^ 2) : KF Fc m)
    (AFrS Fc ks m A uF)) &&
  Fr.eqb (Fr.ofPoly Bc) (Fr.smulC (Rat.cast (sTS Fc ks m g A B kt l cs kc ^ 3) : KF Fc m)
    (BFrS Fc ks m A uF)) &&
  !CPoly.isZero (discCS Fc m Ac Bc) && c != 0 && sTS Fc ks m g A B kt l cs kc != 0 &&
  Fr.eqb (Fr.mul (Fr.mul (MTower.trFr (Fc := Fc) m z) (MTower.trFr (Fc := Fc) m z)) (cFS Fc ks m A 0))
    (Fr.ofPoly [(Rat.cast (sTS Fc ks m g A B kt l cs kc * c * c) : KF Fc m)]) &&
  mGS Fc ks m g A B kt l cs kc != 0

/-- **The check on the twist at level `m + 1`** (function-field certificate over `Kₘ`). -/
def kxChkTS : Bool :=
  kxChkT0S Fc ks m g A B kt l cs z c uF Ac Bc kc &&
  certQ Ac (max (cdeg Ac) (cdeg Bc)) kk (ptDTS Fc ks m g A B kt l cs uF Ac kc)
    (ptZTS Fc ks m g A B kt l cs z c uF kc)

end ChkS

namespace MTower

variable [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L) (m : ℕ)
variable (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
  (z : LC (m + 1)) (c : ℚ) (uF : Fr (KF Fc m)) (Ac Bc : CPoly (KF Fc m)) (kk : ℕ)

lemma ratMap_smulCS {k : Type*} [Field k] [CharZero k] (j : KF Fc m →+* k) (a : ℚ) (f : Fr (KF Fc m)) :
    ratMap j (Fr.val (Fr.smulC (Rat.cast a : KF Fc m) f)) = (a : RatFunc k) * ratMap j (Fr.val f) := by
  rw [Fr.val_smulC, map_mul, map_ratCast, map_ratCast]

lemma ratMap_mulCS {k : Type*} [Field k] [CharZero k] (j : KF Fc m →+* k) (f : Fr (KF Fc m))
    (hf : Fr.ok f) (a : ℚ) :
    ratMap j (Fr.val (Fr.mul f (Fr.ofPoly [(Rat.cast a : KF Fc m)]))) =
      ratMap j (Fr.val f) * (a : RatFunc k) := by
  rw [frMap_mulConst j f hf, map_ratCast, map_ratCast]

omit [CharZero L] in
lemma mK_eq_mKcS (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length) (q : Fin cs.length) :
    ((Differential.SuperData.mK (fun q ↦ kxMNm Fc ks (m + 1) g A B kt l cs q)
      (kxCl (m + 1) g A B kt l cs) k q : ℕ) : ℤ) =
      mKcS Fc ks m g A B kt l cs k q := by
  classical
  unfold Differential.SuperData.mK mKcS
  by_cases h : (kxRep Fc ks (m + 1) g A B kt l cs q).1 = (kxCls Fc ks (m + 1) g A B kt l cs)[(k : ℕ)]
  · have h' := (kxCl_eq_iff (m + 1) g A B kt l cs q k).mpr h
    simp [h', h, List.getD_eq_getElem _ _ k.2]
  · have h' : ¬ kxCl (m + 1) g A B kt l cs q = k :=
      fun h'' ↦ h ((kxCl_eq_iff (m + 1) g A B kt l cs q k).mp h'')
    simp [h', h, List.getD_eq_getElem _ _ k.2]

/-- A square root of a non-zero rational in `F n` is a constant. -/
lemma const_of_sqN (n : ℕ) (x : T.F n) (q : ℚ) (hq : q ≠ 0) (h : x ^ 2 = (q : T.F n)) :
    ∃ c : Cc, algebraMap Cc (T.F n) c = x := by
  have hL : (x : L) ^ 2 = (q : L) := by
    have := congrArg (fun y : T.F n ↦ (y : L)) h
    simpa using this
  have hx0 : (x : L) ≠ 0 := fun h0 ↦ by
    rw [h0, zero_pow two_ne_zero] at hL
    exact hq (by exact_mod_cast hL.symm)
  have hd := congrArg (fun w ↦ w′) hL
  simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hd
  rw [Tower.NestP.deriv_ratCastK (K := L) q] at hd
  have h2 : ((2 : ℕ) : L) * (x : L) ^ (2 - 1) * (x : L)′ = 0 := by rw [← hd]; ring
  norm_num at h2
  rcases h2 with h2 | h2
  · exact absurd (by simp [h2]) hx0
  · obtain ⟨c, hc⟩ := T.hconst _ h2
    exact ⟨c, Subtype.ext (by rw [← hc]; rfl)⟩

lemma consts_of_listN (n : ℕ) : ∀ l : List (T.F n),
    (∀ x ∈ l, ∃ c : Cc, algebraMap Cc (T.F n) c = x) →
    ∃ ls : List Cc, ls.map (algebraMap Cc (T.F n)) = l
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨c, hc⟩ := h x List.mem_cons_self
    obtain ⟨ls, hls⟩ := consts_of_listN n l fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    exact ⟨c :: ls, by simp [hc, hls]⟩

set_option maxHeartbeats 8000000 in
open Classical in
theorem grp_of_chkT0S (h0 : T.Tr (m + 1))
    (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length)
    (hchk : kxChkT0S Fc ks m g A B kt l cs z c uF Ac Bc k = true)
    (hind : ∀ PD PZ : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point,
      Rel _ _ (ptDTS Fc ks m g A B kt l cs uF Ac k) PD →
      Rel _ _ (ptZTS Fc ks m g A B kt l cs z c uF k) PZ →
      ∀ m n : ℤ, m • PD = n • PZ → m = 0 ∧ n = 0)
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
      ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks (m + 1) g A B kt l cs q)
          (kxCl (m + 1) g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0 := by
  intro cC xC βC hns hns0
  simp only [kxChkT0S, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    bne_iff_ne, ne_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hA4, hBok⟩, hcs⟩, hzok⟩, hzC⟩, hu2⟩, huZ⟩, hAe⟩, hBe⟩, hdisc⟩, hc0⟩, hs0⟩, hze⟩,
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
  -- the sum `D` over the class
  set fl := (List.finRange cs.length).filter fun q : Fin cs.length ↦
    inClsS Fc ks m g A B kt l cs k (q : ℕ) with hfl
  set lst : List (ℤ × PtC (KF Fc m) × (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Point) :=
    fl.map (fun q : Fin cs.length ↦ (mKcS Fc ks m g A B kt l cs k (q : ℕ) /
        (mGS Fc ks m g A B kt l cs k : ℤ), ptQTS Fc ks m g A B kt l cs uF k (q : ℕ),
          Point.some _ _ (hns q))) with hlst
  obtain ⟨PD, hRD, hmD⟩ := Differential.SuperData.cert_sum φ jQ (cC 3) (cC 2) (cC 1) (cC 0) u hu
    _ _ hA hB Ac rfl lst (fun e' he' ↦ by
      rw [hlst, List.mem_map] at he'
      obtain ⟨q, hqm, rfl⟩ := he'
      have hqm' := hqm
      rw [hfl, List.mem_filter] at hqm'
      exact hq q hqm'.2)
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
  -- the point `P₊`
  have kz := hzok
  have ozF := okS_spec (Fc := Fc) kz
  have hzeq := (Fr.eqb_iff (Fr.ok_mul (Fr.ok_mul ozF ozF) o0) (Fr.ok_ofPoly _)).mp hze
  rw [Fr.val_mul (Fr.ok_mul ozF ozF) o0, Fr.val_mul ozF ozF, Fr.val_ofPoly] at hzeq
  have hκr : algebraMap (KF Fc m)[X] (RatFunc (KF Fc m)) (CPoly.toPoly [(Rat.cast (s * c * c) : KF Fc m)]) =
      ((s * c * c : ℚ) : RatFunc (KF Fc m)) := by
    simp [CPoly.toPoly, RatFunc.algebraMap_C]
  rw [hκr] at hzeq
  have hφz : φ (T.val (m + 1) z) = ratMap jQ (Fr.val (trFr (Fc := Fc) m z)) := hval z
  have hw : (b₀ * T.val (m + 1) z) ^ 2 = ((s * c * c : ℚ) : T.F (m + 1)) := by
    apply φ.injective
    have hb : φ b₀ ^ 2 = ratMap jQ (Fr.val (cFS Fc ks m A 0)) := by
      rw [← map_pow, hb₀, hsem, ← hcF 0 (by norm_num), hcC]; rfl
    have e2 := congrArg (ratMap jQ) hzeq
    simp only [map_mul, map_ratCast] at e2
    rw [mul_pow, map_mul, map_pow, map_pow, hb, hφz, map_ratCast]
    linear_combination e2
  have hκ0 : s * c * c ≠ 0 := mul_ne_zero (mul_ne_zero hs0 hc0) hc0
  have hvz : T.val (m + 1) z ≠ 0 := fun h ↦ by
    rw [h, mul_zero, zero_pow two_ne_zero] at hw
    exact hκ0 (by exact_mod_cast hw.symm)
  have hzne : Fr.val (trFr (Fc := Fc) m z) ≠ 0 := fun h ↦ by
    rw [h, map_zero] at hφz
    exact hvz ((map_eq_zero_iff _ φ.injective).mp hφz)
  set b₀s : T.F (m + 1) := algebraMap Cc (T.F (m + 1)) (r * c) / T.val (m + 1) z with hb₀s
  have hsq : (b₀ * T.val (m + 1) z) ^ 2 = (algebraMap Cc (T.F (m + 1)) (r * c)) ^ 2 := by
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
  have o3' := okS_spec (Fc := Fc) (hok 3 (by norm_num))
  have o2' := okS_spec (Fc := Fc) (hok 2 (by norm_num))
  have kn := hzC
  have on := okS_spec (Fc := Fc) kn
  have oXZ : Fr.ok (xFrS (Fc := Fc) m uF (aCS Fc ks m A 3) (aCS Fc ks m A 2) (zCS Fc ks m)) := by unfold xFrS; okt
  have odiv := Fr.ok_div (Fr.ok_ofPoly [1]) hzne
  have oYZ : Fr.ok (yZS Fc ks m A z uF) := by unfold yZS; okt
  have hv0 : T.val (m + 1) (zCS Fc ks m) = 0 := Subtype.ext (zero_div _)
  obtain ⟨PZ, hRZ, hmZ⟩ := Differential.SuperData.cert_pt φ jQ (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _
    hA hB _ _ hns0s' (Fr.smulC (Rat.cast s : KF Fc m) (xFrS (Fc := Fc) m uF (aCS Fc ks m A 3) (aCS Fc ks m A 2) (zCS Fc ks m)))
    (Fr.mul (yZS Fc ks m A z uF) (Fr.ofPoly [(Rat.cast (s * s * c) : KF Fc m)]))
    (Fr.ok_smulC _ oXZ) (Fr.ok_mul oYZ (Fr.ok_ofPoly _)) (by
      rw [ratMap_smulCS, T.xFrS_spec m h0 uF ouF _ _ _ (hok 3 (by norm_num)) (hok 2 (by norm_num))
        kn, hcC, hcC, hv0, hudef, mul_pow, hρ2, ← hu₀def]
      ring) (by
      rw [ratMap_mulCS m jQ _ oYZ]
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
      have hcc : algebraMap (T.F m) (RatFunc (T.F m)) (algebraMap Cc (T.F m) (c : Cc)) =
          (c : RatFunc (T.F m)) := by rw [map_ratCast, map_ratCast]
      rw [hcc]
      rw [show (u₀ * ρ) ^ 3 * (φ (cC 3) * (ρ * (c : RatFunc (T.F m)) / φ (T.val (m + 1) z))) =
        (u₀ * ρ) ^ 3 * ρ * (φ (cC 3) * ((c : RatFunc (T.F m)) / φ (T.val (m + 1) z))) by ring, e4]
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
/-- **The group condition at level `m + 1`** (function-field certificate over `Kₘ`). -/
theorem grp_of_chkTS (h0 : T.Tr (m + 1)) (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length)
    (hchk : kxChkTS Fc ks m g A B kt l cs z c uF Ac Bc kk k = true)
    (rtsF : List (T.F (m + 1))) (hrl : rtsF.length = (kxGens Fc ks (m + 1) g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks (m + 1) g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks (m + 1) g A B kt l cs)[i] : T.F (m + 1)))
    (b₀ : T.F (m + 1)) (hb₀ : b₀ ^ 2 = (T.MP (m + 1) h0).sem (A.getD 0 (MO Fc ks (m + 1)).zero)) :
    let cC : ℕ → T.F (m + 1) := (fun i ↦ (GPoly.toPoly (T.MP (m + 1) h0) A).coeff i)
    let xC : Fin cs.length → T.F (m + 1) := (fun q ↦ (T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))
    let βC : Fin cs.length → T.F (m + 1) := (fun q ↦
      ((kxRep Fc ks (m + 1) g A B kt l cs q).2 : T.F (m + 1)) *
        SqrtIndep.prodRoots rtsF (kxRep Fc ks (m + 1) g A B kt l cs q).1 *
        ((T.MP (m + 1) h0).sem (kxD Fc ks (m + 1) g cs q) *
          (T.MP (m + 1) h0).sem (kxR Fc ks (m + 1) A kt l cs q) /
          (GPoly.toPoly (T.MP (m + 1) h0) B).eval ((T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))))
    ∀ (hns : ∀ q, (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * xC q) (cC 3 * βC q))
      (hns0 : (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Nonsingular
        (cC 3 * 0) (cC 3 * b₀)),
      ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK
          (fun q ↦ kxMNm Fc ks (m + 1) g A B kt l cs q)
          (kxCl (m + 1) g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0 := by
  simp only [kxChkTS, Bool.and_eq_true] at hchk
  obtain ⟨hchk0, hcert⟩ := hchk
  have hΔq : 4 * (CPoly.toPoly Ac) ^ 3 + 27 * (CPoly.toPoly Bc) ^ 2 ≠ 0 := by
    simp only [kxChkT0S, Bool.and_eq_true, Bool.not_eq_true'] at hchk0
    have hdisc := hchk0.1.1.1.1.2
    intro h0'
    rw [show 4 * (CPoly.toPoly Ac) ^ 3 + 27 * (CPoly.toPoly Bc) ^ 2 =
      CPoly.toPoly (discCS Fc m Ac Bc) by
      simp only [discCS, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_mul, map_ofNat,
        Polynomial.C_ofNat]; ring, ← CPoly.isZero_iff] at h0'
    rw [h0'] at hdisc; exact absurd hdisc (by decide)
  exact T.grp_of_chkT0S m g A B kt l cs z c uF Ac Bc h0 k hchk0
    (fun PD PZ hRD hRZ m' n h ↦ indep_of_certQ Ac Bc (CPoly.toPoly Ac) (CPoly.toPoly Bc) rfl hΔq kk
      _ _ PD PZ hRD hRZ (by rw [← cdeg_spec, ← cdeg_spec]; exact hcert) m' n h) rtsF hrl hrs b₀ hb₀

end MTower

end Curves.MT
