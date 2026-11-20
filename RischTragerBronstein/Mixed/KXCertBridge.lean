import RischTragerBronstein.Mixed.KXField
import RischTragerBronstein.Mixed.KXHeight
import RischTragerBronstein.Mixed.KXRootSign
import RischTragerBronstein.Mixed.KXSem

/-!
# The group condition of the Mordell–Weil exception from an executable check

For a tower over a linear base curve `Fc = [c₀, [1]]` (so `F 0 ≃ Cc(X)`, `phi0`), at level `0`, when
every squared residue is a rational square (`kxGens = []`), the group hypothesis `HGC` of
`kx_not_elementary_mwC` follows from one Boolean check `kxChk` evaluated over `ℚ`:

* the codes involved have non-zero denominators, `B(c_q) ≠ 0`;
* `Ac`, `Bc` are the coefficients of the short model `y² = x³ + A x + B` of
  `Y² = c₃X³ + c₂X² + c₁X + c₀` (scaled by `u`), and `4A³ + 27B² ≠ 0`;
* `z² A(0) = r²` with `r ≠ 0` (so `√A(0) = ±r/z`);
* the height certificate `certQ` for `D = ∑ m_q P_q` and `P₊` passes.

`grp_of_chk` is the resulting group condition, for every realization and every choice of `√A(0)`.
-/

open Polynomial Differential IntermediateField WeierstrassCurve WeierstrassCurve.Affine

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

section Chk

variable (Fc ks) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- Executable `codeOK`. -/
def codeOKb (b : LC 0) : Bool := (show GPoly (GFrac ℚ) from b).all fun r ↦ !CPoly.isZero r.2

lemma codeOK_of {b : LC 0} (h : codeOKb b = true) : MTower.codeOK b := by
  intro r hr
  have := List.all_eq_true.mp h r hr
  simp only [Bool.not_eq_true', Bool.eq_false_iff] at this
  exact fun h0 ↦ this ((CPoly.isZero_iff _).mpr h0)

/-- The `i`-th coefficient code of `A`. -/
def aC (A : GPoly (LC 0)) (i : ℕ) : LC 0 := A.getD i (MO Fc ks 0).zero

/-- `y` on the linear base. -/
abbrev yL (c0f : CPoly ℚ) : Fr ℚ := (CPoly.neg c0f, [1])

variable (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
  (z : LC 0) (r : ℚ) (uF : Fr ℚ) (Ac Bc : CPoly ℚ) (kk kc : ℕ)

/-- `cᵢ` as fractions. -/
def cF (i : ℕ) : Fr ℚ := codeFr (yL c0f) (aC Fc ks A i)

/-- `u⁴ (c₁c₃ − c₂²/3)`. -/
def AFr : Fr ℚ :=
  Fr.mul (Fr.mul (Fr.mul uF uF) (Fr.mul uF uF))
    (Fr.sub (Fr.mul (cF Fc ks c0f A 1) (cF Fc ks c0f A 3))
      (Fr.smulC (1 / 3) (Fr.mul (cF Fc ks c0f A 2) (cF Fc ks c0f A 2))))

/-- `u⁶ (c₀c₃² − c₂c₁c₃/3 + 2c₂³/27)`. -/
def BFr : Fr ℚ :=
  Fr.mul (Fr.mul (Fr.mul uF uF) (Fr.mul (Fr.mul uF uF) (Fr.mul uF uF)))
    (Fr.add (Fr.sub (Fr.mul (cF Fc ks c0f A 0) (Fr.mul (cF Fc ks c0f A 3) (cF Fc ks c0f A 3)))
      (Fr.smulC (1 / 3) (Fr.mul (cF Fc ks c0f A 2) (Fr.mul (cF Fc ks c0f A 1) (cF Fc ks c0f A 3)))))
      (Fr.smulC (2 / 27) (Fr.mul (cF Fc ks c0f A 2) (Fr.mul (cF Fc ks c0f A 2) (cF Fc ks c0f A 2)))))

/-- The discriminant polynomial `4A³ + 27B²`. -/
def discC : CPoly ℚ := CPoly.add (CPoly.smul 4 (CPoly.mul Ac (CPoly.mul Ac Ac)))
  (CPoly.smul 27 (CPoly.mul Bc Bc))

/-- The certificate point of the pole `c_q`. -/
def ptQ (q : ℕ) : PtC ℚ :=
  some (MTower.xFr (yL c0f) uF (aC Fc ks A 3) (aC Fc ks A 2) (kqC Fc ks 0 cs q),
    Fr.mul (MTower.yBaseFr (yL c0f) uF (aC Fc ks A 3) (kxD Fc ks 0 g cs q) (kxR Fc ks 0 A kt l cs q)
      (kqC Fc ks 0 cs q) B) (Fr.ofPoly [(kxRep Fc ks 0 g A B kt l cs q).2]))

/-- The multiplicity of `c_q` in the class `kc`. -/
def mKc (q : ℕ) : ℤ :=
  if (kxRep Fc ks 0 g A B kt l cs q).1 == (kxCls Fc ks 0 g A B kt l cs).getD kc [] then
    (kxMNm Fc ks 0 g A B kt l cs q : ℤ) else 0

/-- The gcd of the multiplicities (`D = mG · D′`; certifying `D′` is cheaper and suffices). -/
def mG : ℕ := ((List.range cs.length).map (mKc Fc ks g A B kt l cs kc)).foldr
  (fun a b ↦ Int.gcd a (b : ℤ)) 0

/-- The certificate point `D′ = ∑ (m_q / mG) P_q`. -/
def ptD : PtC ℚ :=
  sumC Ac ((List.range cs.length).map fun q ↦
    (mKc Fc ks g A B kt l cs kc q / (mG Fc ks g A B kt l cs kc : ℤ),
      ptQ Fc ks c0f g A B kt l cs uF q))

/-- The certificate point `P₊ = (0, r/z)`. -/
def ptZ : PtC ℚ :=
  some (MTower.xFr (yL c0f) uF (aC Fc ks A 3) (aC Fc ks A 2) [],
    Fr.mul (Fr.mul uF (Fr.mul uF uF)) (Fr.mul (cF Fc ks c0f A 3)
      (Fr.div (Fr.ofPoly [r]) (codeFr (yL c0f) z))))

/-- **The check.** -/
def kxChk : Bool :=
  (List.range 4).all (fun i ↦ codeOKb (aC Fc ks A i)) && B.all codeOKb &&
  (List.range cs.length).all (fun q ↦ codeOKb (kqC Fc ks 0 cs q) &&
    codeOKb (kxD Fc ks 0 g cs q) && codeOKb (kxR Fc ks 0 A kt l cs q) &&
    !Fr.isZ (MTower.hornerFr (yL c0f) (codeFr (yL c0f) (kqC Fc ks 0 cs q)) B)) &&
  codeOKb z && !CPoly.isZero uF.2 && !Fr.isZ uF &&
  Fr.eqb (Fr.ofPoly Ac) (AFr Fc ks c0f A uF) && Fr.eqb (Fr.ofPoly Bc) (BFr Fc ks c0f A uF) &&
  !CPoly.isZero (discC Ac Bc) && r != 0 &&
  Fr.eqb (Fr.mul (Fr.mul (codeFr (yL c0f) z) (codeFr (yL c0f) z)) (cF Fc ks c0f A 0))
    (Fr.ofPoly [r * r]) &&
  certQ Ac (max (cdeg Ac) (cdeg Bc)) kk (ptD Fc ks c0f g A B kt l cs uF Ac kc)
    (ptZ Fc ks c0f A z r uF) && mG Fc ks g A B kt l cs kc != 0

end Chk

lemma foldr_gcd_dvd : ∀ (l : List ℤ), ∀ a ∈ l,
    ((l.foldr (fun a b ↦ Int.gcd a (b : ℤ)) 0 : ℕ) : ℤ) ∣ a
  | [], _, h => absurd h (by simp)
  | x :: l, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Int.gcd_dvd_left _ _
    · exact dvd_trans (Int.gcd_dvd_right _ _) (foldr_gcd_dvd l a h)

/-- **Multiples**: the group condition for `D′` gives it for `g D′` (`g > 0`). -/
lemma grp_of_div {G : Type*} [AddCommGroup G] (D Z : G) (g : ℕ) (hg : 0 < g)
    (h : ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • D + (2 * μ) • Z ≠ 0) :
    ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • ((g : ℤ) • D) + (2 * μ) • Z ≠ 0 := by
  intro N hN μ
  have := h (N * g) (Nat.mul_pos hN hg) μ
  rwa [smul_smul, show (2 : ℤ) * N * g = 2 * ((N * g : ℕ) : ℤ) by push_cast; ring]

/-- `Fr.ok` of a compound fraction from `Fr.ok` of its leaves (reducible matching only). -/
macro "okt" : tactic => `(tactic|
  repeat' first
    | with_reducible assumption
    | with_reducible refine Fr.ok_mul ?_ ?_
    | with_reducible refine Fr.ok_sub ?_ ?_
    | with_reducible refine Fr.ok_add ?_ ?_
    | with_reducible refine Fr.ok_smulC _ ?_)

namespace MTower

variable [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
variable (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
  (z : LC 0) (r : ℚ) (uF : Fr ℚ) (Ac Bc : CPoly ℚ) (kk : ℕ)

omit [CharZero L] in
lemma mK_eq_mKc (k : Fin (kxCls Fc ks 0 g A B kt l cs).length) (q : Fin cs.length) :
    ((Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
      (kxCl 0 g A B kt l cs) k q : ℕ) : ℤ) =
      mKc Fc ks g A B kt l cs k q := by
  classical
  unfold Differential.SuperData.mK mKc
  have hk : (kxCls Fc ks 0 g A B kt l cs).getD k [] = (kxCls Fc ks 0 g A B kt l cs)[(k : ℕ)] :=
    List.getD_eq_getElem _ _ k.2
  by_cases h : (kxRep Fc ks 0 g A B kt l cs q).1 = (kxCls Fc ks 0 g A B kt l cs)[(k : ℕ)]
  · have h' := (kxCl_eq_iff 0 g A B kt l cs q k).mpr h
    simp [h', h]
  · have h' : ¬ kxCl 0 g A B kt l cs q = k :=
      fun h'' ↦ h ((kxCl_eq_iff 0 g A B kt l cs q k).mp h'')
    simp [h', h]

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The group condition from the check** (level `0`, linear base, all residues rational squares),
for every realization and every choice of `√A(0)`. -/
theorem grp_of_chk (hFc : Fc = [c0f, [1]]) (h0 : T.Tr 0)
    (k : Fin (kxCls Fc ks 0 g A B kt l cs).length)
    (hchk : kxChk Fc ks c0f g A B kt l cs z r uF Ac Bc kk k = true)
    (hgens : kxGens Fc ks 0 g A B kt l cs = [])
    (rtsF : List (T.F 0)) (hrl : rtsF.length = (kxGens Fc ks 0 g A B kt l cs).length)
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
  simp only [kxChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    bne_iff_ne, ne_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hA4, hBok⟩, hcs⟩, hzok⟩, hu2⟩, huZ⟩, hAe⟩, hBe⟩, hdisc⟩, hr⟩, hze⟩, hcert⟩, hmG⟩ :=
    hchk
  have hrts : rtsF = [] := List.eq_nil_of_length_eq_zero (by rw [hrl, hgens]; rfl)
  set φ := T.phi0 c0f hFc with hφ
  set j := algebraMap ℚ Cc with hj
  have hyok : Fr.ok (yL c0f) := by simp [Fr.ok, CPoly.toPoly]
  have hval : ∀ b : LC 0, codeOK b → φ (T.val 0 b) = ratMap j (Fr.val (codeFr (yL c0f) b)) :=
    fun b hb ↦ T.phi0_val c0f hFc b hb
  have hsem : ∀ b : LC 0, (T.MP 0 h0).sem b = T.val 0 b := fun b ↦ T.sem_MP_F 0 h0 b
  have hcC : ∀ i, cC i = T.val 0 (aC Fc ks A i) := fun i ↦ by
    simp only [cC, aC]
    rw [Tower.PrimN.coeff_toPoly_getD]
    exact hsem _
  have hok : ∀ i < 4, codeOK (aC Fc ks A i) := fun i hi ↦ codeOK_of (hA4 i hi)
  have oc : ∀ i < 4, Fr.ok (cF Fc ks c0f A i) := fun i hi ↦ codeFr_ok _ hyok _ (hok i hi)
  have hcF : ∀ i < 4, φ (cC i) = ratMap j (Fr.val (cF Fc ks c0f A i)) := fun i hi ↦ by
    rw [hcC]; exact hval _ (hok i hi)
  have ouF : Fr.ok uF := fun h ↦ by
    rw [← CPoly.isZero_iff] at h; rw [h] at hu2; exact absurd hu2 (by decide)
  set u := ratMap j (Fr.val uF) with hudef
  have hu : u ≠ 0 := by
    rw [hudef, map_ne_zero_iff _ (ratMap j).injective]
    intro h; rw [← Fr.isZ_iff ouF] at h; rw [h] at huZ; exact absurd huZ (by decide)
  have o0 := oc 0 (by norm_num)
  have o1 := oc 1 (by norm_num)
  have o2 := oc 2 (by norm_num)
  have o3 := oc 3 (by norm_num)
  have oAFr : Fr.ok (AFr Fc ks c0f A uF) := by
    unfold AFr; okt
  have oBFr : Fr.ok (BFr Fc ks c0f A uF) := by
    unfold BFr; okt
  have hA : algebraMap Cc[X] (RatFunc Cc) ((CPoly.toPoly Ac).map j) =
      u ^ 4 * (φ (cC 1 * cC 3) - φ (cC 2) ^ 2 / 3) := by
    have e := congrArg (ratMap j) ((Fr.eqb_iff (Fr.ok_ofPoly Ac) oAFr).mp hAe)
    rw [Fr.val_ofPoly, ratMap_alg] at e
    rw [e]
    simp only [map_mul, map_pow]
    rw [hcF 1 (by norm_num), hcF 2 (by norm_num), hcF 3 (by norm_num)]
    unfold AFr
    simp (disch := okt) only
      [Fr.val_mul, Fr.val_sub, Fr.val_add, Fr.val_smulC]
    simp only [map_mul, map_sub, map_add, eq_ratCast, map_ratCast, hudef]
    ring
  have hB : algebraMap Cc[X] (RatFunc Cc) ((CPoly.toPoly Bc).map j) =
      u ^ 6 * (φ (cC 0 * cC 3 ^ 2) - φ (cC 2) * φ (cC 1 * cC 3) / 3 + 2 * φ (cC 2) ^ 3 / 27) := by
    have e := congrArg (ratMap j) ((Fr.eqb_iff (Fr.ok_ofPoly Bc) oBFr).mp hBe)
    rw [Fr.val_ofPoly, ratMap_alg] at e
    rw [e]
    simp only [map_mul, map_pow]
    rw [hcF 0 (by norm_num), hcF 1 (by norm_num), hcF 2 (by norm_num), hcF 3 (by norm_num)]
    unfold BFr
    simp (disch := okt) only
      [Fr.val_mul, Fr.val_sub, Fr.val_add, Fr.val_smulC]
    simp only [map_mul, map_sub, map_add, eq_ratCast, map_ratCast, hudef]
    ring
  have hΔ : 4 * ((CPoly.toPoly Ac).map j) ^ 3 + 27 * ((CPoly.toPoly Bc).map j) ^ 2 ≠ 0 := by
    have h1 : CPoly.toPoly (discC Ac Bc) ≠ 0 := fun h ↦ by
      rw [← CPoly.isZero_iff] at h; rw [h] at hdisc; exact absurd hdisc (by decide)
    have h2 : 4 * ((CPoly.toPoly Ac).map j) ^ 3 + 27 * ((CPoly.toPoly Bc).map j) ^ 2 =
        (CPoly.toPoly (discC Ac Bc)).map j := by
      simp only [discC, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_mul, Polynomial.map_add,
        Polynomial.map_mul, Polynomial.map_C]
      simp only [eq_ratCast, map_ofNat, Polynomial.C_ofNat]
      ring
    rw [h2]
    exact (Polynomial.map_ne_zero_iff j.injective).mpr h1
  have hBc : ∀ b ∈ B, codeOK b := fun b hb ↦ codeOK_of (hBok b hb)
  have hq : ∀ q : Fin cs.length, ∃ Pk : (shortW (CPoly.toPoly Ac) (CPoly.toPoly Bc)).toAffine.Point,
      Rel _ _ (ptQ Fc ks c0f g A B kt l cs uF q) Pk ∧
      mapE j _ _ Pk = Differential.SuperData.toShort φ (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _ hA hB
        (Point.some _ _ (hns q)) := by
    intro q
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
    have hB0 : (GPoly.toPoly (T.MP 0 h0) B).eval (T.val 0 (kqC Fc ks 0 cs q)) ≠ 0 := fun h ↦ by
      apply hH0
      rw [h, map_zero] at hHs
      exact (map_eq_zero_iff _ (ratMap j).injective).mp hHs
    have oY : Fr.ok (yBaseFr (yL c0f) uF (aC Fc ks A 3) (kxD Fc ks 0 g cs q)
        (kxR Fc ks 0 A kt l cs q) (kqC Fc ks 0 cs q) B) := by
      unfold yBaseFr
      have := Fr.ok_div (Fr.ok_mul oD oR) hH0
      okt
    have oX : Fr.ok (xFr (yL c0f) uF (aC Fc ks A 3) (aC Fc ks A 2) (kqC Fc ks 0 cs q)) := by
      unfold xFr; okt
    refine Differential.SuperData.cert_pt φ j (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _ hA hB _ _ (hns q)
      _ _ oX (Fr.ok_mul oY (Fr.ok_ofPoly _)) ?_ ?_
    · rw [T.xFr_spec c0f hFc uF ouF _ _ _ (hok 3 (by norm_num)) (hok 2 (by norm_num)) kq, hcC, hcC]
      simp only [xC, hsem]
      rfl
    · rw [frMap_mulConst j _ oY, T.yBaseFr_spec c0f hFc h0 uF ouF _ _ _ _ B (hok 3 (by norm_num)) kD kR
        kq hBc hB0]
      simp only [βC, hrts, hcC, hsem, SqrtIndep.prodRoots, mul_one]
      simp only [map_mul, map_div₀, map_ratCast, eq_ratCast]
      ring
  -- the sum `D`
  set lst : List (ℤ × PtC ℚ × (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Point) :=
    (List.finRange cs.length).map (fun q : Fin cs.length ↦ (mKc Fc ks g A B kt l cs k (q : ℕ) /
        (mG Fc ks g A B kt l cs k : ℤ), ptQ Fc ks c0f g A B kt l cs uF (q : ℕ), Point.some _ _ (hns q))) with hlst
  obtain ⟨PD, hRD, hmD⟩ := Differential.SuperData.cert_sum φ j (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _
    hA hB Ac rfl lst (fun e he ↦ by
      rw [hlst, List.mem_map] at he
      obtain ⟨q, -, rfl⟩ := he
      exact hq q)
  have hl1 : lst.map (fun e ↦ (e.1, e.2.1)) = (List.range cs.length).map (fun q ↦
      (mKc Fc ks g A B kt l cs k q / (mG Fc ks g A B kt l cs k : ℤ),
        ptQ Fc ks c0f g A B kt l cs uF q)) := by
    apply List.ext_getElem <;> simp [hlst]
  rw [hl1] at hRD
  have hl2 : (lst.map fun e ↦ e.1 • e.2.2).sum = ∑ q : Fin cs.length, (mKc Fc ks g A B kt l cs k (q : ℕ) /
      (mG Fc ks g A B kt l cs k : ℤ)) • Point.some _ _ (hns q) := by
    rw [Fin.sum_univ_def, hlst, List.map_map]
    rfl
  have hdvd : ∀ q : Fin cs.length, (mG Fc ks g A B kt l cs k : ℤ) ∣ mKc Fc ks g A B kt l cs k q :=
    fun q ↦ foldr_gcd_dvd _ _ (List.mem_map.mpr ⟨q, List.mem_range.mpr q.2, rfl⟩)
  have hD : ∑ q, ((Differential.SuperData.mK (fun q ↦ kxMNm Fc ks 0 g A B kt l cs q)
      (kxCl 0 g A B kt l cs) k q : ℕ) : ℤ) • Point.some _ _ (hns q) =
      (mG Fc ks g A B kt l cs k : ℤ) • (lst.map fun e ↦ e.1 • e.2.2).sum := by
    rw [hl2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [smul_smul, Int.mul_ediv_cancel' (hdvd q), mK_eq_mKc]
  -- the point `P₊`
  have kz := codeOK_of hzok
  have ozF := codeFr_ok _ hyok _ kz
  have hzeq := (Fr.eqb_iff (Fr.ok_mul (Fr.ok_mul ozF ozF) o0) (Fr.ok_ofPoly _)).mp hze
  rw [Fr.val_mul (Fr.ok_mul ozF ozF) o0, Fr.val_mul ozF ozF, Fr.val_ofPoly] at hzeq
  have hrr : algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly [r * r]) = ((r ^ 2 : ℚ) : RatFunc ℚ) := by
    simp [CPoly.toPoly, RatFunc.algebraMap_C, sq]
  rw [hrr] at hzeq
  have hzne : Fr.val (codeFr (yL c0f) z) ≠ 0 := fun h ↦ by
    rw [h, zero_mul, zero_mul] at hzeq
    have h2 : ((r ^ 2 : ℚ) : RatFunc ℚ) = 0 := hzeq.symm
    rw [Rat.cast_eq_zero] at h2
    exact hr ((pow_eq_zero_iff two_ne_zero).mp h2)
  have hφz : φ (T.val 0 z) = ratMap j (Fr.val (codeFr (yL c0f) z)) := hval z kz
  have hvz : T.val 0 z ≠ 0 := fun h ↦ by
    rw [h, map_zero] at hφz
    exact hzne ((map_eq_zero_iff _ (ratMap j).injective).mp hφz.symm)
  set b₀s : T.F 0 := (r : T.F 0) / T.val 0 z with hb₀s
  have hsq : (b₀ * T.val 0 z) ^ 2 = ((r : T.F 0)) ^ 2 := by
    apply φ.injective
    have hb : φ b₀ ^ 2 = ratMap j (Fr.val (cF Fc ks c0f A 0)) := by
      rw [← map_pow, hb₀, hsem, ← hcF 0 (by norm_num), hcC]; rfl
    have e2 := congrArg (ratMap j) hzeq
    simp only [map_mul, map_ratCast] at e2
    rw [mul_pow, map_mul, map_pow, map_pow, hb, hφz, map_pow, map_ratCast]
    push_cast at e2
    linear_combination e2
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
  have odiv := Fr.ok_div (Fr.ok_ofPoly [r]) hzne
  have oYZ : Fr.ok (Fr.mul (Fr.mul uF (Fr.mul uF uF)) (Fr.mul (cF Fc ks c0f A 3)
      (Fr.div (Fr.ofPoly [r]) (codeFr (yL c0f) z)))) := by okt
  have hv0 : T.val 0 ([] : LC 0) = 0 := by
    apply φ.injective
    rw [hval _ kn, map_zero]
    simp [codeFr, Fr.val_ofPoly, CPoly.toPoly]
  obtain ⟨PZ, hRZ, hmZ⟩ := Differential.SuperData.cert_pt φ j (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _
    hA hB _ _ hns0s' _ _ oXZ oYZ (by
      rw [T.xFr_spec c0f hFc uF ouF _ _ _ (hok 3 (by norm_num)) (hok 2 (by norm_num)) kn, hcC, hcC,
        hv0]) (by
      simp only [Fr.val_mul (Fr.ok_mul ouF (Fr.ok_mul ouF ouF)) (Fr.ok_mul o3 odiv),
        Fr.val_mul ouF (Fr.ok_mul ouF ouF), Fr.val_mul ouF ouF, Fr.val_mul o3 odiv,
        Fr.val_div (Fr.ok_ofPoly [r]) ozF hzne, Fr.val_ofPoly]
      simp only [map_mul, map_div₀, hb₀s, ← hcF 3 (by norm_num), ← hφz, hudef]
      have hrC : ratMap j (algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly [r])) = (r : RatFunc Cc) := by
        rw [ratMap_alg]
        simp only [CPoly.toPoly_cons, CPoly.toPoly_nil, mul_zero, add_zero, Polynomial.map_C,
          RatFunc.algebraMap_C, eq_ratCast]
        exact map_ratCast _ _
      rw [hrC, map_ratCast]
      ring)
  have hc' : certQ Ac (max (CPoly.toPoly Ac).natDegree (CPoly.toPoly Bc).natDegree) kk
      (ptD Fc ks c0f g A B kt l cs uF Ac k) (ptZ Fc ks c0f A z r uF) = true := by
    rw [← cdeg_spec, ← cdeg_spec]; exact hcert
  have hgr := Differential.SuperData.hgrp_of_cert φ j (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _ hA hB hΔ
    _ _ Ac rfl kk _ _ PD PZ hRD hRZ hmD hmZ hc'
  have hgr' : ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • (lst.map fun e ↦ e.1 • e.2.2).sum +
      (2 * μ) • Point.some _ _ hns0s' ≠ 0 := by
    convert hgr
  have hfin := grp_of_div _ _ _ (Nat.pos_of_ne_zero hmG)
    (grp_signs _ _ _ _ (Or.inl rfl) (hsign hns0s') hgr')
  intro N hN μ
  convert hfin N hN μ using 3

end MTower

end Curves.MT
