import RischTragerBronstein.Mixed.KXCertBridge
import RischTragerBronstein.Mixed.KQMMain

/-!
# The bridge check over a number field `k₀`

`KXCertBridge` handles the Mordell–Weil exception of `kxDecide` when every square root involved is
rational. Here the certificate is computed over a field `k₀ ⊇ ℚ` (executable, e.g. Mathlib's
`QuadraticAlgebra ℚ d 0`) containing square roots `ρᵢ` of the class generators `gᵢ` (`kxGens`) and a
square root `σ` of `κ = z² A(0)`:

* the points are `P_q = (x_q, y_q · ρ_q)` with `x_q, y_q` the executable fractions over `ℚ` of
  `KXCertBridge` and `ρ_q = c_q ∏_{T_q} ρᵢ ∈ k₀`, and `P₊ = (x₀, (u³ c₃ / z) · σ)`;
* `kxChkK` = the `ℚ`-side checks, `ρᵢ² = gᵢ`, `σ² = κ`, and `certQ` over `k₀`.

The roots supplied by a realization are constants (a square root of a non-zero rational has zero
derivative: `const_of_sq`), so an embedding `j : k₀ → Cc` with `j ρᵢ = rᵢ`, `j σ = ±s` (hypothesis
`hlift`, proved per field: `qaEmbed` for one quadratic generator) transports the certificate:
`grp_of_chkK` gives the group hypothesis of `kx_not_elementary_mwC`.
-/

open Polynomial Differential IntermediateField WeierstrassCurve WeierstrassCurve.Affine

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

section ChkK

variable (Fc ks) [Fact (Irreducible (toPoly (fKc Fc)))]
variable {k₀ : Type*} [Field k₀] [DecidableEq k₀] [CharZero k₀]
variable (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
  (z : LC 0) (κ : ℚ) (ρs : List k₀) (σ : k₀) (uF : Fr ℚ) (Ac Bc : CPoly ℚ) (kk kc : ℕ)

/-- The `k₀`-factor `c_q ∏_{T_q} ρᵢ` of the ordinate of `P_q`. -/
def rhoQ (q : ℕ) : k₀ :=
  ((kxRep Fc ks 0 g A B kt l cs q).2 : k₀) * SqrtIndep.prodRoots ρs (kxRep Fc ks 0 g A B kt l cs q).1

/-- The certificate point of the pole `c_q`, over `k₀`. -/
def ptQK (q : ℕ) : PtC k₀ :=
  some (Fr.norm (frMap (algebraMap ℚ k₀)
      (MTower.xFr (yL c0f) uF (aC Fc ks A 3) (aC Fc ks A 2) (kqC Fc ks 0 cs q))),
    Fr.norm (Fr.mul (frMap (algebraMap ℚ k₀) (MTower.yBaseFr (yL c0f) uF (aC Fc ks A 3)
      (kxD Fc ks 0 g cs q) (kxR Fc ks 0 A kt l cs q) (kqC Fc ks 0 cs q) B))
      (Fr.ofPoly [rhoQ Fc ks g A B kt l cs ρs q])))

/-- `D′ = ∑ (m_q / mG) P_q` over `k₀`. -/
def ptDK : PtC k₀ :=
  sumC (Ac.map (algebraMap ℚ k₀)) ((List.range cs.length).map fun q ↦
    (mKc Fc ks g A B kt l cs kc q / (mG Fc ks g A B kt l cs kc : ℤ),
      ptQK Fc ks c0f g A B kt l cs ρs uF q))

/-- The `ℚ`-part `u³ c₃ / z` of the ordinate of `P₊`. -/
def yZ : Fr ℚ :=
  Fr.mul (Fr.mul uF (Fr.mul uF uF)) (Fr.mul (cF Fc ks c0f A 3)
    (Fr.div (Fr.ofPoly [1]) (codeFr (yL c0f) z)))

/-- `P₊ = (0, σ/z)` over `k₀`. -/
def ptZK : PtC k₀ :=
  some (Fr.norm (frMap (algebraMap ℚ k₀) (MTower.xFr (yL c0f) uF (aC Fc ks A 3) (aC Fc ks A 2) [])),
    Fr.norm (Fr.mul (frMap (algebraMap ℚ k₀) (yZ Fc ks c0f A z uF)) (Fr.ofPoly [σ])))

/-- **The check over `k₀`.** -/
def kxChkK : Bool :=
  (List.range 4).all (fun i ↦ codeOKb (aC Fc ks A i)) && B.all codeOKb &&
  (List.range cs.length).all (fun q ↦ codeOKb (kqC Fc ks 0 cs q) &&
    codeOKb (kxD Fc ks 0 g cs q) && codeOKb (kxR Fc ks 0 A kt l cs q) &&
    !Fr.isZ (MTower.hornerFr (yL c0f) (codeFr (yL c0f) (kqC Fc ks 0 cs q)) B)) &&
  codeOKb z && !CPoly.isZero uF.2 && !Fr.isZ uF &&
  Fr.eqb (Fr.ofPoly Ac) (AFr Fc ks c0f A uF) && Fr.eqb (Fr.ofPoly Bc) (BFr Fc ks c0f A uF) &&
  !CPoly.isZero (discC Ac Bc) && κ != 0 &&
  Fr.eqb (Fr.mul (Fr.mul (codeFr (yL c0f) z) (codeFr (yL c0f) z)) (cF Fc ks c0f A 0))
    (Fr.ofPoly [κ]) &&
  ρs.length == (kxGens Fc ks 0 g A B kt l cs).length &&
  (List.range ρs.length).all (fun i ↦
    ρs.getD i 0 * ρs.getD i 0 == ((kxGens Fc ks 0 g A B kt l cs).getD i 0 : k₀)) &&
  σ * σ == (κ : k₀) &&
  certQ (Ac.map (algebraMap ℚ k₀)) (max (cdeg Ac) (cdeg Bc)) kk
    (ptDK Fc ks c0f g A B kt l cs ρs uF Ac kc) (ptZK Fc ks c0f A z σ uF) &&
  mG Fc ks g A B kt l cs kc != 0

end ChkK

namespace MTower

variable [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)

/-- **A square root of a non-zero rational in `F 0` is a constant.** -/
lemma const_of_sq (x : T.F 0) (q : ℚ) (hq : q ≠ 0) (h : x ^ 2 = (q : T.F 0)) :
    ∃ c : Cc, algebraMap Cc (T.F 0) c = x := by
  have hL : (x : L) ^ 2 = (q : L) := by
    have := congrArg (fun y : T.F 0 ↦ (y : L)) h
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

omit [Fact (Irreducible (toPoly (fKc Fc)))] in
lemma consts_of_list : ∀ l : List (T.F 0), (∀ x ∈ l, ∃ c : Cc, algebraMap Cc (T.F 0) c = x) →
    ∃ ls : List Cc, ls.map (algebraMap Cc (T.F 0)) = l
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨c, hc⟩ := h x List.mem_cons_self
    obtain ⟨ls, hls⟩ := consts_of_list l fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    exact ⟨c :: ls, by simp [hc, hls]⟩

variable (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
  (z : LC 0) (κ : ℚ) {k₀ : Type*} [Field k₀] [DecidableEq k₀] [CharZero k₀] (ρs : List k₀) (σ : k₀)
  (uF : Fr ℚ) (Ac Bc : CPoly ℚ) (kk : ℕ)

set_option maxHeartbeats 8000000 in
open Classical in
/-- **The group condition from the check over `k₀`**, for every realization, every choice of the
roots of the generators and of `√A(0)`, given embeddings `k₀ → Cc` sending `ρᵢ`, `σ` to any
prescribed roots (`hlift`). -/
theorem grp_of_chkK (hFc : Fc = [c0f, [1]]) (h0 : T.Tr 0)
    (k : Fin (kxCls Fc ks 0 g A B kt l cs).length)
    (hchk : kxChkK Fc ks c0f g A B kt l cs z κ ρs σ uF Ac Bc kk k = true)
    (hlift : ∀ (rs : List Cc) (s : Cc), rs.length = ρs.length →
      (∀ i (hi : i < rs.length) (hi' : i < (kxGens Fc ks 0 g A B kt l cs).length),
        rs[i] ^ 2 = ((kxGens Fc ks 0 g A B kt l cs)[i] : Cc)) → s ^ 2 = (κ : Cc) →
      ∃ j : k₀ →+* Cc, (∀ i (hi : i < ρs.length) (hi' : i < rs.length), j ρs[i] = rs[i]) ∧
        (j σ = s ∨ j σ = -s))
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
  simp only [kxChkK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    bne_iff_ne, ne_eq, beq_iff_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hA4, hBok⟩, hcs⟩, hzok⟩, hu2⟩, huZ⟩, hAe⟩, hBe⟩, hdisc⟩, hκ⟩, hze⟩, hρl⟩,
    hρs⟩, hσ⟩, hcert⟩, hmG⟩ := hchk
  set φ := T.phi0 c0f hFc with hφ
  set jQ := algebraMap ℚ Cc with hjQ
  set e := algebraMap ℚ k₀ with he
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
  set u := ratMap jQ (Fr.val uF) with hudef
  have hu : u ≠ 0 := by
    rw [hudef, map_ne_zero_iff _ (ratMap jQ).injective]
    intro h; rw [← Fr.isZ_iff ouF] at h; rw [h] at huZ; exact absurd huZ (by decide)
  have o0 := oc 0 (by norm_num)
  have o1 := oc 1 (by norm_num)
  have o2 := oc 2 (by norm_num)
  have o3 := oc 3 (by norm_num)
  have oAFr : Fr.ok (AFr Fc ks c0f A uF) := by
    unfold AFr; okt
  have oBFr : Fr.ok (BFr Fc ks c0f A uF) := by
    unfold BFr; okt
  have hAQ : algebraMap Cc[X] (RatFunc Cc) ((CPoly.toPoly Ac).map jQ) =
      u ^ 4 * (φ (cC 1 * cC 3) - φ (cC 2) ^ 2 / 3) := by
    have e' := congrArg (ratMap jQ) ((Fr.eqb_iff (Fr.ok_ofPoly Ac) oAFr).mp hAe)
    rw [Fr.val_ofPoly, ratMap_alg] at e'
    rw [e']
    simp only [map_mul, map_pow]
    rw [hcF 1 (by norm_num), hcF 2 (by norm_num), hcF 3 (by norm_num)]
    unfold AFr
    simp (disch := okt) only [Fr.val_mul, Fr.val_sub, Fr.val_smulC]
    simp only [map_mul, map_sub, eq_ratCast, map_ratCast, hudef]
    ring
  have hBQ : algebraMap Cc[X] (RatFunc Cc) ((CPoly.toPoly Bc).map jQ) =
      u ^ 6 * (φ (cC 0 * cC 3 ^ 2) - φ (cC 2) * φ (cC 1 * cC 3) / 3 + 2 * φ (cC 2) ^ 3 / 27) := by
    have e' := congrArg (ratMap jQ) ((Fr.eqb_iff (Fr.ok_ofPoly Bc) oBFr).mp hBe)
    rw [Fr.val_ofPoly, ratMap_alg] at e'
    rw [e']
    simp only [map_mul, map_pow]
    rw [hcF 0 (by norm_num), hcF 1 (by norm_num), hcF 2 (by norm_num), hcF 3 (by norm_num)]
    unfold BFr
    simp (disch := okt) only [Fr.val_mul, Fr.val_sub, Fr.val_add, Fr.val_smulC]
    simp only [map_mul, map_sub, map_add, eq_ratCast, map_ratCast, hudef]
    ring
  have hΔQ : 4 * ((CPoly.toPoly Ac).map jQ) ^ 3 + 27 * ((CPoly.toPoly Bc).map jQ) ^ 2 ≠ 0 := by
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
  -- the constants and the embedding `j`
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
  obtain ⟨s, hs⟩ := T.const_of_sq _ _ hκ hw
  have hs2 : s ^ 2 = (κ : Cc) := by
    apply (algebraMap Cc (T.F 0)).injective
    rw [map_pow, hs, hw, map_ratCast]
  obtain ⟨j, hjρ, hjσ⟩ := hlift rs s (by rw [hrsl, hρl]) hrs2 hs2
  have hρj : ρs.map j = rs := List.ext_getElem (by simp [hrsl, hρl]) (fun i h1 h2 ↦ by
    simp only [List.getElem_map]; exact hjρ i (by simpa using h1) h2)
  have hje : j.comp e = jQ := RingHom.ext_rat _ _
  have hmapA : ((CPoly.toPoly Ac).map e).map j = (CPoly.toPoly Ac).map jQ := by
    rw [Polynomial.map_map, hje]
  have hmapB : ((CPoly.toPoly Bc).map e).map j = (CPoly.toPoly Bc).map jQ := by
    rw [Polynomial.map_map, hje]
  have hA : algebraMap Cc[X] (RatFunc Cc) (((CPoly.toPoly Ac).map e).map j) =
      u ^ 4 * (φ (cC 1 * cC 3) - φ (cC 2) ^ 2 / 3) := by rw [hmapA]; exact hAQ
  have hB : algebraMap Cc[X] (RatFunc Cc) (((CPoly.toPoly Bc).map e).map j) =
      u ^ 6 * (φ (cC 0 * cC 3 ^ 2) - φ (cC 2) * φ (cC 1 * cC 3) / 3 + 2 * φ (cC 2) ^ 3 / 27) := by
    rw [hmapB]; exact hBQ
  have hΔ : 4 * (((CPoly.toPoly Ac).map e).map j) ^ 3 +
      27 * (((CPoly.toPoly Bc).map e).map j) ^ 2 ≠ 0 := by rw [hmapA, hmapB]; exact hΔQ
  have hratm : ∀ f : Fr ℚ, ratMap j (Fr.val (frMap e f)) = ratMap jQ (Fr.val f) := fun f ↦ by
    rw [frMap_val, ratMap_comp j]
  have hBc : ∀ b ∈ B, codeOK b := fun b hb ↦ codeOK_of (hBok b hb)
  have hβ : ∀ q : Fin cs.length, βC q = algebraMap Cc (T.F 0)
      (((kxRep Fc ks 0 g A B kt l cs q).2 : Cc) *
        SqrtIndep.prodRoots rs (kxRep Fc ks 0 g A B kt l cs q).1) *
      ((T.MP 0 h0).sem (kxD Fc ks 0 g cs q) * (T.MP 0 h0).sem (kxR Fc ks 0 A kt l cs q) /
          (GPoly.toPoly (T.MP 0 h0) B).eval ((T.MP 0 h0).sem (kqC Fc ks 0 cs q))) := fun q ↦ by
    simp only [βC, map_mul, map_ratCast, SqrtIndep.map_prodRoots]
  have hjρq : ∀ q, j (rhoQ Fc ks g A B kt l cs ρs q) = ((kxRep Fc ks 0 g A B kt l cs q).2 : Cc) *
      SqrtIndep.prodRoots rs (kxRep Fc ks 0 g A B kt l cs q).1 := fun q ↦ by
    simp only [rhoQ, map_mul, map_ratCast, SqrtIndep.map_prodRoots, hρj]
  have hq : ∀ q : Fin cs.length, ∃ Pk : (shortW ((CPoly.toPoly Ac).map e)
      ((CPoly.toPoly Bc).map e)).toAffine.Point,
      Rel _ _ (ptQK Fc ks c0f g A B kt l cs ρs uF q) Pk ∧
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
      exact (map_eq_zero_iff _ (ratMap jQ).injective).mp hHs
    have oY : Fr.ok (yBaseFr (yL c0f) uF (aC Fc ks A 3) (kxD Fc ks 0 g cs q)
        (kxR Fc ks 0 A kt l cs q) (kqC Fc ks 0 cs q) B) := by
      unfold yBaseFr
      have := Fr.ok_div (Fr.ok_mul oD oR) hH0
      okt
    have oX : Fr.ok (xFr (yL c0f) uF (aC Fc ks A 3) (aC Fc ks A 2) (kqC Fc ks 0 cs q)) := by
      unfold xFr; okt
    refine Differential.SuperData.cert_pt φ j (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _ hA hB _ _ (hns q)
      _ _ (Fr.ok_norm (frMap_ok e _ oX)) (Fr.ok_norm (Fr.ok_mul (frMap_ok e _ oY) (Fr.ok_ofPoly _)))
      ?_ ?_
    · rw [Fr.val_norm (frMap_ok e _ oX), hratm, T.xFr_spec c0f hFc uF ouF _ _ _ (hok 3 (by norm_num)) (hok 2 (by norm_num)) kq,
        hcC, hcC]
      simp only [xC, hsem]
      rfl
    · rw [Fr.val_norm (Fr.ok_mul (frMap_ok e _ oY) (Fr.ok_ofPoly _)),
        frMap_mulConst j _ (frMap_ok e _ oY), hratm, T.yBaseFr_spec c0f hFc h0 uF ouF _ _ _ _ B
        (hok 3 (by norm_num)) kD kR kq hBc hB0, hjρq, hβ, hcC]
      simp only [hsem, map_mul, map_div₀, hφc]
      ring
  -- the sum `D`
  set lst : List (ℤ × PtC k₀ × (Differential.SuperData.WG (cC 3) (cC 2) (cC 1) (cC 0)).Point) :=
    (List.finRange cs.length).map (fun q : Fin cs.length ↦ (mKc Fc ks g A B kt l cs k (q : ℕ) /
        (mG Fc ks g A B kt l cs k : ℤ), ptQK Fc ks c0f g A B kt l cs ρs uF (q : ℕ),
          Point.some _ _ (hns q))) with hlst
  obtain ⟨PD, hRD, hmD⟩ := Differential.SuperData.cert_sum φ j (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _
    hA hB (Ac.map e) (toPoly_map e Ac) lst (fun e' he' ↦ by
      rw [hlst, List.mem_map] at he'
      obtain ⟨q, -, rfl⟩ := he'
      exact hq q)
  have hl1 : lst.map (fun e ↦ (e.1, e.2.1)) = (List.range cs.length).map (fun q ↦
      (mKc Fc ks g A B kt l cs k q / (mG Fc ks g A B kt l cs k : ℤ),
        ptQK Fc ks c0f g A B kt l cs ρs uF q)) := by
    apply List.ext_getElem <;> simp [hlst]
  rw [hl1] at hRD
  have hl2 : (lst.map fun e ↦ e.1 • e.2.2).sum = ∑ q : Fin cs.length,
      (mKc Fc ks g A B kt l cs k (q : ℕ) / (mG Fc ks g A B kt l cs k : ℤ)) •
        Point.some _ _ (hns q) := by
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
  set b₀s : T.F 0 := algebraMap Cc (T.F 0) (j σ) / T.val 0 z with hb₀s
  have hsq : (b₀ * T.val 0 z) ^ 2 = (algebraMap Cc (T.F 0) (j σ)) ^ 2 := by
    rcases hjσ with h | h <;> rw [h] <;> simp [hs]
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
  obtain ⟨PZ, hRZ, hmZ⟩ := Differential.SuperData.cert_pt φ j (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _
    hA hB _ _ hns0s' _ _ (Fr.ok_norm (frMap_ok e _ oXZ))
    (Fr.ok_norm (Fr.ok_mul (frMap_ok e _ oYZ) (Fr.ok_ofPoly _))) (by
      rw [Fr.val_norm (frMap_ok e _ oXZ), hratm, T.xFr_spec c0f hFc uF ouF _ _ _ (hok 3 (by norm_num)) (hok 2 (by norm_num)) kn,
        hcC, hcC, hv0]) (by
      rw [Fr.val_norm (Fr.ok_mul (frMap_ok e _ oYZ) (Fr.ok_ofPoly _)),
        frMap_mulConst j _ (frMap_ok e _ oYZ), hratm]
      unfold yZ
      simp only [Fr.val_mul (Fr.ok_mul ouF (Fr.ok_mul ouF ouF)) (Fr.ok_mul o3 odiv),
        Fr.val_mul ouF (Fr.ok_mul ouF ouF), Fr.val_mul ouF ouF, Fr.val_mul o3 odiv,
        Fr.val_div (Fr.ok_ofPoly [1]) ozF hzne, Fr.val_ofPoly]
      simp only [map_mul, map_div₀, hb₀s, ← hcF 3 (by norm_num), ← hφz, hudef, hφc]
      have h1 : ratMap jQ (algebraMap ℚ[X] (RatFunc ℚ) (CPoly.toPoly [1])) = 1 := by
        simp [CPoly.toPoly]
      rw [h1]
      ring)
  have hc' : certQ (Ac.map e) (max ((CPoly.toPoly Ac).map e).natDegree
      ((CPoly.toPoly Bc).map e).natDegree) kk
      (ptDK Fc ks c0f g A B kt l cs ρs uF Ac k) (ptZK Fc ks c0f A z σ uF) = true := by
    rw [Polynomial.natDegree_map, Polynomial.natDegree_map, ← cdeg_spec, ← cdeg_spec]; exact hcert
  have hgr := Differential.SuperData.hgrp_of_cert φ j (cC 3) (cC 2) (cC 1) (cC 0) u hu _ _ hA hB hΔ
    _ _ (Ac.map e) (toPoly_map e Ac) kk _ _ PD PZ hRD hRZ hmD hmZ hc'
  have hgr' : ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • (lst.map fun e ↦ e.1 • e.2.2).sum +
      (2 * μ) • Point.some _ _ hns0s' ≠ 0 := by
    convert hgr
  have hfin := grp_of_div _ _ _ (Nat.pos_of_ne_zero hmG)
    (grp_signs _ _ _ _ (Or.inl rfl) (hsign hns0s') hgr')
  intro N hN μ
  convert hfin N hN μ using 3

end MTower

end Curves.MT
