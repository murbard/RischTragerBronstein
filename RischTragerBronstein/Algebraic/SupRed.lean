import RischTragerBronstein.Algebraic.SupLogOracle
import RischTragerBronstein.Jacobian.CertCheckK

/-!
# Good reduction of superelliptic data over a field with a certified reduction

`RedFns p K`: a computable integrality test and residue map, induced (`RedValid`) by an embedding
`φ : K → ℚ_p` (for `ℚ`: `ratFns`; for a number field `ℚ[θ]/(M)` and a simple root `s` of `M` mod
`p`: `nfFns`, with `φ` from Hensel's lemma).
`supCheckR` checks, modulo `p`, the good-reduction conditions for `yⁿ = f(x)` over `K`, a divisor
`Γ` and base points with a non-speciality certificate; `supCheckR_spec` provides the
`SupGoodData` behind `torsion_iff_two_primes_N`.
-/

open Polynomial CPoly CPoly.Kron

namespace Sup

variable (p : ℕ) [hp : Fact p.Prime]

/-- A computable reduction of `K` at `p`: an integrality test and a residue map. -/
structure RedFns (K : Type*) where
  /-- a sufficient test for integrality -/
  ok : K → Bool
  /-- the residue -/
  red : K → ZMod p

/-- The reduction is induced by the embedding `φ : K → ℚ_p`. -/
def RedValid {K : Type*} [Field K] (R : RedFns p K) (φ : K →+* ℚ_[p]) : Prop :=
  ∀ x, R.ok x = true → ∃ z : ℤ_[p], φ x = algebraMap ℤ_[p] ℚ_[p] z ∧ PadicInt.toZMod z = R.red x

/-- The reduction of `ℚ`. -/
def ratFns : RedFns p ℚ := ⟨fun c ↦ c.den % p != 0, Jac.ratMod p⟩

lemma ratFns_valid : RedValid p (ratFns p) (algebraMap ℚ ℚ_[p]) := fun c hc ↦ by
  obtain ⟨w, hw, hwr⟩ := Jac.exists_lift_rat (p := p) (c := c) (by simpa [ratFns] using hc)
  exact ⟨w, hw.symm, hwr⟩

/-- The reduction of a number field `ℚ[θ]/(M)` at `θ ↦ s` modulo `p`. -/
def nfFns {M : CPoly ℚ} (s : ZMod p) : RedFns p (NFC.NF M) :=
  ⟨fun x ↦ Jac.pIntL p x.1, fun x ↦ Jac.redL p s x.1⟩

lemma nfFns_valid {M : CPoly ℚ} [Fact (Irreducible (toPoly M))] (mZ : ℤ[X])
    (hmZ : toPoly M = mZ.map (Int.castRingHom ℚ)) (s : ZMod p)
    (hs : (mZ.map (Int.castRingHom (ZMod p))).eval s = 0)
    (hs' : ((derivative mZ).map (Int.castRingHom (ZMod p))).eval s ≠ 0) :
    ∃ φ : NFC.NF M →+* ℚ_[p], RedValid p (nfFns (M := M) p s) φ := by
  obtain ⟨z, hz, hzs⟩ := Jac.hensel_root_red mZ s hs hs'
  refine ⟨Jac.embedZ mZ hmZ z hz, fun x hx ↦ ?_⟩
  obtain ⟨w, hw, hwr⟩ := Jac.exists_lift_NF mZ hmZ z hz x hx
  refine ⟨w, hw.symm, ?_⟩
  rw [hwr, hzs]; rfl

/-- The certificate coefficient `λ_{i,(i',k)}`. -/
def lamZ (lam : List (List (ZMod p))) (n i i' k : ℕ) : ZMod p :=
  (lam.getD i []).getD (i' * (n - 1) + (k - 1)) 0

/-- **The non-speciality certificate check** over `𝔽_p`. -/
def nsCheckZ (d n g : ℕ) (xs ys : List (ZMod p)) (ζ0 : ZMod p) (lam : List (List (ZMod p))) :
    Bool :=
  (List.range g).all fun i ↦ (basisN n d (n * g)).all fun ai ↦
    decide (xs.getD i 0 ^ ai.1 * ys.getD i 0 ^ ai.2 =
      ∑ i' ∈ Finset.range g, ∑ k ∈ Finset.Ico 1 n, lamZ p lam n i i' k *
        (xs.getD i' 0 ^ ai.1 * (ζ0 ^ k * ys.getD i' 0) ^ ai.2))

variable {p}

lemma nsCheckZ_spec {d n g : ℕ} (hn : 0 < n) {xs ys : List (ZMod p)} {ζ0 : ZMod p}
    {lam : List (List (ZMod p))} (h : nsCheckZ p d n g xs ys ζ0 lam = true) :
    ∀ U : (ZMod p)[X][X], (∀ j a, (U.coeff j).coeff a ≠ 0 → j < n ∧ n * a + d * j ≤ n * g) →
      (∀ i : Fin g, ∀ k, 1 ≤ k → k < n → evalW U (xs.getD i 0) (ζ0 ^ k * ys.getD i 0) = 0) →
      ∀ i : Fin g, evalW U (xs.getD i 0) (ys.getD i 0) = 0 := by
  refine ns_of_cert hn (fun i : Fin g ↦ xs.getD i 0) (fun i ↦ ys.getD i 0) ζ0
    (fun i i' k ↦ lamZ p lam n i i' k) ?_
  intro i ai hai
  simp only [nsCheckZ, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have := h i i.2 ai hai
  rw [this, ← Fin.sum_univ_eq_sum_range (fun i' ↦ ∑ k ∈ Finset.Ico 1 n,
    lamZ p lam n i i' k * (xs.getD i' 0 ^ ai.1 * (ζ0 ^ k * ys.getD i' 0) ^ ai.2))]

variable (p)

/-- **The good-reduction conditions at `p`** for `yⁿ = f(x)` over `K`, a divisor `Γ`, base points
`(xᵢ, yᵢ)` over `𝔽_p`, an `n`-th root of unity `ζ₀` and a non-speciality certificate. -/
abbrev supCheckR {K : Type*} [Field K] [DecidableEq K] (R : RedFns p K) (fK : CPoly K) (n g : ℕ)
    {r : ℕ} (αK βK : Fin r → K) (xs ys : List (ZMod p)) (ζ0 : ZMod p)
    (lam : List (List (ZMod p))) : Prop :=
  2 ≤ n ∧ ((n : ℕ) : ZMod p) ≠ 0 ∧ 0 < fK.length - 1 ∧ (∀ c ∈ fK, R.ok c = true) ∧
    R.red (fK.getD (fK.length - 1) 0) ≠ 0 ∧ (n - 1) * (fK.length - 1 - 1) ≤ 2 * g ∧
    CPoly.squarefreeCheck (fK.map R.red) = true ∧ ζ0 ^ n = 1 ∧
    (∀ l ∈ List.range n, 0 < l → ζ0 ^ l ≠ 1) ∧ xs.length = g ∧ ys.length = g ∧
    (∀ i ∈ List.range g, ys.getD i 0 ^ n = evalC (fK.map R.red) (xs.getD i 0) ∧
      ys.getD i 0 ≠ 0) ∧
    xs.Pairwise (· ≠ ·) ∧
    (∀ q, R.ok (αK q) = true ∧ R.ok (βK q) = true ∧ R.red (βK q) ≠ 0 ∧
      βK q ^ n = evalC fK (αK q) ∧ ∀ x ∈ xs, R.red (αK q) ≠ x) ∧
    (∀ q q', αK q = αK q' ∨ R.red (αK q) ≠ R.red (αK q')) ∧
    (∀ q q', q ≠ q' → αK q = αK q' → R.red (βK q) ≠ R.red (βK q')) ∧
    nsCheckZ p (fK.length - 1) n g xs ys ζ0 lam = true

section Spec

variable {p}

lemma norm_lt_one_iff_toZMod' (w : ℤ_[p]) : ‖w‖ < 1 ↔ PadicInt.toZMod w = 0 :=
  EllDV.norm_lt_one_iff_toZMod w

lemma toZMod_eval (P : ℤ_[p][X]) (w : ℤ_[p]) :
    PadicInt.toZMod (P.eval w) = (P.map PadicInt.toZMod).eval (PadicInt.toZMod w) := by
  rw [eval_map, eval₂_at_apply]

/-- The lift of a residue. -/
noncomputable def liftZ (s : ZMod p) : ℤ_[p] := (s.val : ℤ_[p])

lemma toZMod_liftZ (s : ZMod p) : PadicInt.toZMod (liftZ s) = s := by
  simp [liftZ]

variable {K : Type*} [Field K] [DecidableEq K]

set_option maxHeartbeats 1600000 in
/-- **The good-reduction data behind `supCheckR`.** -/
theorem supCheckR_spec (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ) {fK : CPoly K}
    {n g r : ℕ} {αK βK : Fin r → K}
    {xs ys : List (ZMod p)} {ζ0 : ZMod p} {lam : List (List (ZMod p))}
    (h : supCheckR p R fK n g αK βK xs ys ζ0 lam) :
    ∃ D : SupGoodData p φ (CPoly.toPoly fK) n αK βK,
      D.f.map PadicInt.toZMod = CPoly.toPoly (fK.map R.red) ∧
      (∀ q, PadicInt.toZMod (D.α q) = R.red (αK q)) ∧
      (∀ q, PadicInt.toZMod (D.β q) = R.red (βK q)) := by
  classical
  obtain ⟨hn2, hnp, hd, hok, hlc, hgen, hsq, hζ1, hζl, hxl, hyl, hE, hxd, hΓ, hΓd, hΓβ, hns⟩ := h
  have hn : 0 < n := by omega
  -- lifts of integral elements
  set zOf : K → ℤ_[p] := fun c ↦ if hc : R.ok c = true then Classical.choose (hR c hc) else 0
    with hzOf_def
  have hzOf : ∀ c, R.ok c = true →
      φ c = algebraMap ℤ_[p] ℚ_[p] (zOf c) ∧ PadicInt.toZMod (zOf c) = R.red c := by
    intro c hc
    simp only [hzOf_def, dif_pos hc]
    exact Classical.choose_spec (hR c hc)
  have hunit : ∀ w : ℤ_[p], PadicInt.toZMod w ≠ 0 → IsUnit w := fun w h ↦ Jac.isUnit_of_toZMod h
  -- the integral model of the curve
  set fO : ℤ_[p][X] := CPoly.toPoly (fK.map zOf) with hfO_def
  have hcoef : ∀ m, fO.coeff m = if m < fK.length then zOf (fK.getD m 0) else 0 := by
    intro m
    rw [hfO_def, CPoly.coeff_toPoly]
    split_ifs with hm
    · rw [List.getD_eq_getElem _ _ (by simpa using hm), List.getElem_map,
        List.getD_eq_getElem _ _ hm]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
  have hmem : ∀ m, m < fK.length → fK.getD m 0 ∈ fK := fun m hm ↦ by
    rw [List.getD_eq_getElem _ _ hm]; exact List.getElem_mem hm
  have hfmap : (CPoly.toPoly fK).map φ = fO.map (algebraMap ℤ_[p] ℚ_[p]) := by
    ext m
    rw [coeff_map, coeff_map, hcoef, CPoly.coeff_toPoly]
    split_ifs with hm
    · exact (hzOf _ (hok _ (hmem m hm))).1
    · rw [List.getD_eq_default _ _ (by omega), map_zero, map_zero]
  have hfred : fO.map PadicInt.toZMod = CPoly.toPoly (fK.map R.red) := by
    ext m
    rw [coeff_map, hcoef, CPoly.coeff_toPoly]
    split_ifs with hm
    · rw [(hzOf _ (hok _ (hmem m hm))).2, List.getD_eq_getElem _ _ hm,
        List.getD_eq_getElem _ _ (by simpa using hm), List.getElem_map]
    · rw [map_zero, List.getD_eq_default _ _ (by simp; omega)]
  have hlm : fK.length - 1 < fK.length := by omega
  have hlc0 : PadicInt.toZMod (fO.coeff (fK.length - 1)) ≠ 0 := by
    rw [hcoef, if_pos hlm, (hzOf _ (hok _ (hmem _ hlm))).2]; exact hlc
  have hdeg : fO.natDegree = fK.length - 1 := by
    refine le_antisymm ?_ (le_natDegree_of_ne_zero fun h0 ↦ hlc0 (by rw [h0, map_zero]))
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    have hm' : fK.length - 1 < m := by exact_mod_cast hm
    rw [hcoef, if_neg (by omega)]
  have hlcU : IsUnit fO.leadingCoeff := by
    rw [leadingCoeff, hdeg]; exact hunit _ hlc0
  have heval : ∀ w : ℤ_[p], PadicInt.toZMod (fO.eval w) =
      evalC (fK.map R.red) (PadicInt.toZMod w) := by
    intro w
    rw [toZMod_eval, hfred, CPoly.Kron.evalC_eq]
  have hnu : IsUnit (n : ℤ_[p]) := hunit _ (by rw [map_natCast]; exact hnp)
  -- the root of unity
  have hζ0 : ζ0 ≠ 0 := by
    intro h0; rw [h0, zero_pow hn.ne'] at hζ1; exact zero_ne_one hζ1
  obtain ⟨ζ, hζn, hζu, hζd⟩ := exists_nth_root (p := p) hn hnu 1 (liftZ ζ0)
    (hunit _ (by rw [toZMod_liftZ]; exact hζ0)) (by
      rw [norm_lt_one_iff_toZMod', map_sub, map_pow, toZMod_liftZ, hζ1, map_one, sub_self])
  have hζz : PadicInt.toZMod ζ = ζ0 := by
    rw [toZMod_eq_of_norm_sub_lt hζd, toZMod_liftZ]
  have hζl' : ∀ l, 0 < l → l < n → ζ0 ^ l ≠ 1 := fun l hl hln ↦
    hζl l (List.mem_range.mpr hln) hl
  have hζp : IsPrimitiveRoot ζ n := IsPrimitiveRoot.mk_of_lt ζ hn hζn fun l hl hln he ↦
    hζl' l hl hln (by rw [← hζz, ← map_pow, he, map_one])
  have hζk : IsPrimitiveRoot (IsLocalRing.residue ℤ_[p] ζ) n :=
    IsPrimitiveRoot.mk_of_lt _ hn (by rw [← map_pow, hζn, map_one]) fun l hl hln he ↦
      hζl' l hl hln (by
        rw [← hζz, PadicInt.toZMod_eq_residueField_comp_residue, RingHom.comp_apply, ← map_pow,
          RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, he, map_one])
  -- the base points
  set xp : Fin g → ℤ_[p] := fun i ↦ liftZ (xs.getD i 0) with hxp_def
  have hex : ∀ i : Fin g, ∃ y : ℤ_[p], y ^ n = fO.eval (xp i) ∧ IsUnit y ∧
      ‖y - liftZ (ys.getD i 0)‖ < 1 := by
    intro i
    obtain ⟨hdv, hnu'⟩ := hE i (List.mem_range.mpr i.2)
    exact exists_nth_root hn hnu _ _ (hunit _ (by rw [toZMod_liftZ]; exact hnu')) (by
      rw [norm_lt_one_iff_toZMod', map_sub, map_pow, toZMod_liftZ, heval, hxp_def, toZMod_liftZ,
        hdv, sub_self])
  choose yp hyp hyu hyd using hex
  have hxmem : ∀ i : Fin g, xs.getD i 0 ∈ xs := fun i ↦ by
    have hi : (i : ℕ) < xs.length := by rw [hxl]; exact i.2
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  have hres : ∀ z : ℤ_[p], PadicInt.residueField (IsLocalRing.residue ℤ_[p] z) =
      PadicInt.toZMod z := fun z ↦ rfl
  -- the divisor
  set αO : Fin r → ℤ_[p] := fun q ↦ zOf (αK q) with hαO
  set βO : Fin r → ℤ_[p] := fun q ↦ zOf (βK q) with hβO
  have hαO' : ∀ q, φ (αK q) = algebraMap ℤ_[p] ℚ_[p] (αO q) ∧
      PadicInt.toZMod (αO q) = R.red (αK q) := fun q ↦ hzOf _ (hΓ q).1
  have hβO' : ∀ q, φ (βK q) = algebraMap ℤ_[p] ℚ_[p] (βO q) ∧
      PadicInt.toZMod (βO q) = R.red (βK q) := fun q ↦ hzOf _ (hΓ q).2.1
  have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := IsFractionRing.injective ℤ_[p] ℚ_[p]
  refine ⟨{
    f := fO
    hlc := hlcU
    hfmap := hfmap
    hsqk := by
      have hsq' := CPoly.squarefreeCheck_sound hsq
      have e1 : fO.map (IsLocalRing.residue ℤ_[p]) =
          (fO.map PadicInt.toZMod).map PadicInt.residueField.symm.toRingHom := by
        rw [Polynomial.map_map]; congr 1
        ext z
        simp [PadicInt.toZMod_eq_residueField_comp_residue]
      rw [e1, hfred]
      exact ((PerfectField.separable_iff_squarefree.mpr hsq').map).squarefree
    hnu := hnu
    ζ := ζ
    hζ := hζp
    hζk := hζk
    g := g
    hgen := by rw [hdeg]; exact hgen
    x := xp
    y := yp
    hyu := hyu
    hyf := hyp
    hx := by
      intro i j hij
      refine hunit _ ?_
      rw [map_sub, hxp_def, toZMod_liftZ, toZMod_liftZ, sub_ne_zero]
      have hi : (i : ℕ) < xs.length := by rw [hxl]; exact i.2
      have hj : (j : ℕ) < xs.length := by rw [hxl]; exact j.2
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
      · exact List.pairwise_iff_getElem.mp hxd _ _ hi hj hlt
      · exact (List.pairwise_iff_getElem.mp hxd _ _ hj hi hlt).symm
    α := αO
    β := βO
    hαmap := fun q ↦ (hαO' q).1
    hβmap := fun q ↦ (hβO' q).1
    hβu := fun q ↦ hunit _ (by rw [(hβO' q).2]; exact (hΓ q).2.2.1)
    hβf := fun q ↦ by
      apply hinj
      rw [map_pow, ← (hβO' q).1, ← map_pow, (hΓ q).2.2.2.1, CPoly.Kron.evalC_eq,
        ← eval_map_apply, hfmap, eval_map_algebraMap, (hαO' q).1]
      rw [aeval_algebraMap_apply]
      rfl
    hα := fun q q' ↦ (hΓd q q').imp (fun h ↦ by simp only [hαO, h]) fun h ↦ hunit _ (by
      rw [map_sub, (hαO' q).2, (hαO' q').2]; exact sub_ne_zero.mpr h)
    hβd := fun q q' hqq hαe ↦ hunit _ (by
      have hαK : αK q = αK q' := by
        by_contra hne
        rcases hΓd q q' with h' | h'
        · exact hne h'
        · exact h' (by rw [← (hαO' q).2, ← (hαO' q').2, hαe])
      rw [map_sub, (hβO' q).2, (hβO' q').2]; exact sub_ne_zero.mpr (hΓβ q q' hqq hαK))
    hαx := fun q i ↦ hunit _ (by
      rw [map_sub, (hαO' q).2, hxp_def, toZMod_liftZ]
      exact sub_ne_zero.mpr ((hΓ q).2.2.2.2 _ (hxmem i)))
    hNS := by
      intro U hU hUv i
      set V := U.map (mapRingHom PadicInt.residueField.toRingHom) with hV_def
      have hVs : ∀ j a, (V.coeff j).coeff a ≠ 0 → j < n ∧
          n * a + (fK.length - 1) * j ≤ n * g := by
        intro j a hja
        rw [← hdeg]
        refine hU j a fun h0 ↦ hja ?_
        simp [V, h0]
      have hx' : ∀ i, PadicInt.residueField (IsLocalRing.residue ℤ_[p] (xp i)) =
          xs.getD i 0 := fun i ↦ by rw [hres, hxp_def, toZMod_liftZ]
      have hy' : ∀ i, PadicInt.residueField (IsLocalRing.residue ℤ_[p] (yp i)) =
          ys.getD i 0 := fun i ↦ by
        rw [hres, toZMod_eq_of_norm_sub_lt (hyd i), toZMod_liftZ]
      have hζ' : PadicInt.residueField (IsLocalRing.residue ℤ_[p] ζ) = ζ0 := by
        rw [hres, hζz]
      have key := nsCheckZ_spec hn hns V hVs (fun i k hk1 hk ↦ by
        rw [← hx', ← hy', ← hζ', ← map_pow, ← map_mul]
        exact (evalW_map PadicInt.residueField.toRingHom U _ _).trans
          (by rw [hUv i k hk1 hk, map_zero])) i
      rw [← hx', ← hy'] at key
      have h2 : PadicInt.residueField.toRingHom (evalW U (IsLocalRing.residue ℤ_[p] (xp i))
          (IsLocalRing.residue ℤ_[p] (yp i))) = 0 :=
        (evalW_map PadicInt.residueField.toRingHom U _ _).symm.trans key
      exact (map_eq_zero_iff _ PadicInt.residueField.injective).mp h2 },
    hfred, fun q ↦ (hαO' q).2, fun q ↦ (hβO' q).2⟩

end Spec

end Sup
