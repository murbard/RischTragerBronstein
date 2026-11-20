import RischTragerBronstein.Computable.NestXLimP

/-!
# Mixed towers: parametric elementary integration over a logarithmic level

At a level `m + 1` with `ks m = .prim η` every weight is Hermite-reduced,
`wᵢ = gᵢ′ + Pᵢ + Nᵢ / S` over a common squarefree denominator `S`; the logarithmic part forces the
residue test `S ∣ T(∑ cᵢ Rᵢ, S)` (a constant system at level `m + 1`) and the polynomial part is
the parametric elementary polynomial problem (`polyElem`), whose degree-`0` equation is solved one
level down. `primElemStep_spec`: the step is sound and complete (`ElemSolSpec`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP Tower.NestX

section Data

variable (ks : (m : ℕ) → KindN m) (m : ℕ)

/-- The common denominator `S` of the simple parts. -/
def lcmSP (W : List (Code (m + 2))) : GPoly (Code (m + 1)) :=
  lcmList (opsM ks m) ((W.map (hermWP ks m)).map fun h ↦ h.s)

/-- The numerators `Nᵢ` of the simple parts over `S`. -/
def numLP (W : List (Code (m + 2))) : List (GPoly (Code (m + 1))) :=
  (List.zip ((W.map (hermWP ks m)).map fun h ↦ GPoly.divMod (opsM ks m) h.b h.s)
    (W.map (hermWP ks m))).map fun p ↦
      GPoly.mul (opsM ks m) p.1.2 (GPoly.divMod (opsM ks m) (lcmSP ks m W) p.2.s).1

/-- The residue test polynomial of `Nᵢ / S`, reduced modulo `S`. -/
def ttCodeP (W : List (Code (m + 2))) (Ni : GPoly (Code (m + 1))) : GPoly (Code (m + 1)) :=
  (GPoly.divMod (opsM ks m) (residueTestCode (opsM ks m)
    (GPoly.residuePoly (opsM ks m) (wK (opsM ks m) (ks m)) Ni (lcmSP ks m W)) (lcmSP ks m W))
    (lcmSP ks m W)).2

/-- The residue test polynomials, as codes of level `m + 1`. -/
def resCodesP (W : List (Code (m + 2))) : List (Code (m + 2)) :=
  ((numLP ks m W).map (ttCodeP ks m W)).map fun T ↦ ((T, [(opsM ks m).one]) : Code (m + 2))

/-- The basis of the solutions of the residue condition. -/
def E1P (W : List (Code (m + 2))) : List (List ℚ) :=
  (consys ks (m + 1) (resCodesP ks m W)).map (NestTower.vecOf W.length)

/-- The check that `S` is a squarefree common multiple. -/
def lcmCheckP (W : List (Code (m + 2))) : Bool :=
  GPoly.squarefreeCheck (opsM ks m) (lcmSP ks m W) &&
    (W.map (hermWP ks m)).all
      (fun h ↦ GPoly.isZero (opsM ks m) (GPoly.divMod (opsM ks m) (lcmSP ks m W) h.s).2)

/-- The polynomial parts of the reduced parametric problem. -/
def PuEP (W : List (Code (m + 2))) : List (GPoly (Code (m + 1))) :=
  (E1P ks m W).map fun e ↦ lcombGP (opsM ks m) (cstN m) e
    (((W.map (hermWP ks m)).map fun h ↦ GPoly.divMod (opsM ks m) h.b h.s).map Prod.fst)

lemma primElemStep_eq (η : Code (m + 1)) (lim : List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (elem : List (Code (m + 1)) → List (List ℚ)) (W : List (Code (m + 2))) :
    primElemStep ks m η lim elem W =
      if lcmCheckP ks m W then
        (polyElem (opsM ks m) (cstN m) η lim elem (PuEP ks m W)).map fun δ ↦
          vcomb W.length δ (E1P ks m W)
      else [] := rfl

lemma length_numLP (W : List (Code (m + 2))) : (numLP ks m W).length = W.length :=
  NestTower.len_zip_map _ _ _ W

lemma getD_numLP (W : List (Code (m + 2))) {i : ℕ} (hi : i < W.length) :
    (numLP ks m W).getD i [] = GPoly.mul (opsM ks m)
      (GPoly.divMod (opsM ks m) (hermWP ks m (W.getD i (zP ks m))).b
        (hermWP ks m (W.getD i (zP ks m))).s).2
      (GPoly.divMod (opsM ks m) (lcmSP ks m W) (hermWP ks m (W.getD i (zP ks m))).s).1 :=
  NestTower.getD_zip_map _ _ _ W (zP ks m) [] hi

lemma length_resCodesP (W : List (Code (m + 2))) : (resCodesP ks m W).length = W.length := by
  unfold resCodesP
  exact (List.length_map _).trans ((List.length_map _).trans (length_numLP ks m W))

lemma getD_resCodesP (W : List (Code (m + 2))) {i : ℕ} (hi : i < W.length) :
    (resCodesP ks m W).getD i (zP ks m) =
      ((ttCodeP ks m W ((numLP ks m W).getD i []), [(opsM ks m).one]) : Code (m + 2)) :=
  NestTower.getD_map_map _ _ _ [] _ (by rw [length_numLP]; exact hi)

lemma length_E1P (W : List (Code (m + 2))) :
    (E1P ks m W).length = (consys ks (m + 1) (resCodesP ks m W)).length := by
  simp [E1P]

end Data

namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : (m : ℕ) → KindN m}
variable (T : NestMTower Kc E ks)

lemma const_memP (m : ℕ) (z : E) (hz : z′ = 0) : z ∈ T.F m := by
  obtain ⟨κ, rfl⟩ := T.hCall z hz
  exact (T.F m).algebraMap_mem κ

section Step

variable (m : ℕ) (h : T.Tr (m + 1)) {η : Code (m + 1)} (hk : ks m = .prim η)

include hk in
/-- **The common denominator**: squarefree, and every weight is `gᵢ′ + Pᵢ + Nᵢ / S`. -/
lemma lcm_dataP (W : List (Code (m + 2))) (hchk : lcmCheckP ks m W = true) :
    Squarefree (GPoly.toPoly (T.MX m h) (lcmSP ks m W)) ∧
    ∀ i < W.length, (T.MP (m + 1) h).sem (W.getD i (zP ks m)) =
      ((T.MP (m + 1) h).sem (gCodeP ks m (W.getD i (zP ks m))))′ +
      T.phi m (GPoly.toPoly (T.MX m h) (pPartP ks m (W.getD i (zP ks m)))) +
      T.phi m (GPoly.toPoly (T.MX m h) ((numLP ks m W).getD i [])) /
        T.phi m (GPoly.toPoly (T.MX m h) (lcmSP ks m W)) ∧
      (GPoly.toPoly (T.MX m h) ((numLP ks m W).getD i [])).degree <
        (GPoly.toPoly (T.MX m h) (lcmSP ks m W)).degree := by
  set M := T.MX m h with hM
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hinj := T.phi_injective htr
  simp only [lcmCheckP, Bool.and_eq_true] at hchk
  obtain ⟨hsqc, hall⟩ := hchk
  have hsq : Squarefree (GPoly.toPoly M (lcmSP ks m W)) := GPoly.squarefreeCheck_sound M hsqc
  refine ⟨hsq, fun i hi ↦ ?_⟩
  set w := W.getD i (zP ks m) with hw
  obtain ⟨hval, hsqs, hdeg⟩ := T.weight_decompP m h hk w
  have hz := List.all_eq_true.mp hall (hermWP ks m w)
    (List.mem_map.mpr ⟨w, NestTower.getD_mem_of_lt W _ hi, rfl⟩)
  have hr0 := (GPoly.isZero_iff M _).mp hz
  have hdm := GPoly.divMod_spec M (lcmSP ks m W) (hermWP ks m w).s
  rw [hr0, add_zero] at hdm
  set d := GPoly.toPoly M (GPoly.divMod (opsM ks m) (lcmSP ks m W) (hermWP ks m w).s).1 with hd
  set sv := GPoly.toPoly M (hermWP ks m w).s with hsv
  set rv := GPoly.toPoly M
    (GPoly.divMod (opsM ks m) (hermWP ks m w).b (hermWP ks m w).s).2 with hrv
  have hd0 : d ≠ 0 := fun h0 ↦ hsq.ne_zero (by rw [hdm, h0, zero_mul])
  have hN : GPoly.toPoly M ((numLP ks m W).getD i []) = rv * d := by
    rw [getD_numLP ks m W hi, GPoly.toPoly_mul]
  refine ⟨?_, ?_⟩
  · rw [hval, hN, hdm]
    have hφd : T.phi m d ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd0
    have hφs : T.phi m sv ≠ 0 := (map_ne_zero_iff _ hinj).mpr hsqs.ne_zero
    simp only [map_mul]
    field_simp
    ring
  · rw [hN, hdm, degree_mul, degree_mul, add_comm]
    exact WithBot.add_lt_add_left (degree_ne_bot.mpr hd0) hdeg

include hk in
/-- **The residue data**: the residue polynomial of `Nᵢ / S` and its reduced test polynomial. -/
lemma res_dataP (W : List (Code (m + 2)))
    (hS : Squarefree (GPoly.toPoly (T.MX m h) (lcmSP ks m W))) (Ni : GPoly (Code (m + 1))) :
    GPoly.toPoly (T.MX m h) (lcmSP ks m W) ∣
      GPoly.toPoly (T.MX m h)
        (GPoly.residuePoly (opsM ks m) (wK (opsM ks m) (ks m)) Ni (lcmSP ks m W)) *
        (mapCoeffs (GPoly.toPoly (T.MX m h) (lcmSP ks m W)) +
          C (T.ηX m h η) * derivative (GPoly.toPoly (T.MX m h) (lcmSP ks m W))) -
        GPoly.toPoly (T.MX m h) Ni ∧
    GPoly.toPoly (T.MX m h) (lcmSP ks m W) ∣
      residueTest (GPoly.toPoly (T.MX m h)
        (GPoly.residuePoly (opsM ks m) (wK (opsM ks m) (ks m)) Ni (lcmSP ks m W)))
        (GPoly.toPoly (T.MX m h) (lcmSP ks m W)) -
        GPoly.toPoly (T.MX m h) (ttCodeP ks m W Ni) ∧
    (GPoly.toPoly (T.MX m h) (ttCodeP ks m W Ni)).degree <
      (GPoly.toPoly (T.MX m h) (lcmSP ks m W)).degree := by
  set M := T.MX m h with hM
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M (wK (opsM ks m) (ks m)))
      (GPoly.toPoly M (lcmSP ks m W))) (GPoly.toPoly M (lcmSP ks m W)) := by
    rw [T.toPoly_wKX m h]
    let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
    exact isCoprime_deriv_of_squarefree hS (fun p hp _ ↦ T.normal_prim m htr hk p hp)
  have hrs := GPoly.residuePoly_spec M (wK (opsM ks m) (ks m)) Ni _ hS.ne_zero hcop
  rw [T.toPoly_wK_prim m h hk, PrimN.PrimTower.implicitDeriv_C_eq] at hrs
  refine ⟨by simpa using hrs, ?_, GPoly.divMod_degree_lt M _ _ hS.ne_zero⟩
  have hdm := GPoly.divMod_spec M (residueTestCode (opsM ks m)
    (GPoly.residuePoly (opsM ks m) (wK (opsM ks m) (ks m)) Ni (lcmSP ks m W)) (lcmSP ks m W))
    (lcmSP ks m W)
  rw [NestTower.toPoly_residueTestCode] at hdm
  rw [ttCodeP, hdm]
  exact ⟨_, by ring⟩

/-- The relation given by a basis vector of the residue system. -/
lemma rel_resP (W : List (Code (m + 2))) (u : CPoly ℚ)
    (hu : u ∈ consys ks (m + 1) (resCodesP ks m W)) :
    ∑ i ∈ Finset.range W.length, C ((u.getD i 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.MX m h) (ttCodeP ks m W ((numLP ks m W).getD i [])) = 0 := by
  have := T.consys_sound (m + 1) h (resCodesP ks m W) u hu
  rw [NestTower.zipWith_sum_range _ 0 (zP ks m) _ _ (by simp)] at this
  apply T.phi_injX m h
  rw [map_zero, ← this, map_sum]
  refine Finset.sum_congr (by rw [List.length_map, List.length_range, length_resCodesP])
    fun i hi ↦ ?_
  have hi' : i < W.length := by
    have := Finset.mem_range.mp hi
    rwa [List.length_map, List.length_range, length_resCodesP] at this
  rw [NestTower.getD_range_map (fun j ↦ algebraMap ℚ Kc (u.getD j 0)) 0
    (by rw [length_resCodesP]; exact hi'), T.algebraMap_ratX, getD_resCodesP ks m W hi',
    map_mul, T.phi_C_ratX]
  congr 1
  exact (T.semX_poly m h _).symm

/-- The polynomial parts, recombined. -/
lemma sum_pv_eqP (W : List (Code (m + 2))) (δ : List ℚ) :
    ∑ i ∈ Finset.range W.length, C (((vcomb W.length δ (E1P ks m W)).getD i 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.MX m h) (pPartP ks m (W.getD i (zP ks m))) =
    polySumQ (T.MX m h) δ (PuEP ks m W) := by
  rw [polySumQ]
  have hl : (PuEP ks m W).length = (E1P ks m W).length := by simp [PuEP]
  have e : ∀ k ∈ Finset.range (PuEP ks m W).length, C ((δ.getD k 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.MX m h) ((PuEP ks m W).getD k []) = ∑ i ∈ Finset.range W.length,
        C (((δ.getD k 0 * ((E1P ks m W).getD k []).getD i 0 : ℚ)) : T.F m) *
          GPoly.toPoly (T.MX m h) (pPartP ks m (W.getD i (zP ks m))) := fun k hk ↦ by
    have hk' : k < (E1P ks m W).length := by rw [← hl]; exact Finset.mem_range.mp hk
    rw [PuEP, NestTower.getD_map' _ _ [] [] hk', T.toPoly_PuP m h W, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    push_cast
    rw [C_mul]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm, hl]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [getD_vcomb, if_pos (Finset.mem_range.mp hi), ← Finset.sum_mul]
  push_cast
  rw [map_sum]

/-- The test polynomials, recombined, vanish. -/
lemma sum_Tv_eq_zeroP (W : List (Code (m + 2))) (δ : List ℚ) :
    ∑ i ∈ Finset.range W.length, C (((vcomb W.length δ (E1P ks m W)).getD i 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.MX m h) (ttCodeP ks m W ((numLP ks m W).getD i [])) = 0 := by
  set U := consys ks (m + 1) (resCodesP ks m W) with hU
  have e : ∀ i ∈ Finset.range W.length,
      C (((vcomb W.length δ (E1P ks m W)).getD i 0 : ℚ) : T.F m) *
        GPoly.toPoly (T.MX m h) (ttCodeP ks m W ((numLP ks m W).getD i [])) =
      ∑ k ∈ Finset.range U.length, C ((δ.getD k 0 : ℚ) : T.F m) *
        (C (((U.getD k []).getD i 0 : ℚ) : T.F m) *
          GPoly.toPoly (T.MX m h) (ttCodeP ks m W ((numLP ks m W).getD i []))) :=
    fun i hi ↦ by
      have hi' := Finset.mem_range.mp hi
      rw [getD_vcomb, if_pos hi', length_E1P, ← hU]
      push_cast
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [E1P, ← hU, NestTower.getD_map' _ U [] [] (Finset.mem_range.mp hk),
        NestTower.getD_vecOf, if_pos hi', C_mul]
      ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  rw [← Finset.mul_sum, T.rel_resP m h W _
    (NestTower.getD_mem_of_lt U [] (Finset.mem_range.mp hk)), mul_zero]

include T h hk in
/-- **The lcm check always passes** (given transcendence). -/
lemma lcmCheck_trueP (W : List (Code (m + 2))) : lcmCheckP ks m W = true := by
  set M := T.MX m h with hM
  have hs : ∀ p ∈ (W.map (hermWP ks m)).map (fun h ↦ h.s),
      GPoly.toPoly M p ≠ 0 ∧ Squarefree (GPoly.toPoly M p) := by
    intro p hp
    obtain ⟨hr, hrm, rfl⟩ := List.mem_map.mp hp
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hrm
    have := (T.weight_decompP m h hk w).2.1
    exact ⟨this.ne_zero, this⟩
  obtain ⟨hdvd, -, hsqf⟩ := GPolyLcm.lcmList_spec M _ (fun p hp ↦ (hs p hp).1)
  simp only [lcmCheckP, Bool.and_eq_true]
  refine ⟨GPoly.squarefreeCheck_complete M (hsqf fun p hp ↦ (hs p hp).2),
    List.all_eq_true.mpr fun hr hrm ↦ ?_⟩
  refine (GPoly.isZero_iff M _).mpr (GPoly.divMod_exact M _ _ ?_
    (hdvd _ (List.mem_map.mpr ⟨hr, hrm, rfl⟩)))
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hrm
  exact (T.weight_decompP m h hk w).2.1.ne_zero

include hk in
set_option maxHeartbeats 1600000 in
/-- **Soundness of the logarithmic step.** -/
theorem primElemStep_sound (lim : List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (hlim : LimSpec (algebraMap Kc (T.F m)) (T.MX m h) lim)
    (elem : List (Code (m + 1)) → List (List ℚ))
    (hel : ElemSolSpec (algebraMap Kc (T.F m)) (T.MX m h) (fun v ↦ HasElementaryIntegralIn (v : E))
      (fun v ↦ LiouvilleIn (T.F m) (v : E)) elem) (W : List (Code (m + 2))) :
    ∀ β ∈ primElemStep ks m η lim elem W,
      HasElementaryIntegralIn ((sQ (T.MP (m + 1) h) β W : T.F (m + 1)) : E) := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
  set M := T.MX m h with hM
  set M' := T.MP (m + 1) h with hM'
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hinj := T.phi_injective htr
  have hconstK : ∀ y : T.F m, y′ = 0 → ∃ κ : Kc, y = algebraMap Kc (T.F m) κ := fun y hy ↦
    T.const_F y hy
  intro v hv
  rw [primElemStep_eq] at hv
  split_ifs at hv with hchk
  swap
  · simp at hv
  obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hv
  obtain ⟨hsq, hdat⟩ := T.lcm_dataP m h hk W hchk
  set n := W.length with hn
  set Sv := GPoly.toPoly M (lcmSP ks m W) with hSv
  set vq : ℕ → ℚ := fun i ↦ (vcomb n δ (E1P ks m W)).getD i 0 with hvq
  set Nq := ∑ i ∈ Finset.range n, C ((vq i : ℚ) : T.F m) *
    GPoly.toPoly M ((numLP ks m W).getD i []) with hNq
  set Rq := ∑ i ∈ Finset.range n, C ((vq i : ℚ) : T.F m) *
    GPoly.toPoly M (GPoly.residuePoly (opsM ks m) (wK (opsM ks m) (ks m))
      ((numLP ks m W).getD i []) (lcmSP ks m W)) with hRq
  set G := ∑ i ∈ Finset.range n, ((vq i : ℚ) : T.F (m + 1)) *
    M'.sem (gCodeP ks m (W.getD i (zP ks m))) with hG
  -- the polynomial part
  obtain ⟨Q, b, hQb, hb⟩ := polyElem_sound (algebraMap Kc (T.F m)) η lim elem
    (T.sem_cstX m h) hlim hconstK (fun q ↦ T.algebraMap_ratX q)
    (fun b ↦ HasElementaryIntegralIn ((b : T.F m) : E)) (fun ws β hβ ↦ hel.sound ws β hβ)
    (PuEP ks m W) δ hδ
  have hP : ∑ i ∈ Finset.range n, C ((vq i : ℚ) : T.F m) *
      GPoly.toPoly M (pPartP ks m (W.getD i (zP ks m))) = Dη M η Q + C b := by
    rw [← hQb]
    exact T.sum_pv_eqP m h W δ
  -- the value
  have hA : sQ M' (vcomb n δ (E1P ks m W)) W =
      (G + T.phi m Q)′ + T.phi m (C b) + T.phi m Nq / T.phi m Sv := by
    have hφS : T.phi m Sv ≠ 0 := (map_ne_zero_iff _ hinj).mpr hsq.ne_zero
    have hDQ : T.phi m (Dη M η Q) = (T.phi m Q)′ := by
      rw [T.deriv_phi_primX m h hk]
    rw [map_add, ← hDQ, add_assoc (G′), ← map_add (T.phi m), ← hP, hG, T.deriv_sum_ratCastP,
      map_sum, hNq, map_sum, Finset.sum_div, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, sQ]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [(hdat i (Finset.mem_range.mp hi)).1, map_mul, map_mul, T.phi_C_ratX]
    simp only [hvq, hM, hM']
    ring
  -- the logarithmic part
  have hlog : HasElementaryIntegralIn (aeval (T.ts m) Nq / aeval (T.ts m) Sv) := by
    have hst : aeval (T.ts m) Sv ≠ 0 := by
      rw [← T.coe_phi]
      exact fun h0 ↦ hsq.ne_zero (hinj ((Subtype.ext h0).trans (map_zero _).symm))
    have hdeg : Nq.degree < Sv.degree :=
      NestTower.degree_sum_C_mul_lt n _ _ Sv hsq.ne_zero fun i hi ↦ (hdat i hi).2
    have hr : Sv ∣ Rq * (mapCoeffs Sv + (C (T.ηX m h η) + C 0 * X) * derivative Sv) - Nq := by
      rw [C_0, zero_mul, add_zero, hRq, hNq, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.dvd_sum fun i _ ↦ ?_
      have := (T.res_dataP m h hk W hsq ((numLP ks m W).getD i [])).1
      rw [show ∀ a b c d : (T.F m)[X], a * b * c - a * d = a * (b * c - d) from
        fun _ _ _ _ ↦ by ring]
      exact dvd_mul_of_dvd_right this _
    have hT : Sv ∣ residueTest Rq Sv := by
      rw [hRq, residueTest_sum n _ (fun i ↦ T.deriv_ratCast _)]
      have h0 := T.sum_Tv_eq_zeroP m h W δ
      rw [← sub_zero (∑ i ∈ Finset.range n, _), ← h0, ← Finset.sum_sub_distrib]
      refine Finset.dvd_sum fun i _ ↦ ?_
      rw [← mul_sub]
      exact dvd_mul_of_dvd_right (T.res_dataP m h hk W hsq _).2.1 _
    exact hasElementaryIntegralIn_of_residueTest (F := T.F m) (T.ts m) (T.ηX m h η) 0
      (by rw [map_zero, zero_mul, add_zero]; exact T.deriv_ts_primX m h hk) 1 one_ne_zero
      (by rw [logDeriv_one, map_zero]) Sv Nq Rq (PerfectField.separable_iff_squarefree.mpr hsq)
      hst hdeg hr hT
  have hAE : ((sQ M' (vcomb n δ (E1P ks m W)) W : T.F (m + 1)) : E) =
      ((G + T.phi m Q : T.F (m + 1)) : E)′ + ((b : T.F m) : E) +
        aeval (T.ts m) Nq / aeval (T.ts m) Sv := by
    rw [hA, IntermediateField.coe_add, IntermediateField.coe_add, IntermediateField.coe_div,
      coe_deriv, T.coe_phi, T.coe_phi, T.coe_phi, aeval_C]
    rfl
  rw [hAE]
  exact ((hasElementaryIntegralIn_deriv _).add hb).add hlog

include hk in
set_option maxHeartbeats 3200000 in
/-- **Parametric elementary integration over a logarithmic level is sound and complete.** -/
theorem primElemStep_spec (hnd : ∀ y : T.F m, y′ ≠ T.ηX m h η)
    (lim : List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (hlim : LimSpec (algebraMap Kc (T.F m)) (T.MX m h) lim)
    (elem : List (Code (m + 1)) → List (List ℚ))
    (hel : ElemSolSpec (algebraMap Kc (T.F m)) (T.MX m h) (fun v ↦ HasElementaryIntegralIn (v : E))
      (fun v ↦ LiouvilleIn (T.F m) (v : E)) elem) :
    ElemSolSpec (algebraMap Kc (T.F (m + 1))) (T.MP (m + 1) h)
      (fun v ↦ HasElementaryIntegralIn (v : E)) (fun v ↦ LiouvilleIn (T.F (m + 1)) (v : E))
      (primElemStep ks m η lim elem) := by
  classical
  refine ⟨fun W β hβ ↦ T.primElemStep_sound m h hk lim hlim elem hel W β hβ,
    fun W c hc hL ↦ ?_⟩
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
  set M := T.MX m h with hM
  set M' := T.MP (m + 1) h with hM'
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hinj := T.phi_injective htr
  have hconstK : ∀ y : T.F m, y′ = 0 → ∃ κ : Kc, y = algebraMap Kc (T.F m) κ := fun y hy ↦
    T.const_F y hy
  have hchk := T.lcmCheck_trueP m h hk W
  rw [primElemStep_eq, if_pos hchk]
  obtain ⟨hsq, hdat⟩ := T.lcm_dataP m h hk W hchk
  set n := W.length with hn
  set Sv := GPoly.toPoly M (lcmSP ks m W) with hSv
  set ac : ℕ → T.F m := fun i ↦ algebraMap Kc (T.F m) (c.getD i 0) with hac
  have hac' : ∀ i, (ac i)′ = 0 := fun i ↦ T.deriv_algebraMap_Kc _
  set pv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly M (pPartP ks m (W.getD i (zP ks m))) with hpv
  set Nv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly M ((numLP ks m W).getD i []) with hNv
  set Rv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly M (GPoly.residuePoly (opsM ks m)
    (wK (opsM ks m) (ks m)) ((numLP ks m W).getD i []) (lcmSP ks m W)) with hRv
  set Tv : ℕ → (T.F m)[X] := fun i ↦
    GPoly.toPoly M (ttCodeP ks m W ((numLP ks m W).getD i [])) with hTv
  set A := ∑ i ∈ Finset.range n, C (ac i) * pv i with hA
  set Nc := ∑ i ∈ Finset.range n, C (ac i) * Nv i with hNc
  set Rc := ∑ i ∈ Finset.range n, C (ac i) * Rv i with hRc
  set G : T.F (m + 1) := ∑ i ∈ Finset.range n, algebraMap Kc (T.F (m + 1)) (c.getD i 0) *
    M'.sem (gCodeP ks m (W.getD i (zP ks m))) with hG
  have hφS : T.phi m Sv ≠ 0 := (map_ne_zero_iff _ hinj).mpr hsq.ne_zero
  -- the value
  have hsum : sC (algebraMap Kc (T.F (m + 1))) M' c W =
      G′ + T.phi m A + T.phi m Nc / T.phi m Sv := by
    rw [hG, T.deriv_sum_KcP, hA, hNc, map_sum, map_sum, Finset.sum_div, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, sC]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [(hdat i (Finset.mem_range.mp hi)).1, map_mul, map_mul, T.algebraMap_succ]
    simp only [hac, hM, hM', hpv, hNv]
    ring
  obtain ⟨ι, s, cc, u, v, hdata, hv, heq⟩ := hL
  set t := T.ts m with ht
  set ηv := T.ηX m h η with hηdef
  have htd : t′ = algebraMap (T.F m) E ηv := T.deriv_ts_primX m h hk
  have hw : t′ = aeval t (C ηv) := by rw [aeval_C]; exact htd
  have hst : aeval t Sv ≠ 0 := by
    rw [ht, ← T.coe_phi]
    exact fun h0 ↦ hφS (Subtype.ext h0)
  have hval : ((sC (algebraMap Kc (T.F (m + 1))) M' c W : T.F (m + 1)) : E) =
      (G : E)′ + aeval t A + aeval t Nc / aeval t Sv := by
    rw [hsum, IntermediateField.coe_add, IntermediateField.coe_add, IntermediateField.coe_div,
      coe_deriv, T.coe_phi, T.coe_phi, T.coe_phi]
  -- the constants as elements of `F m`
  set c' : ι → T.F m := fun i ↦ if h : (cc i)′ = 0 then ⟨cc i, T.const_memP m _ h⟩ else 0
    with hc'
  have hc'E : ∀ i ∈ s, ((c' i : T.F m) : E) = cc i := fun i hi ↦ by
    simp only [hc']
    rw [dif_pos (hdata i hi).1]
  have hc'd : ∀ i ∈ s, (c' i)′ = 0 := fun i hi ↦
    Subtype.ext (by rw [coe_deriv, hc'E i hi, (hdata i hi).1]; rfl)
  have hconst : ∀ z ∈ (T.F m)⟮t⟯, z′ = 0 → z ∈ Set.range (algebraMap (T.F m) E) :=
    fun z _ hz0 ↦ by
      obtain ⟨κ, rfl⟩ := T.hCall z hz0
      exact ⟨algebraMap Kc (T.F m) κ, rfl⟩
  have hvg : v - (G : E) ∈ (T.F m)⟮t⟯ := (T.mem_F_succ).mp (sub_mem hv G.2)
  have hsumc : ∑ i ∈ s, cc i * logDeriv (u i) =
      ∑ i ∈ s, algebraMap (T.F m) E (c' i) * logDeriv (u i) :=
    Finset.sum_congr rfl fun i hi ↦ by rw [← hc'E i hi]; rfl
  have hbv : aeval t (A * Sv + Nc) / aeval t Sv =
      ∑ i ∈ s, algebraMap (T.F m) E (c' i) * logDeriv (u i) + (v - (G : E))′ := by
    rw [← hsumc, map_sub, ← add_sub_assoc, ← heq, hval, map_add, map_mul]
    field_simp
    ring
  -- the residue condition
  have hr : Sv ∣ Rc * (mapCoeffs Sv + C ηv * derivative Sv) - (A * Sv + Nc) := by
    have e : Rc * (mapCoeffs Sv + C ηv * derivative Sv) - (A * Sv + Nc) =
        ∑ i ∈ Finset.range n, C (ac i) * (Rv i * (mapCoeffs Sv + C ηv * derivative Sv) - Nv i) -
          A * Sv := by
      have e2 : ∑ i ∈ Finset.range n,
          C (ac i) * (Rv i * (mapCoeffs Sv + C ηv * derivative Sv) - Nv i) =
          Rc * (mapCoeffs Sv + C ηv * derivative Sv) - Nc := by
        rw [hRc, hNc, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [e2]
      ring
    rw [e]
    refine dvd_sub (Finset.dvd_sum fun i _ ↦ dvd_mul_of_dvd_right ?_ _) (dvd_mul_left _ _)
    exact (T.res_dataP m h hk W hsq ((numLP ks m W).getD i [])).1
  have hT : Sv ∣ residueTest Rc Sv :=
    residueTest_step_primitive (F := T.F m) t htr ηv htd hconst s c' u
      (fun i hi ↦ ⟨(T.mem_F_succ).mp (hdata i hi).2.1, (hdata i hi).2.2⟩) hc'd (v - (G : E))
      hvg _ _ _ hsq hr hbv
  have hT0 : ∑ i ∈ Finset.range n, C (ac i) * Tv i = 0 := by
    refine eq_zero_of_dvd_of_degree_lt ?_
      (NestTower.degree_sum_C_mul_lt n _ _ Sv hsq.ne_zero fun i _ ↦
        (T.res_dataP m h hk W hsq _).2.2)
    have e : ∑ i ∈ Finset.range n, C (ac i) * Tv i = residueTest Rc Sv -
        ∑ i ∈ Finset.range n, C (ac i) * (residueTest (Rv i) Sv - Tv i) := by
      rw [hRc, residueTest_sum n ac hac', ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [e]
    exact dvd_sub hT (Finset.dvd_sum fun i _ ↦
      dvd_mul_of_dvd_right (T.res_dataP m h hk W hsq _).2.1 _)
  -- the constant system at level `m + 1`
  set U := consys ks (m + 1) (resCodesP ks m W) with hU
  have h0 : (List.zipWith (fun c v ↦ algebraMap Kc (T.F (m + 1)) c * M'.sem v)
      ((List.range (resCodesP ks m W).length).map fun i ↦ c.getD i 0)
      (resCodesP ks m W)).sum = 0 := by
    rw [NestTower.zipWith_sum_range _ 0 (zP ks m) _ _ (by simp)]
    have e : ∀ i ∈ Finset.range ((List.range (resCodesP ks m W).length).map
        fun i ↦ c.getD i 0).length,
        algebraMap Kc (T.F (m + 1)) (((List.range (resCodesP ks m W).length).map
          fun i ↦ c.getD i 0).getD i 0) * M'.sem ((resCodesP ks m W).getD i (zP ks m)) =
        T.phi m (C (ac i) * Tv i) := fun i hi ↦ by
      have hi' : i < n := by
        have := Finset.mem_range.mp hi
        rwa [List.length_map, List.length_range, length_resCodesP] at this
      rw [NestTower.getD_range_map (fun j ↦ c.getD j 0) 0
        (by rw [length_resCodesP]; exact hi'), getD_resCodesP ks m W hi', map_mul,
        T.algebraMap_succ]
      congr 1
      exact T.semX_poly m h _
    rw [Finset.sum_congr rfl e, List.length_map, List.length_range, length_resCodesP, ← map_sum,
      hT0, map_zero]
  obtain ⟨β, hβl, hβ⟩ := T.consys_complete (m + 1) h (resCodesP ks m W) _ (by simp) h0
  have hβc : ∀ i < n, c.getD i 0 = ∑ u ∈ Finset.range U.length,
      β.getD u 0 * algebraMap ℚ Kc ((U.getD u []).getD i 0) := fun i hi ↦ by
    have := hβ i
    rw [NestTower.getD_range_map (fun j ↦ c.getD j 0) 0 (by rw [length_resCodesP]; exact hi),
      NestTower.zipWith_sum_range _ 0 [] _ _ hβl, hβl] at this
    exact this
  -- the polynomial problem
  set βt := (List.range U.length).map fun u ↦ β.getD u 0 with hβt
  have hβtD : ∀ u < U.length, βt.getD u 0 = β.getD u 0 := fun u hu ↦
    NestTower.getD_range_map _ _ hu
  have hlPu : (PuEP ks m W).length = U.length := by simp [PuEP, E1P, hU]
  have hPoly : A = polySumC (algebraMap Kc (T.F m)) M βt (PuEP ks m W) := by
    rw [polySumC, hA]
    have e : ∀ u ∈ Finset.range (PuEP ks m W).length,
        C (algebraMap Kc (T.F m) (βt.getD u 0)) * GPoly.toPoly M ((PuEP ks m W).getD u []) =
        ∑ i ∈ Finset.range n,
          C (algebraMap Kc (T.F m) (β.getD u 0 * algebraMap ℚ Kc ((U.getD u []).getD i 0))) *
            pv i := fun u hu ↦ by
      have hu' : u < U.length := by rw [← hlPu]; exact Finset.mem_range.mp hu
      rw [hβtD u hu', PuEP, NestTower.getD_map' _ (E1P ks m W) [] []
        (by simpa [E1P, hU] using hu'), T.toPoly_PuP m h W, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [E1P, ← hU, NestTower.getD_map' _ U [] [] hu', NestTower.getD_vecOf,
        if_pos (Finset.mem_range.mp hi), map_mul, T.algebraMap_ratX, C_mul, mul_assoc]
    rw [Finset.sum_congr rfl e, Finset.sum_comm, hlPu]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [← Finset.sum_mul, ← map_sum, ← map_sum, ← hβc i (Finset.mem_range.mp hi)]
  -- the fraction field `F m (tₘ)` and the polynomial part of the Liouville form
  let _ := algebraAdjoinSimple (F := T.F m) t
  let _ : Differential (T.F m)[X] := polynomialOfDeriv (C ηv)
  let _ : Differential (T.F m)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮t⟯ := isFractionRing_adjoin_simple _ htr
  have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮t⟯ := differentialAlgebra_adjoin_simple _ _ hw
  have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ P : (T.F m)⟮t⟯) : E) = aeval t P :=
    algebraMap_adjoinSimple _
  have hcoeLog : ∀ y : (T.F m)⟮t⟯, ((logDeriv y : (T.F m)⟮t⟯) : E) = logDeriv (y : E) := by
    intro y
    unfold logDeriv
    rw [IntermediateField.coe_div]
    rfl
  set u'' : ι → (T.F m)⟮t⟯ := fun i ↦ if h : u i ∈ (T.F m)⟮t⟯ then ⟨u i, h⟩ else 1 with hu''d
  have hu'' : ∀ i ∈ s, ((u'' i : (T.F m)⟮t⟯) : E) = u i := fun i hi ↦ by
    simp only [hu''d]
    rw [dif_pos ((T.mem_F_succ).mp (hdata i hi).2.1)]
  have hdegN : Nc.degree < Sv.degree :=
    NestTower.degree_sum_C_mul_lt n _ _ Sv hsq.ne_zero fun i hi ↦ (hdat i hi).2
  obtain ⟨e, Pv, he, hPv⟩ := poly_part_liouville (K := (T.F m)⟮t⟯) (fun _ ↦ rfl) s c' u''
    (fun i hi h0 ↦ (hdata i hi).2.2 (by rw [← hu'' i hi, h0]; rfl)) ⟨v - (G : E), hvg⟩
    A _ ⟨_, _, hsq.ne_zero, hdegN, rfl⟩ (Subtype.ext (by
      rw [IntermediateField.coe_add, IntermediateField.coe_div, hcoe, hcoe, hcoe,
        IntermediateField.coe_add, AddSubmonoidClass.coe_finset_sum]
      have h1 : aeval t A + aeval t Nc / aeval t Sv = aeval t (A * Sv + Nc) / aeval t Sv := by
        rw [map_add, map_mul]
        field_simp
      rw [h1, hbv]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [IntermediateField.coe_mul, hcoe, aeval_C, hcoeLog, hu'' i hi]))
  set SL := ∑ i ∈ s, c' i * logDeriv (e i) with hSL
  have hQ : polySumC (algebraMap Kc (T.F m)) M βt (PuEP ks m W) = Dη M η Pv + C SL := by
    rw [← hPoly]
    change _ = implicitDeriv (C ηv) Pv + C SL
    rw [hPv]
    ring
  have hLSL : LiouvilleIn (T.F m) ((SL : T.F m) : E) := by
    refine ⟨ι, s, cc, fun i ↦ (e i : E), 0, fun i hi ↦ ⟨(hdata i hi).1, (e i).2,
      fun h0 ↦ he i hi (Subtype.ext h0)⟩, zero_mem _, ?_⟩
    rw [map_zero, add_zero, hSL, AddSubmonoidClass.coe_finset_sum]
    exact Finset.sum_congr rfl fun i hi ↦ by
      rw [IntermediateField.coe_mul, hc'E i hi, T.coe_logDeriv_FX]
  obtain ⟨γ, hγ⟩ := polyElem_complete (algebraMap Kc (T.F m)) η lim elem
    (T.sem_cstX m h) hlim hconstK (fun q ↦ T.algebraMap_ratX q) hnd
    (fun b ↦ LiouvilleIn (T.F m) ((b : T.F m) : E))
    (fun y b hb ↦ by
      rw [IntermediateField.coe_add, coe_deriv]
      exact liouvilleIn_deriv_add _ _ y.2 _ hb)
    (fun ws c hc hL ↦ hel.complete ws c hc hL) (PuEP ks m W) βt
    (fun i hi ↦ List.getD_eq_default _ _ (by simp [hβt]; omega)) Pv SL hQ hLSL
  -- assemble
  set pe := polyElem (opsM ks m) (cstN m) η lim elem (PuEP ks m W) with hpe
  refine ⟨γ, fun i ↦ ?_⟩
  rw [List.length_map]
  have e : ∀ k ∈ Finset.range pe.length, γ.getD k 0 * algebraMap ℚ Kc
      (((pe.map fun δ ↦ vcomb n δ (E1P ks m W)).getD k []).getD i 0) =
      γ.getD k 0 * algebraMap ℚ Kc ((vcomb n (pe.getD k []) (E1P ks m W)).getD i 0) :=
    fun k hk ↦ by rw [NestTower.getD_map' _ _ [] [] (Finset.mem_range.mp hk)]
  rw [Finset.sum_congr rfl e]
  by_cases hi : i < n
  · have := recombine n U.length pe.length
      (fun u i ↦ (U.getD u []).getD i 0) (fun j u ↦ (pe.getD j []).getD u 0)
      (fun i ↦ c.getD i 0) (fun u ↦ β.getD u 0) (fun j ↦ γ.getD j 0) hβc
      (fun u hu ↦ by rw [← hβtD u hu, hγ u]) i hi
    rw [this]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [getD_vcomb, if_pos hi, length_E1P, ← hU]
    refine congrArg (fun x ↦ γ.getD k 0 * algebraMap ℚ Kc x) (Finset.sum_congr rfl fun u hu ↦ ?_)
    show (pe.getD k []).getD u 0 * (U.getD u []).getD i 0 =
      (pe.getD k []).getD u 0 * ((E1P ks m W).getD u []).getD i 0
    rw [E1P, ← hU, NestTower.getD_map' _ U [] [] (Finset.mem_range.mp hu), NestTower.getD_vecOf,
      if_pos hi]
  · rw [hc i (by omega)]
    symm
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [getD_vcomb, if_neg hi, map_zero, mul_zero]

end Step

end NestMTower

end Tower.NestM
