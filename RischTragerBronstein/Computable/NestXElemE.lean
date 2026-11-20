import RischTragerBronstein.Computable.NestXLimE

/-!
# Parametric elementary integration at exponential levels of mixed towers

The exponential step `expElemStepX` of `paramElemX` (and the base) for a mixed tower
`NestMTower Kc E ks`: the proofs of `NestMElem.lean`, for an exponential level `ks m = .exp a`,
with the Risch solver one level down and the absence of homogeneous solutions
`e′ + j a′ e = 0` (`j ≠ 0`) as hypotheses.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP Tower.NestX CPoly
section ExpData

variable (ks : (m : ℕ) → KindN m) (m : ℕ)

/-- The derivation polynomial `[0, a′]`. -/
abbrev wkMX : GPoly (Code (m + 1)) := (wK (opsM ks m) (ks m))

/-- The common squarefree denominator of the simple parts. -/
def lcmSMX (W : List (Code (m + 2))) : GPoly (Code (m + 1)) :=
  lcmList (opsM ks m) ((W.map (eSpX ks m)).map ExpSplit.s)

/-- The numerators of the simple parts over `lcmSMX`. -/
def numLMX (W : List (Code (m + 2))) : List (GPoly (Code (m + 1))) :=
  (W.map (eSpX ks m)).map fun e ↦ GPoly.mul (opsM ks m) e.r
    (GPoly.divMod (opsM ks m) (lcmSMX ks m W) e.s).1

/-- The reduced residue test polynomial of `Nᵢ / S`. -/
def ttCodeMX (W : List (Code (m + 2))) (Ni : GPoly (Code (m + 1))) : GPoly (Code (m + 1)) :=
  (GPoly.divMod (opsM ks m) (residueTestCode (opsM ks m)
    (GPoly.residuePoly (opsM ks m) (wkMX ks m) Ni (lcmSMX ks m W)) (lcmSMX ks m W))
    (lcmSMX ks m W)).2

/-- The residue test polynomials as codes of level `m + 1`. -/
def resCodesMX (W : List (Code (m + 2))) : List (Code (m + 2)) :=
  ((numLMX ks m W).map (ttCodeMX ks m W)).map fun T ↦ ((T, [(opsM ks m).one]) : Code (m + 2))

/-- The basis of the residue condition. -/
def E1MX (W : List (Code (m + 2))) : List (List ℚ) :=
  (consys ks (m + 1) (resCodesMX ks m W)).map fun u ↦
    (List.range W.length).map fun i ↦ u.getD i 0

/-- The check on the common denominator. -/
def lcmCheckMX (W : List (Code (m + 2))) : Bool :=
  GPoly.squarefreeCheck (opsM ks m) (lcmSMX ks m W) &&
    (W.map (eSpX ks m)).all
      (fun e ↦ GPoly.isZero (opsM ks m) (GPoly.divMod (opsM ks m) (lcmSMX ks m W) e.s).2)

/-- The common order at `t = 0` of the Laurent parts. -/
def SMX (W : List (Code (m + 2))) : ℕ := laurentS (W.map (eSpX ks m))

/-- The Laurent parts of the basis of the residue condition. -/
def PuMX (W : List (Code (m + 2))) : List (GPoly (Code (m + 1))) :=
  (E1MX ks m W).map fun e ↦ lcombGP (opsM ks m) (cstN m) e
    ((W.map (eSpX ks m)).map (shiftedL (opsM ks m) (SMX ks m W)))

/-- The coefficient solvers. -/
def solMX (a : Code (m + 1)) (rde : Code (m + 1) → List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (elem : List (Code (m + 1)) → List (List ℚ)) (W : List (Code (m + 2))) :
    ℕ → List (Code (m + 1)) → List (List ℚ) := fun i ws ↦
  if i = SMX ks m W then elem ws
  else (rde ((opsM ks m).mul (cstN m ((i : ℚ) - SMX ks m W)) a) ws).map
    Prod.fst

/-- The top degree of the Laurent parts. -/
def topMX (W : List (Code (m + 2))) : ℕ := ((PuMX ks m W).map List.length).foldr max 0

lemma expElemStep_eqX (a : Code (m + 1)) (rde : Code (m + 1) → List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (elem : List (Code (m + 1)) → List (List ℚ)) (W : List (Code (m + 2))) :
    expElemStepX ks m a elem rde W =
      if lcmCheckMX ks m W then
        (elemLoop (E1MX ks m W).length
          (fun i Bs ↦ solMX ks m a rde elem W i (coefCodes (opsM ks m) (cstN m) (PuMX ks m W) i Bs))
          (topMX ks m W) ((List.range (E1MX ks m W).length).map (unitV (E1MX ks m W).length))).map
          fun δ ↦ vcomb W.length δ (E1MX ks m W)
      else [] := rfl

end ExpData


namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : (m : ℕ) → KindN m}
variable (T : NestMTower Kc E ks)

section Data

variable (m : ℕ) (h : T.Tr (m + 1)) {a : Code (m + 1)} (hka : ks m = .exp a)

include hka in
/-- **The common denominator**: squarefree, prime to `t`, and every weight is
`gᵢ′ + Nᵢ / S + Lᵢ / tˢ` with `deg Nᵢ < deg S`. -/
lemma lcm_dataMX (W : List (Code (m + 2))) (hchk : lcmCheckMX ks m W = true) :
    Squarefree (GPoly.toPoly (T.MX m h) (lcmSMX ks m W)) ∧
    ¬X ∣ GPoly.toPoly (T.MX m h) (lcmSMX ks m W) ∧
    ∀ i < W.length, (T.MP (m + 1) h).sem (W.getD i (opsM ks (m + 1)).zero) =
      ((T.M1X m h).sem ((eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gn,
        (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gd))′ +
      T.phi m (GPoly.toPoly (T.MX m h) ((numLMX ks m W).getD i [])) /
        T.phi m (GPoly.toPoly (T.MX m h) (lcmSMX ks m W)) +
      T.σX m h (shiftedL (opsM ks m) (SMX ks m W)
        (eSpX ks m (W.getD i (opsM ks (m + 1)).zero))) / T.phi m (X ^ SMX ks m W) ∧
      (GPoly.toPoly (T.MX m h) ((numLMX ks m W).getD i [])).degree <
        (GPoly.toPoly (T.MX m h) (lcmSMX ks m W)).degree := by
  have hinj := T.phi_injX m h
  simp only [lcmCheckMX, Bool.and_eq_true] at hchk
  obtain ⟨hsqc, hall⟩ := hchk
  have hsq : Squarefree (GPoly.toPoly (T.MX m h) (lcmSMX ks m W)) :=
    GPoly.squarefreeCheck_sound (T.MX m h) hsqc
  have hs : ∀ p ∈ (W.map (eSpX ks m)).map ExpSplit.s, GPoly.toPoly (T.MX m h) p ≠ 0 ∧
      ¬X ∣ GPoly.toPoly (T.MX m h) p := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp he
    exact ⟨(T.exp_weight_decompX m h hka w).2.1.ne_zero, (T.exp_weight_decompX m h hka w).2.2.1⟩
  have hX : ¬X ∣ GPoly.toPoly (T.MX m h) (lcmSMX ks m W) := by
    intro hXd
    have := hXd.trans (lcmList_dvd_prod (T.MX m h) _ fun p hp ↦ (hs p hp).1)
    obtain ⟨q, hq, hXq⟩ := (Prime.dvd_prod_iff prime_X).mp this
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact (hs p hp).2 hXq
  refine ⟨hsq, hX, fun i hi ↦ ?_⟩
  obtain ⟨w, hw⟩ : ∃ w, w = W.getD i (opsM ks (m + 1)).zero := ⟨_, rfl⟩
  rw [← hw]
  have hwm : w ∈ W := by rw [hw, List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  have hS : ∀ e ∈ W.map (eSpX ks m), e.k ≤ SMX ks m W := fun e he ↦ k_le_laurentSX m hka _ e he
  have hval := T.sem_weightX m h hka W (SMX ks m W) hS i hi
  rw [← hw] at hval
  obtain ⟨-, hsqs, -, hdeg⟩ := T.exp_weight_decompX m h hka w
  have hz := List.all_eq_true.mp hall (eSpX ks m w) (List.mem_map.mpr ⟨w, hwm, rfl⟩)
  have hr0 := (GPoly.isZero_iff (T.MX m h) _).mp hz
  have hdm := GPoly.divMod_spec (T.MX m h) (lcmSMX ks m W) (eSpX ks m w).s
  rw [hr0, add_zero] at hdm
  set d := GPoly.toPoly (T.MX m h) (GPoly.divMod (opsM ks m) (lcmSMX ks m W) (eSpX ks m w).s).1
    with hd
  have hd0 : d ≠ 0 := fun h0 ↦ hsq.ne_zero (by rw [hdm, h0, zero_mul])
  have hN : GPoly.toPoly (T.MX m h) ((numLMX ks m W).getD i []) =
      GPoly.toPoly (T.MX m h) (eSpX ks m w).r * d := by
    rw [numLMX, NestTower.getD_map_map (eSpX ks m) _ W (opsM ks (m + 1)).zero [] hi, ← hw,
      GPoly.toPoly_mul]
  refine ⟨?_, ?_⟩
  · have hφd : T.phi m d ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd0
    have hφs : T.phi m (GPoly.toPoly (T.MX m h) (eSpX ks m w).s) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr hsqs.ne_zero
    have hmid : T.σX m h (eSpX ks m w).r / T.σX m h (eSpX ks m w).s =
        T.phi m (GPoly.toPoly (T.MX m h) (eSpX ks m w).r * d) /
          T.phi m (GPoly.toPoly (T.MX m h) (lcmSMX ks m W)) := by
      simp only [σX]
      rw [hdm, map_mul, map_mul]
      field_simp
    rw [hval, hN, hmid]
  · rw [hN, hdm, degree_mul, degree_mul, add_comm]
    exact WithBot.add_lt_add_left (degree_ne_bot.mpr hd0) hdeg

include hka in
/-- **The residue data**: the residue polynomial of `Nᵢ / S` and its reduced test polynomial. -/
lemma res_dataMX (W : List (Code (m + 2)))
    (hS : Squarefree (GPoly.toPoly (T.MX m h) (lcmSMX ks m W)))
    (hX : ¬X ∣ GPoly.toPoly (T.MX m h) (lcmSMX ks m W)) (Ni : GPoly (Code (m + 1))) :
    GPoly.toPoly (T.MX m h) (lcmSMX ks m W) ∣
      GPoly.toPoly (T.MX m h) (GPoly.residuePoly (opsM ks m) (wkMX ks m) Ni (lcmSMX ks m W)) *
        (mapCoeffs (GPoly.toPoly (T.MX m h) (lcmSMX ks m W)) +
          C (T.bX m h a) * X * derivative (GPoly.toPoly (T.MX m h) (lcmSMX ks m W))) -
        GPoly.toPoly (T.MX m h) Ni ∧
    GPoly.toPoly (T.MX m h) (lcmSMX ks m W) ∣
      residueTest (GPoly.toPoly (T.MX m h)
        (GPoly.residuePoly (opsM ks m) (wkMX ks m) Ni (lcmSMX ks m W)))
        (GPoly.toPoly (T.MX m h) (lcmSMX ks m W)) -
        GPoly.toPoly (T.MX m h) (ttCodeMX ks m W Ni) ∧
    (GPoly.toPoly (T.MX m h) (ttCodeMX ks m W Ni)).degree <
      (GPoly.toPoly (T.MX m h) (lcmSMX ks m W)).degree := by
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hwk : GPoly.toPoly (T.MX m h) (wkMX ks m) = C (T.bX m h a) * X := T.toPoly_wK_exp m h hka
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly (T.MX m h) (wkMX ks m))
      (GPoly.toPoly (T.MX m h) (lcmSMX ks m W))) (GPoly.toPoly (T.MX m h) (lcmSMX ks m W)) := by
    rw [hwk, ← T.wPoly_eq_bX m h hka]
    let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
    exact isCoprime_deriv_of_squarefree hS (fun p hp hpS ↦
      T.normal_exp m htr hka p hp (fun hXp ↦ hX (hXp.trans hpS)))
  have hrs := GPoly.residuePoly_spec (T.MX m h) (wkMX ks m) Ni _ hS.ne_zero hcop
  have himp : implicitDeriv (GPoly.toPoly (T.MX m h) (wkMX ks m)) (GPoly.toPoly (T.MX m h) (lcmSMX ks m W)) =
      mapCoeffs (GPoly.toPoly (T.MX m h) (lcmSMX ks m W)) +
        C (T.bX m h a) * X * derivative (GPoly.toPoly (T.MX m h) (lcmSMX ks m W)) := by
    rw [hwk]; simp [implicitDeriv]
  rw [himp] at hrs
  refine ⟨hrs, ?_, GPoly.divMod_degree_lt (T.MX m h) _ _ hS.ne_zero⟩
  have hdm := GPoly.divMod_spec (T.MX m h) (residueTestCode (opsM ks m)
    (GPoly.residuePoly (opsM ks m) (wkMX ks m) Ni (lcmSMX ks m W)) (lcmSMX ks m W))
    (lcmSMX ks m W)
  rw [NestTower.toPoly_residueTestCode] at hdm
  rw [ttCodeMX, hdm]
  exact ⟨_, by ring⟩

lemma length_resCodesMX (W : List (Code (m + 2))) : (resCodesMX ks m W).length = W.length := by
  unfold resCodesMX numLMX
  exact (List.length_map _).trans ((List.length_map _).trans ((List.length_map _).trans
    (List.length_map _)))

lemma getD_resCodesMX (W : List (Code (m + 2))) {i : ℕ} (hi : i < W.length) :
    (resCodesMX ks m W).getD i (opsM ks (m + 1)).zero =
      ((ttCodeMX ks m W ((numLMX ks m W).getD i []), [(opsM ks m).one]) : Code (m + 2)) :=
  NestTower.getD_map_map _ _ _ [] _ (by unfold numLMX; simpa using hi)

/-- The relation given by a basis vector of the residue system. -/
lemma rel_resMX (W : List (Code (m + 2))) (u : CPoly ℚ)
    (hu : u ∈ consys ks (m + 1) (resCodesMX ks m W)) :
    ∑ i ∈ Finset.range W.length, C ((u.getD i 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.MX m h) (ttCodeMX ks m W ((numLMX ks m W).getD i [])) = 0 := by
  have := T.consys_sound (m + 1) h (resCodesMX ks m W) u hu
  rw [NestTower.zipWith_sum_range _ 0 (opsM ks (m + 1)).zero _ _ (by simp)] at this
  apply T.phi_injX m h
  rw [map_zero, ← this, map_sum]
  refine Finset.sum_congr (by rw [List.length_map, List.length_range, length_resCodesMX]) fun i hi ↦ ?_
  have hi' : i < W.length := by
    have := Finset.mem_range.mp hi
    rwa [List.length_map, List.length_range, length_resCodesMX] at this
  rw [NestTower.getD_range_map (fun j ↦ algebraMap ℚ Kc (u.getD j 0)) 0
    (by rw [length_resCodesMX]; exact hi'), T.algebraMap_ratCastMX, getD_resCodesMX m W hi',
    map_mul, T.phi_C_ratCastMX]
  congr 1
  change _ = T.σX m h _ / T.σX m h [(opsM ks m).one]
  rw [T.σX_one, div_one]

lemma length_E1MX (W : List (Code (m + 2))) :
    (E1MX ks m W).length = (consys ks (m + 1) (resCodesMX ks m W)).length := by
  simp [E1MX]

/-- The test polynomials, recombined, vanish. -/
lemma sum_Tv_eq_zeroMX (W : List (Code (m + 2))) (δ : List ℚ) :
    ∑ i ∈ Finset.range W.length, C (((vcomb W.length δ (E1MX ks m W)).getD i 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.MX m h) (ttCodeMX ks m W ((numLMX ks m W).getD i [])) = 0 := by
  set U := consys ks (m + 1) (resCodesMX ks m W) with hU
  have e : ∀ i ∈ Finset.range W.length,
      C (((vcomb W.length δ (E1MX ks m W)).getD i 0 : ℚ) : T.F m) *
        GPoly.toPoly (T.MX m h) (ttCodeMX ks m W ((numLMX ks m W).getD i [])) =
      ∑ k ∈ Finset.range U.length, C ((δ.getD k 0 : ℚ) : T.F m) *
        (C (((U.getD k []).getD i 0 : ℚ) : T.F m) *
          GPoly.toPoly (T.MX m h) (ttCodeMX ks m W ((numLMX ks m W).getD i []))) :=
    fun i hi ↦ by
      have hi' := Finset.mem_range.mp hi
      rw [getD_vcomb, if_pos hi', length_E1MX, ← hU]
      push_cast
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [E1MX, ← hU, NestTower.getD_map' _ U [] [] (Finset.mem_range.mp hk),
        NestTower.getD_range_map _ _ hi', C_mul]
      ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  rw [← Finset.mul_sum, T.rel_resMX m h W _ (NestTower.getD_mem_of_lt U [] (Finset.mem_range.mp hk)), mul_zero]

include T h hka in
/-- **The lcm check always passes.** -/
lemma lcmCheck_trueMX (W : List (Code (m + 2))) : lcmCheckMX ks m W = true := by
  have hs : ∀ p ∈ (W.map (eSpX ks m)).map ExpSplit.s,
      GPoly.toPoly (T.MX m h) p ≠ 0 ∧ Squarefree (GPoly.toPoly (T.MX m h) p) := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp he
    have := (T.exp_weight_decompX m h hka w).2.1
    exact ⟨this.ne_zero, this⟩
  obtain ⟨hdvd, -, hsqf⟩ := GPolyLcm.lcmList_spec (T.MX m h) _ (fun p hp ↦ (hs p hp).1)
  simp only [lcmCheckMX, Bool.and_eq_true]
  refine ⟨GPoly.squarefreeCheck_complete (T.MX m h) (hsqf fun p hp ↦ (hs p hp).2),
    List.all_eq_true.mpr fun e he ↦ ?_⟩
  refine (GPoly.isZero_iff (T.MX m h) _).mpr (GPoly.divMod_exact (T.MX m h) _ _ ?_
    (hdvd _ (List.mem_map.mpr ⟨e, he, rfl⟩)))
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp he
  exact (T.exp_weight_decompX m h hka w).2.1.ne_zero

end Data

section Split

variable (m : ℕ) (h : T.Tr (m + 1)) {a : Code (m + 1)} (hka : ks m = .exp a)

lemma const_memMX (z : E) (hz : z′ = 0) : z ∈ T.F m := by
  obtain ⟨κ, rfl⟩ := T.hCall z hz
  exact (T.F m).algebraMap_mem κ

variable (hhom : ∀ j : ℤ, j ≠ 0 → ∀ e : T.F m, e ≠ 0 → e′ + (j : T.F m) * T.bX m h a * e ≠ 0)

include hhom hka in
set_option maxHeartbeats 1600000 in
/-- **The Liouville analysis of an exponential step**: if `G′ + N / S + P / tˢ` (`N / S` a normal
simple part with residue data `R`) has a Liouville form over `F (m + 1)`, then the residue test
passes, every Laurent coefficient `j ≠ S` of `P` is `y′ + (j - S) a′ y`, and `P_S` has a Liouville
form over `F m`. -/
theorem exp_liouville_splitX (G : T.F (m + 1)) (Nc Sd R P : (T.F m)[X]) (S : ℕ)
    (hsq : Squarefree Sd) (hX : ¬X ∣ Sd) (hdeg : Nc.degree < Sd.degree)
    (hr : Sd ∣ R * (mapCoeffs Sd + C (T.bX m h a) * X * derivative Sd) - Nc)
    (hL : LiouvilleIn (T.F (m + 1))
      (((G′ + T.phi m Nc / T.phi m Sd + T.phi m P / T.phi m (X ^ S) : T.F (m + 1))) : E)) :
    Sd ∣ residueTest R Sd ∧
      (∀ j, j ≠ S → ∃ y : T.F m, y′ + (((j : ℤ) - S : ℤ) : T.F m) * T.bX m h a * y = P.coeff j) ∧
      LiouvilleIn (T.F m) (((P.coeff S : T.F m)) : E) := by
  classical
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hinj := T.phi_injX m h
  obtain ⟨ι, s, cc, u, v, hdata, hv, heq⟩ := hL
  set t := T.ts m with ht
  have htd : t′ = algebraMap (T.F m) E (T.bX m h a) * t := by
    rw [ht, T.deriv_ts_aeval m, T.wPoly_eq_bX m h hka, map_mul, aeval_C, aeval_X]
  have hconst : ∀ z ∈ (T.F m)⟮t⟯, z′ = 0 → z ∈ Set.range (algebraMap (T.F m) E) :=
    fun z _ hz0 ↦ by
      obtain ⟨κ, rfl⟩ := T.hCall z hz0
      exact ⟨algebraMap Kc (T.F m) κ, rfl⟩
  -- the constants as elements of `F m`
  set c' : ι → T.F m := fun i ↦ if hc : (cc i)′ = 0 then ⟨cc i, T.const_memMX m _ hc⟩ else 0
    with hc'
  have hc'E : ∀ i ∈ s, ((c' i : T.F m) : E) = cc i := fun i hi ↦ by
    simp only [hc']
    rw [dif_pos (hdata i hi).1]
  have hc'd : ∀ i ∈ s, (c' i)′ = 0 := fun i hi ↦
    Subtype.ext (by rw [coe_deriv, hc'E i hi, (hdata i hi).1]; rfl)
  have hvg : v - (G : E) ∈ (T.F m)⟮t⟯ := (T.mem_F_succ).mp (sub_mem hv G.2)
  have hsumc : ∑ i ∈ s, cc i * logDeriv (u i) =
      ∑ i ∈ s, algebraMap (T.F m) E (c' i) * logDeriv (u i) :=
    Finset.sum_congr rfl fun i hi ↦ by rw [← hc'E i hi]; rfl
  have hSd0 : aeval t Sd ≠ 0 := by
    rw [ht, ← T.coe_phi]
    exact fun h0 ↦ hsq.ne_zero (hinj ((Subtype.ext h0).trans (map_zero _).symm))
  have htS : (t : E) ^ S ≠ 0 := by
    have : aeval t (X ^ S : (T.F m)[X]) ≠ 0 := by
      rw [ht, ← T.coe_phi]
      exact fun h0 ↦ (pow_ne_zero S X_ne_zero) (hinj ((Subtype.ext h0).trans (map_zero _).symm))
    simpa using this
  have hval : (((G′ + T.phi m Nc / T.phi m Sd + T.phi m P / T.phi m (X ^ S) : T.F (m + 1))) : E) =
      (G : E)′ + aeval t Nc / aeval t Sd + aeval t P / t ^ S := by
    rw [IntermediateField.coe_add, IntermediateField.coe_add, IntermediateField.coe_div,
      IntermediateField.coe_div, coe_deriv, T.coe_phi, T.coe_phi, T.coe_phi, T.coe_phi, map_pow,
      aeval_X]
  rw [hval] at heq
  -- the residue test
  have hT : Sd ∣ residueTest R Sd := by
    refine residueTest_step_exponential (F := T.F m) t htr (T.bX m h a) htd hconst s c' u
      (fun i hi ↦ ⟨(T.mem_F_succ).mp (hdata i hi).2.1, (hdata i hi).2.2⟩) hc'd (v - (G : E)) hvg
      (Nc * X ^ S + P * Sd) Nc Sd R S hsq hX ⟨P, by ring⟩ hr ?_
    rw [← hsumc, map_sub, ← add_sub_assoc, ← heq, map_add, map_mul, map_mul, map_pow, aeval_X]
    field_simp
    ring
  refine ⟨hT, ?_⟩
  -- the Laurent part, in `K = F m (t)`
  have hw := T.deriv_ts_aeval m
  let _ := algebraAdjoinSimple (F := T.F m) t
  let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  let _ : Differential (T.F m)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮t⟯ := isFractionRing_adjoin_simple _ htr
  have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮t⟯ := differentialAlgebra_adjoin_simple _ _ hw
  have hcoe : ∀ Q, ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ Q : (T.F m)⟮t⟯) : E) = aeval t Q :=
    algebraMap_adjoinSimple _
  have hDe : ∀ Q : (T.F m)[X], Q′ = implicitDeriv (C (T.bX m h a) * X) Q := fun Q ↦ by
    change implicitDeriv (T.wPoly m) Q = _
    rw [T.wPoly_eq_bX m h hka]
  have hdK : ∀ y : (T.F m)⟮t⟯, ((y′ : (T.F m)⟮t⟯) : E) = (y : E)′ := fun y ↦ rfl
  have hcoeLog : ∀ y : (T.F m)⟮t⟯, ((logDeriv y : (T.F m)⟮t⟯) : E) = logDeriv (y : E) := by
    intro y
    unfold logDeriv
    rw [IntermediateField.coe_div]
    rfl
  set u'' : ι → (T.F m)⟮t⟯ := fun i ↦ if hu : u i ∈ (T.F m)⟮t⟯ then ⟨u i, hu⟩ else 1 with hu''d
  have hu'' : ∀ i ∈ s, ((u'' i : (T.F m)⟮t⟯) : E) = u i := fun i hi ↦ by
    simp only [hu''d]
    rw [dif_pos ((T.mem_F_succ).mp (hdata i hi).2.1)]
  obtain ⟨e, n, V, kv, he, hPV⟩ := laurent_part_liouville (K := (T.F m)⟮t⟯) hDe s c' u''
    (fun i hi h0 ↦ (hdata i hi).2.2 (by rw [← hu'' i hi, h0]; rfl)) ⟨v - (G : E), hvg⟩ P S
    (algebraMap (T.F m)[X] (T.F m)⟮t⟯ Nc / algebraMap (T.F m)[X] (T.F m)⟮t⟯ Sd)
    ⟨Nc, Sd, hsq.ne_zero, hX, hdeg, rfl⟩ (Subtype.ext (by
      rw [IntermediateField.coe_add, IntermediateField.coe_div, IntermediateField.coe_div, hcoe,
        hcoe, hcoe, hcoe, IntermediateField.coe_add, AddSubmonoidClass.coe_finset_sum, hdK,
        map_pow, aeval_X]
      have h1 : aeval t P / t ^ S + aeval t Nc / aeval t Sd =
          ∑ i ∈ s, algebraMap (T.F m) E (c' i) * logDeriv (u i) + (v - (G : E))′ := by
        rw [← hsumc, map_sub, ← add_sub_assoc, ← heq]
        ring
      rw [h1]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [IntermediateField.coe_mul, hcoe, aeval_C, hcoeLog, hu'' i hi]))
  obtain ⟨hj, hS⟩ := laurent_coeff_eqs (T.bX m h a) P V _ kv S hPV
  refine ⟨hj, ?_⟩
  -- `P_S` has a Liouville form over `F m`
  set α := (T.MX m h).sem a with hα
  have hbα : T.bX m h a = α′ := rfl
  set q : T.F m := ∑ i ∈ s, c' i * (n i : T.F m) with hq
  have hqd : q′ = 0 := by
    rw [hq, map_sum]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rw [Derivation.leibniz, hc'd i hi, show ((n i : T.F m))′ = 0 by
      simpa using deriv_ratCastK (K := T.F m) (n i : ℚ)]
    simp
  have e1 : ∑ i ∈ s, c' i * (logDeriv (e i) + (n i : T.F m) * T.bX m h a) =
      ∑ i ∈ s, c' i * logDeriv (e i) + q * T.bX m h a := by
    rw [hq, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hPS : P.coeff S = ∑ i ∈ s, c' i * logDeriv (e i) + (V.coeff kv + q * α)′ := by
    rw [hS, e1, map_add, Derivation.leibniz, hqd, ← hbα]
    simp only [smul_eq_mul, mul_zero, add_zero]
    ring
  refine ⟨ι, s, cc, fun i ↦ ((e i : T.F m) : E), ((V.coeff kv + q * α : T.F m) : E),
    fun i hi ↦ ⟨(hdata i hi).1, (e i).2, fun h0 ↦ he i hi (Subtype.ext h0)⟩,
    (V.coeff kv + q * α).2, ?_⟩
  rw [hPS, IntermediateField.coe_add, AddSubmonoidClass.coe_finset_sum, coe_deriv]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [IntermediateField.coe_mul, hc'E i hi, T.coe_logDeriv_FX]

end Split

section Adm

variable (m : ℕ) (h : T.Tr (m + 1)) (a : Code (m + 1)) (hka : ks m = .exp a)

/-- Admissibility of the Laurent coefficient `i` (exponent `i - S`), rational combinations. -/
def AdmMX (S i : ℕ) (v : T.F m) : Prop :=
  if i = S then HasElementaryIntegralIn (v : E)
  else ∃ y : T.F m, y′ + (((i : ℤ) - S : ℤ) : T.F m) * T.bX m h a * y = v

/-- Admissibility of the Laurent coefficient `i`, constant combinations. -/
def AdmCMX (S i : ℕ) (v : T.F m) : Prop :=
  if i = S then LiouvilleIn (T.F m) (v : E)
  else ∃ y : T.F m, y′ + (((i : ℤ) - S : ℤ) : T.F m) * T.bX m h a * y = v

lemma admM_zeroX (S i : ℕ) : T.AdmMX m h a S i 0 := by
  unfold AdmMX
  split_ifs
  · have := hasElementaryIntegralIn_deriv (0 : E)
    rwa [Derivation.map_zero] at this
  · exact ⟨0, by simp⟩

/-- Admissibility is a `ℚ`-linear condition. -/
lemma admM_linX (S i : ℕ) (s : Finset ℕ) (q : ℕ → ℚ) (v : ℕ → T.F m)
    (hv : ∀ k ∈ s, T.AdmMX m h a S i (v k)) : T.AdmMX m h a S i (∑ k ∈ s, ((q k : ℚ) : T.F m) * v k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using T.admM_zeroX m h a S i
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    have h1 := hv k (Finset.mem_insert_self k s)
    have h2 := ih fun j hj ↦ hv j (Finset.mem_insert_of_mem hj)
    unfold AdmMX at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ with hi
    · rw [IntermediateField.coe_add, IntermediateField.coe_mul]
      refine HasElementaryIntegralIn.add (h1.const_mul _ ?_) h2
      rw [NestMTower.coe_ratCast]
      exact T.deriv_ratCast_E _
    · obtain ⟨y1, hy1⟩ := h1
      obtain ⟨y2, hy2⟩ := h2
      refine ⟨((q k : ℚ) : T.F m) * y1 + y2, ?_⟩
      rw [← hy1, ← hy2, map_add, Derivation.leibniz, T.deriv_ratCast]
      simp only [smul_eq_mul, mul_zero, add_zero]
      ring

variable (hhom : ∀ j : ℤ, j ≠ 0 → ∀ e : T.F m, e ≠ 0 → e′ + (j : T.F m) * T.bX m h a * e ≠ 0)

/-- **The coefficient solvers meet their specification.** -/
lemma solM_specX (elem : List (Code (m + 1)) → List (List ℚ))
    (hel : ElemSolSpec (algebraMap Kc (T.F m)) (T.MX m h) (fun v ↦ HasElementaryIntegralIn (v : E))
      (fun v ↦ LiouvilleIn (T.F m) (v : E)) elem)
    (rde : Code (m + 1) → List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (hprde : ∀ f : Code (m + 1),
      RdeSpecK (algebraMap Kc (T.F m)) (T.MX m h) ((T.MX m h).sem f)′ (rde f))
    (W : List (Code (m + 2))) (i : ℕ) :
    ElemSolSpec (algebraMap Kc (T.F m)) (T.MX m h) (T.AdmMX m h a (SMX ks m W) i)
      (T.AdmCMX m h a (SMX ks m W) i) (solMX ks m a rde elem W i) := by
  by_cases hi : i = SMX ks m W
  · have e1 : solMX ks m a rde elem W i = elem := funext fun ws ↦ if_pos hi
    have e2 : T.AdmMX m h a (SMX ks m W) i = fun v : T.F m ↦ HasElementaryIntegralIn (v : E) :=
      funext fun v ↦ if_pos hi
    have e3 : T.AdmCMX m h a (SMX ks m W) i = fun v : T.F m ↦ LiouvilleIn (T.F m) (v : E) :=
      funext fun v ↦ if_pos hi
    rw [e1, e2, e3]
    exact hel
  · set f := (opsM ks m).mul (cstN m ((i : ℚ) - SMX ks m W)) a with hf
    have hfd : ((T.MX m h).sem f)′ = (((i : ℤ) - SMX ks m W : ℤ) : T.F m) * T.bX m h a := by
      rw [hf, (T.MX m h).sem_mul, T.sem_cstN m _, Derivation.leibniz, deriv_ratCastK, bX]
      simp only [smul_eq_mul, mul_zero, add_zero]
      push_cast
      ring
    have e1 : solMX ks m a rde elem W i = fun ws ↦ (rde f ws).map Prod.fst :=
      funext fun ws ↦ if_neg hi
    have e2 : T.AdmMX m h a (SMX ks m W) i = fun v ↦
        ∃ y : T.F m, y′ + (((i : ℤ) - SMX ks m W : ℤ) : T.F m) * T.bX m h a * y = v :=
      funext fun v ↦ if_neg hi
    have e3 : T.AdmCMX m h a (SMX ks m W) i = fun v ↦
        ∃ y : T.F m, y′ + (((i : ℤ) - SMX ks m W : ℤ) : T.F m) * T.bX m h a * y = v :=
      funext fun v ↦ if_neg hi
    rw [e1, e2, e3]
    refine ⟨fun ws β hβ ↦ ?_, fun ws c hc hadm ↦ ?_⟩
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hβ
      refine ⟨(T.MX m h).sem r.2, ?_⟩
      rw [← (hprde f).sound ws r hr, hfd]
    · obtain ⟨y, hy⟩ := hadm
      obtain ⟨β, hβc, -⟩ := (hprde f).complete ws c hc y (by rw [hfd]; exact hy)
      refine ⟨β, fun k ↦ ?_⟩
      rw [hβc k, List.length_map]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      rw [NestTower.getD_map' _ _ ([], (opsM ks m).zero) [] (Finset.mem_range.mp hl)]

include hka in
/-- **Admissible Laurent coefficients give an elementary integral.** -/
lemma laurent_elemX (P : (T.F m)[X]) (S : ℕ) (hadm : ∀ i, T.AdmMX m h a S i (P.coeff i)) :
    HasElementaryIntegralIn (((T.phi m P / T.phi m (X ^ S) : T.F (m + 1))) : E) := by
  classical
  have hinj := T.phi_injX m h
  have hXS : T.phi m (X ^ S) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  rw [P.as_sum_range_C_mul_X_pow, map_sum, Finset.sum_div, AddSubmonoidClass.coe_finset_sum]
  refine Finset.sum_induction _ (fun x : E ↦ HasElementaryIntegralIn x) (fun a b ha hb ↦ ha.add hb)
    (by have := hasElementaryIntegralIn_deriv (0 : E); rwa [Derivation.map_zero] at this)
    (fun i _ ↦ ?_)
  have hi := hadm i
  unfold AdmMX at hi
  split_ifs at hi with hiS
  · subst hiS
    rw [map_mul, mul_div_assoc, div_self hXS, mul_one, T.phi_C]
    exact hi
  · obtain ⟨y, hy⟩ := hi
    have e : T.phi m (C (P.coeff i) * X ^ i) / T.phi m (X ^ S) =
        (T.phi m (C y * X ^ i) / T.phi m (X ^ S))′ := by
      rw [T.deriv_laurent_towerX m h hka, ← hy]
      congr 2
      rw [Derivation.leibniz, implicitDeriv_C, deriv_X_pow]
      simp only [smul_eq_mul, C_add, C_mul, C_sub]
      push_cast
      simp only [C_add, C_mul, C_sub, C_neg]
      ring
    rw [e, coe_deriv]
    exact hasElementaryIntegralIn_deriv _

end Adm

section PuFacts

variable (m : ℕ) (h : T.Tr (m + 1)) {a : Code (m + 1)} (hka : ks m = .exp a)

lemma toPoly_PuMX (W : List (Code (m + 2))) {u : ℕ} (hu : u < (E1MX ks m W).length) :
    GPoly.toPoly (T.MX m h) ((PuMX ks m W).getD u []) = ∑ i ∈ Finset.range W.length,
      C ((((E1MX ks m W).getD u []).getD i 0 : ℚ) : T.F m) * GPoly.toPoly (T.MX m h)
        (shiftedL (opsM ks m) (SMX ks m W) (eSpX ks m (W.getD i (opsM ks (m + 1)).zero))) := by
  rw [PuMX, NestTower.getD_map' _ _ [] [] hu, toPoly_lcombGP (T.MX m h) (cstN m) (T.sem_cstN m _),
    zipWith_sum_getD (fun (q : ℚ) (p : GPoly (Code (m + 1))) ↦
      C (q : T.F m) * GPoly.toPoly (T.MX m h) p) 0 [] (by simp)]
  rw [show ((W.map (eSpX ks m)).map (shiftedL (opsM ks m) (SMX ks m W))).length = W.length by simp]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [NestTower.getD_map_map (eSpX ks m) _ W (opsM ks (m + 1)).zero [] (Finset.mem_range.mp hi)]

lemma length_PuMX (W : List (Code (m + 2))) : (PuMX ks m W).length = (E1MX ks m W).length := by
  simp [PuMX]

lemma getD_E1MX (W : List (Code (m + 2))) {u i : ℕ} (hu : u < (E1MX ks m W).length)
    (hi : i < W.length) : ((E1MX ks m W).getD u []).getD i 0 =
      ((consys ks (m + 1) (resCodesMX ks m W)).getD u []).getD i 0 := by
  rw [E1MX, NestTower.getD_map' _ _ [] [] (by simpa [E1MX] using hu), NestTower.getD_range_map _ _ hi]

/-- The Laurent part of a rational combination. -/
lemma sum_PuM_QX (W : List (Code (m + 2))) (δ : List ℚ) :
    ∑ u ∈ Finset.range (PuMX ks m W).length, C ((δ.getD u 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.MX m h) ((PuMX ks m W).getD u []) =
    ∑ i ∈ Finset.range W.length, C (((vcomb W.length δ (E1MX ks m W)).getD i 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.MX m h) (shiftedL (opsM ks m) (SMX ks m W)
        (eSpX ks m (W.getD i (opsM ks (m + 1)).zero))) := by
  have e : ∀ u ∈ Finset.range (PuMX ks m W).length, C ((δ.getD u 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.MX m h) ((PuMX ks m W).getD u []) = ∑ i ∈ Finset.range W.length,
        C (((δ.getD u 0 * ((E1MX ks m W).getD u []).getD i 0 : ℚ)) : T.F m) *
          GPoly.toPoly (T.MX m h) (shiftedL (opsM ks m) (SMX ks m W)
            (eSpX ks m (W.getD i (opsM ks (m + 1)).zero))) := fun u hu ↦ by
    have hu' : u < (E1MX ks m W).length := by rw [← length_PuMX]; exact Finset.mem_range.mp hu
    rw [T.toPoly_PuMX m h W hu', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    push_cast
    rw [C_mul]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm, length_PuMX]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [getD_vcomb, if_pos (Finset.mem_range.mp hi), ← Finset.sum_mul]
  push_cast
  rw [map_sum]

/-- The Laurent part of a constant combination. -/
lemma sum_PuM_KX (W : List (Code (m + 2))) (β0 c : List Kc)
    (hc : ∀ i < W.length, c.getD i 0 = ∑ u ∈ Finset.range (E1MX ks m W).length,
      β0.getD u 0 * algebraMap ℚ Kc (((E1MX ks m W).getD u []).getD i 0)) :
    ∑ u ∈ Finset.range (PuMX ks m W).length, C (algebraMap Kc (T.F m) (β0.getD u 0)) *
      GPoly.toPoly (T.MX m h) ((PuMX ks m W).getD u []) =
    ∑ i ∈ Finset.range W.length, C (algebraMap Kc (T.F m) (c.getD i 0)) *
      GPoly.toPoly (T.MX m h) (shiftedL (opsM ks m) (SMX ks m W)
        (eSpX ks m (W.getD i (opsM ks (m + 1)).zero))) := by
  have e : ∀ u ∈ Finset.range (PuMX ks m W).length, C (algebraMap Kc (T.F m) (β0.getD u 0)) *
      GPoly.toPoly (T.MX m h) ((PuMX ks m W).getD u []) = ∑ i ∈ Finset.range W.length,
        C (algebraMap Kc (T.F m) (β0.getD u 0 * algebraMap ℚ Kc (((E1MX ks m W).getD u []).getD i 0))) *
          GPoly.toPoly (T.MX m h) (shiftedL (opsM ks m) (SMX ks m W)
            (eSpX ks m (W.getD i (opsM ks (m + 1)).zero))) := fun u hu ↦ by
    have hu' : u < (E1MX ks m W).length := by rw [← length_PuMX]; exact Finset.mem_range.mp hu
    rw [T.toPoly_PuMX m h W hu', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, T.algebraMap_ratCastMX, C_mul]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm, length_PuMX]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [hc i (Finset.mem_range.mp hi), ← Finset.sum_mul, ← map_sum, ← map_sum]

end PuFacts

section StepSpec

variable (m : ℕ) (h : T.Tr (m + 1)) {a : Code (m + 1)} (hka : ks m = .exp a)
include hka
variable (hhom : ∀ j : ℤ, j ≠ 0 → ∀ e : T.F m, e ≠ 0 → e′ + (j : T.F m) * T.bX m h a * e ≠ 0)

include hhom in
set_option maxHeartbeats 3200000 in
/-- **Parametric elementary integration over an exponential level is sound and complete.** -/
theorem expElemStepX_spec (elem : List (Code (m + 1)) → List (List ℚ))
    (hel : ElemSolSpec (algebraMap Kc (T.F m)) (T.MX m h) (fun v ↦ HasElementaryIntegralIn (v : E))
      (fun v ↦ LiouvilleIn (T.F m) (v : E)) elem)
    (rde : Code (m + 1) → List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (hprde : ∀ f : Code (m + 1),
      RdeSpecK (algebraMap Kc (T.F m)) (T.MX m h) ((T.MX m h).sem f)′ (rde f)) :
    ElemSolSpec (algebraMap Kc (T.F (m + 1))) (T.MP (m + 1) h)
      (fun v ↦ HasElementaryIntegralIn (v : E)) (fun v ↦ LiouvilleIn (T.F (m + 1)) (v : E))
      (expElemStepX ks m a elem rde) := by
  classical
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
  have hinj := T.phi_injX m h
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  -- the loop, for any `W`
  have hloop : ∀ W : List (Code (m + 2)),
      ESound (T.MX m h) (PuMX ks m W) (T.AdmMX m h a (SMX ks m W)) 0
        (elemLoop (E1MX ks m W).length (fun i Bs ↦ solMX ks m a rde elem W i
          (coefCodes (opsM ks m) (cstN m) (PuMX ks m W) i Bs)) (topMX ks m W)
          ((List.range (E1MX ks m W).length).map (unitV (E1MX ks m W).length))) ∧
      EComplete (algebraMap Kc (T.F m)) (T.MX m h) (PuMX ks m W) (T.AdmCMX m h a (SMX ks m W))
        (E1MX ks m W).length 0
        (elemLoop (E1MX ks m W).length (fun i Bs ↦ solMX ks m a rde elem W i
          (coefCodes (opsM ks m) (cstN m) (PuMX ks m W) i Bs)) (topMX ks m W)
          ((List.range (E1MX ks m W).length).map (unitV (E1MX ks m W).length))) := by
    intro W
    have htop : ∀ u < (PuMX ks m W).length, ((PuMX ks m W).getD u []).length ≤ topMX ks m W :=
      fun u hu ↦ le_foldr_max _ _ (List.mem_map.mpr ⟨_, NestTower.getD_mem_of_lt _ _ hu, rfl⟩)
    refine elemLoop_stage (algebraMap Kc (T.F m)) (M := T.MX m h) (cst := cstN m) (PuMX ks m W)
      (T.sem_cstN m _) (T.AdmMX m h a (SMX ks m W)) (T.AdmCMX m h a (SMX ks m W)) (solMX ks m a rde elem W)
      (fun i ↦ T.solM_specX m h a elem hel rde hprde W i)
      (fun i s q v hv ↦ T.admM_linX m h a (SMX ks m W) i s q v hv) (fun q ↦ T.algebraMap_ratCastMX q)
      (E1MX ks m W).length (length_PuMX m W) _ _ ?_ ?_
    · intro β _ i hi
      rw [cvalQ_eq_zero (PuMX ks m W) (topMX ks m W) htop i hi]
      exact T.admM_zeroX m h a _ i
    · intro c hc _
      exact ⟨(List.range (E1MX ks m W).length).map fun i ↦ c.getD i 0,
        unit_span (E1MX ks m W).length c hc⟩
  refine ⟨fun W β hβ ↦ ?_, fun W c hc hL ↦ ?_⟩
  · -- soundness
    rw [expElemStep_eqX] at hβ
    split_ifs at hβ with hchk
    swap
    · simp at hβ
    obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hβ
    obtain ⟨hsq, hXS, hdat⟩ := T.lcm_dataMX m h hka W hchk
    have hadm : ∀ i, T.AdmMX m h a (SMX ks m W) i (cvalQ (T.MX m h) (PuMX ks m W) i δ) :=
      fun i ↦ (hloop W).1 δ hδ i (Nat.zero_le _)
    set n := W.length with hn
    set S := SMX ks m W with hS
    set Sv := GPoly.toPoly (T.MX m h) (lcmSMX ks m W) with hSv
    set vq : ℕ → ℚ := fun i ↦ (vcomb n δ (E1MX ks m W)).getD i 0 with hvq
    set Nq := ∑ i ∈ Finset.range n, C ((vq i : ℚ) : T.F m) *
      GPoly.toPoly (T.MX m h) ((numLMX ks m W).getD i []) with hNq
    set Rq := ∑ i ∈ Finset.range n, C ((vq i : ℚ) : T.F m) *
      GPoly.toPoly (T.MX m h) (GPoly.residuePoly (opsM ks m) (wkMX ks m)
        ((numLMX ks m W).getD i []) (lcmSMX ks m W)) with hRq
    set Pq := ∑ u ∈ Finset.range (PuMX ks m W).length, C ((δ.getD u 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.MX m h) ((PuMX ks m W).getD u []) with hPq
    set G := ∑ i ∈ Finset.range n, ((vq i : ℚ) : T.F (m + 1)) *
      (T.M1X m h).sem ((eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gn,
        (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gd) with hG
    have hφS : T.phi m Sv ≠ 0 := (map_ne_zero_iff _ hinj).mpr hsq.ne_zero
    have hXSφ : T.phi m (X ^ S) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
    -- the value
    have hA : sQ (T.MP (m + 1) h) (vcomb n δ (E1MX ks m W)) W =
        G′ + T.phi m Nq / T.phi m Sv + T.phi m Pq / T.phi m (X ^ S) := by
      rw [hPq, T.sum_PuM_QX m h W δ, hG, T.deriv_sum_ratCastMX, hNq, map_sum, map_sum, Finset.sum_div,
        Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, sQ]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [(hdat i (Finset.mem_range.mp hi)).1, map_mul, map_mul, T.phi_C_ratCastMX]
      simp only [hvq, σX]
      ring
    have hAE : ((sQ (T.MP (m + 1) h) (vcomb n δ (E1MX ks m W)) W : T.F (m + 1)) : E) =
        (G : E)′ + ((T.phi m Nq / T.phi m Sv : T.F (m + 1)) : E) +
          ((T.phi m Pq / T.phi m (X ^ S) : T.F (m + 1)) : E) := by
      rw [hA, IntermediateField.coe_add, IntermediateField.coe_add, coe_deriv]
    -- the logarithmic part
    have hlog : HasElementaryIntegralIn ((T.phi m Nq / T.phi m Sv : T.F (m + 1)) : E) := by
      have hst : aeval (T.ts m) Sv ≠ 0 := by
        rw [← T.coe_phi]
        exact fun h0 ↦ hφS (Subtype.ext h0)
      have hdeg : Nq.degree < Sv.degree :=
        NestTower.degree_sum_C_mul_lt n _ _ Sv hsq.ne_zero fun i hi ↦ (hdat i hi).2
      have hr : Sv ∣ Rq * (mapCoeffs Sv + (C 0 + C (T.bX m h a) * X) * derivative Sv) - Nq := by
        rw [C_0, zero_add, hRq, hNq, Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.dvd_sum fun i _ ↦ ?_
        have := (T.res_dataMX m h hka W hsq hXS ((numLMX ks m W).getD i [])).1
        rw [show ∀ a b c d : (T.F m)[X], a * b * c - a * d = a * (b * c - d) from
          fun _ _ _ _ ↦ by ring]
        exact dvd_mul_of_dvd_right this _
      have hT : Sv ∣ residueTest Rq Sv := by
        rw [hRq, residueTest_sum n _ (fun i ↦ T.deriv_ratCast _)]
        have h0 := T.sum_Tv_eq_zeroMX m h W δ
        rw [← sub_zero (∑ i ∈ Finset.range n, _), ← h0, ← Finset.sum_sub_distrib]
        refine Finset.dvd_sum fun i _ ↦ ?_
        rw [← mul_sub]
        exact dvd_mul_of_dvd_right (T.res_dataMX m h hka W hsq hXS _).2.1 _
      have ht' : (T.ts m)′ = algebraMap (T.F m) E 0 + algebraMap (T.F m) E (T.bX m h a) * T.ts m := by
        rw [map_zero, zero_add, T.deriv_ts_aeval m, T.wPoly_eq_bX m h hka, map_mul, aeval_C, aeval_X]
      have hts0 : T.ts m ≠ 0 := T.hts0 m a hka
      have hθ : logDeriv (T.ts m) = algebraMap (T.F m) E (T.bX m h a) := by
        unfold logDeriv
        rw [ht', map_zero, zero_add]
        field_simp
      rw [IntermediateField.coe_div, T.coe_phi, T.coe_phi]
      exact hasElementaryIntegralIn_of_residueTest (F := T.F m) (T.ts m) 0 (T.bX m h a) ht' (T.ts m)
        hts0 hθ Sv Nq Rq (PerfectField.separable_iff_squarefree.mpr hsq) hst hdeg hr hT
    -- the Laurent part
    have hlau : HasElementaryIntegralIn ((T.phi m Pq / T.phi m (X ^ S) : T.F (m + 1)) : E) := by
      refine T.laurent_elemX m h a hka Pq S fun i ↦ ?_
      have hc : Pq.coeff i = cvalQ (T.MX m h) (PuMX ks m W) i δ := by
        rw [hPq, finset_sum_coeff, cvalQ]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [coeff_C_mul]
      rw [hc]
      exact hadm i
    rw [hAE]
    exact ((hasElementaryIntegralIn_deriv _).add hlog).add hlau
  · -- completeness
    have hchk := T.lcmCheck_trueMX m h hka W
    rw [expElemStep_eqX, if_pos hchk]
    obtain ⟨hsq, hXS, hdat⟩ := T.lcm_dataMX m h hka W hchk
    set n := W.length with hn
    set S := SMX ks m W with hS
    set Sv := GPoly.toPoly (T.MX m h) (lcmSMX ks m W) with hSv
    set ac : ℕ → T.F m := fun i ↦ algebraMap Kc (T.F m) (c.getD i 0) with hac
    have hac' : ∀ i, (ac i)′ = 0 := fun i ↦ T.deriv_algebraMap_Kc _
    set Nv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly (T.MX m h) ((numLMX ks m W).getD i []) with hNv
    set Rv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly (T.MX m h) (GPoly.residuePoly (opsM ks m)
      (wkMX ks m) ((numLMX ks m W).getD i []) (lcmSMX ks m W)) with hRv
    set Tv : ℕ → (T.F m)[X] := fun i ↦
      GPoly.toPoly (T.MX m h) (ttCodeMX ks m W ((numLMX ks m W).getD i [])) with hTv
    set Nc := ∑ i ∈ Finset.range n, C (ac i) * Nv i with hNc
    set Rc := ∑ i ∈ Finset.range n, C (ac i) * Rv i with hRc
    set Pc := ∑ i ∈ Finset.range n, C (ac i) * GPoly.toPoly (T.MX m h)
      (shiftedL (opsM ks m) S (eSpX ks m (W.getD i (opsM ks (m + 1)).zero))) with hPc
    set G : T.F (m + 1) := ∑ i ∈ Finset.range n, algebraMap Kc (T.F (m + 1)) (c.getD i 0) *
      (T.M1X m h).sem ((eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gn,
        (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gd) with hG
    -- the value
    have hsum : sC (algebraMap Kc (T.F (m + 1))) (T.MP (m + 1) h) c W =
        G′ + T.phi m Nc / T.phi m Sv + T.phi m Pc / T.phi m (X ^ S) := by
      rw [hG, T.deriv_sum_KcMX, hNc, hPc, map_sum, map_sum, Finset.sum_div, Finset.sum_div,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, sC]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [(hdat i (Finset.mem_range.mp hi)).1, map_mul, map_mul, T.algebraMap_succ]
      simp only [hac, hNv, σX]
      ring
    have hdegN : Nc.degree < Sv.degree :=
      NestTower.degree_sum_C_mul_lt n _ _ Sv hsq.ne_zero fun i hi ↦ (hdat i hi).2
    have hr : Sv ∣ Rc * (mapCoeffs Sv + C (T.bX m h a) * X * derivative Sv) - Nc := by
      rw [hRc, hNc, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.dvd_sum fun i _ ↦ ?_
      have := (T.res_dataMX m h hka W hsq hXS ((numLMX ks m W).getD i [])).1
      rw [show ∀ a b c d : (T.F m)[X], a * b * c - a * d = a * (b * c - d) from
        fun _ _ _ _ ↦ by ring]
      exact dvd_mul_of_dvd_right this _
    rw [hsum] at hL
    obtain ⟨hT, hj, hPS⟩ := T.exp_liouville_splitX m h hka hhom G Nc Sv Rc Pc S hsq hXS hdegN hr hL
    -- the residue condition
    have hT0 : ∑ i ∈ Finset.range n, C (ac i) * Tv i = 0 := by
      refine eq_zero_of_dvd_of_degree_lt ?_ (NestTower.degree_sum_C_mul_lt n _ _ Sv hsq.ne_zero
        fun i _ ↦ (T.res_dataMX m h hka W hsq hXS _).2.2)
      have e : ∑ i ∈ Finset.range n, C (ac i) * Tv i = residueTest Rc Sv -
          ∑ i ∈ Finset.range n, C (ac i) * (residueTest (Rv i) Sv - Tv i) := by
        rw [hRc, residueTest_sum n ac hac', ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        ring
      rw [e]
      exact dvd_sub hT (Finset.dvd_sum fun i _ ↦
        dvd_mul_of_dvd_right (T.res_dataMX m h hka W hsq hXS _).2.1 _)
    -- the constant system at level `m + 1`
    set U := consys ks (m + 1) (resCodesMX ks m W) with hU
    have h0 : (List.zipWith (fun c v ↦ algebraMap Kc (T.F (m + 1)) c * (T.MP (m + 1) h).sem v)
        ((List.range (resCodesMX ks m W).length).map fun i ↦ c.getD i 0)
        (resCodesMX ks m W)).sum = 0 := by
      rw [NestTower.zipWith_sum_range _ 0 (opsM ks (m + 1)).zero _ _ (by simp)]
      have e : ∀ i ∈ Finset.range ((List.range (resCodesMX ks m W).length).map
          fun i ↦ c.getD i 0).length,
          algebraMap Kc (T.F (m + 1)) (((List.range (resCodesMX ks m W).length).map
            fun i ↦ c.getD i 0).getD i 0) *
            (T.MP (m + 1) h).sem ((resCodesMX ks m W).getD i (opsM ks (m + 1)).zero) =
          T.phi m (C (ac i) * Tv i) := fun i hi ↦ by
        have hi' : i < n := by
          have := Finset.mem_range.mp hi
          rwa [List.length_map, List.length_range, length_resCodesMX] at this
        rw [NestTower.getD_range_map (fun j ↦ c.getD j 0) 0 (by rw [length_resCodesMX]; exact hi'),
          getD_resCodesMX m W hi', map_mul, T.algebraMap_succ]
        congr 1
        change T.σX m h _ / T.σX m h [(opsM ks m).one] = _
        rw [T.σX_one, div_one]
      rw [Finset.sum_congr rfl e, List.length_map, List.length_range, length_resCodesMX, ← map_sum,
        hT0, map_zero]
    obtain ⟨β, hβl, hβ⟩ := T.consys_complete (m + 1) h (resCodesMX ks m W) _ (by simp) h0
    rw [← hU] at hβl hβ
    have hlE : (E1MX ks m W).length = U.length := length_E1MX m W
    have hβc : ∀ i < n, c.getD i 0 = ∑ u ∈ Finset.range (E1MX ks m W).length,
        β.getD u 0 * algebraMap ℚ Kc (((E1MX ks m W).getD u []).getD i 0) := fun i hi ↦ by
      have := hβ i
      rw [NestTower.getD_range_map (fun j ↦ c.getD j 0) 0 (by rw [length_resCodesMX]; exact hi),
        NestTower.zipWith_sum_range _ 0 [] _ _ hβl, hβl] at this
      rw [this, hlE]
      refine Finset.sum_congr rfl fun u hu ↦ ?_
      rw [getD_E1MX m W (by rw [hlE]; exact Finset.mem_range.mp hu) hi]
    -- the Laurent part in terms of the basis
    have hPcb : Pc = ∑ u ∈ Finset.range (PuMX ks m W).length,
        C (algebraMap Kc (T.F m) (β.getD u 0)) * GPoly.toPoly (T.MX m h) ((PuMX ks m W).getD u []) :=
      (T.sum_PuM_KX m h W β c hβc).symm
    have hadm : ∀ i, 0 ≤ i → T.AdmCMX m h a S i
        (cvalC (algebraMap Kc (T.F m)) (T.MX m h) (PuMX ks m W) i β) := by
      intro i _
      have hcv : cvalC (algebraMap Kc (T.F m)) (T.MX m h) (PuMX ks m W) i β = Pc.coeff i := by
        rw [hPcb, finset_sum_coeff, cvalC]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [coeff_C_mul]
      rw [hcv]
      unfold AdmCMX
      split_ifs with hiS
      · subst hiS; exact hPS
      · exact hj i hiS
    obtain ⟨γ, hγ⟩ := (hloop W).2 β (fun u hu ↦ List.getD_eq_default _ _ (by rw [hβl, ← hlE]; exact hu))
      hadm
    -- recombine
    set pe := elemLoop (E1MX ks m W).length (fun i Bs ↦ solMX ks m a rde elem W i
      (coefCodes (opsM ks m) (cstN m) (PuMX ks m W) i Bs)) (topMX ks m W)
      ((List.range (E1MX ks m W).length).map (unitV (E1MX ks m W).length)) with hpe
    refine ⟨γ, fun i ↦ ?_⟩
    rw [List.length_map]
    have e : ∀ k ∈ Finset.range pe.length, γ.getD k 0 * algebraMap ℚ Kc
        (((pe.map fun δ ↦ vcomb n δ (E1MX ks m W)).getD k []).getD i 0) =
        γ.getD k 0 * algebraMap ℚ Kc ((vcomb n (pe.getD k []) (E1MX ks m W)).getD i 0) :=
      fun k hk ↦ by rw [NestTower.getD_map' _ _ [] [] (Finset.mem_range.mp hk)]
    rw [Finset.sum_congr rfl e]
    by_cases hi : i < n
    · have := recombine n (E1MX ks m W).length pe.length
        (fun u i ↦ ((E1MX ks m W).getD u []).getD i 0) (fun j u ↦ (pe.getD j []).getD u 0)
        (fun i ↦ c.getD i 0) (fun u ↦ β.getD u 0) (fun j ↦ γ.getD j 0) hβc
        (fun u _ ↦ hγ u) i hi
      rw [this]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [getD_vcomb, if_pos hi]
    · rw [hc i (by omega)]
      symm
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [getD_vcomb, if_neg hi, map_zero, mul_zero]

end StepSpec

section Induction

/-- Every element of `Kc(x)` given by a rational code has an elementary integral. -/
theorem rational_inMX (q : GFrac ℚ) : HasElementaryIntegralIn (PrimN.evx Kc T.x q) := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
  by_cases hq : (CPoly.toPoly q.2).map (algebraMap ℚ Kc) = 0
  · have : PrimN.evx Kc T.x q = (0 : E)′ := by simp [PrimN.evx, hq]
    rw [this]
    exact hasElementaryIntegralIn_deriv 0
  intro E' _ _ _ _ _
  let _ : Algebra Kc E' := ((algebraMap E E').comp (algebraMap Kc E)).toAlgebra
  have hDA : DifferentialAlgebra Kc E' :=
    ⟨fun a ↦ by
      change (algebraMap E E' (algebraMap Kc E a))′ = algebraMap E E' (algebraMap Kc E a′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  have hx : (algebraMap E E' T.x)′ = 1 := by rw [deriv_algebraMap, T.hx, map_one]
  have haev : ∀ P : Kc[X], algebraMap E E' (aeval T.x P) = aeval (algebraMap E E' T.x) P :=
    fun P ↦ by
      rw [aeval_def, aeval_def, hom_eval₂]
      rfl
  have := hasElementaryIntegral_rational_in T.hC (algebraMap E E' T.x) hx
    ((CPoly.toPoly q.1).map (algebraMap ℚ Kc)) _ hq 0
  rw [map_zero, zero_add] at this
  rw [PrimN.evx, map_div₀, haev, haev]
  exact this

/-- **The base `Kc(x)`**: everything is elementary. -/
theorem paramElem0X_spec (h : T.Tr 0) :
    ElemSolSpec (algebraMap Kc (T.F 0)) (T.MP 0 h) (fun v ↦ HasElementaryIntegralIn (v : E))
      (fun v ↦ LiouvilleIn (T.F 0) (v : E)) (fun W ↦ (List.range W.length).map (unitV W.length)) := by
  refine ⟨fun W β _ ↦ ?_, fun W c hc _ ↦ ?_⟩
  · have e : sQ (T.MP 0 h) β W = (T.MP 0 h).sem (lcombCode (opsM ks 0) (cstN 0) β W) := by
      rw [sem_lcombCode (T.MP 0 h) (cstN 0) (T.sem_cstN 0 h),
        zipWith_sum_getD (fun (q : ℚ) (a : Code 1) ↦ ((q : ℚ) : T.F 0) * (T.MP 0 h).sem a) 0
          (opsM ks 0).zero (by simp)]
      rfl
    rw [e, T.sem_MP]
    exact T.rational_inMX _
  · exact ⟨(List.range W.length).map fun i ↦ c.getD i 0, unit_span W.length c hc⟩

end Induction

end NestMTower

end Tower.NestM
