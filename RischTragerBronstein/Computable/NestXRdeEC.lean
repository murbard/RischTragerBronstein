import RischTragerBronstein.Computable.NestXRdeEK

/-!
# The Risch equation over an exponential level of a mixed tower: completeness

The balanced case (values at infinity of `h` and of the logarithmic part), the degree bound
`peNbE` (through `pldX_spec` and `ratVal`), the coefficient loop (`rdeLoop_stageX` with
`expShape`), the final constant system; `prdeExpX_spec`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP Tower.NestX CPoly

/-! ### The balanced case, generically -/

section BalGenericXE

variable {F K : Type*} [Field F] [CharZero F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

variable {b : F} (hDe : ∀ P : F[X], P′ = implicitDeriv (C b * X) P)
  (hhom : ∀ r : ℕ, r ≠ 0 → ∀ e : F, e ≠ 0 → e′ + r * b * e ≠ 0)

include hDe hhom in
/-- **The balanced case**: if `F₁ / F₂ = h′ + L - Q′ / Q` (`Q` monic, `L` with value `ℓ` at
infinity) with `deg F₁ = deg F₂`, then `h` has a value at infinity and
`lc F₁ / lc F₂ = h(∞)′ + ℓ - deg Q · b`. -/
lemma bal_coreXE (hn hd Q F1 F2 : F[X]) (Lg : K) (ℓ : F) (hL : InfVal Lg ℓ) (hd0 : hd ≠ 0)
    (hQ : Q.Monic) (hF2 : F2 ≠ 0) (hdeg : F1.natDegree = F2.natDegree)
    (hF : φ F1 / φ F2 = (φ hn / φ hd)′ + Lg - (φ Q)′ / φ Q) :
    hn.natDegree ≤ hd.natDegree ∧ F1.leadingCoeff / F2.leadingCoeff =
      (hn.coeff hd.natDegree / hd.leadingCoeff)′ + ℓ - Q.natDegree * b := by
  have hlog := infVal_logDeriv (K := K) hDe Q hQ.ne_zero
  rw [hQ.leadingCoeff, Derivation.map_one_eq_zero, zero_div, add_zero] at hlog
  have hF' : InfVal (φ F1 / φ F2) (F1.leadingCoeff / F2.leadingCoeff) := by
    have := infVal_of (K := K) F1 F2 hF2 hdeg.le
    rwa [← hdeg] at this
  have hrest := infVal_sub hL hlog
  have hle : hn.natDegree ≤ hd.natDegree := by
    by_contra hlt
    push_neg at hlt
    have hn0 : hn ≠ 0 := by rintro rfl; simp at hlt
    have hr : hn.natDegree - hd.natDegree ≠ 0 := by omega
    have hpos : PosDeg F (φ hn / φ hd) (hn.natDegree - hd.natDegree) :=
      ⟨hn, hd, hd0, hn0, by omega, rfl⟩
    have h2 := posDeg_add hr (posDeg_deriv hDe hhom hr hpos) hrest
    rw [← add_sub_assoc, ← hF] at h2
    have := natDegree_lt_of_posDeg hr h2 hF2 rfl
    omega
  refine ⟨hle, ?_⟩
  have h1 := infVal_add (infVal_deriv hDe (infVal_of (K := K) hn hd hd0 hle)) hrest
  rw [← add_sub_assoc, ← hF] at h1
  rw [infVal_unique hF' h1]
  ring

end BalGenericXE

/-! ### The degree bound `peNbE` -/

section PeNbE

variable {α : Type} (O : COps α)

lemma peNbE_geXE (pl sd : Option ℚ) (A B : GPoly α) (R dDk N : ℕ)
    (h : peNbE O pl sd A B R dDk = some N) :
    R ≤ N + (if (!GPoly.isZero O B && decide (degG O A < degG O B)) = true then degG O B
      else degG O A) := by
  unfold peNbE at h
  simp only at h
  by_cases hz : GPoly.isZero O B = true
  · rw [if_pos hz] at h
    cases h
    simp [hz]
    omega
  · rw [if_neg hz] at h
    have hz' : GPoly.isZero O B = false := by simpa using hz
    by_cases hlt : degG O A < degG O B
    · rw [if_pos hlt] at h
      split_ifs at h with hle
      cases h
      simp [hz', hlt]
      omega
    · rw [if_neg hlt] at h
      simp only [hz', hlt, Bool.not_false, decide_false, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte]
      split_ifs at h with hlt2
      · cases h; omega
      · split at h
        · split at h <;> cases h <;> omega
        · cases h; omega

lemma peNbE_balXE (pl sd : Option ℚ) (A B : GPoly α) (R dDk : ℕ)
    (hz : ¬GPoly.isZero O B = true) (h1 : ¬degG O A < degG O B) (h2 : ¬degG O B < degG O A) :
    ∃ N, peNbE O pl sd A B R dDk = some N ∧ R - degG O A ≤ N ∧
      ∀ q s n, pl = some q → sd = some s → natOfQ (q - s + (dDk : ℚ)) = some n → n ≤ N := by
  unfold peNbE
  simp only [hz, h1, h2, if_false, Bool.false_eq_true]
  rcases pl with _ | q <;> rcases sd with _ | s
  · exact ⟨_, rfl, le_rfl, fun q s n hq _ _ ↦ by cases hq⟩
  · exact ⟨_, rfl, le_rfl, fun q s n hq _ _ ↦ by cases hq⟩
  · exact ⟨_, rfl, le_rfl, fun q s n _ hs _ ↦ by cases hs⟩
  · simp only
    rcases hn : natOfQ (q - s + (dDk : ℚ)) with _ | n
    · refine ⟨_, rfl, le_rfl, fun q' s' n' hq hs hn' ↦ ?_⟩
      cases hq; cases hs; rw [hn] at hn'; cases hn'
    · refine ⟨_, rfl, le_max_left _ _, fun q' s' n' hq hs hn' ↦ ?_⟩
      cases hq; cases hs; rw [hn] at hn'; cases hn'; exact le_max_right _ _

end PeNbE

/-! ### Sums over filtered lists -/

lemma sum_filter_map_XE {β γ : Type*} [AddCommMonoid γ] (p : β → Bool) (g : β → γ) (d : β) :
    ∀ l : List β, ((l.filter p).map g).sum =
      ∑ i ∈ Finset.range l.length, if p (l.getD i d) = true then g (l.getD i d) else 0
  | [] => by simp
  | x :: l => by
    rw [List.length_cons, Finset.sum_range_succ', List.filter_cons]
    have ih := sum_filter_map_XE p g d l
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    split_ifs with hx
    · rw [List.map_cons, List.sum_cons, ih, add_comm]
    · rw [ih, add_zero]

namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : (m : ℕ) → KindN m}
variable (T : NestMTower Kc E ks)

section Values

variable (m : ℕ) (h : T.Tr (m + 1))

/-- The value of `∑ cⱼ deg wⱼ`. -/
lemma sem_sumDegXE (logs : List (LgXE m)) (d : LgXE m) (κ : ℕ → Kc)
    (hκ : ∀ i < logs.length,
      (T.M1X m h).sem (logs.getD i d).1 = algebraMap Kc (T.F (m + 1)) (κ i)) :
    (T.MX m h).sem (sumDegXE ks m (logsCXE (opsM ks m) logs)) = ∑ i ∈ Finset.range logs.length,
      algebraMap Kc (T.F m) (κ i) * (((T.NwXE m h (logs.getD i d)).natDegree : T.F m) -
        (T.DwXE m h (logs.getD i d)).natDegree) := by
  unfold sumDegXE logsCXE
  rw [List.foldr_map]
  have := sem_foldr_filter_XE (T.MX m h) (cstN m) (T.sem_cstX m h)
    (fun cw : LgXE m ↦ !GPoly.isZero (opsM ks m) cw.2.1 && !GPoly.isZero (opsM ks m) cw.2.2)
    (fun cw ↦ lcC (opsM ks m) cw.1) (fun cw ↦ (degZ (opsM ks m) cw.2 : ℚ)) d logs
  simp only at this ⊢
  rw [this]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hnzd : nzXE (opsM ks m) (logs.getD i d) = (!GPoly.isZero (opsM ks m) (logs.getD i d).2.1 &&
      !GPoly.isZero (opsM ks m) (logs.getD i d).2.2) := rfl
  unfold NwXE DwXE
  rw [hnzd]
  split_ifs with hnz
  · rw [T.sem_lcC_constXE m h _ (κ i) (hκ i (Finset.mem_range.mp hi)), degZ,
      degG_eq (T.MX m h), degG_eq (T.MX m h)]
    push_cast
    ring
  · simp

/-- The value of the logarithmic part at infinity, `∑ cⱼ lc(wⱼ)′ / lc(wⱼ)`. -/
lemma logSumV_logsLXE (logs : List (LgXE m)) (d : LgXE m) (κ : ℕ → Kc)
    (hκ : ∀ i < logs.length,
      (T.M1X m h).sem (logs.getD i d).1 = algebraMap Kc (T.F (m + 1)) (κ i)) :
    logSumV (T.MX m h) ((logsCXE (opsM ks m) logs).map fun cw ↦ (cw.1, lcC (opsM ks m) cw.2)) =
      ∑ i ∈ Finset.range logs.length, algebraMap Kc (T.F m) (κ i) *
        (logDeriv (T.NwXE m h (logs.getD i d)).leadingCoeff -
          logDeriv (T.DwXE m h (logs.getD i d)).leadingCoeff) := by
  unfold logSumV logsCXE
  rw [List.map_map, List.map_map]
  rw [sum_filter_map_XE _ _ d]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hnzd : nzXE (opsM ks m) (logs.getD i d) = (!GPoly.isZero (opsM ks m) (logs.getD i d).2.1 &&
      !GPoly.isZero (opsM ks m) (logs.getD i d).2.2) := rfl
  unfold NwXE DwXE
  rw [hnzd]
  split_ifs with hnz
  · obtain ⟨hn0, hd0⟩ := (T.nz_iffXE m h _).mp hnz
    simp only [Function.comp]
    rw [T.sem_lcC_constXE m h _ (κ i) (hκ i (Finset.mem_range.mp hi)), sem_lcC_XE,
      logDeriv_div _ _ (leadingCoeff_ne_zero.mpr hn0) (leadingCoeff_ne_zero.mpr hd0)]
  · simp [logDeriv]

/-- The value of the balanced lower coefficient `⟨h(∞) + (∑ cⱼ deg wⱼ - deg Q) a, lc logs⟩`. -/
lemma sem_fCode_balXE (a : Code (m + 1)) (hc : PrXE m) (logs : List (LgXE m)) (d : LgXE m)
    (κ : ℕ → Kc) (hκ : ∀ i < logs.length,
      (T.M1X m h).sem (logs.getD i d).1 = algebraMap Kc (T.F (m + 1)) (κ i)) (dQ : ℕ) :
    (T.MX m h).sem (fCode (opsM ks m) ⟨(opsM ks m).add (peHinf (opsM ks m) hc)
      ((opsM ks m).mul ((opsM ks m).add (sumDegXE ks m (logsCXE (opsM ks m) logs))
        (cstN m (-((dQ : ℕ) : ℚ)))) a),
      (logsCXE (opsM ks m) logs).map fun cw ↦ (cw.1, lcC (opsM ks m) cw.2)⟩) =
      ((T.MX m h).sem (peHinf (opsM ks m) hc))′ +
        ((T.MX m h).sem (sumDegXE ks m (logsCXE (opsM ks m) logs)) - dQ) * ((T.MX m h).sem a)′ +
        ∑ i ∈ Finset.range logs.length, algebraMap Kc (T.F m) (κ i) *
          (logDeriv (T.NwXE m h (logs.getD i d)).leadingCoeff -
            logDeriv (T.DwXE m h (logs.getD i d)).leadingCoeff) := by
  rw [sem_fCode, T.logSumV_logsLXE m h logs d κ hκ]
  simp only
  rw [(T.MX m h).sem_add, (T.MX m h).sem_mul, (T.MX m h).sem_add, T.sem_cstX m h,
    T.sem_sumDegXE m h logs d κ hκ]
  have hK0 : ∀ c : Kc, (algebraMap Kc (T.F m) c)′ = 0 := fun c ↦ T.deriv_algebraMap_Kc c
  have hsd : (∑ i ∈ Finset.range logs.length, algebraMap Kc (T.F m) (κ i) *
      (((T.NwXE m h (logs.getD i d)).natDegree : T.F m) -
        (T.DwXE m h (logs.getD i d)).natDegree))′ = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [Derivation.leibniz, hK0, smul_zero, add_zero, smul_eq_mul, map_sub,
      show (((T.NwXE m h (logs.getD i d)).natDegree : T.F m))′ = 0 by
        simpa using deriv_ratCastK (K := T.F m) ((T.NwXE m h (logs.getD i d)).natDegree : ℚ),
      show (((T.DwXE m h (logs.getD i d)).natDegree : T.F m))′ = 0 by
        simpa using deriv_ratCastK (K := T.F m) ((T.DwXE m h (logs.getD i d)).natDegree : ℚ),
      sub_zero, mul_zero]
  have hdQ : (((-((dQ : ℕ) : ℚ)) : ℚ) : T.F m)′ = 0 := deriv_ratCastK _
  simp only [map_add, Derivation.leibniz, hsd, hdQ, smul_eq_mul, zero_add, mul_zero, add_zero]
  push_cast
  ring

end Values

section Bal

variable (m : ℕ) (hM : T.MixHyp (m + 1)) {a : Code (m + 1)} (hk : ks m = .exp a)

include hk in
set_option maxHeartbeats 3200000 in
/-- **The balanced case at an exponential level**: `h` has a value at infinity and
`lc F₁ / lc F₂ = h(∞)′ + ∑ cⱼ ((deg Nⱼ - deg Dⱼ) b + lc(Nⱼ)′ / lc(Nⱼ) - lc(Dⱼ)′ / lc(Dⱼ)) - deg Q · b`. -/
theorem pe_balXE (fc hc : PrXE m) (hhc : GPoly.toPoly (T.MX m hM.tr) hc.2 ≠ 0)
    (logs : List (LgXE m)) (d : LgXE m) (κ : ℕ → Kc)
    (hκ : ∀ i < logs.length,
      (T.M1X m hM.tr).sem (logs.getD i d).1 = algebraMap Kc (T.F (m + 1)) (κ i))
    (hfc : (T.M1X m hM.tr).sem fc = ((T.M1X m hM.tr).sem hc)′ + logSumV (T.M1X m hM.tr) logs)
    (Q : GPoly (Code (m + 1))) (hQ : (GPoly.toPoly (T.MX m hM.tr) Q).Monic)
    (hdeg : (GPoly.toPoly (T.MX m hM.tr) (peFX (opsM ks m) ((opsM ks m).monomial
        (wK (opsM ks m) (ks m))) fc Q).1).natDegree =
      (GPoly.toPoly (T.MX m hM.tr) (peFX (opsM ks m) ((opsM ks m).monomial
        (wK (opsM ks m) (ks m))) fc Q).2).natDegree) :
    (GPoly.toPoly (T.MX m hM.tr) hc.1).natDegree ≤ (GPoly.toPoly (T.MX m hM.tr) hc.2).natDegree ∧
      (GPoly.toPoly (T.MX m hM.tr) (peFX (opsM ks m) ((opsM ks m).monomial
          (wK (opsM ks m) (ks m))) fc Q).1).leadingCoeff /
        (GPoly.toPoly (T.MX m hM.tr) (peFX (opsM ks m) ((opsM ks m).monomial
          (wK (opsM ks m) (ks m))) fc Q).2).leadingCoeff =
      ((GPoly.toPoly (T.MX m hM.tr) hc.1).coeff (GPoly.toPoly (T.MX m hM.tr) hc.2).natDegree /
        (GPoly.toPoly (T.MX m hM.tr) hc.2).leadingCoeff)′ +
      ∑ i ∈ Finset.range logs.length, algebraMap Kc (T.F m) (κ i) *
        ((((T.NwXE m hM.tr (logs.getD i d)).natDegree : T.F m) -
          (T.DwXE m hM.tr (logs.getD i d)).natDegree) * T.bX m hM.tr a +
          ((T.NwXE m hM.tr (logs.getD i d)).leadingCoeff)′ /
            (T.NwXE m hM.tr (logs.getD i d)).leadingCoeff -
          ((T.DwXE m hM.tr (logs.getD i d)).leadingCoeff)′ /
            (T.DwXE m hM.tr (logs.getD i d)).leadingCoeff) -
      (GPoly.toPoly (T.MX m hM.tr) Q).natDegree * T.bX m hM.tr a := by
  classical
  set h := hM.tr with hh
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  set O := opsM ks m with hO
  obtain ⟨F, hF⟩ : ∃ F, F = peFX O (O.monomial (wK O (ks m))) fc Q := ⟨_, rfl⟩
  have hsF := T.sem_peFX_XE m h fc Q
  rw [← hF] at hsF hdeg ⊢
  have hF2 : GPoly.toPoly (T.MX m h) F.2 ≠ 0 := by
    have := T.peFX_ne_XE m h fc Q
    rw [← hF] at this
    intro h0; exact this (by rw [σX, h0, map_zero])
  rw [hfc, T.logSumV_eqXE m h logs d κ hκ, T.semX] at hsF
  -- the setting `K = F m (t)`
  set t := T.ts m with ht
  have hw := T.deriv_ts_aeval m
  let _ := algebraAdjoinSimple (F := T.F m) t
  let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  let _ : Differential (T.F m)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮t⟯ := isFractionRing_adjoin_simple _ htr
  have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮t⟯ := differentialAlgebra_adjoin_simple _ _ hw
  have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ P : (T.F m)⟮t⟯) : E) = aeval t P :=
    algebraMap_adjoinSimple _
  have hDe : ∀ P : (T.F m)[X], P′ = implicitDeriv (C (T.bX m h a) * X) P := fun P ↦ by
    change implicitDeriv (T.wPoly m) P = _
    rw [T.wPoly_eq_bX m h hk]
  set φK := algebraMap (T.F m)[X] (T.F m)⟮t⟯ with hφK
  let toK : T.F (m + 1) →+* (T.F m)⟮t⟯ :=
    { toFun := fun z ↦ ⟨(z : E), (T.mem_F_succ).mp z.2⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have htoK_phi : ∀ P, toK (T.phi m P) = φK P := fun P ↦ Subtype.ext (by
    change ((T.phi m P : T.F (m + 1)) : E) = _
    rw [T.coe_phi, hφK, hcoe])
  have htoK_der : ∀ z, toK z′ = (toK z)′ := fun z ↦ rfl
  have htoK_ld : ∀ z, toK (logDeriv z) = logDeriv (toK z) := by
    intro z; unfold logDeriv; rw [map_div₀, htoK_der]
  have hhom : ∀ r : ℕ, r ≠ 0 → ∀ e : T.F m, e ≠ 0 → e′ + r * T.bX m h a * e ≠ 0 := by
    intro r hr e he
    have := hM.homX T (Nat.lt_succ_self m) hk h r (by exact_mod_cast hr) e he
    exact_mod_cast this
  have hKeq := congrArg toK hsF
  simp only [map_div₀, map_sub, map_add, map_sum, map_mul, htoK_der, htoK_ld, htoK_phi] at hKeq
  have hL := infVal_logSum hDe (K := (T.F m)⟮t⟯) (Finset.range logs.length)
    (fun i ↦ algebraMap Kc (T.F m) (κ i)) (fun i ↦ T.NwXE m h (logs.getD i d))
    (fun i ↦ T.DwXE m h (logs.getD i d)) (fun i _ ↦ T.NwD_ne_XE m h _)
  exact bal_coreXE hDe hhom _ _ _ _ _ _ _ hL hhc hQ hF2 hdeg (by rw [hKeq])

include hk in
set_option maxHeartbeats 3200000 in
/-- **The balanced case**: `h` has a value at infinity and the balanced lower coefficient has
value `lc B / lc A`. -/
theorem pe_bal_leadXE (fc hc : PrXE m) (hhc : GPoly.toPoly (T.MX m hM.tr) hc.2 ≠ 0)
    (logs : List (LgXE m)) (d : LgXE m) (κ : ℕ → Kc)
    (hκ : ∀ i < logs.length,
      (T.M1X m hM.tr).sem (logs.getD i d).1 = algebraMap Kc (T.F (m + 1)) (κ i))
    (hfc : (T.M1X m hM.tr).sem fc = ((T.M1X m hM.tr).sem hc)′ + logSumV (T.M1X m hM.tr) logs)
    (Q : GPoly (Code (m + 1))) (hQ : (GPoly.toPoly (T.MX m hM.tr) Q).Monic) (dQ : ℕ)
    (hdQ : (GPoly.toPoly (T.MX m hM.tr) Q).natDegree = dQ) (Rs : List (PrXE m))
    (hP : GPoly.toPoly (T.MX m hM.tr) (prodD (GPoly.mul (opsM ks m)) [(opsM ks m).one] Rs) ≠ 0)
    (hB0 : GPoly.toPoly (T.MX m hM.tr) (peB (opsM ks m) (peFX (opsM ks m) ((opsM ks m).monomial
      (wK (opsM ks m) (ks m))) fc Q) Rs) ≠ 0)
    (hdeg : (GPoly.toPoly (T.MX m hM.tr) (peA (opsM ks m) (peFX (opsM ks m) ((opsM ks m).monomial
        (wK (opsM ks m) (ks m))) fc Q) Rs)).natDegree =
      (GPoly.toPoly (T.MX m hM.tr) (peB (opsM ks m) (peFX (opsM ks m) ((opsM ks m).monomial
        (wK (opsM ks m) (ks m))) fc Q) Rs)).natDegree) :
    (GPoly.toPoly (T.MX m hM.tr) hc.1).natDegree ≤ (GPoly.toPoly (T.MX m hM.tr) hc.2).natDegree ∧
      (T.MX m hM.tr).sem (fCode (opsM ks m) ⟨(opsM ks m).add (peHinf (opsM ks m) hc)
        ((opsM ks m).mul ((opsM ks m).add (sumDegXE ks m (logsCXE (opsM ks m) logs))
          (cstN m (-((dQ : ℕ) : ℚ)))) a),
        (logsCXE (opsM ks m) logs).map fun cw ↦ (cw.1, lcC (opsM ks m) cw.2)⟩) =
      (GPoly.toPoly (T.MX m hM.tr) (peB (opsM ks m) (peFX (opsM ks m) ((opsM ks m).monomial
        (wK (opsM ks m) (ks m))) fc Q) Rs)).leadingCoeff /
      (GPoly.toPoly (T.MX m hM.tr) (peA (opsM ks m) (peFX (opsM ks m) ((opsM ks m).monomial
        (wK (opsM ks m) (ks m))) fc Q) Rs)).leadingCoeff := by
  set h := hM.tr with hh
  set O := opsM ks m with hO
  obtain ⟨F, hF⟩ : ∃ F, F = peFX O (O.monomial (wK O (ks m))) fc Q := ⟨_, rfl⟩
  obtain ⟨P, hPd⟩ : ∃ P, P = prodD (GPoly.mul O) [O.one] Rs := ⟨_, rfl⟩
  rw [← hF] at hB0 hdeg ⊢
  rw [← hPd] at hP
  have hA : GPoly.toPoly (T.MX m h) (peA O F Rs) =
      GPoly.toPoly (T.MX m h) F.2 * GPoly.toPoly (T.MX m h) P := by
    rw [peA, GPoly.toPoly_mul, hPd]
  have hB : GPoly.toPoly (T.MX m h) (peB O F Rs) =
      GPoly.toPoly (T.MX m h) F.1 * GPoly.toPoly (T.MX m h) P := by
    rw [peB, GPoly.toPoly_mul, hPd]
  have hF2 : GPoly.toPoly (T.MX m h) F.2 ≠ 0 := by
    have := T.peFX_ne_XE m h fc Q
    rw [← hF] at this
    intro h0; exact this (by rw [σX, h0, map_zero])
  have hF1 : GPoly.toPoly (T.MX m h) F.1 ≠ 0 := fun h0 ↦ hB0 (by rw [hB, h0, zero_mul])
  rw [hA, hB, natDegree_mul hF2 hP, natDegree_mul hF1 hP] at hdeg
  have hdeg' : (GPoly.toPoly (T.MX m h) F.1).natDegree = (GPoly.toPoly (T.MX m h) F.2).natDegree := by
    omega
  rw [hF] at hdeg'
  obtain ⟨hle, hlc⟩ := T.pe_balXE m hM hk fc hc hhc logs d κ hκ hfc Q hQ hdeg'
  rw [← hF] at hlc
  refine ⟨hle, ?_⟩
  rw [T.sem_fCode_balXE m h a hc logs d κ hκ dQ, sem_peHinf (T.MX m h) hc hhc hle,
    T.sem_sumDegXE m h logs d κ hκ, hA, hB, leadingCoeff_mul, leadingCoeff_mul,
    mul_div_mul_right _ _ (leadingCoeff_ne_zero.mpr hP), hlc, hdQ]
  simp only [logDeriv]
  have e1 : ∀ (u v : ℕ → T.F m) (w : T.F m), ∑ i ∈ Finset.range logs.length,
      algebraMap Kc (T.F m) (κ i) * (u i * w + v i) = (∑ i ∈ Finset.range logs.length,
        algebraMap Kc (T.F m) (κ i) * u i) * w + ∑ i ∈ Finset.range logs.length,
          algebraMap Kc (T.F m) (κ i) * v i := by
    intro u v w
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  simp only [add_sub_assoc] at e1 ⊢
  rw [e1]
  rw [show T.bX m hM.tr a = ((T.MX m h).sem a)′ from rfl]
  ring

include hk in
set_option maxHeartbeats 6400000 in
/-- **The degree bound** `peNbE`: `deg Y ≤ N`, or `Y = 0` when there is no bound. -/
theorem pe_NbXE (hc2 : ∀ u ∈ consys ks m ((opsM ks m).deriv a :: gensD ks m), u.getD 0 0 = 0)
    (fc hc : PrXE m) (hhc : GPoly.toPoly (T.MX m hM.tr) hc.2 ≠ 0)
    (logs : List (LgXE m)) (d : LgXE m) (κ : ℕ → Kc)
    (hκ : ∀ i < logs.length,
      (T.M1X m hM.tr).sem (logs.getD i d).1 = algebraMap Kc (T.F (m + 1)) (κ i))
    (hfc : (T.M1X m hM.tr).sem fc = ((T.M1X m hM.tr).sem hc)′ + logSumV (T.M1X m hM.tr) logs)
    (Q : GPoly (Code (m + 1))) (hQ : (GPoly.toPoly (T.MX m hM.tr) Q).Monic) (dQ : ℕ)
    (hdQ : (GPoly.toPoly (T.MX m hM.tr) Q).natDegree = dQ) (Rs : List (PrXE m))
    (hP : GPoly.toPoly (T.MX m hM.tr) (prodD (GPoly.mul (opsM ks m)) [(opsM ks m).one] Rs) ≠ 0)
    (Y r : (T.F m)[X]) (R : ℕ) (hr : r.natDegree ≤ R)
    (heq : GPoly.toPoly (T.MX m hM.tr) (peA (opsM ks m) (peFX (opsM ks m) ((opsM ks m).monomial
        (wK (opsM ks m) (ks m))) fc Q) Rs) * implicitDeriv (C (T.bX m hM.tr a) * X) Y +
      GPoly.toPoly (T.MX m hM.tr) (peB (opsM ks m) (peFX (opsM ks m) ((opsM ks m).monomial
        (wK (opsM ks m) (ks m))) fc Q) Rs) * Y = r) :
    (∀ N, peNbE (opsM ks m) (pldX ks m (peHinf (opsM ks m) hc) a)
        (ratVal ks m (sumDegXE ks m (logsCXE (opsM ks m) logs)))
        (peA (opsM ks m) (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q) Rs)
        (peB (opsM ks m) (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q) Rs)
        R dQ = some N → Y.natDegree ≤ N) ∧
      (peNbE (opsM ks m) (pldX ks m (peHinf (opsM ks m) hc) a)
        (ratVal ks m (sumDegXE ks m (logsCXE (opsM ks m) logs)))
        (peA (opsM ks m) (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q) Rs)
        (peB (opsM ks m) (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q) Rs)
        R dQ = none → Y = 0) := by
  classical
  set h := hM.tr with hh
  set O := opsM ks m with hO
  have hbal := T.pe_bal_leadXE m hM hk fc hc hhc logs d κ hκ hfc Q hQ dQ hdQ Rs hP
  have hhom : ∀ r : ℕ, r ≠ 0 → ∀ e : T.F m, e ≠ 0 → e′ + r * T.bX m h a * e ≠ 0 := by
    intro r hr e he
    have := hM.homX T (Nat.lt_succ_self m) hk h r (by exact_mod_cast hr) e he
    exact_mod_cast this
  have hA0 : GPoly.toPoly (T.MX m h) (peA O (peFX O (O.monomial (wK O (ks m))) fc Q) Rs) ≠ 0 := by
    rw [peA, GPoly.toPoly_mul]
    refine mul_ne_zero ?_ hP
    have := T.peFX_ne_XE m h fc Q
    intro h0; exact this (by rw [σX, h0, map_zero])
  obtain ⟨A, hAd⟩ : ∃ A, A = peA O (peFX O (O.monomial (wK O (ks m))) fc Q) Rs := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = peB O (peFX O (O.monomial (wK O (ks m))) fc Q) Rs := ⟨_, rfl⟩
  rw [← hAd, ← hBd] at heq hbal ⊢
  rw [← hAd] at hA0
  obtain ⟨pl, hpl⟩ : ∃ pl, pl = pldX ks m (peHinf O hc) a := ⟨_, rfl⟩
  obtain ⟨sd, hsd⟩ : ∃ sd, sd = ratVal ks m (sumDegXE ks m (logsCXE O logs)) := ⟨_, rfl⟩
  rw [← hpl, ← hsd]
  have hdA : degG O A = (GPoly.toPoly (T.MX m h) A).natDegree := degG_eq _ _
  have hdB : degG O B = (GPoly.toPoly (T.MX m h) B).natDegree := degG_eq _ _
  by_cases hBz : GPoly.isZero O B = true
  · have hB0 : GPoly.toPoly (T.MX m h) B = 0 := (GPoly.isZero_iff _ _).mp hBz
    have := natDegree_le_of_rdeExp_A (T.bX m h a) _ _ Y r R hr hA0 (Or.inl hB0) hhom heq
    unfold peNbE
    simp only
    rw [if_pos hBz]
    exact ⟨fun N hN ↦ by cases hN; omega, fun h' ↦ by cases h'⟩
  have hB0 : GPoly.toPoly (T.MX m h) B ≠ 0 := fun h0 ↦ hBz ((GPoly.isZero_iff _ _).mpr h0)
  by_cases hlt : degG O A < degG O B
  · have hlt' : (GPoly.toPoly (T.MX m h) A).natDegree < (GPoly.toPoly (T.MX m h) B).natDegree := by
      omega
    have hY := natDegree_le_of_rdeExp_B (T.bX m h a) _ _ Y r R hr hB0 hlt' heq
    unfold peNbE
    simp only
    rw [if_neg hBz, if_pos hlt]
    by_cases hle : degG O B ≤ R
    · rw [if_pos hle]
      refine ⟨fun N hN ↦ ?_, fun h' ↦ by cases h'⟩
      cases hN
      rcases hY with h0 | h1
      · rw [h0, natDegree_zero]; exact Nat.zero_le _
      · omega
    · rw [if_neg hle]
      refine ⟨fun N hN ↦ (by cases hN), fun _ ↦ ?_⟩
      rcases hY with h0 | h1
      · exact h0
      · omega
  by_cases hlt2 : degG O B < degG O A
  · have hlt2' : (GPoly.toPoly (T.MX m h) B).natDegree < (GPoly.toPoly (T.MX m h) A).natDegree := by
      omega
    have := natDegree_le_of_rdeExp_A (T.bX m h a) _ _ Y r R hr hA0 (Or.inr hlt2') hhom heq
    unfold peNbE
    simp only
    rw [if_neg hBz, if_neg hlt, if_pos hlt2]
    exact ⟨fun N hN ↦ by cases hN; omega, fun h' ↦ by cases h'⟩
  -- the balanced case
  obtain ⟨N0, hN0, hRN, hbn⟩ := peNbE_balXE O pl sd A B R dQ hBz hlt hlt2
  rw [hN0]
  have hdAB : (GPoly.toPoly (T.MX m h) A).natDegree = (GPoly.toPoly (T.MX m h) B).natDegree := by
    omega
  refine ⟨fun N hN ↦ ?_, fun h' ↦ by cases h'⟩
  cases hN
  rw [hdA] at hRN
  rcases natDegree_le_of_rdeExp_bal (T.bX m h a) _ _ Y r R hr hdAB heq with hle | ⟨hY0, htop⟩
  · omega
  -- the top coefficient cancels: the logarithmic-derivative bound applies
  obtain ⟨-, hlead⟩ := hbal hB0 hdAB
  rw [T.sem_fCode_balXE m h a hc logs d κ hκ dQ] at hlead
  set n := Y.natDegree with hn
  set y := Y.leadingCoeff with hy
  set lA := (GPoly.toPoly (T.MX m h) A).leadingCoeff with hlA
  set lB := (GPoly.toPoly (T.MX m h) B).leadingCoeff with hlB
  have hlA0 : lA ≠ 0 := leadingCoeff_ne_zero.mpr hA0
  have hy0 : y ≠ 0 := leadingCoeff_ne_zero.mpr hY0
  set cK : ℕ → T.F m := fun i ↦ algebraMap Kc (T.F m) (κ i) with hcK
  set Nw : ℕ → (T.F m)[X] := fun i ↦ T.NwXE m h (logs.getD i d) with hNw
  set Dw : ℕ → (T.F m)[X] := fun i ↦ T.DwXE m h (logs.getD i d) with hDw
  set len := logs.length with hlen
  set sdK : Kc := ∑ i ∈ Finset.range len, κ i * (((Nw i).natDegree : Kc) - (Dw i).natDegree)
    with hsdK
  have hsdF : (T.MX m h).sem (sumDegXE ks m (logsCXE O logs)) = algebraMap Kc (T.F m) sdK := by
    rw [T.sem_sumDegXE m h logs d κ hκ, hsdK, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_sub, map_natCast, map_natCast]
  set Lsum := ∑ i ∈ Finset.range len, cK i *
    (logDeriv (Nw i).leadingCoeff - logDeriv (Dw i).leadingCoeff) with hLsum
  set α := (T.MX m h).sem a with hα
  set hInf := (T.MX m h).sem (peHinf O hc) with hhInf
  have hK0 : ∀ c : Kc, (algebraMap Kc (T.F m) c)′ = 0 := fun c ↦ T.deriv_algebraMap_Kc c
  -- the identity `(h(∞) + μ a)′ = logDeriv (1 / y) - Lsum`
  have hlnN : ∀ i, (Nw i).leadingCoeff ≠ 0 := fun i ↦
    leadingCoeff_ne_zero.mpr (T.NwD_ne_XE m h _).1
  have hlnD : ∀ i, (Dw i).leadingCoeff ≠ 0 := fun i ↦
    leadingCoeff_ne_zero.mpr (T.NwD_ne_XE m h _).2
  set s' : Finset (Option (Bool × ℕ)) :=
    Finset.insertNone (Finset.univ ×ˢ Finset.range len) with hs'
  set c' : Option (Bool × ℕ) → Kc := fun j ↦ match j with
    | none => 1
    | some (true, i) => -κ i
    | some (false, i) => κ i with hc'
  set u' : Option (Bool × ℕ) → T.F m := fun j ↦ match j with
    | none => y⁻¹
    | some (true, i) => (Nw i).leadingCoeff
    | some (false, i) => (Dw i).leadingCoeff with hu'
  have hsum : ∑ j ∈ s', algebraMap Kc (T.F m) (c' j) * logDeriv (u' j) =
      logDeriv y⁻¹ - Lsum := by
    rw [hs', Finset.sum_insertNone, Finset.sum_product, Fintype.sum_bool]
    simp only [hc', hu', map_one, one_mul, map_neg, neg_mul, Finset.sum_neg_distrib, hLsum, hcK,
      mul_sub, Finset.sum_sub_distrib]
    ring
  have hlogy : logDeriv y⁻¹ = n * T.bX m h a + lB / lA := by
    rw [logDeriv, show y⁻¹ = 1 / y by ring, Derivation.leibniz_div, Derivation.map_one_eq_zero]
    simp only [smul_eq_mul, mul_zero, zero_sub]
    field_simp
    linear_combination -htop
  obtain ⟨q, hq, hμ⟩ := T.pldX_specF_XE m hM hc2 (peHinf O hc) (sdK - dQ + n) s' c' u'
    (fun j _ ↦ by
      rcases j with _ | ⟨_ | _, i⟩
      · exact inv_ne_zero hy0
      · exact hlnD i
      · exact hlnN i) (by
      rw [hsum, hlogy, ← hlead, hsdF, map_add, Derivation.leibniz, hK0, smul_zero, add_zero,
        smul_eq_mul, map_add, map_sub, map_natCast, map_natCast]
      rw [show T.bX m h a = α′ from rfl]
      ring)
  have hsdq : algebraMap Kc (T.F m) sdK = ((q + dQ - n : ℚ) : T.F m) := by
    have : sdK = (q : Kc) + dQ - n := by rw [← hμ]; ring
    rw [this, map_sub, map_add, map_ratCast, map_natCast, map_natCast]
    push_cast; ring
  have hrv : ratVal ks m (sumDegXE ks m (logsCXE O logs)) = some (q + dQ - n) :=
    T.ratVal_spec m hM.mono.tr _ _ (by rw [← hsdq]; exact hsdF)
  exact hbn q (q + dQ - n) n (hpl.trans hq) (hsd.trans hrv)
    (by rw [show q - (q + dQ - n) + (dQ : ℚ) = ((n : ℕ) : ℚ) by ring, natOfQ_natCast])

end Bal

end NestMTower

end Tower.NestM
