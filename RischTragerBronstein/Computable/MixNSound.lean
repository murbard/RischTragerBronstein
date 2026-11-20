import RischTragerBronstein.Computable.MixNBasics
import RischTragerBronstein.Computable.PrimNComplete

/-!
# Mixed towers: soundness of the Risch equation solver and of limited integration

* `rdeM_sound`: `rdeM ks m f A = some Y` gives `Y′ + f Y = A` in `F m`.
* `limIntM_sound`: `limIntM ks m A W = some (cs, Y)` gives `Y′ + ∑ cᵢ wᵢ = A`.

Only the transcendence of the generators is used (normality then follows from `hCall`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.MixN

open Tower.PrimN

section Generic

variable {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

/-- **The invariant of the top-degree recursion**: `D acc′ + P₀ acc + Ap` is preserved. -/
theorem rdeAux_sound (w : GPoly α) (kd : Kind) (f : Code 1) (rde : Code 1 → α → Option α)
    (D P₀ : GPoly α) : ∀ (fuel : ℕ) (Ap acc Y : GPoly α),
    rdeAux O w kd f rde D P₀ fuel Ap acc = some Y →
    GPoly.toPoly M D * implicitDeriv (GPoly.toPoly M w) (GPoly.toPoly M Y) +
        GPoly.toPoly M P₀ * GPoly.toPoly M Y =
      GPoly.toPoly M D * implicitDeriv (GPoly.toPoly M w) (GPoly.toPoly M acc) +
        GPoly.toPoly M P₀ * GPoly.toPoly M acc + GPoly.toPoly M Ap := by
  intro fuel
  induction fuel with
  | zero =>
    intro Ap acc Y h
    simp only [rdeAux] at h
    split_ifs at h with hz
    rw [Option.some.injEq] at h
    subst h
    rw [(GPoly.isZero_iff M Ap).mp hz, add_zero]
  | succ fuel ih =>
    intro Ap acc Y h
    simp only [rdeAux] at h
    split_ifs at h with hz hlt
    · rw [Option.some.injEq] at h
      subst h
      rw [(GPoly.isZero_iff M Ap).mp hz, add_zero]
    · revert h
      split
      · intro h; exact absurd h (by simp)
      · intro h
        rw [ih _ _ _ h]
        simp only [GPoly.toPoly_add, GPoly.toPoly_sub, GPoly.toPoly_mul, map_add,
          GPoly.toPoly_derivT]
        ring

/-- The specification of `laurentSolve`. -/
lemma laurentSolve_spec (b : Code 1) (rde : Code 1 → α → Option α) (Λ : GPoly α) (k : ℕ) :
    ∀ (N : ℕ) (Ys : GPoly α), laurentSolve O b rde Λ k N = some Ys →
      Ys.length = N ∧ ∀ j < N, (j = k → Ys.getD j O.zero = O.zero) ∧
        (j ≠ k → rde (smulQ (((j : ℤ) - k : ℤ) : ℚ) b) (Λ.getD j O.zero) =
          some (Ys.getD j O.zero)) := by
  intro N
  induction N with
  | zero =>
    intro Ys h
    simp only [laurentSolve, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun j hj ↦ absurd hj (Nat.not_lt_zero j)⟩
  | succ N ih =>
    intro Ys h
    simp only [laurentSolve] at h
    split at h
    · exact absurd h (by simp)
    rename_i Ys₀ h₀
    obtain ⟨hl, hs⟩ := ih Ys₀ h₀
    split_ifs at h with hNk
    · simp only [Option.some.injEq] at h
      subst h
      refine ⟨by simp [hl], fun j hj ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact hs j hj
      · rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
        exact ⟨fun _ ↦ rfl, fun h ↦ absurd hNk h⟩
    · obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨by simp [hl], fun j hj ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact hs j hj
      · rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
        exact ⟨fun h ↦ absurd h hNk, fun _ ↦ hY⟩

end Generic

namespace MixTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : List Kind} (T : MixTower Kc E ks)

lemma phi_C (m : ℕ) (z : T.F m) : T.phi m (C z) = T.up m z :=
  Subtype.ext (by rw [coe_phi, aeval_C]; rfl)

lemma ratF_zero_eq (f : Code 1) : T.ratF 0 f = T.model0.sem f :=
  Subtype.ext (T.sem_model0 f).symm

/-- **Soundness of `rdeM`.** -/
theorem rdeM_sound : ∀ (m : ℕ) (h : T.Tr m) (f : Code 1) (A Y : Code (m + 1)),
    rdeM ks m f A = some Y → ((T.MP m h).sem Y)′ + T.ratF m f * (T.MP m h).sem Y =
      (T.MP m h).sem A
  | 0, h, f, A, Y, hY => by
    letI : Differential Kc[X] := polynomialOfDeriv 1
    haveI : DifferentialAlgebra Kc[X] (T.F 0) := ⟨T.deriv_phi0⟩
    have hDK : ∀ P : Kc[X], P′ = derivative P := implicitDeriv_one_of_trivial T.hC
    have hs := CPoly.rdeRationalW_sound (K := T.F 0) (algebraMap ℚ Kc) hDK
      (CPoly.normCoeff_den_ne_zero (R := ℚ) A) (CPoly.normCoeff_den_ne_zero (R := ℚ) f) hY
    change (T.model0.sem Y)′ + T.ratF 0 f * T.model0.sem Y = T.model0.sem A
    have hn := CPoly.normCoeff_spec _ T.phi0_map_injective (A : GFrac ℚ)
    have hnf := CPoly.normCoeff_spec _ T.phi0_map_injective (f : GFrac ℚ)
    simp only [RingHom.comp_apply, coe_mapRingHom] at hn hnf
    rw [show T.model0.sem Y = _ from T.model0_sem_eq Y, show T.model0.sem A = _ from
      T.model0_sem_eq A, ← hn, T.ratF_zero_eq, show T.model0.sem f = _ from T.model0_sem_eq f,
      ← hnf]
    simp only [phi0]
    exact hs
  | m + 1, h, f, A, Y, hY => by
    set hm : T.Tr m := fun i hi ↦ h i (by omega) with hhm
    set M := T.MP m hm with hM
    have htr : Transcendental (T.F m) (T.ts m) := h m (Nat.lt_succ_self m)
    have hsem : ∀ q : GPoly (Code (m + 1)) × GPoly (Code (m + 1)),
        (T.MP (m + 1) h).sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) :=
      fun _ ↦ rfl
    have hsemA : (T.MP (m + 1) h).sem A =
        T.phi m (GPoly.toPoly M A.1) / T.phi m (GPoly.toPoly M A.2) := rfl
    simp only [rdeM] at hY
    split_ifs at hY with hz
    · simp only [Option.some.injEq] at hY
      subst hY
      rw [(T.MP (m + 1) h).sem_zero, hsemA, (GPoly.isZero_iff M _).mp hz]
      simp
    obtain ⟨Yp, hYp, rfl⟩ := Option.map_eq_some_iff.mp hY
    have hinv := rdeAux_sound M (wK ks m) (kind ks m) f (rdeM ks m) A.2
      (GPoly.sub (opsM ks m) (GPoly.smul (opsM ks m) (lift m f) A.2)
        (GPoly.derivT (opsM ks m) (wK ks m) A.2)) _ _ [] Yp hYp
    simp only [GPoly.toPoly_nil, map_zero, mul_zero, zero_add, GPoly.toPoly_mul, GPoly.toPoly_sub,
      GPoly.toPoly_smul, GPoly.toPoly_derivT] at hinv
    rw [hM, T.toPoly_wK, T.sem_lift_F m hm f] at hinv
    have hinj := T.phi_injective htr
    have hA2 : GPoly.toPoly M A.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
    have hφD : T.phi m (GPoly.toPoly M A.2) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hA2
    rw [hsem, hsemA, T.ratF_succ m f, ← phi_C, hM]
    rw [hM] at hφD
    have h2 := congrArg (T.phi m) hinv
    simp only [map_add, map_mul, map_sub, ← T.deriv_phi] at h2
    rw [Derivation.leibniz_div]
    simp only [smul_eq_mul]
    field_simp
    linear_combination h2

/-- **Soundness, inductive step.** -/
theorem limIntM_sound_prim (m : ℕ) (h : T.Tr (m + 1)) {η : Code 1} (hk : kind ks m = .prim η)
    (ih : ∀ A W cs Y, limIntM ks m A W = some (cs, Y) →
      T.LimSound m (fun i hi ↦ h i (by omega)) A W cs Y)
    (A : Code (m + 2)) (W : List (Code 1)) (cs : List ℚ) (Y : Code (m + 2))
    (hres : limIntM ks (m + 1) A W = some (cs, Y)) :
    T.LimSound (m + 1) h A W cs Y := by
  set hm : T.Tr m := fun i hi ↦ h i (by omega) with hhm
  set M := T.MP m hm with hM
  set M' := T.MP (m + 1) h with hM'
  have htr : Transcendental (T.F m) (T.ts m) := h m (Nat.lt_succ_self m)
  have hw : T.wPoly m = C (T.ratF m η) := by simp only [wPoly, hk]
  have hsem : ∀ q : Code (m + 2),
      M'.sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) := fun _ ↦ rfl
  have hsem' : ∀ q : GPoly (Code (m + 1)) × GPoly (Code (m + 1)),
      M'.sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) := fun _ ↦ rfl
  have hcst : ∀ c : ℚ, M.sem (constC (m + 1) c) = (c : T.F m) := T.sem_constC m hm
  simp only [limIntM, hk] at hres
  split_ifs at hres with hz hr0
  · -- a zero denominator: the value is `0`
    simp only [Option.some.injEq, Prod.mk.injEq] at hres
    obtain ⟨rfl, rfl⟩ := hres
    refine ⟨by simp, ?_⟩
    have hA2 : GPoly.toPoly M A.2 = 0 := (GPoly.isZero_iff M _).mp hz
    rw [M'.sem_zero, hsem A, hA2, map_zero, div_zero]
    simp only [ZeroMemClass.coe_zero, map_zero, zero_add, zsum]
    exact zipWith_sum_zero _ W
  -- Hermite reduction and the division
  have hA2 : GPoly.toPoly M A.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
  obtain ⟨hval, hsq⟩ := T.hermite_value m hm htr A.1 A.2 hA2
    (fun p hp _ ↦ T.normal_prim m htr hk p hp)
  generalize GPoly.hermite (opsM ks m) (wK ks m) A.1 A.2 = hr at hres hval hr0 hsq
  have hdm := GPoly.divMod_spec M hr.b hr.s
  generalize GPoly.divMod (opsM ks m) hr.b hr.s = qr at hres hdm hr0
  have hr0' : GPoly.toPoly M qr.2 = 0 := (GPoly.isZero_iff M _).mp hr0
  rw [hr0', add_zero] at hdm
  -- the polynomial part
  generalize hpd : polyDown (opsM ks m) (lift m η) η (limIntM ks m)
    (constC (m + 1)) qr.1 (qr.1.length - 1) (opsM ks m).zero [] = pd at hres
  rcases pd with _ | ⟨Q, Ys⟩
  · exact absurd hres (by simp)
  simp only at hres
  generalize hl : limIntM ks m ((opsM ks m).add (qr.1.getD 0 (opsM ks m).zero)
    ((opsM ks m).neg ((opsM ks m).mul Q (lift m η)))) (η :: W) = l at hres
  rcases l with _ | ⟨_ | ⟨e, cs'⟩, Y₀⟩
  · exact absurd hres (by simp)
  · exact absurd hres (by simp)
  simp only [Option.some.injEq, Prod.mk.injEq] at hres
  obtain ⟨hcs, rfl⟩ := hres
  subst cs'
  -- the solver at level `m`, in `F m`
  have hsolve : ∀ G W r, limIntM ks m G W = some r → r.1.length = W.length ∧
      (M.sem r.2)′ + (List.zipWith (fun (c : ℚ) w ↦ (c : T.F m) * M.sem (lift m w)) r.1 W).sum =
        M.sem G := by
    intro G W r hr
    obtain ⟨h1, h2⟩ := ih G W r.1 r.2 hr
    refine ⟨h1, Subtype.ext ?_⟩
    rw [IntermediateField.coe_add, coe_deriv, T.coe_zipWith_sum]
    exact h2
  have hηv : M.sem (lift m η) = T.ratF m η := T.sem_lift_F m hm η
  have hinit : implicitDeriv (C (M.sem (lift m η)))
      (X ^ (qr.1.length - 1 + 1) * GPoly.toPoly M ((opsM ks m).zero :: [])) =
      X ^ (qr.1.length - 1 + 1) * GPoly.toPoly M (qr.1.drop (qr.1.length - 1 + 1)) +
        C (((qr.1.length - 1 : ℕ) + 1 : T.F m) * M.sem (opsM ks m).zero *
          M.sem (lift m η)) * X ^ (qr.1.length - 1) := by
    rw [List.drop_eq_nil_of_le (by omega)]
    simp [M.sem_zero]
  have hpoly := polyDown_sound M (lift m η) η (fun w ↦ M.sem (lift m w))
    (limIntM ks m) (constC (m + 1)) hsolve rfl (T.sem_constC m hm) T.deriv_ratCast qr.1
    (qr.1.length - 1) (opsM ks m).zero [] Q Ys hinit hpd
  obtain ⟨hlen, hY₀⟩ := hsolve _ _ _ hl
  simp only [List.length_cons, add_left_inj] at hlen
  refine ⟨hlen, ?_⟩
  simp only [List.zipWith_cons_cons, List.sum_cons, M.sem_add, M.sem_neg, M.sem_mul] at hY₀
  rw [hηv] at hY₀ hpoly
  set ηv := T.ratF m η with hηvd
  set SF := (List.zipWith (fun (c : ℚ) w ↦ (c : T.F m) * M.sem (lift m w)) cs W).sum with hSF
  -- the polynomial identity for the output
  have hout : implicitDeriv (C ηv) (GPoly.toPoly M (Y₀ :: (opsM ks m).add Q (constC (m + 1) e) :: Ys))
      = GPoly.toPoly M qr.1 - C SF := by
    have hsplit : GPoly.toPoly M (Y₀ :: (opsM ks m).add Q (constC (m + 1) e) :: Ys) =
        C (M.sem Y₀) + C (e : T.F m) * X + X * GPoly.toPoly M (Q :: Ys) := by
      simp only [GPoly.toPoly_cons, M.sem_add, hcst, C_add]
      ring
    have hq : GPoly.toPoly M qr.1 = C (M.sem (qr.1.getD 0 (opsM ks m).zero)) +
        X * GPoly.toPoly M (qr.1.drop 1) := by
      rw [← toPoly_drop M qr.1 0, List.drop_zero]
    rw [hsplit, map_add, map_add, hpoly, hq, implicitDeriv_C, Derivation.leibniz, implicitDeriv_C,
      implicitDeriv_X, T.deriv_ratCast]
    have hY' : (M.sem Y₀)′ = M.sem (qr.1.getD 0 (opsM ks m).zero) - M.sem Q * ηv - (e : T.F m) * ηv -
        SF := by linear_combination hY₀
    rw [hY']
    simp only [smul_eq_mul, C_0, mul_zero, add_zero, C_sub, C_mul]
    ring
  -- values
  have hone : GPoly.toPoly M [(opsM ks m).one] = 1 := by simp [M.sem_one]
  have hvalY : M'.sem ((opsM ks (m + 1)).add (hr.gn, hr.gd)
      (Y₀ :: (opsM ks m).add Q (constC (m + 1) e) :: Ys, [(opsM ks m).one])) =
      T.phi m (GPoly.toPoly M hr.gn) / T.phi m (GPoly.toPoly M hr.gd) +
        T.phi m (GPoly.toPoly M (Y₀ :: (opsM ks m).add Q (constC (m + 1) e) :: Ys)) := by
    refine (M'.sem_add _ _).trans ?_
    rw [hsem', hsem']
    simp only [hone, map_one, div_one]
  have hbs : T.phi m (GPoly.toPoly M hr.b) / T.phi m (GPoly.toPoly M hr.s) =
      T.phi m (GPoly.toPoly M qr.1) := by
    have hs0 : T.phi m (GPoly.toPoly M hr.s) ≠ 0 :=
      (map_ne_zero_iff _ (T.phi_injective htr)).mpr hsq.ne_zero
    rw [hdm, map_mul, mul_div_assoc, div_self hs0, mul_one]
  have hfinal : (M'.sem ((opsM ks (m + 1)).add (hr.gn, hr.gd)
      (Y₀ :: (opsM ks m).add Q (constC (m + 1) e) :: Ys, [(opsM ks m).one])))′ +
        T.phi m (C SF) = M'.sem A := by
    rw [hvalY, map_add, T.deriv_phi, hw, hout, hsem A, hval, hbs, map_sub]
    ring
  have := congrArg (fun z : T.F (m + 1) ↦ (z : E)) hfinal
  simp only [IntermediateField.coe_add, coe_deriv, T.coe_phi_C, hSF, hM, hM'] at this
  rw [T.coe_zipWith_sum] at this
  exact this


lemma getD_set_ne {α : Type*} (l : List α) (k j : ℕ) (d a : α) (h : j ≠ k) :
    (l.set k a).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, Ne.symm h]

lemma getD_set_self {α : Type*} (l : List α) (k : ℕ) (d a : α) (h : k < l.length) :
    (l.set k a).getD k d = a := by
  simp [List.getD_eq_getElem?_getD, h]

/-- **Soundness, exponential step.** -/
theorem limIntM_sound_exp (m : ℕ) (h : T.Tr (m + 1)) {b : Code 1} (hk : kind ks m = .exp b)
    (ih : ∀ A W cs Y, limIntM ks m A W = some (cs, Y) →
      T.LimSound m (fun i hi ↦ h i (by omega)) A W cs Y)
    (A : Code (m + 2)) (W : List (Code 1)) (cs : List ℚ) (Y : Code (m + 2))
    (hres : limIntM ks (m + 1) A W = some (cs, Y)) :
    T.LimSound (m + 1) h A W cs Y := by
  set hm : T.Tr m := fun i hi ↦ h i (by omega) with hhm
  set M := T.MP m hm with hM
  set M' := T.MP (m + 1) h with hM'
  have htr : Transcendental (T.F m) (T.ts m) := h m (Nat.lt_succ_self m)
  set bv := T.ratF m b with hbv
  have hw : T.wPoly m = C bv * X := by simp only [wPoly, hk]; rfl
  have hsem : ∀ q : Code (m + 2),
      M'.sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) := fun _ ↦ rfl
  have hsem' : ∀ q : GPoly (Code (m + 1)) × GPoly (Code (m + 1)),
      M'.sem q = T.phi m (GPoly.toPoly M q.1) / T.phi m (GPoly.toPoly M q.2) := fun _ ↦ rfl
  simp only [limIntM, hk] at hres
  split_ifs at hres with hz hr0
  · simp only [Option.some.injEq, Prod.mk.injEq] at hres
    obtain ⟨rfl, rfl⟩ := hres
    refine ⟨by simp, ?_⟩
    have hA2 : GPoly.toPoly M A.2 = 0 := (GPoly.isZero_iff M _).mp hz
    rw [M'.sem_zero, hsem A, hA2, map_zero, div_zero]
    simp only [ZeroMemClass.coe_zero, map_zero, zero_add, zsum]
    exact zipWith_sum_zero _ W
  have hA2 : GPoly.toPoly M A.2 ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
  -- split off the powers of `t`
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec M A.1 A.2 hA2
  generalize GPoly.expSplit (opsM ks m) A.1 A.2 = sp at hres hsp1 hsp2 hsp3 hr0
  obtain ⟨u, v, k, d₁⟩ := sp
  simp only at hres hsp1 hsp2 hsp3 hr0
  have hd₁ : GPoly.toPoly M d₁ ≠ 0 := fun h0 ↦ hA2 (by rw [hsp2, h0, mul_zero])
  -- Hermite reduction of the normal part
  obtain ⟨hval, hsq⟩ := T.hermite_value m hm htr u d₁ hd₁ (fun p hp hpd hdvd ↦
    T.normal_exp m htr hk p hp (fun hXp ↦ hsp3 (hXp.trans hpd)) hdvd)
  generalize GPoly.hermite (opsM ks m) (wK ks m) u d₁ = hr at hres hval hr0 hsq
  have hdm := GPoly.divMod_spec M hr.b hr.s
  generalize GPoly.divMod (opsM ks m) hr.b hr.s = qr at hres hdm hr0
  have hr0' : GPoly.toPoly M qr.2 = 0 := (GPoly.isZero_iff M _).mp hr0
  rw [hr0', add_zero] at hdm
  set Λ := GPoly.add (opsM ks m) (GPoly.mul (opsM ks m) qr.1 (GPoly.monomial (opsM ks m) k
    (opsM ks m).one)) v with hΛ
  have hΛp : GPoly.toPoly M Λ = GPoly.toPoly M qr.1 * X ^ k + GPoly.toPoly M v := by
    rw [hΛ, GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_monomial, M.sem_one, C_1, one_mul]
  -- the Laurent coefficients and the coefficient of `t⁰`
  generalize hls : laurentSolve (opsM ks m) b (rdeM ks m) Λ k (max Λ.length (k + 1)) = ls at hres
  generalize hli : limIntM ks m (Λ.getD k (opsM ks m).zero) W = li at hres
  rcases ls with _ | Ys
  · exact absurd hres (by simp)
  rcases li with _ | ⟨cs', Y₀⟩
  · exact absurd hres (by simp)
  simp only [Option.some.injEq, Prod.mk.injEq] at hres
  obtain ⟨hcs, rfl⟩ := hres
  subst cs'
  obtain ⟨hlen, hY₀⟩ := ih _ _ _ _ hli
  refine ⟨hlen, ?_⟩
  obtain ⟨hYl, hYs⟩ := laurentSolve_spec (O := opsM ks m) b (rdeM ks m) Λ k _ Ys hls
  set N := max Λ.length (k + 1) with hN
  set SF := (List.zipWith (fun (c : ℚ) w ↦ (c : T.F m) * M.sem (lift m w)) cs W).sum with hSF
  have hY₀F : (M.sem Y₀)′ + SF = M.sem (Λ.getD k (opsM ks m).zero) := Subtype.ext (by
    rw [IntermediateField.coe_add, coe_deriv, hSF, T.coe_zipWith_sum]
    exact hY₀)
  -- the polynomial identity for the numerator of the solution
  set P := GPoly.toPoly M (Ys.set k Y₀) with hP
  have hPid : implicitDeriv (C bv * X) P - C ((k : T.F m) * bv) * P =
      GPoly.toPoly M Λ - C SF * X ^ k := by
    refine Polynomial.ext fun j ↦ ?_
    rw [coeff_sub, coeff_implicitDeriv_C_mul_X, coeff_C_mul, coeff_sub, coeff_C_mul_X_pow, hP,
      coeff_toPoly_getD, coeff_toPoly_getD]
    by_cases hjN : j < N
    · by_cases hjk : j = k
      · subst hjk
        rw [getD_set_self _ _ _ _ (by omega), if_pos rfl]
        linear_combination hY₀F
      · rw [getD_set_ne _ _ _ _ _ hjk, if_neg hjk]
        have := T.rdeM_sound m hm _ _ _ ((hYs j hjN).2 hjk)
        rw [T.ratF_smulQ] at this
        push_cast at this
        linear_combination this
    · have hj1 : (Ys.set k Y₀).getD j (opsM ks m).zero = (opsM ks m).zero :=
        List.getD_eq_default _ _ (by simp; omega)
      have hj2 : Λ.getD j (opsM ks m).zero = (opsM ks m).zero :=
        List.getD_eq_default _ _ (by omega)
      rw [hj1, hj2, M.sem_zero, if_neg (by omega)]
      simp
  -- values
  have hXk : T.phi m (X ^ k) ≠ 0 := (map_ne_zero_iff _ (T.phi_injective htr)).mpr (pow_ne_zero _ X_ne_zero)
  have hmono : GPoly.toPoly M (GPoly.monomial (opsM ks m) k (opsM ks m).one) = X ^ k := by
    rw [GPoly.toPoly_monomial, M.sem_one, C_1, one_mul]
  have hvalY : M'.sem ((opsM ks (m + 1)).add (hr.gn, hr.gd)
      (Ys.set k Y₀, GPoly.monomial (opsM ks m) k (opsM ks m).one)) =
      T.phi m (GPoly.toPoly M hr.gn) / T.phi m (GPoly.toPoly M hr.gd) +
        T.phi m P / T.phi m (X ^ k) := by
    refine (M'.sem_add _ _).trans ?_
    rw [hsem', hsem', hmono]
  have hlaur : (T.phi m P / T.phi m (X ^ k))′ =
      T.phi m (GPoly.toPoly M Λ) / T.phi m (X ^ k) - T.up m SF := by
    rw [Derivation.leibniz_div, T.deriv_phi, T.deriv_phi, hw, deriv_X_pow]
    have hPid' := congrArg (T.phi m) hPid
    simp only [map_sub, map_mul, map_pow] at hPid'
    have hX1 : T.phi m X ≠ 0 := (map_ne_zero_iff _ (T.phi_injective htr)).mpr X_ne_zero
    rw [← phi_C]
    simp only [smul_eq_mul, map_mul, map_pow]
    field_simp
    linear_combination hPid'
  have hs0 : T.phi m (GPoly.toPoly M hr.s) ≠ 0 :=
    (map_ne_zero_iff _ (T.phi_injective htr)).mpr hsq.ne_zero
  have hd₁' : T.phi m (GPoly.toPoly M d₁) ≠ 0 := (map_ne_zero_iff _ (T.phi_injective htr)).mpr hd₁
  have hAval : M'.sem A = (T.phi m (GPoly.toPoly M hr.gn) / T.phi m (GPoly.toPoly M hr.gd))′ +
      T.phi m (GPoly.toPoly M Λ) / T.phi m (X ^ k) := by
    rw [hsem A, ← hsp1, hsp2]
    have hv' : T.phi m (GPoly.toPoly M u) / T.phi m (GPoly.toPoly M d₁) =
        (T.phi m (GPoly.toPoly M hr.gn) / T.phi m (GPoly.toPoly M hr.gd))′ +
          T.phi m (GPoly.toPoly M qr.1) := by
      rw [hval, hdm, map_mul, mul_div_assoc, div_self hs0, mul_one]
    have hg : (T.phi m (GPoly.toPoly M hr.gn) / T.phi m (GPoly.toPoly M hr.gd))′ =
        T.phi m (GPoly.toPoly M u) / T.phi m (GPoly.toPoly M d₁) - T.phi m (GPoly.toPoly M qr.1) := by
      rw [hv']; ring
    rw [hΛp, hg]
    simp only [map_add, map_mul, map_pow] at hXk ⊢
    field_simp
    ring
  have hfinal : (M'.sem ((opsM ks (m + 1)).add (hr.gn, hr.gd)
      (Ys.set k Y₀, GPoly.monomial (opsM ks m) k (opsM ks m).one)))′ + T.up m SF = M'.sem A := by
    rw [hvalY, map_add, hlaur, hAval]
    ring
  have := congrArg (fun z : T.F (m + 1) ↦ (z : E)) hfinal
  simp only [IntermediateField.coe_add, coe_deriv, coe_up, hSF, hM, hM'] at this
  rw [T.coe_zipWith_sum] at this
  exact this

/-- **Soundness of parametric limited integration** in `F m`. -/
theorem limIntM_sound : ∀ (m : ℕ) (h : T.Tr m) (A : Code (m + 1)) (W : List (Code 1))
    (cs : List ℚ) (Y : Code (m + 1)), limIntM ks m A W = some (cs, Y) → T.LimSound m h A W cs Y
  | 0, h, A, W, cs, Y, hres => T.limIntM_sound_zero h A W cs Y hres
  | m + 1, h, A, W, cs, Y, hres => by
    have ih := limIntM_sound m (fun i hi ↦ h i (by omega))
    cases hk : kind ks m with
    | prim η => exact T.limIntM_sound_prim m h hk ih A W cs Y hres
    | exp b => exact T.limIntM_sound_exp m h hk ih A W cs Y hres

end MixTower

end Tower.MixN
