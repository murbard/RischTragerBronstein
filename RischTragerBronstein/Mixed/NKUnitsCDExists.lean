import RischTragerBronstein.Mixed.NKUnitsCD
import RischTragerBronstein.Computable.SysIndC

/-!
# Existence of unit certificates with denominators

`zeroModC_complete`: the check `p ≡ 0 mod P` succeeds whenever `p(θ) = 0`, given that the powers
`1, θ, …, θ^{n-1}` are independent over `Fₘ₊₁` (the remainder has degree `< n`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential GTors

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma toPoly_MP_eq_MPr (m : ℕ) (h1 : T.Tr (m + 1)) (p : GPoly (LC (m + 1))) :
    GPoly.toPoly (T.MP (m + 1) h1) p = GPoly.toPoly (T.MPr (m + 1) h1) p := by
  induction p with
  | nil => simp [GPoly.toPoly_nil]
  | cons a p ih => rw [GPoly.toPoly_cons, GPoly.toPoly_cons, ih, MPr_sem]

lemma toPoly_nkPC_MP_monic (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m))) :
    (GPoly.toPoly (T.MP (m + 1) h1) (nkPC Fc ks m Pp)).Monic ∧
      (GPoly.toPoly (T.MP (m + 1) h1) (nkPC Fc ks m Pp)).natDegree = Pp.length := by
  rw [T.toPoly_MP_eq_MPr, T.toPoly_nkPC m h1 Pp]
  exact ⟨polyF_monic _ _, polyF_natDegree _ _⟩

/-- **Completeness of `zeroModC`.** -/
lemma zeroModC_complete (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp : List (GPoly (LC m)))
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range Pp.length, (a j : L) * θ ^ j = 0 →
      ∀ j < Pp.length, a j = 0)
    (p : GPoly (LC (m + 1))) (hp : T.evθ m h1 θ p = 0) : zeroModC Fc ks m Pp p = true := by
  set M := T.MP (m + 1) h1 with hM
  set r := remP (MO Fc ks (m + 1)) (nkPC Fc ks m Pp) p with hr
  obtain ⟨hmon, hdeg⟩ := T.toPoly_nkPC_MP_monic m h1 Pp
  have hrθ : aeval θ (GPoly.toPoly M r) = 0 := by
    rw [← T.evθ_MP, hr, T.evθ_remP_MO m h1 θ _ p hP, hp]
  have hlt : (GPoly.toPoly M r).degree < Pp.length := by
    rw [hr, remP, toPoly_divMod_snd M p _ hmon, ← hdeg, ← degree_eq_natDegree hmon.ne_zero]
    exact degree_modByMonic_lt _ hmon
  have hzero : GPoly.toPoly M r = 0 := by
    by_cases h0 : GPoly.toPoly M r = 0
    · exact h0
    have hnd : (GPoly.toPoly M r).natDegree < Pp.length := by
      rwa [degree_eq_natDegree h0, Nat.cast_lt] at hlt
    have hsum := hrθ
    rw [aeval_eq_sum_range' hnd] at hsum
    have hc := hind (fun j ↦ (GPoly.toPoly M r).coeff j) (by
      rw [← hsum]; exact Finset.sum_congr rfl fun j _ ↦ by rw [Algebra.smul_def]; rfl)
    refine Polynomial.ext fun j ↦ ?_
    rw [Polynomial.coeff_zero]
    by_cases hj : j < Pp.length
    · exact hc j hj
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  unfold zeroModC
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [M.isZero_iff]
  have := congrArg (fun q ↦ Polynomial.coeff q i) hzero
  simp only [coeff_toPoly_sem, Polynomial.coeff_zero] at this
  rwa [List.getD_eq_getElem _ _ hi] at this


section Complete

variable (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp : List (GPoly (LC m)))
  (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0)
  (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range Pp.length, (a j : L) * θ ^ j = 0 →
    ∀ j < Pp.length, a j = 0)
include hP hind

lemma unitCD_complete (U V : List (GPoly (LC m))) (d : GPoly (LC m))
    (h : T.evθ m h1 θ (nkFl Fc ks m U) * T.evθ m h1 θ (nkFl Fc ks m V) = T.evP m d * T.evP m d) :
    unitCD Fc ks m Pp U V d = true := by
  refine T.zeroModC_complete m h1 θ Pp hP hind _ ?_
  rw [T.evθ_subC, T.evθ_mulC, T.evθ_mulC, T.evθ_nkFl_single, h, sub_self]

lemma unitIC_complete (U : List (GPoly (LC m))) (d : GPoly (LC m)) (cs : List (GPoly (LC m)))
    (hd : T.evP m d ≠ 0)
    (h : hornerZ (T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d) (cs.map (T.evP m)) 1 = 0) :
    unitIC Fc ks m Pp U d cs = true := by
  refine T.zeroModC_complete m h1 θ Pp hP hind _ ?_
  rw [T.evθ_hornerC, T.evθ_one_MO, T.evθ_nkFl_single, List.map_map,
    hornerD_eq _ _ hd _ _ _ one_ne_zero, one_mul, div_one]
  have hcs : (cs.map ((T.evθ m h1 θ) ∘ fun c ↦ nkFl Fc ks m [c])) = cs.map (T.evP m) :=
    List.map_congr_left fun c _ ↦ T.evθ_nkFl_single m h1 θ c
  rw [hcs, h, mul_zero]

lemma invD_complete (d : GPoly (LC m)) (E : GPoly (LC (m + 1)))
    (h : T.evP m d * T.evθ m h1 θ E = 1) :
    zeroModC Fc ks m Pp (GPoly.sub (MO Fc ks (m + 1))
      (GPoly.mul (MO Fc ks (m + 1)) (nkFl Fc ks m [d]) E) [(MO Fc ks (m + 1)).one]) = true := by
  refine T.zeroModC_complete m h1 θ Pp hP hind _ ?_
  rw [T.evθ_subC, T.evθ_mulC, T.evθ_nkFl_single, T.evθ_one_MO, h, sub_self]

lemma logDerChkD_complete (U V : List (GPoly (LC m))) (d : GPoly (LC m))
    (gl dθ wθ : GPoly (LC (m + 1)))
    (hd1 : zeroModC Fc ks m Pp (GPoly.add (MO Fc ks (m + 1)) (GPoly.mul (MO Fc ks (m + 1)) dθ
      (GPoly.derivX (MO Fc ks (m + 1)) (nkPC Fc ks m Pp))) (GPoly.mapD (MO Fc ks (m + 1)) (nkPC Fc ks m Pp))) = true)
    (hw1 : zeroModC Fc ks m Pp (GPoly.sub (MO Fc ks (m + 1)) (GPoly.mul (MO Fc ks (m + 1)) wθ
      (GPoly.derivX (MO Fc ks (m + 1)) (nkPC Fc ks m Pp))) [(MO Fc ks (m + 1)).one]) = true)
    (hθ' : θ′ = T.evθ m h1 θ dθ) (hd : T.evP m d ≠ 0)
    (huv : T.evθ m h1 θ (nkFl Fc ks m U) * T.evθ m h1 θ (nkFl Fc ks m V) = T.evP m d * T.evP m d)
    (hgl : T.evθ m h1 θ gl = (T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d)′ /
      (T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d)) :
    logDerChkD Fc ks m Pp U V d gl dθ wθ = true := by
  unfold logDerChkD
  simp only [Bool.and_eq_true]
  refine ⟨⟨hd1, hw1⟩, T.zeroModC_complete m h1 θ Pp hP hind _ ?_⟩
  simp only [T.evθ_subC, T.evθ_mulC, T.evθ_addC, T.evθ_nkFl_single]
  have hu' := T.deriv_evθ_MO m h1 θ (nkFl Fc ks m U)
  have hD' := T.deriv_evθ_MO m h1 θ (nkFl Fc ks m [d])
  rw [T.evθ_nkFl_single] at hD'
  rw [← hθ']
  have e1 : T.evθ m h1 θ (GPoly.mapD (MO Fc ks (m + 1)) (nkFl Fc ks m U)) =
      (T.evθ m h1 θ (nkFl Fc ks m U))′ -
        T.evθ m h1 θ (GPoly.derivX (MO Fc ks (m + 1)) (nkFl Fc ks m U)) * θ′ := by
    rw [hu']; ring
  have e2 : T.evθ m h1 θ (GPoly.mapD (MO Fc ks (m + 1)) (nkFl Fc ks m [d])) =
      (T.evP m d)′ - T.evθ m h1 θ (GPoly.derivX (MO Fc ks (m + 1)) (nkFl Fc ks m [d])) * θ′ := by
    rw [hD']; ring
  rw [e1, e2]
  set u := T.evθ m h1 θ (nkFl Fc ks m U)
  set v := T.evθ m h1 θ (nkFl Fc ks m V)
  set δ := T.evP m d
  have hu0 : u ≠ 0 := fun h0 ↦ mul_ne_zero hd hd (by rw [← huv, h0, zero_mul])
  have hv : v = δ * δ / u := by field_simp; linear_combination huv
  rw [Derivation.leibniz_div] at hgl
  simp only [smul_eq_mul] at hgl
  rw [hgl, hv]
  field_simp
  ring

end Complete

section Clear

lemma evP_mulC (m : ℕ) (h : T.Tr m) (a b : GPoly (LC m)) :
    T.evP m (GPoly.mul (MO Fc ks m) a b) = T.evP m a * T.evP m b := by
  rw [← T.aeval_toPoly (T.MP m h) (T.sem_MP m h), ← T.aeval_toPoly (T.MP m h) (T.sem_MP m h),
    ← T.aeval_toPoly (T.MP m h) (T.sem_MP m h), GPoly.toPoly_mul, map_mul]

lemma evP_oneC (m : ℕ) (h : T.Tr m) : T.evP m [(MO Fc ks m).one] = 1 := by
  rw [← T.aeval_toPoly (T.MP m h) (T.sem_MP m h)]
  simp [GPoly.toPoly_cons, GPoly.toPoly_nil, (T.MP m h).sem_one]

lemma ev_frac (m : ℕ) (q : LC (m + 1)) : T.ev (m + 1) q = T.evP m q.1 / T.evP m q.2 := rfl

lemma evθ_consC (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (q : LC (m + 1)) (p : GPoly (LC (m + 1))) :
    T.evθ m h1 θ (q :: p) = T.ev (m + 1) q + θ * T.evθ m h1 θ p := by
  rw [T.evθ_MP, T.evθ_MP, GPoly.toPoly_cons, map_add, map_mul, aeval_C, aeval_X,
    IntermediateField.algebraMap_apply, T.sem_MP]

lemma evθ_nilC (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) : T.evθ m h1 θ [] = 0 := by
  rw [T.evθ_MP]; simp [GPoly.toPoly_nil]

/-- **Clearing denominators**: every `θ`-polynomial with coefficients in `Fₘ(t)` (codes) is
`(∑ Uⱼ θʲ)/d` with `Uⱼ, d ∈ Fₘ[t]` (codes), `d ≠ 0`. -/
lemma clear_den (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) :
    ∀ p : GPoly (LC (m + 1)), ∃ (U : List (GPoly (LC m))) (d : GPoly (LC m)),
      T.evP m d ≠ 0 ∧ T.evθ m h1 θ (nkFl Fc ks m U) = T.evP m d * T.evθ m h1 θ p
  | [] => ⟨[], [(MO Fc ks m).one], by rw [T.evP_oneC m h1.of_succ]; exact one_ne_zero, by
      simp only [nkFl, List.map_nil, T.evθ_nilC, mul_zero]⟩
  | q :: p => by
    classical
    obtain ⟨U', d', hd', hU'⟩ := clear_den m h1 θ p
    have hcons : ∀ (a : GPoly (LC m)) (U : List (GPoly (LC m))),
        T.evθ m h1 θ (nkFl Fc ks m (a :: U)) = T.evP m a + θ * T.evθ m h1 θ (nkFl Fc ks m U) := by
      intro a U
      change T.evθ m h1 θ (polyCode Fc ks m a :: nkFl Fc ks m U) = _
      rw [T.evθ_consC, ev_frac]
      change T.evP m a / T.evP m [(MO Fc ks m).one] + _ = _
      rw [T.evP_oneC m h1.of_succ, div_one]
    by_cases hq : T.evP m q.2 = 0
    · refine ⟨[] :: U', d', hd', ?_⟩
      rw [hcons, T.evθ_consC, ev_frac, hq, div_zero, zero_add, T.evP_nil, zero_add, hU']
      ring
    · refine ⟨GPoly.mul (MO Fc ks m) q.1 d' :: U'.map (fun c ↦ GPoly.mul (MO Fc ks m) c q.2),
        GPoly.mul (MO Fc ks m) q.2 d', ?_, ?_⟩
      · rw [T.evP_mulC m h1.of_succ]; exact mul_ne_zero hq hd'
      · rw [hcons, T.evθ_consC, ev_frac, T.evP_mulC m h1.of_succ, T.evP_mulC m h1.of_succ]
        have hmap : T.evθ m h1 θ (nkFl Fc ks m (U'.map (fun c ↦ GPoly.mul (MO Fc ks m) c q.2))) =
            T.evP m q.2 * T.evθ m h1 θ (nkFl Fc ks m U') := by
          rw [T.evθ_nkFl, T.evθ_nkFl, List.length_map, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj ↦ ?_
          have hj' : j < U'.length := Finset.mem_range.mp hj
          rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map,
            List.getD_eq_getElem _ _ hj', T.evP_mulC m h1.of_succ]
          ring
        rw [hmap, hU']
        field_simp

end Clear

lemma getD_ofFn_lt' {α : Type*} {n i : ℕ} (f : Fin n → α) (hi : i < n) (d : α) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

section Exists

variable (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp : List (GPoly (LC m)))
  (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0)
  (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range Pp.length, (a j : L) * θ ^ j = 0 →
    ∀ j < Pp.length, a j = 0)
include hP hind

/-- **A unit of the integral closure has a certificate**: if `u = p(θ)` and `u⁻¹ = q(θ)` have
coordinates in `Fₘ(t)` (codes) and are roots of monic polynomials over `Fₘ[t]` (`cU`, `cV`), then
`U, V, d, E` exist with all checks of `unitsCD` passing for this unit, and `U/d = u`. -/
theorem unitCD_cert_exists (p q : GPoly (LC (m + 1)))
    (hpq : T.evθ m h1 θ p * T.evθ m h1 θ q = 1) (cU cV : List (GPoly (LC m)))
    (hU : hornerZ (T.evθ m h1 θ p) (cU.map (T.evP m)) 1 = 0)
    (hV : hornerZ (T.evθ m h1 θ q) (cV.map (T.evP m)) 1 = 0) :
    ∃ (U V : List (GPoly (LC m))) (d : GPoly (LC m)) (E : GPoly (LC (m + 1))),
      T.evP m d ≠ 0 ∧
      T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d = T.evθ m h1 θ p ∧
      T.evθ m h1 θ (nkFl Fc ks m V) / T.evP m d = T.evθ m h1 θ q ∧
      (unitCD Fc ks m Pp U V d = true ∧ unitIC Fc ks m Pp U d cU = true ∧
        unitIC Fc ks m Pp V d cV = true ∧
        zeroModC Fc ks m Pp (GPoly.sub (MO Fc ks (m + 1))
          (GPoly.mul (MO Fc ks (m + 1)) (nkFl Fc ks m [d]) E) [(MO Fc ks (m + 1)).one]) = true) := by
  obtain ⟨U1, d1, hd1, hU1⟩ := T.clear_den m h1 θ p
  obtain ⟨V1, d2, hd2, hV1⟩ := T.clear_den m h1 θ q
  have hmapC : ∀ (W : List (GPoly (LC m))) (c : GPoly (LC m)),
      T.evθ m h1 θ (nkFl Fc ks m (W.map fun w ↦ GPoly.mul (MO Fc ks m) w c)) =
        T.evP m c * T.evθ m h1 θ (nkFl Fc ks m W) := by
    intro W c
    rw [T.evθ_nkFl, T.evθ_nkFl, List.length_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' : j < W.length := Finset.mem_range.mp hj
    rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map,
      List.getD_eq_getElem _ _ hj', T.evP_mulC m h1.of_succ]
    ring
  set d := GPoly.mul (MO Fc ks m) d1 d2 with hdd
  have hd : T.evP m d ≠ 0 := by rw [hdd, T.evP_mulC m h1.of_succ]; exact mul_ne_zero hd1 hd2
  set U := U1.map fun w ↦ GPoly.mul (MO Fc ks m) w d2 with hUU
  set V := V1.map fun w ↦ GPoly.mul (MO Fc ks m) w d1 with hVV
  have hUd : T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d = T.evθ m h1 θ p := by
    rw [hUU, hmapC, hU1, hdd, T.evP_mulC m h1.of_succ]
    field_simp
  have hVd : T.evθ m h1 θ (nkFl Fc ks m V) / T.evP m d = T.evθ m h1 θ q := by
    rw [hVV, hmapC, hV1, hdd, T.evP_mulC m h1.of_succ]
    field_simp
  let qd : LC (m + 1) := (([(MO Fc ks m).one], d) : GPoly (LC m) × GPoly (LC m))
  set E : GPoly (LC (m + 1)) := [qd] with hE
  have hEv : T.evP m d * T.evθ m h1 θ E = 1 := by
    rw [hE, T.evθ_consC m h1 θ qd [], T.evθ_nilC, mul_zero, add_zero, ev_frac]
    change T.evP m d * (T.evP m [(MO Fc ks m).one] / T.evP m d) = 1
    rw [T.evP_oneC m h1.of_succ]
    field_simp
  refine ⟨U, V, d, E, hd, hUd, hVd, ?_, ?_, ?_, T.invD_complete m h1 θ Pp hP hind d E hEv⟩
  · refine T.unitCD_complete m h1 θ Pp hP hind U V d ?_
    have h1' := hUd
    have h2' := hVd
    rw [div_eq_iff hd] at h1' h2'
    rw [h1', h2']
    linear_combination (T.evP m d * T.evP m d) * hpq
  · exact T.unitIC_complete m h1 θ Pp hP hind U d cU hd (by rw [hUd]; exact hU)
  · exact T.unitIC_complete m h1 θ Pp hP hind V d cV hd (by rw [hVd]; exact hV)

/-- **Certificates with denominators exist for any family of units of the integral closure**
(with code coordinates): given logarithmic derivatives `gᵢ = uᵢ′/uᵢ` passing the length and trace
conditions and the `θ′` checks, `unitsCD` succeeds. -/
theorem unitsCD_exists (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (gls : List (GPoly (LC (m + 1)))) (ps qs : Fin gls.length → GPoly (LC (m + 1)))
    (cU cV : Fin gls.length → List (GPoly (LC m)))
    (hpq : ∀ i, T.evθ m h1 θ (ps i) * T.evθ m h1 θ (qs i) = 1)
    (hU : ∀ i, hornerZ (T.evθ m h1 θ (ps i)) ((cU i).map (T.evP m)) 1 = 0)
    (hV : ∀ i, hornerZ (T.evθ m h1 θ (qs i)) ((cV i).map (T.evP m)) 1 = 0)
    (hd1 : zeroModC Fc ks m Pp (GPoly.add (MO Fc ks (m + 1)) (GPoly.mul (MO Fc ks (m + 1)) dθ
      (GPoly.derivX (MO Fc ks (m + 1)) (nkPC Fc ks m Pp))) (GPoly.mapD (MO Fc ks (m + 1)) (nkPC Fc ks m Pp))) = true)
    (hw1 : zeroModC Fc ks m Pp (GPoly.sub (MO Fc ks (m + 1)) (GPoly.mul (MO Fc ks (m + 1)) wθ
      (GPoly.derivX (MO Fc ks (m + 1)) (nkPC Fc ks m Pp))) [(MO Fc ks (m + 1)).one]) = true)
    (hθ' : θ′ = T.evθ m h1 θ dθ)
    (hgl : ∀ i : Fin gls.length, T.evθ m h1 θ (gls.getD i []) =
      (T.evθ m h1 θ (ps i))′ / T.evθ m h1 θ (ps i))
    (hlen : ∀ i < gls.length, (gls.getD i []).length ≤ Pp.length)
    (htr : ∀ i < gls.length, (MOr Fc ks (m + 1)).isZero (nkTau Fc ks m Pp.length (gls.getD i []) s) = true) :
    ∃ (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1)))),
      unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true := by
  choose U V d E hd hUd hVd hc using fun i ↦
    T.unitCD_cert_exists m h1 θ Pp hP hind (ps i) (qs i) (hpq i) (cU i) (cV i) (hU i) (hV i)
  refine ⟨List.ofFn U, List.ofFn V, List.ofFn d, List.ofFn cU, List.ofFn cV, List.ofFn E, ?_⟩
  unfold unitsCD
  rw [List.all_eq_true]
  intro i hi
  have hi' : i < gls.length := List.mem_range.mp hi
  set k : Fin gls.length := ⟨i, hi'⟩
  simp only [getD_ofFn_lt' _ hi', Bool.and_eq_true, decide_eq_true_eq]
  obtain ⟨c1, c2, c3, c4⟩ := hc k
  refine ⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, ?_⟩, hlen i hi'⟩, htr i hi'⟩
  have huv : T.evθ m h1 θ (nkFl Fc ks m (U k)) * T.evθ m h1 θ (nkFl Fc ks m (V k)) =
      T.evP m (d k) * T.evP m (d k) := by
    have a1 := hUd k
    have a2 := hVd k
    rw [div_eq_iff (hd k)] at a1 a2
    rw [a1, a2]; linear_combination (T.evP m (d k) * T.evP m (d k)) * hpq k
  refine T.logDerChkD_complete m h1 θ Pp hP hind (U k) (V k) (d k) _ dθ wθ hd1 hw1 hθ' (hd k) huv ?_
  rw [hUd k]
  exact hgl k

end Exists

end MTower

end Curves.MT

