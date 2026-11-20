import RischTragerBronstein.Computable.NestXBase

/-!
# Parametric limited integration at exponential levels of mixed towers

The exponential step `expLimStepX` of `paramLimX` (and the base `paramLim0`) for a mixed tower
`NestMTower Kc E ks`: the proofs of `NestMLim.lean`, for an exponential level `ks m = .exp a`,
with the Risch solver one level down and the absence of homogeneous solutions
`e′ + j a′ e = 0` (`j ≠ 0`) as hypotheses.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP Tower.NestX CPoly

/-- The split of a weight at an exponential level `m + 1` of a mixed tower. -/
def eSpX (ks : (m : ℕ) → KindN m) (m : ℕ) (w : Code (m + 2)) : ExpSplit (Code (m + 1)) :=
  expSplit (opsM ks m) (wK (opsM ks m) (ks m)) w
namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : (m : ℕ) → KindN m}
variable (T : NestMTower Kc E ks)

section Decomp

variable (m : ℕ) (h : T.Tr (m + 1)) {a : Code (m + 1)} (hka : ks m = .exp a)
include hka

set_option maxHeartbeats 800000 in
/-- **The decomposition of a weight** `w = g′ + r / s + L / tᵏ` at an exponential level. -/
theorem exp_weight_decompX (w : GPoly (Code (m + 1)) × GPoly (Code (m + 1))) :
    (T.M1X m h).sem w = ((T.M1X m h).sem ((eSpX ks m w).gn, (eSpX ks m w).gd))′ +
      T.σX m h (eSpX ks m w).r / T.σX m h (eSpX ks m w).s +
      T.σX m h (eSpX ks m w).L / T.σX m h (powX (opsM ks m) (eSpX ks m w).k) ∧
    Squarefree (GPoly.toPoly (T.MX m h) (eSpX ks m w).s) ∧
    ¬X ∣ GPoly.toPoly (T.MX m h) (eSpX ks m w).s ∧
    (GPoly.toPoly (T.MX m h) (eSpX ks m w).r).degree <
      (GPoly.toPoly (T.MX m h) (eSpX ks m w).s).degree := by
  classical
  set O := opsM ks m with hO
  have hm : T.Tr m := fun i hi ↦ h i (by omega)
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hinj := T.phi_injX m h
  obtain ⟨wc, hwc⟩ : ∃ wc, wc = cleanG O w := ⟨_, rfl⟩
  have hwc0 : GPoly.toPoly (T.MX m h) wc.2 ≠ 0 := by
    have := T.σX_cleanG_ne m h w
    rw [← hwc] at this
    intro h0; exact this (by rw [σX, h0, map_zero])
  have hsw : (T.M1X m h).sem w = T.σX m h wc.1 / T.σX m h wc.2 := by
    rw [← T.semX, hwc, T.semX_cleanG]
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 = lowZ O wc.2 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = wc.2.drop s0 := ⟨_, rfl⟩
  have hwd : GPoly.toPoly (T.MX m h) wc.2 = X ^ s0 * GPoly.toPoly (T.MX m h) d := by
    subst hd hs0; exact toPoly_lowZ (T.MX m h) wc.2
  have hd0 : GPoly.toPoly (T.MX m h) d ≠ 0 := fun h0 ↦ hwc0 (by rw [hwd, h0, mul_zero])
  have hdX : ¬X ∣ GPoly.toPoly (T.MX m h) d := by
    subst hd hs0; exact not_X_dvd_drop_lowZ (T.MX m h) wc.2 hwc0
  obtain ⟨rL, hrL⟩ : ∃ rL, rL = GPoly.solveBezout O (powX O s0) d wc.1 := ⟨_, rfl⟩
  have hbez : GPoly.toPoly (T.MX m h) rL.1 * X ^ s0 + GPoly.toPoly (T.MX m h) rL.2 *
      GPoly.toPoly (T.MX m h) d = GPoly.toPoly (T.MX m h) wc.1 := by
    have := GPoly.solveBezout_spec (T.MX m h) (powX O s0) d wc.1 hd0 (by
      rw [toPoly_powX]
      exact IsCoprime.pow_left ((irreducible_X.coprime_iff_not_dvd).mpr hdX))
    rw [toPoly_powX, ← hrL] at this
    exact this
  -- Hermite reduction of `r₀ / d`
  have hnormal : ∀ p : (T.F m)[X], Irreducible p → p ∣ GPoly.toPoly (T.MP m hm) d →
      ¬p ∣ implicitDeriv (T.wPoly m) p := fun p hp hpd ↦
    T.normal_exp m htr hka p hp fun hXp ↦ hdX (hXp.trans hpd)
  have hherm := T.hermite_value m hm htr rL.1 d hd0 hnormal
  obtain ⟨H, hH⟩ : ∃ H, H = GPoly.hermite O (wK O (ks m)) rL.1 d := ⟨_, rfl⟩
  rw [← hH] at hherm
  obtain ⟨hval, hsq⟩ := hherm
  have hsdvd : GPoly.toPoly (T.MX m h) H.s ∣ GPoly.toPoly (T.MX m h) d := by
    rw [hH]; exact GPoly.hermite_s_dvd (T.MX m h) _ rL.1 d hd0
  obtain ⟨qr, hqr⟩ : ∃ qr, qr = GPoly.divMod O H.b H.s := ⟨_, rfl⟩
  have hdm : GPoly.toPoly (T.MX m h) H.b = GPoly.toPoly (T.MX m h) qr.1 * GPoly.toPoly (T.MX m h) H.s +
      GPoly.toPoly (T.MX m h) qr.2 := by rw [hqr]; exact GPoly.divMod_spec (T.MX m h) _ _
  have hdeg : (GPoly.toPoly (T.MX m h) qr.2).degree < (GPoly.toPoly (T.MX m h) H.s).degree := by
    rw [hqr]; exact GPoly.divMod_degree_lt (T.MX m h) _ _ hsq.ne_zero
  -- the split, unfolded
  have hsp : eSpX ks m w = (⟨H.gn, H.gd, qr.2, H.s,
      GPoly.add O rL.2 (GPoly.mul O (powX O s0) qr.1), s0⟩ : ExpSplit (Code (m + 1))) := by
    subst hqr hH hrL hd hs0 hwc; rfl
  rw [hsp]
  refine ⟨?_, hsq, fun hX ↦ hdX (hX.trans hsdvd), hdeg⟩
  simp only
  rw [hsw, T.semX]
  have hs0' : T.phi m (GPoly.toPoly (T.MX m h) H.s) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hsq.ne_zero
  have hdd : T.phi m (GPoly.toPoly (T.MX m h) d) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd0
  have hXs : T.phi m (X ^ s0) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  have hr0 : T.phi m (GPoly.toPoly (T.MX m h) rL.1) = T.phi m (GPoly.toPoly (T.MX m h) d) *
      ((T.phi m (GPoly.toPoly (T.MX m h) H.gn) / T.phi m (GPoly.toPoly (T.MX m h) H.gd))′ +
        T.phi m (GPoly.toPoly (T.MX m h) H.b) / T.phi m (GPoly.toPoly (T.MX m h) H.s)) := by
    rw [← hval]; field_simp
  simp only [σX]
  rw [GPoly.toPoly_add, GPoly.toPoly_mul, toPoly_powX, ← hbez, hwd]
  simp only [map_add, map_mul]
  rw [hr0, hdm]
  simp only [map_add, map_mul]
  field_simp
  ring

end Decomp

section Base

lemma algebraMap_ratCastMX {m : ℕ} (q : ℚ) :
    algebraMap Kc (T.F m) (algebraMap ℚ Kc q) = (q : T.F m) := by
  rw [eq_ratCast (algebraMap ℚ Kc) q, map_ratCast]

lemma phi_C_ratCastMX (m : ℕ) (q : ℚ) : T.phi m (C ((q : ℚ) : T.F m)) = ((q : ℚ) : T.F (m + 1)) := by
  rw [T.phi_C]
  exact map_ratCast _ q

lemma deriv_sum_ratCastMX {m : ℕ} (n : ℕ) (q : ℕ → ℚ) (a : ℕ → T.F m) :
    (∑ i ∈ Finset.range n, (q i : T.F m) * a i)′ = ∑ i ∈ Finset.range n, (q i : T.F m) * (a i)′ := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Derivation.leibniz, T.deriv_ratCast, smul_eq_mul, smul_eq_mul, mul_zero, add_zero, mul_comm]

lemma deriv_sum_KcMX {m : ℕ} (n : ℕ) (q : ℕ → Kc) (a : ℕ → T.F m) :
    (∑ i ∈ Finset.range n, algebraMap Kc (T.F m) (q i) * a i)′ =
      ∑ i ∈ Finset.range n, algebraMap Kc (T.F m) (q i) * (a i)′ := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Derivation.leibniz, T.deriv_algebraMap_Kc, smul_eq_mul, smul_eq_mul, mul_zero, add_zero,
    mul_comm]

lemma sem0_splitMX (h : T.Tr 0) (w : Code 1) :
    (T.MP 0 h).sem w = ((T.MP 0 h).sem (ratPart (ratInt w)))′ + (T.MP 0 h).sem (logPart w) := by
  refine (T.ratInt_spec w).1.trans ?_
  congr 1
  exact (T.model0_sem_eq (logPart w)).symm

set_option maxHeartbeats 800000 in
/-- **Parametric limited integration at the base**: soundness and completeness. -/
theorem paramLim0X_spec (h : T.Tr 0) :
    LimSpec (algebraMap Kc (T.F 0)) (T.MP 0 h) (paramLim0 ks) := by
  set zc := (opsM ks 0).zero with hzc
  have hsound : ∀ W : List (Code 1), ∀ r ∈ paramLim0 ks W,
      ((T.MP 0 h).sem r.2)′ = sQ (T.MP 0 h) r.1 W := by
    intro W r hr
    have hout : paramLim0 ks W = (consys ks 0 (W.map logPart)).map fun u ↦
        (NestTower.vecOf W.length u, lcombCode (opsM ks 0) (cstN 0) (NestTower.vecOf W.length u)
          (W.map fun w ↦ ratPart (ratInt w))) := rfl
    rw [hout] at hr
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
    have hrel : ∑ i ∈ Finset.range W.length,
        ((u.getD i 0 : ℚ) : T.F 0) * (T.MP 0 h).sem (logPart (W.getD i zc)) = 0 := by
      have := T.consys_sound 0 h (W.map logPart) u hu
      rw [NestTower.zipWith_sum_range _ 0 zc _ _ (by simp)] at this
      simp only [List.length_map, List.length_range] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hi' : i < W.length := Finset.mem_range.mp hi
      rw [NestTower.getD_range_map (fun j ↦ algebraMap ℚ Kc (u.getD j 0)) 0 hi', T.algebraMap_ratCastMX,
        NestTower.getD_map' logPart W zc zc hi']
    simp only
    rw [sem_lcombCode (T.MP 0 h) (cstN 0) (T.sem_cstN 0 h),
      NestTower.zipWith_sum_range _ 0 zc _ _ (by simp [NestTower.vecOf])]
    simp only [List.length_map, NestTower.vecOf, List.length_range]
    rw [T.deriv_sum_ratCastMX, sQ]
    have e : ∀ i ∈ Finset.range W.length,
        ((((List.range W.length).map fun i ↦ u.getD i 0).getD i 0 : ℚ) : T.F 0) *
          ((T.MP 0 h).sem ((W.map fun w ↦ ratPart (ratInt w)).getD i zc))′ =
        ((((List.range W.length).map fun i ↦ u.getD i 0).getD i 0 : ℚ) : T.F 0) *
          (T.MP 0 h).sem (W.getD i zc) -
          ((u.getD i 0 : ℚ) : T.F 0) * (T.MP 0 h).sem (logPart (W.getD i zc)) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [NestTower.getD_map' _ W zc zc hi', T.sem0_splitMX h (W.getD i zc),
        NestTower.getD_range_map _ _ hi']
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, hrel, sub_zero]
  refine ⟨hsound, fun W c hc z hz ↦ ?_⟩
  have hout : paramLim0 ks W = (consys ks 0 (W.map logPart)).map fun u ↦
      (NestTower.vecOf W.length u, lcombCode (opsM ks 0) (cstN 0) (NestTower.vecOf W.length u)
        (W.map fun w ↦ ratPart (ratInt w))) := rfl
  letI : Differential Kc[X] := polynomialOfDeriv 1
  haveI : DifferentialAlgebra Kc[X] (T.F 0) := ⟨T.deriv_phi0⟩
  have hD : ∀ P : Kc[X], P′ = derivative P := implicitDeriv_one_of_trivial T.hC
  have hnorm : ∀ p : Kc[X], Irreducible p → ¬p ∣ p′ := fun p hp ↦ by
    rw [hD]; exact Differential.not_dvd_derivative_self hp
  have hL : ∀ i, (T.MP 0 h).sem (logPart (W.getD i zc)) =
      algebraMap Kc[X] (T.F 0) ((CPoly.toPoly (ratInt (W.getD i zc)).r).map
        (algebraMap ℚ Kc)) / algebraMap Kc[X] (T.F 0)
        ((CPoly.toPoly (ratInt (W.getD i zc)).s).map (algebraMap ℚ Kc)) := fun i ↦
    T.model0_sem_eq _
  set l := (List.range W.length).map fun i ↦
    (C (c.getD i 0) * (CPoly.toPoly (ratInt (W.getD i zc)).r).map (algebraMap ℚ Kc),
      (CPoly.toPoly (ratInt (W.getD i zc)).s).map (algebraMap ℚ Kc)) with hl
  set Z := z - ∑ i ∈ Finset.range W.length, algebraMap Kc (T.F 0) (c.getD i 0) *
    (T.MP 0 h).sem (ratPart (ratInt (W.getD i zc))) with hZ
  have hlsum : (l.map fun p ↦ algebraMap Kc[X] (T.F 0) p.1 / algebraMap Kc[X] (T.F 0) p.2).sum =
      ∑ i ∈ Finset.range W.length, algebraMap Kc (T.F 0) (c.getD i 0) *
        (T.MP 0 h).sem (logPart (W.getD i zc)) := by
    rw [hl, List.map_map, NestTower.list_sum_map_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Function.comp_apply]
    rw [hL, map_mul, show algebraMap Kc[X] (T.F 0) (C (c.getD i 0)) =
      algebraMap Kc (T.F 0) (c.getD i 0) from T.phi0_C _]
    ring
  have hZd : Z′ = algebraMap Kc[X] (T.F 0) 0 +
      (l.map fun p ↦ algebraMap Kc[X] (T.F 0) p.1 / algebraMap Kc[X] (T.F 0) p.2).sum := by
    rw [hlsum, map_zero, zero_add, hZ, map_sub, hz, T.deriv_sum_KcMX, sC,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [T.sem0_splitMX h (W.getD i zc)]
    ring
  obtain ⟨hsum0, -⟩ := Differential.deriv_eq_poly_add_sum_proper (K := T.F 0) hnorm 0 l
    (fun p hp ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      exact (T.ratInt_spec _).2.1)
    (fun p hp ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      exact lt_of_le_of_lt (by rw [← smul_eq_C_mul]; exact degree_smul_le _ _)
        (T.ratInt_spec _).2.2)
    Z hZd
  rw [hlsum] at hsum0
  have h0 : (List.zipWith (fun c v ↦ algebraMap Kc (T.F 0) c * (T.MP 0 h).sem v)
      ((List.range W.length).map fun i ↦ c.getD i 0) (W.map logPart)).sum = 0 := by
    rw [NestTower.zipWith_sum_range _ 0 zc _ _ (by simp), ← hsum0]
    simp only [List.length_map, List.length_range]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' : i < W.length := Finset.mem_range.mp hi
    rw [NestTower.getD_range_map (fun j ↦ c.getD j 0) 0 hi', NestTower.getD_map' logPart W zc zc hi']
  obtain ⟨β, hβl, hβ⟩ := T.consys_complete 0 h (W.map logPart) _ (by simp) h0
  have hlen : (paramLim0 ks W).length = (consys ks 0 (W.map logPart)).length := by
    rw [hout, List.length_map]
  have hgetD : ∀ k < (consys ks 0 (W.map logPart)).length,
      (paramLim0 ks W).getD k ([], zc) =
        (NestTower.vecOf W.length ((consys ks 0 (W.map logPart)).getD k []),
          lcombCode (opsM ks 0) (cstN 0)
            (NestTower.vecOf W.length ((consys ks 0 (W.map logPart)).getD k []))
            (W.map fun w ↦ ratPart (ratInt w))) := fun k hk ↦ by
    rw [hout, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
      List.getD_eq_getElem _ _ hk]
  have hcoef : ∀ i, c.getD i 0 = ∑ k ∈ Finset.range (paramLim0 ks W).length,
      β.getD k 0 * algebraMap ℚ Kc (((paramLim0 ks W).getD k ([], zc)).1.getD i 0) := by
    intro i
    rw [hlen]
    by_cases hi : i < W.length
    · have := hβ i
      rw [NestTower.getD_range_map (fun j ↦ c.getD j 0) 0 hi,
        NestTower.zipWith_sum_range _ 0 [] _ _ hβl, hβl] at this
      rw [this]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [hgetD k (Finset.mem_range.mp hk), NestTower.getD_vecOf, if_pos hi]
    · rw [hc i (by omega)]
      symm
      refine Finset.sum_eq_zero fun k hk ↦ ?_
      rw [hgetD k (Finset.mem_range.mp hk), NestTower.getD_vecOf, if_neg hi, map_zero, mul_zero]
  refine ⟨β, hcoef, ?_⟩
  rw [map_sub, hz, T.deriv_sum_KcMX, sub_eq_zero]
  have e1 : ∀ k ∈ Finset.range (paramLim0 ks W).length,
      algebraMap Kc (T.F 0) (β.getD k 0) *
        ((T.MP 0 h).sem ((paramLim0 ks W).getD k ([], zc)).2)′ =
      ∑ i ∈ Finset.range W.length, algebraMap Kc (T.F 0) (β.getD k 0 *
        algebraMap ℚ Kc (((paramLim0 ks W).getD k ([], zc)).1.getD i 0)) *
          (T.MP 0 h).sem (W.getD i zc) := by
    intro k hk
    have hmem : (paramLim0 ks W).getD k ([], zc) ∈ paramLim0 ks W := by
      rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]; exact List.getElem_mem _
    rw [hsound W _ hmem, sQ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, T.algebraMap_ratCastMX]
    ring
  rw [Finset.sum_congr rfl e1, Finset.sum_comm, sC]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_mul, ← map_sum, ← hcoef i]

end Base

section Step

variable (m : ℕ) (h : T.Tr (m + 1)) {a : Code (m + 1)} (hka : ks m = .exp a)
include hka

lemma phi_list_sumX (l : List ((T.F m)[X] × (T.F m)[X])) :
    ((l.map fun p ↦ T.phi m p.1 / T.phi m p.2).sum : T.F (m + 1)) =
      (l.map fun p ↦ T.phi m p.1 / T.phi m p.2).sum := rfl

variable (hhom : ∀ j : ℤ, j ≠ 0 → ∀ e : T.F m, e ≠ 0 → e′ + (j : T.F m) * T.bX m h a * e ≠ 0)

include hhom in
set_option maxHeartbeats 800000 in
/-- **Limited integration over the exponential level**: if `z′ = P / tˢ + ∑ rᵢ / sᵢ` (normal simple
parts), the simple parts cancel and `z = Y / tˢ` with `Y′ - S a′ Y = P`. -/
theorem tower_laurent_stepX (P : (T.F m)[X]) (S : ℕ) (l : List ((T.F m)[X] × (T.F m)[X]))
    (hsq : ∀ p ∈ l, Squarefree p.2) (hX : ∀ p ∈ l, ¬X ∣ p.2)
    (hdeg : ∀ p ∈ l, p.1.degree < p.2.degree) (z : T.F (m + 1))
    (hz : z′ = T.phi m P / T.phi m (X ^ S) + (l.map fun p ↦ T.phi m p.1 / T.phi m p.2).sum) :
    (l.map fun p ↦ T.phi m p.1 / T.phi m p.2).sum = 0 ∧ ∃ Y : (T.F m)[X],
      z = T.phi m Y / T.phi m (X ^ S) ∧
        implicitDeriv (C (T.bX m h a) * X) Y - C ((S : T.F m) * T.bX m h a) * Y = P := by
  classical
  have hm : T.Tr m := fun i hi ↦ h i (by omega)
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hhomZ := hhom
  -- the setting `K = F m (t)`
  set t := T.ts m with ht
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
  have hnorm : ∀ p : (T.F m)[X], Irreducible p → ¬X ∣ p → ¬p ∣ p′ := fun p hp hXp ↦
    T.normal_exp m htr hka p hp hXp
  set φK := algebraMap (T.F m)[X] (T.F m)⟮t⟯ with hφK
  let zK : (T.F m)⟮t⟯ := ⟨(z : E), (T.mem_F_succ).mp z.2⟩
  have hsumE : ∀ l' : List ((T.F m)[X] × (T.F m)[X]),
      (((l'.map fun p ↦ φK p.1 / φK p.2).sum : (T.F m)⟮t⟯) : E) =
        (((l'.map fun p ↦ T.phi m p.1 / T.phi m p.2).sum : T.F (m + 1)) : E) := by
    intro l'
    induction l' with
    | nil => simp
    | cons p l' ih =>
      simp only [List.map_cons, List.sum_cons, IntermediateField.coe_add,
        IntermediateField.coe_div, hcoe, ih, T.coe_phi]
      rfl
  have hzK : zK′ = φK P / φK (X ^ S) + (l.map fun p ↦ φK p.1 / φK p.2).sum := Subtype.ext (by
    rw [hdK, IntermediateField.coe_add, IntermediateField.coe_div, hcoe, hcoe, hsumE]
    change ((z′ : T.F (m + 1)) : E) = _
    rw [hz, IntermediateField.coe_add, IntermediateField.coe_div, T.coe_phi, T.coe_phi])
  obtain ⟨hsum0, V, kv, hV⟩ := deriv_eq_laurent_add_sum_proper hDe hnorm P S l hsq hX hdeg zK hzK
  rw [hsum0, add_zero, hV] at hzK
  obtain ⟨Y, hY, hYd⟩ := laurent_normalize hDe hhomZ V P kv S hzK
  refine ⟨?_, Y, ?_, hYd⟩
  · apply Subtype.ext
    have := congrArg Subtype.val hsum0
    rw [hsumE] at this
    rw [this]; rfl
  · apply Subtype.ext
    have := congrArg Subtype.val (hV.trans hY)
    rw [IntermediateField.coe_div, hcoe, hcoe] at this
    rw [IntermediateField.coe_div, T.coe_phi, T.coe_phi]
    exact this

end Step

section StepSpec

variable (m : ℕ) (h : T.Tr (m + 1)) {a : Code (m + 1)} (hka : ks m = .exp a)
include hka

lemma toPoly_shiftedLX (S : ℕ) (e : ExpSplit (Code (m + 1))) :
    GPoly.toPoly (T.MX m h) (shiftedL (opsM ks m) S e) =
      X ^ (S - e.k) * GPoly.toPoly (T.MX m h) e.L := by
  rw [shiftedL, GPoly.toPoly_append, List.length_replicate]
  have : GPoly.toPoly (T.MX m h) (List.replicate (S - e.k) (opsM ks m).zero) = 0 := by
    induction (S - e.k) with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ, GPoly.toPoly_cons, ih, (T.MX m h).sem_zero]; simp
  rw [this, zero_add]

lemma k_le_laurentSX (Sp : List (ExpSplit (Code (m + 1)))) (e : ExpSplit (Code (m + 1)))
    (he : e ∈ Sp) : e.k ≤ laurentS Sp :=
  le_foldr_max _ _ (List.mem_map.mpr ⟨e, he, rfl⟩)

lemma deriv_laurent_towerX (Y : (T.F m)[X]) (S : ℕ) :
    (T.phi m Y / T.phi m (X ^ S))′ =
      T.phi m (implicitDeriv (C (T.bX m h a) * X) Y - C ((S : T.F m) * T.bX m h a) * Y) /
        T.phi m (X ^ S) := by
  have hinj := T.phi_injX m h
  have hX : T.phi m (X ^ S) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  rw [Derivation.leibniz_div, T.deriv_phi_expX m h hka, T.deriv_phi_expX m h hka, deriv_X_pow]
  simp only [smul_eq_mul, map_sub, map_mul]
  field_simp

lemma natDegree_toPoly_le_lengthX (p : GPoly (Code (m + 1))) :
    (GPoly.toPoly (T.MX m h) p).natDegree ≤ p.length := by
  have := GPoly.degree_toPoly_lt (T.MX m h) p
  by_cases hp : GPoly.toPoly (T.MX m h) p = 0
  · rw [hp, natDegree_zero]; exact Nat.zero_le _
  · rw [degree_eq_natDegree hp] at this
    exact_mod_cast this.le

variable (hhom : ∀ j : ℤ, j ≠ 0 → ∀ e : T.F m, e ≠ 0 → e′ + (j : T.F m) * T.bX m h a * e ≠ 0)

lemma toPoly_oneLX : GPoly.toPoly (T.MX m h) [(opsM ks m).one] = 1 := by
  rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, (T.MX m h).sem_one, C_1]

lemma toPoly_shiftBX (S : ℕ) :
    GPoly.toPoly (T.MX m h) [(opsM ks m).mul (cstN m (-(S : ℚ))) ((opsM ks m).deriv a)] =
      -C ((S : T.F m) * T.bX m h a) := by
  rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, (T.MX m h).sem_mul, T.sem_cstN m _,
    (T.MX m h).sem_deriv, bX]
  push_cast
  rw [neg_mul, C_neg]

/-- The value of a combination of the Laurent parts. -/
lemma phi_PuX (W : List (Code (m + 2))) (S : ℕ) (e : List ℚ) :
    T.phi m (GPoly.toPoly (T.MX m h) (lcombGP (opsM ks m) (cstN m) e
      ((W.map (eSpX ks m)).map (shiftedL (opsM ks m) S)))) / T.phi m (X ^ S) =
      ∑ i ∈ Finset.range W.length, ((e.getD i 0 : ℚ) : T.F (m + 1)) *
        (T.σX m h (shiftedL (opsM ks m) S (eSpX ks m (W.getD i (opsM ks (m + 1)).zero))) /
          T.phi m (X ^ S)) := by
  rw [toPoly_lcombGP (T.MX m h) (cstN m) (T.sem_cstN m _),
    zipWith_sum_getD (fun (q : ℚ) (p : GPoly (Code (m + 1))) ↦
      C (q : T.F m) * GPoly.toPoly (T.MX m h) p) 0 [] (by simp), map_sum, Finset.sum_div]
  rw [show ((W.map (eSpX ks m)).map (shiftedL (opsM ks m) S)).length = W.length by simp]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  rw [NestTower.getD_map_map (eSpX ks m) (shiftedL (opsM ks m) S) W
    (opsM ks (m + 1)).zero [] hi', map_mul, T.phi_C_ratCastMX, mul_div_assoc]

/-- A weight, with its Laurent part over the common `tˢ`. -/
lemma sem_weightX (W : List (Code (m + 2))) (S : ℕ)
    (hS : ∀ e ∈ W.map (eSpX ks m), e.k ≤ S) (i : ℕ) (hi : i < W.length) :
    (T.MP (m + 1) h).sem (W.getD i (opsM ks (m + 1)).zero) =
      ((T.M1X m h).sem ((eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gn,
        (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gd))′ +
      T.σX m h (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).r /
        T.σX m h (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).s +
      T.σX m h (shiftedL (opsM ks m) S (eSpX ks m (W.getD i (opsM ks (m + 1)).zero))) /
        T.phi m (X ^ S) := by
  obtain ⟨w, hw⟩ : ∃ w, w = W.getD i (opsM ks (m + 1)).zero := ⟨_, rfl⟩
  rw [← hw]
  have hk : (eSpX ks m w).k ≤ S := hS _ (List.mem_map.mpr ⟨w, by
    rw [hw, List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _, rfl⟩)
  have hd := (T.exp_weight_decompX m h hka w).1
  refine hd.trans ?_
  congr 1
  have hinj := T.phi_injX m h
  simp only [σX]
  rw [T.toPoly_shiftedLX m h hka, toPoly_powX]
  obtain ⟨d, hd'⟩ : ∃ d, S = (eSpX ks m w).k + d := ⟨S - (eSpX ks m w).k, by omega⟩
  rw [hd', Nat.add_sub_cancel_left, pow_add, map_mul, map_mul]
  have h1 : T.phi m (X ^ (eSpX ks m w).k) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  have h2 : T.phi m (X ^ d) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
  field_simp

/-- The constant system on the simple parts (for any list `vs` of codes of the simple parts). -/
lemma rel_simpleEX (W : List (Code (m + 2))) (vs : List (Code (m + 2))) (hvl : vs.length = W.length)
    (hvs : ∀ i < W.length, (T.MP (m + 1) h).sem (vs.getD i (opsM ks (m + 1)).zero) =
      T.σX m h (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).r /
        T.σX m h (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).s)
    (u : CPoly ℚ) (hu : u ∈ consys ks (m + 1) vs) :
    ∑ i ∈ Finset.range W.length, ((u.getD i 0 : ℚ) : T.F (m + 1)) *
      (T.σX m h (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).r /
        T.σX m h (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).s) = 0 := by
  have hs := T.consys_sound (m + 1) h vs u hu
  rw [NestTower.zipWith_sum_range _ 0 (opsM ks (m + 1)).zero _ _ (by simp),
    List.length_map, List.length_range, hvl] at hs
  rw [← hs]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i < W.length := Finset.mem_range.mp hi
  rw [NestTower.getD_range_map _ _ hi', T.algebraMap_ratCastMX, hvs i hi']

/-- The value of an output (for any list `G` of codes of the Hermite parts). -/
lemma sem_outEX (W : List (Code (m + 2))) (G : List (Code (m + 2))) (hGl : G.length = W.length)
    (hG : ∀ i < W.length, (T.MP (m + 1) h).sem (G.getD i (opsM ks (m + 1)).zero) =
      (T.M1X m h).sem ((eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gn,
        (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gd))
    (c : List ℚ) (Y : GPoly (Code (m + 1))) (S : ℕ) :
    (T.MP (m + 1) h).sem ((opsM ks (m + 1)).add (lcombCode (opsM ks (m + 1))
      (cstN (m + 1)) c G) ((Y, powX (opsM ks m) S) : Code (m + 2))) =
      ∑ i ∈ Finset.range W.length, ((c.getD i 0 : ℚ) : T.F (m + 1)) *
        (T.M1X m h).sem ((eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gn,
          (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gd) +
      T.phi m (GPoly.toPoly (T.MX m h) Y) / T.phi m (X ^ S) := by
  refine ((T.MP (m + 1) h).sem_add _ _).trans ?_
  congr 1
  · rw [sem_lcombCode (T.MP (m + 1) h) (cstN (m + 1)) (T.sem_cstN (m + 1) h),
      zipWith_sum_getD (fun (q : ℚ) (a : Code (m + 2)) ↦ ((q : ℚ) : T.F (m + 1)) *
        (T.MP (m + 1) h).sem a) 0 (opsM ks (m + 1)).zero (by simp), hGl]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hG i (Finset.mem_range.mp hi)]
  · change T.σX m h Y / T.σX m h (powX (opsM ks m) S) = _
    rw [σX, σX, toPoly_powX]

include hhom in
set_option maxHeartbeats 1600000 in
/-- **The Laurent coefficient loop** `Y′ - S a′ Y = ∑ βᵤ Pᵤ` (`rdeLoop` with `A = 1`, `B = -S a′`):
sound and complete. -/
theorem expLim_loopX (lim : List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (hlim : LimSpec (algebraMap Kc (T.F m)) (T.MX m h) lim)
    (rde : Code (m + 1) → List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (hprde : ∀ f : Code (m + 1),
      RdeSpecK (algebraMap Kc (T.F m)) (T.MX m h) ((T.MX m h).sem f)′ (rde f))
    (Pu : List (GPoly (Code (m + 1)))) (S : ℕ) :
    RStageSound (T.MX m h) (T.bX m h a) [(opsM ks m).one]
        [(opsM ks m).mul (cstN m (-(S : ℚ))) ((opsM ks m).deriv a)] Pu 0 0
        (rdeLoop (opsM ks m) (cstN m) (wK (opsM ks m) (ks m))
          [(opsM ks m).one]
          [(opsM ks m).mul (cstN m (-(S : ℚ))) ((opsM ks m).deriv a)] Pu Pu.length 0
          false (opsM ks m).one (opsM ks m).one
          (fun i ws ↦ if i = S then lim ws ++ [([], (opsM ks m).one)]
            else rde ((opsM ks m).mul (cstN m ((i : ℚ) - S)) a) ws)
          (max ((Pu.map List.length).foldr max 0) S + 1) (rdeInit Pu.length)) ∧
    RStageComplete (algebraMap Kc (T.F m)) (T.MX m h) (T.bX m h a) [(opsM ks m).one]
        [(opsM ks m).mul (cstN m (-(S : ℚ))) ((opsM ks m).deriv a)] Pu 0
        (max ((Pu.map List.length).foldr max 0) S) 0
        (rdeLoop (opsM ks m) (cstN m) (wK (opsM ks m) (ks m))
          [(opsM ks m).one]
          [(opsM ks m).mul (cstN m (-(S : ℚ))) ((opsM ks m).deriv a)] Pu Pu.length 0
          false (opsM ks m).one (opsM ks m).one
          (fun i ws ↦ if i = S then lim ws ++ [([], (opsM ks m).one)]
            else rde ((opsM ks m).mul (cstN m ((i : ℚ) - S)) a) ws)
          (max ((Pu.map List.length).foldr max 0) S + 1) (rdeInit Pu.length)) := by
  have hcst : ∀ q, (T.MX m h).sem (cstN m q) = (q : T.F m) := T.sem_cstN m _
  have hw : GPoly.toPoly (T.MX m h) (wK (opsM ks m) (ks m)) = C (T.bX m h a) * X := T.toPoly_wK_exp m h hka
  have hιd : ∀ κ : Kc, (algebraMap Kc (T.F m) κ)′ = 0 := fun κ ↦ T.deriv_algebraMap_Kc κ
  have hιrat : ∀ q : ℚ, algebraMap Kc (T.F m) (algebraMap ℚ Kc q) = (q : T.F m) :=
    fun q ↦ T.algebraMap_ratCastMX q
  have hAp : GPoly.toPoly (T.MX m h) [(opsM ks m).one] = 1 := by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, (T.MX m h).sem_one, C_1]
  have hBp : GPoly.toPoly (T.MX m h) [(opsM ks m).mul (cstN m (-(S : ℚ))) ((opsM ks m).deriv a)] =
      C (-(S : T.F m) * T.bX m h a) := by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, (T.MX m h).sem_mul, hcst,
      (T.MX m h).sem_deriv, bX]
    push_cast; ring
  have hconst : ∀ y : T.F m, y′ = 0 → ∃ κ : Kc, y = algebraMap Kc (T.F m) κ := fun y hy ↦
    T.const_F y hy
  have hC : ∀ i < Pu.length, (GPoly.toPoly (T.MX m h) (Pu.getD i [])).natDegree ≤
      max ((Pu.map List.length).foldr max 0) S + 0 := fun i hi ↦ by
    refine (T.natDegree_toPoly_le_lengthX m h hka _).trans ?_
    rw [add_zero]
    refine le_trans ?_ (le_max_left _ _)
    refine le_foldr_max _ _ (List.mem_map.mpr ⟨_, ?_, rfl⟩)
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  refine rdeLoop_stage (ι := algebraMap Kc (T.F m)) (M := T.MX m h) (cst := cstN m)
    (b := T.bX m h a) (A := [(opsM ks m).one])
    (B := [(opsM ks m).mul (cstN m (-(S : ℚ))) ((opsM ks m).deriv a)]) (Cl := Pu) (δ := 0) (hcst := hcst) (w := (wK (opsM ks m) (ks m))) (hw := hw)
    (hιd := hιd) (hιrat := hιrat) (by rw [hAp, natDegree_one]) (by rw [hBp, natDegree_C])
    false (opsM ks m).one (opsM ks m).one _ (fun h' ↦ by cases h') (fun _ ↦ ⟨?_, ?_, fun k ↦ ?_⟩) _ _ _
    (rdeInit_sound (M := T.MX m h) (T.bX m h a) _ _ Pu 0 _ hC)
    (rdeInit_complete (algebraMap Kc (T.F m)) (M := T.MX m h) (T.bX m h a) _ _ Pu 0 _)
  · rw [hAp, (T.MX m h).sem_one, coeff_one_zero]
  · rw [(T.MX m h).sem_one]; exact one_ne_zero
  · rw [hAp, hBp, coeff_one_zero, coeff_C_zero]
    by_cases hk : k = S
    · subst hk
      refine ⟨0, fun z ↦ by ring, ?_⟩
      simp only [if_pos]
      exact rdeSpec_of_limSpec (algebraMap Kc (T.F m)) (T.MX m h) lim hlim hconst
    · refine ⟨((T.MX m h).sem ((opsM ks m).mul (cstN m ((k : ℚ) - S)) a))′, fun z ↦ ?_, ?_⟩
      · rw [(T.MX m h).sem_mul, hcst, Derivation.leibniz, deriv_ratCastK, bX]
        simp only [smul_eq_mul, mul_zero, add_zero]
        push_cast
        ring
      · simp only [hk, if_false]
        exact hprde _

include hhom in
set_option maxHeartbeats 6400000 in
/-- **Parametric limited integration over an exponential level is sound and complete**, given a
sound and complete solver one level down and the Risch equations one level down. -/
theorem expLimStepX_spec (lim : List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (hlim : LimSpec (algebraMap Kc (T.F m)) (T.MX m h) lim)
    (rde : Code (m + 1) → List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (hprde : ∀ f : Code (m + 1),
      RdeSpecK (algebraMap Kc (T.F m)) (T.MX m h) ((T.MX m h).sem f)′ (rde f)) :
    LimSpec (algebraMap Kc (T.F (m + 1))) (T.MP (m + 1) h) (expLimStepX ks m a lim rde) := by
  classical
  refine ⟨fun W r hr ↦ ?_, fun W c hc z hz ↦ ?_⟩
  · -- soundness
      set O := opsM ks m with hO
      have hm : T.Tr m := fun i hi ↦ h i (by omega)
      have hcst : ∀ q, (T.MX m h).sem (cstN m q) = (q : T.F m) := T.sem_cstN m _
      have hw : GPoly.toPoly (T.MX m h) (wK O (ks m)) = C (T.bX m h a) * X := T.toPoly_wK_exp m h hka
      -- the pieces of the algorithm
      obtain ⟨Sp, hSp⟩ : ∃ Sp, Sp = W.map (eSpX ks m) := ⟨_, rfl⟩
      obtain ⟨U, hU⟩ : ∃ U, U = consys ks (m + 1)
          (Sp.map fun e ↦ ((e.r, e.s) : Code (m + 2))) := ⟨_, rfl⟩
      obtain ⟨Ev, hEv⟩ : ∃ Ev : List (List ℚ), Ev = U.map fun u ↦
          (List.range W.length).map fun i ↦ u.getD i 0 := ⟨_, rfl⟩
      obtain ⟨S, hS⟩ : ∃ S, S = laurentS Sp := ⟨_, rfl⟩
      obtain ⟨Ls, hLs⟩ : ∃ Ls, Ls = Sp.map (shiftedL O S) := ⟨_, rfl⟩
      obtain ⟨Pu, hPu⟩ : ∃ Pu, Pu = Ev.map fun e ↦ lcombGP O (cstN m) e Ls := ⟨_, rfl⟩
      obtain ⟨top, htop⟩ : ∃ top, top = (Pu.map List.length).foldr max 0 := ⟨_, rfl⟩
      obtain ⟨A, hA⟩ : ∃ A : GPoly (Code (m + 1)), A = [O.one] := ⟨_, rfl⟩
      obtain ⟨B, hB⟩ : ∃ B : GPoly (Code (m + 1)), B = [O.mul (cstN m (-(S : ℚ))) (O.deriv a)] :=
        ⟨_, rfl⟩
      obtain ⟨solve, hsolve⟩ : ∃ solve : ℕ → List (Code (m + 1)) → List (List ℚ × Code (m + 1)),
          solve = fun i ws ↦ if i = S then lim ws ++ [([], O.one)]
            else rde (O.mul (cstN m ((i : ℚ) - S)) a) ws := ⟨_, rfl⟩
      obtain ⟨init, hinit⟩ : ∃ init, init = (List.range Ev.length).map fun i ↦
          (unitV Ev.length i, ([] : GPoly (Code (m + 1)))) := ⟨_, rfl⟩
      obtain ⟨Bs, hBs⟩ : ∃ Bs, Bs = rdeLoop O (cstN m) (wK O (ks m)) A B Pu Ev.length 0
          false O.one O.one solve (max top S + 1) init := ⟨_, rfl⟩
      obtain ⟨F', hF'⟩ : ∃ F' : List ℚ × GPoly (Code (m + 1)) → List ℚ × Code (m + 2), F' = fun b ↦
          (vcomb W.length b.1 Ev, (opsM ks (m + 1)).add (lcombCode (opsM ks (m + 1))
            (cstN (m + 1)) (vcomb W.length b.1 Ev) (Sp.map fun e ↦ ((e.gn, e.gd) : Code (m + 2))))
            ((b.2, powX O S) : Code (m + 2))) := ⟨_, rfl⟩
      have hunf : expLimStepX ks m a lim rde W = Bs.map F' := by
        subst hF' hBs hinit hsolve hB hA htop hPu hLs hS hEv hU hSp
        rfl
      rw [hunf] at hr
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
      have hlPu : Pu.length = Ev.length := by rw [hPu, List.length_map]
      have hBs' : Bs = rdeLoop O (cstN m) (wK O (ks m)) [O.one]
          [O.mul (cstN m (-(S : ℚ))) (O.deriv a)] Pu Pu.length 0 false O.one O.one
          (fun i ws ↦ if i = S then lim ws ++ [([], O.one)]
            else rde (O.mul (cstN m ((i : ℚ) - S)) a) ws)
          (max ((Pu.map List.length).foldr max 0) S + 1) (rdeInit Pu.length) := by
        rw [hBs, hA, hB, hsolve, htop, hinit, hlPu]; rfl
      obtain ⟨-, -, hres⟩ := (T.expLim_loopX m h hka hhom lim hlim rde hprde Pu S).1 b (hBs' ▸ hb)
      have hY : implicitDeriv (C (T.bX m h a) * X) (GPoly.toPoly (T.MX m h) b.2) -
          C ((S : T.F m) * T.bX m h a) * GPoly.toPoly (T.MX m h) b.2 =
          ∑ u ∈ Finset.range Pu.length, C ((b.1.getD u 0 : ℚ) : T.F m) *
            GPoly.toPoly (T.MX m h) (Pu.getD u []) := by
        have h0 : resQ (T.MX m h) (T.bX m h a) [O.one] [O.mul (cstN m (-(S : ℚ))) (O.deriv a)] Pu
            b.1 (GPoly.toPoly (T.MX m h) b.2) = 0 :=
          Polynomial.ext fun d ↦ by rw [hres d (by omega), coeff_zero]
        unfold resQ at h0
        rw [T.toPoly_oneLX m h hka, T.toPoly_shiftBX m h hka, one_mul] at h0
        linear_combination h0
      -- the pieces as functions of `i`
      have hlS : ∀ e ∈ W.map (eSpX ks m), e.k ≤ S := fun e he ↦ by
        rw [hS, hSp]; exact k_le_laurentSX m hka _ e he
      have hGl : (Sp.map fun e ↦ ((e.gn, e.gd) : Code (m + 2))).length = W.length := by
        rw [hSp]; exact NestTower.len_map_map _ _ W
      have hG : ∀ i < W.length, (T.MP (m + 1) h).sem ((Sp.map fun e ↦ ((e.gn, e.gd) : Code (m + 2))).getD i
          (opsM ks (m + 1)).zero) = (T.M1X m h).sem ((eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gn,
            (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gd) := fun i hi ↦ by
        rw [hSp]
        exact congrArg (T.MP (m + 1) h).sem (NestTower.getD_map_map (eSpX ks m)
          (fun e ↦ ((e.gn, e.gd) : Code (m + 2))) W (opsM ks (m + 1)).zero
          (opsM ks (m + 1)).zero hi)
      have hvl : (Sp.map fun e ↦ ((e.r, e.s) : Code (m + 2))).length = W.length := by
        rw [hSp]; exact NestTower.len_map_map _ _ W
      have hvs : ∀ i < W.length, (T.MP (m + 1) h).sem ((Sp.map fun e ↦ ((e.r, e.s) : Code (m + 2))).getD i
          (opsM ks (m + 1)).zero) = T.σX m h (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).r /
            T.σX m h (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).s := fun i hi ↦ by
        rw [hSp]
        exact congrArg (T.MP (m + 1) h).sem (NestTower.getD_map_map (eSpX ks m)
          (fun e ↦ ((e.r, e.s) : Code (m + 2))) W (opsM ks (m + 1)).zero
          (opsM ks (m + 1)).zero hi)
      set n := W.length with hn
      set gv : ℕ → T.F (m + 1) := fun i ↦ (T.M1X m h).sem ((eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gn,
        (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gd) with hgv
      set rv : ℕ → T.F (m + 1) := fun i ↦ T.σX m h (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).r /
        T.σX m h (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).s with hrv
      set lv : ℕ → T.F (m + 1) := fun i ↦ T.σX m h (shiftedL O S (eSpX ks m (W.getD i (opsM ks (m + 1)).zero))) /
        T.phi m (X ^ S) with hlv
      set Eq' : ℕ → ℕ → ℚ := fun u i ↦ (U.getD u []).getD i 0 with hEq'
      have hEvE : ∀ u < Ev.length, ∀ i < n, (Ev.getD u []).getD i 0 = Eq' u i := fun u hu i hi ↦ by
        rw [hEv, NestTower.getD_map' _ U [] [] (by simpa [hEv] using hu), NestTower.getD_range_map _ _ hi]
      have hlEv : Ev.length = U.length := by rw [hEv, List.length_map]
      have hPuv : ∀ u < Ev.length, T.phi m (GPoly.toPoly (T.MX m h) (Pu.getD u [])) / T.phi m (X ^ S) =
          ∑ i ∈ Finset.range n, ((Eq' u i : ℚ) : T.F (m + 1)) * lv i := fun u hu ↦ by
        rw [hPu, NestTower.getD_map' _ Ev [] [] hu, hLs, hSp, T.phi_PuX m h hka W S]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [hEvE u hu i (Finset.mem_range.mp hi)]
      have hrel : ∀ u < U.length, ∑ i ∈ Finset.range n, ((Eq' u i : ℚ) : T.F (m + 1)) * rv i = 0 := by
        intro u hu
        have hmem : U.getD u [] ∈ U := by rw [List.getD_eq_getElem _ _ hu]; exact List.getElem_mem _
        exact T.rel_simpleEX m h hka W _ hvl hvs (U.getD u []) (hU ▸ hmem)
      have hc : ∀ i < n, ((vcomb n b.1 Ev).getD i 0 : ℚ) = ∑ u ∈ Finset.range Ev.length,
          b.1.getD u 0 * Eq' u i := fun i hi ↦ by
        rw [getD_vcomb, if_pos hi]
        refine Finset.sum_congr rfl fun u hu ↦ ?_
        rw [hEvE u (Finset.mem_range.mp hu) i hi]
      -- the derivative of the output
      have hso : (T.MP (m + 1) h).sem (F' b).2 = ∑ i ∈ Finset.range W.length,
          (((vcomb n b.1 Ev).getD i 0 : ℚ) : T.F (m + 1)) * gv i +
          T.phi m (GPoly.toPoly (T.MX m h) b.2) / T.phi m (X ^ S) := by
        rw [hF']; exact T.sem_outEX m h hka W _ hGl hG _ _ S
      have hF1 : (F' b).1 = vcomb n b.1 Ev := by rw [hF']
      rw [hso, hF1, map_add, T.deriv_sum_ratCastMX, T.deriv_laurent_towerX m h hka, hY,
        map_sum, Finset.sum_div, sQ]
      have hW : ∀ i ∈ Finset.range W.length, ((((vcomb n b.1 Ev).getD i 0 : ℚ)) : T.F (m + 1)) *
          (T.MP (m + 1) h).sem (W.getD i (opsM ks (m + 1)).zero) =
          (((vcomb n b.1 Ev).getD i 0 : ℚ) : T.F (m + 1)) * (gv i)′ +
          ((((vcomb n b.1 Ev).getD i 0 : ℚ)) : T.F (m + 1)) * rv i +
          ((((vcomb n b.1 Ev).getD i 0 : ℚ)) : T.F (m + 1)) * lv i := fun i hi ↦ by
        rw [T.sem_weightX m h hka W S hlS i (Finset.mem_range.mp hi)]
        simp only [hgv, hrv, hlv]
        ring
      have hr0 : ∑ i ∈ Finset.range W.length, (((vcomb n b.1 Ev).getD i 0 : ℚ) : T.F (m + 1)) * rv i = 0 := by
        have e : ∀ i ∈ Finset.range W.length, (((vcomb n b.1 Ev).getD i 0 : ℚ) : T.F (m + 1)) * rv i =
            ∑ u ∈ Finset.range Ev.length, ((b.1.getD u 0 : ℚ) : T.F (m + 1)) *
              (((Eq' u i : ℚ) : T.F (m + 1)) * rv i) := fun i hi ↦ by
          rw [hc i (Finset.mem_range.mp hi)]; push_cast; rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun u _ ↦ by ring
        rw [Finset.sum_congr rfl e, Finset.sum_comm]
        refine Finset.sum_eq_zero fun u hu ↦ ?_
        rw [← Finset.mul_sum, hrel u (by rw [← hlEv]; exact Finset.mem_range.mp hu), mul_zero]
      have hl : ∑ u ∈ Finset.range Pu.length, T.phi m (C ((b.1.getD u 0 : ℚ) : T.F m) *
          GPoly.toPoly (T.MX m h) (Pu.getD u [])) / T.phi m (X ^ S) =
          ∑ i ∈ Finset.range W.length, (((vcomb n b.1 Ev).getD i 0 : ℚ) : T.F (m + 1)) * lv i := by
        have e2 : ∀ u ∈ Finset.range Pu.length, T.phi m (C ((b.1.getD u 0 : ℚ) : T.F m) *
            GPoly.toPoly (T.MX m h) (Pu.getD u [])) / T.phi m (X ^ S) =
            ∑ i ∈ Finset.range n, ((b.1.getD u 0 : ℚ) : T.F (m + 1)) *
              (((Eq' u i : ℚ) : T.F (m + 1)) * lv i) := fun u hu ↦ by
          rw [map_mul, T.phi_C_ratCastMX, mul_div_assoc,
            hPuv u (by rw [← hlPu]; exact Finset.mem_range.mp hu), Finset.mul_sum]
        rw [Finset.sum_congr rfl e2, Finset.sum_comm, hlPu]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [hc i (Finset.mem_range.mp hi)]
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ ↦ by ring
      rw [Finset.sum_congr rfl hW, Finset.sum_add_distrib, Finset.sum_add_distrib, hr0, hl]
      ring
  · -- completeness
      set O := opsM ks m with hO
      have hm : T.Tr m := fun i hi ↦ h i (by omega)
      have hcst : ∀ q, (T.MX m h).sem (cstN m q) = (q : T.F m) := T.sem_cstN m _
      have hw : GPoly.toPoly (T.MX m h) (wK O (ks m)) = C (T.bX m h a) * X := T.toPoly_wK_exp m h hka
      -- the pieces of the algorithm
      obtain ⟨Sp, hSp⟩ : ∃ Sp, Sp = W.map (eSpX ks m) := ⟨_, rfl⟩
      obtain ⟨U, hU⟩ : ∃ U, U = consys ks (m + 1)
          (Sp.map fun e ↦ ((e.r, e.s) : Code (m + 2))) := ⟨_, rfl⟩
      obtain ⟨Ev, hEv⟩ : ∃ Ev : List (List ℚ), Ev = U.map fun u ↦
          (List.range W.length).map fun i ↦ u.getD i 0 := ⟨_, rfl⟩
      obtain ⟨S, hS⟩ : ∃ S, S = laurentS Sp := ⟨_, rfl⟩
      obtain ⟨Ls, hLs⟩ : ∃ Ls, Ls = Sp.map (shiftedL O S) := ⟨_, rfl⟩
      obtain ⟨Pu, hPu⟩ : ∃ Pu, Pu = Ev.map fun e ↦ lcombGP O (cstN m) e Ls := ⟨_, rfl⟩
      obtain ⟨top, htop⟩ : ∃ top, top = (Pu.map List.length).foldr max 0 := ⟨_, rfl⟩
      obtain ⟨A, hA⟩ : ∃ A : GPoly (Code (m + 1)), A = [O.one] := ⟨_, rfl⟩
      obtain ⟨B, hB⟩ : ∃ B : GPoly (Code (m + 1)), B = [O.mul (cstN m (-(S : ℚ))) (O.deriv a)] :=
        ⟨_, rfl⟩
      obtain ⟨solve, hsolve⟩ : ∃ solve : ℕ → List (Code (m + 1)) → List (List ℚ × Code (m + 1)),
          solve = fun i ws ↦ if i = S then lim ws ++ [([], O.one)]
            else rde (O.mul (cstN m ((i : ℚ) - S)) a) ws := ⟨_, rfl⟩
      obtain ⟨init, hinit⟩ : ∃ init, init = (List.range Ev.length).map fun i ↦
          (unitV Ev.length i, ([] : GPoly (Code (m + 1)))) := ⟨_, rfl⟩
      obtain ⟨Bs, hBs⟩ : ∃ Bs, Bs = rdeLoop O (cstN m) (wK O (ks m)) A B Pu Ev.length 0
          false O.one O.one solve (max top S + 1) init := ⟨_, rfl⟩
      obtain ⟨F', hF'⟩ : ∃ F' : List ℚ × GPoly (Code (m + 1)) → List ℚ × Code (m + 2), F' = fun b ↦
          (vcomb W.length b.1 Ev, (opsM ks (m + 1)).add (lcombCode (opsM ks (m + 1))
            (cstN (m + 1)) (vcomb W.length b.1 Ev) (Sp.map fun e ↦ ((e.gn, e.gd) : Code (m + 2))))
            ((b.2, powX O S) : Code (m + 2))) := ⟨_, rfl⟩
      have hunf : expLimStepX ks m a lim rde W = Bs.map F' := by
        subst hF' hBs hinit hsolve hB hA htop hPu hLs hS hEv hU hSp
        rfl
      rw [hunf]
      have hlPu : Pu.length = Ev.length := by rw [hPu, List.length_map]
      have hBs' : Bs = rdeLoop O (cstN m) (wK O (ks m)) [O.one]
          [O.mul (cstN m (-(S : ℚ))) (O.deriv a)] Pu Pu.length 0 false O.one O.one
          (fun i ws ↦ if i = S then lim ws ++ [([], O.one)]
            else rde (O.mul (cstN m ((i : ℚ) - S)) a) ws)
          (max ((Pu.map List.length).foldr max 0) S + 1) (rdeInit Pu.length) := by
        rw [hBs, hA, hB, hsolve, htop, hinit, hlPu]; rfl
      have hloop := (T.expLim_loopX m h hka hhom lim hlim rde hprde Pu S).2
      rw [← hBs', ← htop] at hloop
      have hlS : ∀ e ∈ W.map (eSpX ks m), e.k ≤ S := fun e he ↦ by
        rw [hS, hSp]; exact k_le_laurentSX m hka _ e he
      have hGl : (Sp.map fun e ↦ ((e.gn, e.gd) : Code (m + 2))).length = W.length := by
        rw [hSp]; exact NestTower.len_map_map _ _ W
      have hG : ∀ i < W.length, (T.MP (m + 1) h).sem ((Sp.map fun e ↦ ((e.gn, e.gd) : Code (m + 2))).getD i
          (opsM ks (m + 1)).zero) = (T.M1X m h).sem ((eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gn,
            (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).gd) := fun i hi ↦ by
        rw [hSp]
        exact congrArg (T.MP (m + 1) h).sem (NestTower.getD_map_map (eSpX ks m)
          (fun e ↦ ((e.gn, e.gd) : Code (m + 2))) W (opsM ks (m + 1)).zero
          (opsM ks (m + 1)).zero hi)
      have hvl : (Sp.map fun e ↦ ((e.r, e.s) : Code (m + 2))).length = W.length := by
        rw [hSp]; exact NestTower.len_map_map _ _ W
      have hvs : ∀ i < W.length, (T.MP (m + 1) h).sem ((Sp.map fun e ↦ ((e.r, e.s) : Code (m + 2))).getD i
          (opsM ks (m + 1)).zero) = T.σX m h (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).r /
            T.σX m h (eSpX ks m (W.getD i (opsM ks (m + 1)).zero)).s := fun i hi ↦ by
        rw [hSp]
        exact congrArg (T.MP (m + 1) h).sem (NestTower.getD_map_map (eSpX ks m)
          (fun e ↦ ((e.r, e.s) : Code (m + 2))) W (opsM ks (m + 1)).zero
          (opsM ks (m + 1)).zero hi)
      set n := W.length with hn
      set ι' := algebraMap Kc (T.F (m + 1)) with hι'
      set ι := algebraMap Kc (T.F m) with hι
      set ew : ℕ → ExpSplit (Code (m + 1)) := fun i ↦ eSpX ks m (W.getD i (opsM ks (m + 1)).zero)
        with hew
      set gv : ℕ → T.F (m + 1) := fun i ↦ (T.M1X m h).sem ((ew i).gn, (ew i).gd) with hgv
      set rv : ℕ → T.F (m + 1) := fun i ↦ T.σX m h (ew i).r / T.σX m h (ew i).s with hrv
      set lv : ℕ → T.F (m + 1) := fun i ↦ T.σX m h (shiftedL O S (ew i)) / T.phi m (X ^ S) with hlv
      set Eq' : ℕ → ℕ → ℚ := fun u i ↦ (U.getD u []).getD i 0 with hEq'
      have hEvE : ∀ u < Ev.length, ∀ i < n, (Ev.getD u []).getD i 0 = Eq' u i := fun u hu i hi ↦ by
        rw [hEv, NestTower.getD_map' _ U [] [] (by simpa [hEv] using hu), NestTower.getD_range_map _ _ hi]
      have hlEv : Ev.length = U.length := by rw [hEv, List.length_map]
      have hPuv : ∀ u < Ev.length, T.phi m (GPoly.toPoly (T.MX m h) (Pu.getD u [])) / T.phi m (X ^ S) =
          ∑ i ∈ Finset.range n, ((Eq' u i : ℚ) : T.F (m + 1)) * lv i := fun u hu ↦ by
        rw [hPu, NestTower.getD_map' _ Ev [] [] hu, hLs, hSp, T.phi_PuX m h hka W S]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [hEvE u hu i (Finset.mem_range.mp hi)]
      have hinj := T.phi_injX m h
      have hXS : T.phi m (X ^ S) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ X_ne_zero)
      -- the equation for `z - G`
      set G := ∑ i ∈ Finset.range n, ι' (c.getD i 0) * gv i with hGd
      have hdec : ∀ i < n, (T.MP (m + 1) h).sem (W.getD i (opsM ks (m + 1)).zero) =
          (gv i)′ + rv i + lv i := fun i hi ↦ T.sem_weightX m h hka W S hlS i hi
      set P := ∑ i ∈ Finset.range n, C (ι (c.getD i 0)) * GPoly.toPoly (T.MX m h) (shiftedL O S (ew i))
        with hP
      set l := (List.range n).map fun i ↦ (C (ι (c.getD i 0)) * GPoly.toPoly (T.MX m h) (ew i).r,
        GPoly.toPoly (T.MX m h) (ew i).s) with hl
      have hlsum : (l.map fun p ↦ T.phi m p.1 / T.phi m p.2).sum =
          ∑ i ∈ Finset.range n, ι' (c.getD i 0) * rv i := by
        rw [hl, List.map_map, NestTower.list_sum_map_range]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [Function.comp_apply, map_mul, hrv, σX]
        rw [T.phi_C, show (IntermediateField.inclusion (T.le_succ m)) (ι (c.getD i 0)) = ι' (c.getD i 0) from rfl]
        ring
      have hPv : T.phi m P / T.phi m (X ^ S) = ∑ i ∈ Finset.range n, ι' (c.getD i 0) * lv i := by
        rw [hP, map_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [map_mul, T.phi_C, mul_div_assoc]
        rfl
      have hzG : (z - G)′ = T.phi m P / T.phi m (X ^ S) + (l.map fun p ↦ T.phi m p.1 / T.phi m p.2).sum := by
        rw [hPv, hlsum, map_sub, hz, hGd, T.deriv_sum_KcMX, sC, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [hdec i (Finset.mem_range.mp hi)]
        ring
      have hwd : ∀ i, Squarefree (GPoly.toPoly (T.MX m h) (ew i).s) ∧ ¬X ∣ GPoly.toPoly (T.MX m h) (ew i).s ∧
          (GPoly.toPoly (T.MX m h) (ew i).r).degree < (GPoly.toPoly (T.MX m h) (ew i).s).degree :=
        fun i ↦ (T.exp_weight_decompX m h hka _).2
      obtain ⟨hsum0, Y, hYz, hYd⟩ := T.tower_laurent_stepX m h hka hhom P S l
        (fun p hp ↦ by obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp; exact (hwd i).1)
        (fun p hp ↦ by obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp; exact (hwd i).2.1)
        (fun p hp ↦ by
          obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
          exact lt_of_le_of_lt (by rw [← smul_eq_C_mul]; exact degree_smul_le _ _) (hwd i).2.2)
        (z - G) hzG
      rw [hlsum] at hsum0
      have hqK : ∀ q : ℚ, ι' (algebraMap ℚ Kc q) = (q : T.F (m + 1)) := fun q ↦ T.algebraMap_ratCastMX q
      -- the constant system on the simple parts
      obtain ⟨vs, hvsd⟩ : ∃ vs : List (Code (m + 2)), vs = Sp.map fun e ↦ ((e.r, e.s) : Code (m + 2)) :=
        ⟨_, rfl⟩
      have hvl' : vs.length = W.length := by rw [hvsd]; exact hvl
      have hvs' : ∀ i < W.length, (T.MP (m + 1) h).sem (vs.getD i (opsM ks (m + 1)).zero) = rv i :=
        fun i hi ↦ by rw [hvsd]; exact hvs i hi
      have hUv : U = consys ks (m + 1) vs := by rw [hU, hvsd]; rfl
      have h0 : (List.zipWith (fun c v ↦ algebraMap Kc (T.F (m + 1)) c * (T.MP (m + 1) h).sem v)
          ((List.range vs.length).map fun i ↦ c.getD i 0) vs).sum = 0 := by
        rw [NestTower.zipWith_sum_range _ 0 (opsM ks (m + 1)).zero _ _ (by simp),
          List.length_map, List.length_range, hvl', ← hsum0]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hi),
          hvs' i (Finset.mem_range.mp hi)]
      obtain ⟨γ0, hγl, hγ⟩ := T.consys_complete (m + 1) h vs _ (by simp) h0
      rw [← hUv] at hγl hγ
      have hγc : ∀ i < n, c.getD i 0 = ∑ u ∈ Finset.range U.length,
          γ0.getD u 0 * algebraMap ℚ Kc (Eq' u i) := fun i hi ↦ by
        have := hγ i
        rw [NestTower.getD_range_map _ _ (by rw [hvl']; exact hi),
          NestTower.zipWith_sum_range _ 0 [] _ _ hγl, hγl] at this
        exact this
      -- `P` is the combination of the `Pᵤ`
      have hPP : P = ∑ u ∈ Finset.range Pu.length, C (ι (γ0.getD u 0)) *
          GPoly.toPoly (T.MX m h) (Pu.getD u []) := by
        apply hinj
        have e2 : T.phi m (∑ u ∈ Finset.range Pu.length, C (ι (γ0.getD u 0)) *
            GPoly.toPoly (T.MX m h) (Pu.getD u [])) / T.phi m (X ^ S) =
            ∑ i ∈ Finset.range n, ι' (c.getD i 0) * lv i := by
          rw [map_sum, Finset.sum_div]
          have e : ∀ u ∈ Finset.range Pu.length, T.phi m (C (ι (γ0.getD u 0)) *
              GPoly.toPoly (T.MX m h) (Pu.getD u [])) / T.phi m (X ^ S) =
              ∑ i ∈ Finset.range n, ι' (γ0.getD u 0) * (((Eq' u i : ℚ) : T.F (m + 1)) * lv i) :=
            fun u hu ↦ by
              rw [map_mul, T.phi_C, mul_div_assoc, hPuv u (by rw [← hlPu]; exact Finset.mem_range.mp hu),
                Finset.mul_sum]
              rfl
          rw [Finset.sum_congr rfl e, Finset.sum_comm]
          refine Finset.sum_congr rfl fun i hi ↦ ?_
          rw [hγc i (Finset.mem_range.mp hi), map_sum, Finset.sum_mul, hlPu, hlEv]
          refine Finset.sum_congr rfl fun u _ ↦ ?_
          rw [map_mul, hqK]
          ring
        have := hPv.trans e2.symm
        rwa [div_left_inj' hXS] at this
      -- no Risch equation `e′ + j a′ e = 0`, `j ≠ 0`
      have hhomZ := hhom
      -- the degree of `Y`
      have hPcoef : ∀ i, top < i → P.coeff i = 0 := fun i hi ↦ by
        rw [hPP, finset_sum_coeff]
        refine Finset.sum_eq_zero fun u hu ↦ ?_
        rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
        refine lt_of_le_of_lt (T.natDegree_toPoly_le_lengthX m h hka _) (lt_of_le_of_lt ?_ hi)
        rw [htop]
        refine le_foldr_max _ _ (List.mem_map.mpr ⟨_, ?_, rfl⟩)
        rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hu)]; exact List.getElem_mem _
      have hYdeg : Y.natDegree ≤ max top S := by
        rw [natDegree_le_iff_coeff_eq_zero]
        intro i hi
        have hi' : max top S < i := by exact_mod_cast hi
        have hc := congrArg (fun Q : (T.F m)[X] ↦ Q.coeff i) hYd
        simp only [coeff_sub, coeff_C_mul, coeff_implicitDeriv_C_mul_X] at hc
        rw [hPcoef i (by omega)] at hc
        by_contra hY0
        refine hhomZ ((i : ℤ) - S) (by omega) (Y.coeff i) hY0 ?_
        push_cast
        linear_combination hc
      -- the coefficient loop
      have hγ0cut : ∀ i, Pu.length ≤ i → γ0.getD i 0 = 0 := fun i hi ↦
        List.getD_eq_default _ _ (by rw [hγl, ← hlEv, ← hlPu]; exact hi)
      obtain ⟨γ, hγγ, hYc⟩ := hloop γ0 hγ0cut Y hYdeg (fun d _ ↦ by
        have : resC ι (T.MX m h) (T.bX m h a) [O.one] [O.mul (cstN m (-(S : ℚ))) (O.deriv a)] Pu γ0 Y = 0 := by
          unfold resC
          rw [T.toPoly_oneLX m h hka, T.toPoly_shiftBX m h hka, one_mul, ← hPP]
          linear_combination hYd
        rw [this, coeff_zero])
      have hYs : Y = ∑ l ∈ Finset.range Bs.length, C (ι (γ.getD l 0)) *
          GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2 := by
        ext i
        rw [hYc i (Nat.zero_le _), finset_sum_coeff]
        simp only [coeff_C_mul]
      -- the output
      have hlen : (Bs.map F').length = Bs.length := List.length_map _
      have hgetD : ∀ k < Bs.length, (Bs.map F').getD k ([], (opsM ks (m + 1)).zero) =
          F' (Bs.getD k ([], [])) := fun k hk ↦ NestTower.getD_map' _ _ ([], []) _ hk
      have hF1 : ∀ b, (F' b).1 = vcomb n b.1 Ev := fun b ↦ by rw [hF']
      have hF2 : ∀ b, (T.MP (m + 1) h).sem (F' b).2 = ∑ i ∈ Finset.range n,
          (((vcomb n b.1 Ev).getD i 0 : ℚ) : T.F (m + 1)) * gv i +
          T.phi m (GPoly.toPoly (T.MX m h) b.2) / T.phi m (X ^ S) := fun b ↦ by
        rw [hF']; exact T.sem_outEX m h hka W _ hGl hG _ _ S
      have hcoefK : ∀ i < n, c.getD i 0 = ∑ k ∈ Finset.range Bs.length, γ.getD k 0 *
          algebraMap ℚ Kc ((vcomb n (Bs.getD k ([], [])).1 Ev).getD i 0) := by
        intro i hi
        rw [hγc i hi]
        have e : ∀ u ∈ Finset.range U.length, γ0.getD u 0 * algebraMap ℚ Kc (Eq' u i) =
            ∑ k ∈ Finset.range Bs.length, γ.getD k 0 *
              algebraMap ℚ Kc ((Bs.getD k ([], [])).1.getD u 0 * Eq' u i) := fun u _ ↦ by
          rw [hγγ u, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [map_mul]; ring
        rw [Finset.sum_congr rfl e, Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [← Finset.mul_sum, ← map_sum, getD_vcomb, if_pos hi, hlEv]
        congr 2
        refine Finset.sum_congr rfl fun u hu ↦ ?_
        rw [hEvE u (by rw [hlEv]; exact Finset.mem_range.mp hu) i hi]
      refine ⟨γ, fun i ↦ ?_, ?_⟩
      · rw [hlen]
        by_cases hi : i < n
        · rw [hcoefK i hi]
          refine Finset.sum_congr rfl fun k hk ↦ ?_
          rw [hgetD k (Finset.mem_range.mp hk), hF1]
        · rw [hc i (by omega)]
          symm
          refine Finset.sum_eq_zero fun k hk ↦ ?_
          rw [hgetD k (Finset.mem_range.mp hk), hF1, getD_vcomb, if_neg hi, map_zero, mul_zero]
      · suffices hz0 : z - ∑ k ∈ Finset.range (Bs.map F').length, ι' (γ.getD k 0) *
            (T.MP (m + 1) h).sem ((Bs.map F').getD k ([], (opsM ks (m + 1)).zero)).2 = 0 by
          rw [hz0, map_zero]
        rw [hlen]
        have e : ∀ k ∈ Finset.range Bs.length, ι' (γ.getD k 0) *
            (T.MP (m + 1) h).sem ((Bs.map F').getD k ([], (opsM ks (m + 1)).zero)).2 =
            ι' (γ.getD k 0) * (∑ i ∈ Finset.range n,
              (((vcomb n (Bs.getD k ([], [])).1 Ev).getD i 0 : ℚ) : T.F (m + 1)) * gv i) +
            ι' (γ.getD k 0) * (T.phi m (GPoly.toPoly (T.MX m h) (Bs.getD k ([], [])).2) /
              T.phi m (X ^ S)) := fun k hk ↦ by
          rw [hgetD k (Finset.mem_range.mp hk), hF2, mul_add]
        rw [Finset.sum_congr rfl e, Finset.sum_add_distrib]
        have hGs : G = ∑ k ∈ Finset.range Bs.length, ι' (γ.getD k 0) * (∑ i ∈ Finset.range n,
            (((vcomb n (Bs.getD k ([], [])).1 Ev).getD i 0 : ℚ) : T.F (m + 1)) * gv i) := by
          rw [hGd]
          have e' : ∀ i ∈ Finset.range n, ι' (c.getD i 0) * gv i = ∑ k ∈ Finset.range Bs.length,
              ι' (γ.getD k 0) * ((((vcomb n (Bs.getD k ([], [])).1 Ev).getD i 0 : ℚ) : T.F (m + 1)) *
                gv i) := fun i hi ↦ by
            rw [hcoefK i (Finset.mem_range.mp hi), map_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            rw [map_mul, hqK]; ring
          rw [Finset.sum_congr rfl e', Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [Finset.mul_sum]
        have hYv : T.phi m Y / T.phi m (X ^ S) = ∑ k ∈ Finset.range Bs.length, ι' (γ.getD k 0) *
            (T.phi m (GPoly.toPoly (T.MX m h) (Bs.getD k ([], [])).2) / T.phi m (X ^ S)) := by
          rw [hYs, map_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [map_mul, T.phi_C, mul_div_assoc]
          rfl
        have hz' : z = G + T.phi m Y / T.phi m (X ^ S) := by rw [← hYz]; ring
        rw [hz', hGs, hYv]
        ring

end StepSpec

end NestMTower

end Tower.NestM
