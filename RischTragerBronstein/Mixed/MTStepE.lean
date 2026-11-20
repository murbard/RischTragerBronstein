import RischTragerBronstein.Mixed.MTStepP

/-!
# Mixed towers over a curve: the inductive step at an exponential level

`MTower.elM_step_exp`: at an exponential level `k` (`tₖ = exp a`), `elM (k + 1)` decides. The
powers of `t` are split off the denominator, the rest is Hermite-reduced; by `expGen_decides`
(with the lift property `expLift`) the integrand is elementary iff the residue test holds, every
Risch equation `y′ + (j − n) a′ y = Λⱼ` (`j ≠ n`) is solvable at level `k` (decided by `prdeC`,
`rdeOKM_iff`), and the constant term `Λₙ` is elementary (decided at level `k`, `constDec`).
The port of `ExpCurveMain.integrateExpCurve_decides` from the curve to a mixed tower.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 8000000 in
/-- **The inductive step at an exponential level.** -/
theorem elM_step_exp [IsAlgClosed Cc] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (k : ℕ) (IH : ELHypM.{u} Fc ks lv k) {a : LC k}
    (hka : ks k = .exp a) (hn : T.n = k + 1) (hc : certC Fc ks lv (k + 1) = true)
    (hgen : ∀ z : L, z ∈ T.F (k + 1)) (qq : LC (k + 1)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b, elM Fc ks lv (k + 1) qq N = some b ∧
      (HasElementaryIntegral (T.ev (k + 1) qq) ↔ b = true) ∧
      (b = true → HasElementaryIntegralIn (T.ev (k + 1) qq)) := by
  classical
  have hcK : certC Fc ks lv k = true := by
    have hc' := hc
    rw [certX_succ, Bool.and_eq_true] at hc'; exact hc'.1
  have MS := T.mspecs hmon hdeg lv (k + 1) (by omega) hc
  have MSk := T.mspecs hmon hdeg lv k (by omega) hcK
  have hTr : T.Tr (k + 1) := MS.hyp.tr
  have hk : T.Tr k := hTr.of_succ
  have hkn : k < T.n := by omega
  have htr : Transcendental (T.F k) (T.ts k) := hTr k (by omega)
  have hsemM : ∀ c, (((T.MP k hk).sem c : T.F k) : L) = T.ev k c := T.sem_MP k hk
  have haev : ∀ p, aeval (T.ts k) (GPoly.toPoly (T.MP k hk) p) = T.evP k p :=
    T.aeval_toPoly (T.MP k hk) hsemM
  have hvalq : T.ev (k + 1) qq = aeval (T.ts k) (GPoly.toPoly (T.MP k hk) (qq : GFrac (LC k)).1) /
      aeval (T.ts k) (GPoly.toPoly (T.MP k hk) (qq : GFrac (LC k)).2) := by
    rw [haev, haev]; rfl
  simp only [elM]
  rw [hvalq]
  set O := MO Fc ks k with hO
  set M := T.MP k hk with hMdef
  set t := T.ts k with htdef
  set η : T.F k := (M.sem a)′ with hηdef
  set A := (qq : GFrac (LC k)).1 with hAdef
  set D := (qq : GFrac (LC k)).2 with hDdef
  set w : GPoly (LC k) := wKC O (.exp a) with hwdef
  have ht0 : t ≠ 0 := T.hts0 k hkn a hka
  have htraw : t′ = (T.ev k a)′ * t := by
    rw [htdef, T.ht k hkn, hka]
    rfl
  have hηE : algebraMap (T.F k) L η = (T.ev k a)′ := by
    rw [← hsemM a]
    rfl
  have ht' : t′ = algebraMap (T.F k) L η * t := by rw [htraw, hηE]
  have hgenK : IntermediateField.adjoin (T.F k) {t} = ⊤ :=
    eq_top_iff.mpr fun z _ ↦ (T.mem_F_succ).mp (hgen z)
  have hEl : IsElementaryExtension (T.F k) L :=
    isElementaryExtension_exp (F₀ := T.F k) t hgenK ht0 (T.ev k a) ⟨M.sem a, hsemM a⟩
      (by rw [logDeriv, htraw, mul_div_assoc, div_self ht0, mul_one])
  have constD := T.constDec k IH hkn.le hcK hEl
  -- the zero integrand
  by_cases hz : GPoly.isZero O D = true
  · have hD0 : GPoly.toPoly M D = 0 := (GPoly.isZero_iff M _).mp hz
    have h00 : HasElementaryIntegralIn (0 : L) := by
      simpa using hasElementaryIntegralIn_deriv (0 : L)
    refine ⟨0, fun N _ ↦ ⟨true, by rw [if_pos hz], ?_, fun _ ↦ ?_⟩⟩
    · rw [hD0, map_zero, div_zero]
      exact ⟨fun _ ↦ rfl, fun _ ↦ h00.hasElementaryIntegral⟩
    · rw [hD0, map_zero, div_zero]; exact h00
  have hD0 : GPoly.toPoly M D ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff M _).mpr h0)
  have hifz : ∀ {β : Type} (a b : β), (if GPoly.isZero (MO Fc ks k) D = true then a else b) = b :=
    fun a b ↦ if_neg hz
  simp only [hifz, hka]
  have hWp : GPoly.toPoly M w = C η * X := by
    simp only [hwdef, wKC, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero]
    rw [M.sem_zero, M.sem_deriv, C_0, zero_add, mul_comm]
  have hWT : C η * X = T.wPoly k := by
    rw [T.wPoly_exp hkn hka, ← T.sem_MP_F]
  have hw : t′ = aeval t (C η * X) := by rw [map_mul, aeval_C, aeval_X, ht']
  -- the fraction field `F k ⟮t⟯`
  letI := algebraAdjoinSimple (F := T.F k) t
  letI dP : Differential (T.F k)[X] := polynomialOfDeriv (C η * X)
  letI : Differential (T.F k)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  haveI hFR : IsFractionRing (T.F k)[X] (T.F k)⟮t⟯ := isFractionRing_adjoin_simple t htr
  haveI hDAL : DifferentialAlgebra (T.F k)[X] (T.F k)⟮t⟯ := differentialAlgebra_adjoin_simple t _ hw
  have hD : ∀ P : (T.F k)[X], P′ = implicitDeriv (GPoly.toPoly M w) P := fun P ↦ by
    rw [hWp]; rfl
  have hφ : ∀ P : (T.F k)[X], (((algebraMap (T.F k)[X] (T.F k)⟮t⟯ P) : (T.F k)⟮t⟯) : L) =
      aeval t P := fun P ↦ algebraMap_adjoinSimple t P
  have hinjt : ∀ P : (T.F k)[X], aeval t P = 0 → P = 0 := fun P h ↦
    transcendental_iff.mp htr P h
  -- (1) split off the powers of `t`
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec M A D hD0
  set sp := GPoly.expSplit O A D with hsp
  set kk := sp.2.2.1 with hkk
  have hd₁0 : GPoly.toPoly M sp.2.2.2 ≠ 0 := fun h ↦ hD0 (by rw [hsp2, h, mul_zero])
  have hnormal : ∀ p : (T.F k)[X], Irreducible p → p ∣ GPoly.toPoly M sp.2.2.2 →
      ¬p ∣ implicitDeriv (GPoly.toPoly M w) p := fun p hp hpd ↦ by
    rw [hWp, hWT]
    exact T.normal_exp k htr hka p hp (fun hX ↦ hsp3 (hX.trans hpd))
  -- (2) Hermite reduction
  have hchk := GPoly.hermiteCheck_hermite M w sp.1 sp.2.2.2 hnormal hd₁0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := (T.F k)⟮t⟯) M w sp.1 sp.2.2.2 _ hD hchk
  have hsdvd := GPoly.hermite_s_dvd M w sp.1 sp.2.2.2 hd₁0
  set h := GPoly.hermite O w sp.1 sp.2.2.2 with hh
  set Sd := GPoly.toPoly M h.s with hSd
  have hS0 : Sd ≠ 0 := hsq.ne_zero
  have hXS : ¬X ∣ Sd := fun hX ↦ hsp3 (hX.trans hsdvd)
  -- (3) polynomial and proper parts
  have hdm := GPoly.divMod_spec M h.b h.s
  have hdeglt := GPoly.divMod_degree_lt M h.b h.s hS0
  set q := (GPoly.divMod O h.b h.s).1 with hq
  set rem := (GPoly.divMod O h.b h.s).2 with hrem
  set Λc := GPoly.add O (GPoly.mul O q (GPoly.monomial O kk O.one)) sp.2.1 with hΛc
  have hΛpoly : GPoly.toPoly M Λc = GPoly.toPoly M q * X ^ kk + GPoly.toPoly M sp.2.1 := by
    rw [hΛc, GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_monomial, M.sem_one, C_1, one_mul]
  -- (4) the residue polynomial
  have hcop0 : IsCoprime Sd′ Sd :=
    isCoprime_deriv_of_squarefree hsq fun p hp hpS ↦ by
      rw [hD p]; exact hnormal p hp (hpS.trans hsdvd)
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M w) Sd) Sd := by
    rw [← hD Sd]; exact hcop0
  have hr := GPoly.residuePoly_spec M w rem h.s hS0 hcop
  have hr' : Sd ∣ GPoly.toPoly M (GPoly.residuePoly O w rem h.s) *
      (mapCoeffs Sd + C η * X * derivative Sd) - GPoly.toPoly M rem := by
    have hidd : implicitDeriv (GPoly.toPoly M w) Sd = mapCoeffs Sd + C η * X * derivative Sd := by
      rw [hWp, implicitDeriv, Derivation.add_apply, Derivation.smul_apply]
      rfl
    rwa [hidd] at hr
  have hst : aeval t Sd ≠ 0 := fun h0 ↦ hS0 (hinjt _ h0)
  -- (5) the integrand
  set Λ := GPoly.toPoly M Λc with hΛ
  set g : L := (((algebraMap (T.F k)[X] (T.F k)⟮t⟯ (GPoly.toPoly M h.gn) /
    algebraMap (T.F k)[X] (T.F k)⟮t⟯ (GPoly.toPoly M h.gd) : (T.F k)⟮t⟯)) : L) with hg
  have hid' : aeval t (GPoly.toPoly M sp.1) / aeval t (GPoly.toPoly M sp.2.2.2) =
      g′ + aeval t (GPoly.toPoly M h.b) / aeval t Sd := by
    have := congrArg Subtype.val hid
    rw [IntermediateField.coe_add, IntermediateField.coe_div, IntermediateField.coe_div, hφ, hφ,
      hφ, hφ] at this
    exact this
  have htk : t ^ kk ≠ 0 := pow_ne_zero _ ht0
  have hd₁' : aeval t (GPoly.toPoly M sp.2.2.2) ≠ 0 := fun h0 ↦ hd₁0 (hinjt _ h0)
  have hform : aeval t (GPoly.toPoly M A) / aeval t (GPoly.toPoly M D) =
      g′ + aeval t Λ / t ^ kk + aeval t (GPoly.toPoly M rem) / aeval t Sd := by
    have hA : aeval t (GPoly.toPoly M A) =
        aeval t (GPoly.toPoly M sp.1) * t ^ kk +
          aeval t (GPoly.toPoly M sp.2.1) * aeval t (GPoly.toPoly M sp.2.2.2) := by
      rw [← hsp1]; simp only [map_add, map_mul, map_pow, aeval_X]
    have hDd : aeval t (GPoly.toPoly M D) = t ^ kk * aeval t (GPoly.toPoly M sp.2.2.2) := by
      rw [hsp2]; simp only [map_mul, map_pow, aeval_X]
    have hb : aeval t (GPoly.toPoly M h.b) =
        aeval t (GPoly.toPoly M q) * aeval t Sd + aeval t (GPoly.toPoly M rem) := by
      rw [hdm, map_add, map_mul]
    have hΛe : aeval t Λ = aeval t (GPoly.toPoly M q) * t ^ kk + aeval t (GPoly.toPoly M sp.2.1) := by
      rw [hΛpoly]; simp only [map_add, map_mul, map_pow, aeval_X]
    calc aeval t (GPoly.toPoly M A) / aeval t (GPoly.toPoly M D)
        = aeval t (GPoly.toPoly M sp.1) / aeval t (GPoly.toPoly M sp.2.2.2) +
          aeval t (GPoly.toPoly M sp.2.1) / t ^ kk := by
          rw [hA, hDd]; field_simp
      _ = g′ + aeval t (GPoly.toPoly M h.b) / aeval t Sd +
          aeval t (GPoly.toPoly M sp.2.1) / t ^ kk := by rw [hid']
      _ = _ := by rw [hb, hΛe]; field_simp; ring
  -- (6) the coefficients of `Λ`
  have hcoef : ∀ j, Λ.coeff j = M.sem (Λc.getD j O.zero) := fun j ↦
    Tower.NestP.coeff_toPoly_getD' M Λc j
  set c0 := Λc.getD kk O.zero with hc0
  have hc0L : algebraMap (T.F k) L (Λ.coeff kk) = T.ev k c0 := by
    rw [hcoef kk]; exact hsemM c0
  have hasc : HasElementaryIntegral (algebraMap (T.F k) L (Λ.coeff kk)) →
      HasElementaryIntegralIn (algebraMap (T.F k) L (Λ.coeff kk)) := fun hel ↦ by
    obtain ⟨N₀, hN₀⟩ := constD c0
    obtain ⟨b, -, hiff, hIn⟩ := hN₀ N₀ le_rfl
    rw [hc0L] at hel ⊢
    exact hIn (hiff.mp hel)
  have key := expGen_decides (F₀ := T.F k) t hgenK η ht0 ht'
    (fun f ↦ ∃ c : LC k, f = M.sem c) (T.expLift hmon hdeg k hkn hc hka hk) g Λ kk
    (fun j _ ↦ ⟨_, hcoef j⟩) (GPoly.toPoly M rem) Sd
    (GPoly.toPoly M (GPoly.residuePoly O w rem h.s)) hsq hXS hdeglt hst hr' hasc
  rw [← hform] at key
  -- (7) the Risch equations and the algorithm
  have hrde : ∀ j, j ≠ kk →
      ((∃ y : T.F k, y′ + ((j : T.F k) - kk) * η * y = Λ.coeff j) ↔
        rdeOKM Fc ks lv k (O.mul (mcst Fc ks k ((j : ℚ) - kk)) a) (Λc.getD j O.zero) = true) :=
    fun j _ ↦ by
      rw [← T.rdeOKM_iff k hk MSk.rde, T.sem_mulCst k hk, hcoef j]
      push_cast
      rfl
  obtain ⟨N₀, hN₀⟩ := constD c0
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b0, hb0, hbiff, hbIn⟩ := hN₀ N hN
  have hrc := GPoly.residueCheck_iff M w rem h.s hS0
  split_ifs with h1 h2
  · refine ⟨false, rfl, ?_, by simp⟩
    simp only [Bool.not_eq_true'] at h1
    simp only [Bool.false_eq_true, iff_false]
    intro hel
    have := hrc.mpr (key.mp hel).1
    rw [this] at h1
    exact Bool.noConfusion h1
  · refine ⟨false, rfl, ?_, by simp⟩
    simp only [Bool.false_eq_true, iff_false]
    intro hel
    have hR := (key.mp hel).2.1
    simp only [Bool.not_eq_true', List.all_eq_false, List.mem_range] at h2
    obtain ⟨j, -, hjf⟩ := h2
    have hjk : j ≠ kk := fun h ↦ hjf (by simp [h])
    exact hjf (by rw [(hrde j hjk).mp (hR j hjk)]; simp)
  · simp only [Bool.not_eq_true', Bool.not_eq_false] at h1 h2
    have hres := hrc.mp h1
    have hR : ∀ j, j ≠ kk → ∃ y : T.F k, y′ + ((j : T.F k) - kk) * η * y = Λ.coeff j := by
      intro j hj
      by_cases hjb : j < Λc.length + kk + 1
      · have := List.all_eq_true.mp h2 j (List.mem_range.mpr hjb)
        simp only [Bool.or_eq_true, decide_eq_true_eq] at this
        exact (hrde j hj).mpr (this.resolve_left hj)
      · refine ⟨0, ?_⟩
        have h0 : Λ.coeff j = 0 := by
          rw [hcoef j, List.getD_eq_default _ _ (by omega)]
          exact M.sem_zero
        rw [h0]; simp
    refine ⟨b0, hb0, ?_, fun hb1 ↦ ?_⟩
    · rw [key, hc0L, hbiff]
      exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨hres, hR, h⟩⟩
    · have hcIn := hbIn hb1
      rw [← hc0L] at hcIn
      rw [hform]
      exact expGen_suff_in (F₀ := T.F k) t η ht0 ht' g Λ kk _ Sd _ hsq hdeglt hst hr' hres hR hcIn

end MTower

end Curves.MT
