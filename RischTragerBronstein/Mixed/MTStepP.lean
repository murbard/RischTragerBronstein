import RischTragerBronstein.Mixed.MTLift

/-!
# Mixed towers over a curve: the inductive step at a logarithmic level

`MTower.elM_step_prim`: at a logarithmic level `k` (`tₖ′ = η`), `elM (k + 1)` decides. The
level-`k + 1` integrand is Hermite-reduced in `t = tₖ`; the residue test and the limited-integration
chain at level `k` (`mchain`) are sound and complete (the Liouville theory of `PrimGen`, applied in
each elementary extension to the realization of the tower over its constants, `exists_lift`, where
the certificate gives transcendence and the specifications of the solvers), and the constant term
is decided at level `k` (`constDec`). The port of `LTMain.elT_step`.
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
/-- **The inductive step at a logarithmic level.** -/
theorem elM_step_prim [IsAlgClosed Cc] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (k : ℕ) (IH : ELHypM.{u} Fc ks lv k) {η : LC k}
    (hkη : ks k = .prim η) (hn : T.n = k + 1) (hc : certC Fc ks lv (k + 1) = true)
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
  have hsemM : ∀ a, (((T.MP k hk).sem a : T.F k) : L) = T.ev k a := T.sem_MP k hk
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
  set ηv := M.sem η with hηv
  set A := (qq : GFrac (LC k)).1 with hAdef
  set D := (qq : GFrac (LC k)).2 with hDdef
  set w : GPoly (LC k) := wKC O (.prim η) with hwdef
  have ht' : t′ = algebraMap (T.F k) L ηv := by
    rw [htdef, T.ht k hkn, hkη]
    exact (hsemM η).symm
  have hgenK : IntermediateField.adjoin (T.F k) {t} = ⊤ :=
    eq_top_iff.mpr fun z _ ↦ (T.mem_F_succ).mp (hgen z)
  have hE : IsElementaryExtension (T.F k) L := by
    obtain ⟨v, hv0, hvη⟩ := MS.hyp.log k (by omega) η hkη
    refine isElementaryExtension_log' t hgenK (v : L) ⟨v, rfl⟩
      (fun h0 ↦ hv0 (Subtype.ext h0)) ?_
    rw [ht', hηv, T.sem_MP_F, hvη, ← T.coe_logDeriv_FX]
    rfl
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
  simp only [hifz]
  have hWp : GPoly.toPoly M w = C ηv := by
    simp [hwdef, wKC, hηv]
  have hw : t′ = aeval t (C ηv) := by rw [aeval_C, ht']
  -- the fraction field `F k ⟮t⟯`
  letI := algebraAdjoinSimple (F := T.F k) t
  letI dP : Differential (T.F k)[X] := polynomialOfDeriv (C ηv)
  letI : Differential (T.F k)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  haveI hFR : IsFractionRing (T.F k)[X] (T.F k)⟮t⟯ := isFractionRing_adjoin_simple t htr
  haveI hDAL : DifferentialAlgebra (T.F k)[X] (T.F k)⟮t⟯ := differentialAlgebra_adjoin_simple t _ hw
  have hD : ∀ P : (T.F k)[X], P′ = implicitDeriv (GPoly.toPoly M w) P := fun P ↦ by
    rw [hWp]; rfl
  have hφ : ∀ P : (T.F k)[X], (((algebraMap (T.F k)[X] (T.F k)⟮t⟯ P) : (T.F k)⟮t⟯) : L) =
      aeval t P := fun P ↦ algebraMap_adjoinSimple t P
  have hinjt : ∀ P : (T.F k)[X], aeval t P = 0 → P = 0 := fun P h ↦
    transcendental_iff.mp htr P h
  have hnormAll : ∀ p : (T.F k)[X], Irreducible p → ¬p ∣ p′ := fun p hp h ↦
    T.normal_prim k htr hkη p hp (by
      rw [T.wPoly_prim hkn hkη, ← T.sem_MP_F]
      exact h)
  have hnormal : ∀ p : (T.F k)[X], Irreducible p → p ∣ GPoly.toPoly M D →
      ¬p ∣ implicitDeriv (GPoly.toPoly M w) p := fun p hp _ h ↦
    hnormAll p hp (by rwa [hD p])
  -- (1) Hermite reduction
  have hchk := GPoly.hermiteCheck_hermite M w A D hnormal hD0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := (T.F k)⟮t⟯) M w A D _ hD hchk
  set h := GPoly.hermite O w A D with hh
  set Sd := GPoly.toPoly M h.s with hSd
  have hS0 : Sd ≠ 0 := hsq.ne_zero
  have hsep : Sd.Separable := PerfectField.separable_iff_squarefree.mpr hsq
  -- (2) polynomial and proper parts
  have hdm := GPoly.divMod_spec M h.b h.s
  have hdeglt := GPoly.divMod_degree_lt M h.b h.s hS0
  set qc := (GPoly.divMod O h.b h.s).1 with hqc
  set rem := (GPoly.divMod O h.b h.s).2 with hrem
  -- (3) the residue polynomial
  have hcop0 : IsCoprime Sd′ Sd := isCoprime_deriv_of_squarefree hsq fun p hp _ ↦ hnormAll p hp
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M w) Sd) Sd := by
    rw [← hD Sd]; exact hcop0
  have hr := GPoly.residuePoly_spec M w rem h.s hS0 hcop
  set r := GPoly.toPoly M (GPoly.residuePoly O w rem h.s) with hrdef
  have hidd : implicitDeriv (GPoly.toPoly M w) Sd = mapCoeffs Sd + C ηv * derivative Sd := by
    rw [hWp, implicitDeriv, Derivation.add_apply, Derivation.smul_apply]
    rfl
  have hr' : Sd ∣ r * (mapCoeffs Sd + C ηv * derivative Sd) - GPoly.toPoly M rem := by
    rwa [hidd] at hr
  have hst : aeval t Sd ≠ 0 := fun h0 ↦ hS0 (hinjt _ h0)
  -- (4) the integrand
  set g : L := (((algebraMap (T.F k)[X] (T.F k)⟮t⟯ (GPoly.toPoly M h.gn) /
    algebraMap (T.F k)[X] (T.F k)⟮t⟯ (GPoly.toPoly M h.gd) : (T.F k)⟮t⟯)) : L) with hg
  set Pq := GPoly.toPoly M qc with hPq
  set Pr := GPoly.toPoly M rem with hPr
  have hform : aeval t (GPoly.toPoly M A) / aeval t (GPoly.toPoly M D) =
      g′ + (aeval t Pq + aeval t Pr / aeval t Sd) := by
    have hid' : aeval t (GPoly.toPoly M A) / aeval t (GPoly.toPoly M D) =
        g′ + aeval t (GPoly.toPoly M h.b) / aeval t Sd := by
      have := congrArg Subtype.val hid
      rw [IntermediateField.coe_add, IntermediateField.coe_div, IntermediateField.coe_div, hφ, hφ,
        hφ, hφ] at this
      exact this
    rw [hid', hdm, map_add, map_mul, ← hSd]
    field_simp
  -- (5) the coefficients of the polynomial part
  have hcoefF : ∀ j, Pq.coeff j = M.sem (qc.getD j O.zero) := fun j ↦
    Tower.NestP.coeff_toPoly_getD' M qc j
  have hcoef : ∀ j, ((Pq.coeff j : T.F k) : L) = T.ev k (qc.getD j O.zero) := fun j ↦ by
    rw [hcoefF, hsemM]
  have hdq : Pq.natDegree ≤ qc.length := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hcoefF, List.getD_eq_default _ _ (by exact_mod_cast hN.le), M.sem_zero]
  have hlogIn : Sd ∣ residueTest r Sd → HasElementaryIntegralIn (aeval t Pr / aeval t Sd) :=
    fun hT ↦ hasElementaryIntegralIn_of_residueTest t ηv 0
      (by rw [ht', map_zero, zero_mul, add_zero]) 1 one_ne_zero
      (by rw [map_zero]; simp [logDeriv]) Sd Pr r hsep hst hdeglt
      (by rwa [C_0, zero_mul, add_zero]) hT
  -- (6) the constant term, one level down
  have constD := T.constDec k IH hkn.le hcK hE
  -- (7) necessity
  have hnec : HasElementaryIntegral (aeval t (GPoly.toPoly M A) / aeval t (GPoly.toPoly M D)) →
      Sd ∣ residueTest r Sd ∧ ∃ R, mchain Fc ks lv k η qc qc.length O.zero = some R ∧
        HasElementaryIntegral (T.ev k (mconst Fc ks k η qc R)) := by
    intro hf
    have h1 : HasElementaryIntegral (aeval t Pq + aeval t Pr / aeval t Sd) := by
      have := hf.sub_in (hasElementaryIntegralIn_deriv g)
      rwa [hform, add_sub_cancel_left] at this
    have hT : Sd ∣ residueTest r Sd := by
      obtain ⟨E, _, _, _, _, hE1, gE, hgE⟩ := h1
      haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap L E).injective
      obtain ⟨TE, hTEn, hTEts, -, hTEmem⟩ := T.exists_lift E
      have htrE : Transcendental (TE.F k) (algebraMap L E t) := by
        have := (TE.mspecs hmon hdeg lv (k + 1) (by omega) hc).hyp.tr k (by omega)
        rwa [hTEts] at this
      exact residue_of_lift_prim (F₀ := T.F k) t hgenK ηv ht' Pq Pr Sd r hsq hr' E hE1 gE hgE hst
        (TE.F k) (TE.derivClosed k) (fun f ↦ hTEmem k _ f.2) htrE
    refine ⟨hT, ?_⟩
    have h2 : HasElementaryIntegral (aeval t Pq) := by
      have := h1.sub_in (hlogIn hT)
      rwa [add_sub_cancel_right] at this
    obtain ⟨E2, _, _, _, _, hE2, g2, hg2⟩ := h2
    haveI : CharZero E2 := charZero_of_injective_algebraMap (algebraMap L E2).injective
    obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E2
    set ψ := algebraMap L E2 with hψ
    have MSE := TE.mspecs hmon hdeg lv (k + 1) (by omega) hc
    have MSEk := TE.mspecs hmon hdeg lv k (by omega) hcK
    have hTETr : TE.Tr (k + 1) := MSE.hyp.tr
    have hTEk : TE.Tr k := MSEk.hyp.tr
    have htrE : Transcendental (TE.F k) (ψ t) := by
      have := hTETr k (by omega)
      rwa [hTEts] at this
    obtain ⟨p, hpF, hrec, htop, hgsum⟩ := poly_of_lift_prim t hgenK ηv ht' Pq qc.length hdq E2 hE2
      g2 hg2 (TE.F k) (TE.derivClosed k) (fun f ↦ hTEmem k _ f.2) htrE
    -- the recurrence inside the lifted level
    set p' : ℕ → TE.F k := fun i ↦ ⟨p i, hpF i⟩ with hp'
    have hsemE : ∀ a, (((TE.MP k hTEk).sem a : TE.F k) : E2) = ψ (T.ev k a) := by
      intro a; rw [TE.sem_MP, hTEev]
    have hηE : (((TE.MP k hTEk).sem η : TE.F k) : E2) = ψ (algebraMap (T.F k) L ηv) := by
      rw [hsemE, ← hsemM]
      rfl
    have hrec' : ∀ i, 1 ≤ i → i ≤ qc.length → (p' i)′ + ((i + 1 : ℕ) : TE.F k) *
        (TE.MP k hTEk).sem η * p' (i + 1) = (TE.MP k hTEk).sem (qc.getD i O.zero) := by
      intro i h1 _
      apply Subtype.ext
      rw [IntermediateField.coe_add, IntermediateField.coe_mul, IntermediateField.coe_mul,
        MTower.coe_deriv, hηE, hsemE, ← hcoef i]
      have := hrec i h1
      push_cast at this ⊢
      exact this
    have hQ0 : (p' (qc.length + 1) - (TE.MP k hTEk).sem O.zero)′ = 0 := by
      rw [(TE.MP k hTEk).sem_zero, sub_zero]
      exact Subtype.ext (by rw [MTower.coe_deriv]; exact htop)
    have hndE : ∀ y : TE.F k, y′ ≠ (TE.MP k hTEk).sem η := by
      intro y hy
      exact MSE.hyp.nd k (by omega) η hkη y (by rw [hy, TE.sem_MP_F])
    obtain ⟨R, hR, hR1⟩ := TE.mchain_complete k hTEk MSEk.lim η hndE qc p' qc.length hrec' O.zero
      hQ0
    refine ⟨R, hR, E2, inferInstance, inferInstance, inferInstance, inferInstance, hE2,
      g2 - ∑ j ∈ Finset.range (qc.length + 1), p (j + 1) * ψ t ^ (j + 1) +
        (p 1 - ψ (T.ev k R)) * ψ t, ?_⟩
    have hκ : (p 1 - ψ (T.ev k R))′ = 0 := by
      have := congrArg Subtype.val hR1
      rw [MTower.coe_deriv, AddSubgroupClass.coe_sub, hsemE] at this
      exact this
    have hc0 : T.ev k (mconst Fc ks k η qc R) =
        T.ev k (qc.getD 0 O.zero) - algebraMap (T.F k) L ηv * T.ev k R := by
      rw [← hsemM, T.sem_mconst, AddSubgroupClass.coe_sub, IntermediateField.coe_mul,
        hsemM (qc.getD 0 O.zero), hsemM R]
      rfl
    have ha0 : algebraMap (T.F k) L (Pq.coeff 0) = T.ev k (qc.getD 0 O.zero) := hcoef 0
    rw [Derivation.map_add, hgsum, Derivation.leibniz, hκ, deriv_algebraMap, ht', hc0, ha0]
    simp only [smul_eq_mul, mul_zero, add_zero, map_sub, map_mul]
    ring
  -- (8) sufficiency, given the chain
  have hsuff : ∀ R, mchain Fc ks lv k η qc qc.length O.zero = some R → Sd ∣ residueTest r Sd →
      HasElementaryIntegralIn (T.ev k (mconst Fc ks k η qc R)) →
      HasElementaryIntegralIn (aeval t (GPoly.toPoly M A) / aeval t (GPoly.toPoly M D)) := by
    intro R hR hT hc
    obtain ⟨P, hPrec, ⟨q0, hq0⟩, hP1⟩ := T.mchain_sound k hk MSk.lim η qc qc.length O.zero R hR
    have htop : ((P (qc.length + 1) : T.F k) : L)′ = 0 := by
      rw [← MTower.coe_deriv, hq0, Derivation.map_add, T.deriv_ratCast, add_zero, M.sem_zero,
        Derivation.map_zero]
      rfl
    have hsum := prim_sum_deriv t (ηv : L) ht' (fun i ↦ T.ev k (qc.getD i O.zero))
      (fun i ↦ (P i : L)) qc.length (fun i h1 h2 ↦ by
        have := congrArg Subtype.val (hPrec i h1 h2)
        rw [IntermediateField.coe_add, IntermediateField.coe_mul, IntermediateField.coe_mul,
          MTower.coe_deriv, hsemM (qc.getD i O.zero)] at this
        push_cast at this ⊢
        exact this) htop
    have hA' : aeval t Pq = ∑ i ∈ Finset.range (qc.length + 1), T.ev k (qc.getD i O.zero) * t ^ i := by
      rw [aeval_eq_sum_range' (n := qc.length + 1) (by omega)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Algebra.smul_def, ← hcoef i]
      rfl
    have hL := ((hc.add (hasElementaryIntegralIn_deriv
      (∑ j ∈ Finset.range (qc.length + 1), (P (j + 1) : L) * t ^ (j + 1)))).add
        (hlogIn hT)).add (hasElementaryIntegralIn_deriv g)
    rw [hform]
    convert hL using 1
    rw [hsum, ← hsemM (mconst Fc ks k η qc R), T.sem_mconst, AddSubgroupClass.coe_sub,
      IntermediateField.coe_mul, hsemM, ← hP1, hA']
    ring
  -- (9) the algorithm
  simp only [hkη]
  cases hres : GPoly.residueCheck O w rem h.s with
  | false =>
    refine ⟨0, fun N _ ↦ ⟨false, by simp, ?_, by simp⟩⟩
    simp only [Bool.false_eq_true, iff_false]
    intro hf
    have := (GPoly.residueCheck_iff M w rem h.s hS0).mpr (hnec hf).1
    rw [hres] at this
    exact Bool.noConfusion this
  | true =>
    have hT : Sd ∣ residueTest r Sd := (GPoly.residueCheck_iff M w rem h.s hS0).mp hres
    cases hch : mchain Fc ks lv k η qc qc.length O.zero with
    | none =>
      refine ⟨0, fun N _ ↦ ⟨false, by simp, ?_, by simp⟩⟩
      simp only [Bool.false_eq_true, iff_false]
      intro hf
      obtain ⟨R, hR, -⟩ := (hnec hf).2
      rw [hch] at hR
      simp at hR
    | some R =>
      obtain ⟨N₀, hN₀⟩ := constD (mconst Fc ks k η qc R)
      refine ⟨N₀, fun N hN ↦ ?_⟩
      obtain ⟨b, hb, hiff, hIn⟩ := hN₀ N hN
      refine ⟨b, by simpa [hres, hch] using hb,
        ⟨fun hf ↦ ?_, fun hb1 ↦ (hsuff R hch hT (hIn hb1)).hasElementaryIntegral⟩,
        fun hb1 ↦ hsuff R hch hT (hIn hb1)⟩
      obtain ⟨-, R', hR', hc⟩ := hnec hf
      rw [hch, Option.some.injEq] at hR'
      subst hR'
      exact hiff.mp hc

end MTower

end Curves.MT
