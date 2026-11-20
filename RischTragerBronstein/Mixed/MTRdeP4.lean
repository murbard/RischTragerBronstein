import RischTragerBronstein.Mixed.MTRdeP3
import RischTragerBronstein.Computable.NestXRdeP4

/-!
# Mixed towers over a curve (`RdeP4`)

Ported from `Tower.NestX` (`NestXRdeP4`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u


namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]
variable (T : MTower Fc ks Cc L)


section Bal

variable (m : ℕ) (h : T.Tr (m + 1))

/-- The leading-coefficient ratio of a constant fraction is the constant. -/
lemma sem_lcC_constXP (w : GPX m) (κ : Cc)
    (hw : (T.M1X m h).sem w = algebraMap Cc (T.F (m + 1)) κ) :
    (T.MX m h).sem (lcC (MO Fc ks m) w) = algebraMap Cc (T.F m) κ := by
  rw [sem_lcCXP]
  by_cases hd : GPoly.toPoly (T.MX m h) w.2 = 0
  · have h0 : (T.M1X m h).sem w = 0 := by
      rw [T.semX, show T.σX m h w.2 = 0 by rw [σX, hd, map_zero], div_zero]
    rw [h0] at hw
    have hκ : κ = 0 := by
      have := hw.symm
      rwa [map_eq_zero_iff _ (algebraMap Cc (T.F (m + 1))).injective] at this
    rw [hd, hκ, leadingCoeff_zero, div_zero, map_zero]
  · have hσd : T.σX m h w.2 ≠ 0 := by
      rw [σX, Ne, map_eq_zero_iff _ (T.phi_injX m h)]; exact hd
    rw [T.semX, div_eq_iff hσd, T.algebraMap_succ, σX, σX, ← map_mul] at hw
    have hN := T.phi_injX m h hw
    rw [hN, leadingCoeff_mul, leadingCoeff_C]
    field_simp [leadingCoeff_ne_zero.mpr hd]

variable {η : LC m} (hk : ks m = .prim η)

/-- The coefficient of the one-level-down equations in the balanced case. -/
def lowFXC (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (m : ℕ) (v : LC m) (fr : FRep (GPX m)) :
    FRep (LC m) :=
  ⟨(GPoly.divMod (MO Fc ks m) (cleanG (MO Fc ks m) fr.h).1 (cleanG (MO Fc ks m) fr.h).2).1.getD 0
      (MO Fc ks m).zero,
    ((GPoly.divMod (MO Fc ks m) (cleanG (MO Fc ks m) fr.h).1 (cleanG (MO Fc ks m) fr.h).2).1.getD 1
      (MO Fc ks m).zero, v) ::
    fr.logs.map fun cw ↦ (lcC (MO Fc ks m) cw.1, lcC (MO Fc ks m) cw.2)⟩

include hk in
set_option maxHeartbeats 3200000 in
/-- **The balanced case at a logarithmic level**: `lowF` is a valid coefficient (constant
logarithmic coefficients) and its value is `lc B / lc A`. -/
theorem prim_balXP (hnd : ∀ y : T.F m, y′ ≠ T.ηX m h η) (v : LC m)
    (hlv : (T.MX m h).sem η = logDeriv ((T.MX m h).sem v))
    (fr : FRep (GPX m)) (hok : FRepOK (T.M1X m h) fr) (Q : GPoly (LC m))
    (hQ : (GPoly.toPoly (T.MX m h) Q).Monic) (Rs : List (GPX m))
    (hP : GPoly.toPoly (T.MX m h) (prodD (GPoly.mul (MO Fc ks m)) [(MO Fc ks m).one] Rs) ≠ 0)
    (hB0 : GPoly.toPoly (T.MX m h) (peB (MO Fc ks m) (peFX (MO Fc ks m)
      ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
      (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr) Q) Rs) ≠ 0)
    (hdeg : (GPoly.toPoly (T.MX m h) (peA (MO Fc ks m) (peFX (MO Fc ks m)
      ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
      (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr) Q) Rs)).natDegree =
      (GPoly.toPoly (T.MX m h) (peB (MO Fc ks m) (peFX (MO Fc ks m)
      ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
      (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr) Q) Rs)).natDegree) :
    FRepOK (T.MX m h) (lowFXC Fc ks m v fr) ∧
      (T.MX m h).sem (fCode (MO Fc ks m) (lowFXC Fc ks m v fr)) =
        (GPoly.toPoly (T.MX m h) (peB (MO Fc ks m) (peFX (MO Fc ks m)
          ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
          (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr) Q) Rs)).leadingCoeff /
        (GPoly.toPoly (T.MX m h) (peA (MO Fc ks m) (peFX (MO Fc ks m)
          ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
          (fCode ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fr) Q) Rs)).leadingCoeff := by
  classical
  set O := MO Fc ks m with hO
  set O' := O.monomial (wKC O (ks m)) with hO'
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  set F := peFX O O' (fCode O' fr) Q with hF
  set P := prodD (GPoly.mul O) [O.one] Rs with hPd
  have hA : GPoly.toPoly (T.MX m h) (peA O F Rs) =
      GPoly.toPoly (T.MX m h) F.2 * GPoly.toPoly (T.MX m h) P := by rw [peA, GPoly.toPoly_mul]
  have hB : GPoly.toPoly (T.MX m h) (peB O F Rs) =
      GPoly.toPoly (T.MX m h) F.1 * GPoly.toPoly (T.MX m h) P := by rw [peB, GPoly.toPoly_mul]
  have hF2 : GPoly.toPoly (T.MX m h) F.2 ≠ 0 := by
    intro h0; exact T.σX_peFX_ne m h _ Q (by rw [σX, h0, map_zero])
  have hF1 : GPoly.toPoly (T.MX m h) F.1 ≠ 0 := fun h0 ↦ hB0 (by rw [hB, h0, zero_mul])
  have hdegF : (GPoly.toPoly (T.MX m h) F.1).natDegree =
      (GPoly.toPoly (T.MX m h) F.2).natDegree := by
    rw [hA, hB, natDegree_mul hF2 hP, natDegree_mul hF1 hP] at hdeg; omega
  have hlead : (GPoly.toPoly (T.MX m h) (peB O F Rs)).leadingCoeff /
      (GPoly.toPoly (T.MX m h) (peA O F Rs)).leadingCoeff =
      (GPoly.toPoly (T.MX m h) F.1).leadingCoeff / (GPoly.toPoly (T.MX m h) F.2).leadingCoeff := by
    rw [hA, hB, leadingCoeff_mul, leadingCoeff_mul,
      mul_div_mul_right _ _ (leadingCoeff_ne_zero.mpr hP)]
  -- the data of `h`
  set hc := cleanG O fr.h with hhc
  have hd0 : GPoly.toPoly (T.MX m h) hc.2 ≠ 0 := by
    intro h0; exact T.σX_cleanG_ne m h fr.h (by rw [σX, h0, map_zero])
  set qH := (GPoly.divMod O hc.1 hc.2).1 with hqH
  have hdiv := GPoly.divMod_spec (T.MX m h) hc.1 hc.2
  have hrr := GPoly.divMod_degree_lt (T.MX m h) hc.1 hc.2 hd0
  -- the logarithmic part
  set logs := fr.logs with hlogs
  obtain ⟨κ, hκ⟩ := T.logs_constXP m h logs hok
  set S := T.sLX m h logs with hS
  set Nw : ℕ → (T.F m)[X] := fun j ↦ GPoly.toPoly (T.MX m h) (logs.getD j (dLX m)).2.1 with hNw
  set Dw : ℕ → (T.F m)[X] := fun j ↦ GPoly.toPoly (T.MX m h) (logs.getD j (dLX m)).2.2 with hDw
  set cF : ℕ → T.F m := fun j ↦ algebraMap Cc (T.F m) (κ j) with hcF
  have hND : ∀ j ∈ S, Nw j ≠ 0 ∧ Dw j ≠ 0 := fun j hj ↦ ((T.mem_sLX m h logs j).mp hj).2
  -- the setting `K = F m (t)`
  set t := T.ts m with ht
  have hw := T.deriv_ts_aeval m
  let _ := algebraAdjoinSimple (F := T.F m) t
  let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  let _ : Differential (T.F m)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮t⟯ := isFractionRing_adjoin_simple _ htr
  have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮t⟯ := differentialAlgebra_adjoin_simple _ _ hw
  have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ P : (T.F m)⟮t⟯) : L) = aeval t P :=
    algebraMap_adjoinSimple _
  have hDp : ∀ P : (T.F m)[X], P′ = implicitDeriv (C (T.ηX m h η)) P := fun P ↦ by
    change implicitDeriv (T.wPoly m) P = _
    rw [T.wPoly_eq_ηX m h hk]
  set φK := algebraMap (T.F m)[X] (T.F m)⟮t⟯ with hφK
  let toK : T.F (m + 1) →+* (T.F m)⟮t⟯ :=
    { toFun := fun z ↦ ⟨(z : L), (T.mem_F_succ).mp z.2⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have htoK_phi : ∀ P, toK (T.phi m P) = φK P := fun P ↦ Subtype.ext (by
    change ((T.phi m P : T.F (m + 1)) : L) = _
    rw [T.coe_phi, hφK, hcoe])
  have htoK_d : ∀ z, toK (z′) = (toK z)′ := fun z ↦ rfl
  have htoK_ld : ∀ z, toK (logDeriv z) = logDeriv (toK z) := fun z ↦ by
    unfold logDeriv; rw [map_div₀, htoK_d]
  have hFK : φK (GPoly.toPoly (T.MX m h) F.1) / φK (GPoly.toPoly (T.MX m h) F.2) =
      (φK (GPoly.toPoly (T.MX m h) hc.1) / φK (GPoly.toPoly (T.MX m h) hc.2))′ +
        ∑ j ∈ S, φK (C (cF j)) * logDeriv (φK (Nw j) / φK (Dw j)) -
          (φK (GPoly.toPoly (T.MX m h) Q))′ / φK (GPoly.toPoly (T.MX m h) Q) := by
    have e0 := congrArg toK (T.sem_peFXP m h (fCode O' fr) Q)
    rw [map_div₀, map_sub, map_div₀, sem_fCode, map_add, htoK_d, htoK_d, htoK_phi, htoK_phi,
      σX, htoK_phi, T.logSumV_eqXP m h logs κ hκ, ← T.semX_cleanG, T.semX, map_div₀,
      htoK_phi, htoK_phi, map_sum] at e0
    rw [e0]
    congr 2
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, htoK_ld, map_div₀, T.algebraMap_succ, htoK_phi, htoK_phi, htoK_phi]
  have hnd' : ∀ y : T.F m, y′ ≠ T.ηX m h η := hnd
  obtain ⟨hq1, hc1, hlc⟩ := bal_coreXP (K := (T.F m)⟮t⟯) hDp hnd' _ _ _ _ _ _ _ hd0 hdiv hrr hQ
    hF2 hdegF S cF Nw Dw hND hFK
  -- the value of `fCode lowF`
  have hq0 : (T.MX m h).sem (qH.getD 0 O.zero) = (GPoly.toPoly (T.MX m h) qH).coeff 0 :=
    (coeff_toPoly_getD' _ _ _).symm
  have hq1' : (T.MX m h).sem (qH.getD 1 O.zero) = (GPoly.toPoly (T.MX m h) qH).coeff 1 :=
    (coeff_toPoly_getD' _ _ _).symm
  have hsum : (fr.logs.map fun cw ↦ (T.MX m h).sem (lcC O cw.1) *
      logDeriv ((T.MX m h).sem (lcC O cw.2))).sum = ∑ j ∈ S, cF j *
        ((Nw j).leadingCoeff′ / (Nw j).leadingCoeff - (Dw j).leadingCoeff′ / (Dw j).leadingCoeff) := by
    rw [← hlogs, sum_map_getDXP _ (dLX m), hS, sLX, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' := Finset.mem_range.mp hj
    rw [sem_lcCXP (T.MX m h) (logs.getD j (dLX m)).2, T.sem_lcC_constXP m h _ (κ j) (hκ j hj')]
    split_ifs with hc'
    · rw [logDeriv_div _ _ (leadingCoeff_ne_zero.mpr hc'.1) (leadingCoeff_ne_zero.mpr hc'.2)]
      rfl
    · have h0 : (GPoly.toPoly (T.MX m h) (logs.getD j (dLX m)).2.1).leadingCoeff /
          (GPoly.toPoly (T.MX m h) (logs.getD j (dLX m)).2.2).leadingCoeff = 0 := by
        rw [not_and_or, not_not, not_not] at hc'
        rcases hc' with hc' | hc'
        · rw [hc', leadingCoeff_zero, zero_div]
        · rw [hc', leadingCoeff_zero, div_zero]
      rw [h0]
      simp [logDeriv]
  refine ⟨?_, ?_⟩
  · intro cw hcw
    rcases List.mem_cons.mp hcw with rfl | hcw
    · change ((T.MX m h).sem (qH.getD 1 O.zero))′ = 0
      rw [hq1']; exact hc1
    · obtain ⟨cw0, hcw0, rfl⟩ := List.mem_map.mp hcw
      obtain ⟨κ0, hκ0⟩ := T.const_F _ (hok cw0 hcw0)
      change ((T.MX m h).sem (lcC O cw0.1))′ = 0
      rw [T.sem_lcC_constXP m h _ κ0 hκ0]
      exact T.deriv_algebraMap_Cc κ0
  · rw [sem_fCode]
    change ((T.MX m h).sem (qH.getD 0 O.zero))′ + logSumV (T.MX m h)
      ((qH.getD 1 O.zero, v) :: fr.logs.map fun cw ↦ (lcC O cw.1, lcC O cw.2)) = _
    rw [logSumV, List.map_cons, List.sum_cons, List.map_map]
    have e1 : ((fun cw : LC m × LC m ↦ (T.MX m h).sem cw.1 *
        logDeriv ((T.MX m h).sem cw.2)) ∘ fun cw : GPX m × GPX m ↦ (lcC O cw.1, lcC O cw.2)) =
        fun cw ↦ (T.MX m h).sem (lcC O cw.1) * logDeriv ((T.MX m h).sem (lcC O cw.2)) := rfl
    rw [e1, hsum, hq0, hq1', hlead, hlc, show T.ηX m h η = logDeriv ((T.MX m h).sem v) from hlv]
    ring

end Bal


end MTower

end Curves.MT
