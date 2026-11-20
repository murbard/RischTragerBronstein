import RischTragerBronstein.Mixed.NKNonTors
import RischTragerBronstein.Mixed.NKTorsionP
import RischTragerBronstein.Torsion.RamRes
import RischTragerBronstein.Torsion.DecideLogP

/-!
# Non-elementary integrals over a non-Kummer curve: residue divisors at places

The version of `Mixed/NKNonTors` with the poles of `f = η B(t, θ)/D(t)` at arbitrary (possibly
ramified) places above the roots `αⱼ` of `D`, certified by a `PlaceCert` (fibre data `x = αⱼ +
T^{Nⱼ}`, roots `πⱼₖ` with multiplicities `sⱼₖ`): the residue along the root `k` is
`ρⱼₖ = Nⱼ B(αⱼ, yⱼₖ(0))/D′(αⱼ)` (`embG_pole_N`), and if `sⱼₖ Γ_{πⱼₖ} = s λ(ρⱼₖ) + eⱼ Nⱼ` with
`Γ` certified non-torsion (`not_torsion_places_map`), then `∫ f` is not elementary
(`nk_not_elementary_P`, via `divGE_of_liouville`). The certificates are those of the automatic
pipeline over constant curves (`autoTorsWits`).
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential GTors

section Res

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

/-- The residue `N B(α, y(0))/D′(α)` along the root `k` above `αⱼ`. -/
def resPc (B : BPoly ℚ) (Pc : PlaceCert F) (j k : ℕ) : F :=
  (Pc.fN j : F) * evalB (mapBQ B) (Pc.fα j) ((Pc.apx j k).getD 0 0) /
    Kron.evalC (CPoly.deriv (denQ Pc.αs)) (Pc.fα j)

/-- **The residue-divisor check at places.** -/
def resDivCheckP (G : GlobalCert F) (Fq : BPoly ℚ) (Pc : PlaceCert F) (B : BPoly ℚ)
    (Dq : CPoly ℚ) (lam : F →ₗ[ℚ] ℚ) (sc : ℕ) (eS : List ℤ) : Bool :=
  decide (G.Fc = mapBQ Fq) && decide (B.length ≤ G.n) &&
  CPoly.beq (Dq.map (algebraMap ℚ F)) (denQ Pc.αs) &&
  (List.range Pc.fib.length).all fun j ↦
    decide (Kron.evalC (CPoly.deriv (denQ Pc.αs)) (Pc.fα j) ≠ 0) &&
    decide (1 ≤ Pc.tp.getD j 0) &&
    (List.range G.n).all fun k ↦
      decide (((Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0 : ℕ) : ℚ) =
        sc * lam (resPc B Pc j k) + eS.getD j 0 * Pc.fN j)

lemma resDivCheckP_spec {G : GlobalCert F} {Fq : BPoly ℚ} {Pc : PlaceCert F} {B : BPoly ℚ}
    {Dq : CPoly ℚ} {lam : F →ₗ[ℚ] ℚ} {sc : ℕ} {eS : List ℤ}
    (h : resDivCheckP G Fq Pc B Dq lam sc eS = true) :
    G.Fc = mapBQ Fq ∧ B.length ≤ G.n ∧ toPoly (Dq.map (algebraMap ℚ F)) = toPoly (denQ Pc.αs) ∧
      ∀ j < Pc.fib.length, Kron.evalC (CPoly.deriv (denQ Pc.αs)) (Pc.fα j) ≠ 0 ∧
        1 ≤ Pc.tp.getD j 0 ∧ ∀ k < G.n,
          ((Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0 : ℕ) : ℚ) =
            sc * lam (resPc B Pc j k) + eS.getD j 0 * Pc.fN j := by
  simp only [resDivCheckP, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    CPoly.beq_iff] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, fun j hj ↦ ⟨(h.2 j hj).1.1, (h.2 j hj).1.2, (h.2 j hj).2⟩⟩

end Res

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 32000000 in
/-- **Non-elementary integrals from a non-torsion residue divisor at places.** As
`nk_not_elementary`, with the poles at arbitrary (possibly ramified) places above the roots of
`D`, certified by a `PlaceCert` (`not_torsion_places_map`): along the root `k` above `αⱼ`
(`x = αⱼ + T^{Nⱼ}`) the residue is `ρⱼₖ = Nⱼ B(αⱼ, yⱼₖ(0))/D′(αⱼ)`, and
`sⱼₖ Γ_{πⱼₖ} = s λ(ρⱼₖ) + eⱼ Nⱼ`. -/
theorem nk_not_elementary_P {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ιC : F →+* Cc)
    (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (G : GlobalCert F) (Fq : BPoly ℚ)
    (hsh : nkShape Fc ks m (liftCurve Fc ks m G.n Fq) = true) (θ : L)
    (hθ : θ ^ G.n + ∑ i ∈ Finset.range G.n,
      T.evP m ((liftCurve Fc ks m G.n Fq).getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (hG : G.globalCheck = true) (Pc : PlaceCert F) (hPc : Pc.check G.Fc G.n = true)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (Rp : RedFns p F) (φp : F →+* ℚ_[p]) (hRp : RedValid p Rp φp) (Cp : PrimeCert p)
    (hCp : primeCheck Rp G Cp = true) (Qp : PlaceCert.PrimeData p)
    (hQp : Pc.primeCheck Rp G.Fc G.n G.I.δL G.I.Bc G.I.Dc Cp.xs Qp = true)
    (Rq : RedFns q F) (φq : F →+* ℚ_[q]) (hRq : RedValid q Rq φq) (Cq : PrimeCert q)
    (hCq : primeCheck Rq G Cq = true) (Qq : PlaceCert.PrimeData q)
    (hQq : Pc.primeCheck Rq G.Fc G.n G.I.δL G.I.Bc G.I.Dc Cq.xs Qq = true)
    (Pb : ℕ) (Lm : List (List F))
    (htest : nonPrincOK G.n ((Qp.mp * Qq.mp) * Pc.cΓ) Pb G.I.δL G.I.Bc G.I.Dc Pc.αs
      (Pc.fcerts G.n) (Pc.bL G.n (Qp.mp * Qq.mp)) Lm = true ∨
      nonPrincOK G.n (pairMult p q Qp.mp Qq.mp * Pc.cΓ) Pb G.I.δL G.I.Bc G.I.Dc Pc.αs
      (Pc.fcerts G.n) (Pc.bL G.n (pairMult p q Qp.mp Qq.mp)) Lm = true)
    (B : BPoly ℚ) (Dq : CPoly ℚ) (lam : F →ₗ[ℚ] ℚ) (sc : ℕ) (eS : List ℤ)
    (hchk : resDivCheckP G Fq Pc B Dq lam sc eS = true) :
    ¬ HasElementaryIntegral (T.ev m η * ∑ j ∈ Finset.range G.n,
      T.evP m (liftQC Fc ks m (B.getD j [])) / T.evP m (liftQC Fc ks m Dq) * θ ^ j) := by
  classical
  intro hf
  set Pk := liftCurve Fc ks m G.n Fq with hPkdef
  have hPkl : Pk.length = G.n := length_liftCurve (Fc := Fc) (ks := ks) m G.n Fq
  have hθ' : θ ^ Pk.length + ∑ i ∈ Finset.range Pk.length, T.evP m (Pk.getD i []) * θ ^ i = 0 := by
    rw [hPkl]; exact hθ
  set f := T.ev m η * ∑ j ∈ Finset.range G.n,
      T.evP m (liftQC Fc ks m (B.getD j [])) / T.evP m (liftQC Fc ks m Dq) * θ ^ j with hfdef
  obtain ⟨E₁, _, _, _, _, hE₁, g, hg⟩ := hf
  haveI : CharZero E₁ := charZero_of_injective_algebraMap (algebraMap L E₁).injective
  obtain ⟨ι, s', c, u, v, hdata, hv, heqL⟩ := liouville_strong hE₁ _ g hg
  -- the tower in `E₁`
  obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E₁
  set ψ := algebraMap L E₁ with hψ
  have MSE := TE.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTE : TE.Tr (m + 1) := MSE.hyp.tr
  have hTEm : TE.Tr m := hTE.of_succ
  have hTr : T.Tr (m + 1) := (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr
  have hPE : ∀ P : GPoly (LC m), TE.evP m P = ψ (T.evP m P) := fun P ↦ by
    rw [← TE.sem_poly_code m hTE, ← T.sem_poly_code m hTr]
    exact (TE.sem_MP (m + 1) hTE _).trans ((hTEev (m + 1) _).trans
      (congrArg ψ (T.sem_MP (m + 1) hTr _).symm))
  have hθE : (ψ θ) ^ Pk.length + ∑ i ∈ Finset.range Pk.length,
      TE.evP m (Pk.getD i []) * (ψ θ) ^ i = 0 := by
    simp only [hPE, ← map_pow, ← map_mul, ← map_sum, ← map_add, hθ', map_zero]
  set S₁ := TE.nkCurve m hTE Pk hsh (ψ θ) hθE with hS₁
  have hsp := TE.nkShape_spec m hTEm Pk hsh
  have hS₁F : S₁.F.natDegree = Pk.length := polyF_natDegree _ _
  have hnS : S₁.F.natDegree = G.n := hS₁F.trans hPkl
  set η₁ : TE.F m := TE.val m η with hη₁
  have hx : S₁.x′ = aeval S₁.x (Polynomial.C η₁) := by
    rw [aeval_C]
    change (TE.ts m)′ = _
    rw [TE.ht m (by omega), hk]
    rfl
  have hnd : ∀ α : AlgebraicClosure (TE.F m),
      α′ ≠ ((Polynomial.C η₁).map (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)))).eval α :=
    fun α ↦ by
      rw [Polynomial.map_C, eval_C]
      exact not_deriv_of_integral η₁ (fun z hz ↦ MSE.hyp.nd m (by omega) η hk z hz) α
        (Algebra.IsIntegral.isIntegral α)
  have hK : ∀ c : TE.F m, (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c)′ =
      algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c′ := fun c ↦ deriv_algebraMap c
  have hconstC : ∀ z : E₁, z′ = 0 → z ∈ Set.range (algebraMap (TE.F m) E₁) := fun z hz ↦ by
    obtain ⟨c0, hc0⟩ := TE.hconst z hz
    exact ⟨⟨z, hc0 ▸ TE.const_mem m c0⟩, rfl⟩
  set T₁ := (TE.F m)⟮S₁.x⟯⟮S₁.y⟯ with hT₁
  have hxT : ∀ w ∈ TE.F (m + 1), w ∈ T₁ := fun w hw ↦
    IntermediateField.algebraMap_mem T₁ (⟨w, (TE.mem_F_succ).mp hw⟩ : (TE.F m)⟮S₁.x⟯)
  have hLT : ∀ z : L, ψ z ∈ T₁ := by
    intro z
    have hz := hgen z
    induction hz using IntermediateField.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact mem_adjoin_simple_self _ _
    | algebraMap w => exact hxT _ (hTEmem (m + 1) _ w.2)
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => rw [map_mul]; exact mul_mem h₁ h₂
    | inv w _ h₁ => rw [map_inv₀]; exact inv_mem h₁
  have hCT : ∀ w ∈ Differential.constField L E₁, w ∈ T₁ := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem w hw =>
      obtain ⟨c0, hc0⟩ := hconstC w hw
      rw [← hc0]
      exact S₁.const_mem c0
    | algebraMap z => exact hLT z
    | add w₁ w₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂
    | inv w _ h₁ => exact inv_mem h₁
  ------------------------------------------------------------------------------------------------
  -- the curve over `ℚ`, the certificate over `F`
  have hGf := globalCheck_spec hG
  obtain ⟨hGn0, hGmon, hGdeg, -⟩ := hGf.shape
  obtain ⟨hGFq, hBl, hDqe, hresC⟩ := resDivCheckP_spec hchk
  set ιq := algebraMap ℚ (TE.F m) with hιq
  set Kb := AlgebraicClosure (TE.F m) with hKb
  set φ := algebraMap (TE.F m) Kb with hφ
  set φF := algebraMap ℚ F with hφF
  have hιmem : ∀ a : F, ψ (algebraMap Cc L (ιC a)) ∈ TE.F m := fun a ↦
    hTEmem m _ (T.const_mem m (ιC a))
  set ι : F →+* TE.F m := RingHom.codRestrict ((algebraMap L E₁).comp ((algebraMap Cc L).comp ιC))
    (TE.F m) hιmem with hιdef
  set ψ₀ : F →+* Kb := φ.comp ι with hψ₀
  have hιq : ι.comp φF = ιq := ratHom_eq _ _
  have hφι' : ∀ a : F, φ (ι a) = ψ₀ a := fun a ↦ rfl
  have hι0 : ∀ a : F, (ι a)′ = 0 := fun a ↦ by
    apply Subtype.ext
    rw [MTower.coe_deriv]
    change (ψ (algebraMap Cc L (ιC a)))′ = 0
    rw [deriv_algebraMap, deriv_algebraMap, T.hC, map_zero, map_zero]
  have hmonQ : (toB Fq).Monic := by
    have h := hGmon
    rw [hGFq, mapBQ, toB_mapHom] at h
    exact Polynomial.monic_of_injective (map_injective _ φF.injective) h
  have hGFm : (toB G.Fc) = (toB Fq).map (mapRingHom φF) := by rw [hGFq, mapBQ, toB_mapHom]
  have hdegQ : (toB Fq).natDegree = G.n := by
    rw [← hGdeg, hGFm, natDegree_map_eq_of_injective (map_injective _ φF.injective)]
  have hSF : S₁.F = (toB G.Fc).map (mapRingHom ι) := by
    rw [show S₁.F = TE.nkF m hTEm Pk from rfl, TE.nkF_liftCurve m hTEm G.n Fq hmonQ hdegQ, hGFm,
      Polynomial.map_map, mapRingHom_comp, hιq]
  -- the places of the certificate
  have hPcF := Pc.check_spec hPc
  have hPcd : Pc.Facts G.Fc (toB G.Fc).natDegree := by rw [hGdeg]; exact hPcF
  have hNpos : ∀ j : Fin Pc.fib.length, 0 < Pc.fN j := fun j ↦ PlaceCert.fN_pos hPcF hGn0 j j.2
  have hspC := fun j : Fin Pc.fib.length ↦ split_places_map S₁ ι G.Fc hGmon hSF Pc hPcd j j.2
  have hlf : ∀ j : Fin Pc.fib.length, S₁.F.map (branchSub (Pc.fN j) (φ (ι (Pc.fα j)))) =
      ((List.ofFn fun k : Fin S₁.F.natDegree ↦ lmap φ (rCC ι G.Fc Pc j k)).map
        fun r ↦ X - Polynomial.C r).prod := fun j ↦
    S₁.split_lmap (K := Kb) (Pc.fN j) (ι (Pc.fα j)) (fun k ↦ rCC ι G.Fc Pc j k) (hspC j).1
  have hinjK : ∀ j : Fin Pc.fib.length, Function.Injective fun k : Fin S₁.F.natDegree ↦
      lmap φ (rCC ι G.Fc Pc j k) := fun j ↦ (lmap_injective _).comp (hspC j).2
  set α : Fin Pc.fib.length → TE.F m := fun j ↦ ι (Pc.fα j) with hαdef
  have hα : Function.Injective α := fun j j' h ↦ PlaceCert.fα_inj hPcF (ι.injective h)
  set lf : Fin Pc.fib.length → List (LaurentSeries Kb) :=
    fun j ↦ List.ofFn fun k : Fin S₁.F.natDegree ↦ lmap φ (rCC ι G.Fc Pc j k) with hlfdef
  -- the roots as power series, with their constant terms
  have hroot : ∀ (j : Fin Pc.fib.length) (k : Fin S₁.F.natDegree), ∃ Yp : PowerSeries Kb,
      lmap φ (rCC ι G.Fc Pc j k) = HahnSeries.ofPowerSeries ℤ Kb Yp ∧
        PowerSeries.constantCoeff Yp = ψ₀ ((Pc.apx j k).getD 0 0) := by
    intro j k
    obtain ⟨-, hrt⟩ := hPcF.rt j j.2
    obtain ⟨hπ, -, hs, -, -, htp⟩ := hrt k (by rw [← hnS]; exact k.2)
    refine ⟨PowerSeries.map ψ₀ (conjPS (Pc.rζ j k) (Pc.rs j k) (repK G.Fc Pc (Pc.rπ j k))), ?_, ?_⟩
    · rw [rCC, rCK, lmap_ofPS, lmap_ofPS, PowerSeries.map_comp]
      rfl
    · have hy : (PowerSeries.X : PowerSeries Kb) ^ (Pc.tp.getD j 0) ∣
          PowerSeries.map ψ₀ (conjPS (Pc.rζ j k) (Pc.rs j k) (repK G.Fc Pc (Pc.rπ j k))) -
            thetaT ψ₀ (toPoly (Pc.apx j k)) := by
        obtain ⟨-, hd⟩ := repK_spec G.Fc Pc (Pc.rπ j k) (hPcF.pl _ hπ).2.2
        have hd' := map_dvd (PowerSeries.map ψ₀) hd
        rw [map_pow, PowerSeries.map_X, map_sub, thetaT_apply, map_coe_poly, Polynomial.map_map,
          RingHom.comp_id, ← thetaT_apply] at hd'
        rw [map_conjPS]
        exact conj_approx ψ₀ (Pc.rζ j k) hs _ _ hd' htp
      have htp1 : 1 ≤ Pc.tp.getD j 0 := (hresC j j.2).2.1
      have hX1 := (pow_dvd_pow (PowerSeries.X : PowerSeries Kb) htp1).trans hy
      rw [pow_one, PowerSeries.X_dvd_iff, map_sub, sub_eq_zero] at hX1
      rw [hX1, thetaT_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
        coeff_map, coeff_toPoly]
  choose Yr hYr hYr0 using hroot
  ------------------------------------------------------------------------------------------------
  -- the integrand as `B(x, y)/D(x)`
  set QB : (TE.F m)[X][X] := Polynomial.C (Polynomial.C η₁) * (toB B).map (mapRingHom ιq)
    with hQB
  set MD : (TE.F m)[X] := (toPoly Dq).map ιq with hMD
  have hevB : S₁.evXY ((toB B).map (mapRingHom ιq)) =
      ∑ j ∈ Finset.range G.n, TE.evP m (liftQC Fc ks m (B.getD j [])) * (ψ θ) ^ j := by
    rw [toB_eq_sum B G.n hBl, CurveData.evXY, Polynomial.map_sum, Polynomial.map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_X, eval_mul, eval_C, eval_pow, eval_X,
      coe_mapRingHom, ← TE.toPoly_liftQC m hTEm]
    congr 1
    exact TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm) _
  have hDv : aeval S₁.x MD = TE.evP m (liftQC Fc ks m Dq) := by
    rw [hMD, ← TE.toPoly_liftQC m hTEm]
    exact TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm) _
  have hfval : ψ f = S₁.evXY QB / aeval S₁.x MD := by
    rw [hQB, hDv]
    have e1 : S₁.evXY (Polynomial.C (Polynomial.C η₁) * (toB B).map (mapRingHom ιq)) =
        (η₁ : E₁) * S₁.evXY ((toB B).map (mapRingHom ιq)) := by
      rw [CurveData.evXY, CurveData.evXY, Polynomial.map_mul, eval_mul, Polynomial.map_C, eval_C]
      congr 1
      exact aeval_C _ _
    rw [e1, hevB, hfdef, map_mul, map_sum, ← hTEev m η, Finset.mul_sum, Finset.mul_sum,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, map_div₀, map_pow, ← hPE, ← hPE]
    rw [show ((η₁ : TE.F m) : E₁) = TE.ev m η from rfl]
    ring
  set fE := S₁.evXY QB / aeval S₁.x MD with hfE
  have hfT : fE ∈ T₁ := by rw [← hfval]; exact hLT f
  ------------------------------------------------------------------------------------------------
  -- the Liouville form over `T₁`
  have heq₁ : fE = v′ + ∑ i ∈ s', c i * logDeriv (u i) := by rw [← hfval, heqL, add_comm]
  obtain ⟨k, d, w, ⟨hd', hw, -⟩, hsum⟩ :=
    logSum_qindep T₁.toSubfield s' c u (fun i hi ↦ (hdata i hi).1)
      (fun i hi ↦ ⟨(hdata i hi).2.2, hCT _ (hdata i hi).2.1⟩)
  set d' : ℕ → TE.F m := fun jj ↦
    if h : jj < k then Classical.choose (hconstC (d jj) (hd' jj h)) else 0 with hd'def
  have hdd : ∀ jj < k, algebraMap (TE.F m) E₁ (d' jj) = d jj := fun jj hjj ↦ by
    simp only [hd'def, dite_cond_eq_true (eq_true hjj)]
    exact Classical.choose_spec (hconstC (d jj) (hd' jj hjj))
  have hww : ∀ jj < k, w jj ∈ T₁ ∧ w jj ≠ 0 := fun jj hjj ↦ ⟨(hw jj hjj).2, (hw jj hjj).1⟩
  have heq' : fE = v′ + ∑ jj ∈ Finset.range k,
      algebraMap (TE.F m) E₁ (d' jj) * ((w jj)′ / w jj) := by
    rw [heq₁, hsum]
    congr 1
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [hdd jj (Finset.mem_range.mp hjj), logDeriv]
  ------------------------------------------------------------------------------------------------
  -- the denominator
  have hMDι : MD = (toPoly (denQ Pc.αs)).map ι := by
    rw [hMD, ← hDqe, toPoly_mapHom, Polynomial.map_map, hιq]
  have hMDφ : MD.map φ = (Pc.αs.map fun a ↦ X - Polynomial.C (ψ₀ a)).prod := by
    rw [hMDι, Polynomial.map_map, toPoly_denQ, Polynomial.map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun a _ ↦ ?_
    simp [hψ₀]
  have hαsl : Pc.αs.length = Pc.fib.length := by simp [PlaceCert.αs]
  have hDb : ∀ b : Kb, b ∉ Set.range (fun j ↦ φ (α j)) → (MD.map φ).eval b ≠ 0 := by
    intro b hb h0
    rw [hMDφ, eval_list_prod, List.prod_eq_zero_iff, List.map_map, List.mem_map] at h0
    obtain ⟨a, ha, hab⟩ := h0
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C, sub_eq_zero] at hab
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    have hi' : i < Pc.fib.length := by rw [← hαsl]; exact hi
    exact hb ⟨⟨i, hi'⟩, by
      change φ (ι (Pc.fα i)) = b
      rw [hφι', hab, ← Pc.αs_getD i hi', List.getD_eq_getElem _ _ hi]⟩
  have hMD0 : MD ≠ 0 := by
    intro h0
    obtain ⟨b, hb⟩ : ∃ b : Kb, b ∉ Set.range (fun j ↦ φ (α j)) :=
      (Set.finite_range _).infinite_compl.nonempty
    exact hDb b hb (by rw [h0, Polynomial.map_zero, eval_zero])
  have hD0 : ∀ j : Fin Pc.fib.length, MD.eval (α j) = 0 := fun j ↦ by
    rw [hMDι, hαdef, eval_map, eval₂_at_apply, toPoly_denQ, eval_list_prod, List.prod_eq_zero,
      map_zero]
    rw [List.map_map, List.mem_map]
    refine ⟨Pc.fα j, ?_, by simp⟩
    rw [← Pc.αs_getD j j.2, List.getD_eq_getElem _ _ (by rw [hαsl]; exact j.2)]
    exact List.getElem_mem _
  have hD1v : ∀ j : Fin Pc.fib.length, (derivative MD).eval (α j) =
      ι (Kron.evalC (CPoly.deriv (denQ Pc.αs)) (Pc.fα j)) := fun j ↦ by
    rw [hMDι, Polynomial.derivative_map, eval_map, eval₂_at_apply, Kron.evalC_eq, toPoly_deriv]
  have hD1 : ∀ j : Fin Pc.fib.length, (derivative MD).eval (α j) ≠ 0 := fun j ↦ by
    rw [hD1v]
    exact (map_ne_zero_iff _ ι.injective).mpr (hresC j j.2).1
  ------------------------------------------------------------------------------------------------
  -- the residues
  set ρ : Fin Pc.fib.length → LaurentSeries Kb → TE.F m := fun j ↦
    Function.extend (fun k : Fin S₁.F.natDegree ↦ lmap φ (rCC ι G.Fc Pc j k))
      (fun k ↦ ι (resPc B Pc j k)) 0 with hρdef
  set Γ : Fin Pc.fib.length → LaurentSeries Kb → ℕ := fun j ↦
    Function.extend (fun k : Fin S₁.F.natDegree ↦ lmap φ (rCC ι G.Fc Pc j k))
      (fun k ↦ Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0) 0 with hΓdef
  have hρk : ∀ j (k : Fin S₁.F.natDegree), ρ j (lmap φ (rCC ι G.Fc Pc j k)) = ι (resPc B Pc j k) := fun j k ↦
    (hinjK j).extend_apply _ _ k
  have hΓk : ∀ j (k : Fin S₁.F.natDegree), Γ j (lmap φ (rCC ι G.Fc Pc j k)) = Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0 :=
    fun j k ↦ (hinjK j).extend_apply _ _ k
  have hroot' : ∀ (j : Fin Pc.fib.length) (k : Fin S₁.F.natDegree),
      (S₁.F.map (branchSub (Pc.fN j) (φ (α j)))).eval (HahnSeries.ofPowerSeries ℤ Kb (Yr j k)) = 0 :=
    fun j k ↦ by
      rw [← hYr j k]
      exact S₁.root_of_mem (hlf j) (List.mem_ofFn.mpr ⟨k, rfl⟩)
  -- transport along `r = ofPS Y`
  have htr : ∀ (j : Fin Pc.fib.length) (r r' : LaurentSeries Kb) (he : r = r')
      (h1 : (S₁.F.map (branchSub (Pc.fN j) (φ (α j)))).eval r = 0)
      (h2 : (S₁.F.map (branchSub (Pc.fN j) (φ (α j)))).eval r' = 0),
      S₁.embG (branchSub (Pc.fN j) (φ (α j))) (branchSub_injective _ (hNpos j) _) r h1 ⟨fE, hfT⟩ =
        S₁.embG (branchSub (Pc.fN j) (φ (α j))) (branchSub_injective _ (hNpos j) _) r' h2
          ⟨fE, hfT⟩ := by
    intro j r r' he h1 h2; subst he; rfl
  have hbelow : ∀ j r (hr : r ∈ lf j) (i : ℤ), i < -(Pc.fN j : ℤ) →
      (S₁.embG (branchSub (Pc.fN j) (φ (α j))) (branchSub_injective _ (hNpos j) _) r
        (S₁.root_of_mem (hlf j) hr) ⟨fE, hfT⟩).coeff i = 0 := by
    intro j r hr i hi
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
    rw [htr j _ _ (hYr j k) _ (hroot' j k)]
    exact (S₁.embG_pole_N QB MD (α j) (hD0 j) (hD1 j) (Pc.fN j) (hNpos j) (Yr j k) (hroot' j k)
      hfT).1 i hi
  have hres : ∀ j r (hr : r ∈ lf j), (S₁.embG (branchSub (Pc.fN j) (φ (α j)))
      (branchSub_injective _ (hNpos j) _) r (S₁.root_of_mem (hlf j) hr) ⟨fE, hfT⟩).coeff
        (-(Pc.fN j : ℤ)) =
      (sBranch (Polynomial.C η₁) (φ (α j)) (Pc.fN j)).coeff (1 - (Pc.fN j : ℤ)) * φ (ρ j r) := by
    intro j r hr
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
    rw [htr j _ _ (hYr j k) _ (hroot' j k), (S₁.embG_pole_N QB MD (α j) (hD0 j) (hD1 j) (Pc.fN j)
      (hNpos j) (Yr j k) (hroot' j k) hfT).2, hρk]
    have hα' : (α j)′ = 0 := hι0 _
    rw [sBranch_coeff _ _ _ (hNpos j), Polynomial.map_C, eval_C, hK, hα', map_zero, sub_zero]
    have e1 : (QB.map (mapRingHom φ)) =
        Polynomial.C (Polynomial.C (φ η₁)) * (toB (mapBQ (F := F) B)).map (mapRingHom ψ₀) := by
      rw [hQB, Polynomial.map_mul, Polynomial.map_C, coe_mapRingHom, Polynomial.map_C,
        Polynomial.map_map, Polynomial.mapRingHom_comp, mapBQ, toB_mapHom, Polynomial.map_map,
        Polynomial.mapRingHom_comp, ← hιq, hψ₀]
      rfl
    rw [e1, Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C, coe_evalRingHom, eval_C,
      hYr0, hD1v]
    have hφ2 : ∀ a : F, algebraMap (TE.F m) Kb (ι a) = ψ₀ a := hφι'
    simp only [hαdef, hφι', hφ2]
    rw [evalB_map, resPc, map_div₀, map_mul, map_natCast]
    have hN0 : (Pc.fN j : Kb) ≠ 0 := by exact_mod_cast (hNpos j).ne'
    have key : ∀ a b c : Kb, a * b / c = 1 / (Pc.fN j : Kb) * a * ((Pc.fN j : Kb) * b / c) := by
      intro a b c
      rw [show 1 / (Pc.fN j : Kb) * a * ((Pc.fN j : Kb) * b / c) =
        (1 / (Pc.fN j : Kb) * (Pc.fN j : Kb)) * (a * b / c) by ring, one_div_mul_cancel hN0, one_mul]
    exact key _ _ _
  ------------------------------------------------------------------------------------------------
  -- no other finite poles
  have hfree : ∀ b : Kb, b ∉ Set.range (fun j ↦ φ (α j)) → ∀ (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries Kb))
      (hl : S₁.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l) (i : ℤ), i < 1 - (N : ℤ) →
      (S₁.embG (branchSub N b) (branchSub_injective N (Nat.pos_of_ne_zero hN) b) r
        (S₁.root_of_mem hl hr) ⟨fE, hfT⟩).coeff i = 0 := by
    intro b hb N hN l hl r hr i hi
    have hNp := Nat.pos_of_ne_zero hN
    set Φ := S₁.embG (branchSub N b) (branchSub_injective N hNp b) r (S₁.root_of_mem hl hr)
      with hΦ
    set Dm : T₁ := ⟨aeval S₁.x MD, S₁.aeval_mem MD⟩ with hDm
    have e : (⟨fE, hfT⟩ : T₁) = S₁.evT QB / Dm :=
      Subtype.ext (by rw [IntermediateField.coe_div, S₁.coe_evT])
    have hdm : Φ Dm = branchSub N b MD := S₁.embG_polyX _ _ _ _ MD (S₁.aeval_mem MD)
    have hdd0 : branchSub (K := Kb) N b MD ≠ 0 :=
      (map_ne_zero_iff _ (branchSub_injective N hNp b)).mpr hMD0
    have hdo : (branchSub (K := Kb) N b MD).order = 0 :=
      Curves.CurveData.order_branchSub_eq_zero (C := TE.F m) MD b N hNp (hDb b hb)
    have hBo : 0 ≤ (Φ (S₁.evT QB)).order := S₁.regularFinite_evT (K := Kb) QB b N hN l hl r hr
    change (Φ ⟨fE, hfT⟩).coeff i = 0
    rw [e, map_div₀, hdm]
    by_cases hb0 : Φ (S₁.evT QB) = 0
    · rw [hb0, zero_div]; rfl
    apply HahnSeries.coeff_eq_zero_of_lt_order
    rw [div_eq_mul_inv, HahnSeries.order_mul hb0 (inv_ne_zero hdd0), order_inv_nk _ hdd0, hdo]
    have : (1 : ℤ) ≤ N := by exact_mod_cast hNp
    omega
  ------------------------------------------------------------------------------------------------
  -- the divisor `Γ`
  obtain ⟨Λ, hΛ⟩ := exists_proj (TE.F m) ι lam
  have hΓ : ∀ j r, r ∈ lf j → (Γ j r : ℚ) = sc * Λ (ρ j r) + eS.getD j 0 * Pc.fN j := by
    intro j r hr
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
    rw [hΓk, hρk, hΛ]
    exact (hresC j j.2).2.2 k (by rw [← hnS]; exact k.2)
  have hgs : ∀ j, ((lf j).map (Γ j)).sum = Pc.fN j * Pc.dΓ.getD j 0 := by
    intro j
    rw [hlfdef]
    simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, hΓk]
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ Pc.rs j k * Pc.Γp.getD (Pc.rπ j k) 0), hnS]
    exact (hPcF.dΓ j j.2).1
  have hsumΓ : ∑ j : Fin Pc.fib.length, Pc.dΓ.getD j 0 = Pc.cΓ * Pk.length := by
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ Pc.dΓ.getD j 0), hPkl]
    exact hPcF.sum
  obtain ⟨M, hM, γ, hγ0, hγ⟩ := S₁.divGE_of_liouville (K := Kb) (Polynomial.C η₁) hx hK hnd
    Pk.length _ hS₁F hsp.1 hsp.2.1 hsp.2.2.1 hsp.2.2.2.1 hsp.2.2.2.2 k d' w hww v fE (hCT v hv)
    hfT heq' α hα (fun j ↦ Pc.fN j) hNpos lf hlf ρ hbelow hres hfree Λ sc (fun j ↦ eS.getD j 0)
    Γ Pc.cΓ (fun j ↦ Pc.dΓ.getD j 0) hΓ hgs hsumΓ
  exact not_torsion_places_map (Kb := Kb) S₁ ι G hSF (globalCheckR_of_globalCheck hG) Pc hPc hpq Rp φp hRp Cp hCp Qp hQp
    Rq φq hRq Cq hCq Qq hQq Pb Lm htest M hM hNpos hlf ⟨γ, hγ0, hγ⟩

/-- **The witness form** (the data of the automatic constant-curve pipeline, `autoTorsWits`):
the certificates of a `TorsWitP` over a number field embedded in the constants, with the residues
of `f` checked by `resDivCheckP` for `λ = coord j₀`, `s`, `eⱼ` of the witness. -/
theorem nk_not_elementary_TW {F : Type*} [Field F] [DecidableEq F] [CharZero F]
    [EllQuad.QCoords F] (ιC : F →+* Cc)
    (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (redAt : (p : ℕ) → Option (RedFns p F))
    (hred : ∀ (p : ℕ) [Fact p.Prime] (R : RedFns p F), redAt p = some R →
      ∃ φ : F →+* ℚ_[p], RedValid p R φ)
    (tw : TorsWitP F) (Fq : BPoly ℚ)
    (hsh : nkShape Fc ks m (liftCurve Fc ks m tw.T.n Fq) = true) (θ : L)
    (hθ : θ ^ tw.T.n + ∑ i ∈ Finset.range tw.T.n,
      T.evP m ((liftCurve Fc ks m tw.T.n Fq).getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (hG : tw.T.globalCheck = true) (hPc : tw.Pc.check tw.T.Fc tw.T.n = true)
    (hpq : tw.p ≠ tw.q) (hP : primeOKP redAt tw.T tw.Pc tw.p tw.Pp tw.Qp = true)
    (hQ : primeOKP redAt tw.T tw.Pc tw.q tw.Pq tw.Qq = true)
    (htest : nonPrincOK tw.T.n ((tw.Qp.mp * tw.Qq.mp) * tw.Pc.cΓ) tw.Pb tw.T.I.δL tw.T.I.Bc
      tw.T.I.Dc tw.Pc.αs (tw.Pc.fcerts tw.T.n) (tw.Pc.bL tw.T.n (tw.Qp.mp * tw.Qq.mp)) tw.Lm = true ∨
      nonPrincOK tw.T.n (pairMult tw.p tw.q tw.Qp.mp tw.Qq.mp * tw.Pc.cΓ) tw.Pb tw.T.I.δL tw.T.I.Bc
      tw.T.I.Dc tw.Pc.αs (tw.Pc.fcerts tw.T.n) (tw.Pc.bL tw.T.n (pairMult tw.p tw.q tw.Qp.mp
        tw.Qq.mp)) tw.Lm = true)
    (B : BPoly ℚ) (Dq : CPoly ℚ)
    (hchk : resDivCheckP tw.T Fq tw.Pc B Dq (EllQuad.QCoords.coord tw.j₀) tw.s tw.eL = true) :
    ¬ HasElementaryIntegral (T.ev m η * ∑ j ∈ Finset.range tw.T.n,
      T.evP m (liftQC Fc ks m (B.getD j [])) / T.evP m (liftQC Fc ks m Dq) * θ ^ j) := by
  obtain ⟨hpp, Rp, hRp, hPp', hQp'⟩ := primeOKP_spec hP
  obtain ⟨hqp, Rq, hRq, hPq', hQq'⟩ := primeOKP_spec hQ
  haveI : Fact tw.p.Prime := ⟨hpp⟩
  haveI : Fact tw.q.Prime := ⟨hqp⟩
  obtain ⟨φp, hφp⟩ := hred tw.p Rp hRp
  obtain ⟨φq, hφq⟩ := hred tw.q Rq hRq
  exact T.nk_not_elementary_P ιC hmon hdeg m hn hc hk tw.T Fq hsh θ hθ hgen hG tw.Pc hPc hpq
    Rp φp hφp tw.Pp hPp' tw.Qp hQp' Rq φq hφq tw.Pq hPq' tw.Qq hQq' tw.Pb tw.Lm htest B Dq
    (EllQuad.QCoords.coord tw.j₀) tw.s tw.eL hchk

end MTower

end Curves.MT
