import RischTragerBronstein.Mixed.NKTorsion
import RischTragerBronstein.Mixed.NKLogRes
import RischTragerBronstein.Torsion.NonTorsionMap

/-!
# Non-elementary integrals over a non-Kummer curve: non-torsion residue divisors

For a logarithmic level `t′ = η` and a curve `θⁿ + ∑ aᵢ(t) θⁱ = 0` defined over `ℚ` with a single
place at infinity, the integrand `f = η B(t, θ)/D(t)` (`B`, `D` over `ℚ`, `D = ∏ⱼ(t − αⱼ)` over a
computable field `F ⊆` constants) has simple poles at the points `(αⱼ, yⱼₖ)` (`F`-rational, all
`n` branches unramified) with residues `ρⱼₖ = B(αⱼ, yⱼₖ)/D′(αⱼ) ∈ F` (with respect to `dt`) and no
other finite poles. If `Γⱼₖ = s λ(ρⱼₖ) + eⱼ` (`s ∈ ℕ`, `eⱼ ∈ ℤ`, `λ : F → ℚ` any `ℚ`-linear form)
is a divisor certified non-torsion over `F` (`not_torsion_of_cert_map`), then `f` has no elementary integral
(`nk_not_elementary`): a Liouville form would make `M Γ − M c ∞` effective-principal after the
projection `Λ : C → ℚ` extending `λ` (`exists_proj`, `divGEU_of_liouville`).
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- A rational polynomial as a code over level `m`. -/
def liftQC (m : ℕ) (p : CPoly ℚ) : GPoly (LC m) := p.map (mcst Fc ks m)

/-- The codes `a₀, …, aₙ₋₁` of a curve over `ℚ`. -/
def liftCurve (m n : ℕ) (W : BPoly ℚ) : List (GPoly (LC m)) :=
  (List.range n).map fun i ↦ liftQC Fc ks m (W.getD i [])

end Codes

section Res

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

/-- `∏ⱼ (X − αⱼ)`. -/
def denQ (αL : List F) : CPoly F := prodC (αL.map fun a ↦ [-a, 1])

/-- A rational bivariate polynomial over `F`. -/
def mapBQ (W : BPoly ℚ) : BPoly F := W.map (·.map (algebraMap ℚ F))

/-- The residue `W(αⱼ, y)/D′(αⱼ)`. -/
def resF (W : BPoly F) (αL : List F) (j : ℕ) (y : F) : F :=
  evalB W (αL.getD j 0) y / Kron.evalC (CPoly.deriv (denQ αL)) (αL.getD j 0)

/-- **The residue-divisor check**: the curve is `Fq` over `ℚ`, `deg_Y B < n`, `D = ∏ⱼ (X − αⱼ)`,
`D′(αⱼ) ≠ 0`, and `Γⱼₖ = s λ(ρⱼₖ) + eⱼ` for the residues `ρⱼₖ ∈ F` and a `ℚ`-linear `λ : F → ℚ`. -/
def resDivCheck (G : GlobalCert F) (Fq B : BPoly ℚ) (Dq : CPoly ℚ) (lam : F →ₗ[ℚ] ℚ) (sc : ℕ)
    (eS : List ℤ) : Bool :=
  decide (G.Fc = mapBQ Fq) && decide (B.length ≤ G.n) &&
  CPoly.beq (Dq.map (algebraMap ℚ F)) (denQ G.αL) &&
  (List.range G.αL.length).all fun j ↦
    decide (Kron.evalC (CPoly.deriv (denQ G.αL)) (G.αL.getD j 0) ≠ 0) &&
    (List.range G.n).all fun k ↦
      decide ((((G.ΓL.getD j []).getD k 0 : ℕ) : ℚ) =
        sc * lam (resF (mapBQ B) G.αL j ((G.yL.getD j []).getD k 0)) + eS.getD j 0)

lemma resDivCheck_spec {G : GlobalCert F} {Fq B : BPoly ℚ} {Dq : CPoly ℚ} {lam : F →ₗ[ℚ] ℚ}
    {sc : ℕ} {eS : List ℤ} (h : resDivCheck G Fq B Dq lam sc eS = true) :
    G.Fc = mapBQ Fq ∧ B.length ≤ G.n ∧ toPoly (Dq.map (algebraMap ℚ F)) = toPoly (denQ G.αL) ∧
      ∀ j < G.αL.length, Kron.evalC (CPoly.deriv (denQ G.αL)) (G.αL.getD j 0) ≠ 0 ∧ ∀ k < G.n,
        (((G.ΓL.getD j []).getD k 0 : ℕ) : ℚ) =
          sc * lam (resF (mapBQ B) G.αL j ((G.yL.getD j []).getD k 0)) + eS.getD j 0 := by
  simp only [resDivCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    CPoly.beq_iff] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

end Res

lemma toPoly_denQ {F : Type*} [Field F] [DecidableEq F] (αL : List F) :
    toPoly (denQ αL) = (αL.map fun a ↦ X - Polynomial.C a).prod := by
  induction αL with
  | nil => simp [denQ, prodC]
  | cons a l ih =>
    simp only [denQ, prodC, List.map_cons, List.foldr_cons, List.prod_cons] at ih ⊢
    rw [toPoly_mul, ih]
    simp only [toPoly_cons, toPoly_nil, mul_zero, add_zero, map_one, map_neg]
    ring

lemma toB_eq_sum {F : Type*} [Field F] (W : BPoly F) (N : ℕ) (hW : W.length ≤ N) :
    toB W = ∑ j ∈ Finset.range N, Polynomial.C (toPoly (W.getD j [])) * X ^ j := by
  ext1 l
  rw [coeff_toB, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hl
  · rfl
  · rw [Finset.mem_range, not_lt] at hl
    rw [List.getD_eq_default _ _ (hW.trans hl)]
    rfl

lemma toB_mapHom {A B : Type*} [CommRing A] [CommRing B] (g : A →+* B) :
    ∀ W : BPoly A, toB (W.map (·.map g)) = (toB W).map (mapRingHom g)
  | [] => by simp
  | c :: W => by
    rw [List.map_cons, toB_cons, toB_cons, toB_mapHom g W, toPoly_mapHom, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, coe_mapRingHom]

/-- The value of a bivariate polynomial under any ring map. -/
lemma evalB_map {F R : Type*} [Field F] [DecidableEq F] [CommRing R] (φ : F →+* R) (B : BPoly F)
    (a y : F) :
    (((toB B).map (mapRingHom φ)).map (evalRingHom (φ a))).eval (φ y) = φ (evalB B a y) := by
  have h : (evalRingHom (φ a)).comp (mapRingHom φ) = φ.comp (evalRingHom a) :=
    RingHom.ext fun P ↦ by
      simp only [RingHom.comp_apply, coe_mapRingHom, coe_evalRingHom, eval_map, eval₂_at_apply]
  rw [Polynomial.map_map, h, ← Polynomial.map_map, eval_map, eval₂_at_apply, evalB_eq, evalW]

lemma ratHom_eq {R : Type*} [DivisionRing R] [CharZero R] (φ ψ : ℚ →+* R) : φ = ψ :=
  Subsingleton.elim _ _

/-- **Extending a `ℚ`-linear form** along a field embedding `F → C`. -/
lemma exists_proj (C : Type*) [Field C] [CharZero C] {F : Type*} [Field F] [CharZero F]
    (ι : F →+* C) (lam : F →ₗ[ℚ] ℚ) : ∃ Λ : C →ₗ[ℚ] ℚ, ∀ a : F, Λ (ι a) = lam a := by
  set ιL : F →ₗ[ℚ] C := ι.toRatAlgHom.toLinearMap with hιL
  have hker : LinearMap.ker ιL = ⊥ := LinearMap.ker_eq_bot.mpr ι.injective
  obtain ⟨g, hg⟩ := ιL.exists_leftInverse_of_injective hker
  refine ⟨lam.comp g, fun a ↦ ?_⟩
  have := congrArg (fun h : F →ₗ[ℚ] F ↦ h a) hg
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
  rw [LinearMap.comp_apply]
  exact congrArg lam this

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma toPoly_liftQC (m : ℕ) (h : T.Tr m) (p : CPoly ℚ) :
    GPoly.toPoly (T.MP m h) (liftQC Fc ks m p) = (toPoly p).map (algebraMap ℚ (T.F m)) := by
  induction p with
  | nil => simp [liftQC]
  | cons a p ih =>
    simp only [liftQC, List.map_cons] at ih ⊢
    rw [GPoly.toPoly_cons, ih, toPoly_cons, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X, T.sem_mcst m h, eq_ratCast]

lemma length_liftCurve (m n : ℕ) (W : BPoly ℚ) : (liftCurve Fc ks m n W).length = n := by
  simp [liftCurve]

lemma nkF_liftCurve (m : ℕ) (h : T.Tr m) (n : ℕ) (W : BPoly ℚ) (hmon : (toB W).Monic)
    (hdeg : (toB W).natDegree = n) :
    T.nkF m h (liftCurve Fc ks m n W) = (toB W).map (mapRingHom (algebraMap ℚ (T.F m))) := by
  rw [nkF, length_liftCurve]
  ext1 i
  rw [coeff_map]
  rcases lt_trichotomy i n with hi | rfl | hi
  · rw [polyF_coeff _ _ _ hi, liftCurve, List.getD_eq_getElem _ _ (by simpa using hi),
      List.getElem_map, List.getElem_range, toPoly_liftQC, coeff_toB, coe_mapRingHom]
  · have h1 := (polyF_monic (fun j ↦ GPoly.toPoly (T.MP m h)
      ((liftCurve Fc ks m i W).getD j [])) i)
    rw [Monic, Polynomial.leadingCoeff, polyF_natDegree] at h1
    rw [h1, ← hdeg, ← Polynomial.leadingCoeff, hmon.leadingCoeff, map_one]
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [polyF_natDegree]; exact hi),
      coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hi), map_zero]

set_option maxHeartbeats 16000000 in
/-- **Non-elementary integrals from a non-torsion residue divisor.** Over a logarithmic level
`t′ = η`, on the curve `θⁿ + ∑ aᵢ(t) θⁱ = 0` defined over `ℚ` (certified by `G` over a computable
field `F` embedded in the constants, single place at infinity), the integrand `η B(t, θ)/D(t)`
with `D = ∏ⱼ(t − αⱼ)` has residues `ρⱼₖ = B(αⱼ, yⱼₖ)/D′(αⱼ) ∈ F`; if `Γⱼₖ = s λ(ρⱼₖ) + eⱼ` (any
`ℚ`-linear `λ : F → ℚ`) is certified non-torsion, it has no elementary integral. -/
theorem nk_not_elementary {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ιC : F →+* Cc)
    (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (G : GlobalCert F) (Fq : BPoly ℚ)
    (hsh : nkShape Fc ks m (liftCurve Fc ks m G.n Fq) = true) (θ : L)
    (hθ : θ ^ G.n + ∑ i ∈ Finset.range G.n,
      T.evP m ((liftCurve Fc ks m G.n Fq).getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (hG : G.globalCheck = true) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (Rp : RedFns p F) (φp : F →+* ℚ_[p]) (hRp : RedValid p Rp φp) (Cp : PrimeCert p)
    (hCp : primeCheck Rp G Cp = true)
    (Rq : RedFns q F) (φq : F →+* ℚ_[q]) (hRq : RedValid q Rq φq) (Cq : PrimeCert q)
    (hCq : primeCheck Rq G Cq = true) (Pb : ℕ) (Lm : List (List F))
    (htest : nonPrincCheck G.n ((Cp.mp * Cq.mp) * G.cdeg) Pb G.I.δL G.I.Bc G.I.Dc G.αL G.cΓ
      (G.ΓL.map (·.map ((Cp.mp * Cq.mp) * ·))) Lm = true)
    (B : BPoly ℚ) (Dq : CPoly ℚ) (lam : F →ₗ[ℚ] ℚ) (sc : ℕ) (eS : List ℤ)
    (hchk : resDivCheck G Fq B Dq lam sc eS = true) :
    ¬ HasElementaryIntegral (T.ev m η * ∑ j ∈ Finset.range G.n,
      T.evP m (liftQC Fc ks m (B.getD j [])) / T.evP m (liftQC Fc ks m Dq) * θ ^ j) := by
  classical
  intro hf
  set Pc := liftCurve Fc ks m G.n Fq with hPc
  have hPcl : Pc.length = G.n := length_liftCurve (Fc := Fc) (ks := ks) m G.n Fq
  have hθ' : θ ^ Pc.length + ∑ i ∈ Finset.range Pc.length, T.evP m (Pc.getD i []) * θ ^ i = 0 := by
    rw [hPcl]; exact hθ
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
  have hθE : (ψ θ) ^ Pc.length + ∑ i ∈ Finset.range Pc.length,
      TE.evP m (Pc.getD i []) * (ψ θ) ^ i = 0 := by
    simp only [hPE, ← map_pow, ← map_mul, ← map_sum, ← map_add, hθ', map_zero]
  set S₁ := TE.nkCurve m hTE Pc hsh (ψ θ) hθE with hS₁
  have hsp := TE.nkShape_spec m hTEm Pc hsh
  have hS₁F : S₁.F.natDegree = Pc.length := polyF_natDegree _ _
  have hnS : S₁.F.natDegree = G.n := hS₁F.trans hPcl
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
  obtain ⟨-, hGmon, hGdeg, -⟩ := hGf.shape
  obtain ⟨hGFq, hBl, hDqe, hresC⟩ := resDivCheck_spec hchk
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
    rw [show S₁.F = TE.nkF m hTEm Pc from rfl, TE.nkF_liftCurve m hTEm G.n Fq hmonQ hdegQ, hGFm,
      Polynomial.map_map, mapRingHom_comp, hιq]
  obtain ⟨-, hαnd, hpt⟩ := ptCheck_spec ψ₀ hGmon hGdeg hGf.pt
  -- the branches at the points
  have hY0 : ∀ j : Fin G.αL.length, ∃ Y : Fin G.n → PowerSeries Kb,
      (∀ k, PowerSeries.constantCoeff (Y k) = ψ₀ ((G.yL.getD j []).getD k 0)) ∧
      ((toB G.Fc).map (mapRingHom ψ₀)).map (branchSub (C := Kb) (K := Kb) 1 (ψ₀ (G.αL.getD j 0))) =
        ∏ k, (X - Polynomial.C (HahnSeries.ofPowerSeries ℤ Kb (Y k))) := fun j ↦ by
    obtain ⟨Y, hYc, hYs, -⟩ := (hpt j j.2).2
    exact ⟨Y, hYc, hYs⟩
  choose Y0 hY0c hY0s using hY0
  set Y : Fin G.αL.length → Fin S₁.F.natDegree → PowerSeries Kb :=
    fun j k ↦ Y0 j (Fin.cast hnS k) with hYdef
  set α : Fin G.αL.length → TE.F m := fun j ↦ ι (G.αL.getD j 0) with hαdef
  set ys : Fin G.αL.length → Fin S₁.F.natDegree → TE.F m :=
    fun j k ↦ ι ((G.yL.getD j []).getD k 0) with hysdef
  have hbr : ∀ (N : ℕ) (a : F), S₁.F.map (branchSub (C := TE.F m) (K := Kb) N (ψ₀ a)) =
      ((toB G.Fc).map (mapRingHom ψ₀)).map (branchSub (C := Kb) (K := Kb) N (ψ₀ a)) := by
    intro N a
    rw [hSF, Polynomial.map_map, Polynomial.map_map]
    congr 1
    refine RingHom.ext fun P ↦ ?_
    change branchSub N (ψ₀ a) (P.map ι) = branchSub (C := Kb) (K := Kb) N (ψ₀ a) (P.map ψ₀)
    rw [← Differential.SuperData.branchSub_map, Polynomial.map_map]
  have hY : ∀ j, S₁.F.map (branchSub 1 (φ (α j))) =
      ∏ k, (X - Polynomial.C (HahnSeries.ofPowerSeries ℤ Kb (Y j k))) := fun j ↦ by
    rw [hφι', hbr, hY0s j,
      ← prod_cast hnS (fun k ↦ X - Polynomial.C (HahnSeries.ofPowerSeries ℤ Kb (Y0 j k)))]
  have hYc : ∀ j k, PowerSeries.constantCoeff (Y j k) = φ (ys j k) := fun j k ↦ by
    rw [hYdef, hY0c, hysdef, hφι']
    rfl
  have hα : Function.Injective α := fun j j' h ↦ by
    by_contra hne
    exact nodup_getD_ne hαnd j.2 j'.2 (Fin.val_ne_of_ne hne) 0 (ι.injective h)
  have hys : ∀ j, Function.Injective (ys j) := fun j k k' h ↦ by
    have hl := (hpt j j.2).1
    by_contra hne
    exact nodup_getD_ne hl.2 (by rw [hl.1, ← hnS]; exact k.2) (by rw [hl.1, ← hnS]; exact k'.2)
      (Fin.val_ne_of_ne hne) 0 (ι.injective h)
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
  have hMDι : MD = (toPoly (denQ G.αL)).map ι := by
    rw [hMD, ← hDqe, toPoly_mapHom, Polynomial.map_map, hιq]
  have hMDφ : MD.map φ = (G.αL.map fun a ↦ X - Polynomial.C (ψ₀ a)).prod := by
    rw [hMDι, Polynomial.map_map, toPoly_denQ, Polynomial.map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun a _ ↦ ?_
    simp [hψ₀]
  have hDb : ∀ b : Kb, b ∉ Set.range (fun j ↦ φ (α j)) → (MD.map φ).eval b ≠ 0 := by
    intro b hb h0
    rw [hMDφ, eval_list_prod, List.prod_eq_zero_iff, List.map_map, List.mem_map] at h0
    obtain ⟨a, ha, hab⟩ := h0
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C, sub_eq_zero] at hab
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    exact hb ⟨⟨i, hi⟩, by
      change φ (ι (G.αL.getD i 0)) = b
      rw [hφι', hab, List.getD_eq_getElem _ _ hi]⟩
  have hMD0 : MD ≠ 0 := by
    intro h0
    obtain ⟨b, hb⟩ : ∃ b : Kb, b ∉ Set.range (fun j ↦ φ (α j)) :=
      (Set.finite_range _).infinite_compl.nonempty
    exact hDb b hb (by rw [h0, Polynomial.map_zero, eval_zero])
  have hD0 : ∀ j : Fin G.αL.length, MD.eval (α j) = 0 := fun j ↦ by
    rw [hMDι, hαdef, eval_map, eval₂_at_apply, toPoly_denQ, eval_list_prod, List.prod_eq_zero,
      map_zero]
    rw [List.map_map, List.mem_map]
    refine ⟨G.αL.getD j 0, ?_, by simp⟩
    rw [List.getD_eq_getElem _ _ j.2]
    exact List.getElem_mem _
  have hD1v : ∀ j : Fin G.αL.length, (derivative MD).eval (α j) =
      ι (Kron.evalC (CPoly.deriv (denQ G.αL)) (G.αL.getD j 0)) := fun j ↦ by
    rw [hMDι, Polynomial.derivative_map, eval_map, eval₂_at_apply, Kron.evalC_eq, toPoly_deriv]
  have hD1 : ∀ j : Fin G.αL.length, (derivative MD).eval (α j) ≠ 0 := fun j ↦ by
    rw [hD1v]
    exact (map_ne_zero_iff _ ι.injective).mpr (hresC j j.2).1
  ------------------------------------------------------------------------------------------------
  -- the residues
  set ρ : Fin G.αL.length → Fin S₁.F.natDegree → TE.F m :=
    fun j k ↦ ι (resF (mapBQ B) G.αL j ((G.yL.getD j []).getD k 0)) with hρdef
  have hbelow : ∀ j k (i : ℤ), i < -1 → (S₁.embG (branchSub 1 (φ (α j)))
      (branchSub_injective 1 one_pos _) _ (S₁.root_of_split _ _ (hY j) k) ⟨fE, hfT⟩).coeff i = 0 :=
    fun j k ↦ (S₁.embG_simple_pole QB MD (α j) (hD0 j) (hD1 j) (Y j k)
      (S₁.root_of_split _ _ (hY j) k) hfT).1
  have hres : ∀ j k, (S₁.embG (branchSub 1 (φ (α j)))
      (branchSub_injective 1 one_pos _) _ (S₁.root_of_split _ _ (hY j) k) ⟨fE, hfT⟩).coeff (-1) =
        (sBranch (Polynomial.C η₁) (φ (α j)) 1).coeff 0 * φ (ρ j k) := by
    intro j k
    rw [(S₁.embG_simple_pole QB MD (α j) (hD0 j) (hD1 j) (Y j k)
      (S₁.root_of_split _ _ (hY j) k) hfT).2]
    have hs := sBranch_coeff (C := TE.F m) (Polynomial.C η₁) (φ (α j)) 1 one_pos
    rw [show (1 : ℤ) - ((1 : ℕ) : ℤ) = 0 by norm_num] at hs
    have hα' : (α j)′ = 0 := hι0 _
    rw [hs, Polynomial.map_C, eval_C, hK, hα', map_zero, sub_zero, Nat.cast_one, div_one, one_mul]
    have e1 : (QB.map (mapRingHom φ)) =
        Polynomial.C (Polynomial.C (φ η₁)) * (toB (mapBQ (F := F) B)).map (mapRingHom ψ₀) := by
      rw [hQB, Polynomial.map_mul, Polynomial.map_C, coe_mapRingHom, Polynomial.map_C,
        Polynomial.map_map, Polynomial.mapRingHom_comp, mapBQ, toB_mapHom, Polynomial.map_map,
        Polynomial.mapRingHom_comp, ← hιq, hψ₀]
      rfl
    rw [e1, Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C, coe_evalRingHom, eval_C,
      hYc, hD1v]
    have hφ2 : ∀ a : F, algebraMap (TE.F m) Kb (ι a) = ψ₀ a := hφι'
    simp only [hαdef, hysdef, hρdef, hφι', hφ2]
    rw [evalB_map, resF, map_div₀]
    ring
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
  have hΓ : ∀ (j : Fin G.αL.length) (k : Fin S₁.F.natDegree), (((G.ΓL.getD j []).getD k 0 : ℕ) : ℚ) = sc * Λ (ρ j k) + eS.getD j 0 :=
    fun j k ↦ by
      rw [hρdef]
      simp only
      rw [hΛ]
      exact (hresC j j.2).2 k (by rw [← hnS]; exact k.2)
  have hsumΓ : ∑ j : Fin G.αL.length, ∑ k : Fin S₁.F.natDegree, (G.ΓL.getD j []).getD k 0 =
      G.cdeg * Pc.length := by
    have e : ∀ j : ℕ, ∑ k : Fin S₁.F.natDegree, (G.ΓL.getD j []).getD k 0 =
        ∑ k ∈ Finset.range G.n, (G.ΓL.getD j []).getD k 0 := fun j ↦ by
      rw [Fin.sum_univ_eq_sum_range (fun k ↦ (G.ΓL.getD j []).getD k 0), hnS]
    simp only [e]
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ ∑ k ∈ Finset.range G.n, (G.ΓL.getD j []).getD k 0), hPcl]
    exact hGf.sum
  obtain ⟨M, hM, γ, hγ0, hγ⟩ := S₁.divGEU_of_liouville (K := Kb) (Polynomial.C η₁) hx hK hnd
    Pc.length _ hS₁F hsp.1 hsp.2.1 hsp.2.2.1 hsp.2.2.2.1 hsp.2.2.2.2 k d' w hww v fE (hCT v hv)
    hfT heq' α hα ys hys Y hY hYc ρ hbelow hres hfree Λ sc (fun j ↦ eS.getD j 0)
    (fun j k ↦ (G.ΓL.getD j []).getD k 0) G.cdeg hΓ hsumΓ
  exact not_torsion_of_cert_map (Kb := Kb) S₁ ι G hSF hG hpq Rp φp hRp Cp hCp Rq φq hRq Cq hCq
    Pb Lm htest M hM ⟨γ, hγ0, hγ⟩

end MTower

end Curves.MT
