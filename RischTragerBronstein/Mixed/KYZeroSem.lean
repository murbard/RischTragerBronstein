import RischTragerBronstein.Mixed.KYCol

/-!
# Radicals with poles over an exponential: the fibre over `t = 0`, over `Kₘ ⊗ N`

As in `KRTors`/`KRNorm`, with the number field `N` in place of `ℚ(ζ)` and no norm: the twist
`ỹⁿ = Â = (zⁿ/κ) A` over `Kₘ ⊗ N` has the points `(0, ζᵏ)`, images of the points
`(0, ζ'ᵏ/μ₀)` of `yⁿ = A` (`ky_zfacts`); a negative torsion answer for `Ψ` excludes principal
multiples (`ky_hnt`); the witness of `N Ψ` gives `W₀` with divisor `N Ψ` away from `∞`
(`ky_psi_wit`); positive answers for the single points give the witnesses of `kill_tors`
(`ky_zero_wits`).
-/

open Polynomial Differential IntermediateField CPoly Ramanujan

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable [Fact (Irreducible (toPoly (fKc Fc)))]

lemma kyFA_map (m : ℕ) (hm : T.Tr m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0) (Ah : GPoly (LC m)) :
    (toPoly (kyFA Fc m M Ah)).map (T.psiNFM m hm M ρ hρ) = GPoly.toPoly (T.MP m hm) Ah := by
  rw [kyFA, toPoly_trim, ← toPoly_map', List.map_map, List.map_map, gtoPoly_eq]
  congr 1
  refine List.map_congr_left fun a _ ↦ ?_
  simp only [Function.comp_apply, T.psiNFM_embM, T.psiF_trC m hm]

section ZFacts

variable (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
  (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
  (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
  (n : ℕ) (hn : 0 < n) (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
  (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))] (ρ : T.F m)
  (hρ : aeval ρ (toPoly M) = 0) (zN : CPoly ℚ) (hζ : IsPrimitiveRoot (aeval ρ (toPoly zN)) n)
  (θ : L) (hθ : θ ^ n = T.evP m A)
  (z : LC m) (κ : ℚ) (hZ0 : (T.MP m hTr.of_succ).sem z ≠ 0)
  (hzκ : (T.MP m hTr.of_succ).sem z ^ n * (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero) =
    (κ : T.F m)) (hκ0 : κ ≠ 0) (sF : T.F m) (hsF : sF ^ n = (κ : T.F m))

include hsq hcopA hζ hZ0 hzκ hκ0 hsF in
/-- **The data of the twist over `Kₘ ⊗ N`.** -/
theorem ky_zfacts :
    let S := T.krS m hTr A hsq hdegA n hn θ hθ
    let hTm : T.Tr m := hTr.of_succ
    let μ₀ : T.F m := (T.MP m hTm).sem z / sF
    let ψ := T.psiNFM m hTm M ρ hρ
    let fK := kyFA Fc m M (krAh Fc ks m n A z κ)
    let ζN : NFM Fc m M := ofQ Fc m M zN
    let βS : Fin n → T.F m := fun k ↦ aeval ρ (toPoly zN) ^ (k : ℕ) / μ₀
    μ₀ ≠ 0 ∧ Polynomial.C (μ₀ ^ S.n) * S.p = (toPoly fK).map ψ ∧
      (toPoly fK).natDegree = fK.length - 1 ∧ Squarefree (toPoly fK) ∧
      Nat.Coprime n (fK.length - 1) ∧
      (∀ k : Fin n, ((S.n : ℕ) : NFM Fc m M) * (ζN ^ (k : ℕ)) ^ (S.n - 1) ≠ 0 ∧
        (ζN ^ (k : ℕ)) ^ S.n = (toPoly fK).eval 0) ∧
      (∀ k : Fin n, ζN ^ (k : ℕ) ≠ 0 ∧ (ζN ^ (k : ℕ)) ^ n = (toPoly fK).eval 0) ∧
      Function.Injective (fun k : Fin n ↦ ((0 : NFM Fc m M), ζN ^ (k : ℕ))) ∧
      (∀ k, βS k ≠ 0 ∧ βS k ^ S.n = S.p.eval 0) ∧
      Function.Injective (fun k : Fin n ↦ ((0 : T.F m), βS k)) ∧
      (∀ k : Fin n, ψ (ζN ^ (k : ℕ)) = μ₀ * βS k) := by
  intro S hTm μ₀ ψ fK ζN βS
  have hsF0 : sF ≠ 0 := fun h ↦ by
    rw [h, zero_pow hn.ne'] at hsF; exact hκ0 (by exact_mod_cast hsF.symm)
  have hμ₀ : μ₀ ≠ 0 := div_ne_zero hZ0 hsF0
  have hSn : S.n = n := rfl
  have hSp : S.p = GPoly.toPoly (T.MP m hTm) A := rfl
  have ha0 : S.p.eval 0 = (T.MP m hTm).sem (A.getD 0 (MO Fc ks m).zero) := by
    rw [hSp, T.toPoly_eval_zero m hTm]
  have hμn : μ₀ ^ n = (T.MP m hTm).sem (powC (MO Fc ks m) z n) * ((κ⁻¹ : ℚ) : T.F m) := by
    rw [sem_powC, div_pow, hsF]; push_cast; ring
  have hpf : Polynomial.C (μ₀ ^ S.n) * S.p = (toPoly fK).map ψ := by
    rw [hSn, hμn, hSp, T.kyFA_map m hTm M ρ hρ]
    have e : krAh Fc ks m n A z κ = GPoly.smul (MO Fc ks m)
        ((MO Fc ks m).mul (powC (MO Fc ks m) z n) (mcst Fc ks m κ⁻¹)) A := rfl
    rw [e, GPoly.toPoly_smul, (T.MP m hTm).sem_mul, T.sem_mcst]
  have hp0 : Polynomial.C (μ₀ ^ S.n) * S.p ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr (pow_ne_zero _ hμ₀)) hsq.ne_zero
  have hsqp : Squarefree (Polynomial.C (μ₀ ^ S.n) * S.p) := fun x hx ↦ hsq x
    ((IsUnit.dvd_mul_left (Polynomial.isUnit_C.mpr (pow_ne_zero _ hμ₀).isUnit)).mp hx)
  have hcopp : Nat.Coprime n (Polynomial.C (μ₀ ^ S.n) * S.p).natDegree := by
    rw [natDegree_C_mul (pow_ne_zero _ hμ₀)]; exact hcopA
  obtain ⟨hd, hsqK, hcop2⟩ := fK_factsN ψ fK (CPoly.trim_trim _) _ hpf hp0 hsqp n hcopp
  have hψz : ∀ k : ℕ, ψ (ζN ^ k) = aeval ρ (toPoly zN) ^ k := fun k ↦ by
    rw [map_pow, T.psiNFM_ofQ]
  have hev0 : (toPoly fK).eval 0 = 1 := by
    apply ψ.injective
    rw [map_one, ← eval₂_at_apply, map_zero, ← eval_map, ← hpf, eval_mul, eval_C, ha0, hSn, hμn,
      sem_powC]
    have hκF : (κ : T.F m) ≠ 0 := by exact_mod_cast hκ0
    push_cast
    field_simp
    rw [← hzκ]
  have hzn : ∀ k : ℕ, (ζN ^ k) ^ n = (toPoly fK).eval 0 := fun k ↦ by
    rw [hev0]
    apply ψ.injective
    rw [map_pow, hψz, map_one, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hz0 : ∀ k : ℕ, ζN ^ k ≠ 0 := fun k h ↦ by
    have := congrArg ψ h
    rw [hψz, map_zero] at this
    exact pow_ne_zero _ (hζ.ne_zero (by omega)) this
  refine ⟨hμ₀, hpf, hd, hsqK, hcop2, fun k ↦ ⟨?_, hzn k⟩, fun k ↦ ⟨hz0 k, hzn k⟩, ?_, fun k ↦ ⟨?_, ?_⟩,
    ?_, fun k ↦ ?_⟩
  · refine mul_ne_zero ?_ (pow_ne_zero _ (hz0 k))
    exact_mod_cast hn.ne'
  · intro k l h
    have := congrArg (fun x ↦ ψ x.2) h
    simp only [hψz] at this
    exact Fin.ext (hζ.pow_inj k.2 l.2 this)
  · exact div_ne_zero (pow_ne_zero _ (hζ.ne_zero (by omega))) hμ₀
  · rw [ha0, hSn, div_pow, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, hμn, sem_powC]
    have hκF : (κ : T.F m) ≠ 0 := by exact_mod_cast hκ0
    have hZn : (T.MP m hTm).sem z ^ n ≠ 0 := pow_ne_zero _ hZ0
    push_cast
    field_simp
    rw [← hzκ]
  · intro k l h
    have := congrArg Prod.snd h
    simp only at this
    have h2 : aeval ρ (toPoly zN) ^ (k : ℕ) / μ₀ = aeval ρ (toPoly zN) ^ (l : ℕ) / μ₀ := this
    rw [div_left_inj' hμ₀] at h2
    exact Fin.ext (hζ.pow_inj k.2 l.2 h2)
  · rw [hψz]; simp only [βS]; field_simp

include hsq hcopA hζ hZ0 hzκ hκ0 hsF hρ in
/-- **A negative torsion answer**: no element without zeros or poles over `x ≠ 0` has divisor
`M Ψ`, `Ψ = ∑ c_n(k) P_k`, `M > 0`. -/
theorem ky_hnt (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)}
    (ht : kyTorsPsiC Fc ks m n M A zN z κ cpf ps bound rs = some none) :
    let S := T.krS m hTr A hsq hdegA n hn θ hθ
    let hTm : T.Tr m := hTr.of_succ
    let μ₀ : T.F m := (T.MP m hTm).sem z / sF
    ∀ u : (T.F m)⟮S.x⟯⟮S.y⟯, u ≠ 0 → S.Supp (K := AlgebraicClosure (T.F m)) u → ∀ Mm : ℕ, 0 < Mm →
      (∀ k < S.n, S.rv (aeval ρ (toPoly zN)) (algebraMap (T.F m) (AlgebraicClosure (T.F m)) μ₀⁻¹) u k =
        Mm * ramC S.n k) → False := by
  intro S hTm μ₀ w hw0 hsw Mm hM hrw
  obtain ⟨hμ₀, hpf, hd, hsqK, hcop2, hΓK, hvK, hinj, hβS, hP, hβ'⟩ :=
    T.ky_zfacts m hTr A hsq hdegA n hn hcopA M ρ hρ zN hζ θ hθ z κ hZ0 hzκ hκ0 sF hsF
  set K := AlgebraicClosure (T.F m)
  set βS : Fin n → T.F m := fun k ↦ aeval ρ (toPoly zN) ^ (k : ℕ) / μ₀ with hβSdef
  have hspec := torsOracleC_specY (redAtNFM Fc m M rs) cpf
    (fun p _ R h ↦ redAtNFM_valid Fc m M rs p R h) ps bound hsqK hcop2
  have hnot := (hspec n (fun _ ↦ (0 : NFM Fc m M)) (fun k ↦ ofQ Fc m M zN ^ (k : ℕ)) (ramMult n)
    hvK hinj).2 ht
  have hcopS : Nat.Coprime S.n S.p.natDegree := hcopA
  have hnp := S.pts_not_principal (K := K) hcopS (fun _ ↦ (0 : T.F m)) βS hP hβS (ramMult n)
    (T.psiNFM m hTm M ρ hρ) (kyFA Fc m M (krAh Fc ks m n A z κ)) μ₀ hμ₀ hpf hd (fun _ ↦ 0)
    (fun k ↦ ofQ Fc m M zN ^ (k : ℕ)) (fun _ ↦ map_zero _) hβ' hΓK hnot
  apply hnp Mm hM
  -- `w xᴹᴹ⁰` has divisor `M Γ`
  set M0 : ℤ := ramM0 n
  have hM0 : 0 ≤ M0 := by
    simp only [M0, ramM0]
    exact List.sum_nonneg fun x hx ↦ by obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _
  have hxz : S.xE ^ ((Mm : ℤ) * M0) ≠ 0 := zpow_ne_zero _ S.xE_ne
  set β₀ : K := algebraMap (T.F m) K μ₀⁻¹ with hβ₀def
  have hβ₀ : β₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap (T.F m) K).injective).mpr (inv_ne_zero hμ₀)
  have hv0 : β₀ ^ S.n = (S.p.map (algebraMap (T.F m) K)).eval 0 := by
    have h0 := (hβS ⟨0, hn⟩).2
    simp only [βS, pow_zero, one_div] at h0
    rw [hβ₀def, ← map_pow, h0, eval_map, ← map_zero (algebraMap (T.F m) K), eval₂_at_apply]
  have hbk : ∀ k : Fin n, Differential.SuperData.bk (aeval ρ (toPoly zN)) β₀ (k : ℕ) = algebraMap (T.F m) K (βS k) := fun k ↦ by
    simp only [Differential.SuperData.bk, βS, div_eq_mul_inv]
    rw [map_mul, map_pow, hβ₀def]
  have hgam : ∀ k : Fin n, Differential.SuperData.gammaPts (K := K) (fun _ ↦ (0 : T.F m)) βS (ramMult n)
      (0, algebraMap (T.F m) K (βS k)) = ramMult n k := fun k ↦ by
    rw [Differential.SuperData.gammaPts, Finset.sum_eq_single k]
    · simp
    · intro l _ hl
      rw [if_neg]
      intro h
      apply hl
      apply hP
      simp only [Prod.ext_iff, map_zero, true_and] at h
      simp [(algebraMap (T.F m) K).injective h.symm]
    · simp
  have hord : ∀ α β : K, β ^ S.n = (S.p.map (algebraMap (T.F m) K)).eval α →
      S.ordAt K (w * S.xE ^ ((Mm : ℤ) * M0)) α β =
        Mm * Differential.SuperData.gammaPts (K := K) (fun _ ↦ (0 : T.F m)) βS (ramMult n) (α, β) := by
    intro α β hv
    rw [S.ordAt_mul hv hw0 hxz, S.ordAt_zpow hv, S.ordAt_xE α β hv]
    by_cases hα : α = 0
    · subst hα
      obtain ⟨k, hk, rfl⟩ := S.over_zero_k (aeval ρ (toPoly zN)) hζ β₀ hβ₀ hv0 β hv
      have hb0 := S.bk_ne (aeval ρ (toPoly zN)) hζ β₀ hβ₀ k
      rw [if_pos rfl, if_neg hb0, hbk ⟨k, hk⟩, hgam ⟨k, hk⟩]
      have hr := hrw k hk
      simp only [Differential.SuperData.rv, hbk ⟨k, hk⟩] at hr
      rw [hr]
      have := ramMult_eq n ⟨k, hk⟩
      simp only at this
      rw [this, mul_add, mul_one]
      rfl
    · rw [hsw α β hv hα, if_neg hα, Differential.SuperData.gammaPts, Finset.sum_eq_zero]
      · simp
      intro k _
      rw [if_neg]
      intro h
      exact hα (by simpa using (Prod.ext_iff.mp h).1)
  refine ⟨w * S.xE ^ ((Mm : ℤ) * M0), mul_ne_zero hw0 hxz, fun α β hv ↦ ?_, fun Q hQ ↦ hord Q.1 Q.2 hQ⟩
  rw [hord α β hv]
  positivity


include hsq hcopA hζ hZ0 hzκ hκ0 hsF hρ in
/-- **The witness of `N Ψ`**, read on `yⁿ = A` and corrected by `x^{−N M₀}`: no zeros or poles over
`x ≠ 0`, orders `N c_n(k)` at `(0, ζ'ᵏ/μ₀)`. -/
theorem ky_psi_wit (N : ℕ) (W0b : BPoly (NFM Fc m M))
    (hW : kyWitPsi Fc ks m n M A zN z κ N = some W0b) :
    let S := T.krS m hTr A hsq hdegA n hn θ hθ
    let hTm : T.Tr m := hTr.of_succ
    let μ₀ : T.F m := (T.MP m hTm).sem z / sF
    let ψ := T.psiNFM m hTm M ρ hρ
    let W₀ := S.elemW (((toB W0b).map (mapRingHom ψ)).comp (Polynomial.C (Polynomial.C μ₀) * X)) *
      S.xE ^ (-((N : ℤ) * ramM0 n))
    W₀ ≠ 0 ∧ S.Supp (K := AlgebraicClosure (T.F m)) W₀ ∧
      ∀ i, S.rv (aeval ρ (toPoly zN)) (algebraMap (T.F m) (AlgebraicClosure (T.F m)) μ₀⁻¹) W₀ i =
        N * ramC n i := by
  intro S hTm μ₀ ψ W₀
  classical
  set K := AlgebraicClosure (T.F m)
  obtain ⟨hμ₀, hpf, hd, hsqK, hcop2, hΓK, hvK, hinj, hβS, hP, hβ'⟩ :=
    T.ky_zfacts m hTr A hsq hdegA n hn hcopA M ρ hρ zN hζ θ hθ z κ hZ0 hzκ hκ0 sF hsF
  set ζ' := aeval ρ (toPoly zN) with hζ'
  set βS : Fin n → T.F m := fun k ↦ ζ' ^ (k : ℕ) / μ₀ with hβSdef
  set β₀ : K := algebraMap (T.F m) K μ₀⁻¹ with hβ₀def
  have hβ0 : β₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap (T.F m) K).injective).mpr (inv_ne_zero hμ₀)
  have hv0 : β₀ ^ S.n = (S.p.map (algebraMap (T.F m) K)).eval 0 := by
    have h0 := (hβS ⟨0, hn⟩).2
    simp only [βS, pow_zero, one_div] at h0
    rw [hβ₀def, ← map_pow, h0, eval_map, ← map_zero (algebraMap (T.F m) K), eval₂_at_apply]
  have hcopS : Nat.Coprime S.n S.p.natDegree := hcopA
  obtain ⟨hWt0, hWtord⟩ := S.pts_witness (K := K) hcopS (fun _ ↦ (0 : T.F m)) βS hP hβS (ramMult n)
    ψ (kyFA Fc m M (krAh Fc ks m n A z κ)) μ₀ hμ₀ hpf hd (fun _ ↦ 0)
    (fun k ↦ ofQ Fc m M zN ^ (k : ℕ)) (fun _ ↦ map_zero _) hβ' hΓK N W0b hW
  set Wt := S.elemW (((toB W0b).map (mapRingHom ψ)).comp (Polynomial.C (Polynomial.C μ₀) * X))
    with hWt
  set Mx : ℤ := (N : ℤ) * ramM0 n with hMx
  have hxz : S.xE ^ (-Mx) ≠ 0 := zpow_ne_zero _ S.xE_ne
  have hbk : ∀ k : Fin n, Differential.SuperData.bk ζ' β₀ (k : ℕ) = algebraMap (T.F m) K (βS k) :=
    fun k ↦ by
      simp only [Differential.SuperData.bk, βS, div_eq_mul_inv]
      rw [map_mul, map_pow, hβ₀def]
  have hgam : ∀ k : Fin n, Differential.SuperData.gammaPts (K := K) (fun _ ↦ (0 : T.F m)) βS
      (ramMult n) (0, algebraMap (T.F m) K (βS k)) = ramMult n k := fun k ↦ by
    rw [Differential.SuperData.gammaPts, Finset.sum_eq_single k]
    · simp
    · intro l _ hl
      rw [if_neg]
      intro h
      apply hl
      apply hP
      simp only [Prod.ext_iff, map_zero, true_and] at h
      simp [(algebraMap (T.F m) K).injective h.symm]
    · simp
  refine ⟨mul_ne_zero hWt0 hxz, fun α β hv hα ↦ ?_, fun i ↦ ?_⟩
  · show S.ordAt K (Wt * S.xE ^ (-Mx)) α β = 0
    rw [S.ordAt_mul hv hWt0 hxz, S.ordAt_zpow hv, S.ordAt_xE α β hv, if_neg hα, hWtord α β hv,
      Differential.SuperData.gammaPts, Finset.sum_eq_zero]
    · simp
    intro k _
    rw [if_neg]
    intro h
    exact hα (by simpa using (Prod.ext_iff.mp h).1)
  · rw [← S.rv_mod ζ' hζ β₀ _ i]
    have hi : i % n < n := Nat.mod_lt _ hn
    have hv := S.bk_v ζ' hζ β₀ hv0 (i % n)
    show S.ordAt K (Wt * S.xE ^ (-Mx)) 0 (Differential.SuperData.bk ζ' β₀ (i % n)) = _
    rw [S.ordAt_mul hv hWt0 hxz, S.ordAt_zpow hv, S.ordAt_xE _ _ hv,
      if_pos rfl, if_neg (S.bk_ne ζ' hζ β₀ hβ0 _), hWtord _ _ hv, hbk ⟨i % n, hi⟩, hgam ⟨i % n, hi⟩]
    have := ramMult_eq n ⟨i % n, hi⟩
    simp only at this
    have hmod : ramC n (i % n) = ramC n i := by
      rw [← ramC_gcd, Nat.gcd_comm, ← Nat.gcd_rec, ramC_gcd]
    rw [this, hmod]
    push_cast
    ring

include hsq hcopA hζ hZ0 hzκ hκ0 hsF hρ in
/-- **Every point over `x = 0` torsion**: witnesses `Z_k` of `N_k (0, ζ'ᵏ/μ₀)`. -/
theorem ky_zero_wits (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)}
    (hzt : kyZeroTorsC Fc ks m n M A zN z κ cpf ps bound rs = true) :
    let S := T.krS m hTr A hsq hdegA n hn θ hθ
    let hTm : T.Tr m := hTr.of_succ
    let μ₀ : T.F m := (T.MP m hTm).sem z / sF
    ∀ k < n, ∃ Z : (T.F m)⟮S.x⟯⟮S.y⟯, Z ≠ 0 ∧ ∃ Nk : ℕ, 0 < Nk ∧
      (∀ α β' : AlgebraicClosure (T.F m), β' ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval α →
        α ≠ 0 → S.ordAt (AlgebraicClosure (T.F m)) Z α β' = 0) ∧
      ∀ i < n, S.ordAt (AlgebraicClosure (T.F m)) Z 0
        (Differential.SuperData.bk (aeval ρ (toPoly zN))
          (algebraMap (T.F m) (AlgebraicClosure (T.F m)) μ₀⁻¹) i) = if i = k then (Nk : ℤ) else 0 := by
  intro S hTm μ₀ k hk
  classical
  set K := AlgebraicClosure (T.F m)
  obtain ⟨hμ₀, hpf, hd, hsqK, hcop2, hΓK, hvK, hinj, hβS, hP, hβ'⟩ :=
    T.ky_zfacts m hTr A hsq hdegA n hn hcopA M ρ hρ zN hζ θ hθ z κ hZ0 hzκ hκ0 sF hsF
  set ζ' := aeval ρ (toPoly zN) with hζ'
  set βS : Fin n → T.F m := fun k ↦ ζ' ^ (k : ℕ) / μ₀ with hβSdef
  -- the oracle answer
  have hk' := List.all_eq_true.mp hzt k (List.mem_range.mpr hk)
  obtain ⟨N, hN⟩ : ∃ N, torsOracleC (redAtNFM Fc m M rs) (cpf (kyFA Fc m M (krAh Fc ks m n A z κ))) ps bound
      (kyFA Fc m M (krAh Fc ks m n A z κ)) n
      (gammaL ![(0 : NFM Fc m M)] ![ofQ Fc m M zN ^ k] ![1] 1) = some (some N) := by
    revert hk'
    split
    · rename_i N hN; intro _; exact ⟨N, hN⟩
    · intro h; exact absurd h (by simp)
  have hspec := torsOracleC_specY (redAtNFM Fc m M rs) cpf
    (fun p _ R h ↦ redAtNFM_valid Fc m M rs p R h) ps bound hsqK hcop2
  have hΓ1 : ∀ q : Fin 1, (![ofQ Fc m M zN ^ k] q) ≠ 0 ∧ (![ofQ Fc m M zN ^ k] q) ^ n =
      (toPoly (kyFA Fc m M (krAh Fc ks m n A z κ))).eval (![(0 : NFM Fc m M)] q) := fun q ↦ by
    fin_cases q; exact hvK ⟨k, hk⟩
  obtain ⟨hN1, hPr⟩ := (hspec 1 ![(0 : NFM Fc m M)] ![ofQ Fc m M zN ^ k] ![1] hΓ1
    (fun a b _ ↦ Subsingleton.elim a b)).1 N hN
  have hΓK1 : ∀ q : Fin 1, ((S.n : ℕ) : NFM Fc m M) * (![ofQ Fc m M zN ^ k] q) ^ (S.n - 1) ≠ 0 ∧
      (![ofQ Fc m M zN ^ k] q) ^ S.n =
        (toPoly (kyFA Fc m M (krAh Fc ks m n A z κ))).eval (![(0 : NFM Fc m M)] q) := fun q ↦ by
    fin_cases q; exact hΓK ⟨k, hk⟩
  obtain ⟨Wb, hWb⟩ := Option.ne_none_iff_exists'.mp (witW_ne_none _ n hn _ _ _ _ N hΓK1 hPr)
  have hcopS : Nat.Coprime S.n S.p.natDegree := hcopA
  have hβ1 : ∀ q : Fin 1, (![βS ⟨k, hk⟩] q) ≠ 0 ∧ (![βS ⟨k, hk⟩] q) ^ S.n = S.p.eval (![(0 : T.F m)] q) :=
    fun q ↦ by fin_cases q; exact hβS ⟨k, hk⟩
  obtain ⟨hZ0', hZord⟩ := S.pts_witness (K := K) hcopS ![(0 : T.F m)] ![βS ⟨k, hk⟩]
    (fun a b _ ↦ Subsingleton.elim a b) hβ1 ![1] (T.psiNFM m hTm M ρ hρ)
    (kyFA Fc m M (krAh Fc ks m n A z κ)) μ₀ hμ₀ hpf hd ![(0 : NFM Fc m M)]
    ![ofQ Fc m M zN ^ k] (fun q ↦ by fin_cases q; exact map_zero _)
    (fun q ↦ by fin_cases q; exact hβ' ⟨k, hk⟩) hΓK1 N Wb hWb
  refine ⟨_, hZ0', N, hN1, fun α β' hv hα ↦ ?_, fun i hi ↦ ?_⟩
  · rw [hZord α β' hv, Differential.SuperData.gammaPts, Finset.sum_eq_zero]
    · simp
    intro q _
    rw [if_neg]
    intro h
    exact hα (by fin_cases q; simpa using (Prod.ext_iff.mp h).1)
  · have hbk : Differential.SuperData.bk ζ' (algebraMap (T.F m) K μ₀⁻¹) i =
        algebraMap (T.F m) K (βS ⟨i, hi⟩) := by
      simp only [Differential.SuperData.bk, βS, div_eq_mul_inv]
      rw [map_mul, map_pow]
    have hv : (Differential.SuperData.bk ζ' (algebraMap (T.F m) K μ₀⁻¹) i) ^ S.n =
        (S.p.map (algebraMap (T.F m) K)).eval 0 := by
      rw [hbk, ← map_pow, (hβS ⟨i, hi⟩).2, eval_map, ← map_zero (algebraMap (T.F m) K),
        eval₂_at_apply]
    rw [hZord _ _ hv, Differential.SuperData.gammaPts, Fin.sum_univ_one, hbk]
    by_cases hik : i = k
    · subst hik; simp
    · rw [if_neg, if_neg hik]
      · simp
      intro h
      apply hik
      have h2 := (algebraMap (T.F m) K).injective (Prod.ext_iff.mp h).2
      simp only [Matrix.cons_val_fin_one, βS] at h2
      rw [div_left_inj' hμ₀] at h2
      exact hζ.pow_inj hi hk h2

end ZFacts

end MTower

end Curves.MT
