import RischTragerBronstein.Mixed.KRTwist

/-!
# Radicals over an exponential level: torsion answers read on `yⁿ = A`

In a realization whose `Fₘ` contains a primitive `n`-th root `ω` and `s = ⁿ√κ`, with
`μ₀ = z/s`, the points `P_k = (0, ωᵏ/μ₀)` of `yⁿ = A` are the images of the points `(0, ζᵏ)` of the
twist over `Kₘ(ζ)` (`kr_facts`). A negative torsion answer means that no multiple of
`Ψ = ∑ c_n(k) P_k` is principal (`kr_hnt`, the hypothesis of `four_dl_nontors`).
-/

open Polynomial Differential IntermediateField CPoly Ramanujan

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

lemma ramM0_ge (n k : ℕ) (hk : k < n) : |ramC n k| ≤ ramM0 n := by
  rw [ramM0]
  have : |ramC n k| ∈ (List.range n).map fun k ↦ |ramC n k| :=
    List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  exact List.single_le_sum (fun x hx ↦ by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _) _ this

lemma ramMult_eq (n : ℕ) (k : Fin n) : (ramMult n k : ℤ) = ramC n k + ramM0 n := by
  rw [ramMult, Int.toNat_of_nonneg]
  have := ramM0_ge n k k.2
  have := neg_abs_le (ramC n k)
  omega

namespace MTower

variable (T : MTower Fc ks Cc L)

section Facts

variable [Fact (Irreducible (toPoly (fKc Fc)))]
variable (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
  (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
  (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
  (n : ℕ) (hn : 0 < n) (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
  [Fact (Irreducible (toPoly (cycK Fc m n)))]
  (ω : T.F m) (hω : IsPrimitiveRoot ω n) (θ : L) (hθ : θ ^ n = T.evP m A)
  (z : LC m) (κ : ℚ) (hZ0 : (T.MP m hTr.of_succ).sem z ≠ 0)
  (hzκ : (T.MP m hTr.of_succ).sem z ^ n * (T.MP m hTr.of_succ).sem (A.getD 0 (MO Fc ks m).zero) =
    (κ : T.F m)) (hκ0 : κ ≠ 0) (sF : T.F m) (hsF : sF ^ n = (κ : T.F m))

include hsq hcopA hω hZ0 hzκ hκ0 hsF in
/-- **The data of the twist.** -/
theorem kr_facts :
    let S := T.krS m hTr A hsq hdegA n hn θ hθ
    let hTm : T.Tr m := hTr.of_succ
    let μ₀ : T.F m := (T.MP m hTm).sem z / sF
    let ψ := T.psiNF m hTm n hn ω hω
    let fK := krFK Fc ks m n A z κ
    let βS : Fin n → T.F m := fun k ↦ ω ^ (k : ℕ) / μ₀
    μ₀ ≠ 0 ∧ Polynomial.C (μ₀ ^ S.n) * S.p = (toPoly fK).map ψ ∧
      (toPoly fK).natDegree = fK.length - 1 ∧ Squarefree (toPoly fK) ∧
      Nat.Coprime n (fK.length - 1) ∧
      (∀ k : Fin n, ((S.n : ℕ) : NFz Fc m n) * (zetaN Fc m n ^ (k : ℕ)) ^ (S.n - 1) ≠ 0 ∧
        (zetaN Fc m n ^ (k : ℕ)) ^ S.n = (toPoly fK).eval 0) ∧
      (∀ k : Fin n, zetaN Fc m n ^ (k : ℕ) ≠ 0 ∧ (zetaN Fc m n ^ (k : ℕ)) ^ n = (toPoly fK).eval 0) ∧
      Function.Injective (fun k : Fin n ↦ ((0 : NFz Fc m n), zetaN Fc m n ^ (k : ℕ))) ∧
      (∀ k, βS k ≠ 0 ∧ βS k ^ S.n = S.p.eval 0) ∧
      Function.Injective (fun k : Fin n ↦ ((0 : T.F m), βS k)) ∧
      (∀ k : Fin n, ψ (zetaN Fc m n ^ (k : ℕ)) = μ₀ * βS k) := by
  intro S hTm μ₀ ψ fK βS
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
    rw [hSn, hμn, hSp]; exact T.kr_hpf m hTm n hn ω hω A z κ
  have hp0 : Polynomial.C (μ₀ ^ S.n) * S.p ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr (pow_ne_zero _ hμ₀)) hsq.ne_zero
  have hsqp : Squarefree (Polynomial.C (μ₀ ^ S.n) * S.p) := fun x hx ↦ hsq x
    ((IsUnit.dvd_mul_left (Polynomial.isUnit_C.mpr (pow_ne_zero _ hμ₀).isUnit)).mp hx)
  have hcopp : Nat.Coprime n (Polynomial.C (μ₀ ^ S.n) * S.p).natDegree := by
    rw [natDegree_C_mul (pow_ne_zero _ hμ₀)]; exact hcopA
  obtain ⟨hd, hsqK, hcop2⟩ := fK_factsN ψ fK (CPoly.trim_trim _) _ hpf hp0 hsqp n hcopp
  have hψ : ∀ a, ψ a = 0 → a = 0 := fun a h ↦ (map_eq_zero_iff ψ ψ.injective).mp h
  have hψz : ∀ k : ℕ, ψ (zetaN Fc m n ^ k) = ω ^ k := fun k ↦ by
    rw [map_pow, T.psiNF_zeta]
  have hev0 : (toPoly fK).eval 0 = 1 := by
    apply ψ.injective
    rw [map_one, ← eval₂_at_apply, map_zero, ← eval_map, ← hpf, eval_mul, eval_C, ha0, hSn, hμn,
      sem_powC]
    have hκF : (κ : T.F m) ≠ 0 := by exact_mod_cast hκ0
    push_cast
    field_simp
    rw [← hzκ]
  have hzn : ∀ k : ℕ, (zetaN Fc m n ^ k) ^ n = (toPoly fK).eval 0 := fun k ↦ by
    rw [hev0]
    apply ψ.injective
    rw [map_pow, hψz, map_one, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hz0 : ∀ k : ℕ, zetaN Fc m n ^ k ≠ 0 := fun k h ↦ by
    have := congrArg ψ h
    rw [hψz, map_zero] at this
    exact pow_ne_zero _ (hω.ne_zero (by omega)) this
  refine ⟨hμ₀, hpf, hd, hsqK, hcop2, fun k ↦ ⟨?_, hzn k⟩, fun k ↦ ⟨hz0 k, hzn k⟩, ?_, fun k ↦ ⟨?_, ?_⟩,
    ?_, fun k ↦ ?_⟩
  · refine mul_ne_zero ?_ (pow_ne_zero _ (hz0 k))
    exact_mod_cast hn.ne'
  · intro k l h
    have := congrArg (fun x ↦ ψ x.2) h
    simp only [hψz] at this
    exact Fin.ext (hω.pow_inj k.2 l.2 this)
  · exact div_ne_zero (pow_ne_zero _ (hω.ne_zero (by omega))) hμ₀
  · rw [ha0, hSn, div_pow, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, hμn, sem_powC]
    have hκF : (κ : T.F m) ≠ 0 := by exact_mod_cast hκ0
    have hZn : (T.MP m hTm).sem z ^ n ≠ 0 := pow_ne_zero _ hZ0
    push_cast
    field_simp
    rw [← hzκ]
  · intro k l h
    have := congrArg Prod.snd h
    simp only at this
    have h2 : ω ^ (k : ℕ) / μ₀ = ω ^ (l : ℕ) / μ₀ := this
    rw [div_left_inj' hμ₀] at h2
    exact Fin.ext (hω.pow_inj k.2 l.2 h2)
  · rw [hψz]; simp only [βS]; field_simp

include hsq hcopA hω hZ0 hzκ hκ0 hsF in
/-- **A negative torsion answer**: no element without zeros or poles over `x ≠ 0` has divisor
`M Ψ`, `Ψ = ∑ c_n(k) P_k`, `M > 0`. -/
theorem kr_hnt (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (NFz Fc m n) → CertProv (NFz Fc m n))
    (ht : krTorsC Fc ks m n A z κ cpf ps bound rs = some none) :
    let S := T.krS m hTr A hsq hdegA n hn θ hθ
    let hTm : T.Tr m := hTr.of_succ
    let μ₀ : T.F m := (T.MP m hTm).sem z / sF
    ∀ u : (T.F m)⟮S.x⟯⟮S.y⟯, u ≠ 0 → S.Supp (K := AlgebraicClosure (T.F m)) u → ∀ M : ℕ, 0 < M →
      (∀ k < S.n, S.rv ω (algebraMap (T.F m) (AlgebraicClosure (T.F m)) μ₀⁻¹) u k =
        M * ramC S.n k) → False := by
  intro S hTm μ₀ w hw0 hsw M hM hrw
  obtain ⟨hμ₀, hpf, hd, hsqK, hcop2, hΓK, hvK, hinj, hβS, hP, hβ'⟩ :=
    T.kr_facts m hTr A hsq hdegA n hn hcopA ω hω θ hθ z κ hZ0 hzκ hκ0 sF hsF
  set K := AlgebraicClosure (T.F m)
  set βS : Fin n → T.F m := fun k ↦ ω ^ (k : ℕ) / μ₀ with hβSdef
  have hspec := torsOracleC_spec (redAtNF Fc m n rs) (cpf (krFK Fc ks m n A z κ))
    (fun p _ R h ↦ MTower.redAtNF_valid (Fc := Fc) m n rs p R h) ps bound hsqK hcop2
  have hnot := (hspec n (fun _ ↦ (0 : NFz Fc m n)) (fun k ↦ zetaN Fc m n ^ (k : ℕ)) (ramMult n)
    hvK hinj).2 ht
  have hcopS : Nat.Coprime S.n S.p.natDegree := hcopA
  have hnp := S.pts_not_principal (K := K) hcopS (fun _ ↦ (0 : T.F m)) βS hP hβS (ramMult n)
    (T.psiNF m hTm n hn ω hω) (krFK Fc ks m n A z κ) μ₀ hμ₀ hpf hd (fun _ ↦ 0)
    (fun k ↦ zetaN Fc m n ^ (k : ℕ)) (fun _ ↦ map_zero _) hβ' hΓK hnot
  apply hnp M hM
  -- `w xᴹᴹ⁰` has divisor `M Γ`
  set M0 : ℤ := ramM0 n
  have hM0 : 0 ≤ M0 := by
    simp only [M0, ramM0]
    exact List.sum_nonneg fun x hx ↦ by obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _
  have hxz : S.xE ^ ((M : ℤ) * M0) ≠ 0 := zpow_ne_zero _ S.xE_ne
  set β₀ : K := algebraMap (T.F m) K μ₀⁻¹ with hβ₀def
  have hβ₀ : β₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap (T.F m) K).injective).mpr (inv_ne_zero hμ₀)
  have hv0 : β₀ ^ S.n = (S.p.map (algebraMap (T.F m) K)).eval 0 := by
    have h0 := (hβS ⟨0, hn⟩).2
    simp only [βS, pow_zero, one_div] at h0
    rw [hβ₀def, ← map_pow, h0, eval_map, ← map_zero (algebraMap (T.F m) K), eval₂_at_apply]
  have hbk : ∀ k : Fin n, Differential.SuperData.bk ω β₀ (k : ℕ) = algebraMap (T.F m) K (βS k) := fun k ↦ by
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
      S.ordAt K (w * S.xE ^ ((M : ℤ) * M0)) α β =
        M * Differential.SuperData.gammaPts (K := K) (fun _ ↦ (0 : T.F m)) βS (ramMult n) (α, β) := by
    intro α β hv
    rw [S.ordAt_mul hv hw0 hxz, S.ordAt_zpow hv, S.ordAt_xE α β hv]
    by_cases hα : α = 0
    · subst hα
      obtain ⟨k, hk, rfl⟩ := S.over_zero_k ω hω β₀ hβ₀ hv0 β hv
      have hb0 := S.bk_ne ω hω β₀ hβ₀ k
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
  refine ⟨w * S.xE ^ ((M : ℤ) * M0), mul_ne_zero hw0 hxz, fun α β hv ↦ ?_, fun Q hQ ↦ hord Q.1 Q.2 hQ⟩
  rw [hord α β hv]
  positivity

end Facts

end MTower

end Curves.MT
