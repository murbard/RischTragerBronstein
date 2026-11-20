import RischTragerBronstein.Mixed.KXDep
import RischTragerBronstein.Mixed.KQMBridge
import Mathlib.FieldTheory.KummerPolynomial

/-!
# A relation with `δ₀` forces `P₊` to be defined over the code field

`S : SuperData C L` (`n = 2`), points `(a_i, b_i)` whose twist `(a_i, μ b_i)` lies over a field
`F` (`φ : F → C`, the twisted curve `ỹ² = μ² p` the image of a code `fK`). If
`(0, σ) + ∑ m_i (a_i, b_i)` (with multiplicity `M > 0` at `(0, σ)`) is principal and no non-zero
multiple of `(0, σ) − (0, −σ)` is principal, then `μ σ ∈ φ(F)`: otherwise `F' = F(√δ)`,
`δ = fK(0)`, is a field with two embeddings into `C` (`√δ ↦ ±μσ`), the relation descends to `F'`
(`principalMulN_descend`) and its conjugate gives the relation at `(0, −σ)`; their quotient has
divisor `M ((0, σ) − (0, −σ))` (`rel_point_defined`).
-/

open Polynomial IntermediateField Sup CPoly Classical

set_option linter.unusedSectionVars false

namespace Sup

/-- `PrincipalMulN` is preserved by injective ring maps. -/
lemma principalMulN_map {F E : Type*} [Field F] [Field E] (ψ : F →+* E) {f : F[X]} {n d r : ℕ}
    {α β : Fin r → F} {mq : Fin r → ℕ} {s : ℕ} (h : PrincipalMulN f n d α β mq s) :
    PrincipalMulN (f.map ψ) n d (fun q ↦ ψ (α q)) (fun q ↦ ψ (β q)) mq s := by
  obtain ⟨W, hW0, hWs, hWv⟩ := h
  refine ⟨W.map (mapRingHom ψ), fun h0 ↦ hW0 ?_, fun j a hja ↦ hWs j a fun h0 ↦ hja ?_,
    fun q ↦ (hWv q).mapR ψ⟩
  · exact (Polynomial.map_eq_zero_iff (Polynomial.map_injective ψ ψ.injective)).mp h0
  · rw [coeff_map, coe_mapRingHom, coeff_map, h0, map_zero]

/-- Points of multiplicity `0` can be dropped. -/
lemma principalMulN_restrict {F : Type*} [Field F] {f : F[X]} {n d r rk : ℕ} {α β : Fin r → F}
    {mq : Fin r → ℕ} {s : ℕ} (ι : Fin rk → Fin r) (hι : Function.Injective ι)
    (hsupp : ∀ q, mq q ≠ 0 → ∃ i, ι i = q) (h : PrincipalMulN f n d α β mq s) :
    PrincipalMulN f n d (fun i ↦ α (ι i)) (fun i ↦ β (ι i)) (fun i ↦ mq (ι i)) s := by
  obtain ⟨W, hW0, hWs, hWv⟩ := h
  have hsum : ∑ i, mq (ι i) = ∑ q, mq q := by
    rw [show ∑ i, mq (ι i) = ∑ q ∈ Finset.univ.map ⟨ι, hι⟩, mq q from
      (Finset.sum_map Finset.univ ⟨ι, hι⟩ mq).symm]
    refine Finset.sum_subset (Finset.subset_univ _) fun q _ hq ↦ ?_
    by_contra h0
    obtain ⟨i, rfl⟩ := hsupp q h0
    exact hq (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  refine ⟨W, hW0, fun j a hja ↦ ?_, fun i ↦ hWv (ι i)⟩
  rw [hsum]; exact hWs j a hja

end Sup

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K] [IsAlgClosed K]
variable (S : SuperData C L)

/-- The divisor of an augmented point set. -/
lemma gammaQ_cons {r : ℕ} (a b : Fin r → C) (mq : Fin r → ℕ) (σ : C) (M : ℕ) (Q : K × K) :
    gammaQ (Fin.cons 0 a) (Fin.cons σ b) (Fin.cons M mq) Q =
      gammaQ a b mq Q + M * gammaP (algebraMap C K σ) Q := by
  simp only [gammaQ, gammaP, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, map_zero]
  rw [add_comm]; congr 1; split_ifs <;> simp

/-- An augmented point set is injective. -/
lemma cons_inj {r : ℕ} (a : Fin r → C) (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0) :
    Function.Injective (Fin.cons (0 : C) a : Fin (r + 1) → C) := by
  intro i j h
  induction i using Fin.cases <;> induction j using Fin.cases
  · rfl
  · exact absurd h.symm (by simpa using ha0 _)
  · exact absurd h (by simpa using ha0 _)
  · simp only [Fin.cons_succ] at h; rw [ha h]

section Conj

variable (hn2 : S.n = 2) (hcop : Nat.Coprime S.n S.p.natDegree)
  {r : ℕ} (a b : Fin r → C) (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0)
  (hb : ∀ i, b i ≠ 0 ∧ b i ^ S.n = S.p.eval (a i)) (mq : Fin r → ℕ)

include hn2 hcop ha ha0 hb in
/-- **A principal augmented point set**, from `PrincipalMulN`: a function with exactly that
divisor (`class_witness` over `C` itself). -/
lemma fun_of_principalMulN (σ : C) (hσ0 : σ ≠ 0) (hσ : σ ^ S.n = S.p.eval 0) (M : ℕ)
    (hP : PrincipalMulN S.p S.n S.p.natDegree (Fin.cons 0 a) (Fin.cons σ b) (Fin.cons M mq) 1) :
    ∃ w : C⟮S.x⟯⟮S.y⟯, w ≠ 0 ∧ ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K w α β' = gammaQ (Fin.cons 0 a) (Fin.cons σ b) (Fin.cons M mq) (α, β') := by
  set fC : CPoly C := (List.range (S.p.natDegree + 1)).map S.p.coeff with hfC
  have hfp : CPoly.toPoly fC = S.p := toPoly_coeffs S.p
  have hlen : fC.length - 1 = S.p.natDegree := by simp [hfC]
  have hpf : Polynomial.C ((1 : C) ^ 2) * S.p = (toPoly fC).map (RingHom.id C) := by
    rw [Polynomial.map_id, hfp]; simp
  have hd : (toPoly fC).natDegree = fC.length - 1 := by rw [hfp, hlen]
  have hβ' : ∀ q, (Fin.cons σ b : Fin (r + 1) → C) q ≠ 0 ∧
      (Fin.cons σ b : Fin (r + 1) → C) q ^ S.n = S.p.eval ((Fin.cons 0 a : Fin (r + 1) → C) q) :=
    fun q ↦ by
      induction q using Fin.cases
      · exact ⟨hσ0, hσ⟩
      · exact hb _
  have hΓK : ∀ i : Fin (r + 1), ((2 : ℕ) : C) * (Fin.cons σ b : Fin (r + 1) → C) i ^ (2 - 1) ≠ 0 ∧
      (Fin.cons σ b : Fin (r + 1) → C) i ^ 2 = (toPoly fC).eval ((Fin.cons 0 a : Fin (r + 1) → C) i) :=
    fun i ↦ ⟨by rw [pow_one]; exact mul_ne_zero (by norm_num) (hβ' i).1, by
      rw [hfp, ← hn2]; exact (hβ' i).2⟩
  have hP' : PrincipalMulN (toPoly fC) 2 (fC.length - 1) (Fin.cons 0 a) (Fin.cons σ b)
      (Fin.cons M mq) 1 := by rw [hfp, hlen, ← hn2]; exact hP
  obtain ⟨Wb, hWb⟩ := Option.ne_none_iff_exists'.mp
    (witW_ne_none fC 2 two_pos _ _ _ _ 1 (fun q ↦ by simpa using hΓK q) hP')
  have h := S.class_witness (K := K) hn2 hcop (Fin.cons 0 a) (Fin.cons σ b) (cons_inj a ha ha0) hβ'
    (Fin.cons M mq) (fun _ ↦ (0 : Fin 1)) 0 id (fun _ ↦ rfl) (fun q _ ↦ ⟨q, rfl⟩) (fun _ _ h ↦ h)
    (RingHom.id C) fC 1 one_ne_zero hpf hd _ _ (fun _ ↦ rfl) (fun i ↦ by simp) _ (fun _ ↦ rfl) hΓK
    1 Wb hWb
  refine ⟨_, h.1, fun α β' hv ↦ ?_⟩
  rw [h.2 α β' hv]
  have : mK (Fin.cons M mq) (fun _ : Fin (r + 1) ↦ (0 : Fin 1)) 0 = Fin.cons M mq := by
    funext q; simp [mK]
  rw [this]; simp

include hn2 hcop ha ha0 hb in
/-- **A relation with `δ₀` forces `μσ ∈ φ(F)`.** -/
theorem rel_point_defined {F : Type*} [Field F] [DecidableEq F] (φ : F →+* C) (fK : CPoly F)
    (μ : C) (hμ : μ ≠ 0) (hpf : Polynomial.C (μ ^ 2) * S.p = (toPoly fK).map φ)
    (α β' : Fin r → F) (hα : ∀ i, φ (α i) = a i) (hβ' : ∀ i, φ (β' i) = μ * b i)
    (hΓK : ∀ i, β' i ≠ 0 ∧ β' i ^ 2 = (toPoly fK).eval (α i))
    (σ : C) (hσ0 : σ ≠ 0) (hσ : σ ^ S.n = S.p.eval 0) (M : ℕ) (hM : 0 < M)
    (hrel : S.IsPrincipalS K (gammaQ (Fin.cons 0 a) (Fin.cons σ b) (Fin.cons M mq)) 1)
    (hntZ : ∀ f : C⟮S.x⟯⟮S.y⟯, f ≠ 0 → ∀ M' : ℤ, (∀ α' β'' : K,
      β'' ^ S.n = (S.p.map (algebraMap C K)).eval α' →
        (S.ordAt K f α' β'' : ℚ) = M' * dZ (algebraMap C K σ) (α', β'')) → M' = 0) :
    ∃ bt : F, φ bt = μ * σ := by
  by_contra hno
  push_neg at hno
  set δ : F := fK.getD 0 0 with hδ
  have hσ2 : σ ^ 2 = S.p.eval 0 := by rw [← hn2]; exact hσ
  have hφδ : φ δ = (μ * σ) ^ 2 := by
    have h0 := congrArg (fun P ↦ P.eval 0) hpf
    rw [eval_mul, eval_C, Polynomial.eval_zero_map, ← coeff_zero_eq_eval_zero (p := toPoly fK),
      CPoly.coeff_toPoly, ← hσ2] at h0
    rw [hδ, ← h0]; ring
  have hns : ∀ c : F, c ^ 2 ≠ δ := fun c hc ↦ by
    have h1 : φ c ^ 2 = (μ * σ) ^ 2 := by rw [← map_pow, hc, hφδ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exact hno c h
    · exact hno (-c) (by rw [map_neg, h, neg_neg])
  haveI : Fact (Irreducible (X ^ 2 - Polynomial.C δ)) :=
    ⟨X_pow_sub_C_irreducible_of_prime Nat.prime_two hns⟩
  set g : F[X] := X ^ 2 - Polynomial.C δ with hg
  set ι : F →+* AdjoinRoot g := AdjoinRoot.of g
  have hev : ∀ x : C, x ^ 2 = φ δ → g.eval₂ φ x = 0 := fun x hx ↦ by
    simp [hg, eval₂_sub, hx]
  set φ1 := AdjoinRoot.lift φ (μ * σ) (hev _ hφδ.symm)
  set φ2 := AdjoinRoot.lift φ (-(μ * σ)) (hev _ (by rw [neg_sq]; exact hφδ.symm))
  have h1ι : φ1.comp ι = φ := by ext x; simp [φ1, ι]
  have h2ι : φ2.comp ι = φ := by ext x; simp [φ2, ι]
  set ρ := AdjoinRoot.root g
  have h1ρ : φ1 ρ = μ * σ := by simp [φ1, ρ]
  have h2ρ : φ2 ρ = -(μ * σ) := by simp [φ2, ρ]
  -- step 1: the relation as `PrincipalMulN` over `C`, twisted
  have hinjpt : Function.Injective fun q : Fin (r + 1) ↦
      ((Fin.cons 0 a : Fin (r + 1) → C) q, (Fin.cons σ b : Fin (r + 1) → C) q) := fun i j h ↦
    cons_inj a ha ha0 (Prod.ext_iff.mp h).1
  have hP0 := S.principalMulN_of_isPrincipalS (K := K) hcop (Fin.cons 0 a) (Fin.cons σ b)
    (Fin.cons M mq) hinjpt
    (fun q ↦ by induction q using Fin.cases
                · exact hσ0
                · exact (hb _).1)
    (fun q ↦ by induction q using Fin.cases
                · exact hσ
                · exact (hb _).2) _ (fun Q _ ↦ rfl) 1 hrel
  have hP1 := principalMulN_scale μ hμ hP0
  rw [hn2, hpf] at hP1
  -- step 2: descend to `F' = F(√δ)` along `φ1`
  set α'' : Fin (r + 1) → AdjoinRoot g := Fin.cons 0 fun i ↦ ι (α i)
  set β'' : Fin (r + 1) → AdjoinRoot g := Fin.cons ρ fun i ↦ ι (β' i)
  have hf' : (toPoly fK).map φ = ((toPoly fK).map ι).map φ1 := by rw [Polynomial.map_map, h1ι]
  have e1 : (Fin.cons 0 a : Fin (r + 1) → C) = fun q ↦ φ1 (α'' q) := by
    funext q; induction q using Fin.cases
    · simp [α'']
    · simp [α'', ← hα, ← RingHom.comp_apply, h1ι]
  have e2 : (fun q ↦ μ * (Fin.cons σ b : Fin (r + 1) → C) q) = fun q ↦ φ1 (β'' q) := by
    funext q; induction q using Fin.cases
    · simp [β'', h1ρ]
    · simp [β'', ← hβ', ← RingHom.comp_apply, h1ι]
  rw [hf', e1, e2] at hP1
  have h2F : ((2 : ℕ) : AdjoinRoot g) ≠ 0 := fun h ↦ by
    have := congrArg φ1 h
    rw [map_natCast, map_zero] at this
    exact absurd this (by norm_num)
  have hρ2 : ρ ^ 2 = ι δ := by
    have := AdjoinRoot.eval₂_root g
    simp only [hg, eval₂_sub, eval₂_X_pow, eval₂_C] at this
    exact sub_eq_zero.mp this
  have hΓ' : ∀ q, ((2 : ℕ) : AdjoinRoot g) * β'' q ^ (2 - 1) ≠ 0 ∧
      β'' q ^ 2 = ((toPoly fK).map ι).eval (α'' q) := fun q ↦ by
    induction q using Fin.cases
    · refine ⟨?_, ?_⟩
      · rw [pow_one]
        refine mul_ne_zero h2F fun h0 ↦ ?_
        have : φ1 ρ = 0 := by simp only [β'', Fin.cons_zero] at h0; rw [h0, map_zero]
        rw [h1ρ] at this; exact mul_ne_zero hμ hσ0 this
      · simp only [β'', α'', Fin.cons_zero]
        rw [hρ2, Polynomial.eval_zero_map, ← coeff_zero_eq_eval_zero, CPoly.coeff_toPoly]
    · rename_i i
      simp only [β'', α'', Fin.cons_succ]
      refine ⟨?_, ?_⟩
      · rw [pow_one]
        refine mul_ne_zero h2F fun h0 ↦ (hΓK i).1 ?_
        exact ι.injective (by rw [h0, map_zero])
      · rw [← map_pow, (hΓK i).2, Polynomial.eval_map, eval₂_at_apply]
  have hP2 := principalMulN_descend φ1 _ two_pos _ α'' β'' _ hΓ' 1 hP1
  -- step 3: the conjugate embedding gives the relation at `(0, −σ)`
  have hP3 := principalMulN_map φ2 hP2
  rw [Polynomial.map_map, h2ι, ← hpf] at hP3
  have hP4 := principalMulN_scale μ⁻¹ (inv_ne_zero hμ) hP3
  have e3 : Polynomial.C (μ⁻¹ ^ 2) * (Polynomial.C (μ ^ 2) * S.p) = S.p := by
    rw [← mul_assoc, ← Polynomial.C_mul, ← mul_pow, inv_mul_cancel₀ hμ, one_pow, Polynomial.C_1,
      one_mul]
  have e4 : (fun q ↦ φ2 (α'' q)) = (Fin.cons 0 a : Fin (r + 1) → C) := by
    funext q; induction q using Fin.cases
    · simp [α'']
    · simp [α'', ← hα, ← RingHom.comp_apply, h2ι]
  have e5 : (fun q ↦ μ⁻¹ * φ2 (β'' q)) = (Fin.cons (-σ) b : Fin (r + 1) → C) := by
    funext q; induction q using Fin.cases
    · simp only [β'', Fin.cons_zero, h2ρ]; field_simp
    · simp only [β'', Fin.cons_succ, ← RingHom.comp_apply, h2ι, hβ']; field_simp
  rw [e3, e4, e5, ← hn2] at hP4
  -- step 4: the two functions and their quotient
  obtain ⟨w2, hw2, hw2o⟩ := S.fun_of_principalMulN (K := K) hn2 hcop a b ha ha0 hb mq (-σ) (neg_ne_zero.mpr hσ0)
    (by rw [hn2, neg_sq, ← hn2]; exact hσ) M hP4
  obtain ⟨w1, hw1, -, hw1o⟩ := hrel
  have hf0 : w1 * w2⁻¹ ≠ 0 := mul_ne_zero hw1 (inv_ne_zero hw2)
  have hMz := hntZ (w1 * w2⁻¹) hf0 M fun α' β'' hv ↦ by
    rw [S.ordAt_mul hv hw1 (inv_ne_zero hw2), S.ordAt_inv hv, hw1o (α', β'') hv, hw2o α' β'' hv,
      gammaQ_cons, gammaQ_cons]
    simp only [gammaP, dZ, map_neg, Prod.ext_iff]
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap C K).injective
    have hσK : algebraMap C K σ ≠ 0 := (map_ne_zero_iff _ (algebraMap C K).injective).mpr hσ0
    have hne : algebraMap C K σ ≠ -algebraMap C K σ := fun h ↦ hσK (by
      have h2 : (2 : K) * algebraMap C K σ = 0 := by linear_combination h
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero)
    split_ifs <;> simp_all <;> push_cast <;> ring
  exact absurd (by exact_mod_cast hMz : M = 0) hM.ne'

include hn2 hcop ha ha0 hb in
/-- **`rel_point_defined` from `PrincipalMulN`.** -/
theorem rel_point_defined_pm {F : Type*} [Field F] [DecidableEq F] (φ : F →+* C) (fK : CPoly F)
    (μ : C) (hμ : μ ≠ 0) (hpf : Polynomial.C (μ ^ 2) * S.p = (toPoly fK).map φ)
    (α β' : Fin r → F) (hα : ∀ i, φ (α i) = a i) (hβ' : ∀ i, φ (β' i) = μ * b i)
    (hΓK : ∀ i, β' i ≠ 0 ∧ β' i ^ 2 = (toPoly fK).eval (α i))
    (σ : C) (hσ0 : σ ≠ 0) (hσ : σ ^ S.n = S.p.eval 0) (M : ℕ) (hM : 0 < M)
    (hP0 : PrincipalMulN S.p S.n S.p.natDegree (Fin.cons 0 a) (Fin.cons σ b) (Fin.cons M mq) 1)
    (hntZ : ∀ f : C⟮S.x⟯⟮S.y⟯, f ≠ 0 → ∀ M' : ℤ, (∀ α' β'' : K,
      β'' ^ S.n = (S.p.map (algebraMap C K)).eval α' →
        (S.ordAt K f α' β'' : ℚ) = M' * dZ (algebraMap C K σ) (α', β'')) → M' = 0) :
    ∃ bt : F, φ bt = μ * σ := by
  by_contra hno
  push_neg at hno
  set δ : F := fK.getD 0 0 with hδ
  have hσ2 : σ ^ 2 = S.p.eval 0 := by rw [← hn2]; exact hσ
  have hφδ : φ δ = (μ * σ) ^ 2 := by
    have h0 := congrArg (fun P ↦ P.eval 0) hpf
    rw [eval_mul, eval_C, Polynomial.eval_zero_map, ← coeff_zero_eq_eval_zero (p := toPoly fK),
      CPoly.coeff_toPoly, ← hσ2] at h0
    rw [hδ, ← h0]; ring
  have hns : ∀ c : F, c ^ 2 ≠ δ := fun c hc ↦ by
    have h1 : φ c ^ 2 = (μ * σ) ^ 2 := by rw [← map_pow, hc, hφδ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exact hno c h
    · exact hno (-c) (by rw [map_neg, h, neg_neg])
  haveI : Fact (Irreducible (X ^ 2 - Polynomial.C δ)) :=
    ⟨X_pow_sub_C_irreducible_of_prime Nat.prime_two hns⟩
  set g : F[X] := X ^ 2 - Polynomial.C δ with hg
  set ι : F →+* AdjoinRoot g := AdjoinRoot.of g
  have hev : ∀ x : C, x ^ 2 = φ δ → g.eval₂ φ x = 0 := fun x hx ↦ by
    simp [hg, eval₂_sub, hx]
  set φ1 := AdjoinRoot.lift φ (μ * σ) (hev _ hφδ.symm)
  set φ2 := AdjoinRoot.lift φ (-(μ * σ)) (hev _ (by rw [neg_sq]; exact hφδ.symm))
  have h1ι : φ1.comp ι = φ := by ext x; simp [φ1, ι]
  have h2ι : φ2.comp ι = φ := by ext x; simp [φ2, ι]
  set ρ := AdjoinRoot.root g
  have h1ρ : φ1 ρ = μ * σ := by simp [φ1, ρ]
  have h2ρ : φ2 ρ = -(μ * σ) := by simp [φ2, ρ]
  have hP1 := principalMulN_scale μ hμ hP0
  rw [hn2, hpf] at hP1
  -- step 2: descend to `F' = F(√δ)` along `φ1`
  set α'' : Fin (r + 1) → AdjoinRoot g := Fin.cons 0 fun i ↦ ι (α i)
  set β'' : Fin (r + 1) → AdjoinRoot g := Fin.cons ρ fun i ↦ ι (β' i)
  have hf' : (toPoly fK).map φ = ((toPoly fK).map ι).map φ1 := by rw [Polynomial.map_map, h1ι]
  have e1 : (Fin.cons 0 a : Fin (r + 1) → C) = fun q ↦ φ1 (α'' q) := by
    funext q; induction q using Fin.cases
    · simp [α'']
    · simp [α'', ← hα, ← RingHom.comp_apply, h1ι]
  have e2 : (fun q ↦ μ * (Fin.cons σ b : Fin (r + 1) → C) q) = fun q ↦ φ1 (β'' q) := by
    funext q; induction q using Fin.cases
    · simp [β'', h1ρ]
    · simp [β'', ← hβ', ← RingHom.comp_apply, h1ι]
  rw [hf', e1, e2] at hP1
  have h2F : ((2 : ℕ) : AdjoinRoot g) ≠ 0 := fun h ↦ by
    have := congrArg φ1 h
    rw [map_natCast, map_zero] at this
    exact absurd this (by norm_num)
  have hρ2 : ρ ^ 2 = ι δ := by
    have := AdjoinRoot.eval₂_root g
    simp only [hg, eval₂_sub, eval₂_X_pow, eval₂_C] at this
    exact sub_eq_zero.mp this
  have hΓ' : ∀ q, ((2 : ℕ) : AdjoinRoot g) * β'' q ^ (2 - 1) ≠ 0 ∧
      β'' q ^ 2 = ((toPoly fK).map ι).eval (α'' q) := fun q ↦ by
    induction q using Fin.cases
    · refine ⟨?_, ?_⟩
      · rw [pow_one]
        refine mul_ne_zero h2F fun h0 ↦ ?_
        have : φ1 ρ = 0 := by simp only [β'', Fin.cons_zero] at h0; rw [h0, map_zero]
        rw [h1ρ] at this; exact mul_ne_zero hμ hσ0 this
      · simp only [β'', α'', Fin.cons_zero]
        rw [hρ2, Polynomial.eval_zero_map, ← coeff_zero_eq_eval_zero, CPoly.coeff_toPoly]
    · rename_i i
      simp only [β'', α'', Fin.cons_succ]
      refine ⟨?_, ?_⟩
      · rw [pow_one]
        refine mul_ne_zero h2F fun h0 ↦ (hΓK i).1 ?_
        exact ι.injective (by rw [h0, map_zero])
      · rw [← map_pow, (hΓK i).2, Polynomial.eval_map, eval₂_at_apply]
  have hP2 := principalMulN_descend φ1 _ two_pos _ α'' β'' _ hΓ' 1 hP1
  -- step 3: the conjugate embedding gives the relation at `(0, −σ)`
  have hP3 := principalMulN_map φ2 hP2
  rw [Polynomial.map_map, h2ι, ← hpf] at hP3
  have hP4 := principalMulN_scale μ⁻¹ (inv_ne_zero hμ) hP3
  have e3 : Polynomial.C (μ⁻¹ ^ 2) * (Polynomial.C (μ ^ 2) * S.p) = S.p := by
    rw [← mul_assoc, ← Polynomial.C_mul, ← mul_pow, inv_mul_cancel₀ hμ, one_pow, Polynomial.C_1,
      one_mul]
  have e4 : (fun q ↦ φ2 (α'' q)) = (Fin.cons 0 a : Fin (r + 1) → C) := by
    funext q; induction q using Fin.cases
    · simp [α'']
    · simp [α'', ← hα, ← RingHom.comp_apply, h2ι]
  have e5 : (fun q ↦ μ⁻¹ * φ2 (β'' q)) = (Fin.cons (-σ) b : Fin (r + 1) → C) := by
    funext q; induction q using Fin.cases
    · simp only [β'', Fin.cons_zero, h2ρ]; field_simp
    · simp only [β'', Fin.cons_succ, ← RingHom.comp_apply, h2ι, hβ']; field_simp
  rw [e3, e4, e5, ← hn2] at hP4
  -- step 4: the two functions and their quotient
  obtain ⟨w2, hw2, hw2o⟩ := S.fun_of_principalMulN (K := K) hn2 hcop a b ha ha0 hb mq (-σ) (neg_ne_zero.mpr hσ0)
    (by rw [hn2, neg_sq, ← hn2]; exact hσ) M hP4
  obtain ⟨w1, hw1, hw1o⟩ := S.fun_of_principalMulN (K := K) hn2 hcop a b ha ha0 hb mq σ hσ0 hσ M hP0
  have hf0 : w1 * w2⁻¹ ≠ 0 := mul_ne_zero hw1 (inv_ne_zero hw2)
  have hMz := hntZ (w1 * w2⁻¹) hf0 M fun α' β'' hv ↦ by
    rw [S.ordAt_mul hv hw1 (inv_ne_zero hw2), S.ordAt_inv hv, hw1o α' β'' hv, hw2o α' β'' hv,
      gammaQ_cons, gammaQ_cons]
    simp only [gammaP, dZ, map_neg, Prod.ext_iff]
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap C K).injective
    have hσK : algebraMap C K σ ≠ 0 := (map_ne_zero_iff _ (algebraMap C K).injective).mpr hσ0
    have hne : algebraMap C K σ ≠ -algebraMap C K σ := fun h ↦ hσK (by
      have h2 : (2 : K) * algebraMap C K σ = 0 := by linear_combination h
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero)
    split_ifs <;> simp_all <;> push_cast <;> ring
  exact absurd (by exact_mod_cast hMz : M = 0) hM.ne'

end Conj

end SuperData

end Differential
