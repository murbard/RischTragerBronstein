import RischTragerBronstein.Mixed.KQTwist
import RischTragerBronstein.Mixed.KQMulti

/-!
# Torsion answers for one residue class, read on the untwisted curve

`S : SuperData C L` with `n = 2`; a class `k` of the poles `(c_q, β_q)` (`q` with `κ(q) = k`,
enumerated by `ι : Fin r_k → Fin r`); the twisted curve `ỹ² = μ² p` is the image of a code `fK`
over a computable field `F`, with the points `(α_i, β̃_i) ↦ (c_{ι i}, μ β_{ι i})`.

* `class_not_principal`: no torsion over `F` ⇒ no multiple of `Γ_k` is principal on `S`;
* `class_witness`: the witness over `F`, untwisted, has divisor `N Γ_k` on `S`.
-/

open Polynomial IntermediateField Sup CPoly Classical

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K] [IsAlgClosed K]
variable (S : SuperData C L)

section Class

variable (hn2 : S.n = 2) (hcop : Nat.Coprime S.n S.p.natDegree)
  {r rk nk : ℕ} (c β : Fin r → C) (hc : Function.Injective c)
  (hβ : ∀ q, β q ≠ 0 ∧ β q ^ S.n = S.p.eval (c q)) (m : Fin r → ℕ) (cl : Fin r → Fin nk)
  (k : Fin nk) (ι : Fin rk → Fin r) (hιk : ∀ i, cl (ι i) = k)
  (hsurj : ∀ q, cl q = k → ∃ i, ι i = q) (hιinj : Function.Injective ι)
  {F : Type*} [Field F] [DecidableEq F] (φ : F →+* C) (fK : CPoly F) (μ : C) (hμ : μ ≠ 0)
  (hpf : Polynomial.C (μ ^ 2) * S.p = (toPoly fK).map φ)
  (hd : (toPoly fK).natDegree = fK.length - 1)
  (α β' : Fin rk → F) (hα : ∀ i, φ (α i) = c (ι i)) (hβ' : ∀ i, φ (β' i) = μ * β (ι i))
  (mq : Fin rk → ℕ) (hmq : ∀ i, mq i = m (ι i))

include hc hιk hsurj hιinj in
lemma gammaQ_class (Q : K × K) :
    gammaQ c β (mK m cl k) Q =
      ∑ i, if Q = (algebraMap C K (c (ι i)), algebraMap C K (β (ι i))) then m (ι i) else 0 := by
  rw [gammaQ]
  symm
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun q ↦ cl q = k)]
  have h2 : ∑ q ∈ Finset.univ.filter (fun q ↦ ¬ cl q = k),
      (if Q = (algebraMap C K (c q), algebraMap C K (β q)) then mK m cl k q else 0) = 0 :=
    Finset.sum_eq_zero fun q hq ↦ by
      have := (Finset.mem_filter.mp hq).2
      simp [mK, this]
  rw [h2, add_zero]
  refine Finset.sum_bij (fun i _ ↦ ι i) (fun i _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hιk i⟩)
    (fun i _ j _ h ↦ hιinj h) (fun q hq ↦ ?_) (fun i _ ↦ by simp [mK, hιk i])
  obtain ⟨i, rfl⟩ := hsurj q (Finset.mem_filter.mp hq).2
  exact ⟨i, Finset.mem_univ _, rfl⟩

include hμ in
lemma natDegree_eq_of_scale (hpf' : Polynomial.C (μ ^ 2) * S.p = (toPoly fK).map φ)
    (hd' : (toPoly fK).natDegree = fK.length - 1) : S.p.natDegree = fK.length - 1 := by
  have : (Polynomial.C (μ ^ 2) * S.p).natDegree = S.p.natDegree :=
    natDegree_C_mul (pow_ne_zero 2 hμ)
  rw [← this, hpf', natDegree_map_eq_of_injective φ.injective, hd']

include hn2 hcop hc hβ hιk hsurj hιinj hμ hpf hd hα hβ' hmq in
/-- **No torsion of the twisted class over `F` ⇒ no multiple of `Γ_k` is principal on `S`.** -/
theorem class_not_principal
    (hΓK : ∀ i, ((2 : ℕ) : F) * β' i ^ (2 - 1) ≠ 0 ∧ β' i ^ 2 = (toPoly fK).eval (α i))
    (hnot : ∀ N, 1 ≤ N → ¬ PrincipalMulN (toPoly fK) 2 (fK.length - 1) α β' mq N) :
    ∀ N : ℕ, 0 < N → ¬ S.IsPrincipalS K (gammaQ c β (mK m cl k)) N := by
  intro N hN hP
  apply hnot N hN
  have hinjpt : Function.Injective fun i ↦ (c (ι i), β (ι i)) := fun i j h ↦
    hιinj (hc (Prod.ext_iff.mp h).1)
  have h1 := S.principalMulN_of_isPrincipalS (K := K) hcop (fun i ↦ c (ι i)) (fun i ↦ β (ι i)) mq
    hinjpt (fun i ↦ (hβ (ι i)).1) (fun i ↦ (hβ (ι i)).2) _ (fun Q _ ↦ by
      rw [gammaQ_class c β hc m cl k ι hιk hsurj hιinj Q]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hmq]) N hP
  have h2 := principalMulN_scale μ hμ h1
  rw [hn2] at h2
  refine principalMulN_descend φ (toPoly fK) (by norm_num : 0 < 2) (fK.length - 1) α β' mq
    (fun i ↦ ⟨(hΓK i).1, (hΓK i).2⟩) N ?_
  have e1 : (fun i ↦ φ (α i)) = fun i ↦ c (ι i) := funext hα
  have e2 : (fun i ↦ φ (β' i)) = fun i ↦ μ * β (ι i) := funext hβ'
  rw [e1, e2, ← hpf, ← natDegree_eq_of_scale S φ fK μ hμ hpf hd]
  exact h2

include hn2 hcop hc hβ hιk hsurj hιinj hμ hpf hd hα hβ' hmq in
/-- **The witness of the twisted class, untwisted, has divisor `N Γ_k` on `S`.** -/
theorem class_witness
    (hΓK : ∀ i, ((2 : ℕ) : F) * β' i ^ (2 - 1) ≠ 0 ∧ β' i ^ 2 = (toPoly fK).eval (α i))
    (N : ℕ) (Wb : BPoly F) (hW : witW fK 2 (fK.length - 1) α β' mq N = some Wb) :
    S.elemW (((toB Wb).map (mapRingHom φ)).comp (Polynomial.C (Polynomial.C μ) * X)) ≠ 0 ∧
      ∀ a b : K, b ^ S.n = (S.p.map (algebraMap C K)).eval a →
        S.ordAt K (S.elemW (((toB Wb).map (mapRingHom φ)).comp
          (Polynomial.C (Polynomial.C μ) * X))) a b = N * gammaQ c β (mK m cl k) (a, b) := by
  obtain ⟨hW0, hWs, hWv⟩ := witW_spec fK 2 (by norm_num) (fK.length - 1) α β' mq N hΓK hW
  have hdeg := natDegree_eq_of_scale S φ fK μ hμ hpf hd
  set W := ((toB Wb).map (mapRingHom φ)).comp (Polynomial.C (Polynomial.C μ) * X) with hWdef
  have hCμ : Polynomial.C μ ∈ nonZeroDivisors C[X] :=
    mem_nonZeroDivisors_of_ne_zero (Polynomial.C_ne_zero.mpr hμ)
  have hWne : W ≠ 0 := fun h0 ↦ hW0 ((Polynomial.map_eq_zero_iff
    (Polynomial.map_injective φ φ.injective)).mp ((comp_C_mul_X_eq_zero_iff hCμ).mp h0))
  set M := N * ∑ i, mq i with hM
  have hsupp : ∀ i a, (W.coeff i).coeff a ≠ 0 → i < S.n ∧ S.n * a + S.p.natDegree * i ≤ M := by
    intro i a h
    rw [hWdef, comp_C_mul_X_coeff, ← Polynomial.C_pow, Polynomial.coeff_mul_C, coeff_map,
      coe_mapRingHom, coeff_map] at h
    have h' : ((toB Wb).coeff i).coeff a ≠ 0 := fun h0 ↦ h (by rw [h0, map_zero, zero_mul])
    have := hWs i a h'
    rw [hn2, hdeg]; exact this
  set pt : Fin rk → K × K := fun i ↦ (algebraMap C K (c (ι i)), algebraMap C K (β (ι i))) with hpt
  have hptinj : Function.Injective pt := fun i j h ↦ hιinj (hc ((algebraMap C K).injective
    (Prod.ext_iff.mp h).1))
  have hgpt : ∀ i, gammaQ c β (mK m cl k) (pt i) = m (ι i) := fun i ↦ by
    rw [gammaQ_class c β hc m cl k ι hιk hsurj hιinj, Finset.sum_eq_single i]
    · simp [hpt]
    · intro j _ hj; rw [if_neg]; intro h; exact hj (hptinj h.symm)
    · simp
  set T : Finset (K × K) := Finset.univ.image pt
  set mult : K × K → ℕ := fun Q ↦ N * gammaQ c β (mK m cl k) Q with hmult
  have hvan : ∀ i, VanishAtN S.p 2 W (c (ι i)) (β (ι i)) (N * mq i) := by
    intro i
    have h1 := (hWv i).mapR φ
    rw [← hpf, hα, hβ'] at h1
    have h2 := vanishAtN_scale μ⁻¹ (inv_ne_zero hμ) h1
    have e1 : Polynomial.C (μ⁻¹ ^ 2) * (Polynomial.C (μ ^ 2) * S.p) = S.p := by
      rw [← mul_assoc, ← Polynomial.C_mul, ← mul_pow, inv_mul_cancel₀ hμ, one_pow, Polynomial.C_1,
        one_mul]
    rw [e1, inv_inv, ← mul_assoc, inv_mul_cancel₀ hμ, one_mul] at h2
    exact h2
  have hcert := S.ordAt_elemW_cert (K := K) hcop W hWne M hsupp T mult
    (fun Q hQ ↦ by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hQ
      refine ⟨(map_ne_zero_iff _ (algebraMap C K).injective).mpr (hβ (ι i)).1, ?_⟩
      simp only [hpt]
      rw [← map_pow, (hβ (ι i)).2, eval_map, eval₂_at_apply])
    (by
      rw [Finset.sum_image fun i _ j _ h ↦ hptinj h]
      simp only [hmult, hgpt, hM, Finset.mul_sum, hmq])
    (fun Q hQ ↦ by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hQ
      have := (hvan i).mapR (algebraMap C K)
      simp only [hmult, hgpt, ← hmq]
      rw [hn2]
      exact this)
  refine ⟨hcert.1, fun a b hv ↦ ?_⟩
  rw [hcert.2 (a, b) hv]
  split_ifs with hQ
  · rfl
  · rw [gammaQ_class c β hc m cl k ι hιk hsurj hιinj, Finset.sum_eq_zero]
    · simp
    intro i _
    rw [if_neg]
    intro h
    exact hQ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩)

end Class

end SuperData

end Differential
