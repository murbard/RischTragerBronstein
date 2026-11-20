import RischTragerBronstein.Mixed.KEBridge
import RischTragerBronstein.Mixed.KQLiouville

/-!
# Torsion answers over a code field for several points, read on the curve over `C`

`S : SuperData C L` whose polynomial is the image of `fK` over a computable field `F` under
`φ : F →+* C`; points `(α_q, β_q)` over `F` with multiplicities `m_q`, the divisor
`Γ = ∑ m_q (φ α_q, φ β_q)` (`gammaQ`).

* `not_isPrincipalS_gen`: if no `N Γ` is principal over `F`, none is over the algebraic closure
  of `C`;
* `ordAt_witW_gen`: the witness of `N Γ` found over `F` (`witW`), read in `C(x, y)`, has divisor
  exactly `N Γ`.
-/

open Polynomial IntermediateField Sup CPoly

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K] [IsAlgClosed K]
variable (S : SuperData C L)

section Bridge

variable {F : Type*} [Field F] [DecidableEq F] (φ : F →+* C) (fK : CPoly F)
  (hpf : S.p = (toPoly fK).map φ) (hd : (toPoly fK).natDegree = fK.length - 1)
  (hcop : Nat.Coprime S.n S.p.natDegree)
  {r : ℕ} (α β : Fin r → F) (mq : Fin r → ℕ)
  (hΓK : ∀ q, (S.n : F) * β q ^ (S.n - 1) ≠ 0 ∧ β q ^ S.n = (toPoly fK).eval (α q))
  (hinj : Function.Injective fun q ↦ (φ (α q), φ (β q))) (hβne : ∀ q, β q ≠ 0)
include hpf hd hcop hΓK hinj hβne

lemma natDegree_p' : S.p.natDegree = fK.length - 1 := by
  rw [hpf, natDegree_map_eq_of_injective φ.injective, hd]

open Classical in
/-- **No torsion over the code field ⇒ no torsion over `C`.** -/
theorem not_isPrincipalS_gen
    (hnot : ∀ N, 1 ≤ N → ¬ PrincipalMulN (toPoly fK) S.n (fK.length - 1) α β mq N) :
    ∀ N : ℕ, 0 < N → ¬ S.IsPrincipalS K (gammaQ (fun q ↦ φ (α q)) (fun q ↦ φ (β q)) mq) N := by
  intro N hN hP
  apply hnot N hN
  have hβ0 : ∀ q, φ (β q) ≠ 0 := fun q h0 ↦ hβne q ((map_eq_zero_iff φ φ.injective).mp h0)
  have h1 := S.principalMulN_of_isPrincipalS (K := K) hcop (fun q ↦ φ (α q)) (fun q ↦ φ (β q)) mq
    hinj hβ0 (fun q ↦ by
      rw [← map_pow, (hΓK q).2, hpf, eval_map, ← eval₂_hom])
    _ (fun Q _ ↦ rfl) N hP
  refine principalMulN_descend φ (toPoly fK) S.hn (fK.length - 1) α β mq hΓK N ?_
  rw [← hpf, ← S.natDegree_p' φ fK hpf hd hcop α β hΓK hinj hβne]
  exact h1

open Classical in
/-- **The torsion witness found over the code field has divisor `N Γ` over `C`.** -/
theorem ordAt_witW_gen (N : ℕ) (Wb : BPoly F)
    (hW : witW fK S.n (fK.length - 1) α β mq N = some Wb) :
    S.elemW ((toB Wb).map (mapRingHom φ)) ≠ 0 ∧ ∀ a b : K,
      b ^ S.n = (S.p.map (algebraMap C K)).eval a →
        S.ordAt K (S.elemW ((toB Wb).map (mapRingHom φ))) a b =
          N * gammaQ (fun q ↦ φ (α q)) (fun q ↦ φ (β q)) mq (a, b) := by
  obtain ⟨hW0, hWs, hWv⟩ := witW_spec fK S.n S.hn (fK.length - 1) α β mq N hΓK hW
  have hdeg := S.natDegree_p' φ fK hpf hd hcop α β hΓK hinj hβne
  set W := (toB Wb).map (mapRingHom φ) with hWdef
  have hWne : W ≠ 0 := by
    rw [hWdef]; exact (Polynomial.map_ne_zero_iff (Polynomial.map_injective φ φ.injective)).mpr hW0
  set M := N * ∑ q, mq q with hM
  have hsupp : ∀ i a, (W.coeff i).coeff a ≠ 0 → i < S.n ∧ S.n * a + S.p.natDegree * i ≤ M := by
    intro i a h
    rw [hWdef, coeff_map, coe_mapRingHom, coeff_map] at h
    have h' : ((toB Wb).coeff i).coeff a ≠ 0 := fun h0 ↦ h (by rw [h0, map_zero])
    have := hWs i a h'
    simpa [hdeg] using this
  set ψ := (algebraMap C K).comp φ
  have hpK : (toPoly fK).map ψ = S.p.map (algebraMap C K) := by
    rw [hpf, Polynomial.map_map]
  have hWK : (toB Wb).map (mapRingHom ψ) = W.map (mapRingHom (algebraMap C K)) := by
    rw [hWdef, Polynomial.map_map, ← mapRingHom_comp]
  set pt : Fin r → K × K := fun q ↦ (algebraMap C K (φ (α q)), algebraMap C K (φ (β q))) with hpt
  have hptinj : Function.Injective pt := fun q q' h ↦ hinj (by
    simp only [hpt, Prod.ext_iff] at h
    exact Prod.ext ((algebraMap C K).injective h.1) ((algebraMap C K).injective h.2))
  set T : Finset (K × K) := Finset.univ.image pt with hT
  set mult : K × K → ℕ := fun Q ↦ N * gammaQ (fun q ↦ φ (α q)) (fun q ↦ φ (β q)) mq Q with hmult
  have hmultpt : ∀ q, mult (pt q) = N * mq q := fun q ↦ by
    simp only [hmult, gammaQ]
    congr 1
    rw [Finset.sum_eq_single q]
    · simp [hpt]
    · intro q' _ hq'
      rw [if_neg]
      intro h
      exact hq' (hptinj h).symm
    · simp
  have hcert := S.ordAt_elemW_cert (K := K) hcop W hWne M hsupp T mult
    (fun Q hQ ↦ by
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hQ
      refine ⟨fun h0 ↦ hβne q ((map_eq_zero_iff φ φ.injective).mp
        ((map_eq_zero_iff _ (algebraMap C K).injective).mp h0)), ?_⟩
      · rw [← map_pow, ← map_pow, (hΓK q).2, ← hpK, eval_map]
        show _ = eval₂ ψ (ψ (α q)) _
        rw [eval₂_at_apply]; rfl)
    (by
      rw [hT, Finset.sum_image (fun q _ q' _ h ↦ hptinj h)]
      simp only [hmultpt, hM, Finset.mul_sum])
    (fun Q hQ ↦ by
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hQ
      have hv0 := vanishAtN_map ψ (hWv q)
      rw [hpK, hWK] at hv0
      rw [hmultpt q]
      exact hv0)
  refine ⟨hcert.1, fun a b hv ↦ ?_⟩
  rw [hcert.2 (a, b) hv]
  split_ifs with hQ
  · rfl
  · simp only [gammaQ]
    push_cast
    rw [Finset.sum_eq_zero, mul_zero]
    intro q _
    rw [if_neg]
    intro h
    exact hQ (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, h.symm⟩)

end Bridge

end SuperData

end Differential
