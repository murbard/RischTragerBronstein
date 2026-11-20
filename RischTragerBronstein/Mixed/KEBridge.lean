import RischTragerBronstein.Mixed.KELiouville
import RischTragerBronstein.Algebraic.SupLogAbel
import RischTragerBronstein.Algebraic.SupLogSem
import RischTragerBronstein.Algebraic.SuperPrincipalIff

/-!
# Torsion answers over a code field, read on the curve over `C`

`S : SuperData C L` (`n = 2`, `p(0) = 1`) whose polynomial is the image of `fK` over a computable
field `F` under `φ : F →+* C`; the divisor `P₊ − ∞`, `P₊ = (0, 1)`.

* `not_isPrincipalS_of`: if no `N (P₊ − ∞)` is principal over `F` (`PrincipalMulN`), none is over
  the algebraic closure of `C` (`principalMulN_of_isPrincipalS`, `principalMulN_descend`);
* `ordAt_witW`: the witness `W` of `N (P₊ − ∞)` found over `F` (`witW`), read in `C(x, y)`, has
  divisor exactly `N (P₊ − ∞)` (`ordAt_elemW_cert`, the exact form of `cert_principal`).
-/

open Polynomial IntermediateField Sup CPoly

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K] [IsAlgClosed K]
variable (S : SuperData C L)

open Classical in
/-- **A certificate gives the exact divisor of `elemW W`.** -/
theorem ordAt_elemW_cert (hcop : Nat.Coprime S.n S.p.natDegree) (W : C[X][X]) (hW0 : W ≠ 0)
    (M : ℕ) (hsupp : ∀ i a, (W.coeff i).coeff a ≠ 0 → i < S.n ∧ S.n * a + S.p.natDegree * i ≤ M)
    (T : Finset (K × K)) (mult : K × K → ℕ)
    (hT : ∀ Q ∈ T, Q.2 ≠ 0 ∧ Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1)
    (hM : ∑ Q ∈ T, mult Q = M)
    (hv : ∀ Q ∈ T, VanishAtN (S.p.map (algebraMap C K)) S.n (W.map (mapRingHom (algebraMap C K)))
      Q.1 Q.2 (mult Q)) :
    S.elemW W ≠ 0 ∧ ∀ Q : K × K, Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1 →
      S.ordAt K (S.elemW W) Q.1 Q.2 = if Q ∈ T then (mult Q : ℤ) else 0 := by
  have hW := S.coeff_ge_n_of_supp W M hsupp
  set w := S.elemW W
  have hw0 : w ≠ 0 := S.elemW_ne_zero W hW0 hW
  have hint := S.elemW_integral (K := K) W
  have hge : ∀ Q ∈ T, (mult Q : ℤ) ≤ S.ordAt K w Q.1 Q.2 := fun Q hQ ↦ by
    obtain ⟨hβ, hvQ⟩ := hT Q hQ
    have h1 := S.orderTop_ge_of_vanish Q.1 Q.2 hβ hvQ W hW (mult Q) (hv Q hQ)
    rw [S.ordAt_nb _ _ _ hβ hvQ]
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero_iff _ (RingHom.injective _)).mpr
      hw0)] at h1
    exact_mod_cast h1
  have hvalid : ∀ Q ∈ T, Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1 := fun Q hQ ↦ (hT Q hQ).2
  have hsumT := S.degree_le' K hcop w hw0 hint T hvalid
  have hinf := S.elemW_ordInf (K := K) hcop W M hsupp hw0
  have hsumge : (M : ℤ) ≤ ∑ Q ∈ T, S.ordAt K w Q.1 Q.2 := by
    rw [← hM]; push_cast; exact Finset.sum_le_sum hge
  have heqT : ∀ Q ∈ T, S.ordAt K w Q.1 Q.2 = mult Q := by
    have hM' : (∑ Q ∈ T, (mult Q : ℤ)) = M := by exact_mod_cast hM
    have hsum0 : ∑ Q ∈ T, (S.ordAt K w Q.1 Q.2 - mult Q) = 0 := by
      rw [Finset.sum_sub_distrib, hM']; linarith
    intro Q hQ
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun Q hQ ↦ sub_nonneg.mpr (hge Q hQ))).mp hsum0 Q hQ
    linarith
  refine ⟨hw0, fun Q hQv ↦ ?_⟩
  by_cases hQ : Q ∈ T
  · rw [if_pos hQ, heqT Q hQ]
  · rw [if_neg hQ]
    have h1 := S.degree_le' K hcop w hw0 hint (insert Q T) (fun Q' hQ' ↦ by
      rcases Finset.mem_insert.mp hQ' with rfl | h
      · exact hQv
      · exact hvalid Q' h)
    rw [Finset.sum_insert hQ] at h1
    have h2 := hint Q.1 Q.2 hQv
    linarith

section Bridge

variable {F : Type*} [Field F] [DecidableEq F] (φ : F →+* C) (fK : CPoly F)
  (hpf : S.p = (toPoly fK).map φ) (hd : (toPoly fK).natDegree = fK.length - 1)
  (hcop : Nat.Coprime S.n S.p.natDegree) (hf0 : (toPoly fK).eval 0 = 1) (hnF : (S.n : F) ≠ 0)
include hpf hd hcop hf0 hnF

lemma natDegree_p : S.p.natDegree = fK.length - 1 := by
  rw [hpf, natDegree_map_eq_of_injective φ.injective, hd]

lemma p_eval_zero : S.p.eval 0 = 1 := by
  rw [hpf, eval_map, ← map_zero φ, eval₂_at_apply, hf0, map_one]

lemma images_one :
    (fun q : Fin 1 ↦ φ (![(0 : F)] q)) = ![(0 : C)] ∧ (fun q : Fin 1 ↦ φ (![(1 : F)] q)) = ![(1 : C)] :=
  ⟨funext fun q ↦ by fin_cases q; simp, funext fun q ↦ by fin_cases q; simp⟩

lemma hΓK_one : ∀ q : Fin 1, (S.n : F) * (![(1 : F)] q) ^ (S.n - 1) ≠ 0 ∧
    (![(1 : F)] q) ^ S.n = (toPoly fK).eval (![(0 : F)] q) := fun q ↦ by
  fin_cases q; simp [hnF, hf0]

open Classical in
/-- **No torsion over the code field ⇒ no torsion over `C`.** -/
theorem not_isPrincipalS_of
    (hnot : ∀ N, 1 ≤ N → ¬ PrincipalMulN (toPoly fK) S.n (fK.length - 1) ![(0 : F)] ![1] ![1] N) :
    ∀ N : ℕ, 0 < N → ¬ S.IsPrincipalS K (gammaP (1 : K)) N := by
  intro N hN hP
  apply hnot N hN
  have hp0 := S.p_eval_zero φ fK hpf hd hcop hf0 hnF
  have h1 := S.principalMulN_of_isPrincipalS (K := K) hcop ![(0 : C)] ![1] ![1]
    (fun a b _ ↦ Subsingleton.elim a b) (fun q ↦ by fin_cases q; simp)
    (fun q ↦ by fin_cases q; simp [hp0]) (gammaP (1 : K)) (fun Q _ ↦ by
      simp [gammaP, Fin.sum_univ_one]) N hP
  obtain ⟨e1, e2⟩ := S.images_one φ fK hpf hd hcop hf0 hnF
  refine principalMulN_descend φ (toPoly fK) S.hn (fK.length - 1) ![(0 : F)] ![1] ![1]
    (S.hΓK_one φ fK hpf hd hcop hf0 hnF) N ?_
  rw [e1, e2, ← hpf, ← S.natDegree_p φ fK hpf hd hcop hf0 hnF]
  exact h1

open Classical in
/-- **The torsion witness found over the code field has divisor `N (P₊ − ∞)` over `C`.** -/
theorem ordAt_witW (N : ℕ) (hN : 1 ≤ N) (Wb : BPoly F)
    (hW : witW fK S.n (fK.length - 1) ![(0 : F)] ![1] ![1] N = some Wb) :
    S.elemW ((toB Wb).map (mapRingHom φ)) ≠ 0 ∧ ∀ α β : K,
      β ^ S.n = (S.p.map (algebraMap C K)).eval α →
        S.ordAt K (S.elemW ((toB Wb).map (mapRingHom φ))) α β = N * gammaP (1 : K) (α, β) := by
  obtain ⟨hW0, hWs, hWv⟩ := witW_spec fK S.n S.hn (fK.length - 1) ![(0 : F)] ![1] ![1] N
    (S.hΓK_one φ fK hpf hd hcop hf0 hnF) hW
  have hdeg := S.natDegree_p φ fK hpf hd hcop hf0 hnF
  set W := (toB Wb).map (mapRingHom φ) with hWdef
  have hWne : W ≠ 0 := by
    rw [hWdef]; exact (Polynomial.map_ne_zero_iff (Polynomial.map_injective φ φ.injective)).mpr hW0
  have hsupp : ∀ i a, (W.coeff i).coeff a ≠ 0 → i < S.n ∧ S.n * a + S.p.natDegree * i ≤ N := by
    intro i a h
    rw [hWdef, coeff_map, coe_mapRingHom, coeff_map] at h
    have h' : ((toB Wb).coeff i).coeff a ≠ 0 := fun h0 ↦ h (by rw [h0, map_zero])
    have := hWs i a h'
    simpa [hdeg] using this
  set ψ := (algebraMap C K).comp φ
  have hv0 := vanishAtN_map ψ (hWv 0)
  have hpK : (toPoly fK).map ψ = S.p.map (algebraMap C K) := by
    rw [hpf, Polynomial.map_map]
  have hWK : (toB Wb).map (mapRingHom ψ) = W.map (mapRingHom (algebraMap C K)) := by
    rw [hWdef, Polynomial.map_map, ← mapRingHom_comp]
  rw [hpK, hWK] at hv0
  simp only [Matrix.cons_val_fin_one, map_zero, map_one, Finset.univ_unique, Finset.sum_singleton,
    mul_one] at hv0
  have hcert := S.ordAt_elemW_cert (K := K) hcop W hWne N hsupp {((0 : K), (1 : K))} (fun _ ↦ N)
    (fun Q hQ ↦ by
      rw [Finset.mem_singleton] at hQ
      subst hQ
      refine ⟨one_ne_zero, ?_⟩
      rw [one_pow, eval_zero_map, S.p_eval_zero φ fK hpf hd hcop hf0 hnF, map_one])
    (by simp) (fun Q hQ ↦ by
      rw [Finset.mem_singleton] at hQ
      subst hQ
      simpa using hv0)
  refine ⟨hcert.1, fun α β hv ↦ ?_⟩
  rw [hcert.2 (α, β) hv]
  simp [gammaP]

end Bridge

end SuperData

end Differential
