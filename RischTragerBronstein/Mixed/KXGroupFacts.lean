import RischTragerBronstein.Mixed.KXDepConj

/-!
# From `PrincipalMulN` on an augmented point set to principal divisors

`isPrincipalS_class_of_pm` / `isPrincipalS_P0_of_pm`: the `PrincipalMulN` produced by a group
relation (`pm_of_group`) with `μ = 0` (resp. no class points) makes a multiple of the class divisor
`Γ_k` (resp. of `P₊`) principal — contradicting the non-torsion answers of the oracles.
-/

open Polynomial IntermediateField Sup CPoly Classical

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K] [IsAlgClosed K]
variable (S : SuperData C L)

lemma gammaQ_mul {r : ℕ} (a b : Fin r → C) (mq : Fin r → ℕ) (N : ℕ) (Q : K × K) :
    gammaQ a b (fun q ↦ N * mq q) Q = N * gammaQ a b mq Q := by
  simp only [gammaQ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ ↦ by split_ifs <;> simp

lemma gammaQ_zero {r : ℕ} (a b : Fin r → C) (Q : K × K) :
    gammaQ a b (fun _ ↦ 0) Q = 0 := by
  simp [gammaQ]

section Conj

variable (hn2 : S.n = 2) (hcop : Nat.Coprime S.n S.p.natDegree)
  {r : ℕ} (a b : Fin r → C) (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0)
  (hb : ∀ i, b i ≠ 0 ∧ b i ^ S.n = S.p.eval (a i)) (mq : Fin r → ℕ)

include hn2 hcop ha ha0 hb in
/-- **`μ = 0`: a multiple of the class divisor is principal.** -/
lemma isPrincipalS_class_of_pm (σ : C) (hσ0 : σ ≠ 0) (hσ : σ ^ S.n = S.p.eval 0) (N : ℕ)
    (hP : PrincipalMulN S.p S.n S.p.natDegree (Fin.cons 0 a) (Fin.cons σ b)
      (Fin.cons 0 fun q ↦ N * mq q) 1) :
    S.IsPrincipalS K (gammaQ a b mq) N := by
  obtain ⟨w, hw0, hwo⟩ := S.fun_of_principalMulN (K := K) hn2 hcop a b ha ha0 hb _ σ hσ0 hσ 0 hP
  refine ⟨w, hw0, fun α β' hv ↦ by rw [hwo α β' hv]; positivity, fun Q hv ↦ ?_⟩
  rw [hwo Q.1 Q.2 hv, gammaQ_cons, gammaQ_mul]
  simp

include hn2 hcop ha ha0 hb in
/-- **No class points: a multiple of `P₊` is principal.** -/
lemma isPrincipalS_P0_of_pm (σ : C) (hσ0 : σ ≠ 0) (hσ : σ ^ S.n = S.p.eval 0) (M : ℕ)
    (hP : PrincipalMulN S.p S.n S.p.natDegree (Fin.cons 0 a) (Fin.cons σ b)
      (Fin.cons M fun _ ↦ 0) 1) :
    S.IsPrincipalS K (gammaQ (fun _ : Fin 1 ↦ (0 : C)) (fun _ ↦ σ) (fun _ ↦ 1)) M := by
  obtain ⟨w, hw0, hwo⟩ := S.fun_of_principalMulN (K := K) hn2 hcop a b ha ha0 hb _ σ hσ0 hσ M hP
  refine ⟨w, hw0, fun α β' hv ↦ by rw [hwo α β' hv]; positivity, fun Q hv ↦ ?_⟩
  rw [hwo Q.1 Q.2 hv, gammaQ_cons, gammaQ_zero]
  simp [gammaQ, gammaP]

end Conj

end SuperData

end Differential
