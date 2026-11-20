import RischTragerBronstein.Mixed.KRZSem
import RischTragerBronstein.Mixed.KRClassN

/-!
# Radicals over an exponential level: the twisted curve over `Kₘ(ζ)`

With `z`, `κ = zⁿ a₀`, `s = ⁿ√κ` (constant) and a primitive `n`-th root `ω ∈ Fₘ`, the scale
`μ₀ = z/s` twists `yⁿ = A` into `ỹⁿ = μ₀ⁿ A = Â`, the image of `krFK` under `psiNF ω`
(`kr_hpf`); `Â(0) = 1`, so the points `(0, ζᵏ)` of the twist are rational over `Kₘ(ζ)` and
correspond to the points `(0, ωᵏ/μ₀)` of `yⁿ = A`. The reductions of `Kₘ(ζ)` are valid
(`redAtNF_valid`).
-/

open Polynomial Differential IntermediateField CPoly

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

omit [CharZero L] in
lemma fK_factsN {K C' : Type*} [Field K] [DecidableEq K] [Field C'] (φ : K →+* C') (fK : CPoly K)
    (htrim : CPoly.trim fK = fK) (p : C'[X]) (hpf : p = (toPoly fK).map φ) (hp0 : p ≠ 0)
    (hsq : Squarefree p) (n : ℕ) (hcop : Nat.Coprime n p.natDegree) :
    (toPoly fK).natDegree = fK.length - 1 ∧ Squarefree (toPoly fK) ∧
      Nat.Coprime n (fK.length - 1) := by
  have hne : toPoly fK ≠ 0 := fun h0 ↦ hp0 (by rw [hpf, h0, Polynomial.map_zero])
  have htne : CPoly.trim fK ≠ [] := fun h0 ↦ hne ((CPoly.trim_eq_nil_iff fK).mp h0)
  have hlen := CPoly.length_trim htne
  rw [htrim] at hlen
  have hdeg : (toPoly fK).natDegree = fK.length - 1 := by omega
  have hpdeg : p.natDegree = (toPoly fK).natDegree := by
    rw [hpf, natDegree_map_eq_of_injective φ.injective]
  exact ⟨hdeg, MTower.squarefree_of_map φ _ (hpf ▸ hsq), by rw [← hdeg, ← hpdeg]; exact hcop⟩

namespace MTower

variable (T : MTower Fc ks Cc L)

section Twist

variable [Fact (Irreducible (toPoly (fKc Fc)))]
variable (m : ℕ) (hm : T.Tr m) (n : ℕ) (hn : 0 < n) [Fact (Irreducible (toPoly (cycK Fc m n)))]
  (ω : T.F m) (hω : IsPrimitiveRoot ω n)

lemma toPoly_map_embNF (l : CPoly (KF Fc m)) :
    (toPoly (l.map (embNF Fc m n))).map (T.psiNF m hm n hn ω hω) = (toPoly l).map (T.psiF m hm) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, toPoly_cons, toPoly_cons, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X, ih, T.psiNF_embNF, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X]

/-- **The twist**: `C(μ₀ⁿ) · A = krFK` read through `psiNF ω`, with `μ₀ⁿ = zⁿ/κ`. -/
lemma kr_hpf (A : GPoly (LC m)) (z : LC m) (κ : ℚ) :
    Polynomial.C ((T.MP m hm).sem (powC (MO Fc ks m) z n) * ((κ⁻¹ : ℚ) : T.F m)) *
      GPoly.toPoly (T.MP m hm) A =
      (toPoly (krFK Fc ks m n A z κ)).map (T.psiNF m hm n hn ω hω) := by
  rw [krFK, toPoly_trim, T.toPoly_map_embNF m hm n hn ω hω, T.toPoly_trC_map m hm]
  have e : krAh Fc ks m n A z κ = GPoly.smul (MO Fc ks m)
      ((MO Fc ks m).mul (powC (MO Fc ks m) z n) (mcst Fc ks m κ⁻¹)) A := rfl
  rw [e, GPoly.toPoly_smul, (T.MP m hm).sem_mul, T.sem_mcst]

/-- **The reductions of `Kₘ(ζ)` are induced by embeddings.** -/
theorem redAtNF_valid (rs : ℕ → ℕ) (p : ℕ) [Fact p.Prime] (R : RedFns p (NFz Fc m n))
    (h : redAtNF Fc m n rs p = some R) : ∃ φ : NFz Fc m n →+* ℚ_[p], RedValid p R φ := by
  unfold redAtNF at h
  rw [dif_pos (Fact.out)] at h
  split at h
  · exact absurd h (by simp)
  · rename_i R0 hR0
    split_ifs at h with hok
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
    have hb := List.find?_some hi
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hb
    obtain ⟨φ, hφ⟩ := redAtKF_valid Fc m rs p R0 hR0
    exact nfkFns_exists R0 φ hφ (cycK Fc m n) (List.all_eq_true.mp hok) _ hb.1 hb.2

end Twist

end MTower

end Curves.MT
