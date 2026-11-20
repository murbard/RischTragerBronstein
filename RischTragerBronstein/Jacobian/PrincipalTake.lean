import RischTragerBronstein.Jacobian.PrincipalTest

/-! `principalC_sound` with the explicit function `(full.take A, full.drop A)`. -/

open Polynomial CPoly

namespace Jac

variable {F : Type*} [Field F] [DecidableEq F]

theorem principalC_sound_take (f : CPoly F) (Γ : EDiv F) (A B : ℕ)
    (hΓ : ∀ q ∈ Γ, 2 * q.2.1 ≠ 0 ∧ q.2.1 ^ 2 = (toPoly f).eval q.1) {j : ℕ} {cs : List F}
    (h : principalC f Γ A B = some (j, cs)) :
    ((toPoly ((cs.set j 1).take A), toPoly ((cs.set j 1).drop A)) : F[X] × F[X]) ≠ (0, 0) ∧
      (toPoly ((cs.set j 1).take A)).degree < A ∧ (toPoly ((cs.set j 1).drop A)).degree < B ∧
      Vanishes (toPoly f) (toPoly ((cs.set j 1).take A), toPoly ((cs.set j 1).drop A)) Γ := by
  classical
  obtain ⟨j', hj', hjs⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨cs', hcs', he⟩ := Option.map_eq_some_iff.mp hjs
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hjA : j' < A + B := List.mem_range.mp hj'
  set cols := colsC f Γ A B
  obtain ⟨hlen, hlc⟩ := linSolve_sound _ _ _ hcs'
  rw [List.length_set, length_colsC] at hlen
  set full := cs'.set j' 1
  have hfl : full.length = A + B := by simp [full, hlen]
  have h0 : lcombS (RingHom.id F) full cols = 0 := by
    rw [lcombS_set (RingHom.id F) cs' cols j' 1 (by rw [hlen, length_colsC])
      (by rw [length_colsC]; exact hjA), lcombS_id, hlc]
    simp
  rw [show cols = (basisC A B).map (colOf f Γ) from rfl, lcombS_eq_colSem] at h0
  simp only [Polynomial.map_id, List.map_id', RingHom.id_apply] at h0
  set ψ : F[X] × F[X] := (lsum full ((basisC A B).map fun e ↦ toPoly e.1),
    lsum full ((basisC A B).map fun e ↦ toPoly e.2))
  have hc1 : ∀ t, ψ.1.coeff t = if t < A then full.getD t 0 else 0 := fun t ↦ by
    have := lsum_basis_fst (RingHom.id F) A B full hfl t; simpa using this
  have hc2 : ∀ t, ψ.2.coeff t = if t < B then full.getD (A + t) 0 else 0 := fun t ↦ by
    have := lsum_basis_snd (RingHom.id F) A B full hfl t; simpa using this
  have hfj : full.getD j' 0 = 1 := by
    simp [full, List.getD_eq_getElem?_getD, List.getElem?_set, hlen, hjA]
  have hψeq : ψ = (toPoly (full.take A), toPoly (full.drop A)) := by
    refine Prod.ext (Polynomial.ext fun t ↦ ?_) (Polynomial.ext fun t ↦ ?_)
    · rw [hc1, coeff_toPoly]
      split_ifs with ht
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt ht]
      · rw [List.getD_eq_default]; simp; omega
    · rw [hc2, coeff_toPoly]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
      split_ifs with ht
      · rfl
      · rw [List.getElem?_eq_none (by rw [hfl]; omega)]; rfl
  rw [show toPoly (full.take A) = ψ.1 from (congrArg Prod.fst hψeq).symm,
    show toPoly (full.drop A) = ψ.2 from (congrArg Prod.snd hψeq).symm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hψ
    by_cases hjA' : j' < A
    · have := hc1 j'; rw [if_pos hjA', hfj, show ψ.1 = 0 from congrArg Prod.fst hψ] at this
      simp at this
    · have := hc2 (j' - A)
      rw [if_pos (by omega), show A + (j' - A) = j' by omega, hfj,
        show ψ.2 = 0 from congrArg Prod.snd hψ] at this
      simp at this
  · refine (degree_lt_iff_coeff_zero _ _).mpr fun t ht ↦ ?_
    rw [hc1, if_neg (by exact_mod_cast not_lt.mpr ht)]
  · refine (degree_lt_iff_coeff_zero _ _).mpr fun t ht ↦ ?_
    rw [hc2, if_neg (by exact_mod_cast not_lt.mpr ht)]
  · intro q hq
    obtain ⟨i, rfl⟩ := List.get_of_mem hq
    have h0' : colSem Γ ((branchesC f Γ).map toPoly) ψ.1 ψ.2 = 0 := by
      convert h0 using 2
      simp
    have hz := (colSem_zero_iff Γ ((branchesC f Γ).map toPoly) ψ.1 ψ.2
      (by simp [branchesC])).mp h0' ⟨i, by simpa using i.2⟩
    obtain ⟨h2, hy⟩ := hΓ _ (List.get_mem _ _)
    refine ⟨_, (branchC_spec f _ _ h2 hy _).mono (Nat.le_succ _), ?_⟩
    simpa [branchesC] using hz


end Jac
