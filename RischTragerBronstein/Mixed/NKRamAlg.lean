import RischTragerBronstein.Mixed.NKRamExpand

/-!
# Triangular gauges from a level structure

Over a differential field `K`, index the jets of the places at infinity by `(h, k) ∈ Fin e × Fin r`
(level `h`, place `k`). If a matrix `Z` is block upper triangular in the levels
(`Z (R, k) (h, k') = 0` for `h < R`) with diagonal blocks `diag(d R k)` (`d ≠ 0`), and
`T Z = Z′ − Z D` (`D` diagonal, depending on the level), then `T` is block upper triangular with
diagonal blocks `diag(d′/d − D)` (`tri_of_TZ`), and `Z` has trivial left kernel (`inj_of_Z`).
-/

open Differential

set_option linter.unusedSectionVars false

namespace Curves

section RamAlg

variable {K : Type*} [Field K] [Differential K] {e r : ℕ}

/-- **`y Z = 0 ⇒ y = 0`** for a level-triangular `Z` with invertible diagonal. -/
theorem inj_of_Z (Z : Matrix (Fin e × Fin r) (Fin e × Fin r) K) (d : Fin e → Fin r → K)
    (hd : ∀ R k, d R k ≠ 0)
    (hZlow : ∀ (R h : Fin e) (k k' : Fin r), h < R → Z (R, k) (h, k') = 0)
    (hZdiag : ∀ (R : Fin e) (k k' : Fin r), Z (R, k) (R, k') = if k = k' then d R k else 0)
    (y : Fin e × Fin r → K) (hy : ∀ b, ∑ c, y c * Z c b = 0) : y = 0 := by
  classical
  have key : ∀ h : ℕ, ∀ (H : Fin e) (k' : Fin r), (H : ℕ) = h → y (H, k') = 0 := by
    intro h
    induction h using Nat.strong_induction_on with
    | _ h ih =>
      intro H k' hH
      have h1 := hy (H, k')
      rw [Fintype.sum_prod_type] at h1
      rw [Finset.sum_eq_single H] at h1
      · rw [Finset.sum_eq_single k'] at h1
        · rw [hZdiag, if_pos rfl] at h1
          exact (mul_eq_zero.mp h1).resolve_right (hd H k')
        · intro k _ hk; rw [hZdiag, if_neg hk, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro R _ hR
        refine Finset.sum_eq_zero fun k _ ↦ ?_
        rcases lt_or_gt_of_ne hR with hlt | hgt
        · rw [ih R (by rw [← hH]; exact hlt) R k rfl, zero_mul]
        · rw [hZlow R H k k' hgt, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  funext c
  exact key c.1 c.1 c.2 rfl

/-- **`T` is level-triangular with diagonal `d′/d − D`** when `T Z = Z′ − Z D`. -/
theorem tri_of_TZ (T Z : Matrix (Fin e × Fin r) (Fin e × Fin r) K) (D : Fin e → K)
    (d : Fin e → Fin r → K) (hd : ∀ R k, d R k ≠ 0)
    (hZlow : ∀ (R h : Fin e) (k k' : Fin r), h < R → Z (R, k) (h, k') = 0)
    (hZdiag : ∀ (R : Fin e) (k k' : Fin r), Z (R, k) (R, k') = if k = k' then d R k else 0)
    (hTZ : ∀ a b, ∑ c, T a c * Z c b = (Z a b)′ - Z a b * D b.1) :
    (∀ a b, b.1 < a.1 → T a b = 0) ∧
      ∀ (R : Fin e) (k k' : Fin r),
        T (R, k) (R, k') = if k = k' then (d R k)′ / d R k - D R else 0 := by
  classical
  -- the lower part, by induction on the column level
  have hlow : ∀ h : ℕ, ∀ (H : Fin e) (k' : Fin r), (H : ℕ) = h → ∀ a, H < a.1 → T a (H, k') = 0 := by
    intro h
    induction h using Nat.strong_induction_on with
    | _ h ih =>
      intro H k' hH a ha
      have h1 := hTZ a (H, k')
      have hz : Z a (H, k') = 0 := by
        obtain ⟨R, k⟩ := a
        exact hZlow R H k k' ha
      rw [hz, Derivation.map_zero, zero_mul, sub_zero, Fintype.sum_prod_type,
        Finset.sum_eq_single H] at h1
      · rw [Finset.sum_eq_single k'] at h1
        · rw [hZdiag, if_pos rfl] at h1
          exact (mul_eq_zero.mp h1).resolve_right (hd H k')
        · intro k _ hk; rw [hZdiag, if_neg hk, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro R _ hR
        refine Finset.sum_eq_zero fun k _ ↦ ?_
        rcases lt_or_gt_of_ne hR with hlt | hgt
        · rw [ih R (by rw [← hH]; exact hlt) R k rfl a (lt_trans hlt ha), zero_mul]
        · rw [hZlow R H k k' hgt, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hlow' : ∀ a b, b.1 < a.1 → T a b = 0 := fun a b hb ↦ hlow b.1 b.1 b.2 rfl a hb
  refine ⟨hlow', fun R k k' ↦ ?_⟩
  have h1 := hTZ (R, k) (R, k')
  rw [hZdiag, Fintype.sum_prod_type, Finset.sum_eq_single R] at h1
  · rw [Finset.sum_eq_single k'] at h1
    · rw [hZdiag, if_pos rfl] at h1
      split_ifs at h1 ⊢ with hkk
      · subst hkk
        field_simp [hd R k]
        linear_combination h1
      · rw [Derivation.map_zero, zero_mul, sub_zero] at h1
        exact (mul_eq_zero.mp h1).resolve_right (hd R k')
    · intro k'' _ hk; rw [hZdiag, if_neg hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro R' _ hR
    refine Finset.sum_eq_zero fun k'' _ ↦ ?_
    rcases lt_or_gt_of_ne hR with hlt | hgt
    · rw [hlow' (R, k) (R', k'') hlt, zero_mul]
    · rw [hZlow R' R k'' k' hgt, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end RamAlg

end Curves
