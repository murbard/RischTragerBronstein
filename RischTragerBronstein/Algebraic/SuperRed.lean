import RischTragerBronstein.Computable.RDEPoly
import RischTragerBronstein.Computable.EuclidDegree

/-!
# The reduction `B yʲ / p ↦ (C yʲ)′ + B₀ yʲ / p` for `yⁿ = p` (computable)

For `yⁿ = p` and `r = j / n`, `(C yʲ)′ = (C′ p + r C p′) yʲ / p`. `supRed p r B = (C, B₀)` with
`B = C′ p + r C p′ + B₀` and `deg B₀ ≤ deg p - 2` (`supRed_spec`), as long as `k + r deg p ≠ 0`
for every `k : ℕ` (e.g. `r > 0`). This generalises `supRed` (`r = 1/2`).
-/

open Polynomial

namespace CPoly

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] [DecidableEq 𝕜]

/-- `C′ p + r C p′`. -/
def supR (r : 𝕜) (p c : CPoly 𝕜) : CPoly 𝕜 := add (mul (deriv c) p) (smul r (mul c (deriv p)))

lemma toPoly_supR (r : 𝕜) (p c : CPoly 𝕜) : toPoly (supR r p c) =
    derivative (toPoly c) * toPoly p + C r * (toPoly c * derivative (toPoly p)) := by
  simp [supR]

/-- One step: cancel the coefficient of degree `k + n - 1`. -/
def supStep (r : 𝕜) (p : CPoly 𝕜) (n : ℕ) (lc : 𝕜) (acc : CPoly 𝕜 × CPoly 𝕜) (k : ℕ) :
    CPoly 𝕜 × CPoly 𝕜 :=
  let t := acc.2.getD (k + n - 1) 0 / ((k + n * r : 𝕜) * lc)
  (add acc.1 (monomial k t), sub acc.2 (supR r p (monomial k t)))

/-- **The reduction**: `(C, B₀)` with `B = C′ p + r C p′ + B₀`, `deg B₀ ≤ deg p - 2`. -/
def supRed (r : 𝕜) (p B : CPoly 𝕜) : CPoly 𝕜 × CPoly 𝕜 :=
  ((List.range (B.length + 1)).reverse).foldl (supStep r p ((trim p).length - 1) (lead (trim p)))
    ([], B)

/-- The coefficients of `C′ p + r C p′` for `C = xᵏ`. -/
lemma coeff_supR_monomial (r : 𝕜) (P : 𝕜[X]) (n : ℕ) (hn : P.natDegree = n) (hn1 : 1 ≤ n) (k : ℕ)
    (t : 𝕜) (j : ℕ) (hj : k + n - 1 ≤ j) :
    (derivative (C t * X ^ k) * P + C r * (C t * X ^ k * derivative P)).coeff j =
      if j = k + n - 1 then t * ((k + n * r : 𝕜) * P.leadingCoeff) else 0 := by
  have hd : derivative (C t * X ^ k) = C (t * k) * X ^ (k - 1) := by
    rw [derivative_C_mul_X_pow]
  rw [hd, coeff_add, show C (t * k) * X ^ (k - 1) * P = C (t * k) * (X ^ (k - 1) * P) by ring,
    coeff_C_mul, show C r * (C t * X ^ k * derivative P) =
      C (t * r) * (X ^ k * derivative P) by rw [C_mul]; ring,
    coeff_C_mul]
  have hdp : (derivative P).natDegree ≤ n - 1 := by
    have := natDegree_derivative_le P; omega
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [Nat.cast_zero, mul_zero, zero_mul, pow_zero, one_mul, zero_add, zero_sub]
    split_ifs with hjn
    · rw [hjn, coeff_derivative, Nat.sub_add_cancel hn1, ← hn, Nat.cast_sub (hn ▸ hn1)]
      simp only [Nat.cast_one, sub_add_cancel, leadingCoeff]
      ring
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; ring
  · split_ifs with hjn
    · have h1 : (X ^ (k - 1) * P).coeff j = P.leadingCoeff := by
        rw [coeff_X_pow_mul', if_pos (by omega), show j - (k - 1) = P.natDegree by omega]; rfl
      have h2 : (X ^ k * derivative P).coeff j = P.leadingCoeff * n := by
        rw [coeff_X_pow_mul', if_pos (by omega), show j - k = n - 1 by omega, coeff_derivative,
          Nat.sub_add_cancel hn1, ← hn, Nat.cast_sub (hn ▸ hn1)]
        simp only [Nat.cast_one, sub_add_cancel]; rfl
      rw [h1, h2]; ring
    · have h1 : (X ^ (k - 1) * P).coeff j = 0 := by
        rw [coeff_X_pow_mul']
        split_ifs
        · exact coeff_eq_zero_of_natDegree_lt (by omega)
        · rfl
      have h2 : (X ^ k * derivative P).coeff j = 0 := by
        rw [coeff_X_pow_mul']
        split_ifs
        · exact coeff_eq_zero_of_natDegree_lt (by omega)
        · rfl
      rw [h1, h2]; ring

/-- The fold invariant. -/
lemma supRed_fold (r : 𝕜) (p B : CPoly 𝕜) (n : ℕ) (hn : (toPoly p).natDegree = n) (hn1 : 1 ≤ n)
    (hr : ∀ k : ℕ, (k : 𝕜) + n * r ≠ 0)
    (hlc : lead (trim p) = (toPoly p).leadingCoeff) (hn' : (trim p).length - 1 = n) :
    ∀ (l : List ℕ) (acc : CPoly 𝕜 × CPoly 𝕜) (K : ℕ),
      toPoly B = toPoly (supR r p acc.1) + toPoly acc.2 →
      (∀ j, K + n ≤ j → (toPoly acc.2).coeff j = 0) →
      l = (List.range (K + 1)).reverse →
      toPoly B = toPoly (supR r p (l.foldl (supStep r p ((trim p).length - 1) (lead (trim p)))
          acc).1) + toPoly (l.foldl (supStep r p ((trim p).length - 1) (lead (trim p))) acc).2 ∧
        ∀ j, n - 1 ≤ j → (toPoly (l.foldl (supStep r p ((trim p).length - 1)
          (lead (trim p))) acc).2).coeff j = 0 := by
  intro l
  induction l with
  | nil =>
    intro acc K _ _ hl
    have := congrArg List.length hl
    simp at this
  | cons k l ih =>
    intro acc K hB hz hl
    have hkK : k = K := by
      have := congrArg List.head? hl
      simp [List.range_succ] at this
      exact this
    subst hkK
    rw [List.foldl_cons]
    have hlc0 : (toPoly p).leadingCoeff ≠ 0 := by
      rw [Ne, leadingCoeff_eq_zero]; intro h; rw [h] at hn; simp at hn; omega
    set t := acc.2.getD (k + n - 1) 0 / ((k + n * r : 𝕜) * (toPoly p).leadingCoeff) with ht
    have hstep : supStep r p ((trim p).length - 1) (lead (trim p)) acc k =
        (add acc.1 (monomial k t), sub acc.2 (supR r p (monomial k t))) := by
      simp only [supStep, hn', hlc, ht]
    have hB' : toPoly B =
        toPoly (supR r p (supStep r p ((trim p).length - 1) (lead (trim p)) acc k).1) +
        toPoly (supStep r p ((trim p).length - 1) (lead (trim p)) acc k).2 := by
      rw [hstep, hB]
      simp only [toPoly_supR, toPoly_add, toPoly_sub, derivative_add]
      ring
    have hkn : ((k : 𝕜) + n * r) * (toPoly p).leadingCoeff ≠ 0 := mul_ne_zero (hr k) hlc0
    have hz' : ∀ j, k + n - 1 ≤ j →
        (toPoly (supStep r p ((trim p).length - 1) (lead (trim p)) acc k).2).coeff j = 0 := by
      intro j hj
      rw [hstep, toPoly_sub, coeff_sub, toPoly_supR, toPoly_monomial,
        coeff_supR_monomial r _ n hn hn1 k t j hj]
      split_ifs with hjn
      · rw [coeff_toPoly, hjn, ht, div_mul_cancel₀ _ hkn, sub_self]
      · rw [hz j (by omega), sub_zero]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      have hl0 : l = [] := by
        have := congrArg List.tail hl; simpa using this.symm
      subst hl0
      exact ⟨hB', fun j hj ↦ hz' j (by omega)⟩
    · obtain ⟨K', rfl⟩ : ∃ K', k = K' + 1 := ⟨k - 1, by omega⟩
      have hl' : l = (List.range (K' + 1)).reverse := by
        have := congrArg List.tail hl
        simp [List.range_succ] at this
        rw [this, List.range_succ, List.reverse_append]
        rfl
      exact ih _ K' hB' (fun j hj ↦ hz' j (by omega)) hl'

/-- **Specification of the reduction** (for `deg p ≥ 1`). -/
theorem supRed_spec (r : 𝕜) (p B : CPoly 𝕜) (hp1 : 1 ≤ (toPoly p).natDegree)
    (hr : ∀ k : ℕ, (k : 𝕜) + (toPoly p).natDegree * r ≠ 0) :
    toPoly B = derivative (toPoly (supRed r p B).1) * toPoly p +
        C r * (toPoly (supRed r p B).1 * derivative (toPoly p)) + toPoly (supRed r p B).2 ∧
      (toPoly (supRed r p B).2 = 0 ∨
        (toPoly (supRed r p B).2).natDegree + 2 ≤ (toPoly p).natDegree) := by
  have htr : trim p ≠ [] := by
    intro h
    rw [trim_eq_nil_iff] at h
    rw [h] at hp1; simp at hp1
  obtain ⟨hdeg, hlc, -⟩ := natDegree_toPoly_of_trim_ne_nil htr
  set n := (toPoly p).natDegree
  have hlc' : lead (trim p) = (toPoly p).leadingCoeff := by rw [← hlc, ← hdeg]; rfl
  obtain ⟨h1, h2⟩ := supRed_fold r p B n rfl hp1 hr hlc' hdeg.symm _ ([], B) B.length
    (by simp [toPoly_supR]) (fun j hj ↦ by rw [coeff_toPoly]; exact List.getD_eq_default _ _ (show B.length ≤ j by omega))
    rfl
  refine ⟨?_, ?_⟩
  · rw [supRed]; rw [toPoly_supR] at h1; exact h1
  · by_cases h0 : toPoly (supRed r p B).2 = 0
    · exact Or.inl h0
    · right
      have := h2 ((toPoly (supRed r p B).2).natDegree) |> mt
      by_contra hlt
      apply h0
      have hne := leadingCoeff_ne_zero.mpr h0
      exact absurd (h2 _ (by omega)) hne

end CPoly
