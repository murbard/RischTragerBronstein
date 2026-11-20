import RischTragerBronstein.Algebraic.SuperPrincipal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Counting the monomials `xᵃ yⁱ` of bounded pole order (Riemann's inequality)

For `gcd(n, d) = 1`, `∑_{i<n} (⌊(M − d i)/n⌋ + 1) = M + 1 − g` with `2g = (n − 1)(d − 1)`
(`sum_floor`), since `i ↦ (M − d i) mod n` permutes the residues. Hence the number of monomials
`xᵃ yⁱ` (`i < n`) with `n a + d i ≤ M` is at least `M + 1 − g` (`card_basisN`).
-/

open Polynomial

namespace Sup

/-- `i ↦ (M − d i) mod n` permutes `{0, …, n − 1}`. -/
lemma sum_emod_perm (n d : ℕ) (hn : 0 < n) (hcop : Nat.Coprime n d) (M : ℤ) :
    ∑ i ∈ Finset.range n, (M - d * i) % (n : ℤ) = ∑ r ∈ Finset.range n, (r : ℤ) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  refine Finset.sum_nbij' (fun i ↦ ((M - d * i) % n).toNat)
    (fun r ↦ ((((d : ZMod n)⁻¹ * ((M : ZMod n) - r)) : ZMod n).val)) ?_ ?_ ?_ ?_ ?_
  · intro i _
    rw [Finset.mem_range]
    have h1 := Int.emod_lt_of_pos (M - d * i) hn'
    have h2 := Int.emod_nonneg (M - d * i) hn'.ne'
    omega
  · intro r _
    rw [Finset.mem_range]
    haveI : NeZero n := ⟨hn.ne'⟩
    exact ZMod.val_lt _
  · intro i hi
    haveI : NeZero n := ⟨hn.ne'⟩
    have hi' := Finset.mem_range.mp hi
    have hdu : IsUnit (d : ZMod n) := (ZMod.unitOfCoprime d hcop.symm).isUnit
    have hcast : (((M - d * i) % n).toNat : ZMod n) = (M : ZMod n) - d * i := by
      have h2 := Int.emod_nonneg (M - d * i) hn'.ne'
      have : ((((M - d * i) % n).toNat : ℤ) : ZMod n) = ((M - d * i : ℤ) : ZMod n) := by
        rw [Int.toNat_of_nonneg h2, ZMod.intCast_mod]
      push_cast at this
      exact this
    rw [hcast, sub_sub_cancel, ← mul_assoc, ZMod.inv_mul_of_unit _ hdu, one_mul,
      ZMod.val_natCast, Nat.mod_eq_of_lt hi']
  · intro r hr
    haveI : NeZero n := ⟨hn.ne'⟩
    have hr' := Finset.mem_range.mp hr
    have hdu : IsUnit (d : ZMod n) := (ZMod.unitOfCoprime d hcop.symm).isUnit
    set v := ((((d : ZMod n)⁻¹ * ((M : ZMod n) - r)) : ZMod n).val)
    have hv : ((v : ℕ) : ZMod n) = (d : ZMod n)⁻¹ * ((M : ZMod n) - r) := ZMod.natCast_zmod_val _
    have hmod : ((M - d * v : ℤ) : ZMod n) = (r : ZMod n) := by
      push_cast
      rw [hv, ← mul_assoc, ZMod.mul_inv_of_unit _ hdu, one_mul]; ring
    have := (ZMod.intCast_eq_intCast_iff' (M - d * v) r n).mp (by push_cast at hmod ⊢; exact hmod)
    rw [this, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hr')]
    simp
  · intro i hi
    have h2 := Int.emod_nonneg (M - d * i) hn'.ne'
    rw [Int.toNat_of_nonneg h2]

/-- **The floor-sum identity.** -/
theorem sum_floor (n d : ℕ) (hn : 0 < n) (hcop : Nat.Coprime n d) (M : ℤ) :
    2 * ∑ i ∈ Finset.range n, ((M - d * i) / (n : ℤ) + 1) = 2 * M + 2 - (n - 1) * (d - 1) := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdecomp : ∀ i : ℕ, (M - d * i) = n * ((M - d * i) / n) + (M - d * i) % n := fun i ↦
    (Int.mul_ediv_add_emod _ _).symm
  have hsum : ∑ i ∈ Finset.range n, (M - d * i) =
      n * ∑ i ∈ Finset.range n, ((M - d * i) / n) + ∑ i ∈ Finset.range n, ((M - d * i) % n) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ hdecomp i
  rw [sum_emod_perm n d hn hcop M] at hsum
  have h1 : ∑ i ∈ Finset.range n, (M - d * (i : ℤ)) = n * M - d * ∑ i ∈ Finset.range n, (i : ℤ) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; simp
  have h2 : 2 * ∑ i ∈ Finset.range n, (i : ℤ) = n * (n - 1) := by
    have := Finset.sum_range_id_mul_two n
    have h3 : (∑ i ∈ Finset.range n, (i : ℤ)) = ((∑ i ∈ Finset.range n, i : ℕ) : ℤ) := by
      push_cast; rfl
    rw [h3]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · have : ((∑ i ∈ Finset.range n, i) * 2 : ℕ) = n * (n - 1) := this
      zify [show 1 ≤ n by omega] at this
      linarith
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have key : (n : ℤ) * (2 * ∑ i ∈ Finset.range n, ((M - d * i) / n)) =
      n * (2 * M - (d + 1) * (n - 1)) := by
    have := congrArg (fun z ↦ 2 * z) hsum
    rw [h1] at this
    nlinarith [h2]
  have key' := mul_left_cancel₀ hn' key
  nlinarith [key']

lemma basisN_toFinset (n d M : ℕ) :
    (basisN n d M).toFinset = ((Finset.range (M + 1)) ×ˢ (Finset.range n)).filter
      fun ai ↦ n * ai.1 + d * ai.2 ≤ M := by
  ext ⟨a, i⟩
  simp [basisN]

lemma count_row (n d M i : ℕ) (hn : 0 < n) :
    ((M : ℤ) - d * i) / n + 1 ≤ (((Finset.range (M + 1)).filter fun a ↦ n * a + d * i ≤ M).card : ℤ) := by
  by_cases hdi : d * i ≤ M
  · set q := (M - d * i) / n
    have hsub : Finset.range (q + 1) ⊆ (Finset.range (M + 1)).filter fun a ↦ n * a + d * i ≤ M := by
      intro a ha
      rw [Finset.mem_range] at ha
      rw [Finset.mem_filter, Finset.mem_range]
      have h1 : n * a ≤ n * q := Nat.mul_le_mul_left n (by omega)
      have h2 : n * q ≤ M - d * i := Nat.mul_div_le _ _
      have h3 : a ≤ n * a := Nat.le_mul_of_pos_left a hn
      constructor <;> omega
    have hc := Finset.card_le_card hsub
    rw [Finset.card_range] at hc
    have hq : ((M : ℤ) - d * i) / n = (q : ℤ) := by
      rw [show ((M : ℤ) - d * i) = ((M - d * i : ℕ) : ℤ) by push_cast [hdi]; ring]
      exact_mod_cast (Int.natCast_div _ _).symm
    rw [hq]
    exact_mod_cast hc
  · push_neg at hdi
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    have : ((M : ℤ) - d * i) / n < 0 := Int.ediv_neg_of_neg_of_pos (by push_cast; omega) hn'
    have h0 : (0 : ℤ) ≤ (((Finset.range (M + 1)).filter fun a ↦ n * a + d * i ≤ M).card : ℤ) :=
      by positivity
    omega

/-- **Riemann's inequality** for `L(M ∞)`: at least `M + 1 − g` monomials. -/
theorem card_basisN (n d M : ℕ) (hn : 0 < n) (hcop : Nat.Coprime n d) :
    2 * (M : ℤ) + 2 - (n - 1) * (d - 1) ≤ 2 * ((basisN n d M).length : ℤ) := by
  rw [← List.toFinset_card_of_nodup (nodup_basisN n d M), basisN_toFinset,
    Finset.card_filter, Finset.sum_product_right]
  have h := sum_floor n d hn hcop M
  have hrow : ∀ i ∈ Finset.range n, ((M : ℤ) - d * i) / n + 1 ≤
      ((∑ a ∈ Finset.range (M + 1), if n * a + d * i ≤ M then 1 else 0 : ℕ) : ℤ) := by
    intro i _
    rw [← Finset.card_filter]
    exact count_row n d M i hn
  have := Finset.sum_le_sum hrow
  push_cast at this ⊢
  linarith

section Exists

variable {F : Type*} [Field F]

lemma colSemN_coeff_high : ∀ (Γ : List (F × F × ℕ)) (Vs : List F[X]) (W : F[X][X]) (t : ℕ),
    (Γ.map fun q ↦ q.2.2).sum ≤ t → (colSemN Γ Vs W).coeff t = 0
  | [], _, _, _, _ => by simp [colSemN]
  | _ :: _, [], _, _, _ => by simp [colSemN]
  | q :: Γ, V :: Vs, W, t, ht => by
    simp only [List.map_cons, List.sum_cons] at ht
    simp only [colSemN, coeff_add, Jac.coeff_truncX, if_neg (show ¬ t < q.2.2 by omega), zero_add,
      coeff_X_pow_mul', if_pos (show q.2.2 ≤ t by omega)]
    exact colSemN_coeff_high Γ Vs W (t - q.2.2) (by omega)

lemma lsumW_ofFn_add {B : List (ℕ × ℕ)} (c c' : Fin B.length → F) :
    lsumW (List.ofFn (c + c')) B = lsumW (List.ofFn c) B + lsumW (List.ofFn c') B := by
  simp only [lsumW, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' := Finset.mem_range.mp hk
  simp [hk', C_mul_monomial, add_mul, map_add]

lemma lsumW_ofFn_smul {B : List (ℕ × ℕ)} (r : F) (c : Fin B.length → F) :
    lsumW (List.ofFn (r • c)) B = Polynomial.C (Polynomial.C r) * lsumW (List.ofFn c) B := by
  simp only [lsumW, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' := Finset.mem_range.mp hk
  simp [List.getElem?_ofFn, hk', C_mul_monomial, mul_assoc]

/-- **More monomials than conditions ⇒ a non-zero function vanishing on the divisor.** -/
theorem exists_vanishing_N (n d M : ℕ) (Γ : List (F × F × ℕ)) (Vs : List F[X])
    (hcount : (Γ.map fun q ↦ q.2.2).sum < (basisN n d M).length) :
    ∃ W : F[X][X], W ≠ 0 ∧ (∀ i a, (W.coeff i).coeff a ≠ 0 → (a, i) ∈ basisN n d M) ∧
      colSemN Γ Vs W = 0 := by
  classical
  set B := basisN n d M
  set N := (Γ.map fun q ↦ q.2.2).sum
  let T : (Fin B.length → F) →ₗ[F] (Fin N → F) :=
    { toFun := fun c t ↦ (colSemN Γ Vs (lsumW (List.ofFn c) B)).coeff t
      map_add' := fun c c' ↦ by
        ext t; simp [lsumW_ofFn_add, colSemN_add]
      map_smul' := fun r c ↦ by
        ext t
        simp [lsumW_ofFn_smul, colSemN_C_mul, coeff_C_mul] }
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := T) (by simpa using hcount)
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker] at hc
  have hcoeffs : ∀ k : Fin B.length, ((lsumW (List.ofFn c) B).coeff B[k].2).coeff B[k].1 = c k := by
    intro k
    rw [coeff_lsumW _ B (nodup_basisN n d M), if_pos (by simp)]
    have : B.idxOf (B[k].1, B[k].2) = k := by simp [nodup_basisN n d M, B]
    rw [this, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp
  refine ⟨lsumW (List.ofFn c) B, fun h0 ↦ hc0 ?_, fun i a hia ↦ ?_, ?_⟩
  · ext k
    rw [← hcoeffs k, h0]
    simp
  · by_contra hmem
    apply hia
    rw [coeff_lsumW _ B (nodup_basisN n d M), if_neg hmem]
  · ext t
    by_cases ht : t < N
    · have := congrFun hc ⟨t, ht⟩
      simpa [T] using this
    · rw [coeff_zero]
      exact colSemN_coeff_high Γ Vs _ t (not_lt.mp ht)

end Exists

end Sup
