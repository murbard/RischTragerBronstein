import RischTragerBronstein.Algebraic.HypCore

/-!
# Hyperelliptic integrals with logarithmic part: residue data at rational points

In `K = F(x)` (`F` constants, `′ = d/dx`), the `y`-component identity of a Liouville form for
`f = G / y`, `G = (B(x) + ∑ᵢ rᵢ βᵢ / (x − αᵢ)) / p`:

  `2 p G = 2 p e′ + p′ e + ∑ⱼ κⱼ Mⱼ / Nⱼ`.

At `q = x − αᵢ` (`p(αᵢ) = βᵢ² ≠ 0`) every `Mⱼ / Nⱼ` has polar part `−mᵢⱼ εᵢⱼ βᵢ / (x − αᵢ)` where
`mᵢⱼ = ord_q Nⱼ` and `aⱼ(αᵢ) = εᵢⱼ βᵢ bⱼ(αᵢ)` (`εᵢⱼ = ±1`) (`polar_MN`), and comparing polar parts
gives `2 rᵢ = −∑ⱼ κⱼ mᵢⱼ εᵢⱼ` (`residue_relation`).
-/

open Polynomial

namespace Differential

section Ell

variable {F K : Type*} [Field F] [CharZero F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

/-- A constant over `x − α` is regular at `x − α` only if it vanishes. -/
lemma polar_zero {α c : F} (h : φ (C c) / φ (X - C α) ∈ regularAt K (X - C α) (prime_X_sub_C α)) :
    c = 0 := by
  have hq0 : φ (X - C α) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective F[X] K)).mpr (X_sub_C_ne_zero α)
  have hdvd := dvd_of_algebraMap_eq_mul (x := C c) (prime_X_sub_C α) h (by field_simp)
  exact eq_zero_of_prime_dvd_C (prime_X_sub_C α) hdvd

variable (hder : ∀ P : F[X], P′ = derivative P)
include hder

/-- **The polar part of `M / N` at `x − α`.** -/
lemma polar_MN (p a b : F[X]) (hab : IsCoprime a b) (hN0 : hN p a b ≠ 0) (α β : F)
    (hβ : β ≠ 0) (hpα : p.eval α = β ^ 2) :
    ∃ (m : ℕ) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ (X - C α) ^ m ∣ hN p a b ∧
      ¬(X - C α) ^ (m + 1) ∣ hN p a b ∧ (0 < m → a.eval α = ε * β * b.eval α) ∧
      φ (hM p a b) / φ (hN p a b) + φ (C ((m : F) * ε * β)) / φ (X - C α) ∈
        regularAt K (X - C α) (prime_X_sub_C α) := by
  have hq := prime_X_sub_C (R := F) α
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  obtain ⟨m, N1, hN1, hNeq⟩ := exists_pow_mul_not_dvd hq hN0
  have hdiv : (X - C α) ^ m ∣ hN p a b := ⟨N1, hNeq⟩
  have hndiv : ¬(X - C α) ^ (m + 1) ∣ hN p a b := by
    rintro ⟨w, hw⟩
    rw [hNeq, pow_succ, mul_assoc] at hw
    exact hN1 ⟨w, mul_left_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero α)) hw⟩
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- `x − α ∤ N`: `M / N` is regular
    refine ⟨0, 1, Or.inl rfl, by simp, by simpa [hm0] using hndiv, fun h ↦ absurd h (by omega), ?_⟩
    subst hm0
    simp only [pow_zero, one_mul] at hNeq
    simp only [Nat.cast_zero, zero_mul, map_zero, zero_div, add_zero]
    rw [hNeq, div_eq_mul_inv]
    exact mul_mem (algebraMap_mem_regularAt _ _)
      ((isUnitAt_algebraMap (K := K) hq hN1).inv_mem_regularAt hq)
  -- `x − α ∣ N`: `x − α ∤ b`, and `a(α) = ε β b(α)`
  have hqN : (X - C α) ∣ hN p a b := dvd_trans (dvd_pow_self _ hmpos.ne') hdiv
  have hqb : ¬(X - C α) ∣ b := by
    intro hdb
    have hda : ¬(X - C α) ∣ a := fun hda ↦ hq.not_isUnit (hab.isUnit_of_dvd' hda hdb)
    apply hda
    have : (X - C α) ∣ a ^ 2 := by
      have h1 : (X - C α) ∣ b ^ 2 * p := dvd_mul_of_dvd_left (dvd_pow hdb two_ne_zero) _
      have := dvd_add hqN h1
      simpa [hN] using this
    exact hq.dvd_of_dvd_pow this
  have hbα : b.eval α ≠ 0 := by
    intro h0; exact hqb (dvd_iff_isRoot.mpr h0)
  have hNα : a.eval α ^ 2 = (β * b.eval α) ^ 2 := by
    have := (dvd_iff_isRoot.mp hqN)
    simp only [IsRoot, hN, eval_sub, eval_pow, eval_mul, hpα] at this
    linear_combination this
  obtain ⟨ε, hε, haα⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ a.eval α = ε * β * b.eval α := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hNα with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; push_cast; ring⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; push_cast; ring⟩
  refine ⟨m, ε, hε, hdiv, hndiv, fun _ ↦ haα, ?_⟩
  -- `b M / N + m a / (x − α)` is regular
  have hres := residue_MN (K := K) hder hq p a b hqb m N1 hN1 hNeq
  have hder1 : derivative (X - C α) = 1 := by simp
  rw [hder1, map_one] at hres
  have hub := isUnitAt_algebraMap (K := K) hq hqb
  have hbK : φ b ≠ 0 := map_ne_zero_of_not_dvd hq hqb
  -- `(a − ε β b) / (x − α)` is regular
  obtain ⟨w, hw⟩ : (X - C α) ∣ a - C ((ε : F) * β) * b := by
    rw [dvd_iff_isRoot]; simp [haα]
  have hq0 : φ (X - C α) ≠ 0 := (map_ne_zero_iff _ hinj).mpr (X_sub_C_ne_zero α)
  have e : φ (hM p a b) / φ (hN p a b) + φ (C ((m : F) * ε * β)) / φ (X - C α) =
      (φ b)⁻¹ * ((φ b * (φ (hM p a b) / φ (hN p a b)) + (m : K) * φ a * (1 / φ (X - C α))) -
        (m : K) * φ w) := by
    have hwK : φ a = φ (C ((ε : F) * β)) * φ b + φ (X - C α) * φ w := by
      rw [← map_mul, ← map_mul, ← map_add, ← hw]; ring
    rw [hwK]
    simp only [map_mul, map_natCast, map_intCast]
    field_simp
    ring
  rw [e]
  exact mul_mem (hub.inv_mem_regularAt hq) (sub_mem hres (mul_mem (natCast_mem _ _)
    (algebraMap_mem_regularAt _ _)))

/-- The left-hand side `2(B + ∑ rᵢ βᵢ / (x − αᵢ))` is regular at every irreducible `q` other than
the `x − αᵢ`; at `x − αᵢ` it has polar part `2 rᵢ βᵢ / (x − αᵢ)`. -/
lemma lhs_regular (B : F[X]) {ι : Type*} (s : Finset ι) (α w : ι → F) {q : F[X]}
    (hq : Irreducible q) (hqα : ∀ i ∈ s, ¬q ∣ X - C (α i)) :
    φ (2 * B) + ∑ i ∈ s, φ (C (w i)) / φ (X - C (α i)) ∈ regularAt K q hq.prime := by
  refine add_mem (algebraMap_mem_regularAt _ _) (Subring.sum_mem _ fun i hi ↦ ?_)
  rw [div_eq_mul_inv]
  exact mul_mem (algebraMap_mem_regularAt _ _)
    ((isUnitAt_algebraMap (K := K) hq.prime (hqα i hi)).inv_mem_regularAt hq.prime)

/-- `e` is regular at `q ∤ p` when the left-hand side has at most a simple pole there. -/
lemma e_regular_at {q : F[X]} (hq : Irreducible q) (p : F[X]) (hqp : ¬q ∣ p) (LHS : K)
    (hL : φ q * LHS ∈ regularAt K q hq.prime) {J : Type*} (t : Finset J) (κ : J → F)
    (a b : J → F[X]) (hab : ∀ j ∈ t, IsCoprime (a j) (b j)) (hN0 : ∀ j ∈ t, hN p (a j) (b j) ≠ 0)
    (e : K) (hid : LHS = φ (2 * p) * e′ + φ (derivative p) * e +
      ∑ j ∈ t, φ (C (κ j)) * (φ (hM p (a j) (b j)) / φ (hN p (a j) (b j)))) :
    e ∈ regularAt K q hq.prime := by
  by_contra he
  refine not_mem_eterm_of_pole hder hq.prime (not_dvd_derivative_self hq) p hqp he ?_
  have hS : φ q * ∑ j ∈ t, φ (C (κ j)) * (φ (hM p (a j) (b j)) / φ (hN p (a j) (b j))) ∈
      regularAt K q hq.prime := by
    rw [Finset.mul_sum]
    refine Subring.sum_mem _ fun j hj ↦ ?_
    rw [mul_left_comm]
    exact mul_mem (algebraMap_mem_regularAt _ _)
      (q_mul_MN_mem hder hq.prime p _ _ (hab j hj) (hN0 j hj))
  have : φ q * (φ (2 * p) * e′ + φ (derivative p) * e) = φ q * LHS -
      φ q * ∑ j ∈ t, φ (C (κ j)) * (φ (hM p (a j) (b j)) / φ (hN p (a j) (b j))) := by
    rw [hid]; ring
  rw [this]
  exact sub_mem hL hS

/-- **The residue relation** at `x − αᵢ`, and the shape of the norms `Nⱼ`. -/
theorem ell_core (p : F[X]) (hp : Squarefree p) (B : F[X]) {ι : Type*} (s : Finset ι)
    (α β r : ι → F) (hinj : Set.InjOn α s) (hβ : ∀ i ∈ s, β i ≠ 0)
    (hpα : ∀ i ∈ s, p.eval (α i) = β i ^ 2) (e : K) {J : Type*} (t : Finset J) (κ : J → F)
    (hκ : ∀ g : J → ℚ, ∑ j ∈ t, (g j : F) * κ j = 0 → ∀ j ∈ t, g j = 0)
    (a b : J → F[X]) (hab : ∀ j ∈ t, IsCoprime (a j) (b j))
    (hN0 : ∀ j ∈ t, hN p (a j) (b j) ≠ 0)
    (hid : φ (2 * B) + ∑ i ∈ s, φ (C (2 * r i * β i)) / φ (X - C (α i)) =
      φ (2 * p) * e′ + φ (derivative p) * e +
        ∑ j ∈ t, φ (C (κ j)) * (φ (hM p (a j) (b j)) / φ (hN p (a j) (b j)))) :
    (∀ j ∈ t, ∀ q : F[X], Irreducible q → q ∣ hN p (a j) (b j) →
      (∃ i ∈ s, q ∣ X - C (α i)) ∨ (q ∣ p ∧ ¬q ^ 2 ∣ hN p (a j) (b j))) ∧
    ∀ i ∈ s, ∃ (m : J → ℕ) (ε : J → ℤ), (∀ j ∈ t, (ε j = 1 ∨ ε j = -1) ∧
      (X - C (α i)) ^ m j ∣ hN p (a j) (b j) ∧ ¬(X - C (α i)) ^ (m j + 1) ∣ hN p (a j) (b j) ∧
      (0 < m j → (a j).eval (α i) = ε j * β i * (b j).eval (α i))) ∧
      2 * r i = -∑ j ∈ t, κ j * ((m j : F) * ε j) := by
  classical
  set LHS := φ (2 * B) + ∑ i ∈ s, φ (C (2 * r i * β i)) / φ (X - C (α i)) with hLHS
  have hqpα : ∀ i ∈ s, ¬(X - C (α i)) ∣ p := fun i hi h ↦ by
    have := (dvd_iff_isRoot.mp h)
    rw [IsRoot, hpα i hi] at this
    exact hβ i hi (pow_eq_zero_iff two_ne_zero |>.mp this)
  refine ⟨fun j hj q hq hqN ↦ ?_, fun i hi ↦ ?_⟩
  · -- the shape of the norm
    by_cases hqp : q ∣ p
    · refine Or.inr ⟨hqp, fun hqq ↦ ?_⟩
      -- `q² ∤ N`
      by_cases hqa : q ∣ a j
      · have hqb : ¬q ∣ b j := fun hqb ↦ hq.not_isUnit ((hab j hj).isUnit_of_dvd' hqa hqb)
        have hcop : IsCoprime (q ^ 2) (b j ^ 2) :=
          ((Irreducible.coprime_iff_not_dvd hq).mpr hqb).pow
        have : q ^ 2 ∣ b j ^ 2 * p := by
          have ha2 : q ^ 2 ∣ a j ^ 2 := pow_dvd_pow_of_dvd hqa 2
          have := dvd_sub ha2 hqq
          simpa [hN] using this
        have hqqp := hcop.dvd_of_dvd_mul_left this
        exact hq.not_isUnit (hp q (by rw [← sq]; exact hqqp))
      · apply hqa
        have hqN' : q ∣ hN p (a j) (b j) := hqN
        have : q ∣ a j ^ 2 := by
          have := dvd_add hqN' (dvd_mul_of_dvd_right hqp (b j ^ 2))
          simpa [hN] using this
        exact hq.prime.dvd_of_dvd_pow this
    · left
      by_contra hno
      push_neg at hno
      have hL := lhs_regular (K := K) hder B s α (fun i ↦ 2 * r i * β i) hq hno
      have heR := e_regular_at (K := K) hder hq p hqp LHS (by
        have := mul_mem (algebraMap_mem_regularAt (K := K) hq.prime q) hL; exact this)
        t κ a b hab hN0 e hid
      have hreg : ∑ j ∈ t, φ (C (κ j)) * (φ (hM p (a j) (b j)) / φ (hN p (a j) (b j))) ∈
          regularAt K q hq.prime := by
        have : ∑ j ∈ t, φ (C (κ j)) * (φ (hM p (a j) (b j)) / φ (hN p (a j) (b j))) =
            LHS - (φ (2 * p) * e′ + φ (derivative p) * e) := by rw [hid]; ring
        rw [this]
        exact sub_mem hL (add_mem (mul_mem (algebraMap_mem_regularAt _ _)
          (deriv_mem_regularAt _ heR)) (mul_mem (algebraMap_mem_regularAt _ _) heR))
      exact not_dvd_N_of_regular hder hq (not_dvd_derivative_self hq) p hqp t κ hκ a b hab hN0
        hreg j hj hqN
  · -- the residue relation at `x − αᵢ`
    have hq : Irreducible (X - C (α i)) := irreducible_X_sub_C (α i)
    have hqp := hqpα i hi
    have hpol : ∀ j ∈ t, ∃ (m : ℕ) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ (X - C (α i)) ^ m ∣ hN p (a j) (b j) ∧
        ¬(X - C (α i)) ^ (m + 1) ∣ hN p (a j) (b j) ∧
        (0 < m → (a j).eval (α i) = ε * β i * (b j).eval (α i)) ∧
        φ (hM p (a j) (b j)) / φ (hN p (a j) (b j)) + φ (C ((m : F) * ε * β i)) / φ (X - C (α i)) ∈
          regularAt K (X - C (α i)) (prime_X_sub_C (α i)) := fun j hj ↦
      polar_MN (K := K) hder p (a j) (b j) (hab j hj) (hN0 j hj) (α i) (β i) (hβ i hi) (hpα i hi)
    choose! m ε hε hdv hndv hval hreg using hpol
    refine ⟨m, ε, fun j hj ↦ ⟨hε j hj, hdv j hj, hndv j hj, hval j hj⟩, ?_⟩
    -- the other terms of the left-hand side are regular
    have hR1 : LHS - φ (C (2 * r i * β i)) / φ (X - C (α i)) ∈
        regularAt K (X - C (α i)) (prime_X_sub_C (α i)) := by
      have hsplit : LHS - φ (C (2 * r i * β i)) / φ (X - C (α i)) = φ (2 * B) +
          ∑ i' ∈ s.erase i, φ (C (2 * r i' * β i')) / φ (X - C (α i')) := by
        rw [hLHS, ← Finset.add_sum_erase s _ hi]; ring
      rw [hsplit]
      refine lhs_regular (K := K) hder B (s.erase i) α (fun i ↦ 2 * r i * β i) hq
        fun i' hi' hdv' ↦ ?_
      obtain ⟨hne, hi's⟩ := Finset.mem_erase.mp hi'
      have := (dvd_iff_isRoot.mp (dvd_trans (dvd_refl _) hdv'))
      rw [IsRoot, eval_sub, eval_X, eval_C] at this
      have hdvX : X - C (α i) ∣ X - C (α i') := hdv'
      rw [dvd_iff_isRoot] at hdvX
      simp only [IsRoot, eval_sub, eval_X, eval_C, sub_eq_zero] at hdvX
      exact hne (hinj hi's hi hdvX.symm)
    have heR := e_regular_at (K := K) hder hq p hqp LHS (by
        have h1 := mul_mem (algebraMap_mem_regularAt (K := K) hq.prime (X - C (α i))) hR1
        have hq0 : φ (X - C (α i)) ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective F[X] K)).mpr (X_sub_C_ne_zero _)
        have : φ (X - C (α i)) * LHS = φ (X - C (α i)) * (LHS - φ (C (2 * r i * β i)) /
            φ (X - C (α i))) + φ (C (2 * r i * β i)) := by field_simp; ring
        rw [this]
        exact add_mem h1 (algebraMap_mem_regularAt _ _))
      t κ a b hab hN0 e hid
    have hR2 : ∑ j ∈ t, φ (C (κ j)) * (φ (hM p (a j) (b j)) / φ (hN p (a j) (b j)) +
        φ (C ((m j : F) * ε j * β i)) / φ (X - C (α i))) ∈
          regularAt K (X - C (α i)) (prime_X_sub_C (α i)) :=
      Subring.sum_mem _ fun j hj ↦ mul_mem (algebraMap_mem_regularAt _ _) (hreg j hj)
    have hR3 : φ (2 * p) * e′ + φ (derivative p) * e ∈
        regularAt K (X - C (α i)) (prime_X_sub_C (α i)) :=
      add_mem (mul_mem (algebraMap_mem_regularAt _ _) (deriv_mem_regularAt _ heR))
        (mul_mem (algebraMap_mem_regularAt _ _) heR)
    have hpolar : φ (C (2 * r i * β i + ∑ j ∈ t, κ j * ((m j : F) * ε j * β i))) /
        φ (X - C (α i)) = (φ (2 * p) * e′ + φ (derivative p) * e) -
          (LHS - φ (C (2 * r i * β i)) / φ (X - C (α i))) +
          ∑ j ∈ t, φ (C (κ j)) * (φ (hM p (a j) (b j)) / φ (hN p (a j) (b j)) +
            φ (C ((m j : F) * ε j * β i)) / φ (X - C (α i))) := by
      rw [hid]
      simp only [map_add, map_sum, map_mul, add_div, Finset.sum_div, mul_add,
        Finset.sum_add_distrib]
      ring
    have := polar_zero (K := K) (c := 2 * r i * β i + ∑ j ∈ t, κ j * ((m j : F) * ε j * β i))
      (by rw [hpolar]; exact add_mem (sub_mem hR3 hR1) hR2)
    have hβi := hβ i hi
    have e2 : 2 * r i * β i + ∑ j ∈ t, κ j * ((m j : F) * ε j * β i) =
        β i * (2 * r i + ∑ j ∈ t, κ j * ((m j : F) * ε j)) := by
      rw [mul_add, Finset.mul_sum]; congr 1
      · ring
      · exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [e2] at this
    have := (mul_eq_zero.mp this).resolve_left hβi
    linear_combination this

end Ell

end Differential
