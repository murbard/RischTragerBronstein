import RischTragerBronstein.Algebraic.SupDisc
import RischTragerBronstein.Algebraic.SupCount

/-!
# Vanishing conditions: maps, scalars, values, existence

* `VanishAtN.mapR`, `VanishAtN.C_mul`, `VanishAtN.of_C_mul`;
* `vanish1_of_evalW`, `evalW_of_vanish`: order-one vanishing is the vanishing of the value;
* `eq_of_pow_eq`: over a local domain, `n`-th roots congruent modulo `𝔪` are equal;
* `exists_vanishing_list`: a non-zero function with a support bound vanishing on a list of points
  (with multiplicities), provided the number of conditions is less than the number of monomials.
-/

open Polynomial

namespace Sup

section Ring

variable {R : Type*} [CommRing R]

lemma VanishAtN.mapR {S : Type*} [CommRing S] (φ : R →+* S) {f : R[X]} {n : ℕ} {W : R[X][X]}
    {α β : R} {ℓ : ℕ} (h : VanishAtN f n W α β ℓ) :
    VanishAtN (f.map φ) n (W.map (mapRingHom φ)) (φ α) (φ β) ℓ := by
  obtain ⟨V, hV, hd⟩ := h
  refine ⟨V.map φ, hV.mapR φ, ?_⟩
  rw [← jetN_map]
  simpa using Polynomial.map_dvd φ hd

lemma VanishAtN.mono {f : R[X]} {n : ℕ} {W : R[X][X]} {α β : R} {ℓ ℓ' : ℕ}
    (h : VanishAtN f n W α β ℓ) (hl : ℓ' ≤ ℓ) : VanishAtN f n W α β ℓ' := by
  obtain ⟨V, hV, hd⟩ := h
  exact ⟨V, hV.mono hl, (pow_dvd_pow X hl).trans hd⟩

lemma VanishAtN.C_mul {f : R[X]} {n : ℕ} {W : R[X][X]} {α β : R} {ℓ : ℕ}
    (h : VanishAtN f n W α β ℓ) (c : R) : VanishAtN f n (C (C c) * W) α β ℓ := by
  obtain ⟨V, hV, hd⟩ := h
  exact ⟨V, hV, by rw [jetN_C_mul]; exact dvd_mul_of_dvd_right hd _⟩

lemma VanishAtN.of_C_mul {F : Type*} [Field F] {f : F[X]} {n : ℕ} {W : F[X][X]} {α β : F}
    {ℓ : ℕ} {c : F} (hc : c ≠ 0) (h : VanishAtN f n (C (C c) * W) α β ℓ) :
    VanishAtN f n W α β ℓ := by
  have := h.C_mul c⁻¹
  rwa [← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel₀ hc, map_one, map_one, one_mul] at this

lemma vanish1_of_evalW {f : R[X]} {n : ℕ} {W : R[X][X]} {α β : R} (hβ : β ^ n = f.eval α)
    (h : evalW W α β = 0) : VanishAtN f n W α β 1 := by
  refine ⟨C β, ⟨coeff_C_zero, ?_⟩, ?_⟩
  · rw [pow_one, X_dvd_iff, ← C_pow, coeff_sub, coeff_C_zero, coeff_zero_eq_eval_zero, eval_comp,
      eval_add, eval_X, eval_C, zero_add, hβ, sub_self]
  · rw [pow_one, X_dvd_iff, jetN_coeff_zero, coeff_C_zero, h]

lemma evalW_of_vanish {f : R[X]} {n : ℕ} {W : R[X][X]} {α β : R} {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (h : VanishAtN f n W α β ℓ) : evalW W α β = 0 := by
  obtain ⟨V, hV, hd⟩ := h
  have h1 := (pow_dvd_pow X hℓ).trans hd
  rw [pow_one, X_dvd_iff, jetN_coeff_zero, hV.1] at h1
  exact h1

lemma evalW_map {S : Type*} [CommRing S] (φ : R →+* S) (W : R[X][X]) (a b : R) :
    evalW (W.map (mapRingHom φ)) (φ a) (φ b) = φ (evalW W a b) := by
  unfold evalW
  induction W using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, eval_add, map_add, hp, hq]
  | monomial k a => simp [eval_map, eval₂_hom]

end Ring

section Local

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]

/-- Congruent `n`-th roots with a unit derivative are equal. -/
lemma eq_of_pow_eq {n : ℕ} {Y y : O} (hu : IsUnit ((n : O) * y ^ (n - 1))) (h : Y ^ n = y ^ n)
    (hYy : Y - y ∈ IsLocalRing.maximalIdeal O) : Y = y := by
  set gs := ∑ i ∈ Finset.range n, Y ^ i * y ^ (n - 1 - i)
  have hgs : gs * (Y - y) = Y ^ n - y ^ n := geom_sum₂_mul Y y n
  have hgsu : IsUnit gs := by
    have hm : gs - (n : O) * y ^ (n - 1) ∈ IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
      have hY' := residue_eq_of_sub_mem hYy
      simp only [gs, map_sum, map_mul, map_pow, hY', map_natCast]
      rw [Finset.sum_congr rfl fun i hi ↦ by
        rw [← pow_add, show i + (n - 1 - i) = n - 1 by have := Finset.mem_range.mp hi; omega],
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_self]
    have := unit_add_mem hu hm
    rwa [add_sub_cancel] at this
  rw [h, sub_self] at hgs
  exact sub_eq_zero.mp ((mul_eq_zero.mp hgs).resolve_left hgsu.ne_zero)

end Local

section Exist

variable {F : Type*} [Field F]

open Classical in
/-- A branch jet of order `ℓ` at `P = (α, β, ℓ)` (junk if `P` is not an ordinary point). -/
noncomputable def brJ (f : F[X]) {n : ℕ} (hn : 0 < n) (P : F × F × ℕ) : F[X] :=
  if h : IsUnit ((n : F) * P.2.1 ^ (n - 1)) ∧ P.2.1 ^ n = f.eval P.1 then
    Classical.choose (exists_branchN f hn h.1 h.2 P.2.2)
  else 0

lemma brJ_spec (f : F[X]) {n : ℕ} (hn : 0 < n) (P : F × F × ℕ)
    (hu : IsUnit ((n : F) * P.2.1 ^ (n - 1))) (hP : P.2.1 ^ n = f.eval P.1) :
    IsBranchN f n P.1 P.2.1 P.2.2 (brJ f hn P) := by
  classical
  rw [brJ, dif_pos ⟨hu, hP⟩]
  exact (Classical.choose_spec (exists_branchN f hn hu hP P.2.2)).mono (Nat.le_succ _)

/-- **Existence of a vanishing function** on a list of ordinary points. -/
theorem exists_vanishing_list (f : F[X]) {n : ℕ} (hn : 0 < n) (d M : ℕ) (Γ : List (F × F × ℕ))
    (hΓ : ∀ P ∈ Γ, IsUnit ((n : F) * P.2.1 ^ (n - 1)) ∧ P.2.1 ^ n = f.eval P.1)
    (hcount : (Γ.map fun q ↦ q.2.2).sum < (basisN n d M).length) :
    ∃ W : F[X][X], W ≠ 0 ∧ (∀ i a, (W.coeff i).coeff a ≠ 0 → i < n ∧ n * a + d * i ≤ M) ∧
      ∀ P ∈ Γ, VanishAtN f n W P.1 P.2.1 P.2.2 := by
  obtain ⟨W, hW0, hsupp, hcol⟩ := exists_vanishing_N n d M Γ (Γ.map (brJ f hn)) hcount
  refine ⟨W, hW0, fun i a h ↦ (mem_basisN n d M a i hn).mp (hsupp i a h), fun P hP ↦ ?_⟩
  rw [colSemN_zero_iff Γ _ W (by simp)] at hcol
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hP
  have h := hcol ⟨i, hi⟩
  have hVi : (Γ.map (brJ f hn))[i]! = brJ f hn Γ[i] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]; rfl
  simp only [Fin.getElem_fin] at h
  exact ⟨_, brJ_spec f hn _ (hΓ _ hP).1 (hΓ _ hP).2, by convert h using 2; exact hVi.symm⟩

end Exist

end Sup
