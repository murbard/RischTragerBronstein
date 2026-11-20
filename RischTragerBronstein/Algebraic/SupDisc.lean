import RischTragerBronstein.Algebraic.SupBridge

/-!
# Uniqueness of zeros in a residue disc

* `eval_jetN`: evaluating the jet of `W` along a branch `V` at `t` is `W(α + t, V(t))`;
* `vanish_along`: vanishing to order `ℓ` can be tested along any branch jet of order `ℓ`;
* `disc_unique_N`: over a local domain, if `W` vanishes at `(x, b)` with a unit first-order jet
  coefficient, then `W` has no other zero `(x + t, Y)` in the residue disc (`t ≡ 0`, `Y ≡ b`).
-/

open Polynomial

namespace Sup

lemma eval_jetN {R : Type*} [CommRing R] (W : R[X][X]) (α : R) (V : R[X]) (t : R) :
    (jetN W α V).eval t = evalW W (α + t) (V.eval t) := by
  unfold jetN evalW
  induction W using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, eval_add, hp, hq]
  | monomial k a => simp [eval_comp, add_comm]

/-- Vanishing can be tested along any branch jet of the same order. -/
lemma vanish_along {R : Type*} [CommRing R] {f : R[X]} {n : ℕ} (hn : 0 < n) {W : R[X][X]}
    {α β : R} {ℓ : ℕ} {V : R[X]} (hV : IsBranchN f n α β ℓ V) (hu : IsUnit ((n : R) * β ^ (n - 1)))
    (h : VanishAtN f n W α β ℓ) : X ^ ℓ ∣ jetN W α V := by
  obtain ⟨V', hV', hd⟩ := h
  have h1 := dvd_add (jetN_congr W α (branchN_unique hn hu hV hV')) hd
  rwa [sub_add_cancel] at h1

section Disc

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]

local notation "𝔪" => IsLocalRing.maximalIdeal O

lemma unit_add_mem {u m : O} (hu : IsUnit u) (hm : m ∈ 𝔪) : IsUnit (u + m) := by
  by_contra h
  have h1 : u + m ∈ 𝔪 := (IsLocalRing.mem_maximalIdeal _).mpr h
  have h2 : u ∈ 𝔪 := by
    have := Ideal.sub_mem _ h1 hm; rwa [add_sub_cancel_right] at this
  exact (IsLocalRing.mem_maximalIdeal _).mp h2 hu

lemma residue_eq_of_sub_mem {a b : O} (h : a - b ∈ 𝔪) :
    IsLocalRing.residue O a = IsLocalRing.residue O b := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact h

/-- **Uniqueness in a residue disc.** -/
theorem disc_unique_N (f : O[X]) {n : ℕ} (hn : 0 < n) (ψ : O[X][X]) {x b t Y : O} {V : O[X]}
    (hV : IsBranchN f n x b 2 V) (hu : IsUnit ((n : O) * b ^ (n - 1)))
    (h0 : (jetN ψ x V).coeff 0 = 0) (h1 : IsUnit ((jetN ψ x V).coeff 1))
    (ht : t ∈ 𝔪) (hYb : Y - b ∈ 𝔪) (hY : Y ^ n = f.eval (x + t))
    (hz : evalW ψ (x + t) Y = 0) : t = 0 := by
  have hexp : ∀ P : O[X], ∃ s, P.eval t = P.coeff 0 + t * P.coeff 1 + t ^ 2 * s := by
    intro P
    have hdvd : X ^ 2 ∣ P - C (P.coeff 0) - C (P.coeff 1) * X := by
      rw [X_pow_dvd_iff]
      intro d hd
      interval_cases d <;> simp [coeff_C, coeff_X]
    obtain ⟨Q, hQ⟩ := hdvd
    refine ⟨Q.eval t, ?_⟩
    have e := congrArg (eval t) hQ
    simp only [eval_sub, eval_C, eval_mul, eval_X, eval_pow] at e
    linear_combination e
  obtain ⟨v, hv_def⟩ : ∃ v, V.eval t = v := ⟨_, rfl⟩
  obtain ⟨sv, hsv⟩ := hexp V
  rw [hV.1, hv_def] at hsv
  have hvb : v - b ∈ 𝔪 := by
    rw [hsv, show b + t * V.coeff 1 + t ^ 2 * sv - b = t * (V.coeff 1 + t * sv) by ring]
    exact Ideal.mul_mem_right _ _ ht
  obtain ⟨H, hH⟩ := hV.2
  have hvn : v ^ n - f.eval (x + t) = t ^ 2 * H.eval t := by
    have e := congrArg (eval t) hH
    simp only [eval_sub, eval_pow, eval_comp, eval_add, eval_X, eval_C, eval_mul, hv_def] at e
    rw [add_comm x t]; exact e
  set gs := ∑ i ∈ Finset.range n, Y ^ i * v ^ (n - 1 - i) with hgs_def
  have hgs : gs * (Y - v) = Y ^ n - v ^ n := geom_sum₂_mul Y v n
  have hgsu : IsUnit gs := by
    have hm : gs - (n : O) * b ^ (n - 1) ∈ 𝔪 := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
      have hY' := residue_eq_of_sub_mem hYb
      have hv' := residue_eq_of_sub_mem hvb
      simp only [gs, map_sum, map_mul, map_pow, hY', hv', map_natCast]
      rw [Finset.sum_congr rfl fun i hi ↦ by
        rw [← pow_add, show i + (n - 1 - i) = n - 1 by have := Finset.mem_range.mp hi; omega],
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_self]
    have := unit_add_mem hu hm
    rwa [add_sub_cancel] at this
  obtain ⟨gi, hgi⟩ : ∃ gi, gi * gs = 1 := ⟨↑hgsu.unit⁻¹, by simp⟩
  have hYv : Y - v = t ^ 2 * (-(H.eval t) * gi) := by
    have e : gs * (Y - v) = -(t ^ 2 * H.eval t) := by rw [hgs, hY, ← hvn]; ring
    linear_combination gi * e - (Y - v) * hgi
  obtain ⟨s1, hs1⟩ := sub_dvd_eval_sub Y v (ψ.map (evalRingHom (x + t)))
  change evalW ψ (x + t) Y - evalW ψ (x + t) v = (Y - v) * s1 at hs1
  obtain ⟨sj, hsj⟩ := hexp (jetN ψ x V)
  rw [eval_jetN, h0, hv_def] at hsj
  have hkey : t * ((jetN ψ x V).coeff 1 + t * (sj + (-(H.eval t) * gi) * s1)) = 0 := by
    linear_combination hz - hs1 - hsj - s1 * hYv
  have hunit := unit_add_mem h1 (Ideal.mul_mem_right (sj + (-(H.eval t) * gi) * s1) _ ht)
  exact (mul_eq_zero.mp hkey).resolve_right hunit.ne_zero

end Disc

end Sup
