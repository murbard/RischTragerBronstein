import RischTragerBronstein.Algebraic.SupKernel

/-!
# Jets on a general plane curve `F(x, Y) = 0` over a ring

Char-free local analysis at an unramified point `(α, β)` (`F(α, β) = 0`, `F_Y(α, β)` a unit), in
the local parameter `t = x − α` (`Sup.jetN W α V = W(α + t, V(t))`):

* `IsBranchG F α β ℓ V`: `V` is the branch jet of order `ℓ` through `(α, β)`;
  `VanishAtG F W α β ℓ`: `W` vanishes to order `ℓ` at `(α, β)`;
* `branchG_unique`, `exists_branchG` (Newton's iteration): the branch jet exists and is unique;
* `dvd_coeff_of_eval`: a polynomial of degree `< m` over `R[X]` vanishing modulo `Xˡ` at `m` jets
  with unit differences has all coefficients divisible by `Xˡ`;
* `dvd_of_vanish_allG`: if `W` (of `Y`-degree `< n`) vanishes to order `ℓ` at all `n` points of a
  split fibre `x = α`, then `(x − α)ˡ` divides every coefficient of `W`.
-/

open Polynomial Sup

namespace GTors

section Ring

variable {R : Type*} [CommRing R]

/-- The jet `W(α + t, V(t))` (a name for `Sup.jetN`). -/
noncomputable abbrev jetN' (W : R[X][X]) (α : R) (V : R[X]) : R[X] := jetN W α V

/-- `V` is a branch jet of order `ℓ` of `F = 0` through `(α, β)`. -/
def IsBranchG (F : R[X][X]) (α β : R) (ℓ : ℕ) (V : R[X]) : Prop :=
  V.coeff 0 = β ∧ X ^ ℓ ∣ jetN F α V

/-- `W` vanishes to order `ℓ` at the point `(α, β)` of `F = 0`. -/
def VanishAtG (F W : R[X][X]) (α β : R) (ℓ : ℕ) : Prop :=
  ∃ V, IsBranchG F α β ℓ V ∧ X ^ ℓ ∣ jetN W α V

lemma IsBranchG.mono {F : R[X][X]} {α β : R} {ℓ ℓ' : ℕ} {V : R[X]} (h : IsBranchG F α β ℓ V)
    (hl : ℓ' ≤ ℓ) : IsBranchG F α β ℓ' V :=
  ⟨h.1, (pow_dvd_pow X hl).trans h.2⟩

lemma VanishAtG.mono {F W : R[X][X]} {α β : R} {ℓ ℓ' : ℕ} (h : VanishAtG F W α β ℓ)
    (hl : ℓ' ≤ ℓ) : VanishAtG F W α β ℓ' := by
  obtain ⟨V, hV, hW⟩ := h
  exact ⟨V, hV.mono hl, (pow_dvd_pow X hl).trans hW⟩

lemma jetN_derivative (P : R[X][X]) (α : R) (V : R[X]) :
    ((P.map (compRingHom (X + C α))).derivative).eval V = jetN (derivative P) α V := by
  rw [jetN, derivative_map]

/-- The difference of two jets of `P` factors through `V − U`, with cofactor `P_Y(α, U(0))` at `0`. -/
lemma jet_sub_factor (P : R[X][X]) (α : R) (V U : R[X]) :
    ∃ G : R[X], jetN P α V - jetN P α U = (V - U) * G ∧
      (V.coeff 0 = U.coeff 0 → G.coeff 0 = evalW (derivative P) α (U.coeff 0)) := by
  obtain ⟨k, hk⟩ := binomExpansion (P.map (compRingHom (X + C α))) U (V - U)
  refine ⟨jetN (derivative P) α U + k * (V - U), ?_, fun h0 ↦ ?_⟩
  · rw [jetN, jetN, show V = U + (V - U) by ring, hk, jetN_derivative]
    simp only [add_sub_cancel]
    ring
  · rw [coeff_add, jetN_coeff_zero, mul_coeff_zero, coeff_sub, h0, sub_self, mul_zero, add_zero]

/-- **Uniqueness of the branch jet.** -/
theorem branchG_unique {F : R[X][X]} {α β : R} {ℓ : ℕ} {V U : R[X]}
    (hu : IsUnit (evalW (derivative F) α β)) (hV : IsBranchG F α β ℓ V)
    (hU : IsBranchG F α β ℓ U) : X ^ ℓ ∣ V - U := by
  obtain ⟨G, hG, hG0⟩ := jet_sub_factor F α V U
  have hc : IsUnit (G.coeff 0) := by rw [hG0 (by rw [hV.1, hU.1]), hU.1]; exact hu
  have hd : X ^ ℓ ∣ G * (V - U) := by
    rw [mul_comm, ← hG]; exact dvd_sub hV.2 hU.2
  exact Jac.X_pow_dvd_of_mul hc hd

/-- Vanishing can be tested on any branch jet. -/
theorem vanishAtG_iff {F W : R[X][X]} {α β : R} {ℓ : ℕ} {V : R[X]}
    (hu : IsUnit (evalW (derivative F) α β)) (hV : IsBranchG F α β ℓ V) :
    VanishAtG F W α β ℓ ↔ X ^ ℓ ∣ jetN W α V := by
  constructor
  · rintro ⟨U, hU, hW⟩
    have := dvd_add (jetN_congr W α (branchG_unique hu hV hU)) hW
    rwa [sub_add_cancel] at this
  · exact fun h ↦ ⟨V, hV, h⟩

/-- **Newton's iteration**: the branch jet exists. -/
theorem exists_branchG {F : R[X][X]} {α β : R} (h0 : evalW F α β = 0)
    (hu : IsUnit (evalW (derivative F) α β)) : ∀ ℓ, ∃ V, IsBranchG F α β ℓ V
  | 0 => ⟨C β, by simp, by simp⟩
  | 1 => ⟨C β, by simp, by
      rw [pow_one, X_dvd_iff, jetN_coeff_zero, coeff_C_zero, h0]⟩
  | ℓ + 2 => by
    obtain ⟨V, hV1, hV2⟩ := exists_branchG h0 hu (ℓ + 1)
    obtain ⟨q, hq⟩ := hV2
    set c := q.coeff 0 * ↑hu.unit⁻¹ with hc
    refine ⟨V - C c * X ^ (ℓ + 1), ?_, ?_⟩
    · rw [coeff_sub, coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero, sub_zero, hV1]
    · obtain ⟨k, hk⟩ := binomExpansion (F.map (compRingHom (X + C α))) V (-(C c * X ^ (ℓ + 1)))
      have e : jetN F α (V - C c * X ^ (ℓ + 1)) = X ^ (ℓ + 1) * (q - C c *
          jetN (derivative F) α V) + k * (C c * X ^ (ℓ + 1)) ^ 2 := by
        rw [jetN, sub_eq_add_neg, hk, ← jetN, hq, jetN_derivative]
        ring
      rw [e]
      refine dvd_add ?_ ⟨k * C c ^ 2 * X ^ ℓ, by ring⟩
      rw [pow_succ]
      refine mul_dvd_mul_left _ ?_
      rw [X_dvd_iff, coeff_sub, coeff_C_mul, jetN_coeff_zero, hV1, hc, mul_assoc,
        IsUnit.val_inv_mul, mul_one, sub_self]

/-- **A polynomial vanishing at many jets** (with unit differences) has divisible coefficients. -/
theorem dvd_coeff_of_eval [Nontrivial R] {ℓ : ℕ} : ∀ (m : ℕ) (P : R[X][X]) (v : Fin m → R[X]),
    P.natDegree < m → (∀ i j, i ≠ j → IsUnit ((v i - v j).coeff 0)) →
    (∀ i, X ^ ℓ ∣ P.eval (v i)) → ∀ j, X ^ ℓ ∣ P.coeff j
  | 0, P, _, hP, _, _ => by
    intro j
    have : P = 0 := by
      by_contra h
      exact absurd hP (by simp)
    rw [this, coeff_zero]; exact dvd_zero _
  | m + 1, P, v, hP, hu, hv => by
    by_cases hm : m = 0
    · subst hm
      have hPc : P = C (P.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
      intro j
      rcases j with _ | j
      · have := hv 0
        rwa [hPc, eval_C] at this
      · rw [hPc, coeff_C, if_neg (by omega)]; exact dvd_zero _
    set v0 := v 0
    set Q := P /ₘ (X - C v0) with hQ
    have hPQ : P = Q * (X - C v0) + C (P.eval v0) := by
      have := modByMonic_add_div P (X - C v0)
      rw [modByMonic_X_sub_C_eq_C_eval] at this
      rw [hQ]; linear_combination -this
    have hQdeg : Q.natDegree < m := by
      rw [hQ]
      have := natDegree_divByMonic P (monic_X_sub_C v0)
      rw [natDegree_X_sub_C] at this
      omega
    have hQv : ∀ i : Fin m, X ^ ℓ ∣ Q.eval (v i.succ) := by
      intro i
      have h1 := hv i.succ
      rw [hPQ, eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_C] at h1
      have h2 : X ^ ℓ ∣ (v i.succ - v0) * Q.eval (v i.succ) := by
        have := dvd_sub h1 (hv 0)
        rwa [add_sub_cancel_right, mul_comm] at this
      exact Jac.X_pow_dvd_of_mul (hu _ _ (Fin.succ_ne_zero i)) h2
    have hQc := dvd_coeff_of_eval m Q (fun i ↦ v i.succ) hQdeg
      (fun i j hij ↦ hu _ _ fun h ↦ hij (Fin.succ_injective _ h)) hQv
    intro j
    rw [hPQ, coeff_add, coeff_C]
    rcases j with _ | j
    · rw [mul_coeff_zero, if_pos rfl, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
      refine dvd_add (Dvd.dvd.mul_right (hQc 0) _) (hv 0)
    · rw [if_neg (by omega), add_zero, coeff_mul_X_sub_C]
      exact dvd_sub (hQc j) (Dvd.dvd.mul_right (hQc (j + 1)) _)

/-- **Vanishing on a whole split fibre.** -/
theorem dvd_of_vanish_allG [Nontrivial R] {F W : R[X][X]} {n : ℕ} {α : R} (β : Fin n → R)
    (hβ : ∀ i j, i ≠ j → IsUnit (β i - β j)) (hu : ∀ i, IsUnit (evalW (derivative F) α (β i)))
    (hW : W.natDegree < n) {ℓ : ℕ} (h : ∀ i, VanishAtG F W α (β i) ℓ) :
    ∀ j, (X - C α) ^ ℓ ∣ W.coeff j := by
  choose V hV hVW using h
  have hP := dvd_coeff_of_eval n (W.map (compRingHom (X + C α))) V
    (lt_of_le_of_lt natDegree_map_le hW)
    (fun i j hij ↦ by rw [coeff_sub, (hV i).1, (hV j).1]; exact hβ i j hij)
    (fun i ↦ by rw [← jetN]; exact hVW i)
  intro j
  have := hP j
  rw [coeff_map, coe_compRingHom] at this
  exact Jac.dvd_of_comp this

end Ring

end GTors
