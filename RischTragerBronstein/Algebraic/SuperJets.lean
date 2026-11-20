import RischTragerBronstein.Jacobian.PrincipalTest

/-!
# Jets on superelliptic curves `yⁿ = f(x)` at ordinary points

An element `∑ Wᵢ(x) yⁱ` is a bivariate polynomial `W ∈ R[X][Y]`. At a point `(α, β)` with
`n βⁿ⁻¹` a unit, a *branch jet* of order `ℓ` is `V ∈ R[s]` with `V(0) = β` and
`Vⁿ ≡ f(α + s) (mod sˡ)`; it is unique modulo `sˡ` (`branchN_unique`). The jet of `W` is
`∑ Wᵢ(α + s) Vⁱ` (`jetN`), and `W` *vanishes to order `ℓ`* at `(α, β)` when it is `0` modulo `sˡ`.

`branchCN`: the branch jet computed by Newton's iteration (`branchCN_spec`).
-/

open Polynomial

namespace Sup

section Ring

variable {R : Type*} [CommRing R]

/-- The jet `∑ Wᵢ(α + s) Vⁱ`. -/
noncomputable def jetN (W : R[X][X]) (α : R) (V : R[X]) : R[X] :=
  (W.map (compRingHom (X + C α))).eval V

/-- `V` is a branch jet of order `ℓ` of `ⁿ√f` at `(α, β)`. -/
def IsBranchN (f : R[X]) (n : ℕ) (α β : R) (ℓ : ℕ) (V : R[X]) : Prop :=
  V.coeff 0 = β ∧ X ^ ℓ ∣ V ^ n - f.comp (X + C α)

/-- `W` vanishes to order `ℓ` at the point `(α, β)` of `yⁿ = f`. -/
def VanishAtN (f : R[X]) (n : ℕ) (W : R[X][X]) (α β : R) (ℓ : ℕ) : Prop :=
  ∃ V, IsBranchN f n α β ℓ V ∧ X ^ ℓ ∣ jetN W α V

lemma jetN_add (W W' : R[X][X]) (α : R) (V : R[X]) :
    jetN (W + W') α V = jetN W α V + jetN W' α V := by
  simp [jetN, Polynomial.map_add]

lemma jetN_C_mul (c : R) (W : R[X][X]) (α : R) (V : R[X]) :
    jetN (Polynomial.C (Polynomial.C c) * W) α V = Polynomial.C c * jetN W α V := by
  simp [jetN, Polynomial.map_mul]

lemma jetN_monomial (a i : ℕ) (α : R) (V : R[X]) :
    jetN (Polynomial.monomial i (X ^ a : R[X])) α V = (X + C α) ^ a * V ^ i := by
  simp [jetN]

lemma jetN_map {S : Type*} [CommRing S] (φ : R →+* S) (W : R[X][X]) (α : R) (V : R[X]) :
    (jetN W α V).map φ = jetN (W.map (mapRingHom φ)) (φ α) (V.map φ) := by
  induction W using Polynomial.induction_on' with
  | add P Q hP hQ => rw [jetN_add, Polynomial.map_add, hP, hQ, Polynomial.map_add, jetN_add]
  | monomial i P =>
    simp only [jetN, Polynomial.map_monomial, eval_monomial, coe_compRingHom, coe_mapRingHom,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_comp, Polynomial.map_add,
      Polynomial.map_X, Polynomial.map_C]

/-- `V − U ∣ Vⁱ − Uⁱ`, hence congruent branches give congruent jets. -/
lemma jetN_congr (W : R[X][X]) (α : R) {V U : R[X]} {ℓ : ℕ} (h : X ^ ℓ ∣ V - U) :
    X ^ ℓ ∣ jetN W α V - jetN W α U := by
  simp only [jetN, eval_eq_sum_range, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun i _ ↦ ?_
  rw [← mul_sub]
  exact Dvd.dvd.mul_left (h.trans (sub_dvd_pow_sub_pow V U i)) _

/-- **Uniqueness of branch jets** (when `n βⁿ⁻¹` is a unit). -/
theorem branchN_unique {f : R[X]} {n : ℕ} (hn : 0 < n) {α β : R} {ℓ : ℕ} {V U : R[X]}
    (hu : IsUnit ((n : R) * β ^ (n - 1))) (hV : IsBranchN f n α β ℓ V)
    (hU : IsBranchN f n α β ℓ U) : X ^ ℓ ∣ V - U := by
  have hd : X ^ ℓ ∣ (V - U) * ∑ k ∈ Finset.range n, V ^ k * U ^ (n - 1 - k) := by
    rw [mul_comm, Commute.geom_sum₂_mul (Commute.all V U)]
    have := dvd_sub hV.2 hU.2
    rwa [sub_sub_sub_cancel_right] at this
  refine Jac.X_pow_dvd_of_mul ?_ (by rwa [mul_comm] at hd)
  have hc : (∑ k ∈ Finset.range n, V ^ k * U ^ (n - 1 - k)).coeff 0 = n * β ^ (n - 1) := by
    rw [finsetSum_coeff]
    simp only [coeff_zero_eq_eval_zero, eval_mul, eval_pow]
    rw [← coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero, hV.1, hU.1]
    rw [Finset.sum_congr rfl fun k hk ↦ by
      rw [← pow_add, show k + (n - 1 - k) = n - 1 by have := Finset.mem_range.mp hk; omega]]
    simp
  rwa [hc]

/-- `(V + D)ᵐ ≡ Vᵐ + m D Vᵐ⁻¹ (mod D²)`. -/
lemma add_pow_sq (V D : R[X]) (m : ℕ) :
    ∃ E : R[X], (V + D) ^ (m + 1) = V ^ (m + 1) + C ((m + 1 : ℕ) : R) * D * V ^ m + D ^ 2 * E := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨E, hE⟩ := ih
    refine ⟨C ((m + 1 : ℕ) : R) * V ^ m + (V + D) * E, ?_⟩
    rw [pow_succ, hE]
    simp only [map_natCast]
    push_cast
    ring

end Ring

/-! ### Newton's iteration for the branch jet -/

section Comp

open CPoly

variable {F : Type*} [Field F] [DecidableEq F]

/-- `Vⁿ`. -/
def powC (V : CPoly F) : ℕ → CPoly F
  | 0 => [1]
  | n + 1 => mul (powC V n) V

lemma toPoly_powC (V : CPoly F) (n : ℕ) : toPoly (powC V n) = toPoly V ^ n := by
  induction n with
  | zero => simp [powC]
  | succ n ih => simp [powC, ih, pow_succ]

/-- One Newton step for the `n`-th root jet: fix the coefficient of `Xᵗ`. -/
def branchStepN (F₀ : CPoly F) (n : ℕ) (β : F) (V : CPoly F) (t : ℕ) : CPoly F :=
  sub V (monomial t ((sub (powC V n) F₀).getD t 0 / (n * β ^ (n - 1))))

/-- The branch jet of order `k + 1` of `ⁿ√f` at `(α, β)`. -/
def branchCN (f : CPoly F) (n : ℕ) (α β : F) : ℕ → CPoly F
  | 0 => [β]
  | k + 1 => branchStepN (Jac.taylorC α f) n β (branchCN f n α β k) (k + 1)

/-- **Newton's iteration computes the branch jet.** -/
theorem branchCN_spec (f : CPoly F) (n : ℕ) (hn : 0 < n) (α β : F)
    (hu : (n : F) * β ^ (n - 1) ≠ 0) (hf : β ^ n = (toPoly f).eval α) :
    ∀ k, IsBranchN (toPoly f) n α β (k + 1) (toPoly (branchCN f n α β k)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨by simp [branchCN], ?_⟩
    rw [zero_add, pow_one, X_dvd_iff]
    simp [branchCN, coeff_zero_eq_eval_zero, eval_comp, hf]
  | succ k ih =>
    obtain ⟨hV0, G, hG⟩ := ih
    set V := toPoly (branchCN f n α β k)
    set c : F := (sub (powC (branchCN f n α β k) n) (Jac.taylorC α f)).getD (k + 1) 0 /
      (n * β ^ (n - 1))
    have hstep : toPoly (branchCN f n α β (k + 1)) = V - C c * X ^ (k + 1) := by
      simp [branchCN, branchStepN, V, c]
    have hcoef : (V ^ n - (toPoly f).comp (X + C α)).coeff (k + 1) = c * (n * β ^ (n - 1)) := by
      simp only [c]
      rw [← coeff_toPoly, toPoly_sub, toPoly_powC, Jac.toPoly_taylorC, div_mul_cancel₀ _ hu]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨E, hE⟩ := add_pow_sq V (-(C c * X ^ (k + 1))) m
    refine ⟨?_, ?_⟩
    · rw [hstep, coeff_sub, coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero, sub_zero, hV0]
    · rw [hstep, show V - C c * X ^ (k + 1) = V + -(C c * X ^ (k + 1)) from sub_eq_add_neg _ _,
        hE]
      have e : V ^ (m + 1) + C ((m + 1 : ℕ) : F) * -(C c * X ^ (k + 1)) * V ^ m +
          (-(C c * X ^ (k + 1))) ^ 2 * E - (toPoly f).comp (X + C α) =
          X ^ (k + 1) * (G - C ((m + 1 : ℕ) * c) * V ^ m) +
            X ^ (2 * (k + 1)) * (C (c ^ 2) * E) := by
        rw [show V ^ (m + 1) + C ((m + 1 : ℕ) : F) * -(C c * X ^ (k + 1)) * V ^ m +
          (-(C c * X ^ (k + 1))) ^ 2 * E - (toPoly f).comp (X + C α) =
          (V ^ (m + 1) - (toPoly f).comp (X + C α)) -
            C ((m + 1 : ℕ) * c) * X ^ (k + 1) * V ^ m + X ^ (2 * (k + 1)) * (C (c ^ 2) * E) by
          simp only [map_mul, map_pow, map_natCast]; ring, hG]
        ring
      rw [e]
      refine dvd_add ?_ ?_
      · rw [pow_succ]
        refine mul_dvd_mul_left _ ?_
        rw [X_dvd_iff, coeff_sub, coeff_C_mul]
        have hG1 : G.coeff 0 = (V ^ (m + 1) - (toPoly f).comp (X + C α)).coeff (k + 1) := by
          rw [hG, coeff_X_pow_mul', if_pos (by omega), Nat.sub_self]
        have hVm : (V ^ m).coeff 0 = β ^ m := by
          rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, hV0]
        rw [hG1, hcoef, hVm]
        simp only [Nat.add_sub_cancel]
        push_cast; ring
      · exact Dvd.dvd.mul_right (pow_dvd_pow X (by omega)) _

end Comp

end Sup
