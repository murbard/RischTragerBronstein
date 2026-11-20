import RischTragerBronstein.Jacobian.TorsionDecideR

/-!
# Integrality of the rescaled points

If `β² = f(α)` with `f ∈ ℤ[x]` of degree `≤ 2g + 1` and `den α ∣ d`, then `d² α ∈ ℤ` and
`d^{2g+1} β ∈ ℤ` (`den_scale_x`, `den_scale_y`): `(d^{2g+1} β)² = d^{2(2g+1)} f(α)` is an integer,
and a rational number with integral square is integral.
-/

open Polynomial CPoly CPoly.Kron

namespace Jac

lemma den_one_iff {q : ℚ} : q.den = 1 ↔ ∃ z : ℤ, (z : ℚ) = q :=
  ⟨fun h ↦ ⟨q.num, Rat.coe_int_num_of_den_eq_one h⟩, fun ⟨z, hz⟩ ↦ hz ▸ Rat.den_intCast z⟩

lemma den_eq_one_of_sq {q : ℚ} (h : (q ^ 2).den = 1) : q.den = 1 := by
  rw [Rat.den_pow] at h
  rcases (Nat.pow_eq_one.mp h) with h | h
  · exact h
  · omega

lemma int_mul_den {α : ℚ} {d : ℕ} (hd : α.den ∣ d) : ∃ z : ℤ, (z : ℚ) = (d : ℚ) * α := by
  obtain ⟨k, rfl⟩ := hd
  refine ⟨α.num * k, ?_⟩
  have h := Rat.mul_den_eq_num α
  push_cast; rw [← h]; ring

lemma den_scale_x {α : ℚ} {d : ℕ} (hd : α.den ∣ d) : ((d : ℚ) ^ 2 * α).den = 1 := by
  obtain ⟨z, hz⟩ := int_mul_den hd
  exact den_one_iff.mpr ⟨d * z, by push_cast; rw [hz]; ring⟩

/-- `dⁿ f(α)` is an integer when `deg f < n + 1` and `den α ∣ d`. -/
lemma int_scale_eval {f : List ℤ} {n : ℕ} (hf : f.length ≤ n + 1) {α : ℚ} {d : ℕ}
    (hd : α.den ∣ d) : ∃ z : ℤ, (z : ℚ) = (d : ℚ) ^ n * evalC (f.map (Int.castRingHom ℚ)) α := by
  induction f generalizing n with
  | nil => exact ⟨0, by simp [evalC]⟩
  | cons c f ih =>
    rcases n with _ | n
    · simp only [List.length_cons] at hf
      have : f = [] := List.length_eq_zero_iff.mp (by omega)
      subst this; exact ⟨c, by simp [evalC]⟩
    · obtain ⟨z1, hz1⟩ := ih (n := n) (by simp at hf; omega)
      obtain ⟨z2, hz2⟩ := int_mul_den hd
      refine ⟨c * d ^ (n + 1) + z2 * z1, ?_⟩
      simp only [List.map_cons, evalC, List.foldr_cons] at hz1 ⊢
      push_cast; rw [hz1, hz2]; simp only [eq_intCast]; ring

lemma den_scale_y {f : List ℤ} {g : ℕ} (hf : f.length = 2 * g + 2) {α β : ℚ} {d : ℕ}
    (hd : α.den ∣ d) (hβ : β ^ 2 = evalC (f.map (Int.castRingHom ℚ)) α) :
    ((d : ℚ) ^ (2 * g + 1) * β).den = 1 := by
  apply den_eq_one_of_sq
  obtain ⟨z, hz⟩ := int_scale_eval (n := 2 * g + 1) (by omega) hd (f := f)
  refine den_one_iff.mpr ⟨d ^ (2 * g + 1) * z, ?_⟩
  push_cast; rw [hz, mul_pow, hβ]; ring

end Jac
