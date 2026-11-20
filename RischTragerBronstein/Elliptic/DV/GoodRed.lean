import RischTragerBronstein.Elliptic.DV.Bound

/-!
# Good reduction, checked modulo `p`

`goodRedMod p a b c`: every root of `x³ + ax² + bx + c` in `ℤ/p` is simple — a finite (decidable)
check; `goodRed_of_mod` turns it into `GoodRed p a b c` over `ℚ_p`.
-/

namespace EllDV

variable {p : ℕ} [hp : Fact p.Prime]

/-- The finite check. -/
def goodRedMod (p : ℕ) (a b c : ℤ) : Prop :=
  ∀ s : ZMod p, s ^ 3 + a * s ^ 2 + b * s + c = 0 → 3 * s ^ 2 + 2 * a * s + b ≠ 0

instance (a b c : ℤ) : Decidable (goodRedMod p a b c) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  unfold goodRedMod; infer_instance

lemma norm_lt_one_iff_toZMod (z : ℤ_[p]) : ‖(z : ℚ_[p])‖ < 1 ↔ PadicInt.toZMod z = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  rfl

/-- **The mod-`p` check gives good reduction.** -/
theorem goodRed_of_mod (a b c : ℤ) (h : goodRedMod p a b c) : GoodRed p a b c := by
  intro t ht hf
  set T : ℤ_[p] := ⟨t, ht⟩
  have e1 : ((T ^ 3 + a * T ^ 2 + b * T + c : ℤ_[p]) : ℚ_[p]) = t ^ 3 + a * t ^ 2 + b * t + c := by
    push_cast [T]; rfl
  have hf' : ‖((T ^ 3 + a * T ^ 2 + b * T + c : ℤ_[p]) : ℚ_[p])‖ < 1 := by rw [e1]; exact hf
  rw [norm_lt_one_iff_toZMod] at hf'
  simp only [map_add, map_mul, map_pow, map_intCast] at hf'
  have hd := h _ hf'
  have hle : ‖((3 * T ^ 2 + 2 * a * T + b : ℤ_[p]) : ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one _
  have hnlt : ¬‖((3 * T ^ 2 + 2 * a * T + b : ℤ_[p]) : ℚ_[p])‖ < 1 := by
    rw [norm_lt_one_iff_toZMod]
    simp only [map_add, map_mul, map_pow, map_intCast, map_ofNat]
    exact hd
  have : ‖((3 * T ^ 2 + 2 * a * T + b : ℤ_[p]) : ℚ_[p])‖ = 1 := le_antisymm hle (not_lt.mp hnlt)
  have e2 : ((3 * T ^ 2 + 2 * a * T + b : ℤ_[p]) : ℚ_[p]) = 3 * t ^ 2 + 2 * a * t + b := by
    push_cast [T]; rfl
  rwa [e2] at this

end EllDV
