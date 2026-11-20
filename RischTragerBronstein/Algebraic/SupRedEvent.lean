import RischTragerBronstein.Algebraic.SupRedRF
import RischTragerBronstein.Algebraic.SupRedNFK

/-!
# Elements that reduce well at all large primes

For a family of reductions `Rf p : RedFns p K` (over the primes satisfying `G`), `EvOk G Rf x`:
`x` is integral (`ok`) at every large prime of `G`. `rf_evOk`: for `K(t)` reduced at a fixed integer
residue `t ↦ c`, `x = P/Q` (canonical) is eventually integral when the coefficients of `P, Q` and
`Q(c)⁻¹` are (the residue of `Q(c)` is then a unit). `rat_evOk`: every rational is eventually
integral. `nfk_evOk`: an element of `K[y]/(f)` is when its coefficients are.
-/

open Polynomial CPoly CPoly.Kron RFC

namespace Sup

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

/-- **Eventually integral.** -/
def EvOk (G : ℕ → Prop) (Rf : (p : ℕ) → [Fact p.Prime] → RedFns p K) (x : K) : Prop :=
  ∃ T : ℕ, ∀ (p : ℕ) [Fact p.Prime], G p → T < p → (Rf p).ok x = true

lemma evOk_list (G : ℕ → Prop) (Rf : (p : ℕ) → [Fact p.Prime] → RedFns p K) (l : List K)
    (h : ∀ a ∈ l, EvOk G Rf a) :
    ∃ T : ℕ, ∀ (p : ℕ) [Fact p.Prime], G p → T < p → ∀ a ∈ l, (Rf p).ok a = true := by
  induction l with
  | nil => exact ⟨0, fun _ _ _ _ a ha ↦ absurd ha (by simp)⟩
  | cons b l ih =>
    obtain ⟨T1, h1⟩ := h b (by simp)
    obtain ⟨T2, h2⟩ := ih fun a ha ↦ h a (List.mem_cons_of_mem b ha)
    refine ⟨max T1 T2, fun p _ hG hT a ha ↦ ?_⟩
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h1 p hG (lt_of_le_of_lt (le_max_left _ _) hT)
    · exact h2 p hG (lt_of_le_of_lt (le_max_right _ _) hT) a ha

/-- **The level step**: `K(t)` reduced at `t ↦ c`. -/
theorem rf_evOk (G : ℕ → Prop) (Rf : (p : ℕ) → [Fact p.Prime] → RedFns p K)
    (hV : ∀ (p : ℕ) [Fact p.Prime], G p → ∃ φ : K →+* ℚ_[p], RedValid p (Rf p) φ) (c : ℤ)
    (x : RatFuncC K) (hco : ∀ a ∈ (canon x).1 ++ (canon x).2, EvOk G Rf a)
    (hQ0 : (toPoly (canon x).2).eval (c : K) ≠ 0)
    (hinv : EvOk G Rf ((toPoly (canon x).2).eval (c : K))⁻¹) :
    EvOk G (fun p _ ↦ rfFns p (Rf p) (c : ZMod p)) x := by
  obtain ⟨T1, h1⟩ := evOk_list G Rf _ hco
  obtain ⟨T2, h2⟩ := hinv
  refine ⟨max T1 T2, fun p _ hG hT ↦ ?_⟩
  have hok := h1 p hG (lt_of_le_of_lt (le_max_left _ _) hT)
  have hokI := h2 p hG (lt_of_le_of_lt (le_max_right _ _) hT)
  obtain ⟨φ, hφ⟩ := hV p hG
  have hP : ∀ a ∈ (canon x).1, (Rf p).ok a = true := fun a ha ↦ hok a (List.mem_append_left _ ha)
  have hQ : ∀ a ∈ (canon x).2, (Rf p).ok a = true := fun a ha ↦ hok a (List.mem_append_right _ ha)
  simp only [rfFns, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨hP, hQ⟩, fun h0 ↦ ?_⟩
  -- the value of `Q(c)` is a `p`-adic unit
  obtain ⟨w, hw, hwr⟩ := lift_list (R := Rf p) φ hφ (c : ℤ_[p]) (canon x).2 hQ
  obtain ⟨z, hz, hzr⟩ := hφ _ hokI
  have hcz : PadicInt.toZMod (c : ℤ_[p]) = (c : ZMod p) := by simp
  rw [hcz, h0] at hwr
  have e1 : φ ((toPoly (canon x).2).eval (c : K)) = (w : ℚ_[p]) := by
    rw [← hw, ← eval₂_at_apply]
    congr 1
    simp
  have hwz : (w : ℚ_[p]) * algebraMap ℤ_[p] ℚ_[p] z = 1 := by
    rw [← e1, ← hz, ← map_mul, mul_inv_cancel₀ hQ0, map_one]
  have hwz' : w * z = 1 := by
    apply PadicInt.ext
    rw [PadicInt.coe_mul, PadicInt.coe_one]
    exact hwz
  have := congrArg PadicInt.toZMod hwz'
  rw [map_mul, map_one, hwr, zero_mul] at this
  exact zero_ne_one this

/-- Every rational is eventually integral. -/
theorem rat_evOk (G : ℕ → Prop) (q : ℚ) : EvOk G (fun p _ ↦ ratFns p) q :=
  ⟨q.den, fun p _ _ hT ↦ by
    simp only [ratFns, bne_iff_ne, ne_eq]
    rw [Nat.mod_eq_of_lt hT]; exact q.den_nz⟩

/-- An element of `K[y]/(f)` is eventually integral when its coefficients are. -/
theorem nfk_evOk (G : ℕ → Prop) (Rf : (p : ℕ) → [Fact p.Prime] → RedFns p K) (f : CPoly K)
    (s : (p : ℕ) → ZMod p) (z : NFK.NF f) (h : ∀ a ∈ z.1, EvOk G Rf a) :
    EvOk G (fun p _ ↦ nfkFns (Rf p) f (s p)) z := by
  obtain ⟨T, hT⟩ := evOk_list G Rf _ h
  exact ⟨T, fun p _ hG hp ↦ by
    simp only [nfkFns, List.all_eq_true]; exact hT p hG hp⟩

end Sup
