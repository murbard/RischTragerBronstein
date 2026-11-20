import RischTragerBronstein.Mixed.NFEmbed
import RischTragerBronstein.Mixed.KXCertBridgeK

/-!
# Embeddings of `ℚ(√d)` for the bridge check over `k₀`

`grp_of_chkK` needs, for every field `K` of characteristic `0` and roots `rᵢ` of the class
generators and `s` of `κ`, an embedding `j : k₀ → K` with `j ρᵢ = rᵢ`, `j σ = ±s`. For
`k₀ = ℚ(√d)` (`QuadraticAlgebra ℚ d 0`) and one quadratic generator this is `qaEmbed` (`qa_lift`):

* `gens = [d]`, `ρs = [√d]`, and `σ = c√d` (`κ = c² d`) or `σ = c` (`κ = c²`);
* `gens = []`, `ρs = []`, `σ = c√d` (`κ = c² d`, the root of `d` in `K` being `s / c`).
-/

namespace NFEmbed

variable (d : ℚ)

/-- `√d ∈ ℚ(√d)`. -/
def qaW : QuadraticAlgebra ℚ d 0 := ⟨0, 1⟩

/-- How `σ` sits in `ℚ(√d)`. -/
inductive SigmaForm (d κ : ℚ) : QuadraticAlgebra ℚ d 0 → Prop
  | rad (c : ℚ) (hc : c ≠ 0) (hκ : κ = c ^ 2 * d) : SigmaForm d κ ⟨0, c⟩
  | rat (c : ℚ) (hκ : κ = c ^ 2) : SigmaForm d κ ⟨c, 0⟩

/-- **The lift.** -/
theorem qa_lift {K : Type*} [Field K] [CharZero K] (gens : List ℚ) (κ : ℚ)
    (ρs : List (QuadraticAlgebra ℚ d 0)) (σ : QuadraticAlgebra ℚ d 0)
    (hg : (gens = [d] ∧ ρs = [qaW d]) ∨ (gens = [] ∧ ρs = [] ∧ ∃ c, c ≠ 0 ∧ κ = c ^ 2 * d ∧
      σ = ⟨0, c⟩))
    (hσ : SigmaForm d κ σ)
    (rs : List K) (s : K) (hl : rs.length = ρs.length)
    (hsq : ∀ i (hi : i < rs.length) (hi' : i < gens.length), rs[i] ^ 2 = (gens[i] : K))
    (hs : s ^ 2 = (κ : K)) :
    ∃ j : QuadraticAlgebra ℚ d 0 →+* K,
      (∀ i (hi : i < ρs.length) (hi' : i < rs.length), j ρs[i] = rs[i]) ∧ (j σ = s ∨ j σ = -s) := by
  -- a root of `d` in `K`
  obtain ⟨r, hr, hrρ⟩ : ∃ r : K, r * r = algebraMap ℚ K d ∧
      (∀ i (hi : i < ρs.length) (hi' : i < rs.length), ρs[i] = qaW d ∧ rs[i] = r) := by
    rcases hg with ⟨hg, hρ⟩ | ⟨hg, hρ, c, hc, hκ, -⟩
    · subst hg hρ
      have h0 : 0 < rs.length := by simp at hl; omega
      have h := hsq 0 h0 (by simp)
      simp only [List.getElem_cons_zero] at h
      refine ⟨rs[0], by rw [← sq, h]; simp, fun i hi hi' ↦ ?_⟩
      have : i = 0 := by simpa using hi
      subst this
      exact ⟨rfl, rfl⟩
    · subst hρ
      refine ⟨s / c, ?_, fun i hi ↦ absurd hi (by simp)⟩
      have hc' : (c : K) ≠ 0 := by exact_mod_cast hc
      rw [div_mul_div_comm, ← sq, hs, hκ]
      field_simp
      simp only [eq_ratCast]; push_cast; ring
  refine ⟨(qaEmbed d r hr).toRingHom, fun i hi hi' ↦ ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hrρ i hi hi'
    rw [h1, h2]
    exact qaEmbed_omega d r hr
  · have hsq' : ∀ t : K, t ^ 2 = s ^ 2 → t = s ∨ t = -s := fun t ht ↦ sq_eq_sq_iff_eq_or_eq_neg.mp ht
    apply hsq'
    rcases hσ with ⟨c, hc, hκ⟩ | ⟨c, hκ⟩
    · show (qaEmbed d r hr ⟨0, c⟩) ^ 2 = s ^ 2
      rw [qaEmbed_apply, hs, hκ]
      simp only [map_zero, zero_add]
      rw [mul_pow, sq r, hr]
      simp only [eq_ratCast]; push_cast; ring
    · show (qaEmbed d r hr ⟨c, 0⟩) ^ 2 = s ^ 2
      rw [qaEmbed_apply, hs, hκ]
      simp only [eq_ratCast]; push_cast; ring

end NFEmbed
