import RischTragerBronstein.Liouville.StepPrimitive
import RischTragerBronstein.Liouville.Transcendence

/-!
# A second primitive over a primitive extension

Let `t₁` be a primitive over `F` (`t₁′ = η₁`, transcendental, no new constants) and `η₂ ∈ F`.
An antiderivative of `η₂` inside `F(t₁)` must have the form `c t₁ + d` (`c` constant, `d ∈ F`).
Hence, if `η₂ ≠ c η₁ + d′` for all such `c, d` — a **limited-integration** statement over `F` — then
`η₂` is not a derivative in `F(t₁)`, and a second primitive `t₂′ = η₂` is transcendental over
`F(t₁)`. This is the inductive step for towers of several primitives (`log x`, `log (x + 1)`, …).
-/

open IntermediateField Polynomial

namespace Differential

variable {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
variable [Differential F] [Differential E] [DifferentialAlgebra F E]

theorem deriv_ne_of_not_limited (t : E) (htr : Transcendental F t) (η : F)
    (ht : t′ = algebraMap F E η)
    (hconst : ∀ x ∈ F⟮t⟯, x′ = 0 → x ∈ Set.range (algebraMap F E)) (α : F)
    (hα : ∀ c₀ d : F, c₀′ = 0 → α ≠ c₀ * η + d′) (y : E) (hy : y ∈ F⟮t⟯) :
    y′ ≠ algebraMap F E α := by
  intro h
  obtain ⟨_e, c₀, d, _he, hc₀, hrel⟩ := liouville_step_primitive (ι := Empty) t htr η ht hconst ∅
    (fun _ ↦ 0) (fun _ ↦ 1) (by simp) y hy α (by simp [h])
  simp only [Finset.sum_empty, zero_add] at hrel
  exact hα c₀ d hc₀ hrel

/-- A second primitive is transcendental over `F(t₁)` when its derivative admits no limited
integral over `F`. -/
theorem transcendental_second_primitive (t₁ t₂ : E) (htr : Transcendental F t₁) (η₁ η₂ : F)
    (ht₁ : t₁′ = algebraMap F E η₁) (ht₂ : t₂′ = algebraMap F E η₂)
    (hconst : ∀ x ∈ F⟮t₁⟯, x′ = 0 → x ∈ Set.range (algebraMap F E))
    (hα : ∀ c₀ d : F, c₀′ = 0 → η₂ ≠ c₀ * η₁ + d′)
    [Differential F⟮t₁⟯] [DifferentialAlgebra F⟮t₁⟯ E]
    (hcoe : ∀ z : F⟮t₁⟯, ((z′ : F⟮t₁⟯) : E) = (z : E)′) :
    Transcendental F⟮t₁⟯ t₂ := by
  refine transcendental_primitive (algebraMap F F⟮t₁⟯ η₂) ht₂ fun b hb ↦ ?_
  exact deriv_ne_of_not_limited t₁ htr η₁ ht₁ hconst η₂ hα (b : E) b.2
    (by rw [← hcoe, hb]; rfl)

end Differential
