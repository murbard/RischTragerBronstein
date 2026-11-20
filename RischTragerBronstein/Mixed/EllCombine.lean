import RischTragerBronstein.Mixed.EllDescent

/-!
# Combined pairings, and the trace descent homomorphism

* `pullPair`: a pairing `B` on `G` pulled back along `t : H →+ G`; `sumPair`, symmetry lemmas, and
  `indep_of_pulls`: a non-zero Gram determinant of `∑ Bᵢ(tᵢ ·, tᵢ ·)` certifies independence in `H`.
  Over a quadratic extension `K'/F` this is the complete test: `E(K') ⊗ ℚ` splits into the trace
  part `E(F) ⊗ ℚ` and the twist part, and the Néron–Tate pairing of `E(K')` is (up to the factor
  `2`) the sum of the pulled-back pairings.
* `traceHom`: `P ↦ descent of P + σP`, a group homomorphism `W(K') →+ W(F)` (`σ² = 1`, fixed
  field `F`).
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace FFHeight

open scoped Classical

section Pair

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- Pull back a pairing along a homomorphism. -/
def pullPair (B : G →+ G →+ ℝ) (t : H →+ G) : H →+ H →+ ℝ :=
  { toFun := fun P ↦ (B (t P)).comp t
    map_zero' := by ext Q; simp
    map_add' := fun P P' ↦ by ext Q; simp }

lemma pullPair_apply (B : G →+ G →+ ℝ) (t : H →+ G) (P Q : H) : pullPair B t P Q = B (t P) (t Q) :=
  rfl

lemma pullPair_symm (B : G →+ G →+ ℝ) (hB : ∀ P Q, B P Q = B Q P) (t : H →+ G) (P Q : H) :
    pullPair B t P Q = pullPair B t Q P := by
  simp only [pullPair_apply]; exact hB _ _

/-- **Independence from a sum of pulled-back pairings.** -/
theorem indep_of_pulls {G₂ : Type*} [AddCommGroup G₂] (B₁ : G →+ G →+ ℝ) (B₂ : G₂ →+ G₂ →+ ℝ)
    (h₁ : ∀ P Q, B₁ P Q = B₁ Q P) (h₂ : ∀ P Q, B₂ P Q = B₂ Q P) (t₁ : H →+ G) (t₂ : H →+ G₂)
    (D Z : H) (hg : MWPair.gram (pullPair B₁ t₁ + pullPair B₂ t₂) D Z ≠ 0)
    (m n : ℤ) (hrel : m • D = n • Z) : m = 0 ∧ n = 0 :=
  MWPair.gram_ne_zero_indep _ (fun P Q ↦ by
    simp only [AddMonoidHom.add_apply, pullPair_symm B₁ h₁, pullPair_symm B₂ h₂]) D Z hg m n hrel

end Pair

section Trace

variable {F K' : Type*} [Field F] [Field K'] [Algebra F K']
variable (W : Affine F) (σ : K' →ₐ[F] K')

lemma map_invol (hσ : ∀ z, σ (σ z) = z) (P : (W⁄K').Point) :
    Point.map σ (Point.map σ P) = P := by
  rw [Point.map_map]
  have : σ.comp σ = AlgHom.id F K' := by ext z; exact hσ z
  rw [this]
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

lemma trace_fixed (hσ : ∀ z, σ (σ z) = z) (P : (W⁄K').Point) :
    Point.map σ (P + Point.map σ P) = P + Point.map σ P := by
  rw [map_add, map_invol W σ hσ, add_comm]

/-- The descent of `P + σP`. -/
noncomputable def traceP (hσ : ∀ z, σ (σ z) = z)
    (hfix : ∀ z : K', σ z = z → ∃ c : F, algebraMap F K' c = z) (P : (W⁄K').Point) : (W⁄F).Point :=
  (fixed_descends W σ hfix _ (trace_fixed W σ hσ P)).choose

lemma traceP_spec (hσ : ∀ z, σ (σ z) = z)
    (hfix : ∀ z : K', σ z = z → ∃ c : F, algebraMap F K' c = z) (P : (W⁄K').Point) :
    Point.map (Algebra.ofId F K') (traceP W σ hσ hfix P) = P + Point.map σ P :=
  (fixed_descends W σ hfix _ (trace_fixed W σ hσ P)).choose_spec

/-- **The trace homomorphism** `W(K') →+ W(F)`. -/
noncomputable def traceHom (hσ : ∀ z, σ (σ z) = z)
    (hfix : ∀ z : K', σ z = z → ∃ c : F, algebraMap F K' c = z) : (W⁄K').Point →+ (W⁄F).Point where
  toFun := traceP W σ hσ hfix
  map_zero' := by
    apply Point.map_injective (Algebra.ofId F K')
    rw [traceP_spec, map_zero, map_zero, add_zero]
  map_add' := fun P Q ↦ by
    apply Point.map_injective (Algebra.ofId F K')
    rw [map_add, traceP_spec, traceP_spec, traceP_spec, map_add]; abel

lemma traceHom_spec (hσ : ∀ z, σ (σ z) = z)
    (hfix : ∀ z : K', σ z = z → ∃ c : F, algebraMap F K' c = z) (P : (W⁄K').Point) :
    Point.map (Algebra.ofId F K') (traceHom W σ hσ hfix P) = P + Point.map σ P :=
  traceP_spec W σ hσ hfix P

end Trace

end FFHeight
