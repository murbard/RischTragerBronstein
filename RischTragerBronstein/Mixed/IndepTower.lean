import RischTragerBronstein.Mixed.IndepQ
import RischTragerBronstein.Mixed.KRIrr
import RischTragerBronstein.Mixed.KFRatGuess

/-!
# The recursive independence check over the code fields (linear base)

`recKF c0 k` decides independence of two points on a curve `E_{a,b}` over `Kₖ` (codes in `Kₖ`):
at `k + 1` it lifts to a polynomial model over `Kₖ(X)` (`RFC.canon`, `toRFHom`) and runs the step
(Manin / heights / descent to `Kₖ`, recursing); at `0` it lifts to `ℚ(x)` (`psiLin`) and recurses to
`ℚ` (`recQ`, Néron–Tate heights). `recKF1` is the one-point (infinite order) version.

**`recKF_sound`**, **`recKF1_sound`**: unconditional. **`recKF_complete`**, **`recKF1_complete`**:
unconditionally (height certificates exist, `ExH.certQ_exists_nc`).
-/

open Polynomial CPoly Sup FFHeight

namespace Curves.MT

variable (c0 : CPoly ℚ) [Fact (Irreducible (toPoly (fKc [c0, [1]])))]

local notation "L" => ([c0, [1]] : BPoly ℚ)

/-- Codes of `Kₖ₊₁` over `Kₖ`. -/
def frS (k : ℕ) (z : KF L (k + 1)) : Fr (KF L k) := RFC.canon (K := KF L k) z

/-- Codes of `K₀` over `ℚ`. -/
def fr0 (z : KF L 0) : Fr ℚ := RFC.canon (z.1.getD 0 0)

/-- **The recursive two-point check.** -/
def recKF : (k : ℕ) → ℕ → KF L k → KF L k → Option (KF L k × KF L k) →
    Option (KF L k × KF L k) → Bool
  | 0 => lvlI (fr0 c0) (fun _ ↦ true) recQ
  | k + 1 => lvlI (frS c0 k) (fun x ↦ (ratOfK L k x).isSome) (recKF k)

/-- **The recursive one-point check.** -/
def recKF1 : (k : ℕ) → ℕ → KF L k → KF L k → Option (KF L k × KF L k) → Bool
  | 0 => lvlI1 (fr0 c0) recQ1
  | k + 1 => lvlI1 (frS c0 k) (recKF1 k)

/-- The algebra `Kₖ₊₁ → Kₖ(X)`. -/
noncomputable abbrev algS (k : ℕ) : Algebra (KF L (k + 1)) (RatFunc (KF L k)) :=
  (RFC.toRFHom (K := KF L k)).toAlgebra

/-- The algebra `K₀ → ℚ(x)`. -/
noncomputable abbrev alg0 : Algebra (KF L 0) (RatFunc ℚ) := (psiLin c0).toAlgebra

lemma hfrS (k : ℕ) (z : KF L (k + 1)) :
    Fr.ok (frS c0 k z) ∧ Fr.val (frS c0 k z) = RFC.toRFHom (K := KF L k) z := by
  obtain ⟨h0, -, -, hv⟩ := RFC.canon_spec (K := KF L k) z
  exact ⟨h0, hv.symm⟩

lemma psiLin_eval (z : KF L 0) : psiLin c0 z = RFC.toRF (z.1.getD 0 0) := by
  have h1 : (RFC.mk ([1] : CPoly ℚ) [1] : RFC.RatFuncC ℚ) = 1 :=
    RFC.toRF_injective (by rw [RFC.toRF_const, map_one, RFC.toRF_one])
  have hf : (toPoly (fKc L)).degree = 1 := by
    simp only [fKc, List.map_cons, List.map_nil, toPoly_cons, toPoly_nil, mul_zero, add_zero, h1,
      map_one, mul_one]
    rw [add_comm, degree_X_add_C]
  have hd := NFK.degree_val (fKc L) z
  rw [hf] at hd
  have hn : (toPoly z.1).natDegree = 0 := by
    by_cases h0 : toPoly z.1 = 0
    · simp [h0]
    · rw [degree_eq_natDegree h0] at hd; exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hd)
  have hC := eq_C_of_natDegree_eq_zero hn
  unfold psiLin
  simp only [RingHom.comp_apply]
  change (AdjoinRoot.lift _ _ _) (AdjoinRoot.mk _ (toPoly z.1)) = _
  rw [AdjoinRoot.lift_mk, hC, eval₂_C, coeff_toPoly]
  rfl

lemma hfr0 (z : KF L 0) : Fr.ok (fr0 c0 z) ∧ Fr.val (fr0 c0 z) = psiLin c0 z := by
  obtain ⟨h0, -, -, hv⟩ := RFC.canon_spec (z.1.getD 0 0)
  refine ⟨h0, ?_⟩
  rw [psiLin_eval, hv]; rfl

lemma ratOfK_iff (k : ℕ) (x : KF L k) : (ratOfK L k x).isSome = true ↔ ∃ q : ℚ, x = q := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp h
    exact ⟨q, (ratOfK_spec L hq).symm⟩
  · rintro ⟨q, rfl⟩; rw [ratOfK_ratCast]; rfl

/-- **Soundness of the recursive check.** -/
theorem recKF_sound : ∀ k, RecS (recKF c0 k)
  | 0 => by
    let _ := alg0 c0
    exact lvlI_sound (fr0 c0) (hfr0 c0) (fun _ ↦ rfl) recQ_sound
  | k + 1 => by
    let _ := algS c0 k
    exact lvlI_sound (frS c0 k) (hfrS c0 k) (fun q ↦ (ratOfK_iff c0 k _).mpr ⟨q, rfl⟩)
      (recKF_sound k)

/-- **Soundness of the recursive one-point check.** -/
theorem recKF1_sound : ∀ k, RecS1 (recKF1 c0 k)
  | 0 => by
    let _ := alg0 c0
    exact lvlI1_sound (fr0 c0) (hfr0 c0) recQ1_sound
  | k + 1 => by
    let _ := algS c0 k
    exact lvlI1_sound (frS c0 k) (hfrS c0 k) (recKF1_sound k)

/-- **Completeness of the recursive check** (unconditional). -/
theorem recKF_complete : ∀ k, RecC (recKF c0 k)
  | 0 => by
    let _ := alg0 c0
    exact lvlI_complete (fr0 c0) (hfr0 c0) recQ_complete
  | k + 1 => by
    let _ := algS c0 k
    exact lvlI_complete (frS c0 k) (hfrS c0 k) (recKF_complete k)

/-- **Completeness of the recursive one-point check** (unconditional). -/
theorem recKF1_complete : ∀ k, RecC1 (recKF1 c0 k)
  | 0 => by
    let _ := alg0 c0
    exact lvlI1_complete (fr0 c0) (hfr0 c0) recQ1_complete
  | k + 1 => by
    let _ := algS c0 k
    exact lvlI1_complete (frS c0 k) (hfrS c0 k) (recKF1_complete k)

end Curves.MT
