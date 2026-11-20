import RischTragerBronstein.Rational.HermiteStep
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.Prime

/-!
# Local analysis of a derivation at a prime

Let `A` be a differential domain with fraction field `K`, and `p ∈ A` a prime element.

* `regularAt K p` is the local ring `O_p ⊂ K` of fractions with denominator prime to `p`.
* `IsUnitAt K p g` says that `g` is a unit of `O_p`.
* `deriv_mem_regularAt`: the derivation preserves `O_p` (for every prime `p`).
* `isUnitAt_deriv_pole`: if `p` is **normal** (`p ∤ p′`) and `p ∤ k`, the derivative of a function
  with a pole of order exactly `k ≥ 1` at `p` has a pole of order exactly `k + 1`:
  `(g / p ^ k)′ * p ^ (k + 1)` is a unit of `O_p` whenever `g` is.

These are the facts about orders of poles on which the proof of Liouville's theorem for
transcendental extensions rests (Rosenlicht; Bronstein §4.4, Theorem 4.4.2).
-/

set_option linter.unusedSectionVars false

namespace Differential

variable {A : Type*} (K : Type*) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
variable [IsFractionRing A K]

local notation "φ" => algebraMap A K

/-- The local ring `O_p` of elements of `K = Frac A` regular at the prime `p`. -/
def regularAt (p : A) (hp : Prime p) : Subring K where
  carrier := {f | ∃ a b : A, ¬p ∣ b ∧ f * φ b = φ a}
  mul_mem' := by
    rintro f g ⟨a, b, hb, h⟩ ⟨c, d, hd, h'⟩
    refine ⟨a * c, b * d, fun hdvd ↦ (hp.dvd_or_dvd hdvd).elim hb hd, ?_⟩
    rw [map_mul, map_mul, ← h, ← h']
    ring
  one_mem' := ⟨1, 1, hp.not_dvd_one, by simp⟩
  add_mem' := by
    rintro f g ⟨a, b, hb, h⟩ ⟨c, d, hd, h'⟩
    refine ⟨a * d + c * b, b * d, fun hdvd ↦ (hp.dvd_or_dvd hdvd).elim hb hd, ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']
    ring
  zero_mem' := ⟨0, 1, hp.not_dvd_one, by simp⟩
  neg_mem' := by
    rintro f ⟨a, b, hb, h⟩
    exact ⟨-a, b, hb, by rw [map_neg, ← h]; ring⟩

/-- `g` is a unit of the local ring `O_p`. -/
def IsUnitAt (p : A) (g : K) : Prop := ∃ a b : A, ¬p ∣ a ∧ ¬p ∣ b ∧ g * φ b = φ a

variable {K} {p : A} (hp : Prime p)

lemma mem_regularAt {f : K} : f ∈ regularAt K p hp ↔ ∃ a b : A, ¬p ∣ b ∧ f * φ b = φ a := Iff.rfl

lemma algebraMap_mem_regularAt (a : A) : φ a ∈ regularAt K p hp := ⟨a, 1, hp.not_dvd_one, by simp⟩

lemma IsUnitAt.mem_regularAt {g : K} (hg : IsUnitAt K p g) : g ∈ regularAt K p hp :=
  let ⟨a, b, _, hb, h⟩ := hg
  ⟨a, b, hb, h⟩

include hp in
lemma map_ne_zero_of_not_dvd {b : A} (hb : ¬p ∣ b) : φ b ≠ 0 := by
  intro h
  rw [map_eq_zero_iff _ (IsFractionRing.injective A K)] at h
  exact hb (h ▸ dvd_zero p)

include hp in
lemma IsUnitAt.inv_mem_regularAt {g : K} (hg : IsUnitAt K p g) : g⁻¹ ∈ regularAt K p hp := by
  obtain ⟨a, b, ha, hb, h⟩ := hg
  have ha0 : φ a ≠ 0 := map_ne_zero_of_not_dvd hp ha
  have hb0 : φ b ≠ 0 := map_ne_zero_of_not_dvd hp hb
  refine ⟨b, a, ha, ?_⟩
  have hg0 : g ≠ 0 := by rintro rfl; simp at h; exact ha0 h.symm
  rw [← h]
  field_simp

/-- A unit of `O_p` is not in the maximal ideal: `g ≠ p * f` for `f ∈ O_p`. -/
lemma IsUnitAt.ne_mul {g : K} (hg : IsUnitAt K p g) {f : K} (hf : f ∈ regularAt K p hp) :
    g ≠ φ p * f := by
  obtain ⟨a, b, ha, hb, h⟩ := hg
  obtain ⟨c, d, hd, h'⟩ := hf
  intro heq
  -- `a d = p c b` in `A`
  have : φ (a * d) = φ (p * c * b) := by
    rw [map_mul, map_mul, map_mul, ← h, ← h', heq]
    ring
  have h2 := IsFractionRing.injective A K this
  have : p ∣ a * d := ⟨c * b, by rw [h2]; ring⟩
  exact (hp.dvd_or_dvd this).elim ha hd

variable [Differential A] [Differential K] [DifferentialAlgebra A K]

/-- The derivation maps the local ring `O_p` to itself. -/
theorem deriv_mem_regularAt {f : K} (hf : f ∈ regularAt K p hp) : f′ ∈ regularAt K p hp := by
  obtain ⟨a, b, hb, h⟩ := hf
  refine ⟨a′ * b - a * b′, b * b, fun hdvd ↦ (hp.dvd_or_dvd hdvd).elim hb hb, ?_⟩
  have hd := congrArg (fun y : K ↦ y′) h
  simp only [Derivation.leibniz, deriv_algebraMap, smul_eq_mul] at hd
  rw [map_sub, map_mul, map_mul, map_mul, ← h]
  linear_combination (φ b) * hd

include hp in
/-- At a normal prime, differentiation raises the order of a pole by exactly one. -/
theorem isUnitAt_deriv_pole (hnorm : ¬p ∣ p′) {g : K} (hg : IsUnitAt K p g) (k : ℕ)
    (hk : ¬p ∣ (k : A)) : IsUnitAt K p ((g / φ p ^ k)′ * φ p ^ (k + 1)) := by
  obtain ⟨a, b, ha, hb, h⟩ := hg
  have hp0 : φ p ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A K)]; exact hp.ne_zero
  have hb0 : φ b ≠ 0 := map_ne_zero_of_not_dvd hp hb
  -- `(g / p ^ k)′ * p ^ (k + 1) = g′ p - k g p′`
  have hform : (g / φ p ^ k)′ * φ p ^ (k + 1) = g′ * φ p - k * g * φ p′ := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Derivation.leibniz_div, deriv_pow_succ, deriv_algebraMap]
    simp only [smul_eq_mul]
    field_simp
    push_cast
    ring
  rw [hform]
  refine ⟨(a′ * b - a * b′) * p - k * a * b * p′, b * b, ?_,
    fun hdvd ↦ (hp.dvd_or_dvd hdvd).elim hb hb, ?_⟩
  · intro hdvd
    have h1 : p ∣ (k : A) * a * b * p′ := by
      have := dvd_sub (Dvd.intro_left ((a′ * b - a * b′)) rfl : p ∣ (a′ * b - a * b′) * p) hdvd
      simpa using this
    rcases hp.dvd_or_dvd h1 with h2 | h2
    · rcases hp.dvd_or_dvd h2 with h3 | h3
      · rcases hp.dvd_or_dvd h3 with h4 | h4
        · exact hk h4
        · exact ha h4
      · exact hb h3
    · exact hnorm h2
  · have hd := congrArg (fun y : K ↦ y′) h
    simp only [Derivation.leibniz, deriv_algebraMap, smul_eq_mul] at hd
    simp only [map_sub, map_mul, map_natCast]
    rw [← h]
    linear_combination (φ b * φ p) * hd

end Differential
