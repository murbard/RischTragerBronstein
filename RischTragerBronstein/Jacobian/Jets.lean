import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Jets of functions `a + b y` on `y² = f(x)` at non-Weierstrass points

For a point `(x₀, Y₀)` with `2Y₀` a unit, a *branch jet* of order `ℓ` is a polynomial `V` in the
local variable `s = x − x₀` with `V(0) = Y₀` and `V² ≡ f(x₀ + s) (mod sˡ)`; it is unique modulo
`sˡ` (`branch_unique`). The function `a + b y` *vanishes to order `ℓ`* at `(x₀, Y₀)` when
`a(x₀ + s) + b(x₀ + s) V ≡ 0 (mod sˡ)` (`VanishAt`). Everything is over an arbitrary commutative
ring, so that the same statements can be reduced modulo a prime.

* `dvd_of_vanish_both`: vanishing to order `ℓ` at `(x₀, Y₀)` and at `(x₀, −Y₀)` forces
  `(x − x₀)ˡ ∣ a` and `(x − x₀)ˡ ∣ b`;
* `tangent_jet`: if the jet at `(x₀, Y₀)` is `λ sˡ⁻¹` and the one at `(x₀, −Y₀)` vanishes, then
  `(x − x₀)ˡ⁻¹` divides `a` and `b`, and `λ = 0` when `b = 0`.
-/

open Polynomial

namespace Jac

variable {R : Type*} [CommRing R]

/-- The jet of `a + b y` at `x₀` along the branch `V` (a polynomial in `s = x − x₀`). -/
noncomputable def jet (a b : R[X]) (x₀ : R) (V : R[X]) : R[X] :=
  a.comp (X + C x₀) + b.comp (X + C x₀) * V

/-- `V` is a branch jet of order `ℓ` of `√f` at `(x₀, Y₀)`. -/
def IsBranch (f : R[X]) (x₀ Y₀ : R) (ℓ : ℕ) (V : R[X]) : Prop :=
  V.coeff 0 = Y₀ ∧ X ^ ℓ ∣ V ^ 2 - f.comp (X + C x₀)

/-- `a + b y` vanishes to order `ℓ` at the point `(x₀, Y₀)` of `y² = f`. -/
def VanishAt (f a b : R[X]) (x₀ Y₀ : R) (ℓ : ℕ) : Prop :=
  ∃ V, IsBranch f x₀ Y₀ ℓ V ∧ X ^ ℓ ∣ jet a b x₀ V

/-- Cancelling a factor with unit constant term modulo `Xˡ`. -/
lemma X_pow_dvd_of_mul {c h : R[X]} (hc : IsUnit (c.coeff 0)) {ℓ : ℕ} (hd : X ^ ℓ ∣ c * h) :
    X ^ ℓ ∣ h := by
  rw [X_pow_dvd_iff] at hd ⊢
  intro d hd'
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have h1 := hd d hd'
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ c.coeff i * h.coeff j),
      Finset.sum_range_succ'] at h1
    have h2 : ∑ k ∈ Finset.range d, c.coeff (k + 1) * h.coeff (d - (k + 1)) = 0 :=
      Finset.sum_eq_zero fun k hk ↦ by
        rw [ih (d - (k + 1)) (by simp at hk; omega) (by omega), mul_zero]
    rw [h2, zero_add, Nat.sub_zero] at h1
    exact (hc.mul_right_eq_zero).mp h1

/-- Cancelling a non-zero constant modulo `Xˡ` over a domain. -/
lemma X_pow_dvd_of_C_mul [IsDomain R] {r : R} (hr : r ≠ 0) {h : R[X]} {ℓ : ℕ}
    (hd : X ^ ℓ ∣ C r * h) : X ^ ℓ ∣ h := by
  rw [X_pow_dvd_iff] at hd ⊢
  intro d hd'
  have := hd d hd'
  rw [coeff_C_mul] at this
  exact (mul_eq_zero.mp this).resolve_left hr

/-- **Uniqueness of branch jets.** -/
lemma branch_unique {f : R[X]} {x₀ Y₀ : R} {ℓ : ℕ} {V W : R[X]} (hY : IsUnit (2 * Y₀))
    (hV : IsBranch f x₀ Y₀ ℓ V) (hW : IsBranch f x₀ Y₀ ℓ W) : X ^ ℓ ∣ V - W := by
  apply X_pow_dvd_of_mul (c := V + W)
  · rw [coeff_add, hV.1, hW.1, ← two_mul]; exact hY
  · have e : (V + W) * (V - W) = (V ^ 2 - f.comp (X + C x₀)) - (W ^ 2 - f.comp (X + C x₀)) := by
      ring
    rw [e]; exact dvd_sub hV.2 hW.2

/-- The branch at `(x₀, −Y₀)` is the negative of the branch at `(x₀, Y₀)`. -/
lemma IsBranch.neg {f : R[X]} {x₀ Y₀ : R} {ℓ : ℕ} {V : R[X]} (hV : IsBranch f x₀ Y₀ ℓ V) :
    IsBranch f x₀ (-Y₀) ℓ (-V) :=
  ⟨by rw [coeff_neg, hV.1], by rw [neg_sq]; exact hV.2⟩

lemma IsBranch.map {S : Type*} [CommRing S] (φ : R →+* S) {f : R[X]} {x₀ Y₀ : R} {ℓ : ℕ}
    {V : R[X]} (hV : IsBranch f x₀ Y₀ ℓ V) : IsBranch (f.map φ) (φ x₀) (φ Y₀) ℓ (V.map φ) := by
  refine ⟨by rw [coeff_map, hV.1], ?_⟩
  have := Polynomial.map_dvd φ hV.2
  simpa [Polynomial.map_sub, Polynomial.map_pow, map_comp] using this

lemma jet_map {S : Type*} [CommRing S] (φ : R →+* S) (a b : R[X]) (x₀ : R) (V : R[X]) :
    (jet a b x₀ V).map φ = jet (a.map φ) (b.map φ) (φ x₀) (V.map φ) := by
  simp [jet, map_comp]

lemma jet_add (a b a' b' : R[X]) (x₀ : R) (V : R[X]) :
    jet (a + a') (b + b') x₀ V = jet a b x₀ V + jet a' b' x₀ V := by
  simp only [jet, add_comp]; ring

lemma jet_C_mul (r : R) (a b : R[X]) (x₀ : R) (V : R[X]) :
    jet (C r * a) (C r * b) x₀ V = C r * jet a b x₀ V := by
  simp only [jet, mul_comp, C_comp]; ring

lemma VanishAt.map {S : Type*} [CommRing S] (φ : R →+* S) {f a b : R[X]} {x₀ Y₀ : R} {ℓ : ℕ}
    (h : VanishAt f a b x₀ Y₀ ℓ) : VanishAt (f.map φ) (a.map φ) (b.map φ) (φ x₀) (φ Y₀) ℓ := by
  obtain ⟨V, hV, hj⟩ := h
  exact ⟨V.map φ, hV.map φ, by rw [← jet_map]; simpa using Polynomial.map_dvd φ hj⟩

/-- `Xˡ ∣ P(x₀ + s)` means `(x − x₀)ˡ ∣ P`. -/
lemma dvd_of_comp {P : R[X]} {x₀ : R} {ℓ : ℕ} (h : X ^ ℓ ∣ P.comp (X + C x₀)) :
    (X - C x₀) ^ ℓ ∣ P := by
  obtain ⟨q, hq⟩ := h
  have e := congrArg (fun r : R[X] ↦ r.comp (X - C x₀)) hq
  simp only [comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X, mul_comp,
    pow_comp] at e
  rw [e]; exact dvd_mul_right _ _

lemma comp_dvd_of_dvd {P : R[X]} {x₀ : R} {ℓ : ℕ} (h : (X - C x₀) ^ ℓ ∣ P) :
    X ^ ℓ ∣ P.comp (X + C x₀) := by
  obtain ⟨q, hq⟩ := h
  rw [hq, mul_comp, pow_comp, sub_comp, X_comp, C_comp, add_sub_cancel_right]
  exact dvd_mul_right _ _

/-- **Vanishing on both points over `x₀`.** -/
theorem dvd_of_vanish_both {f a b : R[X]} {x₀ Y₀ : R} {ℓ : ℕ} (hY : IsUnit (2 * Y₀))
    (h₁ : VanishAt f a b x₀ Y₀ ℓ) (h₂ : VanishAt f a b x₀ (-Y₀) ℓ) :
    (X - C x₀) ^ ℓ ∣ a ∧ (X - C x₀) ^ ℓ ∣ b := by
  obtain ⟨V, hV, hj₁⟩ := h₁
  obtain ⟨W, hW, hj₂⟩ := h₂
  have hVW : X ^ ℓ ∣ V - -W := branch_unique hY hV (by simpa using hW.neg)
  have hB : X ^ ℓ ∣ b.comp (X + C x₀) := by
    apply X_pow_dvd_of_mul (c := 2 * V)
    · rw [show (2 : R[X]) = C (2 : R) from (map_ofNat C 2).symm, coeff_C_mul, hV.1]; exact hY
    · have e : 2 * V * b.comp (X + C x₀) = (jet a b x₀ V - jet a b x₀ W) +
          b.comp (X + C x₀) * (V - -W) := by
        simp only [jet]; ring
      rw [e]; exact dvd_add (dvd_sub hj₁ hj₂) (Dvd.dvd.mul_left hVW _)
  have hA : X ^ ℓ ∣ a.comp (X + C x₀) := by
    have e : a.comp (X + C x₀) = jet a b x₀ V - b.comp (X + C x₀) * V := by simp only [jet]; ring
    rw [e]; exact dvd_sub hj₁ (Dvd.dvd.mul_right hB _)
  exact ⟨dvd_of_comp hA, dvd_of_comp hB⟩

/-- **The tangent computation.** -/
theorem tangent_jet {f a b V W : R[X]} {x₀ Y₀ lam : R} {m : ℕ} (hY : IsUnit (2 * Y₀))
    (hV : IsBranch f x₀ Y₀ (m + 1) V) (hW : IsBranch f x₀ (-Y₀) (m + 1) W)
    (h₁ : X ^ (m + 1) ∣ jet a b x₀ V - C lam * X ^ m) (h₂ : X ^ (m + 1) ∣ jet a b x₀ W) :
    (X - C x₀) ^ m ∣ a ∧ (X - C x₀) ^ m ∣ b ∧ (b = 0 → lam = 0) := by
  have hVW : X ^ (m + 1) ∣ V - -W := branch_unique hY hV (by simpa using hW.neg)
  have key : X ^ (m + 1) ∣ 2 * V * b.comp (X + C x₀) - C lam * X ^ m := by
    have e : 2 * V * b.comp (X + C x₀) - C lam * X ^ m =
        ((jet a b x₀ V - C lam * X ^ m) - jet a b x₀ W) + b.comp (X + C x₀) * (V - -W) := by
      simp only [jet]; ring
    rw [e]; exact dvd_add (dvd_sub h₁ h₂) (Dvd.dvd.mul_left hVW _)
  have hm : X ^ m ∣ X ^ (m + 1) := pow_dvd_pow (X : R[X]) (Nat.le_succ m)
  have hB : X ^ m ∣ b.comp (X + C x₀) := by
    apply X_pow_dvd_of_mul (c := 2 * V)
    · rw [show (2 : R[X]) = C (2 : R) from (map_ofNat C 2).symm, coeff_C_mul, hV.1]; exact hY
    · have e : 2 * V * b.comp (X + C x₀) = (2 * V * b.comp (X + C x₀) - C lam * X ^ m) +
          C lam * X ^ m := by ring
      rw [e]; exact dvd_add (hm.trans key) (dvd_mul_left _ _)
  have hA : X ^ m ∣ a.comp (X + C x₀) := by
    have e : a.comp (X + C x₀) = (jet a b x₀ V - C lam * X ^ m) + C lam * X ^ m -
        b.comp (X + C x₀) * V := by
      simp only [jet]; ring
    rw [e]
    exact dvd_sub (dvd_add (hm.trans h₁) (dvd_mul_left _ _)) (Dvd.dvd.mul_right hB _)
  refine ⟨dvd_of_comp hA, dvd_of_comp hB, fun hb ↦ ?_⟩
  have hB0 : b.comp (X + C x₀) = 0 := by simp [hb]
  rw [hB0, mul_zero, zero_sub, dvd_neg, X_pow_dvd_iff] at key
  have := key m (Nat.lt_succ_self m)
  simpa using this

end Jac
