import RischTragerBronstein.Rational.HermiteStep
import Mathlib.RingTheory.Coprime.Basic

/-!
# Hermite reduction at a normal factor

Let `A` be a differential ring in which the positive integers are units (e.g. `F[t]`, `F` of
characteristic zero), mapping to a differential field `K` (e.g. `F(t)`). If `v ∈ A` is *normal*
with respect to `u`, i.e. `u v′` and `v` are coprime, then the pole of `a / (u v ^ (m + 1))` at `v`
can be lowered to a simple pole modulo derivatives:

  `a / (u v ^ (m + 1)) = g′ + b / (u v)`   with `g ∈ K`, `b ∈ A`.

This is the inner loop of Hermite reduction (Bronstein §2.2, §5.3).
-/

namespace Differential

variable {A K : Type*} [CommRing A] [Differential A] [Field K] [Differential K]
variable [Algebra A K] [DifferentialAlgebra A K]

local notation "φ" => algebraMap A K

/-- One Hermite step over `A`: the Bézout relation for `u v′` and `v` provides the data of
`hermite_step`. -/
theorem hermite_reduce_step (a u v : A) (n : ℕ) (hn : n ≠ 0) (hnu : IsUnit (n : A))
    (hu : φ u ≠ 0) (hv : φ v ≠ 0) (hc : IsCoprime (u * v′) v) :
    ∃ (g : K) (b : A), φ a / (φ u * φ v ^ (n + 1)) = g′ + φ b / (φ u * φ v ^ n) := by
  obtain ⟨s, t, hst⟩ := hc
  obtain ⟨⟨_, ninv, hmul, -⟩, rfl⟩ := hnu
  set B : A := -(ninv * a * s) with hB
  set C : A := -(ninv * a * t) with hC
  refine ⟨φ B / φ v ^ n, -(n : A) * C - u * B′, ?_⟩
  have key : -(n : A) * (B * u * v′ + C * v) = a := by
    rw [hB, hC]
    linear_combination (a * (s * (u * v′) + t * v)) * hmul + a * hst
  have := hermite_step (φ a) (φ B) (φ C) (φ u) (φ v) n hn hu hv (by
    rw [deriv_algebraMap, ← key]
    simp only [map_mul, map_add, map_neg, map_natCast])
  rw [this, deriv_algebraMap (A := A) (B := K) B]
  simp only [map_mul, map_sub, map_neg, map_natCast]

/-- Iterated Hermite steps: reduce a pole of arbitrary order at a normal `v` to a simple pole. -/
theorem hermite_reduce_pow (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : A)) (u v : A)
    (hu : φ u ≠ 0) (hv : φ v ≠ 0) (hc : IsCoprime (u * v′) v) (m : ℕ) (a : A) :
    ∃ (g : K) (b : A), φ a / (φ u * φ v ^ (m + 1)) = g′ + φ b / (φ u * φ v) := by
  induction m generalizing a with
  | zero => exact ⟨0, a, by simp⟩
  | succ m ih =>
    obtain ⟨g₁, b₁, h₁⟩ :=
      hermite_reduce_step (K := K) a u v (m + 1) (Nat.succ_ne_zero m) (hnat _ (Nat.succ_ne_zero m))
        hu hv hc
    obtain ⟨g₂, b₂, h₂⟩ := ih b₁
    exact ⟨g₁ + g₂, b₂, by rw [h₁, h₂, map_add]; ring⟩

end Differential
