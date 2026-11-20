import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Irreducibility of `Tⁿ − p(x)`

For `p ∈ k[x]` squarefree and non-constant, `Tⁿ − p` is irreducible over `k[x]` (Eisenstein at an
irreducible factor of `p`: `irreducible_X_pow_sub_C_of_squarefree`) and over any fraction field of
`k[x]` (Gauss: `irreducible_X_pow_sub_C_fraction`). So the superelliptic curve `yⁿ = p(x)` has
function field `k(x)[y]/(yⁿ − p)`.
-/

open Polynomial

variable {k : Type*} [Field k]

/-- **Eisenstein**: `Tⁿ − p` is irreducible over `k[x]`. -/
theorem irreducible_X_pow_sub_C_of_squarefree (n : ℕ) (hn : 0 < n) (p : k[X])
    (hsq : Squarefree p) (hp : 0 < p.natDegree) :
    Irreducible ((X : (k[X])[X]) ^ n - C p) := by
  classical
  have hp0 : p ≠ 0 := hsq.ne_zero
  have hpu : ¬ IsUnit p := fun h ↦ by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree hp0] at h
    have : p.natDegree = 0 := by exact_mod_cast h
    omega
  obtain ⟨q, hq, hqp⟩ := WfDvdMonoid.exists_irreducible_factor hpu hp0
  set P : Ideal k[X] := Ideal.span {q}
  have hP : P.IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq.prime
  set f : (k[X])[X] := X ^ n - C p
  have hmon : f.Monic := monic_X_pow_sub_C p hn.ne'
  have hdeg : f.natDegree = n := natDegree_X_pow_sub_C
  have hcoeff : ∀ m, f.coeff m = (if m = n then 1 else 0) - (if m = 0 then p else 0) := by
    intro m
    simp only [f, coeff_sub, coeff_X_pow, coeff_C]
  apply irreducible_of_eisenstein_criterion hP
  · rw [hmon.leadingCoeff]
    intro h1
    rw [Ideal.mem_span_singleton] at h1
    exact hq.not_isUnit (isUnit_of_dvd_one h1)
  · intro m hm
    rw [degree_eq_natDegree hmon.ne_zero, hdeg] at hm
    have hm' : m < n := by exact_mod_cast hm
    rw [hcoeff, if_neg (by omega)]
    split_ifs
    · rw [zero_sub]; exact P.neg_mem_iff.mpr (Ideal.mem_span_singleton.mpr hqp)
    · simp
  · rw [degree_eq_natDegree hmon.ne_zero, hdeg]; exact_mod_cast hn
  · rw [hcoeff, if_neg (by omega), if_pos rfl, zero_sub, Ideal.span_singleton_pow,
      Ideal.neg_mem_iff, Ideal.mem_span_singleton]
    intro h
    exact hq.not_isUnit (hsq q (by rwa [← sq]))
  · exact hmon.isPrimitive

/-- **Gauss**: `Tⁿ − p` is irreducible over a fraction field of `k[x]`. -/
theorem irreducible_X_pow_sub_C_fraction (n : ℕ) (hn : 0 < n) (p : k[X]) (hsq : Squarefree p)
    (hp : 0 < p.natDegree) (F : Type*) [Field F] [Algebra k[X] F] [IsFractionRing k[X] F] :
    Irreducible ((X : F[X]) ^ n - C (algebraMap k[X] F p)) := by
  have hirr := irreducible_X_pow_sub_C_of_squarefree n hn p hsq hp
  have hprim : ((X : (k[X])[X]) ^ n - C p).IsPrimitive := (monic_X_pow_sub_C p hn.ne').isPrimitive
  have := (hprim.irreducible_iff_irreducible_map_fraction_map (K := F)).mp hirr
  simpa [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C] using this
