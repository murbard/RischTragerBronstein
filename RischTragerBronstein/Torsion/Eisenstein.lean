import RischTragerBronstein.Torsion.StdCurve
import RischTragerBronstein.Algebraic.SuperIrred

/-!
# Eisenstein at a point

`irreducible_eisenstein_at`: if `F ∈ k[x][Y]` is monic of positive degree, all its lower
coefficients vanish at `x = a` and `∂ₓF₀(a) ≠ 0` (so `(x − a)² ∤ F₀`), then `F` is irreducible over
`k(x)` (any characteristic). This gives the curves `stdCurve` over `ℚ_p` and `𝔽_p`.
-/

open Polynomial

namespace Curves

variable {k : Type*} [Field k]

lemma not_sq_dvd_of_derivative (f : k[X]) (a : k) (h : (derivative f).eval a ≠ 0) :
    ¬ (X - C a) ^ 2 ∣ f := by
  rintro ⟨g, rfl⟩
  apply h
  simp [derivative_mul, derivative_pow]

/-- **Eisenstein at `x = a`.** -/
theorem irreducible_eisenstein_at (F : k[X][X]) (hF : F.Monic) (hd : 0 < F.natDegree) (a : k)
    (hc : ∀ i < F.natDegree, (F.coeff i).eval a = 0)
    (h0 : (derivative (F.coeff 0)).eval a ≠ 0) :
    Irreducible (F.map (algebraMap k[X] (RatFunc k))) := by
  classical
  have hq : Irreducible (X - C a : k[X]) := irreducible_of_degree_eq_one (degree_X_sub_C a)
  set P : Ideal k[X] := Ideal.span {X - C a}
  have hP : P.IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq.prime
  have hirr : Irreducible F := by
    apply irreducible_of_eisenstein_criterion hP
    · rw [hF.leadingCoeff]
      intro h1
      rw [Ideal.mem_span_singleton] at h1
      exact hq.not_isUnit (isUnit_of_dvd_one h1)
    · intro m hm
      rw [degree_eq_natDegree hF.ne_zero] at hm
      have hm' : m < F.natDegree := by exact_mod_cast hm
      rw [Ideal.mem_span_singleton, dvd_iff_isRoot]
      exact hc m hm'
    · rw [degree_eq_natDegree hF.ne_zero]; exact_mod_cast hd
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact not_sq_dvd_of_derivative _ a h0
    · exact hF.isPrimitive
  exact (hF.isPrimitive.irreducible_iff_irreducible_map_fraction_map (K := RatFunc k)).mp hirr

end Curves
