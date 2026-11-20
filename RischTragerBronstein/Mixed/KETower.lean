import RischTragerBronstein.Mixed.KELiouville
import RischTragerBronstein.Mixed.KPTower

/-!
# Exponential levels: no algebraic solutions of `α′ = η α`

**`not_exp_of_integral`**: if no non-zero `z ∈ C` satisfies `z′ = d η z` (`d ≥ 1`), then no
non-zero `α` algebraic over `C` satisfies `α′ = η α`. With `p` the minimal polynomial of `α` (degree
`d`), `p^δ + η X p′ − d η p` vanishes at `α` and has degree `< d`, so it is `0`; its constant
coefficient gives `p(0)′ = d η p(0)`, and `p(0) ≠ 0`.

For an exponential level `t′ = a′ t` of a mixed tower this is the hypothesis `MixHyp.hom`
(`e′ + j a′ e ≠ 0` for `j ≠ 0`); so every place over `t ≠ 0` is good (`KWMain`).
-/

open Polynomial

namespace Differential

/-- **No non-zero algebraic solution of `α′ = η α`.** -/
theorem not_exp_of_integral {C A : Type*} [Field C] [Field A] [Differential C] [Differential A]
    [Algebra C A] [DifferentialAlgebra C A] [CharZero C] (η : C)
    (hη : ∀ d : ℕ, 0 < d → ∀ z : C, z ≠ 0 → z′ ≠ (d : C) * η * z)
    (α : A) (hα : IsIntegral C α) (hα0 : α ≠ 0) : α′ ≠ algebraMap C A η * α := by
  intro hd
  set p := minpoly C α with hp
  have hmon : p.Monic := minpoly.monic hα
  have hd0 : 0 < p.natDegree := minpoly.natDegree_pos hα
  set d := p.natDegree with hdd
  set q : C[X] := mapCoeffs p + Polynomial.C η * X * derivative p -
    Polynomial.C ((d : C) * η) * p with hq
  have hqα : aeval α q = 0 := by
    have h := deriv_aeval_eq α p
    rw [minpoly.aeval, map_zero, hd] at h
    rw [hq, map_sub, map_add, map_mul, map_mul, map_mul, aeval_C, aeval_C, aeval_X, minpoly.aeval]
    linear_combination -h
  have hdvd : p ∣ q := minpoly.dvd C α hqα
  have hqdeg : q.natDegree < p.natDegree ∨ q = 0 := by
    by_cases hq0 : q = 0
    · exact Or.inr hq0
    left
    refine lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ ?_) (Nat.sub_lt hd0 one_pos)
    rw [hq, coeff_sub, coeff_add, coeff_mapCoeffs, mul_assoc, coeff_C_mul, coeff_C_mul]
    rcases Nat.lt_or_ge k p.natDegree with hk1 | hk1
    · omega
    · rcases hk1.lt_or_eq with hk2 | hk2
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [coeff_eq_zero_of_natDegree_lt hk2, coeff_X_mul, coeff_derivative,
          coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
      · subst hk2
        obtain ⟨k', hk'⟩ : ∃ k', p.natDegree = k' + 1 := ⟨p.natDegree - 1, by omega⟩
        rw [hmon.coeff_natDegree, Derivation.map_one_eq_zero, hk', coeff_X_mul, coeff_derivative,
          ← hk', hmon.coeff_natDegree, hdd, hk']
        push_cast
        ring
  have hq0 : q = 0 := by
    rcases hqdeg with h | h
    · exact Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd h
    · exact h
  have hc := congrArg (fun r ↦ r.coeff 0) hq0
  simp only [hq, coeff_sub, coeff_add, coeff_mapCoeffs, mul_assoc, coeff_C_mul, coeff_zero,
    mul_coeff_zero, coeff_X_zero, zero_mul, mul_zero, add_zero] at hc
  have hp0 : p.coeff 0 ≠ 0 := by
    intro h0
    have hX : X ∣ p := X_dvd_iff.mpr h0
    have hirr := minpoly.irreducible hα
    obtain ⟨u, hu⟩ := hX
    rcases hirr.isUnit_or_isUnit hu with h1 | h1
    · exact not_isUnit_X h1
    · have hpX : p = X * Polynomial.C (u.coeff 0) := by
        rw [hu, Polynomial.eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit h1)]
        simp
      have := minpoly.aeval C α
      rw [← hp, hpX, map_mul, aeval_X, aeval_C] at this
      rcases mul_eq_zero.mp this with h2 | h2
      · exact hα0 h2
      · have hu0 : u.coeff 0 ≠ 0 := fun h3 ↦ by
          rw [Polynomial.eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit h1), h3, map_zero] at h1
          exact not_isUnit_zero h1
        exact hu0 ((map_eq_zero_iff _ (algebraMap C A).injective).mp h2)
  rw [Polynomial.coeff_C_zero] at hc
  exact hη d hd0 (p.coeff 0) hp0 (by linear_combination hc)

end Differential
