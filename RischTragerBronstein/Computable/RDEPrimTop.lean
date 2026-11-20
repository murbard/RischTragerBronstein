import RischTragerBronstein.Computable.RDEPrim

/-!
# The top coefficient of `D Y′ + (g D - D′) Y` in a primitive extension

With `t₁′ = η`, `g ∈ F` not the negative of a logarithmic derivative, `D ≠ 0` and `Y ≠ 0`:
`E = D Y′ + (g D - D′) Y` has degree exactly `deg D + deg Y`, with leading coefficient
`L² (z′ + g z)` where `L = lc D`, `z = lc Y / L`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

variable {F : Type*} [Field F] [Differential F] [Differential F[X]]

lemma natDegree_implicitDeriv_C_le (η : F) (Y : F[X]) :
    (implicitDeriv (C η) Y).natDegree ≤ Y.natDegree := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ ?_
  rw [coeff_implicitDeriv_C, coeff_eq_zero_of_natDegree_lt hk,
    coeff_eq_zero_of_natDegree_lt (by omega), map_zero, zero_mul, mul_zero, add_zero]

theorem rde_poly_top (η g : F) (hD₂ : ∀ P : F[X], P′ = implicitDeriv (C η) P)
    (hgnl : ∀ e : F, e ≠ 0 → e′ + g * e ≠ 0) (D Y : F[X]) (hD0 : D ≠ 0) (hY : Y ≠ 0) :
    (D * Y′ + (C g * D - D′) * Y).natDegree = D.natDegree + Y.natDegree ∧
      (D * Y′ + (C g * D - D′) * Y).coeff (D.natDegree + Y.natDegree) =
        D.leadingCoeff ^ 2 * ((Y.leadingCoeff / D.leadingCoeff)′ +
          g * (Y.leadingCoeff / D.leadingCoeff)) ∧
      D * Y′ + (C g * D - D′) * Y ≠ 0 := by
  set L := D.leadingCoeff with hL
  set y := Y.leadingCoeff with hy
  have hL0 : L ≠ 0 := leadingCoeff_ne_zero.mpr hD0
  have hy0 : y ≠ 0 := leadingCoeff_ne_zero.mpr hY
  have hz0 : y / L ≠ 0 := div_ne_zero hy0 hL0
  have hY' : Y′.natDegree ≤ Y.natDegree := by rw [hD₂]; exact natDegree_implicitDeriv_C_le η Y
  have hD' : D′.natDegree ≤ D.natDegree := by rw [hD₂]; exact natDegree_implicitDeriv_C_le η D
  have hP₀ : (C g * D - D′).natDegree ≤ D.natDegree :=
    (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _)) hD')
  have hle : (D * Y′ + (C g * D - D′) * Y).natDegree ≤ D.natDegree + Y.natDegree := by
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_mul_le.trans (by omega)
    · exact natDegree_mul_le.trans (by omega)
  have hc1 : (D * Y′).coeff (D.natDegree + Y.natDegree) = L * y′ := by
    rw [coeff_mul_add_eq_of_natDegree_le le_rfl hY', hD₂, coeff_implicitDeriv_C,
      coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), zero_mul, mul_zero, add_zero]
    rfl
  have hc2 : ((C g * D - D′) * Y).coeff (D.natDegree + Y.natDegree) = (g * L - L′) * y := by
    rw [coeff_mul_add_eq_of_natDegree_le hP₀ le_rfl, coeff_sub, coeff_C_mul, hD₂,
      coeff_implicitDeriv_C, coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), zero_mul,
      mul_zero, add_zero]
    rfl
  have hcoeff : (D * Y′ + (C g * D - D′) * Y).coeff (D.natDegree + Y.natDegree) =
      L ^ 2 * ((y / L)′ + g * (y / L)) := by
    rw [coeff_add, hc1, hc2, Derivation.leibniz_div]
    simp only [smul_eq_mul]
    field_simp
    ring
  have hne : L ^ 2 * ((y / L)′ + g * (y / L)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hL0) (hgnl _ hz0)
  have hdeg : (D * Y′ + (C g * D - D′) * Y).natDegree = D.natDegree + Y.natDegree :=
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hcoeff]; exact hne))
  exact ⟨hdeg, hcoeff, fun h0 ↦ hne (by rw [← hcoeff, h0, coeff_zero])⟩

end Tower
