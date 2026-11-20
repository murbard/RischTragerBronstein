import RischTragerBronstein.Torsion.LogWitRows
import RischTragerBronstein.Algebraic.SuperExp
import RischTragerBronstein.Algebraic.SuperInfinity
import RischTragerBronstein.Curves.Poles

/-!
# Expansions of `W(x, y)` along branches as combinations

* `branch_expansion`: along `x = a + Tᴺ`, `y = ρ(T)` (`ρ` over `F`), the expansion of
  `W ∈ C[x][y]` is `combS` of the monomial expansions `(a + Tᴺ)ᵉ ρⁱ` with the coefficients of `W`;
* `inf_expansion`: above infinity (`x = T^{-N}`, `y = T^{-kN} w(T)`), it is `T^{-ND}` times
  `combS` of `T^{N(D - e - k i)} wⁱ`, for `D ≥ E + k (n − 1)`.

These feed the linear descent `descend_comb`.
-/

open Polynomial HahnSeries

namespace Curves

open Differential Differential.SuperData

section Expand

variable {C K F : Type*} [Field C] [Field K] [Algebra C K] [Field F] (ψ : F →+* K)

/-- **The expansion along a finite branch.** -/
theorem branch_expansion (W : C[X][X]) (n E : ℕ) (hdeg : W.natDegree < n)
    (hE : ∀ i, (W.coeff i).natDegree ≤ E) (a : F) (N : ℕ) (ρ : PowerSeries F) :
    (W.map (branchSub N (ψ a))).eval (ofPowerSeries ℤ K (PowerSeries.map ψ ρ)) =
      ofPowerSeries ℤ K (combS (fun i e ↦ PowerSeries.map ψ (sigmaF a N ρ i e)) n E
        (fun i e ↦ algebraMap C K ((W.coeff i).coeff e))) := by
  set WK := W.map (mapRingHom (algebraMap C K)) with hWK
  have hbs : (branchSub N (ψ a) : C[X] →+* LaurentSeries K) =
      (ofPowerSeries ℤ K).comp ((subK (ψ a) N).comp (mapRingHom (algebraMap C K))) := rfl
  have hdegK : WK.natDegree < n := lt_of_le_of_lt natDegree_map_le hdeg
  have hEK : ∀ i, (WK.coeff i).natDegree ≤ E := fun i ↦ by
    rw [hWK, coeff_map, coe_mapRingHom]; exact natDegree_map_le.trans (hE i)
  rw [hbs, ← Polynomial.map_map, ← Polynomial.map_map, eval_map, eval₂_at_apply,
    ← hWK]
  congr 1
  rw [expansion_eq_sum ψ a N ρ WK n E hdegK hEK, combS]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
  rw [hWK, coeff_map, coe_mapRingHom, coeff_map]

/-- The monomial expansions above infinity, `T^{N(D − e − k i)} wⁱ`. -/
noncomputable def sigInf {R : Type*} [CommRing R] (N k D : ℕ) (w : PowerSeries R) (i e : ℕ) :
    PowerSeries R :=
  PowerSeries.X ^ (N * (D - e - k * i)) * w ^ i

lemma infSub_X_pow (N e : ℕ) :
    infSub (C := C) (K := K) N (X ^ e) = single (-((N * e : ℕ) : ℤ)) (1 : K) := by
  rw [map_pow, infSub, coe_eval₂RingHom, eval₂_X, single_pow, one_pow, nsmul_eq_mul]
  congr 1; push_cast; ring

lemma infSub_C' (N : ℕ) (c : C) :
    infSub (C := C) (K := K) N (Polynomial.C c) = HahnSeries.C (algebraMap C K c) := by
  rw [infSub, coe_eval₂RingHom, eval₂_C]; rfl

/-- **The expansion above infinity.** -/
theorem inf_expansion (W : C[X][X]) (n E k D : ℕ) (hdeg : W.natDegree < n)
    (hE : ∀ i, (W.coeff i).natDegree ≤ E) (hD : E + k * (n - 1) ≤ D) (N : ℕ)
    (w : PowerSeries F) :
    (W.map (infSub N)).eval (single (-((k * N : ℕ) : ℤ)) (1 : K) *
        ofPowerSeries ℤ K (PowerSeries.map ψ w)) =
      single (-((N * D : ℕ) : ℤ)) (1 : K) *
        ofPowerSeries ℤ K (combS (fun i e ↦ PowerSeries.map ψ (sigInf N k D w i e)) n E
          (fun i e ↦ algebraMap C K ((W.coeff i).coeff e))) := by
  rw [eval_eq_sum_range' (lt_of_le_of_lt natDegree_map_le hdeg), combS, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  rw [coeff_map]
  conv_lhs => rw [as_sum_range' (W.coeff i) (E + 1) (Nat.lt_succ_of_le (hE i))]
  rw [map_sum, Finset.sum_mul, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  have he' := Finset.mem_range.mp he
  have hle : e + k * i ≤ D := by
    have : k * i ≤ k * (n - 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, infSub_C', infSub_X_pow, mul_pow, single_pow,
    one_pow]
  simp only [sigInf, map_mul, map_pow, PowerSeries.map_X,
    HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X, single_pow, one_pow]
  have hs : single (-((N * D : ℕ) : ℤ)) (1 : K) * single ((N * (D - e - k * i)) • (1 : ℤ)) 1 =
      single (-((N * e : ℕ) : ℤ)) (1 : K) * single (i • -((k * N : ℕ) : ℤ)) 1 := by
    simp only [single_mul_single, mul_one, nsmul_eq_mul]
    congr 1
    push_cast [Nat.sub_sub, Nat.cast_sub hle]
    ring
  calc _ = HahnSeries.C (algebraMap C K ((W.coeff i).coeff e)) *
        (single (-((N * e : ℕ) : ℤ)) (1 : K) * single (i • -((k * N : ℕ) : ℤ)) 1) *
          ofPowerSeries ℤ K (PowerSeries.map ψ w) ^ i := by ring
    _ = _ := by rw [← hs]; ring
/-- `combS` commutes with coefficient maps. -/
lemma map_combS {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (σ : ℕ → ℕ → PowerSeries R)
    (n E : ℕ) (d : ℕ → ℕ → R) :
    PowerSeries.map φ (combS σ n E d) = combS (fun i e ↦ PowerSeries.map φ (σ i e)) n E
      (fun i e ↦ φ (d i e)) := by
  simp [combS, map_sum, PowerSeries.map_C]

/-- The polynomial with coefficients `d i e` (`i < n`, `e ≤ E`). -/
noncomputable def polyOfCoeffs {R : Type*} [CommRing R] (n E : ℕ) (d : ℕ → ℕ → R) : R[X][X] :=
  ∑ i ∈ Finset.range n, Polynomial.C (∑ e ∈ Finset.range (E + 1), Polynomial.C (d i e) * X ^ e) *
    X ^ i

lemma coeff_polyOfCoeffs {R : Type*} [CommRing R] (n E : ℕ) (d : ℕ → ℕ → R) (i e : ℕ) :
    ((polyOfCoeffs n E d).coeff i).coeff e =
      if i < n ∧ e < E + 1 then d i e else 0 := by
  simp only [polyOfCoeffs, finset_sum_coeff, coeff_C_mul_X_pow,
    apply_ite (fun p : R[X] ↦ p.coeff e), Polynomial.coeff_zero]
  by_cases hi : i < n <;> by_cases he : e < E + 1 <;>
    simp [hi, he, Finset.sum_ite_eq, Finset.sum_ite_eq', finset_sum_coeff, coeff_C_mul_X_pow]

end Expand

end Curves
