import RischTragerBronstein.Torsion.RedLib4

/-!
# Irreducibility certificates exist (1): subset products are not polynomials

For the equation `F ∈ k[x][Y]` of a curve (`S.F = F.map ψ`), monic of degree `n` with `x`-degrees at
most `d`, split at `x = a` into distinct power series roots `yⱼ`: for every subset `J` with
`0 < |J| < n`, the product `∏_{j ∈ J} (Y − yⱼ)` has a coefficient with a non-zero `Tᵗ` term,
`t > d` (**`exists_coeff_subset`**). Otherwise the product would come from a monic factor of `F` in
`k[x][Y]` of `Y`-degree `|J|` (truncation, division by a monic polynomial), contradicting the
irreducibility of the curve (`S.irr`).
-/

open Polynomial HahnSeries

namespace Curves

open Differential LaurentSeries

section Subsets

variable {k : Type*} [Field k]

lemma trunc_eq_of_coeff (c : PowerSeries k) (d : ℕ) (h : ∀ t, d < t → PowerSeries.coeff t c = 0) :
    ((PowerSeries.trunc (d + 1) c : k[X]) : PowerSeries k) = c := by
  ext t
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with ht
  · rfl
  · exact (h t (by omega)).symm

lemma branchSub_comp_sub (a : k) (p : k[X]) :
    branchSub (C := k) (K := k) 1 a (p.comp (X - Polynomial.C a)) = ofPowerSeries ℤ k (p : PowerSeries k) := by
  rw [branchSub_apply]
  congr 2
  simp only [Algebra.algebraMap_self, Polynomial.map_id, pow_one, Polynomial.comp_assoc,
    Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, add_sub_cancel_left, Polynomial.comp_X]

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

/-- **Subset products of the roots are not polynomials of degree `≤ d`.** -/
theorem exists_coeff_subset (S : CurveData C L) (ψ : k →+* C) (Fk : k[X][X])
    (hSF : S.F = Fk.map (mapRingHom ψ)) (hmon : Fk.Monic) (a : k) (d : ℕ)
    (hd : ∀ i, (Fk.coeff i).natDegree ≤ d) (y : Fin Fk.natDegree → PowerSeries k)
    (hsplit : Fk.map (branchSub (C := k) (K := k) 1 a) =
      ∏ j, (X - Polynomial.C (HahnSeries.ofPowerSeries ℤ k (y j))))
    (J : Finset (Fin Fk.natDegree)) (hJ0 : 0 < J.card) (hJn : J.card < Fk.natDegree) :
    ∃ i t, d < t ∧ PowerSeries.coeff t ((∏ j ∈ J, (X - Polynomial.C (y j))).coeff i) ≠ 0 := by
  classical
  by_contra hne
  push Not at hne
  set PT : (PowerSeries k)[X] := ∏ j ∈ J, (X - Polynomial.C (y j)) with hPT
  have hPTm : PT.Monic := monic_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C _
  have hPTd : PT.natDegree = J.card := by
    rw [hPT, natDegree_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C _]
    simp
  -- the factor over `k[x]`
  set g : ℕ → k[X] := fun i ↦ (PowerSeries.trunc (d + 1) (PT.coeff i)).comp (X - Polynomial.C a)
  set G : k[X][X] := ∑ i ∈ Finset.range (PT.natDegree + 1), Polynomial.C (g i) * X ^ i with hG
  have hbs : Function.Injective (branchSub (C := k) (K := k) 1 a) := branchSub_injective 1 one_pos a
  have hGmap : G.map (branchSub (C := k) (K := k) 1 a) = PT.map (HahnSeries.ofPowerSeries ℤ k) := by
    rw [hG, Polynomial.map_sum]
    conv_rhs => rw [PT.as_sum_range_C_mul_X_pow, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, branchSub_comp_sub,
      trunc_eq_of_coeff (PT.coeff i) d (fun t ht ↦ hne i t ht)]
  have hGm : G.Monic := by
    refine Polynomial.monic_of_injective hbs ?_
    rw [hGmap]; exact hPTm.map _
  have hGd : G.natDegree = J.card := by
    rw [← natDegree_map_eq_of_injective hbs G, hGmap, hPTm.natDegree_map, hPTd]
  -- `G` divides `F`
  have hdiv : G ∣ Fk := by
    rw [← modByMonic_eq_zero_iff_dvd hGm]
    apply Polynomial.map_injective _ hbs
    rw [Polynomial.map_zero, map_modByMonic _ hGm, hGmap, hsplit, modByMonic_eq_zero_iff_dvd (hPTm.map _)]
    rw [← Finset.prod_mul_prod_compl J, hPT, Polynomial.map_prod]
    refine dvd_mul_of_dvd_left (dvd_of_eq ?_) _
    exact Finset.prod_congr rfl fun j _ ↦ by simp
  obtain ⟨Q, hQ⟩ := hdiv
  -- contradiction with the irreducibility of the curve
  have hQm : Q.Monic := by
    have := hmon
    rw [hQ] at this
    exact hGm.of_mul_monic_left this
  have hQd : Q.natDegree = Fk.natDegree - J.card := by
    have := congrArg natDegree hQ
    rw [hGm.natDegree_mul hQm, hGd] at this
    omega
  have hn : S.F.natDegree = Fk.natDegree := by rw [hSF, hmon.natDegree_map]
  have hG' := hGm.map (mapRingHom ψ)
  have hQ' := hQm.map (mapRingHom ψ)
  have h0 : S.evXY (G.map (mapRingHom ψ)) * S.evXY (Q.map (mapRingHom ψ)) = 0 := by
    rw [← S.evXY_mul, ← Polynomial.map_mul, ← hQ, ← hSF, S.evXY_F]
  rcases mul_eq_zero.mp h0 with h | h
  · have := S.irr _ (by rw [hGm.natDegree_map, hGd, hn]; exact hJn) h
    exact hG'.ne_zero this
  · have := S.irr _ (by rw [hQm.natDegree_map, hQd, hn]; omega) h
    exact hQ'.ne_zero this

end Subsets

end Curves
