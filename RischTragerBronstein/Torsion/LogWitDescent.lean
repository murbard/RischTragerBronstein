import RischTragerBronstein.Torsion.LogWitExpand
import RischTragerBronstein.Curves.Integral

/-!
# Descending functions with prescribed orders to the coefficient field

**`descend_W`**: a non-zero `W₁ ∈ C[x][y]` (`deg_y < n`, `deg_x ≤ E`) whose expansions along a
finite list of branches defined over `F` (finite ones `x = a + Tᴺ, y = ρ`, and ones above infinity
`x = T^{-N}, y = T^{-kN} w`) have order at least the given bounds yields a non-zero
`W ∈ F[x][y]` with the same degree bounds and the same lower bounds (linear descent,
`descend_comb`).
-/

open Polynomial HahnSeries

namespace Curves

open Differential Differential.SuperData

section Descent

variable {C K F : Type*} [Field C] [Field K] [Algebra C K] [Field F]

lemma lowerBd_ofPS_coeff (V : PowerSeries K) (t : ℕ) :
    LowerBd (ofPowerSeries ℤ K V) t ↔ ∀ s < t, PowerSeries.coeff s V = 0 :=
  (lowerBd_ofPS_iff V t).trans PowerSeries.X_pow_dvd_iff

lemma lowerBd_single_mul (V : PowerSeries K) (M : ℕ) (t : ℤ) :
    LowerBd (single (-(M : ℤ)) (1 : K) * ofPowerSeries ℤ K V) t ↔
      ∀ s : ℕ, (s : ℤ) < t + M → PowerSeries.coeff s V = 0 := by
  constructor
  · intro h s hs
    have := h ((s : ℤ) + -(M : ℤ)) (by omega)
    rw [coeff_single_mul_add, one_mul, ofPowerSeries_apply_coeff] at this
    exact this
  · intro h j hj
    have e : j = (j + M) + -(M : ℤ) := by ring
    rw [e, coeff_single_mul_add, one_mul]
    rcases Int.eq_nat_or_neg (j + M) with ⟨s, hs | hs⟩
    · rw [hs, ofPowerSeries_apply_coeff]; exact h s (by omega)
    · by_cases h0 : ofPowerSeries ℤ K V = 0
      · rw [h0]; rfl
      · by_cases hs0 : s = 0
        · subst hs0
          rw [hs, Nat.cast_zero, neg_zero, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl,
            ofPowerSeries_apply_coeff]
          exact h 0 (by omega)
        · rw [hs]
          exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le (by omega) (order_ofPS_nonneg V))

variable (ψ₀ : F →+* C)

/-- **Descent of a function with prescribed lower bounds along branches over `F`.** -/
theorem descend_W (n E k D : ℕ) (hD : E + k * (n - 1) ≤ D)
    (fb : List (F × ℕ × PowerSeries F × ℕ)) (ib : List (ℕ × PowerSeries F × ℤ))
    (W₁ : C[X][X]) (hdeg : W₁.natDegree < n) (hE : ∀ i, (W₁.coeff i).natDegree ≤ E)
    (hW₁ : W₁ ≠ 0)
    (hfin : ∀ β ∈ fb, LowerBd ((W₁.map (branchSub β.2.1 ((algebraMap C K).comp ψ₀ β.1))).eval
      (ofPowerSeries ℤ K (PowerSeries.map ((algebraMap C K).comp ψ₀) β.2.2.1))) β.2.2.2)
    (hinf : ∀ γ ∈ ib, LowerBd ((W₁.map (infSub γ.1)).eval (single (-((k * γ.1 : ℕ) : ℤ)) (1 : K) *
      ofPowerSeries ℤ K (PowerSeries.map ((algebraMap C K).comp ψ₀) γ.2.1))) γ.2.2) :
    ∃ W : F[X][X], W ≠ 0 ∧ W.natDegree < n ∧ (∀ i, (W.coeff i).natDegree ≤ E) ∧
      (∀ β ∈ fb, LowerBd (((W.map (mapRingHom ψ₀)).map (branchSub β.2.1 ((algebraMap C K).comp ψ₀ β.1))).eval
        (ofPowerSeries ℤ K (PowerSeries.map ((algebraMap C K).comp ψ₀) β.2.2.1))) β.2.2.2) ∧
      (∀ γ ∈ ib, LowerBd (((W.map (mapRingHom ψ₀)).map (infSub γ.1)).eval
        (single (-((k * γ.1 : ℕ) : ℤ)) (1 : K) *
          ofPowerSeries ℤ K (PowerSeries.map ((algebraMap C K).comp ψ₀) γ.2.1))) γ.2.2) := by
  classical
  set ψ := (algebraMap C K).comp ψ₀ with hψ
  set c : ℕ → ℕ → K := fun i e ↦ algebraMap C K ((W₁.coeff i).coeff e) with hc
  set branches : List ((ℕ → ℕ → PowerSeries F) × ℕ) :=
    fb.map (fun β ↦ (sigmaF β.1 β.2.1 β.2.2.1, β.2.2.2)) ++
      ib.map (fun γ ↦ (sigInf γ.1 k D γ.2.1, (γ.2.2 + ((γ.1 * D : ℕ) : ℤ)).toNat)) with hbr
  -- a non-zero coefficient of `W₁`
  have hc0 : ∃ i < n, ∃ e < E + 1, c i e ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, W₁.coeff i ≠ 0 := by
      by_contra h; push Not at h; exact hW₁ (Polynomial.ext h)
    obtain ⟨e, he⟩ : ∃ e, (W₁.coeff i).coeff e ≠ 0 := by
      by_contra h; push Not at h; exact hi (Polynomial.ext h)
    refine ⟨i, lt_of_le_of_lt (le_natDegree_of_ne_zero hi) hdeg, e,
      Nat.lt_succ_of_le ((le_natDegree_of_ne_zero he).trans (hE i)), ?_⟩
    rw [hc]; exact (map_ne_zero_iff _ (algebraMap C K).injective).mpr he
  have hbr_mem : ∀ β ∈ branches, (∃ b ∈ fb, β = (sigmaF b.1 b.2.1 b.2.2.1, b.2.2.2)) ∨
      (∃ g ∈ ib, β = (sigInf g.1 k D g.2.1, (g.2.2 + ((g.1 * D : ℕ) : ℤ)).toNat)) := fun β hβ ↦ by
    rcases List.mem_append.mp hβ with h | h
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h; exact Or.inl ⟨b, hb, rfl⟩
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp h; exact Or.inr ⟨g, hg, rfl⟩
  obtain ⟨d, hd0, hd⟩ := descend_comb ψ branches n E c hc0 (fun β hβ s hs ↦ by
    rcases hbr_mem β hβ with ⟨b, hb, rfl⟩ | ⟨g, hg, rfl⟩
    · have h1 := hfin b hb
      rw [branch_expansion ψ W₁ n E hdeg hE b.1 b.2.1 b.2.2.1, lowerBd_ofPS_coeff] at h1
      exact h1 s hs
    · have h1 := hinf g hg
      rw [inf_expansion ψ W₁ n E k D hdeg hE hD g.1 g.2.1, lowerBd_single_mul] at h1
      exact h1 s (by simp only at hs; omega))
  set W := polyOfCoeffs n E d with hW
  have hcoef : ∀ i e, (W.coeff i).coeff e = if i < n ∧ e < E + 1 then d i e else 0 :=
    coeff_polyOfCoeffs n E d
  obtain ⟨i0, hi0, e0, he0, hd00⟩ := hd0
  have hWdeg : W.natDegree < n := by
    have : W.natDegree ≤ n - 1 := natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ by
      have hi' : n - 1 < i := by exact_mod_cast hi
      refine Polynomial.ext fun e ↦ ?_
      rw [hcoef, if_neg (by omega), Polynomial.coeff_zero]
    omega
  have hWE : ∀ i, (W.coeff i).natDegree ≤ E := fun i ↦
    natDegree_le_iff_coeff_eq_zero.mpr fun e he ↦ by
      have he' : E < e := by exact_mod_cast he
      rw [hcoef, if_neg (by omega)]
  have hW0 : W ≠ 0 := fun h ↦ hd00 (by
    have := hcoef i0 e0
    rw [h, Polynomial.coeff_zero, Polynomial.coeff_zero, if_pos ⟨hi0, he0⟩] at this
    exact this.symm)
  have hWm : (W.map (mapRingHom ψ₀)).natDegree < n := lt_of_le_of_lt natDegree_map_le hWdeg
  have hWmE : ∀ i, ((W.map (mapRingHom ψ₀)).coeff i).natDegree ≤ E := fun i ↦ by
    rw [coeff_map, coe_mapRingHom]; exact natDegree_map_le.trans (hWE i)
  -- the combination of `W` is that of `d`
  have hcomb : ∀ σ : ℕ → ℕ → PowerSeries F,
      combS (fun i e ↦ PowerSeries.map ψ (σ i e)) n E
        (fun i e ↦ algebraMap C K (((W.map (mapRingHom ψ₀)).coeff i).coeff e)) =
      PowerSeries.map ψ (combS σ n E d) := fun σ ↦ by
    rw [map_combS]
    refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun e he ↦ ?_
    simp only
    rw [coeff_map, coe_mapRingHom, coeff_map, hcoef, if_pos ⟨Finset.mem_range.mp hi,
      Finset.mem_range.mp he⟩, hψ, RingHom.comp_apply]
  refine ⟨W, hW0, hWdeg, hWE, fun β hβ ↦ ?_, fun γ hγ ↦ ?_⟩
  · rw [branch_expansion ψ _ n E hWm hWmE β.1 β.2.1 β.2.2.1, hcomb, lowerBd_ofPS_coeff]
    intro s hs
    rw [PowerSeries.coeff_map, hd _ (List.mem_append_left _ (List.mem_map.mpr ⟨β, hβ, rfl⟩)) s hs,
      map_zero]
  · rw [inf_expansion ψ _ n E k D hWm hWmE hD γ.1 γ.2.1, hcomb, lowerBd_single_mul]
    intro s hs
    rw [PowerSeries.coeff_map, hd _ (List.mem_append_right _ (List.mem_map.mpr ⟨γ, hγ, rfl⟩)) s
      (by simp only; omega), map_zero]

end Descent

end Curves
