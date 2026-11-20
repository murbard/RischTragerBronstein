import RischTragerBronstein.Torsion.DescendNorm

/-!
# Unramified branch systems from integral data (general curves)

`unram_system`: a fibre of `F` over a ring `R` splitting into simple roots gives, over any
algebraically closed field receiving `R`, a complete unramified branch system through the images of
the roots.
-/

open Polynomial HahnSeries

namespace Curves

open Differential LaurentSeries GTors

section Help

variable {R C L Kb : Type*} [CommRing R] [Field C] [Field L] [Algebra C L] [Field Kb] [Algebra C Kb]

lemma fibreAt_eval_map (F : R[X][X]) (ψ : R →+* C) (a b : R) :
    (fibreAt (F.map (mapRingHom ψ)) (algebraMap C Kb (ψ a))).eval (algebraMap C Kb (ψ b)) =
      algebraMap C Kb (ψ (Sup.evalW F a b)) := by
  rw [fibreAt, ← Sup.evalW, Polynomial.map_map, ← RingHom.comp_apply (algebraMap C Kb) ψ,
    ← RingHom.comp_apply (algebraMap C Kb) ψ, ← RingHom.comp_apply (algebraMap C Kb) ψ,
    ← evalW_mapG, Polynomial.mapRingHom_comp]

lemma prod_cast {M : Type*} [CommMonoid M] {a b : ℕ} (h : a = b) (f : Fin b → M) :
    ∏ k : Fin a, f (Fin.cast h k) = ∏ k, f k :=
  Fintype.prod_equiv (finCongr h) _ _ fun _ ↦ rfl

/-- **The dimension count** for the auxiliary function. -/
lemma count_ineq {J : Type*} [Fintype J] {n g cΓ M : ℕ} (c' dΓ : J → ℕ) (δ : Fin n → ℕ)
    (hn : 0 < n) (hδ0 : δ ⟨0, hn⟩ = 0) (hδ : ∀ j : Fin n, (j : ℕ) ≠ 0 → 1 ≤ δ j)
    (hg : ∑ j, δ j + 1 = g + n) (hle : ∀ j, dΓ j ≤ n * c' j) (hsumΓ : ∑ j, dΓ j = cΓ * n)
    (hM : M + cΓ = ∑ j, c' j + g) :
    ∑ j, (n * c' j - dΓ j) + g * (n - 1) < ∑ i, (M + 1 - δ i) := by
  classical
  have hδle : ∀ i, δ i ≤ g + 1 := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · have : i = ⟨0, hn⟩ := Fin.ext hi
      rw [this, hδ0]; omega
    · have h1 : ∑ k ∈ (Finset.univ.erase i).erase ⟨0, hn⟩, 1 ≤ ∑ k ∈ Finset.univ.erase i, δ k := by
        calc ∑ k ∈ (Finset.univ.erase i).erase ⟨0, hn⟩, 1
            ≤ ∑ k ∈ (Finset.univ.erase i).erase ⟨0, hn⟩, δ k :=
              Finset.sum_le_sum fun k hk ↦ hδ k (by
                intro h0; exact (Finset.ne_of_mem_erase hk) (Fin.ext h0))
          _ ≤ ∑ k ∈ Finset.univ.erase i, δ k :=
              Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
      have hmem : (⟨0, hn⟩ : Fin n) ∈ Finset.univ.erase i :=
        Finset.mem_erase.mpr ⟨fun h ↦ hi (by rw [← h]), Finset.mem_univ _⟩
      rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem hmem,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h1
      have h2 := Finset.add_sum_erase Finset.univ δ (Finset.mem_univ i)
      omega
  have hcΓ : cΓ ≤ ∑ j, c' j := by
    have h1 : cΓ * n ≤ (∑ j, c' j) * n := by
      rw [← hsumΓ, Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ ↦ by rw [mul_comm]; exact hle j
    exact Nat.le_of_mul_le_mul_right h1 hn
  have hMg : g ≤ M := by omega
  have h1 : ∑ i, (M + 1 - δ i) = n * (M + 1) - ∑ i, δ i := by
    rw [Finset.sum_tsub_distrib _ fun i _ ↦ (hδle i).trans (by omega), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h2 : ∑ j, (n * c' j - dΓ j) = n * ∑ j, c' j - cΓ * n := by
    rw [Finset.sum_tsub_distrib _ fun j _ ↦ hle j, ← Finset.mul_sum, hsumΓ]
  rw [h1, h2]
  have h3 : cΓ * n ≤ n * ∑ j, c' j := by rw [mul_comm]; exact Nat.mul_le_mul_left n hcΓ
  have hsum : ∑ i, δ i = g + n - 1 := by omega
  rw [hsum]
  have hM' : M = ∑ j, c' j + g - cΓ := by omega
  subst hM'
  zify [h3, hcΓ, (show 1 ≤ n by omega), (show g + n - 1 ≤ n * (∑ j, c' j + g - cΓ + 1) by
    nlinarith), (show cΓ ≤ ∑ j, c' j + g by omega)]
  push_cast [Nat.cast_sub hcΓ]
  nlinarith

lemma rootMultiplicity_pow' {K : Type*} [Field K] (p : K[X]) (hp : p ≠ 0) (a : K) (k : ℕ) :
    (p ^ k).rootMultiplicity a = k * p.rootMultiplicity a := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ih]; ring

lemma root_simple_of_mult_one {K : Type*} [Field K] {p : K[X]} {a : K}
    (h : p.rootMultiplicity a = 1) : p.IsRoot a ∧ ¬ (derivative p).IsRoot a := by
  have hp : p ≠ 0 := by rintro rfl; simp at h
  refine ⟨(rootMultiplicity_pos hp).mp (by rw [h]; exact one_pos), ?_⟩
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp a
  rw [h, pow_one] at hpq
  intro hd
  apply hq
  rw [dvd_iff_isRoot]
  rw [hpq, Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
    Polynomial.derivative_C, sub_zero, one_mul] at hd
  simpa [IsRoot] using hd

namespace CurveData

variable (S : CurveData C L) [IsAlgClosed Kb]

/-- **Unramified branch systems from a split fibre.** -/
lemma unram_system (F : R[X][X]) (ψ : R →+* C) (hSF : S.F = F.map (mapRingHom ψ)) (x₀ : R)
    (yv : Fin S.F.natDegree → R)
    (hsplit : F.map (evalRingHom x₀) = ∏ k, (X - Polynomial.C (yv k)))
    (hFu : ∀ k, algebraMap C Kb (ψ (Sup.evalW (derivative F) x₀ (yv k))) ≠ 0)
    (hinj : Function.Injective fun k ↦ algebraMap C Kb (ψ (yv k))) :
    ∃ Y : Fin S.F.natDegree → PowerSeries Kb,
      (∀ k, (fibrePS S.F (algebraMap C Kb (ψ x₀))).eval (Y k) = 0) ∧
      (∀ k, PowerSeries.constantCoeff (Y k) = algebraMap C Kb (ψ (yv k))) ∧
      (∀ k, (fibreAt (derivative S.F) (algebraMap C Kb (ψ x₀))).eval
        (algebraMap C Kb (ψ (yv k))) ≠ 0) ∧
      S.F.map (branchSub 1 (algebraMap C Kb (ψ x₀))) =
        ((List.ofFn fun k ↦ ofPowerSeries ℤ Kb (Y k)).map fun r ↦ X - Polynomial.C r).prod := by
  have hroot : ∀ k, Sup.evalW F x₀ (yv k) = 0 := fun k ↦ by
    rw [Sup.evalW, hsplit, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  have hb : ∀ k, (fibreAt S.F (algebraMap C Kb (ψ x₀))).eval (algebraMap C Kb (ψ (yv k))) = 0 :=
    fun k ↦ by rw [hSF, fibreAt_eval_map, hroot, map_zero, map_zero]
  have hb' : ∀ k, (fibreAt (derivative S.F) (algebraMap C Kb (ψ x₀))).eval
      (algebraMap C Kb (ψ (yv k))) ≠ 0 := fun k ↦ by
    rw [hSF, Polynomial.derivative_map, fibreAt_eval_map]; exact hFu k
  obtain ⟨Y, hY, hs⟩ := split_unramified S.F S.monic (algebraMap C Kb (ψ x₀)) _ hinj hb hb'
  refine ⟨Y, fun k ↦ (hY k).1, fun k ↦ (hY k).2, hb', ?_⟩
  rw [hs, List.map_ofFn, List.prod_ofFn]; rfl

end CurveData

end Help

end Curves
