import RischTragerBronstein.Torsion.PrimeStepUnram

/-!
# Two primes bound the torsion order (unramified divisors)

`torsion_bound_unram`: if two distinct primes `p, q` satisfy the prime step (every principal
multiple `M Γ` forces `(m_p p^v) Γ`, resp. `(m_q q^w) Γ`, to be principal), then any torsion class
has `(m_p m_q) Γ` principal. `not_torsion_unram`: hence, if the linear-algebra test fails for
`(m_p m_q) Γ`, no multiple of `Γ − c ∞ₓ` is principal.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section TP

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K] [IsAlgClosed K]

namespace CurveData

variable (S : CurveData C L)

/-- **Two primes.** -/
theorem torsion_bound_unram (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K) {J : Type*}
    [Fintype J] (α : J → C) (hα : Function.Injective α) (yC : J → Fin S.F.natDegree → C)
    (Y0 : J → Fin S.F.natDegree → PowerSeries C)
    (hY0c : ∀ j k, PowerSeries.constantCoeff (Y0 j k) = yC j k)
    (hsp : ∀ j, S.F.map (branchSub (C := C) (K := C) 1 (α j)) =
      ∏ k, (X - Polynomial.C (ofPowerSeries ℤ C (Y0 j k))))
    (hyinj : ∀ j, Function.Injective (yC j)) (ΓC : J → Fin S.F.natDegree → ℕ) (c : ℕ)
    (hsumΓ : ∑ j, ∑ k, ΓC j k = c * S.F.natDegree)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (mp mq : ℕ) (hmp : 0 < mp) (hmq : 0 < mq)
    (hstep_p : ∀ M : ℕ, 0 < M → (∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGEU (K := K) α yC (fun j k ↦ M * ΓC j k) (M * c) γ) →
      ∃ v : ℕ, ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGEU (K := K) α yC (fun j k ↦ (mp * p ^ v) * ΓC j k) ((mp * p ^ v) * c) γ)
    (hstep_q : ∀ M : ℕ, 0 < M → (∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGEU (K := K) α yC (fun j k ↦ M * ΓC j k) (M * c) γ) →
      ∃ w : ℕ, ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGEU (K := K) α yC (fun j k ↦ (mq * q ^ w) * ΓC j k) ((mq * q ^ w) * c) γ)
    (M : ℕ) (hM : 0 < M) (htor : ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGEU (K := K) α yC (fun j k ↦ M * ΓC j k) (M * c) γ) :
    ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
      S.DivGEU (K := K) α yC (fun j k ↦ (mp * mq) * ΓC j k) ((mp * mq) * c) γ := by
  classical
  set ι := algebraMap C K with hι
  set YK : J → Fin S.F.natDegree → PowerSeries K := fun j k ↦ PowerSeries.map ι (Y0 j k) with hYK
  have hlmap : ∀ j k, lmap ι (ofPowerSeries ℤ C (Y0 j k)) = ofPowerSeries ℤ K (YK j k) :=
    fun j k ↦ lmap_ofPS ι _
  have hspK : ∀ j, S.F.map (branchSub 1 (ι (α j))) =
      ∏ k, (X - Polynomial.C (ofPowerSeries ℤ K (YK j k))) := by
    intro j
    rw [S.split_lmap 1 (α j) _ (hsp j), List.map_ofFn, List.prod_ofFn]
    exact Finset.prod_congr rfl fun k _ ↦ by simp only [Function.comp_apply]; rw [hlmap]
  have hYKc : ∀ j k, PowerSeries.constantCoeff (YK j k) = ι (yC j k) := by
    intro j k
    rw [hYK, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hY0c]
  have hYKinj : ∀ j, Function.Injective fun k ↦ ofPowerSeries ℤ K (YK j k) := by
    intro j a b h
    have := congrArg (fun z : LaurentSeries K ↦ z.coeff 0) h
    simp only [coeff_ofPS, le_refl, if_true, Int.toNat_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hYKc] at this
    exact hyinj j (ι.injective this)
  set ΓK : J → LaurentSeries K → ℕ :=
    fun j ↦ Function.extend (fun k ↦ ofPowerSeries ℤ K (YK j k)) (ΓC j) 0 with hΓK
  -- conversions between the two forms, for all multiples
  have hconv : ∀ t : ℕ, ∀ γ : C⟮S.x⟯⟮S.y⟯,
      S.DivGEU (K := K) α yC (fun j k ↦ t * ΓC j k) (t * c) γ ↔
        S.DivGE α (fun _ ↦ 1) (fun _ ↦ one_pos) (fun j ↦ List.ofFn fun k ↦ ofPowerSeries ℤ K (YK j k))
          (fun j ↦ S.list_split _ _ (hspK j)) (fun j r ↦ t * ΓK j r) (t * c) γ := by
    intro t γ
    rw [S.divGEU_iff α yC YK hspK hYKc hyinj _ _ γ]
    have : (fun j ↦ Function.extend (fun k ↦ ofPowerSeries ℤ K (YK j k)) (fun k ↦ t * ΓC j k) 0) =
        fun j r ↦ t * ΓK j r := funext fun j ↦ extend_mul_left _ _ _
    rw [this]
  have hdΓ : ∀ j, ((List.ofFn fun k ↦ ofPowerSeries ℤ K (YK j k)).map (ΓK j)).sum =
      1 * ∑ k, ΓC j k := by
    intro j
    rw [List.map_ofFn, List.sum_ofFn, one_mul]
    exact Finset.sum_congr rfl fun k _ ↦ (hYKinj j).extend_apply _ _ k
  obtain ⟨γ, hγ0, hγ⟩ := S.principal_two_primes hBr hBI α hα (fun _ ↦ 1) (fun _ ↦ one_pos) _
    (fun j ↦ S.list_split _ _ (hspK j)) ΓK c (fun j ↦ ∑ k, ΓC j k) hdΓ hsumΓ p q hp hq hpq mp mq
    hmp hmq
    (fun M' hM' h ↦ by
      obtain ⟨γ, hγ0, hγ⟩ := h
      obtain ⟨v, γ', hγ'0, hγ'⟩ := hstep_p M' hM' ⟨γ, hγ0, (hconv M' γ).mpr hγ⟩
      exact ⟨v, γ', hγ'0, (hconv _ γ').mp hγ'⟩)
    (fun M' hM' h ↦ by
      obtain ⟨γ, hγ0, hγ⟩ := h
      obtain ⟨w, γ', hγ'0, hγ'⟩ := hstep_q M' hM' ⟨γ, hγ0, (hconv M' γ).mpr hγ⟩
      exact ⟨w, γ', hγ'0, (hconv _ γ').mp hγ'⟩)
    M hM (by obtain ⟨γ, hγ0, hγ⟩ := htor; exact ⟨γ, hγ0, (hconv M γ).mp hγ⟩)
  exact ⟨γ, hγ0, (hconv _ γ).mpr hγ⟩

/-- **Non-torsion from two primes and a failed test.** -/
theorem not_torsion_unram (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K)
    {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} {δ : Fin S.F.natDegree → ℕ}
    (hB : S.IsIntBasis K B D δ) {J : Type*}
    [Fintype J] (α : J → C) (hα : Function.Injective α) (yC : J → Fin S.F.natDegree → C)
    (Y0 : J → Fin S.F.natDegree → PowerSeries C)
    (hY0c : ∀ j k, PowerSeries.constantCoeff (Y0 j k) = yC j k)
    (hsp : ∀ j, S.F.map (branchSub (C := C) (K := C) 1 (α j)) =
      ∏ k, (X - Polynomial.C (ofPowerSeries ℤ C (Y0 j k))))
    (hyinj : ∀ j, Function.Injective (yC j)) (ΓC : J → Fin S.F.natDegree → ℕ) (c : ℕ)
    (hsumΓ : ∑ j, ∑ k, ΓC j k = c * S.F.natDegree)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (mp mq : ℕ) (hmp : 0 < mp) (hmq : 0 < mq)
    (hstep_p : ∀ M : ℕ, 0 < M → (∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGEU (K := K) α yC (fun j k ↦ M * ΓC j k) (M * c) γ) →
      ∃ v : ℕ, ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGEU (K := K) α yC (fun j k ↦ (mp * p ^ v) * ΓC j k) ((mp * p ^ v) * c) γ)
    (hstep_q : ∀ M : ℕ, 0 < M → (∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGEU (K := K) α yC (fun j k ↦ M * ΓC j k) (M * c) γ) →
      ∃ w : ℕ, ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGEU (K := K) α yC (fun j k ↦ (mq * q ^ w) * ΓC j k) ((mq * q ^ w) * c) γ)
    (htest : ¬ princTest δ ((mp * mq) * c) (fun _ : J × Fin S.F.natDegree ↦ 1) (fun q ↦ α q.1)
        (fun q i ↦ basisSer B D 1 (α q.1) (ofPowerSeries ℤ C (Y0 q.1 q.2)) i)
        (fun q ↦ (mp * mq) * ΓC q.1 q.2)) :
    ∀ M : ℕ, 0 < M → ¬ ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
      S.DivGEU (K := K) α yC (fun j k ↦ M * ΓC j k) (M * c) γ := by
  intro M hM htor
  apply htest
  exact (S.principal_iff_test_unram hB α yC Y0 hY0c hsp hyinj _ _).mp
    (S.torsion_bound_unram hBr hBI α hα yC Y0 hY0c hsp hyinj ΓC c hsumΓ p q hp hq hpq mp mq hmp
      hmq hstep_p hstep_q M hM htor)

end CurveData

end TP

end Curves
