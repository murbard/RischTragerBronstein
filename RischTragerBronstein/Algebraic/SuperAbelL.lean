import RischTragerBronstein.Algebraic.SuperAbelCore

/-!
# Abel's direction on a superelliptic curve, from a Liouville form

`super_abel`: if `f = v′ + ∑ cᵢ uᵢ′/uᵢ` on the superelliptic function field `C⟮x⟯⟮y⟯` (constants
`C`, `x′ = 1`), `f` has residue `r(Q)` at the non-branch points `Q ∈ Pts` and no residue at the
other non-branch points, and `Λ : K → ℚ` is `ℚ`-linear with `Λ(r(Q)) = z(Q)/D`, then a positive
multiple of the divisor `∑ z(Q) Q` becomes principal after the standard normalisation
(`abel_core`) on the base change to `K`.
-/

open Polynomial IntermediateField HahnSeries

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]

variable (S : SuperData C L)

lemma exists_int_of_den_dvd (q : ℚ) (d : ℕ) (h : q.den ∣ d) : ∃ k : ℤ, q * d = k := by
  obtain ⟨m, rfl⟩ := h
  refine ⟨q.num * m, ?_⟩
  push_cast
  rw [← mul_assoc, Rat.mul_den_eq_num]

open Classical in
/-- **Abel's direction** (superelliptic, from a Liouville form). -/
theorem super_abel (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) {ι : Type*} (s : Finset ι)
    (c : ι → C) (u : ι → L) (hu : ∀ i, u i ∈ C⟮S.x⟯⟮S.y⟯) (hu0 : ∀ i, u i ≠ 0) (v f : L)
    (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, algebraMap C L (c i) * ((u i)′ / u i))
    (Pts : Finset (K × K)) (hPts : ∀ Q ∈ Pts, Q.2 ≠ 0 ∧
      Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1) (r : K × K → K)
    (hres : ∀ (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α),
      LaurentSeries.res (S.embXY α β hβ hβp ⟨f, hf⟩) = if (α, β) ∈ Pts then r (α, β) else 0)
    (Λ : K →ₗ[ℚ] ℚ) (z : K × K → ℤ) (D : ℕ) (hD : D ≠ 0)
    (hΛ : ∀ Q ∈ Pts, Λ (r Q) = z Q / D) :
    ∃ M : ℕ, 1 ≤ M ∧ (S.base K).IsPrincipalS K (fun Q ↦ if Q.2 = 0 then 0 else
      ((if Q ∈ Pts then (M : ℤ) * z Q else 0) +
        ∑ Q' ∈ Pts.filter (fun Q ↦ z Q < 0) with Q'.1 = Q.1,
          |if Q' ∈ Pts then (M : ℤ) * z Q' else 0|).toNat) S.n := by
  -- clear denominators of `Λ(cᵢ)`
  set lam : ι → ℚ := fun i ↦ Λ (algebraMap C K (c i))
  set M : ℕ := ∏ i ∈ s, (lam i).den
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ (lam i).den_nz
  have hG : ∀ i ∈ s, ∃ k : ℤ, lam i * M = k := fun i hi ↦
    exists_int_of_den_dvd _ _ (Finset.dvd_prod_of_mem _ hi)
  choose! G hGdef using hG
  -- the product of the logarithms
  set U : ι → C⟮S.x⟯⟮S.y⟯ := fun i ↦ ⟨u i, hu i⟩
  have hU0 : ∀ i, U i ≠ 0 := fun i h ↦ hu0 i (congrArg Subtype.val h)
  set w₀ : C⟮S.x⟯⟮S.y⟯ := ∏ i ∈ s, U i ^ ((D : ℤ) * G i)
  have hw₀ : w₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ (hU0 i)
  -- its orders at the non-branch points
  have hord : ∀ (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α),
      S.ordAt K w₀ α β = if (α, β) ∈ Pts then (M : ℤ) * z (α, β) else 0 := by
    intro α β hβ hβp
    have hr := S.res_liouville hC hx α β hβ hβp s c u hu hu0 v f hv hf heq
    rw [hres α β hβ hβp] at hr
    have hΛr := congrArg Λ hr
    rw [map_sum] at hΛr
    have hterm : ∀ i ∈ s, Λ (algebraMap C K (c i) *
        ((S.embXY α β hβ hβp ⟨u i, hu i⟩).order : K)) =
        ((S.embXY α β hβ hβp ⟨u i, hu i⟩).order : ℚ) * lam i := fun i _ ↦ by
      rw [show algebraMap C K (c i) * ((S.embXY α β hβ hβp ⟨u i, hu i⟩).order : K) =
        ((S.embXY α β hβ hβp ⟨u i, hu i⟩).order : ℚ) • algebraMap C K (c i) by
          rw [Rat.smul_def]; push_cast; ring, map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl hterm] at hΛr
    have hsum : S.ordAt K w₀ α β = ∑ i ∈ s, (D : ℤ) * G i *
        (S.embXY α β hβ hβp ⟨u i, hu i⟩).order := by
      rw [S.ordAt_prod hβp _ _ (fun i _ ↦ zpow_ne_zero _ (hU0 i))]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [S.ordAt_zpow hβp, S.ordAt_nb _ α β hβ hβp]
    rw [hsum]
    have hq : (∑ i ∈ s, (D : ℤ) * G i * (S.embXY α β hβ hβp ⟨u i, hu i⟩).order : ℚ) =
        (D : ℚ) * M * ∑ i ∈ s, ((S.embXY α β hβ hβp ⟨u i, hu i⟩).order : ℚ) * lam i := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [← hGdef i hi]; ring
    rw [← hΛr] at hq
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    split_ifs at hq ⊢ with hmem
    · rw [hΛ _ hmem] at hq
      have : ((∑ i ∈ s, (D : ℤ) * G i * (S.embXY α β hβ hβp ⟨u i, hu i⟩).order : ℤ) : ℚ) =
          ((M * z (α, β) : ℤ) : ℚ) := by
        push_cast at hq ⊢; rw [hq]; field_simp
      exact_mod_cast this
    · rw [map_zero, mul_zero] at hq
      exact_mod_cast hq
  -- move to the base change and apply the core
  set zf : K × K → ℤ := fun Q ↦ if Q ∈ Pts then (M : ℤ) * z Q else 0
  have hcore := (S.base K).abel_core (K := K) (S.tau K w₀) (S.tau_ne_zero K hw₀) zf
    (fun Q hβ hv ↦ by
      have hv' : Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1 := by rw [← base_eval]; exact hv
      rw [S.ordAt_tau K w₀ Q.1 Q.2 hv', hord Q.1 Q.2 hβ hv'])
    (Pts.filter fun Q ↦ z Q < 0)
    (fun Q hQ ↦ by
      obtain ⟨h1, h2⟩ := hPts Q (Finset.mem_filter.mp hQ).1
      exact ⟨h1, by rw [base_eval]; exact h2⟩)
    (fun Q _ _ hzQ ↦ by
      simp only [zf] at hzQ
      split_ifs at hzQ with hmem
      · refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
        by_contra hnn
        have : (0 : ℤ) ≤ M * z Q := mul_nonneg (by positivity) (not_lt.mp hnn)
        omega
      · exact absurd hzQ (lt_irrefl 0))
    (fun e _ ↦ ⟨e, rfl⟩) (fun Q _ ↦ ⟨Q.1, rfl⟩)
  exact ⟨M, Nat.one_le_iff_ne_zero.mpr hM0, hcore⟩

end SuperData

end Differential
