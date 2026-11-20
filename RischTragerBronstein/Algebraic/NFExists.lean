import RischTragerBronstein.Algebraic.NFRoots

/-!
# Every finite set of algebraic numbers lies in a certified number field

**`exists_nf`**: for a finite set `S ⊆ ℚ̄` there is `M ∈ ℚ[γ]` accepted by the irreducibility test
`Kron.irredQ` and a root `θ` of `M` such that every element of `S` is the image of an element of
the computable number field `NF M` under the embedding `rho M : γ ↦ θ`.

Proof: a primitive element `α` of `ℚ(S)` (`Field.exists_primitive_element`), made integral
(`θ = y α`, `exists_integral_multiple`); `M` is the minimal polynomial of `θ` over `ℤ` (monic,
primitive, irreducible over `ℚ` by Gauss), accepted by `irredQ` (`irredQ_complete`).

This is the number-field part of the existence of certificates (`CertExists`): any finite amount of
algebraic data (Puiseux coefficients, points, roots of unity) can be written over some `NF M`.
-/

open Polynomial CPoly IntermediateField

namespace NFC

lemma toPoly_coeffList {F : Type*} [CommRing F] (f : F[X]) :
    CPoly.toPoly ((List.range (f.natDegree + 1)).map f.coeff) = f := by
  ext k
  rw [CPoly.coeff_toPoly]
  rcases Nat.lt_or_ge k (f.natDegree + 1) with hk | hk
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

lemma gcdL_of_one_mem : ∀ {l : List ℤ}, (1 : ℤ) ∈ l → Kron.gcdL l = 1
  | a :: l, h => by
    simp only [Kron.gcdL, List.foldr_cons] at *
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := gcdL_of_one_mem h
      simp only [Kron.gcdL] at this
      rw [this]; simp

/-- **Finitely many algebraic numbers lie in a certified number field** (with integral `M`). -/
theorem exists_nf_int (S : Finset QB) :
    ∃ M : CPoly ℚ, ∃ hM : Kron.irredQ M = true, (∀ q ∈ M, q.den = 1) ∧
      ∃ θ : QB, ∃ hθ : aeval θ (toPoly M) = 0,
      haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      ∀ s ∈ S, ∃ c : NF M, rho M hθ c = s := by
  classical
  set E := IntermediateField.adjoin ℚ (S : Set QB) with hE
  have hint : ∀ x : QB, IsIntegral ℚ x := fun x ↦ (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  haveI : FiniteDimensional ℚ E :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ hint x
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  -- an integral multiple of the primitive element
  have hαalg : IsAlgebraic ℤ (α : QB) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ QB).mpr (hint _).isAlgebraic
  obtain ⟨y, hy0, hyint⟩ := hαalg.exists_integral_multiple
  set θ : QB := y • (α : QB) with hθdef
  have hθint : IsIntegral ℤ θ := hyint
  set m := minpoly ℤ θ with hm
  have hmmon : m.Monic := minpoly.monic hθint
  have hmQ : minpoly ℚ θ = m.map (Int.castRingHom ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hθint
  -- the list of coefficients
  set M : CPoly ℚ := (List.range (m.natDegree + 1)).map fun i ↦ ((m.coeff i : ℤ) : ℚ) with hMdef
  have hMpoly : toPoly M = minpoly ℚ θ := by
    rw [hmQ, ← toPoly_coeffList (m.map (Int.castRingHom ℚ)), natDegree_map_eq_of_injective
      (RingHom.injective_int (Int.castRingHom ℚ))]
    congr 1
    refine List.map_congr_left fun i _ ↦ ?_
    rw [coeff_map]; rfl
  have hMint : ∀ q ∈ M, q.den = 1 := fun q hq ↦ by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
    exact Rat.den_intCast _
  have hMgcd : Kron.gcdL (M.map Rat.num) = 1 := by
    refine gcdL_of_one_mem ?_
    refine List.mem_map.mpr ⟨((m.coeff m.natDegree : ℤ) : ℚ), List.mem_map.mpr
      ⟨m.natDegree, List.mem_range.mpr (Nat.lt_succ_self _), rfl⟩, ?_⟩
    rw [Rat.num_intCast]
    exact hmmon.leadingCoeff
  have hMirr : Irreducible (toPoly M) := by
    rw [hMpoly]; exact minpoly.irreducible (hint θ)
  have hM : Kron.irredQ M = true := Kron.irredQ_complete M hMint hMgcd hMirr
  have hθ : aeval θ (toPoly M) = 0 := by rw [hMpoly]; exact minpoly.aeval ℚ θ
  refine ⟨M, hM, hMint, θ, hθ, fun s hs ↦ ?_⟩
  -- `s` is a polynomial in `α`, hence in `θ`
  have hsE : s ∈ E := IntermediateField.subset_adjoin ℚ _ hs
  have htop : (⟨s, hsE⟩ : E) ∈ ℚ⟮α⟯ := by rw [hα]; exact IntermediateField.mem_top
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic α),
    Algebra.adjoin_singleton_eq_range_aeval] at htop
  obtain ⟨p, hp⟩ := htop
  have hpQB : aeval (α : QB) p = s := by
    have := congrArg (Subtype.val) hp
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [← this]
    exact aeval_algebraMap_apply QB α p
  have hy : (y : QB) ≠ 0 := Int.cast_ne_zero.mpr hy0
  set q : ℚ[X] := p.comp (Polynomial.C ((y : ℚ)⁻¹) * X) with hq
  have hqθ : aeval θ q = s := by
    rw [hq, aeval_comp, map_mul, aeval_C, aeval_X, map_inv₀, map_intCast, hθdef, zsmul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hy, one_mul, hpQB]
  have : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  refine ⟨mk M ((List.range (q.natDegree + 1)).map q.coeff), ?_⟩
  rw [rho_apply, evAt_mk M hθ, toPoly_coeffList, hqθ]

/-- **Finitely many algebraic numbers lie in a certified number field.** -/
theorem exists_nf (S : Finset QB) :
    ∃ M : CPoly ℚ, ∃ hM : Kron.irredQ M = true, ∃ θ : QB, ∃ hθ : aeval θ (toPoly M) = 0,
      haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      ∀ s ∈ S, ∃ c : NF M, rho M hθ c = s := by
  obtain ⟨M, hM, -, θ, hθ, h⟩ := exists_nf_int S
  exact ⟨M, hM, θ, hθ, h⟩

end NFC
