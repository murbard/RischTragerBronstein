import RischTragerBronstein.Torsion.PrincTest
import Mathlib.FieldTheory.Finite.Basic

/-!
# Towards the finiteness of `Pic⁰` over finite fields: Riemann's inequality by counting

`princTest_of_card_lt`: when the principality test has more unknowns (coefficients of the
`cᵢ(x)`, `deg cᵢ + δᵢ ≤ M`) than conditions (`∑ b_q` Taylor coefficients), it passes — a non-zero
solution of a homogeneous linear system with more unknowns than equations. This is the linear
algebra behind Riemann's inequality `ℓ(D) ≥ deg D + 1 − g` in the explicit model, the first step of
the proof that every divisor class of degree `0` over a finite field has finite order.
-/

open Polynomial HahnSeries Module

namespace Curves

open Differential LaurentSeries

section Count

variable {C : Type*} [Field C]

/-- **More unknowns than equations**: the test passes. -/
theorem princTest_of_card_lt {n : ℕ} (δ : Fin n → ℕ) (M : ℕ) {Q : Type*} [Fintype Q] (e : Q → ℕ)
    (a : Q → C) (σ : Q → Fin n → LaurentSeries C) (b : Q → ℕ) (hσ : ∀ q i, LowerBd (σ q i) 0)
    (hcard : ∑ q, b q < ∑ i, (M + 1 - δ i)) : princTest δ M e a σ b := by
  classical
  rw [princTest_iff δ M e a σ b hσ]
  intro hli
  have h1 := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma, Fintype.card_sigma] at h1
  simp only [Fintype.card_fin] at h1
  omega

/-- **Rank bound**: if every column of the test lies in the range of a linear map from a space of
dimension smaller than the number of unknowns, the test passes (the rows along conjugate branches
of a ramified place are redundant, so counting rows is not enough there). -/
theorem princTest_of_range {n : ℕ} (δ : Fin n → ℕ) (M : ℕ) {Q : Type*} [Fintype Q] (e : Q → ℕ)
    (a : Q → C) (σ : Q → Fin n → LaurentSeries C) (b : Q → ℕ) (hσ : ∀ q i, LowerBd (σ q i) 0)
    {R : Type*} [Fintype R] (Ψ : (R → C) →ₗ[C] ((Σ q : Q, Fin (b q)) → C))
    (hcol : ∀ ie, princCol δ M e a σ b ie ∈ LinearMap.range Ψ)
    (hcard : Fintype.card R < ∑ i, (M + 1 - δ i)) : princTest δ M e a σ b := by
  classical
  rw [princTest_iff δ M e a σ b hσ]
  intro hli
  -- the columns, as a family in the range of `Ψ`
  set v : (Σ i : Fin n, Fin (M + 1 - δ i)) → LinearMap.range Ψ := fun ie ↦ ⟨_, hcol ie⟩
  have hv : LinearIndependent C v := by
    refine LinearIndependent.of_comp (LinearMap.range Ψ).subtype ?_
    exact hli
  have h1 := hv.fintype_card_le_finrank
  have h2 : finrank C (LinearMap.range Ψ) ≤ Fintype.card R := by
    have := LinearMap.finrank_range_le Ψ
    rwa [Module.finrank_fintype_fun_eq_card] at this
  rw [Fintype.card_sigma] at h1
  simp only [Fintype.card_fin] at h1
  omega

end Count

section Frob

/-! ### Frobenius and root multiplicities over a finite field

For `P ∈ C[x]`, `C = 𝔽_q`, and `K ⊇ C`: the map `b ↦ b^q` permutes the roots of `P` in `K` and
preserves their multiplicities; every root satisfies `b^{q^k} = b` with `k = (#roots)!`. -/

variable {C K : Type*} [Field C] [Fintype C] [Field K] [Algebra C K]

/-- The Frobenius `x ↦ x^q` of `K` (`q = #C`). -/
lemma exists_frob : ∃ φ : K →+* K, ∀ x, φ x = x ^ Fintype.card C := by
  obtain ⟨p, hC, n, hp, hcard⟩ := FiniteField.card' C
  haveI := hC
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap C K).injective p
  haveI : Fact p.Prime := ⟨hp⟩
  exact ⟨iterateFrobenius K p n, fun x ↦ by rw [iterateFrobenius_def, hcard]⟩

/-- An injective self-map preserving a finite set `R` fixes it after `(#R)!` steps. -/
lemma iterate_fix_of_mapsTo {K : Type*} {f : K → K} (hf : Function.Injective f) (R : Finset K)
    (hR : ∀ b ∈ R, f b ∈ R) : ∀ b ∈ R, f^[R.card.factorial] b = b := by
  classical
  let g : R → R := fun b ↦ ⟨f b, hR b b.2⟩
  have hg : Function.Injective g := fun b b' h ↦ Subtype.ext (hf (congrArg Subtype.val h))
  let σ : Equiv.Perm R := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)
  have h2 : ∀ (k : ℕ) (b' : R), ((σ ^ k) b' : K) = f^[k] b' := by
    intro k
    induction k with
    | zero => intro b'; rfl
    | succ k ih =>
      intro b'
      rw [pow_succ', Equiv.Perm.mul_apply, Function.iterate_succ_apply']
      show f ((σ ^ k) b' : K) = _
      rw [ih]
  intro b hb
  have hσ : σ ^ R.card.factorial = 1 := by
    have := pow_card_eq_one (x := σ)
    rwa [Fintype.card_perm, Fintype.card_coe] at this
  have h3 : (σ ^ R.card.factorial) ⟨b, hb⟩ = ⟨b, hb⟩ := by rw [hσ]; rfl
  have := congrArg Subtype.val h3
  rwa [h2] at this

variable {φ : K →+* K} (hφ : ∀ x, φ x = x ^ Fintype.card C)
include hφ

lemma frob_fix (c : C) : φ (algebraMap C K c) = algebraMap C K c := by
  rw [hφ, ← map_pow, FiniteField.pow_card]

lemma map_frob (P : C[X]) : (P.map (algebraMap C K)).map φ = P.map (algebraMap C K) := by
  rw [Polynomial.map_map]
  congr 1
  exact RingHom.ext fun c ↦ frob_fix hφ c

lemma rootMult_le_frob (P : C[X]) (hP : P ≠ 0) (b : K) :
    (P.map (algebraMap C K)).rootMultiplicity b ≤
      (P.map (algebraMap C K)).rootMultiplicity (φ b) := by
  have h0 : (P.map (algebraMap C K)).map φ ≠ 0 := by
    rw [map_frob hφ]; exact (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hP
  have := le_rootMultiplicity_map h0 b
  rwa [map_frob hφ] at this

lemma iterate_frob (k : ℕ) (b : K) : φ^[k] b = b ^ (Fintype.card C ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, hφ, ← pow_mul, pow_succ]

/-- **The roots are fixed by a bounded power of the Frobenius.** -/
lemma frob_iterate_root (P : C[X]) (hP : P ≠ 0) :
    ∃ k, 0 < k ∧ ∀ b ∈ (P.map (algebraMap C K)).roots, φ^[k] b = b := by
  classical
  set Q := P.map (algebraMap C K) with hQ
  have hQ0 : Q ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hP
  set R := Q.roots.toFinset with hR
  have hmaps : ∀ b ∈ R, φ b ∈ R := fun b hb ↦ by
    rw [hR, Multiset.mem_toFinset, mem_roots hQ0, ← rootMultiplicity_pos hQ0] at hb ⊢
    exact lt_of_lt_of_le hb (rootMult_le_frob hφ P hP b)
  -- the Frobenius permutes `R`
  let f : R → R := fun b ↦ ⟨φ b, hmaps b b.2⟩
  have hf : Function.Injective f := fun b b' h ↦
    Subtype.ext (φ.injective (congrArg Subtype.val h))
  let σ : Equiv.Perm R := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  refine ⟨orderOf σ, orderOf_pos σ, fun b hb ↦ ?_⟩
  have h1 : (σ ^ orderOf σ) ⟨b, Multiset.mem_toFinset.mpr hb⟩ = ⟨b, Multiset.mem_toFinset.mpr hb⟩ := by
    rw [pow_orderOf_eq_one]; rfl
  have h2 : ∀ (k : ℕ) (b' : R), ((σ ^ k) b' : K) = φ^[k] b' := by
    intro k
    induction k with
    | zero => intro b'; rfl
    | succ k ih =>
      intro b'
      rw [pow_succ', Equiv.Perm.mul_apply, Function.iterate_succ_apply']
      show φ ((σ ^ k) b' : K) = _
      rw [ih]
  have := congrArg Subtype.val h1
  rwa [h2] at this

/-- **Frobenius-invariance of multiplicities.** -/
lemma rootMult_frob (P : C[X]) (hP : P ≠ 0) (b : K) :
    (P.map (algebraMap C K)).rootMultiplicity (φ b) =
      (P.map (algebraMap C K)).rootMultiplicity b := by
  classical
  set Q := P.map (algebraMap C K) with hQ
  have hQ0 : Q ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hP
  have hmono : ∀ (i : ℕ) (z : K), Q.rootMultiplicity z ≤ Q.rootMultiplicity (φ^[i] z) := by
    intro i
    induction i with
    | zero => intro z; rfl
    | succ i ih =>
      intro z
      rw [Function.iterate_succ_apply']
      exact (ih z).trans (rootMult_le_frob hφ P hP _)
  by_cases hb : Q.rootMultiplicity (φ b) = 0
  · rw [hb]
    exact (Nat.eq_zero_of_le_zero ((rootMult_le_frob hφ P hP b).trans hb.le)).symm
  · obtain ⟨k, hk, hfix⟩ := frob_iterate_root hφ P hP
    have memR : ∀ z, z ∈ Q.roots ↔ 0 < Q.rootMultiplicity z := fun z ↦ by
      rw [mem_roots hQ0, rootMultiplicity_pos hQ0]
    have hroot : φ b ∈ Q.roots := (memR _).mpr (Nat.pos_of_ne_zero hb)
    have hfb := hfix (φ b) hroot
    -- `φ^[k] b = b` (apply the injective `φ` once more)
    have hkb : φ^[k] b = b := by
      apply φ.injective
      rw [← Function.iterate_succ_apply' φ k b, Function.iterate_succ_apply]
      exact hfb
    have ek : φ^[k - 1] (φ b) = b := by
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hk, hkb]
    apply le_antisymm _ (rootMult_le_frob hφ P hP b)
    have := hmono (k - 1) (φ b)
    rwa [ek] at this

/-- The fixed points of `φᵏ` form a finite set. -/
lemma finite_frob_fixed (k : ℕ) (hk : 0 < k) : {b : K | φ^[k] b = b}.Finite := by
  classical
  have hq : 1 < Fintype.card C ^ k := Nat.one_lt_pow hk.ne' Fintype.one_lt_card
  set Q : K[X] := X ^ (Fintype.card C ^ k) - X with hQ
  have hQ0 : Q ≠ 0 := by
    intro h
    have := congrArg natDegree h
    rw [hQ, natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X, natDegree_X_pow]; exact hq),
      natDegree_X_pow, natDegree_zero] at this
    omega
  refine (Q.roots.toFinset.finite_toSet).subset fun b hb ↦ ?_
  have hb' : b ^ (Fintype.card C ^ k) = b := by
    have := hb
    simp only [Set.mem_ofPred_eq] at this
    rwa [iterate_frob hφ] at this
  rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hQ0, IsRoot, hQ, eval_sub, eval_pow, eval_X,
    hb', sub_self]

end Frob

end Curves
