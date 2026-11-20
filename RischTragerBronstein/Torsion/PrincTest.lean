import RischTragerBronstein.Torsion.PrincipalMul
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# The linear-algebra principality test and field extensions

`princTest δ M e a σ b`: some non-zero coordinate vector `c` (`deg cᵢ + δᵢ ≤ M`) makes each
`∑ᵢ cᵢ(a_q + T^{e_q}) σ_{q,i}` vanish to order `b_q`. It is the linear dependence of explicit
columns (`princTest_iff`), hence invariant under field extensions (`princTest_map_iff`).
-/

open Polynomial HahnSeries Module

namespace Curves

open Differential LaurentSeries

section Test

variable {C : Type*} [Field C]

/-- **The principality test.** -/
def princTest {n : ℕ} (δ : Fin n → ℕ) (M : ℕ) {Q : Type*} (e : Q → ℕ) (a : Q → C)
    (σ : Q → Fin n → LaurentSeries C) (b : Q → ℕ) : Prop :=
  ∃ cc : Fin n → C[X], cc ≠ 0 ∧ (∀ i, cc i ≠ 0 → (cc i).natDegree + δ i ≤ M) ∧
    ∀ q, LowerBd (∑ i, branchSub (C := C) (K := C) (e q) (a q) (cc i) * σ q i) (b q)

/-- The columns of the test. -/
noncomputable def princCol {n : ℕ} (δ : Fin n → ℕ) (M : ℕ) {Q : Type*} (e : Q → ℕ) (a : Q → C)
    (σ : Q → Fin n → LaurentSeries C) (b : Q → ℕ) :
    (Σ i : Fin n, Fin (M + 1 - δ i)) → (Σ q : Q, Fin (b q)) → C :=
  fun ie qt ↦ (branchSub (C := C) (K := C) (e qt.1) (a qt.1) (X ^ (ie.2 : ℕ)) * σ qt.1 ie.1).coeff (qt.2 : ℕ)

lemma polyOfFin_eq_sum {k : ℕ} (v : Fin k → C) :
    polyOfFin v = ∑ e : Fin k, Polynomial.C (v e) * X ^ (e : ℕ) := rfl

theorem princTest_iff {n : ℕ} (δ : Fin n → ℕ) (M : ℕ) {Q : Type*} [Fintype Q] (e : Q → ℕ)
    (a : Q → C) (σ : Q → Fin n → LaurentSeries C) (b : Q → ℕ) (hσ : ∀ q i, LowerBd (σ q i) 0) :
    princTest δ M e a σ b ↔ ¬ LinearIndependent C (princCol δ M e a σ b) := by
  classical
  rw [Fintype.not_linearIndependent_iff]
  -- the series attached to a coefficient array
  have hser : ∀ (g : (Σ i : Fin n, Fin (M + 1 - δ i)) → C) (q : Q),
      ∑ i, branchSub (C := C) (K := C) (e q) (a q) (polyOfFin fun e' ↦ g ⟨i, e'⟩) * σ q i =
        ∑ ie : (Σ i : Fin n, Fin (M + 1 - δ i)), g ie •
          (branchSub (C := C) (K := C) (e q) (a q) (X ^ (ie.2 : ℕ)) * σ q ie.1) := by
    intro g q
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [polyOfFin_eq_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e' _ ↦ ?_
    rw [map_mul, bs_C, mul_assoc, HahnSeries.C_mul_eq_smul]
    rfl
  constructor
  · rintro ⟨cc, hc0, hdeg, hlb⟩
    -- the coefficient array
    refine ⟨fun ie ↦ (cc ie.1).coeff ie.2, ?_, ?_⟩
    · funext qt
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, princCol, Pi.zero_apply]
      have hcc : ∀ i, cc i = polyOfFin fun e' : Fin (M + 1 - δ i) ↦ (cc i).coeff e' := by
        intro i
        ext t
        by_cases ht : t < M + 1 - δ i
        · rw [polyOfFin_coeff _ ⟨t, ht⟩]
        · rw [polyOfFin, finset_sum_coeff]
          rw [Finset.sum_eq_zero fun e' _ ↦ by
            rw [coeff_C_mul_X_pow, if_neg (by have := e'.isLt; omega)]]
          by_cases h0 : cc i = 0
          · rw [h0, Polynomial.coeff_zero]
          · exact coeff_eq_zero_of_natDegree_lt (by have := hdeg i h0; omega)
      have := congrArg (fun z : LaurentSeries C ↦ z.coeff (qt.2 : ℕ)) (hser (fun ie ↦ (cc ie.1).coeff ie.2) qt.1)
      simp only [← hcc] at this
      have h1 := hlb qt.1 ((qt.2 : ℕ) : ℤ) (by exact_mod_cast qt.2.isLt)
      rw [this, HahnSeries.coeff_sum] at h1
      simpa [HahnSeries.coeff_smul] using h1
    · by_contra hall
      push Not at hall
      apply hc0
      funext i
      ext t
      by_cases ht : t < M + 1 - δ i
      · exact hall ⟨i, ⟨t, ht⟩⟩
      · by_cases h0 : cc i = 0
        · rw [h0]; simp
        · simp only [Pi.zero_apply, Polynomial.coeff_zero]
          exact coeff_eq_zero_of_natDegree_lt (by have := hdeg i h0; omega)
  · rintro ⟨g, hg, i0, hi0⟩
    refine ⟨fun i ↦ polyOfFin fun e' ↦ g ⟨i, e'⟩, fun h0 ↦ hi0 ?_, fun i hi ↦ ?_, fun q t ht ↦ ?_⟩
    · have := congrArg (fun cc : Fin n → C[X] ↦ (cc i0.1).coeff i0.2) h0
      simp only [Pi.zero_apply, Polynomial.coeff_zero, polyOfFin_coeff] at this
      exact this
    · have hk : 0 < M + 1 - δ i := by
        by_contra h
        apply hi
        simp only [polyOfFin]
        exact Finset.sum_eq_zero fun e' _ ↦ absurd e'.isLt (by omega)
      have := polyOfFin_natDegree (fun e' : Fin (M + 1 - δ i) ↦ g ⟨i, e'⟩) hk
      have h2 : (polyOfFin fun e' : Fin (M + 1 - δ i) ↦ g ⟨i, e'⟩).natDegree + δ i ≤ M := by omega
      exact h2
    · rw [hser]
      by_cases ht0 : t < 0
      · rw [HahnSeries.coeff_sum]
        refine Finset.sum_eq_zero fun ie _ ↦ ?_
        rw [HahnSeries.coeff_smul]
        have hb : LowerBd (branchSub (C := C) (K := C) (e q) (a q) (X ^ (ie.2 : ℕ))) 0 := by
          rw [branchSub_apply]; intro k hk; exact LaurentSeries.coeff_ofPS_neg _ hk
        have := (hb.mul (hσ q ie.1)) t (by simpa using ht0)
        rw [this, smul_zero]
      · push Not at ht0
        have := congrFun hg ⟨q, ⟨t.toNat, by omega⟩⟩
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, princCol, Pi.zero_apply] at this
        rw [HahnSeries.coeff_sum]
        simp only [HahnSeries.coeff_smul, smul_eq_mul]
        rw [← Int.toNat_of_nonneg ht0]
        exact this

variable {C' : Type*} [Field C']

lemma lmap_branchSub' (φ : C →+* C') (N : ℕ) (a : C) (P : C[X]) :
    lmap φ (branchSub (C := C) (K := C) N a P) = branchSub (C := C') (K := C') N (φ a) (P.map φ) := by
  letI := φ.toAlgebra
  have h := lmap_branchSub (K := C') N a P
  have e1 : branchSub (C := C) (K := C') N (φ a) P =
      branchSub (C := C') (K := C') N (φ a) (P.map φ) := by
    rw [branchSub_apply, branchSub_apply, Polynomial.map_map]
    rfl
  rw [← e1]
  exact h

/-- **The test is invariant under field extensions.** -/
theorem princTest_map_iff (φ : C →+* C') {n : ℕ} (δ : Fin n → ℕ) (M : ℕ) {Q : Type*} [Fintype Q]
    (e : Q → ℕ) (a : Q → C) (σ : Q → Fin n → LaurentSeries C) (b : Q → ℕ)
    (hσ : ∀ q i, LowerBd (σ q i) 0) :
    princTest δ M e (fun q ↦ φ (a q)) (fun q i ↦ lmap φ (σ q i)) b ↔ princTest δ M e a σ b := by
  letI := φ.toAlgebra
  have hσ' : ∀ q i, LowerBd (lmap φ (σ q i)) 0 := fun q i ↦ (lowerBd_lmap_iff φ _ _).mpr (hσ q i)
  rw [princTest_iff δ M e _ _ b hσ', princTest_iff δ M e a σ b hσ]
  have hcol : princCol δ M e (fun q ↦ φ (a q)) (fun q i ↦ lmap φ (σ q i)) b =
      fun ie ↦ algebraMap C C' ∘ princCol δ M e a σ b ie := by
    funext ie qt
    simp only [princCol, Function.comp_apply]
    rw [← Polynomial.map_X φ, ← Polynomial.map_pow, ← lmap_branchSub', ← map_mul, lmap_coeff]
    rfl
  rw [hcol, linearIndependent_algebraMap_comp_iff]

end Test

end Curves
