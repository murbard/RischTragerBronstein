import RischTragerBronstein.Algebraic.SuperBase

/-!
# Arithmetic of orders on a superelliptic curve

At every point `(α, β)` of `yⁿ = p(x)` the order `ordAt` is the order of a ring embedding into
Laurent series (`ordAt_hom`), hence a valuation on non-zero elements: `ordAt_mul`, `ordAt_pow`,
`ordAt_inv`, `ordAt_zpow`, `ordAt_prod`. Same for `ordInf`.

`ordAt_X_sub`: `x − c` has order `1` at the non-branch points above `c`, `n` at the branch point
`c`, and `0` elsewhere.
-/

open Polynomial IntermediateField HahnSeries

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [PerfectField C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K] [IsAlgClosed K]

variable (S : SuperData C L)

/-- At a point of the curve, `ordAt` is the order of a ring embedding. -/
lemma ordAt_hom (α β : K) (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    ∃ φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K, ∀ w, S.ordAt K w α β = (φ w).order := by
  by_cases hβ : β = 0
  · subst hβ
    have he : (S.p.map (algebraMap C K)).eval α = 0 := by rw [← hv, zero_pow S.hn.ne']
    obtain ⟨γ, hγ, hγp⟩ := S.exists_gamma α he
    exact ⟨S.embB α γ he hγ hγp, fun w ↦ S.ordAt_br w α γ he hγ hγp⟩
  · exact ⟨S.embXY α β hβ hv, fun w ↦ S.ordAt_nb w α β hβ hv⟩

lemma ordInf_hom (hcop : Nat.Coprime S.n S.p.natDegree) :
    ∃ φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K, ∀ w, S.ordInf K w = (φ w).order := by
  obtain ⟨lam, hlam, hlp⟩ := S.exists_lam (K := K)
  exact ⟨S.embI lam hlam hlp, fun w ↦ S.ordInf_eq hcop w lam hlam hlp⟩

section Val

variable {M : Type*} [Field M] (φ : M →+* LaurentSeries K)

lemma order_hom_mul {u v : M} (hu : u ≠ 0) (hv : v ≠ 0) :
    (φ (u * v)).order = (φ u).order + (φ v).order := by
  rw [map_mul, HahnSeries.order_mul ((map_ne_zero_iff _ φ.injective).mpr hu)
    ((map_ne_zero_iff _ φ.injective).mpr hv)]

lemma order_hom_pow (u : M) (k : ℕ) : (φ (u ^ k)).order = k * (φ u).order := by
  rw [map_pow, HahnSeries.order_pow, nsmul_eq_mul]

lemma order_hom_inv (u : M) : (φ u⁻¹).order = -(φ u).order := by
  by_cases hu : u = 0
  · simp [hu]
  rw [map_inv₀, order_inv' _ ((map_ne_zero_iff _ φ.injective).mpr hu)]

lemma order_hom_zpow (u : M) (k : ℤ) : (φ (u ^ k)).order = k * (φ u).order := by
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, order_hom_pow]
  · rw [zpow_neg, zpow_natCast, order_hom_inv, order_hom_pow]; ring

lemma order_hom_prod {ι : Type*} (s : Finset ι) (u : ι → M) (hu : ∀ i ∈ s, u i ≠ 0) :
    (φ (∏ i ∈ s, u i)).order = ∑ i ∈ s, (φ (u i)).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      order_hom_mul φ (hu j (Finset.mem_insert_self j s))
        (Finset.prod_ne_zero_iff.mpr fun i hi ↦ hu i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hu i (Finset.mem_insert_of_mem hi)]

end Val

section Point

variable {α β : K} (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α)
include hv

lemma ordAt_mul {u v : C⟮S.x⟯⟮S.y⟯} (hu : u ≠ 0) (hw : v ≠ 0) :
    S.ordAt K (u * v) α β = S.ordAt K u α β + S.ordAt K v α β := by
  obtain ⟨φ, hφ⟩ := S.ordAt_hom α β hv
  rw [hφ, hφ, hφ, order_hom_mul φ hu hw]

lemma ordAt_pow (u : C⟮S.x⟯⟮S.y⟯) (k : ℕ) : S.ordAt K (u ^ k) α β = k * S.ordAt K u α β := by
  obtain ⟨φ, hφ⟩ := S.ordAt_hom α β hv
  rw [hφ, hφ, order_hom_pow]

lemma ordAt_zpow (u : C⟮S.x⟯⟮S.y⟯) (k : ℤ) : S.ordAt K (u ^ k) α β = k * S.ordAt K u α β := by
  obtain ⟨φ, hφ⟩ := S.ordAt_hom α β hv
  rw [hφ, hφ, order_hom_zpow]

lemma ordAt_inv (u : C⟮S.x⟯⟮S.y⟯) : S.ordAt K u⁻¹ α β = -S.ordAt K u α β := by
  obtain ⟨φ, hφ⟩ := S.ordAt_hom α β hv
  rw [hφ, hφ, order_hom_inv]

lemma ordAt_prod {ι : Type*} (s : Finset ι) (u : ι → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i ∈ s, u i ≠ 0) :
    S.ordAt K (∏ i ∈ s, u i) α β = ∑ i ∈ s, S.ordAt K (u i) α β := by
  obtain ⟨φ, hφ⟩ := S.ordAt_hom α β hv
  rw [hφ, order_hom_prod φ s u hu]
  exact Finset.sum_congr rfl fun i _ ↦ (hφ _).symm

omit hv in
lemma ordInf_mul (hcop : Nat.Coprime S.n S.p.natDegree) {u v : C⟮S.x⟯⟮S.y⟯} (hu : u ≠ 0)
    (hw : v ≠ 0) : S.ordInf K (u * v) = S.ordInf K u + S.ordInf K v := by
  obtain ⟨φ, hφ⟩ := S.ordInf_hom (K := K) hcop
  rw [hφ, hφ, hφ, order_hom_mul φ hu hw]

end Point

/-- The element `P(x)` of `C⟮x⟯⟮y⟯`. -/
noncomputable def polyX (P : C[X]) : C⟮S.x⟯⟮S.y⟯ :=
  letI := algebraAdjoinSimple (F := C) S.x
  algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (algebraMap C[X] C⟮S.x⟯ P)

lemma polyX_ne_zero {P : C[X]} (hP : P ≠ 0) : S.polyX P ≠ 0 := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  rw [polyX]
  exact (map_ne_zero_iff _ (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯).injective).mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective C[X] C⟮S.x⟯)).mpr hP)

lemma polyX_mul (P Q : C[X]) : S.polyX (P * Q) = S.polyX P * S.polyX Q := by
  simp [polyX]

lemma polyX_pow (P : C[X]) (k : ℕ) : S.polyX (P ^ k) = S.polyX P ^ k := by
  simp [polyX]

open Classical in
/-- **Orders of polynomials in `x`**: `ord_{(α,β)} P(x) = e · mult_α P` with `e = 1` off the
branch points and `e = n` at them. -/
theorem ordAt_polyX (P : C[X]) (hP : P ≠ 0) (α β : K)
    (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    S.ordAt K (S.polyX P) α β =
      (if β = 0 then (S.n : ℤ) else 1) * ((P.map (algebraMap C K)).rootMultiplicity α : ℤ) := by
  let _ := algebraAdjoinSimple (F := C) S.x
  by_cases hβ : β = 0
  · subst hβ
    have he : (S.p.map (algebraMap C K)).eval α = 0 := by rw [← hv, zero_pow S.hn.ne']
    obtain ⟨γ, hγ, hγp⟩ := S.exists_gamma α he
    rw [S.ordAt_br _ α γ he hγ hγp, if_pos rfl, polyX]
    unfold embB
    rw [S.embG_algebraMap, S.embXG_algebraMap, order_branchSub S.n S.hn α P hP]
    push_cast; ring
  · rw [S.ordAt_nb _ α β hβ hv, if_neg hβ, polyX, S.embXY_algebraMap, S.embX_algebraMap,
      shiftHom_eq_branchSub, order_branchSub 1 one_pos α P hP]
    push_cast; ring

open Classical in
omit [IsAlgClosed K] in
lemma ordAt_X_sub_mult (c α : K) :
    (((X - Polynomial.C c : K[X]).map (algebraMap K K)).rootMultiplicity α : ℤ) =
      if α = c then 1 else 0 := by
  rw [Algebra.algebraMap_self, Polynomial.map_id, rootMultiplicity_X_sub_C]
  split_ifs <;> simp

/-- **Order at infinity of a polynomial in `x`**: `−n deg P`. -/
theorem ordInf_polyX (hcop : Nat.Coprime S.n S.p.natDegree) (P : C[X]) (hP : P ≠ 0) :
    S.ordInf K (S.polyX P) = -(S.n * P.natDegree : ℤ) := by
  letI := algebraAdjoinSimple (F := C) S.x
  obtain ⟨lam, hlam, hlp⟩ := S.exists_lam (K := K)
  rw [S.ordInf_eq hcop _ lam hlam hlp, polyX]
  unfold embI
  rw [S.embG_algebraMap, S.embXG_inf_poly P hP]

end SuperData

end Differential
