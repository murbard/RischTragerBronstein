import RischTragerBronstein.Torsion.Bridge

/-!
# The `ℓ`-th power step (general curves)

`ell_powerG`: if `ψ = ∑ cⱼ wⱼ` (pole order `≤ M`) vanishes on `∑ c'_j F_{α_j} − Γ` and `Ξ` has
divisor `≥ ℓ Γ − ℓ c ∞ₓ`, with `M + c = ∑ c'_j + g`, then `ψ^ℓ Ξ / ∏(x − α_j)^{ℓ c'_j}` has
coordinates `q` with `deg q_j + δ_j ≤ ℓ g`, and its order is at least `ℓ ord ψ` along every branch
above any point other than the `α_j`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section Ell

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L) [IsAlgClosed K]

/-- **The `ℓ`-th power step.** -/
theorem ell_powerG {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} {δ : Fin S.F.natDegree → ℕ}
    (hB : S.IsIntBasis K B D δ)
    (c : Fin S.F.natDegree → C[X]) (hc0 : c ≠ 0) (M : ℕ)
    (hdeg : ∀ j, c j ≠ 0 → (c j).natDegree + δ j ≤ M)
    {J : Type*} [Fintype J] (α : J → C) (hα : Function.Injective α) (N : J → ℕ)
    (hN : ∀ j, 0 < N j) (lf : J → List (LaurentSeries K))
    (hlf : ∀ j, S.F.map (branchSub (N j) (algebraMap C K (α j))) =
      ((lf j).map fun r ↦ X - Polynomial.C r).prod)
    (Γ : J → LaurentSeries K → ℕ) (cΓ : ℕ) (c' : J → ℕ) {g : ℕ}
    (hM : M + cΓ = ∑ j, c' j + g)
    (hvT : ∀ j r (hr : r ∈ lf j), ((c' j * N j : ℕ) : ℤ) - Γ j r ≤
      (S.embG (branchSub (N j) (algebraMap C K (α j))) (branchSub_injective _ (hN j) _) r
        (S.root_of_mem (hlf j) hr) (S.elt B D c)).order)
    (ℓ : ℕ) (Ξ : C⟮S.x⟯⟮S.y⟯) (hΞ0 : Ξ ≠ 0)
    (hΞ : S.DivGE α N hN lf hlf (fun j r ↦ ℓ * Γ j r) (ℓ * cΓ) Ξ) :
    ∃ q : Fin S.F.natDegree → C[X], q ≠ 0 ∧ (∀ j, q j ≠ 0 → (q j).natDegree + δ j ≤ ℓ * g) ∧
      ∀ b : K, b ∉ Set.range (fun j ↦ algebraMap C K (α j)) → ∀ (N' : ℕ) (hN' : N' ≠ 0)
        (l : List (LaurentSeries K))
        (hl : S.F.map (branchSub N' b) = (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries K) (hr : r ∈ l),
        (ℓ : ℤ) * (S.embG (branchSub N' b) (branchSub_injective N' (Nat.pos_of_ne_zero hN') b) r
          (S.root_of_mem hl hr) (S.elt B D c)).order ≤
        (S.embG (branchSub N' b) (branchSub_injective N' (Nat.pos_of_ne_zero hN') b) r
          (S.root_of_mem hl hr) (S.elt B D q)).order := by
  classical
  set ι := algebraMap C K with hι
  set ψ := S.elt B D c with hψ
  have hψ0 : ψ ≠ 0 := fun h ↦ hc0 (elt_eq_zero hB.hD hB.deg hB.det c h)
  have hreg : S.RegularFinite K ψ := regular_elt hB.reg c
  set P : C[X] := (∏ j, (X - Polynomial.C (α j)) ^ c' j) ^ ℓ with hP
  have hP0 : P ≠ 0 :=
    pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _))
  have hPK : P.map ι = ∏ j, (X - Polynomial.C (ι (α j))) ^ (ℓ * c' j) := by
    rw [hP, Polynomial.map_pow, Polynomial.map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, ← pow_mul,
      mul_comm]
  have hαι : Function.Injective fun j ↦ ι (α j) := fun a b h ↦ hα (ι.injective h)
  have hdegP : P.natDegree = ℓ * ∑ j, c' j := by
    rw [hP, natDegree_pow, natDegree_prodPow]
  set Φ := ψ ^ ℓ * Ξ * (S.polyF P)⁻¹ with hΦ
  have hordΦ : ∀ (g' : C[X] →+* LaurentSeries K) (hg : Function.Injective g') (r : LaurentSeries K)
      (hr : (S.F.map g').eval r = 0), (S.embG g' hg r hr Φ).order =
        ℓ * (S.embG g' hg r hr ψ).order + (S.embG g' hg r hr Ξ).order - (g' P).order := by
    intro g' hg r hr
    have h1 : S.embG g' hg r hr ψ ≠ 0 := (map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hψ0
    have h2 : S.embG g' hg r hr Ξ ≠ 0 := (map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hΞ0
    have h3 : g' P ≠ 0 := (map_ne_zero_iff _ hg).mpr hP0
    rw [hΦ, map_mul, map_mul, map_pow, map_inv₀, S.embG_polyF,
      HahnSeries.order_mul (mul_ne_zero (pow_ne_zero _ h1) h2) (inv_ne_zero h3),
      HahnSeries.order_mul (pow_ne_zero _ h1) h2, order_inv' _ h3, HahnSeries.order_pow]
    push_cast; ring
  have hΦreg : S.RegularFinite K Φ := by
    intro a N' hN' l hl r hr
    have hN0 : 0 < N' := Nat.pos_of_ne_zero hN'
    rw [hordΦ, order_branchSub _ hN0 _ _ hP0, hPK]
    by_cases ha : ∃ j, ι (α j) = a
    · obtain ⟨j, rfl⟩ := ha
      rw [rootMultiplicity_prodPow_pt _ hαι _ j]
      obtain ⟨r0, hr0, htr⟩ := S.order_transfer (ι (α j)) (N j) N' (hN j) hN0 (lf j) l (hlf j) hl r hr
      have e1 := htr Ξ
      have e2 := htr ψ
      have b1 := hΞ.1 j r0 hr0
      have b2 := hvT j r0 hr0
      have hNj : (0 : ℤ) < N j := by exact_mod_cast hN j
      set oψ := (S.embG (branchSub N' (ι (α j))) (branchSub_injective N' hN0 _) r
        (S.root_of_mem hl hr) ψ).order with hoψ
      set oΞ := (S.embG (branchSub N' (ι (α j))) (branchSub_injective N' hN0 _) r
        (S.root_of_mem hl hr) Ξ).order with hoΞ
      set oψ0 := (S.embG (branchSub (N j) (ι (α j))) (branchSub_injective _ (hN j) _) r0
        (S.root_of_mem (hlf j) hr0) ψ).order with hoψ0
      set oΞ0 := (S.embG (branchSub (N j) (ι (α j))) (branchSub_injective _ (hN j) _) r0
        (S.root_of_mem (hlf j) hr0) Ξ).order with hoΞ0
      have key : (N j : ℤ) * (N' * (ℓ * c' j)) ≤ N j * (ℓ * oψ + oΞ) := by
        have hEq : (N j : ℤ) * (ℓ * oψ + oΞ) = N' * (ℓ * oψ0 + oΞ0) := by
          linear_combination (ℓ : ℤ) * e2 + e1
        rw [hEq]
        push_cast at b1 b2
        have hℓ : (0 : ℤ) ≤ ℓ := by positivity
        have hN'0 : (0 : ℤ) ≤ N' := by positivity
        have : (ℓ : ℤ) * (c' j * N j) ≤ ℓ * oψ0 + oΞ0 := by nlinarith
        nlinarith
      have := le_of_mul_le_mul_left key hNj
      push_cast
      linarith
    · push_neg at ha
      rw [rootMultiplicity_prodPow_off _ _ a (by rintro ⟨j, hj⟩; exact ha j hj)]
      have h1 := hΞ.2.1 a (by rintro ⟨j, hj⟩; exact ha j hj) N' hN' l hl r hr
      have h2 := hreg a N' hN' l hl r hr
      have hℓ : (0 : ℤ) ≤ ℓ := by positivity
      push_cast
      nlinarith
  have hΦinf : ∀ (N' : ℕ) (hN' : N' ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (infSub N') = (l.map fun r ↦ X - Polynomial.C r).prod) (r : LaurentSeries K)
      (hr : r ∈ l), LowerBd (S.embG (infSub N') (infSub_injective N' (Nat.pos_of_ne_zero hN')) r
        (S.root_of_mem hl hr) Φ) (-((N' * (ℓ * g) : ℕ) : ℤ)) := by
    intro N' hN' l hl r hr
    have hN0 : 0 < N' := Nat.pos_of_ne_zero hN'
    refine lowerBd_of_le_order _ _ ?_
    rw [hordΦ, order_infSub _ hN0 _ hP0, hdegP]
    have h1 := hΞ.2.2 N' hN' l hl r hr
    have h2 := le_order_of_lowerBd _ ((map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hψ0) _
      (inf_elt hB.inf c M hdeg N' hN' l hl r hr)
    have h3 : ((M + cΓ : ℕ) : ℤ) = ((∑ j, c' j + g : ℕ) : ℤ) := by rw [hM]
    have hℓ : (0 : ℤ) ≤ ℓ := by positivity
    push_cast at h1 h2 h3 ⊢
    have h4 := mul_nonneg hℓ (sub_nonneg.mpr h2)
    have h5 : (N' : ℤ) * ℓ * (M + cΓ) = N' * ℓ * (∑ x, (c' x : ℤ) + g) := by rw [h3]
    nlinarith [h4, h5, h1]
  obtain ⟨q, hΦq, hqdeg⟩ := lspace_complete hB Φ hΦreg (ℓ * g) hΦinf
  have hΦ0 : Φ ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ hψ0) hΞ0)
    (inv_ne_zero (S.polyF_ne_zero hP0))
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hΦ0
    rw [hΦq]
    simp [elt]
  refine ⟨q, hq0, hqdeg, fun b hb N' hN' l hl r hr ↦ ?_⟩
  have hN0 : 0 < N' := Nat.pos_of_ne_zero hN'
  rw [← hΦq, hordΦ, order_branchSub _ hN0 _ _ hP0, hPK, rootMultiplicity_prodPow_off _ _ b hb]
  have := hΞ.2.1 b hb N' hN' l hl r hr
  push_cast
  linarith

end CurveData

end Ell

end Curves
