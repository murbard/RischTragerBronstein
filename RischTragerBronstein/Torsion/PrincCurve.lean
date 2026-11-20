import RischTragerBronstein.Torsion.PrincTest

/-!
# Principality on the curve is the linear-algebra test

For a divisor `Γ − M ∞ₓ` given along complete branch systems with coefficients in the base field
`C` (roots `rC j k` at `x = α_j + T^{N_j}`), `principal_iff_test`: some `γ ≠ 0` has
`div γ ≥ Γ − M ∞ₓ` iff `princTest` holds for the expansions `σ` of the integral basis.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section PC

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

/-- The expansions of the basis functions along base-field roots. -/
noncomputable def basisSer (B : Fin n → C[X][X]) (D : C[X]) (N : ℕ) (a : C) (r : LaurentSeries C)
    (i : Fin n) : LaurentSeries C :=
  ((B i).map (branchSub (C := C) (K := C) N a)).eval r * (branchSub (C := C) (K := C) N a D)⁻¹

namespace CurveData

variable (S : CurveData C L)

lemma split_lmap (N : ℕ) (a : C) (r : Fin S.F.natDegree → LaurentSeries C)
    (hs : S.F.map (branchSub (C := C) (K := C) N a) = ∏ k, (X - Polynomial.C (r k))) :
    S.F.map (branchSub N (algebraMap C K a)) =
      ((List.ofFn fun k ↦ lmap (algebraMap C K) (r k)).map fun s ↦ X - Polynomial.C s).prod := by
  have h : branchSub (C := C) (K := K) N (algebraMap C K a) =
      (lmap (algebraMap C K)).comp (branchSub (C := C) (K := C) N a) :=
    RingHom.ext fun P ↦ (lmap_branchSub N a P).symm
  rw [h, ← Polynomial.map_map, hs, Polynomial.map_prod, List.map_ofFn, List.prod_ofFn]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  simp

lemma embG_elt_lmap (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (c : Fin S.F.natDegree → C[X])
    (N : ℕ) (hN : 0 < N) (a : C) (r : LaurentSeries C)
    (hr : (S.F.map (branchSub (K := C) N a)).eval r = 0) :
    S.embG (branchSub N (algebraMap C K a)) (branchSub_injective N hN _) (lmap (algebraMap C K) r)
      (S.lmap_root N a r hr) (S.elt B D c) =
      lmap (algebraMap C K) (∑ i, branchSub (C := C) (K := C) N a (c i) * basisSer B D N a r i) := by
  rw [embG_elt, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, lmap_branchSub, S.embG_lmap_fnWQ N hN a r hr]
  rfl

variable [IsAlgClosed K]

/-- **Principality is the linear-algebra test.** -/
theorem principal_iff_test {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} {δ : Fin S.F.natDegree → ℕ}
    (hB : S.IsIntBasis K B D δ) {J : Type*} [Fintype J] (α : J → C) (N : J → ℕ)
    (hN : ∀ j, 0 < N j) (rC : J → Fin S.F.natDegree → LaurentSeries C)
    (hsC : ∀ j, S.F.map (branchSub (C := C) (K := C) (N j) (α j)) = ∏ k, (X - Polynomial.C (rC j k)))
    (ΓC : J → Fin S.F.natDegree → ℕ) (ΓK : J → LaurentSeries K → ℕ)
    (hΓK : ∀ j k, ΓK j (lmap (algebraMap C K) (rC j k)) = ΓC j k) (M : ℕ) :
    (∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧ S.DivGE α N hN
      (fun j ↦ List.ofFn fun k ↦ lmap (algebraMap C K) (rC j k))
      (fun j ↦ S.split_lmap (N j) (α j) (rC j) (hsC j)) ΓK M γ) ↔
    princTest δ M (Q := J × Fin S.F.natDegree) (fun q ↦ N q.1) (fun q ↦ α q.1)
      (fun q i ↦ basisSer B D (N q.1) (α q.1) (rC q.1 q.2) i) (fun q ↦ ΓC q.1 q.2) := by
  classical
  set ι := algebraMap C K with hι
  have hroot : ∀ j k, (S.F.map (branchSub (K := C) (N j) (α j))).eval (rC j k) = 0 := fun j k ↦ by
    rw [hsC j, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  constructor
  · rintro ⟨γ, hγ0, hγ⟩
    -- `γ` is regular at all finite branches
    have hreg : S.RegularFinite K γ := by
      intro a N' hN' l hl r hr
      by_cases ha : ∃ j, ι (α j) = a
      · obtain ⟨j, rfl⟩ := ha
        obtain ⟨r0, hr0, htr⟩ := S.order_transfer (ι (α j)) (N j) N' (hN j)
          (Nat.pos_of_ne_zero hN') _ l (S.split_lmap (N j) (α j) (rC j) (hsC j)) hl r hr
        have h1 := htr γ
        have h2 := hγ.1 j r0 hr0
        have hNj : (0 : ℤ) < N j := by exact_mod_cast hN j
        have : (0 : ℤ) ≤ N j * (S.embG (branchSub N' (ι (α j)))
            (branchSub_injective N' (Nat.pos_of_ne_zero hN') _) r (S.root_of_mem hl hr) γ).order := by
          rw [h1]; exact mul_nonneg (by positivity) (le_trans (by positivity) h2)
        exact le_of_mul_le_mul_left (by rw [mul_zero]; exact this) hNj
      · exact hγ.2.1 a (by rintro ⟨j, hj⟩; exact ha ⟨j, hj⟩) N' hN' l hl r hr
    obtain ⟨cc, hγcc, hccdeg⟩ := lspace_complete hB γ hreg M (fun N' hN' l hl r hr ↦
      lowerBd_of_le_order _ _ (hγ.2.2 N' hN' l hl r hr))
    refine ⟨cc, fun h0 ↦ hγ0 (by rw [hγcc, h0]; simp [elt]), hccdeg, fun q ↦ ?_⟩
    obtain ⟨j, k⟩ := q
    have hmem : lmap ι (rC j k) ∈ List.ofFn fun k ↦ lmap ι (rC j k) := List.mem_ofFn.mpr ⟨k, rfl⟩
    have h1 := hγ.1 j _ hmem
    rw [hΓK] at h1
    have hne : S.embG (branchSub (N j) (ι (α j))) (branchSub_injective _ (hN j) _)
        (lmap ι (rC j k)) (S.root_of_mem (S.split_lmap (N j) (α j) (rC j) (hsC j)) hmem) γ ≠ 0 :=
      (map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hγ0
    have h2 := lowerBd_of_le_order _ _ h1
    rw [hγcc, S.embG_elt_lmap B D cc (N j) (hN j) (α j) (rC j k) (hroot j k)] at h2
    exact (lowerBd_lmap_iff _ _ _).mp h2
  · rintro ⟨cc, hcc0, hccdeg, hlb⟩
    have hγ0 : S.elt B D cc ≠ 0 := fun h ↦ hcc0 (elt_eq_zero hB.hD hB.deg hB.det cc h)
    refine ⟨S.elt B D cc, hγ0, fun j r hr ↦ ?_, fun b _ N' hN' l hl r hr ↦
      regular_elt hB.reg cc b N' hN' l hl r hr, fun N' hN' l hl r hr ↦
      le_order_of_lowerBd _ ((map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hγ0) _
        (inf_elt hB.inf cc M hccdeg N' hN' l hl r hr)⟩
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
    rw [hΓK]
    refine le_order_of_lowerBd _ ((map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hγ0) _ ?_
    rw [S.embG_elt_lmap B D cc (N j) (hN j) (α j) (rC j k) (hroot j k)]
    exact (lowerBd_lmap_iff _ _ _).mpr (hlb (j, k))

end CurveData

end PC

end Curves
