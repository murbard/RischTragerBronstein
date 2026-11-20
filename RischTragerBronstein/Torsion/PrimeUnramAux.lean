import RischTragerBronstein.Torsion.UnramTest

/-!
# Auxiliary lemmas for the prime step (unramified divisors)
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section Aux

variable {C : Type*} [Field C]

lemma princTest_reindex {n : ℕ} (δ : Fin n → ℕ) (M : ℕ) {Q Q' : Type*} (eq : Q' ≃ Q)
    (e : Q → ℕ) (a : Q → C) (σ : Q → Fin n → LaurentSeries C) (b : Q → ℕ) :
    princTest δ M (fun q ↦ e (eq q)) (fun q ↦ a (eq q)) (fun q ↦ σ (eq q)) (fun q ↦ b (eq q)) ↔
      princTest δ M e a σ b := by
  unfold princTest
  refine exists_congr fun cc ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  constructor
  · intro h q
    have := h (eq.symm q)
    simpa using this
  · intro h q
    exact h (eq q)

variable {C' : Type*} [Field C']

lemma split_map (φ : C →+* C') (F : C[X][X]) (N : ℕ) (a : C) {n : ℕ} (r : Fin n → LaurentSeries C)
    (hs : F.map (branchSub (C := C) (K := C) N a) = ∏ k, (X - Polynomial.C (r k))) :
    (F.map (mapRingHom φ)).map (branchSub (C := C') (K := C') N (φ a)) =
      ∏ k, (X - Polynomial.C (lmap φ (r k))) := by
  have h : (branchSub (C := C') (K := C') N (φ a)).comp (mapRingHom φ) =
      (lmap φ).comp (branchSub (C := C) (K := C) N a) :=
    RingHom.ext fun P ↦ by simp only [RingHom.comp_apply, coe_mapRingHom]; rw [lmap_branchSub']
  rw [Polynomial.map_map, h, ← Polynomial.map_map, hs, Polynomial.map_prod]
  exact Finset.prod_congr rfl fun k _ ↦ by simp

end Aux

section Ser

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- The basis expansions along Hensel branches are integral. -/
lemma basisSer_lowerBd_unram {B : Fin S.F.natDegree → C[X][X]} {D : C[X]}
    {δ : Fin S.F.natDegree → ℕ} (hB : S.IsIntBasis K B D δ) (a : C)
    (Y0 : Fin S.F.natDegree → PowerSeries C)
    (hsp : S.F.map (branchSub (C := C) (K := C) 1 a) =
      ∏ k, (X - Polynomial.C (ofPowerSeries ℤ C (Y0 k)))) (k i : Fin S.F.natDegree) :
    LowerBd (basisSer B D 1 a (ofPowerSeries ℤ C (Y0 k)) i) 0 := by
  have hroot : (S.F.map (branchSub (K := C) 1 a)).eval (ofPowerSeries ℤ C (Y0 k)) = 0 := by
    rw [hsp, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  have hl := S.split_lmap (K := K) 1 a (fun k ↦ ofPowerSeries ℤ C (Y0 k)) hsp
  have h1 := hB.reg i (algebraMap C K a) 1 one_ne_zero _ hl _ (List.mem_ofFn.mpr ⟨k, rfl⟩)
  rw [S.embG_lmap_fnWQ 1 one_pos a _ hroot] at h1
  exact (lowerBd_lmap_iff _ _ _).mp (lowerBd_of_le_order _ 0 h1)

end CurveData

end Ser

section Transport

variable {C L C' L' : Type*} [Field C] [Field L] [Algebra C L] [Field C'] [Field L'] [Algebra C' L']

/-- **Transport of the unramified test along a field embedding.** -/
theorem princTest_transport (S : CurveData C L) (S' : CurveData C' L') (φ : C →+* C')
    (hnK : S'.F.natDegree = S.F.natDegree) (B : Fin S.F.natDegree → C[X][X]) (D : C[X])
    (δ : Fin S.F.natDegree → ℕ) (B' : Fin S'.F.natDegree → C'[X][X]) (D' : C'[X])
    (hB' : ∀ i, B' i = (B (Fin.cast hnK i)).map (mapRingHom φ)) (hD' : D' = D.map φ)
    {J : Type*} (α : J → C) (α' : J → C') (hα' : ∀ j, α' j = φ (α j))
    (Y0 : J → Fin S.F.natDegree → PowerSeries C) (Y0' : J → Fin S'.F.natDegree → PowerSeries C')
    (hY0' : ∀ j k, Y0' j k = PowerSeries.map φ (Y0 j (Fin.cast hnK k)))
    (hσ : ∀ (q : J × Fin S.F.natDegree) i,
      LowerBd (basisSer B D 1 (α q.1) (ofPowerSeries ℤ C (Y0 q.1 q.2)) i) 0)
    [Fintype J] (β : J → Fin S.F.natDegree → ℕ) (M : ℕ) :
    princTest δ M (fun _ : J × Fin S.F.natDegree ↦ 1) (fun q ↦ α q.1)
        (fun q i ↦ basisSer B D 1 (α q.1) (ofPowerSeries ℤ C (Y0 q.1 q.2)) i) (fun q ↦ β q.1 q.2) ↔
      princTest (fun i ↦ δ (Fin.cast hnK i)) M (fun _ : J × Fin S'.F.natDegree ↦ 1)
        (fun q ↦ α' q.1) (fun q i ↦ basisSer B' D' 1 (α' q.1) (ofPowerSeries ℤ C' (Y0' q.1 q.2)) i)
        (fun q ↦ β q.1 (Fin.cast hnK q.2)) := by
  rw [← princTest_map_iff φ δ M _ _ _ _ hσ, ← princTest_cast hnK]
  set eq : J × Fin S'.F.natDegree ≃ J × Fin S.F.natDegree :=
    Equiv.prodCongr (Equiv.refl J) (finCongr hnK) with heq
  rw [← princTest_reindex (fun i ↦ δ (Fin.cast hnK i)) M eq]
  have e1 : (fun q : J × Fin S'.F.natDegree ↦ φ (α (eq q).1)) = fun q ↦ α' q.1 := by
    funext q; rw [hα']; rfl
  have e2 : (fun (q : J × Fin S'.F.natDegree) (i : Fin S'.F.natDegree) ↦
      lmap φ (basisSer B D 1 (α (eq q).1) (ofPowerSeries ℤ C (Y0 (eq q).1 (eq q).2)) (Fin.cast hnK i))) =
      fun q i ↦ basisSer B' D' 1 (α' q.1) (ofPowerSeries ℤ C' (Y0' q.1 q.2)) i := by
    funext q i
    have hBf : B' = fun i ↦ (B (Fin.cast hnK i)).map (mapRingHom φ) := funext hB'
    rw [basisSer_map, lmap_ofPS, hY0', hα', hD', hBf]
    rfl
  simp only [e1] at *
  rw [show (fun (q : J × Fin S'.F.natDegree) (i : Fin S'.F.natDegree) ↦
      lmap φ (basisSer B D 1 (α (eq q).1) (ofPowerSeries ℤ C (Y0 (eq q).1 (eq q).2))
        (Fin.cast hnK i))) = _ from e2]
  rfl

end Transport

end Curves
