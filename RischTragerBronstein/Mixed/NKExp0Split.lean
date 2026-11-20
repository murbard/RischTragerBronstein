import RischTragerBronstein.Mixed.NKExp0Gauge
import RischTragerBronstein.Torsion.HenselBranch

/-!
# The gauge at `x = 0` for a split fibre (exponential level)

`S : CurveData C L` with `x′ = b x` and a fibre above `x = 0` with `n` distinct roots `βₖ ∈ C`
(`F(0, Y) = ∏ (Y − βₖ)`). The branches above `0` are the Hensel lifts `Yₖ` with `Yₖ(0) = βₖ`
(`split_unramified`). The Lagrange elements `εₖ = ∏_{l ≠ k} (y − β_l)/(βₖ − β_l)` are integral with
values `δₖₗ` along the branches. For an integral basis `w` with derivation matrix `M = P/S₀`,
`S₀(0) ≠ 0`, the coordinates `U` of `ε` at `0` are invertible, and the derivation of the residue
algebra `O₀/x` in the basis `ε` vanishes: `(U′ + U M(0)) U⁻¹ = 0` (`exists_gauge0_split`).
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

namespace CurveData

section Gauge0S

variable {C L K : Type*} [Field C] [CharZero C] [DecidableEq C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

variable (S : CurveData C L)

/-- The constant coefficient of a function along a power-series branch above `0`. -/
lemma coeff0_embG_evT (Q : C[X][X]) (Yp : PowerSeries K)
    (hY : (S.F.map (branchSub 1 (0 : K))).eval (ofPowerSeries ℤ K Yp) = 0) :
    (S.embG (branchSub 1 (0 : K)) (branchSub_injective 1 one_pos 0) (ofPowerSeries ℤ K Yp) hY
      (S.evT Q)).coeff 0 =
      ((Q.map (mapRingHom (algebraMap C K))).map (evalRingHom 0)).eval
        (PowerSeries.constantCoeff Yp) := by
  rw [S.embG_evT]
  have e1 : Q.map (branchSub (K := K) 1 0) = (Q.map (psSub 1 0)).map (ofPowerSeries ℤ K) := by
    rw [Polynomial.map_map]; rfl
  rw [e1, eval_map, Polynomial.eval₂_at_apply,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, ← Polynomial.eval₂_at_apply, ← eval_map]
  congr 1
  rw [Polynomial.map_map, Polynomial.map_map]
  congr 1
  refine RingHom.ext fun P ↦ ?_
  show PowerSeries.constantCoeff (psSub 1 (0 : K) P) = (P.map (algebraMap C K)).eval 0
  exact coeff_zero_psSub 0 P

/-- The Lagrange elements `εₖ(y)`. -/
noncomputable def lagE (β : Fin S.F.natDegree → C) (k : Fin S.F.natDegree) : C⟮S.x⟯⟮S.y⟯ :=
  S.evT ((Lagrange.basis Finset.univ β k).map Polynomial.C)

lemma fibre_lagE (β : Fin S.F.natDegree → C) (k : Fin S.F.natDegree) :
    (((Lagrange.basis Finset.univ β k).map Polynomial.C).map (mapRingHom (algebraMap C K))).map
      (evalRingHom 0) = (Lagrange.basis Finset.univ β k).map (algebraMap C K) := by
  rw [Polynomial.map_map, Polynomial.map_map]
  congr 1
  ext c
  simp

variable (b : C) (hx : S.x′ = aeval S.x (Polynomial.C b * X))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

set_option maxHeartbeats 8000000 in
include hx hK in
/-- **The gauge at `x = 0` for a split fibre**: the coordinates `U` at `0` of the Lagrange
elements `εₖ` are invertible and `(U′ + U M(0)) U⁻¹ = 0`. -/
theorem exists_gauge0_split (β : Fin S.F.natDegree → C) (hβ : Function.Injective β)
    (hfib : S.F.map (Polynomial.evalRingHom 0) = ∏ k, (X - Polynomial.C (β k)))
    (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (hwB : S.IBasis K w) (S0 : C[X]) (hS0 : S0.coeff 0 ≠ 0)
    (P : Fin S.F.natDegree → Fin S.F.natDegree → C[X])
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
        S.polyE S0 = ∑ j, S.polyE (P i j) * w j) :
    ∃ (U Ui : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C),
      U * Ui = 1 ∧ Ui * U = 1 ∧
      (U.map (fun z ↦ z′) + U * Matrix.of (fun i j ↦ (P i j).coeff 0 / S0.coeff 0)) * Ui = 0 := by
  classical
  -- the fibre over `K`
  have hfa : ∀ G : C[X][X], fibreAt G (0 : K) = (G.map (evalRingHom 0)).map (algebraMap C K) := by
    intro G
    rw [fibreAt, Polynomial.map_map, Polynomial.map_map]
    congr 1
    refine RingHom.ext fun P ↦ ?_
    show (P.map (algebraMap C K)).eval 0 = algebraMap C K (P.eval 0)
    rw [eval_map, ← map_zero (algebraMap C K), Polynomial.eval₂_at_apply]
  have hevK : ∀ (G : C[X]) (c : C), (G.map (algebraMap C K)).eval (algebraMap C K c) =
      algebraMap C K (G.eval c) := fun G c ↦ by rw [eval_map, Polynomial.eval₂_at_apply]
  have hroot : ∀ k, (fibreAt S.F (0 : K)).eval (algebraMap C K (β k)) = 0 := fun k ↦ by
    rw [hfa, hevK, hfib, eval_prod, Finset.prod_eq_zero (Finset.mem_univ k) (by simp), map_zero]
  have hβK : Function.Injective fun k ↦ algebraMap C K (β k) :=
    (algebraMap C K).injective.comp hβ
  have hsimple : ∀ k, (fibreAt (derivative S.F) (0 : K)).eval (algebraMap C K (β k)) ≠ 0 := by
    intro k
    rw [hfa, hevK, ← Polynomial.derivative_map, hfib, derivative_prod_finset, eval_finsetSum,
      Finset.sum_eq_single k]
    · rw [eval_mul, derivative_sub, derivative_X, derivative_C, sub_zero, eval_one, mul_one,
        eval_prod]
      refine (map_ne_zero_iff _ (algebraMap C K).injective).mpr
        (Finset.prod_ne_zero_iff.mpr fun l hl ↦ ?_)
      rw [eval_sub, eval_X, eval_C, sub_ne_zero]
      exact fun h ↦ (Finset.mem_erase.mp hl).1 (hβ h).symm
    · intro j _ hjk
      rw [eval_mul, eval_prod, Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hjk,
        Finset.mem_univ k⟩) (by simp), zero_mul]
    · intro h; exact absurd (Finset.mem_univ k) h
  obtain ⟨Y, hY, hsplit⟩ := split_unramified S.F S.monic (0 : K)
    (fun k ↦ algebraMap C K (β k)) hβK hroot hsimple
  set l := List.ofFn fun k ↦ ofPowerSeries ℤ K (Y k) with hldef
  have hl : S.F.map (branchSub 1 (0 : K)) = (l.map fun r ↦ X - Polynomial.C r).prod :=
    S.list_split 0 Y hsplit
  have hYl : ∀ k, ofPowerSeries ℤ K (Y k) ∈ l := fun k ↦ List.mem_ofFn.mpr ⟨k, rfl⟩
  have hN0 : (0 : ℕ) < 1 := one_pos
  set φ : Fin S.F.natDegree → (C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K) := fun k ↦
    S.embG (branchSub 1 0) (branchSub_injective 1 one_pos 0) (ofPowerSeries ℤ K (Y k))
      (S.root_of_mem hl (hYl k)) with hφ
  set e : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯ := fun i ↦ S.lagE β i with he
  -- the values `δᵢₖ`
  have hval : ∀ i k, (φ k (e i)).coeff 0 = if i = k then 1 else 0 := by
    intro i k
    simp only [hφ, he, lagE]
    rw [S.coeff0_embG_evT, S.fibre_lagE, (hY k).2, hevK]
    split_ifs with hik
    · subst hik
      rw [Lagrange.eval_basis_self (Set.injOn_of_injective hβ) (Finset.mem_univ _), map_one]
    · rw [Lagrange.eval_basis_of_ne hik (Finset.mem_univ _), map_zero]
  have hlowe : ∀ i k, LowerBd (φ k (e i)) 0 := fun i k ↦
    lowerBd_of_order_nk ((S.regularFinite_evT (K := K) _) 0 1 one_ne_zero l hl _ (hYl k))
  -- the coordinates
  have hreg : ∀ i, S.RegularFinite K (e i) := fun i ↦ S.regularFinite_evT (K := K) _
  choose p hp using fun i ↦ hwB.2.1 (e i) (hreg i)
  have hpL : ∀ i, (e i : L) = ∑ k, aeval S.x (p i k) * (w k : L) := fun i ↦ by
    have := congrArg Subtype.val (hp i)
    simpa [CurveData.polyE] using this
  have hPL : ∀ k, (w k : L)′ * aeval S.x S0 = ∑ j, aeval S.x (P k j) * (w j : L) := fun k ↦ by
    have := congrArg Subtype.val (hP k)
    simpa [CurveData.polyE] using this
  set U : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C := Matrix.of fun i k ↦ (p i k).coeff 0 with hU
  have hwreg : ∀ k q, LowerBd (φ q (w k)) 0 := fun k q ↦
    lowerBd_of_order_nk (hwB.1 k 0 1 one_ne_zero l hl _ (hYl q))
  have hcomb : ∀ q (c : Fin S.F.natDegree → C[X]), (∀ k, (c k).coeff 0 = 0) →
      LowerBd (φ q (∑ k, S.polyE (c k) * w k)) 1 := fun q c hc ↦ by
    rw [map_sum]
    refine lowerBd_sum _ _ fun k _ ↦ ?_
    rw [map_mul, show φ q (S.polyE (c k)) = branchSub 1 0 (c k) from S.embG_polyX _ _ _ _ _ _]
    simpa using (lowerBd_branchSub_zero 1 one_pos (c k) (hc k)).mul (hwreg k q)
  have hφC : ∀ q (c : C), φ q (S.polyE (Polynomial.C c)) = HahnSeries.C (algebraMap C K c) :=
    fun q c ↦ by
      rw [show φ q (S.polyE (Polynomial.C c)) = branchSub 1 0 (Polynomial.C c) from
        S.embG_polyX _ _ _ _ _ _, branchSub_C'']
  -- `U` is invertible
  have hUind : ∀ v : Fin S.F.natDegree → C, Matrix.vecMul v U = 0 → v = 0 := by
    intro v hv
    funext q
    have hz := hcomb q (fun k ↦ ∑ i, Polynomial.C (v i) * p i k) fun k ↦ by
      rw [finsetSum_coeff]
      have := congrFun hv k
      simp only [Matrix.vecMul, dotProduct, hU, Matrix.of_apply, Pi.zero_apply] at this
      rw [← this]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [Polynomial.coeff_C_mul]
    have heq : (∑ k, S.polyE (∑ i, Polynomial.C (v i) * p i k) * w k) =
        ∑ i, S.polyE (Polynomial.C (v i)) * e i := by
      apply Subtype.ext
      simp only [CurveData.polyE, IntermediateField.coe_sum, IntermediateField.coe_mul, map_sum,
        map_mul, hpL, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    rw [heq, map_sum] at hz
    have hc := hz 0 one_pos
    rw [HahnSeries.coeff_sum, Finset.sum_eq_single q] at hc
    · rw [map_mul, hφC, LaurentSeries.coeff_C_mul, hval, if_pos rfl, mul_one] at hc
      exact (map_eq_zero_iff _ (algebraMap C K).injective).mp hc
    · intro i _ hiq
      rw [map_mul, hφC, LaurentSeries.coeff_C_mul, hval, if_neg hiq, mul_zero]
    · intro h; exact absurd (Finset.mem_univ q) h
  have hdet : U.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    exact hv0 (hUind v hv)
  have hUu : IsUnit U.det := isUnit_iff_ne_zero.mpr hdet
  set M0 : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C :=
    Matrix.of (fun i j ↦ (P i j).coeff 0 / S0.coeff 0) with hM0
  set Lam := (U.map (fun z ↦ z′) + U * M0) * U⁻¹ with hLam
  have hLU : Lam * U = U.map (fun z ↦ z′) + U * M0 := by
    rw [hLam, Matrix.mul_assoc, Matrix.nonsing_inv_mul U hUu, Matrix.mul_one]
  -- the residual polynomials
  set D : Fin S.F.natDegree → Fin S.F.natDegree → C[X] := fun i k ↦
    S0 * (mapCoeffs (p i k) + Polynomial.C b * X * derivative (p i k)) + ∑ l, p i l * P l k -
      ∑ l, Polynomial.C (Lam i l) * S0 * p l k with hD
  have hD0 : ∀ i k, (D i k).coeff 0 = 0 := by
    intro i k
    have h := congrFun (congrFun hLU i) k
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply, hU, hM0, Matrix.of_apply] at h
    simp only [hD, Polynomial.coeff_sub, Polynomial.coeff_add, mul_coeff_zero, finsetSum_coeff,
      coeff_mapCoeffs,
      coeff_C_zero, coeff_X_zero, mul_zero, zero_mul, add_zero]
    have e1 : ∑ l, Lam i l * S0.coeff 0 * (p l k).coeff 0 =
        S0.coeff 0 * ∑ l, Lam i l * (p l k).coeff 0 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ ↦ by ring
    rw [e1, h, mul_add, Finset.mul_sum]
    have e2 : ∀ l, S0.coeff 0 * ((p i l).coeff 0 * ((P l k).coeff 0 / S0.coeff 0)) =
        (p i l).coeff 0 * (P l k).coeff 0 := fun l ↦ by field_simp
    simp only [e2]
    ring
  have hDL : ∀ i, ((e i : L)′ - ∑ l, algebraMap C L (Lam i l) * (e l : L)) * aeval S.x S0 =
      ∑ k, aeval S.x (D i k) * (w k : L) := by
    intro i
    have h1 : (e i : L)′ * aeval S.x S0 = ∑ k, aeval S.x (S0 * (mapCoeffs (p i k) +
        Polynomial.C b * X * derivative (p i k))) * (w k : L) +
        ∑ k, aeval S.x (∑ l, p i l * P l k) * (w k : L) := by
      rw [hpL i, map_sum, Finset.sum_mul]
      have e1 : ∀ k, (aeval S.x (p i k) * (w k : L))′ * aeval S.x S0 =
          aeval S.x (S0 * (mapCoeffs (p i k) + Polynomial.C b * X * derivative (p i k))) * (w k : L) +
          aeval S.x (p i k) * ∑ j, aeval S.x (P k j) * (w j : L) := fun k ↦ by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, deriv_aeval_eq, hx, ← hPL k]
        simp only [map_mul, map_add, aeval_C, aeval_X]
        ring
      rw [Finset.sum_congr rfl fun k _ ↦ e1 k, Finset.sum_add_distrib]
      congr 1
      simp only [Finset.mul_sum, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_mul]; ring
    have h2 : (∑ l, algebraMap C L (Lam i l) * (e l : L)) * aeval S.x S0 =
        ∑ k, aeval S.x (∑ l, Polynomial.C (Lam i l) * S0 * p l k) * (w k : L) := by
      simp only [hpL, Finset.mul_sum, Finset.sum_mul, map_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
      simp only [map_mul, aeval_C]; ring
    rw [sub_mul, h1, h2, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [hD, map_sub, map_add]
    ring
  -- the key identity along each branch, at `T⁰`
  have hS0ne : S0 ≠ 0 := by rintro rfl; exact hS0 (coeff_zero 0)
  have hS0b : branchSub (K := K) 1 0 S0 ≠ 0 := branchSub_zero_ne_zero 1 one_pos S0 hS0ne
  have hS0o : (branchSub (K := K) 1 0 S0).order = 0 := by
    rw [order_branchSub_zero 1 one_pos S0 hS0ne, natTrailingDegree_eq_zero.mpr (Or.inr hS0)]
    simp
  have hkey : ∀ i q, ((φ q (e i)).coeff 0)′ =
      ∑ j, algebraMap C K (Lam i j) * (φ q (e j)).coeff 0 := by
    intro i q
    have hmem := S.derivClosedXYW' (Polynomial.C b * X) hx (e i) (e i).2
    set R : C⟮S.x⟯⟮S.y⟯ := ⟨(e i : L)′, hmem⟩ - ∑ l, S.polyE (Polynomial.C (Lam i l)) * e l with hR
    have hRe : R * S.polyE S0 = ∑ k, S.polyE (D i k) * w k := by
      apply Subtype.ext
      simp only [hR, CurveData.polyE, MulMemClass.coe_mul, AddSubgroupClass.coe_sub,
        AddSubmonoidClass.coe_finsetSum, aeval_C]
      exact hDL i
    have hRb : LowerBd (φ q R) 1 := by
      have h1 := hcomb q (D i) (hD0 i)
      rw [← hRe, map_mul, show φ q (S.polyE S0) = branchSub 1 0 S0 from S.embG_polyX _ _ _ _ _ _]
        at h1
      have e : φ q R = φ q R * branchSub (K := K) 1 0 S0 * (branchSub (K := K) 1 0 S0)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hS0b, mul_one]
      rw [e]
      simpa using h1.mul (lowerBd_inv_of_order_zero hS0b hS0o)
    have hd := S.embG_dSW' (Polynomial.C b * X) hx hK (zeroSpeedE b 1)
      (HahnSeries.C 0 + single ((1 : ℕ) : ℤ) 1) (dS_zeroSpeedE b 1 one_pos) (branchSub 1 0)
      (branchSub_injective 1 one_pos 0) (fun P ↦ by rw [SuperData.branchSub_eq_subst])
      (ofPowerSeries ℤ K (Y q)) (S.root_of_mem hl (hYl q)) (e i : L) (e i).2
    simp only [Subtype.coe_eta] at hd
    have hφR : φ q R = dS (zeroSpeedE b 1) (φ q (e i)) -
        ∑ l, HahnSeries.C (algebraMap C K (Lam i l)) * φ q (e l) := by
      rw [hR, map_sub, map_sum]
      simp only [map_mul, hφC]
      rw [show φ q ⟨(e i : L)′, hmem⟩ = dS (zeroSpeedE b 1) (φ q (e i)) from hd]
    have hc := hRb 0 one_pos
    rw [hφR, HahnSeries.coeff_sub, coeff_dS_zeroSpeedE, HahnSeries.coeff_sum, sub_eq_zero] at hc
    have e0 : ((0 : ℤ) : K) / ((1 : ℕ) : K) = 0 := by simp
    rw [e0, mul_zero, zero_mul, add_zero] at hc
    rw [hc]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [LaurentSeries.coeff_C_mul]
  -- `Λ = 0`
  have hLam0 : Lam = 0 := by
    ext i q
    have h := hkey i q
    rw [hval, Finset.sum_eq_single q] at h
    · rw [hval, if_pos rfl, mul_one] at h
      have h0 : ((if i = q then (1 : K) else 0))′ = 0 := by
        split_ifs
        · exact Derivation.map_one_eq_zero _
        · exact Derivation.map_zero _
      rw [h0] at h
      exact (map_eq_zero_iff _ (algebraMap C K).injective).mp h.symm
    · intro j _ hjq
      rw [hval, if_neg hjq, mul_zero]
    · intro h; exact absurd (Finset.mem_univ q) h
  exact ⟨U, U⁻¹, Matrix.mul_nonsing_inv U hUu, Matrix.nonsing_inv_mul U hUu, hLam0⟩

end Gauge0S

end CurveData

end Curves
