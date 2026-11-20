import RischTragerBronstein.Mixed.NKInf2Unit
import RischTragerBronstein.Torsion.PicTorsion2

/-!
# Units of a curve split at infinity

For any curve `S` over `C` (no constancy assumption, e.g. a curve over `Fₘ(t)` with coefficients
depending on lower levels) and a complete branch system above infinity `l` (`n` roots), units
at the finite places have order sum `0` along `l` (`unit_sum_inf`: the norm of a unit is a
constant), and a function regular at the finite places with non-negative orders along `l` is
algebraic over `C` (`algebraic_of_regular_l`). Hence, when `n − 1` units are multiplicatively
independent modulo constants, every unit is, up to a power, a constant times a power product of
them (`mem_pow_units_inf`) — no description of the places at infinity is needed: the order
vectors of units lie in the hyperplane `∑ = 0` of `ℚⁿ`, and independent units span it.
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential GTors CPoly Sup

section UnitsInf

variable {C L Kb : Type*} [Field C] [Field L] [Algebra C L] [Field Kb] [Algebra C Kb]
  [IsAlgClosed Kb] [CharZero Kb]

namespace CurveData

variable (S : CurveData C L)

/-- **A function without finite poles and with non-negative orders along one branch system
above infinity is algebraic over the constants.** -/
theorem algebraic_of_regular_l (f : C⟮S.x⟯⟮S.y⟯) (hfin : S.RegularFinite Kb f) (N : ℕ)
    (hN : 0 < N) (l : List (LaurentSeries Kb))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (hinf : ∀ r (hr : r ∈ l),
      0 ≤ (S.embG (infSub N) (infSub_injective N hN) r (S.root_of_mem hl hr) f).order) :
    ∃ M0 : C[X], M0.Monic ∧ aeval (f : L) M0 = 0 := by
  classical
  obtain ⟨W, Q, M, hQ, hWQ, hM, hPM, hev⟩ := S.integral_of_regular_dataG S.hasBranches f hfin
  have hinj := infSub_injective (C := C) (K := Kb) N hN
  obtain ⟨v, hv, hMg⟩ := S.M_map_split f W Q M hQ hWQ hPM (infSub (K := Kb) N) hinj l hl
  have hconst : ∀ j, (M.coeff j).natDegree = 0 := by
    intro j
    by_cases h0 : M.coeff j = 0
    · rw [h0, natDegree_zero]
    have hord : 0 ≤ (infSub (K := Kb) N (M.coeff j)).order := by
      have := congrArg (fun P ↦ P.coeff j) hMg
      simp only [coeff_map] at this
      rw [this, show (l.map fun r ↦ (X - Polynomial.C (v r) : (LaurentSeries Kb)[X])) =
        ((l.map v).map fun s ↦ X - Polynomial.C s) by rw [List.map_map]; rfl]
      refine order_coeff_prod_nonneg (K := Kb) _ (fun s hs ↦ ?_) j
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
      rw [hv r hr]
      exact hinf r hr
    rw [order_infSub N hN _ h0] at hord
    have h1 : ((N * (M.coeff j).natDegree : ℕ) : ℤ) ≤ 0 := by push_cast; linarith
    have h2 : N * (M.coeff j).natDegree = 0 := by omega
    exact (mul_eq_zero.mp h2).resolve_left hN.ne'
  refine ⟨M.map Polynomial.constantCoeff, hM.map _, ?_⟩
  have hMC : M = (M.map Polynomial.constantCoeff).map Polynomial.C := by
    refine Polynomial.ext fun j ↦ ?_
    rw [coeff_map, coeff_map, Polynomial.constantCoeff_apply]
    exact eq_C_of_natDegree_eq_zero (hconst j)
  rw [hMC, Polynomial.map_map] at hev
  rw [aeval_def, ← eval_map]
  convert hev using 2
  ext c
  simp

/-- **Units have order sum `0` above infinity** (their norm is a constant). -/
theorem unit_sum_inf (z : C⟮S.x⟯⟮S.y⟯) (hz : z ≠ 0)
    (hfin : ∀ (a : Kb) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) z).order = 0)
    (N : ℕ) (hN : 0 < N) (l : List (LaurentSeries Kb))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) :
    (l.attach.map fun r ↦ (S.embG (infSub N) (infSub_injective N hN) r.1
      (S.root_of_mem hl r.2) z).order).sum = 0 := by
  classical
  have hF1 : S.F ≠ 1 := fun h ↦ S.natDegree_F_ne_zero (by rw [h, natDegree_one])
  obtain ⟨W, Q, hQ, hWQ, hWn⟩ := S.exists_repr_lt z hF1
  have hWm : W.natDegree ≤ S.F.natDegree := hWn.le
  have hW : S.evXY W ≠ 0 := by
    rw [← hWQ]; exact mul_ne_zero (fun h ↦ hz (Subtype.ext h)) (fun h ↦ S.htr ⟨Q, hQ, h⟩)
  -- the norm has the degree of `Qⁿ`
  have hmu : ∀ b : Kb, S.muW W S.F.natDegree Q b = 0 := by
    intro b
    obtain ⟨Nb, hNb, lb, hlb⟩ := S.hasBranches_list S.hasBranches b
    have hs := S.fibre_sum z hz W Q hQ hWQ S.F.natDegree hWm Nb hNb b lb hlb
    rw [List.sum_eq_zero fun x hx ↦ ?_] at hs
    · have : (Nb : ℤ) ≠ 0 := by exact_mod_cast hNb.ne'
      exact (mul_eq_zero.mp hs.symm).resolve_left this
    · obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
      exact hfin b Nb hNb.ne' lb hlb r.1 r.2
  have hnorm0 := S.normW_ne_zero W S.F.natDegree hWm hW _ (infSub_injective N hN) l hl
  have hdeg : (S.normW W S.F.natDegree).natDegree = S.F.natDegree * Q.natDegree := by
    have hroots : ((S.normW W S.F.natDegree).map (algebraMap C Kb)).roots =
        S.F.natDegree • (Q.map (algebraMap C Kb)).roots := by
      ext b
      rw [Multiset.count_nsmul, count_roots, count_roots]
      have := hmu b
      simp only [CurveData.muW] at this
      omega
    rw [← natDegree_map_eq_of_injective (algebraMap C Kb).injective,
      ← natDegree_map_eq_of_injective (algebraMap C Kb).injective Q,
      ← IsAlgClosed.card_roots_eq_natDegree, ← IsAlgClosed.card_roots_eq_natDegree, hroots,
      Multiset.card_nsmul]
  have hsum := S.sum_order_inf W S.F.natDegree hWm hW N hN l hl
  have hQb : infSub (K := Kb) N Q ≠ 0 := (map_ne_zero_iff _ (infSub_injective N hN)).mpr hQ
  have hrel : ∀ (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (infSub N) (infSub_injective N hN) r (S.root_of_mem hl hr) z).order =
        ((W.map (infSub N)).eval r).order + N * Q.natDegree := by
    intro r hr
    have e := congrArg (S.embG (infSub N) (infSub_injective N hN) r (S.root_of_mem hl hr))
      (show z * ⟨aeval S.x Q, S.aeval_mem Q⟩ = ⟨S.evXY W, S.evXY_mem W⟩ from Subtype.ext hWQ)
    rw [map_mul, S.embG_polyX, S.embG_wE_eq (RingHom.id C) W] at e
    have hz0 : S.embG (infSub N) (infSub_injective N hN) r (S.root_of_mem hl hr) z ≠ 0 :=
      (map_ne_zero_iff _ (RingHom.injective _)).mpr hz
    have := congrArg HahnSeries.order e
    rw [HahnSeries.order_mul hz0 hQb, order_infSub N hN _ hQ] at this
    push_cast at this
    linarith
  rw [List.map_congr_left fun r _ ↦ hrel r.1 r.2]
  rw [List.attach_map_val (f := fun r ↦ ((W.map (infSub N)).eval r).order + N * Q.natDegree),
    List.sum_map_add, hsum, List.map_const', List.sum_replicate, S.length_of_split hl, hdeg]
  push_cast
  ring

set_option maxHeartbeats 8000000 in
/-- **Units are power products of `n − 1` given independent units** (a curve whose branch system
above infinity has `n = m + 1` roots): every unit `w` satisfies `w^N = c ∏ uᵢ^{aᵢ}`, `N ≠ 0`. -/
theorem mem_pow_units_inf [CharZero C] (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C Kb))))
    (N : ℕ) (hN : 0 < N) (l : List (LaurentSeries Kb))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    {m : ℕ} (hlen : S.F.natDegree = m + 1)
    (u : Fin m → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i, u i ≠ 0)
    (hfinu : ∀ i (a : Kb) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (u i)).order = 0)
    (hind : ∀ a : Fin m → ℤ, (∃ c : C, ∏ i, (u i : L) ^ a i = algebraMap C L c) → a = 0)
    (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0)
    (hfin : ∀ (a : Kb) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) w).order = 0) :
    ∃ (N' : ℤ) (a : Fin m → ℤ), N' ≠ 0 ∧ ∃ c : C,
      (w : L) ^ N' = algebraMap C L c * ∏ i, (u i : L) ^ a i := by
  classical
  have hlenl : l.length = m + 1 := by rw [S.length_of_split hl, hlen]
  set ρ : Fin (m + 1) → LaurentSeries Kb := fun p ↦ l.get ⟨p, by rw [hlenl]; exact p.2⟩ with hρ
  have hρl : ∀ p, ρ p ∈ l := fun p ↦ List.get_mem _ _
  set φ : Fin (m + 1) → (C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries Kb) := fun p ↦
    S.embG (infSub N) (infSub_injective N hN) (ρ p) (S.root_of_mem hl (hρl p)) with hφ
  -- orders of power products
  have hordp : ∀ (g : C[X] →+* LaurentSeries Kb) (hg : Function.Injective g) (Y : LaurentSeries Kb)
      (hY : (S.F.map g).eval Y = 0) (e0 : ℤ) (e : Fin m → ℤ),
      (S.embG g hg Y hY (w ^ e0 * ∏ i, u i ^ e i)).order =
        e0 * (S.embG g hg Y hY w).order + ∑ i, e i * (S.embG g hg Y hY (u i)).order := by
    intro g hg Y hY e0 e
    have hw' : S.embG g hg Y hY w ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hw
    obtain ⟨hp0, hpo⟩ := order_prod_zpow_nk Finset.univ (fun i ↦ S.embG g hg Y hY (u i))
      (fun i _ ↦ (map_ne_zero_iff _ (RingHom.injective _)).mpr (hu i)) e
    rw [map_mul, map_zpow₀, map_prod]
    simp only [map_zpow₀]
    rw [HahnSeries.order_mul (zpow_ne_zero _ hw') hp0, order_zpow_ls _ hw', hpo]
  have hprod_ne : ∀ (e0 : ℤ) (e : Fin m → ℤ), w ^ e0 * ∏ i, u i ^ e i ≠ 0 := fun e0 e ↦
    mul_ne_zero (zpow_ne_zero _ hw) (Finset.prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ (hu i))
  -- a power product with vanishing orders at the roots `0, …, m − 1` is a constant
  have hkey : ∀ (e0 : ℤ) (e : Fin m → ℤ),
      (∀ p : Fin m, e0 * (φ p.castSucc w).order + ∑ i, e i * (φ p.castSucc (u i)).order = 0) →
      ∃ c : C, ((w ^ e0 * ∏ i, u i ^ e i : C⟮S.x⟯⟮S.y⟯) : L) = algebraMap C L c := by
    intro e0 e hzero
    set y := w ^ e0 * ∏ i, u i ^ e i with hy
    have hy1 : ∀ (a : Kb) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
        (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries Kb) (hr : r ∈ l), (S.embG (branchSub N a)
          (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r (S.root_of_mem hl hr) y).order = 0 :=
      fun a N hN l hl r hr ↦ by
        rw [hy, hordp, hfin a N hN l hl r hr, Finset.sum_eq_zero fun i _ ↦ by
          rw [hfinu i a N hN l hl r hr, mul_zero]]; ring
    have hsum := S.unit_sum_inf y (hprod_ne e0 e) hy1 N hN l hl
    rw [sum_attach_eq_fin l (fun r hr ↦ (S.embG (infSub N) (infSub_injective N hN) r
      (S.root_of_mem hl hr) y).order)] at hsum
    have hall : ∀ p : Fin (m + 1), (φ p y).order = 0 := by
      have hlow : ∀ p : Fin m, (φ p.castSucc y).order = 0 := fun p ↦ by
        rw [hy, hφ]; dsimp only; rw [hordp]; exact hzero p
      have e1 : ∑ i : Fin l.length, (S.embG (infSub N) (infSub_injective N hN) (l.get i)
          (S.root_of_mem hl (List.get_mem l i)) y).order = ∑ p : Fin (m + 1), (φ p y).order :=
        Fintype.sum_equiv (finCongr hlenl) _ _ fun i ↦ rfl
      rw [e1, Fin.sum_univ_castSucc, Finset.sum_eq_zero fun p _ ↦ hlow p, zero_add] at hsum
      intro p
      refine Fin.lastCases ?_ (fun p ↦ hlow p) p
      exact hsum
    have hreg : S.RegularFinite Kb y := fun a N hN l hl r hr ↦ (hy1 a N hN l hl r hr).ge
    obtain ⟨M0, hM0, hyM⟩ := S.algebraic_of_regular_l y hreg N hN l hl fun r hr ↦ by
      obtain ⟨⟨p, hp⟩, rfl⟩ := List.get_of_mem hr
      have := hall ⟨p, by rw [← hlenl]; exact hp⟩
      exact this.ge
    exact S.mem_const_of_alg_geo hgeo y M0 hM0 hyM
  -- the order matrix of the units at the roots `0, …, m − 1`
  set A : Matrix (Fin m) (Fin m) ℤ := fun i p ↦ (φ p.castSucc (u i)).order with hA
  set b : Fin m → ℤ := fun p ↦ (φ p.castSucc w).order with hb
  have hcoe : ∀ (e0 : ℤ) (e : Fin m → ℤ), ((w ^ e0 * ∏ i, u i ^ e i : C⟮S.x⟯⟮S.y⟯) : L) =
      (w : L) ^ e0 * ∏ i, (u i : L) ^ e i := fun e0 e ↦ by
    rw [IntermediateField.coe_mul, show ((w ^ e0 : C⟮S.x⟯⟮S.y⟯) : L) = (w : L) ^ e0 from
      map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val w e0, IntermediateField.coe_prod]
    congr 1
  by_cases hdet : A.det = 0
  · -- the units would be dependent
    exfalso
    obtain ⟨a, ha0, hAa⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
      (show A.transpose.det = 0 by rw [Matrix.det_transpose]; exact hdet)
    obtain ⟨c, hc⟩ := hkey 0 a fun p ↦ by
      have := congrFun hAa p
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hA, Pi.zero_apply] at this
      rw [zero_mul, zero_add]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    apply ha0
    apply hind a
    refine ⟨c, ?_⟩
    rw [← hc, hcoe, zpow_zero, one_mul]
  · -- Cramer: `A.transpose (adj A.transpose b) = det A • b`
    set a : Fin m → ℤ := Matrix.mulVec (A.transpose).adjugate b with ha
    have hAa : Matrix.mulVec A.transpose a = A.det • b := by
      rw [ha, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.det_transpose, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    obtain ⟨c, hc⟩ := hkey A.det (fun i ↦ -a i) fun p ↦ by
      have := congrFun hAa p
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hA, Pi.smul_apply,
        smul_eq_mul] at this
      have e : ∑ i, -a i * (φ p.castSucc (u i)).order = -(A.det * b p) := by
        rw [← this, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [neg_mul, mul_comm (a i)]; rfl
      rw [e, hb]; ring
    refine ⟨A.det, a, hdet, c, ?_⟩
    rw [hcoe] at hc
    have hprodne : ∏ i, (u i : L) ^ a i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦
      zpow_ne_zero _ (fun h ↦ hu i (Subtype.ext h))
    have e2 : ∏ i, (u i : L) ^ (-a i) = (∏ i, (u i : L) ^ a i)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun i _ ↦ zpow_neg _ _
    rw [e2] at hc
    rw [← hc, mul_assoc, inv_mul_cancel₀ hprodne, mul_one]


/-- **Every unit is a power product of the `u i`**: a function without zeros or poles at the finite
places is, up to a non-zero power, a constant times a power product of the `u i`. -/
def UnitsSpan (Kb : Type*) [Field Kb] [Algebra C Kb] {m : ℕ} (u : Fin m → C⟮S.x⟯⟮S.y⟯) : Prop :=
  ∀ w : C⟮S.x⟯⟮S.y⟯, w ≠ 0 →
    (∀ (a : Kb) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) w).order = 0) →
    ∃ (N' : ℤ) (a : Fin m → ℤ), N' ≠ 0 ∧ ∃ c : C,
      (w : L) ^ N' = algebraMap C L c * ∏ i, (u i : L) ^ a i

/-- `n − 1` independent units span the units (`mem_pow_units_inf`). -/
lemma unitsSpan_inf [CharZero C] (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C Kb))))
    (N : ℕ) (hN : 0 < N) (l : List (LaurentSeries Kb))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    {m : ℕ} (hlen : S.F.natDegree = m + 1)
    (u : Fin m → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i, u i ≠ 0)
    (hfinu : ∀ i (a : Kb) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (u i)).order = 0)
    (hind : ∀ a : Fin m → ℤ, (∃ c : C, ∏ i, (u i : L) ^ a i = algebraMap C L c) → a = 0) :
    S.UnitsSpan Kb u := fun w hw hfin ↦
  S.mem_pow_units_inf hgeo N hN l hl hlen u hu hfinu hind w hw hfin

end CurveData

end UnitsInf

end Curves
