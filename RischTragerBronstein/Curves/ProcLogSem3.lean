import RischTragerBronstein.Curves.ProcLogSem2

/-!
# The numerator of the logarithmic remainder

For `u = W(x, y)/Q(x)`: `logNumW (x, y) = (u′/u) · W Q F_Y` (`evXY_logNumW`), and
`logNum (x, y) = (f − v′ − ∑ c_j u_j′/u_j) · R0² F_Y ∏ W_j Q_j` (`evXY_logNum`).
-/

open Polynomial IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential

section Lists

lemma prod_finRange_map {M : Type*} [CommMonoid M] {d : ℕ} (g : Fin d → M) :
    ((List.finRange d).map g).prod = ∏ i, g i := by
  rw [← List.prod_toFinset _ (List.nodup_finRange d)]
  congr 1
  ext i; simp

lemma sum_finRange_map {M : Type*} [AddCommMonoid M] {d : ℕ} (g : Fin d → M) :
    ((List.finRange d).map g).sum = ∑ i, g i := by
  rw [← List.sum_toFinset _ (List.nodup_finRange d)]
  congr 1
  ext i; simp

lemma prod_filter_ne_map {M : Type*} [CommMonoid M] {d : ℕ} (g : Fin d → M) (j : Fin d) :
    (((List.finRange d).filter fun i ↦ decide (i ≠ j)).map g).prod =
      ∏ i ∈ Finset.univ.erase j, g i := by
  rw [← List.prod_toFinset _ ((List.nodup_finRange d).filter _)]
  congr 1
  ext i; simp [and_comm]

end Lists

section Curve

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]

namespace CurveData

variable (S : CurveData C L)

/-- The logarithm witness `u = W(x, y)/Q(x)`. -/
noncomputable def uE (ψ₀ : F →+* C) (w : LogWit F) : C⟮S.x⟯⟮S.y⟯ :=
  S.wE ψ₀ w.W / S.qE ψ₀ w.Q

variable {P : CurveProb F} {ψ₀ : F →+* C}

lemma evXY_wqB (w : LogWit F) :
    S.evXY ((toB (CurveProb.wqB w)).map (mapRingHom ψ₀)) =
      (S.wE ψ₀ w.W : L) * (S.qE ψ₀ w.Q : L) := by
  rw [CurveProb.wqB, toB_smulB, Polynomial.map_mul, Polynomial.map_C, S.evXY_mul, S.evXY_C]
  simp only [coe_mapRingHom]
  rw [mul_comm]; rfl

/-- **The logarithmic derivative numerator.** -/
theorem evXY_logNumW (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (w : LogWit F)
    (hW : (S.wE ψ₀ w.W : L) ≠ 0) (hQ : (S.qE ψ₀ w.Q : L) ≠ 0) :
    S.evXY ((toB (P.logNumW w)).map (mapRingHom ψ₀)) =
      (S.uE ψ₀ w : L)′ / (S.uE ψ₀ w : L) *
        ((S.wE ψ₀ w.W : L) * (S.qE ψ₀ w.Q : L) * S.evXY (derivative S.F)) := by
  have hFY0 : S.evXY (derivative S.F) ≠ 0 := S.evXY_derivative_ne_zero
  have hW' : (S.evXY ((toB w.W).map (mapRingHom ψ₀)))′ * S.evXY (derivative S.F) =
      S.evXY (dX ((toB w.W).map (mapRingHom ψ₀))) * S.evXY (derivative S.F) -
        S.evXY (derivative ((toB w.W).map (mapRingHom ψ₀))) * S.evXY (dX S.F) := by
    rw [S.deriv_evXY hC hx, S.deriv_y hC hx]
    field_simp
    ring
  have hQ' : (aeval S.x ((toPoly w.Q).map ψ₀))′ = aeval S.x (derivative ((toPoly w.Q).map ψ₀)) :=
    deriv_aeval_x S.x hC hx _
  have hL : S.evXY ((toB (P.logNumW w)).map (mapRingHom ψ₀)) =
      aeval S.x ((toPoly w.Q).map ψ₀) *
          (S.evXY (dX ((toB w.W).map (mapRingHom ψ₀))) * S.evXY (derivative S.F) -
            S.evXY (derivative ((toB w.W).map (mapRingHom ψ₀))) * S.evXY (dX S.F)) -
        aeval S.x (derivative ((toPoly w.Q).map ψ₀)) * S.evXY ((toB w.W).map (mapRingHom ψ₀)) *
          S.evXY (derivative S.F) := by
    have hm1 : S.evXY (-1) = -1 := by simp [evXY]
    rw [CurveProb.logNumW, hSF]
    simp only [hm1, toB_addB, toB_smulB, toB_mulB, toB_dXB, toB_derivYB, toPoly_deriv, toPoly_single,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ← derivative_map, ← dX_map,
      S.evXY_add, S.evXY_mul, S.evXY_C, coe_mapRingHom, map_neg, map_one, Polynomial.map_neg,
      Polynomial.map_one, derivative_map]
    ring
  rw [hL]
  simp only [uE, wE, qE, IntermediateField.coe_div] at hW hQ ⊢
  set Wv := S.evXY ((toB w.W).map (mapRingHom ψ₀)) with hWv
  set Qv := aeval S.x ((toPoly w.Q).map ψ₀) with hQv
  set u := Wv / Qv with hudef
  have hu : u * Qv = Wv := div_mul_cancel₀ _ hQ
  have hu0 : u ≠ 0 := div_ne_zero hW hQ
  have hder : u′ * Qv + u * aeval S.x (derivative ((toPoly w.Q).map ψ₀)) = Wv′ := by
    rw [← hu, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hQ']; ring
  rw [div_mul_eq_mul_div, eq_div_iff hu0]
  linear_combination (-(u * Qv * S.evXY (derivative S.F))) * hder + (-(u * Qv)) * hW' +
    (u * aeval S.x (derivative ((toPoly w.Q).map ψ₀)) * S.evXY (derivative S.F) +
      u′ * Qv * S.evXY (derivative S.F)) * hu

/-- `Q ↦ Q(x, y)` as a ring homomorphism on `F[X][X]`. -/
noncomputable def evHom (ψ₀ : F →+* C) : F[X][X] →+* L :=
  (Polynomial.eval₂RingHom (aeval S.x).toRingHom S.y).comp (mapRingHom (mapRingHom ψ₀))

omit [CharZero F] [EllQuad.QCoords F] [DecidableEq F] [CharZero C] [CharZero L] [Differential C]
  [Differential L] [DifferentialAlgebra C L] in
lemma evHom_apply (ψ₀ : F →+* C) (Q : F[X][X]) :
    S.evHom ψ₀ Q = S.evXY (Q.map (mapRingHom ψ₀)) := by
  simp [evHom, evXY, eval_map]

omit [CharZero F] [EllQuad.QCoords F] [DecidableEq F] [CharZero C] [CharZero L] [Differential C]
  [Differential L] [DifferentialAlgebra C L] in
lemma evHom_CC (ψ₀ : F →+* C) (c : F) :
    S.evHom ψ₀ (Polynomial.C (Polynomial.C c)) = algebraMap C L (ψ₀ c) := by
  simp [evHom]

omit [CharZero F] [EllQuad.QCoords F] [DecidableEq F] [CharZero C] [CharZero L] [Differential C]
  [Differential L] [DifferentialAlgebra C L] in
lemma evHom_C (ψ₀ : F →+* C) (q : F[X]) :
    S.evHom ψ₀ (Polynomial.C q) = aeval S.x (q.map ψ₀) := by
  simp [evHom]

/-- The exact part `v = ∑ c_b b` from a solution `cs`. -/
noncomputable def vvE (P : CurveProb F) (ψ₀ : F →+* C) (cs : List F) : C⟮S.x⟯⟮S.y⟯ :=
  ∑ b ∈ Finset.range P.basisIdx.length,
    S.cst (ψ₀ (cs.getD b 0)) * S.bE P ψ₀ (P.basisIdx.getD b (0, 0))

lemma vvE_spec (hV : P.ValidFacts) (cs : List F) :
    (S.vvE P ψ₀ cs : L) * aeval S.x ((toPoly P.R0).map ψ₀) =
      S.evXY ((toB (P.Wsol cs)).map (mapRingHom ψ₀)) := by
  rw [toB_Wsol, Polynomial.map_sum, S.evXY_sum, vvE, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [MulMemClass.coe_mul, mul_assoc, S.bE_spec P ψ₀ hV, Polynomial.map_mul, Polynomial.map_C,
    coe_mapRingHom, Polynomial.map_C, S.evXY_C_mul]
  rfl

/-- **The numerator of the logarithmic remainder.** -/
theorem evXY_logNum (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) (cs : List F)
    (ws : List (LogWit F))
    (hW : ∀ j : Fin (dim F), (S.wE ψ₀ (CurveProb.witAt ws j).W : L) ≠ 0)
    (hQ : ∀ j : Fin (dim F), (S.qE ψ₀ (CurveProb.witAt ws j).Q : L) ≠ 0) :
    S.evXY ((toB (P.logNum cs ws)).map (mapRingHom ψ₀)) =
      ((S.fE P ψ₀ : L) - (S.vvE P ψ₀ cs : L)′ -
        ∑ j : Fin (dim F), algebraMap C L (ψ₀ (CurveProb.cLog (CurveProb.witAt ws j) j)) *
          ((S.uE ψ₀ (CurveProb.witAt ws j) : L)′ / (S.uE ψ₀ (CurveProb.witAt ws j) : L))) *
        aeval S.x ((toPoly P.R0).map ψ₀) ^ 2 * S.evXY (derivative S.F) *
        ∏ j : Fin (dim F),
          ((S.wE ψ₀ (CurveProb.witAt ws j).W : L) * (S.qE ψ₀ (CurveProb.witAt ws j).Q : L)) := by
  classical
  set a : Fin (dim F) → L := fun j ↦
    (S.wE ψ₀ (CurveProb.witAt ws j).W : L) * (S.qE ψ₀ (CurveProb.witAt ws j).Q : L) with ha
  set ℓ : Fin (dim F) → L := fun j ↦
    (S.uE ψ₀ (CurveProb.witAt ws j) : L)′ / (S.uE ψ₀ (CurveProb.witAt ws j) : L) with hℓ
  set FY := S.evXY (derivative S.F) with hFY
  have hPg := S.evXY_Pg hC hx hSF hV (P.Wsol cs) _ (S.vvE_spec hV cs)
  have hwq : ∀ j : Fin (dim F), S.evHom ψ₀ (toB (CurveProb.wqB (CurveProb.witAt ws j))) = a j :=
    fun j ↦ by rw [evHom_apply, S.evXY_wqB]
  have hln : ∀ j : Fin (dim F), S.evHom ψ₀ (toB (P.logNumW (CurveProb.witAt ws j))) =
      ℓ j * (a j * FY) := fun j ↦ by
    rw [evHom_apply, S.evXY_logNumW hC hx hSF _ (hW j) (hQ j)]
  have hPg' : S.evHom ψ₀ (toB (P.Pg (P.Wsol cs))) = ((S.fE P ψ₀ : L) - (S.vvE P ψ₀ cs : L)′) *
      aeval S.x ((toPoly P.R0).map ψ₀) ^ 2 * FY := by rw [evHom_apply, hPg]
  rw [← evHom_apply, CurveProb.logNum]
  simp only [toB_addB, toB_mulB, toB_smulB, toB_prodB, toB_sumB, List.map_map, Function.comp_def,
    toPoly_single, toPoly_mul, prod_finRange_map, sum_finRange_map, prod_filter_ne_map, map_add,
    map_mul, map_sum, map_prod, hwq, hln, hPg', evHom_CC, evHom_C, Polynomial.map_mul]
  simp only [Polynomial.map_C, aeval_C, Polynomial.map_neg, Polynomial.map_one, map_neg, map_one]
  have hfac : ∀ j : Fin (dim F), algebraMap C L (ψ₀ (CurveProb.cLog (CurveProb.witAt ws j) j)) *
      (ℓ j * (a j * FY) * ∏ i ∈ Finset.univ.erase j, a i) =
      algebraMap C L (ψ₀ (CurveProb.cLog (CurveProb.witAt ws j) j)) * ℓ j * FY * ∏ i, a i :=
    fun j ↦ by
      rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ j)]; ring
  simp only [hfac, ← Finset.sum_mul, map_neg, map_one]
  ring

end CurveData

end Curve

end Curves
