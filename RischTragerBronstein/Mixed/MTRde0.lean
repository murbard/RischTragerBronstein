import RischTragerBronstein.Mixed.MTLimE
import RischTragerBronstein.Mixed.MTRdeP

/-!
# Mixed towers over a curve: the base level

At level `0` (the function field `Cc(x, y)` of the curve):

* `const_rat`: a constant value of a curve code is rational (through the relation finder);
* `paramLim0C_spec`: parametric limited integration is `curveRde` with `h = 0`;
* `prde0C_spec`: the parametric Risch equation for `f = h′ + ∑ cⱼ wⱼ′ / wⱼ` (constant `cⱼ`) is
  `curveRdeL`, the constants `cⱼ` read off as rationals by `ratValC`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

/-- The coefficient vectors of an output list all have length `n`: past `n` they vanish. -/
lemma getD_fst_ge {α : Type*} (out : List (List ℚ × α)) (d : α) (n : ℕ)
    (hl : ∀ r ∈ out, r.1.length = n) (k i : ℕ) (hi : n ≤ i) :
    (out.getD k ([], d)).1.getD i 0 = 0 := by
  by_cases hk : k < out.length
  · rw [List.getD_eq_getElem _ _ hk]
    rw [List.getD_eq_default _ _ (by rw [hl _ (List.getElem_mem hk)]; exact hi)]
  · rw [List.getD_eq_default out _ (not_lt.mp hk)]
    simp

lemma curveRdeG_length (Fc : BPoly ℚ) (fc : GPoly (GFrac ℚ)) (den : CPoly ℚ) (Eb : ℕ)
    (ws : List (GPoly (GFrac ℚ))) : ∀ r ∈ curveRdeG Fc fc den Eb ws, r.1.length = ws.length := by
  intro r hr
  obtain ⟨u, -, rfl⟩ := List.mem_map.mp hr
  simp [rdeOutG]

lemma curveRde_length (Fc : BPoly ℚ) (h : GPoly (GFrac ℚ)) (ws : List (GPoly (GFrac ℚ))) :
    ∀ r ∈ curveRde Fc h ws, r.1.length = ws.length := by
  intro r hr
  obtain ⟨u, -, rfl⟩ := List.mem_map.mp hr
  simp [rdeOut]

namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]
variable (T : MTower Fc ks Cc L)

/-- **A constant value of a code is rational.** -/
theorem const_rat (m : ℕ) (h : T.Tr m) (c : LC m) (hc : ((T.MP m h).sem c)′ = 0) :
    ∃ q : ℚ, (T.MP m h).sem c = (q : T.F m) := by
  classical
  obtain ⟨κ, hκ⟩ := T.const_F _ hc
  set vs : List (LC m) := [c, (MO Fc ks m).one] with hvs
  have hrel : (List.zipWith (fun c v ↦ algebraMap Cc (T.F m) c * (T.MP m h).sem v)
      [(1 : Cc), -κ] vs).sum = 0 := by
    simp only [hvs, List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_cons, List.sum_nil,
      (T.MP m h).sem_one, hκ, map_one, map_neg]
    ring
  obtain ⟨u, hu, hu0⟩ := T.exists_coeff0_ne m h vs _ rfl hrel (by simp)
  have hs := T.mrel_sound m h vs u hu
  simp only [hvs, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append,
    List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_cons, List.sum_nil,
    (T.MP m h).sem_one, mul_one, add_zero] at hs
  refine ⟨-(u.getD 1 0) / u.getD 0 0, ?_⟩
  have hu0' : ((u.getD 0 0 : ℚ) : T.F m) ≠ 0 := by exact_mod_cast hu0
  rw [algebraMap_ratCast, algebraMap_ratCast] at hs
  push_cast
  field_simp
  linear_combination hs

/-- `ratValC` reads off a constant value. -/
theorem ratValC_of_const (m : ℕ) (h : T.Tr m) (c : LC m) (hc : ((T.MP m h).sem c)′ = 0) :
    (T.MP m h).sem c = (((ratValC Fc ks m c).getD 0 : ℚ) : T.F m) := by
  obtain ⟨q, hq⟩ := T.const_rat m h c hc
  rw [T.ratVal_spec m h c q hq, Option.getD_some, hq]

variable (lv : (m : ℕ) → LC m)

lemma paramLimC_zero : paramLimC Fc ks lv 0 = curveRde Fc (curveOps Fc).zero := by
  funext W
  rfl

lemma prdeC_zero (fr : FRep (LC 0)) :
    prdeC Fc ks lv 0 fr = curveRdeL Fc fr.h (logsQ Fc ks fr.logs) := by
  funext W
  rfl

/-- **Parametric limited integration on the curve.** -/
theorem paramLim0C_spec (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (h : T.Tr 0) : LimSpec (algebraMap Cc (T.F 0)) (T.MP 0 h) (paramLimC Fc ks lv 0) := by
  set M := cM T.hC T.S T.hx Fc T.hSF with hM
  rw [paramLimC_zero]
  refine ⟨fun W r hr ↦ ?_, fun W c hc z hz ↦ ?_⟩
  · have hs := curveRde_sound T.hC T.S T.hx Fc T.hSF (curveOps Fc).zero W r hr
    rw [M.sem_zero, Derivation.map_zero, zero_mul, add_zero] at hs
    apply Subtype.ext
    rw [coe_deriv, T.sem_MP, sQ, AddSubmonoidClass.coe_finsetSum]
    refine hs.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [IntermediateField.coe_mul, T.sem_MP, coe_ratCast]
    rfl
  · have hzE : (z : L)′ + (M.sem (curveOps Fc).zero)′ * (z : L) = ∑ j ∈ Finset.range W.length,
        algebraMap Cc L (c.getD j 0) * M.sem (W.getD j []) := by
      rw [M.sem_zero, Derivation.map_zero, zero_mul, add_zero, ← coe_deriv, hz, sC,
        AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [IntermediateField.coe_mul, T.sem_MP]
      rfl
    obtain ⟨β, hβ1, hβ2⟩ := curveRde_complete T.hC T.S T.hx Fc T.hSF hmon hdeg _ W c (z : L)
      z.2 hzE
    refine ⟨β, fun i ↦ ?_, ?_⟩
    · by_cases hi : i < W.length
      · rw [hβ1 i hi]
        rfl
      · rw [hc i (by omega)]
        symm
        refine Finset.sum_eq_zero fun k _ ↦ ?_
        have hz0 := getD_fst_ge (α := LC 0) (curveRde Fc (curveOps Fc).zero W) (MO Fc ks 0).zero
          W.length (curveRde_length Fc _ W) k i (by omega)
        rw [hz0, map_zero, mul_zero]
    · have key : ∀ y : T.F 0, (z : L) = (y : L) → (z - y)′ = 0 := fun y hy ↦ by
        rw [Subtype.ext hy, sub_self, map_zero]
      apply key
      rw [hβ2, AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [IntermediateField.coe_mul]
      rfl

/-- The logarithms kept by `logsQ` have non-zero values. -/
lemma logsQ_ne (h : T.Tr 0) (logs : List (LC 0 × LC 0)) :
    ∀ p ∈ logsQ Fc ks logs, (cM T.hC T.S T.hx Fc T.hSF).sem p.2 ≠ 0 := by
  intro p hp
  obtain ⟨cw, hcw, rfl⟩ := List.mem_map.mp hp
  have hnz := (List.mem_filter.mp hcw).2
  intro h0
  have : (MO Fc ks 0).isZero cw.2 = true := by
    rw [(T.MP 0 h).isZero_iff]
    apply Subtype.ext
    rw [T.sem_MP]
    exact h0
  rw [this] at hnz
  simp at hnz

/-- **The logarithmic part** as the sum over `logsQ`. -/
lemma logSumV_logsQ (h : T.Tr 0) : ∀ (logs : List (LC 0 × LC 0)),
    (∀ cw ∈ logs, ((T.MP 0 h).sem cw.1)′ = 0) →
    ((logSumV (T.MP 0 h) logs : T.F 0) : L) =
      ∑ i ∈ Finset.range (logsQ Fc ks logs).length, (((logsQ Fc ks logs).getD i (0, [])).1 : L) *
        logDeriv ((cM T.hC T.S T.hx Fc T.hSF).sem ((logsQ Fc ks logs).getD i (0, [])).2)
  | [], _ => by simp [logSumV, logsQ]
  | cw :: l, hok => by
    have ih := logSumV_logsQ h l fun c hc ↦ hok c (List.mem_cons_of_mem _ hc)
    have hsplit : ((logSumV (T.MP 0 h) (cw :: l) : T.F 0) : L) =
        ((T.MP 0 h).sem cw.1 : L) * logDeriv (((T.MP 0 h).sem cw.2 : T.F 0) : L) +
          ((logSumV (T.MP 0 h) l : T.F 0) : L) := by
      simp only [logSumV, List.map_cons, List.sum_cons, IntermediateField.coe_add,
        IntermediateField.coe_mul, T.coe_logDeriv_FX]
    rw [hsplit, ih]
    by_cases hz : (MO Fc ks 0).isZero cw.2 = true
    · have hl : logsQ Fc ks (cw :: l) = logsQ Fc ks l := by
        simp only [logsQ, List.filter_cons, hz, Bool.not_true]
        rfl
      have h0 : (T.MP 0 h).sem cw.2 = 0 := ((T.MP 0 h).isZero_iff _).mp hz
      rw [hl, h0]
      simp
    · have hz' : (MO Fc ks 0).isZero cw.2 = false := by simpa using hz
      have hl : logsQ Fc ks (cw :: l) =
          (((ratValC Fc ks 0 cw.1).getD 0, (cw.2 : GPoly (GFrac ℚ))) : ℚ × GPoly (GFrac ℚ)) ::
            logsQ Fc ks l := by
        simp only [logsQ, List.filter_cons, hz', Bool.not_false]
        rfl
      rw [hl, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [add_comm]
      congr 1
      rw [T.ratValC_of_const 0 h cw.1 (hok cw List.mem_cons_self), coe_ratCast, T.sem_MP]
      rfl

/-- The value of the coefficient `f` of an `FRep` on the curve. -/
lemma sem_fCode0 (h : T.Tr 0) (fr : FRep (LC 0)) (hok : FRepOK (T.MP 0 h) fr) :
    (((T.MP 0 h).sem (fCode (MO Fc ks 0) fr) : T.F 0) : L) =
      ((cM T.hC T.S T.hx Fc T.hSF).sem fr.h)′ +
        ∑ i ∈ Finset.range (logsQ Fc ks fr.logs).length,
          (((logsQ Fc ks fr.logs).getD i (0, [])).1 : L) *
            logDeriv ((cM T.hC T.S T.hx Fc T.hSF).sem ((logsQ Fc ks fr.logs).getD i (0, [])).2) := by
  rw [sem_fCode, IntermediateField.coe_add, coe_deriv, T.sem_MP, T.logSumV_logsQ h fr.logs hok]
  rfl

/-- **The parametric Risch equation on the curve.** -/
theorem prde0C_spec (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (h : T.Tr 0) (fr : FRep (LC 0)) (hok : FRepOK (T.MP 0 h) fr) :
    RdeSpecK (algebraMap Cc (T.F 0)) (T.MP 0 h) ((T.MP 0 h).sem (fCode (MO Fc ks 0) fr))
      (prdeC Fc ks lv 0 fr) := by
  set M := cM T.hC T.S T.hx Fc T.hSF with hM
  have hf := T.sem_fCode0 h fr hok
  rw [prdeC_zero]
  refine ⟨fun W r hr ↦ ?_, fun W c hc z hz ↦ ?_⟩
  · have hs := curveRdeL_sound T.hC T.S T.hx Fc T.hSF fr.h (logsQ Fc ks fr.logs) W r hr
    apply Subtype.ext
    rw [IntermediateField.coe_add, IntermediateField.coe_mul, coe_deriv, T.sem_MP, hf, sQ,
      AddSubmonoidClass.coe_finsetSum]
    refine hs.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [IntermediateField.coe_mul, T.sem_MP, coe_ratCast]
    rfl
  · have hzE : (z : L)′ + ((M.sem fr.h)′ + ∑ i ∈ Finset.range (logsQ Fc ks fr.logs).length,
          (((logsQ Fc ks fr.logs).getD i (0, [])).1 : L) *
            logDeriv (M.sem ((logsQ Fc ks fr.logs).getD i (0, [])).2)) * (z : L) =
        ∑ j ∈ Finset.range W.length, algebraMap Cc L (c.getD j 0) * M.sem (W.getD j []) := by
      rw [← hf, ← coe_deriv, ← IntermediateField.coe_mul, ← IntermediateField.coe_add, hz, sC,
        AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [IntermediateField.coe_mul, T.sem_MP]
      rfl
    have hu0 : ∀ i < (logsQ Fc ks fr.logs).length,
        M.sem ((logsQ Fc ks fr.logs).getD i (0, [])).2 ≠ 0 := fun i hi ↦
      T.logsQ_ne h fr.logs _ (getD_memC _ _ hi)
    obtain ⟨β, hβ1, hβ2⟩ := curveRdeL_complete T.hC T.S T.hx Fc T.hSF hmon hdeg fr.h
      (logsQ Fc ks fr.logs) hu0 W c (z : L) z.2 hzE
    refine ⟨β, fun i ↦ ?_, ?_⟩
    · by_cases hi : i < W.length
      · rw [hβ1 i hi]
        rfl
      · rw [hc i (by omega)]
        symm
        refine Finset.sum_eq_zero fun k _ ↦ ?_
        have hz0 := getD_fst_ge (α := LC 0) (curveRdeL Fc fr.h (logsQ Fc ks fr.logs) W)
          (MO Fc ks 0).zero W.length (curveRdeG_length Fc _ _ _ W) k i (by omega)
        rw [hz0, map_zero, mul_zero]
    · apply Subtype.ext
      rw [hβ2, AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [IntermediateField.coe_mul]
      rfl

end MTower

end Curves.MT
