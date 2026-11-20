import RischTragerBronstein.Curves.DiscC

/-!
# Bivariate tools for general curves

* `dXB`: the `x`-derivative (`toB_dXB`);
* `modF Fc n`: reduction modulo the monic curve equation (`modF_dvd`, `length_modF`);
* `isZeroB`; `evXY_eq_zero_iff`: `W(x, y) = 0` on the curve iff `W mod F = 0` (irreducibility).
-/

open Polynomial

namespace Curves

open CPoly Sup Differential

section Defs

variable {F : Type*} [Field F] [DecidableEq F]

/-- The `x`-derivative. -/
def dXB (W : BPoly F) : BPoly F := W.map CPoly.deriv

/-- The remainder of `W` modulo a monic `F = Fₗₒ + Yⁿ` (`Fc.take n = Fₗₒ`). -/
def modF (Fc : BPoly F) (n : ℕ) (W : BPoly F) : BPoly F :=
  if h : W.length ≤ n then W
  else modF Fc n (addB (W.take (W.length - 1))
    (List.replicate (W.length - 1 - n) [] ++ smulB (CPoly.neg (W.getD (W.length - 1) [])) (Fc.take n)))
termination_by W.length
decreasing_by
  rw [length_addB, List.length_take, List.length_append, List.length_replicate, smulB,
    List.length_map, List.length_take]
  have : n < W.length := by omega
  rcases Nat.lt_or_ge n Fc.length with hF | hF <;> simp [min_eq_left, *] <;> omega

/-- All coefficients vanish. -/
def isZeroB (W : BPoly F) : Bool := W.all CPoly.isZero

end Defs

section Sem

variable {F : Type*} [Field F] [DecidableEq F]

lemma toB_dXB (W : BPoly F) : toB (dXB W) = dX (toB W) := by
  ext1 i
  rw [dX_coeff, coeff_toB, coeff_toB, dXB, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : W[i]? with
  | none =>
    simp only [Option.map_none, Option.getD_none, toPoly_nil]
    rw [List.getD_eq_getElem?_getD, h, Option.getD_none, toPoly_nil, derivative_zero]
  | some c =>
    simp only [Option.map_some, Option.getD_some, toPoly_deriv]
    rw [List.getD_eq_getElem?_getD, h, Option.getD_some]

lemma isZeroB_iff (W : BPoly F) : isZeroB W = true ↔ toB W = 0 := by
  constructor
  · intro h
    ext1 i
    rw [coeff_toB, Polynomial.coeff_zero]
    by_cases hi : i < W.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact (isZero_iff _).mp (List.all_eq_true.mp h _ (List.getElem_mem hi))
    · rw [List.getD_eq_default _ _ (not_lt.mp hi), toPoly_nil]
  · intro h
    refine List.all_eq_true.mpr fun c hc ↦ ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    rw [isZero_iff]
    have := congrArg (fun P ↦ P.coeff i) h
    simp only [coeff_toB, Polynomial.coeff_zero] at this
    rwa [List.getD_eq_getElem _ _ hi] at this

lemma length_modF (Fc : BPoly F) (n : ℕ) (W : BPoly F) : (modF Fc n W).length ≤ n := by
  induction W using (measure List.length).wf.induction with
  | h W ih =>
    rw [modF]
    split_ifs with h
    · exact h
    · refine ih _ ?_
      show _ < W.length
      rw [length_addB, List.length_take, List.length_append, List.length_replicate, smulB,
        List.length_map, List.length_take]
      have : n < W.length := by omega
      rcases Nat.lt_or_ge n Fc.length with hF | hF <;> simp [min_eq_left, *] <;> omega

/-- **Reduction is a congruence** modulo `F = Fₗₒ + Yⁿ`. -/
lemma modF_dvd (Fc : BPoly F) (n : ℕ) (hF : toB Fc = toB (Fc.take n) + X ^ n) (W : BPoly F) :
    toB Fc ∣ toB (modF Fc n W) - toB W := by
  induction W using (measure List.length).wf.induction with
  | h W ih =>
    rw [modF]
    split_ifs with h
    · simp
    · have hlen : n < W.length := by omega
      set m := W.length - 1 with hm
      set t := W.getD m [] with ht
      set W' := addB (W.take m) (List.replicate (m - n) [] ++ smulB (CPoly.neg t) (Fc.take n))
        with hW'
      have h1 := ih W' (by
        show W'.length < W.length
        rw [hW', length_addB, List.length_take, List.length_append, List.length_replicate, smulB,
          List.length_map, List.length_take]
        rcases Nat.lt_or_ge n Fc.length with hF' | hF' <;> simp [min_eq_left, *] <;> omega)
      have hW : toB W = toB (W.take m) + X ^ m * Polynomial.C (toPoly t) := by
        conv_lhs => rw [← List.take_append_drop m W]
        rw [toB_append, List.length_take, min_eq_left (by omega)]
        have : W.drop m = [t] := by
          rw [ht, List.getD_eq_getElem _ _ (by omega), List.drop_eq_getElem_cons (by omega),
            List.drop_eq_nil_of_le (by omega)]
        rw [this, toB_cons, toB_nil, mul_zero, add_zero]
      have hW'e : toB W' = toB (W.take m) - X ^ (m - n) * Polynomial.C (toPoly t) *
          toB (Fc.take n) := by
        rw [hW', toB_addB, toB_append, List.length_replicate, toB_smulB, toPoly_neg]
        have : toB (List.replicate (m - n) ([] : CPoly F)) = 0 := by
          induction (m - n) with
          | zero => rfl
          | succ j ihj => rw [List.replicate_succ, toB_cons, ihj, toPoly_nil, map_zero]; ring
        rw [this, zero_add, map_neg]; ring
      have key : toB W' - toB W = -(X ^ (m - n) * Polynomial.C (toPoly t)) * toB Fc := by
        rw [hW'e, hW, hF]
        have : (X : (F[X])[X]) ^ m = X ^ (m - n) * X ^ n := by
          rw [← pow_add, Nat.sub_add_cancel (by omega)]
        rw [this]; ring
      have := dvd_add h1 (Dvd.intro_left _ key.symm)
      rwa [sub_add_sub_cancel] at this

end Sem

section Zero

variable {F : Type*} [Field F] [DecidableEq F]
variable {C L : Type*} [Field C] [Field L] [Algebra C L]

lemma natDegree_toB_lt (W : BPoly F) (n : ℕ) (hW : W.length ≤ n) (hn : 0 < n) :
    (toB W).natDegree < n := by
  refine lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ ?_) (by omega :
    n - 1 < n)
  have hi' : n - 1 < i := by exact_mod_cast hi
  rw [coeff_toB, List.getD_eq_default _ _ (by omega), toPoly_nil]

namespace CurveData

variable (S : CurveData C L)

lemma evXY_add (P Q : C[X][X]) : S.evXY (P + Q) = S.evXY P + S.evXY Q := by
  simp [evXY, Polynomial.map_add]

lemma evXY_mul (P Q : C[X][X]) : S.evXY (P * Q) = S.evXY P * S.evXY Q := by
  simp [evXY, Polynomial.map_mul]

lemma evXY_sub (P Q : C[X][X]) : S.evXY (P - Q) = S.evXY P - S.evXY Q := by
  simp [evXY, Polynomial.map_sub]

/-- **The zero test**: `W(x, y) = 0` iff the remainder of `W` modulo `F` vanishes. -/
theorem evXY_zero_iff (Fc : BPoly F) (ψ₀ : F →+* C) (hSF : S.F = (toB Fc).map (mapRingHom ψ₀))
    (n : ℕ) (hn : S.F.natDegree = n) (hF : toB Fc = toB (Fc.take n) + X ^ n) (W : BPoly F) :
    S.evXY ((toB W).map (mapRingHom ψ₀)) = 0 ↔ isZeroB (modF Fc n W) = true := by
  have hn0 : 0 < n := by rw [← hn]; exact Nat.pos_of_ne_zero S.natDegree_F_ne_zero
  obtain ⟨q, hq⟩ := modF_dvd Fc n hF W
  have hR : S.evXY ((toB (modF Fc n W)).map (mapRingHom ψ₀)) =
      S.evXY ((toB W).map (mapRingHom ψ₀)) := by
    have e : toB (modF Fc n W) = toB W + toB Fc * q := by rw [← hq]; ring
    rw [e, Polynomial.map_add, Polynomial.map_mul, S.evXY_add, S.evXY_mul, ← hSF, S.evXY_F,
      zero_mul, add_zero]
  rw [isZeroB_iff, ← hR]
  constructor
  · intro h0
    have hdeg : ((toB (modF Fc n W)).map (mapRingHom ψ₀)).natDegree < S.F.natDegree := by
      rw [hn]
      exact natDegree_map_le.trans_lt (natDegree_toB_lt _ n (length_modF Fc n W) hn0)
    have := S.irr _ hdeg h0
    exact (Polynomial.map_eq_zero_iff (Polynomial.map_injective _ ψ₀.injective)).mp this
  · intro h0
    rw [h0, Polynomial.map_zero, evXY, Polynomial.map_zero, eval_zero]

end CurveData

end Zero

end Curves
