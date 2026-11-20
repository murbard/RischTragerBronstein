import RischTragerBronstein.Curves.ProcRFSound6

/-!
# The symbolic zero test

`evXY_Pg`: on the curve, `Pg W (x, y) = (f − v′) · R0(x)² · F_Y(x, y)` whenever
`v · R0(x) = W(x, y)`. `zeroTest_iff`: the computed test `isZeroB (modF … (Pg (Wsol c)))`
holds iff `f = (∑ c_b b)′`.
-/

open Polynomial IntermediateField

namespace Curves

open CPoly Sup Differential

section Alg

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

lemma toPoly_single (c : F) : toPoly [c] = Polynomial.C c := by simp

lemma toB_Pg (P : CurveProb F) (W : BPoly F) :
    toB (P.Pg W) = Polynomial.C (toPoly (discRC P.Fc P.n P.k) * toPoly P.R0) * toB P.A *
        derivative (toB P.Fc) -
      (Polynomial.C (toPoly P.R0) * dX (toB W) -
        Polynomial.C (derivative (toPoly P.R0)) * toB W) * derivative (toB P.Fc) +
      Polynomial.C (toPoly P.R0) * derivative (toB W) * dX (toB P.Fc) := by
  simp only [CurveProb.Pg, toB_addB, toB_mulB, toB_smulB, toB_dXB, toB_derivYB, toPoly_mul,
    toPoly_smul, toPoly_deriv, toPoly_single, map_mul, map_neg, map_one]
  ring

lemma toB_foldr_Wsol (cs : List F) (B : ℕ → BPoly F) (l : List ℕ) :
    toB (l.foldr (fun b acc ↦ addB (smulB [cs.getD b 0] (B b)) acc) []) =
      (l.map fun b ↦ Polynomial.C (Polynomial.C (cs.getD b 0)) * toB (B b)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, toB_addB, toB_smulB, ih, toPoly_single]; rfl

lemma toB_Wsol (P : CurveProb F) (cs : List F) :
    toB (P.Wsol cs) = ∑ b ∈ Finset.range P.basisIdx.length,
      Polynomial.C (Polynomial.C (cs.getD b 0)) *
        toB (basisB (P.basisIdx.getD b (0, 0)).1 (P.basisIdx.getD b (0, 0)).2) := by
  rw [CurveProb.Wsol, toB_foldr_Wsol, sum_range_map]

/-- `F = F_{<n} + Yⁿ` for a valid problem. -/
lemma toB_Fc_split (P : CurveProb F) (hl : P.Fc.length = P.n + 1) (hlast : P.Fc.getD P.n [] = [1]) :
    toB P.Fc = toB (P.Fc.take P.n) + X ^ P.n := by
  conv_lhs => rw [← List.take_append_drop P.n P.Fc]
  have hd : P.Fc.drop P.n = [[1]] := by
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
    rw [List.getD_eq_getElem _ _ (by omega)] at hlast
    rw [hlast]
  rw [toB_append, hd, List.length_take, min_eq_left (by omega), toB_cons, toB_nil, mul_zero,
    add_zero, toPoly_single]
  simp

end Alg

section Curve

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]

lemma dX_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (Q : R[X][X]) :
    (dX Q).map (mapRingHom φ) = dX (Q.map (mapRingHom φ)) := by
  ext1 i
  rw [coeff_map, dX_coeff, dX_coeff, coeff_map]
  exact (derivative_map _ _).symm

namespace CurveData

variable (S : CurveData C L)

lemma evXY_CC (q : C[X]) (Q : C[X][X]) :
    S.evXY (Polynomial.C q * Q) = aeval S.x q * S.evXY Q := by
  rw [S.evXY_mul]
  congr 1
  simp [evXY]

variable {P : CurveProb F} {ψ₀ : F →+* C}

lemma evXY_C' (q : C[X]) : S.evXY (Polynomial.C q) = aeval S.x q := by simp [evXY]

lemma evXY_sum {ι : Type*} (s : Finset ι) (Q : ι → C[X][X]) :
    S.evXY (∑ i ∈ s, Q i) = ∑ i ∈ s, S.evXY (Q i) := by
  simp [evXY, Polynomial.map_sum, eval_finsetSum]

/-- **The numerator identity** behind the zero test. -/
theorem evXY_Pg (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) (W : BPoly F) (v : L)
    (hv : v * aeval S.x ((toPoly P.R0).map ψ₀) = S.evXY ((toB W).map (mapRingHom ψ₀))) :
    S.evXY ((toB (P.Pg W)).map (mapRingHom ψ₀)) =
      ((S.fE P ψ₀ : L) - v′) * aeval S.x ((toPoly P.R0).map ψ₀) ^ 2 *
        S.evXY (derivative S.F) := by
  have hfD : (S.fE P ψ₀ : L) * aeval S.x ((toPoly P.D).map ψ₀) =
      S.evXY ((toB P.A).map (mapRingHom ψ₀)) := S.fE_spec P ψ₀ hV
  have hfR : (S.fE P ψ₀ : L) * aeval S.x ((toPoly P.R0).map ψ₀) =
      aeval S.x ((toPoly (discRC P.Fc P.n P.k)).map ψ₀) *
        S.evXY ((toB P.A).map (mapRingHom ψ₀)) := by
    rw [toPoly_R0, Polynomial.map_mul, map_mul, ← hfD]
    ring
  have hvR' : v′ * aeval S.x ((toPoly P.R0).map ψ₀) +
      v * aeval S.x (derivative ((toPoly P.R0).map ψ₀)) =
      (S.evXY ((toB W).map (mapRingHom ψ₀)))′ := by
    rw [← hv, Derivation.leibniz, smul_eq_mul, smul_eq_mul, deriv_aeval_x S.x hC hx]
    ring
  have hFY0 : S.evXY (derivative S.F) ≠ 0 := S.evXY_derivative_ne_zero
  have hW' : (S.evXY ((toB W).map (mapRingHom ψ₀)))′ * S.evXY (derivative S.F) =
      S.evXY (dX ((toB W).map (mapRingHom ψ₀))) * S.evXY (derivative S.F) -
        S.evXY (derivative ((toB W).map (mapRingHom ψ₀))) * S.evXY (dX S.F) := by
    rw [S.deriv_evXY hC hx, S.deriv_y hC hx]
    field_simp
    ring
  have hL : S.evXY ((toB (P.Pg W)).map (mapRingHom ψ₀)) =
      aeval S.x ((toPoly (discRC P.Fc P.n P.k)).map ψ₀) * aeval S.x ((toPoly P.R0).map ψ₀) *
          S.evXY ((toB P.A).map (mapRingHom ψ₀)) * S.evXY (derivative S.F) -
        (aeval S.x ((toPoly P.R0).map ψ₀) * S.evXY (dX ((toB W).map (mapRingHom ψ₀))) -
          aeval S.x (derivative ((toPoly P.R0).map ψ₀)) *
            S.evXY ((toB W).map (mapRingHom ψ₀))) * S.evXY (derivative S.F) +
        aeval S.x ((toPoly P.R0).map ψ₀) * S.evXY (derivative ((toB W).map (mapRingHom ψ₀))) *
          S.evXY (dX S.F) := by
    rw [toB_Pg, hSF]
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
      ← derivative_map, ← dX_map, S.evXY_add, S.evXY_sub, S.evXY_mul, S.evXY_C', coe_mapRingHom,
      Polynomial.map_mul, map_mul]
  rw [hL]
  linear_combination (-(aeval S.x ((toPoly P.R0).map ψ₀) * S.evXY (derivative S.F))) * hfR +
    (aeval S.x ((toPoly P.R0).map ψ₀) * S.evXY (derivative S.F)) * hvR' -
    (aeval S.x (derivative ((toPoly P.R0).map ψ₀)) * S.evXY (derivative S.F)) * hv +
    aeval S.x ((toPoly P.R0).map ψ₀) * hW'

/-- **The zero test.** -/
theorem zeroTest_iff (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) (hl : P.Fc.length = P.n + 1)
    (hlast : P.Fc.getD P.n [] = [1]) (cs : List F) :
    isZeroB (modF P.Fc P.n (P.Pg (P.Wsol cs))) = true ↔
      (S.fE P ψ₀ : L) = ((∑ b ∈ Finset.range P.basisIdx.length,
        S.cst (ψ₀ (cs.getD b 0)) * S.bE P ψ₀ (P.basisIdx.getD b (0, 0)) : C⟮S.x⟯⟮S.y⟯) : L)′ := by
  have hv : ((∑ b ∈ Finset.range P.basisIdx.length,
        S.cst (ψ₀ (cs.getD b 0)) * S.bE P ψ₀ (P.basisIdx.getD b (0, 0)) : C⟮S.x⟯⟮S.y⟯) : L) *
      aeval S.x ((toPoly P.R0).map ψ₀) = S.evXY ((toB (P.Wsol cs)).map (mapRingHom ψ₀)) := by
    rw [toB_Wsol, Polynomial.map_sum, S.evXY_sum, AddSubmonoidClass.coe_finsetSum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [MulMemClass.coe_mul, mul_assoc, S.bE_spec P ψ₀ hV, Polynomial.map_mul, Polynomial.map_C,
      coe_mapRingHom, Polynomial.map_C, S.evXY_C_mul]
    rfl
  rw [← S.evXY_zero_iff P.Fc ψ₀ hSF P.n (S.natDegree_F_eq P ψ₀ hSF hV)
    (toB_Fc_split P hl hlast), S.evXY_Pg hC hx hSF hV _ _ hv]
  have hR : aeval S.x ((toPoly P.R0).map ψ₀) ≠ 0 := S.aeval_x_ne_zero _ (by
    rw [Ne, Polynomial.map_eq_zero_iff ψ₀.injective]; exact P.R0_ne_zero hV)
  rw [mul_eq_zero, mul_eq_zero, sub_eq_zero]
  simp only [pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, hR,
    S.evXY_derivative_ne_zero, or_false]

end CurveData

end Curve

end Curves
