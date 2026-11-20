import RischTragerBronstein.Torsion.RamRoots
import RischTragerBronstein.Torsion.PrimeEv1

/-!
# Coefficients of certified representatives lie in any subring containing the data

For a subring `O` of a field `F` containing the coefficients of `F(x, Y)`, the point `a`, the
approximation `y` of a `rootCheck`, and the inverse of the leading coefficient of `F_Y(a + Tᵉ, y)`,
the representative `ρ ∈ F⟦T⟧` (the root of `F(a + Tᵉ, Y)` close to `y`) has all its coefficients in
`O` (**`rep_coeff_mem`**): Hensel's lemma over `O⟦T⟧` (`hensel_quantR`) and uniqueness over `F`.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Sub

lemma toB_mapL' {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (W : BPoly A) :
    toB (W.map (·.map φ)) = (toB W).map (mapRingHom φ) := by
  induction W with
  | nil => simp
  | cons c W ih =>
    rw [List.map_cons, toB_cons, toB_cons, ih, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X, coe_mapRingHom, Sup.toPoly_mapHom]

variable {F : Type*} [Field F] [DecidableEq F] (O : Subring F)

/-- The lift to `O` (zero off `O`). -/
noncomputable def liftO (x : F) : O := by
  classical
  exact if h : x ∈ O then ⟨x, h⟩ else 0

lemma liftO_coe {x : F} (h : x ∈ O) : ((liftO O x : O) : F) = x := by
  classical
  unfold liftO; rw [dif_pos h]

lemma map_liftO {l : List F} (h : InS O l) : (l.map (liftO O)).map O.subtype = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun c hc ↦ liftO_coe O (h c hc)

/-- **The coefficients of a certified representative lie in `O`.** -/
theorem rep_coeff_mem {Fc : BPoly F} (hF : InSB O Fc) {a : F} (ha : a ∈ O) {e prec : ℕ}
    {y : CPoly F} (hy : InS O y) (h : rootCheck Fc a e prec y = true)
    (hu : ((bivEval (derivYB Fc) (shiftC a e) y).getD
      (ordC (bivEval (derivYB Fc) (shiftC a e) y)) 0)⁻¹ ∈ O)
    (ρ : PowerSeries F) (hρ : (repEq (RingHom.id F) Fc a e).eval ρ = 0)
    (hd : (PowerSeries.X : PowerSeries F) ^ prec ∣ ρ - thetaT (RingHom.id F) (toPoly y)) :
    ∀ i, PowerSeries.coeff i ρ ∈ O := by
  obtain ⟨h1, h2, h3⟩ := rootCheck_spec h
  set ι := O.subtype with hι
  have hιi : Function.Injective ι := Subtype.val_injective
  set FO : O[X][X] := toB (Fc.map (·.map (liftO O))) with hFO
  have hFι : FO.map (mapRingHom ι) = (toB Fc).map (mapRingHom (RingHom.id F)) := by
    rw [hFO, ← toB_mapL', List.map_map, Polynomial.mapRingHom_id, Polynomial.map_id]
    congr 1
    conv_rhs => rw [← List.map_id Fc]
    exact List.map_congr_left fun P hP ↦ map_liftO O (hF P hP)
  set αO := liftO O a with hαO
  have hαι : ι αO = (RingHom.id F) a := liftO_coe O ha
  set y₀ : O[X] := toPoly (y.map (liftO O)) with hy₀
  have hyι : y₀.map ι = (toPoly y).map (RingHom.id F) := by
    rw [hy₀, ← Sup.toPoly_mapHom, map_liftO O hy, Polynomial.map_id]
  set B := ordC (bivEval (derivYB Fc) (shiftC a e) y) with hBdef
  set H := FO.map (psSubR e αO) with hH
  have hA : (PowerSeries.X : PowerSeries O) ^ (B + prec) ∣ H.eval (y₀ : PowerSeries O) := by
    refine coeff_eq_zero_of_map ι hιi _ _ fun i hi ↦ ?_
    rw [lift_eval ι (RingHom.id F) FO Fc hFι e αO a hαι y₀ y hyι, coeff_thetaT, h3 i hi, map_zero]
  have hdQι : (derivative FO).map (mapRingHom ι) =
      (toB (derivYB Fc)).map (mapRingHom (RingHom.id F)) := by
    rw [← Polynomial.derivative_map, hFι, Polynomial.derivative_map, toB_derivYB]
  have hdH : derivative H = (derivative FO).map (psSubR e αO) := by
    rw [hH, Polynomial.derivative_map]
  have hDB : (PowerSeries.X : PowerSeries O) ^ B ∣ (derivative H).eval (y₀ : PowerSeries O) := by
    refine coeff_eq_zero_of_map ι hιi _ _ fun i hi ↦ ?_
    rw [hdH, lift_eval ι (RingHom.id F) (derivative FO) (derivYB Fc) hdQι e αO a hαι y₀ y hyι,
      coeff_thetaT, getD_lt_ordC _ i hi, map_zero]
  obtain ⟨u, hu'⟩ := hDB
  have hcu : ι (PowerSeries.constantCoeff u) =
      (bivEval (derivYB Fc) (shiftC a e) y).getD B 0 := by
    have e1 : PowerSeries.constantCoeff u =
        PowerSeries.coeff B ((derivative H).eval (y₀ : PowerSeries O)) := by
      rw [hu', PowerSeries.coeff_X_pow_mul', ite_eq_left_iff.mpr (fun h ↦ absurd le_rfl h), Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [e1, ← PowerSeries.coeff_map, hdH, lift_eval ι (RingHom.id F) (derivative FO) (derivYB Fc)
      hdQι e αO a hαι y₀ y hyι, coeff_thetaT, RingHom.id_apply]
  have hu0 : (bivEval (derivYB Fc) (shiftC a e) y).getD B 0 ≠ 0 := getD_ordC _ h2
  have hunit : IsUnit (PowerSeries.constantCoeff u) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hu⟩, hιi ?_⟩
    rw [map_mul, map_one, hcu]
    exact mul_inv_cancel₀ hu0
  obtain ⟨yO, hyO, hdO⟩ := hensel_quantR H (y₀ : PowerSeries O) (B + prec) B u hA hu' hunit
    (by omega)
  rw [Nat.add_sub_cancel_left] at hdO
  -- the image of the root over `O` is `ρ`
  have heq : PowerSeries.map ι yO = ρ := by
    refine rep_unique (RingHom.id F) h _ _ ?_ hρ ?_ hd
    · have := congrArg (PowerSeries.map ι) hyO
      rw [map_eval_psSubR, hFι, hαι, map_zero] at this
      exact this
    · have := map_dvd (PowerSeries.map ι) hdO
      rwa [map_pow, PowerSeries.map_X, map_sub, map_coe_poly, hyι, ← thetaT_apply] at this
  intro i
  rw [← heq, PowerSeries.coeff_map]
  exact (PowerSeries.coeff i yO).2

end Sub

end Curves
