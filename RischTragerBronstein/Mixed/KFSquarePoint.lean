import RischTragerBronstein.Mixed.KFSquareOdd
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.LaurentSeries

/-!
# Rational non-squares over base curves with a smooth rational point

If the base curve `F(x, y) = 0` (monic in `y`) has a rational point `(x₀, y₀)` with
`∂F/∂y (x₀, y₀) ≠ 0`, Hensel's lemma in `ℚ⟦t⟧` (`X`-adically complete) gives `y(t)` with
`F(x₀ + t, y(t)) = 0`, hence an embedding `K₀ ↪ ℚ((t))`. A square root of a rational `q` in
`ℚ((t))` has leading coefficient `√q ∈ ℚ` (`laurent_sq`); so rational non-squares stay non-squares
in every `Kₘ` (`not_isSquare_KF_point`), checked by `ptOK` / `ptSearch`. `sqOK` collects the
accepted bases: linear, odd degree in `y`, `quadOK`, or a smooth integral point.
-/

open Polynomial CPoly

namespace Curves.MT

/-- Evaluation of a list polynomial. -/
def evalQ (p : CPoly ℚ) (x : ℚ) : ℚ := p.foldr (fun a acc ↦ a + x * acc) 0

lemma evalQ_eq : ∀ (p : CPoly ℚ) (x : ℚ), evalQ p x = (toPoly p).eval x
  | [], _ => by simp [evalQ, CPoly.toPoly]
  | a :: p, x => by
    simp only [evalQ, List.foldr_cons] at *
    rw [show List.foldr (fun a acc ↦ a + x * acc) 0 p = evalQ p x from rfl, evalQ_eq p x]
    simp [CPoly.toPoly_cons]

lemma toPoly_map_hom {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S) :
    ∀ l : CPoly R, toPoly (l.map h) = (toPoly l).map h
  | [] => by simp [CPoly.toPoly]
  | a :: l => by simp [CPoly.toPoly_cons, toPoly_map_hom h l]

/-- **Square roots of rationals in `ℚ((t))` are rational.** -/
theorem laurent_sq (q : ℚ) (s : LaurentSeries ℚ) (h : s * s = (q : LaurentSeries ℚ)) :
    IsSquare q := by
  by_cases hq : q = 0
  · exact ⟨0, by rw [hq, mul_zero]⟩
  have hl := congrArg HahnSeries.leadingCoeff h
  rw [HahnSeries.leadingCoeff_mul, ← map_ratCast (HahnSeries.C (Γ := ℤ) (R := ℚ)) q,
    HahnSeries.C_apply, HahnSeries.leadingCoeff_of_single] at hl
  exact ⟨s.leadingCoeff, hl.symm⟩

section Embed

variable (x0 : ℚ)

/-- `p ↦ p(x₀ + t)` into `ℚ⟦t⟧`. -/
noncomputable def shiftH : ℚ[X] →+* PowerSeries ℚ :=
  Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.compRingHom (X + Polynomial.C x0))

/-- `p ↦ p(x₀ + t)` into `ℚ((t))`. -/
noncomputable def shiftL : ℚ[X] →+* LaurentSeries ℚ :=
  (HahnSeries.ofPowerSeries ℤ ℚ).comp (shiftH x0)

lemma shiftL_injective : Function.Injective (shiftL x0) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have h1 : shiftH x0 p = 0 :=
    HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ)
      (by rw [map_zero]; exact hp : HahnSeries.ofPowerSeries ℤ ℚ (shiftH x0 p) =
        HahnSeries.ofPowerSeries ℤ ℚ 0)
  have h2 : p.comp (X + Polynomial.C x0) = 0 := by
    have : ((p.comp (X + Polynomial.C x0) : ℚ[X]) : PowerSeries ℚ) = 0 := h1
    exact_mod_cast this
  rcases comp_eq_zero_iff.mp h2 with h | ⟨-, h⟩
  · exact h
  · exfalso
    have := congrArg natDegree h
    rw [natDegree_X_add_C, natDegree_C] at this
    exact one_ne_zero this

/-- The embedding `ℚ(x) → ℚ((t))`, `x ↦ x₀ + t`. -/
noncomputable def shiftR : RatFunc ℚ →+* LaurentSeries ℚ :=
  IsFractionRing.lift (shiftL_injective x0)

/-- The same on the computable `ℚ(x)`. -/
noncomputable def shiftK : RFC.RatFuncC ℚ →+* LaurentSeries ℚ :=
  (shiftR x0).comp RFC.toRFHom

lemma shiftK_mk (c : CPoly ℚ) :
    shiftK x0 (RFC.mk c [1]) = HahnSeries.ofPowerSeries ℤ ℚ (shiftH x0 (toPoly c)) := by
  have hm : RFC.toRFHom (K := ℚ) (RFC.mk c [1]) = algebraMap ℚ[X] (RatFunc ℚ) (toPoly c) := by
    show RFC.toRF (K := ℚ) (RFC.mk c [1]) = _
    rw [RFC.toRF_mk]; simp [CPoly.toPoly]
  simp only [shiftK, RingHom.comp_apply, hm, shiftR, IsFractionRing.lift_algebraMap]
  rfl

lemma constantCoeff_shiftH (p : ℚ[X]) : PowerSeries.constantCoeff (shiftH x0 p) = p.eval x0 := by
  simp only [shiftH, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.compRingHom]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
    coeff_zero_eq_eval_zero]
  change eval 0 (p.comp (X + Polynomial.C x0)) = eval x0 p
  rw [eval_comp]; simp

end Embed

lemma monic_toPoly_append_one {R : Type*} [CommRing R] [Nontrivial R] (l : CPoly R) :
    (toPoly (l ++ [1])).Monic := by
  refine monic_of_degree_le l.length ?_ ?_
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [CPoly.coeff_toPoly, List.getD_eq_default]
    simp only [List.length_append, List.length_singleton]
    exact_mod_cast hm
  · rw [CPoly.coeff_toPoly, List.getD_eq_getElem _ _ (by simp)]
    simp

/-- The specialized polynomial `F(x₀, Y)`. -/
def specF (Fc : Sup.BPoly ℚ) (x0 : ℚ) : CPoly ℚ := Fc.map fun c ↦ evalQ c x0

/-- **A smooth rational point** `(x₀, y₀)` of a base curve monic in `y`. -/
def ptOK (Fc : Sup.BPoly ℚ) (x0 y0 : ℚ) : Bool :=
  Fc.getLast? == some [1] && evalQ (specF Fc x0) y0 == 0 &&
    evalQ (CPoly.deriv (specF Fc x0)) y0 != 0

open scoped Classical in
/-- **Rational non-squares stay non-squares in every `Kₘ`** (base curve with a smooth rational
point). -/
theorem not_isSquare_KF_point (Fc : Sup.BPoly ℚ) [hF : Fact (Irreducible (toPoly (fKc Fc)))]
    (x0 y0 : ℚ) (hpt : ptOK Fc x0 y0 = true) (q : ℚ) (hq : ¬ IsSquare q) (m : ℕ) :
    ¬ IsSquare ((q : ℚ) : KF Fc m) := by
  simp only [ptOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hpt
  obtain ⟨⟨hlast, h0⟩, h1⟩ := hpt
  intro h
  obtain ⟨r, hr⟩ := sq_KF_descend Fc q m h
  set f := toPoly (fKc Fc)
  -- the polynomial over `ℚ⟦t⟧`
  set g : (PowerSeries ℚ)[X] := toPoly (Fc.map fun c ↦ shiftH x0 (toPoly c)) with hg
  have hFc : Fc = Fc.dropLast ++ [[1]] := by
    have := List.dropLast_append_getLast? (l := Fc) [1] hlast
    exact this.symm
  have hgm : g.Monic := by
    rw [hg, hFc, List.map_append, List.map_singleton]
    have : shiftH x0 (toPoly [1]) = 1 := by simp [CPoly.toPoly]
    rw [this]
    exact monic_toPoly_append_one _
  have hfg : f.map (shiftK x0) = g.map (HahnSeries.ofPowerSeries ℤ ℚ) := by
    rw [hg, ← toPoly_map_hom, ← toPoly_map_hom]
    show toPoly ((Fc.map fun c ↦ RFC.mk c [1]).map (shiftK x0)) = _
    rw [List.map_map, List.map_map]
    congr 1
    exact List.map_congr_left fun c _ ↦ shiftK_mk x0 c
  have hgc : g.map PowerSeries.constantCoeff = toPoly (specF Fc x0) := by
    rw [hg, ← toPoly_map_hom, List.map_map, specF]
    congr 1
    exact List.map_congr_left fun c _ ↦ by
      simp only [Function.comp_apply, constantCoeff_shiftH, evalQ_eq]
  -- Hensel
  set a0 : PowerSeries ℚ := PowerSeries.C y0
  have he0 : g.eval a0 ∈ Ideal.span {(PowerSeries.X : PowerSeries ℚ)} := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, ← eval₂_at_apply, ← eval_map,
      PowerSeries.constantCoeff_C, hgc, ← evalQ_eq]
    exact h0
  have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ℚ)})
      (g.derivative.eval a0)) := by
    refine IsUnit.map _ ?_
    rw [PowerSeries.isUnit_iff_constantCoeff, ← eval₂_at_apply, ← eval_map, ← derivative_map,
      PowerSeries.constantCoeff_C, hgc, ← CPoly.toPoly_deriv, ← evalQ_eq]
    exact Ne.isUnit h1
  obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian g hgm a0 he0 hu
  -- the embedding of `K₀`
  have hroot : f.eval₂ (shiftK x0) (HahnSeries.ofPowerSeries ℤ ℚ a) = 0 := by
    rw [← eval_map, hfg, eval_map, eval₂_at_apply, ha.eq_zero, map_zero]
  set ψ := (AdjoinRoot.lift (shiftK x0) _ hroot).comp (NFK.toARHom (fKc Fc))
  have hψ : ψ r * ψ r = ((q : ℚ) : LaurentSeries ℚ) := by rw [← map_mul, ← hr, map_ratCast]
  exact hq (laurent_sq q (ψ r) hψ)

/-- A search for a smooth integral point `(x₀, y₀)`, `|x₀|, |y₀| ≤ 8`. -/
def ptSearch (Fc : Sup.BPoly ℚ) : Bool :=
  ((List.range 17).flatMap fun i ↦ (List.range 17).map fun j ↦
    (((i : ℤ) - 8 : ℚ), ((j : ℤ) - 8 : ℚ))).any fun p ↦ ptOK Fc p.1 p.2

theorem not_isSquare_KF_ptSearch (Fc : Sup.BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]
    (h : ptSearch Fc = true) (q : ℚ) (hq : ¬ IsSquare q) (m : ℕ) :
    ¬ IsSquare ((q : ℚ) : KF Fc m) := by
  unfold ptSearch at h
  obtain ⟨p, -, hp⟩ := List.any_eq_true.mp h
  exact not_isSquare_KF_point Fc p.1 p.2 hp q hq m

-- `y² = x³ + 1` (`F = y² − x³ − 1`) has the smooth point `(0, 1)`.
#guard ptSearch [[-1, 0, 0, -1], [], [1]] = true

/-- The base curves for which the conjugation searches at levels `m + 1` are valid. -/
def sqOK (Fc : Sup.BPoly ℚ) : Bool :=
  Fc == [Fc.headD [], [1]] || (CPoly.trim (fKc Fc)).length % 2 == 0 || quadOK Fc || ptSearch Fc

theorem not_isSquare_KF_sqOK (Fc : Sup.BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]
    (h : sqOK Fc = true) (q : ℚ) (hq : ¬ IsSquare q) (m : ℕ) : ¬ IsSquare ((q : ℚ) : KF Fc m) := by
  simp only [sqOK, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h
  · exact not_isSquare_KF' Fc _ h q hq m
  · exact not_isSquare_KF_odd Fc h q hq m
  · exact not_isSquare_KF_quadOK Fc h q hq m
  · exact not_isSquare_KF_ptSearch Fc h q hq m

lemma sqOK_of_linear (Fc : Sup.BPoly ℚ) (c0 : CPoly ℚ) (h : Fc = [c0, [1]]) : sqOK Fc = true := by
  subst h; simp [sqOK]

-- `y² + x³ + 1`: discriminant `−4(x³ + 1)`, squarefree and non-constant.
#guard quadOK [[1, 0, 0, 1], [], [1]] = true
#guard sqOK [[1, 0, 0, 1], [], [1]] = true


end Curves.MT
