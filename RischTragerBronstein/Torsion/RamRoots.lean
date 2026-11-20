import RischTragerBronstein.Torsion.GoodPrimeStep
import RischTragerBronstein.Torsion.RamStep
import RischTragerBronstein.Torsion.TestCertN
import RischTragerBronstein.Curves.HenselR

/-!
# Representatives of ramified places from certificates

A `rootCheck` of an approximation `y` of a root of `F(a + Tᵉ, Y)` gives:

* `rep_root_field`, `rep_unique`: the root over `K⟦T⟧` (any field, through `ψ`) and its uniqueness;
* `rep_root_Zp`: the root over `ℤ_p⟦T⟧`, when the leading term of `F_Y(a + Tᵉ, y)` is a unit;
* `conjPS`, `conjC`: the conjugates `T ↦ ζ T` of the reparametrizations `T ↦ Tˢ`, as power series
  and on approximations.
-/

open Polynomial HahnSeries

namespace Curves

open Differential LaurentSeries CPoly Sup GTors

section Conj

variable {R : Type*} [CommRing R]

/-- `∑ₘ ζᵐ ρ_{m/s} Tᵐ` (sum over `s ∣ m`): the series `ρ(Tˢ)` rotated by `T ↦ ζ T`. -/
noncomputable def conjPS (ζ : R) (s : ℕ) (ρ : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun m ↦ if s ∣ m then ζ ^ m * PowerSeries.coeff (m / s) ρ else 0

lemma coeff_conjPS (ζ : R) (s : ℕ) (ρ : PowerSeries R) (m : ℕ) :
    PowerSeries.coeff m (conjPS ζ s ρ) = if s ∣ m then ζ ^ m * PowerSeries.coeff (m / s) ρ else 0 :=
  PowerSeries.coeff_mk _ _

lemma map_conjPS {S : Type*} [CommRing S] (f : R →+* S) (ζ : R) (s : ℕ) (ρ : PowerSeries R) :
    PowerSeries.map f (conjPS ζ s ρ) = conjPS (f ζ) s (PowerSeries.map f ρ) := by
  ext m
  rw [PowerSeries.coeff_map, coeff_conjPS, coeff_conjPS, PowerSeries.coeff_map]
  split_ifs <;> simp

lemma conjPS_sub (ζ : R) (s : ℕ) (ρ ρ' : PowerSeries R) :
    conjPS ζ s (ρ - ρ') = conjPS ζ s ρ - conjPS ζ s ρ' := by
  ext m
  rw [map_sub, coeff_conjPS, coeff_conjPS, coeff_conjPS, map_sub]
  split_ifs <;> ring

lemma X_pow_dvd_conjPS (ζ : R) {s : ℕ} (hs : 0 < s) {P : ℕ} {ρ : PowerSeries R}
    (h : (PowerSeries.X : PowerSeries R) ^ P ∣ ρ) :
    (PowerSeries.X : PowerSeries R) ^ (s * P) ∣ conjPS ζ s ρ := by
  rw [PowerSeries.X_pow_dvd_iff] at h ⊢
  intro m hm
  rw [coeff_conjPS]
  split_ifs
  · rw [h (m / s) (Nat.div_lt_of_lt_mul hm), mul_zero]
  · rfl

lemma map_coe_poly {S : Type*} [CommRing S] (f : R →+* S) (P : R[X]) :
    PowerSeries.map f (P : PowerSeries R) = ((P.map f : S[X]) : PowerSeries S) := by
  ext m
  rw [PowerSeries.coeff_map, Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_map]

end Conj

section ConjL

variable {K : Type*} [Field K]

lemma ofPS_conjPS (ζ : K) (hζ : ζ ≠ 0) (s : ℕ) (hs : 0 < s) (ρ : PowerSeries K) :
    ofPowerSeries ℤ K (conjPS ζ s ρ) = rot ζ hζ (lsub s hs (ofPowerSeries ℤ K ρ)) := by
  ext m
  rw [rot_coeff, coeff_ofPS]
  split_ifs with hm
  · obtain ⟨m', rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [Int.toNat_natCast, coeff_conjPS, zpow_natCast]
    split_ifs with hd
    · obtain ⟨k, rfl⟩ := hd
      have e : ((s * k : ℕ) : ℤ) = (s : ℤ) * (k : ℤ) := by push_cast; ring
      rw [e, lsub_coeff_mul, coeff_ofPS, if_pos (by positivity), Int.toNat_natCast,
        Nat.mul_div_cancel_left _ hs]
    · rw [lsub_coeff_not_dvd s hs _ _ (fun h ↦ hd (by exact_mod_cast h)), mul_zero]
  · by_cases hd : (s : ℤ) ∣ m
    · obtain ⟨k, rfl⟩ := hd
      rw [lsub_coeff_mul, coeff_ofPS, if_neg (by
        intro hk; exact hm (mul_nonneg (by positivity) hk)), mul_zero]
    · rw [lsub_coeff_not_dvd s hs _ _ hd, mul_zero]

end ConjL

section ConjC

variable {F : Type*} [Field F] [DecidableEq F] {K : Type*} [Field K]

/-- The approximation of `conjPS ζ s ρ` from one of `ρ`. -/
def conjC (ζ : F) (s : ℕ) (y : CPoly F) : CPoly F :=
  (List.range (s * y.length)).map fun m ↦ if s ∣ m then ζ ^ m * y.getD (m / s) 0 else 0

lemma getD_conjC (ζ : F) {s : ℕ} (hs : 0 < s) (y : CPoly F) (m : ℕ) :
    (conjC ζ s y).getD m 0 = if s ∣ m then ζ ^ m * y.getD (m / s) 0 else 0 := by
  by_cases hm : m < s * y.length
  · rw [conjC, List.getD_eq_getElem _ _ (by simpa using hm), List.getElem_map, List.getElem_range]
  · rw [List.getD_eq_default _ _ (by simp [conjC]; omega)]
    split_ifs with hd
    · rw [List.getD_eq_default _ _ (by
        obtain ⟨k, rfl⟩ := hd
        rw [Nat.mul_div_cancel_left _ hs]
        by_contra h; exact hm (by nlinarith)), mul_zero]
    · rfl

lemma thetaT_conjC (ψ : F →+* K) (ζ : F) {s : ℕ} (hs : 0 < s) (y : CPoly F) :
    thetaT ψ (toPoly (conjC ζ s y)) = conjPS (ψ ζ) s (thetaT ψ (toPoly y)) := by
  ext m
  rw [coeff_thetaT, getD_conjC ζ hs, coeff_conjPS, coeff_thetaT]
  split_ifs <;> simp

end ConjC

section Subst

variable {R S : Type*} [CommRing R] [CommRing S]

lemma psSubR_map (f : R →+* S) (e : ℕ) (a : R) (P : R[X]) :
    PowerSeries.map f (psSubR e a P) = psSubR e (f a) (P.map f) := by
  simp only [psSubR, RingHom.comp_apply, coe_compRingHom, Polynomial.coeToPowerSeries.ringHom_apply]
  rw [map_coe_poly, Polynomial.map_comp]
  simp

lemma map_eval_psSubR (f : R →+* S) (e : ℕ) (a : R) (Q : R[X][X]) (ρ : PowerSeries R) :
    PowerSeries.map f ((Q.map (psSubR e a)).eval ρ) =
      ((Q.map (mapRingHom f)).map (psSubR e (f a))).eval (PowerSeries.map f ρ) := by
  rw [eval_map, eval_map, eval₂_map, hom_eval₂]
  congr 1
  refine RingHom.ext fun P ↦ ?_
  simp only [RingHom.comp_apply, coe_mapRingHom]
  exact psSubR_map f e a P

variable {F : Type*} [Field F] [DecidableEq F] {K : Type*} [Field K]

lemma thetaN_eq (ψ : F →+* K) (a : F) (N : ℕ) :
    thetaN ψ a N = (psSubR N (ψ a)).comp (mapRingHom ψ) := by
  refine RingHom.ext fun P ↦ ?_
  simp only [thetaN, RingHom.comp_apply, thetaT_apply, psSubR, coe_compRingHom,
    Polynomial.coeToPowerSeries.ringHom_apply, coe_mapRingHom, Polynomial.map_comp]
  simp

lemma thetaT_bivEval' (ψ : F →+* K) (W : BPoly F) (a : F) (N : ℕ) (Y : CPoly F) :
    thetaT ψ (toPoly (bivEval W (shiftC a N) Y)) =
      (((toB W).map (mapRingHom ψ)).map (psSubR N (ψ a))).eval (thetaT ψ (toPoly Y)) := by
  rw [thetaT_bivEval, thetaN_eq, ← Polynomial.map_map]

/-- Evaluation of an integral model along a lifted approximation. -/
lemma lift_eval {O : Type*} [CommRing O] (f : O →+* K) (ψ : F →+* K) (Q : O[X][X]) (W : BPoly F)
    (hQ : Q.map (mapRingHom f) = (toB W).map (mapRingHom ψ)) (e : ℕ) (αO : O) (a : F)
    (hα : f αO = ψ a) (y₀ : O[X]) (y : CPoly F) (hy : y₀.map f = (toPoly y).map ψ) :
    PowerSeries.map f ((Q.map (psSubR e αO)).eval (y₀ : PowerSeries O)) =
      thetaT ψ (toPoly (bivEval W (shiftC a e) y)) := by
  rw [map_eval_psSubR, hQ, hα, thetaT_bivEval', map_coe_poly, hy, thetaT_apply]

end Subst

section Roots

variable {F : Type*} [Field F] [DecidableEq F] {K : Type*} [Field K]

/-- The equation of the representative. -/
noncomputable abbrev repEq (ψ : F →+* K) (Fc : BPoly F) (a : F) (e : ℕ) :
    Polynomial (PowerSeries K) :=
  ((toB Fc).map (mapRingHom ψ)).map (psSubR e (ψ a))

lemma rootCheck_spec {Fc : BPoly F} {a : F} {e prec : ℕ} {y : CPoly F}
    (h : rootCheck Fc a e prec y = true) :
    ordC (bivEval (derivYB Fc) (shiftC a e) y) < prec ∧
      ordC (bivEval (derivYB Fc) (shiftC a e) y) < (bivEval (derivYB Fc) (shiftC a e) y).length ∧
      ∀ i < ordC (bivEval (derivYB Fc) (shiftC a e) y) + prec,
        (bivEval Fc (shiftC a e) y).getD i 0 = 0 := by
  exact rootCheck_facts h

lemma repEq_deriv (ψ : F →+* K) (Fc : BPoly F) (a : F) (e : ℕ) (y : CPoly F) :
    (derivative (repEq ψ Fc a e)).eval (thetaT ψ (toPoly y)) =
      thetaT ψ (toPoly (bivEval (derivYB Fc) (shiftC a e) y)) := by
  rw [repEq, Polynomial.derivative_map, Polynomial.derivative_map, ← toB_derivYB,
    thetaT_bivEval']

/-- **The representative over a field.** -/
theorem rep_root_field (ψ : F →+* K) {Fc : BPoly F} {a : F} {e prec : ℕ} {y : CPoly F}
    (h : rootCheck Fc a e prec y = true) :
    ∃ ρ : PowerSeries K, (repEq ψ Fc a e).eval ρ = 0 ∧
      (PowerSeries.X : PowerSeries K) ^ prec ∣ ρ - thetaT ψ (toPoly y) := by
  obtain ⟨h1, h2, h3⟩ := rootCheck_spec h
  obtain ⟨hB, hu⟩ := thetaT_ordC ψ _ h2
  obtain ⟨ρ, hρ, hd⟩ := hensel_quant (repEq ψ Fc a e) (thetaT ψ (toPoly y))
    (ordC (bivEval (derivYB Fc) (shiftC a e) y) + prec) _ _
    (by rw [← thetaT_bivEval']; exact X_pow_dvd_thetaT ψ _ _ h3)
    (by rw [repEq_deriv]; exact hB) hu (by omega)
  exact ⟨ρ, hρ, by rwa [Nat.add_sub_cancel_left] at hd⟩

/-- **Uniqueness of the representative.** -/
theorem rep_unique (ψ : F →+* K) {Fc : BPoly F} {a : F} {e prec : ℕ} {y : CPoly F}
    (h : rootCheck Fc a e prec y = true) (ρ ρ' : PowerSeries K) (hρ : (repEq ψ Fc a e).eval ρ = 0)
    (hρ' : (repEq ψ Fc a e).eval ρ' = 0)
    (hd : (PowerSeries.X : PowerSeries K) ^ prec ∣ ρ - thetaT ψ (toPoly y))
    (hd' : (PowerSeries.X : PowerSeries K) ^ prec ∣ ρ' - thetaT ψ (toPoly y)) : ρ = ρ' := by
  obtain ⟨h1, h2, -⟩ := rootCheck_spec h
  obtain ⟨hB, hu⟩ := thetaT_ordC ψ _ h2
  exact hensel_unique (repEq ψ Fc a e) (thetaT ψ (toPoly y)) ρ ρ'
    (ordC (bivEval (derivYB Fc) (shiftC a e) y) + prec) _ _ (by rw [repEq_deriv]; exact hB) hu
    (by omega) hρ hρ' (by rwa [Nat.add_sub_cancel_left]) (by rwa [Nat.add_sub_cancel_left])

end Roots

section Zp

variable {K : Type*} [Field K] [DecidableEq K]
variable {p : ℕ} [hp : Fact p.Prime] (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ)

local notation "ι" => algebraMap ℤ_[p] ℚ_[p]

lemma coeff_eq_zero_of_map {O L : Type*} [CommRing O] [CommRing L] (f : O →+* L)
    (hf : Function.Injective f) (Z : PowerSeries O) (A : ℕ)
    (h : ∀ i < A, PowerSeries.coeff i (PowerSeries.map f Z) = 0) :
    (PowerSeries.X : PowerSeries O) ^ A ∣ Z := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro i hi
  apply hf
  rw [map_zero, ← PowerSeries.coeff_map]
  exact h i hi

/-- **The representative over `ℤ_p`.** -/
theorem rep_root_Zp (Fc : BPoly K) (hokF : ∀ P ∈ Fc, ∀ c ∈ P, R.ok c = true) (a : K)
    (hoka : R.ok a = true) {e prec : ℕ} {y : CPoly K} (hoky : ∀ c ∈ y, R.ok c = true)
    (h : rootCheck Fc a e prec y = true)
    (hu : (bivEval (derivYB (redBL R Fc)) (shiftC (R.red a) e) (y.map R.red)).getD
      (ordC (bivEval (derivYB Fc) (shiftC a e) y)) 0 ≠ 0) :
    ∃ ρO : PowerSeries ℤ_[p],
      ((toB (liftBL R φ hR Fc)).map (psSubR e (zL R φ hR a))).eval ρO = 0 ∧
      (PowerSeries.X : PowerSeries ℤ_[p]) ^ prec ∣
        ρO - ((toPoly (liftL R φ hR y) : ℤ_[p][X]) : PowerSeries ℤ_[p]) := by
  obtain ⟨h1, h2, h3⟩ := rootCheck_spec h
  set FO : ℤ_[p][X][X] := toB (liftBL R φ hR Fc) with hFO
  set αO := zL R φ hR a with hαO
  set y₀ : ℤ_[p][X] := toPoly (liftL R φ hR y) with hy₀
  set B := ordC (bivEval (derivYB Fc) (shiftC a e) y) with hBdef
  have hFι : FO.map (mapRingHom ι) = (toB Fc).map (mapRingHom φ) := toB_liftBL_map R φ hR _ hokF
  have hFz : FO.map (mapRingHom PadicInt.toZMod) = toB (redBL R Fc) := toB_liftBL_red R φ hR _ hokF
  have hαι : ι αO = φ a := zL_map R φ hR hoka
  have hαz : PadicInt.toZMod αO = R.red a := zL_red R φ hR hoka
  have hyι : y₀.map ι = (toPoly y).map φ := toPoly_liftL_map R φ hR _ hoky
  have hyz : y₀.map PadicInt.toZMod = toPoly (y.map R.red) := toPoly_liftL_red R φ hR _ hoky
  have hιi : Function.Injective ι := IsFractionRing.injective ℤ_[p] ℚ_[p]
  set H := FO.map (psSubR e αO) with hH
  -- `T^{B + prec} ∣ H(y₀)`
  have hA : (PowerSeries.X : PowerSeries ℤ_[p]) ^ (B + prec) ∣ H.eval (y₀ : PowerSeries ℤ_[p]) := by
    refine coeff_eq_zero_of_map ι hιi _ _ fun i hi ↦ ?_
    rw [lift_eval ι φ FO Fc hFι e αO a hαι y₀ y hyι, coeff_thetaT, h3 i hi, map_zero]
  -- `H′(y₀) = T^B u`
  have hdQι : (derivative FO).map (mapRingHom ι) = (toB (derivYB Fc)).map (mapRingHom φ) := by
    rw [← Polynomial.derivative_map, hFι, Polynomial.derivative_map, toB_derivYB]
  have hdQz : (derivative FO).map (mapRingHom PadicInt.toZMod) =
      (toB (derivYB (redBL R Fc))).map (mapRingHom (RingHom.id (ZMod p))) := by
    rw [← Polynomial.derivative_map, hFz, toB_derivYB, Polynomial.mapRingHom_id, Polynomial.map_id]
  have hdH : derivative H = (derivative FO).map (psSubR e αO) := by
    rw [hH, Polynomial.derivative_map]
  have hDB : (PowerSeries.X : PowerSeries ℤ_[p]) ^ B ∣ (derivative H).eval (y₀ : PowerSeries ℤ_[p]) := by
    refine coeff_eq_zero_of_map ι hιi _ _ fun i hi ↦ ?_
    rw [hdH, lift_eval ι φ (derivative FO) (derivYB Fc) hdQι e αO a hαι y₀ y hyι, coeff_thetaT,
      getD_lt_ordC _ i hi, map_zero]
  obtain ⟨u, hu'⟩ := hDB
  have hcu : PadicInt.toZMod (PowerSeries.constantCoeff u) ≠ 0 := by
    have e1 : PowerSeries.constantCoeff u =
        PowerSeries.coeff B ((derivative H).eval (y₀ : PowerSeries ℤ_[p])) := by
      rw [hu', PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [e1, ← PowerSeries.coeff_map, hdH, lift_eval PadicInt.toZMod (RingHom.id (ZMod p))
      (derivative FO) (derivYB (redBL R Fc)) hdQz e αO (R.red a) hαz y₀ (y.map R.red)
      (by rw [hyz, Polynomial.map_id]), coeff_thetaT, RingHom.id_apply]
    exact hu
  obtain ⟨ρ, hρ, hd⟩ := hensel_quantR H (y₀ : PowerSeries ℤ_[p]) (B + prec) B u hA hu'
    (Jac.isUnit_of_toZMod hcu) (by omega)
  exact ⟨ρ, hρ, by rwa [Nat.add_sub_cancel_left] at hd⟩

/-- **The integral and the rational representatives agree.** -/
theorem rep_match (Fc : BPoly K) (hokF : ∀ P ∈ Fc, ∀ c ∈ P, R.ok c = true) (a : K)
    (hoka : R.ok a = true) {e prec : ℕ} {y : CPoly K} (hoky : ∀ c ∈ y, R.ok c = true)
    (h : rootCheck Fc a e prec y = true) (ρO : PowerSeries ℤ_[p])
    (hρO : ((toB (liftBL R φ hR Fc)).map (psSubR e (zL R φ hR a))).eval ρO = 0)
    (hdO : (PowerSeries.X : PowerSeries ℤ_[p]) ^ prec ∣
        ρO - ((toPoly (liftL R φ hR y) : ℤ_[p][X]) : PowerSeries ℤ_[p]))
    (ρK : PowerSeries K) (hρK : (repEq (RingHom.id K) Fc a e).eval ρK = 0)
    (hdK : (PowerSeries.X : PowerSeries K) ^ prec ∣ ρK - thetaT (RingHom.id K) (toPoly y)) :
    PowerSeries.map ι ρO = PowerSeries.map φ ρK := by
  have hFι : (toB (liftBL R φ hR Fc)).map (mapRingHom ι) = (toB Fc).map (mapRingHom φ) :=
    toB_liftBL_map R φ hR _ hokF
  have hαι : ι (zL R φ hR a) = φ a := zL_map R φ hR hoka
  have hyι : (toPoly (liftL R φ hR y)).map ι = (toPoly y).map φ := toPoly_liftL_map R φ hR _ hoky
  refine rep_unique φ h _ _ ?_ ?_ ?_ ?_
  · have := congrArg (PowerSeries.map ι) hρO
    rw [map_eval_psSubR, hFι, hαι, map_zero] at this
    exact this
  · have hid : repEq (RingHom.id K) Fc a e = (toB Fc).map (psSubR e a) := by
      simp [repEq, Polynomial.mapRingHom_id]
    have := congrArg (PowerSeries.map φ) hρK
    rw [hid, map_eval_psSubR, map_zero] at this
    exact this
  · have := map_dvd (PowerSeries.map ι) hdO
    rwa [map_pow, PowerSeries.map_X, map_sub, map_coe_poly, hyι, ← thetaT_apply] at this
  · have := map_dvd (PowerSeries.map φ) hdK
    rwa [map_pow, PowerSeries.map_X, map_sub, thetaT_apply, map_coe_poly, Polynomial.map_map,
      RingHom.comp_id, ← thetaT_apply] at this

end Zp

end Curves
