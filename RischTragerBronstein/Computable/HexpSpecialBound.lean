import RischTragerBronstein.Computable.HexpBase
import RischTragerBronstein.Computable.RDENonCancelExpBound
import RischTragerBronstein.Computable.RationalComplete
import RischTragerBronstein.RDE.LogDerivRigid

/-!
# The special bound over a general hyperexponential

`t₁′ = η t₁`, `η = Hn / Hd ∈ R(x)` (certified monomial). For the non-cancelling Risch equation
over `R(x)(t₁)` with coefficient `g`, whose `t₁⁰` coefficient is `z a₀′` (`a₀ ∈ R(x)`, `z ∈ ℤ`),
the power of `t₁` in the denominator of a solution is bounded by `specialBoundH`: every
natural `r` with `z a₀′ - r η` a logarithmic derivative in `S(x)` is at most the bound.

Write `η = ηᴴ + b / s` (Hermite: `ηᴴ` a derivative, `s` squarefree, `deg b < deg s`). If
`r η - z a₀′ = e′ / e` then `r ηᴴ - z a₀′` is a derivative whose sum with the proper
simple-pole fraction `r b / s` is a logarithmic derivative, so it vanishes
(`deriv_eq_zero_of_add_proper_eq_logDeriv`): `r ηᴴ = z a₀′`. If `ηᴴ ≠ 0` this determines `r`
(computed by `linSolve` and `natTest`); if `ηᴴ = 0` then `e′ = r η e`, impossible for `r > 0`
by the monomial certificate.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R] [HasNatTest R]

/-- The Hermite part `η - b / s` of `η = Hn / Hd`, as a fraction. -/
def hermPartH (Hn Hd : CPoly R) : CPoly R × CPoly R :=
  (CPoly.sub (CPoly.mul Hn (CPoly.integrateRational Hn Hd).s)
    (CPoly.mul (CPoly.integrateRational Hn Hd).r Hd), CPoly.mul Hd (CPoly.integrateRational Hn Hd).s)

/-- The derivative of a fraction `n / d`. -/
def derivFrac (q : CPoly R × CPoly R) : CPoly R × CPoly R :=
  (CPoly.sub (CPoly.mul (CPoly.deriv q.1) q.2) (CPoly.mul q.1 (CPoly.deriv q.2)), CPoly.mul q.2 q.2)

/-- **The special bound**: `max m r` for the only candidate `r` with `r ηᴴ = z a₀′`. -/
def specialBoundH (Hn Hd : CPoly R) (a₀ : GFrac R) (z : ℤ) (m : ℕ) : ℕ :=
  match CPoly.linSolve [CPoly.mul (hermPartH Hn Hd).1 (derivFrac a₀).2]
      (CPoly.smul (z : R) (CPoly.mul (derivFrac a₀).1 (hermPartH Hn Hd).2)) with
  | some [c] =>
    match HasNatTest.natTest c with
    | some r => max m r
    | none => m
  | _ => m

lemma le_specialBoundH (Hn Hd : CPoly R) (a₀ : GFrac R) (z : ℤ) (m : ℕ) :
    m ≤ specialBoundH Hn Hd a₀ z m := by
  unfold specialBoundH
  split
  · split
    · exact le_max_left _ _
    · exact le_rfl
  · exact le_rfl

end Defs

variable {R S K₁ : Type*} [Field R] [DecidableEq R] [CharZero R] [HasNatTest R]
variable [CPoly.HasRatRoots R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]

local notation "φ" => algebraMap S[X] K₁

/-- The value of a derivative of a fraction. -/
lemma ev_derivFrac (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P) (q : CPoly R × CPoly R)
    (hq : CPoly.toPoly q.2 ≠ 0) : CPoly.ev K₁ ι (derivFrac q) = (CPoly.ev K₁ ι q)′ := by
  have hφ : φ ((CPoly.toPoly q.2).map ι) ≠ 0 := CPoly.map_toPoly_ne_zero ι hq
  simp only [CPoly.ev, derivFrac, CPoly.toPoly_sub, CPoly.toPoly_mul, CPoly.toPoly_deriv,
    Polynomial.map_sub, Polynomial.map_mul, map_sub, map_mul, ← derivative_map]
  rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap, hD, hD]
  simp only [smul_eq_mul]
  field_simp

/-- **No cancellation above the special bound.** -/
theorem specialBoundH_spec (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    (Hn Hd μ : CPoly R) (hHn0 : CPoly.toPoly Hn ≠ 0) (hHd0 : CPoly.toPoly Hd ≠ 0)
    (hcop : IsCoprime (CPoly.toPoly Hn) (CPoly.toPoly Hd))
    (hcert : CPoly.hyperexpMonomialCheck Hn Hd μ = true)
    (a₀ : GFrac R) (ha₀ : CPoly.toPoly a₀.2 ≠ 0) (z : ℤ) (m r : ℕ)
    (hr : specialBoundH Hn Hd a₀ z m < r) (e : K₁) (he : e ≠ 0) :
    e′ + ((z : K₁) * (CPoly.ev K₁ ι a₀)′ - r * ηh ι Hn Hd) * e ≠ 0 := by
  intro h
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K₁
  have hιinj : Function.Injective ι := ι.injective
  have hr0 : 0 < r := lt_of_le_of_lt (Nat.zero_le _) hr
  -- the Hermite data of `η`
  have hchk := CPoly.rationalCheck_integrateRational Hn Hd hHd0
  obtain ⟨I, hI⟩ : ∃ I, I = CPoly.integrateRational Hn Hd := ⟨_, rfl⟩
  rw [← hI] at hchk
  rw [CPoly.rationalCheck, Bool.and_eq_true, decide_eq_true_eq, CPoly.hermiteCheck_iff] at hchk
  obtain ⟨⟨-, hgd0, hs0, hid, hsqc⟩, hlen⟩ := hchk
  have hsq := CPoly.squarefreeCheck_sound hsqc
  have hdeg := CPoly.degree_lt_of_trim_length_lt hlen
  simp only [CPoly.toPoly_add, CPoly.toPoly_mul, CPoly.toPoly_deriv] at hid
  set m' := fun P : R[X] ↦ P.map ι with hm'
  have hφgd : φ ((CPoly.toPoly I.gd).map ι) ≠ 0 := CPoly.map_toPoly_ne_zero ι hgd0
  have hφs : φ ((CPoly.toPoly I.s).map ι) ≠ 0 := CPoly.map_toPoly_ne_zero ι hs0
  have hφHd : φ ((CPoly.toPoly Hd).map ι) ≠ 0 := CPoly.map_toPoly_ne_zero ι hHd0
  set G : K₁ := φ ((CPoly.toPoly I.gn).map ι) / φ ((CPoly.toPoly I.gd).map ι) +
    φ ((CPoly.toPoly I.Q).map ι) with hG
  have hG' : G′ = ηh ι Hn Hd - φ ((CPoly.toPoly I.r).map ι) / φ ((CPoly.toPoly I.s).map ι) := by
    have hidS := congrArg (fun P : R[X] ↦ φ (P.map ι)) hid
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, map_mul, map_add,
      map_sub, ← derivative_map] at hidS
    rw [hG, map_add, Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap, deriv_algebraMap,
      hD, hD, hD, ηh]
    simp only [smul_eq_mul]
    field_simp
    linear_combination -hidS
  -- `r G - z a₀` has vanishing derivative
  set W : K₁ := (r : K₁) * G - (z : K₁) * CPoly.ev K₁ ι a₀ with hW
  have hlog : logDeriv e = r * ηh ι Hn Hd - (z : K₁) * (CPoly.ev K₁ ι a₀)′ := by
    rw [logDeriv, div_eq_iff he]
    linear_combination h
  have hW' : W′ + φ (C (r : S) * (CPoly.toPoly I.r).map ι) / φ ((CPoly.toPoly I.s).map ι) =
      logDeriv e := by
    rw [hW, map_sub, Derivation.leibniz, Derivation.leibniz, hG', Derivation.map_natCast,
      Derivation.map_intCast, hlog, map_mul, C_eq_natCast, map_natCast]
    simp only [smul_eq_mul, zero_mul, add_zero]
    ring
  have hsqS : Squarefree ((CPoly.toPoly I.s).map ι) :=
    ((PerfectField.separable_iff_squarefree.mpr hsq).map).squarefree
  have hdegS : (C (r : S) * (CPoly.toPoly I.r).map ι).degree < ((CPoly.toPoly I.s).map ι).degree := by
    refine lt_of_le_of_lt (show degree (C (r : S) * (CPoly.toPoly I.r).map ι) ≤
        degree ((CPoly.toPoly I.r).map ι) by rw [← smul_eq_C_mul]; exact degree_smul_le _ _) ?_
    rw [degree_map, degree_map]; exact hdeg
  have hW0 := deriv_eq_zero_of_add_proper_eq_logDeriv hD _ _ hsqS hdegS W e he hW'
  have hkey : (r : K₁) * (ηh ι Hn Hd - φ ((CPoly.toPoly I.r).map ι) /
      φ ((CPoly.toPoly I.s).map ι)) = (z : K₁) * (CPoly.ev K₁ ι a₀)′ := by
    rw [hW, map_sub, Derivation.leibniz, Derivation.leibniz, hG', Derivation.map_natCast,
      Derivation.map_intCast] at hW0
    simp only [smul_eq_mul, zero_mul, add_zero] at hW0
    linear_combination hW0
  set ηH : K₁ := ηh ι Hn Hd - φ ((CPoly.toPoly I.r).map ι) / φ ((CPoly.toPoly I.s).map ι)
    with hηH
  by_cases hH0 : ηH = 0
  · -- no Hermite part: `e′ = r η e`, excluded by the monomial certificate
    rw [hH0, mul_zero] at hkey
    refine he (CPoly.hyperexpW_homogeneous (K := K₁) ι hD hHn0 hHd0 hcop hcert (r : ℤ)
      (by exact_mod_cast hr0.ne') e ?_)
    rw [C_eq_intCast, map_intCast, Int.cast_natCast]
    change e′ = (r : K₁) * ηh ι Hn Hd * e
    linear_combination h - e * hkey.symm
  · -- the Hermite part determines `r`
    have hevH : CPoly.ev K₁ ι (hermPartH Hn Hd) = ηH := by
      simp only [CPoly.ev, hermPartH, ← hI, CPoly.toPoly_sub, CPoly.toPoly_mul, Polynomial.map_sub,
        Polynomial.map_mul, map_sub, map_mul, hηH, ηh]
      field_simp
    have hda0 : CPoly.toPoly (derivFrac a₀).2 ≠ 0 := by
      simp only [derivFrac, CPoly.toPoly_mul]; exact mul_ne_zero ha₀ ha₀
    have hevD := ev_derivFrac (K₁ := K₁) ι hD a₀ ha₀
    have hD₁0' : CPoly.toPoly (hermPartH Hn Hd).2 ≠ 0 := by
      simp only [hermPartH, ← hI, CPoly.toPoly_mul]; exact mul_ne_zero hHd0 (by exact hs0)
    have hφD₁' : φ ((CPoly.toPoly (hermPartH Hn Hd).2).map ι) ≠ 0 := CPoly.map_toPoly_ne_zero ι hD₁0'
    have hφD₂' : φ ((CPoly.toPoly (derivFrac a₀).2).map ι) ≠ 0 := CPoly.map_toPoly_ne_zero ι hda0
    rw [← hevH, ← hevD, CPoly.ev, CPoly.ev] at hkey
    field_simp at hkey
    set N₁ := (hermPartH Hn Hd).1
    set D₁ := (hermPartH Hn Hd).2
    set N₂ := (derivFrac a₀).1
    set D₂ := (derivFrac a₀).2
    have hD₁0 : CPoly.toPoly D₁ ≠ 0 := hD₁0'
    have hφD₁ : φ ((CPoly.toPoly D₁).map ι) ≠ 0 := CPoly.map_toPoly_ne_zero ι hD₁0
    have hφD₂ : φ ((CPoly.toPoly D₂).map ι) ≠ 0 := CPoly.map_toPoly_ne_zero ι hda0
    have hN₁0 : CPoly.toPoly N₁ ≠ 0 := fun h0 ↦ hH0 (by
      rw [← hevH, CPoly.ev]; change φ ((CPoly.toPoly N₁).map ι) / _ = _
      rw [h0, Polynomial.map_zero, map_zero, zero_div])
    have hv0 : CPoly.toPoly (CPoly.mul N₁ D₂) ≠ 0 := by
      rw [CPoly.toPoly_mul]; exact mul_ne_zero hN₁0 hda0
    -- the cross-multiplied identity over `S`
    have hcross : C (r : S) * (CPoly.toPoly (CPoly.mul N₁ D₂)).map ι =
        (CPoly.toPoly (CPoly.smul (z : R) (CPoly.mul N₂ D₁))).map ι := by
      apply hinj
      simp only [CPoly.toPoly_mul, CPoly.toPoly_smul, Polynomial.map_mul, map_C, map_mul,
        map_intCast, C_eq_natCast, C_eq_intCast, map_natCast, Polynomial.map_intCast]
      linear_combination hkey
    have hne := CPoly.linSolve_complete_map ι [CPoly.mul N₁ D₂]
      (CPoly.smul (z : R) (CPoly.mul N₂ D₁)) [(r : S)] rfl (by
        simp only [CPoly.lcombS, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons,
          List.sum_nil, add_zero]
        exact hcross)
    obtain ⟨cs, hcs⟩ := Option.ne_none_iff_exists'.mp hne
    obtain ⟨hlen1, hlc⟩ := CPoly.linSolve_sound _ _ cs hcs
    obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := List.length_eq_one_iff.mp hlen1
    simp only [CPoly.lcomb, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons,
      List.sum_nil, add_zero] at hlc
    have hcr : c = (r : R) := by
      apply hιinj
      have h1 := congrArg (Polynomial.map ι) hlc
      rw [Polynomial.map_mul, map_C, ← hcross] at h1
      have hvS : (CPoly.toPoly (CPoly.mul N₁ D₂)).map ι ≠ 0 :=
        (Polynomial.map_ne_zero_iff hιinj).mpr hv0
      have := mul_right_cancel₀ hvS h1
      rw [C_inj] at this
      rw [this, map_natCast]
    have hnat : HasNatTest.natTest c = some r := (HasNatTest.natTest_spec _ _).mpr hcr
    have hb : specialBoundH Hn Hd a₀ z m = max m r := by
      unfold specialBoundH
      rw [hcs]
      simp only [hnat]
    rw [hb] at hr
    omega

end Tower
