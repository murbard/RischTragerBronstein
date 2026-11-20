import RischTragerBronstein.RDE.ExponentialInField
import RischTragerBronstein.Computable.ExpExpBasics
import RischTragerBronstein.Computable.IntegrateExp

/-!
# Is `f ∈ R(x)(exp a)` a derivative?  (in-field integration in an exponential extension)

`Tower.isDerivExp a Gn Gd`: `expSplit`, Hermite reduction, the proper part must vanish, each
Laurent coefficient `j ≠ k` gives a Risch differential equation over `R(x)`, and the coefficient
`j = k` must be a derivative in `R(x)` (no logarithmic part). Complete over every extension of
the constants: `isDerivExp = false` certifies that a new primitive `t₂′ = W ∈ R(x)(exp a)` is a
transcendental monomial with no new constants.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- Is `Gn / Gd ∈ R(x)(exp a)` a derivative in `R(x)(exp a)`? -/
def isDerivExp (a : CPoly R) (Gn Gd : GPoly (GFrac R)) : Bool :=
  let sp := GPoly.expSplit (ops₁g R) Gn Gd
  let h := GPoly.hermite (ops₁g R) (expW a) sp.1 sp.2.2.2
  let qr := GPoly.divMod (ops₁g R) h.b h.s
  let Λ := GPoly.add (ops₁g R)
    (GPoly.mul (ops₁g R) qr.1 (GPoly.monomial (ops₁g R) sp.2.2.1 (ops₁g R).one)) sp.2.1
  GPoly.isZero (ops₁g R) qr.2 &&
    (List.range (Λ.length + sp.2.2.1 + 1)).all (fun j ↦
      if j = sp.2.2.1 then
        CPoly.isZero (CPoly.integrateRational (polyA Λ j) (polyD Λ j)).r
      else
        (CPoly.rdeRational (CPoly.expCoeffZ a ((j : ℤ) - sp.2.2.1)) (polyA Λ j)
          (polyD Λ j)).isSome)

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

set_option maxHeartbeats 1600000 in
/-- **Completeness**: a derivative in `S(x)(exp a)` is recognised. -/
theorem isDerivExp_complete (ι : R →+* S) (h0 : ∀ s : S, s′ = 0)
    (hD : ∀ P : S[X], P′ = derivative P) (a : CPoly R) (ha : CPoly.trim (CPoly.deriv a) ≠ [])
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (Gn Gd : GPoly (GFrac R)) (hGd : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Gd ≠ 0) (z : K₂)
    (hz : z′ = φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Gn) /
        φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Gd)) :
    isDerivExp a Gn Gd = true := by
  set M₁ := M₁In (K₁ := K₁) ι h0 hD with hM₁
  have hW : GPoly.toPoly M₁ (expW a) = C (ηa ι a) * X := toPoly_expW_In ι h0 hD a
  have hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly M₁ (expW a)) P := fun P ↦ by
    rw [hW]; exact hD₂ P
  have hinj₂ : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hA'0 : (derivative (CPoly.toPoly a)).map ι ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff ι.injective, ← CPoly.toPoly_deriv]
    exact fun h ↦ ha ((CPoly.trim_eq_nil_iff _).mpr h)
  -- (1) split
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec M₁ Gn Gd hGd
  simp only [isDerivExp]
  generalize GPoly.expSplit (ops₁g R) Gn Gd = sp at hsp1 hsp2 hsp3 ⊢
  have hd₁0 : GPoly.toPoly M₁ sp.2.2.2 ≠ 0 := fun h ↦ hGd (by rw [hsp2, h, mul_zero])
  have hnormal : ∀ p : K₁[X], Irreducible p → p ∣ GPoly.toPoly M₁ sp.2.2.2 →
      ¬p ∣ implicitDeriv (GPoly.toPoly M₁ (expW a)) p := fun p hp hpd hsp' ↦
    hsp3 ((dvd_X_of_irreducible_special (ηa ι a) hD₂ hconst hp (by rw [hDW]; exact hsp')).trans hpd)
  -- (2) Hermite
  have hchk := GPoly.hermiteCheck_hermite M₁ (expW a) sp.1 sp.2.2.2 hnormal hd₁0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := K₂) M₁ (expW a) sp.1 sp.2.2.2 _ hDW hchk
  have hsdvd := GPoly.hermite_s_dvd M₁ (expW a) sp.1 sp.2.2.2 hd₁0
  generalize GPoly.hermite (ops₁g R) (expW a) sp.1 sp.2.2.2 = h at hchk hid hsq hsdvd ⊢
  set S' := GPoly.toPoly M₁ h.s with hS'
  have hS0 : S' ≠ 0 := hsq.ne_zero
  have hXS : ¬X ∣ S' := fun hX ↦ hsp3 (hX.trans hsdvd)
  have hdm := GPoly.divMod_spec M₁ h.b h.s
  have hdeglt := GPoly.divMod_degree_lt M₁ h.b h.s hS0
  generalize GPoly.divMod (ops₁g R) h.b h.s = qr at hdm hdeglt ⊢
  set k := sp.2.2.1 with hk
  set Λ := GPoly.add (ops₁g R)
    (GPoly.mul (ops₁g R) qr.1 (GPoly.monomial (ops₁g R) k (ops₁g R).one)) sp.2.1 with hΛ
  have hΛpoly : GPoly.toPoly M₁ Λ = GPoly.toPoly M₁ qr.1 * X ^ k + GPoly.toPoly M₁ sp.2.1 := by
    rw [hΛ, GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_monomial, M₁.sem_one, C_1, one_mul]
  -- (3) the derivative of `z - gn / gd`
  have hX0 : φ₂ (X : K₁[X]) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr X_ne_zero
  have hXk : φ₂ (X : K₁[X]) ^ k ≠ 0 := pow_ne_zero _ hX0
  have hφS : φ₂ S' ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr hS0
  have hφd₁ : φ₂ (GPoly.toPoly M₁ sp.2.2.2) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr hd₁0
  have hz₁ : (z - φ₂ (GPoly.toPoly M₁ h.gn) / φ₂ (GPoly.toPoly M₁ h.gd))′ =
      φ₂ (GPoly.toPoly M₁ Λ) / φ₂ X ^ k + φ₂ (GPoly.toPoly M₁ qr.2) / φ₂ S' := by
    have hAD : φ₂ (GPoly.toPoly M₁ Gn) / φ₂ (GPoly.toPoly M₁ Gd) =
        φ₂ (GPoly.toPoly M₁ sp.1) / φ₂ (GPoly.toPoly M₁ sp.2.2.2) +
          φ₂ (GPoly.toPoly M₁ sp.2.1) / φ₂ X ^ k := by
      rw [← hsp1, hsp2, map_add, map_mul, map_mul, map_mul, map_pow]
      field_simp
    rw [map_sub, hz, hAD, hid, hdm, hΛpoly]
    simp only [map_add, map_mul, map_pow]
    field_simp
    ring
  have hnorm' : ∀ p : K₁[X], p.Monic → Irreducible p → p ≠ X → ¬p ∣ p′ :=
    fun p hm hp hpX hdvd ↦ hpX (by
      have hXp := dvd_X_of_irreducible_special (ηa ι a) hD₂ hconst hp hdvd
      exact eq_of_monic_of_associated hm monic_X
        (associated_of_dvd_dvd (irreducible_X.dvd_symm hp hXp) hXp))
  have hη : ∀ r : ℕ, 0 < r → ∀ e : K₁, e ≠ 0 → e′ - r * ηa ι a * e ≠ 0 := fun r hr e he h' ↦
    he (rde_homogeneous' (K := K₁) hD (-(C (r : S) * (derivative (CPoly.toPoly a)).map ι))
      (neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr (Nat.cast_ne_zero.mpr hr.ne')) hA'0)) e (by
        rw [map_neg, map_mul]
        have : φ (C (r : S)) = (r : K₁) := by
          rw [show (C (r : S) : S[X]) = (r : S[X]) from map_natCast C r, map_natCast]
        rw [this]
        linear_combination h'))
  obtain ⟨hrem0, P, hP⟩ := deriv_eq_laurent_add_proper_exp (K := K₂) (ηa ι a) hD₂ hnorm' hη
    _ _ _ k hsq hXS hdeglt _ hz₁
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨(GPoly.isZero_iff M₁ _).mpr hrem0, fun j hj ↦ ?_⟩
  rw [List.mem_range] at hj
  -- (4) coefficient equations of `(P / t^k)′ = Λ / t^k`
  rw [hrem0, map_zero, zero_div, add_zero, hP] at hz₁
  have hXk' : (φ₂ (X : K₁[X]) ^ k)′ = φ₂ (C ((k : K₁) * ηa ι a)) * φ₂ X ^ k := by
    rw [← map_pow, deriv_algebraMap, hD₂, deriv_X_pow, map_mul, map_pow]
  have hpoly : P′ - C ((k : K₁) * ηa ι a) * P = GPoly.toPoly M₁ Λ := by
    apply hinj₂
    rw [Derivation.leibniz_div, hXk', deriv_algebraMap] at hz₁
    simp only [smul_eq_mul] at hz₁
    simp only [map_sub, map_mul]
    field_simp at hz₁
    have hCm : φ₂ (C ((k : K₁) * ηa ι a)) = φ₂ (C (k : K₁)) * φ₂ (C (ηa ι a)) := by
      rw [C_mul, map_mul]
    rw [hCm] at hz₁
    linear_combination hz₁
  have hcoeff : ∀ j, (GPoly.toPoly M₁ Λ).coeff j = CPoly.ev K₁ ι (polyA Λ j, polyD Λ j) := by
    intro j
    rw [GPoly.coeff_toPoly, polyA, polyD, Prod.mk.eta, ev_normFrac]
    by_cases hj' : j < Λ.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map,
        List.getD_eq_getElem _ _ hj', sem_M₁In]
    · rw [List.getD_eq_default _ _ (by simpa using hj'), List.getD_eq_default _ _ (by omega)]
      simp [CPoly.ev]
  have hcj := congrArg (fun Q : K₁[X] ↦ Q.coeff j) hpoly
  simp only [coeff_sub, coeff_C_mul, hD₂, coeff_implicitDeriv_C_mul_X, hcoeff] at hcj
  by_cases hjk : j = k
  · rw [if_pos hjk]
    rw [hjk] at hcj ⊢
    -- `P_k′ = A_k / D_k`: a derivative in `S(x)`
    have hsol : (P.coeff k)′ = CPoly.ev K₁ ι (polyA Λ k, polyD Λ k) := by
      linear_combination hcj
    have hD0 : CPoly.toPoly (polyD Λ k) ≠ 0 := normFrac_den_ne_zero _
    have hc := CPoly.rationalCheck_integrateRational (polyA Λ k) (polyD Λ k) hD0
    obtain ⟨hdec, hsq', hdeg'⟩ := CPoly.rationalCheck_sound_map (K := K₁) ι hD _ _ _ hc
    by_contra hne
    rw [Bool.not_eq_true] at hne
    have hr0 : (CPoly.toPoly (CPoly.integrateRational (polyA Λ k) (polyD Λ k)).r).map ι ≠ 0 := by
      rw [Ne, Polynomial.map_eq_zero_iff ι.injective, ← CPoly.isZero_iff, hne]
      exact Bool.noConfusion
    refine hr0 (eq_zero_of_deriv_eq_proper_fraction (K := K₁) hD _ _ hsq' hdeg'
      (P.coeff k - (φ ((CPoly.toPoly (CPoly.integrateRational (polyA Λ k) (polyD Λ k)).gn).map ι) /
        φ ((CPoly.toPoly (CPoly.integrateRational (polyA Λ k) (polyD Λ k)).gd).map ι) +
        φ ((CPoly.toPoly (CPoly.integrateRational (polyA Λ k) (polyD Λ k)).Q).map ι))) ?_)
    rw [map_sub, hsol, CPoly.ev, hdec]
    ring
  · rw [if_neg hjk]
    have hz' : (((j : ℤ) - k : ℤ) : R) ≠ 0 :=
      Int.cast_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hjk))
    have hg0 : CPoly.toPoly (CPoly.expCoeffZ a ((j : ℤ) - k)) ≠ 0 := by
      rw [CPoly.expCoeffZ, CPoly.toPoly_smul]
      exact mul_ne_zero (C_ne_zero.mpr hz') fun h' ↦ ha ((CPoly.trim_eq_nil_iff _).mpr h')
    by_contra hnone
    rw [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hnone
    refine CPoly.rdeRational_complete (K := K₁) ι hD (normFrac_den_ne_zero _) hg0 hnone
      (P.coeff j) ?_
    rw [CPoly.expCoeffZ, CPoly.toPoly_smul, CPoly.toPoly_deriv, Polynomial.map_mul, map_C, map_mul]
    have hcast : φ (C (ι (((j : ℤ) - k : ℤ) : R))) = (j : K₁) - k := by
      simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast]
    rw [hcast]
    change _ = CPoly.ev K₁ ι (polyA Λ j, polyD Λ j)
    rw [← hcj]
    simp only [ηa]
    ring

end Tower
