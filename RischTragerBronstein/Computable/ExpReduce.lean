import RischTragerBronstein.Computable.DerivExp

/-!
# The reduction of an element of `R(x)(exp a)` to a Laurent polynomial plus a proper fraction

`Tower.expReduce a Gn Gd` packages the first steps of `isDerivExp`: `expSplit`, Hermite reduction
and Euclidean division, giving
`Gn / Gd = (gn / gd)′ + Λ / t^k + r / s`
with `s` squarefree, prime to `t`, `deg r < deg s` (`expReduce_spec`).

`laurent_coeff_eqs_exp`: if `z′ = Λ / t^k + r / s` in an exponential extension with normal primes,
then `r = 0`, `z = P / t^k` and the coefficients satisfy `Pⱼ′ + (j - k) η Pⱼ = Λⱼ`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- The reduced data of an element of `R(x)(exp a)`. -/
structure ExpRed (R : Type*) where
  /-- numerator of the rational part -/
  gn : GPoly (GFrac R)
  /-- denominator of the rational part -/
  gd : GPoly (GFrac R)
  /-- numerator of the Laurent part -/
  Λ : GPoly (GFrac R)
  /-- the Laurent part is `Λ / t^k` -/
  k : ℕ
  /-- numerator of the proper part -/
  r : GPoly (GFrac R)
  /-- denominator of the proper part -/
  s : GPoly (GFrac R)

/-- `expSplit`, Hermite reduction, Euclidean division. -/
def expReduce (a : CPoly R) (Gn Gd : GPoly (GFrac R)) : ExpRed R :=
  let sp := GPoly.expSplit (ops₁g R) Gn Gd
  let h := GPoly.hermite (ops₁g R) (expW a) sp.1 sp.2.2.2
  let qr := GPoly.divMod (ops₁g R) h.b h.s
  let Λ := GPoly.add (ops₁g R)
    (GPoly.mul (ops₁g R) qr.1 (GPoly.monomial (ops₁g R) sp.2.2.1 (ops₁g R).one)) sp.2.1
  ⟨h.gn, h.gd, Λ, sp.2.2.1, qr.2, h.s⟩

/-- `isDerivExp` in terms of `expReduce`. -/
theorem isDerivExp_eq (a : CPoly R) (Gn Gd : GPoly (GFrac R)) :
    isDerivExp a Gn Gd =
      (GPoly.isZero (ops₁g R) (expReduce a Gn Gd).r &&
        (List.range ((expReduce a Gn Gd).Λ.length + (expReduce a Gn Gd).k + 1)).all (fun j ↦
          if j = (expReduce a Gn Gd).k then
            CPoly.isZero (CPoly.integrateRational (polyA (expReduce a Gn Gd).Λ j)
              (polyD (expReduce a Gn Gd).Λ j)).r
          else
            (CPoly.rdeRational (CPoly.expCoeffZ a ((j : ℤ) - (expReduce a Gn Gd).k))
              (polyA (expReduce a Gn Gd).Λ j) (polyD (expReduce a Gn Gd).Λ j)).isSome)) := rfl

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

/-- The coefficients of `toPoly Λ` are the values of the `polyA / polyD` codes. -/
lemma coeff_toPoly_polyA (ι : R →+* S) (h0 : ∀ s : S, s′ = 0)
    (hD : ∀ P : S[X], P′ = derivative P) (Λ : GPoly (GFrac R)) (j : ℕ) :
    (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Λ).coeff j =
      CPoly.ev K₁ ι (polyA Λ j, polyD Λ j) := by
  rw [GPoly.coeff_toPoly, polyA, polyD, Prod.mk.eta, ev_normFrac]
  by_cases hj' : j < Λ.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map,
      List.getD_eq_getElem _ _ hj', sem_M₁In]
  · rw [List.getD_eq_default _ _ (by simpa using hj'), List.getD_eq_default _ _ (by omega)]
    simp [CPoly.ev]

/-- The semantics of `expCoeffZ`. -/
lemma ev_expCoeffZ (ι : R →+* S) (a : CPoly R) (m : ℤ) :
    φ ((CPoly.toPoly (CPoly.expCoeffZ a m)).map ι) = (m : K₁) * ηa ι a := by
  rw [CPoly.expCoeffZ, CPoly.toPoly_smul, CPoly.toPoly_deriv, Polynomial.map_mul, map_C, map_mul]
  have hcast : φ (C (ι (m : R))) = (m : K₁) := by simp only [map_intCast]
  rw [hcast]

/-- Monic irreducibles other than `X` are normal. -/
lemma normal_of_hconst (η : K₁) (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C η * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n) :
    ∀ p : K₁[X], p.Monic → Irreducible p → p ≠ X → ¬p ∣ p′ :=
  fun p hm hp hpX hdvd ↦ hpX (by
    have hXp := dvd_X_of_irreducible_special η hD₂ hconst hp hdvd
    exact eq_of_monic_of_associated hm monic_X
      (associated_of_dvd_dvd (irreducible_X.dvd_symm hp hXp) hXp))

/-- `t^r` is not in `S(x)` for `r > 0`: `e′ ≠ r a′ e` for `e ≠ 0`. -/
lemma exp_pow_not_in_base (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P) (a : CPoly R) (ha : CPoly.trim (CPoly.deriv a) ≠ []) :
    ∀ r : ℕ, 0 < r → ∀ e : K₁, e ≠ 0 → e′ - r * ηa ι a * e ≠ 0 := by
  have hA'0 : (derivative (CPoly.toPoly a)).map ι ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff ι.injective, ← CPoly.toPoly_deriv]
    exact fun h ↦ ha ((CPoly.trim_eq_nil_iff _).mpr h)
  intro r hr e he h'
  refine he (rde_homogeneous' (K := K₁) hD (-(C (r : S) * (derivative (CPoly.toPoly a)).map ι))
    (neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr (Nat.cast_ne_zero.mpr hr.ne')) hA'0)) e ?_)
  rw [map_neg, map_mul]
  have : φ (C (r : S)) = (r : K₁) := by
    rw [show (C (r : S) : S[X]) = (r : S[X]) from map_natCast C r, map_natCast]
  rw [this]
  linear_combination h'

set_option maxHeartbeats 800000 in
/-- **The reduction identity.** -/
theorem expReduce_spec (ι : R →+* S) (h0 : ∀ s : S, s′ = 0)
    (hD : ∀ P : S[X], P′ = derivative P) (a : CPoly R)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (Gn Gd : GPoly (GFrac R)) (hGd : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Gd ≠ 0) :
    φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Gn) /
        φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Gd) =
      (φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (expReduce a Gn Gd).gn) /
          φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (expReduce a Gn Gd).gd))′ +
        φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (expReduce a Gn Gd).Λ) /
          φ₂ X ^ (expReduce a Gn Gd).k +
        φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (expReduce a Gn Gd).r) /
          φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (expReduce a Gn Gd).s) ∧
    Squarefree (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (expReduce a Gn Gd).s) ∧
    ¬X ∣ GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (expReduce a Gn Gd).s ∧
    (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (expReduce a Gn Gd).r).degree <
      (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (expReduce a Gn Gd).s).degree := by
  set M₁ := M₁In (K₁ := K₁) ι h0 hD with hM₁
  have hW : GPoly.toPoly M₁ (expW a) = C (ηa ι a) * X := toPoly_expW_In ι h0 hD a
  have hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly M₁ (expW a)) P := fun P ↦ by
    rw [hW]; exact hD₂ P
  have hinj₂ : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  obtain ⟨hsp1, hsp2, hsp3⟩ := GPoly.expSplit_spec M₁ Gn Gd hGd
  simp only [expReduce]
  generalize GPoly.expSplit (ops₁g R) Gn Gd = sp at hsp1 hsp2 hsp3 ⊢
  have hd₁0 : GPoly.toPoly M₁ sp.2.2.2 ≠ 0 := fun h ↦ hGd (by rw [hsp2, h, mul_zero])
  have hnormal : ∀ p : K₁[X], Irreducible p → p ∣ GPoly.toPoly M₁ sp.2.2.2 →
      ¬p ∣ implicitDeriv (GPoly.toPoly M₁ (expW a)) p := fun p hp hpd hsp' ↦
    hsp3 ((dvd_X_of_irreducible_special (ηa ι a) hD₂ hconst hp (by rw [hDW]; exact hsp')).trans hpd)
  have hchk := GPoly.hermiteCheck_hermite M₁ (expW a) sp.1 sp.2.2.2 hnormal hd₁0
  obtain ⟨hid, hsq⟩ := GPoly.hermiteCheck_sound_in (L := K₂) M₁ (expW a) sp.1 sp.2.2.2 _ hDW hchk
  have hsdvd := GPoly.hermite_s_dvd M₁ (expW a) sp.1 sp.2.2.2 hd₁0
  generalize GPoly.hermite (ops₁g R) (expW a) sp.1 sp.2.2.2 = h at hchk hid hsq hsdvd ⊢
  have hS0 : GPoly.toPoly M₁ h.s ≠ 0 := hsq.ne_zero
  have hXS : ¬X ∣ GPoly.toPoly M₁ h.s := fun hX ↦ hsp3 (hX.trans hsdvd)
  have hdm := GPoly.divMod_spec M₁ h.b h.s
  have hdeglt := GPoly.divMod_degree_lt M₁ h.b h.s hS0
  generalize GPoly.divMod (ops₁g R) h.b h.s = qr at hdm hdeglt ⊢
  refine ⟨?_, hsq, hXS, hdeglt⟩
  have hΛpoly : GPoly.toPoly M₁ (GPoly.add (ops₁g R)
      (GPoly.mul (ops₁g R) qr.1 (GPoly.monomial (ops₁g R) sp.2.2.1 (ops₁g R).one)) sp.2.1) =
      GPoly.toPoly M₁ qr.1 * X ^ sp.2.2.1 + GPoly.toPoly M₁ sp.2.1 := by
    rw [GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_monomial, M₁.sem_one, C_1, one_mul]
  have hX0 : φ₂ (X : K₁[X]) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr X_ne_zero
  have hXk : φ₂ (X : K₁[X]) ^ sp.2.2.1 ≠ 0 := pow_ne_zero _ hX0
  have hφS : φ₂ (GPoly.toPoly M₁ h.s) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr hS0
  have hφd₁ : φ₂ (GPoly.toPoly M₁ sp.2.2.2) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr hd₁0
  have hAD : φ₂ (GPoly.toPoly M₁ Gn) / φ₂ (GPoly.toPoly M₁ Gd) =
      φ₂ (GPoly.toPoly M₁ sp.1) / φ₂ (GPoly.toPoly M₁ sp.2.2.2) +
        φ₂ (GPoly.toPoly M₁ sp.2.1) / φ₂ X ^ sp.2.2.1 := by
    rw [← hsp1, hsp2, map_add, map_mul, map_mul, map_mul, map_pow]
    field_simp
  rw [hAD, hid, hdm, hΛpoly]
  simp only [map_add, map_mul, map_pow]
  field_simp
  ring

/-- **Coefficient equations of a Laurent antiderivative.** -/
theorem laurent_coeff_eqs_exp (η : K₁) (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C η * X) P)
    (hnorm : ∀ p : K₁[X], p.Monic → Irreducible p → p ≠ X → ¬p ∣ p′)
    (hη : ∀ r : ℕ, 0 < r → ∀ e : K₁, e ≠ 0 → e′ - r * η * e ≠ 0)
    (Λ r s : K₁[X]) (k : ℕ) (hs : Squarefree s) (hXs : ¬X ∣ s) (hdeg : r.degree < s.degree)
    (z : K₂) (h : z′ = φ₂ Λ / φ₂ X ^ k + φ₂ r / φ₂ s) :
    r = 0 ∧ ∃ P : K₁[X], z = φ₂ P / φ₂ X ^ k ∧
      ∀ j : ℕ, (P.coeff j)′ + ((j : K₁) - k) * η * P.coeff j = Λ.coeff j := by
  have hinj₂ : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  obtain ⟨hr0, P, hP⟩ := deriv_eq_laurent_add_proper_exp (K := K₂) η hD₂ hnorm hη
    Λ r s k hs hXs hdeg z h
  refine ⟨hr0, P, hP, fun j ↦ ?_⟩
  rw [hr0, map_zero, zero_div, add_zero, hP] at h
  have hX0 : φ₂ (X : K₁[X]) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr X_ne_zero
  have hXk : φ₂ (X : K₁[X]) ^ k ≠ 0 := pow_ne_zero _ hX0
  have hXk' : (φ₂ (X : K₁[X]) ^ k)′ = φ₂ (C ((k : K₁) * η)) * φ₂ X ^ k := by
    rw [← map_pow, deriv_algebraMap, hD₂, deriv_X_pow, map_mul, map_pow]
  have hpoly : P′ - C ((k : K₁) * η) * P = Λ := by
    apply hinj₂
    rw [Derivation.leibniz_div, hXk', deriv_algebraMap] at h
    simp only [smul_eq_mul] at h
    simp only [map_sub, map_mul]
    field_simp at h
    have hCm : φ₂ (C ((k : K₁) * η)) = φ₂ (C (k : K₁)) * φ₂ (C η) := by
      rw [C_mul, map_mul]
    rw [hCm] at h
    linear_combination h
  have hcj := congrArg (fun Q : K₁[X] ↦ Q.coeff j) hpoly
  simp only [coeff_sub, coeff_C_mul, hD₂, coeff_implicitDeriv_C_mul_X] at hcj
  linear_combination hcj

end Tower
