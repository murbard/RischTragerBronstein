import RischTragerBronstein.Computable.RDEHexp2

/-!
# Two general hyperexponentials: the independence certificate

`t₁′ = η₁ t₁`, `t₂′ = η₂ t₂` with `ηᵢ = Hnᵢ / Hdᵢ ∈ R(x)` arbitrary (certified monomials).
`hexpHexpIndep` certifies that `t₁^m t₂^n ∉ R(x)` for `(m, n) ≠ 0`: the denominators are coprime,
and either the proper part of one of the `ηᵢ` is not a rational multiple of a logarithmic derivative
(`hexpProperCert`) or the polynomial parts are not proportional.

The consequence (`hexpHexpIndep_hom`): `y′ + (c η₂ + z η₁) y = 0` has only the zero solution in
`S(x)` for all integers `c ≠ 0`, `z`, over every constant extension `S ⊇ R`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace CPoly

section Defs

variable {R : Type*} [Field R] [DecidableEq R] [HasRatRoots R]

/-- `gcd (p, q)` is a nonzero constant. -/
def coprimeCheckC (p q : CPoly R) : Bool := (trim (egcd p q).1).length == 1

/-- **The independence certificate** for `t₁′ = (Hn₁ / Hd₁) t₁` and `t₂′ = (Hn₂ / Hd₂) t₂`. -/
def hexpHexpIndep (Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ : CPoly R) : Bool :=
  coprimeCheckC Hd₁ Hd₂ &&
    (hexpProperCert Hn₁ Hd₁ μ₁ || hexpProperCert Hn₂ Hd₂ μ₂ ||
      (linSolve [polyPart Hn₁ Hd₁] (polyPart Hn₂ Hd₂)).isNone)

end Defs

section Spec

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [HasRatRoots R] [HasNatTest R]

theorem coprimeCheckC_sound {p q : CPoly R} (h : coprimeCheckC p q = true) :
    IsCoprime (toPoly p) (toPoly q) := by
  rw [coprimeCheckC, beq_iff_eq] at h
  obtain ⟨γ, hγ⟩ := List.length_eq_one_iff.mp h
  obtain ⟨hγ0, hg⟩ := trim_singleton hγ
  have hbez := egcd_spec p q
  rw [hg] at hbez
  refine ⟨C γ⁻¹ * toPoly (egcd p q).2.1, C γ⁻¹ * toPoly (egcd p q).2.2, ?_⟩
  have : C γ⁻¹ * C γ = (1 : R[X]) := by rw [← C_mul, inv_mul_cancel₀ hγ0, C_1]
  linear_combination C γ⁻¹ * hbez + this

/-- The certificate contains the coprimality of the denominators. -/
lemma hexpHexpIndep_coprime {Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ : CPoly R}
    (hind : hexpHexpIndep Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ = true) :
    IsCoprime (toPoly Hd₁) (toPoly Hd₂) := by
  simp only [hexpHexpIndep, Bool.and_eq_true] at hind
  exact coprimeCheckC_sound hind.1

/-- A proper certificate excludes a constant denominator. -/
lemma not_isUnit_of_hexpProperCert {Gn Gd μ : CPoly R} (hGd0 : toPoly Gd ≠ 0)
    (hprop : hexpProperCert Gn Gd μ = true) : ¬IsUnit (toPoly Gd) := by
  intro hunit
  have hdeg0 : (toPoly Gd).natDegree = 0 := natDegree_eq_zero_of_isUnit hunit
  simp only [hexpProperCert, Bool.or_eq_true, Bool.not_eq_true'] at hprop
  rcases hprop with hsq | hres
  · obtain ⟨p, hp1, hp2⟩ := exists_sq_dvd_of_squarefreeCheck hGd0 hsq
    have := natDegree_le_of_dvd hp2 hGd0
    rw [natDegree_pow, hdeg0] at this
    omega
  · obtain ⟨S₀, G₁, G, q₁, q₂, σ, τ, σ', τ', E1, E2, E3, E4, E5, E6⟩ := simplePart_data Gd hGd0
    obtain ⟨hS0, hSd, -, -, -, -⟩ := Differential.simplePart_props hGd0 E1 E2 E3 E4 E5 E6
    have hSdeg : (toPoly (simplePart Gd)).natDegree = 0 := by
      have := natDegree_le_of_dvd hSd hGd0
      omega
    have hlt := divMod_degree_lt (ratShiftProd (residuePolyW Gn Gd) (HasRatRoots.ratRoots μ))
      (simplePart Gd) hS0
    generalize (divMod (ratShiftProd (residuePolyW Gn Gd) (HasRatRoots.ratRoots μ))
      (simplePart Gd)).2 = Rm at hlt hres
    rw [degree_eq_natDegree hS0, hSdeg] at hlt
    have h0 : toPoly Rm = 0 := by
      by_contra hne
      rw [degree_eq_natDegree hne] at hlt
      exact absurd (WithBot.coe_lt_coe.mp hlt) (Nat.not_lt_zero _)
    rw [(isZero_iff _).mpr h0] at hres
    exact Bool.noConfusion hres

/-- The polynomial part of `η` is nonzero when the proper certificate fails. -/
lemma polyPart_ne_zero_of_cert {Gn Gd μ : CPoly R} (hGn0 : toPoly Gn ≠ 0) (hGd0 : toPoly Gd ≠ 0)
    (hcert : hyperexpMonomialCheck Gn Gd μ = true) (hprop : hexpProperCert Gn Gd μ = false) :
    toPoly (polyPart Gn Gd) ≠ 0 := by
  simp only [hyperexpMonomialCheck, hexpProperCert, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq] at hcert
  simp only [hexpProperCert, Bool.or_eq_false_iff, Bool.not_eq_false'] at hprop
  obtain ⟨-, hdisj⟩ := hcert
  obtain ⟨hsq, hres⟩ := hprop
  have hdeg : (trim Gd).length ≤ (trim Gn).length := by
    rcases hdisj with (h | h) | h
    · rw [hsq] at h; exact absurd h (by decide)
    · exact h
    · rw [hres] at h; exact absurd h (by decide)
  have htGn : trim Gn ≠ [] := fun h0 ↦ hGn0 ((trim_eq_nil_iff _).mp h0)
  have htGd : trim Gd ≠ [] := fun h0 ↦ hGd0 ((trim_eq_nil_iff _).mp h0)
  obtain ⟨hdGn, -, -⟩ := natDegree_toPoly_of_trim_ne_nil htGn
  obtain ⟨hdGd, -, -⟩ := natDegree_toPoly_of_trim_ne_nil htGd
  intro h0
  have hpp := divMod_spec Gn Gd
  have hlt := divMod_degree_lt Gn Gd hGd0
  rw [polyPart] at h0
  rw [h0, zero_mul, zero_add] at hpp
  rw [← hpp] at hlt
  have := natDegree_lt_natDegree hGn0 hlt
  omega

variable {S K : Type*} [Field S] [CharZero S] [Differential S] [Differential S[X]] [Field K]
variable [CharZero K] [Algebra S[X] K] [Differential K[X]]
variable [IsFractionRing S[X] K] [Differential K] [DifferentialAlgebra S[X] K]

local notation "φ" => algebraMap S[X] K

/-- **Local residue transfer.** Let `p` be a simple prime of `Hd` and `D = Hd Q` with `p ∤ Q`.
If `N ≡ z Hn Q (mod p)` then the residue polynomial of `N / D` is `z r₁` modulo `p`, where
`r₁` is the residue polynomial of `Hn / Hd`. -/
lemma residue_local (ι : R →+* S) {N D Hn Hd Q : CPoly R} (hD0 : toPoly D ≠ 0)
    (hHd0 : toPoly Hd ≠ 0) (hDQ : toPoly D = toPoly Hd * toPoly Q) (z : ℤ) {p : S[X]}
    (hp : Irreducible p) (hpHd : p ∣ (toPoly Hd).map ι)
    (hpHd' : ¬p ∣ derivative ((toPoly Hd).map ι)) (hpQ : ¬p ∣ (toPoly Q).map ι)
    (hN : p ∣ (toPoly N).map ι - (z : S[X]) * ((toPoly Hn).map ι * (toPoly Q).map ι)) :
    p ∣ (toPoly (residuePolyW N D)).map ι - (z : S[X]) * (toPoly (residuePolyW Hn Hd)).map ι := by
  obtain ⟨⟨hS0, hcopR⟩, -, -, -, -, hS', -⟩ := simplePart_props_map ι D hD0
  obtain ⟨⟨hS10, hcopR1⟩, -, -, -, -, hS1', -⟩ := simplePart_props_map ι Hd hHd0
  obtain ⟨t, ht⟩ := residuePolyW_bezout N D hS0 hcopR.symm
  obtain ⟨t₁, ht₁⟩ := residuePolyW_bezout Hn Hd hS10 hcopR1.symm
  have hDQ' : (toPoly D).map ι = (toPoly Hd).map ι * (toPoly Q).map ι := by
    rw [hDQ, Polynomial.map_mul]
  -- `p` divides both simple parts
  have hpD : p ∣ (toPoly D).map ι := by rw [hDQ']; exact dvd_mul_of_dvd_left hpHd _
  have hpD' : ¬p ∣ derivative ((toPoly D).map ι) := by
    rw [hDQ', derivative_mul]
    intro h
    have h2 : p ∣ derivative ((toPoly Hd).map ι) * (toPoly Q).map ι := by
      have := dvd_sub h (dvd_mul_of_dvd_left hpHd (derivative ((toPoly Q).map ι)))
      rwa [add_sub_cancel_right] at this
    exact (hp.prime.dvd_or_dvd h2).elim hpHd' hpQ
  have hpS : p ∣ (toPoly (simplePart D)).map ι := hS' p hp hpD hpD'
  have hpS1 : p ∣ (toPoly (simplePart Hd)).map ι := hS1' p hp hpHd hpHd'
  have e := congrArg (Polynomial.map ι) ht
  have e₁ := congrArg (Polynomial.map ι) ht₁
  simp only [Polynomial.map_add, Polynomial.map_mul, ← derivative_map] at e e₁
  rw [hDQ', derivative_mul] at e
  set r := (toPoly (residuePolyW N D)).map ι
  set r₁ := (toPoly (residuePolyW Hn Hd)).map ι
  obtain ⟨M, hM⟩ := hN
  -- `(r - z r₁) Hd′ Q = M - r Hd Q′ - t S + z t₁ S₁ Q`
  have key : (r - (z : S[X]) * r₁) * (derivative ((toPoly Hd).map ι) * (toPoly Q).map ι) =
      p * M - r * (toPoly Hd).map ι * derivative ((toPoly Q).map ι)
        - t.map ι * (toPoly (simplePart D)).map ι
        + (z : S[X]) * t₁.map ι * (toPoly (simplePart Hd)).map ι * (toPoly Q).map ι := by
    linear_combination e - (z : S[X]) * (toPoly Q).map ι * e₁ + hM
  have hdvd : p ∣ (r - (z : S[X]) * r₁) * (derivative ((toPoly Hd).map ι) * (toPoly Q).map ι) := by
    rw [key]
    refine dvd_add (dvd_sub (dvd_sub (dvd_mul_right _ _) ?_) (dvd_mul_of_dvd_right hpS _)) ?_
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpHd _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpS1 _) _
  exact (hp.prime.dvd_or_dvd hdvd).resolve_right fun h ↦
    (hp.prime.dvd_or_dvd h).elim hpHd' hpQ

/-- The polynomial part of `η` is `Hn / Hd` exactly when `Hd` is a constant. -/
lemma toPoly_eq_polyPart_mul_of_isUnit {Gn Gd : CPoly R} (hunit : IsUnit (toPoly Gd)) :
    toPoly Gn = toPoly (polyPart Gn Gd) * toPoly Gd := by
  have hGd0 : toPoly Gd ≠ 0 := hunit.ne_zero
  have hpp := divMod_spec Gn Gd
  have hlt := divMod_degree_lt Gn Gd hGd0
  rw [degree_eq_natDegree hGd0, natDegree_eq_zero_of_isUnit hunit] at hlt
  have h0 : toPoly (divMod Gn Gd).2 = 0 := by
    by_contra hne
    rw [degree_eq_natDegree hne] at hlt
    exact absurd (WithBot.coe_lt_coe.mp hlt) (Nat.not_lt_zero _)
  rw [h0, add_zero] at hpp
  rw [polyPart]; exact hpp

/-- The polynomial part of the combined fraction `(c Hn₂ Hd₁ + z Hn₁ Hd₂) / (Hd₁ Hd₂)` is
`c p₂ + z p₁`; if this is nonzero, the numerator has degree at least that of the denominator. -/
lemma natDegree_combined_le {Hn₁ Hd₁ Hn₂ Hd₂ : CPoly R} (hHd10 : toPoly Hd₁ ≠ 0)
    (hHd20 : toPoly Hd₂ ≠ 0) (c z : R)
    (hne : C c * toPoly (polyPart Hn₂ Hd₂) + C z * toPoly (polyPart Hn₁ Hd₁) ≠ 0) :
    C c * toPoly Hn₂ * toPoly Hd₁ + C z * (toPoly Hn₁ * toPoly Hd₂) ≠ 0 ∧
      (toPoly Hd₁ * toPoly Hd₂).natDegree ≤
        (C c * toPoly Hn₂ * toPoly Hd₁ + C z * (toPoly Hn₁ * toPoly Hd₂)).natDegree := by
  have hpp₁ := divMod_spec Hn₁ Hd₁
  have hpp₂ := divMod_spec Hn₂ Hd₂
  have hlt₁ := divMod_degree_lt Hn₁ Hd₁ hHd10
  have hlt₂ := divMod_degree_lt Hn₂ Hd₂ hHd20
  set q := C c * toPoly (polyPart Hn₂ Hd₂) + C z * toPoly (polyPart Hn₁ Hd₁) with hq
  set D := toPoly Hd₁ * toPoly Hd₂ with hD
  set rem := C c * toPoly (divMod Hn₂ Hd₂).2 * toPoly Hd₁ + C z * (toPoly (divMod Hn₁ Hd₁).2 * toPoly Hd₂)
    with hrem
  have hD0 : D ≠ 0 := mul_ne_zero hHd10 hHd20
  have heq : C c * toPoly Hn₂ * toPoly Hd₁ + C z * (toPoly Hn₁ * toPoly Hd₂) = q * D + rem := by
    rw [hq, hD, hrem, polyPart, polyPart]
    linear_combination (C c * toPoly Hd₁) * hpp₂ + (C z * toPoly Hd₂) * hpp₁
  have hremlt : degree rem < degree (q * D) := by
    rw [degree_mul, hD, degree_mul]
    have h1 : degree (C c * toPoly (divMod Hn₂ Hd₂).2 * toPoly Hd₁) <
        degree (toPoly Hd₁) + degree (toPoly Hd₂) := by
      calc degree (C c * toPoly (divMod Hn₂ Hd₂).2 * toPoly Hd₁)
          ≤ degree (toPoly (divMod Hn₂ Hd₂).2) + degree (toPoly Hd₁) := by
            exact (degree_mul_le _ _).trans (add_le_add_left
              (show degree (C c * toPoly (divMod Hn₂ Hd₂).2) ≤ degree (toPoly (divMod Hn₂ Hd₂).2) by
                rw [← smul_eq_C_mul]; exact degree_smul_le _ _) _)
        _ < degree (toPoly Hd₂) + degree (toPoly Hd₁) := by
            rw [degree_eq_natDegree hHd10, degree_eq_natDegree hHd20]
            have : degree (toPoly (divMod Hn₂ Hd₂).2) < (toPoly Hd₂).natDegree := by
              rwa [← degree_eq_natDegree hHd20]
            exact WithBot.add_lt_add_right (WithBot.coe_ne_bot) this
        _ = degree (toPoly Hd₁) + degree (toPoly Hd₂) := add_comm _ _
    have h2 : degree (C z * (toPoly (divMod Hn₁ Hd₁).2 * toPoly Hd₂)) <
        degree (toPoly Hd₁) + degree (toPoly Hd₂) := by
      calc degree (C z * (toPoly (divMod Hn₁ Hd₁).2 * toPoly Hd₂))
          ≤ degree (toPoly (divMod Hn₁ Hd₁).2) + degree (toPoly Hd₂) :=
            (show degree (C z * (toPoly (divMod Hn₁ Hd₁).2 * toPoly Hd₂)) ≤
                degree (toPoly (divMod Hn₁ Hd₁).2 * toPoly Hd₂) by
              rw [← smul_eq_C_mul]; exact degree_smul_le _ _).trans (degree_mul_le _ _)
        _ < degree (toPoly Hd₁) + degree (toPoly Hd₂) := by
            rw [degree_eq_natDegree hHd10, degree_eq_natDegree hHd20]
            have : degree (toPoly (divMod Hn₁ Hd₁).2) < (toPoly Hd₁).natDegree := by
              rwa [← degree_eq_natDegree hHd10]
            exact WithBot.add_lt_add_right (WithBot.coe_ne_bot) this
    refine lt_of_lt_of_le ((degree_add_le _ _).trans_lt (max_lt h1 h2)) ?_
    exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hne)
  have hdeg : degree (q * D + rem) = degree (q * D) := degree_add_eq_left_of_degree_lt hremlt
  have hne' : q * D + rem ≠ 0 := fun h ↦ by
    rw [h, degree_zero] at hdeg
    exact mul_ne_zero hne hD0 (degree_eq_bot.mp hdeg.symm)
  rw [heq]
  refine ⟨hne', natDegree_le_natDegree ?_⟩
  rw [hdeg, degree_mul (p := q)]
  exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hne)

/-- **The independence certificate gives uniqueness**: `y′ + (c η₂ + z η₁) y = 0` has only the
zero solution in `S(x)`, for all integers `c ≠ 0` and `z`. -/
theorem hexpHexpIndep_hom (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ : CPoly R}
    (hHn10 : toPoly Hn₁ ≠ 0) (hHd10 : toPoly Hd₁ ≠ 0)
    (hcop₁ : IsCoprime (toPoly Hn₁) (toPoly Hd₁)) (hcert₁ : hyperexpMonomialCheck Hn₁ Hd₁ μ₁ = true)
    (hHn20 : toPoly Hn₂ ≠ 0) (hHd20 : toPoly Hd₂ ≠ 0)
    (hcop₂ : IsCoprime (toPoly Hn₂) (toPoly Hd₂)) (hcert₂ : hyperexpMonomialCheck Hn₂ Hd₂ μ₂ = true)
    (hind : hexpHexpIndep Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ = true) (c : ℤ) (hc : c ≠ 0) (z : ℤ) (y : K)
    (h : y′ + (ev K ι (smul (c : R) Hn₂, Hd₂) +
      (z : K) * (φ ((toPoly Hn₁).map ι) / φ ((toPoly Hd₁).map ι))) * y = 0) : y = 0 := by
  have hιinj : Function.Injective ι := ι.injective
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  simp only [hexpHexpIndep, Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none] at hind
  obtain ⟨hcopc, hdisj⟩ := hind
  have hcopHd : IsCoprime (toPoly Hd₁) (toPoly Hd₂) := coprimeCheckC_sound hcopc
  have hcR : (c : R) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hcS : (c : S) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hcK : (c : K) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hφHd₁ : φ ((toPoly Hd₁).map ι) ≠ 0 := map_toPoly_ne_zero ι hHd10
  have hφHd₂ : φ ((toPoly Hd₂).map ι) ≠ 0 := map_toPoly_ne_zero ι hHd20
  have hev₂ : ev K ι (smul (c : R) Hn₂, Hd₂) =
      (c : K) * (φ ((toPoly Hn₂).map ι) / φ ((toPoly Hd₂).map ι)) := by
    rw [ev, toPoly_smul, Polynomial.map_mul, map_C, map_mul, map_intCast, mul_div_assoc]
    congr 1
    rw [C_eq_intCast, map_intCast]
  -- `z = 0`: the monomial certificate of `η₂`
  by_cases hz : z = 0
  · subst hz
    simp only [Int.cast_zero, zero_mul, add_zero, hev₂] at h
    refine hyperexpW_homogeneous (K := K) ι hD hHn20 hHd20 hcop₂ hcert₂ (-c) (neg_ne_zero.mpr hc)
      y ?_
    rw [Int.cast_neg, C_neg, map_neg, C_eq_intCast, map_intCast]
    linear_combination h
  have hzR : (z : R) ≠ 0 := Int.cast_ne_zero.mpr hz
  have hzS : (z : S) ≠ 0 := Int.cast_ne_zero.mpr hz
  have hzK : (z : K) ≠ 0 := Int.cast_ne_zero.mpr hz
  -- the combined fraction `N / D`
  obtain ⟨N, hN⟩ : ∃ N : CPoly R, N = add (mul (smul (c : R) Hn₂) Hd₁) (smul (z : R) (mul Hn₁ Hd₂)) :=
    ⟨_, rfl⟩
  obtain ⟨D, hD'⟩ : ∃ D : CPoly R, D = mul Hd₁ Hd₂ := ⟨_, rfl⟩
  have hNpoly : toPoly N = C (c : R) * toPoly Hn₂ * toPoly Hd₁ + C (z : R) * (toPoly Hn₁ * toPoly Hd₂) := by
    rw [hN, toPoly_add, toPoly_mul, toPoly_smul, toPoly_smul, toPoly_mul]
  have hDpoly : toPoly D = toPoly Hd₁ * toPoly Hd₂ := by rw [hD', toPoly_mul]
  have hD0 : toPoly D ≠ 0 := by rw [hDpoly]; exact mul_ne_zero hHd10 hHd20
  have hDS : (toPoly D).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr hD0
  have hcopG : IsCoprime (toPoly (smul (c : R) Hn₂)) (toPoly Hd₂) := by
    rw [toPoly_smul]
    exact (isCoprime_mul_unit_left_left (isUnit_C.mpr hcR.isUnit) _ _).mpr hcop₂
  have hcopND : IsCoprime (toPoly N) (toPoly D) := by
    rw [hNpoly, hDpoly]
    have hu : IsUnit (C (z : R) : R[X]) := isUnit_C.mpr hzR.isUnit
    have hcG : IsCoprime (C (c : R) * toPoly Hn₂) (toPoly Hd₂) := by
      rw [← toPoly_smul]; exact hcopG
    refine IsCoprime.mul_right ?_ ?_
    · have h1 : IsCoprime (C (z : R) * (toPoly Hn₁ * toPoly Hd₂)) (toPoly Hd₁) :=
        (isCoprime_mul_unit_left_left hu _ _).mpr (hcop₁.mul_left hcopHd.symm)
      have := h1.add_mul_left_left (C (c : R) * toPoly Hn₂)
      rwa [add_comm, mul_comm (toPoly Hd₁)] at this
    · have h1 : IsCoprime (C (c : R) * toPoly Hn₂ * toPoly Hd₁) (toPoly Hd₂) := hcG.mul_left hcopHd
      have := h1.add_mul_left_left (C (z : R) * toPoly Hn₁)
      rwa [show toPoly Hd₂ * (C (z : R) * toPoly Hn₁) = C (z : R) * (toPoly Hn₁ * toPoly Hd₂) by
        ring] at this
  -- the value of the coefficient
  have hval : ev K ι (smul (c : R) Hn₂, Hd₂) +
      (z : K) * (φ ((toPoly Hn₁).map ι) / φ ((toPoly Hd₁).map ι)) =
      φ ((toPoly N).map ι) / φ ((toPoly D).map ι) := by
    rw [hev₂, hNpoly, hDpoly]
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, map_add, map_mul, map_intCast,
      Polynomial.map_intCast, C_eq_intCast]
    field_simp
  -- `N ≠ 0`
  have hN0 : toPoly N ≠ 0 := by
    intro h0
    -- then `Hd₁`, `Hd₂` are units
    have hu₂ : IsUnit (toPoly Hd₂) := by
      have hdvd : toPoly Hd₂ ∣ C (c : R) * toPoly Hn₂ * toPoly Hd₁ :=
        ⟨-(C (z : R) * toPoly Hn₁), by linear_combination h0 - hNpoly⟩
      have hcop' : IsCoprime (C (c : R) * toPoly Hn₂ * toPoly Hd₁) (toPoly Hd₂) := by
        rw [mul_assoc]
        exact (isCoprime_mul_unit_left_left (isUnit_C.mpr hcR.isUnit) _ _).mpr
          (hcop₂.mul_left hcopHd)
      exact hcop'.isUnit_of_dvd' hdvd dvd_rfl
    have hu₁ : IsUnit (toPoly Hd₁) := by
      have hdvd : toPoly Hd₁ ∣ C (z : R) * (toPoly Hn₁ * toPoly Hd₂) :=
        ⟨-(C (c : R) * toPoly Hn₂), by linear_combination h0 - hNpoly⟩
      have hcop' : IsCoprime (C (z : R) * (toPoly Hn₁ * toPoly Hd₂)) (toPoly Hd₁) :=
        (isCoprime_mul_unit_left_left (isUnit_C.mpr hzR.isUnit) _ _).mpr (hcop₁.mul_left hcopHd.symm)
      exact hcop'.isUnit_of_dvd' hdvd dvd_rfl
    rcases hdisj with (hprop | hprop) | hnone
    · exact not_isUnit_of_hexpProperCert hHd10 hprop hu₁
    · exact not_isUnit_of_hexpProperCert hHd20 hprop hu₂
    · -- `c p₂ + z p₁ = 0` contradicts the independence of the polynomial parts
      have e₁ := toPoly_eq_polyPart_mul_of_isUnit (Gn := Hn₁) hu₁
      have e₂ := toPoly_eq_polyPart_mul_of_isUnit (Gn := Hn₂) hu₂
      have hcomb : C (c : R) * toPoly (polyPart Hn₂ Hd₂) + C (z : R) * toPoly (polyPart Hn₁ Hd₁) = 0 := by
        have h1 : (C (c : R) * toPoly (polyPart Hn₂ Hd₂) + C (z : R) * toPoly (polyPart Hn₁ Hd₁)) *
            (toPoly Hd₁ * toPoly Hd₂) = 0 := by
          rw [← h0, hNpoly, e₁, e₂]; ring
        exact (mul_eq_zero.mp h1).resolve_right (mul_ne_zero hHd10 hHd20)
      refine linSolve_complete_map (RingHom.id R) [polyPart Hn₁ Hd₁] (polyPart Hn₂ Hd₂)
        [-(z : R) / c] rfl ?_ hnone
      simp only [lcombS, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons,
        List.sum_nil, add_zero, Polynomial.map_id]
      have hCc : (C (c : R) : R[X]) ≠ 0 := C_ne_zero.mpr hcR
      apply mul_left_cancel₀ hCc
      rw [← mul_assoc, ← C_mul, mul_div_cancel₀ _ hcR, C_neg]
      linear_combination -hcomb
  have hNS : (toPoly N).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr hN0
  -- residue data of `N / D`
  obtain ⟨⟨hS0, hcopR⟩, hS0', hSd', hcop'', hScop', hS', hsqS⟩ := simplePart_props_map ι D hD0
  obtain ⟨t, ht⟩ := residuePolyW_bezout N D hS0 hcopR.symm
  have hrS : (toPoly (simplePart D)).map ι ∣
      (toPoly (residuePolyW N D)).map ι * derivative ((toPoly D).map ι) - (toPoly N).map ι := by
    refine ⟨-(t.map ι), ?_⟩
    have := congrArg (Polynomial.map ι) ht
    simp only [Polynomial.map_add, Polynomial.map_mul, ← derivative_map] at this
    rw [← this]; ring
  obtain ⟨hμ0, q, hq⟩ : toPoly (findMu (simplePart D) (residuePolyW N D)) ≠ 0 ∧ ∃ q : R[X],
      (toPoly (findMu (simplePart D) (residuePolyW N D))).comp (toPoly (residuePolyW N D)) =
        toPoly (simplePart D) * q :=
    muCheck_spec (muCheck_findMu _ _ hS0)
  have hμS : (toPoly (simplePart D)).map ι ∣
      ((toPoly (findMu (simplePart D) (residuePolyW N D))).map ι).comp
        ((toPoly (residuePolyW N D)).map ι) :=
    ⟨q.map ι, by rw [← Polynomial.map_comp, hq, Polynomial.map_mul]⟩
  -- a simple prime of one denominator does not divide the other
  have hnot : ∀ {p : S[X]} {A B : CPoly R}, Irreducible p → IsCoprime (toPoly A) (toPoly B) →
      p ∣ (toPoly A).map ι → ¬p ∣ (toPoly B).map ι := fun {p A B} hp hAB hpA hpB ↦ by
    have := (hAB.map (mapRingHom ι)).isUnit_of_dvd' (by simpa using hpA) (by simpa using hpB)
    exact hp.not_isUnit this
  -- transfer of a non-rational residue of `ηᵢ` to `N / D`
  have transfer : ∀ {Hn Hd μ Q : CPoly R} (w : ℤ), w ≠ 0 → toPoly Hn ≠ 0 → toPoly Hd ≠ 0 →
      hyperexpMonomialCheck Hn Hd μ = true → toPoly D = toPoly Hd * toPoly Q →
      IsCoprime (toPoly Hd) (toPoly Q) →
      (∀ p : S[X], Irreducible p → p ∣ (toPoly Hd).map ι → ¬p ∣ derivative ((toPoly Hd).map ι) →
        p ∣ (toPoly N).map ι - (w : S[X]) * ((toPoly Hn).map ι * (toPoly Q).map ι)) →
      isZero (divMod (ratShiftProd (residuePolyW Hn Hd) (HasRatRoots.ratRoots μ)) (simplePart Hd)).2
        = false →
      ∃ p : S[X], Irreducible p ∧ p ∣ (toPoly (simplePart D)).map ι ∧
        ∀ q : ℚ, ((toPoly (findMu (simplePart D) (residuePolyW N D))).map ι).eval (q : S) = 0 →
          ¬p ∣ (toPoly (residuePolyW N D)).map ι - C (q : S) := by
    intro Hn Hd μ Q w hw hHn0 hHd0 hcert hDQ hcopQ hloc hres
    have hwS : (w : S) ≠ 0 := Int.cast_ne_zero.mpr hw
    simp only [hyperexpMonomialCheck, Bool.and_eq_true] at hcert
    obtain ⟨hμ₁, -⟩ := hcert
    obtain ⟨hμ10, q₁, hq₁⟩ := muCheck_spec hμ₁
    obtain ⟨p, hp, hpS1, hall⟩ := nonrational_residue_alt ι hHd0 hμ10 hres
    obtain ⟨⟨hS10, -⟩, -, hS1d, -, hScop1, -, -⟩ := simplePart_props_map ι Hd hHd0
    have hpHd : p ∣ (toPoly Hd).map ι := hpS1.trans hS1d
    have hpHd' : ¬p ∣ derivative ((toPoly Hd).map ι) := hScop1 p hp hpS1
    have hpQ : ¬p ∣ (toPoly Q).map ι := hnot hp hcopQ hpHd
    have hpD : p ∣ (toPoly D).map ι := by
      rw [hDQ, Polynomial.map_mul]; exact dvd_mul_of_dvd_left hpHd _
    have hpD' : ¬p ∣ derivative ((toPoly D).map ι) := by
      rw [hDQ, Polynomial.map_mul, derivative_mul]
      intro hd
      have h2 : p ∣ derivative ((toPoly Hd).map ι) * (toPoly Q).map ι := by
        have := dvd_sub hd (dvd_mul_of_dvd_left hpHd (derivative ((toPoly Q).map ι)))
        rwa [add_sub_cancel_right] at this
      exact (hp.prime.dvd_or_dvd h2).elim hpHd' hpQ
    refine ⟨p, hp, hS' p hp hpD hpD', fun q hq hdvd ↦ ?_⟩
    have hrw := residue_local ι hD0 hHd0 hDQ w hp hpHd hpHd' hpQ (hloc p hp hpHd hpHd')
    -- `r₁ ≡ q / w (mod p)`
    have hr₁ : p ∣ (toPoly (residuePolyW Hn Hd)).map ι - C ((q : S) / w) := by
      have h1 : p ∣ (w : S[X]) * ((toPoly (residuePolyW Hn Hd)).map ι - C ((q : S) / w)) := by
        have : (w : S[X]) * ((toPoly (residuePolyW Hn Hd)).map ι - C ((q : S) / w)) =
            ((toPoly (residuePolyW N D)).map ι - C (q : S)) -
              ((toPoly (residuePolyW N D)).map ι -
                (w : S[X]) * (toPoly (residuePolyW Hn Hd)).map ι) := by
          rw [mul_sub, ← C_eq_intCast, ← C_mul, mul_div_cancel₀ _ hwS]; ring
        rw [this]
        exact dvd_sub hdvd hrw
      refine (hp.prime.dvd_or_dvd h1).resolve_left fun hpw ↦ ?_
      rw [← C_eq_intCast] at hpw
      exact hp.not_isUnit (isUnit_of_dvd_unit hpw (isUnit_C.mpr hwS.isUnit))
    -- so `q / w` is a rational root of `μ₁`
    have hqw : ((toPoly μ).map ι).eval (((q / w : ℚ) : S)) = 0 := by
      have hmem : p ∣ ((toPoly μ).map ι).comp ((toPoly (residuePolyW Hn Hd)).map ι) :=
        hpS1.trans ⟨q₁.map ι, by rw [← Polynomial.map_comp, hq₁, Polynomial.map_mul]⟩
      have hsub : p ∣ ((toPoly μ).map ι).comp ((toPoly (residuePolyW Hn Hd)).map ι) -
          ((toPoly μ).map ι).comp (C ((q : S) / w)) := by
        have := sub_dvd_eval_sub ((toPoly (residuePolyW Hn Hd)).map ι) (C ((q : S) / w))
          (((toPoly μ).map ι).map C)
        rw [eval_map, eval_map] at this
        exact hr₁.trans this
      have h2 : p ∣ ((toPoly μ).map ι).comp (C ((q : S) / w)) := by
        have := dvd_sub hmem hsub
        rwa [sub_sub_cancel] at this
      rw [comp_C] at h2
      have hcast : (((q / w : ℚ) : S)) = (q : S) / w := by push_cast; rfl
      rw [hcast]
      by_contra hne
      exact hp.not_isUnit (isUnit_of_dvd_unit h2 (isUnit_C.mpr (Ne.isUnit hne)))
    exact hall (q / w) hqw (by
      have : C ((q : S) / w) = C (((q / w : ℚ) : S)) := by push_cast; rfl
      rw [← this]; exact hr₁)
  -- the certificate for `N / D`
  have hcert' : (∃ p : S[X], Irreducible p ∧ p ^ 2 ∣ (toPoly D).map ι) ∨
      ((toPoly D).map ι).natDegree ≤ ((toPoly N).map ι).natDegree ∨
      ∃ p : S[X], Irreducible p ∧ p ∣ (toPoly (simplePart D)).map ι ∧
        ∀ q : ℚ, ((toPoly (findMu (simplePart D) (residuePolyW N D))).map ι).eval (q : S) = 0 →
          ¬p ∣ (toPoly (residuePolyW N D)).map ι - C (q : S) := by
    rcases hdisj with (hprop | hprop) | hnone
    · simp only [hexpProperCert, Bool.or_eq_true, Bool.not_eq_true'] at hprop
      rcases hprop with hsq | hres
      · left
        obtain ⟨p, hp1, hp2⟩ := exists_sq_dvd_of_squarefreeCheck hHd10 hsq
        have hpS : (p.map ι) ^ 2 ∣ (toPoly D).map ι := by
          rw [← Polynomial.map_pow, hDpoly, Polynomial.map_mul]
          exact (Polynomial.map_dvd ι hp2).trans (dvd_mul_right _ _)
        have hpS0 : p.map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr (fun h0 ↦ by
          rw [h0, natDegree_zero] at hp1; omega)
        obtain ⟨p', hp', hp'p⟩ := WfDvdMonoid.exists_irreducible_factor
          (fun hu ↦ by
            have := natDegree_eq_zero_of_isUnit hu
            rw [natDegree_map] at this; omega) hpS0
        exact ⟨p', hp', (pow_dvd_pow_of_dvd hp'p 2).trans hpS⟩
      · right; right
        refine transfer (Hn := Hn₁) (Hd := Hd₁) (μ := μ₁) (Q := Hd₂) z hz hHn10 hHd10 hcert₁
          hDpoly hcopHd (fun p hp hpHd hpHd' ↦ ?_) hres
        have e : (toPoly N).map ι - (z : S[X]) * ((toPoly Hn₁).map ι * (toPoly Hd₂).map ι) =
            (C (c : S) * (toPoly Hn₂).map ι) * (toPoly Hd₁).map ι := by
          rw [hNpoly]
          simp only [Polynomial.map_add, Polynomial.map_mul, map_C, map_intCast]
          rw [Polynomial.map_intCast, Polynomial.map_intCast]
          ring
        rw [e]
        exact dvd_mul_of_dvd_right hpHd _
    · simp only [hexpProperCert, Bool.or_eq_true, Bool.not_eq_true'] at hprop
      rcases hprop with hsq | hres
      · left
        obtain ⟨p, hp1, hp2⟩ := exists_sq_dvd_of_squarefreeCheck hHd20 hsq
        have hpS : (p.map ι) ^ 2 ∣ (toPoly D).map ι := by
          rw [← Polynomial.map_pow, hDpoly, Polynomial.map_mul]
          exact (Polynomial.map_dvd ι hp2).trans (dvd_mul_left _ _)
        have hpS0 : p.map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr (fun h0 ↦ by
          rw [h0, natDegree_zero] at hp1; omega)
        obtain ⟨p', hp', hp'p⟩ := WfDvdMonoid.exists_irreducible_factor
          (fun hu ↦ by
            have := natDegree_eq_zero_of_isUnit hu
            rw [natDegree_map] at this; omega) hpS0
        exact ⟨p', hp', (pow_dvd_pow_of_dvd hp'p 2).trans hpS⟩
      · right; right
        refine transfer (Hn := Hn₂) (Hd := Hd₂) (μ := μ₂) (Q := Hd₁) c hc hHn20 hHd20 hcert₂
          (by rw [hDpoly, mul_comm]) hcopHd.symm (fun p hp hpHd hpHd' ↦ ?_) hres
        have e : (toPoly N).map ι - (c : S[X]) * ((toPoly Hn₂).map ι * (toPoly Hd₁).map ι) =
            (C (z : S) * (toPoly Hn₁).map ι) * (toPoly Hd₂).map ι := by
          rw [hNpoly]
          simp only [Polynomial.map_add, Polynomial.map_mul, map_C, map_intCast]
          rw [Polynomial.map_intCast, Polynomial.map_intCast]
          ring
        rw [e]
        exact dvd_mul_of_dvd_right hpHd _
    · right; left
      have hne : C (c : R) * toPoly (polyPart Hn₂ Hd₂) + C (z : R) * toPoly (polyPart Hn₁ Hd₁) ≠ 0 := by
        intro hcomb
        refine linSolve_complete_map (RingHom.id R) [polyPart Hn₁ Hd₁] (polyPart Hn₂ Hd₂)
          [-(z : R) / c] rfl ?_ hnone
        simp only [lcombS, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons,
          List.sum_nil, add_zero, Polynomial.map_id]
        have hCc : (C (c : R) : R[X]) ≠ 0 := C_ne_zero.mpr hcR
        apply mul_left_cancel₀ hCc
        rw [← mul_assoc, ← C_mul, mul_div_cancel₀ _ hcR, C_neg]
        linear_combination -hcomb
      rw [natDegree_map, natDegree_map, hNpoly, hDpoly]
      exact (natDegree_combined_le hHd10 hHd20 (c : R) (z : R) hne).2
  refine rde_homogeneous_W hD _ _ _ _ _ hNS hDS (hcopND.map (mapRingHom ι)) hSd' hScop' hrS hμS
    hcert' (-1) (by decide) y ?_
  rw [hval] at h
  rw [Int.cast_neg, Int.cast_one, C_neg, C_1, map_neg, map_one]
  linear_combination h

end Spec

end CPoly
