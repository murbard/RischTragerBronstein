import RischTragerBronstein.Mixed.ManinCompute

/-!
# Completeness of the Manin certificates, relative to Manin's kernel theorem

`MKT K` is **Manin's theorem of the kernel** for `y² = x³ + A x + B` over `K(X)` with
`D = d/dX`: if `j` is not constant (`β ≠ 0`), every point in the kernel of the Manin map is torsion.
It is *not proved here*; it enters only as an explicit hypothesis.

`cert_complete`: under `MKT K`, for any two affine points independent modulo torsion, one of the
two executable certificates accepts — the Wronskian certificate `manCert`, or the constant-ratio
certificate `manCertR` with an exact rationality test. Ingredients proved here:
* `const_of_dX`: the constants of `(K(X), d/dX)` are `K` (characteristic `0`);
* a vanishing Wronskian gives a constant ratio `mu Q = c · mu P`;
* the ratio extraction of `manCertR` returns that constant (`reduce` is coprime);
* a rational ratio would give a relation, by `MKT`.

So the Mordell–Weil exception for non-constant curves over `K(X)` is decided by
relation search + Manin certificates **exactly up to `MKT`**.
-/

open Polynomial

namespace Manin

open FFHeight FFHeight.Fr WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)

noncomputable local instance (priority := 2000) intAlgRF' : Algebra ℤ (RatFunc K) :=
  Ring.toIntAlgebra _

open scoped Classical in
/-- **Manin's theorem of the kernel** over `K(X)` (statement only). -/
def MKT (K : Type*) [Field K] [DecidableEq K] [CharZero K] : Prop :=
  ∀ (A B : RatFunc K), 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 → bt dX A B ≠ 0 →
    ∀ R : (sW A B).toAffine.Point, mu dX A B R = 0 → ∃ n : ℕ, n ≠ 0 ∧ n • R = 0

/-- **The constants of `(K(X), d/dX)` are `K`.** -/
theorem const_of_dX (f : RatFunc K) (h : dX f = 0) : ∃ c : K, f = algebraMap K (RatFunc K) c := by
  set p := f.num
  set q := f.denom
  have hq : q ≠ 0 := RatFunc.denom_ne_zero f
  have hf : f = ι p / ι q := (RatFunc.num_div_denom f).symm
  have hq' : ι q ≠ 0 := ι_ne hq
  rw [hf, Derivation.leibniz_div, dX_ι, dX_ι, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h
  have h2 : ι (q * derivative p - p * derivative q) = 0 := by
    rw [map_sub, map_mul, map_mul]
    have := (mul_eq_zero.mp h).resolve_left (by simp [hq'])
    exact this
  have h3 : q * derivative p = p * derivative q := by
    have := (map_eq_zero_iff _ hinj).mp h2
    exact sub_eq_zero.mp this
  have hcop : IsCoprime p q := RatFunc.isCoprime_num_denom f
  -- `q ∣ q'`
  have hdvd : q ∣ derivative q := by
    have : q ∣ p * derivative q := ⟨derivative p, by rw [← h3]⟩
    exact hcop.symm.dvd_of_dvd_mul_left this
  have hq0 : derivative q = 0 := by
    by_contra hne
    have hnd : q.natDegree ≠ 0 := fun h ↦ hne (derivative_eq_zero.mpr h)
    have := natDegree_le_of_dvd hdvd hne
    have hlt := natDegree_derivative_lt hnd
    omega
  have hp0 : derivative p = 0 := by
    rw [hq0, mul_zero] at h3
    exact (mul_eq_zero.mp h3).resolve_left hq
  have ep := eq_C_of_derivative_eq_zero hp0
  have eq := eq_C_of_derivative_eq_zero hq0
  refine ⟨p.coeff 0 / q.coeff 0, ?_⟩
  rw [hf]
  conv_lhs => rw [ep, eq]
  rw [RatFunc.algebraMap_C, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C, map_div₀]

omit [CharZero K] in
theorem headD_eq_coeff (l : CPoly K) (d : K) (hl : l ≠ []) :
    l.headD d = (CPoly.toPoly l).coeff 0 := by
  rw [CPoly.coeff_toPoly]
  cases l with
  | nil => exact absurd rfl hl
  | cons a l => rfl

omit [CharZero K] in
theorem trim_ne_nil {l : CPoly K} (h : CPoly.toPoly l ≠ 0) : CPoly.trim l ≠ [] := by
  intro h0
  apply h
  rw [← CPoly.toPoly_trim, h0]
  rfl

omit [CharZero K] in
/-- **Ratio extraction**: if a normalized fraction has a constant value `c₀`, the head
coefficients of its trimmed numerator and denominator give `c₀`. -/
theorem extract_const (f : Fr K) (hf : ok f) (c₀ : K)
    (hv : val (norm f) = algebraMap K (RatFunc K) c₀) :
    (CPoly.trim (norm f).1).headD 0 / (CPoly.trim (norm f).2).headD 1 = c₀ := by
  have hok : ok (norm f) := ok_norm hf
  have hcop := reduce_coprime f.1 f.2 hf
  change IsCoprime (CPoly.toPoly (norm f).1) (CPoly.toPoly (norm f).2) at hcop
  set a := CPoly.toPoly (norm f).1
  set b := CPoly.toPoly (norm f).2
  have hb : b ≠ 0 := hok
  have hab : a = C c₀ * b := by
    have : ι a / ι b = ι (C c₀) := by rw [RatFunc.algebraMap_C]; exact hv
    rw [div_eq_iff (ι_ne hb), ← map_mul] at this
    exact hinj this
  have hbu : IsUnit b := by
    rw [hab] at hcop
    exact (IsCoprime.isUnit_of_dvd' hcop (dvd_mul_left _ _) dvd_rfl)
  obtain ⟨b0, hb0, hbC⟩ := Polynomial.isUnit_iff.mp hbu
  have hb0' : b0 ≠ 0 := hb0.ne_zero
  have h1 : (CPoly.trim (norm f).1).headD 0 = a.coeff 0 := by
    by_cases ht : CPoly.trim (norm f).1 = []
    · have : a = 0 := by
        show CPoly.toPoly (norm f).1 = 0
        rw [← CPoly.toPoly_trim, ht]; rfl
      rw [ht, this]; simp
    · rw [headD_eq_coeff _ _ ht, CPoly.toPoly_trim]
  have h2 : (CPoly.trim (norm f).2).headD 1 = b.coeff 0 := by
    rw [headD_eq_coeff _ _ (trim_ne_nil hb), CPoly.toPoly_trim]
  rw [h1, h2, hab, ← hbC]
  simp only [coeff_C_mul, coeff_C_zero]
  field_simp

attribute [local irreducible] FFHeight.Fr.ok FFHeight.Fr.val FFHeight.Fr.norm FFHeight.Fr.div
  Manin.muC Manin.dFr FFHeight.Fr.sub FFHeight.Fr.mul FFHeight.Fr.smulC

variable {Ac Bc : CPoly K}

local notation "Aι" => ι (CPoly.toPoly Ac)
local notation "Bι" => ι (CPoly.toPoly Bc)

open scoped Classical in
/-- **Completeness of the Manin certificates, given Manin's kernel theorem.** For affine points
`P, Q` of `y² = x³ + A x + B` over `K(X)` (with `muOK`: `v ≠ 0`, `Δ ≠ 0`, `β ≠ 0`) that are
independent modulo torsion, `manCert` or `manCertR` (with an exact rationality test) accepts. -/
theorem cert_complete (hM : MKT K) {isRat : K → Bool}
    (hRat : ∀ x, isRat x = true ↔ ∃ q : ℚ, x = q) {uP vP uQ vQ : Fr K}
    (h1 : muOK Ac Bc uP vP = true) (h2 : muOK Ac Bc uQ vQ = true)
    (hP : (sW Aι Bι).toAffine.Nonsingular (val uP) (val vP))
    (hQ : (sW Aι Bι).toAffine.Nonsingular (val uQ) (val vQ))
    (hind : ∀ m n : ℤ, ∀ T : (sW Aι Bι).toAffine.Point, (∃ k : ℕ, k ≠ 0 ∧ k • T = 0) →
      m • Point.some _ _ hP = n • Point.some _ _ hQ + T → m = 0 ∧ n = 0) :
    manCert Ac Bc uP vP uQ vQ = true ∨ manCertR Ac Bc isRat uP vP uQ vQ = true := by
  obtain ⟨huP, hvP, hvP0, hZ, hb⟩ := of_muOK h1
  obtain ⟨huQ, hvQ, hvQ0, -, -⟩ := of_muOK h2
  have hΔ : 4 * Aι ^ 3 + 27 * Bι ^ 2 ≠ 0 := by rw [val_ZF] at hZ; exact hZ
  have hβ : bt dX Aι Bι ≠ 0 := by unfold bt; rw [← val_beF hZ]; exact hb
  have okP := ok_muC hZ hb huP hvP0
  have okQ := ok_muC hZ hb huQ hvQ0
  have hmP := val_muC hZ hb huP hvP hvP0 hP
  have hmQ := val_muC hZ hb huQ hvQ hvQ0 hQ
  set P := Point.some _ _ hP
  set Q := Point.some _ _ hQ
  -- `mu P ≠ 0`
  have hP0 : mu dX Aι Bι P ≠ 0 := by
    intro h0
    obtain ⟨n, hn, hnP⟩ := hM _ _ hΔ hβ P h0
    have := (hind n 0 0 ⟨1, one_ne_zero, by simp⟩ (by rw [zero_zsmul, add_zero, natCast_zsmul,
      hnP])).1
    exact hn (by exact_mod_cast this)
  by_cases hW : isZ (wronskC Ac Bc uP vP uQ vQ) = true
  · right
    have okW : ok (wronskC Ac Bc uP vP uQ vQ) := by
      unfold wronskC; exact ok_sub (ok_mul okP (ok_dFr okQ)) (ok_mul okQ (ok_dFr okP))
    have hW0 := (isZ_iff okW).mp hW
    simp only [wronskC] at hW0
    rw [val_sub (ok_mul okP (ok_dFr okQ)) (ok_mul okQ (ok_dFr okP)), val_mul okP (ok_dFr okQ),
      val_mul okQ (ok_dFr okP), val_dFr okQ, val_dFr okP, hmP, hmQ] at hW0
    -- the ratio is constant
    have hd : dX (mu dX Aι Bι Q / mu dX Aι Bι P) = 0 := by
      rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      rw [show mu dX Aι Bι P * dX (mu dX Aι Bι Q) - mu dX Aι Bι Q * dX (mu dX Aι Bι P) = 0 from hW0,
        mul_zero]
    obtain ⟨c₀, hc₀⟩ := const_of_dX _ hd
    have hQc : mu dX Aι Bι Q = algebraMap K (RatFunc K) c₀ * mu dX Aι Bι P := by
      rw [← hc₀]; field_simp
    -- `c₀` is not rational
    have hcq : isRat c₀ = false := by
      rw [Bool.eq_false_iff]
      intro hr
      obtain ⟨q, rfl⟩ := (hRat _).mp hr
      have hrel : mu dX Aι Bι ((q.num : ℤ) • P - (q.den : ℤ) • Q) = 0 := by
        have hm := mu_add dX hΔ ((q.num : ℤ) • P) (-((q.den : ℤ) • Q))
        rw [← sub_eq_add_neg] at hm
        rw [hm, mu_neg]
        have e1 : mu dX Aι Bι ((q.num : ℤ) • P) = (q.num : RatFunc K) * mu dX Aι Bι P := by
          have := map_zsmul (muHom dX hΔ) (q.num : ℤ) P
          rw [zsmul_eq_mul] at this; exact this
        have e2 : mu dX Aι Bι ((q.den : ℤ) • Q) = ((q.den : ℤ) : RatFunc K) * mu dX Aι Bι Q := by
          have := map_zsmul (muHom dX hΔ) (q.den : ℤ) Q
          rw [zsmul_eq_mul] at this; exact this
        rw [e1, e2, hQc, map_ratCast]
        have hden : ((q.den : ℤ) : RatFunc K) ≠ 0 := by exact_mod_cast q.den_nz
        have : ((q : ℚ) : RatFunc K) = (q.num : RatFunc K) / ((q.den : ℤ) : RatFunc K) := by
          push_cast; exact_mod_cast (Rat.num_div_den q).symm
        rw [this]
        field_simp
        ring
      obtain ⟨n, hn, hnR⟩ := hM _ _ hΔ hβ _ hrel
      have hr2 : ((n : ℤ) * q.num) • P = ((n : ℤ) * q.den) • Q + 0 := by
        rw [add_zero, mul_smul, mul_smul, ← sub_eq_zero, ← zsmul_sub, natCast_zsmul]
        exact hnR
      have := (hind _ _ 0 ⟨1, one_ne_zero, by simp⟩ hr2).2
      rcases mul_eq_zero.mp this with h | h
      · exact hn (by exact_mod_cast h)
      · exact q.den_nz (by exact_mod_cast h)
    -- the certificate accepts
    have okD : ok (div (muC Ac Bc uQ vQ) (muC Ac Bc uP vP)) := ok_div okQ (by rw [hmP]; exact hP0)
    have hext := extract_const _ okD c₀ (by
      rw [val_norm okD, val_div okQ okP (by rw [hmP]; exact hP0), hmP, hmQ, hQc]
      field_simp)
    have hP0b : isZ (muC Ac Bc uP vP) = false := by
      rw [Bool.eq_false_iff]; intro h0; exact hP0 (by rw [← hmP]; exact (isZ_iff okP).mp h0)
    have heq : eqb (muC Ac Bc uQ vQ) (smulC c₀ (muC Ac Bc uP vP)) = true := by
      rw [eqb_iff okQ (ok_smulC _ okP), val_smulC, hmP, hmQ, hQc]
    simp only [manCertR, h1, h2, hP0b, hext, hcq, heq, Bool.not_false, Bool.and_self]
  · left
    simp only [manCert, h1, h2, Bool.eq_false_iff.mpr hW, Bool.not_false, Bool.and_self]

end Manin


