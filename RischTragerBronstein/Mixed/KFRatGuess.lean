import RischTragerBronstein.Mixed.KXCertBridgeCKS

/-!
# The rational guess is exact on rational constants

`ratGuess_ratCast`: `ratGuess` recovers `q` from `(q : Kₘ)` (canonical forms of constants:
`canon_const`; normal forms of constants modulo the base curve). Hence `ratOfK` and `ratFr` answer
on rational constants (`ratOfK_ratCast`, `ratFr_const`).
-/

open Polynomial CPoly

namespace Curves.MT

lemma headD_eq_coeff {K : Type*} [CommRing K] (l : CPoly K) : l.headD 0 = (toPoly l).coeff 0 := by
  rw [CPoly.coeff_toPoly]; cases l <;> rfl

lemma headD_eq_coeff' {K : Type*} [CommRing K] (l : CPoly K) (d : K) (hl : toPoly l ≠ 0) :
    l.headD d = (toPoly l).coeff 0 := by
  rw [CPoly.coeff_toPoly]
  cases l with
  | nil => exact absurd (by simp [CPoly.toPoly]) hl
  | cons a t => rfl

/-- **Canonical form of a constant.** -/
lemma canon_const {K : Type*} [Field K] [DecidableEq K] [CharZero K] (c : K) :
    toPoly (RFC.canon (RFC.mk [c] [1] : RFC.RatFuncC K)).1 = Polynomial.C c ∧
      toPoly (RFC.canon (RFC.mk [c] [1] : RFC.RatFuncC K)).2 = 1 := by
  obtain ⟨hQ0, hm, hcop, hv⟩ := RFC.canon_spec (RFC.mk [c] [1] : RFC.RatFuncC K)
  set P := toPoly (RFC.canon (RFC.mk [c] [1] : RFC.RatFuncC K)).1
  set Q := toPoly (RFC.canon (RFC.mk [c] [1] : RFC.RatFuncC K)).2
  rw [RFC.toRF_const] at hv
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hιQ : algebraMap K[X] (RatFunc K) Q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hQ0
  have hPQ : P = Polynomial.C c * Q := by
    apply hinj
    rw [map_mul, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]
    rw [eq_div_iff hιQ] at hv
    exact hv.symm
  have hQu : IsUnit Q := hcop.symm.isUnit_of_dvd' (dvd_refl Q) ⟨Polynomial.C c, by rw [hPQ]; ring⟩
  have hQ1 : Q = 1 := hm.eq_one_of_isUnit hQu
  exact ⟨by rw [hPQ, hQ1, mul_one], hQ1⟩

lemma canon_const_heads {K : Type*} [Field K] [DecidableEq K] [CharZero K] (c : K) :
    (RFC.canon (RFC.mk [c] [1] : RFC.RatFuncC K)).1.headD 0 = c ∧
      (RFC.canon (RFC.mk [c] [1] : RFC.RatFuncC K)).2.headD 1 = 1 := by
  obtain ⟨h1, h2⟩ := canon_const c
  refine ⟨by rw [headD_eq_coeff, h1, coeff_C_zero], ?_⟩
  rw [headD_eq_coeff' _ _ (by rw [h2]; exact one_ne_zero), h2, coeff_one_zero]

variable (Fc : Sup.BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- **`ratGuess` is exact on rational constants.** -/
theorem ratGuess_ratCast : ∀ (m : ℕ) (q : ℚ), ratGuess Fc m (q : KF Fc m) = q
  | 0, q => by
    have hf : 0 < (toPoly (fKc Fc)).degree :=
      Polynomial.degree_pos_of_irreducible (Fact.out : Irreducible (toPoly (fKc Fc)))
    have hl : (toPoly [((q : ℚ) : RFC.RatFuncC ℚ)]).degree < (toPoly (fKc Fc)).degree := by
      refine lt_of_le_of_lt ?_ hf
      simp [CPoly.toPoly, Polynomial.degree_C_le]
    have h0 : ((q : KF Fc 0)).1.headD 0 = ((q : ℚ) : RFC.RatFuncC ℚ) := by
      show (NFK.norm (fKc Fc) [((q : ℚ) : RFC.RatFuncC ℚ)]).headD 0 = _
      rw [headD_eq_coeff, NFK.toPoly_norm_of_lt _ _ hl]
      simp [CPoly.toPoly]
    simp only [ratGuess]
    rw [h0]
    obtain ⟨e1, e2⟩ := canon_const_heads (K := ℚ) q
    have : ((q : ℚ) : RFC.RatFuncC ℚ) = RFC.mk [(q : ℚ)] [1] := rfl
    rw [this, e1, e2, div_one]
  | m + 1, q => by
    simp only [ratGuess]
    have : ((q : ℚ) : KF Fc (m + 1)) = (RFC.mk [((q : ℚ) : KF Fc m)] [1] : RFC.RatFuncC (KF Fc m)) :=
      rfl
    rw [this]
    obtain ⟨e1, e2⟩ := canon_const_heads ((q : ℚ) : KF Fc m)
    rw [e1, e2, ratGuess_ratCast m q, show (1 : KF Fc m) = ((1 : ℚ) : KF Fc m) by simp,
      ratGuess_ratCast m 1, div_one]

lemma ratOfK_ratCast (m : ℕ) (q : ℚ) : ratOfK Fc m (q : KF Fc m) = some q := by
  unfold ratOfK
  rw [ratGuess_ratCast, if_pos rfl]

end Curves.MT
