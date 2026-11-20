import RischTragerBronstein.RDE.NestedBoundsExp

/-!
# Values at infinity in an exponential extension

`K = F(t)`, `t′ = b t`. An element `z = P / R` with `deg P ≤ deg R` has a *value at infinity*
`c = [P]_{deg R} / lc R` (`InfVal z c`), independent of the representation (`infVal_unique`).
Values at infinity are additive and commute with the derivation (`infVal_deriv`: the `b`-terms of
the leading coefficients cancel); `(Q′ / Q)(∞) = deg Q · b + lc(Q)′ / lc(Q)`.

An element of positive degree `r` at infinity (`PosDeg z r`: `deg P = deg R + r`) keeps its degree
under the derivation when no `e′ = r b e` has a non-zero solution, and after adding an element
with a value at infinity (`posDeg_deriv`, `posDeg_add`).
-/

open Polynomial

namespace Differential

variable {F K : Type*} [Field F] [CharZero F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

/-- `z` has value `c` at infinity. -/
def InfVal (z : K) (c : F) : Prop :=
  ∃ P R : F[X], R ≠ 0 ∧ P.natDegree ≤ R.natDegree ∧ z = φ P / φ R ∧
    P.coeff R.natDegree = c * R.leadingCoeff

variable (F) in
/-- `z` has degree `r` at infinity. -/
def PosDeg (z : K) (r : ℕ) : Prop :=
  ∃ P R : F[X], R ≠ 0 ∧ P ≠ 0 ∧ P.natDegree = R.natDegree + r ∧ z = φ P / φ R

omit [CharZero F] [Differential F] [Differential F[X]] [Differential K]
  [DifferentialAlgebra F[X] K] in
lemma infVal_of (P R : F[X]) (hR : R ≠ 0) (hPR : P.natDegree ≤ R.natDegree) :
    InfVal (φ P / φ R) (P.coeff R.natDegree / R.leadingCoeff) :=
  ⟨P, R, hR, hPR, rfl, by field_simp [leadingCoeff_ne_zero.mpr hR]⟩

omit [CharZero F] [Differential F] [Differential F[X]] [Differential K]
  [DifferentialAlgebra F[X] K] in
lemma cross_eq_of_div_eq {P R P' R' : F[X]} (hR : R ≠ 0) (hR' : R' ≠ 0)
    (h : φ P / φ R = φ P' / φ R') : P * R' = P' * R := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have h1 : φ R ≠ 0 := (map_ne_zero_iff _ hinj).mpr hR
  have h2 : φ R' ≠ 0 := (map_ne_zero_iff _ hinj).mpr hR'
  apply hinj
  rw [map_mul, map_mul]
  field_simp at h
  linear_combination h

omit [CharZero F] [Differential F] [Differential F[X]] [Differential K]
  [DifferentialAlgebra F[X] K] in
/-- **The value at infinity is well defined.** -/
lemma infVal_unique {z : K} {c c' : F} (h1 : InfVal z c) (h2 : InfVal z c') : c = c' := by
  obtain ⟨P, R, hR, hPR, rfl, hc⟩ := h1
  obtain ⟨P', R', hR', hPR', hz, hc'⟩ := h2
  have hx := cross_eq_of_div_eq hR hR' hz
  have e := congrArg (fun Q : F[X] ↦ Q.coeff (R.natDegree + R'.natDegree)) hx
  rw [coeff_mul_add_eq_of_natDegree_le hPR le_rfl, add_comm,
    coeff_mul_add_eq_of_natDegree_le hPR' le_rfl, hc, hc', ← leadingCoeff, ← leadingCoeff] at e
  have h1 : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR
  have h2 : R'.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR'
  have : (c - c') * (R.leadingCoeff * R'.leadingCoeff) = 0 := by linear_combination e
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (mul_ne_zero h1 h2))

omit [CharZero F] [Differential F] [Differential F[X]] [Differential K]
  [DifferentialAlgebra F[X] K] in
lemma infVal_C (c : F) : InfVal (φ (C c)) c :=
  ⟨C c, 1, one_ne_zero, by simp, by simp, by simp⟩

omit [CharZero F] [Differential F] [Differential F[X]] [Differential K]
  [DifferentialAlgebra F[X] K] in
lemma infVal_add {z w : K} {c d : F} (hz : InfVal z c) (hw : InfVal w d) :
    InfVal (z + w) (c + d) := by
  obtain ⟨P, R, hR, hPR, rfl, hc⟩ := hz
  obtain ⟨P', R', hR', hPR', rfl, hd⟩ := hw
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have h1 : φ R ≠ 0 := (map_ne_zero_iff _ hinj).mpr hR
  have h2 : φ R' ≠ 0 := (map_ne_zero_iff _ hinj).mpr hR'
  refine ⟨P * R' + P' * R, R * R', mul_ne_zero hR hR', ?_, ?_, ?_⟩
  · rw [natDegree_mul hR hR']
    exact (natDegree_add_le _ _).trans (max_le (natDegree_mul_le.trans (by omega))
      (natDegree_mul_le.trans (by omega)))
  · rw [map_add, map_mul, map_mul, map_mul]; field_simp
  · have e1 : (P * R').coeff (R.natDegree + R'.natDegree) = P.coeff R.natDegree * R'.leadingCoeff :=
      coeff_mul_add_eq_of_natDegree_le hPR le_rfl
    have e2 : (P' * R).coeff (R.natDegree + R'.natDegree) = P'.coeff R'.natDegree * R.leadingCoeff := by
      rw [add_comm]; exact coeff_mul_add_eq_of_natDegree_le hPR' le_rfl
    rw [natDegree_mul hR hR', coeff_add, e1, e2, hc, hd, leadingCoeff_mul]
    ring

omit [CharZero F] [Differential F] [Differential F[X]] [Differential K]
  [DifferentialAlgebra F[X] K] in
lemma infVal_neg {z : K} {c : F} (hz : InfVal z c) : InfVal (-z) (-c) := by
  obtain ⟨P, R, hR, hPR, rfl, hc⟩ := hz
  refine ⟨-P, R, hR, by rwa [natDegree_neg], by rw [map_neg, neg_div], by rw [coeff_neg, hc]; ring⟩

omit [CharZero F] [Differential F] [Differential F[X]] [Differential K]
  [DifferentialAlgebra F[X] K] in
lemma infVal_sub {z w : K} {c d : F} (hz : InfVal z c) (hw : InfVal w d) :
    InfVal (z - w) (c - d) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact infVal_add hz (infVal_neg hw)

variable {b : F} (hDe : ∀ P : F[X], P′ = implicitDeriv (C b * X) P)
include hDe

omit [CharZero F] in
lemma natDegree_Dexp_le (P : F[X]) : (implicitDeriv (C b * X) P).natDegree ≤ P.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_implicitDeriv_C_mul_X, coeff_eq_zero_of_natDegree_lt hi]
  simp

omit [CharZero F] in
lemma deriv_div_eq (P R : F[X]) (hR : R ≠ 0) :
    (φ P / φ R)′ = φ (implicitDeriv (C b * X) P * R - P * implicitDeriv (C b * X) R) / φ (R * R) := by
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have h1 : φ R ≠ 0 := (map_ne_zero_iff _ hinj).mpr hR
  rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap, hDe, hDe]
  simp only [smul_eq_mul, map_sub, map_mul]
  field_simp

omit [CharZero F] in
/-- **Values at infinity commute with the derivation.** -/
lemma infVal_deriv {z : K} {c : F} (hz : InfVal z c) : InfVal z′ c′ := by
  obtain ⟨P, R, hR, hPR, rfl, hc⟩ := hz
  rw [deriv_div_eq (K := K) hDe P R hR]
  have hlc : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR
  refine ⟨_, R * R, mul_ne_zero hR hR, ?_, rfl, ?_⟩
  · rw [natDegree_mul hR hR]
    exact (natDegree_sub_le _ _).trans (max_le (natDegree_mul_le.trans
      (add_le_add ((natDegree_Dexp_le hDe P).trans hPR) le_rfl))
      (natDegree_mul_le.trans (add_le_add hPR (natDegree_Dexp_le hDe R))))
  · rw [natDegree_mul hR hR, coeff_sub,
      coeff_mul_add_eq_of_natDegree_le ((natDegree_Dexp_le hDe P).trans hPR) le_rfl,
      coeff_mul_add_eq_of_natDegree_le hPR (natDegree_Dexp_le hDe R), coeff_implicitDeriv_C_mul_X,
      coeff_implicitDeriv_C_mul_X, hc, leadingCoeff_mul, ← leadingCoeff, Derivation.leibniz]
    simp only [smul_eq_mul]
    ring

omit [CharZero F] in
/-- `(Q′ / Q)(∞) = deg Q · b + lc(Q)′ / lc(Q)`. -/
lemma infVal_logDeriv (Q : F[X]) (hQ : Q ≠ 0) :
    InfVal ((φ Q)′ / φ Q) (Q.natDegree * b + Q.leadingCoeff′ / Q.leadingCoeff) := by
  rw [deriv_algebraMap, hDe]
  have hlc : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  refine ⟨_, Q, hQ, natDegree_Dexp_le hDe Q, rfl, ?_⟩
  rw [coeff_implicitDeriv_C_mul_X, ← leadingCoeff]
  field_simp
  ring

omit [CharZero F] in
/-- The degree at infinity is kept by the derivation. -/
lemma posDeg_deriv (hhom : ∀ r : ℕ, r ≠ 0 → ∀ e : F, e ≠ 0 → e′ + r * b * e ≠ 0) {z : K} {r : ℕ}
    (hr : r ≠ 0) (hz : PosDeg F z r) : PosDeg F z′ r := by
  obtain ⟨P, R, hR, hP, hdeg, rfl⟩ := hz
  rw [deriv_div_eq (K := K) hDe P R hR]
  set N := implicitDeriv (C b * X) P * R - P * implicitDeriv (C b * X) R with hN
  have hlcR : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR
  have hlcP : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  -- the top coefficient of `N`
  have htop : N.coeff (P.natDegree + R.natDegree) = R.leadingCoeff ^ 2 *
      ((P.leadingCoeff / R.leadingCoeff)′ + r * b * (P.leadingCoeff / R.leadingCoeff)) := by
    have e1 : (implicitDeriv (C b * X) P * R).coeff (P.natDegree + R.natDegree) =
        (P.leadingCoeff′ + b * (P.natDegree * P.leadingCoeff)) * R.leadingCoeff := by
      rw [coeff_mul_add_eq_of_natDegree_le (natDegree_Dexp_le hDe P) le_rfl,
        coeff_implicitDeriv_C_mul_X]
      rfl
    have e2 : (P * implicitDeriv (C b * X) R).coeff (P.natDegree + R.natDegree) =
        P.leadingCoeff * (R.leadingCoeff′ + b * (R.natDegree * R.leadingCoeff)) := by
      rw [coeff_mul_add_eq_of_natDegree_le le_rfl (natDegree_Dexp_le hDe R),
        coeff_implicitDeriv_C_mul_X]
      rfl
    rw [hN, coeff_sub, e1, e2, Derivation.leibniz_div, hdeg]
    simp only [smul_eq_mul]
    push_cast
    field_simp
    ring
  have hne : N.coeff (P.natDegree + R.natDegree) ≠ 0 := by
    rw [htop]
    exact mul_ne_zero (pow_ne_zero _ hlcR) (hhom r hr _ (div_ne_zero hlcP hlcR))
  have hNdeg : N.natDegree ≤ P.natDegree + R.natDegree := by
    rw [hN]
    exact (natDegree_sub_le _ _).trans (max_le (natDegree_mul_le.trans
      (add_le_add (natDegree_Dexp_le hDe P) le_rfl))
      (natDegree_mul_le.trans (add_le_add le_rfl (natDegree_Dexp_le hDe R))))
  have hN0 : N ≠ 0 := fun h0 ↦ hne (by rw [h0, coeff_zero])
  refine ⟨N, R * R, mul_ne_zero hR hR, hN0, ?_, rfl⟩
  rw [natDegree_mul hR hR]
  have := le_natDegree_of_ne_zero hne
  omega

omit [CharZero F] [Differential F] [Differential F[X]] [Differential K]
  [DifferentialAlgebra F[X] K] hDe in
/-- A positive degree survives the addition of an element with a value at infinity. -/
lemma posDeg_add {z w : K} {r : ℕ} {c : F} (hr : r ≠ 0) (hz : PosDeg F z r) (hw : InfVal w c) :
    PosDeg F (z + w) r := by
  obtain ⟨P, R, hR, hP, hdeg, rfl⟩ := hz
  obtain ⟨P', R', hR', hPR', rfl, -⟩ := hw
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have h1 : φ R ≠ 0 := (map_ne_zero_iff _ hinj).mpr hR
  have h2 : φ R' ≠ 0 := (map_ne_zero_iff _ hinj).mpr hR'
  have hlc : (P * R').coeff (P.natDegree + R'.natDegree) ≠ 0 := by
    rw [coeff_mul_add_eq_of_natDegree_le le_rfl le_rfl, ← leadingCoeff, ← leadingCoeff]
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hP) (leadingCoeff_ne_zero.mpr hR')
  have hsmall : (P' * R).natDegree < P.natDegree + R'.natDegree :=
    lt_of_le_of_lt natDegree_mul_le (by omega)
  have hcoef : (P * R' + P' * R).coeff (P.natDegree + R'.natDegree) ≠ 0 := by
    rw [coeff_add, coeff_eq_zero_of_natDegree_lt hsmall, add_zero]; exact hlc
  have hN0 : P * R' + P' * R ≠ 0 := fun h0 ↦ hcoef (by rw [h0, coeff_zero])
  refine ⟨P * R' + P' * R, R * R', mul_ne_zero hR hR', hN0, ?_, ?_⟩
  · have hle : (P * R' + P' * R).natDegree ≤ P.natDegree + R'.natDegree :=
      (natDegree_add_le _ _).trans (max_le natDegree_mul_le hsmall.le)
    have hge := le_natDegree_of_ne_zero hcoef
    rw [natDegree_mul hR hR']
    omega
  · rw [map_add, map_mul, map_mul, map_mul]; field_simp

omit [CharZero F] [Differential F] [Differential F[X]] [Differential K]
  [DifferentialAlgebra F[X] K] hDe in
/-- An element of positive degree is not balanced in any representation. -/
lemma natDegree_lt_of_posDeg {z : K} {r : ℕ} (hr : r ≠ 0) (hz : PosDeg F z r) {P R : F[X]}
    (hR : R ≠ 0) (hPR : z = φ P / φ R) : R.natDegree < P.natDegree := by
  obtain ⟨P0, R0, hR0, hP0, hdeg, rfl⟩ := hz
  have hx := cross_eq_of_div_eq hR0 hR hPR
  have hP : P ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hx
    exact hP0 ((mul_eq_zero.mp hx).resolve_right hR)
  have := congrArg natDegree hx
  rw [natDegree_mul hP0 hR, natDegree_mul hP hR0] at this
  omega

end Differential
