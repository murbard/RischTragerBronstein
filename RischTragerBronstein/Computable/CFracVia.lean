import RischTragerBronstein.Computable.CFracIn

/-!
# The tower step through an evaluation map

`CField.monomialVia M w φ`: given a model `M` of `O` in `K`, a ring homomorphism
`φ : K[X] →+* L` into a differential field, injective on the polynomials of codes and compatible
with the derivations (`t′ = w(t)`), the operations `O.monomial w` are modelled in `L` by
`(n, d) ↦ φ n / φ d`. With `φ = aeval t` this models a tower inside **one** ambient field (no
fraction-field type needed): the generator `t` only has to be transcendental over the image.
-/

open Polynomial Differential

namespace CField

variable {α K L : Type*} [Field K] [Differential K] [Field L] [Differential L] {O : COps α}
  (M : CField α K O)

/-- **The tower step through `φ`.** -/
noncomputable def monomialVia (w : GPoly α) (φ : K[X] →+* L)
    (hinj : ∀ p : GPoly α, φ (GPoly.toPoly M p) = 0 → GPoly.toPoly M p = 0)
    (hder : ∀ P : K[X], (φ P)′ = φ (implicitDeriv (GPoly.toPoly M w) P)) :
    CField (GFrac α) L (O.monomial w) :=
  have hφ0 : ∀ {p : GPoly α}, GPoly.isZero O p = false → φ (GPoly.toPoly M p) ≠ 0 :=
    fun {p} h h0 ↦ by
      rw [(GPoly.isZero_iff M p).mpr (hinj p h0)] at h; exact Bool.noConfusion h
  { sem := fun q ↦ φ (GPoly.toPoly M q.1) / φ (GPoly.toPoly M q.2)
    sem_zero := by simp [COps.monomial]
    sem_one := by simp [COps.monomial, M.sem_one]
    sem_add := fun a b ↦ by
      simp only [COps.monomial]
      split_ifs with ha hb
      · have h0 := (GPoly.isZero_iff M _).mp ha
        simp [h0]
      · have h0 := (GPoly.isZero_iff M _).mp hb
        simp [h0]
      · have ha' := hφ0 (Bool.eq_false_iff.mpr ha)
        have hb' := hφ0 (Bool.eq_false_iff.mpr hb)
        simp only [GPoly.toPoly_add, GPoly.toPoly_mul, map_add, map_mul]
        field_simp
    sem_neg := fun a ↦ by
      simp only [COps.monomial, GPoly.toPoly_neg, map_neg, neg_div]
    sem_mul := fun a b ↦ by
      simp only [COps.monomial, GPoly.toPoly_mul, map_mul, mul_div_mul_comm]
    sem_inv := fun a ↦ by
      simp only [COps.monomial, inv_div]
    sem_deriv := fun a ↦ by
      simp only [COps.monomial, GPoly.toPoly_sub, GPoly.toPoly_mul, GPoly.toPoly_derivT, map_mul,
        map_sub]
      by_cases hd : φ (GPoly.toPoly M a.2) = 0
      · have hd' := hinj _ hd
        simp [hd']
      · rw [Derivation.leibniz_div, hder, hder]
        simp only [smul_eq_mul]
        field_simp
    sem_natCast := fun n ↦ by
      simp only [COps.monomial, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero,
        M.sem_natCast, M.sem_one, map_one, div_one]
      rw [← map_natCast φ, ← map_natCast (C : K →+* K[X])]
    isZero_iff := fun a ↦ by
      simp only [COps.monomial, Bool.or_eq_true, div_eq_zero_iff]
      constructor
      · rintro (h | h)
        · left; rw [(GPoly.isZero_iff M _).mp h, map_zero]
        · right; rw [(GPoly.isZero_iff M _).mp h, map_zero]
      · rintro (h | h)
        · left; exact (GPoly.isZero_iff M _).mpr (hinj _ h)
        · right; exact (GPoly.isZero_iff M _).mpr (hinj _ h) }

lemma sem_monomialVia (w : GPoly α) (φ : K[X] →+* L)
    (hinj : ∀ p : GPoly α, φ (GPoly.toPoly M p) = 0 → GPoly.toPoly M p = 0)
    (hder : ∀ P : K[X], (φ P)′ = φ (implicitDeriv (GPoly.toPoly M w) P)) (q : GFrac α) :
    (M.monomialVia w φ hinj hder).sem q = φ (GPoly.toPoly M q.1) / φ (GPoly.toPoly M q.2) := rfl

end CField
