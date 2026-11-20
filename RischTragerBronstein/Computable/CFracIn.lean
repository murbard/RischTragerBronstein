import RischTragerBronstein.Computable.CFrac

/-!
# The tower step, modelled in an arbitrary fraction field

`CField.monomial` models `COps.monomial O w` in `RatFunc K`. For completeness statements over
extensions of the constants — where the fields are subfields `F⟮t⟯` of an ambient differential
field rather than `RatFunc` — we need the same model in **any** differential field `L` that is a
fraction field of `K[X]` with `P′ = implicitDeriv W P` on polynomials. This is `CField.monomialIn`:
the same executable operations are correct in every such `L`.
-/

open Polynomial Differential

namespace GFrac

variable {α K L : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)
variable [Field L] [Algebra K[X] L]

/-- Semantics of a fraction code in `L ⊇ K[X]`. -/
noncomputable def semIn (L : Type*) [Field L] [Algebra K[X] L] (q : GFrac α) : L :=
  algebraMap K[X] L (GPoly.toPoly M q.1) / algebraMap K[X] L (GPoly.toPoly M q.2)

end GFrac

namespace CField

variable {α K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

/-- **The tower step, in any fraction-field model.** -/
noncomputable def monomialIn (w : GPoly α) (L : Type*) [Field L] [Differential L]
    [Algebra K[X] L] [IsFractionRing K[X] L] [Differential K[X]] [DifferentialAlgebra K[X] L]
    (hD : ∀ P : K[X], P′ = implicitDeriv (GPoly.toPoly M w) P) :
    CField (GFrac α) L (O.monomial w) :=
  have hinj : Function.Injective (algebraMap K[X] L) := IsFractionRing.injective K[X] L
  have hφ0 : ∀ {P : K[X]}, P ≠ 0 → algebraMap K[X] L P ≠ 0 :=
    fun h ↦ (map_ne_zero_iff _ hinj).mpr h
  { sem := GFrac.semIn M L
    sem_zero := by simp [GFrac.semIn, COps.monomial]
    sem_one := by simp [GFrac.semIn, COps.monomial, M.sem_one]
    sem_add := fun a b ↦ by
      simp only [COps.monomial]
      split_ifs with ha hb
      · have h0 := (GPoly.isZero_iff M _).mp ha
        simp [GFrac.semIn, h0]
      · have h0 := (GPoly.isZero_iff M _).mp hb
        simp [GFrac.semIn, h0]
      · have ha' := hφ0 (fun h ↦ ha ((GPoly.isZero_iff M _).mpr h))
        have hb' := hφ0 (fun h ↦ hb ((GPoly.isZero_iff M _).mpr h))
        simp only [GFrac.semIn, GPoly.toPoly_add, GPoly.toPoly_mul, map_add, map_mul]
        field_simp
    sem_neg := fun a ↦ by
      simp only [COps.monomial, GFrac.semIn, GPoly.toPoly_neg, map_neg, neg_div]
    sem_mul := fun a b ↦ by
      simp only [COps.monomial, GFrac.semIn, GPoly.toPoly_mul, map_mul, mul_div_mul_comm]
    sem_inv := fun a ↦ by
      simp only [COps.monomial, GFrac.semIn, inv_div]
    sem_deriv := fun a ↦ by
      simp only [COps.monomial, GFrac.semIn, GPoly.toPoly_sub, GPoly.toPoly_mul,
        GPoly.toPoly_derivT, map_mul, map_sub]
      by_cases hd : GPoly.toPoly M a.2 = 0
      · simp [hd]
      · have hd' := hφ0 hd
        rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap, hD, hD]
        simp only [smul_eq_mul]
        field_simp
    sem_natCast := fun n ↦ by
      simp only [COps.monomial, GFrac.semIn, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero,
        add_zero, M.sem_natCast, M.sem_one, map_one, div_one]
      rw [← map_natCast (algebraMap K[X] L), ← map_natCast (C : K →+* K[X])]
    isZero_iff := fun a ↦ by
      simp only [COps.monomial, Bool.or_eq_true, GFrac.semIn, div_eq_zero_iff,
        map_eq_zero_iff _ hinj]
      rw [GPoly.isZero_iff M, GPoly.isZero_iff M] }

/-- **Base change of the constants.** A field `R` with decidable equality models itself inside any
extension field `S` with the trivial derivation, along `ι : R →+* S`: the executable operations of
`R` are correct for the semantics `ι`. -/
def ofHom {R S : Type*} [Field R] [DecidableEq R] [Field S] [Differential S]
    (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) : CField R S (COps.ofDecidableField R) where
  sem := ι
  sem_zero := map_zero ι
  sem_one := map_one ι
  sem_add := fun _ _ ↦ map_add ι _ _
  sem_neg := fun _ ↦ map_neg ι _
  sem_mul := fun _ _ ↦ map_mul ι _ _
  sem_inv := fun _ ↦ map_inv₀ ι _
  sem_deriv := fun _ ↦ by
    change ι 0 = _
    rw [map_zero, h0]
  sem_natCast := fun _ ↦ map_natCast ι _
  isZero_iff := fun a ↦ by
    change decide (a = 0) = true ↔ ι a = 0
    rw [decide_eq_true_eq, map_eq_zero]

/-- **Transport of a model along a morphism of differential fields.** -/
def mapHom {α K K' : Type*} [Field K] [Differential K] [Field K'] [Differential K']
    {O : COps α} (M : CField α K O) (j : K →+* K') (hj : ∀ a : K, j a′ = (j a)′) :
    CField α K' O where
  sem := fun a ↦ j (M.sem a)
  sem_zero := by rw [M.sem_zero, map_zero]
  sem_one := by rw [M.sem_one, map_one]
  sem_add := fun a b ↦ by rw [M.sem_add, map_add]
  sem_neg := fun a ↦ by rw [M.sem_neg, map_neg]
  sem_mul := fun a b ↦ by rw [M.sem_mul, map_mul]
  sem_inv := fun a ↦ by rw [M.sem_inv, map_inv₀]
  sem_deriv := fun a ↦ by rw [M.sem_deriv, hj]
  sem_natCast := fun n ↦ by rw [M.sem_natCast, map_natCast]
  isZero_iff := fun a ↦ by rw [M.isZero_iff, map_eq_zero]

end CField

namespace GPoly

variable {α K K' : Type*} [Field K] [Differential K] [Field K'] [Differential K']
  {O : COps α} (M : CField α K O)

/-- Polynomials commute with the transport of a model. -/
lemma toPoly_mapHom (j : K →+* K') (hj : ∀ a : K, j a′ = (j a)′) (p : GPoly α) :
    toPoly (M.mapHom j hj) p = (toPoly M p).map j := by
  induction p with
  | nil => simp
  | cons a p ih =>
    rw [toPoly_cons, toPoly_cons, ih, Polynomial.map_add, Polynomial.map_mul, map_C, map_X]
    rfl

end GPoly

namespace GFrac

variable {α K K' L L' : Type*} [Field K] [Differential K] [Field K'] [Differential K']
  {O : COps α} (M : CField α K O) [Field L] [Algebra K[X] L] [Field L'] [Algebra K'[X] L']

/-- **Semantics commute with base change**: for a morphism `j₁ : K → K'` of differential fields and
a compatible ring map `j₂ : L → L'` of fraction-field models, the value of a fraction code in `L'`
(over the transported model) is the image of its value in `L`. -/
lemma semIn_mapHom (j₁ : K →+* K') (hj : ∀ a : K, j₁ a′ = (j₁ a)′) (j₂ : L →+* L')
    (hcomp : ∀ P : K[X], j₂ (algebraMap K[X] L P) = algebraMap K'[X] L' (P.map j₁))
    (q : GFrac α) :
    semIn (M.mapHom j₁ hj) L' q = j₂ (semIn M L q) := by
  rw [semIn, semIn, GPoly.toPoly_mapHom, GPoly.toPoly_mapHom, map_div₀, hcomp, hcomp]

end GFrac
