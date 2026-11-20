import RischTragerBronstein.Mixed.NKBasisExists
import RischTragerBronstein.Mixed.NKLogDecide

/-!
# The field of code values and the curve over it

`codeVals m h ⊆ L`: the values `sem c` of the codes `c : LC m` of level `m` — a subfield of `Fₘ`
over `ℚ`, closed under the derivation (`derivClosed_codeVals`). Integral bases of a curve with
code coefficients can be taken with coefficients in this field (`nkCurveQ`, the curve
`F(tₘ, θ) = 0` over `codeVals`), so that the search over codes finds them.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

omit [Field Cc] [Algebra Cc L] [Differential Cc] [DifferentialAlgebra Cc L] [CharZero Cc] in
/-- Rationals are constants. -/
lemma deriv_ratCast_ML (q : ℚ) : (q : L)′ = 0 := by
  have hn : ∀ n : ℕ, ((n : L))′ = 0 := fun n ↦ by
    induction n with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, map_add, ih, Derivation.map_one_eq_zero, add_zero]
  have hz : ∀ z : ℤ, ((z : L))′ = 0 := fun z ↦ by
    rcases Int.eq_nat_or_neg z with ⟨k, rfl | rfl⟩
    · exact_mod_cast hn k
    · push_cast; rw [map_neg, hn, neg_zero]
  rw [← Rat.num_div_den q]
  push_cast
  rw [Derivation.leibniz_div, hz, hn]
  simp

/-- The trivial derivation of `ℚ`. -/
@[instance_reducible] noncomputable def diffRat : Differential ℚ := ⟨0⟩

/-- **The values of the codes of level `m`**, a subfield of `L`. -/
def codeSub (m : ℕ) (h : T.Tr m) : Subfield L where
  carrier := {z | ∃ c : LC m, z = (((T.MP m h).sem c : T.F m) : L)}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨(MO Fc ks m).mul a b, by rw [CField.sem_mul]; rfl⟩
  one_mem' := ⟨(MO Fc ks m).one, by rw [CField.sem_one]; rfl⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨(MO Fc ks m).add a b, by rw [CField.sem_add]; rfl⟩
  zero_mem' := ⟨(MO Fc ks m).zero, by rw [CField.sem_zero]; rfl⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨(MO Fc ks m).neg a, by rw [CField.sem_neg]; rfl⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨(MO Fc ks m).inv a, by rw [CField.sem_inv]; rfl⟩

/-- The code values as an intermediate field over `ℚ`. -/
def codeVals (m : ℕ) (h : T.Tr m) : IntermediateField ℚ L :=
  (T.codeSub m h).toIntermediateField fun q ↦
    ⟨mcst Fc ks m q, by rw [T.sem_mcst m h]; simp⟩

lemma mem_codeVals {m : ℕ} {h : T.Tr m} {z : L} :
    z ∈ T.codeVals m h ↔ ∃ c : LC m, z = (((T.MP m h).sem c : T.F m) : L) := Iff.rfl

lemma sem_mem_codeVals (m : ℕ) (h : T.Tr m) (c : LC m) :
    (((T.MP m h).sem c : T.F m) : L) ∈ T.codeVals m h := ⟨c, rfl⟩

lemma codeVals_le (m : ℕ) (h : T.Tr m) (z : L) (hz : z ∈ T.codeVals m h) : z ∈ T.F m := by
  obtain ⟨c, rfl⟩ := hz
  exact ((T.MP m h).sem c).2

/-- The inclusion of the code values into `Fₘ`. -/
def codeIncl (m : ℕ) (h : T.Tr m) : T.codeVals m h →+* T.F m where
  toFun z := ⟨z, T.codeVals_le m h z z.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

lemma coe_codeIncl (m : ℕ) (h : T.Tr m) (z : T.codeVals m h) :
    ((T.codeIncl m h z : T.F m) : L) = (z : L) := rfl

lemma codeIncl_injective (m : ℕ) (h : T.Tr m) : Function.Injective (T.codeIncl m h) :=
  fun a b hab ↦ Subtype.ext (congrArg (fun z : T.F m ↦ (z : L)) hab)

/-- The code value of a code. -/
noncomputable def cv (m : ℕ) (h : T.Tr m) (c : LC m) : T.codeVals m h := ⟨_, T.sem_mem_codeVals m h c⟩

lemma codeIncl_cv (m : ℕ) (h : T.Tr m) (c : LC m) : T.codeIncl m h (T.cv m h c) = (T.MP m h).sem c :=
  rfl

/-- A polynomial code as a polynomial over the code values. -/
noncomputable def codePolyQ (m : ℕ) (h : T.Tr m) : GPoly (LC m) → (T.codeVals m h)[X]
  | [] => 0
  | a :: p => Polynomial.C (T.cv m h a) + X * codePolyQ m h p

lemma map_codePolyQ (m : ℕ) (h : T.Tr m) (p : GPoly (LC m)) :
    (T.codePolyQ m h p).map (T.codeIncl m h) = GPoly.toPoly (T.MP m h) p := by
  induction p with
  | nil => simp [codePolyQ]
  | cons a p ih =>
    simp only [codePolyQ, Polynomial.map_add, Polynomial.map_C, Polynomial.map_mul, Polynomial.map_X,
      ih, GPoly.toPoly, codeIncl_cv]

/-- The curve polynomial over the code values. -/
noncomputable def nkFQ (m : ℕ) (h : T.Tr m) (Pp : List (GPoly (LC m))) : (T.codeVals m h)[X][X] :=
  polyF (fun i ↦ T.codePolyQ m h (Pp.getD i [])) Pp.length

lemma map_nkFQ (m : ℕ) (h : T.Tr m) (Pp : List (GPoly (LC m))) :
    (T.nkFQ m h Pp).map (Polynomial.mapRingHom (T.codeIncl m h)) = T.nkF m h Pp := by
  rw [nkFQ, nkF, polyF, polyF, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, coe_mapRingHom,
    map_codePolyQ]

lemma transcendental_codeVals (m : ℕ) (h : T.Tr m) (htr : Transcendental (T.F m) (T.ts m)) :
    Transcendental (T.codeVals m h) (T.ts m) := by
  intro ⟨p, hp0, hp⟩
  apply htr
  refine ⟨p.map (T.codeIncl m h), (Polynomial.map_ne_zero_iff (T.codeIncl_injective m h)).mpr hp0, ?_⟩
  have e : (algebraMap (T.F m) L).comp (T.codeIncl m h) = algebraMap (T.codeVals m h) L :=
    RingHom.ext fun z ↦ rfl
  rw [aeval_def, eval₂_map, e, ← aeval_def]
  exact hp

lemma nkFQ_coeff (m : ℕ) (h : T.Tr m) (Pp : List (GPoly (LC m))) (i : ℕ) :
    ((T.nkFQ m h Pp).coeff i).map (T.codeIncl m h) = (T.nkF m h Pp).coeff i := by
  rw [← map_nkFQ, Polynomial.coeff_map, coe_mapRingHom]

lemma nkFQ_natDegree_coeff (m : ℕ) (h : T.Tr m) (Pp : List (GPoly (LC m))) (i : ℕ) :
    ((T.nkFQ m h Pp).coeff i).natDegree = ((T.nkF m h Pp).coeff i).natDegree := by
  rw [← T.nkFQ_coeff, natDegree_map_eq_of_injective (T.codeIncl_injective m h)]

/-- **The curve over the code values** (single place at infinity). -/
noncomputable def nkCurveQ (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m)))
    (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0) :
    CurveData (T.codeVals m h1.of_succ) L :=
  have hsp := T.nkShape_spec m h1.of_succ Pp hsh
  CurveData.ofWeights (T.ts m) θ (T.transcendental_codeVals m h1.of_succ (h1 m (by omega)))
    (T.nkFQ m h1.of_succ Pp) (polyF_monic _ _) Pp.length (degG (MO Fc ks m) (Pp.getD 0 []))
    (polyF_natDegree _ _) hsp.1
    (fun h0 ↦ hsp.2.1 (by
      have := T.nkFQ_coeff m h1.of_succ Pp 0
      rw [h0, Polynomial.map_zero] at this
      exact this.symm))
    (by rw [T.nkFQ_natDegree_coeff]; exact hsp.2.2.1)
    (fun i hi hin ↦ by
      rcases hsp.2.2.2.1 i hi hin with h0 | h0
      · left
        have := T.nkFQ_coeff m h1.of_succ Pp i
        have h0' : (T.nkF m h1.of_succ Pp).coeff i = 0 := h0
        rw [h0'] at this
        exact (Polynomial.map_eq_zero_iff (T.codeIncl_injective m h1.of_succ)).mp this
      · right; rw [T.nkFQ_natDegree_coeff]; exact h0)
    hsp.2.2.2.2
    (by
      have e : ((aeval (T.ts m)).toRingHom : (T.codeVals m h1.of_succ)[X] →+* L) =
          ((aeval (T.ts m)).toRingHom : (T.F m)[X] →+* L).comp
            (Polynomial.mapRingHom (T.codeIncl m h1.of_succ)) := by
        refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
        · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp,
            Function.comp_apply, coe_mapRingHom, Polynomial.map_C, aeval_C]
          rfl
        · simp
      rw [e, ← Polynomial.map_map, map_nkFQ]
      exact T.nkF_root m h1.of_succ Pp θ hθ)

section Diff

attribute [local instance] diffRat in
/-- The derivation kills `ℚ` in `L`. -/
lemma diffAlgRat : DifferentialAlgebra ℚ L := ⟨fun q ↦ by
  show (algebraMap ℚ L q)′ = algebraMap ℚ L (0 : ℚ)
  rw [map_zero, eq_ratCast, deriv_ratCast_ML q]⟩

attribute [local instance] diffRat in
/-- **The code values are closed under the derivation.** -/
lemma derivClosed_codeVals (m : ℕ) (h : T.Tr m) :
    letI := diffAlgRat (L := L)
    DerivClosed (T.codeVals m h) := by
  letI := diffAlgRat (L := L)
  rintro _ ⟨c, rfl⟩
  exact ⟨(MO Fc ks m).deriv c, by rw [CField.sem_deriv, T.coe_deriv]⟩

end Diff

end MTower

end Curves.MT
