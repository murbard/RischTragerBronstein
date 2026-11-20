import RischTragerBronstein.Mixed.NKSplitGauge
import RischTragerBronstein.Mixed.NKEisGeo
import RischTragerBronstein.Mixed.NKCodeField

/-!
# Curves split at infinity: the code check

`splitShapeC Pp s γs`: the coefficients `aᵢ` of `θⁿ + ∑ aᵢ θⁱ` have degree `≤ (n − i) s` in `t`, the
leading polynomial is `∏ₖ (Z − γₖ)` and the codes `γₖ` have distinct values (`splitShape_spec`).
With an Eisenstein certificate, `nkCurveQE` is the curve over the code values.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}

section Codes

variable (Fc ks)

/-- The leading polynomial on codes: `[a₀]_{ns}, [a₁]_{(n−1)s}, …, 1`. -/
def leadPolyC (m : ℕ) (Pp : List (GPoly (LC m))) (s : ℕ) : GPoly (LC m) :=
  ((List.range Pp.length).map fun i ↦ (Pp.getD i []).getD (s * (Pp.length - i)) (MO Fc ks m).zero) ++
    [(MO Fc ks m).one]

/-- `∏ₖ (Z − γₖ)` on codes. -/
def prodXG (m : ℕ) (γs : List (LC m)) : GPoly (LC m) :=
  γs.foldr (fun g acc ↦ GPoly.mul (MO Fc ks m) [(MO Fc ks m).neg g, (MO Fc ks m).one] acc)
    [(MO Fc ks m).one]

/-- **The split shape check.** -/
def splitShapeC (m : ℕ) (Pp : List (GPoly (LC m))) (s : ℕ) (γs : List (LC m)) : Bool :=
  let O := MO Fc ks m
  let n := Pp.length
  decide (0 < n) && decide (γs.length = n) &&
  ((List.range n).all fun i ↦ (List.range (Pp.getD i []).length).all fun k ↦
    decide (k ≤ s * (n - i)) || O.isZero ((Pp.getD i []).getD k O.zero)) &&
  GPoly.isZero O (GPoly.sub O (leadPolyC Fc ks m Pp s) (prodXG Fc ks m γs)) &&
  ((List.range n).all fun k ↦ (List.range n).all fun l ↦
    decide (k = l) || !O.isZero (O.add (γs.getD k O.zero) (O.neg (γs.getD l O.zero))))

end Codes

universe u

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma toPoly_prodXG (m : ℕ) (h : T.Tr m) (γs : List (LC m)) :
    GPoly.toPoly (T.MP m h) (prodXG Fc ks m γs) =
      (γs.map fun g ↦ X - Polynomial.C ((T.MP m h).sem g)).prod := by
  induction γs with
  | nil => simp [prodXG, GPoly.toPoly, (T.MP m h).sem_one]
  | cons g γs ih =>
    rw [prodXG, List.foldr_cons, GPoly.toPoly_mul, ← prodXG, ih, List.map_cons, List.prod_cons]
    congr 1
    simp [GPoly.toPoly, (T.MP m h).sem_neg, (T.MP m h).sem_one, sub_eq_add_neg]
    ring

/-- **The meaning of the split shape check.** -/
lemma splitShape_spec (m : ℕ) (h : T.Tr m) (Pp : List (GPoly (LC m))) (s : ℕ) (γs : List (LC m))
    (hsh : splitShapeC Fc ks m Pp s γs = true) :
    0 < Pp.length ∧ γs.length = Pp.length ∧
    (∀ i < (T.nkF m h Pp).natDegree, ((T.nkF m h Pp).coeff i).natDegree ≤
      s * ((T.nkF m h Pp).natDegree - i)) ∧
    leadPoly s (T.nkF m h Pp) =
      ∏ k : Fin Pp.length, (X - Polynomial.C ((T.MP m h).sem (γs.getD k (MO Fc ks m).zero))) ∧
    Function.Injective fun k : Fin Pp.length ↦ (T.MP m h).sem (γs.getD k (MO Fc ks m).zero) := by
  classical
  unfold splitShapeC at hsh
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true'] at hsh
  obtain ⟨⟨⟨⟨hn0, hlen⟩, hdeg⟩, hlead⟩, hdist⟩ := hsh
  have hFn : (T.nkF m h Pp).natDegree = Pp.length := polyF_natDegree _ _
  refine ⟨hn0, hlen, fun i hi ↦ ?_, ?_, ?_⟩
  · rw [hFn] at hi ⊢
    rw [nkF, polyF_coeff _ _ _ hi, natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_toPoly_sem]
    by_cases hkl : k < (Pp.getD i []).length
    · rcases hdeg i hi k hkl with h1 | h1
      · exact absurd h1 (by have : s * (Pp.length - i) < k := by exact_mod_cast hk
                            omega)
      · exact ((T.MP m h).isZero_iff _).mp h1
    · rw [List.getD_eq_default _ _ (by omega), (T.MP m h).sem_zero]
  · have h1 := (GPoly.isZero_iff (T.MP m h) _).mp hlead
    rw [GPoly.toPoly_sub, sub_eq_zero, T.toPoly_prodXG m h] at h1
    have hprod : (γs.map fun g ↦ X - Polynomial.C ((T.MP m h).sem g)).prod =
        ∏ k : Fin Pp.length, (X - Polynomial.C ((T.MP m h).sem (γs.getD k (MO Fc ks m).zero))) := by
      rw [← List.prod_ofFn]
      congr 1
      apply List.ext_getElem (by simp [hlen])
      intro k h1 h2
      have hk : k < γs.length := by simp at h1 h2; omega
      rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem _ _ hk]
    rw [← hprod, ← h1]
    ext k
    rw [leadPoly, finsetSum_coeff, coeff_toPoly_sem, hFn]
    simp only [coeff_C_mul_X_pow]
    by_cases hk : k ≤ Pp.length
    · rw [Finset.sum_eq_single k (fun j _ hjk ↦ by rw [if_neg (Ne.symm hjk)])
        (fun h ↦ absurd (Finset.mem_range.mpr (by omega)) h), if_pos rfl]
      rcases lt_or_eq_of_le hk with hk | hk
      · rw [nkF, polyF_coeff _ _ _ hk, coeff_toPoly_sem, leadPolyC,
          List.getD_append _ _ _ _ (by simpa using hk),
          List.getD_eq_getElem (l := (List.range Pp.length).map fun i ↦
            (Pp.getD i []).getD (s * (Pp.length - i)) (MO Fc ks m).zero) _ (by simpa using hk),
          List.getElem_map, List.getElem_range]
      · subst hk
        have hmon := (polyF_monic (fun i ↦ GPoly.toPoly (T.MP m h) (Pp.getD i [])) Pp.length)
        have h1 : (T.nkF m h Pp).coeff Pp.length = 1 := by
          rw [← hFn]; exact hmon.coeff_natDegree
        rw [h1, Nat.sub_self, mul_zero, coeff_one_zero, leadPolyC,
          List.getD_append_right _ _ _ _ (by simp), List.length_map, List.length_range,
          Nat.sub_self, List.getD_cons_zero, (T.MP m h).sem_one]
    · rw [Finset.sum_eq_zero fun j hj ↦ by
        rw [if_neg (by have := Finset.mem_range.mp hj; omega)], leadPolyC,
        List.getD_eq_default _ _ (by simp; omega), (T.MP m h).sem_zero]
  · intro k l hkl
    by_contra hne
    rcases hdist k k.2 l l.2 with h2 | h2
    · exact hne (Fin.ext h2)
    · have h3 : (MO Fc ks m).isZero ((MO Fc ks m).add (γs.getD k (MO Fc ks m).zero)
          ((MO Fc ks m).neg (γs.getD l (MO Fc ks m).zero))) = true := by
        rw [(T.MP m h).isZero_iff, (T.MP m h).sem_add, (T.MP m h).sem_neg, ← sub_eq_add_neg]
        exact sub_eq_zero.mpr hkl
      rw [h3] at h2
      exact Bool.noConfusion h2


/-- `F` is irreducible over `Fₘ` (Eisenstein certificate). -/
lemma nkF_irr_of_eisCk (m : ℕ) (h0 : T.Tr m) (Pp : List (GPoly (LC m))) (qE : GPoly (LC m))
    (csE : List (GPoly (LC m))) (sE tE s2E t2E : GPoly (LC m))
    (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true) : Irreducible (T.nkF m h0 Pp) :=
  Monic.irreducible_of_irreducible_map (mapRingHom (algebraMap (T.F m) (AlgebraicClosure (T.F m))))
    _ (polyF_monic _ _) (T.nkF_geo_of_eisCk m h0 Pp qE csE sE tE s2E t2E hck _)

/-- **The curve over the code values** with an Eisenstein certificate (any coefficients). -/
noncomputable def nkCurveQE (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m)))
    (qE : GPoly (LC m)) (csE : List (GPoly (LC m))) (sE tE s2E t2E : GPoly (LC m))
    (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0) :
    CurveData (T.codeVals m h1.of_succ) L where
  x := T.ts m
  y := θ
  F := T.nkFQ m h1.of_succ Pp
  htr := T.transcendental_codeVals m h1.of_succ (h1 m (by omega))
  monic := polyF_monic _ _
  irr := Curves.MT.curve_irr _ _ (T.transcendental_codeVals m h1.of_succ (h1 m (by omega))) _
    (polyF_monic _ _)
    (Monic.irreducible_of_irreducible_map (mapRingHom (T.codeIncl m h1.of_succ)) _ (polyF_monic _ _)
      (by rw [T.map_nkFQ]; exact T.nkF_irr_of_eisCk m h1.of_succ Pp qE csE sE tE s2E t2E hck))
    (by
      have e : ((aeval (T.ts m)).toRingHom : (T.codeVals m h1.of_succ)[X] →+* L) =
          ((aeval (T.ts m)).toRingHom : (T.F m)[X] →+* L).comp
            (Polynomial.mapRingHom (T.codeIncl m h1.of_succ)) := by
        refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
        · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp,
            Function.comp_apply, coe_mapRingHom, Polynomial.map_C, aeval_C]
          rfl
        · simp
      rw [e, ← Polynomial.map_map, T.map_nkFQ]
      exact T.nkF_root m h1.of_succ Pp θ hθ)
  root := by
    have e : ((aeval (T.ts m)).toRingHom : (T.codeVals m h1.of_succ)[X] →+* L) =
        ((aeval (T.ts m)).toRingHom : (T.F m)[X] →+* L).comp
          (Polynomial.mapRingHom (T.codeIncl m h1.of_succ)) := by
      refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
      · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp,
          Function.comp_apply, coe_mapRingHom, Polynomial.map_C, aeval_C]
        rfl
      · simp
    rw [e, ← Polynomial.map_map, T.map_nkFQ]
    exact T.nkF_root m h1.of_succ Pp θ hθ

/-- The leading polynomial commutes with injective coefficient maps. -/
lemma leadPoly_map {A B : Type*} [Field A] [Field B] (φ : A →+* B) (s : ℕ) (F : A[X][X]) :
    leadPoly s (F.map (mapRingHom φ)) = (leadPoly s F).map φ := by
  rw [leadPoly, leadPoly, Polynomial.map_sum, natDegree_map_eq_of_injective
    (Polynomial.map_injective _ φ.injective)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, coeff_map,
    coe_mapRingHom, coeff_map]

end MTower

end Curves.MT
