import RischTragerBronstein.Computable.CAlgVia
import RischTragerBronstein.Computable.GReduce
import RischTragerBronstein.Curves.Branch
import RischTragerBronstein.Algebraic.SupBivar

/-!
# A computable model of the function field of a curve

For a curve `S : CurveData Kc E` (`x′ = 1`, constants `Kc`) whose equation has coefficients in a
computable field `R ⊆ Kc` (`S.F = (toB Fc).map ι`):

* `xModel ι hC S hx`: the codes `GFrac R` (rational functions in `x`), valued in `E`;
* `curveModel …`: the codes `GPoly (GFrac R)` (polynomials in `y` with coefficients in `R(x)`),
  valued in `E` by `y ↦ S.y`, with the operations `COps.algExt` of `CField.algVia`: products and
  zero tests are reduced modulo `F`, inverses come from the extended Euclidean algorithm, and
  `y′ = −F_x/F_y`.
-/

open Polynomial Differential IntermediateField

namespace Curves

open CPoly Sup

section Model

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E]
variable {R : Type*} [Field R] [DecidableEq R] (ι : R →+* Kc) (hC : ∀ c : Kc, c′ = 0)
  (S : CurveData Kc E) (hx : S.x′ = 1)

lemma toPoly_ofHom_list (l : List R) :
    GPoly.toPoly (CField.ofHom ι hC) l = (CPoly.toPoly l).map ι := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [GPoly.toPoly_cons, ih, CPoly.toPoly_cons, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X]
    rfl

/-- The operations of `R(x)`: fractions of polynomials, reduced by their gcd. -/
abbrev xOpsR (R : Type*) [Field R] [DecidableEq R] : COps (GFrac R) :=
  ((COps.ofDecidableField R).monomial [1]).normalizeBy (GPoly.redFrac (COps.ofDecidableField R))

/-- The model of `R(x)` in `E`, before normalization. -/
noncomputable def xModel0 : CField (GFrac R) E ((COps.ofDecidableField R).monomial [1]) :=
  (CField.ofHom ι hC).monomialVia [1] (aeval S.x).toRingHom
    (fun p hp ↦ by
      rw [toPoly_ofHom_list] at hp ⊢
      by_contra h0
      exact S.htr ⟨_, h0, hp⟩)
    (fun P ↦ by
      refine deriv_aeval_eq_implicitDeriv S.x _ ?_ P
      rw [toPoly_ofHom_list, hx]
      simp [CPoly.toPoly])

lemma sem_xModel0 (q : GFrac R) :
    (xModel0 ι hC S hx).sem q =
      aeval S.x ((CPoly.toPoly q.1).map ι) / aeval S.x ((CPoly.toPoly q.2).map ι) := by
  rw [xModel0, CField.sem_monomialVia, toPoly_ofHom_list, toPoly_ofHom_list]
  rfl

lemma sem_xModel0_redFrac (q : GFrac R) :
    (xModel0 ι hC S hx).sem (GPoly.redFrac (COps.ofDecidableField R) q) = (xModel0 ι hC S hx).sem q := by
  set M0 := CField.ofHom ι hC
  rw [sem_xModel0, sem_xModel0]
  by_cases ha : GPoly.toPoly M0 q.2 = 0
  · have hz : GPoly.isZero (COps.ofDecidableField R) q.2 = true := (GPoly.isZero_iff M0 _).mpr ha
    simp [GPoly.redFrac, hz]
  · obtain ⟨h1, h2⟩ := GPoly.redFrac_spec M0 q ha
    rw [toPoly_ofHom_list, toPoly_ofHom_list, toPoly_ofHom_list, toPoly_ofHom_list] at h1
    rw [toPoly_ofHom_list] at h2 ha
    have hne : ∀ Q : Kc[X], Q ≠ 0 → aeval S.x Q ≠ 0 := fun Q hQ h0 ↦ S.htr ⟨Q, hQ, h0⟩
    have h1' := congrArg (aeval S.x) h1
    rw [map_mul, map_mul] at h1'
    rw [div_eq_div_iff (hne _ h2) (hne _ ha)]
    linear_combination h1'

/-- The model of `R(x)` in `E` (reduced fractions). -/
noncomputable def xModel : CField (GFrac R) E (xOpsR R) :=
  (xModel0 ι hC S hx).normalizeBy _ (sem_xModel0_redFrac ι hC S hx)

lemma sem_xModel (q : GFrac R) :
    (xModel ι hC S hx).sem q =
      aeval S.x ((CPoly.toPoly q.1).map ι) / aeval S.x ((CPoly.toPoly q.2).map ι) :=
  sem_xModel0 ι hC S hx q

omit [Differential Kc] [Differential E] [DifferentialAlgebra Kc E] in
lemma aeval_x_mem (P : Kc[X]) : aeval S.x P ∈ Kc⟮S.x⟯ := by
  let _ := algebraAdjoinSimple (F := Kc) S.x
  rw [← algebraMap_adjoinSimple S.x P]
  exact (algebraMap Kc[X] Kc⟮S.x⟯ P).2

lemma sem_xModel_mem (q : GFrac R) : (xModel ι hC S hx).sem q ∈ Kc⟮S.x⟯ := by
  rw [sem_xModel]
  exact div_mem (aeval_x_mem S _) (aeval_x_mem S _)

/-- The codes of the curve equation. -/
def curveCodes (Fc : BPoly R) : GPoly (GFrac R) := Fc.map fun c ↦ (c, [1])

lemma toPoly_curveCodes (Fc : BPoly R) :
    GPoly.toPoly (xModel ι hC S hx) (curveCodes Fc) =
      ((toB Fc).map (mapRingHom ι)).map (aeval S.x).toRingHom := by
  induction Fc with
  | nil => simp [curveCodes]
  | cons c W ih =>
    simp only [curveCodes, List.map_cons] at ih ⊢
    rw [GPoly.toPoly_cons, ih, sem_xModel, toB_cons, Polynomial.map_add, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_X]
    simp [CPoly.toPoly]

include hx in
/-- **Minimality**: no non-zero polynomial of codes of degree `< deg F` vanishes at `y`. -/
lemma curve_hmin (p : GPoly (GFrac R))
    (hp : (GPoly.toPoly (xModel ι hC S hx) p).natDegree < S.F.natDegree)
    (hy : evalRingHom S.y (GPoly.toPoly (xModel ι hC S hx) p) = 0) :
    GPoly.toPoly (xModel ι hC S hx) p = 0 := by
  classical
  set P := GPoly.toPoly (xModel ι hC S hx) p with hPdef
  have hlift : P ∈ Polynomial.lifts (algebraMap Kc⟮S.x⟯ E) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    rw [hPdef, GPoly.coeff_toPoly]
    by_cases hk : k < p.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]
      exact ⟨⟨_, sem_xModel_mem ι hC S hx _⟩, rfl⟩
    · rw [List.getD_eq_default _ _ (by simpa using hk)]
      exact ⟨0, map_zero _⟩
  obtain ⟨q, hq⟩ := Polynomial.mem_lifts P |>.mp hlift
  have hqdeg : q.natDegree = P.natDegree := by
    rw [← hq, natDegree_map_eq_of_injective (algebraMap Kc⟮S.x⟯ E).injective]
  have hqy : aeval S.y q = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hq]; exact hy
  by_contra hP0
  have hq0 : q ≠ 0 := fun h ↦ hP0 (by rw [← hq, h, Polynomial.map_zero])
  have hdvd := minpoly.dvd Kc⟮S.x⟯ S.y hqy
  have hle := natDegree_le_of_dvd hdvd hq0
  rw [S.natDegree_minpoly, hqdeg] at hle
  omega

variable (Fc : BPoly R) (hSF : S.F = (toB Fc).map (mapRingHom ι))

include hSF in
lemma toPoly_curveCodes_eq :
    GPoly.toPoly (xModel ι hC S hx) (curveCodes Fc) = S.F.map (aeval S.x).toRingHom := by
  rw [toPoly_curveCodes, hSF]

include hSF in
lemma curveCodes_monic :
    (GPoly.toPoly (xModel ι hC S hx) (curveCodes Fc)).Monic := by
  rw [toPoly_curveCodes_eq ι hC S hx Fc hSF]; exact S.monic.map _

include hSF in
lemma curveCodes_natDegree :
    (GPoly.toPoly (xModel ι hC S hx) (curveCodes Fc)).natDegree = S.F.natDegree := by
  rw [toPoly_curveCodes_eq ι hC S hx Fc hSF, S.monic.natDegree_map]

include hSF in
lemma curveCodes_root :
    evalRingHom S.y (GPoly.toPoly (xModel ι hC S hx) (curveCodes Fc)) = 0 := by
  rw [toPoly_curveCodes_eq ι hC S hx Fc hSF, coe_evalRingHom]
  exact S.root

omit [Differential Kc] [Differential E] [DifferentialAlgebra Kc E] in
lemma natDegree_F_pos' : 0 < S.F.natDegree := by
  by_contra h
  have h0 : S.F.natDegree = 0 := by omega
  have h1 : S.F = 1 := by
    have hc : S.F.coeff 0 = 1 := by rw [← h0]; exact S.monic.coeff_natDegree
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hc, C_1]
  have := S.root
  rw [h1, Polynomial.map_one, eval_one] at this
  exact one_ne_zero this

omit [Differential Kc] [DifferentialAlgebra Kc E] in
lemma curve_hder (Q : E[X]) :
    (evalRingHom S.y Q)′ =
      evalRingHom S.y (mapCoeffs Q) + evalRingHom S.y (derivative Q) * (evalRingHom S.y X)′ := by
  simp only [coe_evalRingHom, eval_X, ← coe_aeval_eq_eval]
  exact deriv_aeval_eq S.y Q

/-- **The model of the function field `Kc(x, y)` of the curve**, codes `GPoly (GFrac R)`. -/
noncomputable def curveModel [CharZero E] :
    CField (GPoly (GFrac R)) E ((xOpsR R).algExt (curveCodes Fc)) :=
  (xModel ι hC S hx).algVia (curveCodes Fc) S.F.natDegree
    (curveCodes_monic ι hC S hx Fc hSF) (curveCodes_natDegree ι hC S hx Fc hSF)
    (natDegree_F_pos' S) (evalRingHom S.y) (curveCodes_root ι hC S hx Fc hSF)
    (fun p hp hy ↦ curve_hmin ι hC S hx p hp hy) (curve_hder S)

lemma sem_curveModel [CharZero E] (a : GPoly (GFrac R)) :
    (curveModel ι hC S hx Fc hSF).sem a = (GPoly.toPoly (xModel ι hC S hx) a).eval S.y := rfl

end Model

end Curves
