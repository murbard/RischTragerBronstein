import RischTragerBronstein.Torsion.ResThm2

/-!
# The residue theorem on the curve

**`curve_res_sum`**: for `f = W(x, y)/Q(x)` (`deg_y W < n`, `Q` split over `C` with roots in `R`) and
complete branch systems above every `a ∈ R` (ramification `N_a`) and above infinity (`N_∞`),
`∑_{a ∈ R} N_a⁻¹ ∑ₖ res(f dx along rₖ) + N_∞⁻¹ ∑ₖ res(f dx along rₖ^∞) = 0`.
The fibre sums are traces (`map_trW`), and the statement is the residue theorem on the line for
`Tr(W)/Q` (`sum_res_eq_zero`, `res_fibre_eq`, `res_inf_eq`).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Curve

variable {C L : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L)

/-- The sum of the residues of `f dX` along a complete branch system. -/
noncomputable def fibreRes (g : C[X] →+* LaurentSeries C) (hg : Function.Injective g)
    (l : List (LaurentSeries C)) (hl : S.F.map g = (l.map fun r ↦ X - Polynomial.C r).prod)
    (f : C⟮S.x⟯⟮S.y⟯) (X' : LaurentSeries C) : C :=
  (l.attach.map fun r ↦ LaurentSeries.res (S.embG g hg r.1 (S.root_of_mem hl r.2) f * X')).sum

lemma res_add (u v : LaurentSeries C) :
    LaurentSeries.res (u + v) = LaurentSeries.res u + LaurentSeries.res v := by
  simp [LaurentSeries.res]

lemma res_list_sum (l : List (LaurentSeries C)) :
    LaurentSeries.res l.sum = (l.map LaurentSeries.res).sum := by
  induction l with
  | nil => simp [LaurentSeries.res]
  | cons a l ih => rw [List.sum_cons, res_add, ih, List.map_cons, List.sum_cons]

/-- **The fibre sum is the residue of the trace.** -/
lemma fibreRes_eq (g : C[X] →+* LaurentSeries C) (hg : Function.Injective g)
    (l : List (LaurentSeries C)) (hl : S.F.map g = (l.map fun r ↦ X - Polynomial.C r).prod)
    (W : C[X][X]) (hW : W.natDegree < S.F.natDegree) (Q : C[X]) (X' : LaurentSeries C) :
    letI := algebraAdjoinSimple (F := C) S.x
    S.fibreRes g hg l hl (S.fnWQ W Q) X' = LaurentSeries.res (S.embXG g hg
      (algebraMap C[X] C⟮S.x⟯ (S.trW W (S.F.natDegree - 1)) / algebraMap C[X] C⟮S.x⟯ Q) * X') := by
  letI := algebraAdjoinSimple (F := C) S.x
  have hsum : (l.attach.map fun r ↦ S.embG g hg r.1 (S.root_of_mem hl r.2) (S.fnWQ W Q)).sum =
      S.embXG g hg (algebraMap C[X] C⟮S.x⟯ (S.trW W (S.F.natDegree - 1)) /
        algebraMap C[X] C⟮S.x⟯ Q) := by
    simp only [S.embG_fnWQ]
    rw [map_div₀, S.embXG_algebraMap, S.embXG_algebraMap,
      S.map_trW (K := C) g l hl W _ (by omega), div_eq_mul_inv, ← List.sum_map_mul_right]
    congr 1
    conv_rhs => rw [← List.attach_map_subtype_val l, List.map_map]
    rfl
  rw [fibreRes, ← hsum, ← List.sum_map_mul_right, res_list_sum, List.map_map]
  rfl

/-- **The residue theorem on the curve.** -/
theorem curve_res_sum (W : C[X][X]) (hW : W.natDegree < S.F.natDegree) (Q : C[X]) (hQ : Q ≠ 0)
    (hs : Multiset.card Q.roots = Q.natDegree) (R : Finset C) (hR : ∀ b, Q.IsRoot b → b ∈ R)
    (Nf : C → ℕ) (hNf : ∀ a, 0 < Nf a) (lf : C → List (LaurentSeries C))
    (hlf : ∀ a ∈ R, S.F.map (branchSub (Nf a) a) = ((lf a).map fun r ↦ X - Polynomial.C r).prod)
    (Ni : ℕ) (hNi : 0 < Ni) (li : List (LaurentSeries C))
    (hli : S.F.map (infSub (K := C) Ni) = (li.map fun r ↦ X - Polynomial.C r).prod) :
    ∑ a ∈ R.attach, ((Nf (a : C) : C))⁻¹ * S.fibreRes (branchSub (K := C) (Nf (a : C)) (a : C))
        (branchSub_injective _ (hNf (a : C)) (a : C)) (lf (a : C)) (hlf (a : C) a.2) (S.fnWQ W Q)
        (LaurentSeries.derivation (HahnSeries.C (a : C) + single ((Nf (a : C) : ℕ) : ℤ) (1 : C))) +
      ((Ni : C))⁻¹ * S.fibreRes (infSub (K := C) Ni) (infSub_injective _ hNi) li hli (S.fnWQ W Q)
        (LaurentSeries.derivation (single (-(Ni : ℤ)) (1 : C))) = 0 := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  set h : C⟮S.x⟯ := algebraMap C[X] C⟮S.x⟯ (S.trW W (S.F.natDegree - 1)) /
    algebraMap C[X] C⟮S.x⟯ Q with hh
  have hfin : ∀ a : R, ((Nf (a : C) : C))⁻¹ * S.fibreRes (branchSub (K := C) (Nf (a : C)) (a : C))
      (branchSub_injective _ (hNf (a : C)) (a : C)) (lf (a : C)) (hlf (a : C) a.2) (S.fnWQ W Q)
      (LaurentSeries.derivation (HahnSeries.C (a : C) + single ((Nf (a : C) : ℕ) : ℤ) (1 : C))) =
      resAt (Kx := C⟮S.x⟯) (a : C) h := by
    intro a
    rw [S.fibreRes_eq _ _ _ _ W hW Q, S.res_fibre_eq (Nf (a : C)) (hNf (a : C)) (a : C) h,
      ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (hNf (a : C)).ne'), one_mul]
  have hinf : ((Ni : C))⁻¹ * S.fibreRes (infSub (K := C) Ni) (infSub_injective _ hNi) li hli
      (S.fnWQ W Q) (LaurentSeries.derivation (single (-(Ni : ℤ)) (1 : C))) =
      resInf C (Kx := C⟮S.x⟯) h := by
    rw [S.fibreRes_eq _ _ _ _ W hW Q, S.res_inf_eq Ni hNi h, ← mul_assoc,
      inv_mul_cancel₀ (by exact_mod_cast hNi.ne'), one_mul]
  rw [Finset.sum_congr rfl fun a _ ↦ hfin a, hinf]
  rw [Finset.sum_attach R (fun a ↦ resAt (Kx := C⟮S.x⟯) a h)]
  exact sum_res_eq_zero (Kx := C⟮S.x⟯) R Q hQ hs hR _

end CurveData

end Curve

end Curves
