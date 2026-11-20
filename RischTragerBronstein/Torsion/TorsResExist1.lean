import RischTragerBronstein.Torsion.PlaceRes1
import RischTragerBronstein.Torsion.ResThm3

/-!
# The residue theorem for indexed fibres

**`res_theorem_fibres`**: the residue theorem `curve_res_sum` for a family of fibres
`x = a_j + T^{N_j}` (`j : Fin m`, distinct `a_j` covering the roots of `Q`) with complete branch
systems given as functions `Fin n → LaurentSeries C`, and one above infinity:
`∑_j N_j⁻¹ ∑_k res(f dx along y_{jk}) + N_∞⁻¹ ∑_k res(f dx along w_k) = 0` for `f = W(x, y)/Q(x)`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Fibres

variable {C L : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L)

/-- The sum over a branch system given by a function. -/
lemma fibreRes_ofFn (g : C[X] →+* LaurentSeries C) (hg : Function.Injective g)
    (v : Fin S.F.natDegree → LaurentSeries C)
    (hl : S.F.map g = ((List.ofFn v).map fun r ↦ X - Polynomial.C r).prod)
    (hv : ∀ k, (S.F.map g).eval (v k) = 0) (f : C⟮S.x⟯⟮S.y⟯) (X' : LaurentSeries C) :
    S.fibreRes g hg (List.ofFn v) hl f X' =
      ∑ k, LaurentSeries.res (S.embG g hg (v k) (hv k) f * X') := by
  classical
  set φ : LaurentSeries C → C := fun z ↦
    if h : (S.F.map g).eval z = 0 then LaurentSeries.res (S.embG g hg z h f * X') else 0
  have e1 : S.fibreRes g hg (List.ofFn v) hl f X' = ((List.ofFn v).map φ).sum := by
    rw [fibreRes]
    conv_rhs => rw [← List.attach_map_subtype_val (List.ofFn v), List.map_map]
    congr 1
    refine List.map_congr_left fun r _ ↦ ?_
    simp only [Function.comp_apply, φ, dif_pos (S.root_of_mem hl r.2)]
  rw [e1, List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Function.comp_apply, φ, dif_pos (hv k)]

lemma split_ofFn (g : C[X] →+* LaurentSeries C) (v : Fin S.F.natDegree → LaurentSeries C)
    (h : S.F.map g = ∏ k, (X - Polynomial.C (v k))) :
    S.F.map g = ((List.ofFn v).map fun r ↦ X - Polynomial.C r).prod := by
  rw [h, List.map_ofFn, List.prod_ofFn]; rfl

/-- **The residue theorem for indexed fibres.** -/
theorem res_theorem_fibres (W : C[X][X]) (hW : W.natDegree < S.F.natDegree) (Q : C[X])
    (hQ : Q ≠ 0) (hs : Multiset.card Q.roots = Q.natDegree) {m : ℕ} (a : Fin m → C)
    (ha : Function.Injective a) (hR : ∀ b, Q.IsRoot b → ∃ j, a j = b) (N : Fin m → ℕ)
    (hN : ∀ j, 0 < N j) (y : Fin m → Fin S.F.natDegree → LaurentSeries C)
    (hy : ∀ j, S.F.map (branchSub (K := C) (N j) (a j)) = ∏ k, (X - Polynomial.C (y j k)))
    (hyr : ∀ j k, (S.F.map (branchSub (K := C) (N j) (a j))).eval (y j k) = 0)
    (Ni : ℕ) (hNi : 0 < Ni) (w : Fin S.F.natDegree → LaurentSeries C)
    (hw : S.F.map (infSub (K := C) Ni) = ∏ k, (X - Polynomial.C (w k)))
    (hwr : ∀ k, (S.F.map (infSub (K := C) Ni)).eval (w k) = 0) :
    ∑ j, ((N j : C))⁻¹ * ∑ k, LaurentSeries.res (S.embG (branchSub (N j) (a j))
        (branchSub_injective _ (hN j) _) (y j k) (hyr j k) (S.fnWQ W Q) *
          LaurentSeries.derivation (HahnSeries.C (a j) + single ((N j : ℕ) : ℤ) (1 : C))) +
      ((Ni : C))⁻¹ * ∑ k, LaurentSeries.res (S.embG (infSub Ni) (infSub_injective _ hNi) (w k)
        (hwr k) (S.fnWQ W Q) * LaurentSeries.derivation (single (-(Ni : ℤ)) (1 : C))) = 0 := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  set h : C⟮S.x⟯ := algebraMap C[X] C⟮S.x⟯ (S.trW W (S.F.natDegree - 1)) /
    algebraMap C[X] C⟮S.x⟯ Q with hh
  have hfib : ∀ j, ((N j : C))⁻¹ * ∑ k, LaurentSeries.res (S.embG (branchSub (N j) (a j))
      (branchSub_injective _ (hN j) _) (y j k) (hyr j k) (S.fnWQ W Q) *
        LaurentSeries.derivation (HahnSeries.C (a j) + single ((N j : ℕ) : ℤ) (1 : C))) =
      resAt (Kx := C⟮S.x⟯) (a j) h := by
    intro j
    rw [← S.fibreRes_ofFn _ _ (y j) (S.split_ofFn _ (y j) (hy j)) (hyr j),
      S.fibreRes_eq _ _ _ _ W hW Q, S.res_fibre_eq (N j) (hN j) (a j) h, ← mul_assoc,
      inv_mul_cancel₀ (by exact_mod_cast (hN j).ne'), one_mul]
  have hinf : ((Ni : C))⁻¹ * ∑ k, LaurentSeries.res (S.embG (infSub Ni) (infSub_injective _ hNi)
      (w k) (hwr k) (S.fnWQ W Q) * LaurentSeries.derivation (single (-(Ni : ℤ)) (1 : C))) =
      resInf C (Kx := C⟮S.x⟯) h := by
    rw [← S.fibreRes_ofFn _ _ w (S.split_ofFn _ w hw) hwr,
      S.fibreRes_eq _ _ _ _ W hW Q, S.res_inf_eq Ni hNi h, ← mul_assoc,
      inv_mul_cancel₀ (by exact_mod_cast hNi.ne'), one_mul]
  rw [Finset.sum_congr rfl fun j _ ↦ hfib j, hinf]
  have hR' : ∀ b, Q.IsRoot b → b ∈ Finset.univ.image a := fun b hb ↦ by
    obtain ⟨j, rfl⟩ := hR b hb
    exact Finset.mem_image_of_mem a (Finset.mem_univ j)
  have := sum_res_eq_zero (Kx := C⟮S.x⟯) (Finset.univ.image a) Q hQ hs hR' (S.trW W (S.F.natDegree - 1))
  rw [Finset.sum_image fun j _ j' _ h ↦ ha h] at this
  exact this

end CurveData

end Fibres

end Curves
