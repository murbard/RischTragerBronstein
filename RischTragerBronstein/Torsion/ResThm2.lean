import RischTragerBronstein.Torsion.ResThm1
import RischTragerBronstein.Curves.Reparam

/-!
# The residue theorem on the curve (1): traces

* `trW`: the trace of `W(x, y)` over `C(x)`, the coefficient of `t` in `Res_Y(F, 1 + t W)`;
  **`map_trW`**: along any branch system, `g(trW) = ∑ₖ W(rₖ)`;
* `embXG_eq_lsub_expAt`, `embXG_eq_lsub_expInf`: the expansions of `C(x)` along
  `x = a + Tᴺ` / `x = T^{−N}` are those at `x = a + T` / `x = T⁻¹` reparametrized by `T ↦ Tᴺ`, so
  residues along them are `N` times the residues on the line (`res_fibre_eq`, `res_inf_eq`).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries

section Trace

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L)

/-- The trace of `W(x, y)`: the coefficient of `t` in `Res_Y(F, 1 + t W)`. -/
noncomputable def trW (W : C[X][X]) (m : ℕ) : C[X] :=
  (resultant (S.F.map (Polynomial.C : C[X] →+* C[X][X]))
    (1 + Polynomial.C (X : C[X][X]) * W.map (Polynomial.C : C[X] →+* C[X][X]))
    S.F.natDegree m).coeff 1

lemma coeff_one_prod_one_add {A : Type*} [CommRing A] (l : List A) :
    ((l.map fun c ↦ (1 + X * Polynomial.C c : A[X])).prod).coeff 1 = l.sum := by
  induction l with
  | nil => simp [Polynomial.coeff_one]
  | cons c l ih =>
    rw [List.map_cons, List.prod_cons, List.sum_cons, add_mul, one_mul, Polynomial.coeff_add, ih,
      mul_assoc, coeff_X_mul, coeff_C_mul]
    have h0 : ((l.map fun c ↦ (1 + X * Polynomial.C c : A[X])).prod).coeff 0 = 1 := by
      rw [coeff_zero_eq_eval_zero, eval_list_prod]
      exact List.prod_eq_one fun x hx ↦ by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        obtain ⟨c, -, rfl⟩ := List.mem_map.mp hq
        simp
    rw [h0, mul_one]
    ring

/-- **The trace along a branch system.** -/
theorem map_trW {K : Type*} [Field K] [Algebra C K] (g : C[X] →+* LaurentSeries K) (l : List (LaurentSeries K))
    (hl : S.F.map g = (l.map fun r ↦ X - Polynomial.C r).prod) (W : C[X][X]) (m : ℕ)
    (hm : W.natDegree ≤ m) :
    g (S.trW W m) = (l.map fun r ↦ (W.map g).eval r).sum := by
  set ĝ : C[X][X] →+* (LaurentSeries K)[X] := Polynomial.mapRingHom g with hĝ
  have hlen := S.length_of_split hl
  have h1 : (S.F.map (Polynomial.C : C[X] →+* C[X][X])).map ĝ =
      ((l.map Polynomial.C).map fun r ↦ X - Polynomial.C r).prod := by
    rw [Polynomial.map_map, show ĝ.comp (Polynomial.C : C[X] →+* C[X][X]) =
      (Polynomial.C : LaurentSeries K →+* (LaurentSeries K)[X]).comp g from
        RingHom.ext fun P ↦ by simp [hĝ], ← Polynomial.map_map, hl, Polynomial.map_list_prod,
      List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun r _ ↦ ?_
    simp
  have h2 : (1 + Polynomial.C (X : C[X][X]) * W.map (Polynomial.C : C[X] →+* C[X][X])).map ĝ =
      1 + Polynomial.C (X : (LaurentSeries K)[X]) *
        (W.map g).map (Polynomial.C : LaurentSeries K →+* (LaurentSeries K)[X]) := by
    rw [Polynomial.map_add, Polynomial.map_one, Polynomial.map_mul, Polynomial.map_C, hĝ,
      coe_mapRingHom, Polynomial.map_X, Polynomial.map_map, Polynomial.map_map]
    congr 3
    exact RingHom.ext fun P ↦ by simp
  have hdeg : (1 + Polynomial.C (X : (LaurentSeries K)[X]) *
      (W.map g).map (Polynomial.C : LaurentSeries K →+* (LaurentSeries K)[X])).natDegree ≤ m := by
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    exact natDegree_map_le.trans (natDegree_map_le.trans hm)
  have h3 : ∀ r : LaurentSeries K, (1 + Polynomial.C (X : (LaurentSeries K)[X]) *
      (W.map g).map (Polynomial.C : LaurentSeries K →+* (LaurentSeries K)[X])).eval
        (Polynomial.C r) = 1 + X * Polynomial.C ((W.map g).eval r) := by
    intro r
    rw [eval_add, eval_one, eval_mul, eval_C, eval_map, eval₂_at_apply]
  have key : (ĝ (resultant (S.F.map (Polynomial.C : C[X] →+* C[X][X]))
      (1 + Polynomial.C (X : C[X][X]) * W.map (Polynomial.C : C[X] →+* C[X][X]))
      S.F.natDegree m)).coeff 1 = (l.map fun r ↦ (W.map g).eval r).sum := by
    rw [← resultant_map_map, h1, h2, show S.F.natDegree = (l.map Polynomial.C).length by
      rw [List.length_map, hlen], resultant_list_prod _ _ _ hdeg, List.map_map]
    simp only [Function.comp_def, h3]
    rw [show (l.map fun x ↦ (1 + X * Polynomial.C ((W.map g).eval x) : (LaurentSeries K)[X])) =
      ((l.map fun r ↦ (W.map g).eval r).map fun c ↦ (1 + X * Polynomial.C c)) by
        rw [List.map_map]; rfl, coeff_one_prod_one_add]
  rw [trW, ← coeff_map (f := g)]
  exact key

end CurveData

end Trace

section Expand

variable {C L : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L)

/-- Expansions along `x = a + Tᴺ` are reparametrized expansions at `x = a + T`. -/
lemma embXG_eq_lsub_expAt (N : ℕ) (hN : 0 < N) (a : C) (h : C⟮S.x⟯) :
    letI := algebraAdjoinSimple (F := C) S.x
    haveI := isFractionRing_adjoin_simple S.x S.htr
    S.embXG (branchSub (K := C) N a) (branchSub_injective N hN a) h =
      lsub N hN (expAt (C⟮S.x⟯) a h) := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  have e : S.embXG (branchSub (K := C) N a) (branchSub_injective N hN a) =
      (lsub N hN).comp (expAt (C⟮S.x⟯) a) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors C[X]) (RingHom.ext fun P ↦ ?_)
    rw [RingHom.comp_apply, S.embXG_algebraMap, RingHom.comp_apply, RingHom.comp_apply,
      expAt_algebraMap, ← RingHom.comp_apply (lsub N hN), lsub_comp_branchSub, one_mul]
  exact congrArg (fun φ : C⟮S.x⟯ →+* LaurentSeries C ↦ φ h) e

/-- Expansions along `x = T^{−N}` are reparametrized expansions at `x = T⁻¹`. -/
lemma embXG_eq_lsub_expInf (N : ℕ) (hN : 0 < N) (h : C⟮S.x⟯) :
    letI := algebraAdjoinSimple (F := C) S.x
    haveI := isFractionRing_adjoin_simple S.x S.htr
    S.embXG (infSub (K := C) N) (infSub_injective N hN) h =
      lsub N hN (expInf (C := C) (C⟮S.x⟯) h) := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  have e : S.embXG (infSub (K := C) N) (infSub_injective N hN) =
      (lsub N hN).comp (expInf (C := C) (C⟮S.x⟯)) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors C[X]) (RingHom.ext fun P ↦ ?_)
    rw [RingHom.comp_apply, S.embXG_algebraMap, RingHom.comp_apply, RingHom.comp_apply,
      expInf_algebraMap, ← RingHom.comp_apply (lsub N hN), lsub_comp_infSub, one_mul]
  exact congrArg (fun φ : C⟮S.x⟯ →+* LaurentSeries C ↦ φ h) e

/-- **Residues along a finite fibre are `N` times residues on the line.** -/
lemma res_fibre_eq (N : ℕ) (hN : 0 < N) (a : C) (h : C⟮S.x⟯) :
    letI := algebraAdjoinSimple (F := C) S.x
    haveI := isFractionRing_adjoin_simple S.x S.htr
    LaurentSeries.res (S.embXG (branchSub (K := C) N a) (branchSub_injective N hN a) h *
      LaurentSeries.derivation (HahnSeries.C a + single (N : ℤ) (1 : C))) =
      N * resAt (Kx := C⟮S.x⟯) a h := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  have hX : HahnSeries.C a + single (N : ℤ) (1 : C) =
      lsub N hN (HahnSeries.C a + single (1 : ℤ) (1 : C)) := by
    rw [map_add, lsub_C, lsub_single, mul_one]
  have hd : LaurentSeries.derivation (HahnSeries.C a + single (1 : ℤ) (1 : C)) = 1 := by
    have := SuperData.derivation_branchX (K := C) 1 one_pos a
    simp only [Nat.cast_one, sub_self] at this
    rw [this, ← HahnSeries.C_apply, map_one]
  rw [S.embXG_eq_lsub_expAt N hN a h, hX, res_lsub, hd, mul_one]
  rfl

/-- **Residues along the fibre above infinity are `N` times the residue at infinity.** -/
lemma res_inf_eq (N : ℕ) (hN : 0 < N) (h : C⟮S.x⟯) :
    letI := algebraAdjoinSimple (F := C) S.x
    haveI := isFractionRing_adjoin_simple S.x S.htr
    LaurentSeries.res (S.embXG (infSub (K := C) N) (infSub_injective N hN) h *
      LaurentSeries.derivation (single (-(N : ℤ)) (1 : C))) = N * resInf C (Kx := C⟮S.x⟯) h := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  have hX : single (-(N : ℤ)) (1 : C) = lsub N hN (single (-1 : ℤ) (1 : C)) := by
    rw [lsub_single]; congr 1; ring
  have hd : LaurentSeries.derivation (single (-1 : ℤ) (1 : C)) = single (-2 : ℤ) (-1 : C) := by
    have := SuperData.derivation_infX (K := C) 1
    simp only [Nat.cast_one] at this
    rw [this]; norm_num
  rw [S.embXG_eq_lsub_expInf N hN h, hX, res_lsub, hd]
  rfl

end CurveData

end Expand

end Curves
