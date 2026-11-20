import RischTragerBronstein.Curves.ProcRFSound4

/-!
# The ansatz space on the curve

* `fE`: the integrand `A(x, y)/D(x)`; `bE ie`: the basis element `xᵉ yⁱ / R0(x)`;
* `discR_eq`: the curve discriminant is the image of the computed `discRC`;
* `degB_le`: `degB ≤ degBC`;
* `evXY_basis`: a bivariate `W` with `deg_Y W < n`, `deg_x W ≤ E` is a combination of the
  basis monomials, so `W(x, y)/R0(x) = ∑ c_b b`.
-/

open Polynomial IntermediateField

namespace Curves

open CPoly Sup

section Sums

lemma sum_range_map {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∀ m, ((List.range m).map g).sum = ∑ i ∈ Finset.range m, g i
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_map g m,
      Finset.sum_range_succ]
    simp

lemma sum_range_getD {α M : Type*} [AddCommMonoid M] (l : List α) (d : α) (g : α → M) :
    ∑ b ∈ Finset.range l.length, g (l.getD b d) = (l.map g).sum := by
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_fun_getElem]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [List.getD_eq_getElem _ _ b.2]

lemma foldr_add_eq_sum (g : ℕ → ℕ) (m : ℕ) :
    (List.range m).foldr (fun i acc ↦ acc + g i) 0 = ∑ i ∈ Finset.range m, g i := by
  rw [← sum_range_map]
  induction (List.range m) with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, ih, List.map_cons, List.sum_cons, add_comm]

lemma sum_flatMap' {α β M : Type*} [AddCommMonoid M] (f : α → List β) (g : β → M) :
    ∀ l : List α, ((l.flatMap f).map g).sum = (l.map fun a ↦ ((f a).map g).sum).sum
  | [] => by simp
  | a :: l => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_flatMap' f g l, List.map_cons,
      List.sum_cons]

end Sums

section Basis

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

namespace CurveProb

variable (P : CurveProb F)

lemma sum_basisIdx {M : Type*} [AddCommMonoid M] (g : ℕ × ℕ → M) :
    ∑ b ∈ Finset.range P.basisIdx.length, g (P.basisIdx.getD b (0, 0)) =
      ∑ i ∈ Finset.range P.n, ∑ e ∈ Finset.range (P.E + 1), g (i, e) := by
  rw [sum_range_getD, basisIdx, sum_flatMap', ← sum_range_map]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  rw [List.map_map, ← sum_range_map]
  rfl

omit [CharZero F] in
lemma R0_ne_zero (hV : P.ValidFacts) : toPoly P.R0 ≠ 0 := by
  rw [← toPoly_trim]
  intro h0
  have := (trim_eq_nil_iff (trim P.R0)).mpr h0
  rw [trim_trim] at this
  have := hV.R0l; simp_all

end CurveProb

lemma toB_basisB (i e : ℕ) : toB (basisB i e : BPoly F) = X ^ i * Polynomial.C (X ^ e) := by
  rw [basisB, toB_append, List.length_replicate]
  have : toB (List.replicate i ([] : CPoly F)) = 0 := by
    induction i with
    | zero => rfl
    | succ j ihj => rw [List.replicate_succ, toB_cons, ihj, toPoly_nil, map_zero]; ring
  rw [this, zero_add, toB_cons, toB_nil, mul_zero, add_zero, toPoly_xPowC]

end Basis

section Curve

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L)

lemma aeval_x_ne_zero (Q : C[X]) (hQ : Q ≠ 0) : aeval S.x Q ≠ 0 := fun h ↦ S.htr ⟨Q, hQ, h⟩

variable (P : CurveProb F) (ψ₀ : F →+* C)

/-- The integrand `A(x, y)/D(x)`. -/
noncomputable def fE : C⟮S.x⟯⟮S.y⟯ :=
  ⟨S.evXY ((toB P.A).map (mapRingHom ψ₀)) / aeval S.x ((toPoly P.D).map ψ₀),
    div_mem (S.evXY_mem _) (S.aeval_mem _)⟩

/-- The basis element `xᵉ yⁱ / R0(x)`. -/
noncomputable def bE (ie : ℕ × ℕ) : C⟮S.x⟯⟮S.y⟯ :=
  ⟨S.evXY ((toB (basisB ie.1 ie.2)).map (mapRingHom ψ₀)) / aeval S.x ((toPoly P.R0).map ψ₀),
    div_mem (S.evXY_mem _) (S.aeval_mem _)⟩

lemma fE_spec (hV : P.ValidFacts) :
    (S.fE P ψ₀ : L) * aeval S.x ((toPoly P.D).map ψ₀) =
      S.evXY ((toB P.A).map (mapRingHom ψ₀)) :=
  div_mul_cancel₀ _ (S.aeval_x_ne_zero _ (by
    rw [Ne, Polynomial.map_eq_zero_iff ψ₀.injective]; exact hV.D0))

lemma bE_spec (hV : P.ValidFacts) (ie : ℕ × ℕ) :
    (S.bE P ψ₀ ie : L) * aeval S.x ((toPoly P.R0).map ψ₀) =
      S.evXY ((toB (basisB ie.1 ie.2)).map (mapRingHom ψ₀)) :=
  div_mul_cancel₀ _ (S.aeval_x_ne_zero _ (by
    rw [Ne, Polynomial.map_eq_zero_iff ψ₀.injective]; exact P.R0_ne_zero hV))

variable {P ψ₀}

lemma coeff_F (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (i : ℕ) :
    S.F.coeff i = (toPoly (P.Fc.getD i [])).map ψ₀ := by
  rw [hSF, coeff_map, coeff_toB]; rfl

lemma coeff_F_le (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) (i : ℕ) :
    (S.F.coeff i).natDegree ≤ P.k := by
  rw [S.coeff_F hSF, natDegree_map_eq_of_injective ψ₀.injective]; exact hV.kF i

/-- **The discriminant** is the image of the computed one. -/
lemma discR_eq (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) :
    S.discR = (toPoly (discRC P.Fc P.n P.k)).map ψ₀ := by
  rw [toPoly_discRC P.Fc P.n P.k hV.mon hV.deg (fun i ↦ by rw [coeff_toB]; exact hV.kF i),
    CurveData.discR, S.natDegree_F_eq P ψ₀ hSF hV, hSF, derivative_map, resultant_map_map]
  rfl

lemma discR_mul_D (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) :
    S.discR * (toPoly P.D).map ψ₀ = (toPoly P.R0).map ψ₀ := by
  rw [S.discR_eq hSF hV, toPoly_R0, Polynomial.map_mul]

lemma degB_le (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) :
    S.degB ≤ P.degBC := by
  rw [CurveData.degB, CurveProb.degBC, foldr_add_eq_sum, S.natDegree_F_eq P ψ₀ hSF hV]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [S.coeff_F hSF, natDegree_map_eq_of_injective ψ₀.injective, degT_eq]

lemma evXY_C_mul (c : C) (Q : C[X][X]) :
    S.evXY (Polynomial.C (Polynomial.C c) * Q) = algebraMap C L c * S.evXY Q := by
  rw [S.evXY_mul]
  congr 1
  simp [evXY]

/-- **Basis expansion** of a bivariate polynomial of bounded degrees. -/
lemma evXY_basis (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts)
    (W : C[X][X]) (hW : W.natDegree < S.F.natDegree) (hWc : ∀ j, (W.coeff j).natDegree ≤ P.E) :
    S.evXY W = ∑ b ∈ Finset.range P.basisIdx.length,
      algebraMap C L ((W.coeff (P.basisIdx.getD b (0, 0)).1).coeff (P.basisIdx.getD b (0, 0)).2) *
        S.evXY ((toB (basisB (P.basisIdx.getD b (0, 0)).1
          (P.basisIdx.getD b (0, 0)).2)).map (mapRingHom ψ₀)) := by
  rw [P.sum_basisIdx (fun ie ↦ algebraMap C L ((W.coeff ie.1).coeff ie.2) *
    S.evXY ((toB (basisB ie.1 ie.2)).map (mapRingHom ψ₀)))]
  rw [S.natDegree_F_eq P ψ₀ hSF hV] at hW
  have hWe : W = ∑ i ∈ Finset.range P.n, ∑ e ∈ Finset.range (P.E + 1),
      Polynomial.C (Polynomial.C ((W.coeff i).coeff e)) *
        (toB (basisB i e : BPoly F)).map (mapRingHom ψ₀) := by
    conv_lhs => rw [as_sum_range' W P.n hW]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    conv_lhs => rw [← C_mul_X_pow_eq_monomial,
      as_sum_range' (W.coeff i) (P.E + 1) (Nat.lt_succ_of_le (hWc i))]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [toB_basisB, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      coe_mapRingHom, Polynomial.map_pow, Polynomial.map_X, ← C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow]
    ring
  conv_lhs => rw [hWe]
  simp only [evXY, Polynomial.map_sum, eval_finset_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
  have := S.evXY_C_mul ((W.coeff i).coeff e) ((toB (basisB i e : BPoly F)).map (mapRingHom ψ₀))
  simp only [evXY] at this
  exact this

/-- **Elements of the ansatz space are combinations of the basis.** -/
lemma eq_lcomb (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts)
    (w : C⟮S.x⟯⟮S.y⟯) (W : C[X][X]) (hW : W.natDegree < S.F.natDegree)
    (hWc : ∀ j, (W.coeff j).natDegree ≤ P.E)
    (hw : (w : L) * aeval S.x ((toPoly P.R0).map ψ₀) = S.evXY W) :
    w = ∑ b ∈ Finset.range P.basisIdx.length,
      S.cst ((W.coeff (P.basisIdx.getD b (0, 0)).1).coeff (P.basisIdx.getD b (0, 0)).2) *
        S.bE P ψ₀ (P.basisIdx.getD b (0, 0)) := by
  have hR : aeval S.x ((toPoly P.R0).map ψ₀) ≠ 0 := S.aeval_x_ne_zero _ (by
    rw [Ne, Polynomial.map_eq_zero_iff ψ₀.injective]; exact P.R0_ne_zero hV)
  apply Subtype.ext
  apply mul_right_cancel₀ hR
  rw [hw, S.evXY_basis hSF hV W hW hWc, AddSubmonoidClass.coe_finset_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [MulMemClass.coe_mul, mul_assoc, S.bE_spec P ψ₀ hV]
  rfl

end CurveData

end Curve

end Curves
