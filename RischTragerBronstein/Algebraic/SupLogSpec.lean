import RischTragerBronstein.Algebraic.SupLogIdent

/-!
# Correctness of the superelliptic logarithmic-part procedure
-/

open Polynomial CPoly Differential IntermediateField

namespace Sup

section Coe

variable {F : Type*} [Field F]
variable {C L : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L] [CharZero L]

lemma natDegree_lt_of_coeff {R : Type*} [Semiring R] (W : R[X]) (n : ℕ) (hn : 0 < n)
    (hW : ∀ i, n ≤ i → W.coeff i = 0) : W.natDegree < n := by
  by_cases h0 : W = 0
  · rw [h0, natDegree_zero]; exact hn
  by_contra h
  exact (leadingCoeff_ne_zero.mpr h0) (hW _ (by omega))

/-- `elemW` of a mapped polynomial is its evaluation. -/
lemma elemW_map_coe (S : SuperData C L) (ψ : F →+* C) (W : F[X][X])
    (hW : ∀ i, S.n ≤ i → W.coeff i = 0) :
    ((S.elemW (W.map (mapRingHom ψ)) : C⟮S.x⟯⟮S.y⟯) : L) = evalE ψ S.x S.y W := by
  have hdeg := natDegree_lt_of_coeff W S.n S.hn hW
  simp only [SuperData.elemW, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
    SubmonoidClass.coe_pow, AdjoinSimple.coe_gen, S.polyX_coe]
  rw [evalE, coe_eval₂RingHom, eval₂_eq_sum_range' _ hdeg]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [coeff_map]

lemma evalE_ne_zero (S : SuperData C L) (ψ : F →+* C) (W : F[X][X]) (hW0 : W ≠ 0)
    (hW : ∀ i, S.n ≤ i → W.coeff i = 0) : evalE ψ S.x S.y W ≠ 0 := by
  rw [← elemW_map_coe S ψ W hW]
  have := S.elemW_ne_zero (W.map (mapRingHom ψ))
    (fun h ↦ hW0 (Polynomial.map_injective _ (Polynomial.map_injective _ ψ.injective)
      (by rw [h, Polynomial.map_zero])))
    (fun i hi ↦ by rw [coeff_map, hW i hi, map_zero])
  exact fun h ↦ this (Subtype.ext h)

end Coe

section Hom

variable {F : Type*} [Field F]
variable {Kc E Cc L : Type*} [Field Kc] [Field E] [Algebra Kc E] [Field Cc] [Field L] [Algebra Cc L]
  [Differential Kc] [Differential E] [DifferentialAlgebra Kc E] [CharZero E]
  [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero L]

/-- Evaluation commutes with a field embedding. -/
lemma evalE_hom (ι : F →+* Kc) (φ : Kc →+* Cc) (jE : E →+* L)
    (hj : ∀ c : Kc, jE (algebraMap Kc E c) = algebraMap Cc L (φ c)) (x y : E) (W : F[X][X]) :
    jE (evalE ι x y W) = evalE (φ.comp ι) (jE x) (jE y) W := by
  simp only [evalE, coe_eval₂RingHom]
  rw [hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
  · simp [hj]
  · simp

end Hom

section Sound

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
  [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

open EllQuad.QCoords

/-- The superelliptic function field of the data, over `Kc`. -/
noncomputable def superE (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (ι : F →+* Kc)
    (f : CPoly F) (n : ℕ) (hn : 0 < n) (hsq : Squarefree (toPoly f))
    (hpd : 0 < (toPoly f).natDegree) (hy : y ^ n = aeval x ((toPoly f).map ι)) :
    SuperData Kc E :=
  ⟨x, y, n, (toPoly f).map ι, transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero),
    hn, ((PerfectField.separable_iff_squarefree.mpr hsq).map).squarefree,
    by rw [natDegree_map_eq_of_injective ι.injective]; exact hpd, hy,
    Nat.cast_ne_zero.mpr hn.ne'⟩

lemma exC_ne_zero (hC : ∀ c : Kc, c′ = 0) (x : E) (hx : x′ = 1) (ι : F →+* Kc) (P : CPoly F)
    (hP : toPoly P ≠ 0) : exC ι x P ≠ 0 := by
  intro h0
  exact transcendental_of_deriv_ne_zero hC (x := x) (by rw [hx]; exact one_ne_zero)
    ⟨_, (Polynomial.map_ne_zero_iff ι.injective).mpr hP, h0⟩

/-- The integrand `B + B₁/f + ∑ Gᵢ/(x − aᵢ)`. -/
noncomputable def integrandE (ι : F →+* Kc) (x y : E) (f : CPoly F) {m : ℕ} (B B₁ : BPoly F)
    (a : Fin m → F) (G : Fin m → BPoly F) : E :=
  evalE ι x y (toB B) + evalE ι x y (toB B₁) / exC ι x f +
    ∑ i, evalE ι x y (toB (G i)) / (x - algebraMap Kc E (ι (a i)))

/-- **Soundness**: a solution of the exactness test gives an elementary integral. -/
theorem superLog_sound (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (ι : F →+* Kc)
    (f : CPoly F) {n : ℕ} (hn : 0 < n) (hsq : Squarefree (toPoly f))
    (hpd : 0 < (toPoly f).natDegree) (hy : y ^ n = aeval x ((toPoly f).map ι))
    {m : ℕ} (ζ : F) (a b : Fin m → F) (G : Fin m → BPoly F) (B B₁ : BPoly F)
    (NW : Fin (dim F) → ℕ × BPoly F)
    (hNW : ∀ j, toB (NW j).2 ≠ 0 ∧ ∀ i, n ≤ i → (toB (NW j).2).coeff i = 0)
    (basis : List (ℕ × ℕ)) {cs : List F}
    (h : exactTest f n hn (logMT f n ζ a b G B B₁ NW).1 (logMT f n ζ a b G B B₁ NW).2 basis =
      some cs) :
    HasElementaryIntegral (integrandE ι x y f B B₁ a G) := by
  set SE := superE hC x y hx ι f n hn hsq hpd hy
  have hfx : exC ι x f ≠ 0 := exC_ne_zero hC x hx ι f hsq.ne_zero
  have hy0 : y ≠ 0 := by
    intro h0; apply hfx
    rw [exC, ← hy, h0, zero_pow hn.ne']
  have hu : ∀ j, evalE ι x y (toB (NW j).2) ≠ 0 := fun j ↦
    evalE_ne_zero SE ι _ (hNW j).1 (hNW j).2
  have hxa : ∀ i, x - algebraMap Kc E (ι (a i)) ≠ 0 := fun i h0 ↦ by
    have := congrArg (fun t : E ↦ t′) h0
    simp only [map_sub, hx, deriv_algebraMap, hC, map_zero, sub_zero] at this
    exact one_ne_zero this
  have hsnd := exactTest_sound_E hC x y hx ι f hn hy0 hy _ _ basis h
  have hid := logMT_eval hC ι x y hx f hn hy0 hy ζ a b G B B₁ NW hu hxa hfx
  have hM0 : evalE ι x y (toB (logMT f n ζ a b G B B₁ NW).1) ≠ 0 := by
    show evalE ι x y (toB (smulB _ (prodB _))) ≠ 0
    rw [evalE_smulB, exC_prodP, evalE_prodB, List.map_map, prod_finRange]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hxa i)
      (Finset.prod_ne_zero_iff.mpr fun j _ ↦ hu j)
  rw [hid, ← mul_assoc] at hsnd
  have hv := mul_left_cancel₀ (mul_ne_zero hM0 hfx) hsnd
  set w : Fin (dim F) → E := fun j ↦ evalE ι x y (toB (NW j).2) /
    ∏ i, (x - algebraMap Kc E (ι (a i))) ^ ((NW j).1 * negJ n ζ a b G j i)
  have hw0 : ∀ j, w j ≠ 0 := fun j ↦ div_ne_zero (hu j)
    (Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (hxa i))
  set l : List (E × E) := (List.finRange (dim F)).map fun j ↦
    (algebraMap Kc E (ι (cJ n ζ a b G j (NW j).1)), w j)
  have heq : integrandE ι x y f B B₁ a G = (valB ι x y cs basis)′ +
      (l.map fun p ↦ p.1 * logDeriv p.2).sum := by
    rw [List.map_map, sum_finRange, hv, integrandE]
    simp only [Function.comp_apply, w]
    ring
  rw [heq]
  refine hasElementaryIntegral_of_liouville_form _ _ fun p hp ↦ ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
  exact ⟨by rw [deriv_algebraMap, hC, map_zero], hw0 j⟩

end Sound

end Sup
