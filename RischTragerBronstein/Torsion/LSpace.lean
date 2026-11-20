import RischTragerBronstein.Torsion.Exact
import RischTragerBronstein.Torsion.KernelField
import RischTragerBronstein.Torsion.IntBasis

/-!
# The spaces `L(M ∞ₓ)` in integral-basis coordinates (any characteristic)

A *basis* is given by numerators `Bⱼ ∈ C[x][Y]` (`deg_Y Bⱼ ≤ j`, non-zero `Y^j`-coefficient) and a
common denominator `D`: `wⱼ = Bⱼ(x, y)/D(x)`. With coordinates `c : Fin n → C[X]` the function is
`elt c = ∑ cⱼ(x) wⱼ = Ψ(c)(x, y)/D(x)` (`Ψ(c) = PsiC B c`).

`IsIntBasis`: the `wⱼ` are regular at all finite branches, have pole order `≤ δⱼ` above infinity,
and are locally independent above every point and (reduced) at infinity. Then:

* `span_basis`, `elt_eq_zero`: the `wⱼ` form a basis of the function field over `C(x)`;
* `regular_elt`, `inf_elt`: `elt c` is regular at finite branches, with pole order `≤ M` above
  infinity when `deg cⱼ + δⱼ ≤ M`;
* `lspace_complete`: conversely, every such function is `elt c` with `deg cⱼ + δⱼ ≤ M`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section LSpace

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

lemma lowerBd_of_le_order (z : LaurentSeries K) (m : ℤ) (h : m ≤ z.order) : LowerBd z m :=
  fun _ hk ↦ HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hk h)

omit [Algebra C K] in
lemma order_nonneg_of_lowerBd' (z : LaurentSeries K) (hz : LowerBd z 0) : 0 ≤ z.order := by
  by_cases h0 : z = 0
  · rw [h0, HahnSeries.order_zero]
  by_contra hneg
  push Not at hneg
  exact HahnSeries.coeff_order_eq_zero.not.mpr h0 (hz _ hneg)

namespace CurveData

variable (S : CurveData C L)

/-- `P(x)` in the function field. -/
noncomputable def polyF (P : C[X]) : C⟮S.x⟯⟮S.y⟯ :=
  letI := algebraAdjoinSimple (F := C) S.x
  algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (algebraMap C[X] C⟮S.x⟯ P)

lemma coe_polyF (P : C[X]) : (S.polyF P : L) = aeval S.x P := by
  letI := algebraAdjoinSimple (F := C) S.x
  show ((algebraMap C[X] C⟮S.x⟯ P : C⟮S.x⟯) : L) = _
  rw [algebraMap_adjoinSimple]

lemma polyF_ne_zero {P : C[X]} (hP : P ≠ 0) : S.polyF P ≠ 0 := by
  intro h
  have h1 := congrArg Subtype.val h
  rw [coe_polyF] at h1
  exact hP (transcendental_iff.mp S.htr P h1)

lemma embG_polyF (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) (P : C[X]) :
    S.embG g hg Y hY (S.polyF P) = g P := by
  rw [polyF, S.embG_algebraMap, S.embXG_algebraMap]

@[simp] lemma polyF_zero : S.polyF 0 = 0 := by simp [polyF]

lemma coe_evT' (W : C[X][X]) : ((S.evT W : C⟮S.x⟯⟮S.y⟯) : L) = S.evXY W := S.coe_evT W

/-- The function `W(x, y)/Q(x)`. -/
noncomputable def fnWQ (W : C[X][X]) (Q : C[X]) : C⟮S.x⟯⟮S.y⟯ := S.evT W * (S.polyF Q)⁻¹

lemma coe_fnWQ (W : C[X][X]) (Q : C[X]) :
    (S.fnWQ W Q : L) = S.evXY W * (aeval S.x Q)⁻¹ := by
  rw [fnWQ, IntermediateField.coe_mul, IntermediateField.coe_inv, S.coe_evT, coe_polyF]

lemma fnWQ_mul (W : C[X][X]) (Q : C[X]) (hQ : Q ≠ 0) :
    (S.fnWQ W Q : L) * aeval S.x Q = S.evXY W := by
  have h : aeval S.x Q ≠ 0 := by rw [← coe_polyF]; exact fun h ↦ S.polyF_ne_zero hQ (Subtype.ext h)
  rw [coe_fnWQ, mul_assoc, inv_mul_cancel₀ h, mul_one]

lemma embG_fnWQ (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) (W : C[X][X]) (Q : C[X]) :
    S.embG g hg Y hY (S.fnWQ W Q) = (W.map g).eval Y * (g Q)⁻¹ := by
  rw [fnWQ, map_mul, map_inv₀, S.embG_evT, S.embG_polyF]

variable {S}

/-- The function with coordinates `c`: `∑ cⱼ(x) wⱼ`. -/
noncomputable def elt (B : Fin S.F.natDegree → C[X][X]) (D : C[X])
    (c : Fin S.F.natDegree → C[X]) : C⟮S.x⟯⟮S.y⟯ :=
  ∑ j, S.polyF (c j) * S.fnWQ (B j) D

lemma evXY_PsiC (B : Fin S.F.natDegree → C[X][X]) (c : Fin S.F.natDegree → C[X]) :
    S.evXY (PsiC B c) = ∑ j, aeval S.x (c j) * S.evXY (B j) := by
  simp only [PsiC, evXY, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, eval_finsetSum,
    eval_mul, eval_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

lemma elt_eq_fnWQ (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (c : Fin S.F.natDegree → C[X]) :
    S.elt B D c = S.fnWQ (PsiC B c) D := by
  apply Subtype.ext
  rw [coe_fnWQ, evXY_PsiC, elt, IntermediateField.coe_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [IntermediateField.coe_mul, coe_polyF, coe_fnWQ]; ring

lemma embG_elt (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (c : Fin S.F.natDegree → C[X])
    (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) :
    S.embG g hg Y hY (S.elt B D c) = ∑ j, g (c j) * S.embG g hg Y hY (S.fnWQ (B j) D) := by
  rw [elt, map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [map_mul, S.embG_polyF]

lemma elt_add (B : Fin S.F.natDegree → C[X][X]) (D : C[X]) (c c' : Fin S.F.natDegree → C[X]) :
    S.elt B D (c + c') = S.elt B D c + S.elt B D c' := by
  simp only [elt, Pi.add_apply, ← Finset.sum_add_distrib, ← add_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  apply Subtype.ext
  rw [IntermediateField.coe_add, coe_polyF, coe_polyF, coe_polyF, map_add]

variable (S)

/-- A triangular basis has a non-zero determinant. -/
lemma det_of_tri {n : ℕ} (B : Fin n → C[X][X]) (tri : ∀ j, (B j).natDegree ≤ (j : ℕ))
    (lead : ∀ j, (B j).coeff j ≠ 0) :
    (Matrix.of fun (i j : Fin n) ↦ (B j).coeff i).det ≠ 0 := by
  rw [Matrix.det_of_upperTriangular (fun i j (hij : j < i) ↦ by
    simp only [Matrix.of_apply]
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (tri j) hij))]
  exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ by simpa using lead j

/-- **Integral bases**: regularity, pole orders `δⱼ` at infinity, local independence. -/
structure IsIntBasis (K : Type*) [Field K] [Algebra C K] (B : Fin S.F.natDegree → C[X][X])
    (D : C[X]) (δ : Fin S.F.natDegree → ℕ) : Prop where
  hD : D ≠ 0
  deg : ∀ j, (B j).natDegree < S.F.natDegree
  det : (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (B j).coeff i).det ≠ 0
  reg : ∀ j, S.RegularFinite K (S.fnWQ (B j) D)
  inf : ∀ j (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) (r : LaurentSeries K)
    (hr : r ∈ l), LowerBd (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) r
      (S.root_of_mem hl hr) (S.fnWQ (B j) D)) (-((N * δ j : ℕ) : ℤ))
  ind : ∀ a : K, ∃ N, ∃ hN : 0 < N, ∃ r : Fin S.F.natDegree → LaurentSeries K,
    ∃ hs : S.F.map (branchSub N a) = ∏ k, (X - Polynomial.C (r k)),
      S.LocIndep (fun j ↦ S.fnWQ (B j) D) N hN a r hs
  indInf : ∃ N, ∃ hN : 0 < N, ∃ r : Fin S.F.natDegree → LaurentSeries K,
    ∃ hs : S.F.map (infSub N) = ∏ k, (X - Polynomial.C (r k)),
      S.LocIndepInf (fun j ↦ S.fnWQ (B j) D) δ N hN r hs

variable {S}

lemma list_of_fin {g : C[X] →+* LaurentSeries K} {r : Fin S.F.natDegree → LaurentSeries K}
    (hs : S.F.map g = ∏ k, (X - Polynomial.C (r k))) :
    S.F.map g = ((List.ofFn r).map fun r ↦ X - Polynomial.C r).prod := by
  rw [hs, List.map_ofFn, List.prod_ofFn]; rfl

lemma evXY_eq_sum (W : C[X][X]) (m : ℕ) (hm : W.natDegree < m) :
    S.evXY W = ∑ i ∈ Finset.range m, aeval S.x (W.coeff i) * S.y ^ i := by
  rw [evXY, eval_eq_sum_range' (lt_of_le_of_lt natDegree_map_le hm)]
  simp only [coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

/-- The `wⱼ` span the function field over `C(x)`. -/
theorem span_basis {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} (hD : D ≠ 0)
    (deg : ∀ j, (B j).natDegree < S.F.natDegree)
    (det : (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (B j).coeff i).det ≠ 0) (z : C⟮S.x⟯⟮S.y⟯) :
    ∃ q : Fin S.F.natDegree → C⟮S.x⟯,
      z = ∑ j, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (q j) * S.fnWQ (B j) D := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  set V := Submodule.span C⟮S.x⟯ (Set.range fun j ↦ S.fnWQ (B j) D) with hV
  set gen : C⟮S.x⟯⟮S.y⟯ := AdjoinSimple.gen C⟮S.x⟯ S.y with hgen
  have hgenL : (gen : L) = S.y := rfl
  have hpolyF : ∀ P, S.polyF P = algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (algebraMap C[X] C⟮S.x⟯ P) :=
    fun _ ↦ rfl
  have hsmul : ∀ (P : C[X]) (v : C⟮S.x⟯⟮S.y⟯), v ∈ V → S.polyF P * v ∈ V := fun P v hv ↦ by
    rw [hpolyF, ← Algebra.smul_def]; exact V.smul_mem _ hv
  have hdiv : ∀ (P : C[X]) (v : C⟮S.x⟯⟮S.y⟯), P ≠ 0 → S.polyF P * v ∈ V → v ∈ V := by
    intro P v hP h
    have hP' : algebraMap C[X] C⟮S.x⟯ P ≠ 0 := by
      intro h0; apply S.polyF_ne_zero hP; rw [hpolyF, h0, map_zero]
    have := V.smul_mem (algebraMap C[X] C⟮S.x⟯ P)⁻¹ h
    rwa [hpolyF, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hP', one_smul] at this
  have hsum : ∀ (s : Finset ℕ) (f : ℕ → C[X]) (e : ℕ → ℕ), (∀ i ∈ s, gen ^ e i ∈ V) →
      ∑ i ∈ s, S.polyF (f i) * gen ^ e i ∈ V := fun s f e h ↦
    V.sum_mem fun i hi ↦ hsmul _ _ (h i hi)
  -- every power of `y` lies in the span
  have hpow : ∀ k, gen ^ k ∈ V := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases hk : k < S.F.natDegree
      · set M : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C[X] :=
          Matrix.of fun i j ↦ (B j).coeff i with hM
        set jk : Fin S.F.natDegree := ⟨k, hk⟩
        have hcoef : ∀ i : Fin S.F.natDegree,
            ∑ j, (B j).coeff i * M.adjugate j jk = if i = jk then M.det else 0 := by
          intro i
          have := congrFun (congrFun (Matrix.mul_adjugate M) i) jk
          rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at this
          calc ∑ j, (B j).coeff i * M.adjugate j jk = ∑ j, M i j * M.adjugate j jk := rfl
            _ = M.det * (if i = jk then 1 else 0) := this
            _ = _ := by split_ifs <;> simp
        have hid : S.polyF M.det * gen ^ k =
            ∑ j, S.polyF (M.adjugate j jk * D) * S.fnWQ (B j) D := by
          apply Subtype.ext
          simp only [MulMemClass.coe_mul, AddSubmonoidClass.coe_finset_sum,
            SubmonoidClass.coe_pow, coe_polyF, hgenL]
          have e1 : ∀ j, aeval S.x (M.adjugate j jk * D) * (S.fnWQ (B j) D : L) =
              ∑ i : Fin S.F.natDegree, aeval S.x ((B j).coeff i * M.adjugate j jk) * S.y ^ (i : ℕ) := by
            intro j
            rw [map_mul, mul_assoc, mul_comm (aeval S.x D), S.fnWQ_mul _ _ hD,
              evXY_eq_sum (B j) S.F.natDegree (deg j),
              ← Fin.sum_univ_eq_sum_range (fun i ↦ aeval S.x ((B j).coeff i) * S.y ^ i), Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [map_mul]; ring
          rw [Finset.sum_congr rfl fun j _ ↦ e1 j, Finset.sum_comm]
          simp only [← Finset.sum_mul, ← map_sum, hcoef]
          rw [Finset.sum_eq_single jk (fun i _ hi ↦ by rw [if_neg hi, map_zero, zero_mul])
            (fun h ↦ absurd (Finset.mem_univ _) h), if_pos rfl]
        refine hdiv _ _ det ?_
        rw [hid]
        exact V.sum_mem fun j _ ↦ hsmul _ _ (Submodule.subset_span ⟨j, rfl⟩)
      · push_neg at hk
        have hid : gen ^ k = -∑ i ∈ Finset.range S.F.natDegree,
            S.polyF (S.F.coeff i) * gen ^ (k - S.F.natDegree + i) := by
          apply Subtype.ext
          simp only [NegMemClass.coe_neg, MulMemClass.coe_mul, AddSubmonoidClass.coe_finset_sum,
            SubmonoidClass.coe_pow, coe_polyF, hgenL]
          have h0 := S.evXY_F
          rw [evXY_eq_sum S.F (S.F.natDegree + 1) (Nat.lt_succ_self _), Finset.sum_range_succ,
            S.monic.coeff_natDegree, map_one, one_mul] at h0
          have e : S.y ^ k = S.y ^ (k - S.F.natDegree) * S.y ^ S.F.natDegree := by rw [← pow_add, Nat.sub_add_cancel hk]
          rw [e, eq_neg_of_add_eq_zero_right h0, mul_neg, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [pow_add]; ring
        rw [hid]
        exact V.neg_mem (hsum _ _ _ fun i hi ↦ ih _ (by
          have := Finset.mem_range.mp hi; omega))
  -- a general element
  obtain ⟨W, Q, hQ, hWQ⟩ := S.exists_repr z
  have hzV : S.polyF Q * z ∈ V := by
    have hid : S.polyF Q * z =
        ∑ i ∈ Finset.range (W.natDegree + 1), S.polyF (W.coeff i) * gen ^ i := by
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, AddSubmonoidClass.coe_finset_sum, SubmonoidClass.coe_pow,
        coe_polyF, hgenL]
      rw [mul_comm, hWQ, evXY_eq_sum W _ (Nat.lt_succ_self _)]
    rw [hid]
    exact hsum _ _ _ fun i _ ↦ hpow i
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun C⟮S.x⟯).mp (hdiv _ _ hQ hzV)
  exact ⟨q, by rw [← hq]; simp only [Algebra.smul_def]⟩

/-- The coordinates are unique. -/
theorem elt_eq_zero {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} (hD : D ≠ 0)
    (deg : ∀ j, (B j).natDegree < S.F.natDegree)
    (det : (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (B j).coeff i).det ≠ 0)
    (c : Fin S.F.natDegree → C[X]) (h : S.elt B D c = 0) : c = 0 := by
  classical
  have hW : S.evXY (PsiC B c) = 0 := by
    have := S.fnWQ_mul (PsiC B c) D hD
    rw [← elt_eq_fnWQ, h] at this
    rw [← this]; simp
  have hdeg : (PsiC B c).natDegree < S.F.natDegree := by
    have hpos : 0 < S.F.natDegree := Nat.pos_of_ne_zero S.natDegree_F_ne_zero
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := S.F.natDegree - 1)
      fun j _ ↦ ?_) (by omega)
    refine (natDegree_C_mul_le _ _).trans ?_
    have := deg j; omega
  have hP : PsiC B c = 0 := S.irr _ hdeg hW
  refine Matrix.eq_zero_of_mulVec_eq_zero det ?_
  funext i
  have hcoef := congrArg (fun P : C[X][X] ↦ P.coeff i) hP
  simp only [PsiC, finset_sum_coeff, coeff_C_mul, Polynomial.coeff_zero] at hcoef
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
  rw [← hcoef]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

lemma elt_injective {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} (hD : D ≠ 0)
    (deg : ∀ j, (B j).natDegree < S.F.natDegree)
    (det : (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (B j).coeff i).det ≠ 0)
    (c c' : Fin S.F.natDegree → C[X]) (h : S.elt B D c = S.elt B D c') : c = c' := by
  have h1 : S.elt B D (c + (-1 : C[X]) • c') = 0 := by
    rw [elt_add, h, ← elt_add]
    have : c' + (-1 : C[X]) • c' = 0 := by ext1 j; simp
    rw [this]; simp [elt]
  have := elt_eq_zero hD deg det _ h1
  ext1 j
  have := congrFun this j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  linear_combination this

/-- Functions with polynomial coordinates are regular at all finite branches. -/
theorem regular_elt {B : Fin S.F.natDegree → C[X][X]} {D : C[X]}
    (reg : ∀ j, S.RegularFinite K (S.fnWQ (B j) D)) (c : Fin S.F.natDegree → C[X]) :
    S.RegularFinite K (S.elt B D c) := by
  intro a N hN l hl r hr
  refine order_nonneg_of_lowerBd' _ ?_
  rw [embG_elt]
  refine lowerBd_sum _ _ fun j _ ↦ ?_
  have hb : LowerBd (branchSub (K := K) N a (c j)) 0 := by
    rw [branchSub_apply]; intro k hk; exact LaurentSeries.coeff_ofPS_neg _ hk
  have := hb.mul
    (lowerBd_of_le_order _ 0 (reg j a N hN l hl r hr))
  simpa using this

/-- Pole orders above infinity from the degrees of the coordinates. -/
theorem inf_elt {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} {δ : Fin S.F.natDegree → ℕ}
    (inf : ∀ j (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) (r : LaurentSeries K)
      (hr : r ∈ l), LowerBd (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) r
        (S.root_of_mem hl hr) (S.fnWQ (B j) D)) (-((N * δ j : ℕ) : ℤ)))
    (c : Fin S.F.natDegree → C[X]) (M : ℕ) (hc : ∀ j, c j ≠ 0 → (c j).natDegree + δ j ≤ M)
    (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) (r : LaurentSeries K)
    (hr : r ∈ l) :
    LowerBd (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) r
      (S.root_of_mem hl hr) (S.elt B D c)) (-((N * M : ℕ) : ℤ)) := by
  rw [embG_elt]
  refine lowerBd_sum _ _ fun j _ ↦ ?_
  by_cases hcj : c j = 0
  · rw [hcj, map_zero, zero_mul]; exact lowerBd_zero _
  have h := (lowerBd_infSub (K := K) N (Nat.pos_of_ne_zero hN) (c j)).mul (inf j N hN l hl r hr)
  refine h.mono ?_
  have := hc j hcj
  have e : ((N * M : ℕ) : ℤ) ≥ ((N * (c j).natDegree : ℕ) : ℤ) + ((N * δ j : ℕ) : ℤ) := by
    push_cast; nlinarith
  linarith

variable [IsAlgClosed K]

/-- **Completeness**: every function regular at finite branches with pole order `≤ M` above
infinity has polynomial coordinates with `deg cⱼ + δⱼ ≤ M`. -/
theorem lspace_complete {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} {δ : Fin S.F.natDegree → ℕ}
    (hB : S.IsIntBasis K B D δ) (z : C⟮S.x⟯⟮S.y⟯) (hz : S.RegularFinite K z) (M : ℕ)
    (hzi : ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) (r : LaurentSeries K)
      (hr : r ∈ l), LowerBd (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) r
        (S.root_of_mem hl hr) z) (-((N * M : ℕ) : ℤ))) :
    ∃ c : Fin S.F.natDegree → C[X], z = S.elt B D c ∧ ∀ j, c j ≠ 0 → (c j).natDegree + δ j ≤ M := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  obtain ⟨q, hq⟩ := span_basis hB.hD hB.deg hB.det z
  have hP := S.coords_poly_of_indep (K := K) (fun j ↦ S.fnWQ (B j) D) (fun a ↦ by
      obtain ⟨N, hN, r, hs, hI⟩ := hB.ind a
      refine ⟨N, hN, r, hs, hI, fun j k ↦ ?_⟩
      exact lowerBd_of_le_order _ 0 (hB.reg j a N hN.ne' _ (list_of_fin hs) (r k)
        (List.mem_ofFn.mpr ⟨k, rfl⟩)))
    z hz q hq
  choose c hc using hP
  have hzc : z = S.elt B D c := by
    rw [hq, elt]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [← hc j]; rfl
  refine ⟨c, hzc, ?_⟩
  obtain ⟨N, hN, r, hs, hI⟩ := hB.indInf
  refine S.natDegree_le_of_indepInf (fun j ↦ S.fnWQ (B j) D) δ N hN r hs hI
    (fun j k ↦ hB.inf j N hN.ne' _ (list_of_fin hs) (r k) (List.mem_ofFn.mpr ⟨k, rfl⟩)) c M
    (fun k ↦ ?_)
  have := hzi N hN.ne' _ (list_of_fin hs) (r k) (List.mem_ofFn.mpr ⟨k, rfl⟩)
  rw [hzc, elt] at this
  exact this

end CurveData

end LSpace

end Curves
