import RischTragerBronstein.Curves.Fibre
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Integrality from regularity along all finite branches

* `exists_repr`: every `f ∈ C⟮x⟯⟮y⟯` is `W(x, y) / Q(x)` with `W ∈ C[x][Y]`, `Q ≠ 0`;
* `dvd_of_branch_order`: `B ∣ A` in `C[x]` as soon as `A/B` has no pole along `x ↦ a + Tᴺ` for all
  `a ∈ K`;
* `integral_of_regular`: if `f` has no pole along any branch above any finite point, then `f`
  satisfies a monic equation over `C[x]` (through the resultant `Res_Y(F(Y), Q(x) Z − W(x, Y))`,
  which maps to `Q̂ⁿ ∏ⱼ (Z − fⱼ)` along the branches `fⱼ` above each point).
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential

section Div

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [IsAlgClosed K]

/-- **Divisibility from orders** along `x ↦ a + Tᴺ`. -/
theorem dvd_of_branch_order (A B : C[X]) (hB : B ≠ 0)
    (h : ∀ a : K, ∃ N, N ≠ 0 ∧ (branchSub N a B).order ≤ (branchSub N a A).order) : B ∣ A := by
  classical
  by_cases hA : A = 0
  · rw [hA]; exact dvd_zero B
  rw [← map_dvd_map' (algebraMap C K)]
  have hB' : B.map (algebraMap C K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hB
  have hA' : A.map (algebraMap C K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap C K).injective).mpr hA
  rw [IsAlgClosed.dvd_iff_roots_le_roots hB' hA', Multiset.le_iff_count]
  intro a
  rw [count_roots, count_roots]
  obtain ⟨N, hN, hle⟩ := h a
  rw [order_branchSub N (Nat.pos_of_ne_zero hN) a B hB,
    order_branchSub N (Nat.pos_of_ne_zero hN) a A hA] at hle
  have hle' : N * (B.map (algebraMap C K)).rootMultiplicity a ≤
      N * (A.map (algebraMap C K)).rootMultiplicity a := by exact_mod_cast hle
  exact Nat.le_of_mul_le_mul_left hle' (Nat.pos_of_ne_zero hN)

end Div

section Laurent

variable {K : Type*} [Field K]

lemma exists_ofPS_of_order_nonneg (s : LaurentSeries K) (h : 0 ≤ s.order) :
    ∃ t : PowerSeries K, s = ofPowerSeries ℤ K t := by
  refine ⟨PowerSeries.X ^ s.order.toNat * s.powerSeriesPart, ?_⟩
  conv_lhs => rw [← s.single_order_mul_powerSeriesPart]
  rw [map_mul, ofPowerSeries_X_pow, Int.toNat_of_nonneg h]

lemma order_ofPS_nonneg (t : PowerSeries K) : 0 ≤ (ofPowerSeries ℤ K t).order := by
  by_cases ht : ofPowerSeries ℤ K t = 0
  · rw [ht, HahnSeries.order_zero]
  by_contra hneg
  push Not at hneg
  have := HahnSeries.coeff_order_eq_zero.not.mpr ht
  rw [LaurentSeries.coeff_ofPS_neg _ hneg] at this
  exact this rfl

lemma exists_prod_map (l : List (LaurentSeries K)) (hl : ∀ s ∈ l, 0 ≤ s.order) :
    ∃ P : (PowerSeries K)[X],
      (l.map fun s ↦ X - Polynomial.C s).prod = P.map (ofPowerSeries ℤ K) := by
  induction l with
  | nil => exact ⟨1, by simp⟩
  | cons s l ih =>
    obtain ⟨P, hP⟩ := ih fun s' hs' ↦ hl s' (List.mem_cons_of_mem _ hs')
    obtain ⟨t, ht⟩ := exists_ofPS_of_order_nonneg s (hl s List.mem_cons_self)
    refine ⟨(X - Polynomial.C t) * P, ?_⟩
    rw [List.map_cons, List.prod_cons, hP, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, ht]

lemma order_coeff_prod_nonneg (l : List (LaurentSeries K)) (hl : ∀ s ∈ l, 0 ≤ s.order) (k : ℕ) :
    0 ≤ ((l.map fun s ↦ X - Polynomial.C s).prod.coeff k).order := by
  obtain ⟨P, hP⟩ := exists_prod_map l hl
  rw [hP, coeff_map]
  exact order_ofPS_nonneg _

end Laurent

section Repr

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L)

/-- **Representation**: `f = W(x, y) / Q(x)`. -/
theorem exists_repr (f : C⟮S.x⟯⟮S.y⟯) :
    ∃ (W : C[X][X]) (Q : C[X]), Q ≠ 0 ∧ (f : L) * aeval S.x Q = S.evXY W := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  set pb := IntermediateField.adjoin.powerBasis S.isIntegral
  have hgen : pb.gen = AdjoinSimple.gen C⟮S.x⟯ S.y := IntermediateField.adjoin.powerBasis_gen _
  set c : Fin pb.dim → C⟮S.x⟯ := fun i ↦ pb.basis.repr f i
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors C[X])
    Finset.univ c
  choose P hP using fun i ↦ hb i (Finset.mem_univ i)
  refine ⟨∑ i : Fin pb.dim, Polynomial.C (P i) * X ^ (i : ℕ), b,
    nonZeroDivisors.ne_zero b.2, ?_⟩
  have hf := pb.basis.sum_repr f
  have hbx : aeval S.x (b : C[X]) = ((algebraMap C[X] C⟮S.x⟯ b : C⟮S.x⟯) : L) :=
    (algebraMap_adjoinSimple S.x _).symm
  rw [evXY, Polynomial.map_sum, eval_finsetSum]
  conv_lhs => rw [← hf]
  rw [IntermediateField.coe_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, eval_mul,
    eval_C, eval_pow, eval_X, PowerBasis.coe_basis, hgen, Algebra.smul_def,
    IntermediateField.coe_mul, IntermediateField.coe_pow, AdjoinSimple.coe_gen, hbx]
  have hPi := hP i
  rw [Algebra.smul_def] at hPi
  have hPi' : aeval S.x (P i) = ((algebraMap C[X] C⟮S.x⟯ b : C⟮S.x⟯) : L) * (c i : L) := by
    rw [← algebraMap_adjoinSimple S.x (P i), hPi]; rfl
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hPi']
  show (((algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (c i) : C⟮S.x⟯⟮S.y⟯) : L)) * S.y ^ (i : ℕ) *
    ((algebraMap C[X] C⟮S.x⟯ b : C⟮S.x⟯) : L) = _
  have : ((algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (c i) : C⟮S.x⟯⟮S.y⟯) : L) = (c i : L) := rfl
  rw [this]
  ring

end CurveData

end Repr

section ResList

variable {R : Type*} [CommRing R] [Nontrivial R]

lemma list_prod_X_sub_C (l : List R) :
    ((l.map fun r ↦ X - Polynomial.C r).prod).Monic ∧
      ((l.map fun r ↦ X - Polynomial.C r).prod).natDegree = l.length := by
  induction l with
  | nil => simp
  | cons r l ih =>
    rw [List.map_cons, List.prod_cons]
    refine ⟨(monic_X_sub_C r).mul ih.1, ?_⟩
    rw [(monic_X_sub_C r).natDegree_mul ih.1, natDegree_X_sub_C, ih.2, List.length_cons]
    ring

/-- The resultant of a split monic polynomial. -/
lemma list_prod_scale {α : Type*} (l : List α) (c : R) (w v : α → R)
    (h : ∀ r ∈ l, w r = v r * c) :
    (l.map fun r ↦ Polynomial.C c * X - Polynomial.C (w r)).prod =
      Polynomial.C (c ^ l.length) * (l.map fun r ↦ X - Polynomial.C (v r)).prod := by
  induction l with
  | nil => simp
  | cons r l ih =>
    rw [List.map_cons, List.prod_cons, ih fun r' hr' ↦ h r' (List.mem_cons_of_mem _ hr'),
      h r List.mem_cons_self, List.map_cons, List.prod_cons, List.length_cons, pow_succ,
      map_mul, map_mul]
    ring

lemma resultant_list_prod (l : List R) (G : R[X]) (n : ℕ) (hn : G.natDegree ≤ n) :
    resultant (l.map fun r ↦ X - Polynomial.C r).prod G l.length n =
      (l.map fun r ↦ G.eval r).prod := by
  induction l with
  | nil => simp
  | cons r l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, List.length_cons,
      show l.length + 1 = (X - Polynomial.C r).natDegree +
        ((l.map fun r ↦ X - Polynomial.C r).prod).natDegree by
          rw [natDegree_X_sub_C, (list_prod_X_sub_C l).2]; ring,
      resultant_mul_left _ _ _ _ hn, natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ hn,
      (list_prod_X_sub_C l).2, ih]

end ResList

section Res

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

/-- `Q Z − W(Y)` as a polynomial in `Y` over `C[x][Z]`. -/
noncomputable def resG (W : C[X][X]) (Q : C[X]) : C[X][X][X] :=
  Polynomial.C (Polynomial.C Q * Polynomial.X : C[X][X]) -
    W.map (Polynomial.C : C[X] →+* C[X][X])

lemma resG_natDegree (W : C[X][X]) (Q : C[X]) : (resG W Q).natDegree ≤ W.natDegree := by
  refine (natDegree_sub_le _ _).trans (max_le ?_ natDegree_map_le)
  rw [natDegree_C]; exact Nat.zero_le _

namespace CurveData

variable (S : CurveData C L)

lemma natDegree_F_ne_zero : S.F.natDegree ≠ 0 := by
  intro h
  have h1 := Polynomial.eq_one_of_monic_natDegree_zero S.monic h
  have h2 := S.root
  rw [h1, Polynomial.map_one, eval_one] at h2
  exact one_ne_zero h2

/-- `Res_Y(F(Y), Q Z − W(Y)) ∈ C[x][Z]`. -/
noncomputable def resP (W : C[X][X]) (Q : C[X]) : C[X][X] :=
  resultant (S.F.map (Polynomial.C : C[X] →+* C[X][X])) (resG W Q) S.F.natDegree W.natDegree

/-- **`f = W/Q` is a root of the resultant.** -/
theorem resP_eval (f : L) (W : C[X][X]) (Q : C[X]) (hf : f * aeval S.x Q = S.evXY W) :
    (S.resP W Q).eval₂ (aeval S.x).toRingHom f = 0 := by
  obtain ⟨p, q, -, -, e⟩ := exists_mul_add_mul_eq_C_resultant
    (S.F.map (Polynomial.C : C[X] →+* C[X][X])) (resG W Q) (m := S.F.natDegree)
    (n := W.natDegree) natDegree_map_le (resG_natDegree W Q) (Or.inl S.natDegree_F_ne_zero)
  set ψ : C[X][X] →+* L := eval₂RingHom (aeval S.x).toRingHom f with hψ
  have hψC : ψ.comp (Polynomial.C : C[X] →+* C[X][X]) = (aeval S.x).toRingHom := by
    ext P <;> simp [hψ]
  have h1 : eval₂ ψ S.y (S.F.map (Polynomial.C : C[X] →+* C[X][X])) = 0 := by
    rw [eval₂_map, hψC, ← eval_map]; exact S.root
  have h2 : eval₂ ψ S.y (resG W Q) = 0 := by
    rw [resG, eval₂_sub, eval₂_C, eval₂_map, hψC, ← eval_map, ← evXY, ← hf, hψ,
      coe_eval₂RingHom, eval₂_mul, eval₂_C, eval₂_X]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    ring
  have h := congrArg (eval₂RingHom ψ S.y) e
  simp only [map_add, map_mul, coe_eval₂RingHom, eval₂_C, h1, h2, zero_mul, add_zero] at h
  exact h.symm

variable {K : Type*} [Field K]

/-- **The resultant along a split fibre**: if `F(g, Y) = ∏ (Y − rⱼ)`, then
`Res(g) = ∏ⱼ (ĝ(Q) Z − W(g, rⱼ))`. -/
theorem resP_map (g : C[X] →+* LaurentSeries K) (l : List (LaurentSeries K))
    (hl : S.F.map g = (l.map fun r ↦ X - Polynomial.C r).prod) (W : C[X][X]) (Q : C[X]) :
    (S.resP W Q).map g =
      (l.map fun r ↦ Polynomial.C (g Q) * X - Polynomial.C ((W.map g).eval r)).prod := by
  classical
  have hθC : (mapRingHom g).comp (Polynomial.C : C[X] →+* C[X][X]) =
      (Polynomial.C : LaurentSeries K →+* (LaurentSeries K)[X]).comp g := by
    ext P <;> simp
  have hF : (S.F.map (Polynomial.C : C[X] →+* C[X][X])).map (mapRingHom g) =
      ((l.map Polynomial.C).map fun r ↦ X - Polynomial.C r).prod := by
    rw [Polynomial.map_map, hθC, ← Polynomial.map_map, hl, Polynomial.map_list_prod, List.map_map,
      List.map_map]
    congr 1
    refine List.map_congr_left fun r _ ↦ ?_
    simp
  have hlen : (l.map Polynomial.C).length = S.F.natDegree := by
    have := congrArg natDegree hl
    rw [S.monic.natDegree_map, (list_prod_X_sub_C l).2] at this
    rw [List.length_map, this]
  have hG : (resG W Q).map (mapRingHom g) = Polynomial.C (Polynomial.C (g Q) * X) -
      (W.map g).map Polynomial.C := by
    rw [resG, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_map, hθC,
      ← Polynomial.map_map]
    simp
  have hGdeg : ((resG W Q).map (mapRingHom g)).natDegree ≤ W.natDegree :=
    natDegree_map_le.trans (resG_natDegree W Q)
  rw [resP, ← coe_mapRingHom, ← resultant_map_map, hF, ← hlen,
    resultant_list_prod _ _ _ hGdeg, List.map_map]
  congr 1
  refine List.map_congr_left fun r _ ↦ ?_
  rw [Function.comp_apply, hG, eval_sub, eval_C, eval_map, eval₂_at_apply]
  rfl

end CurveData

end Res

section Main

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

lemma root_of_mem {g : C[X] →+* LaurentSeries K} {l : List (LaurentSeries K)}
    (hl : S.F.map g = (l.map fun r ↦ X - Polynomial.C r).prod) {r : LaurentSeries K}
    (hr : r ∈ l) : (S.F.map g).eval r = 0 := by
  rw [hl, eval_list_prod]
  exact List.prod_eq_zero (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, by simp⟩)

/-- **Regularity along all finite branches** (with coefficients in `K`). -/
def RegularFinite (K : Type*) [Field K] [Algebra C K] (f : C⟮S.x⟯⟮S.y⟯) : Prop :=
  ∀ (a : K) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (r : LaurentSeries K) (hr : r ∈ l),
    0 ≤ (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
      (S.root_of_mem hl hr) f).order

lemma embG_polyX (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) (Q : C[X]) (hQ : aeval S.x Q ∈ C⟮S.x⟯⟮S.y⟯) :
    S.embG g hg Y hY ⟨aeval S.x Q, hQ⟩ = g Q := by
  letI := algebraAdjoinSimple (F := C) S.x
  have e : (⟨aeval S.x Q, hQ⟩ : C⟮S.x⟯⟮S.y⟯) =
      algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (algebraMap C[X] C⟮S.x⟯ Q) :=
    Subtype.ext (by
      show aeval S.x Q = ((algebraMap C[X] C⟮S.x⟯ Q : C⟮S.x⟯) : L)
      rw [algebraMap_adjoinSimple])
  rw [e, S.embG_algebraMap, S.embXG_algebraMap]

lemma aeval_mem (Q : C[X]) : aeval S.x Q ∈ C⟮S.x⟯⟮S.y⟯ := by
  letI := algebraAdjoinSimple (F := C) S.x
  rw [← algebraMap_adjoinSimple (F := C) S.x Q]
  exact IntermediateField.algebraMap_mem _ _

/-- The branch values of `W(x, y)` for `f · Q(x) = W(x, y)`. -/
lemma eval_W_branch (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (Y : LaurentSeries K) (hY : (S.F.map g).eval Y = 0) (f : C⟮S.x⟯⟮S.y⟯) (W : C[X][X])
    (Q : C[X]) (hWQ : (f : L) * aeval S.x Q = S.evXY W) :
    (W.map g).eval Y = S.embG g hg Y hY f * g Q := by
  rw [← S.embG_evT g hg Y hY W, ← S.embG_polyX g hg Y hY Q (S.aeval_mem Q), ← map_mul]
  congr 1
  exact Subtype.ext (by rw [S.coe_evT, ← hWQ]; rfl)

variable [IsAlgClosed K]

/-- The data behind `integral_of_regular`: `f = W/Q`, `Res(W, Q) = Qⁿ M` with `M` monic
(given branch systems above every point). -/
theorem integral_of_regular_dataG (hB : S.HasBranches K) (f : C⟮S.x⟯⟮S.y⟯)
    (hreg : S.RegularFinite K f) :
    ∃ (W : C[X][X]) (Q : C[X]) (M : C[X][X]), Q ≠ 0 ∧ (f : L) * aeval S.x Q = S.evXY W ∧
      M.Monic ∧ S.resP W Q = Polynomial.C (Q ^ S.F.natDegree) * M ∧
      (M.map (aeval S.x).toRingHom).eval (f : L) = 0 := by
  classical
  obtain ⟨W, Q, hQ, hWQ⟩ := S.exists_repr f
  set n := S.F.natDegree with hn
  set P := S.resP W Q with hP
  -- the fibre above each point
  have hfib : ∀ a : K, ∃ N, N ≠ 0 ∧ ∃ Mf : (LaurentSeries K)[X], Mf.Monic ∧ Mf.natDegree = n ∧
      (∀ k, 0 ≤ (Mf.coeff k).order) ∧
      P.map (branchSub N a) = Polynomial.C (branchSub N a Q ^ n) * Mf := by
    intro a
    obtain ⟨N, hN, l0, hl0, hsplit⟩ := hB a
    obtain ⟨l, hl⟩ : ∃ l, l = l0.map (ofPowerSeries ℤ K) := ⟨_, rfl⟩
    have hsplit' : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod := by
      rw [hsplit, hl, List.map_map]; rfl
    have hinj := branchSub_injective (C := C) (K := K) N (Nat.pos_of_ne_zero hN) a
    obtain ⟨v, hv⟩ : ∃ v : LaurentSeries K → LaurentSeries K, ∀ r (hr : r ∈ l),
        v r = S.embG (branchSub N a) hinj r (S.root_of_mem hsplit' hr) f :=
      ⟨fun r ↦ if hr : r ∈ l then S.embG (branchSub N a) hinj r (S.root_of_mem hsplit' hr) f
        else 0, fun r hr ↦ by simp only [hr, dite_true]⟩
    have e : (l.map fun r ↦ X - Polynomial.C (v r)) = ((l.map v).map fun s ↦ X - Polynomial.C s) :=
      by rw [List.map_map]; rfl
    refine ⟨N, hN, (l.map fun r ↦ X - Polynomial.C (v r)).prod, by rw [e]; exact (list_prod_X_sub_C _).1,
      by rw [e, (list_prod_X_sub_C _).2, List.length_map, hl, List.length_map, hl0], ?_, ?_⟩
    · rw [e]
      refine order_coeff_prod_nonneg _ fun s hs ↦ ?_
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
      rw [hv r hr]
      exact hreg a N hN l hsplit' r hr
    · rw [hP, S.resP_map _ l hsplit' W Q]
      have hlen : l.length = n := by rw [hl, List.length_map, hl0]
      rw [list_prod_scale l _ _ v, hlen]
      intro r hr
      rw [hv r hr]
      exact S.eval_W_branch _ hinj r _ f W Q hWQ
  -- the coefficients of `P` are divisible by `Qⁿ`
  have hQn : Q ^ n ≠ 0 := pow_ne_zero _ hQ
  have hdiv : ∀ k, Q ^ n ∣ P.coeff k := by
    intro k
    by_cases hPk : P.coeff k = 0
    · rw [hPk]; exact dvd_zero _
    refine dvd_of_branch_order (K := K) _ _ hQn fun a ↦ ?_
    obtain ⟨N, hN, Mf, -, -, hord, hmap⟩ := hfib a
    have hinj := branchSub_injective (C := C) (K := K) N (Nat.pos_of_ne_zero hN) a
    refine ⟨N, hN, ?_⟩
    have hc := congrArg (fun p ↦ p.coeff k) hmap
    simp only [coeff_map, coeff_C_mul] at hc
    have hg0 : branchSub N a (P.coeff k) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hPk
    have hQ0 : branchSub N a Q ^ n ≠ 0 := pow_ne_zero _ ((map_ne_zero_iff _ hinj).mpr hQ)
    have hM0 : Mf.coeff k ≠ 0 := fun h0 ↦ hg0 (by rw [hc, h0, mul_zero])
    rw [hc, map_pow, HahnSeries.order_mul hQ0 hM0]
    have := hord k
    omega
  have hPn : P.coeff n = Q ^ n := by
    obtain ⟨N, hN, Mf, hMm, hMd, -, hmap⟩ := hfib 0
    have hinj := branchSub_injective (C := C) (K := K) N (Nat.pos_of_ne_zero hN) (0 : K)
    have hc := congrArg (fun p ↦ p.coeff n) hmap
    simp only [coeff_map, coeff_C_mul] at hc
    have h1 : Mf.coeff n = 1 := by rw [← hMd]; exact hMm.coeff_natDegree
    rw [h1, mul_one, ← map_pow] at hc
    exact hinj hc
  have hPhi : ∀ k, n < k → P.coeff k = 0 := by
    intro k hk
    obtain ⟨N, hN, Mf, -, hMd, -, hmap⟩ := hfib 0
    have hinj := branchSub_injective (C := C) (K := K) N (Nat.pos_of_ne_zero hN) (0 : K)
    have hc := congrArg (fun p ↦ p.coeff k) hmap
    simp only [coeff_map, coeff_C_mul] at hc
    rw [coeff_eq_zero_of_natDegree_lt (p := Mf) (by omega), mul_zero] at hc
    exact hinj (hc.trans (map_zero _).symm)
  choose d hd using hdiv
  set M : C[X][X] := ∑ k ∈ Finset.range (n + 1), Polynomial.C (d k) * X ^ k with hM
  have hMc : ∀ k, M.coeff k = if k ≤ n then d k else 0 := by
    intro k
    simp only [hM, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]
  have hPM : P = Polynomial.C (Q ^ n) * M := by
    refine Polynomial.ext fun k ↦ ?_
    rw [coeff_C_mul, hMc]
    split_ifs with hk
    · exact hd k
    · rw [mul_zero]; exact hPhi k (by omega)
  have hdn : d n = 1 := by
    have := hd n
    rw [hPn] at this
    exact (mul_eq_left₀ hQn).mp this.symm
  refine ⟨W, Q, M, hQ, hWQ, monic_of_natDegree_le_of_coeff_eq_one n
    (natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ by
      rw [hMc, if_neg (by exact_mod_cast not_le.mpr hk)])
    (by rw [hMc, if_pos le_rfl, hdn]), hPM, ?_⟩
  have h0 := S.resP_eval (f : L) W Q hWQ
  rw [← hP, hPM, eval₂_mul, eval₂_C] at h0
  have hQx : (aeval S.x).toRingHom (Q ^ n) ≠ 0 := by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow]
    exact pow_ne_zero _ (fun h ↦ S.htr ⟨Q, hQ, h⟩)
  rw [eval_map]
  exact (mul_eq_zero.mp h0).resolve_left hQx

/-- **Integrality from regularity**: if `f` has no pole along any branch above any finite point,
it satisfies a monic equation over `C[x]`. -/
theorem integral_of_regularG (hB : S.HasBranches K) (f : C⟮S.x⟯⟮S.y⟯)
    (hreg : S.RegularFinite K f) :
    ∃ M : C[X][X], M.Monic ∧ (M.map (aeval S.x).toRingHom).eval (f : L) = 0 := by
  obtain ⟨W, Q, M, -, -, hM, -, hev⟩ := S.integral_of_regular_dataG hB f hreg
  exact ⟨M, hM, hev⟩

variable [CharZero K]

theorem integral_of_regular_data (f : C⟮S.x⟯⟮S.y⟯) (hreg : S.RegularFinite K f) :
    ∃ (W : C[X][X]) (Q : C[X]) (M : C[X][X]), Q ≠ 0 ∧ (f : L) * aeval S.x Q = S.evXY W ∧
      M.Monic ∧ S.resP W Q = Polynomial.C (Q ^ S.F.natDegree) * M ∧
      (M.map (aeval S.x).toRingHom).eval (f : L) = 0 :=
  S.integral_of_regular_dataG S.hasBranches f hreg

theorem integral_of_regular (f : C⟮S.x⟯⟮S.y⟯) (hreg : S.RegularFinite K f) :
    ∃ M : C[X][X], M.Monic ∧ (M.map (aeval S.x).toRingHom).eval (f : L) = 0 :=
  S.integral_of_regularG S.hasBranches f hreg

end CurveData

end Main

end Curves
