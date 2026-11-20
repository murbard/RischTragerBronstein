import RischTragerBronstein.Mixed.NKUnitsInf

/-!
# S-units supported at infinity and above `x = 0`

Over an exponential level the logarithmic derivatives are regular at the places above `t = 0`, so
the logarithms of a Liouville form are *S-units* for `S` = the places at infinity and above `0`.
For such a unit the order sums satisfy `N₀ ∑_∞ ord + N ∑_0 ord = 0` (`unit_sum_inf0`, the norm is
`c xᵏ`), and when `x` and `m` further S-units are independent modulo constants, with
`m + 2` = (number of roots above infinity) + (number of roots above `0`), every S-unit is, up to
a power, a constant times a power product of `x` and the given units (`mem_pow_units_inf0`).
The linear algebra is the Cramer step `pow_units_cramer`, shared with `mem_pow_units_inf`.
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential GTors CPoly Sup

section UnitsInf0

variable {C L Kb : Type*} [Field C] [Field L] [Algebra C L] [Field Kb] [Algebra C Kb]
  [IsAlgClosed Kb] [CharZero Kb]

namespace CurveData

variable (S : CurveData C L)

set_option maxHeartbeats 1600000 in
/-- **The Cramer step**: given `k` independent elements `vᵢ` and `k` valuations `φₚ` such that a
power product of `w` and the `vᵢ` with vanishing orders is a constant, a power of `w` is a constant
times a power product of the `vᵢ`. -/
theorem pow_units_cramer {k : ℕ} (v : Fin k → C⟮S.x⟯⟮S.y⟯) (hv : ∀ i, v i ≠ 0)
    (w : C⟮S.x⟯⟮S.y⟯) (φ : Fin k → (C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries Kb))
    (hkey : ∀ (e0 : ℤ) (e : Fin k → ℤ),
      (∀ p, e0 * (φ p w).order + ∑ i, e i * (φ p (v i)).order = 0) →
      ∃ c : C, ((w ^ e0 * ∏ i, v i ^ e i : C⟮S.x⟯⟮S.y⟯) : L) = algebraMap C L c)
    (hind : ∀ a : Fin k → ℤ, (∃ c : C, ∏ i, (v i : L) ^ a i = algebraMap C L c) → a = 0) :
    ∃ (N' : ℤ) (a : Fin k → ℤ), N' ≠ 0 ∧ ∃ c : C,
      (w : L) ^ N' = algebraMap C L c * ∏ i, (v i : L) ^ a i := by
  classical
  set A : Matrix (Fin k) (Fin k) ℤ := fun i p ↦ (φ p (v i)).order with hA
  set b : Fin k → ℤ := fun p ↦ (φ p w).order with hb
  have hcoe : ∀ (e0 : ℤ) (e : Fin k → ℤ), ((w ^ e0 * ∏ i, v i ^ e i : C⟮S.x⟯⟮S.y⟯) : L) =
      (w : L) ^ e0 * ∏ i, (v i : L) ^ e i := fun e0 e ↦ by
    rw [IntermediateField.coe_mul, show ((w ^ e0 : C⟮S.x⟯⟮S.y⟯) : L) = (w : L) ^ e0 from
      map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val w e0, IntermediateField.coe_prod]
    congr 1
  by_cases hdet : A.det = 0
  · exfalso
    obtain ⟨a, ha0, hAa⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
      (show A.transpose.det = 0 by rw [Matrix.det_transpose]; exact hdet)
    obtain ⟨c, hc⟩ := hkey 0 a fun p ↦ by
      have := congrFun hAa p
      simp only [Matrix.mulVec, dotProduct, hA, Pi.zero_apply] at this
      rw [zero_mul, zero_add, ← this]
      exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    apply ha0
    apply hind a
    refine ⟨c, ?_⟩
    rw [← hc, hcoe, zpow_zero, one_mul]
  · set a : Fin k → ℤ := Matrix.mulVec (A.transpose).adjugate b with ha
    have hAa : Matrix.mulVec A.transpose a = A.det • b := by
      rw [ha, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.det_transpose, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    obtain ⟨c, hc⟩ := hkey A.det (fun i ↦ -a i) fun p ↦ by
      have := congrFun hAa p
      simp only [Matrix.mulVec, dotProduct, hA, Pi.smul_apply,
        smul_eq_mul] at this
      have e : ∑ i, -a i * (φ p (v i)).order = -(A.det * b p) := by
        rw [← this, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [neg_mul, mul_comm (a i)]; rfl
      rw [e, hb]; ring
    refine ⟨A.det, a, hdet, c, ?_⟩
    rw [hcoe] at hc
    have hprodne : ∏ i, (v i : L) ^ a i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦
      zpow_ne_zero _ (fun h ↦ hv i (Subtype.ext h))
    have e2 : ∏ i, (v i : L) ^ (-a i) = (∏ i, (v i : L) ^ a i)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun i _ ↦ zpow_neg _ _
    rw [e2] at hc
    rw [← hc, mul_assoc, inv_mul_cancel₀ hprodne, mul_one]

/-- The roots of a polynomial over an algebraically closed field: away from `0` the norm has the
multiplicities of `Qⁿ`, so its degree is `n deg Q + μ₀`. -/
lemma natDegree_of_mult (P Q : C[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (n : ℕ) (μ0 : ℤ)
    (hb : ∀ b : Kb, b ≠ 0 → (P.map (algebraMap C Kb)).rootMultiplicity b =
      n * (Q.map (algebraMap C Kb)).rootMultiplicity b)
    (h0 : ((P.map (algebraMap C Kb)).rootMultiplicity 0 : ℤ) =
      n * (Q.map (algebraMap C Kb)).rootMultiplicity 0 + μ0) :
    (P.natDegree : ℤ) = n * Q.natDegree + μ0 := by
  classical
  set A := (P.map (algebraMap C Kb)).roots with hA
  set B := (Q.map (algebraMap C Kb)).roots with hB
  have hP' : P.map (algebraMap C Kb) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap C Kb).injective).mpr hP
  have hQ' : Q.map (algebraMap C Kb) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap C Kb).injective).mpr hQ
  have hfilt : A.filter (· ≠ 0) = n • B.filter (· ≠ 0) := by
    ext b
    rw [Multiset.count_nsmul, Multiset.count_filter, Multiset.count_filter]
    by_cases hb0 : b ≠ 0
    · rw [if_pos hb0, if_pos hb0, hA, hB, count_roots, count_roots]
      exact hb b hb0
    · rw [if_neg hb0, if_neg hb0, mul_zero]
  have hsplitA : (A.card : ℤ) = (A.filter (· ≠ 0)).card + A.count 0 := by
    have := Multiset.filter_add_not (· ≠ 0) A
    have hc := congrArg Multiset.card this
    rw [Multiset.card_add] at hc
    have hz : (A.filter fun b ↦ ¬b ≠ 0) = Multiset.replicate (A.count 0) 0 := by
      rw [Multiset.eq_replicate]
      refine ⟨?_, fun b hb ↦ ?_⟩
      · rw [Multiset.count_eq_card_filter_eq]
        congr 1
        exact Multiset.filter_congr fun b _ ↦ by simp [eq_comm]
      · simpa using (Multiset.mem_filter.mp hb).2
    rw [hz, Multiset.card_replicate] at hc
    exact_mod_cast hc.symm
  have hsplitB : (B.card : ℤ) = (B.filter (· ≠ 0)).card + B.count 0 := by
    have := Multiset.filter_add_not (· ≠ 0) B
    have hc := congrArg Multiset.card this
    rw [Multiset.card_add] at hc
    have hz : (B.filter fun b ↦ ¬b ≠ 0) = Multiset.replicate (B.count 0) 0 := by
      rw [Multiset.eq_replicate]
      refine ⟨?_, fun b hb ↦ ?_⟩
      · rw [Multiset.count_eq_card_filter_eq]
        congr 1
        exact Multiset.filter_congr fun b _ ↦ by simp [eq_comm]
      · simpa using (Multiset.mem_filter.mp hb).2
    rw [hz, Multiset.card_replicate] at hc
    exact_mod_cast hc.symm
  have hcA : A.count 0 = (P.map (algebraMap C Kb)).rootMultiplicity 0 := count_roots _
  have hcB : B.count 0 = (Q.map (algebraMap C Kb)).rootMultiplicity 0 := count_roots _
  rw [← natDegree_map_eq_of_injective (algebraMap C Kb).injective,
    ← natDegree_map_eq_of_injective (algebraMap C Kb).injective Q,
    ← IsAlgClosed.card_roots_eq_natDegree, ← IsAlgClosed.card_roots_eq_natDegree, ← hA, ← hB,
    hsplitA, hsplitB, hfilt, Multiset.card_nsmul, hcA, hcB]
  push_cast
  linarith

/-- **Units off `x = 0` have weighted order sums `0`**: `N₀ ∑_∞ ord + N ∑_0 ord = 0`. -/
theorem unit_sum_inf0 (z : C⟮S.x⟯⟮S.y⟯) (hz : z ≠ 0)
    (hfin : ∀ (a : Kb), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) z).order = 0)
    (N : ℕ) (hN : 0 < N) (l : List (LaurentSeries Kb))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (N0 : ℕ) (hN0 : 0 < N0) (l0 : List (LaurentSeries Kb))
    (hl0 : S.F.map (branchSub N0 0) = (l0.map fun r ↦ X - Polynomial.C r).prod) :
    (N0 : ℤ) * (l.attach.map fun r ↦ (S.embG (infSub N) (infSub_injective N hN) r.1
      (S.root_of_mem hl r.2) z).order).sum +
    N * (l0.attach.map fun r ↦ (S.embG (branchSub N0 0) (branchSub_injective N0 hN0 0) r.1
      (S.root_of_mem hl0 r.2) z).order).sum = 0 := by
  classical
  have hF1 : S.F ≠ 1 := fun h ↦ S.natDegree_F_ne_zero (by rw [h, natDegree_one])
  obtain ⟨W, Q, hQ, hWQ, hWn⟩ := S.exists_repr_lt z hF1
  have hWm : W.natDegree ≤ S.F.natDegree := hWn.le
  have hW : S.evXY W ≠ 0 := by
    rw [← hWQ]; exact mul_ne_zero (fun h ↦ hz (Subtype.ext h)) (fun h ↦ S.htr ⟨Q, hQ, h⟩)
  have hmu : ∀ b : Kb, b ≠ 0 → S.muW W S.F.natDegree Q b = 0 := by
    intro b hb
    obtain ⟨Nb, hNb, lb, hlb⟩ := S.hasBranches_list S.hasBranches b
    have hs := S.fibre_sum z hz W Q hQ hWQ S.F.natDegree hWm Nb hNb b lb hlb
    rw [List.sum_eq_zero fun x hx ↦ ?_] at hs
    · have : (Nb : ℤ) ≠ 0 := by exact_mod_cast hNb.ne'
      exact (mul_eq_zero.mp hs.symm).resolve_left this
    · obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
      exact hfin b hb Nb hNb.ne' lb hlb r.1 r.2
  have hs0 := S.fibre_sum z hz W Q hQ hWQ S.F.natDegree hWm N0 hN0 0 l0 hl0
  have hnorm0 := S.normW_ne_zero W S.F.natDegree hWm hW _ (infSub_injective N hN) l hl
  have hdeg : ((S.normW W S.F.natDegree).natDegree : ℤ) =
      S.F.natDegree * Q.natDegree + S.muW W S.F.natDegree Q (0 : Kb) :=
    natDegree_of_mult (Kb := Kb) _ Q hnorm0 hQ S.F.natDegree _
      (fun b hb ↦ by
        have := hmu b hb
        simp only [CurveData.muW] at this
        omega)
      (by simp only [CurveData.muW]; ring)
  have hsum := S.sum_order_inf W S.F.natDegree hWm hW N hN l hl
  have hQb : infSub (K := Kb) N Q ≠ 0 := (map_ne_zero_iff _ (infSub_injective N hN)).mpr hQ
  have hrel : ∀ (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (infSub N) (infSub_injective N hN) r (S.root_of_mem hl hr) z).order =
        ((W.map (infSub N)).eval r).order + N * Q.natDegree := by
    intro r hr
    have e := congrArg (S.embG (infSub N) (infSub_injective N hN) r (S.root_of_mem hl hr))
      (show z * ⟨aeval S.x Q, S.aeval_mem Q⟩ = ⟨S.evXY W, S.evXY_mem W⟩ from Subtype.ext hWQ)
    rw [map_mul, S.embG_polyX, S.embG_wE_eq (RingHom.id C) W] at e
    have hz0 : S.embG (infSub N) (infSub_injective N hN) r (S.root_of_mem hl hr) z ≠ 0 :=
      (map_ne_zero_iff _ (RingHom.injective _)).mpr hz
    have := congrArg HahnSeries.order e
    rw [HahnSeries.order_mul hz0 hQb, order_infSub N hN _ hQ] at this
    push_cast at this
    linarith
  rw [hs0, List.map_congr_left fun r _ ↦ hrel r.1 r.2]
  rw [List.attach_map_val (f := fun r ↦ ((W.map (infSub N)).eval r).order + N * Q.natDegree),
    List.sum_map_add, hsum, List.map_const', List.sum_replicate, S.length_of_split hl]
  push_cast
  rw [hdeg]
  ring

/-- `x` as an element of the function field. -/
noncomputable def xE : C⟮S.x⟯⟮S.y⟯ := ⟨aeval S.x (X : C[X]), S.aeval_mem X⟩

lemma coe_xE : (S.xE : L) = S.x := by simp [xE]

lemma xE_ne_zero : S.xE ≠ 0 := fun h ↦ S.htr ⟨X, X_ne_zero, by
  have := congrArg Subtype.val h
  simpa [xE] using this⟩

lemma order_xE_branch (a : Kb) (ha : a ≠ 0) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
    (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (r : LaurentSeries Kb) (hr : r ∈ l) :
    (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
      (S.root_of_mem hl hr) S.xE).order = 0 := by
  rw [xE, S.embG_polyX]
  exact order_branchSub_eq_zero (C := C) X a N (Nat.pos_of_ne_zero hN) (by simpa using ha)

set_option maxHeartbeats 8000000 in
/-- **S-units are power products of `x` and `m` given independent S-units** (`S` = the places at
infinity and above `0`; `m + 2` = number of roots above infinity + number of roots above `0`):
every S-unit `w` satisfies `w^N' = c x^κ ∏ uᵢ^{aᵢ}`, `N' ≠ 0`. -/
theorem mem_pow_units_inf0 [CharZero C]
    (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C Kb))))
    (N : ℕ) (hN : 0 < N) (l : List (LaurentSeries Kb))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (N0 : ℕ) (hN0 : 0 < N0) (l0 : List (LaurentSeries Kb))
    (hl0 : S.F.map (branchSub N0 0) = (l0.map fun r ↦ X - Polynomial.C r).prod)
    {m : ℕ} (hlen : l.length + l0.length = m + 2)
    (u : Fin m → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i, u i ≠ 0)
    (hfinu : ∀ i (a : Kb), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (u i)).order = 0)
    (hind : ∀ (e0 : ℤ) (a : Fin m → ℤ),
      (∃ c : C, S.x ^ e0 * ∏ i, (u i : L) ^ a i = algebraMap C L c) → e0 = 0 ∧ a = 0)
    (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0)
    (hfin : ∀ (a : Kb), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) w).order = 0) :
    ∃ (N' κ : ℤ) (a : Fin m → ℤ), N' ≠ 0 ∧ ∃ c : C,
      (w : L) ^ N' = algebraMap C L c * S.x ^ κ * ∏ i, (u i : L) ^ a i := by
  classical
  set n := l.length with hn
  have hn0 : 0 < n := by
    rw [hn, S.length_of_split hl]; exact Nat.pos_of_ne_zero S.natDegree_F_ne_zero
  -- the family `x, u₀, …`
  set v : Fin (m + 1) → C⟮S.x⟯⟮S.y⟯ := Fin.cons S.xE u with hv
  have hv0 : ∀ i, v i ≠ 0 := fun i ↦ Fin.cases S.xE_ne_zero (fun i ↦ hu i) i
  have hfinv : ∀ i (a : Kb), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (v i)).order = 0 := by
    intro i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · intro a ha N hN l hl r hr
      simp only [hv, Fin.cons_zero]
      exact S.order_xE_branch a ha N hN l hl r hr
    · intro a ha N hN l hl r hr
      simp only [hv, Fin.cons_succ]
      exact hfinu i a ha N hN l hl r hr
  -- the rows: the first `n − 1` roots above infinity and all roots above `0`
  have hlt : ∀ p : Fin (m + 1), ¬ (p : ℕ) < n - 1 → (p : ℕ) - (n - 1) < l0.length := by
    intro p hp; omega
  set φ : Fin (m + 1) → (C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries Kb) := fun p ↦
    if h : (p : ℕ) < n - 1 then
      S.embG (infSub N) (infSub_injective N hN) (l.get ⟨p, by omega⟩)
        (S.root_of_mem hl (List.get_mem _ _))
    else
      S.embG (branchSub N0 0) (branchSub_injective N0 hN0 0) (l0.get ⟨p - (n - 1), hlt p h⟩)
        (S.root_of_mem hl0 (List.get_mem _ _)) with hφ
  -- orders of power products
  have hordp : ∀ (g : C[X] →+* LaurentSeries Kb) (hg : Function.Injective g) (Y : LaurentSeries Kb)
      (hY : (S.F.map g).eval Y = 0) (e0 : ℤ) (e : Fin (m + 1) → ℤ),
      (S.embG g hg Y hY (w ^ e0 * ∏ i, v i ^ e i)).order =
        e0 * (S.embG g hg Y hY w).order + ∑ i, e i * (S.embG g hg Y hY (v i)).order := by
    intro g hg Y hY e0 e
    have hw' : S.embG g hg Y hY w ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hw
    obtain ⟨hp0, hpo⟩ := order_prod_zpow_nk Finset.univ (fun i ↦ S.embG g hg Y hY (v i))
      (fun i _ ↦ (map_ne_zero_iff _ (RingHom.injective _)).mpr (hv0 i)) e
    rw [map_mul, map_zpow₀, map_prod]
    simp only [map_zpow₀]
    rw [HahnSeries.order_mul (zpow_ne_zero _ hw') hp0, order_zpow_ls _ hw', hpo]
  have hprod_ne : ∀ (e0 : ℤ) (e : Fin (m + 1) → ℤ), w ^ e0 * ∏ i, v i ^ e i ≠ 0 := fun e0 e ↦
    mul_ne_zero (zpow_ne_zero _ hw) (Finset.prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ (hv0 i))
  have hkey : ∀ (e0 : ℤ) (e : Fin (m + 1) → ℤ),
      (∀ p, e0 * (φ p w).order + ∑ i, e i * (φ p (v i)).order = 0) →
      ∃ c : C, ((w ^ e0 * ∏ i, v i ^ e i : C⟮S.x⟯⟮S.y⟯) : L) = algebraMap C L c := by
    intro e0 e hzero
    set y := w ^ e0 * ∏ i, v i ^ e i with hy
    have hy1 : ∀ (a : Kb), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
        (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries Kb) (hr : r ∈ l), (S.embG (branchSub N a)
          (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r (S.root_of_mem hl hr) y).order = 0 :=
      fun a ha N hN l hl r hr ↦ by
        rw [hy, hordp, hfin a ha N hN l hl r hr, Finset.sum_eq_zero fun i _ ↦ by
          rw [hfinv i a ha N hN l hl r hr, mul_zero]]; ring
    have hrow : ∀ p, (φ p y).order = 0 := fun p ↦ by
      have := hzero p
      by_cases h : (p : ℕ) < n - 1
      · have e1 : φ p = S.embG (infSub N) (infSub_injective N hN) (l.get ⟨p, by omega⟩)
            (S.root_of_mem hl (List.get_mem _ _)) := by rw [hφ]; simp only [dif_pos h]
        rw [e1] at this ⊢; rw [hy, hordp]; exact this
      · have e1 : φ p = S.embG (branchSub N0 0) (branchSub_injective N0 hN0 0)
            (l0.get ⟨p - (n - 1), hlt p h⟩) (S.root_of_mem hl0 (List.get_mem _ _)) := by
          rw [hφ]; simp only [dif_neg h]
        rw [e1] at this ⊢; rw [hy, hordp]; exact this
    -- all orders above `0` vanish
    have hzero0 : ∀ i : Fin l0.length, (S.embG (branchSub N0 0) (branchSub_injective N0 hN0 0)
        (l0.get i) (S.root_of_mem hl0 (List.get_mem _ _)) y).order = 0 := by
      intro i
      have hp : (n - 1) + (i : ℕ) < m + 1 := by omega
      have := hrow ⟨(n - 1) + i, hp⟩
      rw [hφ] at this
      simp only [show ¬ ((n - 1) + (i : ℕ) < n - 1) by omega, dite_false] at this
      convert this using 4 <;> simp
    -- the first `n − 1` orders above infinity vanish, hence all of them
    have hsum := S.unit_sum_inf0 y (hprod_ne e0 e) hy1 N hN l hl N0 hN0 l0 hl0
    rw [sum_attach_eq_fin l (fun r hr ↦ (S.embG (infSub N) (infSub_injective N hN) r
      (S.root_of_mem hl hr) y).order),
      sum_attach_eq_fin l0 (fun r hr ↦ (S.embG (branchSub N0 0) (branchSub_injective N0 hN0 0) r
      (S.root_of_mem hl0 hr) y).order), Finset.sum_eq_zero fun i _ ↦ hzero0 i, mul_zero,
      add_zero] at hsum
    have hinf : ∀ i : Fin l.length, (S.embG (infSub N) (infSub_injective N hN) (l.get i)
        (S.root_of_mem hl (List.get_mem _ _)) y).order = 0 := by
      have hlow : ∀ i : Fin l.length, (i : ℕ) < n - 1 → (S.embG (infSub N) (infSub_injective N hN)
          (l.get i) (S.root_of_mem hl (List.get_mem _ _)) y).order = 0 := by
        intro i hi
        have hp : (i : ℕ) < m + 1 := by omega
        have := hrow ⟨i, hp⟩
        rw [hφ] at this
        simp only [show ((i : ℕ) < n - 1) from hi, dite_true] at this
        exact this
      have hN0z : (N0 : ℤ) ≠ 0 := by exact_mod_cast hN0.ne'
      have hs : ∑ i : Fin l.length, (S.embG (infSub N) (infSub_injective N hN) (l.get i)
          (S.root_of_mem hl (List.get_mem _ _)) y).order = 0 :=
        (mul_eq_zero.mp hsum).resolve_left hN0z
      have hlast : ∀ i : Fin l.length, (i : ℕ) = n - 1 → (S.embG (infSub N)
          (infSub_injective N hN) (l.get i) (S.root_of_mem hl (List.get_mem _ _)) y).order = 0 := by
        intro i hi
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Finset.sum_eq_zero fun j hj ↦ hlow j
          (by
            have hji := Finset.ne_of_mem_erase hj
            have : (j : ℕ) ≠ i := fun h ↦ hji (Fin.ext h)
            omega), add_zero] at hs
        exact hs
      intro i
      by_cases hi : (i : ℕ) < n - 1
      · exact hlow i hi
      · exact hlast i (by omega)
    -- regular at the finite places
    have hreg : S.RegularFinite Kb y := by
      intro a N' hN' l' hl' r hr
      by_cases ha : a = 0
      · subst ha
        obtain ⟨r0, hr0, htr⟩ := S.order_transfer 0 N0 N' hN0 (Nat.pos_of_ne_zero hN') l0 l' hl0
          hl' r hr
        obtain ⟨i, rfl⟩ := List.get_of_mem hr0
        have h1 := htr y
        rw [hzero0 i, mul_zero] at h1
        have hN0z : (0 : ℤ) < N0 := by exact_mod_cast hN0
        nlinarith
      · exact (hy1 a ha N' hN' l' hl' r hr).ge
    obtain ⟨M0, hM0, hyM⟩ := S.algebraic_of_regular_l y hreg N hN l hl fun r hr ↦ by
      obtain ⟨i, rfl⟩ := List.get_of_mem hr
      exact (hinf i).ge
    exact S.mem_const_of_alg_geo hgeo y M0 hM0 hyM
  have hindv : ∀ a : Fin (m + 1) → ℤ, (∃ c : C, ∏ i, (v i : L) ^ a i = algebraMap C L c) →
      a = 0 := by
    intro a ⟨c, hc⟩
    rw [Fin.prod_univ_succ] at hc
    simp only [hv, Fin.cons_zero, Fin.cons_succ, coe_xE] at hc
    obtain ⟨h0, h1⟩ := hind (a 0) (fun i ↦ a i.succ) ⟨c, hc⟩
    funext i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · exact h0
    · exact congrFun h1 i
  obtain ⟨N', a, hN', c, hc⟩ := S.pow_units_cramer (Kb := Kb) v hv0 w φ hkey hindv
  refine ⟨N', a 0, fun i ↦ a i.succ, hN', c, ?_⟩
  rw [hc, Fin.prod_univ_succ]
  simp only [hv, Fin.cons_zero, Fin.cons_succ, coe_xE]
  ring

/-- **Every S-unit is a power product of `x` and the `u i`** (`S` = the places at infinity and above
`0`): a function without zeros or poles at the finite places `a ≠ 0` is, up to a non-zero power, a
constant times a power product of `x` and the `u i`. -/
def UnitsSpan0 (Kb : Type*) [Field Kb] [Algebra C Kb] {m : ℕ} (u : Fin m → C⟮S.x⟯⟮S.y⟯) : Prop :=
  ∀ w : C⟮S.x⟯⟮S.y⟯, w ≠ 0 →
    (∀ (a : Kb), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) w).order = 0) →
    ∃ (N' κ : ℤ) (a : Fin m → ℤ), N' ≠ 0 ∧ ∃ c : C,
      (w : L) ^ N' = algebraMap C L c * S.x ^ κ * ∏ i, (u i : L) ^ a i

/-- `x` and `m` independent S-units span the S-units when `m + 2` is the number of roots above
infinity and above `0` (`mem_pow_units_inf0`). -/
lemma unitsSpan0_inf [CharZero C] (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C Kb))))
    (N : ℕ) (hN : 0 < N) (l : List (LaurentSeries Kb))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (N0 : ℕ) (hN0 : 0 < N0) (l0 : List (LaurentSeries Kb))
    (hl0 : S.F.map (branchSub N0 0) = (l0.map fun r ↦ X - Polynomial.C r).prod)
    {m : ℕ} (hlen : l.length + l0.length = m + 2)
    (u : Fin m → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i, u i ≠ 0)
    (hfinu : ∀ i (a : Kb), a ≠ 0 → ∀ (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries Kb))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries Kb) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) (u i)).order = 0)
    (hind : ∀ (e0 : ℤ) (a : Fin m → ℤ),
      (∃ c : C, S.x ^ e0 * ∏ i, (u i : L) ^ a i = algebraMap C L c) → e0 = 0 ∧ a = 0) :
    S.UnitsSpan0 Kb u := fun w hw hfin ↦
  S.mem_pow_units_inf0 hgeo N hN l hl N0 hN0 l0 hl0 hlen u hu hfinu hind w hw hfin

end CurveData

end UnitsInf0

end Curves
