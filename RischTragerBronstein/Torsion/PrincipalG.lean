import RischTragerBronstein.Torsion.ExactFn
import RischTragerBronstein.Torsion.LSpace

/-!
# Principal divisors from functions vanishing on complementary divisors

Divisors `Γ − c ∞ₓ` with `Γ ≥ 0` supported above the points `α_j ∈ C` are given along complete
branch systems `lf j` (at `x = α_j + T^{N_j}`) by multiplicities `Γ j r`.

* `order_transfer`: branch systems above the same point are related by `T ↦ Tᴺ` (char-free);
* `DivGE`: `div γ ≥ Γ − c ∞ₓ`;
* `principal_of_vanishG`: if `ψ = ∑ cⱼ wⱼ` (pole order `≤ M` above infinity) vanishes on
  `∑ c'_j F_{α_j} − Γ` and on the full fibres above the `xᵢ`, with `M + c = ∑ c'_j + g`, then
  `γ = ∏(x − α_j)^{c'_j} ∏(x − xᵢ) / ψ` has `div γ ≥ Γ − c ∞ₓ`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section Mult

variable {K : Type*} [Field K]

open Classical in
lemma rootMultiplicity_prodPow {I : Type*} [Fintype I] (pt : I → K) (e : I → ℕ) (b : K) :
    (∏ i, (X - Polynomial.C (pt i)) ^ e i).rootMultiplicity b = ∑ i, if pt i = b then e i else 0 := by
  classical
  suffices h : ∀ s : Finset I, (∏ i ∈ s, (X - Polynomial.C (pt i)) ^ e i).rootMultiplicity b =
      ∑ i ∈ s, if pt i = b then e i else 0 from h _
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, rootMultiplicity_mul, ih]
    · congr 1
      split_ifs with h
      · rw [h, rootMultiplicity_X_sub_C_pow]
      · rw [rootMultiplicity_eq_zero]
        simp only [IsRoot.def, eval_pow, eval_sub, eval_X, eval_C]
        exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm h))
    · exact mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _))
        (Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _))

lemma rootMultiplicity_prodPow_pt {I : Type*} [Fintype I] (pt : I → K)
    (hpt : Function.Injective pt) (e : I → ℕ) (i : I) :
    (∏ i, (X - Polynomial.C (pt i)) ^ e i).rootMultiplicity (pt i) = e i := by
  classical
  rw [rootMultiplicity_prodPow, Finset.sum_eq_single i (fun j _ hj ↦ if_neg fun h ↦ hj (hpt h))
    (fun h ↦ absurd (Finset.mem_univ i) h), if_pos rfl]

lemma rootMultiplicity_prodPow_off {I : Type*} [Fintype I] (pt : I → K) (e : I → ℕ) (b : K)
    (hb : b ∉ Set.range pt) : (∏ i, (X - Polynomial.C (pt i)) ^ e i).rootMultiplicity b = 0 := by
  rw [rootMultiplicity_prodPow]
  exact Finset.sum_eq_zero fun i _ ↦ if_neg fun h ↦ hb ⟨i, h⟩

lemma natDegree_prodPow {I : Type*} [Fintype I] (pt : I → K) (e : I → ℕ) :
    (∏ i, (X - Polynomial.C (pt i)) ^ e i).natDegree = ∑ i, e i := by
  rw [natDegree_prod _ _ fun i _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)]
  simp [natDegree_pow]

end Mult

section Lsub

variable {K : Type*} [Field K]

lemma order_lsub' (M : ℕ) (hM : 0 < M) (z : LaurentSeries K) :
    (lsub M hM z).order = M * z.order := by
  by_cases hz : z = 0
  · rw [hz, map_zero, HahnSeries.order_zero, mul_zero]
  have hz' : lsub M hM z ≠ 0 := fun h ↦ hz (lsub_injective M hM (h.trans (map_zero _).symm))
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_) ?_
  · rw [lsub_coeff_mul]; exact HahnSeries.coeff_order_eq_zero.not.mpr hz
  · by_contra hlt
    push Not at hlt
    have hc := HahnSeries.coeff_order_eq_zero.not.mpr hz'
    by_cases hd : (M : ℤ) ∣ (lsub M hM z).order
    · obtain ⟨k, hk⟩ := hd
      rw [hk, lsub_coeff_mul] at hc
      have : k < z.order := by
        have h0 : (0 : ℤ) < M := by exact_mod_cast hM
        nlinarith
      exact hc (HahnSeries.coeff_eq_zero_of_lt_order this)
    · exact hc (lsub_coeff_not_dvd M hM z _ hd)

lemma order_inv' (z : LaurentSeries K) (hz : z ≠ 0) : z⁻¹.order = -z.order := by
  have h := congrArg HahnSeries.order (mul_inv_cancel₀ hz)
  rw [HahnSeries.order_mul hz (inv_ne_zero hz), HahnSeries.order_one] at h
  linarith

lemma le_order_of_lowerBd (z : LaurentSeries K) (hz : z ≠ 0) (m : ℤ) (h : LowerBd z m) :
    m ≤ z.order := by
  by_contra hlt
  push Not at hlt
  exact HahnSeries.coeff_order_eq_zero.not.mpr hz (h _ hlt)

lemma list_sum_const_sub {α : Type*} (l : List α) (A : ℤ) (f : α → ℕ) :
    (l.map fun r ↦ A - (f r : ℤ)).sum = l.length * A - ((l.map f).sum : ℕ) := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring

end Lsub

section Principal

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **Transfer between branch systems above the same point** (char-free). -/
lemma order_transfer (b : K) (N N' : ℕ) (hN : 0 < N) (hN' : 0 < N')
    (l l' : List (LaurentSeries K))
    (hl : S.F.map (branchSub N b) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (hl' : S.F.map (branchSub N' b) = (l'.map fun r ↦ X - Polynomial.C r).prod)
    (r' : LaurentSeries K) (hr' : r' ∈ l') :
    ∃ r, ∃ hr : r ∈ l, ∀ u : C⟮S.x⟯⟮S.y⟯,
      (N : ℤ) * (S.embG (branchSub N' b) (branchSub_injective N' hN' b) r'
        (S.root_of_mem hl' hr') u).order =
      N' * (S.embG (branchSub N b) (branchSub_injective N hN b) r (S.root_of_mem hl hr) u).order := by
  have hc1 : (lsub N hN).comp (branchSub (C := C) N' b) = branchSub (N * N') b := by
    rw [lsub_comp_branchSub, mul_comm]
  have hc2 : (lsub N' hN').comp (branchSub (C := C) N b) = branchSub (N * N') b := by
    rw [lsub_comp_branchSub]
  -- `lsub N r'` is a root of the lifted first system
  have hroot : (S.F.map (branchSub (N * N') b)).eval (lsub N hN r') = 0 := by
    rw [← hc1, ← Polynomial.map_map, eval_map, eval₂_at_apply, S.root_of_mem hl' hr', map_zero]
  have hsplit : S.F.map (branchSub (N * N') b) =
      ((l.map (lsub N' hN')).map fun r ↦ X - Polynomial.C r).prod := by
    rw [← hc2, ← Polynomial.map_map, hl, Polynomial.map_list_prod, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun r _ ↦ ?_
    simp
  rw [hsplit, eval_list_prod, List.prod_eq_zero_iff, List.map_map] at hroot
  obtain ⟨s, hs, hs0⟩ := List.mem_map.mp hroot
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C, sub_eq_zero] at hs0
  refine ⟨r, hr, fun u ↦ ?_⟩
  have e1 := S.embG_lsub_fin N hN N' hN' b r' (S.root_of_mem hl' hr') (by
      rw [hs0, ← hc2, ← Polynomial.map_map, eval_map, eval₂_at_apply, S.root_of_mem hl hr, map_zero]) u
  have e2 := S.embG_lsub_fin N' hN' N hN b r (S.root_of_mem hl hr) (by
    rw [mul_comm N' N, ← hc2, ← Polynomial.map_map, eval_map, eval₂_at_apply,
      S.root_of_mem hl hr, map_zero]) u
  have e3 : S.embG (branchSub (N * N') b) (branchSub_injective (N * N') (Nat.mul_pos hN hN') b)
      (lsub N hN r') (by rw [hs0, ← hc2, ← Polynomial.map_map, eval_map, eval₂_at_apply,
        S.root_of_mem hl hr, map_zero]) u =
      S.embG (branchSub (N' * N) b) (branchSub_injective (N' * N) (Nat.mul_pos hN' hN) b)
        (lsub N' hN' r) (by rw [mul_comm N' N, ← hc2, ← Polynomial.map_map, eval_map,
          eval₂_at_apply, S.root_of_mem hl hr, map_zero]) u :=
    congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K ↦ φ u)
      (S.embG_congr' (by rw [mul_comm]) _ _ hs0 _ _)
  have := congrArg HahnSeries.order (e1.symm.trans (e3.trans e2))
  rwa [order_lsub', order_lsub'] at this

/-- `div γ ≥ Γ − c ∞ₓ`. -/
def DivGE {J : Type*} (α : J → C) (N : J → ℕ) (hN : ∀ j, 0 < N j)
    (lf : J → List (LaurentSeries K))
    (hlf : ∀ j, S.F.map (branchSub (N j) (algebraMap C K (α j))) =
      ((lf j).map fun r ↦ X - Polynomial.C r).prod)
    (Γ : J → LaurentSeries K → ℕ) (c : ℕ) (γ : C⟮S.x⟯⟮S.y⟯) : Prop :=
  (∀ j r (hr : r ∈ lf j), (Γ j r : ℤ) ≤ (S.embG (branchSub (N j) (algebraMap C K (α j)))
    (branchSub_injective _ (hN j) _) r (S.root_of_mem (hlf j) hr) γ).order) ∧
  (∀ b : K, b ∉ Set.range (fun j ↦ algebraMap C K (α j)) → ∀ (N' : ℕ) (hN' : N' ≠ 0)
    (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N' b) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (r : LaurentSeries K) (hr : r ∈ l), 0 ≤ (S.embG (branchSub N' b)
      (branchSub_injective N' (Nat.pos_of_ne_zero hN') b) r (S.root_of_mem hl hr) γ).order) ∧
  (∀ (N' : ℕ) (hN' : N' ≠ 0) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N') = (l.map fun r ↦ X - Polynomial.C r).prod)
    (r : LaurentSeries K) (hr : r ∈ l), -((N' * c : ℕ) : ℤ) ≤ (S.embG (infSub N')
      (infSub_injective N' (Nat.pos_of_ne_zero hN')) r (S.root_of_mem hl hr) γ).order)

variable [IsAlgClosed K]

/-- **Principality from a function vanishing on the complementary divisor.** -/
theorem principal_of_vanishG (hBr : S.HasBranches K) (hBI : S.HasBranchesInf K)
    {B : Fin S.F.natDegree → C[X][X]} {D : C[X]} {δ : Fin S.F.natDegree → ℕ}
    (hD : D ≠ 0) (deg : ∀ j, (B j).natDegree < S.F.natDegree)
    (det : (Matrix.of fun (i j : Fin S.F.natDegree) ↦ (B j).coeff i).det ≠ 0)
    (reg : ∀ j, S.RegularFinite K (S.fnWQ (B j) D))
    (inf : ∀ j (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod) (r : LaurentSeries K)
      (hr : r ∈ l), LowerBd (S.embG (infSub N) (infSub_injective N (Nat.pos_of_ne_zero hN)) r
        (S.root_of_mem hl hr) (S.fnWQ (B j) D)) (-((N * δ j : ℕ) : ℤ)))
    (c : Fin S.F.natDegree → C[X]) (hc0 : c ≠ 0) (M : ℕ)
    (hdeg : ∀ j, c j ≠ 0 → (c j).natDegree + δ j ≤ M)
    {J : Type*} [Fintype J] (α : J → C) (hα : Function.Injective α) (N : J → ℕ)
    (hN : ∀ j, 0 < N j) (lf : J → List (LaurentSeries K))
    (hlf : ∀ j, S.F.map (branchSub (N j) (algebraMap C K (α j))) =
      ((lf j).map fun r ↦ X - Polynomial.C r).prod)
    (Γ : J → LaurentSeries K → ℕ) (cΓ : ℕ) (c' : J → ℕ) (dΓ : J → ℕ)
    (hdΓ : ∀ j, ((lf j).map (Γ j)).sum = N j * dΓ j) (hsumΓ : ∑ j, dΓ j = cΓ * S.F.natDegree)
    {g : ℕ} (xs : Fin g → C) (hxs : Function.Injective xs) (hxα : ∀ i j, xs i ≠ α j)
    (ls : Fin g → List (LaurentSeries K))
    (hls : ∀ i, S.F.map (branchSub 1 (algebraMap C K (xs i))) =
      ((ls i).map fun r ↦ X - Polynomial.C r).prod)
    (hM : M + cΓ = ∑ j, c' j + g)
    (hvT : ∀ j r (hr : r ∈ lf j), ((c' j * N j : ℕ) : ℤ) - Γ j r ≤
      (S.embG (branchSub (N j) (algebraMap C K (α j))) (branchSub_injective _ (hN j) _) r
        (S.root_of_mem (hlf j) hr) (S.elt B D c)).order)
    (hvx : ∀ i r (hr : r ∈ ls i), 1 ≤
      (S.embG (branchSub 1 (algebraMap C K (xs i))) (branchSub_injective _ one_pos _) r
        (S.root_of_mem (hls i) hr) (S.elt B D c)).order) :
    ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧ S.DivGE α N hN lf hlf Γ cΓ γ := by
  classical
  set ι := algebraMap C K with hι
  obtain ⟨n, hn⟩ : ∃ n, n = S.F.natDegree := ⟨_, rfl⟩
  set ψ := S.elt B D c with hψ
  have hψ0 : ψ ≠ 0 := fun h ↦ hc0 (elt_eq_zero hD deg det c h)
  have hreg : S.RegularFinite K ψ := regular_elt reg c
  -- the index set: `Γ`-points and base points
  set pt : J ⊕ Fin g → K := Sum.elim (fun j ↦ ι (α j)) (fun i ↦ ι (xs i)) with hpt
  have hptI : Function.Injective pt := Function.Injective.sumElim
    (fun a b h ↦ hα (ι.injective h)) (fun a b h ↦ hxs (ι.injective h))
    (fun a b h ↦ hxα b a (ι.injective h).symm)
  set NI : J ⊕ Fin g → ℕ := Sum.elim N (fun _ ↦ 1) with hNI
  have hNI0 : ∀ k, 0 < NI k := fun k ↦ by cases k <;> simp [hNI, hN]
  set lI : J ⊕ Fin g → List (LaurentSeries K) := Sum.elim lf ls with hlI
  have hlI' : ∀ k, S.F.map (branchSub (NI k) (pt k)) = ((lI k).map fun r ↦ X - Polynomial.C r).prod :=
    fun k ↦ by cases k with
      | inl j => exact hlf j
      | inr i => exact hls i
  set zI : J ⊕ Fin g → LaurentSeries K → ℤ :=
    Sum.elim (fun j r ↦ ((c' j * N j : ℕ) : ℤ) - Γ j r) (fun _ _ ↦ 1) with hzI
  set dI : J ⊕ Fin g → ℤ := Sum.elim (fun j ↦ (n : ℤ) * c' j - dΓ j) (fun _ ↦ (n : ℤ)) with hdI
  have hlenT : ∀ j, (lf j).length = n := fun j ↦ (S.length_of_split (hlf j)).trans hn.symm
  have hlenx : ∀ i, (ls i).length = n := fun i ↦ (S.length_of_split (hls i)).trans hn.symm
  -- the exact divisor of `ψ`, for any branch system above infinity
  have key : ∀ (Ni : ℕ) (hNi : 0 < Ni) (li : List (LaurentSeries K))
      (hli : S.F.map (infSub Ni) = (li.map fun r ↦ X - Polynomial.C r).prod),
      (∀ k r (hr : r ∈ lI k), zI k r = (S.embG (branchSub (NI k) (pt k))
        (branchSub_injective _ (hNI0 k) _) r (S.root_of_mem (hlI' k) hr) ψ).order) ∧
      (∀ r (hr : r ∈ li), -((Ni * M : ℕ) : ℤ) = (S.embG (infSub Ni) (infSub_injective Ni hNi) r
        (S.root_of_mem hli hr) ψ).order) ∧
      (∀ b, b ∉ Set.range pt → ∀ (N' : ℕ) (hN' : N' ≠ 0) (l : List (LaurentSeries K))
        (hl : S.F.map (branchSub N' b) = (l.map fun r ↦ X - Polynomial.C r).prod)
        (r : LaurentSeries K) (hr : r ∈ l), (S.embG (branchSub N' b)
          (branchSub_injective N' (Nat.pos_of_ne_zero hN') b) r (S.root_of_mem hl hr) ψ).order = 0) := by
    intro Ni hNi li hli
    have hleni : li.length = n := (S.length_of_split hli).trans hn.symm
    refine S.exact_fn hBr ψ hψ0 pt hptI NI hNI0 lI hlI' zI (fun k r hr ↦ ?_)
      (fun b _ N' hN' l hl r hr ↦ hreg b N' hN' l hl r hr) Ni hNi li hli
      (fun _ ↦ -((Ni * M : ℕ) : ℤ)) (fun r hr ↦ ?_) dI (fun k ↦ ?_) (-((n : ℤ) * M)) ?_ ?_
    · cases k with
      | inl j => exact hvT j r hr
      | inr i => exact hvx i r hr
    · refine le_order_of_lowerBd _ ((map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hψ0) _ ?_
      exact inf_elt inf c M hdeg Ni hNi.ne' li hli r hr
    · cases k with
      | inl j =>
        simp only [hzI, hNI, hdI, Sum.elim_inl, hlI]
        rw [list_sum_const_sub, hdΓ j, hlenT j]
        push_cast; ring
      | inr i =>
        simp only [hzI, hNI, hdI, Sum.elim_inr, hlI]
        rw [List.map_const', List.sum_replicate, hlenx i]
        simp
    · rw [List.map_const', List.sum_replicate, hleni]
      push_cast; ring
    · rw [Fintype.sum_sum_type]
      simp only [hdI, Sum.elim_inl, Sum.elim_inr, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h1 : ((∑ j, dΓ j : ℕ) : ℤ) = cΓ * n := by rw [hsumΓ, ← hn]; push_cast; ring
      have h2 : ((M + cΓ : ℕ) : ℤ) = ((∑ j, c' j + g : ℕ) : ℤ) := by rw [hM]
      push_cast at h1 h2
      rw [h1]
      linear_combination (-(n : ℤ)) * h2
  obtain ⟨Ni0, hNi0, li0, -, hli0⟩ := hBI
  obtain ⟨hE1, -, hE3⟩ := key Ni0 (Nat.pos_of_ne_zero hNi0) li0 hli0
  -- `γ = ∏(x − α_j)^{c'_j} ∏(x − xᵢ) / ψ`
  set ptC : J ⊕ Fin g → C := Sum.elim α xs with hptC
  set e : J ⊕ Fin g → ℕ := Sum.elim c' (fun _ ↦ 1) with he
  set P : C[X] := ∏ k, (X - Polynomial.C (ptC k)) ^ e k with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
  have hPK : P.map ι = ∏ k, (X - Polynomial.C (pt k)) ^ e k := by
    rw [hP, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    cases k <;> rfl
  have hdegP : P.natDegree = ∑ j, c' j + g := by
    rw [hP, natDegree_prodPow, Fintype.sum_sum_type]
    simp [he]
  refine ⟨S.polyF P * ψ⁻¹, mul_ne_zero (S.polyF_ne_zero hP0) (inv_ne_zero hψ0), ?_, ?_, ?_⟩
  · -- at the points of `Γ`
    intro j r hr
    have hψr := hE1 (Sum.inl j) r hr
    simp only [hzI, Sum.elim_inl] at hψr
    have hne : S.embG (branchSub (N j) (ι (α j))) (branchSub_injective _ (hN j) _) r
        (S.root_of_mem (hlf j) hr) ψ ≠ 0 := (map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hψ0
    rw [map_mul, map_inv₀, S.embG_polyF, HahnSeries.order_mul
      ((map_ne_zero_iff _ (branchSub_injective _ (hN j) _)).mpr hP0) (inv_ne_zero hne),
      order_inv' _ hne, order_branchSub _ (hN j) _ _ hP0, hPK]
    have hm := rootMultiplicity_prodPow_pt pt hptI e (Sum.inl j)
    simp only [hpt, he, Sum.elim_inl] at hm
    rw [hm]
    have : (S.embG (branchSub (N j) (ι (α j))) (branchSub_injective _ (hN j) _) r
        (S.root_of_mem (hlf j) hr) ψ).order =
        (S.embG (branchSub (NI (Sum.inl j)) (pt (Sum.inl j))) (branchSub_injective _ (hNI0 _) _) r
        (S.root_of_mem (hlI' (Sum.inl j)) hr) ψ).order := rfl
    rw [this, ← hψr]
    push_cast; ring_nf; rfl
  · -- off the points of `Γ`
    intro b hb N' hN' l hl r hr
    have hN0 : 0 < N' := Nat.pos_of_ne_zero hN'
    have hne : S.embG (branchSub N' b) (branchSub_injective _ hN0 _) r (S.root_of_mem hl hr) ψ ≠ 0 :=
      (map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hψ0
    rw [map_mul, map_inv₀, S.embG_polyF, HahnSeries.order_mul
      ((map_ne_zero_iff _ (branchSub_injective _ hN0 _)).mpr hP0) (inv_ne_zero hne),
      order_inv' _ hne, order_branchSub _ hN0 _ _ hP0, hPK]
    by_cases hbx : ∃ i, ι (xs i) = b
    · obtain ⟨i, rfl⟩ := hbx
      have hm := rootMultiplicity_prodPow_pt pt hptI e (Sum.inr i)
      simp only [hpt, he, Sum.elim_inr] at hm
      rw [hm]
      obtain ⟨r0, hr0, htr⟩ := S.order_transfer (ι (xs i)) 1 N' one_pos hN0 (ls i) l (hls i) hl r hr
      have h1 := htr ψ
      have h2 := hE1 (Sum.inr i) r0 hr0
      simp only [hzI, Sum.elim_inr] at h2
      have : (S.embG (branchSub 1 (ι (xs i))) (branchSub_injective _ one_pos _) r0
          (S.root_of_mem (hls i) hr0) ψ).order =
          (S.embG (branchSub (NI (Sum.inr i)) (pt (Sum.inr i))) (branchSub_injective _ (hNI0 _) _) r0
          (S.root_of_mem (hlI' (Sum.inr i)) hr0) ψ).order := rfl
      rw [this, ← h2] at h1
      push_cast at h1 ⊢
      linarith
    · have hbpt : b ∉ Set.range pt := by
        rintro ⟨k, rfl⟩
        cases k with
        | inl j => exact hb ⟨j, rfl⟩
        | inr i => exact hbx ⟨i, rfl⟩
      rw [hE3 b hbpt N' hN' l hl r hr, rootMultiplicity_prodPow_off pt e b hbpt]
      simp
  · -- above infinity
    intro N' hN' l hl r hr
    have hN0 : 0 < N' := Nat.pos_of_ne_zero hN'
    obtain ⟨-, hI, -⟩ := key N' hN0 l hl
    have hne : S.embG (infSub N') (infSub_injective _ hN0) r (S.root_of_mem hl hr) ψ ≠ 0 :=
      (map_ne_zero_iff _ (S.embG _ _ _ _).injective).mpr hψ0
    rw [map_mul, map_inv₀, S.embG_polyF, HahnSeries.order_mul
      ((map_ne_zero_iff _ (infSub_injective _ hN0)).mpr hP0) (inv_ne_zero hne),
      order_inv' _ hne, order_infSub _ hN0 _ hP0, ← hI r hr, hdegP]
    have h2 : ((M + cΓ : ℕ) : ℤ) = ((∑ j, c' j + g : ℕ) : ℤ) := by rw [hM]
    push_cast at h2 ⊢
    nlinarith

end CurveData

end Principal

end Curves
