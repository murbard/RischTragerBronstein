import RischTragerBronstein.Mixed.NKInf2N
import RischTragerBronstein.Mixed.NKInfRLog

/-!
# Several places at infinity with units over a number field

Units `uᵢ = ∑ₖ αᵏ Aᵢₖ` (`i < r − 1`, a common `α` root of `μ`), certified as in `NKUnitN`, with
`uᵢ′/uᵢ = ∑ₖ αᵏ gᵢₖ`. `indepCN`: the coordinates `j ≥ 1` of the `uᵢ′/uᵢ` (elements of `ℚ(x, t, α)`,
coded over `ℚ(α)`) have a right inverse, so the `uᵢ` are multiplicatively independent modulo
`Fₘ` (`indepCN_sound`).
-/

open Polynomial IntermediateField NCodes

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The `ℚ(α)`-code of the coordinate `j` of `∑ₖ αᵏ gₖ`. -/
def coordN (m : ℕ) (gs : List (GPoly (LC (m + 1)))) (j : ℕ) : List (LC (m + 1)) :=
  gs.map fun g ↦ g.getD j (MOr Fc ks (m + 1)).zero

/-- **The independence certificate over `ℚ(α)`**: columns `J` (all `≥ 1`) and a right inverse
`H` (entries `ℚ(α)`-codes) of the matrix of coordinates `M_{ip} = coord_{Jₚ}(uᵢ′/uᵢ)`. -/
def indepCN (m : ℕ) (μ : List ℤ) (gss : List (List (GPoly (LC (m + 1))))) (J : List ℕ)
    (H : List (List (List (LC (m + 1))))) : Bool :=
  let S := scOps Fc ks m
  let O1 := MO Fc ks (m + 1)
  let k := gss.length
  (List.range k).all (fun p ↦ decide (1 ≤ J.getD p 0)) &&
  (List.range k).all fun i ↦ (List.range k).all fun l ↦
    let c := nRed S μ (((List.range k).map fun p ↦
      nConv S (coordN Fc ks m (gss.getD i []) (J.getD p 0)) ((H.getD p []).getD l [])).foldr
        (nAdd S) [])
    O1.isZero (O1.add (c.getD 0 O1.zero) (O1.neg (if i = l then O1.one else O1.zero))) &&
    (List.range μ.length).all fun s ↦ s == 0 || O1.isZero (c.getD s O1.zero)

/-- **The unit checks** for `r − 1` units over `ℚ(α)`. -/
def unitsRNC (m : ℕ) (Pp : List (GPoly (LC m))) (μ : List ℤ)
    (Ass Bss : List (List (List (GPoly (LC m))))) (gss : List (List (GPoly (LC (m + 1)))))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1))) : Bool :=
  decide (0 < μ.length) &&
  (List.range gss.length).all fun i ↦
    unitCN Fc ks m Pp μ (Ass.getD i []) (Bss.getD i []) &&
    logDerChkN Fc ks m Pp μ (Ass.getD i []) (gss.getD i []) dθ wθ &&
    decide ((gss.getD i []).length = μ.length) &&
    (List.range μ.length).all fun k ↦ decide (((gss.getD i []).getD k []).length ≤ Pp.length) &&
      (MOr Fc ks (m + 1)).isZero (nkTau Fc ks m Pp.length ((gss.getD i []).getD k []) s)

end Codes

lemma unitsRNC_spec {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {m : ℕ} {Pp : List (GPoly (LC m))}
    {μ : List ℤ} {Ass Bss : List (List (List (GPoly (LC m))))}
    {gss : List (List (GPoly (LC (m + 1))))} {dθ wθ : GPoly (LC (m + 1))} {s : List (LC (m + 1))}
    (h : unitsRNC Fc ks m Pp μ Ass Bss gss dθ wθ s = true) :
    0 < μ.length ∧ ∀ i < gss.length,
      unitCN Fc ks m Pp μ (Ass.getD i []) (Bss.getD i []) = true ∧
      logDerChkN Fc ks m Pp μ (Ass.getD i []) (gss.getD i []) dθ wθ = true ∧
      (gss.getD i []).length = μ.length ∧
      ∀ k < μ.length, ((gss.getD i []).getD k []).length ≤ Pp.length ∧
        (MOr Fc ks (m + 1)).isZero (nkTau Fc ks m Pp.length ((gss.getD i []).getD k []) s) = true := by
  unfold unitsRNC at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1, fun i hi ↦ ⟨(h.2 i hi).1.1.1, (h.2 i hi).1.1.2, (h.2 i hi).1.2, (h.2 i hi).2⟩⟩

/-- Indices in a flattened list of lists of equal length `d`. -/
lemma getD_flatten_mul {α : Type*} (d : ℕ) (x : α) :
    ∀ (l : List (List α)), (∀ i < l.length, (l.getD i []).length = d) →
      ∀ i < l.length, ∀ k < d, l.flatten.getD (i * d + k) x = (l.getD i []).getD k x
  | [], _, i, hi, _, _ => absurd hi (by simp)
  | a :: l, hl, i, hi, k, hk => by
    have ha : a.length = d := by simpa using hl 0 (by simp)
    rw [List.flatten_cons]
    rcases i with _ | i
    · simp only [zero_mul, zero_add, List.getD_cons_zero]
      rw [List.getD_append _ _ _ _ (by omega)]
    · rw [List.getD_append_right _ _ _ _ (by rw [ha]; nlinarith), List.getD_cons_succ,
        show (i + 1) * d + k - a.length = i * d + k by rw [ha]; ring_nf; omega]
      exact getD_flatten_mul d x l (fun j hj ↦ by simpa using hl (j + 1) (by simp; omega)) i
        (by simpa using hi) k hk

lemma length_flatten_mul {α : Type*} (d : ℕ) :
    ∀ (l : List (List α)), (∀ i < l.length, (l.getD i []).length = d) →
      l.flatten.length = l.length * d
  | [], _ => by simp
  | a :: l, hl => by
    have ha : a.length = d := by simpa using hl 0 (by simp)
    rw [List.flatten_cons, List.length_append, ha, length_flatten_mul d l (fun j hj ↦ by
      simpa using hl (j + 1) (by simp; omega)), List.length_cons]
    ring

/-- A sum over `range (r d)` as a double sum. -/
lemma sum_range_mul {M : Type*} [AddCommMonoid M] (d : ℕ) (f : ℕ → M) :
    ∀ r, ∑ q ∈ Finset.range (r * d), f q = ∑ i ∈ Finset.range r, ∑ k ∈ Finset.range d, f (i * d + k)
  | 0 => by simp
  | r + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_range_mul d f r, Finset.sum_range_succ]

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma nVal_foldr_nAdd {β : Type} {R : ROps β} {K : Type*} [CommRing K] {sem : β → K}
    (hS : RSem R sem) (α : K) (l : List (List β)) :
    nVal sem α (l.foldr (nAdd R) []) = (l.map (nVal sem α)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, nVal_nAdd hS, ih, List.map_cons, List.sum_cons]

/-- **Soundness of `indepCN`**: no product `∏ uᵢ^{aᵢ}` with `a ≠ 0` lies in `Fₘ`. -/
theorem indepCN_sound (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (n : ℕ)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range n, (a j : L) * θ ^ j = 0 →
      ∀ j < n, a j = 0)
    (μ : List ℤ) (hd : 0 < μ.length) (α : L) (hαF : α ∈ T.F m)
    (hμ : α ^ μ.length + ∑ i ∈ Finset.range μ.length, (μ.getD i 0 : L) * α ^ i = 0)
    (gss : List (List (GPoly (LC (m + 1)))))
    (hgl : ∀ i < gss.length, (gss.getD i []).length = μ.length)
    (hlen : ∀ i < gss.length, ∀ k < μ.length, ((gss.getD i []).getD k []).length ≤ n)
    (u : Fin gss.length → L) (hu : ∀ i, u i ≠ 0)
    (hlog : ∀ i : Fin gss.length, (u i)′ / u i = nVal (T.evθ m h1 θ) α (gss.getD i []))
    (J : List ℕ) (H : List (List (List (LC (m + 1))))) (hc : indepCN Fc ks m μ gss J H = true) :
    ∀ a : Fin gss.length → ℤ, (∃ c : T.F m, ∏ i, (u i) ^ (a i) = (c : L)) → a = 0 := by
  classical
  rintro a ⟨c, hc'⟩
  set M1 := T.MPr (m + 1) h1 with hM1
  set z := (MOr Fc ks (m + 1)).zero with hz
  have hαF1 : α ∈ T.F (m + 1) := T.le_succ m hαF
  set αF : T.F (m + 1) := ⟨α, hαF1⟩ with hαFd
  -- the coordinates of `uᵢ′/uᵢ`
  set MM : ℕ → ℕ → T.F (m + 1) := fun i j ↦
    ∑ k ∈ Finset.range μ.length, αF ^ k * M1.sem (((gss.getD i []).getD k []).getD j z) with hMM
  have hcoord : ∀ i : Fin gss.length, (u i)′ / u i = ∑ j ∈ Finset.range n, (MM i j : L) * θ ^ j := by
    intro i
    rw [hlog i, nVal_eq_sum (T.evθ_RSem m h1 θ) α _ μ.length (hgl i i.2).le]
    simp only [hMM, AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul,
      SubmonoidClass.coe_pow, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    change α ^ k * T.evθ m h1 θ ((gss.getD i []).getD k []) = _
    rw [T.evθ_list_le m h1 θ _ n (hlen i i.2 k (Finset.mem_range.mp hk)), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hαFd]; ring
  have hprod0 : ∏ i, u i ^ a i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ (hu i)
  have hld : (c : L)′ / c = ∑ i, (a i : L) * ((u i)′ / u i) := by
    rw [← hc', logDeriv_finset_prod _ _ (fun i _ ↦ zpow_ne_zero _ (hu i))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have := logDeriv_zpow' (u i) (hu i) (a i)
    simp only [logDeriv] at this
    exact this
  have hcd : ((c′ / c : T.F m) : L) ∈ T.F (m + 1) := T.le_succ m (c′ / c).2
  set cd : T.F (m + 1) := ⟨_, hcd⟩ with hcdd
  have hcdv : (cd : L) = (c : L)′ / c := by
    rw [hcdd]
    change (((c′ / c : T.F m)) : L) = _
    push_cast
    rfl
  set b : ℕ → T.F (m + 1) := fun j ↦
    ∑ i : Fin gss.length, (a i : T.F (m + 1)) * MM i j - if j = 0 then cd else 0 with hb
  have hred0 : ∀ c : List (LC (m + 1)), (∀ s < μ.length,
      (s == 0 || (MO Fc ks (m + 1)).isZero (c.getD s (MO Fc ks (m + 1)).zero)) = true) →
      ∑ s ∈ Finset.range μ.length, α ^ s *
        (((T.MP (m + 1) h1).sem (c.getD s (scOps Fc ks m).zero) : T.F (m + 1)) : L) =
      (((T.MP (m + 1) h1).sem (c.getD 0 (MO Fc ks (m + 1)).zero) : T.F (m + 1)) : L) := by
    intro c hc0
    rw [Finset.sum_eq_single 0 (fun s hs hs0 ↦ by
        have h := hc0 s (Finset.mem_range.mp hs)
        simp only [Bool.or_eq_true, beq_iff_eq] at h
        have hz := ((T.MP (m + 1) h1).isZero_iff _).mp (h.resolve_left hs0)
        change α ^ s * (((T.MP (m + 1) h1).sem (c.getD s (MO Fc ks (m + 1)).zero) :
          T.F (m + 1)) : L) = 0
        rw [hz]; simp) (fun h ↦ absurd (Finset.mem_range.mpr hd) h), pow_zero, one_mul]
    rfl
  have hn0 : 0 < n ∨ gss.length = 0 := by
    by_cases hk0 : gss.length = 0
    · exact Or.inr hk0
    left
    by_contra hn
    have hc2 := hc
    simp only [indepCN, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc2
    have h00 := (hc2.2 0 (by omega) 0 (by omega))
    have hz0 := ((T.MP (m + 1) h1).isZero_iff _).mp h00.1
    have hS := T.sc_RSem m h1
    -- the value of the reduced sum is `0`: every coordinate code is zero
    have hval := nVal_eq_sum hS α (nRed (scOps Fc ks m) μ (((List.range gss.length).map fun p ↦
      nConv (scOps Fc ks m) (coordN Fc ks m (gss.getD 0 []) (J.getD p 0))
        ((H.getD p []).getD 0 [])).foldr (nAdd (scOps Fc ks m)) [])) μ.length (length_nRed _ μ hd _)
    rw [nVal_nRed hS α μ hd hμ, nVal_foldr_nAdd hS, List.map_map] at hval
    have hzero : ∀ p, nVal (fun a ↦ (((T.MP (m + 1) h1).sem a : T.F (m + 1)) : L)) α
        (coordN Fc ks m (gss.getD 0 []) (J.getD p 0)) = 0 := by
      intro p
      rw [nVal_eq_sum hS α _ μ.length (by rw [coordN, List.length_map, hgl 0 (by omega)])]
      refine Finset.sum_eq_zero fun k hk ↦ ?_
      have hk' : k < (gss.getD 0 []).length := by rw [hgl 0 (by omega)]; exact Finset.mem_range.mp hk
      rw [coordN, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk'), List.getElem_map,
        List.getD_eq_default _ _ (by
          have := hlen 0 (by omega) k (by rw [← hgl 0 (by omega)]; exact hk')
          rw [List.getD_eq_getElem _ _ hk'] at this; omega)]
      have : (T.MP (m + 1) h1).sem (MOr Fc ks (m + 1)).zero = 0 := (T.MPr (m + 1) h1).sem_zero
      simp [this]
    simp only [Function.comp_def, nVal_nConv hS, hzero, zero_mul, List.map_const',
      List.sum_replicate, smul_zero] at hval
    rw [hred0 _ h00.2] at hval
    rw [(T.MP (m + 1) h1).sem_add, (T.MP (m + 1) h1).sem_neg, add_neg_eq_zero] at hz0
    simp only [↓reduceIte, (T.MP (m + 1) h1).sem_one] at hz0
    rw [hz0] at hval
    simp at hval
  rcases hn0 with hn0 | hk0
  swap
  · funext i; exact absurd i.2 (by omega)
  have hsum : ∑ j ∈ Finset.range n, (b j : L) * θ ^ j = 0 := by
    have hite : ∑ j ∈ Finset.range n, (((if j = 0 then cd else 0 : T.F (m + 1))) : L) * θ ^ j =
        cd := by
      rw [Finset.sum_eq_single 0 (fun j _ hj ↦ by rw [if_neg hj]; simp)
        (fun h ↦ absurd (Finset.mem_range.mpr hn0) h), if_pos rfl, pow_zero, mul_one]
    simp only [hb, AddSubgroupClass.coe_sub, sub_mul, Finset.sum_sub_distrib]
    rw [hite, hcdv, hld]
    simp only [hcoord, AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    push_cast
    ring
  have hb0 := hind b hsum
  have hcol : ∀ j, 1 ≤ j → ∑ i : Fin gss.length, (a i : T.F (m + 1)) * MM i j = 0 := by
    intro j hj
    by_cases hjn : j < n
    · have := hb0 j hjn
      simp only [hb, if_neg (show j ≠ 0 by omega), sub_zero] at this
      exact this
    · refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [show MM i j = 0 from Finset.sum_eq_zero fun k hk ↦ by
        rw [List.getD_eq_default _ _ (by
          have := hlen i i.2 k (Finset.mem_range.mp hk); omega), M1.sem_zero, mul_zero], mul_zero]
  -- the right inverse
  have hS := T.sc_RSem m h1
  simp only [indepCN, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨hJ, hH⟩ := hc
  set Hv : ℕ → ℕ → L := fun p l ↦
    nVal (fun a ↦ (((T.MP (m + 1) h1).sem a : T.F (m + 1)) : L)) α ((H.getD p []).getD l [])
    with hHv
  have hcN : ∀ i < gss.length, ∀ p, nVal (fun a ↦ (((T.MP (m + 1) h1).sem a : T.F (m + 1)) : L)) α
      (coordN Fc ks m (gss.getD i []) p) = (MM i p : L) := by
    intro i hi p
    rw [nVal_eq_sum hS α _ μ.length (by rw [coordN, List.length_map, hgl i hi])]
    simp only [hMM, AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul,
      SubmonoidClass.coe_pow]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' : k < (gss.getD i []).length := by rw [hgl i hi]; exact Finset.mem_range.mp hk
    rw [coordN, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk'), List.getElem_map,
      ← List.getD_eq_getElem _ [] hk', MPr_sem]
  have hinv : ∀ i < gss.length, ∀ l < gss.length, ∑ p ∈ Finset.range gss.length,
      (MM i (J.getD p 0) : L) * Hv p l = if i = l then 1 else 0 := by
    intro i hi l hl
    obtain ⟨h0, hs⟩ := hH i hi l hl
    have hval := nVal_eq_sum hS α (nRed (scOps Fc ks m) μ (((List.range gss.length).map fun p ↦
      nConv (scOps Fc ks m) (coordN Fc ks m (gss.getD i []) (J.getD p 0))
        ((H.getD p []).getD l [])).foldr (nAdd (scOps Fc ks m)) [])) μ.length (length_nRed _ μ hd _)
    rw [nVal_nRed hS α μ hd hμ, nVal_foldr_nAdd hS, List.map_map,
      ← List.sum_toFinset _ List.nodup_range, List.toFinset_range] at hval
    simp only [Function.comp_def, nVal_nConv hS, hcN i hi] at hval
    rw [hval, hred0 _ hs]
    have hz0 := ((T.MP (m + 1) h1).isZero_iff _).mp h0
    rw [(T.MP (m + 1) h1).sem_add, (T.MP (m + 1) h1).sem_neg, add_neg_eq_zero] at hz0
    rw [hz0]
    split_ifs
    · rw [(T.MP (m + 1) h1).sem_one]; rfl
    · rw [(T.MP (m + 1) h1).sem_zero]; rfl
  funext l
  have hl := l.2
  have e : ((a l : ℤ) : L) = 0 := by
    have h1' : ((a l : ℤ) : L) = ∑ i : Fin gss.length, (a i : L) *
        ∑ p ∈ Finset.range gss.length, (MM i (J.getD p 0) : L) * Hv p l := by
      rw [Finset.sum_eq_single l (fun i _ hi ↦ by
          rw [hinv i i.2 l hl, if_neg (fun h ↦ hi (Fin.ext h)), mul_zero])
        (fun h ↦ absurd (Finset.mem_univ l) h), hinv l hl l hl, if_pos rfl, mul_one]
    rw [h1']
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun p hp ↦ ?_
    have := congrArg (fun z : T.F (m + 1) ↦ (z : L)) (hcol (J.getD p 0) (hJ p (Finset.mem_range.mp hp)))
    simp only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul, ZeroMemClass.coe_zero]
      at this
    push_cast at this
    rw [show ∑ i : Fin gss.length, (a i : L) * ((MM i (J.getD p 0) : L) * Hv p l) =
        (∑ i : Fin gss.length, (a i : L) * (MM i (J.getD p 0) : L)) * Hv p l by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ ↦ by ring, this, zero_mul]
  exact_mod_cast e

set_option maxHeartbeats 4000000 in
/-- **`⇐`** (several places at infinity, units over `ℚ(α)`, any solver). -/
theorem nk_sufficientRN (m : ℕ) (h1 : T.Tr (m + 1)) (htr : Transcendental (T.F m) (T.ts m))
    (solve : SysSolver m) (wD bD : T.F m) (S : T.SolverSpec m h1.of_succ wD bD solve)
    (Pp : List (GPoly (LC m))) (hn0 : 0 < Pp.length) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range Pp.length, (a j : L) * θ ^ j = 0 →
      ∀ j < Pp.length, a j = 0)
    (μ : List ℤ) (Ass Bss : List (List (List (GPoly (LC m)))))
    (gss : List (List (GPoly (LC (m + 1))))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsRNC Fc ks m Pp μ Ass Bss gss dθ wθ s = true)
    (αs : Fin μ.length → Cc) (hαinj : Function.Injective αs)
    (hαμ : ∀ i, αs i ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : Cc) * αs i ^ l = 0)
    (fp : List (GPoly (LC m))) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTL Fc ks m solve (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))
        gss.flatten = some res)
    (hr : res = true)
    (hq : HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) := by
  classical
  obtain ⟨hd, hall⟩ := unitsRNC_spec hU
  have hgl : ∀ i < gss.length, (gss.getD i []).length = μ.length := fun i hi ↦ (hall i hi).2.2.1
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
  have hind' : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [hlen]; exact hind
  have hiff := T.exactTL_correct m h1 htr solve wD bD S (nkPC Fc ks m Pp) _ θ hP hind' Tc Ti
    gss.flatten res hres
  obtain ⟨c, Y, hY⟩ := hiff.mp hr
  set M1 := T.MPr (m + 1) h1 with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  have hS := T.evθ_RSem m h1 θ
  set αL : Fin μ.length → L := fun i ↦ algebraMap Cc L (αs i) with hαL
  have hμL : ∀ i, αL i ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : L) * αL i ^ l = 0 :=
    fun i ↦ by
      have := congrArg (algebraMap Cc L) (hαμ i)
      simpa [map_add, map_sum, map_mul, map_pow, map_intCast] using this
  have hαc : ∀ i, (αL i)′ = 0 := fun i ↦ by rw [hαL]; simp only; rw [deriv_algebraMap, T.hC, map_zero]
  -- the conjugate units `u_{p j}`
  set u : ℕ → Fin μ.length → L := fun p i ↦
    nVal (T.evθ m h1 θ) (αL i) ((Ass.getD p []).map (nkFl Fc ks m)) with hu
  have hu0 : ∀ p < gss.length, ∀ i, u p i ≠ 0 := fun p hp i ↦
    left_ne_zero_of_mul_eq_one (T.unitCN_sound m h1 θ Pp hP μ hd (αL i) (hμL i) _ _
      (hall p hp).1)
  set G : ℕ → ℕ → L := fun p k ↦ T.evθ m h1 θ ((gss.getD p []).getD k []) with hG
  have hGk : ∀ p < gss.length, ∀ k : Fin μ.length, G p k = ∑ i : Fin μ.length,
      algebraMap Cc L ((Matrix.vandermonde αs)⁻¹ k i) * logDeriv (u p i) := by
    intro p hp k
    refine gk_eq_sum αs hαinj (fun k : Fin μ.length ↦ G p k) (fun i ↦ logDeriv (u p i))
      (fun i ↦ ?_) k
    rw [logDeriv, T.logDerChkN_sound m h1 θ Pp hP μ hd (αL i) (hαc i) (hμL i) _ _ dθ wθ
        (hall p hp).2.1, mul_div_assoc, div_self (hu0 p hp i), mul_one,
      nVal_eq_sum hS (αL i) _ μ.length (hgl p hp).le,
      ← Fin.sum_univ_eq_sum_range (fun k ↦ αL i ^ k * T.evθ m h1 θ
        ((gss.getD p []).getD k (θOps Fc ks m).zero))]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_pow]; rfl
  -- the exact part
  have hflen := length_flatten_mul μ.length gss hgl
  have hg : ∑ j ∈ Finset.range Pp.length, (∑ q ∈ Finset.range gss.flatten.length,
      algebraMap Cc L (c q) * ((M1.sem ((gss.flatten.getD q []).getD j O1.zero) :
        T.F (m + 1)) : L)) * θ ^ j =
      ∑ p ∈ Finset.range gss.length, ∑ k : Fin μ.length,
        algebraMap Cc L (c (p * μ.length + k)) * G p k := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm, hflen, sum_range_mul]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hp' := Finset.mem_range.mp hp
    rw [getD_flatten_mul μ.length [] gss hgl p hp' k k.2, hG]
    simp only
    rw [T.evθ_list_le m h1 θ _ Pp.length ((hall p hp').2.2.2 k k.2).1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hlen] at hY
  simp only [sub_mul, Finset.sum_sub_distrib] at hY
  rw [hg, T.sum_nkRest m h1 Pp.length hn0] at hY
  set e : ℕ → Fin μ.length → Cc := fun p i ↦
    ∑ k : Fin μ.length, c (p * μ.length + k) * (Matrix.vandermonde αs)⁻¹ k i with he
  have hlog : ∑ p ∈ Finset.range gss.length, ∑ k : Fin μ.length,
      algebraMap Cc L (c (p * μ.length + k)) * G p k =
      ∑ p ∈ Finset.range gss.length, ∑ i : Fin μ.length, algebraMap Cc L (e p i) *
        logDeriv (u p i) := by
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    simp only [hGk p (Finset.mem_range.mp hp), Finset.mul_sum, he, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by rw [map_mul]; ring
  rw [hlog] at hY
  set pairs : List (ℕ × Fin μ.length) :=
    (List.range gss.length).flatMap fun p ↦ (List.finRange μ.length).map fun i ↦ (p, i) with hpairs
  have hpsum : ∀ F : ℕ → Fin μ.length → L, (pairs.map fun q ↦ F q.1 q.2).sum =
      ∑ p ∈ Finset.range gss.length, ∑ i : Fin μ.length, F p i := by
    intro F
    have hfm : ∀ l : List ℕ, ((l.flatMap fun p ↦ (List.finRange μ.length).map fun i ↦ (p, i)).map
        fun q ↦ F q.1 q.2).sum = (l.map fun p ↦ (((List.finRange μ.length).map fun i ↦ (p, i)).map
          fun q ↦ F q.1 q.2).sum).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
          List.sum_cons]
    rw [hpairs, hfm, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [List.map_map, Fin.sum_univ_def]
    rfl
  rw [show ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j =
      T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) +
        (∑ i ∈ Finset.range Pp.length, (Y i : L) * θ ^ i)′ +
          (pairs.map fun q ↦ algebraMap Cc L (e q.1 q.2) * logDeriv (u q.1 q.2)).sum by
    rw [hpsum (fun p i ↦ algebraMap Cc L (e p i) * logDeriv (u p i)), hY]; ring]
  refine (hq.add_in (hasElementaryIntegralIn_deriv _)).add_in ?_
  exact hasElementaryIntegralIn_logSum (fun q ↦ algebraMap Cc L (e q.1 q.2)) (fun q ↦ u q.1 q.2)
    pairs (fun q hq ↦ ⟨by rw [deriv_algebraMap, T.hC, map_zero], hu0 q.1 (by
      rw [hpairs, List.mem_flatMap] at hq
      obtain ⟨p, hp, hq'⟩ := hq
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq'
      exact List.mem_range.mp hp) q.2⟩)

set_option maxHeartbeats 16000000 in
/-- **`⇒`** (several places at infinity, units over `ℚ(α)`, logarithmic level). -/
theorem nk_necessaryRN (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ) (hPp : Pp = liftCurve Fc ks m Pp.length Fq)
    (hmonQ : (toB Fq).Monic) (hdegQ : (toB Fq).natDegree = Pp.length) (hn0 : 0 < Pp.length)
    (hgeo : GeomIrr.{u} Fq) (θ : L)
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ιC : F →+* Cc) (k0 M : ℕ)
    (hinv : InvOK k0 M 0 (shiftB Fq 0)) (hGm : (toB (invB (shiftB Fq 0) k0 M)).Monic)
    (hGn : (toB (invB (shiftB Fq 0) k0 M)).natDegree = Pp.length)
    (μ : List ℤ) (Ass Bss : List (List (List (GPoly (LC m)))))
    (gss : List (List (GPoly (LC (m + 1)))))
    (hpd : RPlaceDataP F (invB (shiftB Fq 0) k0 M) (gss.length + 1))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsRNC Fc ks m Pp μ Ass Bss gss dθ wθ s = true)
    (J : List ℕ) (H : List (List (List (LC (m + 1))))) (hJH : indepCN Fc ks m μ gss J H = true)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ}) (α : Cc)
    (hαμ : α ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : Cc) * α ^ l = 0)
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (fp : List (GPoly (LC m))) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTL Fc ks m (primSysC Fc ks m η (paramLimC Fc ks lv m)) (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))
        gss.flatten = some res)
    (hf : HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j)) :
    res = true ∧
      HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  classical
  set n := Pp.length with hnn
  set f := ∑ j ∈ Finset.range n, T.evP m (fp.getD j []) * θ ^ j with hfdef
  set q := nkTau Fc ks m n (nkFl Fc ks m fp) s with hq
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  obtain ⟨E₁, _, _, _, _, hE₁, g, hg⟩ := hf
  haveI : CharZero E₁ := charZero_of_injective_algebraMap (algebraMap L E₁).injective
  obtain ⟨ι, s', c, u, v, hdata, hv, heqL⟩ := liouville_strong hE₁ _ g hg
  -- the tower in `E₁`
  obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E₁
  set ψ := algebraMap L E₁ with hψ
  have MSE := TE.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTE : TE.Tr (m + 1) := MSE.hyp.tr
  have hTEm : TE.Tr m := hTE.of_succ
  have MSEm := TE.mspecs hmon hdeg lv m (by omega) hcm
  have hPE : ∀ P : GPoly (LC m), TE.evP m P = ψ (T.evP m P) := fun P ↦ by
    rw [← TE.sem_poly_code m hTE, ← T.sem_poly_code m hTr]
    exact (TE.sem_MP (m + 1) hTE _).trans ((hTEev (m + 1) _).trans
      (congrArg ψ (T.sem_MP (m + 1) hTr _).symm))
  have hθE : (ψ θ) ^ n + ∑ i ∈ Finset.range n, TE.evP m (Pp.getD i []) * (ψ θ) ^ i = 0 := by
    simp only [hPE, ← map_pow, ← map_mul, ← map_sum, ← map_add, hθ, map_zero]
  -- the curve over `C₁ = Fₘ` of the lifted tower
  set S₁ := TE.nkCurveG m hTE Pp Fq hPp hmonQ hdegQ hgeo (ψ θ) hθE with hS₁
  have hS₁F : S₁.F.natDegree = n := polyF_natDegree _ _
  set η₁ : TE.F m := TE.val m η with hη₁
  have hx : S₁.x′ = aeval S₁.x (Polynomial.C η₁) := by
    rw [aeval_C]
    change (TE.ts m)′ = _
    rw [TE.ht m (by omega), hk]
    rfl
  have hnd : ∀ α : AlgebraicClosure (TE.F m),
      α′ ≠ ((Polynomial.C η₁).map (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)))).eval α :=
    fun α ↦ by
      rw [Polynomial.map_C, eval_C]
      exact not_deriv_of_integral η₁ (fun z hz ↦ MSE.hyp.nd m (by omega) η hk z hz) α
        (Algebra.IsIntegral.isIntegral α)
  have hK : ∀ c : TE.F m, (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c)′ =
      algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c′ := fun c ↦ deriv_algebraMap c
  have hconstC : ∀ z : E₁, z′ = 0 → z ∈ Set.range (algebraMap (TE.F m) E₁) := fun z hz ↦ by
    obtain ⟨c0, hc0⟩ := TE.hconst z hz
    exact ⟨⟨z, hc0 ▸ TE.const_mem m c0⟩, rfl⟩
  set T₁ := (TE.F m)⟮S₁.x⟯⟮S₁.y⟯ with hT₁
  have hxT : ∀ w ∈ TE.F (m + 1), w ∈ T₁ := fun w hw ↦
    IntermediateField.algebraMap_mem T₁ (⟨w, (TE.mem_F_succ).mp hw⟩ : (TE.F m)⟮S₁.x⟯)
  have hLT : ∀ z : L, ψ z ∈ T₁ := by
    intro z
    have hz := hgen z
    induction hz using IntermediateField.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact mem_adjoin_simple_self _ _
    | algebraMap w => exact hxT _ (hTEmem (m + 1) _ w.2)
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => rw [map_mul]; exact mul_mem h₁ h₂
    | inv w _ h₁ => rw [map_inv₀]; exact inv_mem h₁
  have hCT : ∀ w ∈ Differential.constField L E₁, w ∈ T₁ := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem w hw =>
      obtain ⟨c0, hc0⟩ := hconstC w hw
      rw [← hc0]
      exact S₁.const_mem c0
    | algebraMap z => exact hLT z
    | add w₁ w₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂
    | inv w _ h₁ => exact inv_mem h₁
  -- the integrand is a polynomial in `x, y`
  have hψf : ψ f = ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) * (ψ θ) ^ j := by
    simp only [hfdef, map_sum, map_mul, map_pow, hPE]
  set Q : (TE.F m)[X][X] := ∑ j ∈ Finset.range n,
    Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (fp.getD j [])) * X ^ j with hQ
  have hQv : S₁.evXY Q = ψ f := by
    rw [hψf, CurveData.evXY, hQ, Polynomial.map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eval_mul, eval_C,
      eval_pow, eval_X]
    congr 1
    exact TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm) _
  have hfT : ψ f ∈ T₁ := hLT f
  have hfQ : (⟨ψ f, hfT⟩ : T₁) = S₁.evT Q := Subtype.ext (by rw [S₁.coe_evT, hQv])
  have hreg : S₁.RegularFinite (AlgebraicClosure (TE.F m)) ⟨ψ f, hfT⟩ := by
    rw [hfQ]; exact S₁.regularFinite_evT Q
  -- the logarithmic part lies in `Fₘ`
  have heq₁ : ψ f = v′ + ∑ i ∈ s', c i * logDeriv (u i) := by rw [heqL, add_comm]
  -- the inverted curve and its place data
  have hS₁Q : S₁.F = (toB Fq).map (mapRingHom (algebraMap ℚ (TE.F m))) :=
    TE.nkF_eqQ m hTEm Pp Fq hPp hmonQ hdegQ
  obtain ⟨hMb, hinvEq⟩ := mob_data (C := TE.F m) Fq k0 M hinv S₁.F hS₁Q
  have hGm' : (invP (shiftP S₁.F 0) k0 M).Monic := by rw [hinvEq]; exact hGm.map _
  have hGn' : (invP (shiftP S₁.F 0) k0 M).natDegree = S₁.F.natDegree := by
    rw [hinvEq, natDegree_map_eq_of_injective (map_injective _ (algebraMap ℚ (TE.F m)).injective),
      hGn, hS₁F]
  have hιmem : ∀ a : F, ψ (algebraMap Cc L (ιC a)) ∈ TE.F m := fun a ↦
    hTEmem m _ (T.const_mem m (ιC a))
  set ιF : F →+* TE.F m := RingHom.codRestrict ((algebraMap L E₁).comp ((algebraMap Cc L).comp ιC))
    (TE.F m) hιmem with hιFdef
  obtain ⟨Fc', Pc, hFc', hPcc, hfib1, hpl, hα0⟩ := hpd
  have hmon' : (toB Fc').Monic := by rw [hFc']; exact hGm.map _
  have hn0' : 0 < (toB Fc').natDegree := by
    rw [hFc', natDegree_map_eq_of_injective (map_injective _ (algebraMap ℚ F).injective), hGn]
    exact hn0
  have hPcd : Pc.Facts Fc' (toB Fc').natDegree := Pc.check_spec hPcc
  have hSF' : (mobCurve S₁ 0 k0 M hMb hGm' hGn').F = (toB Fc').map (mapRingHom ιF) := by
    show invP (shiftP S₁.F 0) k0 M = _
    rw [hinvEq, hFc', Polynomial.map_map, mapRingHom_comp,
      ratHom_eq (ιF.comp (algebraMap ℚ F)) (algebraMap ℚ (TE.F m))]
  have hgeo' : Irreducible (S₁.F.map (mapRingHom (algebraMap (TE.F m)
      (AlgebraicClosure (TE.F m))))) := by
    rw [hS₁Q, Polynomial.map_map, mapRingHom_comp, ratHom_eq ((algebraMap (TE.F m)
      (AlgebraicClosure (TE.F m))).comp (algebraMap ℚ (TE.F m))) (algebraMap ℚ _)]
    exact hgeo _
  -- the unit `u₀`, its inverse and its logarithmic derivative
  have hPθE : TE.evθ m hTE (ψ θ) (nkPC Fc ks m Pp) = 0 := by rw [TE.evθ_nkPC]; exact hθE
  have hevPol : ∀ W : List (GPoly (LC m)), S₁.evXY (∑ j ∈ Finset.range W.length,
      Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (W.getD j [])) * X ^ j) =
      TE.evθ m hTE (ψ θ) (nkFl Fc ks m W) := by
    intro W
    rw [TE.evθ_nkFl m hTE (ψ θ) W, CurveData.evXY, Polynomial.map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eval_mul,
      eval_C, eval_pow, eval_X]
    congr 1
    exact TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm) _
  obtain ⟨hd, hall⟩ := unitsRNC_spec hU
  have hgl : ∀ i < gss.length, (gss.getD i []).length = μ.length := fun i hi ↦ (hall i hi).2.2.1
  set k := gss.length with hkk
  set αL : E₁ := ψ (algebraMap Cc L α) with hαL
  have hαc : αL′ = 0 := by rw [hαL, deriv_algebraMap, deriv_algebraMap, T.hC, map_zero, map_zero]
  set α' : Differential.constants E₁ := ⟨αL, hαc⟩ with hα'
  set αE : TE.F m := ⟨αL, TE.const_mem m α'⟩ with hαE
  have hμE : αL ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : E₁) * αL ^ l = 0 := by
    have := congrArg (fun z ↦ ψ (algebraMap Cc L z)) hαμ
    simpa [map_add, map_sum, map_mul, map_pow, map_intCast] using this
  have hevHom : ∀ Q : (TE.F m)[X][X], S₁.evXY Q = ((Polynomial.evalRingHom S₁.y).comp
      (Polynomial.mapRingHom (aeval S₁.x).toRingHom)) Q := fun Q ↦ rfl
  have hevα : S₁.evXY (Polynomial.C (Polynomial.C αE)) = αL := by
    rw [CurveData.evXY, Polynomial.map_C, eval_C]
    simp [hαE, hαL]
  have hgetD : ∀ (Ws : List (List (GPoly (LC m)))) (k : ℕ),
      (Ws.map (nkFl Fc ks m)).getD k [] = nkFl Fc ks m (Ws.getD k []) := fun Ws k ↦ by
    rw [show ([] : List (LC (m + 1))) = nkFl Fc ks m [] from rfl, List.getD_map]
  have hevN : ∀ Ws : List (List (GPoly (LC m))), S₁.evXY (∑ k ∈ Finset.range Ws.length,
      Polynomial.C (Polynomial.C αE) ^ k * ∑ j ∈ Finset.range (Ws.getD k []).length,
        Polynomial.C (GPoly.toPoly (TE.MP m hTEm) ((Ws.getD k []).getD j [])) * X ^ j) =
      nVal (TE.evθ m hTE (ψ θ)) αL (Ws.map (nkFl Fc ks m)) := by
    intro Ws
    rw [nVal_eq_sum (TE.evθ_RSem m hTE (ψ θ)) αL _ Ws.length (by simp), hevHom, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, map_pow, ← hevHom, ← hevHom, hevα, hevPol]
    congr 1
    exact congrArg (TE.evθ m hTE (ψ θ)) (hgetD Ws k).symm
  set UQ : ℕ → (TE.F m)[X][X] := fun i ↦ ∑ kk ∈ Finset.range (Ass.getD i []).length,
      Polynomial.C (Polynomial.C αE) ^ kk * ∑ j ∈ Finset.range ((Ass.getD i []).getD kk []).length,
        Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (((Ass.getD i []).getD kk []).getD j [])) * X ^ j
    with hUQ
  set VQ : ℕ → (TE.F m)[X][X] := fun i ↦ ∑ kk ∈ Finset.range (Bss.getD i []).length,
      Polynomial.C (Polynomial.C αE) ^ kk * ∑ j ∈ Finset.range ((Bss.getD i []).getD kk []).length,
        Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (((Bss.getD i []).getD kk []).getD j [])) * X ^ j
    with hVQ
  set u0T : Fin k → T₁ := fun i ↦ S₁.evT (UQ i) with hu0T
  set v0T : Fin k → T₁ := fun i ↦ S₁.evT (VQ i) with hv0T
  have hu0v : ∀ i : Fin k, (u0T i : E₁) =
      nVal (TE.evθ m hTE (ψ θ)) αL ((Ass.getD i []).map (nkFl Fc ks m)) := fun i ↦ by
    rw [hu0T]; simp only; rw [S₁.coe_evT, hUQ]; simp only; rw [hevN]
  have hv0v : ∀ i : Fin k, (v0T i : E₁) =
      nVal (TE.evθ m hTE (ψ θ)) αL ((Bss.getD i []).map (nkFl Fc ks m)) := fun i ↦ by
    rw [hv0T]; simp only; rw [S₁.coe_evT, hVQ]; simp only; rw [hevN]
  have huvE : ∀ i : Fin k, (u0T i : E₁) * (v0T i : E₁) = 1 := fun i ↦ by
    rw [hu0v, hv0v]; exact TE.unitCN_sound m hTE (ψ θ) Pp hPθE μ hd αL hμE _ _ (hall i i.2).1
  have huv1 : ∀ i, u0T i * v0T i = 1 := fun i ↦
    Subtype.ext (by rw [IntermediateField.coe_mul, huvE]; rfl)
  have hu00 : ∀ i, u0T i ≠ 0 := fun i ↦ left_ne_zero_of_mul_eq_one (huv1 i)
  have hu0E : ∀ i, (u0T i : E₁) ≠ 0 := fun i h ↦ hu00 i (Subtype.ext h)
  have hfin0 : ∀ i (a : AlgebraicClosure (TE.F m)) (N : ℕ) (hN : N ≠ 0)
      (l : List (LaurentSeries (AlgebraicClosure (TE.F m))))
      (hl : S₁.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries (AlgebraicClosure (TE.F m))) (hr : r ∈ l),
      (S₁.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S₁.root_of_mem hl hr) (u0T i)).order = 0 := by
    intro i a N hN l hl r hr
    set φ := S₁.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
      (S₁.root_of_mem hl hr)
    have h1 : φ (u0T i) * φ (v0T i) = 1 := by rw [← map_mul, huv1, map_one]
    have hu' : φ (u0T i) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hv' : φ (v0T i) ≠ 0 := right_ne_zero_of_mul_eq_one h1
    have o1 := S₁.regularFinite_evT (K := AlgebraicClosure (TE.F m)) (UQ i) a N hN l hl r hr
    have o2 := S₁.regularFinite_evT (K := AlgebraicClosure (TE.F m)) (VQ i) a N hN l hl r hr
    have ho := congrArg HahnSeries.order h1
    rw [HahnSeries.order_mul hu' hv', HahnSeries.order_one] at ho
    change 0 ≤ (φ (u0T i)).order at o1
    change 0 ≤ (φ (v0T i)).order at o2
    omega
  set M1 := TE.MPr (m + 1) hTE with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  set G : ℕ → ℕ → E₁ := fun i j ↦ ∑ kk ∈ Finset.range μ.length, αL ^ kk *
    ((M1.sem (((gss.getD i []).getD kk []).getD j O1.zero) : TE.F (m + 1)) : E₁) with hG
  have hαmem : αL ∈ (TE.F m)⟮S₁.x⟯ := IntermediateField.algebraMap_mem _ αE
  have hGmem : ∀ i j, G i j ∈ (TE.F m)⟮S₁.x⟯ := fun i j ↦ sum_mem fun kk _ ↦
    mul_mem (pow_mem hαmem _) ((TE.mem_F_succ).mp (M1.sem (((gss.getD i []).getD kk []).getD j
      O1.zero)).2)
  have hlogN : ∀ i : Fin k, (u0T i : E₁)′ =
      nVal (TE.evθ m hTE (ψ θ)) αL (gss.getD i []) * (u0T i : E₁) := fun i ↦ by
    rw [hu0v]
    exact TE.logDerChkN_sound m hTE (ψ θ) Pp hPθE μ hd αL hαc hμE _ _ dθ wθ (hall i i.2).2.1
  have hnVg : ∀ i : Fin k, nVal (TE.evθ m hTE (ψ θ)) αL (gss.getD i []) =
      ∑ j ∈ Finset.range n, G i j * (ψ θ) ^ j := by
    intro i
    rw [nVal_eq_sum (TE.evθ_RSem m hTE (ψ θ)) αL _ μ.length (hgl i i.2).le]
    simp only [hG, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun kk hk ↦ ?_
    change αL ^ kk * TE.evθ m hTE (ψ θ) ((gss.getD i []).getD kk []) = _
    rw [TE.evθ_list_le m hTE (ψ θ) _ n ((hall i i.2).2.2.2 kk (Finset.mem_range.mp hk)).1,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hlogu : ∀ i : Fin k, logDeriv (u0T i : E₁) = ∑ j ∈ Finset.range n, G i j * (ψ θ) ^ j :=
    fun i ↦ by rw [logDeriv, hlogN i, mul_div_assoc, div_self (hu0E i), mul_one, hnVg i]
  have hindθ := TE.nkCurveG_ind m hTE Pp Fq hPp hmonQ hdegQ hgeo (ψ θ) hθE
  have hindU : ∀ a : Fin k → ℤ, (∃ c : TE.F m, ∏ i, (u0T i : E₁) ^ a i =
      algebraMap (TE.F m) E₁ c) → a = 0 :=
    TE.indepCN_sound m hTE (ψ θ) n hindθ μ hd αL αE.2 hμE gss hgl
      (fun i hi kk hkk ↦ ((hall i hi).2.2.2 kk hkk).1) (fun i ↦ (u0T i : E₁)) hu0E
      (fun i ↦ by rw [hlogN i, mul_div_assoc, div_self (hu0E i), mul_one]) J H hJH
  -- the logarithmic part is `∑ κᵢ uᵢ′/uᵢ + ℓ`
  obtain ⟨κ, ℓ₀, hκ, hℓ₀⟩ := S₁.nk_liouville_units (K := AlgebraicClosure (TE.F m))
    (Polynomial.C η₁) hx hK hnd k0 M hMb hGm' hGn' hgeo' ιF Fc' hmon' hSF' Pc hPcd hn0' hfib1
    hα0 hpl u0T hu00 hfin0 hindU hconstC (ψ f) hfT hreg s' c u
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hCT _ (hdata i hi).2.1⟩) v
    (hCT v hv) heq₁
  set κE : Fin k → E₁ := fun i ↦ algebraMap (TE.F m) E₁ (κ i) with hκE
  have hκE' : ∀ i, (κE i)′ = 0 := fun i ↦ by
    rw [hκE]; simp only; rw [deriv_algebraMap, hκ i, map_zero]
  have hc0 : ∀ i, κE i ∈ Set.range (algebraMap _ E₁) := fun i ↦ TE.hconst _ (hκE' i)
  simp only [Set.mem_range] at hc0
  choose c0 hc0 using hc0
  have hκsum : ∀ w : ℕ → E₁, ∑ j ∈ Finset.range n, (∑ i : Fin k, κE i * G i j) * w j =
      ∑ i : Fin k, κE i * ∑ j ∈ Finset.range n, G i j * w j := fun w ↦ by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  -- the trace
  obtain ⟨hs0, hτ⟩ := TE.traceW_sound m hTE Pp (ψ θ) hPθE dθ wθ s hs
  have hdx : ∀ z ∈ (TE.F m)⟮S₁.x⟯, z′ ∈ (TE.F m)⟮S₁.x⟯ := fun z hz ↦ by
    have := ((⟨z, (TE.mem_F_succ).mpr hz⟩ : TE.F (m + 1))′ : TE.F (m + 1)).2
    rw [MTower.coe_deriv] at this
    exact (TE.mem_F_succ).mp this
  have hκx : ∀ i, κE i ∈ (TE.F m)⟮S₁.x⟯ := fun i ↦ IntermediateField.algebraMap_mem _ (κ i)
  set fc : ℕ → E₁ := fun j ↦ TE.evP m (fp.getD j []) - ∑ i : Fin k, κE i * G i j with hfc
  obtain ⟨w, hw, hwe⟩ := S₁.trace_split (fun j ↦ ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁))
    (fun j ↦ (TE.mem_F_succ).mp (M1.sem (s.getD j O1.zero)).2)
    (by rw [hS₁F, hs0]; push_cast; rfl)
    (fun i hi ↦ by
      rw [hS₁F] at hi ⊢
      obtain ⟨c', hc'd, hc's⟩ := hτ i hi
      refine ⟨fun j ↦ (c' j : E₁), fun j ↦ (TE.mem_F_succ).mp (c' j).2, hc'd, ?_⟩
      have := congrArg (fun z : TE.F (m + 1) ↦ (z : E₁)) hc's
      simp only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul,
        MTower.coe_deriv] at this
      exact this)
    hdx fc (fun j ↦ sub_mem ((TE.mem_F_succ).mp (TE.evP_mem m (TE.ev_mem m) _))
      (sum_mem fun i _ ↦ mul_mem (hκx i) (hGmem i j)))
    v (hCT v hv) (algebraMap (TE.F m) E₁ ℓ₀) (IntermediateField.algebraMap_mem _ ℓ₀)
    (by
      rw [hS₁F]
      change ∑ j ∈ Finset.range n, fc j * (ψ θ) ^ j = _
      simp only [hfc, sub_mul, Finset.sum_sub_distrib]
      rw [hκsum, ← hψf, hℓ₀]
      simp only [← hlogu, hκE]
      ring)
  rw [hS₁F] at hwe
  -- `τ(uᵢ′/uᵢ) = 0`
  have hτ0 : ∀ i : Fin k, ∑ j ∈ Finset.range n, G i j *
      ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) = 0 := by
    intro i
    have hk0 : ∀ kk < μ.length, ∑ j ∈ Finset.range n,
        ((M1.sem (((gss.getD i []).getD kk []).getD j O1.zero) : TE.F (m + 1)) : E₁) *
        ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) = 0 := by
      intro kk hkk
      have h1 := (M1.isZero_iff _).mp ((hall i i.2).2.2.2 kk hkk).2
      rw [TE.sem_nkTau m n hTE ((gss.getD i []).getD kk []) s] at h1
      have hn' : ((n : ℕ) : TE.F (m + 1)) ≠ 0 := by exact_mod_cast hn0.ne'
      have h2 : ∑ j ∈ Finset.range n, M1.sem (((gss.getD i []).getD kk []).getD j O1.zero) *
          M1.sem (s.getD j O1.zero) = 0 :=
        (mul_eq_zero.mp h1).resolve_right (inv_ne_zero hn')
      have := congrArg (fun z : TE.F (m + 1) ↦ (z : E₁)) h2
      simpa only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul,
        ZeroMemClass.coe_zero] using this
    simp only [hG, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun kk hk ↦ ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [hk0 kk (Finset.mem_range.mp hk), mul_zero]
  have hτf : ∑ j ∈ Finset.range n, fc j * ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) =
      ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) *
        ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁) := by
    simp only [hfc, sub_mul, Finset.sum_sub_distrib]
    rw [hκsum, Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin k))) fun i _ ↦ by
      rw [hτ0 i, mul_zero], sub_zero]
  rw [hτf] at hwe
  -- `ψ (τ(f)/n)`
  have hqv : ψ (T.ev (m + 1) q) = (∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) *
      ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁)) / n := by
    rw [← hTEev (m + 1) q, ← TE.coe_sem_MPr (m + 1) hTE q, hq, TE.sem_nkTau m n hTE]
    push_cast
    rw [div_eq_mul_inv]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [TE.sem_nkFl m hTE fp j]
  have hlog : algebraMap (TE.F m) E₁ ℓ₀ =
      ∑ i ∈ s', c i * logDeriv (u i) - ∑ i : Fin k, κE i * logDeriv (u0T i : E₁) := by
    have := hℓ₀.symm.trans heq₁
    rw [eq_sub_iff_add_eq]
    linear_combination this
  refine ⟨?_, ?_⟩
  · ----------------------------------------------------------------------------------------------
    -- the exact part in the lifted tower
    have hvw : v - w ∈ T₁ := sub_mem (hCT v hv) (IntermediateField.algebraMap_mem T₁
      (⟨w, hw⟩ : (TE.F m)⟮S₁.x⟯))
    obtain ⟨Y', hY'm, hY'⟩ := S₁.exists_coords (v - w) hvw
    rw [hS₁F] at hY'
    have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
    have hind : ∀ a : ℕ → TE.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
        (a j : E₁) * (ψ θ) ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
      rw [hlen]; exact TE.nkCurveG_ind m hTE Pp Fq hPp hmonQ hdegQ hgeo (ψ θ) hθE
    have hiff := TE.exactTL_correct m hTE (hTE m (by omega)) _ _ _
      (TE.primSpec (by omega) hTEm (hTE m (by omega)) hk (paramLimC Fc ks lv m) MSEm.lim)
      (nkPC Fc ks m Pp) _ (ψ θ) hPθE hind Tc Ti gss.flatten res hres
    set c' := fun q ↦ if h : q / μ.length < k then c0 ⟨q / μ.length, h⟩ * α' ^ (q % μ.length)
      else 0 with hc'
    refine hiff.mpr ⟨c', fun i ↦ ⟨Y' i, (TE.mem_F_succ).mpr (hY'm i)⟩, ?_⟩
    rw [hlen]
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [TE.sum_nkRest m hTE n hn0, hTEev (m + 1) q]
    have hflen := length_flatten_mul μ.length gss hgl
    have hcs : ∑ j ∈ Finset.range n, (∑ q ∈ Finset.range gss.flatten.length, algebraMap _ E₁
        (c' q) * ((M1.sem ((gss.flatten.getD q []).getD j O1.zero) : TE.F (m + 1)) : E₁)) *
        (ψ θ) ^ j = ∑ i : Fin k, κE i * logDeriv (u0T i : E₁) := by
      have e : ∀ j, ∑ q ∈ Finset.range gss.flatten.length, algebraMap _ E₁ (c' q) *
          ((M1.sem ((gss.flatten.getD q []).getD j O1.zero) : TE.F (m + 1)) : E₁) =
          ∑ i : Fin k, κE i * G i j := fun j ↦ by
        rw [hflen, sum_range_mul, ← Fin.sum_univ_eq_sum_range (fun i ↦ ∑ kk ∈ Finset.range μ.length,
          algebraMap _ E₁ (c' (i * μ.length + kk)) * ((M1.sem ((gss.flatten.getD (i * μ.length + kk)
            []).getD j O1.zero) : TE.F (m + 1)) : E₁))]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [hG, Finset.mul_sum]
        refine Finset.sum_congr rfl fun kk hkk ↦ ?_
        have hkk' := Finset.mem_range.mp hkk
        have hdiv : (i * μ.length + kk) / μ.length = i := by
          rw [show (i : ℕ) * μ.length + kk = kk + μ.length * i by ring,
            Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hkk', zero_add]
        have hmod : (i * μ.length + kk) % μ.length = kk := by
          rw [show (i : ℕ) * μ.length + kk = kk + μ.length * i by ring, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt hkk']
        rw [getD_flatten_mul μ.length [] gss hgl i i.2 kk hkk', hc']
        simp only [hdiv, hmod]
        rw [dif_pos i.2]
        simp only [Fin.eta, map_mul, map_pow, hc0]
        have hαα : algebraMap (Differential.constants E₁) E₁ α' = αL := rfl
        rw [hαα]; ring
      simp only [e]
      rw [hκsum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hlogu]
    rw [hcs]
    change (∑ i ∈ Finset.range n, Y' i * S₁.y ^ i)′ = _
    rw [← hY', ← hψf, hqv, hwe, map_sub, hℓ₀]
    ring
  · ----------------------------------------------------------------------------------------------
    -- `τ(f)/n` has a Liouville form in `E₁`
    set l : List (E₁ × E₁) := s'.toList.map (fun i ↦ (c i, u i)) ++
      (List.finRange k).map (fun i ↦ (-κE i, (u0T i : E₁))) with hl0
    have hl : ∀ p ∈ l, p.1′ = 0 ∧ p.2 ≠ 0 := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
        rw [Finset.mem_toList] at hi
        exact ⟨(hdata i hi).1, (hdata i hi).2.2⟩
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
        exact ⟨by rw [map_neg, hκE' i, neg_zero], hu0E i⟩
    have hform := hasElementaryIntegral_of_liouville_form w l hl
    have hsumeq : w′ + (l.map fun p ↦ p.1 * logDeriv p.2).sum = ψ (T.ev (m + 1) q) := by
      rw [hqv, hwe, hlog, hl0, List.map_append, List.sum_append, List.map_map,
        Finset.sum_map_toList, List.map_map, ← Fin.sum_univ_def]
      simp only [Function.comp_def, neg_mul, Finset.sum_neg_distrib]
      ring
    rw [hsumeq] at hform
    exact HasElementaryIntegral.of_extension hE₁ hform



/-- **The decision with several places at infinity** (logarithmic level; units over `ℚ(α)`,
independent by `indepCN`, with `τ(gᵢₖ) = 0`). -/
theorem nk_iffRN (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (Fq : BPoly ℚ) (hPp : Pp = liftCurve Fc ks m Pp.length Fq)
    (hmonQ : (toB Fq).Monic) (hdegQ : (toB Fq).natDegree = Pp.length) (hn0 : 0 < Pp.length)
    (hgeo : GeomIrr.{u} Fq) (θ : L)
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] (ιC : F →+* Cc) (k0 M : ℕ)
    (hinv : InvOK k0 M 0 (shiftB Fq 0)) (hGm : (toB (invB (shiftB Fq 0) k0 M)).Monic)
    (hGn : (toB (invB (shiftB Fq 0) k0 M)).natDegree = Pp.length)
    (μ : List ℤ) (Ass Bss : List (List (List (GPoly (LC m)))))
    (gss : List (List (GPoly (LC (m + 1)))))
    (hpd : RPlaceDataP F (invB (shiftB Fq 0) k0 M) (gss.length + 1))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsRNC Fc ks m Pp μ Ass Bss gss dθ wθ s = true)
    (J : List ℕ) (H : List (List (List (LC (m + 1))))) (hJH : indepCN Fc ks m μ gss J H = true)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (αs : Fin μ.length → Cc) (hαinj : Function.Injective αs)
    (hαμ : ∀ i, αs i ^ μ.length + ∑ l ∈ Finset.range μ.length, (μ.getD l 0 : Cc) * αs i ^ l = 0)
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (fp : List (GPoly (LC m))) (Tc Ti : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTL Fc ks m (primSysC Fc ks m η (paramLimC Fc ks lv m)) (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))
        gss.flatten = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  have hd := (unitsRNC_spec hU).1
  refine ⟨T.nk_necessaryRN hmon hdeg m hn hc hk Pp Fq hPp hmonQ hdegQ hn0 hgeo θ ιC k0 M hinv hGm
    hGn μ Ass Bss gss hpd dθ wθ s hU J H hJH hθ hgen (αs ⟨0, hd⟩) (hαμ _) hs fp Tc Ti res hres,
    fun h ↦ ?_⟩
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  exact T.nk_sufficientRN m hTr (hTr m (by omega)) _ _ _
    (T.primSpec (by omega) hTr.of_succ (hTr m (by omega)) hk (paramLimC Fc ks lv m) MSm.lim)
    Pp hn0 θ hθ (T.nkCurveG_ind m hTr Pp Fq hPp hmonQ hdegQ hgeo θ hθ) μ Ass Bss gss dθ wθ s hU
    αs hαinj hαμ fp Tc Ti res hres h.1 h.2

end MTower

end Curves.MT
