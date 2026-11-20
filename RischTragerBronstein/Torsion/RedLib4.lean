import RischTragerBronstein.Torsion.RedLib3

/-!
# Reduction of list computations (4): Newton lifts and the subset certificate

* `sMulT_pext`, `evalBT_pext`, `newtonT_pext` (the divisions of Newton's iteration are by units:
  `newtonVals`);
* `prodSubB_pext`, **`irrSubsetCheck_pext`**, **`irrAt_pext`**: the subset certificate of
  irreducibility reduces when the non-zero coefficients it exhibits reduce to non-zero values.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Newton

variable {F F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F']
  {S : Subring F} {g : S →+* F'}

lemma range_map_pext (L : ℕ) (f : ℕ → F) (hf : ∀ m, f m ∈ S) :
    InS S ((List.range L).map f) ∧ ((List.range L).map f).map (pext S g) = (List.range L).map (pext S g ∘ f) := by
  refine ⟨fun c hc ↦ ?_, by rw [List.map_map]⟩
  obtain ⟨m, -, rfl⟩ := List.mem_map.mp hc
  exact hf m

lemma sMulT_pext (p q : List F) (hp : InS S p) (hq : InS S q) (L : ℕ) :
    InS S (sMulT p q L) ∧ (sMulT p q L).map (pext S g) = sMulT (p.map (pext S g)) (q.map (pext S g)) L := by
  have hs : ∀ m, (∑ i ∈ Finset.range (m + 1), p.getD i 0 * q.getD (m - i) 0) ∈ S ∧
      pext S g (∑ i ∈ Finset.range (m + 1), p.getD i 0 * q.getD (m - i) 0) =
        ∑ i ∈ Finset.range (m + 1), pext S g (p.getD i 0) * pext S g (q.getD (m - i) 0) := fun m ↦ by
    obtain ⟨h1, h2⟩ := sum_pext (g := g) (Finset.range (m + 1)) (fun i ↦ p.getD i 0 * q.getD (m - i) 0)
      (fun i _ ↦ S.mul_mem (hp.getD i) (hq.getD _))
    exact ⟨h1, by rw [h2]; exact Finset.sum_congr rfl fun i _ ↦ pext_mul (hp.getD i) (hq.getD _)⟩
  obtain ⟨h1, h2⟩ := range_map_pext (g := g) L _ fun m ↦ (hs m).1
  refine ⟨h1, ?_⟩
  rw [sMulT, h2, sMulT]
  refine List.map_congr_left fun m _ ↦ ?_
  simp only [Function.comp_apply, (hs m).2, getD_pext]

lemma evalBT_pext (Z : List F) (hZ : InS S Z) (L : ℕ) : ∀ (H : List (List F)), InSB S H →
    InS S (evalBT H Z L) ∧ (evalBT H Z L).map (pext S g) = evalBT (H.map (·.map (pext S g))) (Z.map (pext S g)) L
  | [], _ => ⟨InS.nil, rfl⟩
  | c :: H, hH => by
    have hc : InS S c := hH c List.mem_cons_self
    obtain ⟨h1, h2⟩ := evalBT_pext Z hZ L H fun P hP ↦ hH P (List.mem_cons_of_mem _ hP)
    obtain ⟨h3, h4⟩ := sMulT_pext (g := g) Z (evalBT H Z L) hZ h1 L
    have e : evalBT (c :: H) Z L = (List.range L).map fun m ↦ c.getD m 0 + (sMulT Z (evalBT H Z L) L).getD m 0 := rfl
    obtain ⟨h5, h6⟩ := range_map_pext (g := g) L (fun m ↦ c.getD m 0 + (sMulT Z (evalBT H Z L) L).getD m 0)
      fun m ↦ S.add_mem (hc.getD m) (h3.getD m)
    refine ⟨by rw [e]; exact h5, ?_⟩
    rw [e, h6]
    show _ = (List.range L).map fun m ↦ (c.map (pext S g)).getD m 0 +
      (sMulT (Z.map (pext S g)) (evalBT (H.map (·.map (pext S g))) (Z.map (pext S g)) L) L).getD m 0
    refine List.map_congr_left fun m _ ↦ ?_
    simp only [Function.comp_apply]
    rw [pext_add (hc.getD m) (h3.getD m), getD_pext, ← h2, ← h4, getD_pext]

/-- The divisors of Newton's iteration. -/
def newtonVals (H : List (List F)) (L : ℕ) : ℕ → List F → List F
  | 0, _ => []
  | k + 1, Z => (evalBT (derivYB H) Z L).getD 0 0 ::
      newtonVals H L k ((List.range L).map fun m ↦ Z.getD m 0 -
        (sDivT (evalBT H Z L) (evalBT (derivYB H) Z L) L).getD m 0)

/-- **Newton's iteration reduces** when its divisors are units. -/
lemma newtonT_pext (H : List (List F)) (hH : InSB S H) (L : ℕ) : ∀ (k : ℕ) (Z : List F), InS S Z →
    (∀ v ∈ newtonVals H L k Z, v ≠ 0 ∧ v⁻¹ ∈ S) →
    InS S (newtonT H L k Z) ∧ (newtonT H L k Z).map (pext S g) =
      newtonT (H.map (·.map (pext S g))) L k (Z.map (pext S g))
  | 0, Z, hZ, _ => ⟨hZ, rfl⟩
  | k + 1, Z, hZ, hu => by
    obtain ⟨hd, hd'⟩ := derivYB_pext (g := g) H hH
    obtain ⟨hV, hV'⟩ := evalBT_pext (g := g) Z hZ L H hH
    obtain ⟨hD, hD'⟩ := evalBT_pext (g := g) Z hZ L (derivYB H) hd
    obtain ⟨hu0, hui⟩ := hu _ List.mem_cons_self
    obtain ⟨hq, hq'⟩ := divTrunc_pext (g := g) _ _ hV hD hu0 hui L
    obtain ⟨hZ1, hZ1'⟩ := range_map_pext (g := g) L (fun m ↦ Z.getD m 0 -
      (sDivT (evalBT H Z L) (evalBT (derivYB H) Z L) L).getD m 0)
      fun m ↦ S.sub_mem (hZ.getD m) (hq.getD m)
    obtain ⟨h1, h2⟩ := newtonT_pext H hH L k _ hZ1 fun v hv ↦ hu v (List.mem_cons_of_mem _ hv)
    refine ⟨h1, ?_⟩
    show (newtonT H L k _).map (pext S g) = newtonT (H.map (·.map (pext S g))) L k
      ((List.range L).map fun m ↦ (Z.map (pext S g)).getD m 0 -
        (sDivT (evalBT (H.map (·.map (pext S g))) (Z.map (pext S g)) L)
          (evalBT (derivYB (H.map (·.map (pext S g)))) (Z.map (pext S g)) L) L).getD m 0)
    rw [h2, hZ1']
    congr 1
    refine List.map_congr_left fun m _ ↦ ?_
    simp only [Function.comp_apply, sDivT]
    rw [pext_sub (hZ.getD m) (hq.getD m), getD_pext, ← hd', ← hV', ← hD', ← hq', getD_pext]

end Newton

section Subsets

variable {F F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F']
  {S : Subring F} {g : S →+* F'}

lemma smulB_pext (c : List F) (hc : InS S c) (W : List (List F)) (hW : InSB S W) :
    InSB S (smulB c W) ∧ (smulB c W).map (·.map (pext S g)) = smulB (c.map (pext S g)) (W.map (·.map (pext S g))) := by
  refine ⟨fun P hP ↦ ?_, ?_⟩
  · obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hP
    exact (mul_pext (g := g) c Q hc (hW Q hQ)).1
  · simp only [smulB, List.map_map]
    refine List.map_congr_left fun Q hQ ↦ ?_
    simp only [Function.comp_apply]
    exact (mul_pext (g := g) c Q hc (hW Q hQ)).2

lemma mulB_pext : ∀ (W V : List (List F)), InSB S W → InSB S V →
    InSB S (mulB W V) ∧ (mulB W V).map (·.map (pext S g)) = mulB (W.map (·.map (pext S g))) (V.map (·.map (pext S g)))
  | [], V, _, _ => ⟨fun _ h ↦ by simp [mulB] at h, rfl⟩
  | a :: W, V, hW, hV => by
    have ha : InS S a := hW a List.mem_cons_self
    obtain ⟨h1, h2⟩ := mulB_pext W V (fun P hP ↦ hW P (List.mem_cons_of_mem _ hP)) hV
    obtain ⟨h3, h4⟩ := smulB_pext (g := g) a ha V hV
    have h5 : InSB S ([] :: mulB W V) := fun P hP ↦ by
      rcases List.mem_cons.mp hP with rfl | hP
      · exact InS.nil
      · exact h1 P hP
    obtain ⟨h6, h7⟩ := addB_pext (g := g) _ _ h3 h5
    refine ⟨h6, ?_⟩
    simp only [mulB, List.map_cons]
    rw [h7, h4, List.map_cons, h2]
    rfl

lemma neg_pext (p : List F) (hp : InS S p) :
    InS S (neg p) ∧ (neg p).map (pext S g) = neg (p.map (pext S g)) := by
  obtain ⟨h1, h2⟩ := smul_pext (g := g) (S.neg_mem S.one_mem) p hp
  refine ⟨h1, ?_⟩
  rw [neg, h2, pext_neg S.one_mem, pext_one]
  rfl

lemma prodSubB_pext (ys : List (List F)) (hys : InSB S ys) : ∀ (L : List ℕ),
    InSB S (prodSubB ys L) ∧ (prodSubB ys L).map (·.map (pext S g)) = prodSubB (ys.map (·.map (pext S g))) L
  | [] => ⟨fun P hP ↦ by
      simp only [prodSubB, List.foldr_nil, List.mem_singleton] at hP
      subst hP; exact InS.cons S.one_mem InS.nil, by simp [prodSubB, pext_one]⟩
  | j :: L => by
    obtain ⟨h1, h2⟩ := prodSubB_pext ys hys L
    obtain ⟨h3, h4⟩ := neg_pext (g := g) _ (hys.getD j)
    have hlin : InSB S [neg (ys.getD j []), [1]] := fun P hP ↦ by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · exact h3
      · exact InS.cons S.one_mem InS.nil
    obtain ⟨h5, h6⟩ := mulB_pext (g := g) _ _ hlin h1
    have e : prodSubB ys (j :: L) = mulB [neg (ys.getD j []), [1]] (prodSubB ys L) := rfl
    refine ⟨by rw [e]; exact h5, ?_⟩
    rw [e, h6, h2]
    show mulB [(neg (ys.getD j [])).map (pext S g), [pext S g 1]] _ =
      mulB [neg ((ys.map (·.map (pext S g))).getD j []), [1]] (prodSubB (ys.map (·.map (pext S g))) L)
    rw [h4, pext_one, getD_mapLL]

/-- **The subset certificate reduces** (its non-zero coefficients being units). -/
lemma irrSubsetCheck_pext {Fc : List (List F)} {n d : ℕ} {a : F} {c : BranchCert F}
    (hF : InSB S Fc) (ha : a ∈ S) (hys : InSB S c.ys)
    (hu : ∀ y ∈ c.ys, OrdUnit S g (bivEvalT (derivYB Fc) (shiftC a c.N) y c.prec))
    (hsep : SepUnit (S := S) (g := g) c.ys c.prec)
    (hZ : ∀ L ∈ subsetsL n, ∀ i t, ZP S (((prodSubB c.ys L).getD i []).getD t 0))
    (h : irrSubsetCheck Fc n d a c = true) :
    irrSubsetCheck (Fc.map (·.map (pext S g))) n d (pext S g a)
      ⟨c.N, c.ys.map (·.map (pext S g)), c.prec⟩ = true := by
  simp only [irrSubsetCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, List.any_eq_true,
    List.mem_range] at h ⊢
  obtain ⟨⟨⟨hc, hN⟩, hlen⟩, hL⟩ := h
  refine ⟨⟨⟨certCheck_pext hF ha hys hu hsep hc, hN⟩, fun q hq ↦ ?_⟩, fun L hLm ↦ ?_⟩
  · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    rw [List.length_map]; exact hlen q0 hq0
  · rcases hL L hLm with h1 | ⟨i, hi, t, ht, hdt, hne⟩
    · exact Or.inl h1
    · right
      refine ⟨i, hi, t, ht, hdt, ?_⟩
      obtain ⟨h5, h6⟩ := prodSubB_pext (g := g) c.ys hys L
      rw [← h6, getD_mapLL, getD_pext]
      exact fun h0 ↦ hne ((pext_eq_zero_iff (hZ L hLm i t)).mp h0)

end Subsets

section IrrAt

variable {F F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F']
  {S : Subring F} {g : S →+* F'}

/-- **The Newton lifts reduce.** -/
lemma liftRootsAt_pext {Fc : List (List F)} {a : F} {ys0 : List F} {prec : ℕ}
    (hF : InSB S Fc) (ha : a ∈ S) (hy : InS S ys0)
    (hu : ∀ y0 ∈ ys0, ∀ v ∈ newtonVals (Fc.map fun q ↦ compC q (shiftC a 1)) prec
      (Nat.log2 prec + 3) [y0], v ≠ 0 ∧ v⁻¹ ∈ S) :
    InSB S (liftRootsAt Fc a ys0 prec).ys ∧
      liftRootsAt (Fc.map (·.map (pext S g))) (pext S g a) (ys0.map (pext S g)) prec =
        ⟨(liftRootsAt Fc a ys0 prec).N, (liftRootsAt Fc a ys0 prec).ys.map (·.map (pext S g)),
          (liftRootsAt Fc a ys0 prec).prec⟩ := by
  obtain ⟨hs, hs'⟩ := shiftC_pext (g := g) ha 1
  have hH : InSB S (Fc.map fun q ↦ compC q (shiftC a 1)) := fun P hP ↦ by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hP
    exact (compC_pext (g := g) _ hs q (hF q hq)).1
  have hH' : (Fc.map fun q ↦ compC q (shiftC a 1)).map (·.map (pext S g)) =
      Fc.map ((fun q ↦ compC q (shiftC (pext S g a) 1)) ∘ fun x ↦ x.map (pext S g)) := by
    simp only [List.map_map]
    refine List.map_congr_left fun q hq ↦ ?_
    simp only [Function.comp_apply]
    rw [(compC_pext (g := g) _ hs q (hF q hq)).2, hs']
  refine ⟨fun P hP ↦ ?_, ?_⟩
  · simp only [liftRootsAt, List.mem_map] at hP
    obtain ⟨y0, hy0, rfl⟩ := hP
    exact (newtonT_pext (g := g) _ hH prec _ [y0] (InS.cons (hy y0 hy0) InS.nil) (hu y0 hy0)).1
  · simp only [liftRootsAt, List.map_map, BranchCert.mk.injEq, true_and, and_true]
    rw [← hH']
    refine List.map_congr_left fun y0 hy0 ↦ ?_
    simp only [Function.comp_apply]
    obtain ⟨-, h2⟩ := newtonT_pext (g := g) _ hH prec (Nat.log2 prec + 3) [y0]
      (InS.cons (hy y0 hy0) InS.nil) (hu y0 hy0)
    rw [h2]
    rfl

/-- **The irreducibility certificate at a split point reduces.** -/
theorem irrAt_pext {Fc : List (List F)} {n d : ℕ} {a : F} {ys0 : List F} {prec : ℕ}
    (hF : InSB S Fc) (ha : a ∈ S) (hy : InS S ys0)
    (hnu : ∀ y0 ∈ ys0, ∀ v ∈ newtonVals (Fc.map fun q ↦ compC q (shiftC a 1)) prec
      (Nat.log2 prec + 3) [y0], v ≠ 0 ∧ v⁻¹ ∈ S)
    (hu : ∀ y ∈ (liftRootsAt Fc a ys0 prec).ys,
      OrdUnit S g (bivEvalT (derivYB Fc) (shiftC a (liftRootsAt Fc a ys0 prec).N) y prec))
    (hsep : SepUnit (S := S) (g := g) (liftRootsAt Fc a ys0 prec).ys prec)
    (hZ : ∀ L ∈ subsetsL n, ∀ i t,
      ZP S (((prodSubB (liftRootsAt Fc a ys0 prec).ys L).getD i []).getD t 0))
    (h : irrAt Fc n d a ys0 prec = true) :
    irrAt (Fc.map (·.map (pext S g))) n d (pext S g a) (ys0.map (pext S g)) prec = true := by
  obtain ⟨hys, hl⟩ := liftRootsAt_pext (g := g) hF ha hy hnu
  rw [irrAt, hl]
  exact irrSubsetCheck_pext hF ha hys hu hsep hZ h

end IrrAt

end Curves
