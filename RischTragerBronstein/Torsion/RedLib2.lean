import RischTragerBronstein.Torsion.RedLib1

/-!
# Reduction of list computations (2): reflections, truncated division, left inverses

* `reflectC_pext`, `invB_pext`, `shiftB_pext`: structural;
* `divTrunc_pext`: truncated division by a series whose constant term is a unit of `S`;
* `leftInvCheck_pext`: left-inverse certificates reduce.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Ops3

variable {F F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F']
  {S : Subring F} {g : S →+* F'}

lemma reflectC_pext (M : ℕ) (P : List F) (hP : InS S P) :
    InS S (reflectC M P) ∧ (reflectC M P).map (pext S g) = reflectC M (P.map (pext S g)) := by
  refine ⟨fun c hc ↦ ?_, ?_⟩
  · simp only [reflectC, List.mem_ofFn] at hc
    obtain ⟨j, rfl⟩ := hc
    exact hP.getD _
  · simp only [reflectC, List.map_ofFn]
    congr 1
    funext j
    exact (getD_pext _).symm

lemma invBAux_pext (k D : ℕ) : ∀ (W : List (List F)) (i : ℕ), InSB S W →
    InSB S (invBAux k D i W) ∧
      (invBAux k D i W).map (·.map (pext S g)) = invBAux k D i (W.map (·.map (pext S g)))
  | [], _, _ => ⟨fun _ h ↦ by simp [invBAux] at h, rfl⟩
  | c :: W, i, hW => by
    have hc : InS S c := hW c List.mem_cons_self
    obtain ⟨h1, h2⟩ := invBAux_pext k D W (i + 1) (fun P hP ↦ hW P (List.mem_cons_of_mem _ hP))
    obtain ⟨h3, h4⟩ := reflectC_pext (g := g) (D - k * i) c hc
    refine ⟨fun P hP ↦ ?_, ?_⟩
    · simp only [invBAux, List.mem_cons] at hP
      rcases hP with rfl | hP
      · exact h3
      · exact h1 P hP
    · simp only [invBAux, List.map_cons]
      rw [h4, h2]

lemma invB_pext (W : List (List F)) (k D : ℕ) (hW : InSB S W) :
    InSB S (invB W k D) ∧ (invB W k D).map (·.map (pext S g)) = invB (W.map (·.map (pext S g))) k D :=
  invBAux_pext k D W 0 hW

lemma shiftB_pext (W : List (List F)) {e : F} (he : e ∈ S) (hW : InSB S W) :
    InSB S (shiftB W e) ∧ (shiftB W e).map (·.map (pext S g)) = shiftB (W.map (·.map (pext S g))) (pext S g e) := by
  obtain ⟨hs, hs'⟩ := shiftC_pext (g := g) he 1
  refine ⟨fun P hP ↦ ?_, ?_⟩
  · simp only [shiftB, List.mem_map] at hP
    obtain ⟨c, hc, rfl⟩ := hP
    exact (compC_pext (g := g) _ hs c (hW c hc)).1
  · simp only [shiftB, List.map_map]
    refine List.map_congr_left fun c hc ↦ ?_
    simp only [Function.comp_apply]
    rw [(compC_pext (g := g) _ hs c (hW c hc)).2, hs']

lemma sum_pext {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ∈ S) :
    (∑ i ∈ s, f i) ∈ S ∧ pext S g (∑ i ∈ s, f i) = ∑ i ∈ s, pext S g (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S.zero_mem, by simp [pext_zero]⟩
  | insert j s hj ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    have hj' := hf j (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact ⟨S.add_mem hj' h1, by rw [pext_add hj' h1, h2]⟩

/-- **Truncated division reduces** when the constant term is a unit of `S`. -/
lemma divTrunc_pext (W U : List F) (hW : InS S W) (hU : InS S U) (hu0 : U.getD 0 0 ≠ 0)
    (hui : (U.getD 0 0)⁻¹ ∈ S) : ∀ m, InS S (divTrunc W U m) ∧
      (divTrunc W U m).map (pext S g) = divTrunc (W.map (pext S g)) (U.map (pext S g)) m
  | 0 => ⟨InS.nil, rfl⟩
  | m + 1 => by
    obtain ⟨h1, h2⟩ := divTrunc_pext W U hW hU hu0 hui m
    have hsum := sum_pext (g := g) (Finset.range m)
      (fun i ↦ U.getD (m - i) 0 * (divTrunc W U m).getD i 0)
      (fun i _ ↦ S.mul_mem (hU.getD _) (h1.getD _))
    have hnum : W.getD m 0 - ∑ i ∈ Finset.range m, U.getD (m - i) 0 * (divTrunc W U m).getD i 0 ∈ S :=
      S.sub_mem (hW.getD m) hsum.1
    have hq : (W.getD m 0 - ∑ i ∈ Finset.range m, U.getD (m - i) 0 * (divTrunc W U m).getD i 0) /
        U.getD 0 0 ∈ S := by
      rw [div_eq_mul_inv]; exact S.mul_mem hnum hui
    refine ⟨fun c hc ↦ ?_, ?_⟩
    · simp only [divTrunc, List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact h1 c hc
      · exact hq
    · simp only [divTrunc, List.map_append, List.map_cons, List.map_nil]
      rw [h2]
      congr 2
      rw [pext_div hnum (hU.getD 0) hui hu0, pext_sub (hW.getD m) hsum.1, hsum.2, getD_pext,
        getD_pext]
      congr 2
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [pext_mul (hU.getD _) (h1.getD _), getD_pext, ← h2, getD_pext]

/-- **Left-inverse certificates reduce.** -/
lemma leftInvCheck_pext {Lm : List (List F)} {M : ℕ → ℕ → F} {R n : ℕ} (hL : InSB S Lm)
    (hM : ∀ r j, M r j ∈ S) (h : leftInvCheck Lm M R n = true) :
    leftInvCheck (Lm.map (·.map (pext S g))) (fun r j ↦ pext S g (M r j)) R n = true := by
  simp only [leftInvCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h ⊢
  intro i hi j hj
  have hLi : InS S (Lm.getD i []) := by
    by_cases hi' : i < Lm.length
    · rw [List.getD_eq_getElem _ _ hi']; exact hL _ (List.getElem_mem hi')
    · rw [List.getD_eq_default _ _ (by omega)]; exact InS.nil
  have hs := sum_pext (g := g) (Finset.range R) (fun r ↦ (Lm.getD i []).getD r 0 * M r j)
    (fun r _ ↦ S.mul_mem (hLi.getD r) (hM r j))
  have e := congrArg (pext S g) (h i hi j hj)
  rw [hs.2] at e
  rw [show ([] : List F') = ([] : List F).map (pext S g) from rfl, List.getD_map]
  simp only [getD_pext]
  convert e using 1
  · exact Finset.sum_congr rfl fun r _ ↦ (pext_mul (hLi.getD r) (hM r j)).symm
  · split_ifs <;> simp [pext_one, pext_zero]

end Ops3

section Basis

variable {F F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F']
  {S : Subring F} {g : S →+* F'}

lemma pext_ne_zero_of_inv {u : F} (hu : u ∈ S) (hui : u⁻¹ ∈ S) (h0 : u ≠ 0) : pext S g u ≠ 0 := by
  intro h
  have := pext_mul (g := g) hu hui
  rw [mul_inv_cancel₀ h0, pext_one, h, zero_mul] at this
  exact one_ne_zero this

lemma drop_pext (l : List F) (m : ℕ) : (l.drop m).map (pext S g) = (l.map (pext S g)).drop m := by
  simp [List.map_drop]

lemma InS.drop {l : List F} (h : InS S l) (m : ℕ) : InS S (l.drop m) := fun c hc ↦
  h c (List.mem_of_mem_drop hc)

/-- The unit condition of the basis check at a point. -/
def UnitAt (Dc : List F) (a : F) (N : ℕ) : Prop :=
  ((compC Dc (shiftC a N)).getD (muD Dc a N) 0)⁻¹ ∈ S

lemma muD_pext {Dc : List F} {a : F} {N : ℕ} (hD : InS S Dc) (ha : a ∈ S)
    (hlt : muD Dc a N < (compC Dc (shiftC a N)).length) (hu : UnitAt (S := S) Dc a N) :
    muD (Dc.map (pext S g)) (pext S g a) N = muD Dc a N ∧
      (compC (Dc.map (pext S g)) (shiftC (pext S g a) N)) =
        (compC Dc (shiftC a N)).map (pext S g) ∧ InS S (compC Dc (shiftC a N)) := by
  obtain ⟨hs, hs'⟩ := shiftC_pext (g := g) ha N
  obtain ⟨hc, hc'⟩ := compC_pext (g := g) _ hs Dc hD
  have e : compC (Dc.map (pext S g)) (shiftC (pext S g a) N) = (compC Dc (shiftC a N)).map (pext S g) := by
    rw [hc', hs']
  refine ⟨?_, e, hc⟩
  rw [muD, e, ordC_pext _ hc fun _ ↦ pext_ne_zero_of_inv (hc.getD _) hu (getD_ordC _ hlt)]
  rfl

/-- **Truncated expansions of the basis at a point reduce.** -/
lemma serTrunc_pext {B : List (List F)} {Dc : List F} {a : F} {N prec : ℕ} {yt : List F}
    (hB : InSB S B) (hD : InS S Dc) (ha : a ∈ S) (hy : InS S yt)
    (hlt : muD Dc a N < (compC Dc (shiftC a N)).length) (hu : UnitAt (S := S) Dc a N) :
    InS S (serTrunc B Dc a N prec yt) ∧
      (serTrunc B Dc a N prec yt).map (pext S g) =
        serTrunc (B.map (·.map (pext S g))) (Dc.map (pext S g)) (pext S g a) N prec (yt.map (pext S g)) := by
  obtain ⟨hmu, hce, hcS⟩ := muD_pext (g := g) hD ha hlt hu
  obtain ⟨hs, hs'⟩ := shiftC_pext (g := g) ha N
  obtain ⟨hbv, hbv'⟩ := bivEval_pext (g := g) _ _ hs hy B hB
  have hU : InS S ((compC Dc (shiftC a N)).drop (muD Dc a N)) := hcS.drop _
  have hU0 : ((compC Dc (shiftC a N)).drop (muD Dc a N)).getD 0 0 ≠ 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, add_zero, ← List.getD_eq_getElem?_getD]
    exact getD_ordC _ hlt
  have hU0i : (((compC Dc (shiftC a N)).drop (muD Dc a N)).getD 0 0)⁻¹ ∈ S := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, add_zero, ← List.getD_eq_getElem?_getD]
    exact hu
  obtain ⟨h1, h2⟩ := divTrunc_pext (g := g) _ _ hbv hU hU0 hU0i prec
  refine ⟨h1, ?_⟩
  rw [serTrunc, h2, hbv', hs', drop_pext, ← hce, serTrunc, hmu]

end Basis

section BasisCheck

variable {F F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F']
  {S : Subring F} {g : S →+* F'}

lemma getD_mapLL {α β : Type*} (f : α → β) (L : List (List α)) (j : ℕ) :
    (L.map (·.map f)).getD j [] = (L.getD j []).map f := by
  rw [show ([] : List β) = ([] : List α).map f from rfl, List.getD_map]

lemma getD_mapLLL {α β : Type*} (f : α → β) (L : List (List (List α))) (j : ℕ) :
    (L.map (·.map (·.map f))).getD j [] = (L.getD j []).map (·.map f) := by
  rw [show ([] : List (List β)) = ([] : List (List α)).map (·.map f) from rfl, List.getD_map]

lemma InSB.getD {L : List (List F)} (h : InSB S L) (j : ℕ) : InS S (L.getD j []) := by
  by_cases hj : j < L.length
  · rw [List.getD_eq_getElem _ _ hj]; exact h _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]; exact InS.nil

lemma InSBB.getD {L : List (List (List F))} (h : ∀ W ∈ L, InSB S W) (j : ℕ) : InSB S (L.getD j []) := by
  by_cases hj : j < L.length
  · rw [List.getD_eq_getElem _ _ hj]; exact h _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]; exact fun _ h ↦ by simp at h

/-- **The basis check at a point reduces.** -/
lemma basisCheckAt_pext {n : ℕ} {Bc : List (List (List F))} {Dc : List F} {a : F} {c : BranchCert F}
    {Lm : List (List F)} (hB : ∀ W ∈ Bc, InSB S W) (hD : InS S Dc) (ha : a ∈ S) (hys : InSB S c.ys)
    (hL : InSB S Lm) (hu : UnitAt (S := S) Dc a c.N) (h : basisCheckAt n Bc Dc a c Lm = true) :
    basisCheckAt n (Bc.map (·.map (·.map (pext S g)))) (Dc.map (pext S g)) (pext S g a)
      ⟨c.N, c.ys.map (·.map (pext S g)), c.prec⟩ (Lm.map (·.map (pext S g))) = true := by
  simp only [basisCheckAt, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h ⊢
  obtain ⟨⟨⟨hlt, hle⟩, hz⟩, hinv⟩ := h
  obtain ⟨hmu, hce, hcS⟩ := muD_pext (g := g) hD ha hlt hu
  have hser : ∀ j k, InS S (serTrunc (Bc.getD j []) Dc a c.N c.prec (c.ys.getD k [])) ∧
      (serTrunc (Bc.getD j []) Dc a c.N c.prec (c.ys.getD k [])).map (pext S g) =
      serTrunc ((Bc.map (·.map (·.map (pext S g)))).getD j []) (Dc.map (pext S g)) (pext S g a) c.N
        c.prec ((c.ys.map (·.map (pext S g))).getD k []) := fun j k ↦ by
    rw [getD_mapLLL, getD_mapLL]
    exact serTrunc_pext (InSBB.getD hB j) hD ha (hys.getD k) hlt hu
  refine ⟨⟨⟨by rw [hmu, hce, List.length_map]; exact hlt, by rw [hmu]; exact hle⟩, fun j hj k hk t ht ↦ ?_⟩, ?_⟩
  · rw [hmu] at ht
    rw [← (hser j k).2, getD_pext, hz j hj k hk t ht, pext_zero]
  · have hM : ∀ r j, matEntry Bc Dc a c r j ∈ S := fun r j ↦ (hser j (r / c.N)).1.getD _
    have e : ∀ r j, matEntry (Bc.map (·.map (·.map (pext S g)))) (Dc.map (pext S g)) (pext S g a)
        ⟨c.N, c.ys.map (·.map (pext S g)), c.prec⟩ r j = pext S g (matEntry Bc Dc a c r j) := by
      intro r j
      simp only [matEntry]
      rw [hmu, ← (hser j (r / c.N)).2, getD_pext]
    have := leftInvCheck_pext (g := g) hL hM hinv
    simp only [leftInvCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at this ⊢
    intro i hi j hj
    rw [← this i hi j hj]
    exact Finset.sum_congr rfl fun r _ ↦ by rw [e]

end BasisCheck

section InfCheck

variable {F F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F']
  {S : Subring F} {g : S →+* F'}

lemma synDelta_map {α β : Type*} [Field α] [DecidableEq α] [Field β] [DecidableEq β] (f : α → β)
    (k : ℕ) (Dc : List α) (B : List (List α)) :
    synDelta k (Dc.map f) (B.map (·.map f)) = synDelta k Dc B := by
  simp only [synDelta, List.length_map]
  congr 1
  funext i m
  rw [getD_mapLL, List.length_map]

lemma invOKb_map {α β : Type*} [Field α] [DecidableEq α] [Field β] [DecidableEq β] (f : α → β)
    (k D : ℕ) (W : List (List α)) : invOKb k D (W.map (·.map f)) = invOKb k D W := by
  simp only [invOKb, List.length_map, getD_mapLL]

/-- The expansions above infinity reduce. -/
lemma serInf_pext {B : List (List F)} {Dc : List F} {k δ N prec : ℕ} {wt : List F}
    (hB : InSB S B) (hD : InS S Dc) (hw : InS S wt)
    (hU0 : (compC (reflectC (Dc.length - 1) Dc) (shiftC 0 N)).getD 0 0 ≠ 0)
    (hUi : ((compC (reflectC (Dc.length - 1) Dc) (shiftC 0 N)).getD 0 0)⁻¹ ∈ S) :
    InS S (serInf B Dc k δ N prec wt) ∧
      (serInf B Dc k δ N prec wt).map (pext S g) =
        serInf (B.map (·.map (pext S g))) (Dc.map (pext S g)) k δ N prec (wt.map (pext S g)) := by
  obtain ⟨hs, hs'⟩ := shiftC_pext (g := g) S.zero_mem N
  rw [pext_zero] at hs'
  obtain ⟨hI, hI'⟩ := invB_pext (g := g) B k (δ + (Dc.length - 1)) hB
  obtain ⟨hbv, hbv'⟩ := bivEval_pext (g := g) _ _ hs hw _ hI
  obtain ⟨hr, hr'⟩ := reflectC_pext (g := g) (Dc.length - 1) Dc hD
  obtain ⟨hc, hc'⟩ := compC_pext (g := g) _ hs _ hr
  obtain ⟨h1, h2⟩ := divTrunc_pext (g := g) _ _ hbv hc hU0 hUi prec
  refine ⟨h1, ?_⟩
  rw [serInf, h2, hbv', hI', hc', hr', hs', serInf, List.length_map]

/-- **The basis check above infinity reduces.** -/
lemma basisCheckInfS_pext {n k : ℕ} {Bc : List (List (List F))} {Dc : List F} {δ : List ℕ}
    {c : BranchCert F} {Lm : List (List F)} (hB : ∀ W ∈ Bc, InSB S W) (hD : InS S Dc)
    (hys : InSB S c.ys) (hL : InSB S Lm) (hlast : (Dc.getD (Dc.length - 1) 0)⁻¹ ∈ S)
    (hU0 : (compC (reflectC (Dc.length - 1) Dc) (shiftC 0 c.N)).getD 0 0 ≠ 0)
    (hUi : ((compC (reflectC (Dc.length - 1) Dc) (shiftC 0 c.N)).getD 0 0)⁻¹ ∈ S)
    (h : basisCheckInfS n k Bc Dc δ c Lm = true) :
    basisCheckInfS n k (Bc.map (·.map (·.map (pext S g)))) (Dc.map (pext S g)) δ
      ⟨c.N, c.ys.map (·.map (pext S g)), c.prec⟩ (Lm.map (·.map (pext S g))) = true := by
  simp only [basisCheckInfS, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h ⊢
  obtain ⟨⟨⟨hpos, hne⟩, hj⟩, hinv⟩ := h
  have hser : ∀ j m, InS S (serInf (Bc.getD j []) Dc k (synDelta k Dc (Bc.getD j [])) c.N c.prec
      (c.ys.getD m [])) ∧ (serInf (Bc.getD j []) Dc k (synDelta k Dc (Bc.getD j [])) c.N c.prec
        (c.ys.getD m [])).map (pext S g) =
      serInf ((Bc.map (·.map (·.map (pext S g)))).getD j []) (Dc.map (pext S g)) k
        (synDelta k (Dc.map (pext S g)) ((Bc.map (·.map (·.map (pext S g)))).getD j [])) c.N c.prec
        ((c.ys.map (·.map (pext S g))).getD m []) := fun j m ↦ by
    rw [getD_mapLLL, getD_mapLL, synDelta_map]
    exact serInf_pext (InSBB.getD hB j) hD (hys.getD m) hU0 hUi
  refine ⟨⟨⟨by rwa [List.length_map], ?_⟩, fun j hjn ↦ ?_⟩, ?_⟩
  · rw [List.length_map, getD_pext]
    exact pext_ne_zero_of_inv (hD.getD _) hlast hne
  · obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hj j hjn
    rw [getD_mapLLL, synDelta_map, invOKb_map, List.length_map]
    refine ⟨⟨⟨h1, h2⟩, h3⟩, fun m hm t ht ↦ ?_⟩
    have := (hser j m).2
    rw [getD_mapLLL, getD_mapLL, synDelta_map] at this
    rw [getD_mapLL, ← this, getD_pext, h4 m hm t ht, pext_zero]
  · have hM : ∀ r j, matInfS Bc Dc k δ c r j ∈ S := fun r j ↦ (hser j (r / c.N)).1.getD _
    have e : ∀ r j, matInfS (Bc.map (·.map (·.map (pext S g)))) (Dc.map (pext S g)) k δ
        ⟨c.N, c.ys.map (·.map (pext S g)), c.prec⟩ r j = pext S g (matInfS Bc Dc k δ c r j) := by
      intro r j
      simp only [matInfS]
      rw [← (hser j (r / c.N)).2, getD_pext, getD_mapLLL, synDelta_map]
    have := leftInvCheck_pext (g := g) hL hM hinv
    simp only [leftInvCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at this ⊢
    intro i hi j hj'
    rw [← this i hi j hj']
    exact Finset.sum_congr rfl fun r _ ↦ by rw [e]

end InfCheck

end Curves
