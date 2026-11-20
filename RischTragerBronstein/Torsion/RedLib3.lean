import RischTragerBronstein.Torsion.RedLib2

/-!
# Reduction of list computations (3): zero tests, the cover check

Zero tests are preserved when every tested value is either `0` or a unit of `S` (`ZP`):

* `trim_pext`, `isZero_pext`, `degT_pext`;
* `synthDiv_pext`, `stripAt_pext`; **`coverCheck_pext`** (the tested values are collected by
  `coverVals`).
-/

open Polynomial

namespace Curves

open CPoly Sup

section Zero

variable {F F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F']
  {S : Subring F} {g : S →+* F'}

variable (S) in
/-- A value whose zero test survives the reduction. -/
def ZP (v : F) : Prop := v = 0 ∨ (v ∈ S ∧ v⁻¹ ∈ S)

lemma pext_eq_zero_iff {v : F} (hv : ZP S v) : pext S g v = 0 ↔ v = 0 := by
  rcases hv with rfl | ⟨h1, h2⟩
  · simp [pext_zero]
  · by_cases h0 : v = 0
    · simp [h0, pext_zero]
    · simp only [h0, iff_false]; exact pext_ne_zero_of_inv h1 h2 h0

lemma isZero_pext : ∀ (l : List F), (∀ v ∈ l, ZP S v) → isZero (l.map (pext S g)) = isZero l
  | [], _ => rfl
  | a :: l, hl => by
    have ha := pext_eq_zero_iff (g := g) (hl a List.mem_cons_self)
    have ih := isZero_pext l (fun v hv ↦ hl v (List.mem_cons_of_mem _ hv))
    simp only [isZero, List.map_cons, List.all_cons] at ih ⊢
    rw [ih]
    congr 1
    simp [ha]

lemma dropWhile_pext : ∀ (l : List F), (∀ v ∈ l, ZP S v) →
    (l.map (pext S g)).dropWhile (· = 0) = (l.dropWhile (· = 0)).map (pext S g)
  | [], _ => rfl
  | a :: l, hl => by
    have ha := pext_eq_zero_iff (g := g) (hl a List.mem_cons_self)
    by_cases h0 : a = 0
    · rw [List.map_cons, List.dropWhile_cons_of_pos (by simpa using ha.mpr h0),
        List.dropWhile_cons_of_pos (by simpa using h0)]
      exact dropWhile_pext l fun v hv ↦ hl v (List.mem_cons_of_mem _ hv)
    · rw [List.map_cons, List.dropWhile_cons_of_neg (by simpa using fun h ↦ h0 (ha.mp h)),
        List.dropWhile_cons_of_neg (by simpa using h0)]
      rfl

lemma trim_pext (l : List F) (hl : ∀ v ∈ l, ZP S v) :
    trim (l.map (pext S g)) = (trim l).map (pext S g) := by
  simp only [trim, List.map_reverse]
  rw [← List.map_reverse, dropWhile_pext _ (fun v hv ↦ hl v (List.mem_reverse.mp hv))]

lemma degT_pext (l : List F) (hl : ∀ v ∈ l, ZP S v) : degT (l.map (pext S g)) = degT l := by
  rw [degT, trim_pext l hl, List.length_map, degT]

/-! ### Synthetic division and the cover check -/

lemma synthDiv_pext {a : F} (ha : a ∈ S) : ∀ (P : List F), InS S P →
    InS S (synthDiv a P).1 ∧ (synthDiv a P).2 ∈ S ∧
      (synthDiv a P).1.map (pext S g) = (synthDiv (pext S g a) (P.map (pext S g))).1 ∧
      pext S g (synthDiv a P).2 = (synthDiv (pext S g a) (P.map (pext S g))).2
  | [], _ => ⟨InS.nil, S.zero_mem, rfl, by simp [synthDiv, pext_zero]⟩
  | c :: P, hP => by
    obtain ⟨hc, hP'⟩ := hP.of_cons
    obtain ⟨h1, h2, h3, h4⟩ := synthDiv_pext ha P hP'
    refine ⟨InS.cons h2 h1, S.add_mem hc (S.mul_mem ha h2), ?_, ?_⟩
    · simp only [synthDiv, List.map_cons]
      rw [h3, h4]
    · simp only [synthDiv, List.map_cons]
      rw [pext_add hc (S.mul_mem ha h2), pext_mul ha h2, h4]

/-- The values tested by `stripAt`. -/
def stripVals (a : F) : ℕ → List F → List F
  | 0, _ => []
  | fuel + 1, P => (synthDiv a P).2 :: (if (synthDiv a P).2 = 0 then stripVals a fuel (synthDiv a P).1 else [])

lemma stripAt_pext {a : F} (ha : a ∈ S) : ∀ (fuel : ℕ) (P : List F), InS S P →
    (∀ v ∈ stripVals a fuel P, ZP S v) →
    InS S (stripAt a fuel P) ∧ (stripAt a fuel P).map (pext S g) = stripAt (pext S g a) fuel (P.map (pext S g))
  | 0, P, hP, _ => ⟨hP, rfl⟩
  | fuel + 1, P, hP, hZ => by
    obtain ⟨h1, h2, h3, h4⟩ := synthDiv_pext (g := g) ha P hP
    have hr := pext_eq_zero_iff (g := g) (hZ _ List.mem_cons_self)
    by_cases h0 : (synthDiv a P).2 = 0
    · have hZ' : ∀ v ∈ stripVals a fuel (synthDiv a P).1, ZP S v := fun v hv ↦
        hZ v (List.mem_cons_of_mem _ (by rw [if_pos h0]; exact hv))
      obtain ⟨h5, h6⟩ := stripAt_pext ha fuel _ h1 hZ'
      refine ⟨by simp only [stripAt, if_pos h0]; exact h5, ?_⟩
      simp only [stripAt, if_pos h0]
      rw [h6, h3, if_pos (by rw [← h4]; exact hr.mpr h0)]
    · refine ⟨by simp only [stripAt, if_neg h0]; exact hP, ?_⟩
      simp only [stripAt, if_neg h0]
      rw [if_neg (by rw [← h4]; exact fun h ↦ h0 (hr.mp h))]

/-- The values tested by the cover check (the remainders and the final coefficients). -/
def coverVals : List F → List F → List F
  | P, [] => P
  | P, a :: as => stripVals a P.length P ++ coverVals (stripAt a P.length P) as

lemma foldl_strip_pext : ∀ (as : List F) (P : List F), InS S P → (∀ a ∈ as, a ∈ S) →
    (∀ v ∈ coverVals P as, ZP S v) →
    InS S (as.foldl (fun Q a ↦ stripAt a Q.length Q) P) ∧
      (as.foldl (fun Q a ↦ stripAt a Q.length Q) P).map (pext S g) =
        (as.map (pext S g)).foldl (fun Q a ↦ stripAt a Q.length Q) (P.map (pext S g)) ∧
      (∀ v ∈ as.foldl (fun Q a ↦ stripAt a Q.length Q) P, ZP S v)
  | [], P, hP, _, hZ => ⟨hP, rfl, hZ⟩
  | a :: as, P, hP, has, hZ => by
    have hZ1 : ∀ v ∈ stripVals a P.length P, ZP S v := fun v hv ↦
      hZ v (List.mem_append_left _ hv)
    have hZ2 : ∀ v ∈ coverVals (stripAt a P.length P) as, ZP S v := fun v hv ↦
      hZ v (List.mem_append_right _ hv)
    obtain ⟨h1, h2⟩ := stripAt_pext (g := g) (has a List.mem_cons_self) P.length P hP hZ1
    obtain ⟨h3, h4, h5⟩ := foldl_strip_pext as _ h1 (fun b hb ↦ has b (List.mem_cons_of_mem _ hb)) hZ2
    refine ⟨h3, ?_, h5⟩
    simp only [List.foldl_cons, List.map_cons]
    rw [h4, h2, List.length_map]

/-- **The cover check reduces.** -/
lemma coverCheck_pext {P : List F} {as : List F} (hP : InS S P) (has : ∀ a ∈ as, a ∈ S)
    (hZ : ∀ v ∈ coverVals P as, ZP S v) (h : coverCheck P as = true) :
    coverCheck (P.map (pext S g)) (as.map (pext S g)) = true := by
  obtain ⟨-, h2, h3⟩ := foldl_strip_pext (g := g) as P hP has hZ
  simp only [coverCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h ⊢
  rw [← h2, degT_pext _ h3, isZero_pext _ h3]
  exact h

end Zero

section IB

variable {F F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F']
  {S : Subring F} {g : S →+* F'}

/-- **The shape check reduces.** -/
lemma shapeCheck_pext {Fc : List (List F)} {n k : ℕ} (hF : InSB S Fc) (h : shapeCheck Fc n k = true) :
    shapeCheck (Fc.map (·.map (pext S g))) n k = true := by
  obtain ⟨hI, hI'⟩ := invB_pext (g := g) Fc k (k * n) hF
  simp only [shapeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    List.length_map] at h ⊢
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨⟨⟨⟨⟨h1, h2⟩, ?_⟩, by rw [← hI', List.length_map]; exact h4⟩, ?_⟩, fun j hj ↦ ?_⟩
  · rw [getD_mapLL, h3]; simp [pext_one]
  · rw [← hI', getD_mapLL, h5]; simp [pext_one]
  · rw [getD_mapLL, List.length_map]; exact h6 j hj

/-- Reduction of an integral-basis certificate. -/
noncomputable def IntBasisCert.mapP (f : F → F') (I : IntBasisCert F) : IntBasisCert F' :=
  ⟨I.Bc.map (·.map (·.map f)), I.Dc.map f, I.δL,
    I.pts.map fun q ↦ (f q.1, ⟨q.2.1.N, q.2.1.ys.map (·.map f), q.2.1.prec⟩, q.2.2.map (·.map f)),
    ⟨I.infc.N, I.infc.ys.map (·.map f), I.infc.prec⟩, I.Linf.map (·.map f)⟩

/-- **The integral-basis check reduces** (under the unit conditions). -/
theorem ibCheck_pext {Fc : List (List F)} {n k : ℕ} {I : IntBasisCert F} {G : List F}
    (hF : InSB S Fc) (hB : ∀ W ∈ I.Bc, InSB S W) (hD : InS S I.Dc) (hG : InS S G)
    (hDl : I.Dc.getLast? = some 1)
    (hpts : ∀ q ∈ I.pts, q.1 ∈ S ∧ InSB S q.2.1.ys ∧ InSB S q.2.2 ∧
      (∀ y ∈ q.2.1.ys, OrdUnit S g (bivEvalT (derivYB Fc) (shiftC q.1 q.2.1.N) y q.2.1.prec)) ∧
      SepUnit (S := S) (g := g) q.2.1.ys q.2.1.prec ∧ UnitAt (S := S) I.Dc q.1 q.2.1.N)
    (hinf : InSB S I.infc.ys ∧ InSB S I.Linf ∧
      (∀ y ∈ I.infc.ys, OrdUnit S g (bivEvalT (derivYB (invB Fc k (k * n))) (shiftC 0 I.infc.N) y
        I.infc.prec)) ∧ SepUnit (S := S) (g := g) I.infc.ys I.infc.prec)
    (hlast : (I.Dc.getD (I.Dc.length - 1) 0)⁻¹ ∈ S)
    (hU0 : (compC (reflectC (I.Dc.length - 1) I.Dc) (shiftC 0 I.infc.N)).getD 0 0 ≠ 0)
    (hUi : ((compC (reflectC (I.Dc.length - 1) I.Dc) (shiftC 0 I.infc.N)).getD 0 0)⁻¹ ∈ S)
    (hcov : ∀ v ∈ coverVals G (I.pts.map Prod.fst), ZP S v)
    (h : ibCheck Fc n k I G = true) :
    ibCheck (Fc.map (·.map (pext S g))) n k (I.mapP (pext S g)) (G.map (pext S g)) = true := by
  simp only [ibCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true'] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨hsh, hz⟩, hlen⟩, hp⟩, hc⟩, hci⟩, hbi⟩ := h
  refine ⟨⟨⟨⟨⟨⟨shapeCheck_pext hF hsh, ?_⟩, fun j hj ↦ ?_⟩, fun q hq ↦ ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- the denominator is not zero
    simp only [IntBasisCert.mapP]
    rw [isZero, List.all_eq_false]
    have hm : (1 : F) ∈ I.Dc := List.mem_of_getLast? hDl
    exact ⟨pext S g 1, List.mem_map_of_mem hm, by simp [pext_one]⟩
  · simp only [IntBasisCert.mapP]
    rw [getD_mapLLL, List.length_map]; exact hlen j hj
  · -- the special points
    simp only [IntBasisCert.mapP, List.mem_map] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    obtain ⟨hca, hbc⟩ := hp q0 hq0
    obtain ⟨ha, hys, hLm, hou, hsep, hun⟩ := hpts q0 hq0
    exact ⟨certCheck_pext hF ha hys hou hsep hca, basisCheckAt_pext hB hD ha hys hLm hun hbc⟩
  · simp only [IntBasisCert.mapP, List.map_map]
    have := coverCheck_pext (g := g) hG (fun a ha ↦ by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha; exact (hpts q hq).1) hcov hc
    rw [List.map_map] at this
    exact this
  · obtain ⟨hys, -, hou, hsep⟩ := hinf
    obtain ⟨hIn, hIn'⟩ := invB_pext (g := g) Fc k (k * n) hF
    have := certCheck_pext hIn S.zero_mem hys hou hsep hci
    rw [hIn', pext_zero] at this
    exact this
  · obtain ⟨hys, hLi, -, -⟩ := hinf
    exact basisCheckInfS_pext hB hD hys hLi hlast hU0 hUi hbi

end IB

end Curves
