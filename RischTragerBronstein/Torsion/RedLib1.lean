import RischTragerBronstein.Torsion.TorsOrdExist4

/-!
# Reduction of list computations (1): partial homomorphisms

A ring homomorphism `g : S →+* F'` on a subring `S ⊆ F` (the `p`-integral elements) extends to a map
`pext S g : F → F'` (zero off `S`). For lists with entries in `S`, the structural list operations
(`add`, `mul`, `compC`, `shiftC`, `xPowC`, `bivEval`, `bivEvalT`, `reflectC`, `derivYB`, …) commute
with `pext` (`map_add'`, `map_mul'`, …): every entry of the result lies in `S`, and reduction
entrywise gives the operation on the reduced lists.
-/

open Polynomial

namespace Curves

open CPoly Sup

section PExt

variable {F F' : Type*} [Field F] [Field F'] (S : Subring F) (g : S →+* F')

/-- The extension of `g` by zero. -/
noncomputable def pext (x : F) : F' := by
  classical
  exact if h : x ∈ S then g ⟨x, h⟩ else 0

variable {S g}

lemma pext_of_mem {x : F} (h : x ∈ S) : pext S g x = g ⟨x, h⟩ := by
  classical
  unfold pext; exact dif_pos h

lemma pext_zero : pext S g 0 = 0 := by rw [pext_of_mem S.zero_mem]; exact map_zero g

lemma pext_one : pext S g 1 = 1 := by rw [pext_of_mem S.one_mem]; exact map_one g

lemma pext_add {x y : F} (hx : x ∈ S) (hy : y ∈ S) : pext S g (x + y) = pext S g x + pext S g y := by
  rw [pext_of_mem (S.add_mem hx hy), pext_of_mem hx, pext_of_mem hy, ← map_add]; rfl

lemma pext_mul {x y : F} (hx : x ∈ S) (hy : y ∈ S) : pext S g (x * y) = pext S g x * pext S g y := by
  rw [pext_of_mem (S.mul_mem hx hy), pext_of_mem hx, pext_of_mem hy, ← map_mul]; rfl

lemma pext_neg {x : F} (hx : x ∈ S) : pext S g (-x) = -pext S g x := by
  rw [pext_of_mem (S.neg_mem hx), pext_of_mem hx, ← map_neg]; rfl

lemma pext_sub {x y : F} (hx : x ∈ S) (hy : y ∈ S) : pext S g (x - y) = pext S g x - pext S g y := by
  rw [sub_eq_add_neg, pext_add hx (S.neg_mem hy), pext_neg hy, ← sub_eq_add_neg]

lemma pext_natCast (n : ℕ) : pext S g (n : F) = n := by
  rw [pext_of_mem (natCast_mem S n)]
  exact map_natCast g n

lemma pext_inv {x : F} (hx : x ∈ S) (hxi : x⁻¹ ∈ S) (h0 : x ≠ 0) :
    pext S g x⁻¹ = (pext S g x)⁻¹ := by
  have h1 : pext S g x * pext S g x⁻¹ = 1 := by
    rw [← pext_mul hx hxi, mul_inv_cancel₀ h0, pext_one]
  exact eq_inv_of_mul_eq_one_right h1

lemma pext_div {x y : F} (hx : x ∈ S) (hy : y ∈ S) (hyi : y⁻¹ ∈ S) (h0 : y ≠ 0) :
    pext S g (x / y) = pext S g x / pext S g y := by
  rw [div_eq_mul_inv, pext_mul hx hyi, pext_inv hy hyi h0, div_eq_mul_inv]

variable (S)

/-- All entries of a list lie in `S`. -/
def InS (l : List F) : Prop := ∀ c ∈ l, c ∈ S

/-- All entries of a bivariate list lie in `S`. -/
def InSB (W : List (List F)) : Prop := ∀ P ∈ W, InS S P

variable {S}

lemma InS.nil : InS S ([] : List F) := fun _ h ↦ by simp at h

lemma InS.cons {a : F} {l : List F} (ha : a ∈ S) (hl : InS S l) : InS S (a :: l) := by
  intro c hc; rcases List.mem_cons.mp hc with rfl | hc
  · exact ha
  · exact hl c hc

lemma InS.of_cons {a : F} {l : List F} (h : InS S (a :: l)) : a ∈ S ∧ InS S l :=
  ⟨h a List.mem_cons_self, fun c hc ↦ h c (List.mem_cons_of_mem _ hc)⟩

lemma InS.getD {l : List F} (h : InS S l) (i : ℕ) : l.getD i 0 ∈ S := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; exact S.zero_mem

lemma getD_pext {l : List F} (i : ℕ) : (l.map (pext S g)).getD i 0 = pext S g (l.getD i 0) := by
  rw [← pext_zero (S := S) (g := g), List.getD_map]

/-! ### Addition, scalar multiplication, multiplication -/

lemma add_pext : ∀ (p q : List F), InS S p → InS S q →
    InS S (add p q) ∧ (add p q).map (pext S g) = add (p.map (pext S g)) (q.map (pext S g))
  | [], q, _, hq => ⟨hq, rfl⟩
  | a :: p, [], hp, _ => ⟨hp, rfl⟩
  | a :: p, b :: q, hp, hq => by
    obtain ⟨ha, hp'⟩ := hp.of_cons
    obtain ⟨hb, hq'⟩ := hq.of_cons
    obtain ⟨h1, h2⟩ := add_pext p q hp' hq'
    refine ⟨InS.cons (S.add_mem ha hb) h1, ?_⟩
    simp only [add, List.map_cons, h2, pext_add ha hb]

lemma smul_pext {c : F} (hc : c ∈ S) : ∀ (p : List F), InS S p →
    InS S (smul c p) ∧ (smul c p).map (pext S g) = smul (pext S g c) (p.map (pext S g))
  | [], _ => ⟨InS.nil, rfl⟩
  | a :: p, hp => by
    obtain ⟨ha, hp'⟩ := hp.of_cons
    obtain ⟨h1, h2⟩ := smul_pext hc p hp'
    refine ⟨InS.cons (S.mul_mem hc ha) h1, ?_⟩
    simp only [smul, List.map_cons, List.map_map] at h2 ⊢
    rw [pext_mul hc ha]
    congr 1

lemma mul_pext : ∀ (p q : List F), InS S p → InS S q →
    InS S (mul p q) ∧ (mul p q).map (pext S g) = mul (p.map (pext S g)) (q.map (pext S g))
  | [], q, _, _ => ⟨InS.nil, rfl⟩
  | a :: p, q, hp, hq => by
    obtain ⟨ha, hp'⟩ := hp.of_cons
    obtain ⟨h1, h2⟩ := mul_pext p q hp' hq
    obtain ⟨h3, h4⟩ := smul_pext (g := g) ha q hq
    obtain ⟨h5, h6⟩ := add_pext (g := g) (smul a q) (0 :: mul p q) h3 (InS.cons S.zero_mem h1)
    refine ⟨h5, ?_⟩
    simp only [mul, List.map_cons]
    rw [h6, h4, List.map_cons, h2, pext_zero]

end PExt

section Ops2

variable {F F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F']
  {S : Subring F} {g : S →+* F'}

lemma compC_pext (s : List F) (hs : InS S s) : ∀ (c : List F), InS S c →
    InS S (compC c s) ∧ (compC c s).map (pext S g) = compC (c.map (pext S g)) (s.map (pext S g))
  | [], _ => ⟨InS.nil, rfl⟩
  | a :: c, hc => by
    obtain ⟨ha, hc'⟩ := hc.of_cons
    obtain ⟨h1, h2⟩ := compC_pext s hs c hc'
    obtain ⟨h3, h4⟩ := mul_pext (g := g) (compC c s) s h1 hs
    obtain ⟨h5, h6⟩ := add_pext (g := g) [a] (mul (compC c s) s) (InS.cons ha InS.nil) h3
    refine ⟨h5, ?_⟩
    simp only [compC, List.foldr_cons] at h5 h6 ⊢
    rw [h6, List.map_cons, List.map_nil]
    congr 1
    simp only [compC] at h4 h2
    rw [h4, h2]

lemma xPowC_pext (N : ℕ) : InS S (xPowC N : List F) ∧
    (xPowC N : List F).map (pext S g) = xPowC N := by
  refine ⟨fun c hc ↦ ?_, ?_⟩
  · simp only [xPowC, List.mem_append, List.mem_replicate, List.mem_singleton] at hc
    rcases hc with ⟨-, rfl⟩ | rfl
    · exact S.zero_mem
    · exact S.one_mem
  · simp [xPowC, List.map_replicate, pext_zero, pext_one]

lemma shiftC_pext {a : F} (ha : a ∈ S) (N : ℕ) : InS S (shiftC a N) ∧
    (shiftC a N).map (pext S g) = shiftC (pext S g a) N := by
  obtain ⟨h1, h2⟩ := xPowC_pext (S := S) (g := g) N
  obtain ⟨h3, h4⟩ := add_pext (g := g) [a] (xPowC N) (InS.cons ha InS.nil) h1
  exact ⟨h3, by rw [shiftC, h4, h2]; rfl⟩

lemma bivEval_pext (s Y : List F) (hs : InS S s) (hY : InS S Y) : ∀ (W : List (List F)), InSB S W →
    InS S (bivEval W s Y) ∧
      (bivEval W s Y).map (pext S g) = bivEval (W.map (·.map (pext S g))) (s.map (pext S g)) (Y.map (pext S g))
  | [], _ => ⟨InS.nil, rfl⟩
  | c :: W, hW => by
    have hc : InS S c := hW c List.mem_cons_self
    have hW' : InSB S W := fun P hP ↦ hW P (List.mem_cons_of_mem _ hP)
    obtain ⟨h1, h2⟩ := bivEval_pext s Y hs hY W hW'
    obtain ⟨h3, h4⟩ := compC_pext (g := g) s hs c hc
    obtain ⟨h5, h6⟩ := mul_pext (g := g) Y (bivEval W s Y) hY h1
    obtain ⟨h7, h8⟩ := add_pext (g := g) (compC c s) (mul Y (bivEval W s Y)) h3 h5
    have e : bivEval (c :: W) s Y = add (compC c s) (mul Y (bivEval W s Y)) := rfl
    refine ⟨by rw [e]; exact h7, ?_⟩
    rw [e, h8, h4, h6, h2]
    rfl

lemma take_pext (l : List F) (K : ℕ) : (l.take K).map (pext S g) = (l.map (pext S g)).take K := by
  simp [List.map_take]

lemma InS.take {l : List F} (h : InS S l) (K : ℕ) : InS S (l.take K) := fun c hc ↦
  h c (List.mem_of_mem_take hc)

lemma bivEvalT_pext (s Y : List F) (hs : InS S s) (hY : InS S Y) (K : ℕ) : ∀ (W : List (List F)),
    InSB S W → InS S (bivEvalT W s Y K) ∧
      (bivEvalT W s Y K).map (pext S g) =
        bivEvalT (W.map (·.map (pext S g))) (s.map (pext S g)) (Y.map (pext S g)) K
  | [], _ => ⟨InS.nil, rfl⟩
  | c :: W, hW => by
    have hc : InS S c := hW c List.mem_cons_self
    have hW' : InSB S W := fun P hP ↦ hW P (List.mem_cons_of_mem _ hP)
    obtain ⟨h1, h2⟩ := bivEvalT_pext s Y hs hY K W hW'
    obtain ⟨h3, h4⟩ := compC_pext (g := g) s hs c hc
    obtain ⟨h5, h6⟩ := mul_pext (g := g) Y (bivEvalT W s Y K) hY h1
    obtain ⟨h7, h8⟩ := add_pext (g := g) (compC c s) (mul Y (bivEvalT W s Y K)) h3 h5
    have e : bivEvalT (c :: W) s Y K = (add (compC c s) (mul Y (bivEvalT W s Y K))).take K := rfl
    refine ⟨by rw [e]; exact h7.take K, ?_⟩
    rw [e, take_pext, h8, h4, h6, h2]
    rfl

lemma addB_pext : ∀ (W V : List (List F)), InSB S W → InSB S V →
    InSB S (addB W V) ∧ (addB W V).map (·.map (pext S g)) =
      addB (W.map (·.map (pext S g))) (V.map (·.map (pext S g)))
  | [], V, _, hV => ⟨hV, rfl⟩
  | a :: W, [], hW, _ => ⟨hW, rfl⟩
  | a :: W, b :: V, hW, hV => by
    have ha : InS S a := hW a List.mem_cons_self
    have hb : InS S b := hV b List.mem_cons_self
    obtain ⟨h1, h2⟩ := addB_pext W V (fun P hP ↦ hW P (List.mem_cons_of_mem _ hP))
      (fun P hP ↦ hV P (List.mem_cons_of_mem _ hP))
    obtain ⟨h3, h4⟩ := add_pext (g := g) a b ha hb
    refine ⟨fun P hP ↦ ?_, ?_⟩
    · simp only [addB, List.mem_cons] at hP
      rcases hP with rfl | hP
      · exact h3
      · exact h1 P hP
    · simp only [addB, List.map_cons]
      rw [h4, h2]

lemma derivYB_pext : ∀ (W : List (List F)), InSB S W →
    InSB S (derivYB W) ∧ (derivYB W).map (·.map (pext S g)) = derivYB (W.map (·.map (pext S g)))
  | [], _ => ⟨fun _ h ↦ by simp [derivYB] at h, rfl⟩
  | a :: W, hW => by
    have hW' : InSB S W := fun P hP ↦ hW P (List.mem_cons_of_mem _ hP)
    obtain ⟨h1, h2⟩ := derivYB_pext W hW'
    have hc : InSB S ([] :: derivYB W) := fun P hP ↦ by
      rcases List.mem_cons.mp hP with rfl | hP
      · exact InS.nil
      · exact h1 P hP
    obtain ⟨h3, h4⟩ := addB_pext (g := g) W ([] :: derivYB W) hW' hc
    refine ⟨h3, ?_⟩
    simp only [derivYB, List.map_cons]
    rw [h4, List.map_cons, h2]
    rfl

end Ops2

section Checks

variable {F F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F']
  {S : Subring F} {g : S →+* F'}

/-- **The order of the first non-zero coefficient is preserved** if that coefficient reduces to a
non-zero value. -/
lemma ordC_pext : ∀ (P : List F), InS S P →
    (ordC P < P.length → pext S g (P.getD (ordC P) 0) ≠ 0) → ordC (P.map (pext S g)) = ordC P
  | [], _, _ => rfl
  | a :: l, hP, hu => by
    obtain ⟨ha, hl⟩ := hP.of_cons
    by_cases ha0 : a = 0
    · subst ha0
      have e1 : ordC ((0 : F) :: l) = ordC l + 1 := by simp [ordC, List.findIdx_cons]
      have e2 : ordC (((0 : F) :: l).map (pext S g)) = ordC (l.map (pext S g)) + 1 := by
        simp [ordC, List.findIdx_cons, pext_zero]
      rw [e1, e2, ordC_pext l hl (fun h ↦ by
        have := hu (by rw [e1]; simp; omega)
        rwa [e1, List.getD_cons_succ] at this)]
    · have e1 : ordC (a :: l) = 0 := by simp [ordC, List.findIdx_cons, ha0]
      have hu' := hu (by rw [e1]; simp)
      rw [e1, List.getD_cons_zero] at hu'
      rw [e1]
      simp [ordC, List.findIdx_cons, hu']

variable (S g)

/-- The unit condition for a list: its first non-zero coefficient reduces to a non-zero value. -/
def OrdUnit (P : List F) : Prop := ordC P < P.length → pext S g (P.getD (ordC P) 0) ≠ 0

variable {S g}

/-- **Root checks reduce.** -/
lemma rootCheck_pext {Fc : List (List F)} {a : F} {N prec : ℕ} {y : List F}
    (hF : InSB S Fc) (ha : a ∈ S) (hy : InS S y)
    (hu : OrdUnit S g (bivEvalT (derivYB Fc) (shiftC a N) y prec))
    (h : rootCheck Fc a N prec y = true) :
    rootCheck (Fc.map (·.map (pext S g))) (pext S g a) N prec (y.map (pext S g)) = true := by
  obtain ⟨hdF, hdF'⟩ := derivYB_pext (g := g) Fc hF
  obtain ⟨hs, hs'⟩ := shiftC_pext (g := g) ha N
  obtain ⟨hD, hD'⟩ := bivEvalT_pext (g := g) _ _ hs hy prec (derivYB Fc) hdF
  simp only [rootCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [← hdF', ← hs', ← hD', ordC_pext _ hD hu]
  obtain ⟨hH, hH'⟩ := bivEvalT_pext (g := g) _ _ hs hy
    (ordC (bivEvalT (derivYB Fc) (shiftC a N) y prec) + prec) Fc hF
  refine ⟨⟨h1, by rwa [List.length_map]⟩, fun i hi ↦ ?_⟩
  rw [← hH', getD_pext, h3 i hi, pext_zero]

/-- The separation condition: the first differing coefficients reduce to distinct values. -/
def SepUnit (ys : List (List F)) (prec : ℕ) : Prop :=
  ∀ k l, k ≠ l → k < ys.length → l < ys.length → ∃ i < prec,
    pext S g ((ys.getD k []).getD i 0) ≠ pext S g ((ys.getD l []).getD i 0)

/-- **Separation checks reduce.** -/
lemma sepCheck_pext {ys : List (List F)} {prec : ℕ} (hu : SepUnit (S := S) (g := g) ys prec) :
    sepCheck (ys.map (·.map (pext S g))) prec = true := by
  simp only [sepCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true, List.length_map]
  intro k hk l hl
  by_cases hkl : k = l
  · exact Or.inl hkl
  right
  obtain ⟨i, hi, hne⟩ := hu k l hkl hk hl
  refine ⟨i, hi, ?_⟩
  rwa [show ([] : List F') = ([] : List F).map (pext S g) from rfl, List.getD_map, List.getD_map,
    getD_pext, getD_pext]

/-- **Branch certificates reduce.** -/
lemma certCheck_pext {Fc : List (List F)} {n : ℕ} {a : F} {c : BranchCert F}
    (hF : InSB S Fc) (ha : a ∈ S) (hys : InSB S c.ys)
    (hu : ∀ y ∈ c.ys, OrdUnit S g (bivEvalT (derivYB Fc) (shiftC a c.N) y c.prec))
    (hsep : SepUnit (S := S) (g := g) c.ys c.prec) (h : certCheck Fc n a c = true) :
    certCheck (Fc.map (·.map (pext S g))) n (pext S g a)
      ⟨c.N, c.ys.map (·.map (pext S g)), c.prec⟩ = true := by
  simp only [certCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨hN, hlen⟩, hroots⟩, -⟩ := h
  refine ⟨⟨⟨hN, by rw [List.length_map, hlen]⟩, fun y hy ↦ ?_⟩, sepCheck_pext hsep⟩
  obtain ⟨y0, hy0, rfl⟩ := List.mem_map.mp hy
  exact rootCheck_pext hF ha (hys y0 hy0) (hu y0 hy0) (hroots y0 hy0)

end Checks

end Curves
