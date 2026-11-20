import RischTragerBronstein.Mixed.NKWronskDecide
import RischTragerBronstein.Mixed.NKExactWitTL
import RischTragerBronstein.Mixed.MTWitSound

/-!
# Several places at infinity, non-constant curves: the antiderivative

The decision `nk_decidesInfVGPW` (`∫ f(θ)` for `θⁿ + ∑ aᵢ(t) θⁱ = 0` over a logarithm `t`, split at
infinity) made constructive. `searchIVGPW` mirrors `searchIVGP` (`searchIVGPW_isSome`) and returns
the accepted candidate (units `uᵢ`) and the explicit exact part `(c, Y)` of `exactTLVGW`;
`nk_explicitInfVG`: then
`f(θ) = τ + (∑ₖ Yₖ θᵏ)′ + ∑ᵢ cᵢ uᵢ′/uᵢ` with `τ = Tr(f)/n ∈ Fₘ₊₁`, whose antiderivative `elMW`
returns (`elMW_validE`, `L` being elementary over `F₀`: `isElementary_alg`).
`nk_integrateInfVGPW`: for every large bound, `nkInfVGW` answers, its answer is exactly whether
the integral is elementary, and an answer comes with all of these pieces.
-/

open Polynomial IntermediateField Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- The witness of the exact part: the candidate and `(c, Y)`. -/
abbrev IVGW (m : ℕ) := CandIVG m × List ℚ × List (LC (m + 1))

/-- **`ivgTry` with the witness.** -/
def ivgTryW (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (c : CandIVG m) : Option (Option (IVGW m)) :=
  if (decide (c.2.2.1.length + 1 = Pp.length) &&
      unitsC Fc ks m Pp c.1 c.2.1 c.2.2.1 dθ wθ s && indepC Fc ks m c.2.2.1 c.2.2.2.1 c.2.2.2.2.1)
    = true then
    (exactTLVGW Fc ks m η rde [] c.2.2.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2.2.2
      (fun i ↦ c.2.2.2.2.2.2.2.1.getD i 0) (nkPC Fc ks m Pp) c.2.2.2.2.2.1 c.2.2.2.2.2.2.1 f
      c.2.2.1).map (Option.map fun w ↦ (c, w))
  else none

/-- **`searchIVG` with the witness.** -/
def searchIVGW (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (B : ℕ) : Option (Option (IVGW m)) :=
  (List.range B).findSome? fun k ↦ match (Encodable.decode k : Option (CandIVG m)) with
    | none => none
    | some c => ivgTryW Fc ks m η rde Pp dθ wθ s f c

/-- **`searchIVGP` with the witness.** -/
def searchIVGPW (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandIVG m)) (B : ℕ) : Option (Option (IVGW m)) :=
  match pre.findSome? (ivgTryW Fc ks m η rde Pp dθ wθ s f) with
  | some b => some b
  | none => searchIVGW Fc ks m η rde Pp dθ wθ s f B

lemma findSome?_mapW {α β γ : Type*} (l : List α) (f : α → Option β) (g : β → γ) :
    (l.findSome? f).map g = l.findSome? fun a ↦ (f a).map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.findSome?_cons]
    cases f a <;> simp [ih]

lemma ivgTryW_isSome (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (c : CandIVG m) :
    (ivgTryW Fc ks m η rde Pp dθ wθ s f c).map Option.isSome =
      ivgTry Fc ks m η rde Pp dθ wθ s f c := by
  unfold ivgTryW ivgTry
  split_ifs
  · rw [map_map_isSome, exactTLVGW_isSome]
  · rfl

lemma searchIVGW_isSome (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (B : ℕ) :
    (searchIVGW Fc ks m η rde Pp dθ wθ s f B).map Option.isSome =
      searchIVG Fc ks m η rde Pp dθ wθ s f B := by
  unfold searchIVGW searchIVG
  rw [findSome?_mapW]
  congr 1
  funext k
  cases (Encodable.decode k : Option (CandIVG m)) with
  | none => rfl
  | some c => exact ivgTryW_isSome _ _ _ _ _ _ _ _ _ _ _

/-- **`searchIVGPW` answers as `searchIVGP`.** -/
theorem searchIVGPW_isSome (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandIVG m)) (B : ℕ) :
    (searchIVGPW Fc ks m η rde Pp dθ wθ s f pre B).map Option.isSome =
      searchIVGP Fc ks m η rde Pp dθ wθ s f pre B := by
  have hp : pre.findSome? (ivgTry Fc ks m η rde Pp dθ wθ s f) =
      (pre.findSome? (ivgTryW Fc ks m η rde Pp dθ wθ s f)).map Option.isSome := by
    rw [findSome?_mapW]
    congr 1
    funext c
    exact (ivgTryW_isSome _ _ _ _ _ _ _ _ _ _ _).symm
  unfold searchIVGPW searchIVGP
  rw [hp]
  cases pre.findSome? (ivgTryW Fc ks m η rde Pp dθ wθ s f) with
  | some b => rfl
  | none => exact searchIVGW_isSome _ _ _ _ _ _ _ _ _ _ _

lemma ivgTryW_src (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (c : CandIVG m) (w : IVGW m)
    (h : ivgTryW Fc ks m η rde Pp dθ wθ s f c = some (some w)) :
    w.1.2.2.1.length + 1 = Pp.length ∧ unitsC Fc ks m Pp w.1.1 w.1.2.1 w.1.2.2.1 dθ wθ s = true ∧
      exactTLVGW Fc ks m η rde [] w.1.2.2.2.2.2.2.2.2.1 w.1.2.2.2.2.2.2.2.2.2
        (fun i ↦ w.1.2.2.2.2.2.2.2.1.getD i 0) (nkPC Fc ks m Pp) w.1.2.2.2.2.2.1
        w.1.2.2.2.2.2.2.1 f w.1.2.2.1 = some (some w.2) := by
  unfold ivgTryW at h
  split_ifs at h with hc
  obtain ⟨o, ho, hoe⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨w', rfl, rfl⟩ := Option.map_eq_some_iff.mp hoe
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨hc.1.1, hc.1.2, ho⟩

/-- **Provenance of a witness of `searchIVGPW`.** -/
theorem searchIVGPW_src (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandIVG m)) (B : ℕ) (w : IVGW m)
    (h : searchIVGPW Fc ks m η rde Pp dθ wθ s f pre B = some (some w)) :
    w.1.2.2.1.length + 1 = Pp.length ∧ unitsC Fc ks m Pp w.1.1 w.1.2.1 w.1.2.2.1 dθ wθ s = true ∧
      exactTLVGW Fc ks m η rde [] w.1.2.2.2.2.2.2.2.2.1 w.1.2.2.2.2.2.2.2.2.2
        (fun i ↦ w.1.2.2.2.2.2.2.2.1.getD i 0) (nkPC Fc ks m Pp) w.1.2.2.2.2.2.1
        w.1.2.2.2.2.2.2.1 f w.1.2.2.1 = some (some w.2) := by
  unfold searchIVGPW at h
  split at h
  · rename_i b hb
    obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some hb
    rw [h] at hc
    exact ivgTryW_src Fc ks m η rde Pp dθ wθ s f c w hc
  · unfold searchIVGW at h
    obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
    split at hk
    · exact absurd hk (by simp)
    · exact ivgTryW_src Fc ks m η rde Pp dθ wθ s f _ w hk

/-- **The constructive decision**: the antiderivative of the trace part (`elMW`) and the exact
part with the logarithms (`searchIVGPW`); `some none` means "not elementary". -/
def nkInfVGW (m : ℕ) (η : LC m) (Pp : List (GPoly (LC m))) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (pre : List (CandIVG m)) (N : ℕ) :
    Option (Option (ADW (m + 1) × IVGW m)) :=
  match elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N,
    searchIVGPW Fc ks m η (prdeC Fc ks lv m) Pp dθ wθ s
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N with
  | some a, some b => some (match a, b with
    | some a, some b => some (a, b)
    | _, _ => none)
  | _, _ => none

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
/-- **The antiderivative, explicitly**: with units `uᵢ` and an exact part `(c, Y)` returned by
`exactTLVGW`, `f(θ) = τ + (∑ₖ Yₖ θᵏ)′ + ∑ᵢ cᵢ uᵢ′/uᵢ` with `τ = Tr(f)/n ∈ Fₘ₊₁` and `uᵢ ≠ 0`. -/
theorem nk_explicitInfVG (m : ℕ) (h1 : T.Tr (m + 1)) (hm : m < T.n) {η : LC m}
    (hk : ks m = .prim η) (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (dg : List (FRep (LC m))) (C Ci : List (List (LC m))) (r : ℕ → ℤ)
    (Pp : List (GPoly (LC m))) (hn0 : 0 < Pp.length) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range Pp.length, (a j : L) * θ ^ j = 0 →
      ∀ j < Pp.length, a j = 0)
    (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsC Fc ks m Pp Us Vs gls dθ wθ s = true)
    (fp : List (GPoly (LC m))) (Tc Ti : List (List (LC (m + 1))))
    (wt : List ℚ × List (LC (m + 1)))
    (hres : exactTLVGW Fc ks m η rde dg C Ci r (nkPC Fc ks m Pp) Tc Ti
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) gls =
        some (some wt)) :
    (∀ i < gls.length, T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) ≠ 0) ∧
    ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j =
      T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) +
      (∑ k ∈ Finset.range Pp.length, T.ev (m + 1) (wt.2.getD k (MOr Fc ks (m + 1)).zero) * θ ^ k)′ +
      ∑ i ∈ Finset.range gls.length, ((wt.1.getD i 0 : ℚ) : L) *
        logDeriv (T.evθ m h1 θ (nkFl Fc ks m (Us.getD i []))) := by
  classical
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
  have hind' : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [hlen]; exact hind
  have hY := T.exactTLVGW_valid m h1 hm hk htr rde hrde dg C Ci r (nkPC Fc ks m Pp) _ θ hP hind' Tc
    Ti gls wt hres
  unfold ExW at hY
  set M1 := T.MPr (m + 1) h1 with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  set u : ℕ → L := fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) with hu
  have hui : ∀ i < gls.length, u i ≠ 0 ∧ T.evθ m h1 θ (gls.getD i []) = (u i)′ / u i := by
    intro i hi
    obtain ⟨huv, hgl, -, -⟩ := unitsC_spec hU i hi
    have huvL := T.unitC_sound m h1 θ Pp _ _ hP huv
    exact ⟨left_ne_zero_of_mul_eq_one huvL, T.logDerChk_sound m h1 θ Pp _ _ _ dθ wθ hP huvL hgl⟩
  refine ⟨fun i hi ↦ (hui i hi).1, ?_⟩
  have hg : ∑ j ∈ Finset.range Pp.length, (∑ i ∈ Finset.range gls.length,
      ((wt.1.getD i 0 : ℚ) : L) * ((M1.sem ((gls.getD i []).getD j O1.zero) : T.F (m + 1)) : L)) *
        θ ^ j =
      ∑ i ∈ Finset.range gls.length, ((wt.1.getD i 0 : ℚ) : L) * logDeriv (u i) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.mp hi
    rw [logDeriv, ← (hui i hi').2, T.evθ_list_le m h1 θ _ Pp.length (unitsC_spec hU i hi').2.2.1,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hlen] at hY
  simp only [sub_mul, Finset.sum_sub_distrib] at hY
  rw [hg, T.sum_nkRest m h1 Pp.length hn0] at hY
  have hev : ∀ k, ((M1.sem (wt.2.getD k O1.zero) : T.F (m + 1)) : L) =
      T.ev (m + 1) (wt.2.getD k O1.zero) := fun k ↦ T.sem_MP (m + 1) h1 _
  simp only [hev] at hY
  rw [hY]
  ring

/-- **The integral, decided and computed** (several places at infinity, non-constant curves,
logarithmic level): for every large bound `N`, `nkInfVGW` answers; the answer is `some _`
exactly when `∫ f(θ)` is elementary, and then it carries an antiderivative of the trace part
(`ValidW`) and units `uᵢ ≠ 0` with an exact part `(c, Y)` such that
`f(θ) = τ + (∑ₖ Yₖ θᵏ)′ + ∑ᵢ cᵢ uᵢ′/uᵢ`. -/
theorem nk_integrateInfVGPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (sp : ℕ) (γs : List (LC m)) (hsplit : splitShapeC Fc ks m Pp sp γs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = Pp.length ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandIVG m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkInfVGW Fc ks lv m η Pp dθ wθ s fp pre N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ a b, o = some (a, b) → ∀ h1 : T.Tr (m + 1),
        T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) a ∧
        (∀ i < b.1.2.2.1.length, T.evθ m h1 θ (nkFl Fc ks m (b.1.1.getD i [])) ≠ 0) ∧
        ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j =
          T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) +
          (∑ k ∈ Finset.range Pp.length,
            T.ev (m + 1) (b.2.2.getD k (MOr Fc ks (m + 1)).zero) * θ ^ k)′ +
          ∑ i ∈ Finset.range b.1.2.2.1.length, ((b.2.1.getD i 0 : ℚ) : L) *
            logDeriv (T.evθ m h1 θ (nkFl Fc ks m (b.1.1.getD i []))) := by
  classical
  obtain ⟨N₀, hN₀⟩ := T.nk_decidesInfVGPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck sp
    γs hsplit θ hθ hgen dθ wθ s hs hunits fp pre
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  -- `L` is elementary over `F₀`
  have hmem : ∀ i, T.evP m (Pp.getD i []) ∈ T.F (m + 1) := fun i ↦ T.evP_mem m (T.ev_mem m) _
  have hθi : IsIntegral (T.F (m + 1)) θ := by
    refine ⟨polyF (fun i ↦ (⟨T.evP m (Pp.getD i []), hmem i⟩ : T.F (m + 1))) Pp.length,
      polyF_monic _ _, ?_⟩
    rw [← eval_map, polyF_eval_map]
    exact hθ
  have hE0 := T.isElementary_alg hmon hdeg (m + 1) hn hc θ hθi hgen 0 (Nat.zero_le _)
  have hn0 : 0 < Pp.length := by
    obtain ⟨_, _, gls, hk1, -⟩ := hunits
    omega
  have hind := T.nkCurveE_ind m hTr Pp qE csE sE tE s2E t2E hck θ hθ
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, res, hb, hres, hiff⟩ := hN₀ N hN
  rw [← elMW_isSome] at hb
  rw [← searchIVGPW_isSome] at hres
  obtain ⟨oa, hoa, rfl⟩ := Option.map_eq_some_iff.mp hb
  obtain ⟨ob, hob, rfl⟩ := Option.map_eq_some_iff.mp hres
  refine ⟨_, by unfold nkInfVGW; rw [hoa, hob], ?_, ?_⟩
  · rw [hiff]
    cases oa <;> cases ob <;> simp
  · intro a w hw h1
    have hw' : oa = some a ∧ ob = some w := by
      cases oa <;> cases ob <;> simp_all
    obtain ⟨rfl, rfl⟩ := hw'
    refine ⟨T.elMW_validE hmon hdeg hshF (m + 1) hn hc hE0 (m + 1) le_rfl _ N a hoa, ?_⟩
    obtain ⟨-, hU, hex⟩ := searchIVGPW_src Fc ks m η _ Pp dθ wθ s _ pre N w hob
    exact T.nk_explicitInfVG m h1 (by omega) hk (h1 m (by omega)) (prdeC Fc ks lv m) MSm.rde [] _ _ _
      Pp hn0 θ hθ hind _ _ _ dθ wθ s hU fp _ _ w.2 hex

end MTower

end Curves.MT
