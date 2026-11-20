import RischTragerBronstein.Mixed.NKWitInfVG

/-!
# Ramified places at infinity, non-constant curves: the antiderivative

The decision `nk_decidesInfVRPW` (a single slope `s/e` at infinity, logarithmic level) made
constructive, exactly as `NKWitInfVG`: `searchIVRPW` mirrors `searchIVRP` (`searchIVRPW_isSome`),
and `nk_integrateInfVRPW` returns, with an elementary answer, the antiderivative of the trace
part (`ValidW`) and units `uᵢ ≠ 0` with an exact part `(c, Y)`:
`f(θ) = τ + (∑ₖ Yₖ θᵏ)′ + ∑ᵢ cᵢ uᵢ′/uᵢ` (`nk_explicitInfVG`).
-/

open Polynomial IntermediateField Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- The witness of the exact part: the candidate and `(c, Y)`. -/
abbrev IVRW (m : ℕ) := CandIVR m × List ℚ × List (LC (m + 1))

/-- **`ivrTry` with the witness.** -/
def ivrTryW (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (c : CandIVR m) : Option (Option (IVRW m)) :=
  if (decide (c.1.2.2.1.length + 1 = Pp.length / e) &&
      unitsC Fc ks m Pp c.1.1 c.1.2.1 c.1.2.2.1 dθ wθ s &&
      indepC Fc ks m c.1.2.2.1 c.1.2.2.2.1 c.1.2.2.2.2.1) = true then
    (exactTLVGW Fc ks m η rde (dgOfR m c.2) c.1.2.2.2.2.2.2.2.2.1 c.1.2.2.2.2.2.2.2.2.2
      (fun i ↦ c.1.2.2.2.2.2.2.2.1.getD i 0) (nkPC Fc ks m Pp) c.1.2.2.2.2.2.1 c.1.2.2.2.2.2.2.1 f
      c.1.2.2.1).map (Option.map fun w ↦ (c, w))
  else none

/-- **`searchIVG` with the witness.** -/
def searchIVRW (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (B : ℕ) : Option (Option (IVRW m)) :=
  (List.range B).findSome? fun k ↦ match (Encodable.decode k : Option (CandIVR m)) with
    | none => none
    | some c => ivrTryW Fc ks m η rde Pp e dθ wθ s f c

/-- **`searchIVGP` with the witness.** -/
def searchIVRPW (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandIVR m)) (B : ℕ) : Option (Option (IVRW m)) :=
  match pre.findSome? (ivrTryW Fc ks m η rde Pp e dθ wθ s f) with
  | some b => some b
  | none => searchIVRW Fc ks m η rde Pp e dθ wθ s f B

lemma ivrTryW_isSome (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (c : CandIVR m) :
    (ivrTryW Fc ks m η rde Pp e dθ wθ s f c).map Option.isSome =
      ivrTry Fc ks m η rde Pp e dθ wθ s f c := by
  unfold ivrTryW ivrTry
  split_ifs
  · rw [map_map_isSome, exactTLVGW_isSome]
  · rfl

lemma searchIVRW_isSome (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (B : ℕ) :
    (searchIVRW Fc ks m η rde Pp e dθ wθ s f B).map Option.isSome =
      searchIVR Fc ks m η rde Pp e dθ wθ s f B := by
  unfold searchIVRW searchIVR
  rw [findSome?_mapW]
  congr 1
  funext k
  cases (Encodable.decode k : Option (CandIVR m)) with
  | none => rfl
  | some c => exact ivrTryW_isSome _ _ _ _ _ _ _ _ _ _ _ _

/-- **`searchIVRPW` answers as `searchIVGP`.** -/
theorem searchIVRPW_isSome (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandIVR m)) (B : ℕ) :
    (searchIVRPW Fc ks m η rde Pp e dθ wθ s f pre B).map Option.isSome =
      searchIVRP Fc ks m η rde Pp e dθ wθ s f pre B := by
  have hp : pre.findSome? (ivrTry Fc ks m η rde Pp e dθ wθ s f) =
      (pre.findSome? (ivrTryW Fc ks m η rde Pp e dθ wθ s f)).map Option.isSome := by
    rw [findSome?_mapW]
    congr 1
    funext c
    exact (ivrTryW_isSome _ _ _ _ _ _ _ _ _ _ _ _).symm
  unfold searchIVRPW searchIVRP
  rw [hp]
  cases pre.findSome? (ivrTryW Fc ks m η rde Pp e dθ wθ s f) with
  | some b => rfl
  | none => exact searchIVRW_isSome _ _ _ _ _ _ _ _ _ _ _ _

lemma ivrTryW_src (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (c : CandIVR m) (w : IVRW m)
    (h : ivrTryW Fc ks m η rde Pp e dθ wθ s f c = some (some w)) :
    w.1.1.2.2.1.length + 1 = Pp.length / e ∧
      unitsC Fc ks m Pp w.1.1.1 w.1.1.2.1 w.1.1.2.2.1 dθ wθ s = true ∧
      exactTLVGW Fc ks m η rde (dgOfR m w.1.2) w.1.1.2.2.2.2.2.2.2.2.1 w.1.1.2.2.2.2.2.2.2.2.2
        (fun i ↦ w.1.1.2.2.2.2.2.2.2.1.getD i 0) (nkPC Fc ks m Pp) w.1.1.2.2.2.2.2.1
        w.1.1.2.2.2.2.2.2.1 f w.1.1.2.2.1 = some (some w.2) := by
  unfold ivrTryW at h
  split_ifs at h with hc
  obtain ⟨o, ho, hoe⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨w', rfl, rfl⟩ := Option.map_eq_some_iff.mp hoe
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨hc.1.1, hc.1.2, ho⟩

/-- **Provenance of a witness of `searchIVRPW`.** -/
theorem searchIVRPW_src (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandIVR m)) (B : ℕ) (w : IVRW m)
    (h : searchIVRPW Fc ks m η rde Pp e dθ wθ s f pre B = some (some w)) :
    w.1.1.2.2.1.length + 1 = Pp.length / e ∧
      unitsC Fc ks m Pp w.1.1.1 w.1.1.2.1 w.1.1.2.2.1 dθ wθ s = true ∧
      exactTLVGW Fc ks m η rde (dgOfR m w.1.2) w.1.1.2.2.2.2.2.2.2.2.1 w.1.1.2.2.2.2.2.2.2.2.2
        (fun i ↦ w.1.1.2.2.2.2.2.2.2.1.getD i 0) (nkPC Fc ks m Pp) w.1.1.2.2.2.2.2.1
        w.1.1.2.2.2.2.2.2.1 f w.1.1.2.2.1 = some (some w.2) := by
  unfold searchIVRPW at h
  split at h
  · rename_i b hb
    obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some hb
    rw [h] at hc
    exact ivrTryW_src Fc ks m η rde Pp e dθ wθ s f c w hc
  · unfold searchIVRW at h
    obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
    split at hk
    · exact absurd hk (by simp)
    · exact ivrTryW_src Fc ks m η rde Pp e dθ wθ s f _ w hk

/-- **The constructive decision**: the antiderivative of the trace part (`elMW`) and the exact
part with the logarithms (`searchIVRPW`); `some none` means "not elementary". -/
def nkInfVRW (m : ℕ) (η : LC m) (Pp : List (GPoly (LC m))) (e : ℕ) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (pre : List (CandIVR m)) (N : ℕ) :
    Option (Option (ADW (m + 1) × IVRW m)) :=
  match elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N,
    searchIVRPW Fc ks m η (prdeC Fc ks lv m) Pp e dθ wθ s
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

/-- **The integral, decided and computed** (several places at infinity, non-constant curves,
logarithmic level): for every large bound `N`, `nkInfVRW` answers; the answer is `some _`
exactly when `∫ f(θ)` is elementary, and then it carries an antiderivative of the trace part
(`ValidW`) and units `uᵢ ≠ 0` with an exact part `(c, Y)` such that
`f(θ) = τ + (∑ₖ Yₖ θᵏ)′ + ∑ᵢ cᵢ uᵢ′/uᵢ`. -/
theorem nk_integrateInfVRPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (e sR : ℕ) (γs : List (LC m)) (hram : ramShapeC Fc ks m Pp e sR γs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = Pp.length / e ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandIVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkInfVRW Fc ks lv m η Pp e dθ wθ s fp pre N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ a b, o = some (a, b) → ∀ h1 : T.Tr (m + 1),
        T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) a ∧
        (∀ i < b.1.1.2.2.1.length, T.evθ m h1 θ (nkFl Fc ks m (b.1.1.1.getD i [])) ≠ 0) ∧
        ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j =
          T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) +
          (∑ k ∈ Finset.range Pp.length,
            T.ev (m + 1) (b.2.2.getD k (MOr Fc ks (m + 1)).zero) * θ ^ k)′ +
          ∑ i ∈ Finset.range b.1.1.2.2.1.length, ((b.2.1.getD i 0 : ℚ) : L) *
            logDeriv (T.evθ m h1 θ (nkFl Fc ks m (b.1.1.1.getD i []))) := by
  classical
  obtain ⟨N₀, hN₀⟩ := T.nk_decidesInfVRPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck
    e sR γs hram θ hθ hgen dθ wθ s hs hunits fp pre
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
    rcases Nat.eq_zero_or_pos Pp.length with h0 | h0
    · rw [h0, Nat.zero_div] at hk1; omega
    · exact h0
  have hind := T.nkCurveE_ind m hTr Pp qE csE sE tE s2E t2E hck θ hθ
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, res, hb, hres, hiff⟩ := hN₀ N hN
  rw [← elMW_isSome] at hb
  rw [← searchIVRPW_isSome] at hres
  obtain ⟨oa, hoa, rfl⟩ := Option.map_eq_some_iff.mp hb
  obtain ⟨ob, hob, rfl⟩ := Option.map_eq_some_iff.mp hres
  refine ⟨_, by unfold nkInfVRW; rw [hoa, hob], ?_, ?_⟩
  · rw [hiff]
    cases oa <;> cases ob <;> simp
  · intro a w hw h1
    have hw' : oa = some a ∧ ob = some w := by
      cases oa <;> cases ob <;> simp_all
    obtain ⟨rfl, rfl⟩ := hw'
    refine ⟨T.elMW_validE hmon hdeg hshF (m + 1) hn hc hE0 (m + 1) le_rfl _ N a hoa, ?_⟩
    obtain ⟨-, hU, hex⟩ := searchIVRPW_src Fc ks m η _ Pp e dθ wθ s _ pre N w hob
    exact T.nk_explicitInfVG m h1 (by omega) hk (h1 m (by omega)) (prdeC Fc ks lv m) MSm.rde _ _ _ _
      Pp hn0 θ hθ hind _ _ _ dθ wθ s hU fp _ _ w.2 hex

end MTower

end Curves.MT
