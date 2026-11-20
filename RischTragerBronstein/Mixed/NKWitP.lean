import RischTragerBronstein.Mixed.NKWitTRE

/-!
# Precomputed candidates first: the antiderivative

The practical searches `searchTRP`, `searchTREP` try precomputed (untrusted) candidates of their
own type first and then the enumeration; `prefW` mirrors this prefix generically
(`prefW_isSome`, `prefW_src`). `nk_integrateTRP`, `nk_integrateTREP`: constructive versions of
`nk_decidesTRP`, `nk_decidesTREP`.
-/

open Polynomial IntermediateField Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX GTors

/-- Precomputed candidates (of any type) first, then `rest`. -/
def prefW {C W : Type*} (exW : C → Option (Option W)) (pre : List C) (rest : Option (Option W)) :
    Option (Option W) :=
  match pre.findSome? exW with
  | some b => some b
  | none => rest

lemma prefW_isSome {C W : Type*} (exW : C → Option (Option W)) (ex : C → Option Bool)
    (h : ∀ c, (exW c).map Option.isSome = ex c) (pre : List C) (rest : Option (Option W))
    (restB : Option Bool) (hrest : rest.map Option.isSome = restB) :
    (prefW exW pre rest).map Option.isSome =
      match pre.findSome? ex with
      | some b => some b
      | none => restB := by
  have hp : pre.findSome? ex = (pre.findSome? exW).map Option.isSome := by
    rw [findSome?_mapG]
    congr 1
    funext c
    exact (h c).symm
  unfold prefW
  rw [hp]
  cases pre.findSome? exW with
  | some b => rfl
  | none => exact hrest

lemma prefW_src {C W : Type*} (exW : C → Option (Option W)) (pre : List C)
    (rest : Option (Option W)) (w : W) (h : prefW exW pre rest = some (some w)) :
    (∃ c ∈ pre, exW c = some (some w)) ∨ rest = some (some w) := by
  unfold prefW at h
  split at h
  · rename_i b hb
    obtain ⟨c, hc, hce⟩ := List.exists_of_findSome?_eq_some hb
    exact Or.inl ⟨c, hc, hce.trans h⟩
  · exact Or.inr h

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

lemma treExW_isSome (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (c : CandTRE) :
    (treExW Fc ks m a rdeD P f c).map Option.isSome =
      exactTRE Fc ks m a rdeD (fun i ↦ c.2.2.1.getD i 0) c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2 P
        (matL Fc ks m c.1) (matL Fc ks m c.2.1) f :=
  exactTREW_isSome _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **The constructive decision with precomputed candidates** (constant curves, logarithmic
level). -/
def nkTRPW (m : ℕ) (η : LC m) (Pp : List (GPoly (LC m))) (s : List (LC (m + 1)))
    (fp : List (GPoly (LC m)))
    (pre : List (List (List (LC (m + 1))) × List (List (LC (m + 1))) × (ℕ → ℤ))) (N : ℕ) :=
  let f := nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N)
    (prefW (fun c ↦ exactTLSW Fc ks m η
        (fun n A0 q hh G0 ↦ primSysB Fc ks m η (paramLimC Fc ks lv m) n A0 q hh G0 0) c.2.2
        (nkPC Fc ks m Pp) c.1 c.2.1 f []) pre
      ((searchPW (fun _ ↦ true) (trExW Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp) f)
        [] N).map (Option.map Prod.snd)))

/-- **The constructive decision with precomputed candidates** (constant curves, exponential
level). -/
def nkTREPW (m : ℕ) (a : LC m) (Pp : List (GPoly (LC m))) (s : List (LC (m + 1)))
    (fp : List (GPoly (LC m))) (pre : List (PreTRE m)) (N : ℕ) :=
  let f := nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N)
    (prefW (fun c ↦ exactTREW Fc ks m a (rdeE Fc ks lv m) c.2.2.1 c.2.2.2.1 c.2.2.2.2.1
        c.2.2.2.2.2 (nkPC Fc ks m Pp) c.1 c.2.1 f) pre
      ((searchPW (fun _ ↦ true) (treExW Fc ks m a (rdeE Fc ks lv m) (nkPC Fc ks m Pp) f)
        [] N).map (Option.map Prod.snd)))

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **`nk_decidesTRP`, constructive.** -/
theorem nk_integrateTRP (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m)))
    (F0 : ℚ[X][X]) (hF0 : F0.Monic) (hlen : Pp.length = F0.natDegree)
    (hcoef : ∀ i < Pp.length, T.evP m (Pp.getD i []) = aeval (T.ts m) (F0.coeff i))
    (pre : List (List (List (LC (m + 1))) × List (List (LC (m + 1))) × (ℕ → ℤ))) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkTRPW Fc ks lv m η Pp s fp pre N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExpl m h1 θ Pp fp s (fun _ ↦ 1) 0 b := by
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦ ?_)
    _ (T.nk_decidesTRP hmon hdeg hshF m hn hc hk Pp hsh θ hθ hgen s hs fp F0 hF0 hlen hcoef pre) _
    fun N w hw h1 ↦ ?_
  · unfold searchTRP
    refine prefW_isSome _ _ (fun c ↦ (exactTLSW_isSome _ _ _ _ _ _ _ _ _ _ _).trans
      (exactTR_eq _ _ _ _ _ _ _ _ _ _).symm) _ _ _ ?_
    rw [map_map_isSome, searchPW_isSome _ _ _ (trExW_isSome Fc ks m η _ _ _) [] N,
      ← searchTR_eq]
  · have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
    have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
        (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
      rw [length_nkPC]; exact T.nkCurve_ind m h1 Pp hsh θ hθ
    have hspec := T.primSpecB (by omega) h1.of_succ hk _ MSm.lim
    have hex : ∃ (r : ℕ → ℤ) (Tc Ti : List (List (LC (m + 1)))),
        exactTLSW Fc ks m η (fun n A0 q hh G0 ↦ primSysB Fc ks m η (paramLimC Fc ks lv m) n A0 q
          hh G0 0) r (nkPC Fc ks m Pp) Tc Ti (nkRest Fc ks m (nkFl Fc ks m fp)
            (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) [] = some (some w) := by
      rcases prefW_src _ _ _ w hw with ⟨c, -, hc⟩ | hr
      · exact ⟨_, _, _, hc⟩
      · obtain ⟨o, ho, hoe⟩ := Option.map_eq_some_iff.mp hr
        obtain ⟨w', rfl, rfl⟩ := Option.map_eq_some_iff.mp hoe
        exact ⟨_, _, _, (searchPW_src _ _ [] N w' ho).2⟩
    obtain ⟨r, Tc, Ti, hex⟩ := hex
    have hY := T.exactTLSW_valid m h1 (by omega) hk (h1 m (by omega)) _ hspec r (nkPC Fc ks m Pp) _ θ
      hP hind Tc Ti [] w hex
    exact T.nk_explicit_core m h1 Pp (T.nkShape_spec m h1.of_succ Pp hsh).1 θ [] (fun _ ↦ 1)
      (fun i hi ↦ absurd hi (by simp)) (fun i hi ↦ absurd hi (by simp)) fp s w hY

/-- **`nk_decidesTREP`, constructive.** -/
theorem nk_integrateTREP (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m)))
    (F0 : ℚ[X][X]) (hF0 : F0.Monic) (hlen : Pp.length = F0.natDegree)
    (hcoef : ∀ i < Pp.length, T.evP m (Pp.getD i []) = aeval (T.ts m) (F0.coeff i))
    (pre : List (PreTRE m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkTREPW Fc ks lv m a Pp s fp pre N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExpl m h1 θ Pp fp s (fun _ ↦ 1) 0 b := by
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦ ?_)
    _ (T.nk_decidesTREP hmon hdeg hshF m hn hc hk Pp hsh hsh0 θ hθ hgen s hs fp F0 hF0 hlen hcoef
      pre) _ fun N w hw h1 ↦ ?_
  · unfold searchTREP
    refine prefW_isSome _ _ (fun c ↦ exactTREW_isSome _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ ?_
    rw [map_map_isSome, searchPW_isSome _ _ _ (treExW_isSome Fc ks m a _ _ _) [] N,
      ← searchTRE_eq]
  · obtain ⟨hrde, hom⟩ := T.expTRE_specs hmon hdeg m hn hc hk
    have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
    have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
        (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
      rw [length_nkPC]; exact T.nkCurve_ind m h1 Pp hsh θ hθ
    have hex : ∃ (r : ℕ → ℤ) (N0 : ℕ) (C Ci : List (List ℚ)) (Tc Ti : List (List (LC (m + 1)))),
        exactTREW Fc ks m a (rdeE Fc ks lv m) r N0 C Ci (nkPC Fc ks m Pp) Tc Ti
          (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) =
            some (some w) := by
      rcases prefW_src _ _ _ w hw with ⟨c, -, hc⟩ | hr
      · exact ⟨_, _, _, _, _, _, hc⟩
      · obtain ⟨o, ho, hoe⟩ := Option.map_eq_some_iff.mp hr
        obtain ⟨w', rfl, rfl⟩ := Option.map_eq_some_iff.mp hoe
        exact ⟨_, _, _, _, _, _, (searchPW_src _ _ [] N w' ho).2⟩
    obtain ⟨r, N0, C, Ci, Tc, Ti, hex⟩ := hex
    have hY := T.exactTREW_valid m h1 (by omega) hk (h1 m (by omega)) _ hrde hom r N0 C Ci
      (nkPC Fc ks m Pp) _ θ hP hind Tc Ti w hex
    exact T.nk_explicit_core m h1 Pp (T.nkShape_spec m h1.of_succ Pp hsh).1 θ [] (fun _ ↦ 1)
      (fun i hi ↦ absurd hi (by simp)) (fun i hi ↦ absurd hi (by simp)) fp s w hY

end MTower

end Curves.MT
