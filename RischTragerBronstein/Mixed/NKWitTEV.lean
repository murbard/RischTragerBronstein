import RischTragerBronstein.Mixed.NKWitTV
import RischTragerBronstein.Mixed.NKDecidesTEV

/-!
# A single place at infinity over an exponential level: the antiderivative

`exactTEV` is `exactTLEVS` with no parameters (`exactTEV_eq`), so `exactTLEVSW` returns its exact
part; `nk_integrateTEV` makes the decision `nk_decidesTEV` constructive: an elementary answer
carries an antiderivative of the trace part and an exact part `Y` with `f(θ) = τ + (∑ₖ Yₖ θᵏ)′`.
-/

open Polynomial IntermediateField Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

lemma exactWREV_eq (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (ℚ × ℚ × LC m)) (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (r : ℕ → ℤ) (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m)) :
    exactWREV Fc ks m a rde dg N Mc f r C Ci dg0 =
      exactWREVLS Fc ks m a (fun n A0 q hh G0 ↦ expSysV Fc ks m a rde dg n A0 q hh G0 0) N Mc f []
        r C Ci dg0 := by
  unfold exactWREV exactWREVLS
  simp only [List.flatten_nil, List.append_nil, List.map_nil, exactWE_eq]
  split_ifs
  · rfl
  · rfl
  · rfl
  · rfl
  · split
    · rename_i h; simp only [h]
    · rename_i r h; simp only [h]

lemma exactTEV_eq (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (ℚ × ℚ × LC m)) (r : ℕ → ℤ) (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m))
    (P : GPoly (LC (m + 1))) (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) :
    exactTEV Fc ks m a rde dg r C Ci dg0 P Tc Ti f =
      exactTLEVS Fc ks m a (fun n A0 q hh G0 ↦ expSysV Fc ks m a rde dg n A0 q hh G0 0) r C Ci dg0
        P Tc Ti f [] := by
  unfold exactTEV exactTG exactTLEVS
  simp only [exactWREV_eq, List.map_nil]
  split_ifs
  · rfl
  · split
    · rename_i h; simp only [h]
    · rename_i r h; simp only [h]

/-- The exact part of a candidate, with the witness. -/
def tevExW (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (c : CandTEV m) :
    Option (Option (List ℚ × List (LC (m + 1)))) :=
  exactTLEVSW Fc ks m a (fun n A0 q hh G0 ↦ expSysV Fc ks m a rde c.2.2.2.1 n A0 q hh G0 0)
    (fun i ↦ c.2.2.1.getD i 0) c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2 P c.1 c.2.1 f []

lemma tevExW_isSome (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (c : CandTEV m) :
    (tevExW Fc ks m a rde P f c).map Option.isSome =
      exactTEV Fc ks m a rde c.2.2.2.1 (fun i ↦ c.2.2.1.getD i 0) c.2.2.2.2.1
        c.2.2.2.2.2.1 c.2.2.2.2.2.2 P c.1 c.2.1 f := by
  rw [exactTEV_eq]; exact exactTLEVSW_isSome _ _ _ _ _ _ _ _ _ _ _ _ _ _

lemma searchTEV_eq (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (B : ℕ) :
    searchTEV Fc ks m a rde P f B = searchPS (fun _ ↦ true)
      (fun c : CandTEV m ↦ exactTEV Fc ks m a rde c.2.2.2.1 (fun i ↦ c.2.2.1.getD i 0)
        c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2 P c.1 c.2.1 f) [] B := by
  unfold searchTEV searchPS searchS
  simp only [List.findSome?_nil]
  congr 1
  funext k
  cases (Encodable.decode k : Option (CandTEV m)) with
  | none => rfl
  | some c => rfl

/-- **The constructive decision** (a single place at infinity, exponential level). -/
def nkTEVW (m : ℕ) (a : LC m) (Pp : List (GPoly (LC m))) (s : List (LC (m + 1)))
    (fp : List (GPoly (LC m))) (N : ℕ) :=
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N)
    (searchPW (fun _ ↦ true) (tevExW Fc ks m a (prdeC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) [] N)

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The integral with a single place at infinity (exponential level), decided and computed.** -/
theorem nk_integrateTEV (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkTEVW Fc ks lv m a Pp s fp N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExpl m h1 θ Pp fp s (fun _ ↦ 1) 0 b.2 := by
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦
      (searchPW_isSome _ _ _ (tevExW_isSome Fc ks m a _ _ _) [] N).trans
        (searchTEV_eq Fc ks m a _ _ _ N).symm)
    _ (T.nk_decidesTEV hmon hdeg hshF m hn hc hk Pp hsh hsh0 θ hθ hgen s hs fp) _
    fun N w hw h1 ↦ ?_
  obtain ⟨-, hex⟩ := searchPW_src _ _ [] N w hw
  obtain ⟨hrde, hom⟩ := T.expTEV_specs hmon hdeg m hn hc hk
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [length_nkPC]; exact T.nkCurve_ind m h1 Pp hsh θ hθ
  have hY := T.exactTLEVSW_valid m h1 (by omega) hk (h1 m (by omega)) _
    (T.expSpecV (by omega) h1.of_succ hk _ hrde hom _) hom _ _ _ _ (nkPC Fc ks m Pp) _ θ hP hind
    _ _ [] w.2 hex
  exact T.nk_explicit_core m h1 Pp (T.nkShape_spec m h1.of_succ Pp hsh).1 θ [] (fun _ ↦ 1)
    (fun i hi ↦ absurd hi (by simp)) (fun i hi ↦ absurd hi (by simp)) fp s w.2 hY

end MTower

end Curves.MT
