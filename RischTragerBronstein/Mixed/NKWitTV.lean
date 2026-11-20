import RischTragerBronstein.Mixed.NKWitET
import RischTragerBronstein.Mixed.NKSearchTV

/-!
# A single place at infinity, non-constant curves: the antiderivative

`exactTV` is the parametric pipeline without parameters (`exactTV_eq`: `exactWE` is `exactWLE`
and `exactWRS` is `exactWRSL` with no parameters), so `exactTLSW` returns its exact part. The
decision `nk_decidesTV` (an enumeration of candidates) made constructive: `nkTVW` answers for
every large bound exactly whether the integral is elementary and returns an antiderivative of the
trace part (`ValidW`) and an exact part `Y` with `f(θ) = τ + (∑ₖ Yₖ θᵏ)′`
(`nk_integrateTV`); the same for the precomputed candidates of `searchTVP` (`nk_integrateTVP`).
-/

open Polynomial IntermediateField Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

lemma exactWE_eq (m : ℕ) (solve : SysSolver m) (N : ℕ) (Mc : List (List (LC (m + 1))))
    (f : List (LC (m + 1))) (E : GPoly (LC m)) :
    exactWE Fc ks m solve N Mc f E = exactWLE Fc ks m solve N Mc f [] E := by
  unfold exactWE exactWLE
  simp only [List.flatten_nil, List.append_nil, matFn_matData, List.map_cons, List.map_nil]
  split_ifs
  · rfl
  · rfl
  · split
    · rename_i h; simp only [h]
    · rename_i r h; simp only [h]

lemma exactWRS_eq (m : ℕ) (η : LC m) (solve : SysSolver m) (N : ℕ)
    (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (r : ℕ → ℤ) :
    exactWRS Fc ks m η solve N Mc f r = exactWRSL Fc ks m η solve N Mc f [] r := by
  unfold exactWRS exactWRSL
  simp only [List.flatten_nil, List.append_nil, matFn_matData, List.map_nil, exactWE_eq]
  split_ifs
  · rfl
  · rfl
  · split
    · rename_i h; simp only [h]
    · rename_i r h; simp only [h]

lemma exactTV_eq (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (FRep (LC m))) (r : ℕ → ℤ) (P : GPoly (LC (m + 1)))
    (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) :
    exactTV Fc ks m η rde dg r P Tc Ti f =
      exactTLS Fc ks m η (fun n A0 q hh G0 ↦ primSysV Fc ks m η rde dg n A0 q hh G0) r P Tc Ti
        f [] := by
  unfold exactTV exactTG exactTLS exactWRV
  simp only [exactWRS_eq, List.map_nil]
  split_ifs
  · rfl
  · split
    · rename_i h; simp only [h]
    · rename_i r h; simp only [h]

/-- The exact part of a candidate `(T, T⁻¹, shifts, diagonal)`, with the witness. -/
def tvExW (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (c : CandTV m) :
    Option (Option (List ℚ × List (LC (m + 1)))) :=
  exactTLSW Fc ks m η (fun n A0 q hh G0 ↦ primSysV Fc ks m η rde c.2.2.2 n A0 q hh G0)
    (fun i ↦ c.2.2.1.getD i 0) P c.1 c.2.1 f []

lemma tvExW_isSome (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (c : CandTV m) :
    (tvExW Fc ks m η rde P f c).map Option.isSome =
      exactTV Fc ks m η rde c.2.2.2 (fun i ↦ c.2.2.1.getD i 0) P c.1 c.2.1 f := by
  rw [exactTV_eq]; exact exactTLSW_isSome _ _ _ _ _ _ _ _ _ _ _

lemma searchTV_eq (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (B : ℕ) :
    searchTV Fc ks m η rde P f B = searchPS (fun _ ↦ true)
      (fun c : CandTV m ↦ exactTV Fc ks m η rde c.2.2.2 (fun i ↦ c.2.2.1.getD i 0) P c.1 c.2.1 f)
      [] B := by
  unfold searchTV searchPS searchS
  simp only [List.findSome?_nil]
  congr 1
  funext k
  cases (Encodable.decode k : Option (CandTV m)) with
  | none => rfl
  | some c => rfl

/-- **The constructive decision** (a single place at infinity, logarithmic level). -/
def nkTVW (m : ℕ) (η : LC m) (Pp : List (GPoly (LC m))) (s : List (LC (m + 1)))
    (fp : List (GPoly (LC m))) (N : ℕ) :=
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N)
    (searchPW (fun _ ↦ true) (tvExW Fc ks m η (prdeC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) [] N)

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The integral with a single place at infinity (logarithmic level), decided and computed**:
an elementary answer carries an antiderivative of the trace part and an exact part `Y` with
`f(θ) = τ + (∑ₖ Yₖ θᵏ)′`. -/
theorem nk_integrateTV (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkTVW Fc ks lv m η Pp s fp N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExpl m h1 θ Pp fp s (fun _ ↦ 1) 0 b.2 := by
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦
      (searchPW_isSome _ _ _ (tvExW_isSome Fc ks m η _ _ _) [] N).trans
        (searchTV_eq Fc ks m η _ _ _ N).symm)
    _ (T.nk_decidesTV hmon hdeg hshF m hn hc hk Pp hsh θ hθ hgen s hs fp) _ fun N w hw h1 ↦ ?_
  obtain ⟨-, hex⟩ := searchPW_src _ _ [] N w hw
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [length_nkPC]; exact T.nkCurve_ind m h1 Pp hsh θ hθ
  have hY := T.exactTLSW_valid m h1 (by omega) hk (h1 m (by omega)) _
    (T.primSpecV (by omega) h1.of_succ hk _ MSm.rde _) _ (nkPC Fc ks m Pp) _ θ hP hind _ _ [] w.2 hex
  exact T.nk_explicit_core m h1 Pp (T.nkShape_spec m h1.of_succ Pp hsh).1 θ [] (fun _ ↦ 1)
    (fun i hi ↦ absurd hi (by simp)) (fun i hi ↦ absurd hi (by simp)) fp s w.2 hY

end MTower

end Curves.MT
