import RischTragerBronstein.Mixed.NKDecidesInfVMR
import RischTragerBronstein.Mixed.NKDecidesETInfVMR
import RischTragerBronstein.Mixed.NKWitET
import RischTragerBronstein.Mixed.NKWitInfVR
import RischTragerBronstein.Mixed.NKDecidesPM

/-!
# Several slopes at infinity: units without certificate, and the antiderivative

For the deciders `nk_decidesInfVMR` (logarithmic level) and `nk_decidesETInfVMR` (exponential
level, a single place above `t = 0`):

* `…PW`: the units' logarithmic derivatives need only be independent over the constants modulo
  `Fₘ₊₁` (the certificate exists, `indepWC_exists_of_logs`);
* `…PM`: the units need only be multiplicatively independent modulo the constants
  (`hli_of_mult`);
* `nk_integrateInfVMRPW`, `nk_integrateETInfVMRPW`: the constructive versions through the generic
  witness search (`searchPW`, `nk_integrate_core`): for every large bound the answer is
  elementary-ness, and an elementary answer carries an antiderivative of the trace part (`ValidW`)
  and units `uᵢ ≠ 0` with an exact part `(c, Y)`: `f(θ) = τ + (∑ₖ Yₖ θᵏ)′ + ∑ᵢ cᵢ uᵢ′/uᵢ`
  (`NKExpl`).
-/

open Polynomial IntermediateField Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- The checks on a candidate (several slopes, logarithmic level). -/
def ivmCond (m : ℕ) (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (c : CandIVR m) : Bool :=
  decide (c.1.2.2.1.length + 1 = np) &&
      unitsC Fc ks m Pp c.1.1 c.1.2.1 c.1.2.2.1 dθ wθ s &&
      indepC Fc ks m c.1.2.2.1 c.1.2.2.2.1 c.1.2.2.2.2.1

/-- The exact-part test of a candidate (logarithmic level). -/
def ivmEx (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandIVR m) : Option Bool :=
  exactTLVG Fc ks m η rde (dgOfR m c.2) c.1.2.2.2.2.2.2.2.2.1 c.1.2.2.2.2.2.2.2.2.2
    (fun i ↦ c.1.2.2.2.2.2.2.2.1.getD i 0) (nkPC Fc ks m Pp) c.1.2.2.2.2.2.1 c.1.2.2.2.2.2.2.1 f
    c.1.2.2.1

/-- The exact-part test of a candidate, with the witness (logarithmic level). -/
def ivmExW (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandIVR m) :
    Option (Option (List ℚ × List (LC (m + 1)))) :=
  exactTLVGW Fc ks m η rde (dgOfR m c.2) c.1.2.2.2.2.2.2.2.2.1 c.1.2.2.2.2.2.2.2.2.2
    (fun i ↦ c.1.2.2.2.2.2.2.2.1.getD i 0) (nkPC Fc ks m Pp) c.1.2.2.2.2.2.1 c.1.2.2.2.2.2.2.1 f
    c.1.2.2.1

lemma ivmExW_isSome (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandIVR m) :
    (ivmExW Fc ks m η rde Pp f c).map Option.isSome = ivmEx Fc ks m η rde Pp f c :=
  exactTLVGW_isSome _ _ _ _ _ _ _ _ _ _ _ _ _ _

lemma searchIVMP_eq (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandIVR m)) (B : ℕ) :
    searchIVMP Fc ks m η rde Pp np dθ wθ s f pre B =
      searchPS (ivmCond Fc ks m Pp np dθ wθ s) (ivmEx Fc ks m η rde Pp f) pre B := by
  have ht : ivmTry Fc ks m η rde Pp np dθ wθ s f =
      tryS (ivmCond Fc ks m Pp np dθ wθ s) (ivmEx Fc ks m η rde Pp f) := funext fun _ ↦ rfl
  have hs : searchIVM Fc ks m η rde Pp np dθ wθ s f B =
      searchS (ivmCond Fc ks m Pp np dθ wθ s) (ivmEx Fc ks m η rde Pp f) B := by
    unfold searchIVM searchS
    congr 1
    funext k
    cases (Encodable.decode k : Option (CandIVR m)) with
    | none => rfl
    | some c => exact congrFun ht c
  unfold searchIVMP searchPS
  rw [ht, hs]
  generalize List.findSome? (tryS (ivmCond Fc ks m Pp np dθ wθ s) (ivmEx Fc ks m η rde Pp f)) pre = o
  cases o <;> rfl

/-- **The constructive decision** (several slopes, logarithmic level). -/
def nkInfVMRW (m : ℕ) (η : LC m) (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (pre : List (CandIVR m)) (N : ℕ) :=
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N)
    (searchPW (ivmCond Fc ks m Pp np dθ wθ s) (ivmExW Fc ks m η (prdeC Fc ks lv m) Pp
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) pre N)

/-- The checks on a candidate (several slopes, exponential level). -/
def etvmCond (m : ℕ) (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (c : CandETVR m) : Bool :=
  decide (c.1.2.2.1.length + 1 = np) &&
      unitsC Fc ks m Pp c.1.1 c.1.2.1 c.1.2.2.1 dθ wθ s &&
      indepC Fc ks m c.1.2.2.1 c.1.2.2.2.1 c.1.2.2.2.2.1

lemma searchETVMP_eq (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandETVR m)) (B : ℕ) :
    searchETVMP Fc ks m a rde Pp np dθ wθ s f pre B =
      searchPS (etvmCond Fc ks m Pp np dθ wθ s) (etvrEx Fc ks m a rde Pp f) pre B := by
  have ht : etvmTry Fc ks m a rde Pp np dθ wθ s f =
      tryS (etvmCond Fc ks m Pp np dθ wθ s) (etvrEx Fc ks m a rde Pp f) := funext fun _ ↦ rfl
  have hs : searchETVM Fc ks m a rde Pp np dθ wθ s f B =
      searchS (etvmCond Fc ks m Pp np dθ wθ s) (etvrEx Fc ks m a rde Pp f) B := by
    unfold searchETVM searchS
    congr 1
    funext k
    cases (Encodable.decode k : Option (CandETVR m)) with
    | none => rfl
    | some c => exact congrFun ht c
  unfold searchETVMP searchPS
  rw [ht, hs]
  generalize List.findSome? (tryS (etvmCond Fc ks m Pp np dθ wθ s) (etvrEx Fc ks m a rde Pp f)) pre = o
  cases o <;> rfl

/-- **The constructive decision** (several slopes, exponential level). -/
def nkETVMRW (m : ℕ) (a : LC m) (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (pre : List (CandETVR m)) (N : ℕ) :=
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N)
    (searchPW (etvmCond Fc ks m Pp np dθ wθ s) (etvrExW Fc ks m a (prdeC Fc ks lv m) Pp
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) pre N)

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **`nk_decidesInfVMR` without an independence certificate.** -/
theorem nk_decidesInfVMRPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = nPlacesR segs ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandIVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchIVMP Fc ks m η (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  obtain ⟨Us, Vs, gls, hk1, hU, hli⟩ := hunits
  have hTr : T.Tr (m + 1) := (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr
  obtain ⟨J, D, H, -, hJH⟩ := T.indepWC_exists_of_logs m hTr θ Pp.length gls
    (fun i hi ↦ (unitsC_spec hU i hi).2.2.1) (hli hTr)
  exact T.nk_decidesInfVMR hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms θ hθ
    hgen dθ wθ s hs ⟨Us, Vs, gls, J ++ D, H, hk1, hU, hJH⟩ fp pre

/-- **`nk_decidesETInfVMR` without an independence certificate.** -/
theorem nk_decidesETInfVMRPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = nPlacesR segs ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandETVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchETVMP Fc ks m a (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  obtain ⟨Us, Vs, gls, hk1, hU, hli⟩ := hunits
  have hTr : T.Tr (m + 1) := (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr
  obtain ⟨J, D, H, -, hJH⟩ := T.indepWC_exists_of_logs m hTr θ Pp.length gls
    (fun i hi ↦ (unitsC_spec hU i hi).2.2.1) (hli hTr)
  exact T.nk_decidesETInfVMR hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms hsh0
    θ hθ hgen dθ wθ s hs ⟨Us, Vs, gls, J ++ D, H, hk1, hU, hJH⟩ fp pre

lemma pos_of_multiShapeRC (m : ℕ) (Pp : List (GPoly (LC m))) (segs : List (SegRC m))
    (hms : multiShapeRC Fc ks m Pp segs = true) : 0 < Pp.length := by
  unfold multiShapeRC at hms
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hms
  exact hms.1.1.1.1

/-- **`nk_decidesInfVMRPW` with multiplicatively independent units.** -/
theorem nk_decidesInfVMRPM (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = nPlacesR segs ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ a : Fin gls.length → ℤ, (∃ c : Cc, ∏ i : Fin gls.length,
        T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) ^ a i = algebraMap Cc L c) → a = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandIVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchIVMP Fc ks m η (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  obtain ⟨Us, Vs, gls, hk1, hU, hmult⟩ := hunits
  have hn0 := pos_of_multiShapeRC m Pp segs hms
  have hP : ∀ h1 : T.Tr (m + 1), T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := fun h1 ↦ by
    rw [T.evθ_nkPC]; exact hθ
  exact T.nk_decidesInfVMRPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms θ hθ
    hgen dθ wθ s hs
    ⟨Us, Vs, gls, hk1, hU, fun h1 ↦ T.hli_of_mult m h1 θ Pp (hP h1) hn0
      (T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ) Us Vs gls dθ wθ s hs hU (hmult h1)⟩
    fp pre

/-- **`nk_decidesETInfVMRPW` with multiplicatively independent units.** -/
theorem nk_decidesETInfVMRPM (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = nPlacesR segs ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ a : Fin gls.length → ℤ, (∃ c : Cc, ∏ i : Fin gls.length,
        T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) ^ a i = algebraMap Cc L c) → a = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandETVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchETVMP Fc ks m a (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  obtain ⟨Us, Vs, gls, hk1, hU, hmult⟩ := hunits
  have hn0 := pos_of_multiShapeRC m Pp segs hms
  have hP : ∀ h1 : T.Tr (m + 1), T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := fun h1 ↦ by
    rw [T.evθ_nkPC]; exact hθ
  exact T.nk_decidesETInfVMRPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms hsh0
    θ hθ hgen dθ wθ s hs
    ⟨Us, Vs, gls, hk1, hU, fun h1 ↦ T.hli_of_mult m h1 θ Pp (hP h1) hn0
      (T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ) Us Vs gls dθ wθ s hs hU (hmult h1)⟩
    fp pre

/-- **The integral with several slopes at infinity (logarithmic level), decided and computed.** -/
theorem nk_integrateInfVMRPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = nPlacesR segs ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandIVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkInfVMRW Fc ks lv m η Pp (nPlacesR segs) dθ wθ s fp pre N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExpl m h1 θ Pp fp s
          (fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (b.1.1.1.getD i []))) b.1.1.2.2.1.length b.2 := by
  have hn0 := pos_of_multiShapeRC m Pp segs hms
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦
      (searchPW_isSome _ _ _ (ivmExW_isSome Fc ks m η _ Pp _) pre N).trans
        (searchIVMP_eq Fc ks m η _ Pp (nPlacesR segs) dθ wθ s _ pre N).symm)
    _ (T.nk_decidesInfVMRPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms
      θ hθ hgen dθ wθ s hs hunits fp pre) _ fun N w hw h1 ↦ ?_
  obtain ⟨hcd, hex⟩ := searchPW_src _ _ pre N w hw
  simp only [ivmCond, Bool.and_eq_true, decide_eq_true_eq] at hcd
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [length_nkPC]; exact T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  have hY := T.exactTLVGW_valid m h1 (by omega) hk (h1 m (by omega)) _ MSm.rde _ _ _ _
    (nkPC Fc ks m Pp) _ θ hP hind _ _ _ w.2 hex
  exact T.nk_explicit_core m h1 Pp hn0 θ _ _
    (T.units_logs m h1 θ Pp hP _ _ _ dθ wθ s hcd.1.2)
    (fun i hi ↦ (unitsC_spec hcd.1.2 i hi).2.2.1) fp s w.2 hY

/-- **The integral with several slopes at infinity (exponential level), decided and computed.** -/
theorem nk_integrateETInfVMRPW (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true)
    (hsh0 : nkShape0 Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = nPlacesR segs ∧ unitsC Fc ks m Pp Us Vs gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandETVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkETVMRW Fc ks lv m a Pp (nPlacesR segs) dθ wθ s fp pre N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExpl m h1 θ Pp fp s
          (fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (b.1.1.1.getD i []))) b.1.1.2.2.1.length b.2 := by
  have hn0 := pos_of_multiShapeRC m Pp segs hms
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦
      (searchPW_isSome _ _ _ (etvrExW_isSome Fc ks m a _ Pp _) pre N).trans
        (searchETVMP_eq Fc ks m a _ Pp (nPlacesR segs) dθ wθ s _ pre N).symm)
    _ (T.nk_decidesETInfVMRPW hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms
      hsh0 θ hθ hgen dθ wθ s hs hunits fp pre) _ fun N w hw h1 ↦ ?_
  obtain ⟨hcd, hex⟩ := searchPW_src _ _ pre N w hw
  simp only [etvmCond, Bool.and_eq_true, decide_eq_true_eq] at hcd
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [length_nkPC]; exact T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ
  obtain ⟨hrde, hom⟩ := T.expTEV_specs hmon hdeg m hn hc hk
  have hY := T.exactTLEVGW_valid m h1 (by omega) hk (h1 m (by omega)) _ hrde hom _ _ _ _ _ _ _
    (nkPC Fc ks m Pp) _ θ hP hind _ _ _ w.2 hex
  exact T.nk_explicit_core m h1 Pp hn0 θ _ _
    (T.units_logs m h1 θ Pp hP _ _ _ dθ wθ s hcd.1.2)
    (fun i hi ↦ (unitsC_spec hcd.1.2 i hi).2.2.1) fp s w.2 hY

end MTower

end Curves.MT
