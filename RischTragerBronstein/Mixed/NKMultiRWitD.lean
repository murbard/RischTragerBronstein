import RischTragerBronstein.Mixed.NKMultiRWit
import RischTragerBronstein.Mixed.NKDecidesInfVMRD
import RischTragerBronstein.Mixed.NKDecidesETInfVMRD
import RischTragerBronstein.Mixed.NKUnitsLogsD

/-!
# Several slopes at infinity: units without certificate, and the antiderivative

For the deciders `nk_decidesInfVMRD` (logarithmic level) and `nk_decidesETInfVMRD` (exponential
level, a single place above `t = 0`):

* `…PW`: the units' logarithmic derivatives need only be independent over the constants modulo
  `Fₘ₊₁` (the certificate exists, `indepWC_exists_of_logs`);
* `…PM`: the units need only be multiplicatively independent modulo the constants
  (`hli_of_mult`);
* `nk_integrateInfVMRPWD`, `nk_integrateETInfVMRPWD`: the constructive versions through the generic
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

/-- `etvrEx` on candidates with denominators. -/
def etvrExD (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandETVRD m) : Option Bool :=
  etvrEx Fc ks m a rde Pp f c.1

/-- `etvrExW` on candidates with denominators. -/
def etvrExWD (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandETVRD m) :
    Option (Option (List ℚ × List (LC (m + 1)))) :=
  etvrExW Fc ks m a rde Pp f c.1

lemma etvrExW_isSomeD (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandETVRD m) :
    (etvrExWD Fc ks m a rde Pp f c).map Option.isSome = etvrExD Fc ks m a rde Pp f c :=
  etvrExW_isSome Fc ks m a rde Pp f c.1


/-- The checks on a candidate (several slopes, logarithmic level). -/
def ivmCondD (m : ℕ) (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (c : CandIVRD m) : Bool :=
  decide (c.1.1.2.2.1.length + 1 = np) &&
      unitsCD Fc ks m Pp c.1.1.1 c.1.1.2.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 c.1.1.2.2.1 dθ wθ s &&
      indepC Fc ks m c.1.1.2.2.1 c.1.1.2.2.2.1 c.1.1.2.2.2.2.1

/-- The exact-part test of a candidate (logarithmic level). -/
def ivmExD (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandIVRD m) : Option Bool :=
  exactTLVG Fc ks m η rde (dgOfR m c.1.2) c.1.1.2.2.2.2.2.2.2.2.1 c.1.1.2.2.2.2.2.2.2.2.2
    (fun i ↦ c.1.1.2.2.2.2.2.2.2.1.getD i 0) (nkPC Fc ks m Pp) c.1.1.2.2.2.2.2.1 c.1.1.2.2.2.2.2.2.1 f
    c.1.1.2.2.1

/-- The exact-part test of a candidate, with the witness (logarithmic level). -/
def ivmExWD (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandIVRD m) :
    Option (Option (List ℚ × List (LC (m + 1)))) :=
  exactTLVGW Fc ks m η rde (dgOfR m c.1.2) c.1.1.2.2.2.2.2.2.2.2.1 c.1.1.2.2.2.2.2.2.2.2.2
    (fun i ↦ c.1.1.2.2.2.2.2.2.2.1.getD i 0) (nkPC Fc ks m Pp) c.1.1.2.2.2.2.2.1 c.1.1.2.2.2.2.2.2.1 f
    c.1.1.2.2.1

lemma ivmExW_isSomeD (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (f : List (LC (m + 1))) (c : CandIVRD m) :
    (ivmExWD Fc ks m η rde Pp f c).map Option.isSome = ivmExD Fc ks m η rde Pp f c :=
  exactTLVGW_isSome _ _ _ _ _ _ _ _ _ _ _ _ _ _

lemma searchIVMP_eqD (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandIVRD m)) (B : ℕ) :
    searchIVMPD Fc ks m η rde Pp np dθ wθ s f pre B =
      searchPS (ivmCondD Fc ks m Pp np dθ wθ s) (ivmExD Fc ks m η rde Pp f) pre B := by
  have ht : ivmTryD Fc ks m η rde Pp np dθ wθ s f =
      tryS (ivmCondD Fc ks m Pp np dθ wθ s) (ivmExD Fc ks m η rde Pp f) := funext fun _ ↦ rfl
  have hs : searchIVMD Fc ks m η rde Pp np dθ wθ s f B =
      searchS (ivmCondD Fc ks m Pp np dθ wθ s) (ivmExD Fc ks m η rde Pp f) B := by
    unfold searchIVMD searchS
    congr 1
    funext k
    cases (Encodable.decode k : Option (CandIVRD m)) with
    | none => rfl
    | some c => exact congrFun ht c
  unfold searchIVMPD searchPS
  rw [ht, hs]
  generalize List.findSome? (tryS (ivmCondD Fc ks m Pp np dθ wθ s) (ivmExD Fc ks m η rde Pp f)) pre = o
  cases o <;> rfl

/-- **The constructive decision** (several slopes, logarithmic level). -/
def nkInfVMRWD (m : ℕ) (η : LC m) (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (pre : List (CandIVRD m)) (N : ℕ) :=
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N)
    (searchPW (ivmCondD Fc ks m Pp np dθ wθ s) (ivmExWD Fc ks m η (prdeC Fc ks lv m) Pp
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) pre N)

/-- The checks on a candidate (several slopes, exponential level). -/
def etvmCondD (m : ℕ) (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (c : CandETVRD m) : Bool :=
  decide (c.1.1.2.2.1.length + 1 = np) &&
      unitsCD Fc ks m Pp c.1.1.1 c.1.1.2.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 c.1.1.2.2.1 dθ wθ s &&
      indepC Fc ks m c.1.1.2.2.1 c.1.1.2.2.2.1 c.1.1.2.2.2.2.1

lemma searchETVMP_eqD (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (f : List (LC (m + 1))) (pre : List (CandETVRD m)) (B : ℕ) :
    searchETVMPD Fc ks m a rde Pp np dθ wθ s f pre B =
      searchPS (etvmCondD Fc ks m Pp np dθ wθ s) (etvrExD Fc ks m a rde Pp f) pre B := by
  have ht : etvmTryD Fc ks m a rde Pp np dθ wθ s f =
      tryS (etvmCondD Fc ks m Pp np dθ wθ s) (etvrExD Fc ks m a rde Pp f) := funext fun _ ↦ rfl
  have hs : searchETVMD Fc ks m a rde Pp np dθ wθ s f B =
      searchS (etvmCondD Fc ks m Pp np dθ wθ s) (etvrExD Fc ks m a rde Pp f) B := by
    unfold searchETVMD searchS
    congr 1
    funext k
    cases (Encodable.decode k : Option (CandETVRD m)) with
    | none => rfl
    | some c => exact congrFun ht c
  unfold searchETVMPD searchPS
  rw [ht, hs]
  generalize List.findSome? (tryS (etvmCondD Fc ks m Pp np dθ wθ s) (etvrExD Fc ks m a rde Pp f)) pre = o
  cases o <;> rfl

/-- **The constructive decision** (several slopes, exponential level). -/
def nkETVMRWD (m : ℕ) (a : LC m) (Pp : List (GPoly (LC m))) (np : ℕ) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (pre : List (CandETVRD m)) (N : ℕ) :=
  combineW (elMW Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N)
    (searchPW (etvmCondD Fc ks m Pp np dθ wθ s) (etvrExWD Fc ks m a (prdeC Fc ks lv m) Pp
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) pre N)

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **`nk_decidesInfVMRD` without an independence certificate.** -/
theorem nk_decidesInfVMRPWD (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
      (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = nPlacesR segs ∧ unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandIVRD m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchIVMPD Fc ks m η (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  obtain ⟨Us, Vs, ds, cUs, cVs, Es, gls, hk1, hU, hli⟩ := hunits
  have hTr : T.Tr (m + 1) := (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr
  obtain ⟨J, D, H, -, hJH⟩ := T.indepWC_exists_of_logs m hTr θ Pp.length gls
    (fun i hi ↦ (unitsCD_spec hU i hi).2.2.1) (hli hTr)
  exact T.nk_decidesInfVMRD hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms θ hθ
    hgen dθ wθ s hs ⟨Us, Vs, ds, cUs, cVs, Es, gls, J ++ D, H, hk1, hU, hJH⟩ fp pre

/-- **`nk_decidesETInfVMRD` without an independence certificate.** -/
theorem nk_decidesETInfVMRPWD (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
      (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = nPlacesR segs ∧ unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandETVRD m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      searchETVMPD Fc ks m a (prdeC Fc ks lv m) Pp (nPlacesR segs) dθ wθ s
        (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) pre N =
          some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  obtain ⟨Us, Vs, ds, cUs, cVs, Es, gls, hk1, hU, hli⟩ := hunits
  have hTr : T.Tr (m + 1) := (T.mspecs hmon hdeg lv (m + 1) (by omega) hc).hyp.tr
  obtain ⟨J, D, H, -, hJH⟩ := T.indepWC_exists_of_logs m hTr θ Pp.length gls
    (fun i hi ↦ (unitsCD_spec hU i hi).2.2.1) (hli hTr)
  exact T.nk_decidesETInfVMRD hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms hsh0
    θ hθ hgen dθ wθ s hs ⟨Us, Vs, ds, cUs, cVs, Es, gls, J ++ D, H, hk1, hU, hJH⟩ fp pre

lemma pos_of_multiShapeRCD (m : ℕ) (Pp : List (GPoly (LC m))) (segs : List (SegRC m))
    (hms : multiShapeRC Fc ks m Pp segs = true) : 0 < Pp.length := by
  unfold multiShapeRC at hms
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hms
  exact hms.1.1.1.1



/-- **The integral with several slopes at infinity (logarithmic level), decided and computed.** -/
theorem nk_integrateInfVMRPWD (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
      (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = nPlacesR segs ∧ unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandIVRD m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkInfVMRWD Fc ks lv m η Pp (nPlacesR segs) dθ wθ s fp pre N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExpl m h1 θ Pp fp s
          (fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (b.1.1.1.1.getD i [])) / T.evP m (b.1.2.1.getD i [])) b.1.1.1.2.2.1.length b.2 := by
  have hn0 := pos_of_multiShapeRCD m Pp segs hms
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦
      (searchPW_isSome _ _ _ (ivmExW_isSomeD Fc ks m η _ Pp _) pre N).trans
        (searchIVMP_eqD Fc ks m η _ Pp (nPlacesR segs) dθ wθ s _ pre N).symm)
    _ (T.nk_decidesInfVMRPWD hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms
      θ hθ hgen dθ wθ s hs hunits fp pre) _ fun N w hw h1 ↦ ?_
  obtain ⟨hcd, hex⟩ := searchPW_src _ _ pre N w hw
  simp only [ivmCondD, Bool.and_eq_true, decide_eq_true_eq] at hcd
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
    (T.units_logsD m h1 θ Pp hP _ _ _ _ _ _ _ dθ wθ s hcd.1.2)
    (fun i hi ↦ (unitsCD_spec hcd.1.2 i hi).2.2.1) fp s w.2 hY

/-- **The integral with several slopes at infinity (exponential level), decided and computed.** -/
theorem nk_integrateETInfVMRPWD (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
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
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
      (gls : List (GPoly (LC (m + 1)))),
      gls.length + 1 = nPlacesR segs ∧ unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true ∧
      ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
        (∀ i, (c i)′ = 0) →
        (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0)
    (fp : List (GPoly (LC m))) (pre : List (CandETVRD m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, nkETVMRWD Fc ks lv m a Pp (nPlacesR segs) dθ wθ s fp pre N = some o ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        o.isSome) ∧
      ∀ w b, o = some (w, b) → T.ValidW (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) w ∧
        ∀ h1 : T.Tr (m + 1), T.NKExpl m h1 θ Pp fp s
          (fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (b.1.1.1.1.getD i [])) / T.evP m (b.1.2.1.getD i [])) b.1.1.1.2.2.1.length b.2 := by
  have hn0 := pos_of_multiShapeRCD m Pp segs hms
  refine T.nk_integrate_core hmon hdeg hshF m hn hc
    (T.elem0_of_curve hmon hdeg m hn hc Pp θ hθ hgen) _ _ _ (fun N ↦
      (searchPW_isSome _ _ _ (etvrExW_isSomeD Fc ks m a _ Pp _) pre N).trans
        (searchETVMP_eqD Fc ks m a _ Pp (nPlacesR segs) dθ wθ s _ pre N).symm)
    _ (T.nk_decidesETInfVMRPWD hmon hdeg hshF m hn hc hk Pp qE csE sE tE s2E t2E hck segs hms
      hsh0 θ hθ hgen dθ wθ s hs hunits fp pre) _ fun N w hw h1 ↦ ?_
  obtain ⟨hcd, hex⟩ := searchPW_src _ _ pre N w hw
  simp only [etvmCondD, Bool.and_eq_true, decide_eq_true_eq] at hcd
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [length_nkPC]; exact T.nkCurveE_ind m h1 Pp qE csE sE tE s2E t2E hck θ hθ
  obtain ⟨hrde, hom⟩ := T.expTEV_specs hmon hdeg m hn hc hk
  have hY := T.exactTLEVGW_valid m h1 (by omega) hk (h1 m (by omega)) _ hrde hom _ _ _ _ _ _ _
    (nkPC Fc ks m Pp) _ θ hP hind _ _ _ w.2 hex
  exact T.nk_explicit_core m h1 Pp hn0 θ _ _
    (T.units_logsD m h1 θ Pp hP _ _ _ _ _ _ _ dθ wθ s hcd.1.2)
    (fun i hi ↦ (unitsCD_spec hcd.1.2 i hi).2.2.1) fp s w.2 hY

end MTower

end Curves.MT

