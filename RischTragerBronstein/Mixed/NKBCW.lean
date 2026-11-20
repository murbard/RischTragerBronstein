import RischTragerBronstein.Mixed.NKBCMR
import RischTragerBronstein.Mixed.NKMultiRWit
import RischTragerBronstein.Mixed.NKIndepPW

/-!
# Changing the base curve with the antiderivative

`bc_integrates`: `bc_decides` for constructive procedures — the witness is valid for a tower `T'`
on the new base curve over an algebraic extension `L'` of `L`, in which the translated codes have
the values of the original ones. Instances: `nk_integrateInfVMR_bc` (several slopes at infinity,
logarithmic level).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

set_option maxHeartbeats 8000000 in
/-- **Transfer of a constructive decision through a change of base curve**: if, over every tower
`T'` on the new base curve, a procedure `W` decides the translated integral with a witness valid
for `T'` (`V`), then it decides the original one, the witness being valid for a tower `T'` over an
algebraic extension `L'` of `L` (with the values of the translated codes). -/
theorem bc_integrates [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
    (Q : GPoly (LC 0)) [Fact (Irreducible (toPoly (qK Fc Q)))]
    (Fc' : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc')))] (Yc : GPoly (GFrac ℚ))
    (hbc : bcOK Fc Q Fc' Yc = true)
    (hmon' : (toB Fc').Monic) (hlen' : (toB Fc').natDegree = Fc'.length - 1)
    (hd' : 0 < (toB Fc').natDegree) (hgeo : GeomIrr.{u} Fc')
    (m : ℕ) (hn : T.n = m + 1) (Pp fp : List (GPoly (LC m))) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    {X : Type*} (W : ℕ → Option (Option X))
    (V : ∀ {Cc' L' : Type u} [Field Cc'] [Field L'] [Algebra Cc' L'] [Differential Cc']
      [Differential L'] [DifferentialAlgebra Cc' L'] [CharZero Cc'] [CharZero L'],
      MTower Fc' (tauK Fc' Yc ks) Cc' L' → L' → Option X → Prop)
    (H : ∀ {Cc' L' : Type u} [Field Cc'] [Field L'] [Algebra Cc' L'] [Differential Cc']
      [Differential L'] [DifferentialAlgebra Cc' L'] [CharZero Cc'] [CharZero L']
      (T' : MTower Fc' (tauK Fc' Yc ks) Cc' L'), T'.n = m + 1 → ∀ θ' : L',
      θ' ^ Pp.length + ∑ i ∈ Finset.range Pp.length,
        T'.evP m ((Pp.map (·.map (tauC Fc' Yc m))).getD i []) * θ' ^ i = 0 →
      (∀ z : L', z ∈ IntermediateField.adjoin (T'.F (m + 1)) {θ'}) →
      ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, W N = some o ∧
        (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length,
          T'.evP m ((fp.map (·.map (tauC Fc' Yc m))).getD j []) * θ' ^ j) ↔ o.isSome) ∧
        V T' θ' o) :
    ∃ (L' : Type u) (_ : Field L') (_ : Differential L') (_ : CharZero L') (_ : Algebra L L')
      (_ : DifferentialAlgebra L L') (T' : MTower Fc' (tauK Fc' Yc ks) (constants L') L'),
      (∀ m q, T'.ev m (tauC Fc' Yc m q) = algebraMap L L' (T.ev m q)) ∧
      ∃ N₀, ∀ N, N₀ ≤ N → ∃ o, W N = some o ∧
        (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
          o.isSome) ∧ V T' (algebraMap L L' θ) o := by
  classical
  obtain ⟨L', _, _, _, _, _, halg, T', hTn, hts, hev, hmem, hgenw⟩ :=
    T.base_change Q Fc' Yc hbc hmon' hlen' hd' hgeo
  set ι := algebraMap L L' with hι
  have hevP : ∀ A : GPoly (LC m), T'.evP m (A.map (tauC Fc' Yc m)) = ι (T.evP m A) := by
    intro A
    have h0 : ∀ a, (cM T'.hC T'.S T'.hx Fc' T'.hSF).sem (tau0 Fc' Yc a) =
        ι ((cM T.hC T.S T.hx Fc T.hSF).sem a) := fun a ↦ hev 0 a
    have hts' : T'.ts = fun i ↦ ι (T.ts i) := funext hts
    show evPL _ T'.ts m _ = _
    rw [hts']
    exact evPL_tau Fc' Yc ι _ _ h0 T.ts m A
  have hgetD : ∀ (W : List (GPoly (LC m))) (i : ℕ),
      (W.map (·.map (tauC Fc' Yc m))).getD i [] = (W.getD i []).map (tauC Fc' Yc m) := by
    intro W i
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
    cases W[i]? <;> rfl
  have hθ' : (ι θ) ^ Pp.length + ∑ i ∈ Finset.range Pp.length,
      T'.evP m ((Pp.map (·.map (tauC Fc' Yc m))).getD i []) * (ι θ) ^ i = 0 := by
    simp only [hgetD, hevP, ← map_pow, ← map_mul, ← map_sum, ← map_add, hθ, map_zero]
  have hgen' : ∀ z : L', z ∈ IntermediateField.adjoin (T'.F (m + 1)) {ι θ} := by
    set K := IntermediateField.adjoin (T'.F (m + 1)) {ι θ} with hK
    have hLK : ∀ r : L, ι r ∈ K := by
      intro r
      have hr := hgen r
      induction hr using IntermediateField.adjoin_induction with
      | mem w hw =>
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact mem_adjoin_simple_self _ _
      | algebraMap w =>
        exact IntermediateField.algebraMap_mem K (⟨ι w, hmem (m + 1) _ w.2⟩ : T'.F (m + 1))
      | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
      | mul w₁ w₂ _ _ h₁ h₂ => rw [map_mul]; exact mul_mem h₁ h₂
      | inv w _ h₁ => rw [map_inv₀]; exact inv_mem h₁
    let K' : IntermediateField L L' :=
      { K.toSubfield with algebraMap_mem' := hLK }
    have hy : T'.S.y ∈ K := by
      have h0 : T'.S.y ∈ T'.F 0 := by
        have := T'.ev_mem 0 yCode
        rwa [show T'.ev 0 yCode = T'.S.y from sem_yCode T'.hC T'.S T'.hx Fc' T'.hSF] at this
      exact IntermediateField.algebraMap_mem K
        (⟨T'.S.y, T'.F_mono (Nat.zero_le _) h0⟩ : T'.F (m + 1))
    have hle : IntermediateField.adjoin L {T'.S.y} ≤ K' := by
      rw [IntermediateField.adjoin_le_iff]
      rintro w rfl
      exact hy
    intro z
    have hz : z ∈ K' := hle (hgenw z)
    exact hz
  obtain ⟨N₀, hN₀⟩ := H T' (by rw [hTn, hn]) (ι θ) hθ' hgen'
  refine ⟨L', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, T', hev,
    N₀, fun N hN ↦ ?_⟩
  obtain ⟨o, hW, hiff, hV⟩ := hN₀ N hN
  refine ⟨o, hW, ?_, hV⟩
  have hf : (∑ j ∈ Finset.range Pp.length,
      T'.evP m ((fp.map (·.map (tauC Fc' Yc m))).getD j []) * (ι θ) ^ j) =
      ι (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) := by
    simp only [hgetD, hevP, map_sum, map_mul, map_pow]
  rw [hf] at hiff
  rw [← hiff]
  exact ⟨HasElementaryIntegral.to_isAlgebraic halg, HasElementaryIntegral.of_isAlgebraic halg⟩


set_option maxHeartbeats 8000000 in
/-- **`nk_integrateInfVMRPW` over a new base curve**: several slopes at infinity whose places
become rational after the change of base curve; the antiderivative lives in a tower `T'` over the
new base, in an algebraic extension of `L`. -/
theorem nk_integrateInfVMR_bc [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
    (Q : GPoly (LC 0)) [Fact (Irreducible (toPoly (qK Fc Q)))]
    (Fc' : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc')))] (Yc : GPoly (GFrac ℚ))
    (hbc : bcOK Fc Q Fc' Yc = true)
    (hmon' : (toB Fc').Monic) (hlen' : (toB Fc').natDegree = Fc'.length - 1)
    (hd' : 0 < (toB Fc').natDegree) (hgeo : GeomIrr.{u} Fc')
    (hdeg' : (toB Fc').natDegree = cvN Fc') (hshF' : curveShape Fc' = true)
    (lv' : (m : ℕ) → LC m)
    (m : ℕ) (hn : T.n = m + 1) (hc' : certC Fc' (tauK Fc' Yc ks) lv' (m + 1) = true)
    {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m))
    (hck : eisCk Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) qE csE sE tE s2E t2E = true)
    (segs : List (SegRC m))
    (hms : multiShapeRC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) segs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s = true)
    (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1)))) (J : List ℕ)
    (H : List (List (LC (m + 1)))) (hk1 : gls.length + 1 = nPlacesR segs)
    (hU : unitsC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) Us Vs gls dθ wθ s = true)
    (hJH : indepC Fc' (tauK Fc' Yc ks) m gls J H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandIVR m)) :
    ∃ (L' : Type u) (_ : Field L') (_ : Differential L') (_ : CharZero L') (_ : Algebra L L')
      (_ : DifferentialAlgebra L L') (T' : MTower Fc' (tauK Fc' Yc ks) (constants L') L'),
      (∀ m q, T'.ev m (tauC Fc' Yc m q) = algebraMap L L' (T.ev m q)) ∧
      ∃ N₀, ∀ N, N₀ ≤ N → ∃ o,
        nkInfVMRW Fc' (tauK Fc' Yc ks) lv' m (tauC Fc' Yc m η) (Pp.map (·.map (tauC Fc' Yc m)))
          (nPlacesR segs) dθ wθ s (fp.map (·.map (tauC Fc' Yc m))) pre N = some o ∧
        (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
          o.isSome) ∧
        ∀ w b, o = some (w, b) →
          T'.ValidW (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))).length
            (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) w ∧
          ∀ h1 : T'.Tr (m + 1), T'.NKExpl m h1 (algebraMap L L' θ) (Pp.map (·.map (tauC Fc' Yc m)))
            (fp.map (·.map (tauC Fc' Yc m))) s
            (fun i ↦ T'.evθ m h1 (algebraMap L L' θ)
              (nkFl Fc' (tauK Fc' Yc ks) m (b.1.1.1.getD i []))) b.1.1.2.2.1.length b.2 := by
  have hk' : tauK Fc' Yc ks m = .prim (tauC Fc' Yc m η) := by unfold tauK; rw [hk]
  have hn0 : 0 < (Pp.map (·.map (tauC Fc' Yc m))).length := by
    unfold multiShapeRC at hms
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hms
    exact hms.1.1.1.1
  have key := T.bc_integrates Q Fc' Yc hbc hmon' hlen' hd' hgeo m hn Pp fp θ hθ hgen
    (nkInfVMRW Fc' (tauK Fc' Yc ks) lv' m (tauC Fc' Yc m η) (Pp.map (·.map (tauC Fc' Yc m)))
      (nPlacesR segs) dθ wθ s (fp.map (·.map (tauC Fc' Yc m))) pre)
    (fun {Cc' L'} _ _ _ _ _ _ _ _ T' θ' o ↦ ∀ w b, o = some (w, b) →
      T'.ValidW (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))).length
        (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) w ∧
      ∀ h1 : T'.Tr (m + 1), T'.NKExpl m h1 θ' (Pp.map (·.map (tauC Fc' Yc m)))
        (fp.map (·.map (tauC Fc' Yc m))) s
        (fun i ↦ T'.evθ m h1 θ' (nkFl Fc' (tauK Fc' Yc ks) m (b.1.1.1.getD i [])))
        b.1.1.2.2.1.length b.2)
    (fun {Cc' L'} _ _ _ _ _ _ _ _ T' hTn θ' hθ' hgen' ↦ by
      have hθ'' : θ' ^ (Pp.map (·.map (tauC Fc' Yc m))).length +
          ∑ i ∈ Finset.range (Pp.map (·.map (tauC Fc' Yc m))).length,
          T'.evP m ((Pp.map (·.map (tauC Fc' Yc m))).getD i []) * θ' ^ i = 0 := by
        rw [List.length_map]; exact hθ'
      have hli := T'.hli_of_indepC m _ hn0 θ' hθ''
        (fun h1 ↦ T'.nkCurveE_ind m h1 _ qE csE sE tE s2E t2E hck θ' hθ'') Us Vs gls dθ wθ s hs hU J H hJH
      obtain ⟨N₀, hN₀⟩ := T'.nk_integrateInfVMRPW hmon' hdeg' hshF' m hTn hc' hk'
        _ qE csE sE tE s2E t2E hck segs hms θ' hθ'' hgen' dθ wθ s hs
        ⟨Us, Vs, gls, hk1, hU, hli⟩ (fp.map (·.map (tauC Fc' Yc m))) pre
      refine ⟨N₀, fun N hN ↦ ?_⟩
      obtain ⟨o, h1, h2, h3⟩ := hN₀ N hN
      rw [List.length_map] at h2
      exact ⟨o, h1, h2, h3⟩)
  exact key

end MTower

end Curves.MT
