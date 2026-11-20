import RischTragerBronstein.Mixed.KBMain
import RischTragerBronstein.Mixed.NKSplit0Cand
import RischTragerBronstein.Mixed.NKRamCand

/-!
# Non-rational places through a change of the base curve

A place at infinity or above `t = 0` whose residue field is `Fₘ(β)` with `β` algebraic over the base
field `F₀` becomes rational after changing the base curve to one whose function field contains `β`
(`MTower.base_change`, `Mixed/KBLift`): the curve `θⁿ + ∑ aᵢ θⁱ` is translated (`tauC`) and the
deciders run over the new tower `T'`; elementary integrability transfers along the algebraic
extension `L ⊆ L'` (`HasElementaryIntegral.of_isAlgebraic`, `to_isAlgebraic`).

**`nk_decidesETInf0P_bc`**: `nk_decidesETInf0P` over the base-changed tower decides the original
integral. Example (`Mixed/NKBCExamples`): `√(e²ˣ + x eˣ + x)`, fibre `θ² = x` above `t = 0`, base
curve `w² = x`.
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
/-- **Transfer of a decision through a change of base curve**: if, over every tower `T'` on the new
base curve, a code-level procedure `D` decides the translated integral, then it decides the
original one. -/
theorem bc_decides [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
    (Q : GPoly (LC 0)) [Fact (Irreducible (toPoly (qK Fc Q)))]
    (Fc' : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc')))] (Yc : GPoly (GFrac ℚ))
    (hbc : bcOK Fc Q Fc' Yc = true)
    (hmon' : (toB Fc').Monic) (hlen' : (toB Fc').natDegree = Fc'.length - 1)
    (hd' : 0 < (toB Fc').natDegree) (hgeo : GeomIrr.{u} Fc')
    (m : ℕ) (hn : T.n = m + 1) (Pp fp : List (GPoly (LC m))) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (D : ℕ → Bool → Bool → Prop)
    (H : ∀ {Cc' L' : Type u} [Field Cc'] [Field L'] [Algebra Cc' L'] [Differential Cc']
      [Differential L'] [DifferentialAlgebra Cc' L'] [CharZero Cc'] [CharZero L']
      (T' : MTower Fc' (tauK Fc' Yc ks) Cc' L'), T'.n = m + 1 → ∀ θ' : L',
      θ' ^ Pp.length + ∑ i ∈ Finset.range Pp.length,
        T'.evP m ((Pp.map (·.map (tauC Fc' Yc m))).getD i []) * θ' ^ i = 0 →
      (∀ z : L', z ∈ IntermediateField.adjoin (T'.F (m + 1)) {θ'}) →
      ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res, D N b res ∧
        (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length,
          T'.evP m ((fp.map (·.map (tauC Fc' Yc m))).getD j []) * θ' ^ j) ↔
          res = true ∧ b = true)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res, D N b res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
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
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, res, hD, hiff⟩ := hN₀ N hN
  refine ⟨b, res, hD, ?_⟩
  have hf : (∑ j ∈ Finset.range Pp.length,
      T'.evP m ((fp.map (·.map (tauC Fc' Yc m))).getD j []) * (ι θ) ^ j) =
      ι (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) := by
    simp only [hgetD, hevP, map_sum, map_mul, map_pow]
  rw [hf] at hiff
  rw [← hiff]
  exact ⟨HasElementaryIntegral.to_isAlgebraic halg, HasElementaryIntegral.of_isAlgebraic halg⟩

set_option maxHeartbeats 8000000 in
/-- **The split decider at an exponential level over a new base curve.** -/
theorem nk_decidesETInf0P_bc [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
    (Q : GPoly (LC 0)) [Fact (Irreducible (toPoly (qK Fc Q)))]
    (Fc' : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc')))] (Yc : GPoly (GFrac ℚ))
    (hbc : bcOK Fc Q Fc' Yc = true)
    (hmon' : (toB Fc').Monic) (hlen' : (toB Fc').natDegree = Fc'.length - 1)
    (hd' : 0 < (toB Fc').natDegree) (hgeo : GeomIrr.{u} Fc')
    (hdeg' : (toB Fc').natDegree = cvN Fc') (hshF' : curveShape Fc' = true)
    (lv' : (m : ℕ) → LC m)
    (m : ℕ) (hn : T.n = m + 1) (hc' : certC Fc' (tauK Fc' Yc ks) lv' (m + 1) = true)
    {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m))
    (hck : eisCk Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) qE csE sE tE s2E t2E =
      true)
    (sp : ℕ) (γs : List (LC m))
    (hsplit : splitShapeC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) sp γs = true)
    (βs : List (LC m))
    (hsp0 : split0C Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) βs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ)
      (gls : List (GPoly (LC (m + 1)))) (J D : List ℕ) (H : List (List (LC (m + 1)))),
      gls.length + 2 = 2 * Pp.length ∧
      unitsC0 Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) Us Vs kk jj
        ((MO Fc' (tauK Fc' Yc ks) m).deriv (tauC Fc' Yc m a)) gls dθ wθ s = true ∧
      indepWC Fc' (tauK Fc' Yc ks) m gls J D H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandET0 m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      elM Fc' (tauK Fc' Yc ks) lv' (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m Pp.length
        (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) N = some b ∧
      searchET0P Fc' (tauK Fc' Yc ks) m (tauC Fc' Yc m a) (prdeC Fc' (tauK Fc' Yc ks) lv' m)
        (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s
        (nkRest Fc' (tauK Fc' Yc ks) m (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m))))
          (nkTau Fc' (tauK Fc' Yc ks) m Pp.length
            (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s)) pre N = some res ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
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
  have hlenP : (Pp.map (·.map (tauC Fc' Yc m))).length = Pp.length := List.length_map _
  have hθ' : (ι θ) ^ (Pp.map (·.map (tauC Fc' Yc m))).length +
      ∑ i ∈ Finset.range (Pp.map (·.map (tauC Fc' Yc m))).length,
        T'.evP m ((Pp.map (·.map (tauC Fc' Yc m))).getD i []) * (ι θ) ^ i = 0 := by
    rw [hlenP]
    simp only [hgetD, hevP, ← map_pow, ← map_mul, ← map_sum, ← map_add, hθ, map_zero]
  have hk' : tauK Fc' Yc ks m = .exp (tauC Fc' Yc m a) := by
    unfold tauK; rw [hk]
  -- `L'` is generated by `T'`'s levels and `θ`
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
  rw [← hlenP] at hunits
  obtain ⟨N₀, hN₀⟩ := T'.nk_decidesETInf0P hmon' hdeg' hshF' m (by rw [hTn, hn]) hc' hk'
    (Pp.map (·.map (tauC Fc' Yc m))) qE csE sE tE s2E t2E hck sp γs hsplit βs hsp0 (ι θ) hθ' hgen'
    dθ wθ s hs hunits (fp.map (·.map (tauC Fc' Yc m))) pre
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, res, hb, hres, hiff⟩ := hN₀ N hN
  rw [hlenP] at hb hres hiff
  refine ⟨b, res, hb, hres, ?_⟩
  have hf : (∑ j ∈ Finset.range Pp.length,
      T'.evP m ((fp.map (·.map (tauC Fc' Yc m))).getD j []) * (ι θ) ^ j) =
      ι (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) := by
    simp only [hgetD, hevP, map_sum, map_mul, map_pow]
  rw [hf] at hiff
  rw [← hiff]
  exact ⟨HasElementaryIntegral.to_isAlgebraic halg, HasElementaryIntegral.of_isAlgebraic halg⟩

set_option maxHeartbeats 8000000 in
/-- **`nk_decidesInfVGP` over a new base curve** (`bc_decides`). -/
theorem nk_decidesInfVGP_bc [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
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
    (sp : ℕ) (γs : List (LC m)) (hsplit : splitShapeC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) sp γs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
      (J : List ℕ) (H : List (List (LC (m + 1)))), gls.length + 1 = Pp.length ∧
      unitsC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) Us Vs gls dθ wθ s = true ∧ indepC Fc' (tauK Fc' Yc ks) m gls J H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandIVG m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      (elM Fc' (tauK Fc' Yc ks) lv' (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m Pp.length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) N = some b ∧
      searchIVGP Fc' (tauK Fc' Yc ks) m (tauC Fc' Yc m η) (prdeC Fc' (tauK Fc' Yc ks) lv' m) (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s
        (nkRest Fc' (tauK Fc' Yc ks) m (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m))))
          (nkTau Fc' (tauK Fc' Yc ks) m Pp.length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s)) pre N = some res) ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  have hk' : tauK Fc' Yc ks m = .prim (tauC Fc' Yc m η) := by unfold tauK; rw [hk]
  refine T.bc_decides Q Fc' Yc hbc hmon' hlen' hd' hgeo m hn Pp fp θ hθ hgen _ ?_
  intro Cc' L' _ _ _ _ _ _ _ _ T' hTn θ' hθ' hgen'
  have hθ'' : θ' ^ (Pp.map (·.map (tauC Fc' Yc m))).length + ∑ i ∈ Finset.range (Pp.map (·.map (tauC Fc' Yc m))).length,
      T'.evP m ((Pp.map (·.map (tauC Fc' Yc m))).getD i []) * θ' ^ i = 0 := by rw [List.length_map]; exact hθ'
  have hunits' := hunits
  rw [← List.length_map (f := (·.map (tauC Fc' Yc m))) (as := Pp)] at hunits'
  obtain ⟨N₀, hN₀⟩ := T'.nk_decidesInfVGP hmon' hdeg' hshF' m hTn hc' hk' (Pp.map (·.map (tauC Fc' Yc m))) qE csE sE tE s2E t2E hck
    sp γs hsplit θ' hθ'' hgen' dθ wθ s hs hunits' (fp.map (·.map (tauC Fc' Yc m))) pre
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, res, h1, h2, h3⟩ := hN₀ N hN
  rw [List.length_map] at h1 h2 h3
  exact ⟨b, res, ⟨h1, h2⟩, h3⟩

set_option maxHeartbeats 8000000 in
/-- **`nk_decidesETInfVGP` over a new base curve** (`bc_decides`). -/
theorem nk_decidesETInfVGP_bc [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
    (Q : GPoly (LC 0)) [Fact (Irreducible (toPoly (qK Fc Q)))]
    (Fc' : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc')))] (Yc : GPoly (GFrac ℚ))
    (hbc : bcOK Fc Q Fc' Yc = true)
    (hmon' : (toB Fc').Monic) (hlen' : (toB Fc').natDegree = Fc'.length - 1)
    (hd' : 0 < (toB Fc').natDegree) (hgeo : GeomIrr.{u} Fc')
    (hdeg' : (toB Fc').natDegree = cvN Fc') (hshF' : curveShape Fc' = true)
    (lv' : (m : ℕ) → LC m)
    (m : ℕ) (hn : T.n = m + 1) (hc' : certC Fc' (tauK Fc' Yc ks) lv' (m + 1) = true)
    {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m))
    (hck : eisCk Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) qE csE sE tE s2E t2E = true)
    (sp : ℕ) (γs : List (LC m)) (hsplit : splitShapeC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) sp γs = true)
    (hsh0 : nkShape0 Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
      (J : List ℕ) (H : List (List (LC (m + 1)))), gls.length + 1 = Pp.length ∧
      unitsC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) Us Vs gls dθ wθ s = true ∧ indepC Fc' (tauK Fc' Yc ks) m gls J H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandETVG m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      (elM Fc' (tauK Fc' Yc ks) lv' (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m Pp.length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) N = some b ∧
      searchETVGP Fc' (tauK Fc' Yc ks) m (tauC Fc' Yc m a) (prdeC Fc' (tauK Fc' Yc ks) lv' m) (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s
        (nkRest Fc' (tauK Fc' Yc ks) m (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m))))
          (nkTau Fc' (tauK Fc' Yc ks) m Pp.length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s)) pre N = some res) ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  have hk' : tauK Fc' Yc ks m = .exp (tauC Fc' Yc m a) := by unfold tauK; rw [hk]
  refine T.bc_decides Q Fc' Yc hbc hmon' hlen' hd' hgeo m hn Pp fp θ hθ hgen _ ?_
  intro Cc' L' _ _ _ _ _ _ _ _ T' hTn θ' hθ' hgen'
  have hθ'' : θ' ^ (Pp.map (·.map (tauC Fc' Yc m))).length + ∑ i ∈ Finset.range (Pp.map (·.map (tauC Fc' Yc m))).length,
      T'.evP m ((Pp.map (·.map (tauC Fc' Yc m))).getD i []) * θ' ^ i = 0 := by rw [List.length_map]; exact hθ'
  have hunits' := hunits
  rw [← List.length_map (f := (·.map (tauC Fc' Yc m))) (as := Pp)] at hunits'
  obtain ⟨N₀, hN₀⟩ := T'.nk_decidesETInfVGP hmon' hdeg' hshF' m hTn hc' hk' (Pp.map (·.map (tauC Fc' Yc m))) qE csE sE tE s2E t2E hck
    sp γs hsplit hsh0 θ' hθ'' hgen' dθ wθ s hs hunits' (fp.map (·.map (tauC Fc' Yc m))) pre
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, res, h1, h2, h3⟩ := hN₀ N hN
  rw [List.length_map] at h1 h2 h3
  exact ⟨b, res, ⟨h1, h2⟩, h3⟩

set_option maxHeartbeats 8000000 in
/-- **`nk_decidesInfVRP` over a new base curve** (`bc_decides`). -/
theorem nk_decidesInfVRP_bc [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
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
    (e sR : ℕ) (γs : List (LC m)) (hram : ramShapeC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) e sR γs = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
      (J : List ℕ) (H : List (List (LC (m + 1)))), gls.length + 1 = Pp.length / e ∧
      unitsC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) Us Vs gls dθ wθ s = true ∧ indepC Fc' (tauK Fc' Yc ks) m gls J H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandIVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      (elM Fc' (tauK Fc' Yc ks) lv' (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m Pp.length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) N = some b ∧
      searchIVRP Fc' (tauK Fc' Yc ks) m (tauC Fc' Yc m η) (prdeC Fc' (tauK Fc' Yc ks) lv' m) (Pp.map (·.map (tauC Fc' Yc m))) e dθ wθ s
        (nkRest Fc' (tauK Fc' Yc ks) m (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m))))
          (nkTau Fc' (tauK Fc' Yc ks) m Pp.length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s)) pre N = some res) ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  have hk' : tauK Fc' Yc ks m = .prim (tauC Fc' Yc m η) := by unfold tauK; rw [hk]
  refine T.bc_decides Q Fc' Yc hbc hmon' hlen' hd' hgeo m hn Pp fp θ hθ hgen _ ?_
  intro Cc' L' _ _ _ _ _ _ _ _ T' hTn θ' hθ' hgen'
  have hθ'' : θ' ^ (Pp.map (·.map (tauC Fc' Yc m))).length + ∑ i ∈ Finset.range (Pp.map (·.map (tauC Fc' Yc m))).length,
      T'.evP m ((Pp.map (·.map (tauC Fc' Yc m))).getD i []) * θ' ^ i = 0 := by rw [List.length_map]; exact hθ'
  have hunits' := hunits
  rw [← List.length_map (f := (·.map (tauC Fc' Yc m))) (as := Pp)] at hunits'
  obtain ⟨N₀, hN₀⟩ := T'.nk_decidesInfVRP hmon' hdeg' hshF' m hTn hc' hk' (Pp.map (·.map (tauC Fc' Yc m))) qE csE sE tE s2E t2E hck
    e sR γs hram θ' hθ'' hgen' dθ wθ s hs hunits' (fp.map (·.map (tauC Fc' Yc m))) pre
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, res, h1, h2, h3⟩ := hN₀ N hN
  rw [List.length_map] at h1 h2 h3
  exact ⟨b, res, ⟨h1, h2⟩, h3⟩

set_option maxHeartbeats 8000000 in
/-- **`nk_decidesETInfVRP` over a new base curve** (`bc_decides`). -/
theorem nk_decidesETInfVRP_bc [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L)
    (Q : GPoly (LC 0)) [Fact (Irreducible (toPoly (qK Fc Q)))]
    (Fc' : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc')))] (Yc : GPoly (GFrac ℚ))
    (hbc : bcOK Fc Q Fc' Yc = true)
    (hmon' : (toB Fc').Monic) (hlen' : (toB Fc').natDegree = Fc'.length - 1)
    (hd' : 0 < (toB Fc').natDegree) (hgeo : GeomIrr.{u} Fc')
    (hdeg' : (toB Fc').natDegree = cvN Fc') (hshF' : curveShape Fc' = true)
    (lv' : (m : ℕ) → LC m)
    (m : ℕ) (hn : T.n = m + 1) (hc' : certC Fc' (tauK Fc' Yc ks) lv' (m + 1) = true)
    {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m))
    (hck : eisCk Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) qE csE sE tE s2E t2E = true)
    (e sR : ℕ) (γs : List (LC m)) (hram : ramShapeC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) e sR γs = true)
    (hsh0 : nkShape0 Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) dθ wθ s = true)
    (hunits : ∃ (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
      (J : List ℕ) (H : List (List (LC (m + 1)))), gls.length + 1 = Pp.length / e ∧
      unitsC Fc' (tauK Fc' Yc ks) m (Pp.map (·.map (tauC Fc' Yc m))) Us Vs gls dθ wθ s = true ∧ indepC Fc' (tauK Fc' Yc ks) m gls J H = true)
    (fp : List (GPoly (LC m))) (pre : List (CandETVR m)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b res,
      (elM Fc' (tauK Fc' Yc ks) lv' (m + 1) (nkTau Fc' (tauK Fc' Yc ks) m Pp.length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s) N = some b ∧
      searchETVRP Fc' (tauK Fc' Yc ks) m (tauC Fc' Yc m a) (prdeC Fc' (tauK Fc' Yc ks) lv' m) (Pp.map (·.map (tauC Fc' Yc m))) e dθ wθ s
        (nkRest Fc' (tauK Fc' Yc ks) m (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m))))
          (nkTau Fc' (tauK Fc' Yc ks) m Pp.length (nkFl Fc' (tauK Fc' Yc ks) m (fp.map (·.map (tauC Fc' Yc m)))) s)) pre N = some res) ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  have hk' : tauK Fc' Yc ks m = .exp (tauC Fc' Yc m a) := by unfold tauK; rw [hk]
  refine T.bc_decides Q Fc' Yc hbc hmon' hlen' hd' hgeo m hn Pp fp θ hθ hgen _ ?_
  intro Cc' L' _ _ _ _ _ _ _ _ T' hTn θ' hθ' hgen'
  have hθ'' : θ' ^ (Pp.map (·.map (tauC Fc' Yc m))).length + ∑ i ∈ Finset.range (Pp.map (·.map (tauC Fc' Yc m))).length,
      T'.evP m ((Pp.map (·.map (tauC Fc' Yc m))).getD i []) * θ' ^ i = 0 := by rw [List.length_map]; exact hθ'
  have hunits' := hunits
  rw [← List.length_map (f := (·.map (tauC Fc' Yc m))) (as := Pp)] at hunits'
  obtain ⟨N₀, hN₀⟩ := T'.nk_decidesETInfVRP hmon' hdeg' hshF' m hTn hc' hk' (Pp.map (·.map (tauC Fc' Yc m))) qE csE sE tE s2E t2E hck
    e sR γs hram hsh0 θ' hθ'' hgen' dθ wθ s hs hunits' (fp.map (·.map (tauC Fc' Yc m))) pre
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, res, h1, h2, h3⟩ := hN₀ N hN
  rw [List.length_map] at h1 h2 h3
  exact ⟨b, res, ⟨h1, h2⟩, h3⟩

end MTower

end Curves.MT
