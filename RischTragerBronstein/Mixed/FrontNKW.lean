import RischTragerBronstein.Mixed.FrontNK
import RischTragerBronstein.Mixed.NKWitTV
import RischTragerBronstein.Mixed.FrontIntegrate

/-!
# The non-Kummer front end with the antiderivative

`frontNKLogW` mirrors `frontNKLog` (`frontNKLogW_isSome`) and returns the antiderivative of the
trace part (`elMW`) and the exact part `Y` (`exactTLSW` on the candidate from the shape), with
`f(θ) = τ + (∑ₖ Yₖ θᵏ)′` (`frontNKLogW_valid`); `frontNKLogShow` prints it.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup Tower.NestM Tower.NestX Tower.Sys

/-- The antiderivative: the pieces for the trace part and the exact part. -/
inductive NKFW where
  | mk (m : ℕ) (wτ : ADW (m + 1)) (wt : List ℚ × List (LC (m + 1)))

variable (Fc : BPoly ℚ)

/-- **`frontNKLog` with the antiderivative.** -/
def frontNKLogW (ps es : List EE) (N : ℕ) : Option (Option NKFW) :=
  match (nkE ps es).nodesOf.length with
  | 0 => none
  | m + 1 =>
    let K := ksOf Fc (nkE ps es)
    let lv := lvOf Fc (nkE ps es)
    if !(curveShape Fc && certC Fc K lv (m + 1)) then none else
    match K m with
    | .exp _ => none
    | .prim η =>
      let cp : EE → Option (GPoly (LC m)) := fun e ↦
        (comp Fc (nkE ps es).nodesOf K (m + 1) e).bind (polyOf Fc m K)
      match allSomeL (ps.map cp), allSomeL ((List.range ps.length).map fun j ↦
          cp (es.getD j (EE.cst 0))) with
      | some Pp, some fp =>
        if !(nkShape Fc K m Pp) then none else
        let s := traceCodes Fc K m (nkPC Fc K m Pp)
        if !(traceC Fc K m (nkPC Fc K m Pp) s) then none else
        match [nkCandV Fc K m Pp].findSome? (fun c ↦ exactTLSW Fc K m η
            (fun n A0 q hh G0 ↦ primSysV Fc K m η (prdeC Fc K lv m) c.2.2.2 n A0 q hh G0) c.2.2.1
            (nkPC Fc K m Pp) c.1 c.2.1
            (nkRest Fc K m (nkFl Fc K m fp) (nkTau Fc K m Pp.length (nkFl Fc K m fp) s)) []),
          elMW Fc K lv (m + 1) (nkTau Fc K m Pp.length (nkFl Fc K m fp) s) N with
        | some o1, some o0 => some (match o1, o0 with
          | some wt, some wτ => some (.mk m wτ wt)
          | _, _ => none)
        | _, _ => none
      | _, _ => none

/-- **`frontNKLogW` answers as `frontNKLog`.** -/
theorem frontNKLogW_isSome (ps es : List EE) (N : ℕ) :
    (frontNKLogW Fc ps es N).map Option.isSome = frontNKLog Fc ps es N := by
  unfold frontNKLogW frontNKLog
  rcases (nkE ps es).nodesOf.length with _ | m
  · rfl
  dsimp only
  by_cases hcs : (!(curveShape Fc && certC Fc (ksOf Fc (nkE ps es)) (lvOf Fc (nkE ps es)) (m + 1))) = true
  · rw [if_pos hcs, if_pos hcs]; rfl
  rw [if_neg hcs, if_neg hcs]
  rcases ksOf Fc (nkE ps es) m with η | g
  swap
  · rfl
  dsimp only
  rcases allSomeL (ps.map fun e ↦ (comp Fc (nkE ps es).nodesOf (ksOf Fc (nkE ps es)) (m + 1)
    e).bind (polyOf Fc m (ksOf Fc (nkE ps es)))) with _ | Pp
  · rfl
  rcases allSomeL ((List.range ps.length).map fun j ↦ (comp Fc (nkE ps es).nodesOf
    (ksOf Fc (nkE ps es)) (m + 1) (es.getD j (EE.cst 0))).bind (polyOf Fc m (ksOf Fc (nkE ps es))))
    with _ | fp
  · rfl
  dsimp only
  by_cases hd1 : (!nkShape Fc (ksOf Fc (nkE ps es)) m Pp) = true
  · rw [if_pos hd1, if_pos hd1]; rfl
  rw [if_neg hd1, if_neg hd1]
  by_cases hd2 : (!traceC Fc (ksOf Fc (nkE ps es)) m (nkPC Fc (ksOf Fc (nkE ps es)) m Pp)
      (traceCodes Fc (ksOf Fc (nkE ps es)) m (nkPC Fc (ksOf Fc (nkE ps es)) m Pp))) = true
  · rw [if_pos hd2, if_pos hd2]; rfl
  rw [if_neg hd2, if_neg hd2]
  have hS : ∀ c : List (List (LC (m + 1))) × List (List (LC (m + 1))) × (ℕ → ℤ) × List (FRep (LC m)),
      (exactTLSW Fc (ksOf Fc (nkE ps es)) m η (fun n A0 q hh G0 ↦ primSysV Fc (ksOf Fc (nkE ps es)) m η
        (prdeC Fc (ksOf Fc (nkE ps es)) (lvOf Fc (nkE ps es)) m) c.2.2.2 n A0 q hh G0) c.2.2.1
        (nkPC Fc (ksOf Fc (nkE ps es)) m Pp) c.1 c.2.1 (nkRest Fc (ksOf Fc (nkE ps es)) m
          (nkFl Fc (ksOf Fc (nkE ps es)) m fp) (nkTau Fc (ksOf Fc (nkE ps es)) m Pp.length
            (nkFl Fc (ksOf Fc (nkE ps es)) m fp) (traceCodes Fc (ksOf Fc (nkE ps es)) m
              (nkPC Fc (ksOf Fc (nkE ps es)) m Pp)))) []).map Option.isSome =
      exactTV Fc (ksOf Fc (nkE ps es)) m η (prdeC Fc (ksOf Fc (nkE ps es)) (lvOf Fc (nkE ps es)) m)
        c.2.2.2 c.2.2.1 (nkPC Fc (ksOf Fc (nkE ps es)) m Pp) c.1 c.2.1 (nkRest Fc (ksOf Fc (nkE ps es)) m
          (nkFl Fc (ksOf Fc (nkE ps es)) m fp) (nkTau Fc (ksOf Fc (nkE ps es)) m Pp.length
            (nkFl Fc (ksOf Fc (nkE ps es)) m fp) (traceCodes Fc (ksOf Fc (nkE ps es)) m
              (nkPC Fc (ksOf Fc (nkE ps es)) m Pp)))) := fun c ↦ by
    rw [exactTV_eq]; exact exactTLSW_isSome _ _ _ _ _ _ _ _ _ _ _
  unfold searchTVP
  simp only [List.findSome?_cons, List.findSome?_nil]
  rw [← hS, ← elMW_isSome]
  rcases exactTLSW Fc (ksOf Fc (nkE ps es)) m η _ _ _ _ _ _ [] with _ | o1
  · cases elMW Fc (ksOf Fc (nkE ps es)) (lvOf Fc (nkE ps es)) (m + 1) _ N <;> rfl
  rcases elMW Fc (ksOf Fc (nkE ps es)) (lvOf Fc (nkE ps es)) (m + 1) _ N with _ | o0
  · cases o1 <;> rfl
  cases o1 <;> cases o0 <;> rfl

/-- **The antiderivative as strings**: the tower, the pieces for the trace part, the exact part
`∑ Yₖ θᵏ`. -/
def frontNKLogShow (ps es : List EE) (N : ℕ) : List String :=
  match frontNKLogW Fc ps es N with
  | none => ["no answer"]
  | some none => ["not elementary"]
  | some (some (.mk m wτ wt)) => "elementary; tower:" :: nodesRender (nkE ps es) ++
      "antiderivative of the trace part = sum of the pieces:" ::
        ADW.render Fc (ksOf Fc (nkE ps es)) N (m + 1) wτ ++
      ["exact part: " ++ joinSum ((List.range ps.length).filterMap fun k ↦
        if (MOr Fc (ksOf Fc (nkE ps es)) (m + 1)).isZero
          (wt.2.getD k (MOr Fc (ksOf Fc (nkE ps es)) (m + 1)).zero) then none
        else some ("(" ++ showLC Fc (ksOf Fc (nkE ps es)) (m + 1)
          (wt.2.getD k (MOr Fc (ksOf Fc (nkE ps es)) (m + 1)).zero) ++ ") theta^" ++ toString k))]

universe u

variable {Fc}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **Every antiderivative returned by `frontNKLogW` is valid**: a valid `elMW` witness for the
trace part `τ`, and `∑ⱼ eⱼ θʲ = τ + (∑ₖ Yₖ θᵏ)′`. -/
theorem frontNKLogW_valid [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (ps es : List EE) (N : ℕ) (k : ℕ) (wτ : ADW (k + 1))
    (wt : List ℚ × List (LC (k + 1))) (hb : frontNKLogW Fc ps es N = some (some (.mk k wτ wt)))
    (T : MTower Fc (ksOf Fc (nkE ps es)) Cc L) (hn : T.n = (nkE ps es).nodesOf.length) (θ : L)
    (hθ : θ ^ ps.length + ∑ i ∈ Finset.range ps.length,
      evE Fc T (nkE ps es).nodesOf (ps.getD i (EE.cst 0)) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (nkE ps es).nodesOf.length) {θ}) :
    ∃ τ : LC (k + 1), T.ValidW (k + 1) τ wτ ∧
      ∑ j ∈ Finset.range ps.length, evE Fc T (nkE ps es).nodesOf (es.getD j (EE.cst 0)) * θ ^ j =
        T.ev (k + 1) τ + (∑ i ∈ Finset.range ps.length,
          T.ev (k + 1) (wt.2.getD i (MOr Fc (ksOf Fc (nkE ps es)) (k + 1)).zero) * θ ^ i)′ := by
  classical
  unfold frontNKLogW at hb
  obtain ⟨m, hlen⟩ : ∃ m, (nkE ps es).nodesOf.length = m + 1 := by
    rcases h0 : (nkE ps es).nodesOf.length with _ | m
    · rw [h0] at hb; cases hb
    · exact ⟨m, rfl⟩
  rw [hlen] at hb hn hgen
  dsimp only at hb
  by_cases hcs : (curveShape Fc && certC Fc (ksOf Fc (nkE ps es)) (lvOf Fc (nkE ps es)) (m + 1)) = true
  swap
  · rw [if_pos (by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr hcs)] at hb; cases hb
  rw [if_neg (by rw [hcs]; decide)] at hb
  obtain ⟨hsh, hc⟩ := Bool.and_eq_true_iff.mp hcs
  have MS := T.mspecs hmon hdeg (lvOf Fc (nkE ps es)) (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  split at hb
  · cases hb
  rename_i η hkη
  rcases hPp : allSomeL (ps.map fun e ↦ (comp Fc (nkE ps es).nodesOf (ksOf Fc (nkE ps es)) (m + 1)
    e).bind (polyOf Fc m (ksOf Fc (nkE ps es)))) with _ | Pp
  · rw [hPp] at hb; cases hb
  rcases hfp : allSomeL ((List.range ps.length).map fun j ↦ (comp Fc (nkE ps es).nodesOf
    (ksOf Fc (nkE ps es)) (m + 1) (es.getD j (EE.cst 0))).bind (polyOf Fc m (ksOf Fc (nkE ps es))))
    with _ | fp
  · rw [hPp, hfp] at hb; cases hb
  rw [hPp, hfp] at hb
  dsimp only at hb
  -- the values of the compiled coefficients
  have hval : ∀ (e : EE) (p : GPoly (LC m)), (comp Fc (nkE ps es).nodesOf (ksOf Fc (nkE ps es))
      (m + 1) e).bind (polyOf Fc m (ksOf Fc (nkE ps es))) = some p →
      T.evP m p = evE Fc T (nkE ps es).nodesOf e := by
    intro e p hep
    obtain ⟨q, hq, hpq⟩ := Option.bind_eq_some_iff.mp hep
    rw [polyOf_spec T m hTm q p hpq, comp_spec Fc T _ (m + 1) hTr e q hq]
  obtain ⟨hPl, hPv⟩ := allSomeL_spec [] _ Pp hPp
  obtain ⟨hfl, hfv⟩ := allSomeL_spec [] _ fp hfp
  simp only [List.length_map, List.length_range] at hPl hfl
  have hPe : ∀ i < ps.length, T.evP m (Pp.getD i []) = evE Fc T (nkE ps es).nodesOf
      (ps.getD i (EE.cst 0)) := by
    intro i hi
    have := hPv i (by simpa using hi)
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map] at this
    rw [hval _ _ this, List.getD_eq_getElem _ _ hi]
  have hfe : ∀ j < ps.length, T.evP m (fp.getD j []) = evE Fc T (nkE ps es).nodesOf
      (es.getD j (EE.cst 0)) := by
    intro j hj
    have := hfv j (by simpa using hj)
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range] at this
    exact hval _ _ this
  by_cases hd1 : (!nkShape Fc (ksOf Fc (nkE ps es)) m Pp) = true
  · rw [if_pos hd1] at hb; cases hb
  rw [if_neg hd1] at hb
  have hshp : nkShape Fc (ksOf Fc (nkE ps es)) m Pp = true := by simpa using hd1
  by_cases hd2 : (!traceC Fc (ksOf Fc (nkE ps es)) m (nkPC Fc (ksOf Fc (nkE ps es)) m Pp)
      (traceCodes Fc (ksOf Fc (nkE ps es)) m (nkPC Fc (ksOf Fc (nkE ps es)) m Pp))) = true
  · rw [if_pos hd2] at hb; cases hb
  rw [if_neg hd2] at hb
  have hs : traceC Fc (ksOf Fc (nkE ps es)) m (nkPC Fc (ksOf Fc (nkE ps es)) m Pp)
      (traceCodes Fc (ksOf Fc (nkE ps es)) m (nkPC Fc (ksOf Fc (nkE ps es)) m Pp)) = true := by
    simpa using hd2
  have hθ' : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0 := by
    rw [hPl, ← hθ]
    congr 1
    exact Finset.sum_congr rfl fun i hi ↦ by rw [hPe i (Finset.mem_range.mp hi)]
  simp only [List.findSome?_cons, List.findSome?_nil] at hb
  rcases hex : exactTLSW Fc (ksOf Fc (nkE ps es)) m η _ _ _ _ _ _ [] with _ | o1
  · rw [hex] at hb
    revert hb
    cases elMW Fc (ksOf Fc (nkE ps es)) (lvOf Fc (nkE ps es)) (m + 1) _ N <;> simp
  rcases o1 with _ | wt'
  · rw [hex] at hb
    revert hb
    cases elMW Fc (ksOf Fc (nkE ps es)) (lvOf Fc (nkE ps es)) (m + 1) _ N <;> simp
  rw [hex] at hb
  rcases hτ : elMW Fc (ksOf Fc (nkE ps es)) (lvOf Fc (nkE ps es)) (m + 1)
    (nkTau Fc (ksOf Fc (nkE ps es)) m Pp.length (nkFl Fc (ksOf Fc (nkE ps es)) m fp)
      (traceCodes Fc (ksOf Fc (nkE ps es)) m (nkPC Fc (ksOf Fc (nkE ps es)) m Pp))) N with _ | o0
  · rw [hτ] at hb; cases hb
  rcases o0 with _ | wτ'
  · rw [hτ] at hb; cases hb
  rw [hτ] at hb
  simp only [Option.some.injEq, NKFW.mk.injEq] at hb
  obtain ⟨rfl, hw0, hw1⟩ := hb
  subst hw0
  subst hw1
  have hcm : certC Fc (ksOf Fc (nkE ps es)) (lvOf Fc (nkE ps es)) m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg (lvOf Fc (nkE ps es)) m (by omega) hcm
  have hP : T.evθ m hTr θ (nkPC Fc (ksOf Fc (nkE ps es)) m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ'
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc (ksOf Fc (nkE ps es)) m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc (ksOf Fc (nkE ps es)) m Pp).length - 1, a j = 0 := by
    rw [Curves.MT.MTower.length_nkPC]; exact T.nkCurve_ind m hTr Pp hshp θ hθ'
  have hY := T.exactTLSW_valid m hTr (by omega) hkη (hTr m (by omega)) _
    (T.primSpecV (by omega) hTr.of_succ hkη _ MSm.rde _) _ (nkPC Fc (ksOf Fc (nkE ps es)) m Pp) _ θ
    hP hind _ _ [] wt' hex
  have hexpl := T.nk_explicit_core m hTr Pp (T.nkShape_spec m hTr.of_succ Pp hshp).1 θ []
    (fun _ ↦ 1) (fun i hi ↦ absurd hi (by simp)) (fun i hi ↦ absurd hi (by simp)) fp _ wt' hY
  -- `L` elementary over `F₀`
  have hmem : ∀ i, T.evP m (Pp.getD i []) ∈ T.F (m + 1) := fun i ↦ T.evP_mem m (T.ev_mem m) _
  have hθi : IsIntegral (T.F (m + 1)) θ := by
    refine ⟨polyF (fun i ↦ (⟨T.evP m (Pp.getD i []), hmem i⟩ : T.F (m + 1))) Pp.length,
      polyF_monic _ _, ?_⟩
    rw [← eval_map, polyF_eval_map]
    exact hθ'
  have hE0 := T.isElementary_alg hmon hdeg (m + 1) hn hc θ hθi hgen 0 (Nat.zero_le _)
  refine ⟨_, T.elMW_validE hmon hdeg hsh (m + 1) hn hc hE0 (m + 1) le_rfl _ N _ hτ, ?_⟩
  obtain ⟨-, hid⟩ := hexpl
  rw [show ∑ j ∈ Finset.range ps.length, evE Fc T (nkE ps es).nodesOf (es.getD j (EE.cst 0)) * θ ^ j =
      ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j by
    rw [hPl]
    exact Finset.sum_congr rfl fun j hj ↦ by rw [hfe j (Finset.mem_range.mp hj)], hid, hPl]
  simp

end Curves.MT.Front
