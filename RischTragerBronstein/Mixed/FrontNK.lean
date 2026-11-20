import RischTragerBronstein.Mixed.FrontRoot
import RischTragerBronstein.Mixed.NKSearchTV
import RischTragerBronstein.Mixed.NKTrace

/-!
# The front end for a non-Kummer algebraic function over a logarithm

`frontNKLog ps es N`: decides `∫ ∑ⱼ eⱼ θʲ` for `θⁿ + ∑ᵢ aᵢ θⁱ = 0`, the coefficients `aᵢ` (`ps`)
and `eⱼ` (`es`) expressions that compile to polynomials in the top generator `t`, a logarithm, and
the curve with a single place at infinity (`nkShape`). The power sums are computed (`traceCodes`)
and checked (`traceC`), the candidate basis comes from the shape (`nkCandV`, `searchTVP`), and the
trace part `τ` is decided by `elM`: elementary iff the exact part exists and `∫ τ` is elementary
(`nk_iffTV`). `frontNKLog_sound`: every answer is correct for every realization of the compiled
tower and every root `θ` generating `L` over it.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup Tower.NestM Tower.NestX Tower.Sys

/-- All the values of a list of options. -/
def allSomeL {α : Type*} : List (Option α) → Option (List α)
  | [] => some []
  | o :: l => o.bind fun a ↦ (allSomeL l).map (a :: ·)

lemma allSomeL_spec {α : Type*} (d : α) : ∀ (l : List (Option α)) (r : List α),
    allSomeL l = some r → r.length = l.length ∧ ∀ i < l.length, l.getD i none = some (r.getD i d)
  | [], r, h => by
    simp only [allSomeL, Option.some.injEq] at h
    subst h; simp
  | o :: l, r, h => by
    simp only [allSomeL, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, rfl, r', hr', rfl⟩ := h
    obtain ⟨hlen, hall⟩ := allSomeL_spec d l r' hr'
    refine ⟨by simp [hlen], fun i hi ↦ ?_⟩
    rcases i with _ | i
    · simp
    · simp only [List.getD_cons_succ]
      exact hall i (by simpa using hi)

variable (Fc : BPoly ℚ)

/-- The code of a polynomial in the top generator (a fraction with constant denominator). -/
def polyOf (m : ℕ) (K : (m : ℕ) → KindC m) (q : LC (m + 1)) : Option (GPoly (LC m)) :=
  let O := MO Fc K m
  if degG O q.2 ≠ 0 ∨ GPoly.isZero O q.2 = true then none
  else some (q.1.map (O.mul (O.inv (q.2.getD 0 O.zero))))

/-- The expression whose nodes make the tower. -/
def nkE (ps es : List EE) : EE := EE.add (sumE ps) (sumE es)

/-- **The front end for `∫ ∑ⱼ eⱼ θʲ`, `θⁿ + ∑ aᵢ θⁱ = 0`, over a logarithm.** -/
def frontNKLog (ps es : List EE) (N : ℕ) : Option Bool :=
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
        match searchTVP Fc K m η (prdeC Fc K lv m) (nkPC Fc K m Pp)
            (nkRest Fc K m (nkFl Fc K m fp) (nkTau Fc K m Pp.length (nkFl Fc K m fp) s))
            [nkCandV Fc K m Pp],
          elM Fc K lv (m + 1) (nkTau Fc K m Pp.length (nkFl Fc K m fp) s) N with
        | some res, some b => some (res && b)
        | _, _ => none
      | _, _ => none

universe u

variable {Fc} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

lemma polyOf_spec [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L) (m : ℕ) (h : T.Tr m) (q : LC (m + 1)) (p : GPoly (LC m))
    (hp : polyOf Fc m ks q = some p) : T.evP m p = T.ev (m + 1) q := by
  unfold polyOf at hp
  dsimp only at hp
  split_ifs at hp with hd
  obtain rfl := Option.some.inj hp
  push Not at hd
  exact ev_constDen T m h q hd.1 (by simpa using hd.2)

/-- **Every answer of `frontNKLog` is correct**: for every realization `T` of the compiled tower
and every root `θ` of `Yⁿ + ∑ aᵢ Yⁱ` generating `L` over it. -/
theorem frontNKLog_sound [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (ps es : List EE) (N : ℕ) (b : Bool)
    (hb : frontNKLog Fc ps es N = some b)
    (T : MTower Fc (ksOf Fc (nkE ps es)) Cc L) (hn : T.n = (nkE ps es).nodesOf.length) (θ : L)
    (hθ : θ ^ ps.length + ∑ i ∈ Finset.range ps.length,
      evE Fc T (nkE ps es).nodesOf (ps.getD i (EE.cst 0)) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (nkE ps es).nodesOf.length) {θ}) :
    HasElementaryIntegral (∑ j ∈ Finset.range ps.length,
      evE Fc T (nkE ps es).nodesOf (es.getD j (EE.cst 0)) * θ ^ j) ↔ b = true := by
  classical
  unfold frontNKLog at hb
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
  split at hb
  · rename_i res b' hres hb'
    obtain rfl := (Option.some.inj hb).symm
    have hθ' : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0 := by
      rw [hPl, ← hθ]
      congr 1
      exact Finset.sum_congr rfl fun i hi ↦ by rw [hPe i (Finset.mem_range.mp hi)]
    have hint : ∑ j ∈ Finset.range ps.length, evE Fc T (nkE ps es).nodesOf (es.getD j (EE.cst 0)) *
        θ ^ j = ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j := by
      rw [hPl]
      exact Finset.sum_congr rfl fun j hj ↦ by rw [hfe j (Finset.mem_range.mp hj)]
    obtain ⟨dg, r, Tc, Ti, hex⟩ := searchTVP_sound Fc (ksOf Fc (nkE ps es)) m η _ _ _ _ res hres
    rw [hint, T.nk_iffTV hmon hdeg m hn hc hkη Pp hshp θ hθ' hgen _ hs fp dg r Tc Ti res hex,
      Bool.and_eq_true]
    apply and_congr_right
    intro _
    -- the trace part in the subtower
    obtain ⟨T', hT'n, hT'ev, hT'gen, -⟩ := T.exists_sub (m + 1) (by omega)
    have hmem : ∀ i, T.evP m (Pp.getD i []) ∈ T.F (m + 1) := fun i ↦ T.evP_mem m (T.ev_mem m) _
    have hθi : IsIntegral (T.F (m + 1)) θ := by
      refine ⟨polyF (fun i ↦ (⟨T.evP m (Pp.getD i []), hmem i⟩ : T.F (m + 1))) Pp.length,
        polyF_monic _ _, ?_⟩
      rw [← eval_map, polyF_eval_map]
      exact hθ'
    have halg : Algebra.IsAlgebraic (T.F (m + 1)) L := ⟨fun z ↦ by
      have := IntermediateField.isAlgebraic_adjoin_simple hθi
      exact (IntermediateField.isAlgebraic_iff (x := (⟨z, hgen z⟩ :
        IntermediateField.adjoin (T.F (m + 1)) {θ}))).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩
    set τ := nkTau Fc (ksOf Fc (nkE ps es)) m Pp.length (nkFl Fc (ksOf Fc (nkE ps es)) m fp)
      (traceCodes Fc (ksOf Fc (nkE ps es)) m (nkPC Fc (ksOf Fc (nkE ps es)) m Pp)) with hτ
    have h0 : HasElementaryIntegral (T.ev (m + 1) τ) ↔ HasElementaryIntegral (T'.ev (m + 1) τ) := by
      rw [← hasElementaryIntegral_isAlgebraic_iff halg]
      rw [show algebraMap (T.F (m + 1)) L (T'.ev (m + 1) τ) = T.ev (m + 1) τ from
        hT'ev (m + 1) le_rfl τ]
    rw [h0]
    exact (elM_sound hmon hdeg hsh T' (m + 1) hT'n hc hT'gen _ N b' hb').1
  · cases hb

end Curves.MT.Front
