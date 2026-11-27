import RischTragerBronstein.Mixed.FrontRootSumP
import RischTragerBronstein.Mixed.KRMain
import RischTragerBronstein.Mixed.KYMain
import RischTragerBronstein.Elementary.CommonExt

/-!
# Whole integrands `∑ⱼ eⱼ θʲ`, `θⁿ = a`, over a logarithm or an exponential

`frontRootSumX M n zN a es pls gss`: decides `∫ ∑_{j<n} eⱼ θʲ` when `a` compiles to a squarefree
polynomial `A(t)` of degree prime to `n` in the top generator `t`, of either kind:

* `e₀` by `elM`;
* below a logarithm, the components `eⱼ` (`j ≥ 1`) by `rootComp` (`kpDecideK` without poles,
  `kvDecide` with the poles `pls[j]`);
* below an exponential, by `rootCompE`: the denominator of `eⱼ` must be `c tᵏ ∏(t − c_q) Aˡ`
  (exact divisions), decided by `krDecide` without poles and by `kyDecide` with the poles
  `pls[j]` and the roots `gss[j]` of the residue invariants in the number field `ℚ[X]/(M)`.

`frontRootSumX_sound`: every answer is correct. The components decouple (`kl_componentsW`), and
conversely integrable components add up (`HasElementaryIntegral.sum`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup Tower.NestM Tower.NestX Tower.Sys

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- The decision for one component `q₁ θʲ` (`0 < j < n`) below an exponential, from its code
`q₁` and the codes `cq` of its poles. -/
def rootCompE (m : ℕ) (K : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (n j : ℕ) [Fact (Irreducible (toPoly (cycK Fc m n)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (g : LC m) (A : GPoly (LC m)) (q1 : LC (m + 1)) (cq : List (LC m)) (ps : List ℕ) (bound : ℕ)
    (rs : ℕ → ℕ) : Option Bool :=
  let O := MO Fc K m
  let sA := stripG O A q1.2.length q1.2
  match divLins Fc m K cq sA.1 with
  | none => none
  | some D1 =>
    let st := stripG O (tX Fc K m) D1.length D1
    if degG O st.1 ≠ 0 ∨ GPoly.isZero O st.1 = true then none else
    if cq.length = 0 then
      krDecide Fc K lv m n j A (q1.1.map (O.mul (O.inv (st.1.getD 0 O.zero)))) st.2 sA.2
        ps bound rs
    else
      kyDecide Fc K lv m n j g M zN gs A (q1.1.map (O.mul (O.inv (st.1.getD 0 O.zero)))) st.2 sA.2
        cq ps bound rs

/-- **The front end for `∫ ∑_{j<n} eⱼ θʲ`, `θⁿ = a`, with poles, over a logarithm or an
exponential.** -/
def frontRootSumX (M : CPoly ℚ) [∀ m, Fact (Irreducible (toPoly (liftQ Fc m M)))] (n : ℕ)
    [∀ m, Fact (Irreducible (toPoly (cycK Fc m n)))]
    (zN : CPoly ℚ) (a : EE) (es : List EE) (pls : List (List EE)) (gss : List (List (CPoly ℚ)))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) : Option Bool :=
  match (rspE a es pls).nodesOf.length with
  | 0 => none
  | m + 1 =>
    let E := rspE a es pls
    let K := ksOf Fc E
    let lv := lvOf Fc E
    let O := MO Fc K m
    if !(curveShape Fc && certC Fc K lv (m + 1)) then none else
    match comp Fc E.nodesOf K (m + 1) a, comp Fc E.nodesOf K (m + 1) (es.getD 0 (EE.cst 0)) with
    | some qa, some f0 =>
      if degG O qa.2 ≠ 0 ∨ GPoly.isZero O qa.2 = true then none else
      let A := qa.1.map (O.mul (O.inv (qa.2.getD 0 O.zero)))
      if !(GPoly.squarefreeCheck O A) ∨ degG O A = 0 ∨ Nat.gcd n (degG O A) ≠ 1 ∨ n = 0 ∨
        n < es.length then none else
      let dj : ℕ → Option Bool := fun j ↦
        match comp Fc E.nodesOf K (m + 1) (es.getD j (EE.cst 0)),
          allSomeL ((pls.getD j []).map fun c ↦ comp Fc E.nodesOf K m c) with
        | some q, some cq =>
          match K m with
          | .prim η => rootComp Fc m K lv M n j zN (gss.getD j []) η A q cq ps bound rs
          | .exp g => rootCompE Fc m K lv M n j zN (gss.getD j []) g A q cq ps bound rs
        | _, _ => none
      match elM Fc K lv (m + 1) f0 N,
        allSomeL ((List.range n).map fun j ↦ if j = 0 then some true else dj j) with
      | some b0, some bs => some (b0 && bs.all id)
      | _, _ => none
    | _, _ => none

universe u

variable {Fc} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **Every answer of `rootCompE` is correct.** -/
theorem rootCompE_spec (T : MTower Fc ks Cc L) (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (n j : ℕ) [Fact (Irreducible (toPoly (cycK Fc m n)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime n (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ n = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (q1 : LC (m + 1)) (cq : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (b : Bool)
    (hb : rootCompE Fc m ks lv M n j zN gs g A q1 cq ps bound rs = some b) :
    HasElementaryIntegral (T.ev (m + 1) q1 * θ ^ j) ↔ b = true := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  unfold rootCompE at hb
  dsimp only at hb
  have haev : ∀ q, T.evP m q = aeval (T.ts m) (GPoly.toPoly (T.MP m hTm) q) := fun q ↦
    (T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm) q).symm
  have hsA := stripG_spec (MO Fc ks m) (T.MP m hTm) A q1.2.length q1.2
  rcases hD1 : divLins Fc m ks cq (stripG (MO Fc ks m) A q1.2.length q1.2).1 with _ | D1
  · rw [hD1] at hb; cases hb
  rw [hD1] at hb
  dsimp only at hb
  have hdl := divLins_spec T m hTm cq _ D1 hD1
  have hq2 : T.evP m q1.2 = T.evP m A ^ (stripG (MO Fc ks m) A q1.2.length q1.2).2 *
      (T.evP m (prodLinG Fc ks m cq) * T.evP m D1) := by
    rw [haev q1.2, hsA, map_mul, map_pow, ← haev, ← haev, hdl]
  by_cases hd3 : degG (MO Fc ks m) (stripG (MO Fc ks m) (tX Fc ks m) D1.length D1).1 ≠ 0 ∨
      GPoly.isZero (MO Fc ks m) (stripG (MO Fc ks m) (tX Fc ks m) D1.length D1).1 = true
  · rw [if_pos hd3] at hb; cases hb
  rw [if_neg hd3] at hb
  push Not at hd3
  obtain ⟨hcv, hcne⟩ := evP_const T m hTm _ hd3.1 (by simpa using hd3.2)
  have hst := stripG_spec (MO Fc ks m) (T.MP m hTm) (tX Fc ks m) D1.length D1
  have hD1v : T.evP m D1 = T.ts m ^ (stripG (MO Fc ks m) (tX Fc ks m) D1.length D1).2 *
      T.ev m ((stripG (MO Fc ks m) (tX Fc ks m) D1.length D1).1.getD 0 (MO Fc ks m).zero) := by
    rw [haev D1, hst, map_mul, map_pow, T.toPoly_tX m hTm, aeval_X, ← haev, hcv]
  have hscale := ev_pair_scale T m hTm q1 (kxDen Fc ks m A
    (stripG (MO Fc ks m) (tX Fc ks m) D1.length D1).2
    (stripG (MO Fc ks m) A q1.2.length q1.2).2 cq) _ hcne (by
    rw [hq2, hD1v]
    simp only [kxDen, haev (GPoly.mul _ _ _), GPoly.toPoly_mul, map_mul, ← haev,
      T.evP_monoG m hTm, T.evP_powG m hTm]
    ring)
  rw [hscale]
  by_cases h0 : cq.length = 0
  · rw [if_pos h0] at hb
    obtain rfl := List.length_eq_zero_iff.mp h0
    have hden : T.evP m (kxDen Fc ks m A (stripG (MO Fc ks m) (tX Fc ks m) D1.length D1).2
        (stripG (MO Fc ks m) A q1.2.length q1.2).2 []) =
        T.ts m ^ (stripG (MO Fc ks m) (tX Fc ks m) D1.length D1).2 *
          T.evP m A ^ (stripG (MO Fc ks m) A q1.2.length q1.2).2 := by
      simp only [kxDen, haev (GPoly.mul _ _ _), GPoly.toPoly_mul, map_mul, ← haev,
        T.evP_monoG m hTm, T.evP_powG m hTm]
      rw [show prodLinG Fc ks m [] = [(MO Fc ks m).one] from rfl, evP_single Fc T m,
        T.ev_one_code m hTm, mul_one]
    rw [show ∀ (B Dn : GPoly (LC m)), T.ev (m + 1) ((B, Dn) : LC (m + 1)) =
      T.evP m B / T.evP m Dn from fun _ _ ↦ rfl, hden]
    exact T.krDecide_correct hmon hdeg m hn hc hk n j A hsqc hdegpos hcop θ hθ hgen _ _ _ ps bound
      rs b hb
  · rw [if_neg h0] at hb
    exact T.kyDecide_correct hmon hdeg m hn hc hk n j M zN gs A hsqc hdegpos hcop θ hθ hgen _ _ _
      cq ps bound rs b hb

/-- **Every answer of `frontRootSumX` is correct**: for every realization `T` of the compiled
tower and every `n`-th root `θ` of `a` generating `L` over it, `∫ ∑_{j<n} eⱼ θʲ` is elementary
iff the answer is `true`. -/
theorem frontRootSumX_sound (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (M : CPoly ℚ) [∀ m, Fact (Irreducible (toPoly (liftQ Fc m M)))] (n : ℕ)
    [∀ m, Fact (Irreducible (toPoly (cycK Fc m n)))]
    (zN : CPoly ℚ) (a : EE) (es : List EE) (pls : List (List EE)) (gss : List (List (CPoly ℚ)))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) (b : Bool)
    (hb : frontRootSumX Fc M n zN a es pls gss ps bound rs N = some b)
    (T : MTower Fc (ksOf Fc (rspE a es pls)) Cc L) (hn : T.n = (rspE a es pls).nodesOf.length)
    (θ : L) (hθ : θ ^ n = evE Fc T (rspE a es pls).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (rspE a es pls).nodesOf.length) {θ}) :
    HasElementaryIntegral (∑ j ∈ Finset.range n,
      evE Fc T (rspE a es pls).nodesOf (es.getD j (EE.cst 0)) * θ ^ j) ↔ b = true := by
  classical
  unfold frontRootSumX at hb
  obtain ⟨m, hlen⟩ : ∃ m, (rspE a es pls).nodesOf.length = m + 1 := by
    rcases h0 : (rspE a es pls).nodesOf.length with _ | m
    · rw [h0] at hb; cases hb
    · exact ⟨m, rfl⟩
  rw [hlen] at hb hn hgen
  dsimp only at hb
  by_cases hcs : (curveShape Fc && certC Fc (ksOf Fc (rspE a es pls)) (lvOf Fc (rspE a es pls)) (m + 1)) = true
  swap
  · rw [if_pos (by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr hcs)] at hb; cases hb
  rw [if_neg (by rw [hcs]; decide)] at hb
  obtain ⟨hsh, hc⟩ := Bool.and_eq_true_iff.mp hcs
  have MS := T.mspecs hmon hdeg (lvOf Fc (rspE a es pls)) (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  rcases hqa : comp Fc (rspE a es pls).nodesOf (ksOf Fc (rspE a es pls)) (m + 1) a with _ | qa
  · rw [hqa] at hb; cases hb
  rcases hf0 : comp Fc (rspE a es pls).nodesOf (ksOf Fc (rspE a es pls)) (m + 1) (es.getD 0 (EE.cst 0)) with _ | f0
  · rw [hqa, hf0] at hb; cases hb
  rw [hqa, hf0] at hb
  dsimp only at hb
  have hva := comp_spec Fc T (rspE a es pls).nodesOf (m + 1) hTr a qa hqa
  by_cases hd1 : degG (MO Fc (ksOf Fc (rspE a es pls)) m) qa.2 ≠ 0 ∨
      GPoly.isZero (MO Fc (ksOf Fc (rspE a es pls)) m) qa.2 = true
  · rw [if_pos hd1] at hb; cases hb
  rw [if_neg hd1] at hb
  push Not at hd1
  have hd1' : GPoly.isZero (MO Fc (ksOf Fc (rspE a es pls)) m) qa.2 = false := by simpa using hd1.2
  set A := qa.1.map ((MO Fc (ksOf Fc (rspE a es pls)) m).mul ((MO Fc (ksOf Fc (rspE a es pls)) m).inv
    (qa.2.getD 0 (MO Fc (ksOf Fc (rspE a es pls)) m).zero))) with hA
  by_cases hd2 : (!GPoly.squarefreeCheck (MO Fc (ksOf Fc (rspE a es pls)) m) A) = true ∨
      degG (MO Fc (ksOf Fc (rspE a es pls)) m) A = 0 ∨
      Nat.gcd n (degG (MO Fc (ksOf Fc (rspE a es pls)) m) A) ≠ 1 ∨ n = 0 ∨ n < es.length
  · rw [if_pos hd2] at hb; cases hb
  rw [if_neg hd2] at hb
  push Not at hd2
  obtain ⟨hsq, hdegpos, hgcd, hn0, hlen'⟩ := hd2
  have hsqc : GPoly.squarefreeCheck (MO Fc (ksOf Fc (rspE a es pls)) m) A = true := by simpa using hsq
  have hdegpos' : 0 < degG (MO Fc (ksOf Fc (rspE a es pls)) m) A := by omega
  have hnpos : 0 < n := by omega
  have hθA : θ ^ n = T.evP m A := by
    rw [hθ, ← hva, hA, ev_constDen T m hTm qa hd1.1 hd1']
  set dj : ℕ → Option Bool := fun j ↦
    match comp Fc (rspE a es pls).nodesOf (ksOf Fc (rspE a es pls)) (m + 1) (es.getD j (EE.cst 0)),
      allSomeL ((pls.getD j []).map fun c ↦ comp Fc (rspE a es pls).nodesOf (ksOf Fc (rspE a es pls)) m c) with
    | some q, some cq =>
      match ksOf Fc (rspE a es pls) m with
      | .prim η => rootComp Fc m (ksOf Fc (rspE a es pls)) (lvOf Fc (rspE a es pls)) M n j zN
          (gss.getD j []) η A q cq ps bound rs
      | .exp g => rootCompE Fc m (ksOf Fc (rspE a es pls)) (lvOf Fc (rspE a es pls)) M n j zN
          (gss.getD j []) g A q cq ps bound rs
    | _, _ => none with hdj
  rcases hb0 : elM Fc (ksOf Fc (rspE a es pls)) (lvOf Fc (rspE a es pls)) (m + 1) f0 N with _ | b0
  · rw [hb0] at hb; cases hb
  rcases hbs : allSomeL ((List.range n).map fun j ↦ if j = 0 then some true else dj j)
    with _ | bs
  · rw [hb0, hbs] at hb; cases hb
  rw [hb0, hbs] at hb
  obtain rfl := (Option.some.inj hb).symm
  obtain ⟨hbl, hbget⟩ := allSomeL_spec false _ bs hbs
  simp only [List.length_map, List.length_range] at hbl hbget
  have hdjs : ∀ j < n, j ≠ 0 → dj j = some (bs.getD j false) := by
    intro j hjn hj0
    simpa [List.getD_eq_getElem?_getD, List.getElem?_range hjn, hj0] using hbget j hjn
  have hbs0 : bs.getD 0 false = true := by
    have := hbget 0 hnpos
    simpa [List.getD_eq_getElem?_getD, List.getElem?_range hnpos] using this.symm
  -- the components
  have hcomp : ∀ j, 0 < j → j < n → ∃ bj, dj j = some bj ∧
      (HasElementaryIntegral (evE Fc T (rspE a es pls).nodesOf (es.getD j (EE.cst 0)) * θ ^ j) ↔
        bj = true) := by
    intro j hj0 hjn
    have hbj := hdjs j hjn (by omega)
    refine ⟨_, hbj, ?_⟩
    have hbj' := hbj
    simp only [hdj] at hbj'
    rcases hq : comp Fc (rspE a es pls).nodesOf (ksOf Fc (rspE a es pls)) (m + 1) (es.getD j (EE.cst 0)) with _ | q
    · rw [hq] at hbj'; cases hbj'
    rcases hcq : allSomeL ((pls.getD j []).map fun c ↦ comp Fc (rspE a es pls).nodesOf (ksOf Fc (rspE a es pls)) m c)
      with _ | cq
    · rw [hq, hcq] at hbj'; cases hbj'
    rw [hq, hcq] at hbj'
    rw [← comp_spec Fc T (rspE a es pls).nodesOf (m + 1) hTr _ q hq]
    rcases hkk : ksOf Fc (rspE a es pls) m with η | g
    · have hkη := hkk
      simp only [hkk] at hbj'
      exact (rootComp_spec T hmon hdeg m hn hc hkη M n j hj0 hjn zN _ A hsqc hdegpos' hgcd θ hθA
        hgen q cq ps bound rs _ hbj').1
    · have hkg := hkk
      simp only [hkk] at hbj'
      exact rootCompE_spec T hmon hdeg m hn hc hkg M n j zN _ A hsqc hdegpos' hgcd θ hθA
        hgen q cq ps bound rs _ hbj'
  -- `L` is algebraic and elementary over `Fₘ₊₁`
  have hθmem : θ ^ n ∈ T.F (m + 1) := by
    rw [hθA, ← T.sem_poly_code m hTr]
    exact SetLike.coe_mem _
  have hθi : IsIntegral (T.F (m + 1)) θ := by
    refine ⟨X ^ n - C ⟨θ ^ n, hθmem⟩, monic_X_pow_sub_C _ hn0, ?_⟩
    simp [eval₂_sub, eval₂_X_pow, eval₂_C]
  have halg : Algebra.IsAlgebraic (T.F (m + 1)) L := ⟨fun z ↦ by
    have := IntermediateField.isAlgebraic_adjoin_simple hθi
    exact (IntermediateField.isAlgebraic_iff (x := (⟨z, hgen z⟩ :
      IntermediateField.adjoin (T.F (m + 1)) {θ}))).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩
  -- the part `e₀` in the subtower
  obtain ⟨T', hT'n, hT'ev, hT'gen, -⟩ := T.exists_sub (m + 1) (by omega)
  have hs0 := elM_sound hmon hdeg hsh T' (m + 1) hT'n hc hT'gen f0 N b0 hb0
  have hT'v : algebraMap (T.F (m + 1)) L (T'.ev (m + 1) f0) = T.ev (m + 1) f0 :=
    hT'ev (m + 1) le_rfl f0
  have hv0 := comp_spec Fc T (rspE a es pls).nodesOf (m + 1) hTr _ f0 hf0
  have h0 : HasElementaryIntegral (T.ev (m + 1) f0) ↔ b0 = true := by
    rw [← hT'v, hasElementaryIntegral_isAlgebraic_iff halg]
    exact hs0.1
  rw [Bool.and_eq_true, all_id_iff, hbl]
  constructor
  · intro hf
    -- codes of all the components
    set cs : ℕ → LC (m + 1) := fun j ↦
      (comp Fc (rspE a es pls).nodesOf (ksOf Fc (rspE a es pls)) (m + 1) (es.getD j (EE.cst 0))).getD f0 with hcsdef
    have hcsv : ∀ j < n, T.ev (m + 1) (cs j) = evE Fc T (rspE a es pls).nodesOf (es.getD j (EE.cst 0)) := by
      intro j hjn
      by_cases hj0 : j = 0
      · subst hj0
        simp only [hcsdef, hf0, Option.getD_some]
        exact hv0
      · have hbj' := hdjs j hjn hj0
        simp only [hdj] at hbj'
        rcases hq : comp Fc (rspE a es pls).nodesOf (ksOf Fc (rspE a es pls)) (m + 1) (es.getD j (EE.cst 0)) with _ | q
        · rw [hq] at hbj'; cases hbj'
        simp only [hcsdef, hq, Option.getD_some]
        exact comp_spec Fc T (rspE a es pls).nodesOf (m + 1) hTr _ q hq
    have hf' : HasElementaryIntegral (∑ j ∈ Finset.range n, T.ev (m + 1) (cs j) * θ ^ j) := by
      rw [Finset.sum_congr rfl fun j hj ↦ by rw [hcsv j (Finset.mem_range.mp hj)]]
      exact hf
    have hcomps := T.kl_componentsW hmon hdeg m hn hc A n hnpos hsqc hdegpos' θ hθA hgen cs hf'
    refine ⟨?_, fun j hjm ↦ ?_⟩
    · have := hcomps 0 hnpos
      rw [pow_zero, mul_one, hcsv 0 hnpos, ← hv0] at this
      exact h0.mp this
    · have hjn : j < n := hjm
      by_cases hj0 : j = 0
      · rw [hj0]; exact hbs0
      · obtain ⟨bj, hbj, hiff⟩ := hcomp j (by omega) hjn
        have := hcomps j hjn
        rw [hcsv j hjn] at this
        rw [hdjs j hjn hj0] at hbj
        rw [Option.some.inj hbj]
        exact hiff.mp this
  · rintro ⟨h0t, hall⟩
    refine HasElementaryIntegral.sum _ _ fun j hjm ↦ ?_
    have hjn := Finset.mem_range.mp hjm
    by_cases hj0 : j = 0
    · subst hj0
      rw [pow_zero, mul_one, ← hv0]
      exact h0.mpr h0t
    · obtain ⟨bj, hbj, hiff⟩ := hcomp j (by omega) hjn
      rw [hdjs j hjn hj0] at hbj
      exact hiff.mpr (Option.some.inj hbj ▸ hall j hjn)

end Curves.MT.Front
