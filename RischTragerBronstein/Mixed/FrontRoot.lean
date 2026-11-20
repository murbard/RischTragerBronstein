import RischTragerBronstein.Mixed.FrontSqrt
import RischTragerBronstein.Mixed.KLDecide

/-!
# The front end with an `n`-th root over a logarithm

`frontRootLog n a es N`: decides `∫ ∑_{j<n} eⱼ θʲ` with `θⁿ = a`, for expressions `a`, `eⱼ` in
`x`, `y`, `exp`, `log`, when the top generator is a logarithm, `a` is a squarefree polynomial
`A(t)` in it with `gcd(n, deg A) = 1`, and for `j ≥ 1` the denominator of `eⱼ` is `c Aᵏ`: the part
`e₀` by `elM`, the others by `kpDecideK` (`kl_iff`: the components decouple). `frontRootLog_sound`:
every answer is correct for every realization of the compiled tower and every `n`-th root `θ`
of `a` generating `L` over it.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup Tower.NestM Tower.NestX Tower.Sys

variable (Fc : BPoly ℚ)

/-- The sum of a list of expressions. -/
def sumE : List EE → EE
  | [] => EE.cst 0
  | e :: l => EE.add e (sumE l)

/-- The combined expression whose nodes make the tower. -/
def rtE (a : EE) (es : List EE) : EE := EE.add a (sumE es)

/-- The shape `c Aᵏ` of the denominator of a code: `(B, k)` with `B = (num)/c`. -/
def denShape (m : ℕ) (K : (m : ℕ) → KindC m) (A : GPoly (LC m)) (q : LC (m + 1)) :
    Option (GPoly (LC m) × ℕ) :=
  let O := MO Fc K m
  let st := stripG O A q.2.length q.2
  if degG O st.1 ≠ 0 ∨ GPoly.isZero O st.1 = true then none
  else some (q.1.map (O.mul (O.inv (st.1.getD 0 O.zero))), st.2)

/-- **The front end for `∫ ∑_{j<n} eⱼ θʲ`, `θⁿ = a`, over a logarithm.** -/
def frontRootLog (n : ℕ) (a : EE) (es : List EE) (N : ℕ) : Option Bool :=
  match (rtE a es).nodesOf.length with
  | 0 => none
  | m + 1 =>
    let K := ksOf Fc (rtE a es)
    let lv := lvOf Fc (rtE a es)
    let O := MO Fc K m
    if !(curveShape Fc && certC Fc K lv (m + 1)) then none else
    match K m with
    | .exp _ => none
    | .prim _ =>
      let cs : ℕ → Option (LC (m + 1)) := fun j ↦
        comp Fc (rtE a es).nodesOf K (m + 1) (es.getD j (EE.cst 0))
      match comp Fc (rtE a es).nodesOf K (m + 1) a, cs 0 with
      | some qa, some f0 =>
        if degG O qa.2 ≠ 0 ∨ GPoly.isZero O qa.2 = true then none else
        let A := qa.1.map (O.mul (O.inv (qa.2.getD 0 O.zero)))
        if !(GPoly.squarefreeCheck O A) ∨ degG O A = 0 ∨ Nat.gcd n (degG O A) ≠ 1 ∨ n = 0 ∨
          n < es.length then none else
        let shp : ℕ → Option (GPoly (LC m) × ℕ) := fun j ↦ (cs j).bind (denShape Fc m K A)
        if !((List.range n).all fun j ↦ decide (j = 0) || (shp j).isSome) then none else
        (elM Fc K lv (m + 1) f0 N).map fun b0 ↦
          b0 && (List.range n).all fun j ↦ decide (j = 0) || match shp j with
            | some Bk => kpDecideK Fc K lv m j n A Bk.1 Bk.2
            | none => false
      | _, _ => none

universe u

variable {Fc} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

lemma denShape_spec [Fact (Irreducible (toPoly (fKc Fc)))] (T : MTower Fc ks Cc L) (m : ℕ) (h : T.Tr m) (A : GPoly (LC m))
    (q : LC (m + 1)) (Bk : GPoly (LC m) × ℕ) (hs : denShape Fc m ks A q = some Bk) :
    T.ev (m + 1) q = T.evP m Bk.1 / T.evP m A ^ Bk.2 := by
  unfold denShape at hs
  dsimp only at hs
  split_ifs at hs with hd
  obtain rfl := (Option.some.inj hs)
  push Not at hd
  exact ev_stripP T m h q A _ hd.1 (by simpa using hd.2)

/-- **Every answer of `frontRootLog` is correct**: for every realization `T` of the compiled
tower and every `n`-th root `θ` of `a` generating `L` over it. -/
theorem frontRootLog_sound [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (n : ℕ)
    (a : EE) (es : List EE) (N : ℕ) (b : Bool) (hb : frontRootLog Fc n a es N = some b)
    (T : MTower Fc (ksOf Fc (rtE a es)) Cc L) (hn : T.n = (rtE a es).nodesOf.length) (θ : L)
    (hθ : θ ^ n = evE Fc T (rtE a es).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (rtE a es).nodesOf.length) {θ}) :
    HasElementaryIntegral (∑ j ∈ Finset.range n,
      evE Fc T (rtE a es).nodesOf (es.getD j (EE.cst 0)) * θ ^ j) ↔ b = true := by
  classical
  unfold frontRootLog at hb
  obtain ⟨m, hlen⟩ : ∃ m, (rtE a es).nodesOf.length = m + 1 := by
    rcases h0 : (rtE a es).nodesOf.length with _ | m
    · rw [h0] at hb; cases hb
    · exact ⟨m, rfl⟩
  rw [hlen] at hb hn hgen
  dsimp only at hb
  by_cases hcs : (curveShape Fc && certC Fc (ksOf Fc (rtE a es)) (lvOf Fc (rtE a es)) (m + 1)) = true
  swap
  · rw [if_pos (by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr hcs)] at hb; cases hb
  rw [if_neg (by rw [hcs]; decide)] at hb
  obtain ⟨hsh, hc⟩ := Bool.and_eq_true_iff.mp hcs
  have MS := T.mspecs hmon hdeg (lvOf Fc (rtE a es)) (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  split at hb
  · cases hb
  rename_i η hkη
  rcases hqa : comp Fc (rtE a es).nodesOf (ksOf Fc (rtE a es)) (m + 1) a with _ | qa
  · rw [hqa] at hb; cases hb
  rcases hf0 : comp Fc (rtE a es).nodesOf (ksOf Fc (rtE a es)) (m + 1) (es.getD 0 (EE.cst 0))
    with _ | f0
  · rw [hqa, hf0] at hb; cases hb
  rw [hqa, hf0] at hb
  dsimp only at hb
  have hva := comp_spec Fc T (rtE a es).nodesOf (m + 1) hTr a qa hqa
  by_cases hd1 : degG (MO Fc (ksOf Fc (rtE a es)) m) qa.2 ≠ 0 ∨
      GPoly.isZero (MO Fc (ksOf Fc (rtE a es)) m) qa.2 = true
  · rw [if_pos hd1] at hb; cases hb
  rw [if_neg hd1] at hb
  push Not at hd1
  have hd1' : GPoly.isZero (MO Fc (ksOf Fc (rtE a es)) m) qa.2 = false := by simpa using hd1.2
  set A := qa.1.map ((MO Fc (ksOf Fc (rtE a es)) m).mul ((MO Fc (ksOf Fc (rtE a es)) m).inv
    (qa.2.getD 0 (MO Fc (ksOf Fc (rtE a es)) m).zero))) with hA
  by_cases hd2 : (!GPoly.squarefreeCheck (MO Fc (ksOf Fc (rtE a es)) m) A) = true ∨
      degG (MO Fc (ksOf Fc (rtE a es)) m) A = 0 ∨
      Nat.gcd n (degG (MO Fc (ksOf Fc (rtE a es)) m) A) ≠ 1 ∨ n = 0 ∨ n < es.length
  · rw [if_pos hd2] at hb; cases hb
  rw [if_neg hd2] at hb
  push Not at hd2
  obtain ⟨hsq, hdegpos, hgcd, hn0, hlen'⟩ := hd2
  have hsqc : GPoly.squarefreeCheck (MO Fc (ksOf Fc (rtE a es)) m) A = true := by simpa using hsq
  have hθA : θ ^ n = T.evP m A := by
    rw [hθ, ← hva, hA, ev_constDen T m hTm qa hd1.1 hd1']
  set shp : ℕ → Option (GPoly (LC m) × ℕ) := fun j ↦
    (comp Fc (rtE a es).nodesOf (ksOf Fc (rtE a es)) (m + 1) (es.getD j (EE.cst 0))).bind
      (denShape Fc m (ksOf Fc (rtE a es)) A) with hshp
  by_cases hd3 : (!((List.range n).all fun j ↦ decide (j = 0) || (shp j).isSome)) = true
  · rw [if_pos hd3] at hb; cases hb
  rw [if_neg hd3] at hb
  have hd3' : ∀ x < n, ¬x = 0 → ¬shp x = none := by simpa using hd3
  have hall : ∀ j ∈ Finset.Ico 1 n, (shp j).isSome := by
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    exact Option.isSome_iff_ne_none.mpr (hd3' j hj'.2 (by omega))
  set Bf : ℕ → GPoly (LC m) := fun j ↦ ((shp j).getD ([], 0)).1 with hBf
  set kf : ℕ → ℕ := fun j ↦ ((shp j).getD ([], 0)).2 with hkf
  -- the components
  have hcomp : ∀ j ∈ Finset.Ico 1 n,
      evE Fc T (rtE a es).nodesOf (es.getD j (EE.cst 0)) = T.evP m (Bf j) / T.evP m A ^ kf j := by
    intro j hj
    obtain ⟨Bk, hBk⟩ := Option.isSome_iff_exists.mp (hall j hj)
    have hBk' := hBk
    simp only [hshp, Option.bind_eq_some_iff] at hBk'
    obtain ⟨q, hq, hds⟩ := hBk'
    rw [← comp_spec Fc T (rtE a es).nodesOf (m + 1) hTr _ q hq, denShape_spec T m hTm A q Bk hds]
    simp only [hBf, hkf, hBk, Option.getD_some]
  have hsum : ∑ j ∈ Finset.range n, evE Fc T (rtE a es).nodesOf (es.getD j (EE.cst 0)) * θ ^ j =
      T.ev (m + 1) f0 + ∑ j ∈ Finset.Ico 1 n, T.evP m (Bf j) / T.evP m A ^ kf j * θ ^ j := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), pow_zero, mul_one,
      comp_spec Fc T (rtE a es).nodesOf (m + 1) hTr _ f0 hf0]
    congr 1
    exact Finset.sum_congr rfl fun j hj ↦ by rw [hcomp j hj]
  rw [hsum, T.kl_iff hmon hdeg m hn hc hkη A n (by omega) hsqc (by omega) hgcd θ hθA hgen f0 Bf kf]
  -- the part `e₀` in the subtower
  obtain ⟨T', hT'n, hT'ev, hT'gen, -⟩ := T.exists_sub (m + 1) (by omega)
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
  have h0 : HasElementaryIntegral (T.ev (m + 1) f0) ↔ HasElementaryIntegral (T'.ev (m + 1) f0) := by
    rw [← hasElementaryIntegral_isAlgebraic_iff halg]
    rw [show algebraMap (T.F (m + 1)) L (T'.ev (m + 1) f0) = T.ev (m + 1) f0 from
      hT'ev (m + 1) le_rfl f0]
  obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb
  rw [h0, (elM_sound hmon hdeg hsh T' (m + 1) hT'n hc hT'gen f0 N b0 hb0).1]
  rw [Bool.and_eq_true]
  apply and_congr_right
  intro _
  rw [List.all_eq_true]
  constructor
  · intro hj j hjm
    have hj' := List.mem_range.mp hjm
    by_cases hj0 : j = 0
    · simp [hj0]
    · obtain ⟨Bk, hBk⟩ := Option.isSome_iff_exists.mp (hall j (Finset.mem_Ico.mpr ⟨by omega, hj'⟩))
      have hBk' : (comp Fc (rtE a es).nodesOf (ksOf Fc (rtE a es)) (m + 1)
          (es.getD j (EE.cst 0))).bind (denShape Fc m (ksOf Fc (rtE a es)) A) = some Bk := hBk
      have := hj j (Finset.mem_Ico.mpr ⟨by omega, hj'⟩)
      simp only [hBf, hkf, hBk, Option.getD_some] at this
      simp only [hj0, decide_false, Bool.false_or, hBk']
      exact this
  · intro hj j hjm
    have hjm' := Finset.mem_Ico.mp hjm
    have := hj j (List.mem_range.mpr hjm'.2)
    obtain ⟨Bk, hBk⟩ := Option.isSome_iff_exists.mp (hall j hjm)
    have hBk' : (comp Fc (rtE a es).nodesOf (ksOf Fc (rtE a es)) (m + 1)
        (es.getD j (EE.cst 0))).bind (denShape Fc m (ksOf Fc (rtE a es)) A) = some Bk := hBk
    simp only [show j ≠ 0 by omega, decide_false, Bool.false_or, hBk'] at this
    simp only [hBf, hkf, hBk, Option.getD_some]
    exact this

end Curves.MT.Front
