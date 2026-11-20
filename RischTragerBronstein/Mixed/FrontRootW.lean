import RischTragerBronstein.Mixed.FrontRoot
import RischTragerBronstein.Mixed.FrontSqrtW

/-!
# `n`-th roots over a logarithm: the antiderivative

`frontRootLogW` mirrors `frontRootLog` (`frontRootLogW_isSome`) and returns the antiderivative:
the pieces of `elMW` for `e₀` and `yⱼ` with `(yⱼ θʲ)′ = eⱼ θʲ` from `kpSolveK` (`frontRootLogW_valid`);
`frontRootLogShow` prints it.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup Tower.NestM Tower.NestX Tower.Sys

/-- The antiderivative of `∑ eⱼ θʲ`: the pieces for `e₀` and the coefficients `yⱼ`. -/
inductive RootW where
  | mk (m : ℕ) (w0 : ADW (m + 1)) (ys : List (LC (m + 1)))

variable (Fc : BPoly ℚ)

/-- **`frontRootLog` with the antiderivative.** -/
def frontRootLogW (n : ℕ) (a : EE) (es : List EE) (N : ℕ) : Option (Option RootW) :=
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
        (elMW Fc K lv (m + 1) f0 N).map fun o0 ↦ match o0 with
          | none => none
          | some w0 =>
            if (List.range n).all fun j ↦ decide (j = 0) ||
                ((shp j).bind fun Bk ↦ kpSolveK Fc K lv m j n A Bk.1 Bk.2).isSome then
              some (.mk m w0 ((List.range n).map fun j ↦
                ((shp j).bind fun Bk ↦ kpSolveK Fc K lv m j n A Bk.1 Bk.2).getD (MO Fc K (m + 1)).zero))
            else none
      | _, _ => none


/-- **`frontRootLogW` answers as `frontRootLog`.** -/
theorem frontRootLogW_isSome (n : ℕ) (a : EE) (es : List EE) (N : ℕ) :
    (frontRootLogW Fc n a es N).map Option.isSome = frontRootLog Fc n a es N := by
  unfold frontRootLogW frontRootLog
  rcases (rtE a es).nodesOf.length with _ | m
  · rfl
  dsimp only
  by_cases hcs : (!(curveShape Fc && certC Fc (ksOf Fc (rtE a es)) (lvOf Fc (rtE a es)) (m + 1))) = true
  · rw [if_pos hcs, if_pos hcs]; rfl
  rw [if_neg hcs, if_neg hcs]
  rcases ksOf Fc (rtE a es) m with η | g
  swap
  · rfl
  dsimp only
  rcases comp Fc (rtE a es).nodesOf (ksOf Fc (rtE a es)) (m + 1) a with _ | qa
  · rfl
  rcases comp Fc (rtE a es).nodesOf (ksOf Fc (rtE a es)) (m + 1) (es.getD 0 (EE.cst 0)) with _ | f0
  · rfl
  dsimp only
  by_cases hd1 : degG (MO Fc (ksOf Fc (rtE a es)) m) qa.2 ≠ 0 ∨
      GPoly.isZero (MO Fc (ksOf Fc (rtE a es)) m) qa.2 = true
  · rw [if_pos hd1, if_pos hd1]; rfl
  rw [if_neg hd1, if_neg hd1]
  generalize qa.1.map ((MO Fc (ksOf Fc (rtE a es)) m).mul ((MO Fc (ksOf Fc (rtE a es)) m).inv
    (qa.2.getD 0 (MO Fc (ksOf Fc (rtE a es)) m).zero))) = A
  by_cases hd2 : (!GPoly.squarefreeCheck (MO Fc (ksOf Fc (rtE a es)) m) A) = true ∨
      degG (MO Fc (ksOf Fc (rtE a es)) m) A = 0 ∨
      Nat.gcd n (degG (MO Fc (ksOf Fc (rtE a es)) m) A) ≠ 1 ∨ n = 0 ∨ n < es.length
  · rw [if_pos hd2, if_pos hd2]; rfl
  rw [if_neg hd2, if_neg hd2]
  split
  · rfl
  rw [← elMW_isSome, Option.map_map, Option.map_map]
  congr 1
  funext o0
  rcases o0 with _ | w0
  · rfl
  simp only [Function.comp_apply]
  split
  · rename_i hC
    simp only [Option.isSome_some, Bool.true_and]
    symm
    rw [List.all_eq_true] at hC ⊢
    intro j hj
    have hCj := hC j hj
    split
    · rename_i Bk hBk
      rw [hBk] at hCj
      simpa [kpSolveK_isSome] using hCj
    · rename_i hBk
      rw [hBk] at hCj
      simpa using hCj
  · rename_i hC
    simp only [Option.isSome_none, Option.isSome_some, Bool.true_and]
    symm
    rw [Bool.eq_false_iff]
    intro hall
    apply hC
    rw [List.all_eq_true] at hall ⊢
    intro j hj
    have hCj := hall j hj
    revert hCj
    split
    · rename_i Bk hBk
      rw [hBk]
      simp [kpSolveK_isSome]
    · rename_i hBk
      rw [hBk]
      simp

/-- **The antiderivative as strings**: the tower, the pieces for `e₀`, then `yⱼ a^{j/n}`. -/
def frontRootLogShow (n : ℕ) (a : EE) (es : List EE) (N : ℕ) : List String :=
  match frontRootLogW Fc n a es N with
  | none => ["no answer at this bound"]
  | some none => ["not elementary"]
  | some (some (.mk m w0 ys)) => "elementary; tower:" :: nodesRender (rtE a es) ++
      "antiderivative of e0 = sum of the pieces:" ::
        ADW.render Fc (ksOf Fc (rtE a es)) N (m + 1) w0 ++
      ((List.range n).filterMap fun j ↦ if j = 0 ∨ (MO Fc (ksOf Fc (rtE a es)) (m + 1)).isZero
          (ys.getD j (MO Fc (ksOf Fc (rtE a es)) (m + 1)).zero) = true then none else
        some ("(" ++ showLC Fc (ksOf Fc (rtE a es)) (m + 1)
          (ys.getD j (MO Fc (ksOf Fc (rtE a es)) (m + 1)).zero) ++ ") * (" ++ a.toStr ++ ")^(" ++
          toString j ++ "/" ++ toString n ++ ")"))

universe u

variable {Fc}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **Every antiderivative returned by `frontRootLogW` is valid**: the pieces of `e₀` are a valid
`elMW` witness for its code, and `(yⱼ θʲ)′ = eⱼ θʲ` for `1 ≤ j < n`. -/
theorem frontRootLogW_valid [Fact (Irreducible (toPoly (fKc Fc)))] (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (n : ℕ) (a : EE) (es : List EE) (N : ℕ) (m : ℕ)
    (w0 : ADW (m + 1)) (ys : List (LC (m + 1)))
    (hb : frontRootLogW Fc n a es N = some (some (.mk m w0 ys)))
    (T : MTower Fc (ksOf Fc (rtE a es)) Cc L) (hn : T.n = (rtE a es).nodesOf.length) (θ : L)
    (hθ : θ ^ n = evE Fc T (rtE a es).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (rtE a es).nodesOf.length) {θ}) :
    (∃ f0 : LC (m + 1), T.ev (m + 1) f0 = evE Fc T (rtE a es).nodesOf (es.getD 0 (EE.cst 0)) ∧
      T.ValidW (m + 1) f0 w0) ∧
    ∀ j ∈ Finset.Ico 1 n, (T.ev (m + 1) (ys.getD j (MO Fc (ksOf Fc (rtE a es)) (m + 1)).zero) *
      θ ^ j)′ = evE Fc T (rtE a es).nodesOf (es.getD j (EE.cst 0)) * θ ^ j := by
  classical
  unfold frontRootLogW at hb
  obtain ⟨m', hlen⟩ : ∃ m', (rtE a es).nodesOf.length = m' + 1 := by
    rcases h0 : (rtE a es).nodesOf.length with _ | m'
    · rw [h0] at hb; cases hb
    · exact ⟨m', rfl⟩
  rw [hlen] at hb hn hgen
  dsimp only at hb
  by_cases hcs : (curveShape Fc && certC Fc (ksOf Fc (rtE a es)) (lvOf Fc (rtE a es)) (m' + 1)) = true
  swap
  · rw [if_pos (by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr hcs)] at hb; cases hb
  rw [if_neg (by rw [hcs]; decide)] at hb
  obtain ⟨hsh, hc⟩ := Bool.and_eq_true_iff.mp hcs
  have MS := T.mspecs hmon hdeg (lvOf Fc (rtE a es)) (m' + 1) (by omega) hc
  have hTr : T.Tr (m' + 1) := MS.hyp.tr
  have hTm : T.Tr m' := hTr.of_succ
  split at hb
  · cases hb
  rename_i η hkη
  rcases hqa : comp Fc (rtE a es).nodesOf (ksOf Fc (rtE a es)) (m' + 1) a with _ | qa
  · rw [hqa] at hb; cases hb
  rcases hf0 : comp Fc (rtE a es).nodesOf (ksOf Fc (rtE a es)) (m' + 1) (es.getD 0 (EE.cst 0))
    with _ | f0
  · rw [hqa, hf0] at hb; cases hb
  rw [hqa, hf0] at hb
  dsimp only at hb
  have hva := comp_spec Fc T (rtE a es).nodesOf (m' + 1) hTr a qa hqa
  by_cases hd1 : degG (MO Fc (ksOf Fc (rtE a es)) m') qa.2 ≠ 0 ∨
      GPoly.isZero (MO Fc (ksOf Fc (rtE a es)) m') qa.2 = true
  · rw [if_pos hd1] at hb; cases hb
  rw [if_neg hd1] at hb
  push Not at hd1
  have hd1' : GPoly.isZero (MO Fc (ksOf Fc (rtE a es)) m') qa.2 = false := by simpa using hd1.2
  set A := qa.1.map ((MO Fc (ksOf Fc (rtE a es)) m').mul ((MO Fc (ksOf Fc (rtE a es)) m').inv
    (qa.2.getD 0 (MO Fc (ksOf Fc (rtE a es)) m').zero))) with hA
  by_cases hd2 : (!GPoly.squarefreeCheck (MO Fc (ksOf Fc (rtE a es)) m') A) = true ∨
      degG (MO Fc (ksOf Fc (rtE a es)) m') A = 0 ∨
      Nat.gcd n (degG (MO Fc (ksOf Fc (rtE a es)) m') A) ≠ 1 ∨ n = 0 ∨ n < es.length
  · rw [if_pos hd2] at hb; cases hb
  rw [if_neg hd2] at hb
  push Not at hd2
  obtain ⟨hsq, hdegpos, hgcd, hn0, hlen'⟩ := hd2
  have hθA : θ ^ n = T.evP m' A := by
    rw [hθ, ← hva, hA, ev_constDen T m' hTm qa hd1.1 hd1']
  split at hb
  · cases hb
  rename_i hd3
  obtain ⟨o0, ho0, hoe⟩ := Option.map_eq_some_iff.mp hb
  rcases o0 with _ | w0'
  · cases hoe
  dsimp only at hoe
  split at hoe
  swap
  · cases hoe
  rename_i hC
  simp only [Option.some.injEq, RootW.mk.injEq] at hoe
  obtain ⟨rfl, hw0, rfl⟩ := hoe
  subst hw0
  have hθmem : θ ^ n ∈ T.F (m' + 1) := by
    rw [hθA, ← T.sem_poly_code m' hTr]
    exact SetLike.coe_mem _
  have hθi : IsIntegral (T.F (m' + 1)) θ := by
    refine ⟨X ^ n - C ⟨θ ^ n, hθmem⟩, monic_X_pow_sub_C _ hn0, ?_⟩
    simp [eval₂_sub, eval₂_X_pow, eval₂_C]
  have hE0 := T.isElementary_alg hmon hdeg (m' + 1) hn hc θ hθi hgen 0 (Nat.zero_le _)
  refine ⟨⟨f0, comp_spec Fc T _ (m' + 1) hTr _ f0 hf0,
    T.elMW_validE hmon hdeg hsh (m' + 1) hn hc hE0 (m' + 1) le_rfl f0 N _ ho0⟩, fun j hj ↦ ?_⟩
  have hj' := Finset.mem_Ico.mp hj
  have hCj := List.all_eq_true.mp hC j (List.mem_range.mpr hj'.2)
  simp only [show j ≠ 0 by omega, decide_false, Bool.false_or] at hCj
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hCj
  obtain ⟨Bk, hBk, hyk⟩ := Option.bind_eq_some_iff.mp hy
  obtain ⟨q, hq, hds⟩ := Option.bind_eq_some_iff.mp hBk
  rw [Tower.NestP.NestTower.getD_range_map _ _ hj'.2, hy, Option.getD_some]
  rw [T.kpK_antiderivative hmon hdeg m' hn hc A n (by omega) (by omega) θ hθA j Bk.1 Bk.2 y hyk,
    ← comp_spec Fc T _ (m' + 1) hTr _ q hq, denShape_spec T m' hTm A q Bk hds]

end Curves.MT.Front
