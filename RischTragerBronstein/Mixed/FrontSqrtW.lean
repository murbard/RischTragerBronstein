import RischTragerBronstein.Mixed.FrontSqrtSum
import RischTragerBronstein.Mixed.KPWit
import RischTragerBronstein.Mixed.KEWit
import RischTragerBronstein.Mixed.FrontIntegrate

/-!
# The square-root front end with the antiderivative

`frontSqrtEW` mirrors `frontSqrtE` (`frontSqrtEW_isSome`) and returns, with a positive answer,
the antiderivative: below an exponential the witness of `keDecideCW` (`y √a`, or
`(y/q₀) √a + C (log(W₀ + W₁ Y) − ½ log N)` with `Y = z √a/√κ`, `C = −(q₁/q₀) √κ`), below a
logarithm `y √a` with `y` from `kpSolveK` (`(y θ)′ = B/Aᵏ θ`, `kpK_antiderivative`).
`frontSqrtEW_valid`: the witness is valid for every realization and square root; `SqW.render`
prints it.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- **The antiderivative of `B/aᵏ θʲ`** over a logarithmic level, if elementary. -/
def kpSolveK (m : ℕ) (j n : ℕ) (a B : GPoly (LC m)) (k : ℕ) : Option (LC (m + 1)) :=
  rdeSolFr Fc ks lv (m + 1) (kpFr Fc ks m j n a) ((B, powG (MO Fc ks m) a k) : LC (m + 1))

lemma kpSolveK_isSome (m : ℕ) (j n : ℕ) (a B : GPoly (LC m)) (k : ℕ) :
    (kpSolveK Fc ks lv m j n a B k).isSome = kpDecideK Fc ks lv m j n a B k :=
  rdeSolFr_isSome _ _ _ _ _ _

universe u

variable {Fc ks lv} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The antiderivative of `B/aᵏ θʲ`**: `(y θʲ)′ = B/aᵏ θʲ`. -/
theorem kpK_antiderivative (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (a : GPoly (LC m)) (nn : ℕ)
    (hnn : 0 < nn) (hdegpos : 0 < degG (MO Fc ks m) a) (θ : L) (hθ : θ ^ nn = T.evP m a)
    (j : ℕ) (B : GPoly (LC m)) (k : ℕ) (y : LC (m + 1))
    (hy : kpSolveK Fc ks lv m j nn a B k = some y) :
    (T.ev (m + 1) y * θ ^ j)′ = T.evP m B / T.evP m a ^ k * θ ^ j := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hspec := MS.rde _ (T.kpFr_ok m hTr j nn a)
  have hA0 : T.evP m a ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) a hdegpos
  have hz := T.rdeSolFr_sound (m + 1) hTr _ hspec _ y hy
  have hzL := congrArg Subtype.val hz
  rw [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv, T.sem_kpFr m hTr,
    T.sem_frac_code m hTr, T.evP_powG m hTr.of_succ, T.sem_MP] at hzL
  rw [deriv_mul_radical θ (T.evP m a) nn hnn hθ hA0, hzL]

end MTower

end Curves.MT

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup Tower.NestM Tower.NestX Tower.Sys

lemma map_map_isSomeF {α β : Type*} (x : Option (Option α)) (g : α → β) :
    (x.map (Option.map g)).map Option.isSome = x.map Option.isSome := by
  cases x with
  | none => rfl
  | some y => cases y <;> rfl

/-- The antiderivative found by the square-root front end. -/
inductive SqW where
  | ke (m : ℕ) (w : KEW m)
  | kp (m : ℕ) (y : LC (m + 1))

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- **`frontSqrtE` with the antiderivative.** -/
def frontSqrtEW (E a e1 : EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : Option (Option SqW) :=
  match E.nodesOf.length with
  | 0 => none
  | m + 1 =>
    let K := ksOf Fc E
    let lv := lvOf Fc E
    let O := MO Fc K m
    if !(curveShape Fc && certC Fc K lv (m + 1)) then none else
    match comp Fc E.nodesOf K (m + 1) a, comp Fc E.nodesOf K (m + 1) e1 with
    | some qa, some q1 =>
      if degG O qa.2 ≠ 0 ∨ GPoly.isZero O qa.2 = true then none else
      let A := qa.1.map (O.mul (O.inv (qa.2.getD 0 O.zero)))
      if !(GPoly.squarefreeCheck O A) ∨ degG O A % 2 = 0 then none else
      let sA := stripG O A q1.2.length q1.2
      match K m with
      | .exp g =>
        if O.isZero (A.getD 0 O.zero) = true then none else
        let st := stripG O (tX Fc K m) sA.1.length sA.1
        if degG O st.1 ≠ 0 ∨ GPoly.isZero O st.1 = true then none else
        (keDecideCW Fc K lv m A (q1.1.map (O.mul (O.inv (st.1.getD 0 O.zero)))) st.2 sA.2 ps bound rs
          fun fK ↦ searchCert fK 2).map (Option.map (SqW.ke m))
      | .prim η =>
        if degG O sA.1 ≠ 0 ∨ GPoly.isZero O sA.1 = true then none else
        some ((kpSolveK Fc K lv m 1 2 A (q1.1.map (O.mul (O.inv (sA.1.getD 0 O.zero)))) sA.2).map
          (SqW.kp m))
    | _, _ => none


/-- **`frontSqrtEW` answers as `frontSqrtE`.** -/
theorem frontSqrtEW_isSome (E a e1 : EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) :
    (frontSqrtEW Fc E a e1 ps bound rs).map Option.isSome = frontSqrtE Fc E a e1 ps bound rs := by
  unfold frontSqrtEW frontSqrtE
  rcases E.nodesOf.length with _ | m
  · rfl
  dsimp only
  split_ifs
  · rfl
  rcases comp Fc E.nodesOf (ksOf Fc E) (m + 1) a with _ | qa
  · rfl
  rcases comp Fc E.nodesOf (ksOf Fc E) (m + 1) e1 with _ | q1
  · rfl
  dsimp only
  split_ifs
  all_goals (try rfl)
  all_goals (rcases ksOf Fc E m with η | g)
  all_goals (try dsimp only)
  all_goals (first
    | rfl
    | (simp only [Option.map_some, Option.isSome_map, kpSolveK_isSome]; done)
    | (rw [map_map_isSomeF, keDecideCW_isSome]; rfl))

/-- **The antiderivative as a string** (`sa`: the radicand; levels `tₘ` as in `nodesRender`). -/
def SqW.render (ks : (m : ℕ) → KindC m) (sa : String) : SqW → String
  | .kp m y => "(" ++ showLC Fc ks (m + 1) y ++ ") * sqrt(" ++ sa ++ ")"
  | .ke m (.plain y) => "(" ++ showLC Fc ks (m + 1) y ++ ") * sqrt(" ++ sa ++ ")"
  | .ke m (.param y q0 q1 z κ W0 W1) =>
    if q1 = 0 then "(" ++ showLC Fc ks (m + 1) y ++ ")/" ++ showQ q0 ++ " * sqrt(" ++ sa ++ ")" else
    "(" ++ showLC Fc ks (m + 1) y ++ ")/" ++ showQ q0 ++ " * sqrt(" ++ sa ++ ") + C log(" ++
      showGP Fc ks m W0 ++ " + (" ++ showGP Fc ks m W1 ++ ") Y) - (C/2) log(N), where Y = (" ++
      showLC Fc ks m z ++ ") sqrt(" ++ sa ++ ")/sqrt(" ++ showQ κ ++ "), C = " ++
      showQ (-q1 / q0) ++ " sqrt(" ++ showQ κ ++ "), N = (" ++ showGP Fc ks m W0 ++ ")^2 - (" ++
      showGP Fc ks m W1 ++ ")^2 (" ++ showLC Fc ks m z ++ ")^2/" ++ showQ κ ++ " (" ++ sa ++ ")"

/-- **`∫ e₁ √a`, decided and computed, as strings**: the levels, then the answer. -/
def frontSqrtShow (a e1 : EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) : List String :=
  nodesRender (sqE a e1) ++
  [match frontSqrtEW Fc (sqE a e1) a e1 ps bound rs with
    | some (some w) => "elementary: " ++ w.render Fc (ksOf Fc (sqE a e1)) a.toStr
    | some none => "not elementary"
    | none => "no answer"]

universe u

variable {Fc}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **Validity of an antiderivative found by the square-root front end**: `f = (y θ)′`, or the
data of a Kummer decision whose witness is valid (`KEW.Valid`). -/
def SqW.Valid {ks : (m : ℕ) → KindC m} (T : MTower Fc ks Cc L) (θ f : L) : SqW → Prop
  | .kp m y => (T.ev (m + 1) y * θ)′ = f
  | .ke m w => ∃ (A B : GPoly (LC m)) (k l : ℕ),
      f = T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ ∧ θ ^ 2 = T.evP m A ∧
        MTower.KEW.Valid T m A B k l θ w

/-- **Every antiderivative returned by `frontSqrtEW` is valid**, for every realization `T` of the
compiled tower and every square root `θ` of `a` generating `L` over it. -/
theorem frontSqrtEW_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (E a e1 : EE)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (w : SqW)
    (hb : frontSqrtEW Fc E a e1 ps bound rs = some (some w))
    (T : MTower Fc (ksOf Fc E) Cc L) (hn : T.n = E.nodesOf.length) (θ : L)
    (hθ : θ ^ 2 = evE Fc T E.nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F E.nodesOf.length) {θ}) :
    SqW.Valid T θ (evE Fc T E.nodesOf e1 * θ) w := by
  classical
  unfold frontSqrtEW at hb
  obtain ⟨m, hlen⟩ : ∃ m, E.nodesOf.length = m + 1 := by
    rcases h0 : E.nodesOf.length with _ | m
    · rw [h0] at hb; cases hb
    · exact ⟨m, rfl⟩
  rw [hlen] at hb hn hgen
  dsimp only at hb
  by_cases hcs : (curveShape Fc && certC Fc (ksOf Fc E) (lvOf Fc E) (m + 1)) = true
  swap
  · rw [if_pos (by rw [Bool.not_eq_true']; exact Bool.eq_false_iff.mpr hcs)] at hb; cases hb
  rw [if_neg (by rw [hcs]; decide)] at hb
  obtain ⟨hsh, hc⟩ := Bool.and_eq_true_iff.mp hcs
  have MS := T.mspecs hmon hdeg (lvOf Fc E) (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  rcases hqa : comp Fc E.nodesOf (ksOf Fc E) (m + 1) a with _ | qa
  · rw [hqa] at hb; cases hb
  rcases hq1 : comp Fc E.nodesOf (ksOf Fc E) (m + 1) e1 with _ | q1
  · rw [hqa, hq1] at hb; cases hb
  rw [hqa, hq1] at hb
  dsimp only at hb
  have hva := comp_spec Fc T E.nodesOf (m + 1) hTr a qa hqa
  have hv1 := comp_spec Fc T E.nodesOf (m + 1) hTr e1 q1 hq1
  by_cases hd1 : degG (MO Fc (ksOf Fc E) m) qa.2 ≠ 0 ∨ GPoly.isZero (MO Fc (ksOf Fc E) m) qa.2 = true
  · rw [if_pos hd1] at hb; cases hb
  rw [if_neg hd1] at hb
  push Not at hd1
  have hd1' : GPoly.isZero (MO Fc (ksOf Fc E) m) qa.2 = false := by simpa using hd1.2
  set A := qa.1.map ((MO Fc (ksOf Fc E) m).mul ((MO Fc (ksOf Fc E) m).inv (qa.2.getD 0 (MO Fc (ksOf Fc E) m).zero))) with hA
  by_cases hd2 : (!GPoly.squarefreeCheck (MO Fc (ksOf Fc E) m) A) = true ∨ degG (MO Fc (ksOf Fc E) m) A % 2 = 0
  · rw [if_pos hd2] at hb; cases hb
  rw [if_neg hd2] at hb
  push Not at hd2
  have hθA : θ ^ 2 = T.evP m A := by
    rw [hθ, ← hva, hA, ev_constDen T m hTm qa hd1.1 hd1']
  have hsqc : GPoly.squarefreeCheck (MO Fc (ksOf Fc E) m) A = true := by simpa using hd2.1
  have hodd : degG (MO Fc (ksOf Fc E) m) A % 2 = 1 := by omega
  have hdegpos : 0 < degG (MO Fc (ksOf Fc E) m) A := by omega
  have hcop : Nat.Coprime 2 (degG (MO Fc (ksOf Fc E) m) A) := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hodd)
  split at hb
  · -- below an exponential
    rename_i g hkg
    by_cases hz : (MO Fc (ksOf Fc E) m).isZero (A.getD 0 (MO Fc (ksOf Fc E) m).zero) = true
    · rw [if_pos hz] at hb; cases hb
    rw [if_neg hz] at hb
    by_cases hd3 : degG (MO Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m) (tX Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1.length
        (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1).1 ≠ 0 ∨ GPoly.isZero (MO Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m) (tX Fc (ksOf Fc E) m)
        (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1.length (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1).1 = true
    · rw [if_pos hd3] at hb; cases hb
    rw [if_neg hd3] at hb
    push Not at hd3
    have ha0 : (MO Fc (ksOf Fc E) m).isZero (A.getD 0 (MO Fc (ksOf Fc E) m).zero) = false := by simpa using hz
    have hz3 : GPoly.isZero (MO Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m) (tX Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1.length
        (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1).1 = false := by simpa using hd3.2
    obtain ⟨o, ho, hoe⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨w', rfl, rfl⟩ := Option.map_eq_some_iff.mp hoe
    refine ⟨A, _, _, _, ?_, hθA, T.keDecideCW_valid hmon hdeg m hn hc A hdegpos ha0 θ hθA _ _ _ ps bound
      rs _ w' ho⟩
    rw [← hv1, ev_stripE T m hTm q1 A _ _ hd3.1 hz3]
  · -- below a logarithm
    rename_i η hkη
    by_cases hd3 : degG (MO Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1 ≠ 0 ∨
        GPoly.isZero (MO Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1 = true
    · rw [if_pos hd3] at hb; cases hb
    rw [if_neg hd3] at hb
    push Not at hd3
    have hz3 : GPoly.isZero (MO Fc (ksOf Fc E) m) (stripG (MO Fc (ksOf Fc E) m) A q1.2.length q1.2).1 = false := by simpa using hd3.2
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp (Option.some.inj hb)
    have hdec := T.kpK_antiderivative hmon hdeg m hn hc A 2 two_pos hdegpos θ hθA 1 _ _ y hy
    simp only [pow_one] at hdec
    show (T.ev (m + 1) y * θ)′ = evE Fc T E.nodesOf e1 * θ
    rw [hdec, ← hv1, ev_stripP T m hTm q1 A _ hd3.1 hz3]


end Curves.MT.Front
