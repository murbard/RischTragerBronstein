import RischTragerBronstein.Mixed.FrontSqrtSumW

/-!
# The front end with a square root, arbitrary rational expressions in `√a`

`SE`: expressions over the curve and its `exp`/`log` tower with a square root `θ = √a` as an
atom (`exp`/`log` take `θ`-free arguments). `SE.split a s = (e₀, e₁)` rewrites `s` as
`e₀ + e₁ θ` by arithmetic in the quadratic extension (`(u₀ + u₁ θ)⁻¹ =
(u₀ − u₁ θ)/(u₀² − u₁² a)`); `SE.split_spec`: the rewriting is correct as soon as `θ` is not in
a field containing all the values (also when `u₀ + u₁ θ = 0`, with `0⁻¹ = 0`).
`frontSqrtAuto` decides `∫ s` through `frontSqrtSum`; `frontSqrtAuto_sound` (θ is not in
`Fₘ₊₁`: `X² − A` is the minimal polynomial, `A` squarefree of positive degree). With the
antiderivative: `frontSqrtAutoW`, `frontSqrtAutoW_valid`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT.Front

open Curves Curves.LT Curves.MT CPoly Sup Tower.NestM Tower.NestX Tower.Sys

/-- Expressions with one square root `th`. -/
inductive SE where
  | x
  | y
  | th
  | cst (c : ℚ)
  | add (a b : SE)
  | mul (a b : SE)
  | neg (a : SE)
  | inv (a : SE)
  | exp (a : EE)
  | log (a : EE)
  deriving DecidableEq, Repr

/-- `u + v`, dropping zeros. -/
def addS (u v : EE) : EE :=
  if u = EE.cst 0 then v else if v = EE.cst 0 then u else EE.add u v

/-- `u v`, dropping ones and absorbing zeros. -/
def mulS (u v : EE) : EE :=
  if u = EE.cst 0 ∨ v = EE.cst 0 then EE.cst 0
  else if u = EE.cst 1 then v else if v = EE.cst 1 then u else EE.mul u v

/-- `−u`, keeping zero. -/
def negS (u : EE) : EE := if u = EE.cst 0 then u else EE.neg u

namespace SE

/-- **The splitting** `s = e₀ + e₁ √a`. -/
def split (a : EE) : SE → EE × EE
  | x => (EE.x, EE.cst 0)
  | y => (EE.y, EE.cst 0)
  | th => (EE.cst 0, EE.cst 1)
  | cst c => (EE.cst c, EE.cst 0)
  | add u v =>
    let p := split a u
    let q := split a v
    (addS p.1 q.1, addS p.2 q.2)
  | mul u v =>
    let p := split a u
    let q := split a v
    (addS (mulS p.1 q.1) (mulS (mulS p.2 q.2) a), addS (mulS p.1 q.2) (mulS p.2 q.1))
  | neg u =>
    let p := split a u
    (negS p.1, negS p.2)
  | inv u =>
    let p := split a u
    if p.2 = EE.cst 0 then (EE.inv p.1, EE.cst 0)
    else
      let D := addS (mulS p.1 p.1) (negS (mulS (mulS p.2 p.2) a))
      (mulS p.1 (EE.inv D), negS (mulS p.2 (EE.inv D)))
  | exp b => (EE.exp b, EE.cst 0)
  | log b => (EE.log b, EE.cst 0)

end SE

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- **The front end for `∫ s`, `s` rational in `√a`.** -/
def frontSqrtAuto (a : EE) (s : SE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) :
    Option Bool :=
  frontSqrtSum Fc a (s.split a).1 (s.split a).2 ps bound rs N

/-- The tower expression of `frontSqrtAuto`. -/
def saE (a : EE) (s : SE) : EE := ssE a (s.split a).1 (s.split a).2

/-- **`frontSqrtAuto` with the antiderivative.** -/
def frontSqrtAutoW (a : EE) (s : SE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) :
    Option (Option SumW) :=
  frontSqrtSumW Fc a (s.split a).1 (s.split a).2 ps bound rs N

theorem frontSqrtAutoW_isSome (a : EE) (s : SE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (N : ℕ) : (frontSqrtAutoW Fc a s ps bound rs N).map Option.isSome =
      frontSqrtAuto Fc a s ps bound rs N :=
  frontSqrtSumW_isSome Fc _ _ _ _ _ _ _

/-- The display of the answer. -/
def frontSqrtAutoShow (a : EE) (s : SE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) :
    List String :=
  ("integrand = " ++ (s.split a).1.toStr ++ " + (" ++ (s.split a).2.toStr ++ ") sqrt(" ++
    a.toStr ++ ")") :: frontSqrtSumShow Fc a (s.split a).1 (s.split a).2 ps bound rs N

universe u

variable {Fc} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **The value of an expression with a square root `θ`.** -/
noncomputable def evS (T : MTower Fc ks Cc L) (nodes : List EE) (θ : L) : SE → L
  | SE.x => T.S.x
  | SE.y => T.S.y
  | SE.th => θ
  | SE.cst c => (c : L)
  | SE.add a b => evS T nodes θ a + evS T nodes θ b
  | SE.mul a b => evS T nodes θ a * evS T nodes θ b
  | SE.neg a => -evS T nodes θ a
  | SE.inv a => (evS T nodes θ a)⁻¹
  | SE.exp a => evE Fc T nodes (EE.exp a)
  | SE.log a => evE Fc T nodes (EE.log a)

section Split

variable (T : MTower Fc ks Cc L) (nodes : List EE)

lemma evE_addS (u v : EE) : evE Fc T nodes (addS u v) = evE Fc T nodes u + evE Fc T nodes v := by
  unfold addS
  split_ifs with h1 h2
  · subst h1; simp [evE]
  · subst h2; simp [evE]
  · rfl

lemma evE_mulS (u v : EE) : evE Fc T nodes (mulS u v) = evE Fc T nodes u * evE Fc T nodes v := by
  unfold mulS
  split_ifs with h1 h2 h3
  · rcases h1 with h1 | h1 <;> subst h1 <;> simp [evE]
  · subst h2; simp [evE]
  · subst h3; simp [evE]
  · rfl

lemma evE_negS (u : EE) : evE Fc T nodes (negS u) = -evE Fc T nodes u := by
  unfold negS
  split_ifs with h1
  · subst h1; simp [evE]
  · rfl

/-- **The splitting is correct**: if `θ² = a` and `θ` is not in a field `K` containing the values
of all `θ`-free expressions, then `s = e₀ + e₁ θ`. -/
theorem SE.split_spec (a : EE) (θ : L) (hθ : θ ^ 2 = evE Fc T nodes a) (K : Set L)
    (hmem : ∀ e : EE, evE Fc T nodes e ∈ K)
    (hirr : ∀ u v : L, u ∈ K → v ∈ K → u = v * θ → v = 0) :
    ∀ s : SE, evS T nodes θ s = evE Fc T nodes (s.split a).1 + evE Fc T nodes (s.split a).2 * θ
  | SE.x => by simp [evS, SE.split, evE]
  | SE.y => by simp [evS, SE.split, evE]
  | SE.th => by simp [evS, SE.split, evE]
  | SE.cst c => by simp [evS, SE.split, evE]
  | SE.add u v => by
    simp only [evS, SE.split, evE_addS]
    rw [SE.split_spec a θ hθ K hmem hirr u, SE.split_spec a θ hθ K hmem hirr v]; ring
  | SE.mul u v => by
    simp only [evS, SE.split, evE_addS, evE_mulS]
    rw [SE.split_spec a θ hθ K hmem hirr u, SE.split_spec a θ hθ K hmem hirr v, ← hθ]; ring
  | SE.neg u => by
    simp only [evS, SE.split, evE_negS]
    rw [SE.split_spec a θ hθ K hmem hirr u]; ring
  | SE.inv u => by
    simp only [evS, SE.split]
    rw [SE.split_spec a θ hθ K hmem hirr u]
    split_ifs with h0
    · rw [h0]; simp [evE]
    · simp only [evE_addS, evE_mulS, evE_negS, evE, ← hθ]
      set u0 := evE Fc T nodes (u.split a).1
      set u1 := evE Fc T nodes (u.split a).2
      by_cases hD : u0 * u0 + -(u1 * u1 * θ ^ 2) = 0
      · have hw : u0 + u1 * θ = 0 := by
          have hf : (u0 + u1 * θ) * (u0 - u1 * θ) = 0 := by rw [← hD]; ring
          rcases mul_eq_zero.mp hf with h | h
          · exact h
          · have hu1 := hirr u0 u1 (hmem _) (hmem _) (by linear_combination h)
            have hu0 : u0 = 0 := by rw [sub_eq_zero.mp h, hu1, zero_mul]
            rw [hu0, hu1]; ring
        rw [hw, hD]; simp
      · have hw : u0 + u1 * θ ≠ 0 := fun hw ↦ hD (by
          have : u0 = -(u1 * θ) := by linear_combination hw
          rw [this]; ring)
        symm
        apply eq_inv_of_mul_eq_one_left
        rw [show (u0 * (u0 * u0 + -(u1 * u1 * θ ^ 2))⁻¹ + -(u1 * (u0 * u0 + -(u1 * u1 * θ ^ 2))⁻¹) * θ) *
          (u0 + u1 * θ) = (u0 * u0 + -(u1 * u1 * θ ^ 2)) * (u0 * u0 + -(u1 * u1 * θ ^ 2))⁻¹ by ring,
          mul_inv_cancel₀ hD]
  | SE.exp b => by simp [evS, SE.split, evE]
  | SE.log b => by simp [evS, SE.split, evE]

end Split

/-! ### `θ` is not in `Fₘ₊₁` -/

lemma ts_mem_n (T : MTower Fc ks Cc L) (i : ℕ) : T.ts i ∈ T.F T.n := by
  by_cases hi : i < T.n
  · exact T.F_mono (by omega) (T.ts_mem i)
  · rw [T.hts i (by omega)]; exact zero_mem _

lemma evE_mem (T : MTower Fc ks Cc L) (nodes : List EE) :
    ∀ e : EE, evE Fc T nodes e ∈ T.F T.n
  | EE.x => by rw [evE, ← ev0_x]; exact T.F_mono (Nat.zero_le _) (T.ev_mem 0 _)
  | EE.y => by rw [evE, ← ev0_y]; exact T.F_mono (Nat.zero_le _) (T.ev_mem 0 _)
  | EE.cst c => by
    rw [evE, ← map_ratCast (algebraMap Cc L)]; exact T.const_mem _ _
  | EE.add a b => add_mem (evE_mem T nodes a) (evE_mem T nodes b)
  | EE.mul a b => mul_mem (evE_mem T nodes a) (evE_mem T nodes b)
  | EE.neg a => neg_mem (evE_mem T nodes a)
  | EE.inv a => inv_mem (evE_mem T nodes a)
  | EE.exp a => by
    simp only [evE]
    split
    · exact ts_mem_n T _
    · exact zero_mem _
  | EE.log a => by
    simp only [evE]
    split
    · exact ts_mem_n T _
    · exact zero_mem _

/-- **`θ` is not in `Fₘ₊₁`** when `θ² = A(tₘ)`, `A` squarefree of positive degree. -/
lemma theta_notMem (T : MTower Fc ks Cc L) (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
    (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true) (hdegpos : 0 < degG (MO Fc ks m) A)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) : θ ∉ T.F (m + 1) := by
  intro hmem
  have hTm : T.Tr m := hTr.of_succ
  set p₁ : (T.F m)[X] := GPoly.toPoly (T.MP m hTm) A with hp₁
  have hsq₁ : Squarefree p₁ := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg₁ : p₁.natDegree = degG (MO Fc ks m) A := (degG_eq (T.MP m hTm) A).symm
  have hy₁ : θ ^ 2 = aeval (T.ts m) p₁ := by
    rw [hp₁, T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm), hθ]
  let S₁ : SuperData (T.F m) L :=
    ⟨T.ts m, θ, 2, p₁, hTr m (by omega), two_pos, hsq₁, by rw [hdeg₁]; exact hdegpos, hy₁,
      by norm_num⟩
  have hmp := S₁.minpoly_eq
  have hθ' : θ ∈ IntermediateField.adjoin (T.F m) {S₁.x} := (T.mem_F_succ).mp hmem
  have h1 : minpoly (IntermediateField.adjoin (T.F m) {S₁.x}) S₁.y =
      X - Polynomial.C (⟨θ, hθ'⟩ : IntermediateField.adjoin (T.F m) {S₁.x}) :=
    minpoly.eq_X_sub_C L (⟨θ, hθ'⟩ : IntermediateField.adjoin (T.F m) {S₁.x})
  have h2 := congrArg Polynomial.natDegree (hmp.symm.trans h1)
  rw [natDegree_X_pow_sub_C, natDegree_X_sub_C] at h2
  exact absurd h2 (by norm_num)

/-! ### Soundness -/

/-- An answer of `frontSqrtSum` comes with an answer for the part `e₁ √a`. -/
lemma frontSqrtSum_e1 (a e0 e1 : EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) (b : Bool)
    (hb : frontSqrtSum Fc a e0 e1 ps bound rs N = some b) :
    ∃ b1, frontSqrtE Fc (ssE a e0 e1) a e1 ps bound rs = some b1 := by
  unfold frontSqrtSum at hb
  revert hb
  rcases (ssE a e0 e1).nodesOf.length with _ | m
  · intro hb; cases hb
  dsimp only
  rcases comp Fc (ssE a e0 e1).nodesOf (ksOf Fc (ssE a e0 e1)) (m + 1) e0 with _ | f0
  · intro hb; cases hb
  dsimp only
  rcases elM Fc (ksOf Fc (ssE a e0 e1)) (lvOf Fc (ssE a e0 e1)) (m + 1) f0 N with _ | b0 <;>
  rcases frontSqrtE Fc (ssE a e0 e1) a e1 ps bound rs with _ | b1
  all_goals first | (intro hb; cases hb; done) | exact fun _ ↦ ⟨_, rfl⟩

/-- Shared setup: `θ ∉ Fₘ₊₁` and the splitting is correct. -/
lemma frontSqrtAuto_split (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (a e0 e1 : EE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (b1 : Bool)
    (hb1 : frontSqrtE Fc (ssE a e0 e1) a e1 ps bound rs = some b1)
    (T : MTower Fc (ksOf Fc (ssE a e0 e1)) Cc L) (hn : T.n = (ssE a e0 e1).nodesOf.length)
    (θ : L) (hθ : θ ^ 2 = evE Fc T (ssE a e0 e1).nodesOf a) :
    ∀ u v : L, u ∈ T.F T.n → v ∈ T.F T.n → u = v * θ → v = 0 := by
  classical
  obtain ⟨m, qa, q1, hlen, hsh, hc, hqa, hq1, hd, hz, hsqc, hdegpos⟩ :=
    frontSqrtE_data (ssE a e0 e1) a e1 ps bound rs b1 hb1
  have MS := T.mspecs hmon hdeg (lvOf Fc (ssE a e0 e1)) (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hva := comp_spec Fc T (ssE a e0 e1).nodesOf (m + 1) hTr a qa hqa
  have hθA : θ ^ 2 = T.evP m (qa.1.map ((MO Fc (ksOf Fc (ssE a e0 e1)) m).mul
      ((MO Fc (ksOf Fc (ssE a e0 e1)) m).inv
        (qa.2.getD 0 (MO Fc (ksOf Fc (ssE a e0 e1)) m).zero)))) := by
    rw [hθ, ← hva, ev_constDen T m hTm qa hd hz]
  have hnot := theta_notMem T m hTr _ hsqc hdegpos θ hθA
  intro u v hu hv huv
  by_contra hv0
  apply hnot
  have : θ = u / v := by rw [huv]; field_simp
  rw [this, ← hlen, ← hn]
  exact div_mem hu hv

/-- **Every answer of `frontSqrtAuto` is correct**: for every realization `T` of the compiled
tower and every square root `θ` of `a` generating `L` over it, `∫ s` is elementary iff the
answer is `true`. -/
theorem frontSqrtAuto_sound (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (a : EE) (s : SE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) (b : Bool)
    (hb : frontSqrtAuto Fc a s ps bound rs N = some b)
    (T : MTower Fc (ksOf Fc (saE a s)) Cc L) (hn : T.n = (saE a s).nodesOf.length)
    (θ : L) (hθ : θ ^ 2 = evE Fc T (saE a s).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (saE a s).nodesOf.length) {θ}) :
    HasElementaryIntegral (evS T (saE a s).nodesOf θ s) ↔ b = true := by
  classical
  have hs := frontSqrtSum_sound hmon hdeg a _ _ ps bound rs N b hb T hn θ hθ hgen
  -- the part `e₁ √a` was answered
  obtain ⟨b1, hb1⟩ := frontSqrtSum_e1 a _ _ ps bound rs N b hb
  have hirr := frontSqrtAuto_split hmon hdeg a _ _ ps bound rs b1 hb1 T hn θ hθ
  rw [SE.split_spec T _ a θ hθ (T.F T.n : Set L) (evE_mem T _) hirr s]
  exact hs

/-- **Every antiderivative returned by `frontSqrtAutoW` is valid**, for the integrand `s`. -/
theorem frontSqrtAutoW_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (a : EE) (s : SE) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (N : ℕ) (m : ℕ)
    (w0 : ADW (m + 1)) (w1 : SqW)
    (hb : frontSqrtAutoW Fc a s ps bound rs N = some (some (.mk m w0 w1)))
    (T : MTower Fc (ksOf Fc (saE a s)) Cc L) (hn : T.n = (saE a s).nodesOf.length)
    (θ : L) (hθ : θ ^ 2 = evE Fc T (saE a s).nodesOf a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (saE a s).nodesOf.length) {θ}) :
    evS T (saE a s).nodesOf θ s = evE Fc T (saE a s).nodesOf (s.split a).1 +
      evE Fc T (saE a s).nodesOf (s.split a).2 * θ ∧
    (∃ f0 : LC (m + 1), T.ev (m + 1) f0 = evE Fc T (saE a s).nodesOf (s.split a).1 ∧
      T.ValidW (m + 1) f0 w0) ∧
    SqW.Valid T θ (evE Fc T (saE a s).nodesOf (s.split a).2 * θ) w1 := by
  classical
  have hv := frontSqrtSumW_valid hmon hdeg a _ _ ps bound rs N m w0 w1 hb T hn θ hθ hgen
  refine ⟨?_, hv⟩
  have hsome : (frontSqrtAutoW Fc a s ps bound rs N).map Option.isSome = some true := by
    rw [hb]; rfl
  rw [frontSqrtAutoW_isSome] at hsome
  obtain ⟨b1, hb1⟩ := frontSqrtSum_e1 a _ _ ps bound rs N true hsome
  have hirr := frontSqrtAuto_split hmon hdeg a _ _ ps bound rs b1 hb1 T hn θ hθ
  exact SE.split_spec T _ a θ hθ (T.F T.n : Set L) (evE_mem T _) hirr s

end Curves.MT.Front
