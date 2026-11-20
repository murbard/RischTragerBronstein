import RischTragerBronstein.Torsion.CurveWit
import RischTragerBronstein.Torsion.DecideEnum

/-!
# Curve antiderivatives along the total decision

`stageNFW`, `decideLoopW`, `decideCurveQW`, `CertQ.runW`, `decideEnumW`, `decideTotalW` mirror the
automatic pipeline and the certificate enumeration, returning with a `true` answer the number
field `ℚ[γ]/(M)`, the problem `P` over it and the witness `w` of `P.decideLogW` (`CurveWQ`);
`mob` marks a witness for a Möbius-transformed problem. They answer exactly as the deciders
(`…_isSome`), and every returned witness comes from `decideLogW` on the base change of the
problem (`CurveWQ.Src`), so it gives the antiderivative `v + ∑ cⱼ log uⱼ` explicitly
(`CurveWQ.valid`).
-/

open Polynomial

namespace Curves

open CPoly Sup EllQuad.QCoords Differential

lemma findSome?_map' {α β γ : Type*} (l : List α) (f : α → Option β) (g : β → γ) :
    (l.findSome? f).map g = l.findSome? fun a ↦ (f a).map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.findSome?_cons]
    cases f a <;> simp [ih]

/-- **A curve antiderivative over a number field.** -/
structure CurveWQ where
  M : IrrQ
  P : CurveProb (NFC.NF M.1)
  w : CurveW (NFC.NF M.1)
  /-- the Möbius transformation `(e, k₀, DA, k')` of the certificate, if any -/
  mob : Option (NFC.NF M.1 × ℕ × ℕ × ℕ)

section Loop

variable (P0 : CurveProb ℚ)

/-- `stageNF` with the witness. -/
def stageNFW (fast : Bool) (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] (kI : ℕ) (exs : List ℕ)
    (ex fuel L tp B : ℕ) (pqs : List (ℕ × ℕ)) :
    Except (CPoly (NFC.NF M)) (Option (Option (CurveProb (NFC.NF M) × CurveW (NFC.NF M)))) :=
  let φ := algebraMap ℚ (NFC.NF M)
  let rf := if fast then NFC.rfNFZ M else NFC.rfNF M
  let Fc := P0.Fc.map (·.map φ)
  let A := P0.A.map (·.map φ)
  let D := P0.D.map φ
  let pqs := if pqs.isEmpty then autoPairs M 3 else pqs
  match probeMissing rf Fc P0.n P0.k kI D L fuel with
  | some g => .error g
  | none =>
    .ok ((autoGlobal rf Fc P0.n kI ex fuel).bind fun T ↦
      exs.findSome? fun e ↦ (autoCurveProb rf Fc P0.n P0.k A D e).bind fun P ↦
        pqs.findSome? fun pq ↦
          (decideAutoFullW rf (redAtM M) (P0.baseChange φ P0.k P.pts P.inf) T L tp B pq.1 pq.2).map
            (Option.map fun w ↦ (P0.baseChange φ P0.k P.pts P.inf, w)))

lemma stageNFW_isSome (fast : Bool) (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] (kI : ℕ)
    (exs : List ℕ) (ex fuel L tp B : ℕ) (pqs : List (ℕ × ℕ)) :
    (stageNFW P0 fast M kI exs ex fuel L tp B pqs).map (Option.map Option.isSome) =
      stageNF P0 fast M kI exs ex fuel L tp B pqs := by
  unfold stageNFW stageNF
  dsimp only
  split
  · rename_i g hg
    rw [hg]
    rfl
  · rename_i hg
    rw [hg]
    simp only [Except.map]
    congr 1
    rw [Option.map_bind]
    congr 1
    funext T
    simp only [Function.comp_apply]
    rw [findSome?_map']
    congr 1
    funext e
    rw [Option.map_bind]
    congr 1
    funext P
    simp only [Function.comp_apply]
    rw [findSome?_map']
    congr 1
    funext pq
    rw [Option.map_map, ← decideAutoFullW_isSome]
    congr 1
    funext o
    cases o <;> rfl

/-- `decideLoop` with the witness. -/
def decideLoopW (fast : Bool) (kI : ℕ) (exs : List ℕ) (ex fuel L tp B : ℕ) (pqs : List (ℕ × ℕ)) :
    ℕ → (M : CPoly ℚ) → Kron.irredQ M = true → Option (Option CurveWQ)
  | 0, _, _ => none
  | m + 1, M, hM =>
    haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    match stageNFW P0 fast M kI exs ex fuel L tp B pqs with
    | .ok r => r.map (Option.map fun pw ↦ ⟨⟨M, hM⟩, pw.1, pw.2, none⟩)
    | .error g =>
      match NFC.extStep M (remRoots fast M g) with
      | some ⟨M', hM'⟩ => decideLoopW fast kI exs ex fuel L tp B pqs m M' hM'
      | none => none

lemma decideLoopW_isSome (fast : Bool) (kI : ℕ) (exs : List ℕ) (ex fuel L tp B : ℕ)
    (pqs : List (ℕ × ℕ)) : ∀ (m : ℕ) (M : CPoly ℚ) (hM : Kron.irredQ M = true),
    (decideLoopW P0 fast kI exs ex fuel L tp B pqs m M hM).map Option.isSome =
      decideLoop P0 fast kI exs ex fuel L tp B pqs m M hM
  | 0, _, _ => rfl
  | m + 1, M, hM => by
    have : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    unfold decideLoopW decideLoop
    rw [← stageNFW_isSome]
    cases stageNFW P0 fast M kI exs ex fuel L tp B pqs with
    | error g =>
      simp only [Except.map]
      split
      · rename_i M' hM' heq
        rw [heq]
        exact decideLoopW_isSome fast kI exs ex fuel L tp B pqs m _ _
      · rename_i heq
        rw [heq]
        rfl
    | ok r =>
      simp only [Except.map, Option.map_map]
      congr 1
      funext o
      cases o <;> rfl

/-- `decideCurveQ` with the witness. -/
def decideCurveQW (Fc A : BPoly ℚ) (D : CPoly ℚ) (fuel : ℕ := 4) : Option (Option CurveWQ) :=
  decideLoopW (curveProbQ Fc A D) true (autoKI Fc) [0, 8, 16] 2 10 16 10 12 [] fuel [0, 1] irredQ_X

lemma decideCurveQW_isSome (Fc A : BPoly ℚ) (D : CPoly ℚ) (fuel : ℕ) :
    (decideCurveQW Fc A D fuel).map Option.isSome = decideCurveQ Fc A D fuel :=
  decideLoopW_isSome _ _ _ _ _ _ _ _ _ _ _ _ _

/-- `CertQ.run` with the witness. -/
def CertQ.runW (c : CertQ) : Option (Option CurveWQ) :=
  haveI : Fact (Irreducible (toPoly c.1.1)) := ⟨Kron.irredQ_sound _ c.1.2⟩
  let d : List (NFC.NF c.1.1 × BranchCert (NFC.NF c.1.1)) × BranchCert (NFC.NF c.1.1) ×
      List (LogWit (NFC.NF c.1.1)) × List (TorsWitP (NFC.NF c.1.1)) ×
      Option (NFC.NF c.1.1 × ℕ × ℕ × ℕ) := c.2
  match d.2.2.2.2 with
  | none =>
    (decideLogTPW (redAtM c.1.1) (P0.baseChange (algebraMap ℚ (NFC.NF c.1.1)) P0.k d.1 d.2.1)
      d.2.2.1 [] d.2.2.2.1).map (Option.map fun w ↦
        ⟨c.1, P0.baseChange (algebraMap ℚ (NFC.NF c.1.1)) P0.k d.1 d.2.1, w, none⟩)
  | some (e, k₀, DA, k') =>
      let P := P0.baseChange (algebraMap ℚ (NFC.NF c.1.1)) P0.k [] ⟨1, [], 0⟩
      if mobCheck P (P.mobT e k₀ DA k' d.1 d.2.1) e k₀ DA then
        (decideLogTPW (redAtM c.1.1) (P.mobT e k₀ DA k' d.1 d.2.1) d.2.2.1 [] d.2.2.2.1).map
          (Option.map fun w ↦ ⟨c.1, P.mobT e k₀ DA k' d.1 d.2.1, w, some (e, k₀, DA, k')⟩)
      else none

lemma CertQ.runW_isSome (c : CertQ) : (CertQ.runW P0 c).map Option.isSome = c.run P0 := by
  have : Fact (Irreducible (toPoly c.1.1)) := ⟨Kron.irredQ_sound _ c.1.2⟩
  unfold CertQ.runW CertQ.run
  dsimp only
  split
  · rename_i heq
    rw [heq]
    dsimp only
    rw [Option.map_map, ← decideLogTPW_isSome]
    congr 1
    funext o
    cases o <;> rfl
  · rename_i e k₀ DA k' heq
    rw [heq]
    dsimp only
    split_ifs
    · rw [Option.map_map, ← decideLogTPW_isSome]
      congr 1
      funext o
      cases o <;> rfl
    · rfl

/-- `decideEnum` with the witness. -/
def decideEnumW (N : ℕ) : Option (Option CurveWQ) :=
  (List.range N).findSome? fun k ↦ (Encodable.decode (α := CertQ) k).bind (CertQ.runW P0)

lemma decideEnumW_isSome (N : ℕ) : (decideEnumW P0 N).map Option.isSome = decideEnum P0 N := by
  unfold decideEnumW decideEnum
  rw [findSome?_map']
  congr 1
  funext k
  rw [Option.map_bind]
  congr 1
  funext c
  simp only [Function.comp_apply]
  exact CertQ.runW_isSome P0 c

end Loop

/-- **`decideTotal` with the curve antiderivative.** -/
def decideTotalW (Fc A : BPoly ℚ) (D : CPoly ℚ) (N : ℕ) : Option (Option CurveWQ) :=
  (decideCurveQW Fc A D).or (decideEnumW (curveProbQ Fc A D) N)

lemma decideTotalW_isSome (Fc A : BPoly ℚ) (D : CPoly ℚ) (N : ℕ) :
    (decideTotalW Fc A D N).map Option.isSome = decideTotal Fc A D N := by
  unfold decideTotalW decideTotal
  rw [← decideCurveQW_isSome, ← decideEnumW_isSome]
  cases decideCurveQW Fc A D <;> rfl

/-- **Where a witness comes from**: for a direct witness, the problem is a base change of `P0`;
for a Möbius witness, the problem is the transform (`mobCheck`) of the base change of `P0` at the
recorded data; in both cases the witness is returned by `decideLogW`. -/
def CurveWQ.Src (P0 : CurveProb ℚ) (W : CurveWQ) : Prop :=
  haveI : Fact (Irreducible (toPoly W.M.1)) := ⟨Kron.irredQ_sound _ W.M.2⟩
  (W.mob = none → ∃ pts inf, W.P = P0.baseChange (algebraMap ℚ (NFC.NF W.M.1)) P0.k pts inf) ∧
  (∀ e k₀ DA k', W.mob = some (e, k₀, DA, k') →
    mobCheck (P0.baseChange (algebraMap ℚ (NFC.NF W.M.1)) P0.k [] ⟨1, [], 0⟩) W.P e k₀ DA = true) ∧
  ∃ ws, W.P.decideLogW ws = some (some W.w)

section SrcLemmas

variable (P0 : CurveProb ℚ)

lemma stageNFW_src (fast : Bool) (M : CPoly ℚ) [Fact (Irreducible (toPoly M))] (kI : ℕ)
    (exs : List ℕ) (ex fuel L tp B : ℕ) (pqs : List (ℕ × ℕ)) (P : CurveProb (NFC.NF M))
    (w : CurveW (NFC.NF M))
    (h : stageNFW P0 fast M kI exs ex fuel L tp B pqs = .ok (some (some (P, w)))) :
    (∃ pts inf, P = P0.baseChange (algebraMap ℚ (NFC.NF M)) P0.k pts inf) ∧
      ∃ ws, P.decideLogW ws = some (some w) := by
  unfold stageNFW at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · have h' := Except.ok.inj h
    simp only [Option.bind_eq_some_iff, List.findSome?_eq_some_iff] at h'
    obtain ⟨T, -, -, e, -, -, ⟨Pa, -, l1, pq, l2, -, hpq, -⟩, -⟩ := h'
    obtain ⟨o, ho, hoe⟩ := Option.map_eq_some_iff.mp hpq
    obtain ⟨w', rfl, he⟩ := Option.map_eq_some_iff.mp hoe
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨⟨_, _, rfl⟩, decideAutoFullW_src ho⟩

lemma decideLoopW_src (fast : Bool) (kI : ℕ) (exs : List ℕ) (ex fuel L tp B : ℕ)
    (pqs : List (ℕ × ℕ)) : ∀ (m : ℕ) (M : CPoly ℚ) (hM : Kron.irredQ M = true) (W : CurveWQ),
    decideLoopW P0 fast kI exs ex fuel L tp B pqs m M hM = some (some W) → W.Src P0
  | 0, _, _, _, h => absurd h (by simp [decideLoopW])
  | m + 1, M, hM, W, h => by
    have : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    unfold decideLoopW at h
    split at h
    · rename_i r hr
      obtain ⟨o, rfl, hoe⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨⟨P, w⟩, rfl, rfl⟩ := Option.map_eq_some_iff.mp hoe
      obtain ⟨h1, h2⟩ := stageNFW_src P0 fast M kI exs ex fuel L tp B pqs P w hr
      exact ⟨fun _ ↦ h1, fun _ _ _ _ h ↦ absurd h (by simp), h2⟩
    · split at h
      · exact decideLoopW_src fast kI exs ex fuel L tp B pqs m _ _ W h
      · exact absurd h (by simp)

lemma CertQ.runW_src (c : CertQ) (W : CurveWQ) (h : CertQ.runW P0 c = some (some W)) :
    W.Src P0 := by
  have : Fact (Irreducible (toPoly c.1.1)) := ⟨Kron.irredQ_sound _ c.1.2⟩
  unfold CertQ.runW at h
  dsimp only at h
  split at h
  · obtain ⟨o, ho, hoe⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨w, rfl, rfl⟩ := Option.map_eq_some_iff.mp hoe
    exact ⟨fun _ ↦ ⟨_, _, rfl⟩, fun _ _ _ _ h ↦ absurd h (by simp), _, decideLogTPW_src ho⟩
  · rename_i e k₀ DA k' _
    split_ifs at h with hm
    obtain ⟨o, ho, hoe⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨w, rfl, rfl⟩ := Option.map_eq_some_iff.mp hoe
    refine ⟨fun h ↦ absurd h (by simp), fun e' k₀' DA' k'' he ↦ ?_, _, decideLogTPW_src ho⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    exact hm

lemma decideEnumW_src (N : ℕ) (W : CurveWQ) (h : decideEnumW P0 N = some (some W)) :
    W.Src P0 := by
  unfold decideEnumW at h
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨c, -, hc⟩ := Option.bind_eq_some_iff.mp hk
  exact CertQ.runW_src P0 c W hc

end SrcLemmas

lemma decideTotalW_src (Fc A : BPoly ℚ) (D : CPoly ℚ) (N : ℕ) (W : CurveWQ)
    (h : decideTotalW Fc A D N = some (some W)) : W.Src (curveProbQ Fc A D) := by
  unfold decideTotalW at h
  cases hq : decideCurveQW Fc A D with
  | none =>
    rw [hq, Option.none_or] at h
    exact decideEnumW_src _ N W h
  | some o =>
    rw [hq, Option.some_or] at h
    rw [h] at hq
    exact decideLoopW_src _ _ _ _ _ _ _ _ _ _ _ _ _ W hq

section Valid

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The curve antiderivative, explicitly**: a direct witness of the problem `P0` over `ℚ` gives,
on any realization of the curve over algebraically closed constants (with any embedding
`ι : ℚ[γ]/(M) → Kc`), `f = v′ (+ ∑ⱼ cⱼ uⱼ′/uⱼ)` for the problem over `ℚ[γ]/(M)`, whose integrand is
`f`. -/
theorem CurveWQ.valid (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (P0 : CurveProb ℚ) (hSF : S.F = (toB P0.Fc).map (mapRingHom (algebraMap ℚ Kc)))
    (W : CurveWQ) (hsrc : W.Src P0) (hmob : W.mob = none) :
    haveI : Fact (Irreducible (toPoly W.M.1)) := ⟨Kron.irredQ_sound _ W.M.2⟩
    ∀ ι : NFC.NF W.M.1 →+* Kc, S.fE P0 (algebraMap ℚ Kc) = S.fE W.P ι ∧ W.w.Valid S W.P ι := by
  have : Fact (Irreducible (toPoly W.M.1)) := ⟨Kron.irredQ_sound _ W.M.2⟩
  intro ι
  obtain ⟨pts, inf, hP⟩ := hsrc.1 hmob
  obtain ⟨ws, hw⟩ := hsrc.2.2
  have hι : ι.comp (algebraMap ℚ (NFC.NF W.M.1)) = algebraMap ℚ Kc := Subsingleton.elim _ _
  have hSF' : S.F = (toB W.P.Fc).map (mapRingHom ι) := by
    rw [hP, hSF, CurveProb.baseChange, toB_mapL, Polynomial.map_map, mapRingHom_comp, hι]
  refine ⟨?_, CurveProb.decideLogW_valid S hC hx W.P ι hSF' ws W.w hw⟩
  rw [hP, S.fE_baseChange, hι]

end Valid

end Curves
