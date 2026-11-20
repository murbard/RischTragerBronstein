import RischTragerBronstein.Torsion.AutoLog

/-!
# Curve antiderivatives: the witnesses of `true`

A `true` answer of the curve decision comes from `CurveProb.decideLog`: the coefficients `cs` of
the exact part `v` (`linSolve`) and, when there are residues, the log witnesses `ws`, with
`f = v′` or `f = v′ + ∑ⱼ cⱼ uⱼ′/uⱼ` (`uⱼ = Wⱼ/Qⱼ`). `decideLogW`, `decideLogTW`, `decideLogTPW`,
`decideAutoFullW` return these data along the answers (`CurveW`), and answer exactly as the
deciders (`…_isSome`).
-/

namespace Curves

open CPoly Sup EllQuad.QCoords Differential Polynomial

/-- **The witness of an elementary integral on a curve**: the exact-part coefficients, the log
witnesses and whether the logarithmic part is used. -/
structure CurveW (F : Type*) where
  cs : List F
  ws : List (LogWit F)
  logs : Bool

section Defs

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- `decideLog` with the witness. -/
def CurveProb.decideLogW (P : CurveProb F) (ws : List (LogWit F)) : Option (Option (CurveW F)) :=
  if P.valid then
    match linSolve P.cols P.rhs with
    | none => some none
    | some cs =>
      if P.allRes.all (· = 0) then
        some (if isZeroB (modF P.Fc P.n (P.Pg (P.Wsol cs))) then some ⟨cs, [], false⟩ else none)
      else if P.witCheck ws then
        some (if isZeroB (modF P.Fc P.n (P.logNum cs ws)) then some ⟨cs, ws, true⟩ else none)
      else none
  else none

lemma CurveProb.decideLogW_isSome (P : CurveProb F) (ws : List (LogWit F)) :
    (P.decideLogW ws).map Option.isSome = P.decideLog ws := by
  unfold CurveProb.decideLogW CurveProb.decideLog
  by_cases hv : P.valid = true
  · simp only [hv, if_true]
    cases linSolve P.cols P.rhs with
    | none => rfl
    | some cs =>
      simp only
      by_cases h1 : (P.allRes.all fun x ↦ decide (x = 0)) = true
      · simp only [h1, if_true, Option.map_some]
        split_ifs with h <;> simp [h]
      · simp only [h1, Bool.false_eq_true, if_false]
        by_cases h2 : P.witCheck ws = true
        · simp only [h2, if_true, Option.map_some]
          split_ifs with h <;> simp [h]
        · simp [h2]
  · simp [hv]

/-- `decideLogT` with the witness. -/
def decideLogTW (redAt : (p : ℕ) → Option (RedFns p F)) (P : CurveProb F) (ws : List (LogWit F))
    (tws : List (TorsWit F)) : Option (Option (CurveW F)) :=
  match P.decideLogW ws with
  | some r => some r
  | none => if tws.any (torsOK redAt P) then some none else none

lemma decideLogTW_isSome (redAt : (p : ℕ) → Option (RedFns p F)) (P : CurveProb F)
    (ws : List (LogWit F)) (tws : List (TorsWit F)) :
    (decideLogTW redAt P ws tws).map Option.isSome = decideLogT redAt P ws tws := by
  unfold decideLogTW decideLogT
  rw [← P.decideLogW_isSome ws]
  cases P.decideLogW ws with
  | some r => rfl
  | none => simp only [Option.map_none]; split_ifs <;> rfl

/-- `decideLogTP` with the witness. -/
def decideLogTPW (redAt : (p : ℕ) → Option (RedFns p F)) (P : CurveProb F) (ws : List (LogWit F))
    (tws : List (TorsWit F)) (twps : List (TorsWitP F)) : Option (Option (CurveW F)) :=
  match decideLogTW redAt P ws tws with
  | some r => some r
  | none => if twps.any (torsOKP redAt P) then some none else none

lemma decideLogTPW_isSome (redAt : (p : ℕ) → Option (RedFns p F)) (P : CurveProb F)
    (ws : List (LogWit F)) (tws : List (TorsWit F)) (twps : List (TorsWitP F)) :
    (decideLogTPW redAt P ws tws twps).map Option.isSome = decideLogTP redAt P ws tws twps := by
  unfold decideLogTPW decideLogTP
  rw [← decideLogTW_isSome redAt P ws tws]
  cases decideLogTW redAt P ws tws with
  | some r => rfl
  | none => simp only [Option.map_none]; split_ifs <;> rfl

/-- `decideAutoFull` with the witness. -/
def decideAutoFullW (rf : RootFinder F) (redAt : (p : ℕ) → Option (RedFns p F))
    (P : CurveProb F) (T : GlobalCert F) (L tp B p q : ℕ) : Option (Option (CurveW F)) :=
  let js := (List.finRange (dim F)).mergeSort fun i j ↦ coordCost rf P T L tp i ≤ coordCost rf P T L tp j
  match js.findSome? fun j ↦ ((autoCoord rf redAt P T L tp B p q j).map (·.2)).bind
      fun tws ↦ tws.find? (torsOKP redAt P) with
  | some tw => decideLogTPW redAt P [] [] [tw]
  | none =>
    let cs := (List.finRange (dim F)).map (autoCoord rf redAt P T L tp B p q)
    decideLogTPW redAt P (cs.map fun c ↦ (c.bind (·.1)).getD ⟨1, [[1]], [1]⟩) []
      (cs.flatMap fun c ↦ (c.map (·.2)).getD [])

lemma decideAutoFullW_isSome (rf : RootFinder F) (redAt : (p : ℕ) → Option (RedFns p F))
    (P : CurveProb F) (T : GlobalCert F) (L tp B p q : ℕ) :
    (decideAutoFullW rf redAt P T L tp B p q).map Option.isSome =
      decideAutoFull rf redAt P T L tp B p q := by
  unfold decideAutoFullW decideAutoFull
  dsimp only
  split
  · rename_i tw heq
    rw [heq]
    exact decideLogTPW_isSome _ _ _ _ _
  · rename_i heq
    rw [heq]
    exact decideLogTPW_isSome _ _ _ _ _

end Defs

section Valid

variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
  [Differential C] [Differential L] [DifferentialAlgebra C L]
variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- **A valid curve antiderivative**: `f = v′ (+ ∑ⱼ cⱼ uⱼ′/uⱼ)`, with `uⱼ ≠ 0`. -/
def CurveW.Valid (S : CurveData C L) (P : CurveProb F) (ψ₀ : F →+* C) (w : CurveW F) : Prop :=
  (S.fE P ψ₀ : L) = (S.vvE P ψ₀ w.cs : L)′ +
    (if w.logs then ∑ j : Fin (dim F), algebraMap C L (CurveData.cj ψ₀ w.ws j) *
      ((S.uE ψ₀ (CurveProb.witAt w.ws j) : L)′ / (S.uE ψ₀ (CurveProb.witAt w.ws j) : L)) else 0) ∧
  (w.logs = true → ∀ j : Fin (dim F), (S.uE ψ₀ (CurveProb.witAt w.ws j) : L) ≠ 0)

/-- **The witness of `decideLog` is valid.** -/
theorem CurveProb.decideLogW_valid (S : CurveData C L) (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (P : CurveProb F) (ψ₀ : F →+* C) (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀))
    (ws : List (LogWit F)) (w : CurveW F) (h : P.decideLogW ws = some (some w)) :
    w.Valid S P ψ₀ := by
  unfold CurveProb.decideLogW at h
  by_cases hv : P.valid = true
  swap
  · simp [hv] at h
  simp only [hv, if_true] at h
  have hV := P.valid_spec hv
  split at h
  · simp at h
  · rename_i cs _
    by_cases h1 : (P.allRes.all fun x ↦ decide (x = 0)) = true
    · simp only [h1, if_true, Option.some.injEq] at h
      split_ifs at h with hz
      obtain rfl := (Option.some.inj h).symm
      refine ⟨?_, fun h ↦ absurd h (by simp)⟩
      rw [(S.zeroTest_iff hC hx hSF hV hV.len hV.last cs).mp hz]
      simp only [Bool.false_eq_true, if_false, add_zero]
      rfl
    · simp only [h1, Bool.false_eq_true, if_false] at h
      split_ifs at h with hw hz
      · obtain rfl := (Option.some.inj (Option.some.inj h)).symm
        have h0 := (S.logTest_iff hC hx hSF hV cs ws hw).mp hz
        rw [CurveData.hL, sub_eq_zero, sub_eq_iff_eq_add'] at h0
        refine ⟨?_, fun _ j ↦ S.uE_ne_zero hSF hV _ j (P.witCheck_spec ws hw j)⟩
        simp only [if_true]
        rw [h0]
      · simp at h

end Valid

section Src

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

lemma decideLogTW_src {redAt : (p : ℕ) → Option (RedFns p F)} {P : CurveProb F}
    {ws : List (LogWit F)} {tws : List (TorsWit F)} {w : CurveW F}
    (h : decideLogTW redAt P ws tws = some (some w)) : P.decideLogW ws = some (some w) := by
  unfold decideLogTW at h
  split at h
  · rename_i r hr; rw [hr, h]
  · split_ifs at h
    all_goals simp at h

lemma decideLogTPW_src {redAt : (p : ℕ) → Option (RedFns p F)} {P : CurveProb F}
    {ws : List (LogWit F)} {tws : List (TorsWit F)} {twps : List (TorsWitP F)} {w : CurveW F}
    (h : decideLogTPW redAt P ws tws twps = some (some w)) : P.decideLogW ws = some (some w) := by
  unfold decideLogTPW at h
  split at h
  · rename_i r hr; rw [h] at hr; exact decideLogTW_src hr
  · split_ifs at h
    all_goals simp at h

lemma decideAutoFullW_src {rf : RootFinder F} {redAt : (p : ℕ) → Option (RedFns p F)}
    {P : CurveProb F} {T : GlobalCert F} {L tp B p q : ℕ} {w : CurveW F}
    (h : decideAutoFullW rf redAt P T L tp B p q = some (some w)) :
    ∃ ws, P.decideLogW ws = some (some w) := by
  unfold decideAutoFullW at h
  dsimp only at h
  split at h
  · exact ⟨_, decideLogTPW_src h⟩
  · exact ⟨_, decideLogTPW_src h⟩

end Src

end Curves
