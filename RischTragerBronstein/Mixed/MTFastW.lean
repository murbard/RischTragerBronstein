import RischTragerBronstein.Mixed.MTFast

/-!
# The fast path over the line, with the antiderivative

`elMWF` is `elMW` with the level-`0` call of `decideTotal` replaced by an immediate answer on a
line (the witness at level `0` is the base integrand itself; it is integrated by
`integrateRational` when rendered). `elMWF_elMW`: an answer of `elMWF` is an answer of `elMW` at
some bound; hence `elMWF_valid` (returned antiderivatives are valid) and `elMWF_none` (the answer
"not elementary" is correct).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- One level of `elMW`: a final answer, or the code to integrate one level down together with
the pieces of this level. -/
def stepMW (m : ℕ) (q : LC (m + 1)) : Option (Option (ADW (m + 1))) ⊕ (LC m × LevelW m) :=
  let O := MO Fc ks m
  let q' : GFrac (LC m) := q
  if GPoly.isZero O q'.2 then .inl (some (some (zeroW Fc ks (m + 1))))
  else match ks m with
  | .prim η =>
    let w := wKC O (.prim η)
    let h := GPoly.hermite O w q'.1 q'.2
    let qr := GPoly.divMod O h.b h.s
    if !(GPoly.residueCheck O w qr.2 h.s) then .inl (some none)
    else match mchainW Fc ks lv m η qr.1 qr.1.length O.zero with
      | none => .inl (some none)
      | some (Q1, P) => .inr (mconst Fc ks m η qr.1 Q1,
          ⟨h.gn, h.gd, P, 0, qr.2, h.s, GPoly.residuePoly O w qr.2 h.s⟩)
  | .exp a =>
    let w := wKC O (.exp a)
    let sp := GPoly.expSplit O q'.1 q'.2
    let k := sp.2.2.1
    let h := GPoly.hermite O w sp.1 sp.2.2.2
    let qr := GPoly.divMod O h.b h.s
    let Λ := GPoly.add O (GPoly.mul O qr.1 (GPoly.monomial O k O.one)) sp.2.1
    if !(GPoly.residueCheck O w qr.2 h.s) then .inl (some none)
    else match (List.range (Λ.length + k + 1)).mapM fun j ↦
        if j = k then some O.zero
        else rdeSolM Fc ks lv m (O.mul (mcst Fc ks m ((j : ℚ) - k)) a) (Λ.getD j O.zero) with
      | none => .inl (some none)
      | some ys => .inr (Λ.getD k O.zero,
          ⟨h.gn, h.gd, ys, k, qr.2, h.s, GPoly.residuePoly O w qr.2 h.s⟩)

/-- **`elMW`, fast over the line.** -/
def elMWF : (m : ℕ) → LC m → ℕ → Option (Option (ADW m))
  | 0, q, N => if isLine Fc then some (some (q : ADW 0))
      else (decideTotal Fc ((codeW (cvNorm Fc q)).map trim) (codeQ (cvNorm Fc q)) N).map
        fun b ↦ if b then some (q : ADW 0) else none
  | m + 1, q, N =>
    match stepMW Fc ks lv m q with
    | .inl r => r
    | .inr (c, lw) => (elMWF m c N).map fun o ↦ o.map fun w0 ↦ ((lw, w0) : LevelW m × ADW m)

variable {Fc ks lv}

/-- `elMW` in terms of `stepMW`. -/
lemma elMW_succ (m : ℕ) (q : LC (m + 1)) (N : ℕ) :
    elMW Fc ks lv (m + 1) q N = match stepMW Fc ks lv m q with
      | .inl r => r
      | .inr (c, lw) =>
        (elMW Fc ks lv m c N).map fun o ↦ o.map fun w0 ↦ ((lw, w0) : LevelW m × ADW m) := by
  rw [elMW]
  unfold stepMW
  dsimp only
  by_cases hz : GPoly.isZero (MO Fc ks m) (q : GFrac (LC m)).2 = true
  · rw [if_pos hz, if_pos hz]
  · rw [if_neg hz, if_neg hz]
    cases ks m with
    | prim η =>
      dsimp only
      split_ifs with hr
      · rfl
      · split <;> (rename_i heq; simp only [heq])
    | exp a =>
      dsimp only
      split_ifs with hr
      · rfl
      · split <;> (rename_i heq; simp only [heq])

/-- **An answer of `elMWF` is an answer of `elMW` at some bound.** -/
theorem elMWF_elMW (h0 : isLine Fc = true → ∀ q : LC 0, ∃ N', elM Fc ks lv 0 q N' = some true) :
    ∀ (m : ℕ) (q : LC m) (N : ℕ) (r : Option (ADW m)), elMWF Fc ks lv m q N = some r →
      ∃ N', elMW Fc ks lv m q N' = some r := by
  intro m
  induction m with
  | zero =>
    intro q N r h
    unfold elMWF at h
    by_cases hl : isLine Fc = true
    · rw [if_pos hl] at h
      obtain rfl := Option.some.inj h
      obtain ⟨N', hN'⟩ := h0 hl q
      refine ⟨N', ?_⟩
      have hN'' : decideTotal Fc ((codeW (cvNorm Fc q)).map trim) (codeQ (cvNorm Fc q)) N' =
          some true := hN'
      rw [elMW, hN'']
      rfl
    · rw [if_neg hl] at h
      exact ⟨N, by rw [elMW]; exact h⟩
  | succ m ih =>
    intro q N r h
    rw [elMWF] at h
    rcases hs : stepMW Fc ks lv m q with r0 | ⟨c, lw⟩
    · rw [hs] at h
      exact ⟨0, by rw [elMW_succ, hs]; exact h⟩
    · rw [hs] at h
      dsimp only at h
      rcases hrec : elMWF Fc ks lv m c N with _ | o
      · rw [hrec] at h; cases h
      · rw [hrec] at h
        obtain ⟨N', hN'⟩ := ih c N o hrec
        exact ⟨N', by rw [elMW_succ, hs]; dsimp only; rw [hN']; exact h⟩

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- `elM` eventually answers `true` at level `0` on a line (given any realization). -/
lemma elM_line (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hsh : curveShape Fc = true) (T : MTower Fc ks Cc L) (k : ℕ)
    (hc : certC Fc ks lv k = true) (hl : isLine Fc = true) (q0 : LC 0) :
    ∃ N', elM Fc ks lv 0 q0 N' = some true := by
  obtain ⟨T0, hT0n, hT0ev, hT0gen, -⟩ := T.exists_sub 0 (by omega)
  have hc0 : certC Fc ks lv 0 = true := MTower.certC_le hc 0 (Nat.zero_le k)
  obtain ⟨N₀, hN⟩ := elM_decides_any hmon hdeg hsh T0 0 hT0n hc0 hT0gen q0
  obtain ⟨b', hb', hiff, -⟩ := hN N₀ le_rfl
  have : b' = true := hiff.mp (T0.line_hasElementaryIntegral hl q0)
  exact ⟨N₀, this ▸ hb'⟩

/-- **Every antiderivative returned by `elMWF` is valid.** -/
theorem elMWF_valid (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hsh : curveShape Fc = true) (T : MTower Fc ks Cc L) (n : ℕ) (hn : T.n = n)
    (hc : certC Fc ks lv n = true) (hgen : ∀ z : L, z ∈ T.F n) (q : LC n) (N : ℕ) (w : ADW n)
    (h : elMWF Fc ks lv n q N = some (some w)) : T.ValidW n q w := by
  obtain ⟨N', hN'⟩ := elMWF_elMW (fun hl q0 ↦ elM_line hmon hdeg hsh T n hc hl q0) n q N _ h
  exact T.elMW_valid hmon hdeg hsh n hn hc hgen n le_rfl q N' w hN'

/-- **The answer "not elementary" of `elMWF` is correct.** -/
theorem elMWF_none (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hsh : curveShape Fc = true) (T : MTower Fc ks Cc L) (n : ℕ) (hn : T.n = n)
    (hc : certC Fc ks lv n = true) (hgen : ∀ z : L, z ∈ T.F n) (q : LC n) (N : ℕ)
    (h : elMWF Fc ks lv n q N = some none) : ¬HasElementaryIntegral (T.ev n q) := by
  obtain ⟨N', hN'⟩ := elMWF_elMW (fun hl q0 ↦ elM_line hmon hdeg hsh T n hc hl q0) n q N _ h
  have h1 := elMW_isSome Fc ks lv n q N'
  rw [hN'] at h1
  have h2 := (elM_sound hmon hdeg hsh T n hn hc hgen q N' false h1.symm).1
  intro hE
  exact Bool.false_ne_true (h2.mp hE)

end Curves.MT
