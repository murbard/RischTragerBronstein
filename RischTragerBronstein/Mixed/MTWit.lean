import RischTragerBronstein.Mixed.MTSound

/-!
# Mixed towers over a curve: the antiderivative, not only the answer

`elMW Fc ks lv m q N` runs `elM` and, when the integral is elementary, returns the pieces of an
antiderivative, level by level (`ADW m`):

* at a level `m + 1` (`t = tₘ`), a `LevelW m`: the Hermite part `gn / gd`, the polynomial part
  `pc(t) / t^kk` (the limited-integration chain `mchainW` below a logarithm, `kk = 0`; the
  solutions of the Risch equations below an exponential), and the logarithmic part `b / s` with
  its residue polynomial `r` — whose integral is `∑_{s(α)=0} r(α) log (t − α)` (minus
  `(∑ r(α)) log t` over an exponential; the `r(α)` are constants);
* at level `0`, the remaining integrand on the curve, whose integral `decideTotal` found
  elementary.

`elMW_isSome`: `elMW` answers exactly when `elM` does, with `some` iff `elM` says `true`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- One step of the chain with its constant: `(Q', γ)` with `Q'′ + γ η = a − (j + 1) η Q`. -/
def mchainStepW (m : ℕ) (η a Q : LC m) (j : ℕ) : Option (LC m × ℚ) :=
  ((paramLimC Fc ks lv m [mchainRHS Fc ks m η a Q j, η]).find?
    fun r ↦ decide (r.1.getD 0 0 ≠ 0)).map
    fun r ↦ ((MO Fc ks m).mul (mcst Fc ks m (r.1.getD 0 0)⁻¹) r.2, -(r.1.getD 1 0 / r.1.getD 0 0))

/-- The chain from index `j` down to `1`, returning `Q₁` and the coefficients `P₀ = 0, P₁, …, Pⱼ₊₁`
of the polynomial part: `Pᵢ′ + (i + 1) η Pᵢ₊₁ = aᵢ` (`1 ≤ i ≤ j`), `Pⱼ₊₁ ≡ Q` up to a rational. -/
def mchainW (m : ℕ) (η : LC m) (Λ : GPoly (LC m)) : ℕ → LC m → Option (LC m × GPoly (LC m))
  | 0, Q => some (Q, [(MO Fc ks m).zero, Q])
  | j + 1, Q => (mchainStepW Fc ks lv m η (Λ.getD (j + 1) (MO Fc ks m).zero) Q (j + 1)).bind
      fun p ↦ (mchainW m η Λ j p.1).map fun R ↦
        (R.1, R.2 ++ [(MO Fc ks m).add Q (mcst Fc ks m (p.2 / (j + 2 : ℕ)))])

/-- A solution of the Risch equation `y′ + h′ y = f` at level `m`, if one is found. -/
def rdeSolM (m : ℕ) (h f : LC m) : Option (LC m) :=
  ((prdeC Fc ks lv m ⟨h, []⟩ [f]).find? fun r ↦ decide (r.1.getD 0 0 ≠ 0)).map
    fun r ↦ (MO Fc ks m).mul (mcst Fc ks m (r.1.getD 0 0)⁻¹) r.2

/-- **The pieces of an antiderivative at a level `m + 1`** (codes of level `m`, polynomials in
`t = tₘ`): `∫ q = gn/gd + pc/t^kk + ∫ b/s + ∫ (constant term at level m)`; `r` is the residue
polynomial of `b / s`. -/
structure LevelW (m : ℕ) where
  gn : GPoly (LC m)
  gd : GPoly (LC m)
  pc : GPoly (LC m)
  kk : ℕ
  b : GPoly (LC m)
  s : GPoly (LC m)
  r : GPoly (LC m)

/-- **Antiderivative witnesses**: one `LevelW` per level, and the remaining integrand on the
curve. -/
def ADW : ℕ → Type
  | 0 => LC 0
  | m + 1 => LevelW m × ADW m

/-- The witness of the zero integrand. -/
def zeroW : (m : ℕ) → ADW m
  | 0 => (MO Fc ks 0).zero
  | m + 1 => (⟨[], [(MO Fc ks m).one], [], 0, [], [(MO Fc ks m).one], []⟩, zeroW m)

/-- **Elementary integration with the antiderivative**: `none` — no answer at this bound;
`some none` — not elementary; `some (some w)` — elementary, with the pieces `w`. -/
def elMW : (m : ℕ) → LC m → ℕ → Option (Option (ADW m))
  | 0, q, N => (decideTotal Fc ((codeW (cvNorm Fc q)).map trim) (codeQ (cvNorm Fc q)) N).map
      fun b ↦ if b then some (q : ADW 0) else none
  | m + 1, q, N =>
    let O := MO Fc ks m
    let q' : GFrac (LC m) := q
    if GPoly.isZero O q'.2 then some (some (zeroW Fc ks (m + 1)))
    else match ks m with
    | .prim η =>
      let w := wKC O (.prim η)
      let h := GPoly.hermite O w q'.1 q'.2
      let qr := GPoly.divMod O h.b h.s
      if !(GPoly.residueCheck O w qr.2 h.s) then some none
      else match mchainW Fc ks lv m η qr.1 qr.1.length O.zero with
        | none => some none
        | some (Q1, P) =>
          (elMW m (mconst Fc ks m η qr.1 Q1) N).map fun o ↦ o.map fun w0 ↦
            ((⟨h.gn, h.gd, P, 0, qr.2, h.s, GPoly.residuePoly O w qr.2 h.s⟩ : LevelW m), w0)
    | .exp a =>
      let w := wKC O (.exp a)
      let sp := GPoly.expSplit O q'.1 q'.2
      let k := sp.2.2.1
      let h := GPoly.hermite O w sp.1 sp.2.2.2
      let qr := GPoly.divMod O h.b h.s
      let Λ := GPoly.add O (GPoly.mul O qr.1 (GPoly.monomial O k O.one)) sp.2.1
      if !(GPoly.residueCheck O w qr.2 h.s) then some none
      else match (List.range (Λ.length + k + 1)).mapM fun j ↦
          if j = k then some O.zero
          else rdeSolM Fc ks lv m (O.mul (mcst Fc ks m ((j : ℚ) - k)) a) (Λ.getD j O.zero) with
        | none => some none
        | some ys =>
          (elMW m (Λ.getD k O.zero) N).map fun o ↦ o.map fun w0 ↦
            ((⟨h.gn, h.gd, ys, k, qr.2, h.s, GPoly.residuePoly O w qr.2 h.s⟩ : LevelW m), w0)

/-! ### Agreement with `elM` -/

lemma mchainStepW_fst (m : ℕ) (η a Q : LC m) (j : ℕ) :
    (mchainStepW Fc ks lv m η a Q j).map Prod.fst = mchainStep Fc ks lv m η a Q j := by
  simp only [mchainStepW, mchainStep, Option.map_map]
  rfl

lemma mchainW_fst (m : ℕ) (η : LC m) (Λ : GPoly (LC m)) :
    ∀ (j : ℕ) (Q : LC m), (mchainW Fc ks lv m η Λ j Q).map Prod.fst = mchain Fc ks lv m η Λ j Q
  | 0, Q => rfl
  | j + 1, Q => by
    simp only [mchainW, mchain]
    rw [← mchainStepW_fst]
    cases mchainStepW Fc ks lv m η (Λ.getD (j + 1) (MO Fc ks m).zero) Q (j + 1) with
    | none => rfl
    | some p =>
      simp only [Option.bind_some, Option.map_some]
      rw [← mchainW_fst m η Λ j p.1, Option.map_map]
      rfl

lemma rdeSolM_isSome (m : ℕ) (h f : LC m) :
    (rdeSolM Fc ks lv m h f).isSome = rdeOKM Fc ks lv m h f := by
  simp only [rdeSolM, rdeOKM, Option.isSome_map]
  rw [Bool.eq_iff_iff, List.find?_isSome, List.any_eq_true]

lemma mapM_isSome_all {α β : Type*} (f : α → Option β) :
    ∀ l : List α, (l.mapM f).isSome = l.all fun a ↦ (f a).isSome
  | [] => rfl
  | a :: l => by
    rw [List.mapM_cons, List.all_cons, ← mapM_isSome_all f l]
    cases f a <;> cases l.mapM f <;> rfl


lemma ite_true_or (p : Prop) [Decidable p] (b : Bool) :
    (if p then true else b) = (decide p || b) := by
  by_cases h : p <;> simp [h]

/-- **`elMW` answers exactly as `elM`.** -/
theorem elMW_isSome : ∀ (m : ℕ) (q : LC m) (N : ℕ),
    (elMW Fc ks lv m q N).map Option.isSome = elM Fc ks lv m q N
  | 0, q, N => by
    simp only [elMW, elM, Option.map_map]
    cases decideTotal Fc ((codeW (cvNorm Fc q)).map trim) (codeQ (cvNorm Fc q)) N with
    | none => rfl
    | some b => cases b <;> rfl
  | m + 1, q, N => by
    simp only [elMW, elM]
    split_ifs with hz
    · rfl
    · cases hk : ks m with
      | prim η =>
        simp only
        split_ifs with hr
        · rfl
        · rw [← mchainW_fst]
          cases mchainW Fc ks lv m η _ _ _ with
          | none => rfl
          | some p =>
            obtain ⟨Q1, P⟩ := p
            simp only [Option.map_some]
            rw [← elMW_isSome m, Option.map_map]
            congr 1
            funext o
            cases o <;> rfl
      | exp a =>
        simp only
        split_ifs with hr hall
        · rfl
        · split
          · rfl
          · rename_i ys heq
            exfalso
            have h1 := congrArg Option.isSome heq
            rw [mapM_isSome_all] at h1
            simp only [apply_ite Option.isSome, Option.isSome_some, rdeSolM_isSome, ite_true_or]
              at h1
            simp only [Bool.not_eq_true'] at hall
            rw [hall] at h1
            exact Bool.false_ne_true h1
        · split
          · rename_i heq
            exfalso
            have h1 := congrArg Option.isSome heq
            rw [mapM_isSome_all] at h1
            simp only [apply_ite Option.isSome, Option.isSome_some, Option.isSome_none,
              rdeSolM_isSome, ite_true_or] at h1
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hall
            rw [hall] at h1
            exact Bool.false_ne_true h1.symm
          · rw [← elMW_isSome m, Option.map_map]
            congr 1
            funext o
            cases o <;> rfl

end Curves.MT
