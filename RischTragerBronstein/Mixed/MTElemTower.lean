import RischTragerBronstein.Mixed.MTSound

/-!
# A mixed tower is an elementary extension of each of its levels

`MTower.isElementary_F`: for a realization of height `n` generating `L` with a valid certificate,
`L` is an elementary extension of `F k` for every `k ≤ n` (each `tⱼ` is a logarithm or an
exponential over `F j`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **`F n` is an elementary tower over every level.** -/
theorem isElementary_tower (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (n : ℕ)
    (hn : T.n = n) (hc : certC Fc ks lv n = true) (k : ℕ) (hk : k ≤ n) :
    IsElementaryTower (extendScalars (T.F_mono hk) : IntermediateField (T.F k) L) := by
  classical
  have MS := T.mspecs hmon hdeg lv n (by omega) hc
  have key : ∀ j (hkj : k ≤ j), j ≤ n →
      IsElementaryTower (extendScalars (T.F_mono hkj) : IntermediateField (T.F k) L) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro _
      rw [show (extendScalars (T.F_mono (le_refl k)) : IntermediateField (T.F k) L) = ⊥ from
        extendScalars_self _]
      exact .base
    | succ j hkj ih =>
      intro hjn
      have hjn' : j < T.n := by omega
      have heq : (extendScalars (T.F_mono (show k ≤ j + 1 by omega)) :
          IntermediateField (T.F k) L) =
          extendScalars (T.F_mono hkj) ⊔ (T.F k)⟮T.ts j⟯ := by
        apply le_antisymm
        · intro z hz
          rw [mem_extendScalars, T.mem_F_succ] at hz
          have hle : T.F j ≤ (extendScalars (T.F_mono hkj) ⊔ (T.F k)⟮T.ts j⟯ :
              IntermediateField (T.F k) L).restrictScalars Cc := fun y hy ↦
            (le_sup_left : extendScalars (T.F_mono hkj) ≤ _) ((mem_extendScalars _).mpr hy)
          have ht : T.ts j ∈ (extendScalars (T.F_mono hkj) ⊔ (T.F k)⟮T.ts j⟯ :
              IntermediateField (T.F k) L) :=
            (le_sup_right : (T.F k)⟮T.ts j⟯ ≤ _) (mem_adjoin_simple_self _ _)
          have := (adjoin_le_iff (F := T.F j) (T := extendScalars (K := Cc) hle)).mpr
            (Set.singleton_subset_iff.mpr ht) hz
          exact this
        · refine sup_le (fun z hz ↦ ?_) ?_
          · exact (mem_extendScalars _).mpr (T.le_succ j ((mem_extendScalars _).mp hz))
          · rw [adjoin_simple_le_iff, mem_extendScalars]
            exact T.ts_mem j
      rw [heq]
      refine .adjoin _ _ (ih (by omega)) ?_
      have htj := T.ht j hjn'
      cases hkj' : ks j with
      | prim η =>
        right; left
        obtain ⟨v, hv0, hvη⟩ := MS.hyp.log j (by omega) η hkj'
        refine ⟨(v : L), (mem_extendScalars _).mpr v.2, fun h0 ↦ hv0 (Subtype.ext h0), ?_⟩
        rw [htj, hkj']
        change T.ev j η = _
        have := congrArg Subtype.val hvη
        rw [T.coe_logDeriv_FX] at this
        exact this
      | exp a =>
        right; right
        refine ⟨T.hts0 j hjn' a hkj', T.ev j a, (mem_extendScalars _).mpr (T.ev_mem j a), ?_⟩
        rw [logDeriv, htj, hkj']
        change (T.ev j a)′ * T.ts j / T.ts j = _
        rw [mul_div_assoc, div_self (T.hts0 j hjn' a hkj'), mul_one]
  exact key n hk le_rfl

/-- **`L` is an elementary extension of every level.** -/
theorem isElementary_F (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (n : ℕ)
    (hn : T.n = n) (hc : certC Fc ks lv n = true) (hgen : ∀ z : L, z ∈ T.F n) (k : ℕ)
    (hk : k ≤ n) : IsElementaryExtension (T.F k) L := by
  have htop := T.isElementary_tower hmon hdeg n hn hc k hk
  rwa [show (extendScalars (T.F_mono hk) : IntermediateField (T.F k) L) = ⊤ from
    eq_top_iff.mpr fun z _ ↦ (mem_extendScalars _).mpr (hgen z)] at htop

/-- **An algebraic extension of the tower is elementary over every level**: `L = F n (θ)` with
`θ` integral over `F n`. -/
theorem isElementary_alg (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (n : ℕ)
    (hn : T.n = n) (hc : certC Fc ks lv n = true) (θ : L) (hθ : IsIntegral (T.F n) θ)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F n) {θ}) (k : ℕ)
    (hk : k ≤ n) : IsElementaryExtension (T.F k) L := by
  set E : IntermediateField (T.F k) L := extendScalars (T.F_mono hk) with hE
  have htop : E ⊔ (T.F k)⟮θ⟯ = ⊤ := by
    refine eq_top_iff.mpr fun z _ ↦ ?_
    have hle : T.F n ≤ (E ⊔ (T.F k)⟮θ⟯ : IntermediateField (T.F k) L).restrictScalars Cc :=
      fun y hy ↦ (le_sup_left : E ≤ _) ((mem_extendScalars _).mpr hy)
    have ht : θ ∈ (E ⊔ (T.F k)⟮θ⟯ : IntermediateField (T.F k) L) :=
      (le_sup_right : (T.F k)⟮θ⟯ ≤ _) (mem_adjoin_simple_self _ _)
    exact (adjoin_le_iff (F := T.F n) (T := extendScalars (K := Cc) hle)).mpr
      (Set.singleton_subset_iff.mpr ht) (hgen z)
  have hT : IsElementaryTower (E ⊔ (T.F k)⟮θ⟯) := by
    refine .adjoin _ _ (T.isElementary_tower hmon hdeg n hn hc k hk) (Or.inl ?_)
    obtain ⟨p, hpm, hp⟩ := hθ
    let φ : T.F n →+* E :=
      { toFun := fun x ↦ ⟨x, (mem_extendScalars _).mpr x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    refine ⟨p.map φ, (hpm.map φ).ne_zero, ?_⟩
    rw [aeval_def, eval₂_map]
    exact hp
  unfold IsElementaryExtension
  rwa [htop] at hT

end MTower

end Curves.MT
