import RischTragerBronstein.Mixed.KRIrr
import RischTragerBronstein.Mixed.KRTwist

/-!
# A number field over the code fields

For `M ∈ ℚ[X]` (irreducible over `Kₘ`), `NFM m M = Kₘ[X]/(M)` (`NFK`), with the reductions
`redAtNFM` (a reduction of `Kₘ` and a simple root of `M` modulo `p`; valid by Hensel,
`redAtNFM_valid`) and, for a root `ρ ∈ Fₘ` of `M`, the evaluation `psiNFM : NFM m M → Fₘ` extending
`psiF` by `X ↦ ρ`. Elements with rational coordinates are `ofQ l`, evaluated as `l(ρ)`
(`psiNFM_ofQ`). For the base `ℚ(x)`, a monic irreducible `M` stays irreducible over every `Kₘ`
(`liftQ_irr_linear`).
-/

open Polynomial Differential IntermediateField CPoly CPoly.Kron

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- `M` over `Kₘ`. -/
def liftQ (m : ℕ) (M : CPoly ℚ) : CPoly (KF Fc m) :=
  CPoly.trim (List.map (fun q : ℚ ↦ (Rat.cast q : KF Fc m)) M)

lemma toPoly_liftQ (m : ℕ) (M : CPoly ℚ) :
    toPoly (liftQ Fc m M) = (toPoly M).map (algebraMap ℚ (KF Fc m)) := by
  rw [liftQ, toPoly_trim]
  induction M with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, toPoly_cons, toPoly_cons, ih, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X, eq_ratCast]

/-- `M` stays irreducible over every code field of a linear base. -/
theorem liftQ_irr_KF (c0 : CPoly ℚ) [Fact (Irreducible (toPoly (fKc [c0, [1]])))]
    (M : CPoly ℚ) (hmon : (toPoly M).Monic) (hirr : Irreducible (toPoly M)) :
    ∀ m, Irreducible ((toPoly M).map (algebraMap ℚ (KF [c0, [1]] m)))
  | 0 => irr_pullback (psiLin c0) _ hmon _ (irr_ratFunc _ hmon hirr)
  | m + 1 => by
    letI := (KB [c0, [1]] m).2.fld
    letI := (KB [c0, [1]] m).2.deq
    letI := (KB [c0, [1]] m).2.cz
    have ih := liftQ_irr_KF c0 M hmon hirr m
    have h := irr_ratFunc _ (hmon.map _) ih
    rw [Polynomial.map_map] at h
    exact irr_pullback (RFC.toRFHom (K := KF [c0, [1]] m)) _ hmon _ h

/-- **Irreducibility over the code fields of a linear base.** -/
theorem liftQ_irr_linear (c0 : CPoly ℚ) [Fact (Irreducible (toPoly (fKc [c0, [1]])))]
    (M : CPoly ℚ) (hmon : (toPoly M).Monic) (hirr : Irreducible (toPoly M)) (m : ℕ) :
    Irreducible (toPoly (liftQ [c0, [1]] m M)) := by
  rw [toPoly_liftQ]; exact liftQ_irr_KF c0 M hmon hirr m

section NFMsec

variable (m : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]

/-- `Kₘ ⊗ N`, `N = ℚ[X]/(M)`. -/
abbrev NFM : Type := NFK.NF (liftQ Fc m M)

/-- `Kₘ → Kₘ ⊗ N`. -/
def embM (a : KF Fc m) : NFM Fc m M := NFK.mk _ [a]

/-- An element with rational coordinates. -/
def ofQ (l : CPoly ℚ) : NFM Fc m M := NFK.mk _ (List.map (fun q : ℚ ↦ (Rat.cast q : KF Fc m)) l)

/-- **The reductions of `Kₘ ⊗ N`**: a reduction of `Kₘ` and a simple root of `M` modulo `p`. -/
def redAtNFM (rs : ℕ → ℕ) (p : ℕ) : Option (RedFns p (NFM Fc m M)) :=
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    match redAtKF Fc m rs p with
    | none => none
    | some R =>
      if (liftQ Fc m M).all R.ok then
        ((List.range p).find? fun i ↦
          evalC ((liftQ Fc m M).map R.red) (i : ZMod p) == 0 &&
          evalC (CPoly.deriv ((liftQ Fc m M).map R.red)) (i : ZMod p) != 0).map fun i ↦
            nfkFns R (liftQ Fc m M) (i : ZMod p)
      else none
  else none

/-- **The reductions of `Kₘ ⊗ N` are induced by embeddings.** -/
theorem redAtNFM_valid (rs : ℕ → ℕ) (p : ℕ) [Fact p.Prime] (R : RedFns p (NFM Fc m M))
    (h : redAtNFM Fc m M rs p = some R) : ∃ φ : NFM Fc m M →+* ℚ_[p], RedValid p R φ := by
  unfold redAtNFM at h
  rw [dif_pos (Fact.out)] at h
  split at h
  · exact absurd h (by simp)
  · rename_i R0 hR0
    split_ifs at h with hok
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
    have hb := List.find?_some hi
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hb
    obtain ⟨φ, hφ⟩ := redAtKF_valid Fc m rs p R0 hR0
    exact nfkFns_exists R0 φ hφ (liftQ Fc m M) (List.all_eq_true.mp hok) _ hb.1 hb.2

end NFMsec

universe u

variable {Fc} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

section Psi

variable (m : ℕ) (hm : T.Tr m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
  (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0)

include hρ in
lemma liftQ_root : (toPoly (liftQ Fc m M)).eval₂ (T.psiF m hm) ρ = 0 := by
  rw [toPoly_liftQ, eval₂_map, show (T.psiF m hm).comp (algebraMap ℚ (KF Fc m)) = algebraMap ℚ (T.F m)
    from RingHom.ext_rat _ _, ← aeval_def, hρ]

/-- **`Kₘ ⊗ N → Fₘ`**, `X ↦ ρ`. -/
noncomputable def psiNFM : NFM Fc m M →+* T.F m :=
  (AdjoinRoot.lift (T.psiF m hm) ρ (T.liftQ_root m hm M ρ hρ)).comp (NFK.toARHom _)

lemma psiNFM_mk (l : CPoly (KF Fc m)) :
    T.psiNFM m hm M ρ hρ (NFK.mk _ l) = (toPoly l).eval₂ (T.psiF m hm) ρ := by
  simp only [psiNFM, RingHom.comp_apply]
  change AdjoinRoot.lift _ _ _ (NFK.toAR _ (NFK.mk _ l)) = _
  rw [NFK.toAR_mk, AdjoinRoot.lift_mk]

lemma psiNFM_val (a : NFM Fc m M) :
    T.psiNFM m hm M ρ hρ a = (toPoly a.1).eval₂ (T.psiF m hm) ρ := by
  simp only [psiNFM, RingHom.comp_apply]
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.mk _ (toPoly a.1)) = _
  rw [AdjoinRoot.lift_mk]

lemma psiNFM_embM (a : KF Fc m) : T.psiNFM m hm M ρ hρ (embM Fc m M a) = T.psiF m hm a := by
  rw [embM, psiNFM_mk]; simp

lemma psiNFM_ofQ (l : CPoly ℚ) : T.psiNFM m hm M ρ hρ (ofQ Fc m M l) = aeval ρ (toPoly l) := by
  rw [ofQ, psiNFM_mk]
  have hmap : ∀ l : List ℚ, toPoly (List.map (fun q : ℚ ↦ (Rat.cast q : KF Fc m)) l) =
      (toPoly l).map (algebraMap ℚ _) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, toPoly_cons, toPoly_cons, ih, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_X, eq_ratCast]
  rw [hmap, eval₂_map, show (T.psiF m hm).comp (algebraMap ℚ (KF Fc m)) = algebraMap ℚ (T.F m)
    from RingHom.ext_rat _ _, ← aeval_def]

end Psi

end MTower

end Curves.MT
