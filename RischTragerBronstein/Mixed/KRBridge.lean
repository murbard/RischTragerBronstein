import RischTragerBronstein.Mixed.KRCyclo
import RischTragerBronstein.Mixed.KRSetup
import RischTragerBronstein.Mixed.KQMBridge

/-!
# The cyclotomic code field and the curve

`psiNF ω`: the ring homomorphism `Kₘ(ζ) → Fₘ` extending `psiF` by `ζ ↦ ω`, for a primitive `n`-th
root of unity `ω ∈ Fₘ` (`Φₙ(ω) = 0`, `cycloQ_spec`). The Galois action `tauN u` (`ζ ↦ ζᵘ`) is read
as `psiNF ω ∘ tauN u = psiNF (ωᵘ)` (`psiNF_tauN`).
-/

open Polynomial Differential IntermediateField CPoly

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

lemma toPoly_expandC {R : Type*} [Field R] [DecidableEq R] (u : ℕ) (hu : 0 < u) :
    ∀ l : List R, toPoly (expandC u l) = expand R u (toPoly l)
  | [] => by simp [expandC]
  | a :: l => by
    rw [expandC, toPoly_cons, CPoly.toPoly_append, toPoly_expandC u hu l, toPoly_cons, map_add, map_mul,
      expand_C, expand_X, List.length_replicate]
    have h0 : toPoly (List.replicate (u - 1) (0 : R)) = 0 := by
      induction (u - 1) with
      | zero => simp
      | succ k ih => simp [List.replicate_succ, ih]
    rw [h0, zero_add, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hu]

namespace MTower

variable (T : MTower Fc ks Cc L)

section NF

variable [Fact (Irreducible (toPoly (fKc Fc)))]
variable (m : ℕ) (hm : T.Tr m) (n : ℕ) (hn : 0 < n) [Fact (Irreducible (toPoly (cycK Fc m n)))]

include hn in
lemma toPoly_cycK_map : (toPoly (cycK Fc m n)).map (T.psiF m hm) = cyclotomic n (T.F m) := by
  rw [cycK, toPoly_trim]
  have hmap : ∀ l : List ℚ, toPoly (List.map (fun q : ℚ ↦ (Rat.cast q : KF Fc m)) l) =
      (toPoly l).map (algebraMap ℚ _) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, toPoly_cons, toPoly_cons, ih, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_X, eq_ratCast]
  rw [hmap, Polynomial.map_map, cycloQ_spec n hn, map_cyclotomic]

include hn in
lemma cycK_root (ω : T.F m) (hω : IsPrimitiveRoot ω n) :
    (toPoly (cycK Fc m n)).eval₂ (T.psiF m hm) ω = 0 := by
  rw [← eval_map, T.toPoly_cycK_map m hm n hn]
  exact (hω.isRoot_cyclotomic hn)

/-- **`Kₘ(ζ) → Fₘ`**, `ζ ↦ ω`. -/
noncomputable def psiNF (ω : T.F m) (hω : IsPrimitiveRoot ω n) : NFz Fc m n →+* T.F m :=
  (AdjoinRoot.lift (T.psiF m hm) ω (T.cycK_root m hm n hn ω hω)).comp (NFK.toARHom _)

lemma psiNF_mk (ω : T.F m) (hω : IsPrimitiveRoot ω n) (l : CPoly (KF Fc m)) :
    T.psiNF m hm n hn ω hω (NFK.mk _ l) = (toPoly l).eval₂ (T.psiF m hm) ω := by
  simp only [psiNF, RingHom.comp_apply]
  change AdjoinRoot.lift _ _ _ (NFK.toAR _ (NFK.mk _ l)) = _
  rw [NFK.toAR_mk, AdjoinRoot.lift_mk]

lemma psiNF_val (ω : T.F m) (hω : IsPrimitiveRoot ω n) (a : NFz Fc m n) :
    T.psiNF m hm n hn ω hω a = (toPoly a.1).eval₂ (T.psiF m hm) ω := by
  simp only [psiNF, RingHom.comp_apply]
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.mk _ (toPoly a.1)) = _
  rw [AdjoinRoot.lift_mk]

lemma psiNF_embNF (ω : T.F m) (hω : IsPrimitiveRoot ω n) (a : KF Fc m) :
    T.psiNF m hm n hn ω hω (embNF Fc m n a) = T.psiF m hm a := by
  rw [embNF, psiNF_mk]; simp

lemma psiNF_zeta (ω : T.F m) (hω : IsPrimitiveRoot ω n) :
    T.psiNF m hm n hn ω hω (zetaN Fc m n) = ω := by
  rw [zetaN, psiNF_mk]; simp

/-- **The Galois action**: `psiNF ω ∘ τ_u = psiNF ωᵘ`. -/
lemma psiNF_tauN (ω : T.F m) (hω : IsPrimitiveRoot ω n) (u : ℕ) (hu : Nat.Coprime u n)
    (hu0 : 0 < u) (a : NFz Fc m n) :
    T.psiNF m hm n hn ω hω (tauN Fc m n u a) =
      T.psiNF m hm n hn (ω ^ u) (hω.pow_of_coprime u hu) a := by
  rw [tauN, psiNF_mk, psiNF_val, toPoly_expandC u hu0, ← eval_map, ← eval_map, Polynomial.map_expand,
    expand_eval]

end NF

end MTower

end Curves.MT
