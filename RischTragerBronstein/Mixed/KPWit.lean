import RischTragerBronstein.Mixed.KPDecideMain

/-!
# Kummer radicals over a logarithm: the antiderivative

`∫ B(t) θʲ` (`θⁿ = a(t)`) is elementary iff the Risch equation `y′ + (j/n)(a′/a) y = B` has a
solution in `Fₘ₊₁` (`kp_decides`), and then `∫ B θʲ = y θʲ`. `kpSolve` returns that solution
(`rdeSolFr`: the solution read off the parametric solver `prdeC`); it answers exactly as
`kpDecide` (`kpSolve_isSome`) and `(y θʲ)′ = B θʲ` (`kp_antiderivative`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- A solution of the Risch equation `y′ + h y = w` (`h` the value of `fr`), if one is found. -/
def rdeSolFr (m : ℕ) (fr : FRep (LC m)) (w : LC m) : Option (LC m) :=
  ((prdeC Fc ks lv m fr [w]).find? fun r ↦ decide (r.1.getD 0 0 ≠ 0)).map
    fun r ↦ (MO Fc ks m).mul (mcst Fc ks m (r.1.getD 0 0)⁻¹) r.2

lemma rdeSolFr_isSome (m : ℕ) (fr : FRep (LC m)) (w : LC m) :
    (rdeSolFr Fc ks lv m fr w).isSome = rdeOKFr Fc ks lv m fr w := by
  simp only [rdeSolFr, rdeOKFr, Option.isSome_map]
  rw [Bool.eq_iff_iff, List.find?_isSome, List.any_eq_true]

/-- **The antiderivative** of `B θʲ` over a logarithmic level, if elementary. -/
def kpSolve (m : ℕ) (j n : ℕ) (a B : GPoly (LC m)) : Option (LC (m + 1)) :=
  rdeSolFr Fc ks lv (m + 1) (kpFr Fc ks m j n a) ((B, [(MO Fc ks m).one]) : LC (m + 1))

lemma kpSolve_isSome (m : ℕ) (j n : ℕ) (a B : GPoly (LC m)) :
    (kpSolve Fc ks lv m j n a B).isSome = kpDecide Fc ks lv m j n a B :=
  rdeSolFr_isSome _ _ _ _ _ _

universe u

variable {Fc ks lv} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma rdeSolFr_sound (m : ℕ) (h : T.Tr m) (fr : FRep (LC m))
    (hs : RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h) ((T.MP m h).sem (fCode (MO Fc ks m) fr))
      (prdeC Fc ks lv m fr)) (w y : LC m) (hy : rdeSolFr Fc ks lv m fr w = some y) :
    ((T.MP m h).sem y)′ + (T.MP m h).sem (fCode (MO Fc ks m) fr) * (T.MP m h).sem y =
      (T.MP m h).sem w := by
  classical
  set M := T.MP m h
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hy
  have hr0 := List.find?_some hr
  simp only [decide_eq_true_eq] at hr0
  have hsd := hs.sound [w] r (List.mem_of_find?_eq_some hr)
  rw [sQ] at hsd
  simp only [List.length_cons, List.length_nil, zero_add, Finset.range_one,
    Finset.sum_singleton, List.getD_cons_zero] at hsd
  have hq : ((r.1.getD 0 0 : ℚ) : T.F m) ≠ 0 := by exact_mod_cast hr0
  rw [M.sem_mul, T.sem_mcst, Derivation.leibniz, T.deriv_ratCast]
  simp only [smul_eq_mul, mul_zero, add_zero]
  rw [Rat.cast_inv]
  field_simp
  linear_combination hsd

/-- **The antiderivative of a Kummer radical over a logarithm**: `(y θʲ)′ = B θʲ`. -/
theorem kp_antiderivative (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) (a : GPoly (LC m)) (nn : ℕ)
    (hnn : 0 < nn) (hdegpos : 0 < degG (MO Fc ks m) a) (θ : L) (hθ : θ ^ nn = T.evP m a)
    (j : ℕ) (B : GPoly (LC m)) (y : LC (m + 1)) (hy : kpSolve Fc ks lv m j nn a B = some y) :
    (T.ev (m + 1) y * θ ^ j)′ = T.evP m B * θ ^ j := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hspec := MS.rde _ (T.kpFr_ok m hTr j nn a)
  have hA0 : T.evP m a ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) a hdegpos
  have hz := T.rdeSolFr_sound (m + 1) hTr _ hspec _ y hy
  have hzL := congrArg Subtype.val hz
  rw [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv, T.sem_kpFr m hTr,
    T.sem_poly_code m hTr, T.sem_MP] at hzL
  rw [deriv_mul_radical θ (T.evP m a) nn hnn hθ hA0, hzL]

end MTower

end Curves.MT
