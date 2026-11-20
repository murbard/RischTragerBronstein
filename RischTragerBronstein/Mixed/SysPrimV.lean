import RischTragerBronstein.Mixed.SysPrimL
import RischTragerBronstein.Mixed.NKExactWE
import RischTragerBronstein.Mixed.MTSpecs

/-!
# Coupled systems at a primitive level with a triangular limit matrix

`primSysV … dg` runs `primSysBL … 0` with the triangular solver one level down (`triLowC`), after
checking (with the zero test) that the limit matrix `Λ = lamCL` is upper triangular with diagonal
entries `fCode dgᵢ = hᵢ′ + ∑ cᵢₖ wᵢₖ′/wᵢₖ` with constant `cᵢₖ` (`triOKC`). This is the shape met by
non-constant curves (the limit matrix acts on the residue algebra at infinity through the
derivation of the coefficients). It meets the solver specification with known denominators
(`primSpecV`), so `exactWE` and its variants may use it.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The diagonal representation `i`. -/
def dgAt (m : ℕ) (dg : List (FRep (LC m))) (i : ℕ) : FRep (LC m) :=
  dg.getD i ⟨(MO Fc ks m).zero, []⟩

/-- **The checks**: `Λ` upper triangular, its diagonal given by `dg`, constant log coefficients. -/
def triOKC (m : ℕ) (dg : List (FRep (LC m))) (n : ℕ) (Λc : Fin n → Fin n → LC m) : Bool :=
  let O := MO Fc ks m
  (List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
    (!decide (j < i) || O.isZero (Λc i j)) &&
    O.isZero (O.add (Λc i i) (O.neg (fCode O (dgAt Fc ks m dg i)))) &&
    (dgAt Fc ks m dg i).logs.all fun cw ↦ O.isZero (O.deriv cw.1)

/-- The triangular solver one level down. -/
def triLowC (m : ℕ) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (FRep (LC m))) (n : ℕ) (Λc : Fin n → Fin n → LC m) (ws : List (Fin n → LC m)) :
    List (List ℚ × (Fin n → LC m)) :=
  triSys (MO Fc ks m) (mcst Fc ks m) (fun i ↦ rde (dgAt Fc ks m dg i)) Λc ws

/-- **The solver**: `primSysBL … 0` with `triLowC`, when `triOKC` holds for the limit matrix. -/
def primSysV (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (FRep (LC m))) (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m)) (q h : GPoly (LC m))
    (G0 : List (Fin n → GPoly (LC m))) :
    Option (GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))) :=
  if triOKC Fc ks m dg n (lamCL Fc ks m η n A0 q h G0 0) then
    primSysBL Fc ks m η n (triLowC Fc ks m rde dg n) A0 q h G0 0
  else none

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable {m : ℕ}

/-- **The triangular solver meets the system specification** when the checks pass. -/
theorem triLowC_spec (h : T.Tr m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h) ((T.MP m h).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (dg : List (FRep (LC m))) (n : ℕ) (Λc : Fin n → Fin n → LC m)
    (hok : triOKC Fc ks m dg n Λc = true) (ws : List (Fin n → LC m)) :
    SysSpecAt (algebraMap Cc (T.F m)) (fun i j ↦ (T.MP m h).sem (Λc i j))
      (ws.map (semVa (T.MP m h))) (semR (T.MP m h) (triLowC Fc ks m rde dg n Λc ws)) := by
  set M := T.MP m h with hM
  simp only [triOKC, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at hok
  have hF : (fun i j ↦ M.sem (Λc i j)) =
      triF M (fun i ↦ M.sem (fCode (MO Fc ks m) (dgAt Fc ks m dg i))) Λc := by
    funext i j
    simp only [triF]
    split_ifs with h1 h2
    · subst h1
      have := (M.isZero_iff _).mp (hok i i).1.2
      rw [M.sem_add, M.sem_neg] at this
      exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using this)
    · rfl
    · have hji : j < i := lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)
      rcases (hok i j).1.1 with h3 | h3
      · exact absurd hji (not_lt.mpr h3)
      · exact (M.isZero_iff _).mp h3
  rw [hF]
  exact triSys_spec _ M (mcst Fc ks m) (T.sem_mcst m h) _ _ ws _
    (fun i ↦ hrde _ (fun cw hcw ↦ by
      have := (M.isZero_iff _).mp ((hok i i).2 cw hcw)
      rwa [M.sem_deriv] at this))
    T.algebraMap_ratCast

/-- A successful `primSysV` has monic `q`, `h` and the `W`-system denominator. -/
lemma primSysV_some {η : LC m} {rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m)}
    {dg : List (FRep (LC m))} {n : ℕ}
    {A0 : Fin n → Fin n → GPoly (LC m)} {q hq : GPoly (LC m)} {G0 : List (Fin n → GPoly (LC m))}
    {r : GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))}
    (hres : primSysV Fc ks m η rde dg n A0 q hq G0 = some r) :
    triOKC Fc ks m dg n (lamCL Fc ks m η n A0 q hq G0 0) = true ∧
    isMonicC (MO Fc ks m) q = true ∧ isMonicC (MO Fc ks m) hq = true ∧
    r.1 = (wSys Fc ks m η n A0 q hq G0 0).Den := by
  unfold primSysV at hres
  split_ifs at hres with htri
  refine ⟨htri, ?_⟩
  unfold primSysBL at hres
  simp only at hres
  split_ifs at hres with hmon
  split at hres
  · exact absurd hres (by simp)
  have : (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hq) = true := by
    revert hmon; cases (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hq) <;> simp
  exact ⟨(Bool.and_eq_true_iff.mp this).1, (Bool.and_eq_true_iff.mp this).2,
    by rw [← Option.some.inj hres]⟩

/-- **`primSysV` meets the solver specification with known denominators** (primitive level). -/
theorem primSpecV (hm : m < T.n) (h0 : T.Tr m) {η : LC m} (hk : ks m = .prim η)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h0) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h0) ((T.MP m h0).sem (fCode (MO Fc ks m) fr))
        (rde fr))
    (dg : List (FRep (LC m))) :
    T.SolverSpecB m h0 ((T.MP m h0).sem η) 0
      (fun n A0 q hh G0 ↦ primSysV Fc ks m η rde dg n A0 q hh G0) where
  hD := T.phi_DzL m hm hk h0
  sound := fun n A0 q hh G0 Den out hres ↦ by
    have hres' := hres
    unfold primSysV at hres'
    split_ifs at hres' with htri
    exact T.primSysBL_sound m h0 η n A0 q hh G0 0 _ Den out hres'
  den := fun n A0 q hh G0 r hres ↦ by
    obtain ⟨-, hm1, hm2, hB⟩ := primSysV_some hres
    have hq := (isMonicC_spec (T.MP m h0) q hm1).ne_zero
    have hh' := (isMonicC_spec (T.MP m h0) hh hm2).ne_zero
    refine ⟨?_, hq, hh'⟩
    rw [hB, T.wSys_Den m h0 η n A0 q hh G0 0]
    exact mul_ne_zero hh' (pow_ne_zero _ hq)
  complete := fun n A0 q hh G0 Den out hres c hc Z d hd hsol hdvd ↦ by
    have hres' := hres
    unfold primSysV at hres'
    split_ifs at hres' with htri
    exact T.primSysBL_complete m h0 η n A0 q hh G0 0 _
      (fun ws ↦ T.triLowC_spec h0 rde hrde dg n _ htri ws) Den out hres' c hc Z d hd hsol
      (fun i ↦ by rw [pow_zero, mul_one]; exact hdvd i)

end MTower

end Curves.MT
