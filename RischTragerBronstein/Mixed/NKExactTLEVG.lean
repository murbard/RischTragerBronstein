import RischTragerBronstein.Mixed.NKExactTLEV
import RischTragerBronstein.Mixed.SysGauge

/-!
# The exponential exact-part test with a gauge at infinity

`expSysVG … Cg Cgi`: the solver `expSysV` behind the constant gauge `Cg` (`gaugeSolver`), whose
limit matrix at infinity need only be triangular after the gauge (several places at infinity).
`exactTLEVG`: `exactTLEVS` with this solver; correct (`exactTLEVG_correct`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **`expSysV` behind the constant gauge `Cg`.** -/
def expSysVG (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (ℚ × ℚ × LC m)) (Cg Cgi : List (List (LC m))) : SysSolver m :=
  gaugeSolver Fc ks m (fun n A0 q hh G0 ↦ expSysV Fc ks m a rde dg n A0 q hh G0 0) Cg Cgi

/-- **The exact-part test in the basis `w = T θ`, with several parameters and a gauge at
infinity** (exponential level). -/
def exactTLEVG (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (ℚ × ℚ × LC m)) (Cg Cgi : List (List (LC m))) (r : ℕ → ℤ)
    (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m)) (P : GPoly (LC (m + 1)))
    (Tc Ti : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (gs : List (List (LC (m + 1)))) :
    Option Bool :=
  exactTLEVS Fc ks m a (expSysVG Fc ks m a rde dg Cg Cgi) r C Ci dg0 P Tc Ti f gs

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) (m : ℕ)

/-- **`expSysVG` meets the solver specification with known denominators.** -/
theorem expSpecVG (hm : m < T.n) (h0 : T.Tr m) {a : LC m} (hk : ks m = .exp a)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h0) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h0) ((T.MP m h0).sem (fCode (MO Fc ks m) fr))
        (rde fr))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h0).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (dg : List (ℚ × ℚ × LC m)) (Cg Cgi : List (List (LC m))) :
    T.SolverSpecB m h0 0 ((T.MP m h0).sem ((MO Fc ks m).deriv a))
      (expSysVG Fc ks m a rde dg Cg Cgi) :=
  T.gaugeSolver_spec h0 _ _ _ (T.expSpecV hm h0 hk rde hrde hom dg) Cg Cgi

/-- **`expSysVG` answers** for monic `q`, `h`, `deg A₀ ≤ deg q` and a limit `A₀/q → Λ` at infinity
that the gauge makes upper triangular with diagonal `pᵢ a′ + qᵢ cᵢ′/cᵢ` (given by `dg`). -/
theorem expSysVG_isSome (h0 : T.Tr m) (a : LC m)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m)) (dg : List (ℚ × ℚ × LC m))
    (Cg Cgi : List (List (LC m))) (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m)) (q hh : GPoly (LC m))
    (G0 : List (Fin n → GPoly (LC m)))
    (hmon : (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hh) = true)
    (hA : ∀ i j, (GPoly.toPoly (T.MP m h0) (A0 i j)).natDegree ≤
      (GPoly.toPoly (T.MP m h0) q).natDegree)
    (Λ : Fin n → Fin n → T.F m)
    (hΛ : ∀ i j, (GPoly.toPoly (T.MP m h0) (A0 i j)).coeff (GPoly.toPoly (T.MP m h0) q).natDegree =
      Λ i j)
    (hinv : invOKG Fc ks m n Cg Cgi = true)
    (htri : ∀ i j, j < i → gaugeM (fun i j : Fin n ↦ (T.MP m h0).sem (cgV Fc ks m Cg i j))
      (fun i j : Fin n ↦ (T.MP m h0).sem (cgV Fc ks m Cgi i j)) Λ i j = 0)
    (hdiag : ∀ i : Fin n, gaugeM (fun i j : Fin n ↦ (T.MP m h0).sem (cgV Fc ks m Cg i j))
      (fun i j : Fin n ↦ (T.MP m h0).sem (cgV Fc ks m Cgi i j)) Λ i i =
        (T.MP m h0).sem (fCode (MO Fc ks m) (frE Fc ks m a 0 (dgEAt Fc ks m dg i)))) :
    (expSysVG Fc ks m a rde dg Cg Cgi n A0 q hh G0).isSome := by
  have hqM := isMonicC_spec (T.MP m h0) q (Bool.and_eq_true_iff.mp hmon).1
  have hl := fun i j ↦ gaugeA_lim _ hqM (T.cMat h0 n Cg) (T.cMat h0 n Cgi)
    (semMat (T.MP m h0) A0) Λ (fun i j ↦ by simpa [semMat] using hA i j)
    (fun i j ↦ by simpa [semMat] using hΛ i j) i j
  have hent : ∀ i j, GPoly.toPoly (T.MP m h0) (gaugeAG Fc ks m n Cg Cgi A0 q i j) =
      gaugeA (GPoly.toPoly (T.MP m h0) q) (T.cMat h0 n Cg) (T.cMat h0 n Cgi)
        (semMat (T.MP m h0) A0) i j := fun i j ↦ by
    rw [← T.semMat_gaugeAG h0]; rfl
  apply gaugeSolver_isSome _ Cg Cgi A0 q hh G0 hinv
  exact T.expSysV_isSome m h0 n _ q hh _ 0 a rde dg hmon (fun i j ↦ by rw [hent]; exact (hl i j).1)
    _ (fun i j ↦ by rw [hent]; exact (hl i j).2) (fun i j hji ↦ htri i j hji) hdiag

/-- **Correctness of `exactTLEVG`.** -/
theorem exactTLEVG_correct (h1 : T.Tr (m + 1)) (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (dg : List (ℚ × ℚ × LC m)) (Cg Cgi : List (List (LC m))) (r : ℕ → ℤ)
    (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range (P.length - 1), (a j : L) * θ ^ j = 0 →
      ∀ j < P.length - 1, a j = 0)
    (Tc Ti : List (List (LC (m + 1)))) (gs : List (List (LC (m + 1)))) (res : Bool)
    (hres : exactTLEVG Fc ks m a rde dg Cg Cgi r C Ci dg0 P Tc Ti f gs = some res) :
    res = true ↔ ∃ (c : ℕ → Cc) (Y : ℕ → T.F (m + 1)),
      (∑ i ∈ Finset.range (P.length - 1), (Y i : L) * θ ^ i)′ =
        ∑ j ∈ Finset.range (P.length - 1),
          (((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) -
            ∑ i ∈ Finset.range gs.length, algebraMap Cc L (c i) *
              ((T.MPr (m + 1) h1).sem ((gs.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L)) *
            θ ^ j :=
  T.exactTLEVS_correct m h1 hm hk htr _ (T.expSpecVG m hm h1.of_succ hk rde hrde hom dg Cg Cgi) hom
    r C Ci dg0 P f θ hP hind Tc Ti gs res hres

end MTower

end Curves.MT
