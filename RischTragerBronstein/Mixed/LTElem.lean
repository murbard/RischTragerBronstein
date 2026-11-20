import RischTragerBronstein.Mixed.LTChain

/-!
# Towers of logarithms over a curve: elementary integration

`elT Fc us m q N` decides whether the level-`m` code `q` has an elementary integral:

* level `0`: the total decision on the curve (`decideTotal`, search bound `N`);
* level `m + 1` (`t = tₘ = log uₘ`): Hermite reduction in `t`, the residue test, the chain of
  limited integration problems at level `m` (`lchain`), and the constant term `a₀ − η Q₁`
  decided at level `m` — the one-level-lower instance of the one-logarithm decision of
  `LogCurveMain`.

This file: the algorithm, and the base of the induction (`el0_decides`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.LT

open CPoly Sup

variable (Fc : BPoly ℚ) (us : (m : ℕ) → LC m)

/-- **Elementary integration in the log tower over the curve**, with search bound `N`. -/
def elT : (m : ℕ) → LC m → ℕ → Option Bool
  | 0, q, N => decideTotal Fc ((codeW (cvNorm Fc q)).map trim) (codeQ (cvNorm Fc q)) N
  | m + 1, q, N =>
    let O := LO Fc us m
    let w : GPoly (LC m) := [etaC Fc us m]
    let q' : GFrac (LC m) := q
    if GPoly.isZero O q'.2 then some true
    else
      let h := GPoly.hermite O w q'.1 q'.2
      let qr := GPoly.divMod O h.b h.s
      if !(GPoly.residueCheck O w qr.2 h.s) then some false
      else match lchain Fc us m qr.1 qr.1.length O.zero with
        | none => some false
        | some Q1 => elT m (lconst Fc us m qr.1 Q1) N

/-! ### Integrals over every extension of a base -/

section Base

universe w

variable {F₀ K : Type w} [Field F₀] [Field K] [Algebra F₀ K] [Differential F₀] [Differential K]
  [DifferentialAlgebra F₀ K]

/-- An integral over every extension of `F₀` is one over every extension of an elementary
extension `K` of `F₀`. -/
lemma HasElementaryIntegralIn.of_base (hE : IsElementaryExtension F₀ K) {f : F₀}
    (h : HasElementaryIntegralIn f) : HasElementaryIntegralIn (algebraMap F₀ K f) := by
  intro E _ _ _ _ hE'
  let _ : Algebra F₀ E := ((algebraMap K E).comp (algebraMap F₀ K)).toAlgebra
  have : IsScalarTower F₀ K E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hDA : DifferentialAlgebra F₀ E :=
    ⟨fun a ↦ by
      change (algebraMap K E (algebraMap F₀ K a))′ = algebraMap K E (algebraMap F₀ K a′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  exact h E (hE.trans hE')

end Base

/-! ### The base of the induction -/

section Level0

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]
variable (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
  (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯)
  (hSF : S.F = (toB Fc).map (mapRingHom (algebraMap ℚ Kc)))

set_option maxHeartbeats 1000000 in
include hgen in
/-- **Level `0`**: a curve code is decided by the total decision on the curve; a positive answer
gives an elementary integral over every extension. -/
theorem el0_decides (hsh : curveShape Fc = true) (c : GPoly (GFrac ℚ)) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b, decideTotal Fc ((codeW (cvNorm Fc c)).map trim)
        (codeQ (cvNorm Fc c)) N = some b ∧
      (HasElementaryIntegral ((cM hC S hx Fc hSF).sem c) ↔ b = true) ∧
      (b = true → HasElementaryIntegralIn ((cM hC S hx Fc hSF).sem c)) := by
  set M := cM hC S hx Fc hSF
  set W := (codeW (cvNorm Fc c)).map trim with hW
  set Q := codeQ (cvNorm Fc c) with hQ
  have hQ0 : toPoly Q ≠ 0 := codeQ_ne_zero _
  have hshape := shapeOK_constProb Fc hsh (codeW (cvNorm Fc c)) Q hQ0
  obtain ⟨N₀, hN₀⟩ := decideTotal_decides hC S hx hgen Fc W Q hshape hSF
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff⟩ := hN₀ N hN
  refine ⟨b, hb, ?_⟩
  have hval : ((S.fE (curveProbQ Fc W Q) (algebraMap ℚ Kc) : Kc⟮S.x⟯⟮S.y⟯) : E) = M.sem c := by
    change S.evXY _ / aeval S.x _ = M.sem c
    change S.evXY ((toB W).map (mapRingHom (algebraMap ℚ Kc))) /
      aeval S.x ((toPoly Q).map (algebraMap ℚ Kc)) = _
    rw [hW, toB_map_trim, ← evRH_eq_evXY, evRH_toB, eval_codeW hC S hx Fc hSF,
      sem_cvNorm hC S hx Fc hSF]
    have hne := aeval_codeQ_ne_zero S (cvNorm Fc c)
    rw [← hQ] at hne ⊢
    exact mul_div_cancel_left₀ _ hne
  rw [← hiff, ← hval]
  refine ⟨Iff.rfl, fun h0 ↦ ?_⟩
  exact (curve_liouvilleForm hC S hx hgen (curveProbQ Fc W Q) hshape hSF h0).hasElementaryIntegralIn

end Level0

end Curves.LT
