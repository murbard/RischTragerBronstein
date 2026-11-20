import RischTragerBronstein.Curves.ProcRFSound7

/-!
# Correctness of the residue-free decision on a general curve

`decideRF_spec`: for a curve `F(x, y) = 0` over an algebraically closed field of constants `Kc`
(defined over a computable field `F ↪ Kc`), and the integrand `f = A(x, y)/D(x)`: whenever
`P.decideRF = some b`, `f` has an elementary integral **iff** `b = true`.

* `some false`: the linear system for the exact part has no solution — by `rows_of_liouville`
  (Liouville's theorem, pole bounds, the ansatz) no elementary integral exists;
* `some b` after a solution with all residues zero: `b` is the zero test for `f − v′`, which
  decides elementarity by `eq_deriv_of_rows` (second kind + regularity).
-/

open Polynomial IntermediateField

namespace Curves

open CPoly Sup Differential

section Transport

variable {Kc E Cc L : Type*} [Field Kc] [Field E] [Algebra Kc E] [Field Cc] [Field L]
  [Algebra Cc L]

namespace CurveData

variable (S : CurveData Kc E) (SL : CurveData Cc L) (φ : Kc →+* Cc) (jE : E →+* L)
  (hxL : SL.x = jE S.x) (hyL : SL.y = jE S.y)
  (hjC : ∀ c : Kc, jE (algebraMap Kc E c) = algebraMap Cc L (φ c))

include hxL hjC in
lemma jE_aeval (q : Kc[X]) : jE (aeval S.x q) = aeval SL.x (q.map φ) := by
  rw [aeval_def, aeval_def, eval₂_map, hom_eval₂, hxL]
  congr 1
  ext c
  exact hjC c

include hxL hyL hjC in
lemma jE_evXY (Q : Kc[X][X]) : jE (S.evXY Q) = SL.evXY (Q.map (mapRingHom φ)) := by
  simp only [evXY, eval_map, eval₂_map]
  rw [hom_eval₂, hyL]
  congr 1
  refine RingHom.ext fun q ↦ ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_mapRingHom]
  exact S.jE_aeval SL φ jE hxL hjC q

end CurveData

end Transport

section Main

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

/-- **Correctness of the residue-free decision** on a general curve. -/
theorem decideRF_spec (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) {F : Type*} [Field F] [DecidableEq F] [CharZero F]
    (P : CurveProb F) (ι : F →+* Kc) (hSF : S.F = (toB P.Fc).map (mapRingHom ι)) (b : Bool)
    (h : P.decideRF = some b) :
    HasElementaryIntegral ((S.fE P ι : Kc⟮S.x⟯⟮S.y⟯) : E) ↔ b = true := by
  classical
  unfold CurveProb.decideRF at h
  by_cases hval : P.valid = true
  swap
  · rw [if_neg hval] at h; exact absurd h (by simp)
  rw [if_pos hval] at h
  have hV := P.valid_spec hval
  -- transport of the problem to a lifted curve
  have lift : ∀ (Cc L : Type u) [Field Cc] [CharZero Cc] [Field L] [CharZero L] [Algebra Cc L]
      (φ : Kc →+* Cc) (jE : E →+* L) (SL : CurveData Cc L), SL.x = jE S.x → SL.y = jE S.y →
      SL.F = S.F.map (mapRingHom φ) →
      (∀ c : Kc, jE (algebraMap Kc E c) = algebraMap Cc L (φ c)) →
      SL.F = (toB P.Fc).map (mapRingHom (φ.comp ι)) ∧
        jE (S.fE P ι : E) = (SL.fE P (φ.comp ι) : L) := by
    intro Cc L _ _ _ _ _ φ jE SL hxL hyL hFL hjC
    have hSF' : SL.F = (toB P.Fc).map (mapRingHom (φ.comp ι)) := by
      rw [hFL, hSF, Polynomial.map_map, ← mapRingHom_comp]
    refine ⟨hSF', ?_⟩
    simp only [CurveData.fE, map_div₀]
    rw [S.jE_evXY SL φ jE hxL hyL hjC, S.jE_aeval SL φ jE hxL hjC, Polynomial.map_map,
      Polynomial.map_map, ← mapRingHom_comp]
  split at h
  · -- no exact part: not elementary
    rename_i hnone
    obtain rfl : b = false := (Option.some.inj h).symm
    simp only [Bool.false_eq_true, iff_false]
    intro hel
    refine curve_lift hC S hx hgen _ hel ?_
    intro Cc L _ _ _ _ _ _ _ _ φ jE SL hCc hxc hconst hxL hyL hFL hjd hjC hjE v hv ιI sI d w
      hd hw heq
    obtain ⟨hSF', hjf⟩ := lift Cc L φ jE SL hxL hyL hFL hjC
    haveI : CharZero (AlgebraicClosure Cc) :=
      charZero_of_injective_algebraMap (algebraMap Cc (AlgebraicClosure Cc)).injective
    rw [hjf] at heq
    obtain ⟨cv, hrows⟩ := SL.rows_of_liouville (K := AlgebraicClosure Cc) hCc hxc hconst hSF' hV
      v hv sI d w hd hw heq
    have hlc := lcombS_cols (φ.comp ι) P.basisIdx.length
      ((List.range P.basisIdx.length).map cv) (by simp) P.allRows (fun r hr ↦ by
        rw [← hrows r hr]
        refine Finset.sum_congr rfl fun b hb ↦ ?_
        rw [List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_map, List.getElem_range])
    exact linSolve_complete_map (φ.comp ι) P.cols P.rhs _ (by simp [CurveProb.cols]) hlc hnone
  · rename_i cs hsome
    by_cases hres : P.allRes.all (· = 0) = true
    swap
    · rw [if_neg hres] at h; exact absurd h (by simp)
    rw [if_pos hres] at h
    obtain rfl := (Option.some.inj h).symm
    have hres' : ∀ r ∈ P.allRes, r = 0 := fun r hr ↦ by
      simpa using List.all_eq_true.mp hres r hr
    obtain ⟨hcsl, hlc⟩ := linSolve_sound _ _ _ hsome
    have hcsl' : cs.length = P.basisIdx.length := by rw [hcsl]; simp [CurveProb.cols]
    have hrowsF := rows_of_lcomb P.basisIdx.length cs hcsl' P.allRows hlc
    constructor
    · intro hel
      refine curve_lift hC S hx hgen _ hel ?_
      intro Cc L _ _ _ _ _ _ _ _ φ jE SL hCc hxc hconst hxL hyL hFL hjd hjC hjE v hv ιI sI d w
        hd hw heq
      obtain ⟨hSF', hjf⟩ := lift Cc L φ jE SL hxL hyL hFL hjC
      haveI : CharZero (AlgebraicClosure Cc) :=
        charZero_of_injective_algebraMap (algebraMap Cc (AlgebraicClosure Cc)).injective
      rw [hjf] at heq
      have hrows : ∀ r ∈ P.allRows, ∑ b ∈ Finset.range P.basisIdx.length,
          (φ.comp ι) (cs.getD b 0) * (φ.comp ι) (r.1.getD b 0) = (φ.comp ι) r.2 := by
        intro r hr
        rw [← hrowsF r hr, map_sum]
        simp only [map_mul]
      have hfin := SL.eq_deriv_of_rows (K := AlgebraicClosure Cc) hCc hxc hconst hSF' hV _ hrows
        hres' v hv sI d w hd hw heq
      exact (SL.zeroTest_iff hCc hxc hSF' hV hV.len hV.last cs).mpr hfin
    · intro hb
      rw [S.zeroTest_iff hC hx hSF hV hV.len hV.last cs] at hb
      rw [hb]
      exact hasElementaryIntegral_of_deriv _

end Main

end Curves
