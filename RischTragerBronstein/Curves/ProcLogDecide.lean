import RischTragerBronstein.Curves.ProcLogSem5

/-!
# Correctness of the decision with logarithmic part on a general curve

`decideLog_spec`: for a curve over an algebraically closed field of constants `Kc` (defined over a
computable field `F ↪ Kc` with `ℚ`-coordinates), the integrand `f = A(x, y)/D(x)` and any list of
log witnesses `ws`: whenever `P.decideLog ws = some b`, `f` has an elementary integral **iff**
`b = true`. When `b = true`, `f = v′ + ∑ c_j u_j′/u_j` explicitly.
-/

open Polynomial IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential

section Main

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]

namespace CurveData

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

/-- The zero test for the logarithmic remainder. -/
lemma logTest_iff {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
    [Differential C] [Differential L] [DifferentialAlgebra C L] (S : CurveData C L)
    (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) {P : CurveProb F} {ψ₀ : F →+* C}
    (hSF : S.F = (toB P.Fc).map (mapRingHom ψ₀)) (hV : P.ValidFacts) (cs : List F)
    (ws : List (LogWit F)) (hwit : P.witCheck ws = true) :
    isZeroB (modF P.Fc P.n (P.logNum cs ws)) = true ↔ S.hL P ψ₀ cs ws = 0 := by
  rw [← S.evXY_zero_iff P.Fc ψ₀ hSF P.n (S.natDegree_F_eq P ψ₀ hSF hV)
    (toB_Fc_split P hV.len hV.last)]
  have hW := fun j ↦ S.wE_ne_zero hSF hV _ (P.witCheck_spec ws hwit j).cover
  have hQ := fun j ↦ S.qE_ne_zero (ψ₀ := ψ₀) _ (P.witCheck_spec ws hwit j).Q0
  rw [S.evXY_logNum hC hx hSF hV cs ws hW hQ]
  have hR : aeval S.x ((toPoly P.R0).map ψ₀) ≠ 0 := S.aeval_x_ne_zero _ (by
    rw [Ne, Polynomial.map_eq_zero_iff ψ₀.injective]; exact P.R0_ne_zero hV)
  have hprod : ∏ j : Fin (dim F),
      ((S.wE ψ₀ (CurveProb.witAt ws j).W : L) * (S.qE ψ₀ (CurveProb.witAt ws j).Q : L)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ ↦ mul_ne_zero (hW j) (hQ j)
  constructor
  · intro h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · exact h3
        · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h3) hR
      · exact absurd h2 S.evXY_derivative_ne_zero
    · exact absurd h1 hprod
  · intro h0
    rw [mul_assoc, mul_assoc]
    exact mul_eq_zero_of_left h0 _

end CurveData

/-- **Correctness of the decision with logarithmic part** on a general curve. -/
theorem decideLog_spec (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (hgen : ∀ z : E, z ∈ Kc⟮S.x⟯⟮S.y⟯) {F : Type*} [Field F] [DecidableEq F] [CharZero F]
    [EllQuad.QCoords F] (P : CurveProb F) (ι : F →+* Kc)
    (hSF : S.F = (toB P.Fc).map (mapRingHom ι)) (ws : List (LogWit F)) (b : Bool)
    (h : P.decideLog ws = some b) :
    HasElementaryIntegral ((S.fE P ι : Kc⟮S.x⟯⟮S.y⟯) : E) ↔ b = true := by
  classical
  unfold CurveProb.decideLog at h
  by_cases hval : P.valid = true
  swap
  · rw [if_neg hval] at h; exact absurd h (by simp)
  rw [if_pos hval] at h
  have hV := P.valid_spec hval
  -- the residue-free and no-exact-part cases are those of `decideRF`
  have hRF : P.decideRF = if P.valid then
      match linSolve P.cols P.rhs with
      | none => some false
      | some cs =>
        if P.allRes.all (· = 0) then some (isZeroB (modF P.Fc P.n (P.Pg (P.Wsol cs))))
        else none
      else none := rfl
  split at h
  · rename_i hnone
    have : P.decideRF = some b := by rw [hRF, if_pos hval, hnone]; exact h
    exact decideRF_spec hC S hx hgen P ι hSF b this
  · rename_i cs hsome
    by_cases hres : P.allRes.all (· = 0) = true
    · rw [if_pos hres] at h
      have : P.decideRF = some b := by rw [hRF, if_pos hval, hsome]; simp only [if_pos hres]; exact h
      exact decideRF_spec hC S hx hgen P ι hSF b this
    rw [if_neg hres] at h
    by_cases hwit : P.witCheck ws = true
    swap
    · rw [if_neg hwit] at h; exact absurd h (by simp)
    rw [if_pos hwit] at h
    obtain rfl := (Option.some.inj h).symm
    obtain ⟨hcsl, hlc⟩ := linSolve_sound _ _ _ hsome
    have hcsl' : cs.length = P.basisIdx.length := by rw [hcsl]; simp [CurveProb.cols]
    have hrowsF := rows_of_lcomb P.basisIdx.length cs hcsl' P.allRows hlc
    constructor
    · intro hel
      refine curve_lift hC S hx hgen _ hel ?_
      intro Cc L _ _ _ _ _ _ _ _ φ jE SL hCc hxc hconst hxL hyL hFL hjd hjC hjE v hv ιI sI d w
        hd hw heq
      have hSF' : SL.F = (toB P.Fc).map (mapRingHom (φ.comp ι)) := by
        rw [hFL, hSF, Polynomial.map_map, ← mapRingHom_comp]
      have hjf : jE (S.fE P ι : E) = (SL.fE P (φ.comp ι) : L) := by
        simp only [CurveData.fE, map_div₀]
        rw [S.jE_evXY SL φ jE hxL hyL hjC, S.jE_aeval SL φ jE hxL hjC, Polynomial.map_map,
          Polynomial.map_map, ← mapRingHom_comp]
      rw [hjf] at heq
      haveI : CharZero (AlgebraicClosure Cc) :=
        charZero_of_injective_algebraMap (algebraMap Cc (AlgebraicClosure Cc)).injective
      have hrows : ∀ r ∈ P.allRows, ∑ b ∈ Finset.range P.basisIdx.length,
          (φ.comp ι) (cs.getD b 0) * (φ.comp ι) (r.1.getD b 0) = (φ.comp ι) r.2 := by
        intro r hr
        rw [← hrowsF r hr, map_sum]
        simp only [map_mul]
      have h0 := SL.eq_log_of_rows (AlgebraicClosure Cc) hCc hxc hconst hSF' hV cs ws hwit
        hrows v hv sI d w hd hw heq
      exact (SL.logTest_iff hCc hxc hSF' hV cs ws hwit).mpr h0
    · intro hb
      have h0 := (S.logTest_iff hC hx hSF hV cs ws hwit).mp hb
      rw [CurveData.hL, sub_eq_zero, sub_eq_iff_eq_add'] at h0
      rw [h0]
      have := hasElementaryIntegral_of_liouville_form (S.vvE P ι cs : E)
        ((List.finRange (dim F)).map fun j ↦ (algebraMap Kc E (CurveData.cj ι ws j),
          (S.uE ι (CurveProb.witAt ws j) : E))) (fun p hp ↦ by
          obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
          exact ⟨by rw [deriv_algebraMap, hC, map_zero],
            S.uE_ne_zero hSF hV _ j (P.witCheck_spec ws hwit j)⟩)
      rw [List.map_map] at this
      convert this using 2
      rw [sum_finRange_map]
      rfl

end Main

end Curves
