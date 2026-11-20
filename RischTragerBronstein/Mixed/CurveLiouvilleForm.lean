import RischTragerBronstein.Curves.ProcLogDecide

/-!
# Positive answers of the curve decision are explicit Liouville forms

`LiouvilleFormE f`: `f = v′ + ∑ cᵢ uᵢ′/uᵢ` with constants `cᵢ` and `v, uᵢ` in the field itself.
Such an `f` has an elementary integral over **every** differential extension
(`LiouvilleFormE.hasElementaryIntegralIn`), which lets the answer of the curve decision be
transported up a tower of transcendental extensions.

* `decideRF_true`, `decideLog_true`: a positive answer of `decideRF` / `decideLog` is a Liouville
  form over the function field of the curve.
-/

open Polynomial IntermediateField EllQuad.QCoords

namespace Curves

open CPoly Sup Differential

section Form

universe u

/-- `f = v′ + ∑ cᵢ uᵢ′/uᵢ` with constants `cᵢ`, `uᵢ ≠ 0`. -/
def LiouvilleFormE {E : Type*} [Field E] [Differential E] (f : E) : Prop :=
  ∃ (v : E) (l : List (E × E)), (∀ p ∈ l, p.1′ = 0 ∧ p.2 ≠ 0) ∧
    f = v′ + (l.map fun p ↦ p.1 * logDeriv p.2).sum

variable {E : Type u} [Field E] [Differential E]

lemma LiouvilleFormE.map {E' : Type*} [Field E'] [Differential E'] (j : E →+* E')
    (hj : ∀ z : E, (j z)′ = j z′) {f : E} (h : LiouvilleFormE f) : LiouvilleFormE (j f) := by
  obtain ⟨v, l, hl, rfl⟩ := h
  refine ⟨j v, l.map fun p ↦ (j p.1, j p.2), fun p hp ↦ ?_, ?_⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ⟨by rw [hj, (hl q hq).1, map_zero], (map_ne_zero j).mpr (hl q hq).2⟩
  · rw [map_add, hj, map_list_sum, List.map_map, List.map_map]
    congr 2
    refine List.map_congr_left fun p _ ↦ ?_
    simp only [Function.comp_apply, map_mul, logDeriv, map_div₀, hj]

lemma LiouvilleFormE.hasElementaryIntegralIn {f : E} (h : LiouvilleFormE f) :
    HasElementaryIntegralIn f := by
  intro E' _ _ _ _ _
  obtain ⟨v, l, hl, heq⟩ := h.map (algebraMap E E') (fun z ↦ deriv_algebraMap z)
  rw [heq]
  exact hasElementaryIntegral_of_liouville_form v l hl

lemma LiouvilleFormE.hasElementaryIntegral {f : E} (h : LiouvilleFormE f) :
    HasElementaryIntegral f := h.hasElementaryIntegralIn.hasElementaryIntegral

lemma liouvilleFormE_deriv (v : E) : LiouvilleFormE v′ := ⟨v, [], by simp, by simp⟩

end Form

section Curve

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]
variable {F : Type*} [Field F] [DecidableEq F] [CharZero F]

/-- **A positive answer of `decideRF` is an exact derivative.** -/
theorem decideRF_true (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E) (hx : S.x′ = 1)
    (P : CurveProb F) (ι : F →+* Kc) (hSF : S.F = (toB P.Fc).map (mapRingHom ι))
    (h : P.decideRF = some true) : LiouvilleFormE ((S.fE P ι : Kc⟮S.x⟯⟮S.y⟯) : E) := by
  classical
  unfold CurveProb.decideRF at h
  by_cases hval : P.valid = true
  swap
  · rw [if_neg hval] at h; exact absurd h (by simp)
  rw [if_pos hval] at h
  have hV := P.valid_spec hval
  split at h
  · exact absurd h (by simp)
  · rename_i cs hsome
    by_cases hres : P.allRes.all (· = 0) = true
    swap
    · rw [if_neg hres] at h; exact absurd h (by simp)
    rw [if_pos hres] at h
    have hb := Option.some.inj h
    rw [S.zeroTest_iff hC hx hSF hV hV.len hV.last cs] at hb
    rw [hb]
    exact liouvilleFormE_deriv _

/-- **A positive answer of `decideLog` is a Liouville form.** -/
theorem decideLog_true [EllQuad.QCoords F] (hC : ∀ c : Kc, c′ = 0) (S : CurveData Kc E)
    (hx : S.x′ = 1) (P : CurveProb F) (ι : F →+* Kc) (hSF : S.F = (toB P.Fc).map (mapRingHom ι))
    (ws : List (LogWit F)) (h : P.decideLog ws = some true) :
    LiouvilleFormE ((S.fE P ι : Kc⟮S.x⟯⟮S.y⟯) : E) := by
  classical
  unfold CurveProb.decideLog at h
  by_cases hval : P.valid = true
  swap
  · rw [if_neg hval] at h; exact absurd h (by simp)
  rw [if_pos hval] at h
  have hV := P.valid_spec hval
  split at h
  · exact absurd h (by simp)
  · rename_i cs hsome
    by_cases hres : P.allRes.all (· = 0) = true
    · rw [if_pos hres] at h
      have hb := Option.some.inj h
      rw [S.zeroTest_iff hC hx hSF hV hV.len hV.last cs] at hb
      rw [hb]
      exact liouvilleFormE_deriv _
    rw [if_neg hres] at h
    by_cases hwit : P.witCheck ws = true
    swap
    · rw [if_neg hwit] at h; exact absurd h (by simp)
    rw [if_pos hwit] at h
    have hb := Option.some.inj h
    have h0 := (S.logTest_iff hC hx hSF hV cs ws hwit).mp hb
    rw [CurveData.hL, sub_eq_zero, sub_eq_iff_eq_add'] at h0
    rw [h0]
    refine ⟨(S.vvE P ι cs : E), (List.finRange (dim F)).map fun j ↦
      (algebraMap Kc E (CurveData.cj ι ws j), (S.uE ι (CurveProb.witAt ws j) : E)),
      fun p hp ↦ ?_, ?_⟩
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
      exact ⟨by rw [deriv_algebraMap, hC, map_zero],
        S.uE_ne_zero hSF hV _ j (P.witCheck_spec ws hwit j)⟩
    · rw [List.map_map, sum_finRange_map]
      rfl

end Curve

end Curves
