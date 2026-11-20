import RischTragerBronstein.Mixed.NKUnits0D
import RischTragerBronstein.Mixed.NKUnitsCDExists

/-!
# Existence of S-unit certificates with denominators

`unitsC0D_exists`: for S-units `uᵢ = wᵢ t^{−jᵢ}` where `wᵢ = pᵢ(θ)` and `wᵢ′ = qᵢ(θ)` have code
coordinates, are integral over `Fₘ[t]` and satisfy `wᵢ wᵢ′ = t^{kᵢ}`, the checks of `unitsC0D` succeed.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential GTors

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

section Exists0

variable (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp : List (GPoly (LC m)))
  (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0)
  (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range Pp.length, (a j : L) * θ ^ j = 0 →
    ∀ j < Pp.length, a j = 0)
include hP hind

lemma unitDCD_complete (U V : List (GPoly (LC m))) (d : GPoly (LC m)) (k : ℕ)
    (h : T.evθ m h1 θ (nkFl Fc ks m U) * T.evθ m h1 θ (nkFl Fc ks m V) =
      T.evP m d * T.evP m d * T.ts m ^ k) :
    unitDCD Fc ks m Pp U V d k = true := by
  refine T.zeroModC_complete m h1 θ Pp hP hind _ ?_
  simp only [T.evθ_subC, T.evθ_mulC, T.evθ_nkFl_single, T.evP_monoG m h1.of_succ]
  rw [h, sub_self]

lemma logDerDCD_complete (U V : List (GPoly (LC m))) (d : GPoly (LC m)) (k j : ℕ) (ηc : LC m)
    (gl dθ wθ : GPoly (LC (m + 1))) (hts : T.ts m ≠ 0)
    (hd1 : zeroModC Fc ks m Pp (GPoly.add (MO Fc ks (m + 1)) (GPoly.mul (MO Fc ks (m + 1)) dθ
      (GPoly.derivX (MO Fc ks (m + 1)) (nkPC Fc ks m Pp))) (GPoly.mapD (MO Fc ks (m + 1)) (nkPC Fc ks m Pp))) = true)
    (hw1 : zeroModC Fc ks m Pp (GPoly.sub (MO Fc ks (m + 1)) (GPoly.mul (MO Fc ks (m + 1)) wθ
      (GPoly.derivX (MO Fc ks (m + 1)) (nkPC Fc ks m Pp))) [(MO Fc ks (m + 1)).one]) = true)
    (hθ' : θ′ = T.evθ m h1 θ dθ) (hd : T.evP m d ≠ 0)
    (huv : T.evθ m h1 θ (nkFl Fc ks m U) * T.evθ m h1 θ (nkFl Fc ks m V) =
      T.evP m d * T.evP m d * T.ts m ^ k)
    (hgl : T.evθ m h1 θ gl = (T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d)′ /
      (T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d) - (j : L) * T.ev m ηc) :
    logDerDCD Fc ks m Pp U V d k j ηc gl dθ wθ = true := by
  unfold logDerDCD
  simp only [Bool.and_eq_true]
  refine ⟨⟨hd1, hw1⟩, T.zeroModC_complete m h1 θ Pp hP hind _ ?_⟩
  have hjη : T.ev m ((MO Fc ks m).mul (mcst Fc ks m (j : ℚ)) ηc) = (j : L) * T.ev m ηc := by
    rw [← T.sem_MP m h1.of_succ, (T.MP m h1.of_succ).sem_mul, T.sem_mcst m h1.of_succ,
      IntermediateField.coe_mul, T.sem_MP m h1.of_succ]
    push_cast; ring
  simp only [T.evθ_subC, T.evθ_mulC, T.evθ_addC, T.evθ_nkFl_single, T.evP_monoG m h1.of_succ,
    T.evP_smulG m h1.of_succ, hjη]
  have hu' := T.deriv_evθ_MO m h1 θ (nkFl Fc ks m U)
  have hD' := T.deriv_evθ_MO m h1 θ (nkFl Fc ks m [d])
  rw [T.evθ_nkFl_single] at hD'
  rw [← hθ']
  have e1 : T.evθ m h1 θ (GPoly.mapD (MO Fc ks (m + 1)) (nkFl Fc ks m U)) =
      (T.evθ m h1 θ (nkFl Fc ks m U))′ -
        T.evθ m h1 θ (GPoly.derivX (MO Fc ks (m + 1)) (nkFl Fc ks m U)) * θ′ := by
    rw [hu']; ring
  have e2 : T.evθ m h1 θ (GPoly.mapD (MO Fc ks (m + 1)) (nkFl Fc ks m [d])) =
      (T.evP m d)′ - T.evθ m h1 θ (GPoly.derivX (MO Fc ks (m + 1)) (nkFl Fc ks m [d])) * θ′ := by
    rw [hD']; ring
  rw [e1, e2]
  set uu := T.evθ m h1 θ (nkFl Fc ks m U)
  set vv := T.evθ m h1 θ (nkFl Fc ks m V)
  set δ := T.evP m d
  have htk : T.ts m ^ k ≠ 0 := pow_ne_zero _ hts
  have hu0 : uu ≠ 0 := fun h0 ↦ mul_ne_zero (mul_ne_zero hd hd) htk (by rw [← huv, h0, zero_mul])
  have hv : vv = δ * δ * T.ts m ^ k / uu := by field_simp; linear_combination huv
  rw [Derivation.leibniz_div] at hgl
  simp only [smul_eq_mul] at hgl
  rw [hgl, hv]
  field_simp
  ring

/-- **S-unit certificates with denominators exist.** -/
theorem unitsC0D_exists (hts : T.ts m ≠ 0) (ηc : LC m) (dθ wθ : GPoly (LC (m + 1)))
    (s : List (LC (m + 1))) (gls : List (GPoly (LC (m + 1))))
    (ps qs : Fin gls.length → GPoly (LC (m + 1))) (kf jf : Fin gls.length → ℕ)
    (cU cV : Fin gls.length → List (GPoly (LC m)))
    (hpq : ∀ i, T.evθ m h1 θ (ps i) * T.evθ m h1 θ (qs i) = T.ts m ^ kf i)
    (hjk : ∀ i, jf i ≤ kf i)
    (hU : ∀ i, hornerZ (T.evθ m h1 θ (ps i)) ((cU i).map (T.evP m)) 1 = 0)
    (hV : ∀ i, hornerZ (T.evθ m h1 θ (qs i)) ((cV i).map (T.evP m)) 1 = 0)
    (hd1 : zeroModC Fc ks m Pp (GPoly.add (MO Fc ks (m + 1)) (GPoly.mul (MO Fc ks (m + 1)) dθ
      (GPoly.derivX (MO Fc ks (m + 1)) (nkPC Fc ks m Pp))) (GPoly.mapD (MO Fc ks (m + 1)) (nkPC Fc ks m Pp))) = true)
    (hw1 : zeroModC Fc ks m Pp (GPoly.sub (MO Fc ks (m + 1)) (GPoly.mul (MO Fc ks (m + 1)) wθ
      (GPoly.derivX (MO Fc ks (m + 1)) (nkPC Fc ks m Pp))) [(MO Fc ks (m + 1)).one]) = true)
    (hθ' : θ′ = T.evθ m h1 θ dθ)
    (hgl : ∀ i : Fin gls.length, T.evθ m h1 θ (gls.getD i []) =
      (T.evθ m h1 θ (ps i))′ / T.evθ m h1 θ (ps i) - (jf i : L) * T.ev m ηc)
    (hlen : ∀ i < gls.length, (gls.getD i []).length ≤ Pp.length)
    (htr : ∀ i < gls.length, (MOr Fc ks (m + 1)).isZero (nkTau Fc ks m Pp.length (gls.getD i []) s) = true) :
    ∃ (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ) (ds : List (GPoly (LC m)))
      (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1)))),
      unitsC0D Fc ks m Pp Us Vs kk jj ds cUs cVs Es ηc gls dθ wθ s = true := by
  -- reuse the unit construction: `p q` with `p q = tᵏ`; clear denominators of `p` and `q`
  have hpq' : ∀ i, T.evθ m h1 θ (ps i) * (T.evθ m h1 θ (qs i) / T.ts m ^ kf i) = 1 := fun i ↦ by
    rw [← mul_div_assoc, hpq i, div_self (pow_ne_zero _ hts)]
  choose U1 d1 hd1' hU1 using fun i ↦ T.clear_den m h1 θ (ps i)
  choose V1 d2 hd2' hV1 using fun i ↦ T.clear_den m h1 θ (qs i)
  have hmapC : ∀ (W : List (GPoly (LC m))) (c : GPoly (LC m)),
      T.evθ m h1 θ (nkFl Fc ks m (W.map fun w ↦ GPoly.mul (MO Fc ks m) w c)) =
        T.evP m c * T.evθ m h1 θ (nkFl Fc ks m W) := by
    intro W c
    rw [T.evθ_nkFl, T.evθ_nkFl, List.length_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' : j < W.length := Finset.mem_range.mp hj
    rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map,
      List.getD_eq_getElem _ _ hj', T.evP_mulC m h1.of_succ]
    ring
  set d : Fin gls.length → GPoly (LC m) := fun i ↦ GPoly.mul (MO Fc ks m) (d1 i) (d2 i) with hdd
  have hd : ∀ i, T.evP m (d i) ≠ 0 := fun i ↦ by
    rw [hdd]; simp only; rw [T.evP_mulC m h1.of_succ]; exact mul_ne_zero (hd1' i) (hd2' i)
  set U : Fin gls.length → List (GPoly (LC m)) := fun i ↦
    (U1 i).map fun w ↦ GPoly.mul (MO Fc ks m) w (d2 i) with hUU
  set V : Fin gls.length → List (GPoly (LC m)) := fun i ↦
    (V1 i).map fun w ↦ GPoly.mul (MO Fc ks m) w (d1 i) with hVV
  have hUd : ∀ i, T.evθ m h1 θ (nkFl Fc ks m (U i)) / T.evP m (d i) = T.evθ m h1 θ (ps i) :=
    fun i ↦ by
      rw [hUU, hdd]; simp only; rw [hmapC, hU1, T.evP_mulC m h1.of_succ]
      have := hd1' i; have := hd2' i
      field_simp
  have hVd : ∀ i, T.evθ m h1 θ (nkFl Fc ks m (V i)) / T.evP m (d i) = T.evθ m h1 θ (qs i) :=
    fun i ↦ by
      rw [hVV, hdd]; simp only; rw [hmapC, hV1, T.evP_mulC m h1.of_succ]
      have := hd1' i; have := hd2' i
      field_simp
  let qd : Fin gls.length → LC (m + 1) := fun i ↦
    (([(MO Fc ks m).one], d i) : GPoly (LC m) × GPoly (LC m))
  set E : Fin gls.length → GPoly (LC (m + 1)) := fun i ↦ [qd i] with hE
  have hEv : ∀ i, T.evP m (d i) * T.evθ m h1 θ (E i) = 1 := fun i ↦ by
    rw [hE]; simp only
    rw [T.evθ_consC m h1 θ (qd i) [], T.evθ_nilC, mul_zero, add_zero, ev_frac]
    change T.evP m (d i) * (T.evP m [(MO Fc ks m).one] / T.evP m (d i)) = 1
    rw [T.evP_oneC m h1.of_succ]
    field_simp [hd i]
  refine ⟨List.ofFn U, List.ofFn V, List.ofFn kf, List.ofFn jf, List.ofFn d, List.ofFn cU,
    List.ofFn cV, List.ofFn E, ?_⟩
  unfold unitsC0D
  rw [List.all_eq_true]
  intro i hi
  have hi' : i < gls.length := List.mem_range.mp hi
  set k : Fin gls.length := ⟨i, hi'⟩
  simp only [getD_ofFn_lt' _ hi', Bool.and_eq_true, decide_eq_true_eq]
  have huv : T.evθ m h1 θ (nkFl Fc ks m (U k)) * T.evθ m h1 θ (nkFl Fc ks m (V k)) =
      T.evP m (d k) * T.evP m (d k) * T.ts m ^ kf k := by
    have a1 := hUd k
    have a2 := hVd k
    rw [div_eq_iff (hd k)] at a1 a2
    rw [a1, a2]; linear_combination (T.evP m (d k) * T.evP m (d k)) * hpq k
  refine ⟨⟨⟨⟨⟨⟨⟨T.unitDCD_complete m h1 θ Pp hP hind _ _ _ _ huv,
    T.unitIC_complete m h1 θ Pp hP hind _ _ _ (hd k) (by rw [hUd k]; exact hU k)⟩,
    T.unitIC_complete m h1 θ Pp hP hind _ _ _ (hd k) (by rw [hVd k]; exact hV k)⟩,
    T.invD_complete m h1 θ Pp hP hind _ _ (hEv k)⟩, hjk k⟩, ?_⟩, hlen i hi'⟩, htr i hi'⟩
  refine T.logDerDCD_complete m h1 θ Pp hP hind _ _ _ _ _ _ _ dθ wθ hts hd1 hw1 hθ' (hd k) huv ?_
  rw [hUd k]
  exact hgl k

end Exists0

end MTower

end Curves.MT

