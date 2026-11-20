import RischTragerBronstein.Mixed.MTSpecs
import RischTragerBronstein.Mixed.LTTransfer

/-!
# Mixed towers over a curve: lifting and restricting realizations

* `MTower.exists_lift`: a realization pushed into any differential extension `E` of `L`, over
  the constants of `E` (the curve over the new constants, `curve_over_constants`);
* `MTower.exists_sub`: the sub-tower of height `k`, realized inside the field `F k`, which it
  generates.

Unlike logarithmic towers, no transfer of transcendence is needed here: the certificate `certC`
proves it in every realization (`mspecs`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT

universe u v

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}

lemma kderC_map {L L' : Type*} [Field L] [Differential L] [Field L'] [Differential L']
    (ψ : L →+* L') (hψ : ∀ z, (ψ z)′ = ψ z′) {m : ℕ} (ev : LC m → L) (t : L) :
    ∀ k : KindC m, kderC (fun q ↦ ψ (ev q)) (ψ t) k = ψ (kderC ev t k)
  | .prim η => rfl
  | .exp a => by simp only [kderC, hψ, map_mul]

section Lift

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **The realization in an extension**, over its constants. -/
theorem MTower.exists_lift (T : MTower Fc ks Cc L) (E : Type v) [Field E] [Differential E]
    [Algebra L E] [DifferentialAlgebra L E] [CharZero E] :
    ∃ T' : MTower Fc ks (constants E) E, T'.n = T.n ∧
      (∀ i, T'.ts i = algebraMap L E (T.ts i)) ∧
      (∀ m q, T'.ev m q = algebraMap L E (T.ev m q)) ∧
      (∀ m, ∀ z ∈ T.F m, algebraMap L E z ∈ T'.F m) := by
  obtain ⟨φ, SL, hxL, hSLx, hSLy, hSLF, hφ, hmem⟩ := curve_over_constants T.hC T.S T.hx T.hconst E
  have hSFL : SL.F = (toB Fc).map (mapRingHom (algebraMap ℚ (constants E))) := by
    rw [hSLF, T.hSF, Polynomial.map_map, mapRingHom_comp]
    congr 2
    exact RingHom.ext_rat _ _
  set ψ := algebraMap L E with hψ
  have hCc : ∀ c : constants E, c′ = 0 := fun _ ↦ rfl
  have hsem : ∀ a, (cM hCc SL hxL Fc hSFL).sem a = ψ ((cM T.hC T.S T.hx Fc T.hSF).sem a) :=
    fun a ↦ sem_cM_map T.hC T.S T.hx Fc T.hSF hCc SL hxL hSFL ψ hSLx hSLy a
  have hev : ∀ m q, evL (cM hCc SL hxL Fc hSFL).sem (fun i ↦ ψ (T.ts i)) m q = ψ (T.ev m q) :=
    fun m q ↦ map_evL ψ _ _ hsem T.ts m q
  have hψd : ∀ z : L, (ψ z)′ = ψ z′ := fun z ↦ deriv_algebraMap z
  let T' : MTower Fc ks (constants E) E :=
    { S := SL
      hC := hCc
      hx := hxL
      hSF := hSFL
      n := T.n
      ts := fun i ↦ ψ (T.ts i)
      hts := fun m hm ↦ by simp only [T.hts m hm, map_zero]
      ht := fun m hm ↦ by
        have e : evL (cM hCc SL hxL Fc hSFL).sem (fun i ↦ ψ (T.ts i)) m =
            fun q ↦ ψ (T.ev m q) := funext (hev m)
        rw [e, kderC_map ψ hψd, hψd, T.ht m hm]
      hts0 := fun m hm a hk ↦ (map_ne_zero ψ).mpr (T.hts0 m hm a hk)
      hconst := fun z hz ↦ ⟨⟨z, hz⟩, rfl⟩ }
  have hmemT : ∀ m, ∀ z ∈ T.F m, ψ z ∈ T'.F m := by
    intro m
    induction m with
    | zero => exact fun z hz ↦ hmem z hz
    | succ m ih =>
      intro z hz
      let N : IntermediateField (T.F m) L :=
        { carrier := {w | ψ w ∈ T'.F (m + 1)}
          mul_mem' := fun {a b} ha hb ↦ by
            change ψ (a * b) ∈ T'.F (m + 1); rw [map_mul]; exact mul_mem ha hb
          one_mem' := by change ψ 1 ∈ T'.F (m + 1); rw [map_one]; exact one_mem _
          add_mem' := fun {a b} ha hb ↦ by
            change ψ (a + b) ∈ T'.F (m + 1); rw [map_add]; exact add_mem ha hb
          zero_mem' := by change ψ 0 ∈ T'.F (m + 1); rw [map_zero]; exact zero_mem _
          algebraMap_mem' := fun f ↦ T'.le_succ m (ih f f.2)
          inv_mem' := fun a ha ↦ by
            change ψ a⁻¹ ∈ T'.F (m + 1); rw [map_inv₀]; exact inv_mem ha }
      have hle : IntermediateField.adjoin (T.F m) {T.ts m} ≤ N := by
        rw [IntermediateField.adjoin_le_iff]
        rintro w rfl
        exact T'.ts_mem m
      exact hle ((T.mem_F_succ).mp hz)
  exact ⟨T', rfl, fun _ ↦ rfl, hev, hmemT⟩

end Lift

/-! ### The sub-tower of height `k` inside `F k` -/

section Sub

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

/-- **The sub-tower of height `k`**, realized inside the field `F k`; it generates `F k`. -/
theorem MTower.exists_sub (T : MTower Fc ks Cc L) (k : ℕ) (hk : k ≤ T.n) :
    ∃ T' : MTower Fc ks Cc (T.F k), T'.n = k ∧
      (∀ m ≤ k, ∀ q, ((T'.ev m q : T.F k) : L) = T.ev m q) ∧
      (∀ z : T.F k, z ∈ T'.F k) ∧ (∀ i < k, ((T'.ts i : T.F k) : L) = T.ts i) := by
  have hx0 : T.S.x ∈ T.F k := T.F_mono (Nat.zero_le k)
    ((Cc⟮T.S.x⟯⟮T.S.y⟯).algebraMap_mem ⟨T.S.x, mem_adjoin_simple_self Cc T.S.x⟩)
  have hy0 : T.S.y ∈ T.F k := T.F_mono (Nat.zero_le k) (mem_adjoin_simple_self _ T.S.y)
  set S' := restrictC T.S (T.F k) hx0 hy0 with hS'
  have hx' : S'.x′ = 1 := Subtype.ext (by rw [MTower.coe_deriv]; exact T.hx)
  set j := algebraMap (T.F k) L with hj
  have hjd : ∀ z : T.F k, (j z)′ = j z′ := fun z ↦ rfl
  have hsem0 : ∀ a, (cM T.hC T.S T.hx Fc T.hSF).sem a = j ((cM T.hC S' hx' Fc T.hSF).sem a) :=
    fun a ↦ sem_cM_map T.hC S' hx' Fc T.hSF T.hC T.S T.hx T.hSF j rfl rfl a
  set ts' : ℕ → T.F k := fun i ↦ if h : i < k then
    ⟨T.ts i, T.F_mono (by omega : i + 1 ≤ k) (T.ts_mem i)⟩ else 0 with hts'
  have hts'j : ∀ i < k, j (ts' i) = T.ts i := fun i hi ↦ by
    simp only [hts', dif_pos hi]; rfl
  have hev : ∀ m ≤ k, ∀ q, j (evL (cM T.hC S' hx' Fc T.hSF).sem ts' m q) = T.ev m q := by
    intro m hm q
    rw [← map_evL j _ _ hsem0 ts' m q]
    exact evL_congr _ _ _ m (fun i hi ↦ hts'j i (by omega)) q
  let T' : MTower Fc ks Cc (T.F k) :=
    { S := S'
      hC := T.hC
      hx := hx'
      hSF := T.hSF
      n := k
      ts := ts'
      hts := fun m hm ↦ by simp only [hts', dif_neg (show ¬m < k by omega)]
      ht := fun m hm ↦ by
        apply j.injective
        have e : (fun q ↦ j (evL (cM T.hC S' hx' Fc T.hSF).sem ts' m q)) = T.ev m :=
          funext (hev m hm.le)
        rw [← hjd, ← kderC_map j hjd, e, hts'j m hm, T.ht m (by omega)]
      hts0 := fun m hm a hk h0 ↦ T.hts0 m (by omega) a hk (by
        rw [← hts'j m hm, h0, map_zero])
      hconst := fun z hz ↦ by
        obtain ⟨c, hc⟩ := T.hconst (z : L) (by rw [← MTower.coe_deriv, hz]; rfl)
        exact ⟨c, Subtype.ext hc⟩ }
  have hgen : ∀ m ≤ k, ∀ z : T.F k, (z : L) ∈ T.F m → z ∈ T'.F m := by
    intro m
    induction m with
    | zero => exact fun _ z hz ↦ restrictC_gen T.S (T.F k) hx0 hy0 z hz
    | succ m ih =>
      intro hm z hz
      let N : IntermediateField (T.F m) L :=
        { carrier := {w | ∃ h : w ∈ T.F k, (⟨w, h⟩ : T.F k) ∈ T'.F (m + 1)}
          mul_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ ↦ ⟨mul_mem ha hb, mul_mem ha' hb'⟩
          one_mem' := ⟨one_mem _, one_mem _⟩
          add_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ ↦ ⟨add_mem ha hb, add_mem ha' hb'⟩
          zero_mem' := ⟨zero_mem _, zero_mem _⟩
          algebraMap_mem' := fun f ↦ ⟨T.F_mono (by omega) f.2,
            T'.le_succ m (ih (by omega) ⟨f, T.F_mono (by omega) f.2⟩ f.2)⟩
          inv_mem' := fun a ⟨ha, ha'⟩ ↦ ⟨inv_mem ha, inv_mem ha'⟩ }
      have hle : IntermediateField.adjoin (T.F m) {T.ts m} ≤ N := by
        rw [IntermediateField.adjoin_le_iff]
        rintro w rfl
        refine ⟨T.F_mono (by omega : m + 1 ≤ k) (T.ts_mem m), ?_⟩
        have : (⟨T.ts m, T.F_mono (by omega : m + 1 ≤ k) (T.ts_mem m)⟩ : T.F k) = T'.ts m := by
          change _ = ts' m
          simp only [hts', dif_pos (show m < k by omega)]
        rw [this]
        exact T'.ts_mem m
      obtain ⟨h, h'⟩ := hle ((T.mem_F_succ).mp hz)
      exact h'
  exact ⟨T', rfl, fun m hm q ↦ hev m hm q, fun z ↦ hgen k le_rfl z z.2, hts'j⟩

end Sub

end Curves.MT
