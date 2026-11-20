import RischTragerBronstein.Mixed.NKUnitsCD
import RischTragerBronstein.Mixed.NKUnits0Decide

/-!
# S-unit certificates with denominators (places above `t = 0`)

`unitsC0D`: the analogue of `unitsC0` for S-units `uᵢ = (Uᵢ/dᵢ) t^{−jᵢ}` where `Uᵢ/dᵢ` and
`Vᵢ/dᵢ` are integral over `Fₘ[t]` (`unitIC`) with `(Uᵢ/dᵢ)(Vᵢ/dᵢ) = t^{kᵢ}` (`unitDCD`), and
`gᵢ = uᵢ′/uᵢ` (`logDerDCD`: `g d² tᵏ + j η d² tᵏ + d′ d tᵏ ≡ U′V`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential GTors

universe u

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- `U V ≡ d² tᵏ` modulo `P`. -/
def unitDCD (m : ℕ) (Pp : List (GPoly (LC m))) (U V : List (GPoly (LC m))) (d : GPoly (LC m))
    (k : ℕ) : Bool :=
  let O1 := MO Fc ks (m + 1)
  let D := nkFl Fc ks m [d]
  zeroModC Fc ks m Pp (GPoly.sub O1 (GPoly.mul O1 (nkFl Fc ks m U) (nkFl Fc ks m V))
    (GPoly.mul O1 (GPoly.mul O1 D D) (nkFl Fc ks m [monoG Fc ks m k])))

/-- `θ′ = dθ`, `wθ P_Y ≡ 1`, and `g d² tᵏ + j η d² tᵏ + d′ d tᵏ ≡ U′ V` modulo `P`. -/
def logDerDCD (m : ℕ) (Pp : List (GPoly (LC m))) (U V : List (GPoly (LC m))) (d : GPoly (LC m))
    (k j : ℕ) (ηc : LC m) (gl dθ wθ : GPoly (LC (m + 1))) : Bool :=
  let O1 := MO Fc ks (m + 1)
  let P := nkPC Fc ks m Pp
  let u := nkFl Fc ks m U
  let D := nkFl Fc ks m [d]
  let Tk := nkFl Fc ks m [monoG Fc ks m k]
  zeroModC Fc ks m Pp (GPoly.add O1 (GPoly.mul O1 dθ (GPoly.derivX O1 P)) (GPoly.mapD O1 P)) &&
  zeroModC Fc ks m Pp (GPoly.sub O1 (GPoly.mul O1 wθ (GPoly.derivX O1 P)) [O1.one]) &&
  zeroModC Fc ks m Pp (GPoly.sub O1
    (GPoly.add O1 (GPoly.add O1 (GPoly.mul O1 gl (GPoly.mul O1 (GPoly.mul O1 D D) Tk))
      (GPoly.mul O1 (nkFl Fc ks m [GPoly.smul (MO Fc ks m) ((MO Fc ks m).mul (mcst Fc ks m (j : ℚ)) ηc)
        (monoG Fc ks m k)]) (GPoly.mul O1 D D)))
      (GPoly.mul O1 (GPoly.add O1 (GPoly.mapD O1 D) (GPoly.mul O1 dθ (GPoly.derivX O1 D)))
        (GPoly.mul O1 D Tk)))
    (GPoly.mul O1 (GPoly.add O1 (GPoly.mapD O1 u) (GPoly.mul O1 dθ (GPoly.derivX O1 u)))
      (nkFl Fc ks m V)))

/-- **S-units with denominators**, certified. -/
def unitsC0D (m : ℕ) (Pp : List (GPoly (LC m))) (Us Vs : List (List (GPoly (LC m))))
    (kk jj : List ℕ) (ds : List (GPoly (LC m))) (cUs cVs : List (List (GPoly (LC m))))
    (Es : List (GPoly (LC (m + 1)))) (ηc : LC m)
    (gls : List (GPoly (LC (m + 1)))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1))) : Bool :=
  (List.range gls.length).all fun i ↦
    (unitDCD Fc ks m Pp (Us.getD i []) (Vs.getD i []) (ds.getD i []) (kk.getD i 0) &&
      unitIC Fc ks m Pp (Us.getD i []) (ds.getD i []) (cUs.getD i []) &&
      unitIC Fc ks m Pp (Vs.getD i []) (ds.getD i []) (cVs.getD i []) &&
      zeroModC Fc ks m Pp (GPoly.sub (MO Fc ks (m + 1))
        (GPoly.mul (MO Fc ks (m + 1)) (nkFl Fc ks m [ds.getD i []]) (Es.getD i []))
        [(MO Fc ks (m + 1)).one])) &&
    decide (jj.getD i 0 ≤ kk.getD i 0) &&
    logDerDCD Fc ks m Pp (Us.getD i []) (Vs.getD i []) (ds.getD i []) (kk.getD i 0) (jj.getD i 0) ηc
      (gls.getD i []) dθ wθ &&
    decide ((gls.getD i []).length ≤ Pp.length) &&
    (MOr Fc ks (m + 1)).isZero (nkTau Fc ks m Pp.length (gls.getD i []) s)

end Codes

lemma unitsC0D_spec {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {m : ℕ} {Pp : List (GPoly (LC m))}
    {Us Vs : List (List (GPoly (LC m)))} {kk jj : List ℕ} {ds : List (GPoly (LC m))}
    {cUs cVs : List (List (GPoly (LC m)))} {Es : List (GPoly (LC (m + 1)))} {ηc : LC m}
    {gls : List (GPoly (LC (m + 1)))} {dθ wθ : GPoly (LC (m + 1))} {s : List (LC (m + 1))}
    (h : unitsC0D Fc ks m Pp Us Vs kk jj ds cUs cVs Es ηc gls dθ wθ s = true) (i : ℕ)
    (hi : i < gls.length) :
    (unitDCD Fc ks m Pp (Us.getD i []) (Vs.getD i []) (ds.getD i []) (kk.getD i 0) = true ∧
      unitIC Fc ks m Pp (Us.getD i []) (ds.getD i []) (cUs.getD i []) = true ∧
      unitIC Fc ks m Pp (Vs.getD i []) (ds.getD i []) (cVs.getD i []) = true ∧
      zeroModC Fc ks m Pp (GPoly.sub (MO Fc ks (m + 1))
        (GPoly.mul (MO Fc ks (m + 1)) (nkFl Fc ks m [ds.getD i []]) (Es.getD i []))
        [(MO Fc ks (m + 1)).one]) = true) ∧
    logDerDCD Fc ks m Pp (Us.getD i []) (Vs.getD i []) (ds.getD i []) (kk.getD i 0) (jj.getD i 0) ηc
      (gls.getD i []) dθ wθ = true ∧
    (gls.getD i []).length ≤ Pp.length ∧
    (MOr Fc ks (m + 1)).isZero (nkTau Fc ks m Pp.length (gls.getD i []) s) = true ∧
    jj.getD i 0 ≤ kk.getD i 0 := by
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨⟨this.1.1.1.1.1.1.1, this.1.1.1.1.1.1.2, this.1.1.1.1.1.2, this.1.1.1.1.2⟩, this.1.1.2,
    this.1.2, this.2, this.1.1.1.2⟩

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **What a `unitsC0D` certificate gives**, for `w = U/δ`, `w' = V/δ`: `δ ≠ 0`, `w w' = tᵏ`, `w`
and `w'` integral over `Fₘ[t]`, and `g = w′/w − j η`. -/
lemma units0D_facts (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp : List (GPoly (LC m)))
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0) (hts : T.ts m ≠ 0)
    (U V : List (GPoly (LC m))) (d : GPoly (LC m)) (k j : ℕ) (ηc : LC m)
    (cU cV : List (GPoly (LC m))) (E : GPoly (LC (m + 1))) (gl dθ wθ : GPoly (LC (m + 1)))
    (h : (unitDCD Fc ks m Pp U V d k = true ∧ unitIC Fc ks m Pp U d cU = true ∧
      unitIC Fc ks m Pp V d cV = true ∧
      zeroModC Fc ks m Pp (GPoly.sub (MO Fc ks (m + 1))
        (GPoly.mul (MO Fc ks (m + 1)) (nkFl Fc ks m [d]) E) [(MO Fc ks (m + 1)).one]) = true))
    (hg : logDerDCD Fc ks m Pp U V d k j ηc gl dθ wθ = true) :
    T.evP m d ≠ 0 ∧
    T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d * (T.evθ m h1 θ (nkFl Fc ks m V) / T.evP m d) =
      T.ts m ^ k ∧
    hornerZ (T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d) (cU.map (T.evP m)) 1 = 0 ∧
    hornerZ (T.evθ m h1 θ (nkFl Fc ks m V) / T.evP m d) (cV.map (T.evP m)) 1 = 0 ∧
    T.evθ m h1 θ gl = (T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d)′ /
      (T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d) - (j : L) * T.ev m ηc := by
  obtain ⟨huv, hIU, hIV, hE⟩ := h
  have hE' := T.zeroModC_sound m h1 θ Pp _ hP hE
  rw [T.evθ_subC, T.evθ_mulC, T.evθ_nkFl_single, T.evθ_one_MO, sub_eq_zero] at hE'
  have hδ : T.evP m d ≠ 0 := left_ne_zero_of_mul_eq_one hE'
  have huv' := T.zeroModC_sound m h1 θ Pp _ hP huv
  simp only [T.evθ_subC, T.evθ_mulC, T.evθ_nkFl_single, T.evP_monoG m h1.of_succ,
    sub_eq_zero] at huv'
  refine ⟨hδ, ?_, T.unitIC_sound m h1 θ Pp U d cU hP hδ hIU,
    T.unitIC_sound m h1 θ Pp V d cV hP hδ hIV, ?_⟩
  · rw [div_mul_div_comm, huv']; field_simp
  · unfold logDerDCD at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨⟨hd, hw⟩, hg⟩ := hg
    have hθ' := T.deriv_θ_of_chk m h1 θ Pp dθ wθ hP hd hw
    have hg' := T.zeroModC_sound m h1 θ Pp _ hP hg
    have hjη : T.ev m ((MO Fc ks m).mul (mcst Fc ks m (j : ℚ)) ηc) = (j : L) * T.ev m ηc := by
      rw [← T.sem_MP m h1.of_succ, (T.MP m h1.of_succ).sem_mul, T.sem_mcst m h1.of_succ,
        IntermediateField.coe_mul, T.sem_MP m h1.of_succ]
      push_cast; ring
    simp only [T.evθ_subC, T.evθ_addC, T.evθ_mulC, T.evθ_nkFl_single, T.evP_monoG m h1.of_succ,
      T.evP_smulG m h1.of_succ, hjη, sub_eq_zero] at hg'
    have hu' := T.deriv_evθ_MO m h1 θ (nkFl Fc ks m U)
    have hD' := T.deriv_evθ_MO m h1 θ (nkFl Fc ks m [d])
    rw [T.evθ_nkFl_single] at hD'
    rw [← hθ'] at hg'
    have e1 : T.evθ m h1 θ (GPoly.mapD (MO Fc ks (m + 1)) (nkFl Fc ks m U)) =
        (T.evθ m h1 θ (nkFl Fc ks m U))′ -
          T.evθ m h1 θ (GPoly.derivX (MO Fc ks (m + 1)) (nkFl Fc ks m U)) * θ′ := by
      rw [hu']; ring
    have e2 : T.evθ m h1 θ (GPoly.mapD (MO Fc ks (m + 1)) (nkFl Fc ks m [d])) =
        (T.evP m d)′ - T.evθ m h1 θ (GPoly.derivX (MO Fc ks (m + 1)) (nkFl Fc ks m [d])) * θ′ := by
      rw [hD']; ring
    rw [e1, e2] at hg'
    set uu := T.evθ m h1 θ (nkFl Fc ks m U)
    set vv := T.evθ m h1 θ (nkFl Fc ks m V)
    set δ := T.evP m d
    have htk : T.ts m ^ k ≠ 0 := pow_ne_zero _ hts
    have hu0 : uu ≠ 0 := fun h0 ↦ mul_ne_zero (mul_ne_zero hδ hδ) htk (by rw [← huv', h0, zero_mul])
    have hv : vv = δ * δ * T.ts m ^ k / uu := by field_simp; linear_combination huv'
    rw [hv] at hg'
    rw [Derivation.leibniz_div]
    simp only [smul_eq_mul]
    field_simp
    field_simp at hg'
    linear_combination hg'

end MTower

end Curves.MT
