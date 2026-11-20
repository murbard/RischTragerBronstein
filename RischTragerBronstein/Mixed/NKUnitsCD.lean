import RischTragerBronstein.Mixed.NKUnitIC
import RischTragerBronstein.Mixed.NKInfRDecide

/-!
# Unit certificates with denominators

`unitsCD`: the analogue of `unitsC` for units `uᵢ = Uᵢ/dᵢ` of the integral closure of `Fₘ[t]`
that need not lie in `Fₘ[t][θ]`: `Uᵢ Vᵢ ≡ dᵢ²`, `Uᵢ/dᵢ` and `Vᵢ/dᵢ` integral (`unitIC`), `dᵢ`
invertible (`dᵢ Eᵢ ≡ 1`), and `gᵢ = uᵢ′/uᵢ` (`logDerChkD`). `unitsCD_facts` collects what the
units-span arguments use.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential GTors

universe u

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **Units with denominators**, certified. -/
def unitsCD (m : ℕ) (Pp : List (GPoly (LC m))) (Us Vs : List (List (GPoly (LC m))))
    (ds : List (GPoly (LC m))) (cUs cVs : List (List (GPoly (LC m))))
    (Es : List (GPoly (LC (m + 1)))) (gls : List (GPoly (LC (m + 1))))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1))) : Bool :=
  (List.range gls.length).all fun i ↦
    (unitCD Fc ks m Pp (Us.getD i []) (Vs.getD i []) (ds.getD i []) &&
      unitIC Fc ks m Pp (Us.getD i []) (ds.getD i []) (cUs.getD i []) &&
      unitIC Fc ks m Pp (Vs.getD i []) (ds.getD i []) (cVs.getD i []) &&
      zeroModC Fc ks m Pp (GPoly.sub (MO Fc ks (m + 1))
        (GPoly.mul (MO Fc ks (m + 1)) (nkFl Fc ks m [ds.getD i []]) (Es.getD i []))
        [(MO Fc ks (m + 1)).one])) &&
    logDerChkD Fc ks m Pp (Us.getD i []) (Vs.getD i []) (ds.getD i []) (gls.getD i []) dθ wθ &&
    decide ((gls.getD i []).length ≤ Pp.length) &&
    (MOr Fc ks (m + 1)).isZero (nkTau Fc ks m Pp.length (gls.getD i []) s)

end Codes

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}

lemma unitsCD_spec {m : ℕ} {Pp : List (GPoly (LC m))} {Us Vs : List (List (GPoly (LC m)))}
    {ds : List (GPoly (LC m))} {cUs cVs : List (List (GPoly (LC m)))}
    {Es : List (GPoly (LC (m + 1)))}
    {gls : List (GPoly (LC (m + 1)))} {dθ wθ : GPoly (LC (m + 1))} {s : List (LC (m + 1))}
    (h : unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true) (i : ℕ) (hi : i < gls.length) :
    (unitCD Fc ks m Pp (Us.getD i []) (Vs.getD i []) (ds.getD i []) = true ∧
      unitIC Fc ks m Pp (Us.getD i []) (ds.getD i []) (cUs.getD i []) = true ∧
      unitIC Fc ks m Pp (Vs.getD i []) (ds.getD i []) (cVs.getD i []) = true ∧
      zeroModC Fc ks m Pp (GPoly.sub (MO Fc ks (m + 1))
        (GPoly.mul (MO Fc ks (m + 1)) (nkFl Fc ks m [ds.getD i []]) (Es.getD i []))
        [(MO Fc ks (m + 1)).one]) = true) ∧
    logDerChkD Fc ks m Pp (Us.getD i []) (Vs.getD i []) (ds.getD i []) (gls.getD i []) dθ wθ = true ∧
    (gls.getD i []).length ≤ Pp.length ∧
    (MOr Fc ks (m + 1)).isZero (nkTau Fc ks m Pp.length (gls.getD i []) s) = true := by
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨⟨this.1.1.1.1.1.1, this.1.1.1.1.1.2, this.1.1.1.1.2, this.1.1.1.2⟩, this.1.1.2, this.1.2,
    this.2⟩

variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **What a `unitsCD` certificate gives**, for `u = U/δ`, `v = V/δ`: `δ ≠ 0`, `u v = 1`, `u`
and `v` are roots of monic polynomials over `Fₘ[t]`, and `g = u′/u`. -/
lemma unitsCD_facts (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp : List (GPoly (LC m)))
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0) (U V : List (GPoly (LC m))) (d : GPoly (LC m))
    (cU cV : List (GPoly (LC m))) (E : GPoly (LC (m + 1))) (gl dθ wθ : GPoly (LC (m + 1)))
    (h : (unitCD Fc ks m Pp U V d = true ∧ unitIC Fc ks m Pp U d cU = true ∧
      unitIC Fc ks m Pp V d cV = true ∧
      zeroModC Fc ks m Pp (GPoly.sub (MO Fc ks (m + 1))
        (GPoly.mul (MO Fc ks (m + 1)) (nkFl Fc ks m [d]) E) [(MO Fc ks (m + 1)).one]) = true))
    (hg : logDerChkD Fc ks m Pp U V d gl dθ wθ = true) :
    T.evP m d ≠ 0 ∧
    T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d * (T.evθ m h1 θ (nkFl Fc ks m V) / T.evP m d) = 1 ∧
    hornerZ (T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d) (cU.map (T.evP m)) 1 = 0 ∧
    hornerZ (T.evθ m h1 θ (nkFl Fc ks m V) / T.evP m d) (cV.map (T.evP m)) 1 = 0 ∧
    T.evθ m h1 θ gl = (T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d)′ /
      (T.evθ m h1 θ (nkFl Fc ks m U) / T.evP m d) := by
  obtain ⟨huv, hIU, hIV, hE⟩ := h
  have hE' := T.zeroModC_sound m h1 θ Pp _ hP hE
  rw [T.evθ_subC, T.evθ_mulC, T.evθ_nkFl_single, T.evθ_one_MO, sub_eq_zero] at hE'
  have hδ : T.evP m d ≠ 0 := left_ne_zero_of_mul_eq_one hE'
  have huv' := T.unitCD_sound m h1 θ Pp U V d hP huv
  refine ⟨hδ, ?_, T.unitIC_sound m h1 θ Pp U d cU hP hδ hIU,
    T.unitIC_sound m h1 θ Pp V d cV hP hδ hIV,
    T.logDerChkD_sound m h1 θ Pp U V d gl dθ wθ hP hδ huv' hg⟩
  rw [div_mul_div_comm, huv', div_self (mul_ne_zero hδ hδ)]

end MTower

end Curves.MT
