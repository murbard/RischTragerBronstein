import RischTragerBronstein.Mixed.NKMultLin
import RischTragerBronstein.Mixed.NKUnits0Decide
import RischTragerBronstein.Mixed.NKWitET

/-!
# From an independence certificate to linear independence of logarithmic derivatives

`hli_of_indepC`: units certified by `unitsC` whose logarithmic derivatives pass `indepC` (they are
multiplicatively independent modulo `Fₘ₊₁`, `indepC_sound1`) have logarithmic derivatives that are
linearly independent over the constants of the code field modulo `Fₘ₊₁` (`hli_of_mult`) — the
hypothesis of the `…PW` deciders, for every realization of the tower.
-/

open Polynomial IntermediateField Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM GTors

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Certified independence gives the hypothesis of the `…PW` deciders.** -/
theorem hli_of_indepC (m : ℕ) (Pp : List (GPoly (LC m))) (hn0 : 0 < Pp.length) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hind : ∀ h1 : T.Tr (m + 1), ∀ a : ℕ → T.F (m + 1),
      ∑ j ∈ Finset.range Pp.length, (a j : L) * θ ^ j = 0 → ∀ j < Pp.length, a j = 0)
    (Us Vs : List (List (GPoly (LC m)))) (gls : List (GPoly (LC (m + 1))))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true) (hU : unitsC Fc ks m Pp Us Vs gls dθ wθ s = true)
    (J : List ℕ) (H : List (List (LC (m + 1)))) (hJH : indepC Fc ks m gls J H = true) :
    ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
      (∀ i, (c i)′ = 0) →
      (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0 := by
  intro h1
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hlogs := T.units_logs m h1 θ Pp hP Us Vs gls dθ wθ s hU
  refine T.hli_of_mult m h1 θ Pp hP hn0 (hind h1) Us Vs gls dθ wθ s hs hU fun a ⟨c, hc⟩ ↦ ?_
  exact T.indepC_sound1 m h1 θ Pp.length (hind h1) gls (fun i hi ↦ (unitsC_spec hU i hi).2.2.1)
    (fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (Us.getD i []))) (fun i ↦ (hlogs i i.2).1)
    (fun i ↦ (hlogs i i.2).2) J H hJH a
    ⟨⟨algebraMap Cc L c, T.const_mem (m + 1) c⟩, hc⟩

end MTower

end Curves.MT
