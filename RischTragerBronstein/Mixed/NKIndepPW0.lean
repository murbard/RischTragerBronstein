import RischTragerBronstein.Mixed.NKIndepPW

/-!
# From a Wronskian independence certificate to the hypothesis of the split-at-0 `…PW` deciders

`hli_of_indepWC0`: S-units `uᵢ t^{−jᵢ}` certified by `unitsC0` whose logarithmic derivatives pass
`indepWC` are multiplicatively independent modulo `Fₘ₊₁` (`indepWC_sound1`), so their logarithmic
derivatives are linearly independent over the constants of the code field modulo `Fₘ₊₁`
(`hli_of_mult0`).
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

/-- **Certified independence of S-units gives the hypothesis of the split-at-0 `…PW` deciders.** -/
theorem hli_of_indepWC0 (m : ℕ) (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (Pp : List (GPoly (LC m))) (hn0 : 0 < Pp.length) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hind : ∀ h1 : T.Tr (m + 1), ∀ a : ℕ → T.F (m + 1),
      ∑ j ∈ Finset.range Pp.length, (a j : L) * θ ^ j = 0 → ∀ j < Pp.length, a j = 0)
    (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ) (gls : List (GPoly (LC (m + 1))))
    (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (hU : unitsC0 Fc ks m Pp Us Vs kk jj ((MO Fc ks m).deriv a) gls dθ wθ s = true)
    (J D : List ℕ) (H : List (List (LC (m + 1)))) (hJH : indepWC Fc ks m gls J D H = true) :
    ∀ h1 : T.Tr (m + 1), ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) →
      (∀ i, (c i)′ = 0) →
      (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0 := by
  intro h1
  have htr := h1 m (by omega)
  have hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hlogs := T.units0_logs m h1 hm hk htr θ Pp hP Us Vs kk jj gls dθ wθ s hU
  refine T.hli_of_mult0 m h1 hm hk htr θ Pp hP hn0 (hind h1) Us Vs kk jj gls dθ wθ s hs hU
    fun e ⟨c, hc⟩ ↦ ?_
  exact T.indepWC_sound1 m h1 θ Pp.length hn0 (hind h1) gls
    (fun i hi ↦ (unitsC0_spec hU i hi).2.2.1)
    (fun i ↦ T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) * T.ts m ^ (-((jj.getD i 0 : ℕ) : ℤ)))
    (fun i ↦ (hlogs i i.2).1) (fun i ↦ (hlogs i i.2).2) J D H hJH e
    ⟨⟨algebraMap Cc L c, T.const_mem (m + 1) c⟩, hc⟩

end MTower

end Curves.MT

