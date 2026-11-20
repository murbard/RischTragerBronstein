import RischTragerBronstein.Mixed.NKUnitsCD
import RischTragerBronstein.Mixed.NKUnits0D
import RischTragerBronstein.Mixed.NKConstBasis

/-!
# Logarithmic derivatives of certified units with denominators

`units_logsD`, `units0_logsD`: the analogues of `units_logs`, `units0_logs` for `unitsCD`,
`unitsC0D` — each `uᵢ = Uᵢ/dᵢ` (resp. `(Uᵢ/dᵢ) t^{−jᵢ}`) is nonzero with `gᵢ = uᵢ′/uᵢ`.
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

lemma units_logsD (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp : List (GPoly (LC m)))
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0)
    (Us Vs : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
    (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
    (gls : List (GPoly (LC (m + 1)))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsCD Fc ks m Pp Us Vs ds cUs cVs Es gls dθ wθ s = true) :
    ∀ i < gls.length,
      T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) / T.evP m (ds.getD i []) ≠ 0 ∧
      T.evθ m h1 θ (gls.getD i []) =
        (T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) / T.evP m (ds.getD i []))′ /
          (T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) / T.evP m (ds.getD i [])) := by
  intro i hi
  have hf := T.unitsCD_facts m h1 θ Pp hP _ _ _ _ _ _ _ dθ wθ (unitsCD_spec hU i hi).1
    (unitsCD_spec hU i hi).2.1
  exact ⟨left_ne_zero_of_mul_eq_one hf.2.1, hf.2.2.2.2⟩

lemma units0_logsD (m : ℕ) (h1 : T.Tr (m + 1)) (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m)) (θ : L) (Pp : List (GPoly (LC m)))
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0)
    (Us Vs : List (List (GPoly (LC m)))) (kk jj : List ℕ) (ds : List (GPoly (LC m)))
    (cUs cVs : List (List (GPoly (LC m)))) (Es : List (GPoly (LC (m + 1))))
    (gls : List (GPoly (LC (m + 1)))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hU : unitsC0D Fc ks m Pp Us Vs kk jj ds cUs cVs Es ((MO Fc ks m).deriv a) gls dθ wθ s = true) :
    ∀ i < gls.length,
      T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) / T.evP m (ds.getD i []) *
        T.ts m ^ (-((jj.getD i 0 : ℕ) : ℤ)) ≠ 0 ∧
      T.evθ m h1 θ (gls.getD i []) =
        (T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) / T.evP m (ds.getD i []) *
          T.ts m ^ (-((jj.getD i 0 : ℕ) : ℤ)))′ /
        (T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) / T.evP m (ds.getD i []) *
          T.ts m ^ (-((jj.getD i 0 : ℕ) : ℤ))) := by
  have hts : T.ts m ≠ 0 := fun h ↦ htr ⟨X, X_ne_zero, by rw [aeval_X]; exact h⟩
  intro i hi
  have hf := T.units0D_facts m h1 θ Pp hP hts _ _ _ _ _ _ _ _ _ _ dθ wθ
    (unitsC0D_spec hU i hi).1 (unitsC0D_spec hU i hi).2.1
  have hW0 : T.evθ m h1 θ (nkFl Fc ks m (Us.getD i [])) / T.evP m (ds.getD i []) ≠ 0 := fun h0 ↦
    pow_ne_zero _ hts (by rw [← hf.2.1, h0, zero_mul])
  have hηE : T.ev m ((MO Fc ks m).deriv a) = logDeriv (T.ts m) := by
    rw [logDeriv, T.deriv_ts_L_exp m h1.of_succ hm hk, T.sem_MP m h1.of_succ, mul_div_assoc,
      div_self hts, mul_one]
  refine ⟨mul_ne_zero hW0 (zpow_ne_zero _ hts), ?_⟩
  rw [hf.2.2.2.2, ← logDeriv, ← logDeriv, Differential.logDeriv_mul _ _ hW0 (zpow_ne_zero _ hts),
    logDeriv_zpow' _ hts, hηE]
  push_cast
  ring

end MTower

end Curves.MT
