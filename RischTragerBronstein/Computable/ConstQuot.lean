import RischTragerBronstein.Computable.LimitedPrimWComplete

/-!
# The constant quotient of two polynomials over `R(x)`

`Tower.constQuot P Q`: if `P = c · Q` for a constant `c` (of any extension `S ⊇ R` of the
constants), returns that constant, which then lies in `R`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- The candidate constant `P / Q`. -/
def constQuot (P Q : GPoly (GFrac R)) : Option R :=
  let q := (GPoly.divMod (ops₁g R) P Q).1
  let nd := normFrac (q.getD 0 ([], [1]))
  match CPoly.linSolve [nd.2] nd.1 with
  | some [c] => some c
  | _ => none

end Defs

variable {R S K₁ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]

local notation "φ" => algebraMap S[X] K₁

theorem constQuot_complete (ι : R →+* S) (h0 : ∀ s : S, s′ = 0)
    (hD : ∀ P : S[X], P′ = derivative P) (Pc Qc : GPoly (GFrac R)) (c : S)
    (hQc0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Qc ≠ 0)
    (hPQ : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Pc =
      C (φ (C c)) * GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Qc) :
    ∃ c', constQuot Pc Qc = some c' ∧ ι c' = c := by
  set M₁ := M₁In (K₁ := K₁) ι h0 hD with hM₁
  have hinj₁ : Function.Injective φ := IsFractionRing.injective S[X] K₁
  set ct : K₁ := φ (C c) with hct
  have hdq := GPoly.divMod_spec M₁ Pc Qc
  have hdr := GPoly.divMod_degree_lt M₁ Pc Qc hQc0
  set q := (GPoly.divMod (ops₁g R) Pc Qc).1 with hq
  have hqC : GPoly.toPoly M₁ q = C ct := by
    by_contra hne
    have hne' : GPoly.toPoly M₁ q - C ct ≠ 0 := sub_ne_zero.mpr hne
    have hmul : (GPoly.toPoly M₁ q - C ct) * GPoly.toPoly M₁ Qc =
        -GPoly.toPoly M₁ (GPoly.divMod (ops₁g R) Pc Qc).2 := by
      linear_combination hPQ - hdq
    have hle : (GPoly.toPoly M₁ Qc).degree ≤
        (GPoly.toPoly M₁ (GPoly.divMod (ops₁g R) Pc Qc).2).degree := by
      rw [← degree_neg (GPoly.toPoly M₁ (GPoly.divMod (ops₁g R) Pc Qc).2), ← hmul, degree_mul]
      exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hne')
    exact absurd hdr (not_lt.mpr hle)
  have hsem0 : CPoly.ev K₁ ι (q.getD 0 ([], [1])) = ct := by
    have h1 := congrArg (fun P : K₁[X] ↦ P.coeff 0) hqC
    simp only [GPoly.coeff_toPoly, coeff_C_zero] at h1
    rw [← sem_M₁In (K₁ := K₁) ι h0 hD, ← h1]
    exact (getD_map_sem_zero M₁ q ([], [1]) (by
      rw [hM₁, sem_M₁In]; simp [CPoly.ev, CPoly.toPoly])).symm
  set nd := normFrac (q.getD 0 ([], [1])) with hnd
  have hnd2 : CPoly.toPoly nd.2 ≠ 0 := normFrac_den_ne_zero _
  have hnd2' : (CPoly.toPoly nd.2).map ι ≠ 0 :=
    (Polynomial.map_ne_zero_iff ι.injective).mpr hnd2
  have hndev : (CPoly.toPoly nd.1).map ι = C c * (CPoly.toPoly nd.2).map ι := by
    have h1 : CPoly.ev K₁ ι nd = ct := by rw [hnd, ev_normFrac, hsem0]
    apply hinj₁
    have hφd : φ ((CPoly.toPoly nd.2).map ι) ≠ 0 := (map_ne_zero_iff _ hinj₁).mpr hnd2'
    rw [map_mul, ← hct, ← h1, CPoly.ev]
    field_simp
  have hne := CPoly.linSolve_complete_map ι [nd.2] nd.1 [c] rfl (by
    simp [CPoly.lcombS, hndev])
  obtain ⟨cs, hcs⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨hlen, hcomb⟩ := CPoly.linSolve_sound _ _ _ hcs
  obtain ⟨c', rfl⟩ := List.length_eq_one_iff.mp hlen
  refine ⟨c', by simp only [constQuot, ← hq, ← hnd, hcs], ?_⟩
  have h1 : C c' * CPoly.toPoly nd.2 = CPoly.toPoly nd.1 := by
    simpa [CPoly.lcomb] using hcomb
  have h2 := congrArg (Polynomial.map ι) h1
  rw [Polynomial.map_mul, map_C, hndev] at h2
  exact C_injective (mul_right_cancel₀ hnd2' h2)

end Tower
