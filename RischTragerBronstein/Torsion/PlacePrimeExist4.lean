import RischTragerBronstein.Torsion.PlacePrimeExist3

/-!
# Place data modulo large primes (4): one multiplier for a refining family

**`placeCheck_family`**: for a family `Ds t` of place certificates refining `Ds 0` (same fibres,
places, roots and multiplicities; approximations extended), all passing the checks without the
multiplier at a prime `p`, there is one `m_p` such that every `Ds t` whose precisions dominate
`m_p s Γ_π + μ_j` passes `PlaceCert.primeCheck` with multiplier `m_p`.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Family

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]
variable {p : ℕ} [hp : Fact p.Prime] (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ)

include φ hR in
/-- **One multiplier for a refining family of place certificates.** -/
theorem placeCheck_family {L : Type*} [Field L] [Algebra K L]
    (S : CurveData K L) (T : GlobalCert K) (hSF : S.F = toB T.Fc)
    (hT : GlobalFacts T) (P : PrimeCert p) (hP : PrimeFacts R T P)
    (Ds : ℕ → PlaceCert K) (hchk : ∀ t, (Ds t).Facts T.Fc S.F.natDegree)
    (hfib : ∀ t, (Ds t).fib = (Ds 0).fib) (hrt : ∀ t, (Ds t).rt = (Ds 0).rt)
    (hΓp : ∀ t, (Ds t).Γp = (Ds 0).Γp) (hcΓ : ∀ t, (Ds t).cΓ = (Ds 0).cΓ)
    (hpl : ∀ t, (Ds t).pl.length = (Ds 0).pl.length)
    (hπ : ∀ t, ∀ π < (Ds 0).pl.length, (Ds t).pj π = (Ds 0).pj π ∧ (Ds t).pe π = (Ds 0).pe π ∧
      (Ds 0).pp π ≤ (Ds t).pp π ∧ (Ds 0).py π <+: (Ds t).py π)
    (hlen : ∀ π < (Ds 0).pl.length, (Ds 0).pp π ≤ ((Ds 0).py π).length)
    (hpre : ∀ t, (Ds t).primePre R T.Fc T.n T.I.Dc P.xs = true) :
    ∃ mm : ℕ, 0 < mm ∧ ∀ t,
      (∀ j < (Ds 0).fib.length, muD (T.I.Dc.map R.red) (R.red ((Ds 0).fα j)) ((Ds 0).fN j) <
        (compC (T.I.Dc.map R.red) (shiftC (R.red ((Ds 0).fα j)) ((Ds 0).fN j))).length) →
      (∀ j < (Ds 0).fib.length, ∀ k < T.n,
        mm * ((Ds 0).rs j k * (Ds 0).Γp.getD ((Ds 0).rπ j k) 0) +
          muD (T.I.Dc.map R.red) (R.red ((Ds 0).fα j)) ((Ds 0).fN j) ≤ (Ds t).tp.getD j 0) →
      ∃ Q : PlaceCert.PrimeData p, Q.mp = mm ∧
        (Ds t).primeCheck R T.Fc T.n T.I.δL T.I.Bc T.I.Dc P.xs Q = true := by
  obtain ⟨mm, hmm, hw⟩ := exists_placeWit_ext R φ hR S T hSF hT P hP (Ds 0) (hchk 0) (hpre 0)
  refine ⟨mm, hmm, fun t hμ htp ↦ ?_⟩
  have hfα : ∀ j, (Ds t).fα j = (Ds 0).fα j := fun j ↦ by simp only [PlaceCert.fα, hfib t]
  have hfN : ∀ j, (Ds t).fN j = (Ds 0).fN j := fun j ↦ by simp only [PlaceCert.fN, hfib t]
  have hrs : ∀ j k, (Ds t).rs j k = (Ds 0).rs j k := fun j k ↦ by simp only [PlaceCert.rs, hrt t]
  have hrπ : ∀ j k, (Ds t).rπ j k = (Ds 0).rπ j k := fun j k ↦ by simp only [PlaceCert.rπ, hrt t]
  have hnS : S.F.natDegree = T.n := by rw [hSF, hT.shape.2.2.1]
  have hside : testSideN T.n (T.I.Dc.map R.red) ((Ds t).map R.red).αs
      (((Ds t).map R.red).fcerts T.n) (((Ds t).map R.red).bL T.n mm) = true := by
    refine testSideN_of_tpM _ _ _ _ (fun j hj ↦ ?_) (fun j hj k hk ↦ ?_)
    · rw [PlaceCert.map_fib_length, hfib t] at hj
      rw [PlaceCert.map_fα _ _ _ (by rw [hfib t]; exact hj), PlaceCert.map_fN _ _ _
        (by rw [hfib t]; exact hj), hfα, hfN]
      exact hμ j hj
    · rw [PlaceCert.map_fib_length, hfib t] at hj
      have hjt : j < (Ds t).fib.length := by rw [hfib t]; exact hj
      have h1 : j < (Ds t).rt.length := by rw [(hchk t).rtl]; exact hjt
      have h2 : k < ((Ds t).rt.getD j []).length := by rw [((hchk t).rt j hjt).1, hnS]; exact hk
      rw [PlaceCert.map_rs _ _ _ _ h1 h2, PlaceCert.map_rπ _ _ _ _ h1 h2, PlaceCert.map_Γp,
        PlaceCert.map_tp, PlaceCert.map_fα _ _ _ hjt, PlaceCert.map_fN _ _ _ hjt, hrs, hrπ, hΓp t,
        hfα, hfN]
      exact htp j hj k hk
  have hsome := hw (Ds t) (hfib t) (hrt t) (hΓp t) (hcΓ t) (hpl t)
    (fun π hπ' ↦ ⟨(hπ t π hπ').1, (hπ t π hπ').2.1, (hπ t π hπ').2.2.1, fun i hi ↦
      getD_of_prefix (hπ t π hπ').2.2.2 (lt_of_lt_of_le hi (hlen π hπ'))⟩) (hchk t) (hpre t) hside
  obtain ⟨G, hG⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨⟨mm, G⟩, rfl, ?_⟩
  rw [PlaceCert.primeCheck_eq, hpre t]
  simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hmm, placeWit_spec hG⟩

end Family

end Curves
