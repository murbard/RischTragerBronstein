import RischTragerBronstein.Torsion.PcERefine
import RischTragerBronstein.Torsion.PrimeCertExist3

/-!
# Place data modulo large primes (1): integrality of all approximations

For a family `Ds t` of place certificates over `NF M` refining each other (same fibres and places,
approximations extended as `t` grows, precisions growing past `t`), all coefficients of all
approximations are integral at every prime where `M` and the data of `Ds 0` are integral
(**`py_ok_family`**): every coefficient is a coefficient of the root certified by `Ds 0`
(`rep_coeff_ok`).
-/

open Polynomial

namespace Curves

open CPoly Sup

/-- The leading coefficient of `F_Y(a + Tᵉ, y)` (a unit at good primes). -/
def derivLead {F : Type*} [Field F] [DecidableEq F] (Fc : BPoly F) (a : F) (e : ℕ) (y : CPoly F) : F :=
  (bivEval (derivYB Fc) (shiftC a e) y).getD (ordC (bivEval (derivYB Fc) (shiftC a e) y)) 0

section Family

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

local notation "KM" => NFC.NF M

variable {p : ℕ} [Fact p.Prime]

/-- **All approximations of a refining family are integral.** -/
theorem py_ok_family (R : RedFns p KM) (hR : NFRed p R)
    (hM : toPoly M ∈ lifts (ratSub p).subtype) (hlc : (toPoly M).leadingCoeff⁻¹ ∈ ratSub p)
    {Fc : BPoly KM} {n : ℕ} (hF : ∀ P ∈ Fc, ∀ c ∈ P, R.ok c = true) (Ds : ℕ → PlaceCert KM)
    (hchk : ∀ t, (Ds t).Facts Fc n)
    (hfib : ∀ t, (Ds t).fib = (Ds 0).fib) (hpl : ∀ t, (Ds t).pl.length = (Ds 0).pl.length)
    (hpj : ∀ t, ∀ π < (Ds 0).pl.length, (Ds t).pj π = (Ds 0).pj π)
    (hpe : ∀ t, ∀ π < (Ds 0).pl.length, (Ds t).pe π = (Ds 0).pe π)
    (hpp : ∀ t, ∀ π < (Ds 0).pl.length, (Ds 0).pp π ≤ (Ds t).pp π ∧ t < (Ds t).pp π)
    (hlen : ∀ π < (Ds 0).pl.length, (Ds 0).pp π ≤ ((Ds 0).py π).length)
    (hpre : ∀ t t', t ≤ t' → ∀ π < (Ds 0).pl.length, (Ds t).py π <+: (Ds t').py π)
    (h0 : ∀ π < (Ds 0).pl.length, R.ok ((Ds 0).fα ((Ds 0).pj π)) = true ∧
      (∀ c ∈ (Ds 0).py π, R.ok c = true) ∧
      R.ok (derivLead Fc ((Ds 0).fα ((Ds 0).pj π)) ((Ds 0).pe π) ((Ds 0).py π))⁻¹ = true) :
    ∀ t, ∀ π < (Ds t).pl.length, ∀ c ∈ (Ds t).py π, R.ok c = true := by
  intro t π hπ c hc
  rw [hpl] at hπ
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  set t'' := t + i
  have hpre1 := hpre t t'' (by omega) π hπ
  have hpre0 := hpre 0 t'' (Nat.zero_le _) π hπ
  have hci : ((Ds t'').py π).getD i 0 = ((Ds t).py π)[i] := by
    rw [getD_of_prefix hpre1 hi, List.getD_eq_getElem _ _ hi]
  rw [← hci]
  -- the certified root of the refined approximation
  have hπ'' : π < (Ds t'').pl.length := by rw [hpl]; exact hπ
  have hrc := ((hchk t'').pl π hπ'').2.2
  rw [hpj t'' π hπ, hpe t'' π hπ, PlaceCert.fα, hfib t''] at hrc
  obtain ⟨ρ, hρ, hd⟩ := rep_root_field (RingHom.id KM) hrc
  -- it is the root certified by `Ds 0`
  have hrc0 := ((hchk 0).pl π hπ).2.2
  obtain ⟨hpp0, hpp''⟩ := hpp t'' π hπ
  have hd0 : (PowerSeries.X : PowerSeries KM) ^ (Ds 0).pp π ∣
      ρ - thetaT (RingHom.id KM) (toPoly ((Ds 0).py π)) := by
    have h1 := (pow_dvd_pow _ hpp0).trans hd
    have h2 := X_pow_dvd_thetaT_sub (RingHom.id KM) ((Ds t'').py π) ((Ds 0).py π) ((Ds 0).pp π)
      fun j hj ↦ by rw [coeff_toPoly, coeff_toPoly, getD_of_prefix hpre0 (by
        have := hlen π hπ; omega)]
    have := dvd_add h1 h2
    rwa [sub_add_sub_cancel] at this
  obtain ⟨ha, hy, hu⟩ := h0 π hπ
  have hall := rep_coeff_ok R hR hM hlc hF ha hy hrc0 hu ρ hρ hd0
  -- the coefficient `i`
  have hco : PowerSeries.coeff i ρ = ((Ds t'').py π).getD i 0 := by
    have := (PowerSeries.X_pow_dvd_iff.mp hd) i (by omega)
    rw [map_sub, coeff_thetaT, RingHom.id_apply, sub_eq_zero] at this
    exact this
  rw [← hco]
  exact hall i

end Family

end Curves
