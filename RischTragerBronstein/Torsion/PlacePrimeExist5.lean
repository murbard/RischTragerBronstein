import RischTragerBronstein.Torsion.PlacePrimeExist4

/-!
# Place data modulo large primes (5): orders of the denominator, goodness at large primes

* **`muD_red`**: at a good prime, the order of the reduced denominator at a reduced fibre is the
  characteristic-`0` order (for every ramification `N`);
* **`evG_goodPl`**: the goodness hypotheses of the place checks hold at all large primes.
-/

open Polynomial Filter

namespace Curves

open CPoly Sup

section Red

variable {K : Type*} [Field K] [DecidableEq K] {p : ℕ} [Fact p.Prime] (R : RedFns p K)
  {φ : K →+* ℚ_[p]} (hR : RedValid p R φ)

local notation "Sφ" => intSub φ
local notation "gφ" => psiRed φ

include hR in
/-- **The reduced denominator has the same order at the reduced fibre.** -/
theorem muD_red {Dc : CPoly K} {a : K} (hD : ∀ c ∈ Dc, R.ok c = true) (ha : R.ok a = true)
    (hne : muD Dc a 1 < (compC Dc (shiftC a 1)).length)
    (hG : Good R ((compC Dc (shiftC a 1)).getD (muD Dc a 1) 0)) {N : ℕ} (hN : 0 < N) :
    muD (Dc.map R.red) (R.red a) N = muD Dc a N ∧
      muD (Dc.map R.red) (R.red a) N < (compC (Dc.map R.red) (shiftC (R.red a) N)).length := by
  have hDS : InS Sφ Dc := inS_of_ok R hR hD
  have haS : a ∈ Sφ := mem_intSub_of_ok R hR ha
  obtain ⟨hs, hs'⟩ := shiftC_pext (g := gφ) haS 1
  obtain ⟨hc, hc'⟩ := compC_pext (g := gφ) _ hs Dc hDS
  have e1 : compC (Dc.map R.red) (shiftC (R.red a) 1) = (compC Dc (shiftC a 1)).map (pext Sφ gφ) := by
    rw [hc', hs', ← pext_eq_red R hR ha, map_pext_eq R hR hD]
  have hou : OrdUnit Sφ gφ (compC Dc (shiftC a 1)) :=
    ordUnit_of (zp_of_good R hR hG)
  have h1 : muD (Dc.map R.red) (R.red a) 1 = muD Dc a 1 := by
    unfold muD
    rw [e1, ordC_pext _ hc hou]
  have h1' : muD (Dc.map R.red) (R.red a) 1 < (compC (Dc.map R.red) (shiftC (R.red a) 1)).length := by
    rw [h1, e1, List.length_map]; exact hne
  obtain ⟨m1, m2⟩ := muD_mul (Dc.map R.red) (R.red a) hN h1'
  obtain ⟨m3, -⟩ := muD_mul Dc a hN hne
  exact ⟨by rw [m1, m3, h1], m2⟩

end Red

section Ev

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

local notation "KM" => NFC.NF M

/-- **The goodness hypotheses of the place checks hold at all large primes.** -/
theorem evG_goodPl (Fc : BPoly KM) (n : ℕ) (Dc : CPoly KM) (xs : List KM) (D : PlaceCert KM) :
    EvG fun p R ↦ GoodPl R Fc n Dc xs D := by
  have h1 := (evG_good 0).and ((evG_goodLL Fc).and ((evG_goodL Dc).and ((evG_goodL xs).and
    ((evG_lt D.fib.length fun j _ ↦ evG_good (D.fα j)).and
    (evG_lt D.fib.length fun j _ ↦ evG_lt D.fib.length fun j' _ ↦ evG_good (D.fα j - D.fα j'))))))
  have h2 := (evG_lt D.pl.length fun π _ ↦ evG_goodL (D.py π)).and
    ((evG_lt D.fib.length fun j _ ↦ evG_lt n fun k _ ↦ evG_good (D.rζ j k)).and
    ((evG_lt D.fib.length fun j _ ↦
      evG_good ((compC Dc (shiftC (D.fα j) 1)).getD (muD Dc (D.fα j) 1) 0)).and
    ((evG_lt D.fib.length fun j _ ↦ evG_lt xs.length fun i _ ↦ evG_good (D.fα j - xs.getD i 0)).and
    ((evG_lt D.pl.length fun π _ ↦ evG_good (derivLead Fc (D.fα (D.pj π)) (D.pe π) (D.py π))).and
    (evG_lt D.fib.length fun j _ ↦ evG_lt n fun k _ ↦ evG_lt n fun l _ ↦
      evG_lt (D.tp.getD j 0) fun i _ ↦
        evG_good ((D.apx j k).getD i 0 - (D.apx j l).getD i 0))))))
  refine (h1.and h2).mono fun p R h ↦ ?_
  obtain ⟨⟨z, F, Dg, x, α, αd⟩, py, ζ, μ, αx, u, sep⟩ := h
  exact ⟨z, F, Dg, x, α, αd, py, ζ, μ, αx, u, sep⟩

end Ev

end Curves
