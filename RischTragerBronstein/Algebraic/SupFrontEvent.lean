import RischTragerBronstein.Algebraic.SupFrontComplete
import RischTragerBronstein.Algebraic.SupRedGEvent

/-!
# The superelliptic front end is a decision procedure over a number field

`superFront_eventually`: over `K = NF M`, with valid splitting data, global base points (avoiding
the poles `aᵢ`) and a global non-speciality certificate, `superFront` with the global-certificate
torsion oracle answers for every large bound. With `superFront_spec` (and `torsOracleC_spec`)
the answer is correct.
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad Jac

namespace Sup

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

set_option maxHeartbeats 4000000 in
/-- **The front end eventually answers.** -/
theorem superFront_eventually {mZl : List ℤ}
    (hmZ : toPoly M = (toPoly mZl).map (Int.castRingHom ℚ)) (hM1 : 0 < (toPoly mZl).natDegree)
    {fK : CPoly (NFC.NF M)} {n : ℕ} (hn2 : 2 ≤ n) (hd : 0 < fK.length - 1)
    (hlc : fK.getD (fK.length - 1) 0 ≠ 0) (hsq : Squarefree (toPoly fK))
    (hdeg : (toPoly fK).natDegree = fK.length - 1) (hcop : Nat.Coprime n (fK.length - 1))
    {ζ : NFC.NF M} (hζ : IsPrimitiveRoot ζ n)
    {xs ys : List (NFC.NF M)} (hgen : (n - 1) * (fK.length - 1 - 1) ≤ 2 * xs.length)
    (hlen : ys.length = xs.length)
    (hE : ∀ i < xs.length, ys.getD i 0 ≠ 0 ∧ ys.getD i 0 ^ n = evalC fK (xs.getD i 0))
    (hxd : ∀ i < xs.length, ∀ j < xs.length, i ≠ j → xs.getD i 0 ≠ xs.getD j 0)
    {lam : List (List (NFC.NF M))}
    (hcert : ∀ i < xs.length, ∀ ai ∈ basisN n (fK.length - 1) (n * xs.length),
      xs.getD i 0 ^ ai.1 * ys.getD i 0 ^ ai.2 =
        ∑ i' ∈ Finset.range xs.length, ∑ k ∈ Finset.Ico 1 n, lamK lam n i i' k *
          (xs.getD i' 0 ^ ai.1 * (ζ ^ k * ys.getD i' 0) ^ ai.2))
    (A : List (CPoly (NFC.NF M))) (D : CPoly (NFC.NF M)) (hD : toPoly D ≠ 0)
    {m : ℕ} (a b : Fin m → NFC.NF M) (ha : Function.Injective a) (hb : ∀ i, b i ≠ 0)
    (hbf : ∀ i, b i ^ n = (toPoly fK).eval (a i)) (hax : ∀ i, ∀ x ∈ xs, a i ≠ x)
    (lc : NFC.NF M) (hlc0 : lc ≠ 0)
    (hS : toPoly (nbPartK fK D) = Polynomial.C lc * ∏ i, (X - Polynomial.C (a i))) :
    ∃ B0, ∀ B, B0 ≤ B → superFront fK n ζ (torsOracleC (nfRedAt (M := M) mZl)
      (globalCert ζ xs ys lam) (primesBelow B) B fK n) A D a b ≠ none := by
  classical
  have hn : 0 < n := by omega
  have hζn : ζ ^ n = 1 := hζ.pow_eq_one
  have hζl : ∀ l, 0 < l → l < n → ζ ^ l ≠ 1 := fun l hl hln h ↦ by
    have := hζ.pow_eq_one_iff_dvd l |>.mp h
    exact absurd (Nat.le_of_dvd hl this) (by omega)
  set G := frontG fK n A D a
  have hB : ∀ j : Fin (EllQuad.QCoords.dim (NFC.NF M)), ∃ B0, ∀ B, B0 ≤ B →
      (torsJ n ζ a b G (torsOracleC (nfRedAt (M := M) mZl) (globalCert ζ xs ys lam)
        (primesBelow B) B fK n) j).isSome := by
    intro j
    refine torsOracleG_eventually hmZ hM1 hn2 hd hlc hsq hcop hζn hζl hgen hlen hE hxd hcert
      (ptA n a) (ptB n ζ b) (mqJ n ζ a b G j) (fun q ↦ ⟨pt_ne_zero hn hζ b hb q, ?_,
        fun x hx ↦ hax _ x hx⟩) (pt_injective hζ a b ha hb)
    rw [evalC_eq]; exact pt_valid _ hζ a b hbf q
  choose B0 hB0 using hB
  refine ⟨Finset.univ.sup B0, fun B hBB ↦ ?_⟩
  have hp1 : 1 ≤ (toPoly fK).natDegree := by rw [hdeg]; omega
  refine superFront_ne_none_of fK hn hsq hp1 hζ _ (torsOracleC_spec _ _ (fun p _ R h ↦
    nfRedAt_valid mZl hmZ p R h) _ _ hsq hcop) A D hD a b ha hb hbf lc hlc0 hS fun j ↦ ?_
  exact hB0 j B (le_trans (Finset.le_sup (Finset.mem_univ j)) hBB)

end Sup
