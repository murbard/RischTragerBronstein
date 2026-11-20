import RischTragerBronstein.Jacobian.PrincipalMul

/-!
# The torsion bound from one prime, and from two primes

`principal_of_reduction`: over a Henselian discrete valuation ring `O` (fraction field `K`,
residue field `𝕜`), if `(s ℓ) D` is principal over `K` with `ℓ` a unit of `O`, and `m D̄` is
principal over `𝕜`, then `(m s) D` is principal over `K`. (Apply it with `s` the `p`-part of the
order: the order of a torsion divisor divides `m · pᵃ`.)

`dvd_mul_of_two_primes`: `gcd (m pᵃ) (m' qᵇ) ∣ m m'` for distinct primes `p, q` — so with two
primes of good reduction, a torsion divisor `D` has `(m_p m_q) D` principal.
-/

open Polynomial

namespace Jac

section Aux

variable {R S : Type*} [CommRing R] [CommRing S]

lemma emap_escale (φ : R →+* S) (n : ℕ) (Γ : EDiv R) :
    emap φ (escale n Γ) = escale n (emap φ Γ) := by
  simp [emap, escale, Function.comp_def]

lemma escale_escale (n m : ℕ) (Γ : EDiv R) : escale n (escale m Γ) = escale (n * m) Γ := by
  simp [escale, Function.comp_def, mul_assoc]

lemma pairwise_escale {n : ℕ} {Γ : EDiv R} (h : Γ.Pairwise fun q q' ↦ IsUnit (q.1 - q'.1)) :
    (escale n Γ).Pairwise fun q q' ↦ IsUnit (q.1 - q'.1) := by
  simp only [escale, List.pairwise_map]; exact h

lemma OnCurve.escale' {f : R[X]} {n : ℕ} {Γ : EDiv R} (h : OnCurve f Γ) :
    OnCurve f (Jac.escale n Γ) := by
  intro q hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
  exact h q' hq'

end Aux

variable {O K : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [HenselianRing O (IsLocalRing.maximalIdeal O)] [Field K] [Algebra O K] [IsFractionRing O K]

local notation "𝕜" => IsLocalRing.ResidueField O
local notation "ρ" => IsLocalRing.residue O
local notation "ι" => algebraMap O K

/-- **The one-prime torsion bound.** -/
theorem principal_of_reduction {ϖ : O} (hϖ : Irreducible ϖ) (h2 : IsUnit (2 : O)) {g : ℕ}
    (f : O[X]) (hf : f.natDegree = 2 * g + 1) (hlc : IsUnit f.leadingCoeff)
    (x y : Fin g → O) (hyu : ∀ i, IsUnit (y i)) (hyf : ∀ i, y i ^ 2 = f.eval (x i))
    (hx : ∀ i j, i ≠ j → IsUnit (x i - x j))
    (Γ : EDiv O) (hon : OnCurve f Γ) (hΓx : Γ.Pairwise fun q q' ↦ IsUnit (q.1 - q'.1))
    (hΓE : ∀ q ∈ Γ, ∀ i, IsUnit (q.1 - x i))
    {s ℓ m : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓ : IsUnit (ℓ : O))
    (hn : PrincipalMul (f.map ι) g (emap ι Γ) (s * ℓ))
    (hm : PrincipalMul (f.map ρ) g (emap ρ Γ) m) :
    PrincipalMul (f.map ι) g (emap ι Γ) (m * s) := by
  have hι : Function.Injective ι := IsFractionRing.injective O K
  have hfK : (f.map ι).natDegree = 2 * g + 1 := by rw [natDegree_map_eq_of_injective hι, hf]
  have hfk : (f.map ρ).natDegree = 2 * g + 1 := by
    rw [natDegree_map_of_leadingCoeff_ne_zero _ ((hlc.map ρ).ne_zero), hf]
  have honK : OnCurve (f.map ι) (emap ι Γ) := OnCurve.map hon
  have honk : OnCurve (f.map ρ) (emap ρ Γ) := OnCurve.map hon
  obtain ⟨γb, hγ0, hγp, hγv⟩ := hm.of_dvd hfk honk (dvd_mul_right m s)
  obtain ⟨Ξ, hΞ0, hΞp, hΞv⟩ := hn.of_dvd hfK honK (show s * ℓ ∣ ℓ * (m * s) from
    ⟨m, by ring⟩)
  obtain ⟨γ, hγ0', hγp', hγv'⟩ := torsion_descends hϖ h2 f hf hlc x y hyu hyf hx
    (escale (m * s) Γ) (OnCurve.escale' hon) (pairwise_escale hΓx)
    (fun q hq i ↦ by obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq; exact hΓE q' hq' i)
    γb hγ0 (by rw [edeg_escale, ← edeg_emap ρ Γ]; exact hγp)
    (by rw [emap_escale]; exact hγv) ℓ hℓ1 hℓ Ξ hΞ0
    (by rw [edeg_escale, ← edeg_emap ι Γ, ← mul_assoc]; exact hΞp)
    (by rw [emap_escale, escale_escale]; exact hΞv)
  exact ⟨γ, hγ0', by rw [edeg_escale, ← edeg_emap ι Γ] at hγp'; exact hγp',
    by rw [emap_escale] at hγv'; exact hγv'⟩

/-- `gcd (m pᵃ) (m' qᵇ) ∣ m m'` for distinct primes. -/
theorem gcd_dvd_mul_of_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (m m' a b : ℕ) : Nat.gcd (m * p ^ a) (m' * q ^ b) ∣ m * m' := by
  set G := Nat.gcd (m * p ^ a) (m' * q ^ b)
  have hG1 : G ∣ m * p ^ a := Nat.gcd_dvd_left _ _
  have hG2 : G ∣ m' * q ^ b := Nat.gcd_dvd_right _ _
  -- split `G` into its part coprime to `q` and its `q`-part
  have hcop : Nat.Coprime (p ^ a) (q ^ b) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq)
  -- `G ∣ lcm`-style argument: `G ∣ m (m' qᵇ)` and `G ∣ (m pᵃ) m'`
  have h1 : G ∣ m * (m' * q ^ b) := Dvd.dvd.mul_left hG2 m
  have h2 : G ∣ m * p ^ a * m' := Dvd.dvd.mul_right hG1 m'
  have h3 : G ∣ Nat.gcd (m * m' * q ^ b) (m * m' * p ^ a) :=
    Nat.dvd_gcd (by rw [← mul_assoc] at h1; exact h1) (by
      rw [show m * p ^ a * m' = m * m' * p ^ a by ring] at h2; exact h2)
  rw [Nat.gcd_mul_left, (hcop.symm).gcd_eq_one, mul_one] at h3
  exact h3

end Jac
