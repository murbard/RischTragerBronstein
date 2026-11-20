import RischTragerBronstein.Algebraic.SupPrincipalMul
import RischTragerBronstein.Jacobian.TwoPrimes

/-!
# Deciding torsion on superelliptic Jacobians with two primes

Let `K` be a field (e.g. a number field) with embeddings into `ℚ_p` and `ℚ_q`, under which the
curve `yⁿ = f(x)` and the divisor `Γ` have good integral models (`SupGoodData`: unit leading
coefficient, squarefree reduction, `n` a unit, a primitive `n`-th root of unity in `ℤ_p` also
modulo `p`, non-special base points, points of `Γ` with distinct abscissae modulo `p`).

* `principal_at_prime_N`: if `m Γ̄` is principal modulo `p`, every torsion order `N` of `Γ` gives
  `(m p^{v_p(N)}) Γ` principal over `K`;
* `torsion_iff_two_primes_N`: `Γ` is torsion **iff** `(m_p m_q) Γ` is principal over `K`.
-/

open Polynomial

namespace Sup

instance residueField_padic_finite (p : ℕ) [Fact p.Prime] :
    Finite (IsLocalRing.ResidueField ℤ_[p]) :=
  Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv

/-- **Good integral data at `p`** for the curve `yⁿ = f_K(x)` and the points `(α_q, β_q)` over
`K`, transported to `ℚ_p` by `φ`. -/
structure SupGoodData (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] (φ : K →+* ℚ_[p])
    (fK : K[X]) (n : ℕ) {r : ℕ} (αK βK : Fin r → K) where
  f : ℤ_[p][X]
  hlc : IsUnit f.leadingCoeff
  hfmap : fK.map φ = f.map (algebraMap ℤ_[p] ℚ_[p])
  hsqk : Squarefree (f.map (IsLocalRing.residue ℤ_[p]))
  hnu : IsUnit (n : ℤ_[p])
  ζ : ℤ_[p]
  hζ : IsPrimitiveRoot ζ n
  hζk : IsPrimitiveRoot (IsLocalRing.residue ℤ_[p] ζ) n
  g : ℕ
  hgen : (n - 1) * (f.natDegree - 1) ≤ 2 * g
  x : Fin g → ℤ_[p]
  y : Fin g → ℤ_[p]
  hyu : ∀ i, IsUnit (y i)
  hyf : ∀ i, y i ^ n = f.eval (x i)
  hx : ∀ i j, i ≠ j → IsUnit (x i - x j)
  α : Fin r → ℤ_[p]
  β : Fin r → ℤ_[p]
  hαmap : ∀ q, φ (αK q) = algebraMap ℤ_[p] ℚ_[p] (α q)
  hβmap : ∀ q, φ (βK q) = algebraMap ℤ_[p] ℚ_[p] (β q)
  hβu : ∀ q, IsUnit (β q)
  hβf : ∀ q, β q ^ n = f.eval (α q)
  hα : ∀ q q', α q = α q' ∨ IsUnit (α q - α q')
  hβd : ∀ q q', q ≠ q' → α q = α q' → IsUnit (β q - β q')
  hαx : ∀ q i, IsUnit (α q - x i)
  hNS : ∀ U : (IsLocalRing.ResidueField ℤ_[p])[X][X], (∀ j a, (U.coeff j).coeff a ≠ 0 → j < n ∧
      n * a + f.natDegree * j ≤ n * g) →
    (∀ i k, 1 ≤ k → k < n → evalW U (IsLocalRing.residue ℤ_[p] (x i))
      (IsLocalRing.residue ℤ_[p] ζ ^ k * IsLocalRing.residue ℤ_[p] (y i)) = 0) →
    ∀ i, evalW U (IsLocalRing.residue ℤ_[p] (x i)) (IsLocalRing.residue ℤ_[p] (y i)) = 0

section Padic

variable {p : ℕ} [hp : Fact p.Prime]

local notation "ιp" => algebraMap ℤ_[p] ℚ_[p]
local notation "ρp" => IsLocalRing.residue ℤ_[p]

/-- **One prime.** -/
theorem principal_at_prime_N {K : Type*} [Field K] [DecidableEq K] [PerfectField K]
    (φ : K →+* ℚ_[p]) (fK : K[X]) {n : ℕ} (hn : 0 < n) (hsqK : Squarefree fK)
    (hd : 0 < fK.natDegree) (hcop : Nat.Coprime n fK.natDegree) {r : ℕ} (αK βK : Fin r → K)
    (mu : Fin r → ℕ) (hΓK : ∀ q, (n : K) * βK q ^ (n - 1) ≠ 0 ∧ βK q ^ n = fK.eval (αK q))
    (D : SupGoodData p φ fK n αK βK) (m : ℕ)
    (hm : PrincipalMulN (D.f.map ρp) n fK.natDegree (fun q ↦ ρp (D.α q)) (fun q ↦ ρp (D.β q)) mu m)
    {N : ℕ} (hN1 : 1 ≤ N) (hN : PrincipalMulN fK n fK.natDegree αK βK mu N) :
    PrincipalMulN fK n fK.natDegree αK βK mu (m * p ^ (N.factorization p)) := by
  have hϖ : Irreducible (p : ℤ_[p]) := PadicInt.irreducible_p
  have hιi : Function.Injective ιp := IsFractionRing.injective ℤ_[p] ℚ_[p]
  have hfdeg : D.f.natDegree = fK.natDegree := by
    rw [← natDegree_map_eq_of_injective hιi, ← D.hfmap,
      natDegree_map_eq_of_injective φ.injective]
  have hsqQ : Squarefree (D.f.map ιp) := by
    rw [← D.hfmap]
    exact ((PerfectField.separable_iff_squarefree.mpr hsqK).map).squarefree
  set a := N.factorization p
  set ℓ := N / p ^ a
  have hNℓ : p ^ a * ℓ = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr fun h ↦ by
    rw [h, mul_zero] at hNℓ; omega
  have hℓu : IsUnit (ℓ : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact Nat.coprime_ordCompl hp.out (Nat.one_le_iff_ne_zero.mp hN1)
  have e1 : (fun q ↦ φ (αK q)) = fun q ↦ ιp (D.α q) := funext D.hαmap
  have e2 : (fun q ↦ φ (βK q)) = fun q ↦ ιp (D.β q) := funext D.hβmap
  have hNp := hN.map φ
  rw [D.hfmap, e1, e2, ← hNℓ, ← hfdeg] at hNp
  have := principal_of_reduction_N hϖ D.f hn D.hlc (by rw [hfdeg]; exact hd)
    (by rw [hfdeg]; exact hcop) D.hsqk hsqQ D.hnu D.ζ D.hζ D.hζk D.hgen D.x D.y D.hyu D.hyf D.hx
    D.α D.β mu D.hβu D.hβf D.hα D.hβd D.hαx D.hNS hℓ1 hℓu hNp (by rw [hfdeg]; exact hm)
  rw [← e1, ← e2, ← D.hfmap, hfdeg] at this
  exact principalMulN_descend φ fK hn _ αK βK mu hΓK _ this

/-- **Torsion is decided by two primes.** -/
theorem torsion_iff_two_primes_N {q : ℕ} [hq : Fact q.Prime] (hpq : p ≠ q)
    {K : Type*} [Field K] [DecidableEq K] [PerfectField K]
    (φp : K →+* ℚ_[p]) (φq : K →+* ℚ_[q]) (fK : K[X]) {n : ℕ} (hn : 0 < n) (hsqK : Squarefree fK)
    (hd : 0 < fK.natDegree) (hcop : Nat.Coprime n fK.natDegree) (hnK : (n : K) ≠ 0) {r : ℕ}
    (αK βK : Fin r → K) (mu : Fin r → ℕ) (hPK : Function.Injective fun q ↦ (αK q, βK q))
    (hβK : ∀ i, βK i ≠ 0)
    (hΓK : ∀ q, (n : K) * βK q ^ (n - 1) ≠ 0 ∧ βK q ^ n = fK.eval (αK q))
    (Dp : SupGoodData p φp fK n αK βK) (Dq : SupGoodData q φq fK n αK βK)
    (mp : ℕ) (hmp1 : 1 ≤ mp)
    (hmp : PrincipalMulN (Dp.f.map (IsLocalRing.residue ℤ_[p])) n fK.natDegree
      (fun i ↦ IsLocalRing.residue ℤ_[p] (Dp.α i)) (fun i ↦ IsLocalRing.residue ℤ_[p] (Dp.β i)) mu mp)
    (mq : ℕ) (hmq1 : 1 ≤ mq)
    (hmq : PrincipalMulN (Dq.f.map (IsLocalRing.residue ℤ_[q])) n fK.natDegree
      (fun i ↦ IsLocalRing.residue ℤ_[q] (Dq.α i)) (fun i ↦ IsLocalRing.residue ℤ_[q] (Dq.β i)) mu mq) :
    (∃ N, 1 ≤ N ∧ PrincipalMulN fK n fK.natDegree αK βK mu N) ↔
      PrincipalMulN fK n fK.natDegree αK βK mu (mp * mq) := by
  constructor
  · rintro ⟨N, hN1, hN⟩
    have h1 := principal_at_prime_N φp fK hn hsqK hd hcop αK βK mu hΓK Dp mp hmp hN1 hN
    have h2 := principal_at_prime_N (p := q) φq fK hn hsqK hd hcop αK βK mu hΓK Dq mq hmq hN1 hN
    have hg := PrincipalMulN.gcd fK hn hsqK hd hcop hnK αK βK mu hPK hβK (fun i ↦ (hΓK i).2) h1 h2
    exact PrincipalMulN.of_dvd fK hn hsqK hd hcop hnK αK βK mu hPK hβK (fun i ↦ (hΓK i).2)
      (Jac.gcd_dvd_mul_of_two_primes hp.out hq.out hpq _ _ _ _) hg
  · intro h
    exact ⟨mp * mq, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), h⟩

end Padic

end Sup
