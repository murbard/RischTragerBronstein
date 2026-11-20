import RischTragerBronstein.Jacobian.AbelHyp

/-!
# Deciding torsion with two primes

Let `K` be a field (e.g. a number field) with embeddings into `ℚ_p` and `ℚ_q` (`p ≠ q` odd primes)
under which the curve and the divisor have good integral models (`principal_at_prime`'s
hypotheses). If `m_p D̄` is principal over the residue field at `p` and `m_q D̄` at `q`, then

* `principal_at_prime`: every torsion order `n` gives `(m_p · p^{v_p(n)}) D` principal over `K`;
* `torsion_iff_two_primes`: `D` is torsion **iff** `(m_p m_q) D` is principal over `K`.

The right-hand side is a finite linear-algebra question (`principalC`), so this decides torsion.
-/

open Polynomial

namespace Jac

/-- Principality is preserved by field embeddings. -/
lemma PrincipalMul.map {K S : Type*} [Field K] [Field S] (φ : K →+* S) {f : K[X]} {g : ℕ}
    {Γ : EDiv K} {n : ℕ} (h : PrincipalMul f g Γ n) : PrincipalMul (f.map φ) g (emap φ Γ) n := by
  obtain ⟨ψ, hψ0, hψp, hψv⟩ := h
  refine ⟨(ψ.1.map φ, ψ.2.map φ), ?_, ?_, ?_⟩
  · intro h
    apply hψ0
    exact Prod.ext (Polynomial.map_injective φ φ.injective (by simpa using congrArg Prod.fst h))
      (Polynomial.map_injective φ φ.injective (by simpa using congrArg Prod.snd h))
  · rw [edeg_emap]
    refine ⟨by simpa [natDegree_map_eq_of_injective φ.injective] using hψp.1, ?_⟩
    rcases hψp.2 with h | h
    · left; simp [h]
    · right; simpa [natDegree_map_eq_of_injective φ.injective] using h
  · rw [← emap_escale]; exact hψv.map

section Padic

variable {p : ℕ} [hp : Fact p.Prime]

local notation "ιp" => algebraMap ℤ_[p] ℚ_[p]
local notation "ρp" => IsLocalRing.residue ℤ_[p]

/-- **One prime.** -/
theorem principal_at_prime (hp2 : p ≠ 2) {K : Type*} [Field K] [DecidableEq K]
    (φ : K →+* ℚ_[p]) {g : ℕ} (fK : K[X]) (Γ : EDiv K)
    (hΓK : ∀ q ∈ Γ, 2 * q.2.1 ≠ 0 ∧ q.2.1 ^ 2 = fK.eval q.1)
    (fO : ℤ_[p][X]) (hf : fO.natDegree = 2 * g + 1) (hlc : IsUnit fO.leadingCoeff)
    (hfmap : fK.map φ = fO.map ιp)
    (x y : Fin g → ℤ_[p]) (hyu : ∀ i, IsUnit (y i)) (hyf : ∀ i, y i ^ 2 = fO.eval (x i))
    (hx : ∀ i j, i ≠ j → IsUnit (x i - x j))
    (ΓO : EDiv ℤ_[p]) (hmapΓ : emap φ Γ = emap ιp ΓO) (hon : OnCurve fO ΓO)
    (hΓx : ΓO.Pairwise fun q q' ↦ IsUnit (q.1 - q'.1)) (hΓE : ∀ q ∈ ΓO, ∀ i, IsUnit (q.1 - x i))
    (m : ℕ) (hm : PrincipalMul (fO.map ρp) g (emap ρp ΓO) m)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : PrincipalMul fK g Γ n) :
    PrincipalMul fK g Γ (m * p ^ (n.factorization p)) := by
  have hϖ : Irreducible (p : ℤ_[p]) := PadicInt.irreducible_p
  have h2 : IsUnit (2 : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    have := (PadicInt.norm_natCast_eq_one_iff (p := p) (n := 2)).mpr
      ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2)
    simpa using this
  set a := n.factorization p
  set ℓ := n / p ^ a
  have hnℓ : p ^ a * ℓ = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr fun h ↦ by
    rw [h, mul_zero] at hnℓ; omega
  have hℓu : IsUnit (ℓ : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact Nat.coprime_ordCompl hp.out (Nat.one_le_iff_ne_zero.mp hn1)
  have hnp := hn.map φ
  rw [hfmap, hmapΓ, ← hnℓ] at hnp
  have := principal_of_reduction hϖ h2 fO hf hlc x y hyu hyf hx ΓO hon hΓx hΓE hℓ1 hℓu hnp hm
  rw [← hfmap, ← hmapΓ] at this
  exact principalMul_descend φ fK g Γ hΓK _ this

/-- **Torsion is decided by two primes.** -/
theorem torsion_iff_two_primes {q : ℕ} [hq : Fact q.Prime] (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p ≠ q) {K : Type*} [Field K] [DecidableEq K]
    (φp : K →+* ℚ_[p]) (φq : K →+* ℚ_[q]) {g : ℕ} (fK : K[X]) (hfK : fK.natDegree = 2 * g + 1)
    (Γ : EDiv K) (hΓK : ∀ r ∈ Γ, 2 * r.2.1 ≠ 0 ∧ r.2.1 ^ 2 = fK.eval r.1)
    (hΓnd : (Γ.map Prod.fst).Nodup)
    -- integral data at `p`
    (fp : ℤ_[p][X]) (hfp : fp.natDegree = 2 * g + 1) (hlcp : IsUnit fp.leadingCoeff)
    (hfmapp : fK.map φp = fp.map ιp)
    (xp yp : Fin g → ℤ_[p]) (hyup : ∀ i, IsUnit (yp i)) (hyfp : ∀ i, yp i ^ 2 = fp.eval (xp i))
    (hxp : ∀ i j, i ≠ j → IsUnit (xp i - xp j))
    (Γp : EDiv ℤ_[p]) (hmapΓp : emap φp Γ = emap ιp Γp) (honp : OnCurve fp Γp)
    (hΓxp : Γp.Pairwise fun r r' ↦ IsUnit (r.1 - r'.1))
    (hΓEp : ∀ r ∈ Γp, ∀ i, IsUnit (r.1 - xp i))
    (mp : ℕ) (hmp1 : 1 ≤ mp) (hmp : PrincipalMul (fp.map (IsLocalRing.residue ℤ_[p])) g
      (emap (IsLocalRing.residue ℤ_[p]) Γp) mp)
    -- integral data at `q`
    (fq : ℤ_[q][X]) (hfq : fq.natDegree = 2 * g + 1) (hlcq : IsUnit fq.leadingCoeff)
    (hfmapq : fK.map φq = fq.map (algebraMap ℤ_[q] ℚ_[q]))
    (xq yq : Fin g → ℤ_[q]) (hyuq : ∀ i, IsUnit (yq i)) (hyfq : ∀ i, yq i ^ 2 = fq.eval (xq i))
    (hxq : ∀ i j, i ≠ j → IsUnit (xq i - xq j))
    (Γq : EDiv ℤ_[q]) (hmapΓq : emap φq Γ = emap (algebraMap ℤ_[q] ℚ_[q]) Γq)
    (honq : OnCurve fq Γq) (hΓxq : Γq.Pairwise fun r r' ↦ IsUnit (r.1 - r'.1))
    (hΓEq : ∀ r ∈ Γq, ∀ i, IsUnit (r.1 - xq i))
    (mq : ℕ) (hmq1 : 1 ≤ mq) (hmq : PrincipalMul (fq.map (IsLocalRing.residue ℤ_[q])) g
      (emap (IsLocalRing.residue ℤ_[q]) Γq) mq) :
    (∃ n, 1 ≤ n ∧ PrincipalMul fK g Γ n) ↔ PrincipalMul fK g Γ (mp * mq) := by
  have honK : OnCurve fK Γ := fun r hr ↦ ⟨IsUnit.mk0 _ (hΓK r hr).1, (hΓK r hr).2⟩
  constructor
  · rintro ⟨n, hn1, hn⟩
    have h1 := principal_at_prime hp2 φp fK Γ hΓK fp hfp hlcp hfmapp xp yp hyup hyfp hxp Γp
      hmapΓp honp hΓxp hΓEp mp hmp hn1 hn
    have h2 := principal_at_prime (p := q) hq2 φq fK Γ hΓK fq hfq hlcq hfmapq xq yq hyuq hyfq hxq
      Γq hmapΓq honq hΓxq hΓEq mq hmq hn1 hn
    have hg := PrincipalMul.gcd hfK honK hΓnd h1 h2
    exact hg.of_dvd hfK honK (gcd_dvd_mul_of_two_primes hp.out hq.out hpq _ _ _ _)
  · intro h
    exact ⟨mp * mq, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), h⟩

end Padic

end Jac
