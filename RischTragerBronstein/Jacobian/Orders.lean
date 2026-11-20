import RischTragerBronstein.Jacobian.TwoPrimes

/-!
# Non-torsion from the exact orders at two primes

`principal_reduce`: a principal multiple over `K = Frac O` stays principal modulo `ϖ`.

`order_eq_of_torsion`: if `D` is torsion, of exact order `o`, and `m_p` is the exact order of `D̄`
modulo `p`, then `o = m_p · pᶜ` for some `c`. Hence (`not_torsion_of_orders`) if the exact orders
`m_p`, `m_q` at two primes admit no `c, d` with `m_p pᶜ = m_q qᵈ`, then `D` is not torsion — a
certificate checked by finite computations over `𝔽_p` and `𝔽_q` only.
-/

open Polynomial

namespace Jac

section Reduce

variable {O K : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]

/-- **Principality survives reduction.** -/
theorem principal_reduce {ϖ : O} (hϖ : Irreducible ϖ) {g : ℕ} (f : O[X]) (Γ : EDiv O)
    (hon : OnCurve f Γ) {n : ℕ} (h : PrincipalMul (f.map (algebraMap O K)) g
      (emap (algebraMap O K) Γ) n) :
    PrincipalMul (f.map (IsLocalRing.residue O)) g (emap (IsLocalRing.residue O) Γ) n := by
  obtain ⟨ψ, hψ0, hψp, hψv⟩ := h
  rw [edeg_emap] at hψp
  obtain ⟨ψ₁, hprim, hp1, hv1, -⟩ := descend hϖ (OnCurve.escale' hon) (g := g) hψ0 hψp
    (by rw [emap_escale]; exact hψv)
  refine ⟨(ψ₁.1.map (IsLocalRing.residue O), ψ₁.2.map (IsLocalRing.residue O)), ?_, ?_, ?_⟩
  · intro h
    apply hprim
    exact ⟨(C_dvd_iff_map hϖ _).mpr (congrArg Prod.fst h),
      (C_dvd_iff_map hϖ _).mpr (congrArg Prod.snd h)⟩
  · rw [edeg_emap]
    refine ⟨(Nat.mul_le_mul_left 2 natDegree_map_le).trans hp1.1, ?_⟩
    rcases hp1.2 with h | h
    · left; simp [h]
    · right
      exact (Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.mul_le_mul_left 2 natDegree_map_le) _) _).trans h
  · rw [← emap_escale]; exact hv1.map

end Reduce

section Padic

variable {p : ℕ} [hp : Fact p.Prime]

local notation "ιp" => algebraMap ℤ_[p] ℚ_[p]
local notation "ρp" => IsLocalRing.residue ℤ_[p]

/-- **The exact order is `m_p` times a power of `p`.** -/
theorem order_at_prime (hp2 : p ≠ 2) {K : Type*} [Field K] [DecidableEq K]
    (φ : K →+* ℚ_[p]) {g : ℕ} (fK : K[X]) (hfK : fK.natDegree = 2 * g + 1) (Γ : EDiv K)
    (hΓK : ∀ q ∈ Γ, 2 * q.2.1 ≠ 0 ∧ q.2.1 ^ 2 = fK.eval q.1) (hΓnd : (Γ.map Prod.fst).Nodup)
    (fO : ℤ_[p][X]) (hf : fO.natDegree = 2 * g + 1) (hlc : IsUnit fO.leadingCoeff)
    (hfmap : fK.map φ = fO.map ιp)
    (x y : Fin g → ℤ_[p]) (hyu : ∀ i, IsUnit (y i)) (hyf : ∀ i, y i ^ 2 = fO.eval (x i))
    (hx : ∀ i j, i ≠ j → IsUnit (x i - x j))
    (ΓO : EDiv ℤ_[p]) (hmapΓ : emap φ Γ = emap ιp ΓO) (hon : OnCurve fO ΓO)
    (hΓx : ΓO.Pairwise fun q q' ↦ IsUnit (q.1 - q'.1)) (hΓE : ∀ q ∈ ΓO, ∀ i, IsUnit (q.1 - x i))
    (m : ℕ) (hm1 : 1 ≤ m) (hm : PrincipalMul (fO.map ρp) g (emap ρp ΓO) m)
    (hmin : ∀ m', 1 ≤ m' → m' < m → ¬ PrincipalMul (fO.map ρp) g (emap ρp ΓO) m')
    {o : ℕ} (ho1 : 1 ≤ o) (ho : PrincipalMul fK g Γ o)
    (homin : ∀ n, 1 ≤ n → n < o → ¬ PrincipalMul fK g Γ n) : ∃ c, o = m * p ^ c := by
  have hϖ : Irreducible (p : ℤ_[p]) := PadicInt.irreducible_p
  have honK : OnCurve fK Γ := fun r hr ↦ ⟨IsUnit.mk0 _ (hΓK r hr).1, (hΓK r hr).2⟩
  have hfk : (fO.map ρp).natDegree = 2 * g + 1 := by
    rw [natDegree_map_of_leadingCoeff_ne_zero _ ((hlc.map ρp).ne_zero), hf]
  have honk : OnCurve (fO.map ρp) (emap ρp ΓO) := OnCurve.map hon
  have hndk : ((emap ρp ΓO).map Prod.fst).Nodup := by
    have := nodup_map_of_pairwise_unit ρp ΓO hΓx
    simpa [emap, Function.comp_def] using this
  -- `m ∣ o`
  have hok : PrincipalMul (fO.map ρp) g (emap ρp ΓO) o := by
    have h1 := ho.map φ
    rw [hfmap, hmapΓ] at h1
    exact principal_reduce hϖ fO ΓO hon h1
  have hmo : m ∣ o := by
    have hg := PrincipalMul.gcd hfk honk hndk hok hm
    have hg1 : 1 ≤ Nat.gcd o m := Nat.gcd_pos_of_pos_left _ ho1
    have hgle : Nat.gcd o m ≤ m := Nat.gcd_le_right _ hm1
    by_contra hnd
    have hlt : Nat.gcd o m < m := lt_of_le_of_ne hgle fun h ↦ hnd (h ▸ Nat.gcd_dvd_left o m)
    exact hmin _ hg1 hlt hg
  -- `o ∣ m pᵃ`
  have hat := principal_at_prime hp2 φ fK Γ hΓK fO hf hlc hfmap x y hyu hyf hx ΓO hmapΓ hon hΓx
    hΓE m hm ho1 ho
  have hodvd : o ∣ m * p ^ (o.factorization p) := by
    set M := m * p ^ (o.factorization p) with hMdef
    have hg := PrincipalMul.gcd hfK honK hΓnd ho hat
    have hg1 : 1 ≤ Nat.gcd o M := Nat.gcd_pos_of_pos_left _ ho1
    have hgle : Nat.gcd o M ≤ o := Nat.gcd_le_left _ ho1
    by_contra hnd
    have hlt : Nat.gcd o M < o := lt_of_le_of_ne hgle fun h ↦ hnd (h ▸ Nat.gcd_dvd_right o M)
    exact homin _ hg1 hlt hg
  obtain ⟨k, rfl⟩ := hmo
  have hk : k ∣ p ^ ((m * k).factorization p) :=
    (Nat.mul_dvd_mul_iff_left (by omega)).mp hodvd
  obtain ⟨c, -, rfl⟩ := (Nat.dvd_prime_pow hp.out).mp hk
  exact ⟨c, rfl⟩

/-- Transport from `ZMod p` to the residue field of `ℤ_p`. -/
lemma principal_residue_of_zmod {g : ℕ} (fO : ℤ_[p][X]) (ΓO : EDiv ℤ_[p]) {m : ℕ}
    (h : PrincipalMul (fO.map (PadicInt.toZMod (p := p))) g (emap PadicInt.toZMod ΓO) m) :
    PrincipalMul (fO.map ρp) g (emap ρp ΓO) m := by
  have e1 : (fO.map (PadicInt.toZMod (p := p))).map (PadicInt.residueField (p := p)).symm.toRingHom
      = fO.map ρp := by
    rw [Polynomial.map_map, PadicInt.toZMod_eq_residueField_comp_residue, ← RingHom.comp_assoc]
    simp
  have e2 : emap (PadicInt.residueField (p := p)).symm.toRingHom (emap PadicInt.toZMod ΓO) =
      emap ρp ΓO := by
    simp [emap, Function.comp_def, PadicInt.toZMod_eq_residueField_comp_residue]
  have := h.map (PadicInt.residueField (p := p)).symm.toRingHom
  rwa [e1, e2] at this

lemma principal_zmod_of_residue {g : ℕ} (fO : ℤ_[p][X]) (ΓO : EDiv ℤ_[p]) {m : ℕ}
    (h : PrincipalMul (fO.map ρp) g (emap ρp ΓO) m) :
    PrincipalMul (fO.map (PadicInt.toZMod (p := p))) g (emap PadicInt.toZMod ΓO) m := by
  have e1 : (fO.map ρp).map (PadicInt.residueField (p := p)).toRingHom =
      fO.map (PadicInt.toZMod (p := p)) := by
    rw [Polynomial.map_map, PadicInt.toZMod_eq_residueField_comp_residue]
  have e2 : emap (PadicInt.residueField (p := p)).toRingHom (emap ρp ΓO) =
      emap PadicInt.toZMod ΓO := by
    simp [emap, Function.comp_def, PadicInt.toZMod_eq_residueField_comp_residue]
  have := h.map (PadicInt.residueField (p := p)).toRingHom
  rwa [e1, e2] at this

end Padic

/-- A prime-power certificate that `m pᶜ = m' qᵈ` is impossible. -/
lemma ne_of_prime_pow_left {p q r k m m' : ℕ} (hq : q.Prime) (hr : r.Prime) (hrq : r ≠ q)
    (h1 : r ^ k ∣ m) (h2 : ¬ r ^ k ∣ m') : ∀ c d, m * p ^ c ≠ m' * q ^ d := by
  intro c d he
  apply h2
  have : r ^ k ∣ m' * q ^ d := he ▸ Dvd.dvd.mul_right h1 _
  exact (Nat.Coprime.pow _ _ ((Nat.coprime_primes hr hq).mpr hrq)).dvd_of_dvd_mul_right this

lemma ne_of_prime_pow_right {p q r k m m' : ℕ} (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p)
    (h1 : r ^ k ∣ m') (h2 : ¬ r ^ k ∣ m) : ∀ c d, m * p ^ c ≠ m' * q ^ d := by
  intro c d he
  apply h2
  have : r ^ k ∣ m * p ^ c := he ▸ Dvd.dvd.mul_right h1 _
  exact (Nat.Coprime.pow _ _ ((Nat.coprime_primes hr hp).mpr hrp)).dvd_of_dvd_mul_right this

section Two

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

/-- **Non-torsion from incompatible exact orders at two primes.** -/
theorem not_torsion_of_orders (hp2 : p ≠ 2) (hq2 : q ≠ 2) {K : Type*} [Field K] [DecidableEq K]
    (φp : K →+* ℚ_[p]) (φq : K →+* ℚ_[q]) {g : ℕ} (fK : K[X]) (hfK : fK.natDegree = 2 * g + 1)
    (Γ : EDiv K) (hΓK : ∀ r ∈ Γ, 2 * r.2.1 ≠ 0 ∧ r.2.1 ^ 2 = fK.eval r.1)
    (hΓnd : (Γ.map Prod.fst).Nodup)
    (fp : ℤ_[p][X]) (hfp : fp.natDegree = 2 * g + 1) (hlcp : IsUnit fp.leadingCoeff)
    (hfmapp : fK.map φp = fp.map (algebraMap ℤ_[p] ℚ_[p]))
    (xp yp : Fin g → ℤ_[p]) (hyup : ∀ i, IsUnit (yp i)) (hyfp : ∀ i, yp i ^ 2 = fp.eval (xp i))
    (hxp : ∀ i j, i ≠ j → IsUnit (xp i - xp j))
    (Γp : EDiv ℤ_[p]) (hmapΓp : emap φp Γ = emap (algebraMap ℤ_[p] ℚ_[p]) Γp)
    (honp : OnCurve fp Γp) (hΓxp : Γp.Pairwise fun r r' ↦ IsUnit (r.1 - r'.1))
    (hΓEp : ∀ r ∈ Γp, ∀ i, IsUnit (r.1 - xp i))
    (mp : ℕ) (hmp1 : 1 ≤ mp)
    (hmp : PrincipalMul (fp.map (IsLocalRing.residue ℤ_[p])) g
      (emap (IsLocalRing.residue ℤ_[p]) Γp) mp)
    (hmpmin : ∀ m', 1 ≤ m' → m' < mp → ¬ PrincipalMul (fp.map (IsLocalRing.residue ℤ_[p])) g
      (emap (IsLocalRing.residue ℤ_[p]) Γp) m')
    (fq : ℤ_[q][X]) (hfq : fq.natDegree = 2 * g + 1) (hlcq : IsUnit fq.leadingCoeff)
    (hfmapq : fK.map φq = fq.map (algebraMap ℤ_[q] ℚ_[q]))
    (xq yq : Fin g → ℤ_[q]) (hyuq : ∀ i, IsUnit (yq i)) (hyfq : ∀ i, yq i ^ 2 = fq.eval (xq i))
    (hxq : ∀ i j, i ≠ j → IsUnit (xq i - xq j))
    (Γq : EDiv ℤ_[q]) (hmapΓq : emap φq Γ = emap (algebraMap ℤ_[q] ℚ_[q]) Γq)
    (honq : OnCurve fq Γq) (hΓxq : Γq.Pairwise fun r r' ↦ IsUnit (r.1 - r'.1))
    (hΓEq : ∀ r ∈ Γq, ∀ i, IsUnit (r.1 - xq i))
    (mq : ℕ) (hmq1 : 1 ≤ mq)
    (hmq : PrincipalMul (fq.map (IsLocalRing.residue ℤ_[q])) g
      (emap (IsLocalRing.residue ℤ_[q]) Γq) mq)
    (hmqmin : ∀ m', 1 ≤ m' → m' < mq → ¬ PrincipalMul (fq.map (IsLocalRing.residue ℤ_[q])) g
      (emap (IsLocalRing.residue ℤ_[q]) Γq) m')
    (hinc : ∀ c d, mp * p ^ c ≠ mq * q ^ d) :
    ∀ n, 1 ≤ n → ¬ PrincipalMul fK g Γ n := by
  classical
  intro n hn1 hn
  have hex : ∃ o, 1 ≤ o ∧ PrincipalMul fK g Γ o := ⟨n, hn1, hn⟩
  set o := Nat.find hex
  obtain ⟨ho1, ho⟩ := Nat.find_spec hex
  have homin : ∀ n', 1 ≤ n' → n' < o → ¬ PrincipalMul fK g Γ n' := fun n' h1 h2 h3 ↦
    Nat.find_min hex h2 ⟨h1, h3⟩
  obtain ⟨c, hc⟩ := order_at_prime hp2 φp fK hfK Γ hΓK hΓnd fp hfp hlcp hfmapp xp yp hyup hyfp
    hxp Γp hmapΓp honp hΓxp hΓEp mp hmp1 hmp hmpmin ho1 ho homin
  obtain ⟨d, hd⟩ := order_at_prime (p := q) hq2 φq fK hfK Γ hΓK hΓnd fq hfq hlcq hfmapq xq yq
    hyuq hyfq hxq Γq hmapΓq honq hΓxq hΓEq mq hmq1 hmq hmqmin ho1 ho homin
  exact hinc c d (hc.symm.trans hd)

end Two

end Jac
