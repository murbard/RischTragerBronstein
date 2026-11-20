import RischTragerBronstein.Algebraic.SupRed

/-!
# The order of a reduced divisor and the torsion decision over `K`

`orderModR`: the least `m ≥ 1` with `m Γ̄` principal over `𝔽_p` (it exists by finiteness of
`Pic⁰`). `torsDecideR_iff`: with two good primes, `Γ` is torsion iff `(m_p m_q) Γ` is principal,
which `supPrincipalC` tests.
-/

open Polynomial CPoly CPoly.Kron

namespace Sup

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [DecidableEq K]

/-- The test "`m Γ̄` is principal" over `𝔽_p`. -/
def prinTestR (R : RedFns p K) (fK : CPoly K) (n : ℕ) {r : ℕ} (α β : Fin r → K) (mq : Fin r → ℕ)
    (m : ℕ) : Bool :=
  (supPrincipalC (fK.map R.red) n (fK.length - 1)
    (gammaL (fun q ↦ R.red (α q)) (fun q ↦ R.red (β q)) mq m) (m * ∑ q, mq q)).isSome

/-- The facts modulo `p` behind `supCheckR`. -/
lemma zmod_factsR (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ) {fK : CPoly K}
    {n g r : ℕ} {α β : Fin r → K} {xs ys : List (ZMod p)} {ζ0 : ZMod p}
    {lam : List (List (ZMod p))} (hg : supCheckR p R fK n g α β xs ys ζ0 lam) :
    (CPoly.toPoly (fK.map R.red)).natDegree = fK.length - 1 ∧
    Squarefree (CPoly.toPoly (fK.map R.red)) ∧ ((n : ℕ) : ZMod p) ≠ 0 ∧
    Function.Injective (fun q ↦ (R.red (α q), R.red (β q))) ∧ (∀ q, R.red (β q) ≠ 0) ∧
    (∀ q, R.red (β q) ^ n = (CPoly.toPoly (fK.map R.red)).eval (R.red (α q))) := by
  obtain ⟨D, hDf, hDα, hDβ⟩ := supCheckR_spec R φ hR hg
  have H := hg
  obtain ⟨hn2, hnp, hd, hok, hlc, -, hsq, -, -, -, -, -, -, hΓ, hΓd, hΓβ, -⟩ := H
  refine ⟨?_, CPoly.squarefreeCheck_sound hsq, hnp, ?_, fun q ↦ (hΓ q).2.2.1, fun q ↦ ?_⟩
  · have hlc0 : (CPoly.toPoly (fK.map R.red)).coeff (fK.length - 1) ≠ 0 := by
      rw [CPoly.coeff_toPoly, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
        ← List.getD_eq_getElem _ 0]; exact hlc
    refine le_antisymm ?_ (le_natDegree_of_ne_zero hlc0)
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    have hm' : fK.length - 1 < m := by exact_mod_cast hm
    rw [CPoly.coeff_toPoly, List.getD_eq_default _ _ (by simp; omega)]
  · intro q q' h
    have h1 : R.red (α q) = R.red (α q') := congrArg Prod.fst h
    have h2 : R.red (β q) = R.red (β q') := congrArg Prod.snd h
    have hαe : α q = α q' := (hΓd q q').resolve_right (not_not.mpr h1)
    by_contra hne
    exact hΓβ q q' hne hαe h2
  · have := congrArg PadicInt.toZMod (D.hβf q)
    rw [map_pow, hDβ, toZMod_eval, hDf, hDα] at this
    exact this

lemma exists_orderR (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ) {fK : CPoly K}
    {n g r : ℕ} {α β : Fin r → K} (mq : Fin r → ℕ) {xs ys : List (ZMod p)} {ζ0 : ZMod p}
    {lam : List (List (ZMod p))} (hg : supCheckR p R fK n g α β xs ys ζ0 lam)
    (hcop : Nat.Coprime n (fK.length - 1)) : ∃ m, 1 ≤ m ∧ prinTestR R fK n α β mq m = true := by
  obtain ⟨hdeg, hsq, hnk, hαk, hβk, hβf⟩ := zmod_factsR R φ hR hg
  have hn2 : 2 ≤ n := hg.1
  have hn : 0 < n := by omega
  obtain ⟨m, hm1, hm⟩ := exists_principalMulN (CPoly.toPoly (fK.map R.red)) hn hsq
    (by rw [hdeg]; exact hg.2.2.1) (by rw [hdeg]; exact hcop) hnk _ _ mq hn2 hαk hβk hβf
  refine ⟨m, hm1, ?_⟩
  rw [hdeg] at hm
  exact (principalMulN_iff_test (fK.map R.red) hn _ _ _ mq
    (fun q ↦ ⟨mul_ne_zero hnk (pow_ne_zero _ (hβk q)), hβf q⟩) m).mp hm

/-- The order search, bounded (for computation). -/
def orderSearchR (R : RedFns p K) (fK : CPoly K) (n : ℕ) {r : ℕ} (α β : Fin r → K)
    (mq : Fin r → ℕ) (bound : ℕ) : Option ℕ :=
  ((List.range bound).find? fun m ↦ prinTestR R fK n α β mq (m + 1)).map (· + 1)

/-- Transfer of principality modulo `p` to the residue field of `ℤ_p`. -/
lemma principal_residue (R : RedFns p K) (φ : K →+* ℚ_[p]) {fK : CPoly K} {n : ℕ} {r : ℕ}
    {α β : Fin r → K} (D : SupGoodData p φ (CPoly.toPoly fK) n α β)
    (hDf : D.f.map PadicInt.toZMod = CPoly.toPoly (fK.map R.red))
    (hDα : ∀ q, PadicInt.toZMod (D.α q) = R.red (α q))
    (hDβ : ∀ q, PadicInt.toZMod (D.β q) = R.red (β q)) (mq : Fin r → ℕ) {d m : ℕ}
    (h : PrincipalMulN (CPoly.toPoly (fK.map R.red)) n d (fun q ↦ R.red (α q))
      (fun q ↦ R.red (β q)) mq m) :
    PrincipalMulN (D.f.map (IsLocalRing.residue ℤ_[p])) n d
      (fun i ↦ IsLocalRing.residue ℤ_[p] (D.α i)) (fun i ↦ IsLocalRing.residue ℤ_[p] (D.β i))
      mq m := by
  have hP' := h.map (PadicInt.residueField (p := p)).symm.toRingHom
  have e0 : ∀ z : ℤ_[p], (PadicInt.residueField (p := p)).symm.toRingHom (PadicInt.toZMod z) =
      IsLocalRing.residue ℤ_[p] z := fun z ↦ by
    rw [PadicInt.toZMod_eq_residueField_comp_residue]
    simp
  have e1 : (CPoly.toPoly (fK.map R.red)).map (PadicInt.residueField (p := p)).symm.toRingHom =
      D.f.map (IsLocalRing.residue ℤ_[p]) := by
    rw [← hDf, Polynomial.map_map]
    congr 1
    ext z
    exact e0 z
  rw [e1] at hP'
  simp only [← hDα, ← hDβ, e0] at hP'
  exact hP'

lemma orderSearchR_spec (R : RedFns p K) (fK : CPoly K) (n : ℕ) {r : ℕ} (α β : Fin r → K)
    (mq : Fin r → ℕ) (bound : ℕ) {m : ℕ} (h : orderSearchR R fK n α β mq bound = some m) :
    1 ≤ m ∧ prinTestR R fK n α β mq m = true := by
  unfold orderSearchR at h
  obtain ⟨m0, hm0, rfl⟩ := Option.map_eq_some_iff.mp h
  have := List.find?_some hm0
  exact ⟨by omega, this⟩

/-- The degree of the curve, from the check. -/
lemma natDegree_of_checkR (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ)
    {fK : CPoly K} {n g r : ℕ} {α β : Fin r → K} {xs ys : List (ZMod p)} {ζ0 : ZMod p}
    {lam : List (List (ZMod p))} (hg : supCheckR p R fK n g α β xs ys ζ0 lam) :
    (CPoly.toPoly fK).natDegree = fK.length - 1 := by
  obtain ⟨-, -, hd, hok, hlc, -⟩ := hg
  have hlm : fK.length - 1 < fK.length := by omega
  have hne : fK.getD (fK.length - 1) 0 ≠ 0 := by
    intro h0
    have hmem : fK.getD (fK.length - 1) 0 ∈ fK := by
      rw [List.getD_eq_getElem _ _ hlm]; exact List.getElem_mem hlm
    obtain ⟨z, hz, hzr⟩ := hR _ (hok _ hmem)
    rw [h0, map_zero] at hz
    have hz0 : z = 0 := (IsFractionRing.injective ℤ_[p] ℚ_[p]) (by rw [← hz, map_zero])
    apply hlc
    rw [← hzr, hz0, map_zero]
  refine le_antisymm ?_ (le_natDegree_of_ne_zero (by rw [CPoly.coeff_toPoly]; exact hne))
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  have hm' : fK.length - 1 < m := by exact_mod_cast hm
  rw [CPoly.coeff_toPoly, List.getD_eq_default _ _ (by omega)]

lemma factorization_mul_pow_other {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ ≠ p) (m a : ℕ) (hm : m ≠ 0) :
    (m * p ^ a).factorization ℓ = m.factorization ℓ := by
  rw [Nat.factorization_mul hm (pow_ne_zero _ hp.ne_zero), Nat.factorization_pow,
    hp.factorization]
  simp [Finsupp.single_apply, Ne.symm hℓ]

lemma gcd_dvd_gcd_pow_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {mp mq : ℕ}
    (hmp : mp ≠ 0) (hmq : mq ≠ 0) (a b : ℕ) :
    Nat.gcd (mp * p ^ a) (mq * q ^ b) ∣ mp * p ^ (mp + mq) := by
  have hG0 : Nat.gcd (mp * p ^ a) (mq * q ^ b) ≠ 0 :=
    Nat.gcd_ne_zero_left (Nat.mul_ne_zero hmp (pow_ne_zero _ hp.ne_zero))
  rw [← Nat.factorization_le_iff_dvd hG0 (Nat.mul_ne_zero hmp (pow_ne_zero _ hp.ne_zero))]
  intro ℓ
  by_cases hℓ : ℓ = p
  · subst hℓ
    have h1 := (Nat.factorization_le_iff_dvd hG0 (Nat.mul_ne_zero hmq (pow_ne_zero _ hq.ne_zero))).mpr
      (Nat.gcd_dvd_right _ _) ℓ
    rw [factorization_mul_pow_other hq hpq mq b hmq] at h1
    have h2 := Nat.factorization_lt ℓ hmq
    rw [Nat.factorization_mul hmp (pow_ne_zero _ hp.ne_zero), Nat.factorization_pow,
      hp.factorization]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
    omega
  · have h1 := (Nat.factorization_le_iff_dvd hG0 (Nat.mul_ne_zero hmp (pow_ne_zero _ hp.ne_zero))).mpr
      (Nat.gcd_dvd_left _ _) ℓ
    rw [factorization_mul_pow_other hp hℓ mp a hmp] at h1
    rw [factorization_mul_pow_other hp hℓ mp _ hmp]
    exact h1

lemma gcd_dvd_gcd_pow {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {mp mq : ℕ}
    (hmp : mp ≠ 0) (hmq : mq ≠ 0) (a b : ℕ) :
    Nat.gcd (mp * p ^ a) (mq * q ^ b) ∣
      Nat.gcd (mp * p ^ (mp + mq)) (mq * q ^ (mp + mq)) := by
  refine Nat.dvd_gcd (gcd_dvd_gcd_pow_one hp hq hpq hmp hmq a b) ?_
  rw [Nat.gcd_comm]
  have := gcd_dvd_gcd_pow_one hq hp (Ne.symm hpq) hmq hmp b a
  rwa [add_comm mq mp] at this

/-- **The torsion decision** over `K` at two primes. -/
def torsDecideR {q : ℕ} [Fact q.Prime] (Rp : RedFns p K) (Rq : RedFns q K) (fK : CPoly K) (n : ℕ) {r : ℕ}
    (α β : Fin r → K) (mu : Fin r → ℕ) (bound : ℕ) : Option (Option ℕ) :=
  match orderSearchR Rp fK n α β mu bound, orderSearchR Rq fK n α β mu bound with
  | some mp, some mq =>
    let t := Nat.gcd (mp * p ^ (mp + mq)) (mq * q ^ (mp + mq))
    if (supPrincipalC fK n (fK.length - 1) (gammaL α β mu t) (t * ∑ i, mu i)).isSome then
      some (some t) else some none
  | _, _ => none

set_option maxHeartbeats 1600000 in
/-- **Correctness of the torsion decision** over `K`. -/
theorem torsDecideR_spec [CharZero K] {q : ℕ} [hq : Fact q.Prime] (hpq : p ≠ q)
    (Rp : RedFns p K) (φp : K →+* ℚ_[p]) (hRp : RedValid p Rp φp)
    (Rq : RedFns q K) (φq : K →+* ℚ_[q]) (hRq : RedValid q Rq φq)
    {fK : CPoly K} {n : ℕ} (hsqK : Squarefree (CPoly.toPoly fK))
    (hcop : Nat.Coprime n (fK.length - 1)) {r : ℕ} {α β : Fin r → K} (mu : Fin r → ℕ)
    (hP : Function.Injective fun i ↦ (α i, β i))
    (hv : ∀ i, β i ≠ 0 ∧ β i ^ n = (CPoly.toPoly fK).eval (α i)) (bound : ℕ)
    {gp : ℕ} {xsp ysp : List (ZMod p)} {ζp : ZMod p} {lamp : List (List (ZMod p))}
    (hgp : supCheckR p Rp fK n gp α β xsp ysp ζp lamp)
    {gq : ℕ} {xsq ysq : List (ZMod q)} {ζq : ZMod q} {lamq : List (List (ZMod q))}
    (hgq : supCheckR q Rq fK n gq α β xsq ysq ζq lamq) :
    (∀ N, torsDecideR Rp Rq fK n α β mu bound = some (some N) →
      1 ≤ N ∧ PrincipalMulN (CPoly.toPoly fK) n (fK.length - 1) α β mu N) ∧
    (torsDecideR Rp Rq fK n α β mu bound = some none →
      ∀ N, 1 ≤ N → ¬ PrincipalMulN (CPoly.toPoly fK) n (fK.length - 1) α β mu N) := by
  have hn2 : 2 ≤ n := hgp.1
  have hn : 0 < n := by omega
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hΓK : ∀ i, (n : K) * β i ^ (n - 1) ≠ 0 ∧ β i ^ n = (CPoly.toPoly fK).eval (α i) :=
    fun i ↦ ⟨mul_ne_zero hnK (pow_ne_zero _ (hv i).1), (hv i).2⟩
  have hdeg := natDegree_of_checkR Rp φp hRp hgp
  unfold torsDecideR
  split
  · rename_i mp mq hmp hmq
    obtain ⟨hmp1, hmpt⟩ := orderSearchR_spec Rp fK n α β mu bound hmp
    obtain ⟨hmq1, hmqt⟩ := orderSearchR_spec Rq fK n α β mu bound hmq
    have hpq' : Nat.Prime p := hp.out
    have ht0 : Nat.gcd (mp * p ^ (mp + mq)) (mq * q ^ (mp + mq)) ≠ 0 :=
      Nat.gcd_ne_zero_left (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hpq'.ne_zero))
    simp only []
    split_ifs with htest
    · refine ⟨fun N hN ↦ ?_, fun h ↦ (by cases h)⟩
      simp only [Option.some.injEq] at hN
      subst hN
      exact ⟨Nat.one_le_iff_ne_zero.mpr ht0,
        (principalMulN_iff_test fK hn _ α β mu hΓK _).mpr htest⟩
    · refine ⟨fun N hN ↦ (by cases hN), fun _ N hN1 hPN ↦ htest ?_⟩
      -- the reductions
      obtain ⟨Dp, hDpf, hDpα, hDpβ⟩ := supCheckR_spec Rp φp hRp hgp
      obtain ⟨Dq, hDqf, hDqα, hDqβ⟩ := supCheckR_spec Rq φq hRq hgq
      obtain ⟨-, -, hnkp, -, hβkp, hβfp⟩ := zmod_factsR Rp φp hRp hgp
      obtain ⟨-, -, hnkq, -, hβkq, hβfq⟩ := zmod_factsR Rq φq hRq hgq
      have hPp := (principalMulN_iff_test (fK.map Rp.red) hn _ _ _ mu
        (fun i ↦ ⟨mul_ne_zero hnkp (pow_ne_zero _ (hβkp i)), hβfp i⟩) mp).mpr hmpt
      have hPq := (principalMulN_iff_test (fK.map Rq.red) hn _ _ _ mu
        (fun i ↦ ⟨mul_ne_zero hnkq (pow_ne_zero _ (hβkq i)), hβfq i⟩) mq).mpr hmqt
      have hRp' := principal_residue Rp φp Dp hDpf hDpα hDpβ mu hPp
      have hRq' := principal_residue Rq φq Dq hDqf hDqα hDqβ mu hPq
      rw [← hdeg] at hRp' hRq' hPN
      have hd0 : 0 < (CPoly.toPoly fK).natDegree := by rw [hdeg]; exact hgp.2.2.1
      have hcop' : Nat.Coprime n (CPoly.toPoly fK).natDegree := by rw [hdeg]; exact hcop
      have h1 := principal_at_prime_N φp (CPoly.toPoly fK) hn hsqK hd0 hcop' α β mu hΓK Dp mp hRp'
        hN1 hPN
      have h2 := principal_at_prime_N (p := q) φq (CPoly.toPoly fK) hn hsqK hd0 hcop' α β mu hΓK Dq
        mq hRq' hN1 hPN
      have hg := PrincipalMulN.gcd (CPoly.toPoly fK) hn hsqK hd0 hcop' hnK α β mu hP
        (fun i ↦ (hv i).1) (fun i ↦ (hv i).2) h1 h2
      have hmain := PrincipalMulN.of_dvd (CPoly.toPoly fK) hn hsqK hd0 hcop' hnK α β mu hP
        (fun i ↦ (hv i).1) (fun i ↦ (hv i).2)
        (gcd_dvd_gcd_pow hpq' hq.out hpq (by omega) (by omega) _ _) hg
      rw [hdeg] at hmain
      exact (principalMulN_iff_test fK hn _ α β mu hΓK _).mp hmain
  · exact ⟨fun N hN ↦ (by cases hN), fun h ↦ (by cases h)⟩

end Sup
