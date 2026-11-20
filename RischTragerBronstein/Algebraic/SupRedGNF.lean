import RischTragerBronstein.Algebraic.SupRedG
import RischTragerBronstein.Jacobian.GoodPrimesKF

/-!
# Good primes for global certificates over a number field

`exists_simple_root_prime`: for `M = mZ` (over `ℤ`) irreducible, there are primes `p > T` at which
`mZ` has a simple root modulo `p` (Schur's theorem, and the resultant of `mZ` and `mZ′`).
`pInt_of_den`: an element of `NF M` is `p`-integral for `p` above the sum of its denominators.
-/

open Polynomial CPoly CPoly.Kron

namespace Sup

section NF

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

/-- **Simple roots modulo infinitely many primes.** -/
lemma exists_simple_root_prime (mZ : ℤ[X]) (hmZ : toPoly M = mZ.map (Int.castRingHom ℚ))
    (hF0 : 0 < mZ.natDegree) (T : ℕ) :
    ∃ p, T < p ∧ p.Prime ∧ ∃ s : ZMod p, (mZ.map (Int.castRingHom (ZMod p))).eval s = 0 ∧
      ((derivative mZ).map (Int.castRingHom (ZMod p))).eval s ≠ 0 := by
  obtain ⟨u', v', -, -, huv'⟩ := exists_mul_add_mul_eq_C_resultant mZ (derivative mZ) le_rfl le_rfl
    (Or.inl hF0.ne')
  set R := resultant mZ (derivative mZ)
  have hR0 : R ≠ 0 := by
    intro h0
    have hmap := resultant_map_map mZ (derivative mZ) mZ.natDegree (derivative mZ).natDegree
      (Int.castRingHom ℚ)
    rw [← show R = resultant mZ (derivative mZ) from rfl, h0, map_zero] at hmap
    have hsepM : (toPoly M).Separable := (Irreducible.separable (Fact.out))
    rw [hmZ] at hsepM
    have hne := resultant_ne_zero (mZ.map (Int.castRingHom ℚ)) _ (hsepM : IsCoprime _ _)
    rw [derivative_map, natDegree_map_eq_of_injective (RingHom.injective_int _),
      natDegree_map_eq_of_injective (RingHom.injective_int _)] at hne
    exact hne hmap
  obtain ⟨p, hp, hpS, n, hn⟩ := Schur.exists_prime_dvd_eval mZ hF0
    (Finset.range (T + 1) ∪ Nat.primeFactors R.natAbs)
  have hpT : T < p := by
    by_contra h; exact hpS (Finset.mem_union_left _ (Finset.mem_range.mpr (by omega)))
  have hpR : ¬ (p : ℤ) ∣ R := fun h ↦ hpS (Finset.mem_union_right _
    (Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp h, Int.natAbs_ne_zero.mpr hR0⟩))
  refine ⟨p, hpT, hp, (n : ZMod p), ?_, ?_⟩
  · rw [eval_map, eval₂_at_intCast, eq_intCast, Int.cast_id,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hn]
  · intro h0
    apply hpR
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hs : (mZ.map (Int.castRingHom (ZMod p))).eval (n : ZMod p) = 0 := by
      rw [eval_map, eval₂_at_intCast, eq_intCast, Int.cast_id,
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hn]
    have := congrArg (fun P : ℤ[X] ↦ (P.map (Int.castRingHom (ZMod p))).eval (n : ZMod p)) huv'
    simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, map_C, eval_C] at this
    simp only [hs, h0, mul_zero, zero_mul, zero_add, eq_intCast] at this
    exact this.symm

/-- The sum of the denominators of an element. -/
def denSum (x : NFC.NF M) : ℕ := (x.1.map (·.den)).sum

lemma pInt_of_den {x : NFC.NF M} {p : ℕ} (h : denSum x < p) : Jac.pIntL p x.1 = true :=
  Jac.pIntL_of_lt fun c hc ↦ lt_of_le_of_lt (Jac.den_le_sum hc) h

end NF

section Good

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

lemma nfRedAt_eq {mZl : List ℤ} {p : ℕ} [Fact p.Prime] {s : ZMod p}
    (hs : ((toPoly mZl).map (Int.castRingHom (ZMod p))).eval s = 0)
    (hs' : ((derivative (toPoly mZl)).map (Int.castRingHom (ZMod p))).eval s ≠ 0) :
    ∃ s' : ZMod p, nfRedAt (M := M) mZl p = some (nfFns p s') ∧
      ((toPoly mZl).map (Int.castRingHom (ZMod p))).eval s' = 0 ∧
      ((derivative (toPoly mZl)).map (Int.castRingHom (ZMod p))).eval s' ≠ 0 := by
  have hP : ∀ t : ZMod p, (evalC (Jac.castL p mZl) t == 0 &&
      evalC (CPoly.deriv (Jac.castL p mZl)) t != 0) = true ↔
      ((toPoly mZl).map (Int.castRingHom (ZMod p))).eval t = 0 ∧
      ((derivative (toPoly mZl)).map (Int.castRingHom (ZMod p))).eval t ≠ 0 := by
    intro t
    rw [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, evalC_eq, evalC_eq, toPoly_deriv, Jac.castL_eq,
      derivative_map]
  have hmem : s ∈ zmodElems p := by
    simp only [zmodElems, List.mem_map, List.mem_range]
    exact ⟨s.val, ZMod.val_lt s, ZMod.natCast_zmod_val s⟩
  obtain ⟨s', hs'f⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome (p := fun t : ZMod p ↦ evalC (Jac.castL p mZl) t == 0 &&
      evalC (CPoly.deriv (Jac.castL p mZl)) t != 0) |>.mpr ⟨s, hmem, (hP s).mpr ⟨hs, hs'⟩⟩)
  have hc := (hP s').mp (List.find?_some (p := fun t : ZMod p ↦ evalC (Jac.castL p mZl) t == 0 &&
      evalC (CPoly.deriv (Jac.castL p mZl)) t != 0) hs'f)
  exact ⟨s', by simp [nfRedAt, hs'f], hc⟩


set_option maxHeartbeats 4000000 in
/-- **All large primes with a simple root of `M` are good** for the reduced global certificate. -/
theorem goodPrime_eventually {mZl : List ℤ} (hmZ : toPoly M = (toPoly mZl).map (Int.castRingHom ℚ))
    {fK : CPoly (NFC.NF M)} {n : ℕ} (hn2 : 2 ≤ n) (hd : 0 < fK.length - 1)
    (hlc : fK.getD (fK.length - 1) 0 ≠ 0) (hsq : Squarefree (toPoly fK))
    {ζ : NFC.NF M} (hζn : ζ ^ n = 1) (hζl : ∀ l, 0 < l → l < n → ζ ^ l ≠ 1)
    {xs ys : List (NFC.NF M)} (hgen : (n - 1) * (fK.length - 1 - 1) ≤ 2 * xs.length)
    (hlen : ys.length = xs.length)
    (hE : ∀ i < xs.length, ys.getD i 0 ≠ 0 ∧ ys.getD i 0 ^ n = evalC fK (xs.getD i 0))
    (hxd : ∀ i < xs.length, ∀ j < xs.length, i ≠ j → xs.getD i 0 ≠ xs.getD j 0)
    {r : ℕ} {α β : Fin r → NFC.NF M}
    (hΓ : ∀ q, β q ≠ 0 ∧ β q ^ n = evalC fK (α q) ∧ ∀ x ∈ xs, α q ≠ x)
    (hinj : Function.Injective fun q ↦ (α q, β q))
    {lam : List (List (NFC.NF M))}
    (hcert : ∀ i < xs.length, ∀ ai ∈ basisN n (fK.length - 1) (n * xs.length),
      xs.getD i 0 ^ ai.1 * ys.getD i 0 ^ ai.2 =
        ∑ i' ∈ Finset.range xs.length, ∑ k ∈ Finset.Ico 1 n, lamK lam n i i' k *
          (xs.getD i' 0 ^ ai.1 * (ζ ^ k * ys.getD i' 0) ^ ai.2)) :
    ∃ T0, ∀ p, T0 < p → p.Prime → (∃ s : ZMod p,
      ((toPoly mZl).map (Int.castRingHom (ZMod p))).eval s = 0 ∧
      ((derivative (toPoly mZl)).map (Int.castRingHom (ZMod p))).eval s ≠ 0) →
      goodPrime (nfRedAt (M := M) mZl) (globalCert ζ xs ys lam) fK n α β p = true := by
  classical
  obtain ⟨u, v, huv⟩ := (PerfectField.separable_iff_squarefree.mpr hsq : IsCoprime _ _)
  set uL : CPoly (NFC.NF M) := (List.range (u.natDegree + 1)).map u.coeff
  set vL : CPoly (NFC.NF M) := (List.range (v.natDegree + 1)).map v.coeff
  have huL : toPoly uL = u := EllAlgo.toPoly_range_coeff u _ (Or.inr (Nat.lt_succ_self _))
  have hvL : toPoly vL = v := EllAlgo.toPoly_range_coeff v _ (Or.inr (Nat.lt_succ_self _))
  set dL : List (NFC.NF M) → ℕ := fun l ↦ (l.map denSum).sum
  set T0 : ℕ := n + dL fK + denSum (fK.getD (fK.length - 1) 0)⁻¹ + dL uL + dL vL + denSum ζ +
    ∑ l ∈ Finset.range n, denSum (ζ ^ l - 1)⁻¹ + dL xs + dL ys +
    ∑ i ∈ Finset.range xs.length, denSum (ys.getD i 0)⁻¹ +
    ∑ i ∈ Finset.range xs.length, ∑ j ∈ Finset.range xs.length, denSum (xs.getD i 0 - xs.getD j 0)⁻¹ +
    ∑ q : Fin r, (denSum (α q) + denSum (β q) + denSum (β q)⁻¹ +
      ∑ i ∈ Finset.range xs.length, denSum (α q - xs.getD i 0)⁻¹ +
      ∑ q' : Fin r, (denSum (α q - α q')⁻¹ + denSum (β q - β q')⁻¹)) +
    (lam.map dL).sum + denSum (0 : NFC.NF M) with hT0
  have hB1 : n + dL fK + denSum (fK.getD (fK.length - 1) 0)⁻¹ + dL uL + dL vL + denSum ζ +
      ∑ l ∈ Finset.range n, denSum (ζ ^ l - 1)⁻¹ + dL xs + dL ys +
      ∑ i ∈ Finset.range xs.length, denSum (ys.getD i 0)⁻¹ + (lam.map dL).sum + denSum (0 : NFC.NF M) ≤ T0 := by
    rw [hT0]; omega
  refine ⟨T0, fun p hpT hp ⟨s, hs, hs'⟩ ↦ ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hok : ∀ x : NFC.NF M, denSum x ≤ T0 → Jac.pIntL p x.1 = true := fun x hx ↦
    pInt_of_den (by omega)
  have hmemL : ∀ (l : List (NFC.NF M)) (x : NFC.NF M), x ∈ l → denSum x ≤ dL l := fun l x hx ↦
    List.le_sum_of_mem (List.mem_map_of_mem hx)
  obtain ⟨s', hR, hs1, hs2⟩ := nfRedAt_eq (M := M) (mZl := mZl) hs hs'
  obtain ⟨φ, hφ⟩ := nfFns_valid p (toPoly mZl) hmZ s' hs1 hs2
  set R := nfFns (M := M) p s'
  unfold goodPrime
  rw [dif_pos hp]
  simp only [hR, globalCert]
  unfold goodCheck
  refine decide_eq_true ?_
  have hgi : ∀ i, i < xs.length → ∀ j, j < xs.length → denSum (xs.getD i 0 - xs.getD j 0)⁻¹ ≤ T0 := by
    intro i hi j hj
    have h1 := Finset.single_le_sum (f := fun j ↦ denSum (xs.getD i 0 - xs.getD j 0)⁻¹)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr hj)
    have h2 := Finset.single_le_sum (f := fun i ↦ ∑ j ∈ Finset.range xs.length,
      denSum (xs.getD i 0 - xs.getD j 0)⁻¹) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr hi)
    omega
  have hq : ∀ q : Fin r, denSum (α q) + denSum (β q) + denSum (β q)⁻¹ +
      ∑ i ∈ Finset.range xs.length, denSum (α q - xs.getD i 0)⁻¹ +
      ∑ q' : Fin r, (denSum (α q - α q')⁻¹ + denSum (β q - β q')⁻¹) ≤ T0 := fun q ↦ by
    have := Finset.single_le_sum (f := fun q ↦ denSum (α q) + denSum (β q) + denSum (β q)⁻¹ +
      ∑ i ∈ Finset.range xs.length, denSum (α q - xs.getD i 0)⁻¹ +
      ∑ q' : Fin r, (denSum (α q - α q')⁻¹ + denSum (β q - β q')⁻¹)) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ q)
    omega
  have hqq : ∀ q q' : Fin r, denSum (α q - α q')⁻¹ + denSum (β q - β q')⁻¹ ≤ T0 := fun q q' ↦ by
    have h1 := Finset.single_le_sum (f := fun q' ↦ denSum (α q - α q')⁻¹ + denSum (β q - β q')⁻¹)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ q')
    have := hq q
    omega
  have hqx : ∀ q : Fin r, ∀ i < xs.length, denSum (α q - xs.getD i 0)⁻¹ ≤ T0 := fun q i hi ↦ by
    have h1 := Finset.single_le_sum (f := fun i ↦ denSum (α q - xs.getD i 0)⁻¹)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr hi)
    have := hq q
    omega
  have hokR : ∀ x : NFC.NF M, denSum x ≤ T0 → R.ok x = true := fun x hx ↦ hok x hx
  have hgetmem : ∀ i < xs.length, xs.getD i 0 ∈ xs := fun i hi ↦ by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  have hgetmemy : ∀ i < xs.length, ys.getD i 0 ∈ ys := fun i hi ↦ by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem (by omega)
  have hnp : ((n : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hlm : fK.length - 1 < fK.length := by omega
  refine globalCert_check φ R hφ hn2 hnp hd (fun c hc ↦ hokR c (by have := hmemL fK c hc; omega))
    hlc (hokR _ (by omega)) (u := uL) (v := vL)
    (fun c hc ↦ hokR c (by have := hmemL uL c hc; omega))
    (fun c hc ↦ hokR c (by have := hmemL vL c hc; omega)) (by rw [huL, hvL]; exact huv)
    (hokR ζ (by omega)) hζn ?_ hgen hlen ?_ ?_ ?_ ?_ ?_ (hokR 0 (by omega)) ?_ hcert
  · intro l hl hln
    refine ⟨(ζ ^ l - 1)⁻¹, hokR _ ?_, mul_inv_cancel₀ (sub_ne_zero.mpr (hζl l hl hln))⟩
    have := Finset.single_le_sum (f := fun l ↦ denSum (ζ ^ l - 1)⁻¹) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.mpr hln)
    omega
  · intro i hi
    obtain ⟨hy0, hye⟩ := hE i hi
    have h1 := hmemL xs _ (hgetmem i hi)
    have h2 := hmemL ys _ (hgetmemy i hi)
    have h3 := Finset.single_le_sum (f := fun i ↦ denSum (ys.getD i 0)⁻¹) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.mpr hi)
    exact ⟨hokR _ (by omega), hokR _ (by omega), hy0, hokR _ (by omega), hye⟩
  · intro i hi j hj hij
    exact ⟨hxd i hi j hj hij, hokR _ (hgi i hi j hj)⟩
  · intro q
    obtain ⟨hb0, hbe, hax⟩ := hΓ q
    have := hq q
    refine ⟨hokR _ (by omega), hokR _ (by omega), hb0, hokR _ (by omega), hbe, fun x hx ↦
      ⟨hax x hx, ?_⟩⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have := hqx q i hi
    rw [List.getD_eq_getElem _ _ hi] at this
    exact hokR _ this
  · intro q q' _
    have := hqq q q'
    exact hokR _ (by omega)
  · intro q q' hqq' hα
    refine ⟨fun hb ↦ hqq' (hinj (Prod.ext hα hb)), ?_⟩
    have := hqq q q'
    exact hokR _ (by omega)
  · intro l hl c hc
    have h1 := hmemL l c hc
    have h2 : dL l ≤ (lam.map dL).sum := List.le_sum_of_mem (List.mem_map_of_mem hl)
    exact hokR c (by omega)

end Good

end Sup
