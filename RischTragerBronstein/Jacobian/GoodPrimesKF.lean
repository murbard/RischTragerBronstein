import RischTragerBronstein.Jacobian.TorsionDecideKF
import RischTragerBronstein.Jacobian.GoodPrimesK

/-!
# Good primes for a curve over a number field

`exists_goodKF`: for `y² = f(x)`, `f ∈ K[x]` squarefree of degree `2g + 1`, `K = NF M`, a
divisor `Γ` over `K`, and base points `(aᵢ, bᵢ)` with `aᵢ ∈ ℤ`, `bᵢ ∈ K`, `goodKF` succeeds at
primes above any bound. As in `exists_goodK` (Schur's theorem for `M`, Hensel), with the curve
reduced coefficientwise; polynomial identities over `K` with `p`-integral coefficients (the Bézout
identity `u f + v f′ = 1`, `bᵢ² = f(aᵢ)`) are lifted to `ℤ_p` and reduced (`exists_liftPoly`).
-/

open Polynomial CPoly CPoly.Kron EllAlgo

namespace Jac

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

lemma evalC_liftZ {p : ℕ} [NeZero p] (l : CPoly (ZMod p)) (r : ℤ) :
    ((evalC (liftZ l) r : ℤ) : ZMod p) = evalC l (r : ZMod p) := by
  rw [evalC_eq, evalC_eq, ← eq_intCast (Int.castRingHom (ZMod p)), ← eval₂_hom, ← eval_map,
    ← toPoly_map_list, liftZ, List.map_map]
  congr 2
  · exact List.map_id'' (fun c ↦ by simp) _

/-- **Lifting polynomials with `p`-integral coefficients.** -/
lemma exists_liftPoly {p : ℕ} [Fact p.Prime] (Fm : ℤ[X])
    (hmZ : toPoly M = Fm.map (Int.castRingHom ℚ)) (z : ℤ_[p]) (hz : aeval z Fm = 0)
    (P : CPoly (NFC.NF M)) (hP : ∀ c ∈ P, pIntL p c.1 = true) :
    ∃ LP : ℤ_[p][X], LP.map (algebraMap ℤ_[p] ℚ_[p]) = (toPoly P).map (embedZ Fm hmZ z hz) ∧
      LP.map PadicInt.toZMod = toPoly (redF p (PadicInt.toZMod z) P) := by
  classical
  have hl : ∀ x : NFC.NF M, pIntL p x.1 = true → ∃ w : ℤ_[p],
      (w : ℚ_[p]) = embedZ Fm hmZ z hz x ∧ PadicInt.toZMod w = redL p (PadicInt.toZMod z) x.1 :=
    fun x hx ↦ exists_lift_NF Fm hmZ z hz x hx
  choose! lf hlf1 hlf2 using hl
  refine ⟨toPoly (P.map lf), ?_, ?_⟩
  · rw [← toPoly_map_list, ← toPoly_map_list, List.map_map]
    congr 1
    exact List.map_congr_left fun c hc ↦ hlf1 c (hP c hc)
  · rw [← toPoly_map_list, List.map_map, redF]
    congr 1
    exact List.map_congr_left fun c hc ↦ hlf2 c (hP c hc)

set_option maxHeartbeats 3200000 in
/-- **Good primes exist** for a curve and a divisor over `K = NF M`, when base points with
`x ∈ ℤ` and `y ∈ K` are available. -/
theorem exists_goodKF (hMZ : ∀ q ∈ M, q.den = 1) {f : CPoly (NFC.NF M)} {g : ℕ}
    (hlen : f.length = 2 * g + 2) (hlc : f.getD (2 * g + 1) 0 ≠ 0)
    (hsq : Squarefree (toPoly f)) (hM1 : 0 < (toPoly M).natDegree)
    (Γ : EDiv (NFC.NF M)) (hΓ : ∀ q ∈ Γ, q.2.1 ≠ 0) (hΓd : Γ.Pairwise fun u v ↦ u.1 ≠ v.1)
    (as bs : List (NFC.NF M)) (hasl : as.length = g) (hbsl : bs.length = g)
    (hab : ∀ i (hi : i < g), bs[i]'(by omega) * bs[i]'(by omega) =
      (toPoly f).eval (as[i]'(by omega)) ∧ bs[i]'(by omega) ≠ 0)
    (hasnd : as.Nodup) (hΓa : ∀ q ∈ Γ, ∀ a ∈ as, q.1 ≠ a) (N : ℕ) :
    ∃ p, N < p ∧ (goodKF (M.map Rat.num) f g Γ p).isSome := by
  classical
  set mZ := M.map Rat.num
  have hmZ : toPoly M = (toPoly mZ).map (Int.castRingHom ℚ) := (Kron.polyZ_map M hMZ).symm
  set F : ℤ[X] := toPoly mZ
  have hF0 : 0 < F.natDegree := by
    rw [← natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)), ← hmZ]
    exact hM1
  -- the Bézout identity for `f`
  have hcop : IsCoprime (toPoly f) (derivative (toPoly f)) :=
    (PerfectField.separable_iff_squarefree.mpr hsq)
  obtain ⟨u, v, huv⟩ := hcop
  set uL : CPoly (NFC.NF M) := (List.range (u.natDegree + 1)).map u.coeff
  set vL : CPoly (NFC.NF M) := (List.range (v.natDegree + 1)).map v.coeff
  have huL : toPoly uL = u := toPoly_range_coeff u _ (Or.inr (Nat.lt_succ_self _))
  have hvL : toPoly vL = v := toPoly_range_coeff v _ (Or.inr (Nat.lt_succ_self _))
  set lead := f.getD (2 * g + 1) 0
  -- the elements whose reductions matter
  set Els : List (NFC.NF M) :=
    Γ.flatMap (fun q ↦ [q.1, q.2.1, q.2.1⁻¹]) ++
    Γ.flatMap (fun q ↦ Γ.flatMap fun q' ↦ [q.1 - q'.1, (q.1 - q'.1)⁻¹]) ++
    Γ.flatMap (fun q ↦ as.flatMap fun a ↦ [q.1 - a, (q.1 - a)⁻¹]) ++
    as ++
    as.flatMap (fun a ↦ as.flatMap fun a' ↦ [a - a', (a - a')⁻¹]) ++
    bs ++
    bs.map (·⁻¹) ++
    f ++
    [lead⁻¹] ++
    uL ++
    vL
  set Td := (Els.map fun x ↦ (x.1.map (·.den)).sum).sum
  set T := N + 3 + Td
  obtain ⟨u', v', -, -, huv'⟩ := exists_mul_add_mul_eq_C_resultant F (derivative F) le_rfl le_rfl
    (Or.inl hF0.ne')
  set R := resultant F (derivative F)
  have hR0 : R ≠ 0 := by
    intro h0
    have hmap := resultant_map_map F (derivative F) F.natDegree (derivative F).natDegree
      (Int.castRingHom ℚ)
    rw [← show R = resultant F (derivative F) from rfl, h0, map_zero] at hmap
    have hsepM : (toPoly M).Separable := (Irreducible.separable (Fact.out))
    rw [hmZ] at hsepM
    have hne := resultant_ne_zero (F.map (Int.castRingHom ℚ)) _ (hsepM : IsCoprime _ _)
    rw [derivative_map, natDegree_map_eq_of_injective (RingHom.injective_int _),
      natDegree_map_eq_of_injective (RingHom.injective_int _)] at hne
    exact hne hmap
  obtain ⟨p, hp, hpS, n, hn⟩ := Schur.exists_prime_dvd_eval F hF0
    (Finset.range (T + 1) ∪ Nat.primeFactors R.natAbs)
  have hpT : T < p := by
    by_contra h; exact hpS (Finset.mem_union_left _ (Finset.mem_range.mpr (by omega)))
  have hpR : ¬ (p : ℤ) ∣ R := fun h ↦ hpS (Finset.mem_union_right _
    (Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp h, Int.natAbs_ne_zero.mpr hR0⟩))
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨p, by omega, ?_⟩
  have hp0 : 0 < p := hp.pos
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hp2 : p ≠ 2 := by omega
  -- the root and its lift
  set s : ZMod p := (n : ZMod p)
  have hs : (F.map (Int.castRingHom (ZMod p))).eval s = 0 := by
    rw [eval_map, eval₂_at_intCast, eq_intCast, Int.cast_id,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hn]
  have hs' : ((derivative F).map (Int.castRingHom (ZMod p))).eval s ≠ 0 := by
    intro h0
    apply hpR
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := congrArg (fun P : ℤ[X] ↦ (P.map (Int.castRingHom (ZMod p))).eval s) huv'
    simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, map_C, eval_C] at this
    simp only [hs, h0, mul_zero, zero_mul, zero_add, eq_intCast] at this
    exact this.symm
  obtain ⟨z, hz, hzs⟩ := hensel_root_red F s hs hs'
  have hzs' : PadicInt.toZMod z = s := hzs
  -- integrality of the relevant elements
  have hpI : ∀ x ∈ Els, pIntL p x.1 = true := fun x hx ↦ pIntL_of_lt fun c hc ↦ by
    have h1 := den_le_sum hc
    have h2 : (x.1.map (·.den)).sum ≤ Td := List.le_sum_of_mem (List.mem_map_of_mem
      (f := fun x : NFC.NF M ↦ (x.1.map (·.den)).sum) hx)
    omega
  have mem1 : ∀ q ∈ Γ, q.1 ∈ Els ∧ q.2.1 ∈ Els ∧ q.2.1⁻¹ ∈ Els := fun q hq ↦
    ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨q, hq, by simp⟩)))))))))),
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨q, hq, by simp⟩)))))))))),
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨q, hq, by simp⟩))))))))))⟩
  have mem2 : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q'.1 ∈ Els ∧ (q.1 - q'.1)⁻¹ ∈ Els := fun q hq q' hq' ↦
    ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, List.mem_flatMap.mpr ⟨q', hq', by simp⟩⟩)))))))))),
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, List.mem_flatMap.mpr ⟨q', hq', by simp⟩⟩))))))))))⟩
  have mem3 : ∀ q ∈ Γ, ∀ a ∈ as, q.1 - a ∈ Els ∧ (q.1 - a)⁻¹ ∈ Els := fun q hq a ha ↦
    ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, List.mem_flatMap.mpr ⟨a, ha, by simp⟩⟩))))))))),
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, List.mem_flatMap.mpr ⟨a, ha, by simp⟩⟩)))))))))⟩
  have mema : ∀ a ∈ as, a ∈ Els := fun a ha ↦ List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (ha))))))))
  have mema2 : ∀ a ∈ as, ∀ a' ∈ as, a - a' ∈ Els ∧ (a - a')⁻¹ ∈ Els := fun a ha a' ha' ↦
    ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, List.mem_flatMap.mpr ⟨a', ha', by simp⟩⟩))))))),
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨a, ha, List.mem_flatMap.mpr ⟨a', ha', by simp⟩⟩)))))))⟩
  have mem4 : ∀ b ∈ bs, b ∈ Els ∧ b⁻¹ ∈ Els := fun b hb ↦
    ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (hb)))))), List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hb)))))⟩
  have memf : ∀ c ∈ f, c ∈ Els := fun c hc ↦ List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (hc))))
  have memlead : lead⁻¹ ∈ Els := List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have memu : ∀ c ∈ uL, c ∈ Els := fun c hc ↦ List.mem_append_left _ (List.mem_append_right _ (hc))
  have memv : ∀ c ∈ vL, c ∈ Els := fun c hc ↦ List.mem_append_right _ (hc)
  have hlt : 2 * g + 1 < f.length := by omega
  have hleadmem : lead ∈ f := by
    simp only [lead]; rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
  -- the lifted curve and Bézout data
  obtain ⟨LF, hLF1, hLF2⟩ := exists_liftPoly F hmZ z hz f fun c hc ↦ hpI _ (memf c hc)
  obtain ⟨LU, hLU1, hLU2⟩ := exists_liftPoly F hmZ z hz uL fun c hc ↦ hpI _ (memu c hc)
  obtain ⟨LV, hLV1, hLV2⟩ := exists_liftPoly F hmZ z hz vL fun c hc ↦ hpI _ (memv c hc)
  rw [hzs'] at hLF2 hLU2 hLV2
  set φ := embedZ F hmZ z hz
  set ι := algebraMap ℤ_[p] ℚ_[p]
  have hιinj : Function.Injective ι := Subtype.coe_injective
  have hbez : LU * LF + LV * derivative LF = 1 := by
    apply Polynomial.map_injective ι hιinj
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, ← derivative_map]
    rw [hLU1, hLF1, hLV1, huL, hvL, derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
      ← Polynomial.map_add, huv, Polynomial.map_one]
  have hcopZ : IsCoprime (toPoly (redF p s f)) (derivative (toPoly (redF p s f))) := by
    refine ⟨toPoly (redF p s uL), toPoly (redF p s vL), ?_⟩
    have := congrArg (Polynomial.map (PadicInt.toZMod (p := p))) hbez
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, ← derivative_map]
      at this
    rwa [hLU2, hLF2, hLV2] at this
  -- the reductions (with `s = z mod p`)
  have R1 : ∀ q ∈ Γ, redL p s q.2.1.1 ≠ 0 := fun q hq ↦ by
    rw [← hzs']
    exact redL_ne_zero F hmZ z hz (hΓ q hq) (hpI _ (mem1 q hq).2.1) (hpI _ (mem1 q hq).2.2)
  have R2 : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 ≠ q'.1 → redL p s q.1.1 ≠ redL p s q'.1.1 := by
    intro q hq q' hq' hne
    rw [← hzs', ← sub_ne_zero, ← redL_sub F hmZ z hz (hpI _ (mem1 q hq).1) (hpI _ (mem1 q' hq').1)
      (hpI _ (mem2 q hq q' hq').1)]
    exact redL_ne_zero F hmZ z hz (sub_ne_zero.mpr hne) (hpI _ (mem2 q hq q' hq').1)
      (hpI _ (mem2 q hq q' hq').2)
  have R3 : ∀ q ∈ Γ, ∀ a ∈ as, redL p s q.1.1 - redL p s a.1 ≠ 0 := by
    intro q hq a ha
    obtain ⟨h1, h2⟩ := mem3 q hq a ha
    rw [← hzs', ← redL_sub F hmZ z hz (hpI _ (mem1 q hq).1) (hpI _ (mema a ha)) (hpI _ h1)]
    exact redL_ne_zero F hmZ z hz (sub_ne_zero.mpr (hΓa q hq a ha)) (hpI _ h1) (hpI _ h2)
  have Rd : ∀ a ∈ as, ∀ a' ∈ as, a ≠ a' → redL p s a.1 ≠ redL p s a'.1 := by
    intro a ha a' ha' hne
    obtain ⟨h1, h2⟩ := mema2 a ha a' ha'
    rw [← hzs', ← sub_ne_zero, ← redL_sub F hmZ z hz (hpI _ (mema a ha)) (hpI _ (mema a' ha'))
      (hpI _ h1)]
    exact redL_ne_zero F hmZ z hz (sub_ne_zero.mpr hne) (hpI _ h1) (hpI _ h2)
  have hlead0 : lead ≠ 0 := hlc
  have Rlc : redL p s lead.1 ≠ 0 := by
    rw [← hzs']
    exact redL_ne_zero F hmZ z hz hlead0 (hpI _ (memf _ hleadmem)) (hpI _ memlead)
  have R4 : ∀ i (hi : i < g), redL p s (bs[i]'(by omega)).1 ≠ 0 ∧
      redL p s (bs[i]'(by omega)).1 ^ 2 =
        (toPoly (redF p s f)).eval (redL p s (as[i]'(by omega)).1) := by
    intro i hi
    have hb := List.getElem_mem (l := bs) (by omega : i < bs.length)
    have ha := List.getElem_mem (l := as) (by omega : i < as.length)
    obtain ⟨h1, h2⟩ := mem4 _ hb
    refine ⟨by rw [← hzs']; exact redL_ne_zero F hmZ z hz (hab i hi).2 (hpI _ h1) (hpI _ h2), ?_⟩
    obtain ⟨w, hw1, hw2⟩ := exists_lift_NF F hmZ z hz _ (hpI _ h1)
    obtain ⟨wa, hwa1, hwa2⟩ := exists_lift_NF F hmZ z hz _ (hpI _ (mema _ ha))
    rw [hzs'] at hw2 hwa2
    have hw : w ^ 2 = LF.eval wa := by
      apply hιinj
      have e1 : ι (LF.eval wa) = φ ((toPoly f).eval (as[i]'(by omega))) := by
        rw [show ι (LF.eval wa) = (LF.map ι).eval (ι wa) by rw [eval_map, eval₂_hom],
          hLF1, eval_map, show ι wa = (wa : ℚ_[p]) from rfl, hwa1, eval₂_hom]
      rw [map_pow, show ι w = (w : ℚ_[p]) from rfl, hw1, ← map_pow, sq, (hab i hi).1, e1]
    rw [← hw2, ← map_pow, hw, toZMod_eval, hLF2, hwa2]
  -- the base points `aᵢ mod p`
  have hcast : ∀ a : NFC.NF M, (((redL p s a.1).val : ℕ) : ZMod p) = redL p s a.1 := fun a ↦
    ZMod.natCast_zmod_val _
  set L := as.map fun a ↦ (redL p s a.1).val
  have hLnd : L.Nodup := by
    refine hasnd.map_on fun a ha a' ha' he ↦ ?_
    by_contra hne
    exact Rd a ha a' ha' hne (by rw [← hcast a, ← hcast a', he])
  set fZ := liftZ (redF p s f)
  have hcand : ∃ L : List ℕ, L.Nodup ∧ g ≤ L.length ∧ ∀ r ∈ L, r < p ∧
      (∀ a ∈ Γ.map (fun q ↦ redL p s q.1.1), a - (r : ZMod p) ≠ 0) ∧
      (sqrtMod p (evalC fZ r)).isSome := by
    refine ⟨L, hLnd, by simp [L, hasl], fun r hr ↦ ?_⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    have hig : i < g := by omega
    refine ⟨ZMod.val_lt _, ?_, ?_⟩
    · intro c hc
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
      rw [hcast]
      exact R3 q hq _ ha
    · obtain ⟨hb0, hb2⟩ := R4 i hig
      set y : ℤ := ((redL p s (bs[i]'(by omega)).1).val : ℤ)
      have hy : (y : ZMod p) = redL p s (bs[i]'(by omega)).1 := by simp [y]
      apply sqrtMod_isSome hp0 (y := y)
      · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hy]; exact hb0
      · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [evalC_liftZ, hy, hb2, evalC_eq, Int.cast_natCast, hcast, sub_self]
  obtain ⟨xs, ys, hfind, hxl, hyl, hE, hxd, havoid⟩ := findE0K_good (f := fZ) (g := g) hcand
  -- the prime is good
  unfold goodKF
  rw [dif_pos hp, List.findSome?_isSome_iff]
  refine ⟨s.val, List.mem_range.mpr (ZMod.val_lt s), ?_⟩
  simp only [ZMod.natCast_zmod_val]
  rw [hfind]
  dsimp only
  rw [if_pos]
  · rfl
  refine ⟨⟨hp2, hlen, fun c hc ↦ hpI _ (memf c hc), Rlc, hxl, hyl, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    obtain ⟨h1, h2⟩ := hE i hi
    refine ⟨?_, fun h0 ↦ h2 (by rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h0)⟩
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h1
    push_cast at this
    rw [evalC_liftZ] at this
    exact sub_eq_zero.mp this
  · exact hxd.imp fun h he ↦ h (by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [he, sub_self])
  · rw [evalC_eq, castL_eq]; exact hs
  · rw [evalC_eq, toPoly_deriv, castL_eq, derivative_map]; exact hs'
  · intro q hq
    exact ⟨hpI _ (mem1 q hq).1, hpI _ (mem1 q hq).2.1,
      mul_ne_zero (two_ne_zero_zmod hp2) (R1 q hq),
      fun x hx ↦ havoid x hx _ (List.mem_map_of_mem hq)⟩
  · exact hΓd.imp_of_mem fun {u v} hu hv huv ↦ R2 u hu v hv huv
  · exact squarefreeCheck_complete hcopZ

end Jac
