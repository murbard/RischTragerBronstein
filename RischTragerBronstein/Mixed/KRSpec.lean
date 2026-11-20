import RischTragerBronstein.Mixed.KFSpecExist
import RischTragerBronstein.Mixed.KRTwist
import RischTragerBronstein.Mixed.KRIrr
import RischTragerBronstein.Algebraic.SupLocalEventN
import RischTragerBronstein.Algebraic.SupSimpleRoot2

/-!
# Good primes for the cyclotomic code fields `Kₘ(ζₙ)`

Rational constants are specializable at every level (`specB_ratCast`) and reduce to their
residues (`red_ratCast`). The reductions `redAtNF` of `Kₘ(ζₙ)` exist at infinitely many primes for
suitable residues (simultaneous simple roots of the specialized base curve and of `Φₙ`,
`exists_simple_roots_prime`), and at those primes `n ∣ p − 1` (a simple root of `Φₙ` modulo `p ∤ n`
is a primitive `n`-th root of unity). Hence the local-certificate oracle over `Kₘ(ζₙ)` eventually
answers (`kfz_torsLocal_exists`).
-/

open Polynomial CPoly CPoly.Kron

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup

lemma mem_coeff {K : Type*} [CommRing K] (l : CPoly K) (a : K) (ha : a ∈ l) :
    ∃ i, a = (toPoly l).coeff i := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  exact ⟨i, by rw [coeff_toPoly, List.getD_eq_getElem _ _ hi]⟩

lemma mem_of_toPoly_C {K : Type*} [CommRing K] (l : CPoly K) (c : K) (h : toPoly l = C c) :
    ∀ a ∈ l, a = c ∨ a = 0 := fun a ha ↦ by
  obtain ⟨i, rfl⟩ := mem_coeff l a ha
  rw [h, coeff_C]; split_ifs <;> simp

/-- The canonical form of a polynomial in `K(t)`. -/
lemma canon_of_poly {K : Type*} [Field K] [DecidableEq K] [CharZero K] (x : RFC.RatFuncC K) (P0 : K[X])
    (h : RFC.toRF x = algebraMap K[X] (RatFunc K) P0) :
    toPoly (RFC.canon x).2 = 1 ∧ toPoly (RFC.canon x).1 = P0 := by
  obtain ⟨h0, hm, hcop, heq⟩ := RFC.canon_spec x
  rw [h] at heq
  set P := toPoly (RFC.canon x).1
  set Q := toPoly (RFC.canon x).2
  have hQ0 : algebraMap K[X] (RatFunc K) Q ≠ 0 := RFC.algebraMap_ne_zero h0
  have hPQ : P0 * Q = P := by
    apply IsFractionRing.injective K[X] (RatFunc K)
    rw [map_mul, heq, div_mul_cancel₀ _ hQ0]
  have hu : IsUnit Q := hcop.isUnit_of_dvd' ⟨P0, by rw [← hPQ, mul_comm]⟩ dvd_rfl
  have hQ1 : Q = 1 := hm.eq_one_of_isUnit hu
  exact ⟨hQ1, by rw [← hPQ, hQ1, mul_one]⟩

lemma toRF_ratCast_C {K : Type*} [Field K] [DecidableEq K] [CharZero K] (q : ℚ) :
    RFC.toRF (q : RFC.RatFuncC K) = algebraMap K[X] (RatFunc K) (C (q : K)) := by
  rw [RFC.toRF_ratCast, RatFunc.algebraMap_C, map_ratCast]

lemma toRF_zero_C {K : Type*} [Field K] [DecidableEq K] [CharZero K] :
    RFC.toRF (0 : RFC.RatFuncC K) = algebraMap K[X] (RatFunc K) 0 := by
  rw [RFC.toRF_zero, map_zero]

/-- The residue of a rational constant. -/
lemma red_ratCast {K : Type*} [Field K] [CharZero K] {p : ℕ} [Fact p.Prime] (R : RedFns p K)
    (φ : K →+* ℚ_[p]) (hR : RedValid p R φ) (q : ℚ) (hok : R.ok (q : K) = true)
    (hq : q.den % p ≠ 0) : R.red (q : K) = Jac.ratMod p q := by
  obtain ⟨z, hz, hzr⟩ := hR _ hok
  rw [← hzr]
  exact ratMod_of_lift hq (by
    rw [show ((z : ℚ_[p])) = algebraMap ℤ_[p] ℚ_[p] z from rfl, ← hz, map_ratCast])


section Rat

variable (Fc : BPoly ℚ) [hF : Fact (Irreducible (toPoly (fKc Fc)))]

/-- **Rational constants are specializable.** -/
theorem specB_ratCast (rs : ℕ → ℕ) : ∀ m (q : ℚ), specB Fc rs m (q : KF Fc m) = true := by
  intro m
  induction m with
  | zero =>
    intro q
    simp only [specB, List.all_eq_true, bne_iff_ne, ne_eq]
    change ∀ a ∈ (NFK.mk (fKc Fc) [((q : ℚ) : RFC.RatFuncC ℚ)]).1, _
    intro a ha
    have hdeg : 0 < (toPoly (fKc Fc)).degree := by
      have := hF.out.natDegree_pos
      rw [degree_eq_natDegree hF.out.ne_zero]; exact_mod_cast this
    have hp : toPoly (NFK.mk (fKc Fc) [((q : ℚ) : RFC.RatFuncC ℚ)]).1 = C ((q : ℚ) : RFC.RatFuncC ℚ) := by
      show toPoly (NFK.norm (fKc Fc) [((q : ℚ) : RFC.RatFuncC ℚ)]) = _
      rw [NFK.toPoly_norm_of_lt _ _ (by
        simp only [toPoly_cons, toPoly_nil, mul_zero, add_zero]
        exact lt_of_le_of_lt (degree_C_le) hdeg)]
      simp
    rcases mem_of_toPoly_C _ _ hp a ha with rfl | rfl
    · rw [evalC_eq, (canon_of_poly _ _ (toRF_ratCast_C q)).1, eval_one]; exact one_ne_zero
    · rw [evalC_eq, (canon_of_poly _ _ toRF_zero_C).1, eval_one]; exact one_ne_zero
  | succ m ih =>
    intro q
    have hx : (show RFC.RatFuncC (KF Fc m) from ((q : ℚ) : KF Fc (m + 1))) =
        ((q : ℚ) : RFC.RatFuncC (KF Fc m)) := rfl
    show (((RFC.canon (show RFC.RatFuncC (KF Fc m) from ((q : ℚ) : KF Fc (m + 1)))).1 ++
        (RFC.canon (show RFC.RatFuncC (KF Fc m) from ((q : ℚ) : KF Fc (m + 1)))).2).all
          (specB Fc rs m) &&
      evalC (RFC.canon (show RFC.RatFuncC (KF Fc m) from ((q : ℚ) : KF Fc (m + 1)))).2
        ((rs (m + 1) : ℕ) : KF Fc m) != 0 &&
      specB Fc rs m (evalC (RFC.canon (show RFC.RatFuncC (KF Fc m) from
        ((q : ℚ) : KF Fc (m + 1)))).2 ((rs (m + 1) : ℕ) : KF Fc m))⁻¹) = true
    rw [hx]
    obtain ⟨h2, h1⟩ := canon_of_poly _ _ (toRF_ratCast_C (K := KF Fc m) q)
    have hz : specB Fc rs m 0 = true := by simpa using ih 0
    have ho : specB Fc rs m 1 = true := by simpa using ih 1
    simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, evalC_eq, h2, eval_one,
      inv_one]
    refine ⟨⟨fun a ha ↦ ?_, one_ne_zero⟩, ho⟩
    rcases List.mem_append.mp ha with ha | ha
    · rcases mem_of_toPoly_C _ _ h1 a ha with rfl | rfl
      · exact ih q
      · exact hz
    · rcases mem_of_toPoly_C _ _ (h2.trans C_1.symm) a ha with rfl | rfl
      · exact ho
      · exact hz

end Rat


section Base

variable (Fc : BPoly ℚ)

/-- **Simple roots of the cleared specialized curve give the base check**, at all large primes. -/
theorem baseOK_of_root (c0 : ℕ) (hQ : ∀ a ∈ fKc Fc, evalC (RFC.canon a).2 (c0 : ℚ) ≠ 0)
    (D : ℤ) (hD : D ≠ 0) (mZ : ℤ[X])
    (hmZ : mZ.map (Int.castRingHom ℚ) = C (D : ℚ) * toPoly (fSpec Fc c0)) :
    ∃ T, ∀ (p : ℕ) [Fact p.Prime], T < p → ∀ s : ZMod p,
      (mZ.map (Int.castRingHom (ZMod p))).eval s = 0 →
      ((derivative mZ).map (Int.castRingHom (ZMod p))).eval s ≠ 0 →
      baseOK Fc p s (c0 : ZMod p) = true := by
  have hev : ∀ a ∈ fKc Fc, EvOk (fun _ ↦ True) (fun p _ ↦ rfFns p (ratFns p) (((c0 : ℤ)) : ZMod p))
      a := fun a ha ↦
    rf_evOk (fun _ ↦ True) (fun p _ ↦ ratFns p) (fun p _ _ ↦ ⟨_, ratFns_valid p⟩) (c0 : ℤ) a
      (fun b _ ↦ rat_evOk _ b) (by rw [← evalC_eq]; push_cast; exact hQ a ha) (rat_evOk _ _)
  obtain ⟨T1, hT1⟩ := evOk_list _ _ _ hev
  set T2 := ((fSpec Fc c0).map (·.den)).sum
  refine ⟨T1 + T2 + D.natAbs + 1, fun p _ hpT s hs hs' ↦ ?_⟩
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hok : ∀ a ∈ fKc Fc, (redX p (c0 : ZMod p)).ok a = true := fun a ha ↦ by
    have := hT1 p trivial (by omega) a ha
    simpa [redX] using this
  have hden : ∀ q ∈ fSpec Fc c0, q.den < p := fun q hq ↦ by
    have := den_lt_sum hq; omega
  have hlist : (fKc Fc).map (redX p (c0 : ZMod p)).red = (fSpec Fc c0).map (Jac.ratMod p) := by
    rw [fSpec, List.map_map]
    refine List.map_congr_left fun a ha ↦ ?_
    rw [Function.comp_apply, redX_red c0 a (hok a ha)]
    have := hden _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
    rw [Nat.mod_eq_of_lt this]; exact Rat.den_nz _
  have hDp : (D : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    have := Nat.le_of_dvd (Int.natAbs_pos.mpr hD) (Int.natCast_dvd.mp h)
    omega
  have hpoly : mZ.map (Int.castRingHom (ZMod p)) =
      C (D : ZMod p) * toPoly ((fSpec Fc c0).map (Jac.ratMod p)) := by
    ext i
    rw [coeff_map, coeff_C_mul, coeff_toPoly, getD_map_zero _ ratMod_zero]
    have hc := congrArg (fun P ↦ P.coeff i) hmZ
    simp only [coeff_map, coeff_C_mul, coeff_toPoly, eq_intCast] at hc
    have hg := den_getD_mod hp1 hden i
    rw [eq_intCast, ← ratMod_int, hc, ratMod_mul (by simp [Nat.mod_eq_of_lt hp1]) hg
      (by rw [← hc]; simp [Nat.mod_eq_of_lt hp1]), ratMod_int]
  simp only [baseOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  refine ⟨⟨hok, ?_⟩, ?_⟩
  · rw [hlist, evalC_eq]
    rw [hpoly, eval_mul, eval_C] at hs
    exact (mul_eq_zero.mp hs).resolve_left hDp
  · rw [hlist, evalC_eq, toPoly_deriv]
    rw [← derivative_map, hpoly, derivative_C_mul, eval_mul, eval_C] at hs'
    exact fun h ↦ hs' (by rw [h, mul_zero])

end Base

lemma evOk_congr {K : Type*} [Field K] (G : ℕ → Prop) (Rf Rf' : (p : ℕ) → [Fact p.Prime] → RedFns p K)
    (h : ∀ (p : ℕ) [Fact p.Prime], G p → Rf p = Rf' p) (x : K) (hx : EvOk G Rf x) : EvOk G Rf' x := by
  obtain ⟨T, hT⟩ := hx
  exact ⟨T, fun p _ hG hp ↦ by rw [← h p hG]; exact hT p hG hp⟩


section NFz

variable (Fc : BPoly ℚ) [hF : Fact (Irreducible (toPoly (fKc Fc)))] (m n : ℕ)

lemma s0opt_of_redAtKF (rs : ℕ → ℕ) (p : ℕ) [Fact p.Prime] (h : (redAtKF Fc m rs p).isSome) :
    (s0opt Fc rs p).isSome := by
  unfold redAtKF at h
  unfold s0opt
  rw [dif_pos Fact.out] at h ⊢
  rw [range_bind_eq] at h
  simpa using h

/-- The coefficients of `cycK` are the integer coefficients of `Φₙ`. -/
lemma coeff_cycK (hn : 0 < n) (i : ℕ) :
    (toPoly (cycK Fc m n)).coeff i = ((((cyclotomic n ℤ).coeff i : ℤ) : ℚ) : KF Fc m) := by
  rw [toPoly_cycK Fc m n hn, coeff_map, ← map_cyclotomic_int, coeff_map, eq_intCast, eq_ratCast]

/-- **The reduction of `cycK` is `Φₙ` modulo `p`.** -/
lemma toPoly_cycK_red (hn : 0 < n) (p : ℕ) [Fact p.Prime] (R0 : RedFns p (KF Fc m))
    (φ : KF Fc m →+* ℚ_[p]) (hR0 : RedValid p R0 φ) (hok : ∀ c ∈ cycK Fc m n, R0.ok c = true) :
    toPoly ((cycK Fc m n).map R0.red) = cyclotomic n (ZMod p) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  ext i
  rw [coeff_toPoly, ← map_cyclotomic_int, coeff_map, eq_intCast]
  by_cases hi : i < (cycK Fc m n).length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
    have hc : (cycK Fc m n)[i] = ((((cyclotomic n ℤ).coeff i : ℤ) : ℚ) : KF Fc m) := by
      rw [← coeff_cycK Fc m n hn i, coeff_toPoly, List.getD_eq_getElem _ _ hi]
    rw [hc, red_ratCast R0 φ hR0 _ (by rw [← hc]; exact hok _ (List.getElem_mem hi))
      (by simp [Nat.mod_eq_of_lt hp1]), ratMod_int]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    have h0 : (toPoly (cycK Fc m n)).coeff i = 0 := by
      rw [coeff_toPoly, List.getD_eq_default _ _ (by omega)]
    rw [coeff_cycK Fc m n hn] at h0
    have : (cyclotomic n ℤ).coeff i = 0 := by exact_mod_cast h0
    rw [this, Int.cast_zero]

end NFz


section NFz2

variable (Fc : BPoly ℚ) [hF : Fact (Irreducible (toPoly (fKc Fc)))] (m n : ℕ)
  [hz : Fact (Irreducible (toPoly (cycK Fc m n)))]

/-- **The shape of the reductions of `Kₘ(ζₙ)`.** -/
lemma redAtNF_spec (rs : ℕ → ℕ) (p : ℕ) [Fact p.Prime] (h : (redAtNF Fc m n rs p).isSome) :
    (s0opt Fc rs p).isSome ∧ ∃ ρ : ZMod p,
      redAtNF Fc m n rs p = some (nfkFns (redKF Fc p ((s0opt Fc rs p).getD 0)
        (fun j ↦ (rs j : ZMod p)) m) (cycK Fc m n) ρ) ∧
      (∀ c ∈ cycK Fc m n, (redKF Fc p ((s0opt Fc rs p).getD 0) (fun j ↦ (rs j : ZMod p)) m).ok c
        = true) ∧
      evalC ((cycK Fc m n).map (redKF Fc p ((s0opt Fc rs p).getD 0)
        (fun j ↦ (rs j : ZMod p)) m).red) ρ = 0 := by
  have hKF : (redAtKF Fc m rs p).isSome := by
    unfold redAtNF at h
    rw [dif_pos Fact.out] at h
    cases hK : redAtKF Fc m rs p with
    | none => rw [hK] at h; exact absurd h (by simp)
    | some R => rfl
  have hs0 := s0opt_of_redAtKF Fc m rs p hKF
  refine ⟨hs0, ?_⟩
  have hR := redAtKF_eq Fc m rs p hs0
  unfold redAtNF at h ⊢
  rw [dif_pos Fact.out] at h ⊢
  rw [hR] at h ⊢
  simp only at h ⊢
  split_ifs at h ⊢ with hall
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hx
    have hp := List.find?_some hi
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hp
    refine ⟨_, hx, fun c hc ↦ List.all_eq_true.mp hall c hc, hp.1⟩
  · exact absurd h (by simp)

end NFz2


section NFz3

variable (Fc : BPoly ℚ) [hF : Fact (Irreducible (toPoly (fKc Fc)))] (m n : ℕ)
  [hz : Fact (Irreducible (toPoly (cycK Fc m n)))]

/-- The reductions of `Kₘ(ζₙ)` as a total family. -/
def RfNF (rs : ℕ → ℕ) (p : ℕ) [Fact p.Prime] : RedFns p (NFz Fc m n) :=
  (redAtNF Fc m n rs p).getD ⟨fun _ ↦ false, fun _ ↦ 0⟩

/-- **The good primes of `Kₘ(ζₙ)`**: the reduction exists and `p > n`. -/
def GNF (rs : ℕ → ℕ) (p : ℕ) : Prop := (redAtNF Fc m n rs p).isSome = true ∧ n < p

lemma redAtNF_eq_RfNF (rs : ℕ → ℕ) (p : ℕ) [Fact p.Prime] (h : GNF Fc m n rs p) :
    redAtNF Fc m n rs p = some (RfNF Fc m n rs p) := by
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp h.1
  rw [RfNF, hR]; rfl

/-- At the good primes, `n ∣ p − 1`. -/
lemma GNF_dvd (hn : 0 < n) (rs : ℕ → ℕ) (p : ℕ) (hp : p.Prime) (h : GNF Fc m n rs p) :
    n ∣ p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hs0, ρ, -, hall, hroot⟩ := redAtNF_spec Fc m n rs p h.1
  obtain ⟨φ, hφ⟩ := redKF_valid Fc p _ (fun j ↦ (rs j : ZMod p)) (baseOK_s0opt Fc rs p hs0) m
  rw [evalC_eq, toPoly_cycK_red Fc m n hn p _ φ hφ hall] at hroot
  haveI : NeZero (n : ZMod p) := ⟨by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd; have := Nat.le_of_dvd hn hd; have := h.2; omega⟩
  have hprim : IsPrimitiveRoot ρ n := (isRoot_cyclotomic_iff).mp hroot
  have hρ0 : ρ ≠ 0 := hprim.ne_zero (by omega)
  rw [hprim.eq_orderOf]
  exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hρ0)

lemma evOk_mono {K : Type*} [Field K] (G G' : ℕ → Prop) (hG : ∀ p, G p → G' p)
    (Rf : (p : ℕ) → [Fact p.Prime] → RedFns p K) (x : K) (hx : EvOk G' Rf x) : EvOk G Rf x := by
  obtain ⟨T, hT⟩ := hx
  exact ⟨T, fun p _ hp hpT ↦ hT p (hG p hp) hpT⟩

/-- Elements of `Kₘ(ζₙ)` with specializable coefficients reduce well at all large good primes. -/
lemma evOk_nfz (rs : ℕ → ℕ) (z : NFz Fc m n) (hz : ∀ c ∈ z.1, specB Fc rs m c = true) :
    EvOk (GNF Fc m n rs) (fun p _ ↦ RfNF Fc m n rs p) z := by
  set Gb : ℕ → Prop := fun p ↦ (s0opt Fc rs p).isSome = true
  set s0 : (p : ℕ) → ZMod p := fun p ↦ (s0opt Fc rs p).getD 0
  have hGb : ∀ (p : ℕ) [Fact p.Prime], Gb p → baseOK Fc p (s0 p) (rs 0 : ZMod p) = true :=
    fun p _ hp ↦ baseOK_s0opt Fc rs p hp
  have hev : ∀ c ∈ z.1, EvOk Gb (fun p _ ↦ redKF Fc p (s0 p) (fun j ↦ (rs j : ZMod p)) m) c :=
    fun c hc ↦ specB_evOk Fc rs Gb s0 hGb m c (hz c hc)
  obtain ⟨T, hT⟩ := evOk_list _ _ _ hev
  refine ⟨T, fun p _ hp hpT ↦ ?_⟩
  obtain ⟨hs0, ρ, hρ, -, -⟩ := redAtNF_spec Fc m n rs p hp.1
  have hR : RfNF Fc m n rs p = nfkFns (redKF Fc p (s0 p) (fun j ↦ (rs j : ZMod p)) m)
      (cycK Fc m n) ρ := by
    have := redAtNF_eq_RfNF Fc m n rs p hp
    rw [hρ] at this
    exact (Option.some.inj this).symm
  show (RfNF Fc m n rs p).ok z = true
  rw [hR]
  simp only [nfkFns, List.all_eq_true]
  exact hT p hs0 hpT

end NFz3


section NFz4

variable (Fc : BPoly ℚ) [hF : Fact (Irreducible (toPoly (fKc Fc)))] (m n : ℕ)
  [hz : Fact (Irreducible (toPoly (cycK Fc m n)))]

/-- **Infinitely many good primes for `Kₘ(ζₙ)`** at residues outside `kfBad`. -/
lemma GNF_infinite (hn : 1 ≤ n) (rs : ℕ → ℕ) (h0 : rs 0 ∉ kfBad Fc) :
    ∀ N, ∃ p, p.Prime ∧ GNF Fc m n rs p ∧ N < p := by
  intro N
  obtain ⟨hsep, hdeg⟩ := kfBad_good Fc (rs 0) h0
  obtain ⟨D, hD, mZ, hmZ, hsepZ, hdegZ⟩ := clear_good _ hsep hdeg
  obtain ⟨T0, hT0⟩ := baseOK_of_root Fc (rs 0) (fKc_hQ Fc _) D hD mZ hmZ
  set Gb : ℕ → Prop := fun p ↦ (s0opt Fc rs p).isSome = true
  set s0 : (p : ℕ) → ZMod p := fun p ↦ (s0opt Fc rs p).getD 0
  have hGb : ∀ (p : ℕ) [Fact p.Prime], Gb p → baseOK Fc p (s0 p) (rs 0 : ZMod p) = true :=
    fun p _ hp ↦ baseOK_s0opt Fc rs p hp
  have hev : ∀ c ∈ cycK Fc m n,
      EvOk Gb (fun p _ ↦ redKF Fc p (s0 p) (fun j ↦ (rs j : ZMod p)) m) c := fun c hc ↦ by
    obtain ⟨i, rfl⟩ := mem_coeff _ c hc
    rw [coeff_cycK Fc m n (by omega)]
    exact specB_evOk Fc rs Gb s0 hGb m _ (specB_ratCast Fc rs m _)
  obtain ⟨T1, hT1⟩ := evOk_list _ _ _ hev
  have hΦsep : ((cyclotomic n ℤ).map (Int.castRingHom ℚ)).Separable := by
    rw [map_cyclotomic_int]; exact (cyclotomic.irreducible_rat (by omega)).separable
  have hΦdeg : 0 < (cyclotomic n ℤ).natDegree := by
    rw [natDegree_cyclotomic]; exact Nat.totient_pos.mpr (by omega)
  obtain ⟨p, hpT, hp, ⟨_, s, hs, hs'⟩, ⟨_, ρ, hρ, hρ'⟩⟩ :=
    exists_simple_roots_prime mZ (cyclotomic n ℤ) hsepZ hΦsep hdegZ hΦdeg (N + T0 + T1 + n + 1)
  haveI : Fact p.Prime := ⟨hp⟩
  have hb := hT0 p (by omega) s hs hs'
  have hs0 := s0opt_isSome Fc rs p s hb
  have hall : ∀ c ∈ cycK Fc m n,
      (redKF Fc p ((s0opt Fc rs p).getD 0) (fun j ↦ (rs j : ZMod p)) m).ok c = true :=
    hT1 p hs0 (by omega)
  obtain ⟨φ, hφ⟩ := redKF_valid Fc p _ (fun j ↦ (rs j : ZMod p)) (baseOK_s0opt Fc rs p hs0) m
  have hcyc := toPoly_cycK_red Fc m n (by omega) p _ φ hφ hall
  refine ⟨p, hp, ⟨?_, by omega⟩, by omega⟩
  unfold redAtNF
  rw [dif_pos hp]
  rw [redAtKF_eq Fc m rs p hs0]
  simp only
  rw [if_pos (List.all_eq_true.mpr hall), Option.isSome_map, range_bind_eq, List.find?_isSome]
  refine ⟨ρ, List.mem_map.mpr ⟨ρ.val, List.mem_range.mpr (ZMod.val_lt ρ),
    ZMod.natCast_zmod_val ρ⟩, ?_⟩
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, evalC_eq, hcyc, toPoly_deriv]
  refine ⟨?_, ?_⟩
  · rw [← map_cyclotomic_int n (ZMod p)]; exact hρ
  · rw [← map_cyclotomic_int n (ZMod p), derivative_map]; exact hρ'

end NFz4


section NFz5

variable (Fc : BPoly ℚ) [hF : Fact (Irreducible (toPoly (fKc Fc)))] (m n : ℕ)
  [hz : Fact (Irreducible (toPoly (cycK Fc m n)))]

/-- **The local-certificate oracle over `Kₘ(ζₙ)` eventually answers**: the coefficients (in `Kₘ`)
the query needs specialized, at residues outside `kfBad`. -/
theorem kfz_query_els (hn : 2 ≤ n) {fK : CPoly (NFz Fc m n)} (hd : 0 < fK.length - 1)
    (hlc : fK.getD (fK.length - 1) 0 ≠ 0) (hsq : Squarefree (toPoly fK))
    (hcop : Nat.Coprime n (fK.length - 1)) (l : List (NFz Fc m n × NFz Fc m n × ℕ))
    (hΓ : ∀ q : Fin l.length, (l.get q).2.1 ≠ 0 ∧ (l.get q).2.1 ^ n = evalC fK (l.get q).1)
    (hinj : Function.Injective fun q : Fin l.length ↦ ((l.get q).1, (l.get q).2.1)) :
    ∃ Els : List (KF Fc m), ∀ rs : ℕ → ℕ, rs 0 ∉ kfBad Fc → (∀ x ∈ Els, specB Fc rs m x = true) →
      ∃ B0, ∀ B, B0 ≤ B →
        (torsOracleC (redAtNF Fc m n rs) (localCert fK n) (primesBelow B) B fK n l).isSome := by
  have hcp : IsCoprime (toPoly fK) (derivative (toPoly fK)) :=
    PerfectField.separable_iff_squarefree.mpr hsq
  obtain ⟨u, v, huv⟩ := hcp
  set uL : CPoly (NFz Fc m n) := (List.range (u.natDegree + 1)).map u.coeff
  set vL : CPoly (NFz Fc m n) := (List.range (v.natDegree + 1)).map v.coeff
  have huL : toPoly uL = u := EllAlgo.toPoly_range_coeff u _ (Or.inr (Nat.lt_succ_self _))
  have hvL : toPoly vL = v := EllAlgo.toPoly_range_coeff v _ (Or.inr (Nat.lt_succ_self _))
  set NEls : List (NFz Fc m n) := fK ++ [(fK.getD (fK.length - 1) 0)⁻¹] ++ uL ++ vL ++
    l.flatMap (fun q ↦ [q.1, q.2.1, q.2.1⁻¹]) ++
    l.flatMap (fun q ↦ l.flatMap fun q' ↦ [(q.1 - q'.1)⁻¹, (q.2.1 - q'.2.1)⁻¹]) with hNEls
  refine ⟨NEls.flatMap fun z ↦ z.1, fun rs h0 hE ↦ ?_⟩
  have ev : ∀ z ∈ NEls, EvOk (GNF Fc m n rs) (fun p _ ↦ RfNF Fc m n rs p) z := fun z hz ↦
    evOk_nfz Fc m n rs z fun c hc ↦ hE c (List.mem_flatMap.mpr ⟨z, hz, hc⟩)
  have hgm : ∀ q : Fin l.length, l.get q ∈ l := fun q ↦ List.get_mem l q
  refine torsOracleLocalN_eventually n hn (redAtNF Fc m n rs) (GNF Fc m n rs)
    (fun p hp ↦ by
      by_cases hpp : p.Prime
      · exact GNF_dvd Fc m n (by omega) rs p hpp hp
      · exfalso
        have := hp.1
        unfold redAtNF at this
        rw [dif_neg hpp] at this
        exact absurd this (by simp))
    (GNF_infinite Fc m n (by omega) rs h0) (fun p _ ↦ RfNF Fc m n rs p)
    (fun p _ hp ↦ redAtNF_eq_RfNF Fc m n rs p hp)
    (fun p _ R h ↦ MTower.redAtNF_valid (Fc := Fc) m n rs p R h) hd hlc hcop (u := uL) (v := vL)
    (by rw [huL, hvL]; linear_combination huv) l hΓ hinj
    (fun c hc ↦ ev c (by simp [hNEls, hc])) (ev _ (by simp [hNEls]))
    (fun c hc ↦ ev c (by simp [hNEls, hc])) (fun c hc ↦ ev c (by simp [hNEls, hc]))
    (fun q ↦ ev _ ?_) (fun q ↦ ev _ ?_) (fun q ↦ ev _ ?_) (fun q q' _ ↦ ev _ ?_)
    (fun q q' _ _ ↦ ev _ ?_)
  · exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, hgm q, by simp⟩))
  · exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, hgm q, by simp⟩))
  · exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, hgm q, by simp⟩))
  · exact List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, hgm q, List.mem_flatMap.mpr ⟨_, hgm q', by simp⟩⟩)
  · exact List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, hgm q, List.mem_flatMap.mpr ⟨_, hgm q', by simp⟩⟩)

end NFz5

end Curves.MT
