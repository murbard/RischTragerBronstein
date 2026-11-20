import RischTragerBronstein.Mixed.KRSpec
import RischTragerBronstein.Mixed.KYField

/-!
# Good primes for the code fields `Kₘ ⊗ N`

As `Mixed/KRSpec` for `Kₘ(ζₙ)`, for the number-field extensions `NFM m M = Kₘ[X]/(M)` of the
code fields (`redAtNFM_spec`, `evOk_nfm`).
-/

open Polynomial CPoly CPoly.Kron

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup

section NFm2

variable (Fc : BPoly ℚ) [hF : Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (M : CPoly ℚ)
  [hz : Fact (Irreducible (toPoly (liftQ Fc m M)))]

/-- **The shape of the reductions of `Kₘ ⊗ N`.** -/
lemma redAtNFM_spec (rs : ℕ → ℕ) (p : ℕ) [Fact p.Prime] (h : (redAtNFM Fc m M rs p).isSome) :
    (s0opt Fc rs p).isSome ∧ ∃ ρ : ZMod p,
      redAtNFM Fc m M rs p = some (nfkFns (redKF Fc p ((s0opt Fc rs p).getD 0)
        (fun j ↦ (rs j : ZMod p)) m) (liftQ Fc m M) ρ) ∧
      (∀ c ∈ liftQ Fc m M, (redKF Fc p ((s0opt Fc rs p).getD 0) (fun j ↦ (rs j : ZMod p)) m).ok c
        = true) ∧
      evalC ((liftQ Fc m M).map (redKF Fc p ((s0opt Fc rs p).getD 0)
        (fun j ↦ (rs j : ZMod p)) m).red) ρ = 0 := by
  have hKF : (redAtKF Fc m rs p).isSome := by
    unfold redAtNFM at h
    rw [dif_pos Fact.out] at h
    cases hK : redAtKF Fc m rs p with
    | none => rw [hK] at h; exact absurd h (by simp)
    | some R => rfl
  have hs0 := s0opt_of_redAtKF Fc m rs p hKF
  refine ⟨hs0, ?_⟩
  have hR := redAtKF_eq Fc m rs p hs0
  unfold redAtNFM at h ⊢
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

end NFm2


section NFm3

variable (Fc : BPoly ℚ) [hF : Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (M : CPoly ℚ)
  [hz : Fact (Irreducible (toPoly (liftQ Fc m M)))]

/-- The reductions of `Kₘ ⊗ N` as a total family. -/
def RfNM (rs : ℕ → ℕ) (p : ℕ) [Fact p.Prime] : RedFns p (NFM Fc m M) :=
  (redAtNFM Fc m M rs p).getD ⟨fun _ ↦ false, fun _ ↦ 0⟩

/-- **The good primes of `Kₘ ⊗ N`**: the reduction exists and `p > n`. -/
def GNM (rs : ℕ → ℕ) (T : ℕ) (p : ℕ) : Prop := (redAtNFM Fc m M rs p).isSome = true ∧ T < p

lemma redAtNFM_eq_RfNM (rs : ℕ → ℕ) (p : ℕ) [Fact p.Prime] (T : ℕ) (h : GNM Fc m M rs T p) :
    redAtNFM Fc m M rs p = some (RfNM Fc m M rs p) := by
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp h.1
  rw [RfNM, hR]; rfl

/-- Elements of `Kₘ ⊗ N` with specializable coefficients reduce well at all large good primes. -/
lemma evOk_nfm (rs : ℕ → ℕ) (T : ℕ) (z : NFM Fc m M) (hz : ∀ c ∈ z.1, specB Fc rs m c = true) :
    EvOk (GNM Fc m M rs T) (fun p _ ↦ RfNM Fc m M rs p) z := by
  set Gb : ℕ → Prop := fun p ↦ (s0opt Fc rs p).isSome = true
  set s0 : (p : ℕ) → ZMod p := fun p ↦ (s0opt Fc rs p).getD 0
  have hGb : ∀ (p : ℕ) [Fact p.Prime], Gb p → baseOK Fc p (s0 p) (rs 0 : ZMod p) = true :=
    fun p _ hp ↦ baseOK_s0opt Fc rs p hp
  have hev : ∀ c ∈ z.1, EvOk Gb (fun p _ ↦ redKF Fc p (s0 p) (fun j ↦ (rs j : ZMod p)) m) c :=
    fun c hc ↦ specB_evOk Fc rs Gb s0 hGb m c (hz c hc)
  obtain ⟨T1, hT⟩ := evOk_list _ _ _ hev
  refine ⟨T1, fun p _ hp hpT ↦ ?_⟩
  obtain ⟨hs0, ρ, hρ, -, -⟩ := redAtNFM_spec Fc m M rs p hp.1
  have hR : RfNM Fc m M rs p = nfkFns (redKF Fc p (s0 p) (fun j ↦ (rs j : ZMod p)) m)
      (liftQ Fc m M) ρ := by
    have := redAtNFM_eq_RfNM Fc m M rs p T hp
    rw [hρ] at this
    exact (Option.some.inj this).symm
  show (RfNM Fc m M rs p).ok z = true
  rw [hR]
  simp only [nfkFns, List.all_eq_true]
  exact hT p hs0 hpT

end NFm3


/-- **A primitive `n`-th root of unity with a residue forces `n ∣ p − 1`.** -/
lemma dvd_of_prim_red {K : Type*} [Field K] [CharZero K] {p : ℕ} [Fact p.Prime] (R : RedFns p K)
    (φ : K →+* ℚ_[p]) (hR : RedValid p R φ) {n : ℕ} (hn : 0 < n) (hpn : n < p) (ζ : K)
    (hζ : IsPrimitiveRoot ζ n) (hok : R.ok ζ = true) : n ∣ p - 1 := by
  obtain ⟨z, hz, hzr⟩ := hR ζ hok
  have h1 : (cyclotomic n ℚ_[p]).eval (φ ζ) = 0 := by
    have := hζ.isRoot_cyclotomic hn
    rw [IsRoot.def, ← map_cyclotomic n φ, eval_map, eval₂_at_apply] at *
    rw [this, map_zero]
  have h2 : (cyclotomic n ℤ_[p]).eval z = 0 := by
    apply PadicInt.ext
    rw [PadicInt.coe_zero, show (((cyclotomic n ℤ_[p]).eval z : ℤ_[p]) : ℚ_[p]) =
      PadicInt.Coe.ringHom ((cyclotomic n ℤ_[p]).eval z) from rfl, ← eval₂_at_apply, ← eval_map,
      map_cyclotomic]
    rw [show PadicInt.Coe.ringHom z = φ ζ from hz.symm]
    exact h1
  have h3 : (cyclotomic n (ZMod p)).eval (R.red ζ) = 0 := by
    rw [← hzr, ← map_cyclotomic n (PadicInt.toZMod (p := p)), eval_map, eval₂_at_apply, h2,
      map_zero]
  have : NeZero (n : ZMod p) := ⟨by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd; have := Nat.le_of_dvd hn hd; omega⟩
  have hprim : IsPrimitiveRoot (R.red ζ) n := (isRoot_cyclotomic_iff).mp h3
  rw [hprim.eq_orderOf]
  exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one (hprim.ne_zero hn.ne'))

section NFm4

variable (Fc : BPoly ℚ) [hF : Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (M : CPoly ℚ)
  [hz : Fact (Irreducible (toPoly (liftQ Fc m M)))]

lemma coeff_liftQ (i : ℕ) :
    (toPoly (liftQ Fc m M)).coeff i = (((toPoly M).coeff i : ℚ) : KF Fc m) := by
  rw [toPoly_liftQ, coeff_map, eq_ratCast]

/-- **The reduction of `M` over `Kₘ` is its residue modulo `p`** (up to the clearing constant). -/
lemma toPoly_liftQ_red (p : ℕ) [Fact p.Prime] (R0 : RedFns p (KF Fc m)) (φ : KF Fc m →+* ℚ_[p])
    (hR0 : RedValid p R0 φ) (hok : ∀ c ∈ liftQ Fc m M, R0.ok c = true) (D : ℤ) (mZ : ℤ[X])
    (hmZ : mZ.map (Int.castRingHom ℚ) = C (D : ℚ) * toPoly M) (hD : (D : ZMod p) ≠ 0)
    (hden : ∀ q ∈ M, q.den < p) :
    C (D : ZMod p) * toPoly ((liftQ Fc m M).map R0.red) = mZ.map (Int.castRingHom (ZMod p)) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hMc : ∀ i, ((toPoly M).coeff i).den % p ≠ 0 := fun i ↦ by
    rw [coeff_toPoly]; exact den_getD_mod hp1 hden i
  ext i
  rw [coeff_C_mul, coeff_toPoly, coeff_map, eq_intCast]
  have hc := congrArg (fun P ↦ P.coeff i) hmZ
  simp only [coeff_map, coeff_C_mul, eq_intCast] at hc
  have hZ : ((mZ.coeff i : ℤ) : ZMod p) = (D : ZMod p) * Jac.ratMod p ((toPoly M).coeff i) := by
    rw [← ratMod_int, hc, ratMod_mul (by simp [Nat.mod_eq_of_lt hp1]) (hMc i)
      (by rw [← hc]; simp [Nat.mod_eq_of_lt hp1]), ratMod_int]
  rw [hZ]
  congr 1
  by_cases hi : i < (liftQ Fc m M).length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
    have hcq : (liftQ Fc m M)[i] = (((toPoly M).coeff i : ℚ) : KF Fc m) := by
      rw [← coeff_liftQ, coeff_toPoly, List.getD_eq_getElem _ _ hi]
    rw [hcq, red_ratCast R0 φ hR0 _ (by rw [← hcq]; exact hok _ (List.getElem_mem hi)) (hMc i)]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    have h0 : (toPoly (liftQ Fc m M)).coeff i = 0 := by
      rw [coeff_toPoly, List.getD_eq_default _ _ (by omega)]
    rw [coeff_liftQ] at h0
    have : (toPoly M).coeff i = 0 := by exact_mod_cast h0
    rw [this, ratMod_zero]

/-- **Infinitely many good primes for `Kₘ ⊗ N`** at residues outside `kfBad`. -/
lemma GNM_infinite (rs : ℕ → ℕ) (h0 : rs 0 ∉ kfBad Fc) (D : ℤ) (hD : D ≠ 0) (mZ : ℤ[X])
    (hmZ : mZ.map (Int.castRingHom ℚ) = C (D : ℚ) * toPoly M)
    (hsepM : (mZ.map (Int.castRingHom ℚ)).Separable) (hdegM : 0 < mZ.natDegree) (T : ℕ) :
    ∀ N, ∃ p, p.Prime ∧ GNM Fc m M rs T p ∧ N < p := by
  intro N
  obtain ⟨hsep, hdeg⟩ := kfBad_good Fc (rs 0) h0
  obtain ⟨D0, hD0, mZ0, hmZ0, hsepZ, hdegZ⟩ := clear_good _ hsep hdeg
  obtain ⟨T0, hT0⟩ := baseOK_of_root Fc (rs 0) (fKc_hQ Fc _) D0 hD0 mZ0 hmZ0
  set Gb : ℕ → Prop := fun p ↦ (s0opt Fc rs p).isSome = true
  set s0 : (p : ℕ) → ZMod p := fun p ↦ (s0opt Fc rs p).getD 0
  have hGb : ∀ (p : ℕ) [Fact p.Prime], Gb p → baseOK Fc p (s0 p) (rs 0 : ZMod p) = true :=
    fun p _ hp ↦ baseOK_s0opt Fc rs p hp
  have hev : ∀ c ∈ liftQ Fc m M,
      EvOk Gb (fun p _ ↦ redKF Fc p (s0 p) (fun j ↦ (rs j : ZMod p)) m) c := fun c hc ↦ by
    obtain ⟨i, rfl⟩ := mem_coeff _ c hc
    rw [coeff_liftQ]
    exact specB_evOk Fc rs Gb s0 hGb m _ (specB_ratCast Fc rs m _)
  obtain ⟨T1, hT1⟩ := evOk_list _ _ _ hev
  set T2 := (M.map (·.den)).sum
  obtain ⟨p, hpT, hp, ⟨_, s, hs, hs'⟩, ⟨_, ρ, hρ, hρ'⟩⟩ :=
    exists_simple_roots_prime mZ0 mZ hsepZ hsepM hdegZ hdegM
      (N + T + T0 + T1 + T2 + D.natAbs + 1)
  haveI : Fact p.Prime := ⟨hp⟩
  have hb := hT0 p (by omega) s hs hs'
  have hs0 := s0opt_isSome Fc rs p s hb
  have hall : ∀ c ∈ liftQ Fc m M,
      (redKF Fc p ((s0opt Fc rs p).getD 0) (fun j ↦ (rs j : ZMod p)) m).ok c = true :=
    hT1 p hs0 (by omega)
  obtain ⟨φ, hφ⟩ := redKF_valid Fc p _ (fun j ↦ (rs j : ZMod p)) (baseOK_s0opt Fc rs p hs0) m
  have hDp : (D : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact not_dvd_of_natAbs_lt hD (by omega)
  have hrel := toPoly_liftQ_red Fc m M p _ φ hφ hall D mZ hmZ hDp
    (fun q hq ↦ by have := den_lt_sum hq; omega)
  refine ⟨p, hp, ⟨?_, by omega⟩, by omega⟩
  unfold redAtNFM
  rw [dif_pos hp]
  rw [redAtKF_eq Fc m rs p hs0]
  simp only
  rw [if_pos (List.all_eq_true.mpr hall), Option.isSome_map, range_bind_eq, List.find?_isSome]
  refine ⟨ρ, List.mem_map.mpr ⟨ρ.val, List.mem_range.mpr (ZMod.val_lt ρ),
    ZMod.natCast_zmod_val ρ⟩, ?_⟩
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, evalC_eq, toPoly_deriv]
  refine ⟨?_, ?_⟩
  · have := congrArg (fun P ↦ P.eval ρ) hrel
    simp only [eval_mul, eval_C] at this
    rw [hρ] at this
    exact (mul_eq_zero.mp this).resolve_left hDp
  · intro hd
    have := congrArg (fun P ↦ (derivative P).eval ρ) hrel
    simp only [derivative_C_mul, eval_mul, eval_C, hd, mul_zero] at this
    rw [← derivative_map] at hρ'
    exact hρ' this.symm

end NFm4

section NFm5

variable (Fc : BPoly ℚ) [hF : Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (M : CPoly ℚ)
  [hz : Fact (Irreducible (toPoly (liftQ Fc m M)))]

/-- **The local-certificate oracle over `Kₘ ⊗ N` eventually answers** (`N ∋ ζₙ`). -/
theorem kfm_query_els (n : ℕ) (hn : 2 ≤ n) (ζ : NFM Fc m M) (hζ : IsPrimitiveRoot ζ n)
    (D : ℤ) (hD : D ≠ 0) (mZ : ℤ[X])
    (hmZ : mZ.map (Int.castRingHom ℚ) = C (D : ℚ) * toPoly M)
    (hsepM : (mZ.map (Int.castRingHom ℚ)).Separable) (hdegM : 0 < mZ.natDegree)
    {fK : CPoly (NFM Fc m M)} (hd : 0 < fK.length - 1)
    (hlc : fK.getD (fK.length - 1) 0 ≠ 0) (hsq : Squarefree (toPoly fK))
    (hcop : Nat.Coprime n (fK.length - 1)) {r : ℕ} (α β : Fin r → NFM Fc m M) (mq : Fin r → ℕ)
    (hv : ∀ q, β q ≠ 0 ∧ β q ^ n = (toPoly fK).eval (α q))
    (hinj : Function.Injective fun q ↦ (α q, β q)) :
    ∃ Els : List (KF Fc m), ∀ rs : ℕ → ℕ, rs 0 ∉ kfBad Fc → (∀ x ∈ Els, specB Fc rs m x = true) →
      ∃ B0, ∀ B, B0 ≤ B →
        (torsOracleC (redAtNFM Fc m M rs) (localCert fK n) (primesBelow B) B fK n
          (Sup.gammaL α β mq 1)).isSome := by
  set l := Sup.gammaL α β mq 1 with hl
  have hlen : l.length = r := by simp [hl, Sup.gammaL]
  set e : Fin l.length ≃ Fin r := finCongr hlen with he
  have hget : ∀ q : Fin l.length, l.get q = (α (e q), β (e q), 1 * mq (e q)) := by
    intro q
    simp [hl, Sup.gammaL, he]
    exact ⟨rfl, rfl, rfl⟩
  have hΓ : ∀ q : Fin l.length, (l.get q).2.1 ≠ 0 ∧ (l.get q).2.1 ^ n = evalC fK (l.get q).1 :=
    fun q ↦ by rw [hget q, evalC_eq]; exact hv (e q)
  have hinj' : Function.Injective fun q : Fin l.length ↦ ((l.get q).1, (l.get q).2.1) :=
    fun q q' h ↦ by simp only [hget] at h; exact e.injective (hinj h)
  have hcp : IsCoprime (toPoly fK) (derivative (toPoly fK)) :=
    PerfectField.separable_iff_squarefree.mpr hsq
  obtain ⟨u, v, huv⟩ := hcp
  set uL : CPoly (NFM Fc m M) := (List.range (u.natDegree + 1)).map u.coeff
  set vL : CPoly (NFM Fc m M) := (List.range (v.natDegree + 1)).map v.coeff
  have huL : toPoly uL = u := EllAlgo.toPoly_range_coeff u _ (Or.inr (Nat.lt_succ_self _))
  have hvL : toPoly vL = v := EllAlgo.toPoly_range_coeff v _ (Or.inr (Nat.lt_succ_self _))
  set NEls : List (NFM Fc m M) := [ζ] ++ fK ++ [(fK.getD (fK.length - 1) 0)⁻¹] ++ uL ++ vL ++
    l.flatMap (fun q ↦ [q.1, q.2.1, q.2.1⁻¹]) ++
    l.flatMap (fun q ↦ l.flatMap fun q' ↦ [(q.1 - q'.1)⁻¹, (q.2.1 - q'.2.1)⁻¹]) with hNEls
  refine ⟨NEls.flatMap fun z ↦ z.1, fun rs h0 hE ↦ ?_⟩
  have ev : ∀ T, ∀ z ∈ NEls, EvOk (GNM Fc m M rs T) (fun p _ ↦ RfNM Fc m M rs p) z :=
    fun T z hz ↦ evOk_nfm Fc m M rs T z fun c hc ↦ hE c (List.mem_flatMap.mpr ⟨z, hz, hc⟩)
  obtain ⟨Tζ, hTζ⟩ := ev 0 ζ (by simp [hNEls])
  set T := Tζ + n with hT
  have hgm : ∀ q : Fin l.length, l.get q ∈ l := fun q ↦ List.get_mem l q
  refine torsOracleLocalN_eventually n hn (redAtNFM Fc m M rs) (GNM Fc m M rs T)
    (fun p hp ↦ by
      have hpp : p.Prime := by
        by_contra hpp
        have := hp.1
        unfold redAtNFM at this
        rw [dif_neg hpp] at this
        exact absurd this (by simp)
      haveI : Fact p.Prime := ⟨hpp⟩
      obtain ⟨φ, hφ⟩ := redAtNFM_valid Fc m M rs p _ (redAtNFM_eq_RfNM Fc m M rs p T hp)
      exact dvd_of_prim_red _ φ hφ (by omega) (by have := hp.2; omega) ζ hζ
        (hTζ p ⟨hp.1, by have := hp.2; omega⟩ (by have := hp.2; omega)))
    (GNM_infinite Fc m M rs h0 D hD mZ hmZ hsepM hdegM T) (fun p _ ↦ RfNM Fc m M rs p)
    (fun p _ hp ↦ redAtNFM_eq_RfNM Fc m M rs p T hp)
    (fun p _ R h ↦ redAtNFM_valid Fc m M rs p R h) hd hlc hcop (u := uL) (v := vL)
    (by rw [huL, hvL]; linear_combination huv) l hΓ hinj'
    (fun c hc ↦ ev T c (by simp [hNEls, hc])) (ev T _ (by simp [hNEls]))
    (fun c hc ↦ ev T c (by simp [hNEls, hc])) (fun c hc ↦ ev T c (by simp [hNEls, hc]))
    (fun q ↦ ev T _ ?_) (fun q ↦ ev T _ ?_) (fun q ↦ ev T _ ?_) (fun q q' _ ↦ ev T _ ?_)
    (fun q q' _ _ ↦ ev T _ ?_)
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

end NFm5

end Curves.MT
