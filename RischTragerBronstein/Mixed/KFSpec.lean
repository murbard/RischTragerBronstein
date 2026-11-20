import RischTragerBronstein.Mixed.KEReduce
import RischTragerBronstein.Algebraic.SupSimpleRoot
import RischTragerBronstein.Algebraic.SupLocalEvent

/-!
# Good primes for the code fields: specialization of the base curve

`redX p c₀` reduces `ℚ(x)` at `x ↦ c₀`; for `a = P/Q` with `Q(c₀) ≠ 0` the residue is the reduction
of the rational number `a(c₀) = rfVal a c₀` (`redX_red`). Hence, when the specialized curve
`F(c₀, Y)` (cleared to `mZ ∈ ℤ[Y]`) is separable, infinitely many primes admit a simple root `s₀`
of the reduced curve (`baseOK_infinite`), so `redAtKF` answers at infinitely many primes.
-/

open Polynomial CPoly CPoly.Kron

set_option linter.unusedSectionVars false

namespace Sup

variable {p : ℕ} [Fact p.Prime]

lemma ratMod_of_lift {c : ℚ} (hc : c.den % p ≠ 0) {w : ℤ_[p]} (hw : (w : ℚ_[p]) = c) :
    PadicInt.toZMod w = Jac.ratMod p c := by
  obtain ⟨w', hw', hwr⟩ := Jac.exists_lift_rat (p := p) hc
  rw [← hwr, show w = w' from PadicInt.ext (hw.trans hw'.symm)]

lemma ratMod_mul {a b : ℚ} (ha : a.den % p ≠ 0) (hb : b.den % p ≠ 0) (hab : (a * b).den % p ≠ 0) :
    Jac.ratMod p (a * b) = Jac.ratMod p a * Jac.ratMod p b := by
  obtain ⟨wa, ha1, ha2⟩ := Jac.exists_lift_rat (p := p) ha
  obtain ⟨wb, hb1, hb2⟩ := Jac.exists_lift_rat (p := p) hb
  rw [← ha2, ← hb2, ← map_mul]
  exact (ratMod_of_lift hab (by rw [PadicInt.coe_mul, ha1, hb1]; push_cast; rfl)).symm

lemma ratMod_int (k : ℤ) : Jac.ratMod p (k : ℚ) = (k : ZMod p) := by
  simp [Jac.ratMod]

lemma ratMod_zero : Jac.ratMod p 0 = 0 := by simp [Jac.ratMod]

end Sup

namespace Curves.MT

open Sup

/-- The value of `a = P/Q ∈ ℚ(x)` at `x = c`. -/
def rfVal (a : RFC.RatFuncC ℚ) (c : ℚ) : ℚ := evalC (RFC.canon a).1 c / evalC (RFC.canon a).2 c

lemma eval₂_natCast_padic {p : ℕ} [Fact p.Prime] (l : CPoly ℚ) (c : ℕ) :
    (toPoly l).eval₂ (algebraMap ℚ ℚ_[p]) (((c : ℤ_[p]) : ℚ_[p])) =
      algebraMap ℚ ℚ_[p] (evalC l (c : ℚ)) := by
  have hc : (((c : ℤ_[p]) : ℚ_[p])) = algebraMap ℚ ℚ_[p] (c : ℚ) := by simp
  rw [evalC_eq, hc, eval₂_at_apply]

/-- **The residue of `ℚ(x)` at `x ↦ c₀`** is the reduction of the value at `c₀`. -/
lemma redX_red {p : ℕ} [Fact p.Prime] (c0 : ℕ) (a : RFC.RatFuncC ℚ)
    (hok : (redX p (c0 : ZMod p)).ok a = true) (hv : (rfVal a c0).den % p ≠ 0) :
    (redX p (c0 : ZMod p)).red a = Jac.ratMod p (rfVal a c0) := by
  simp only [redX, rfFns, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at hok ⊢
  obtain ⟨⟨hP, hQ⟩, hQr⟩ := hok
  have hcz : PadicInt.toZMod ((c0 : ℤ_[p])) = (c0 : ZMod p) := by simp
  obtain ⟨wP, hwP, hwPr⟩ := lift_list (ratFns p) _ (ratFns_valid p) (c0 : ℤ_[p]) _ hP
  obtain ⟨wQ, hwQ, hwQr⟩ := lift_list (ratFns p) _ (ratFns_valid p) (c0 : ℤ_[p]) _ hQ
  obtain ⟨wv, hwv, hwvr⟩ := Jac.exists_lift_rat (p := p) hv
  rw [eval₂_natCast_padic] at hwP hwQ
  rw [hcz] at hwPr hwQr
  have hQ0 : evalC (RFC.canon a).2 (c0 : ℚ) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hwQ
    have : wQ = 0 := PadicInt.ext (by rw [← hwQ]; rfl)
    rw [this, map_zero] at hwQr
    exact hQr hwQr.symm
  have hPv : evalC (RFC.canon a).1 (c0 : ℚ) = rfVal a c0 * evalC (RFC.canon a).2 (c0 : ℚ) := by
    unfold rfVal; field_simp
  have hw : wP = wv * wQ := PadicInt.ext (by
    rw [PadicInt.coe_mul, ← hwP, hwv, ← hwQ, hPv]
    push_cast; rfl)
  rw [← hwPr, ← hwQr, hw, map_mul, hwvr, mul_div_assoc, div_self (hwQr ▸ hQr), mul_one]

variable (Fc : BPoly ℚ)

/-- The specialized base curve `F(c₀, Y)`. -/
def fSpec (c0 : ℚ) : CPoly ℚ := (fKc Fc).map (rfVal · c0)

lemma getD_map_zero {α β : Type*} [Zero α] [Zero β] (f : α → β) (hf : f 0 = 0) (l : List α)
    (i : ℕ) : (l.map f).getD i 0 = f (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [hf]

lemma den_getD_mod {l : List ℚ} {p : ℕ} (hp : 1 < p) (h : ∀ q ∈ l, q.den < p) (i : ℕ) :
    (l.getD i 0).den % p ≠ 0 := by
  rw [List.getD_eq_getElem?_getD]
  rcases hl : l[i]? with _ | q
  · simp [Nat.mod_eq_of_lt hp]
  · simp only [Option.getD_some]
    rw [Nat.mod_eq_of_lt (h q (List.mem_of_getElem? hl))]
    exact q.den_nz

lemma den_lt_sum {l : List ℚ} {q : ℚ} (hq : q ∈ l) : q.den ≤ (l.map (·.den)).sum :=
  List.le_sum_of_mem (List.mem_map.mpr ⟨q, hq, rfl⟩)

/-- **Infinitely many primes admit a simple root of the reduced base curve**, when the specialized
curve `F(c₀, Y)` is separable (cleared to `mZ ∈ ℤ[Y]`). -/
theorem baseOK_infinite (c0 : ℕ) (hQ : ∀ a ∈ fKc Fc, evalC (RFC.canon a).2 (c0 : ℚ) ≠ 0)
    (D : ℤ) (hD : D ≠ 0) (mZ : ℤ[X])
    (hmZ : mZ.map (Int.castRingHom ℚ) = C (D : ℚ) * toPoly (fSpec Fc c0))
    (hsep : (mZ.map (Int.castRingHom ℚ)).Separable) (hdeg : 0 < mZ.natDegree) (T : ℕ) :
    ∃ p, T < p ∧ ∃ hp : p.Prime, ∃ s : ZMod p,
      (haveI : Fact p.Prime := ⟨hp⟩; baseOK Fc p s (c0 : ZMod p)) = true := by
  -- integrality of the coefficients
  have hev : ∀ a ∈ fKc Fc, EvOk (fun _ ↦ True) (fun p _ ↦ rfFns p (ratFns p) (((c0 : ℤ)) : ZMod p))
      a := fun a ha ↦
    rf_evOk (fun _ ↦ True) (fun p _ ↦ ratFns p) (fun p _ _ ↦ ⟨_, ratFns_valid p⟩) (c0 : ℤ) a
      (fun b _ ↦ rat_evOk _ b) (by rw [← evalC_eq]; push_cast; exact hQ a ha) (rat_evOk _ _)
  obtain ⟨T1, hT1⟩ := evOk_list _ _ _ hev
  set T2 := ((fSpec Fc c0).map (·.den)).sum
  obtain ⟨p, hpT, hp, s, hs, hs'⟩ := exists_simple_root_prime_sep mZ hsep hdeg
    (T + T1 + T2 + D.natAbs + 1)
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  refine ⟨p, by omega, hp, s, ?_⟩
  show baseOK Fc p s (c0 : ZMod p) = true
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

variable [hF : Fact (Irreducible (toPoly (fKc Fc)))]

/-- The simple root found by `redAtKF` at `p`. -/
def s0opt (rs : ℕ → ℕ) (p : ℕ) : Option (ZMod p) :=
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    ((List.range p).map fun a : ℕ ↦ (a : ZMod p)).find? fun i ↦ baseOK Fc p i (rs 0 : ZMod p)
  else none

lemma range_bind_eq (p : ℕ) :
    (do let a ← List.range p; pure (a : ZMod p) : List (ZMod p)) =
      (List.range p).map fun a : ℕ ↦ (a : ZMod p) := by
  simp [List.map_eq_flatMap]

lemma redAtKF_eq (m : ℕ) (rs : ℕ → ℕ) (p : ℕ) [Fact p.Prime] (h : (s0opt Fc rs p).isSome) :
    redAtKF Fc m rs p = some (redKF Fc p ((s0opt Fc rs p).getD 0)
      (fun j ↦ (rs j : ZMod p)) m) := by
  unfold s0opt at h ⊢
  unfold redAtKF
  rw [dif_pos Fact.out] at h ⊢
  rw [dif_pos Fact.out]
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
  rw [hi, range_bind_eq, hi]; rfl

lemma baseOK_s0opt (rs : ℕ → ℕ) (p : ℕ) [Fact p.Prime] (h : (s0opt Fc rs p).isSome) :
    baseOK Fc p ((s0opt Fc rs p).getD 0) (rs 0 : ZMod p) = true := by
  unfold s0opt at h ⊢
  rw [dif_pos Fact.out] at h ⊢
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
  rw [hi]
  have := List.find?_some hi
  simpa using this

lemma s0opt_isSome (rs : ℕ → ℕ) (p : ℕ) [Fact p.Prime] (s : ZMod p)
    (h : baseOK Fc p s (rs 0 : ZMod p) = true) : (s0opt Fc rs p).isSome := by
  unfold s0opt
  rw [dif_pos Fact.out, List.find?_isSome]
  exact ⟨s, List.mem_map.mpr ⟨s.val, List.mem_range.mpr (ZMod.val_lt s),
    ZMod.natCast_zmod_val s⟩, h⟩

/-- **Specializable elements**: every denominator met in the recursive reduction is nonzero at
the chosen integer residues (`x ↦ rs 0`, `tᵢ ↦ rs (i + 1)`), recursively for the inverses. -/
def specB (rs : ℕ → ℕ) : (m : ℕ) → KF Fc m → Bool
  | 0 => fun z ↦ (show NFK.NF (fKc Fc) from z).1.all fun a ↦
      evalC (RFC.canon a).2 ((rs 0 : ℕ) : ℚ) != 0
  | m + 1 => fun x ↦
      let x' : RFC.RatFuncC (KF Fc m) := x
      ((RFC.canon x').1 ++ (RFC.canon x').2).all (specB rs m) &&
      evalC (RFC.canon x').2 ((rs (m + 1) : ℕ) : KF Fc m) != 0 &&
      specB rs m (evalC (RFC.canon x').2 ((rs (m + 1) : ℕ) : KF Fc m))⁻¹

/-- **Specializable elements reduce well at all large good primes.** -/
theorem specB_evOk (rs : ℕ → ℕ) (G : ℕ → Prop) (s0 : (p : ℕ) → ZMod p)
    (hG : ∀ (p : ℕ) [Fact p.Prime], G p → baseOK Fc p (s0 p) (rs 0 : ZMod p) = true) :
    ∀ m (x : KF Fc m), specB Fc rs m x = true →
      EvOk G (fun p _ ↦ redKF Fc p (s0 p) (fun j ↦ (rs j : ZMod p)) m) x := by
  intro m
  induction m with
  | zero =>
    intro x h
    simp only [specB, List.all_eq_true, bne_iff_ne, ne_eq] at h
    refine nfk_evOk G (fun p _ ↦ redX p (rs 0 : ZMod p)) (fKc Fc) s0
      (show NFK.NF (fKc Fc) from x) fun a ha ↦ ?_
    have := rf_evOk G (fun p _ ↦ ratFns p) (fun p _ _ ↦ ⟨_, ratFns_valid p⟩) ((rs 0 : ℕ) : ℤ) a
      (fun b _ ↦ rat_evOk G b) (by rw [← evalC_eq]; push_cast; exact h a ha) (rat_evOk G _)
    simp only [Int.cast_natCast] at this
    exact this
  | succ m ih =>
    intro x h
    have h' : (((RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).1 ++
        (RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).2).all (specB Fc rs m) &&
      evalC (RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).2 ((rs (m + 1) : ℕ) : KF Fc m) != 0 &&
      specB Fc rs m (evalC (RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).2
        ((rs (m + 1) : ℕ) : KF Fc m))⁻¹) = true := h
    simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h'
    obtain ⟨⟨hco, hQ⟩, hinv⟩ := h'
    have := rf_evOk G (fun p _ ↦ redKF Fc p (s0 p) (fun j ↦ (rs j : ZMod p)) m)
      (fun p _ hp ↦ redKF_valid Fc p (s0 p) (fun j ↦ (rs j : ZMod p)) (hG p hp) m) ((rs (m + 1) : ℕ) : ℤ)
      (show RFC.RatFuncC (KF Fc m) from x)
      (fun b hb ↦ ih b (hco b hb))
      (by rw [← evalC_eq]; push_cast; exact hQ)
      (by rw [← evalC_eq]; push_cast; exact ih _ hinv)
    simp only [Int.cast_natCast] at this
    exact this

set_option maxHeartbeats 1600000 in
/-- **The local-certificate oracle eventually answers over the code fields** (square roots): for
residues `rs` at which the base curve specializes to a separable `F(rs 0, Y)` and the query data
are specializable (`specB`). -/
theorem kf_torsLocal_eventually (m : ℕ) (rs : ℕ → ℕ)
    (hQ : ∀ a ∈ fKc Fc, evalC (RFC.canon a).2 ((rs 0 : ℕ) : ℚ) ≠ 0)
    (D : ℤ) (hD : D ≠ 0) (mZ : ℤ[X])
    (hmZ : mZ.map (Int.castRingHom ℚ) = C (D : ℚ) * toPoly (fSpec Fc (rs 0)))
    (hsep : (mZ.map (Int.castRingHom ℚ)).Separable) (hdeg : 0 < mZ.natDegree)
    {fK : CPoly (KF Fc m)} (hd : 0 < fK.length - 1) (hlc : fK.getD (fK.length - 1) 0 ≠ 0)
    (hcop : Nat.Coprime 2 (fK.length - 1)) {u v : List (KF Fc m)}
    (hbez : toPoly u * toPoly fK + toPoly v * derivative (toPoly fK) = 1)
    (l : List (KF Fc m × KF Fc m × ℕ))
    (hΓ : ∀ q : Fin l.length, (l.get q).2.1 ≠ 0 ∧ (l.get q).2.1 ^ 2 = evalC fK (l.get q).1)
    (hinj : Function.Injective fun q : Fin l.length ↦ ((l.get q).1, (l.get q).2.1))
    (hsf : ∀ c ∈ fK, specB Fc rs m c = true)
    (hsl : specB Fc rs m (fK.getD (fK.length - 1) 0)⁻¹ = true)
    (hsu : ∀ c ∈ u, specB Fc rs m c = true) (hsv : ∀ c ∈ v, specB Fc rs m c = true)
    (hsα : ∀ q : Fin l.length, specB Fc rs m (l.get q).1 = true)
    (hsβ : ∀ q : Fin l.length, specB Fc rs m (l.get q).2.1 = true)
    (hsβi : ∀ q : Fin l.length, specB Fc rs m ((l.get q).2.1)⁻¹ = true)
    (hsd : ∀ q q' : Fin l.length, (l.get q).1 ≠ (l.get q').1 →
      specB Fc rs m ((l.get q).1 - (l.get q').1)⁻¹ = true)
    (hsb : ∀ q q' : Fin l.length, q ≠ q' → (l.get q).1 = (l.get q').1 →
      specB Fc rs m ((l.get q).2.1 - (l.get q').2.1)⁻¹ = true) :
    ∃ B0, ∀ B, B0 ≤ B →
      (torsOracleC (redAtKF Fc m rs) (localCert fK 2) (primesBelow B) B fK 2 l).isSome := by
  set G : ℕ → Prop := fun p ↦ (s0opt Fc rs p).isSome = true with hGdef
  set s0 : (p : ℕ) → ZMod p := fun p ↦ (s0opt Fc rs p).getD 0 with hs0
  have hG : ∀ (p : ℕ) [Fact p.Prime], G p → baseOK Fc p (s0 p) (rs 0 : ZMod p) = true :=
    fun p _ hp ↦ baseOK_s0opt Fc rs p hp
  have ev : ∀ x : KF Fc m, specB Fc rs m x = true →
      EvOk G (fun p _ ↦ redKF Fc p (s0 p) (fun j ↦ (rs j : ZMod p)) m) x :=
    specB_evOk Fc rs G s0 hG m
  refine torsOracleLocal_eventually (redAtKF Fc m rs) G ?_
    (fun p _ ↦ redKF Fc p (s0 p) (fun j ↦ (rs j : ZMod p)) m)
    (fun p _ hp ↦ redAtKF_eq Fc m rs p hp)
    (fun p _ R h ↦ redAtKF_valid Fc m rs p R h) hd hlc hcop hbez l hΓ hinj
    (fun c hc ↦ ev c (hsf c hc)) (ev _ hsl) (fun c hc ↦ ev c (hsu c hc))
    (fun c hc ↦ ev c (hsv c hc)) (fun q ↦ ev _ (hsα q)) (fun q ↦ ev _ (hsβ q))
    (fun q ↦ ev _ (hsβi q)) (fun q q' h ↦ ev _ (hsd q q' h)) (fun q q' h h' ↦ ev _ (hsb q q' h h'))
  intro N
  obtain ⟨p, hpN, hp, s, hb⟩ := baseOK_infinite Fc (rs 0) hQ D hD mZ hmZ hsep hdeg N
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨p, hp, s0opt_isSome Fc rs p s hb, hpN⟩

end Curves.MT
