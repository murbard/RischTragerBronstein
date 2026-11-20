import RischTragerBronstein.Mixed.KFSpec
import RischTragerBronstein.Algebraic.EllComplete

/-!
# Good residues exist

`fSpec_good`: outside a finite set of residues `c₀`, the specialized base curve `F(c₀, Y)` is
separable of positive degree (the resultant `Res_Y(F, F_Y) ∈ ℚ[x]` and the leading coefficient do
not vanish at `c₀`). `exists_rs`: for any finite list of elements of `Kₘ`, residues `rs` making them
all specializable (`specB`) exist, with `rs 0` outside any given finite set (top-down choice
avoiding the finitely many roots of the denominators).
-/

open Polynomial CPoly CPoly.Kron

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup

/-- The canonical form of a polynomial. -/
lemma canon_poly (c : CPoly ℚ) : toPoly (RFC.canon (RFC.mk c [1])).2 = 1 ∧
    toPoly (RFC.canon (RFC.mk c [1])).1 = toPoly c := by
  obtain ⟨h0, hm, hcop, heq⟩ := RFC.canon_spec (RFC.mk c [1])
  rw [RFC.toRF_mk] at heq
  simp only [toPoly_cons, toPoly_nil, mul_zero, add_zero, map_one, div_one] at heq
  set P := toPoly (RFC.canon (RFC.mk c [1])).1
  set Q := toPoly (RFC.canon (RFC.mk c [1])).2
  have hQ0 : algebraMap ℚ[X] (RatFunc ℚ) Q ≠ 0 := RFC.algebraMap_ne_zero h0
  have hPQ : toPoly c * Q = P := by
    apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
    rw [map_mul, heq, div_mul_cancel₀ _ hQ0]
  have hu : IsUnit Q := hcop.isUnit_of_dvd' ⟨toPoly c, by rw [← hPQ, mul_comm]⟩ dvd_rfl
  have hQ1 : Q = 1 := hm.eq_one_of_isUnit hu
  refine ⟨hQ1, ?_⟩
  rw [← hPQ, hQ1, mul_one]

lemma rfVal_mk (c : CPoly ℚ) (c0 : ℚ) : rfVal (RFC.mk c [1]) c0 = (toPoly c).eval c0 := by
  unfold rfVal
  rw [evalC_eq, evalC_eq, (canon_poly c).1, (canon_poly c).2, eval_one, div_one]

lemma fKc_hQ (Fc : BPoly ℚ) (c0 : ℚ) : ∀ a ∈ fKc Fc, evalC (RFC.canon a).2 c0 ≠ 0 := by
  intro a ha
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp ha
  rw [evalC_eq, (canon_poly c).1, eval_one]
  exact one_ne_zero

lemma toPoly_fSpec (Fc : BPoly ℚ) (c0 : ℚ) :
    toPoly (fSpec Fc c0) = (toB Fc).map (evalRingHom c0) := by
  unfold fSpec fKc
  induction Fc with
  | nil => simp
  | cons a W ih =>
    simp only [List.map_cons, toPoly_cons, toB_cons, Polynomial.map_add, Polynomial.map_mul,
      map_C, map_X, ih, rfVal_mk, coe_evalRingHom]

lemma map_toRF_fKc (Fc : BPoly ℚ) :
    (toPoly (fKc Fc)).map (RFC.toRFHom (K := ℚ)) = (toB Fc).map (algebraMap ℚ[X] (RatFunc ℚ)) := by
  unfold fKc
  induction Fc with
  | nil => simp
  | cons a W ih =>
    simp only [List.map_cons, toPoly_cons, toB_cons, Polynomial.map_add, Polynomial.map_mul,
      map_C, map_X, ih]
    congr 2
    show RFC.toRF (RFC.mk a [1]) = _
    rw [RFC.toRF_mk]
    simp

lemma toRFHom_injective : Function.Injective (RFC.toRFHom (K := ℚ)) := RFC.toRF_injective

/-- **Generic specializations of the base curve are separable.** -/
theorem fSpec_good (Fc : BPoly ℚ) [hF : Fact (Irreducible (toPoly (fKc Fc)))] :
    ∃ S : Set ℕ, S.Finite ∧ ∀ c0 : ℕ, c0 ∉ S →
      (toPoly (fSpec Fc c0)).Separable ∧ 0 < (toPoly (fSpec Fc c0)).natDegree := by
  set F₂ := toB Fc
  set ι := algebraMap ℚ[X] (RatFunc ℚ)
  have hι : Function.Injective ι := IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  have hsep1 : (toPoly (fKc Fc)).Separable := hF.out.separable
  have hsep2 : (F₂.map ι).Separable := by
    rw [← map_toRF_fKc]; exact hsep1.map
  have hdeg1 : 0 < (toPoly (fKc Fc)).natDegree := hF.out.natDegree_pos
  have hdeg2 : F₂.natDegree = (toPoly (fKc Fc)).natDegree := by
    rw [← natDegree_map_eq_of_injective hι, ← map_toRF_fKc,
      natDegree_map_eq_of_injective toRFHom_injective]
  set R := resultant F₂ (derivative F₂)
  have hR0 : R ≠ 0 := by
    intro h0
    have hmap := resultant_map_map F₂ (derivative F₂) F₂.natDegree (derivative F₂).natDegree ι
    rw [← show R = resultant F₂ (derivative F₂) from rfl, h0, map_zero] at hmap
    have hne := resultant_ne_zero (F₂.map ι) _ ((separable_def _).mp hsep2)
    rw [derivative_map, natDegree_map_eq_of_injective hι,
      natDegree_map_eq_of_injective hι] at hne
    exact hne hmap
  obtain ⟨u, v, -, -, huv⟩ := exists_mul_add_mul_eq_C_resultant F₂ (derivative F₂) le_rfl le_rfl
    (Or.inl (by omega))
  have hlc : F₂.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (by
    intro h; rw [h, natDegree_zero] at hdeg2; omega)
  set B := R * F₂.leadingCoeff
  have hB : B ≠ 0 := mul_ne_zero hR0 hlc
  refine ⟨{n : ℕ | (n : ℚ) ∈ B.roots.toFinset}, ?_, fun c0 hc0 ↦ ?_⟩
  · exact (B.roots.toFinset.finite_toSet).preimage Nat.cast_injective.injOn
  · have hev : B.eval (c0 : ℚ) ≠ 0 := fun h ↦ hc0 (by
      simp only [Set.mem_ofPred_eq, Multiset.mem_toFinset]
      exact (mem_roots hB).mpr h)
    rw [eval_mul] at hev
    have hR : R.eval (c0 : ℚ) ≠ 0 := left_ne_zero_of_mul hev
    have hl : F₂.leadingCoeff.eval (c0 : ℚ) ≠ 0 := right_ne_zero_of_mul hev
    rw [toPoly_fSpec]
    refine ⟨?_, ?_⟩
    · rw [separable_def]
      have := congrArg (Polynomial.map (evalRingHom (c0 : ℚ))) huv
      simp only [Polynomial.map_add, Polynomial.map_mul, map_C, ← derivative_map] at this
      refine ⟨C (R.eval (c0 : ℚ))⁻¹ * u.map (evalRingHom (c0 : ℚ)),
        C (R.eval (c0 : ℚ))⁻¹ * v.map (evalRingHom (c0 : ℚ)), ?_⟩
      have e : (evalRingHom (c0 : ℚ)) R = R.eval (c0 : ℚ) := rfl
      rw [e] at this
      calc C (R.eval (c0 : ℚ))⁻¹ * u.map (evalRingHom (c0 : ℚ)) * F₂.map (evalRingHom (c0 : ℚ)) +
            C (R.eval (c0 : ℚ))⁻¹ * v.map (evalRingHom (c0 : ℚ)) *
              derivative (F₂.map (evalRingHom (c0 : ℚ)))
          = C (R.eval (c0 : ℚ))⁻¹ * (F₂.map (evalRingHom (c0 : ℚ)) * u.map (evalRingHom (c0 : ℚ)) +
            derivative (F₂.map (evalRingHom (c0 : ℚ))) * v.map (evalRingHom (c0 : ℚ))) := by ring
        _ = 1 := by rw [this, ← C_mul, inv_mul_cancel₀ hR, C_1]
    · rw [natDegree_map_of_leadingCoeff_ne_zero _ hl]; show 0 < F₂.natDegree; omega

/-- Clearing denominators. -/
lemma exists_clear (P : ℚ[X]) : ∃ D : ℤ, D ≠ 0 ∧ ∃ mZ : ℤ[X],
    mZ.map (Int.castRingHom ℚ) = C (D : ℚ) * P := by
  obtain ⟨b, hb, hbP⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) P
  refine ⟨b, nonZeroDivisors.ne_zero hb, IsLocalization.integerNormalization (nonZeroDivisors ℤ) P,
    ?_⟩
  rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hbP, zsmul_eq_mul]
  simp

/-- **Infinitely many good primes** at every residue outside the finite exceptional set. -/
theorem baseOK_infinite_good (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (c0 : ℕ)
    (hsep : (toPoly (fSpec Fc c0)).Separable) (hdeg : 0 < (toPoly (fSpec Fc c0)).natDegree)
    (T : ℕ) : ∃ p, T < p ∧ ∃ hp : p.Prime, ∃ s : ZMod p,
      (haveI : Fact p.Prime := ⟨hp⟩; baseOK Fc p s (c0 : ZMod p)) = true := by
  obtain ⟨D, hD, mZ, hmZ⟩ := exists_clear (toPoly (fSpec Fc c0))
  refine baseOK_infinite Fc c0 (fKc_hQ Fc _) D hD mZ hmZ ?_ ?_ T
  · rw [hmZ, mul_comm]
    exact hsep.mul_unit (isUnit_C.mpr (Ne.isUnit (by exact_mod_cast hD : (D : ℚ) ≠ 0)))
  · rw [← natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)), hmZ,
      natDegree_C_mul (by exact_mod_cast hD)]
    exact hdeg

section Exist

variable (Fc : BPoly ℚ) [hF : Fact (Irreducible (toPoly (fKc Fc)))]

lemma specB_congr (rs rs' : ℕ → ℕ) : ∀ m, (∀ j ≤ m, rs j = rs' j) →
    ∀ x : KF Fc m, specB Fc rs m x = specB Fc rs' m x := by
  intro m
  induction m with
  | zero =>
    intro h x
    simp only [specB, h 0 le_rfl]
  | succ m ih =>
    intro h x
    have e : specB Fc rs m = specB Fc rs' m :=
      funext (ih fun j hj ↦ h j (by omega))
    show (((RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).1 ++
        (RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).2).all (specB Fc rs m) &&
      evalC (RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).2 ((rs (m + 1) : ℕ) : KF Fc m) != 0 &&
      specB Fc rs m (evalC (RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).2
        ((rs (m + 1) : ℕ) : KF Fc m))⁻¹) =
      (((RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).1 ++
        (RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).2).all (specB Fc rs' m) &&
      evalC (RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).2 ((rs' (m + 1) : ℕ) : KF Fc m) != 0 &&
      specB Fc rs' m (evalC (RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).2
        ((rs' (m + 1) : ℕ) : KF Fc m))⁻¹)
    rw [e, h (m + 1) le_rfl]

/-- The natural numbers at which a nonzero polynomial vanishes form a finite set. -/
lemma finite_natRoots {K : Type*} [Field K] [DecidableEq K] [CharZero K] (Q : CPoly K) (hQ : toPoly Q ≠ 0) :
    {n : ℕ | evalC Q (n : K) = 0}.Finite := by
  refine ((toPoly Q).roots.toFinset.finite_toSet.preimage Nat.cast_injective.injOn).subset ?_
  intro n hn
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset] at hn ⊢
  rw [evalC_eq] at hn
  exact (mem_roots hQ).mpr hn

lemma finite_list_biUnion {α : Type*} (L : List α) (f : α → Set ℕ) (h : ∀ a ∈ L, (f a).Finite) :
    {n | ∃ a ∈ L, n ∈ f a}.Finite := by
  classical
  have : {n | ∃ a ∈ L, n ∈ f a} = ⋃ a ∈ L.toFinset, f a := by
    ext n; simp
  rw [this]
  exact Set.Finite.biUnion L.toFinset.finite_toSet fun a ha ↦ h a (List.mem_toFinset.mp ha)

/-- **Good residues exist** for any finite list of elements, with `rs 0` outside any finite set. -/
theorem exists_rs : ∀ (m : ℕ) (L : List (KF Fc m)) (S : Set ℕ), S.Finite →
    ∃ rs : ℕ → ℕ, rs 0 ∉ S ∧ ∀ x ∈ L, specB Fc rs m x = true := by
  intro m
  induction m with
  | zero =>
    intro L S hS
    set bad : Set ℕ := S ∪ {n | ∃ z ∈ L, ∃ a ∈ (show NFK.NF (fKc Fc) from z).1,
      evalC (RFC.canon a).2 (n : ℚ) = 0}
    have hbad : bad.Finite := by
      refine hS.union ?_
      have := finite_list_biUnion L (fun z ↦ {n | ∃ a ∈ (show NFK.NF (fKc Fc) from z).1,
        evalC (RFC.canon a).2 (n : ℚ) = 0}) fun z _ ↦ by
          have := finite_list_biUnion (show NFK.NF (fKc Fc) from z).1
            (fun a ↦ {n : ℕ | evalC (RFC.canon a).2 (n : ℚ) = 0})
            fun a _ ↦ finite_natRoots _ (RFC.canon_spec a).1
          simpa using this
      simpa using this
    obtain ⟨c, hc⟩ := hbad.exists_notMem
    refine ⟨fun _ ↦ c, fun h ↦ hc (Or.inl h), fun z hz ↦ ?_⟩
    simp only [specB, List.all_eq_true, bne_iff_ne, ne_eq]
    intro a ha h0
    exact hc (Or.inr ⟨z, hz, a, ha, h0⟩)
  | succ m ih =>
    intro L S hS
    set Qf : KF Fc (m + 1) → CPoly (KF Fc m) :=
      fun x ↦ (RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).2
    have hbad : {n | ∃ x ∈ L, n ∈ {n : ℕ | evalC (Qf x) (n : KF Fc m) = 0}}.Finite :=
      finite_list_biUnion L _ fun x _ ↦ finite_natRoots _ (RFC.canon_spec _).1
    obtain ⟨c, hc⟩ := hbad.exists_notMem
    set L' : List (KF Fc m) := L.flatMap fun x ↦
      (RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).1 ++
        (RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).2 ++ [(evalC (Qf x) (c : KF Fc m))⁻¹]
    obtain ⟨rs', h0, hL'⟩ := ih L' S hS
    set rs := Function.update rs' (m + 1) c
    have hagree : ∀ j ≤ m, rs j = rs' j := fun j hj ↦ by
      simp only [rs]; rw [Function.update_of_ne (by omega)]
    have hsp : ∀ y ∈ L', specB Fc rs m y = true := fun y hy ↦ by
      rw [specB_congr Fc rs rs' m hagree]; exact hL' y hy
    refine ⟨rs, by simp only [rs]; rw [Function.update_of_ne (by omega)]; exact h0,
      fun x hx ↦ ?_⟩
    have hrs : rs (m + 1) = c := by simp [rs]
    have hmem : ∀ y, y ∈ (RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).1 ++
        (RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).2 ++ [(evalC (Qf x) (c : KF Fc m))⁻¹] →
        y ∈ L' := fun y hy ↦ List.mem_flatMap.mpr ⟨x, hx, hy⟩
    show (((RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).1 ++
        (RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).2).all (specB Fc rs m) &&
      evalC (RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).2 ((rs (m + 1) : ℕ) : KF Fc m) != 0 &&
      specB Fc rs m (evalC (RFC.canon (show RFC.RatFuncC (KF Fc m) from x)).2
        ((rs (m + 1) : ℕ) : KF Fc m))⁻¹) = true
    rw [hrs]
    simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨fun y hy ↦ hsp y (hmem y (List.mem_append_left _ hy)), fun h0 ↦ hc ⟨x, hx, h0⟩⟩,
      hsp _ (hmem _ (List.mem_append_right _ (List.mem_singleton_self _)))⟩

/-- A separable specialization, cleared to `ℤ[Y]`. -/
lemma clear_good (P : ℚ[X]) (hsep : P.Separable) (hdeg : 0 < P.natDegree) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ mZ : ℤ[X], mZ.map (Int.castRingHom ℚ) = C (D : ℚ) * P ∧
      (mZ.map (Int.castRingHom ℚ)).Separable ∧ 0 < mZ.natDegree := by
  obtain ⟨D, hD, mZ, hmZ⟩ := exists_clear P
  refine ⟨D, hD, mZ, hmZ, ?_, ?_⟩
  · rw [hmZ, mul_comm]
    exact hsep.mul_unit (isUnit_C.mpr (Ne.isUnit (by exact_mod_cast hD : (D : ℚ) ≠ 0)))
  · rw [← natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)), hmZ,
      natDegree_C_mul (by exact_mod_cast hD)]
    exact hdeg

/-- **The local-certificate oracle decides torsion over the code fields** (square roots): for every
query there are residues `rs` at which it answers for all large bounds. -/
theorem kf_torsLocal_exists (m : ℕ) {fK : CPoly (KF Fc m)} (hd : 0 < fK.length - 1)
    (hlc : fK.getD (fK.length - 1) 0 ≠ 0) (hsq : Squarefree (toPoly fK))
    (hcop : Nat.Coprime 2 (fK.length - 1)) (l : List (KF Fc m × KF Fc m × ℕ))
    (hΓ : ∀ q : Fin l.length, (l.get q).2.1 ≠ 0 ∧ (l.get q).2.1 ^ 2 = evalC fK (l.get q).1)
    (hinj : Function.Injective fun q : Fin l.length ↦ ((l.get q).1, (l.get q).2.1)) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ B, B0 ≤ B →
      (torsOracleC (redAtKF Fc m rs) (localCert fK 2) (primesBelow B) B fK 2 l).isSome := by
  have hcp : IsCoprime (toPoly fK) (derivative (toPoly fK)) :=
    PerfectField.separable_iff_squarefree.mpr hsq
  obtain ⟨u, v, huv⟩ := hcp
  set uL : CPoly (KF Fc m) := (List.range (u.natDegree + 1)).map u.coeff
  set vL : CPoly (KF Fc m) := (List.range (v.natDegree + 1)).map v.coeff
  have huL : toPoly uL = u := EllAlgo.toPoly_range_coeff u _ (Or.inr (Nat.lt_succ_self _))
  have hvL : toPoly vL = v := EllAlgo.toPoly_range_coeff v _ (Or.inr (Nat.lt_succ_self _))
  set Els : List (KF Fc m) := fK ++ [(fK.getD (fK.length - 1) 0)⁻¹] ++ uL ++ vL ++
    l.flatMap (fun q ↦ [q.1, q.2.1, q.2.1⁻¹]) ++
    l.flatMap (fun q ↦ l.flatMap fun q' ↦ [(q.1 - q'.1)⁻¹, (q.2.1 - q'.2.1)⁻¹])
  obtain ⟨S, hS, hSg⟩ := fSpec_good Fc
  obtain ⟨rs, h0, hEls⟩ := exists_rs Fc m Els S hS
  obtain ⟨hsep, hdeg⟩ := hSg (rs 0) h0
  obtain ⟨D, hD, mZ, hmZ, hsepZ, hdegZ⟩ := clear_good _ hsep hdeg
  have hE : ∀ x ∈ Els, specB Fc rs m x = true := hEls
  have hgm : ∀ q : Fin l.length, l.get q ∈ l := fun q ↦ List.get_mem l q
  refine ⟨rs, kf_torsLocal_eventually Fc m rs (fKc_hQ Fc _) D hD mZ hmZ hsepZ hdegZ hd hlc hcop
    (u := uL) (v := vL) (by rw [huL, hvL]; linear_combination huv) l hΓ hinj
    (fun c hc ↦ hE c (by simp [Els, hc])) (hE _ (by simp [Els]))
    (fun c hc ↦ hE c (by simp [Els, hc])) (fun c hc ↦ hE c (by simp [Els, hc]))
    (fun q ↦ hE _ ?_) (fun q ↦ hE _ ?_) (fun q ↦ hE _ ?_) (fun q q' _ ↦ hE _ ?_)
    (fun q q' _ _ ↦ hE _ ?_)⟩
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

/-- **`kf_torsLocal_exists` for a divisor `Σ m_q (P_q − ∞)`** given by its points. -/
theorem kf_torsLocal_exists_gamma (m : ℕ) {fK : CPoly (KF Fc m)} (hd : 0 < fK.length - 1)
    (hlc : fK.getD (fK.length - 1) 0 ≠ 0) (hsq : Squarefree (toPoly fK))
    (hcop : Nat.Coprime 2 (fK.length - 1)) {r : ℕ} (α β : Fin r → KF Fc m) (mq : Fin r → ℕ)
    (hv : ∀ q, β q ≠ 0 ∧ β q ^ 2 = (toPoly fK).eval (α q))
    (hinj : Function.Injective fun q ↦ (α q, β q)) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ B, B0 ≤ B →
      (torsOracleC (redAtKF Fc m rs) (localCert fK 2) (primesBelow B) B fK 2
        (Sup.gammaL α β mq 1)).isSome := by
  set l := Sup.gammaL α β mq 1 with hl
  have hlen : l.length = r := by simp [hl, Sup.gammaL]
  set e : Fin l.length ≃ Fin r := finCongr hlen with he
  have hget : ∀ q : Fin l.length, l.get q = (α (e q), β (e q), 1 * mq (e q)) := by
    intro q
    simp [hl, Sup.gammaL, he]
    exact ⟨rfl, rfl, rfl⟩
  refine kf_torsLocal_exists Fc m hd hlc hsq hcop l (fun q ↦ ?_) (fun q q' h ↦ ?_)
  · rw [hget q, evalC_eq]; exact hv (e q)
  · simp only [hget] at h
    exact e.injective (hinj h)

/-- The exceptional residues of the base curve (`fSpec_good`). -/
noncomputable def kfBad : Set ℕ := Classical.choose (fSpec_good Fc)

lemma kfBad_finite : (kfBad Fc).Finite := (Classical.choose_spec (fSpec_good Fc)).1

lemma kfBad_good (c0 : ℕ) (h : c0 ∉ kfBad Fc) :
    (toPoly (fSpec Fc c0)).Separable ∧ 0 < (toPoly (fSpec Fc c0)).natDegree :=
  (Classical.choose_spec (fSpec_good Fc)).2 c0 h

/-- **The elements a query needs specialized**: at any residues outside `kfBad` making them
specializable, the oracle answers for every large bound. -/
theorem kf_query_els (m : ℕ) {fK : CPoly (KF Fc m)} (hd : 0 < fK.length - 1)
    (hlc : fK.getD (fK.length - 1) 0 ≠ 0) (hsq : Squarefree (toPoly fK))
    (hcop : Nat.Coprime 2 (fK.length - 1)) (l : List (KF Fc m × KF Fc m × ℕ))
    (hΓ : ∀ q : Fin l.length, (l.get q).2.1 ≠ 0 ∧ (l.get q).2.1 ^ 2 = evalC fK (l.get q).1)
    (hinj : Function.Injective fun q : Fin l.length ↦ ((l.get q).1, (l.get q).2.1)) :
    ∃ Els : List (KF Fc m), ∀ rs : ℕ → ℕ, rs 0 ∉ kfBad Fc → (∀ x ∈ Els, specB Fc rs m x = true) →
      ∃ B0, ∀ B, B0 ≤ B →
        (torsOracleC (redAtKF Fc m rs) (localCert fK 2) (primesBelow B) B fK 2 l).isSome := by
  have hcp : IsCoprime (toPoly fK) (derivative (toPoly fK)) :=
    PerfectField.separable_iff_squarefree.mpr hsq
  obtain ⟨u, v, huv⟩ := hcp
  set uL : CPoly (KF Fc m) := (List.range (u.natDegree + 1)).map u.coeff
  set vL : CPoly (KF Fc m) := (List.range (v.natDegree + 1)).map v.coeff
  have huL : toPoly uL = u := EllAlgo.toPoly_range_coeff u _ (Or.inr (Nat.lt_succ_self _))
  have hvL : toPoly vL = v := EllAlgo.toPoly_range_coeff v _ (Or.inr (Nat.lt_succ_self _))
  refine ⟨fK ++ [(fK.getD (fK.length - 1) 0)⁻¹] ++ uL ++ vL ++
    l.flatMap (fun q ↦ [q.1, q.2.1, q.2.1⁻¹]) ++
    l.flatMap (fun q ↦ l.flatMap fun q' ↦ [(q.1 - q'.1)⁻¹, (q.2.1 - q'.2.1)⁻¹]),
    fun rs h0 hE ↦ ?_⟩
  obtain ⟨hsep, hdeg⟩ := kfBad_good Fc (rs 0) h0
  obtain ⟨D, hD, mZ, hmZ, hsepZ, hdegZ⟩ := clear_good _ hsep hdeg
  have hgm : ∀ q : Fin l.length, l.get q ∈ l := fun q ↦ List.get_mem l q
  refine kf_torsLocal_eventually Fc m rs (fKc_hQ Fc _) D hD mZ hmZ hsepZ hdegZ hd hlc hcop
    (u := uL) (v := vL) (by rw [huL, hvL]; linear_combination huv) l hΓ hinj
    (fun c hc ↦ hE c (by simp [hc])) (hE _ (by simp))
    (fun c hc ↦ hE c (by simp [hc])) (fun c hc ↦ hE c (by simp [hc]))
    (fun q ↦ hE _ ?_) (fun q ↦ hE _ ?_) (fun q ↦ hE _ ?_) (fun q q' _ ↦ hE _ ?_)
    (fun q q' _ _ ↦ hE _ ?_)
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

/-- `kf_query_els` for a divisor given by its points. -/
theorem kf_query_els_gamma (m : ℕ) {fK : CPoly (KF Fc m)} (hd : 0 < fK.length - 1)
    (hlc : fK.getD (fK.length - 1) 0 ≠ 0) (hsq : Squarefree (toPoly fK))
    (hcop : Nat.Coprime 2 (fK.length - 1)) {r : ℕ} (α β : Fin r → KF Fc m) (mq : Fin r → ℕ)
    (hv : ∀ q, β q ≠ 0 ∧ β q ^ 2 = (toPoly fK).eval (α q))
    (hinj : Function.Injective fun q ↦ (α q, β q)) :
    ∃ Els : List (KF Fc m), ∀ rs : ℕ → ℕ, rs 0 ∉ kfBad Fc → (∀ x ∈ Els, specB Fc rs m x = true) →
      ∃ B0, ∀ B, B0 ≤ B →
        (torsOracleC (redAtKF Fc m rs) (localCert fK 2) (primesBelow B) B fK 2
          (Sup.gammaL α β mq 1)).isSome := by
  set l := Sup.gammaL α β mq 1 with hl
  have hlen : l.length = r := by simp [hl, Sup.gammaL]
  set e : Fin l.length ≃ Fin r := finCongr hlen with he
  have hget : ∀ q : Fin l.length, l.get q = (α (e q), β (e q), 1 * mq (e q)) := by
    intro q
    simp [hl, Sup.gammaL, he]
    exact ⟨rfl, rfl, rfl⟩
  refine kf_query_els Fc m hd hlc hsq hcop l (fun q ↦ ?_) (fun q q' h ↦ ?_)
  · rw [hget q, evalC_eq]; exact hv (e q)
  · simp only [hget] at h
    exact e.injective (hinj h)

/-- **Several queries at once**: residues serving every query of a finite family. -/
theorem exists_rs_many {ι : Type*} (m : ℕ) (Ts : List ι) (Q : ι → (ℕ → ℕ) → Prop)
    (hQ : ∀ T ∈ Ts, ∃ Els : List (KF Fc m), ∀ rs : ℕ → ℕ, rs 0 ∉ kfBad Fc →
      (∀ x ∈ Els, specB Fc rs m x = true) → Q T rs) :
    ∃ rs : ℕ → ℕ, ∀ T ∈ Ts, Q T rs := by
  classical
  have : ∃ Els : List (KF Fc m), ∀ T ∈ Ts, ∀ rs : ℕ → ℕ, rs 0 ∉ kfBad Fc →
      (∀ x ∈ Els, specB Fc rs m x = true) → Q T rs := by
    induction Ts with
    | nil => exact ⟨[], fun T hT ↦ absurd hT (by simp)⟩
    | cons T Ts ih =>
      obtain ⟨E1, h1⟩ := hQ T (by simp)
      obtain ⟨E2, h2⟩ := ih fun T' hT' ↦ hQ T' (List.mem_cons_of_mem _ hT')
      refine ⟨E1 ++ E2, fun T' hT' rs h0 hE ↦ ?_⟩
      rcases List.mem_cons.mp hT' with rfl | hT'
      · exact h1 rs h0 fun x hx ↦ hE x (List.mem_append_left _ hx)
      · exact h2 T' hT' rs h0 fun x hx ↦ hE x (List.mem_append_right _ hx)
  obtain ⟨Els, hEls⟩ := this
  obtain ⟨rs, h0, hE⟩ := exists_rs Fc m Els (kfBad Fc) (kfBad_finite Fc)
  exact ⟨rs, fun T hT ↦ hEls T hT rs h0 hE⟩

end Exist

end Curves.MT
