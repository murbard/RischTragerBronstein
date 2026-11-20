import RischTragerBronstein.Algebraic.SupPicFinite
import RischTragerBronstein.Algebraic.SupTwoPrimes
import RischTragerBronstein.Jacobian.CertCheck

/-!
# Checking good reduction for superelliptic curves

* `evalW_eq_sum_basis`, `ns_of_cert`: the non-speciality hypothesis of `torsion_descends_N` follows
  from a linear certificate: the evaluation at each `Pᵢ` is a combination of the evaluations at the
  conjugates `σᵏPⱼ` on the monomials `xᵃ yʲ` with `n a + d j ≤ n g`.
-/

open Polynomial

namespace Sup

section Cert

variable {F : Type*} [CommRing F]

open Classical in
/-- The value of `U` with bounded support, as a sum over the monomial basis. -/
lemma evalW_eq_sum_basis (U : F[X][X]) {n d M : ℕ} (hn : 0 < n)
    (hU : ∀ j a, (U.coeff j).coeff a ≠ 0 → j < n ∧ n * a + d * j ≤ M) (a b : F) :
    evalW U a b = ∑ ai ∈ (basisN n d M).toFinset,
      (U.coeff ai.2).coeff ai.1 * (a ^ ai.1 * b ^ ai.2) := by
  have hUn : (U.map (evalRingHom a)).natDegree < n := by
    refine lt_of_le_of_lt natDegree_map_le ?_
    by_contra h
    push_neg at h
    by_cases hU0 : U = 0
    · subst hU0; simp at h; omega
    have hc := leadingCoeff_ne_zero.mpr hU0
    obtain ⟨a', ha'⟩ : ∃ a', (U.coeff U.natDegree).coeff a' ≠ 0 := by
      by_contra h1; push_neg at h1; exact hc (Polynomial.ext h1)
    have := (hU _ a' ha').1
    omega
  have hcoef : ∀ j, (U.coeff j).natDegree < M + 1 := by
    intro j
    by_cases hj : U.coeff j = 0
    · rw [hj, natDegree_zero]; omega
    have hc := leadingCoeff_ne_zero.mpr hj
    have := (hU j _ hc).2
    have : (U.coeff j).natDegree ≤ M := by nlinarith
    omega
  rw [evalW, eval_eq_sum_range' hUn, basisN_toFinset, Finset.sum_filter, Finset.sum_product,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [coeff_map, coe_evalRingHom, eval_eq_sum_range' (hcoef j), Finset.sum_mul]
  refine Finset.sum_congr rfl fun a' _ ↦ ?_
  split_ifs with h
  · ring
  · by_cases hz : (U.coeff j).coeff a' = 0
    · rw [hz]; ring
    · exact absurd (hU j a' hz).2 h

/-- **Non-speciality from a linear certificate.** -/
theorem ns_of_cert {g n d : ℕ} (hn : 0 < n) (x y : Fin g → F) (ζ : F)
    (lam : Fin g → Fin g → ℕ → F)
    (hcert : ∀ i, ∀ ai ∈ basisN n d (n * g), x i ^ ai.1 * y i ^ ai.2 =
      ∑ i', ∑ k ∈ Finset.Ico 1 n, lam i i' k * (x i' ^ ai.1 * (ζ ^ k * y i') ^ ai.2)) :
    ∀ U : F[X][X], (∀ j a, (U.coeff j).coeff a ≠ 0 → j < n ∧ n * a + d * j ≤ n * g) →
      (∀ i k, 1 ≤ k → k < n → evalW U (x i) (ζ ^ k * y i) = 0) →
      ∀ i, evalW U (x i) (y i) = 0 := by
  classical
  intro U hU hv i
  rw [evalW_eq_sum_basis U hn hU,
    Finset.sum_congr rfl fun ai hai ↦ by rw [hcert i ai (List.mem_toFinset.mp hai)]]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i' _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  have hk' := Finset.mem_Ico.mp hk
  have h0 := hv i' k hk'.1 hk'.2
  rw [evalW_eq_sum_basis U hn hU] at h0
  rw [show (∑ ai ∈ (basisN n d (n * g)).toFinset,
      (U.coeff ai.2).coeff ai.1 * (lam i i' k * (x i' ^ ai.1 * (ζ ^ k * y i') ^ ai.2))) =
      lam i i' k * ∑ ai ∈ (basisN n d (n * g)).toFinset,
        (U.coeff ai.2).coeff ai.1 * (x i' ^ ai.1 * (ζ ^ k * y i') ^ ai.2) by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring, h0, mul_zero]

end Cert

section Padic

variable {p : ℕ} [hp : Fact p.Prime]

/-- `n`-th roots in `ℤ_p` by Hensel's lemma. -/
lemma exists_nth_root {n : ℕ} (hn : 0 < n) (hnu : IsUnit (n : ℤ_[p])) (c y₀ : ℤ_[p])
    (hy₀ : IsUnit y₀) (hc : ‖y₀ ^ n - c‖ < 1) :
    ∃ y : ℤ_[p], y ^ n = c ∧ IsUnit y ∧ ‖y - y₀‖ < 1 := by
  have hn1 : ‖(n : ℤ_[p])‖ = 1 := PadicInt.isUnit_iff.mp hnu
  have hy1 : ‖y₀‖ = 1 := PadicInt.isUnit_iff.mp hy₀
  set F : ℤ_[p][X] := X ^ n - C c
  have e1 : ∀ w : ℤ_[p], F.aeval w = w ^ n - c := fun w ↦ by simp [F]
  have e2 : F.derivative.aeval y₀ = n * y₀ ^ (n - 1) := by simp [F, derivative_X_pow]
  have hd : ‖F.derivative.aeval y₀‖ = 1 := by
    rw [e2, norm_mul, hn1, norm_pow, hy1, one_pow, one_mul]
  have hF : ‖F.aeval y₀‖ < ‖F.derivative.aeval y₀‖ ^ 2 := by rw [hd, one_pow, e1]; exact hc
  obtain ⟨z, hz, hzd, -, -⟩ := hensels_lemma hF
  rw [hd] at hzd
  refine ⟨z, ?_, ?_, hzd⟩
  · rw [e1] at hz; exact sub_eq_zero.mp hz
  · rw [PadicInt.isUnit_iff]
    have : z = y₀ + (z - y₀) := by ring
    rw [this, PadicInt.norm_add_eq_max_of_ne (by rw [hy1]; exact (ne_of_gt hzd)), hy1]
    exact max_eq_left hzd.le

lemma toZMod_eq_of_norm_sub_lt {a b : ℤ_[p]} (h : ‖a - b‖ < 1) :
    PadicInt.toZMod a = PadicInt.toZMod b := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZMod,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PadicInt.isUnit_iff]
  exact ne_of_lt h

end Padic

/-- The certificate coefficient `λ_{i, (i', k)}`. -/
def lamC (lam : List (List ℤ)) (n i i' k : ℕ) : ℤ := (lam.getD i []).getD (i' * (n - 1) + (k - 1)) 0

/-- **The non-speciality certificate check** modulo `p`: on every monomial `xᵃ yʲ` of the basis,
evaluation at `Pᵢ` equals `∑ λ_{i,(i',k)} ·` evaluation at `σᵏP_{i'}`. -/
def nsCheck (p : ℕ) (f : List ℤ) (n g : ℕ) (xs ys : List ℤ) (ζ0 : ℤ) (lam : List (List ℤ)) :
    Bool :=
  (List.range g).all fun i ↦ (basisN n (f.length - 1) (n * g)).all fun ai ↦
    decide (((xs.getD i 0 : ZMod p) ^ ai.1 * (ys.getD i 0 : ZMod p) ^ ai.2) =
      ∑ i' ∈ Finset.range g, ∑ k ∈ Finset.Ico 1 n, (lamC lam n i i' k : ZMod p) *
        ((xs.getD i' 0 : ZMod p) ^ ai.1 * ((ζ0 : ZMod p) ^ k * (ys.getD i' 0 : ZMod p)) ^ ai.2))

lemma nsCheck_spec {p : ℕ} {f : List ℤ} {n g : ℕ} (hn : 0 < n) {xs ys : List ℤ} {ζ0 : ℤ}
    {lam : List (List ℤ)} (h : nsCheck p f n g xs ys ζ0 lam = true) :
    ∀ U : (ZMod p)[X][X], (∀ j a, (U.coeff j).coeff a ≠ 0 → j < n ∧
        n * a + (f.length - 1) * j ≤ n * g) →
      (∀ i : Fin g, ∀ k, 1 ≤ k → k < n → evalW U (xs.getD i 0 : ZMod p)
        ((ζ0 : ZMod p) ^ k * (ys.getD i 0 : ZMod p)) = 0) →
      ∀ i : Fin g, evalW U (xs.getD i 0 : ZMod p) (ys.getD i 0 : ZMod p) = 0 := by
  refine ns_of_cert hn (fun i : Fin g ↦ (xs.getD i 0 : ZMod p)) (fun i ↦ (ys.getD i 0 : ZMod p))
    (ζ0 : ZMod p) (fun i i' k ↦ (lamC lam n i i' k : ZMod p)) ?_
  intro i ai hai
  simp only [nsCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have := h i i.2 ai hai
  rw [this, ← Fin.sum_univ_eq_sum_range (fun i' ↦ ∑ k ∈ Finset.Ico 1 n,
    (lamC lam n i i' k : ZMod p) * ((xs.getD i' 0 : ZMod p) ^ ai.1 *
      ((ζ0 : ZMod p) ^ k * (ys.getD i' 0 : ZMod p)) ^ ai.2))]

/-- **The good-reduction conditions at `p`** for `yⁿ = f(x)` (`f ∈ ℤ[x]`), the integral points
`(α_q, β_q)` of `Γ`, base points `(xᵢ, yᵢ mod p)`, an `n`-th root of unity `ζ₀ mod p` and a
non-speciality certificate. -/
abbrev supBaseCheck (p : ℕ) [Fact p.Prime] (f : List ℤ) (n g : ℕ) {r : ℕ} (α β : Fin r → ℤ) (xs ys : List ℤ)
    (ζ0 : ℤ) (lam : List (List ℤ)) : Prop :=
  2 ≤ n ∧ ¬ (p : ℤ) ∣ n ∧ 0 < f.length - 1 ∧ ¬ (p : ℤ) ∣ f.getD (f.length - 1) 0 ∧
    (n - 1) * (f.length - 1 - 1) ≤ 2 * g ∧ CPoly.squarefreeCheck (Jac.castL p f) = true ∧
    (p : ℤ) ∣ ζ0 ^ n - 1 ∧ (∀ l ∈ List.range n, 0 < l → ¬ (p : ℤ) ∣ ζ0 ^ l - 1) ∧
    xs.length = g ∧ ys.length = g ∧
    (∀ i ∈ List.range g, (p : ℤ) ∣ ys.getD i 0 ^ n - CPoly.Kron.evalC f (xs.getD i 0) ∧
      ¬ (p : ℤ) ∣ ys.getD i 0) ∧
    xs.Pairwise (fun u v ↦ ¬ (p : ℤ) ∣ u - v) ∧
    (∀ q, ¬ (p : ℤ) ∣ β q ∧ β q ^ n = CPoly.Kron.evalC f (α q) ∧ ∀ x ∈ xs, ¬ (p : ℤ) ∣ α q - x) ∧
    (∀ q q', α q = α q' ∨ ¬ (p : ℤ) ∣ α q - α q') ∧
    (∀ q q', q ≠ q' → α q = α q' → ¬ (p : ℤ) ∣ β q - β q') ∧
    nsCheck p f n g xs ys ζ0 lam = true

section Spec

variable {p : ℕ} [hp : Fact p.Prime]

local notation "ιp" => Int.castRingHom ℤ_[p]

theorem supBaseCheck_spec {f : List ℤ} {n g r : ℕ} {α β : Fin r → ℤ} {xs ys : List ℤ} {ζ0 : ℤ}
    {lam : List (List ℤ)} (h : supBaseCheck p f n g α β xs ys ζ0 lam) :
    ∃ D : SupGoodData p (algebraMap ℚ ℚ_[p]) ((CPoly.toPoly f).map (Int.castRingHom ℚ)) n
      (fun q ↦ (α q : ℚ)) (fun q ↦ (β q : ℚ)),
      D.f = (CPoly.toPoly f).map (Int.castRingHom ℤ_[p]) ∧
      D.α = (fun q ↦ ((α q : ℤ) : ℤ_[p])) ∧ D.β = (fun q ↦ ((β q : ℤ) : ℤ_[p])) := by
  obtain ⟨hn2, hpn, hd, hlc, hgen, hsq, hζ1, hζl, hxl, hyl, hE, hxd, hΓ, hΓd, hΓβ, hns⟩ := h
  have hn : 0 < n := by omega
  set fO : ℤ_[p][X] := (CPoly.toPoly f).map ιp with hfO_def
  have hcoef : ∀ m, fO.coeff m = ((f.getD m 0 : ℤ) : ℤ_[p]) := by
    intro m; rw [coeff_map, CPoly.coeff_toPoly]; rfl
  have hlc0 : fO.coeff (f.length - 1) ≠ 0 := by
    rw [hcoef]; exact (Jac.isUnit_intCast hlc).ne_zero
  have hdeg : fO.natDegree = f.length - 1 := by
    refine le_antisymm ?_ (le_natDegree_of_ne_zero hlc0)
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    have hm' : f.length - 1 < m := by exact_mod_cast hm
    rw [hcoef, List.getD_eq_default _ _ (by omega), Int.cast_zero]
  have hlcU : IsUnit fO.leadingCoeff := by
    rw [leadingCoeff, hdeg, hcoef]; exact Jac.isUnit_intCast hlc
  have heval : ∀ t : ℤ, fO.eval (t : ℤ_[p]) = ((CPoly.Kron.evalC f t : ℤ) : ℤ_[p]) := by
    intro t
    rw [CPoly.Kron.evalC_eq, hfO_def, eval_map, show (t : ℤ_[p]) = ιp t from rfl, eval₂_at_apply]
    rfl
  have hnu : IsUnit (n : ℤ_[p]) := by
    have := Jac.isUnit_intCast (p := p) hpn; push_cast at this; exact this
  -- the root of unity
  have hζ0 : ¬ (p : ℤ) ∣ ζ0 := by
    intro hd0
    have h1 : (p : ℤ) ∣ ζ0 ^ n := dvd_pow hd0 hn.ne'
    have := (Int.dvd_sub h1 hζ1)
    rw [sub_sub_cancel] at this
    exact hp.out.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
  obtain ⟨ζ, hζn, hζu, hζd⟩ := exists_nth_root (p := p) hn hnu 1 (ζ0 : ℤ_[p])
    (Jac.isUnit_intCast hζ0) (by
      have := (PadicInt.norm_int_lt_one_iff_dvd (p := p) _).mpr hζ1; push_cast at this; exact this)
  have hζz : PadicInt.toZMod ζ = (ζ0 : ZMod p) := by
    rw [toZMod_eq_of_norm_sub_lt hζd, map_intCast]
  have hζl' : ∀ l, 0 < l → l < n → (ζ0 : ZMod p) ^ l ≠ 1 := by
    intro l hl hln he
    apply hζl l (List.mem_range.mpr hln) hl
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast; rw [he, sub_self]
  have hζp : IsPrimitiveRoot ζ n := IsPrimitiveRoot.mk_of_lt ζ hn hζn fun l hl hln he ↦
    hζl' l hl hln (by rw [← hζz, ← map_pow, he, map_one])
  have hζk : IsPrimitiveRoot (IsLocalRing.residue ℤ_[p] ζ) n :=
    IsPrimitiveRoot.mk_of_lt _ hn (by rw [← map_pow, hζn, map_one]) fun l hl hln he ↦
      hζl' l hl hln (by
        rw [← hζz, PadicInt.toZMod_eq_residueField_comp_residue, RingHom.comp_apply, ← map_pow,
          RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, he, map_one])
  -- the base points
  have hex : ∀ i : Fin g, ∃ y : ℤ_[p], y ^ n = fO.eval ((xs.getD i 0 : ℤ) : ℤ_[p]) ∧ IsUnit y ∧
      ‖y - ((ys.getD i 0 : ℤ) : ℤ_[p])‖ < 1 := by
    intro i
    obtain ⟨hdv, hnu'⟩ := hE i (List.mem_range.mpr i.2)
    exact exists_nth_root hn hnu _ _ (Jac.isUnit_intCast hnu') (by
      rw [heval, ← Int.cast_pow, ← Int.cast_sub]
      exact (PadicInt.norm_int_lt_one_iff_dvd _).mpr hdv)
  choose yp hyp hyu hyd using hex
  set xp : Fin g → ℤ_[p] := fun i ↦ ((xs.getD i 0 : ℤ) : ℤ_[p]) with hxp_def
  have hxmem : ∀ i : Fin g, xs.getD i 0 ∈ xs := fun i ↦ by
    have hi : (i : ℕ) < xs.length := by rw [hxl]; exact i.2
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  have e : IsLocalRing.ResidueField ℤ_[p] ≃+* ZMod p := PadicInt.residueField
  have hres : ∀ z : ℤ_[p], PadicInt.residueField (IsLocalRing.residue ℤ_[p] z) =
      PadicInt.toZMod z := fun z ↦ rfl
  refine ⟨{
    f := fO
    hlc := hlcU
    hfmap := by
      rw [Polynomial.map_map, hfO_def, Polynomial.map_map]; congr 1
    hsqk := by
      have hsq' := CPoly.squarefreeCheck_sound hsq
      rw [Jac.castL_eq] at hsq'
      have e1 : fO.map (IsLocalRing.residue ℤ_[p]) = ((CPoly.toPoly f).map
          (Int.castRingHom (ZMod p))).map PadicInt.residueField.symm.toRingHom := by
        rw [hfO_def, Polynomial.map_map, Polynomial.map_map]; congr 1; exact RingHom.ext_int _ _
      rw [e1]
      exact ((PerfectField.separable_iff_squarefree.mpr hsq').map).squarefree
    hnu := hnu
    ζ := ζ
    hζ := hζp
    hζk := hζk
    g := g
    hgen := by rw [hdeg]; exact hgen
    x := xp
    y := yp
    hyu := hyu
    hyf := hyp
    hx := by
      intro i j hij
      apply Jac.isUnit_intCast_sub
      have hi : (i : ℕ) < xs.length := by rw [hxl]; exact i.2
      have hj : (j : ℕ) < xs.length := by rw [hxl]; exact j.2
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
      · exact List.pairwise_iff_getElem.mp hxd _ _ hi hj hlt
      · intro hd'
        exact List.pairwise_iff_getElem.mp hxd _ _ hj hi hlt ((dvd_sub_comm).mp hd')
    α := fun q ↦ ((α q : ℤ) : ℤ_[p])
    β := fun q ↦ ((β q : ℤ) : ℤ_[p])
    hαmap := fun q ↦ by simp
    hβmap := fun q ↦ by simp
    hβu := fun q ↦ Jac.isUnit_intCast (hΓ q).1
    hβf := fun q ↦ by rw [heval, ← (hΓ q).2.1]; push_cast; rfl
    hα := fun q q' ↦ (hΓd q q').imp (fun h ↦ by rw [h]) fun h ↦ Jac.isUnit_intCast_sub _ _ h
    hβd := fun q q' hqq hαe ↦ Jac.isUnit_intCast_sub _ _ (hΓβ q q' hqq (by exact_mod_cast hαe))
    hαx := fun q i ↦ Jac.isUnit_intCast_sub _ _ ((hΓ q).2.2 _ (hxmem i))
    hNS := by
      intro U hU hUv i
      set V := U.map (mapRingHom PadicInt.residueField.toRingHom) with hV_def
      have hVs : ∀ j a, (V.coeff j).coeff a ≠ 0 → j < n ∧
          n * a + (f.length - 1) * j ≤ n * g := by
        intro j a hja
        rw [← hdeg]
        refine hU j a fun h0 ↦ hja ?_
        simp [V, h0]
      have hx' : ∀ i, PadicInt.residueField (IsLocalRing.residue ℤ_[p] (xp i)) =
          (xs.getD i 0 : ZMod p) := fun i ↦ by rw [hres, map_intCast]
      have hy' : ∀ i, PadicInt.residueField (IsLocalRing.residue ℤ_[p] (yp i)) =
          (ys.getD i 0 : ZMod p) := fun i ↦ by
        rw [hres, toZMod_eq_of_norm_sub_lt (hyd i), map_intCast]
      have hζ' : PadicInt.residueField (IsLocalRing.residue ℤ_[p] ζ) = (ζ0 : ZMod p) := by
        rw [hres, hζz]
      have key := nsCheck_spec hn hns V hVs (fun i k hk1 hk ↦ by
        rw [← hx', ← hy', ← hζ', ← map_pow, ← map_mul]
        exact (evalW_map PadicInt.residueField.toRingHom U _ _).trans
          (by rw [hUv i k hk1 hk, map_zero])) i
      rw [← hx', ← hy'] at key
      have h2 : PadicInt.residueField.toRingHom (evalW U (IsLocalRing.residue ℤ_[p] (xp i))
          (IsLocalRing.residue ℤ_[p] (yp i))) = 0 :=
        (evalW_map PadicInt.residueField.toRingHom U _ _).symm.trans key
      exact (map_eq_zero_iff _ PadicInt.residueField.injective).mp h2 }, rfl, rfl, rfl⟩

end Spec

end Sup
