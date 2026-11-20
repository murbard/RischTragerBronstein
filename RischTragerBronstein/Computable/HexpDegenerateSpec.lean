import RischTragerBronstein.Computable.HexpDegenerate

/-!
# Two hyperexponentials with only simple poles: soundness of the certificate

* `evalL`: the value at `Λ = l` of a polynomial in `Λ` with coefficients in `R[x]`;
  `identCheck_spec`: `s ∣ D(l) ρ₁ - Γₗ(l ρ₁ + ρ₂)` for every `l`;
* `nonRatVals_spec`: a non-rational value modulo a prime factor of `s`, over any constant field;
* `residue_int_of_logDeriv`: if `y′ = (G / s) y` with `s` separable, then at every prime `p ∣ s`,
  `p ∣ G - n s′` for an integer `n` (the residue of `G / s` at `p` is the order of `y`);
* `hexpDegen_hom`: the certificate gives uniqueness for `y′ + (c η₂ + z η₁) y = 0`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace CPoly

section Eval

variable {R : Type*} [CommRing R]

/-- The value at `Λ = l`. -/
noncomputable def evalL (l : R) : List (CPoly R) → R[X]
  | [] => 0
  | a :: L => toPoly a + C l * evalL l L

@[simp] lemma evalL_nil (l : R) : evalL l [] = 0 := rfl

@[simp] lemma evalL_cons (l : R) (a : CPoly R) (L : List (CPoly R)) :
    evalL l (a :: L) = toPoly a + C l * evalL l L := rfl

lemma evalL_addL (l : R) : ∀ P Q : List (CPoly R), evalL l (addL P Q) = evalL l P + evalL l Q
  | [], Q => by simp [addL]
  | a :: P, [] => by simp [addL]
  | a :: P, b :: Q => by
    simp only [addL, evalL_cons, toPoly_add, evalL_addL l P Q]; ring

lemma evalL_map_mul (l : R) (g : CPoly R) (P : List (CPoly R)) :
    evalL l (P.map (mul g)) = toPoly g * evalL l P := by
  induction P with
  | nil => simp
  | cons a P ih => simp only [List.map_cons, evalL_cons, toPoly_mul, ih]; ring

lemma evalL_map_smul (l : R) (a : R) (P : List (CPoly R)) :
    evalL l (P.map (smul a)) = C a * evalL l P := by
  induction P with
  | nil => simp
  | cons b P ih => simp only [List.map_cons, evalL_cons, toPoly_smul, ih]; ring

lemma evalL_map_neg (l : R) (P : List (CPoly R)) : evalL l (P.map neg) = -evalL l P := by
  induction P with
  | nil => simp
  | cons b P ih => simp only [List.map_cons, evalL_cons, toPoly_neg, ih]; ring

lemma evalL_mulScal (l : R) (g : CPoly R) (P : List (CPoly R)) :
    evalL l (mulScal g P) = C ((toPoly g).eval l) * evalL l P := by
  induction g with
  | nil => simp [mulScal]
  | cons a g ih =>
    simp only [mulScal, evalL_addL, evalL_map_smul, evalL_cons, toPoly_nil, ih, toPoly_cons,
      eval_add, eval_C, eval_mul, eval_X, C_add, C_mul]
    ring

lemma evalL_powL (l : R) (ρ₁ ρ₂ : CPoly R) (j : ℕ) :
    evalL l (powL ρ₁ ρ₂ j) = (C l * toPoly ρ₁ + toPoly ρ₂) ^ j := by
  induction j with
  | zero => simp [powL]
  | succ j ih =>
    simp only [powL, evalL_addL, evalL_cons, evalL_map_mul, toPoly_nil, ih, pow_succ]
    ring

/-- The polynomial `∑ gᵢ(l) Tⁱ`. -/
noncomputable def gammaL (l : R) (gs : List (CPoly R)) : R[X] :=
  toPoly (gs.map fun g ↦ (toPoly g).eval l)

lemma evalL_combL (l : R) (ρ₁ ρ₂ : CPoly R) (gs : List (CPoly R)) (j : ℕ) :
    evalL l (combL ρ₁ ρ₂ gs j) =
      (C l * toPoly ρ₁ + toPoly ρ₂) ^ j * (gammaL l gs).comp (C l * toPoly ρ₁ + toPoly ρ₂) := by
  induction gs generalizing j with
  | nil => simp [combL, gammaL]
  | cons g gs ih =>
    simp only [combL, evalL_addL, evalL_mulScal, evalL_powL, ih, gammaL, List.map_cons,
      toPoly_cons, add_comp, C_comp, mul_comp, X_comp]
    rw [gammaL] at ih
    ring

lemma dvd_evalL (l : R) {s : R[X]} :
    ∀ L : List (CPoly R), (∀ e ∈ L, s ∣ toPoly e) → s ∣ evalL l L
  | [], _ => by simp
  | a :: L, h => by
    rw [evalL_cons]
    exact dvd_add (h a List.mem_cons_self)
      (dvd_mul_of_dvd_right (dvd_evalL l L fun e he ↦ h e (List.mem_cons_of_mem _ he)) _)

lemma toPoly_map' {S : Type*} [CommRing S] (f : R →+* S) (p : CPoly R) :
    toPoly (p.map f) = (toPoly p).map f := by
  induction p with
  | nil => simp
  | cons a p ih => simp [ih]

lemma toPoly_foldr_mul {F : Type*} [CommRing F] (Ds : List (CPoly F)) :
    toPoly (Ds.foldr mul [1]) = (Ds.map toPoly).prod := by
  induction Ds with
  | nil => simp
  | cons D Ds ih => simp [ih]

end Eval

section Q

lemma dvd_of_rem_zero {s e : CPoly ℚ} (h : isZero (divMod e s).2 = true) : toPoly s ∣ toPoly e :=
  ⟨toPoly (divMod e s).1, by rw [divMod_spec e s, (isZero_iff _).mp h, add_zero, mul_comm]⟩

/-- **The identity**: `s ∣ D(l) ρ₁ - Γₗ(l ρ₁ + ρ₂)` for every `l ∈ ℚ`. -/
theorem identCheck_spec {s ρ₁ ρ₂ D : CPoly ℚ} {gs : List (CPoly ℚ)}
    (h : identCheck s ρ₁ ρ₂ D gs = true) (l : ℚ) :
    toPoly s ∣ C ((toPoly D).eval l) * toPoly ρ₁ -
      (gammaL l gs).comp (C l * toPoly ρ₁ + toPoly ρ₂) := by
  have := dvd_evalL l _ fun e he ↦ dvd_of_rem_zero (List.all_eq_true.mp h e he)
  rw [evalL_addL, evalL_map_neg, evalL_combL, evalL_mulScal] at this
  simpa [sub_eq_add_neg] using this

lemma evalQ_eq (P : CPoly ℚ) (q : ℚ) : evalQ P q = (toPoly P).eval q := by
  induction P with
  | nil => simp [evalQ]
  | cons a P ih => simp [evalQ, ← ih]

lemma ratRootsF_spec {P : CPoly ℚ} {q : ℚ} (hP : toPoly P ≠ 0) (hq : (toPoly P).eval q = 0) :
    q ∈ ratRootsF P :=
  List.mem_dedup.mpr (List.mem_filter.mpr ⟨ratRootsQ_spec P q hP hq, by simp [evalQ_eq, hq]⟩)

variable {S : Type*} [Field S] [CharZero S]

/-- **A non-rational value**: some prime factor `p` of `s` (over `S`) has `a ≢ q (mod p)` for
every rational `q`. -/
theorem nonRatVals_spec (ι : ℚ →+* S) {s a : CPoly ℚ} (hs0 : toPoly s ≠ 0)
    (hsq : Squarefree ((toPoly s).map ι)) (h : nonRatVals s a = true) :
    ∃ p : S[X], Irreducible p ∧ p ∣ (toPoly s).map ι ∧
      ∀ q : ℚ, ¬p ∣ (toPoly a).map ι - C (ι q) := by
  have hιinj : Function.Injective ι := ι.injective
  obtain ⟨hμ0, w, hw⟩ := muCheck_spec (muCheck_findMu s a hs0)
  have hμS : (toPoly s).map ι ∣ ((toPoly (findMu s a)).map ι).comp ((toPoly a).map ι) :=
    ⟨w.map ι, by rw [← Polynomial.map_comp, hw, Polynomial.map_mul]⟩
  unfold nonRatVals at h
  generalize hP : ratShiftProd a (ratRootsF (findMu s a)) = P at h
  have hPpoly : toPoly P = ((ratRootsF (findMu s a)).map fun (q : ℚ) ↦
      toPoly a - C q).prod := by
    rw [← hP, toPoly_ratShiftProd]; simp only [Rat.cast_id]
  obtain ⟨Qd, Rm, hdm⟩ : ∃ Qd Rm, divMod P s = (Qd, Rm) := ⟨_, _, rfl⟩
  have hspec := divMod_spec P s
  have hlt := divMod_degree_lt P s hs0
  rw [hdm] at hspec hlt h
  have hrem : toPoly Rm ≠ 0 := fun h0 ↦ by
    have := (isZero_iff _).mpr h0
    simp [this] at h
  have hndvd : ¬(toPoly s).map ι ∣ (toPoly P).map ι := by
    intro hdvd
    have hremS : (toPoly s).map ι ∣ (toPoly Rm).map ι := by
      have : (toPoly Rm).map ι = (toPoly P).map ι - (toPoly Qd).map ι * (toPoly s).map ι := by
        rw [← Polynomial.map_mul, ← Polynomial.map_sub]
        exact congrArg (Polynomial.map ι) (by rw [hspec]; ring)
      rw [this]
      exact dvd_sub hdvd (dvd_mul_left _ _)
    have h0 := eq_zero_of_dvd_of_degree_lt hremS (by rw [degree_map, degree_map]; exact hlt)
    exact hrem ((Polynomial.map_eq_zero_iff hιinj).mp h0)
  by_contra hall
  push Not at hall
  refine hndvd (dvd_of_squarefree_of_irreducible_dvd hsq fun p hp hpS ↦ ?_)
  obtain ⟨q', hpq'⟩ := hall p hp hpS
  have hq' := Differential.eval_eq_zero_of_dvd_comp hp hpS hμS hpq'
  rw [eval_map, eval₂_at_apply] at hq'
  have hqR : (toPoly (findMu s a)).eval q' = 0 := hιinj (by rw [hq', map_zero])
  have hmem := ratRootsF_spec hμ0 hqR
  rw [hPpoly, Polynomial.map_list_prod, List.map_map]
  refine hpq'.trans (List.dvd_prod ?_)
  refine List.mem_map.mpr ⟨q', hmem, ?_⟩
  simp only [Function.comp_apply, Polynomial.map_sub, map_C]

/-- A non-rational value refutes rational values modulo every prime factor. -/
theorem nonRatVals_false (ι : ℚ →+* S) {s a : CPoly ℚ} (hs0 : toPoly s ≠ 0)
    (hsq : Squarefree ((toPoly s).map ι)) (h : nonRatVals s a = true)
    (hall : ∀ p : S[X], Irreducible p → p ∣ (toPoly s).map ι →
      ∃ q : ℚ, p ∣ (toPoly a).map ι - C (ι q)) : False := by
  obtain ⟨p, hp, hps, hnot⟩ := nonRatVals_spec ι hs0 hsq h
  obtain ⟨q, hq⟩ := hall p hp hps
  exact hnot q hq

/-- **The pair certificate**: no non-zero rational combination `z w₁ + c w₂` takes only rational
values modulo the prime factors of `s` (over any constant field). -/
theorem degenCertQ_sound (ιQ : ℚ →+* S) {s w₁ w₂ : CPoly ℚ} (hcert : degenCertQ s w₁ w₂ = true)
    (z c : ℚ) (hzc : z ≠ 0 ∨ c ≠ 0)
    (hall : ∀ p : S[X], Irreducible p → p ∣ (toPoly s).map ιQ →
      ∃ q : ℚ, p ∣ C (ιQ z) * (toPoly w₁).map ιQ + C (ιQ c) * (toPoly w₂).map ιQ - C (ιQ q)) :
    False := by
  unfold degenCertQ at hcert
  simp only [Bool.and_eq_true] at hcert
  obtain ⟨⟨⟨hsQ0, hsqf⟩, hnr₁⟩, hK⟩ := hcert
  have hsQ0' : toPoly s ≠ 0 := fun h0 ↦ by simp [(isZero_iff _).mpr h0] at hsQ0
  set st := (toPoly s).map ιQ with hst
  have hsep : st.Separable :=
    (PerfectField.separable_iff_squarefree.mpr (squarefreeCheck_sound hsqf)).map
  have hsqS : Squarefree st := hsep.squarefree
  by_cases hc : c = 0
  · have hz : z ≠ 0 := hzc.resolve_right (not_not.mpr hc)
    have hzS : ιQ z ≠ 0 := (map_ne_zero_iff _ ιQ.injective).mpr hz
    refine nonRatVals_false ιQ hsQ0' hsqS hnr₁ fun p hp hps ↦ ?_
    obtain ⟨q, hq⟩ := hall p hp hps
    refine ⟨q / z, ?_⟩
    have e : C (ιQ z) * (toPoly w₁).map ιQ + C (ιQ c) * (toPoly w₂).map ιQ - C (ιQ q) =
        C (ιQ z) * ((toPoly w₁).map ιQ - C (ιQ (q / z))) := by
      rw [hc, map_zero, C_0, zero_mul, add_zero, mul_sub, ← C_mul, ← map_mul,
        mul_div_cancel₀ _ hz]
    rw [e] at hq
    exact (hp.prime.dvd_or_dvd hq).resolve_left fun hd ↦
      hp.not_isUnit (isUnit_of_dvd_unit hd (isUnit_C.mpr hzS.isUnit))
  have hcS : ιQ c ≠ 0 := (map_ne_zero_iff _ ιQ.injective).mpr hc
  set l : ℚ := z / c with hl
  have key : ∀ p : S[X], Irreducible p → p ∣ st →
      ∃ q : ℚ, p ∣ (toPoly (add (smul l w₁) w₂)).map ιQ - C (ιQ q) := by
    intro p hp hps
    obtain ⟨q, hq⟩ := hall p hp hps
    refine ⟨q / c, ?_⟩
    have e : C (ιQ z) * (toPoly w₁).map ιQ + C (ιQ c) * (toPoly w₂).map ιQ - C (ιQ q) =
        C (ιQ c) * ((toPoly (add (smul l w₁) w₂)).map ιQ - C (ιQ (q / c))) := by
      rw [toPoly_add, toPoly_smul, Polynomial.map_add, Polynomial.map_mul, map_C, mul_sub,
        mul_add, ← mul_assoc, ← C_mul, ← C_mul, ← map_mul, ← map_mul, hl,
        mul_div_cancel₀ _ hc, mul_div_cancel₀ _ hc]
    rw [e] at hq
    exact (hp.prime.dvd_or_dvd hq).resolve_left fun hd ↦
      hp.not_isUnit (isUnit_of_dvd_unit hd (isUnit_C.mpr hcS.isUnit))
  cases hk : krylovSolve s w₁ w₂ with
  | none => simp [hk] at hK
  | some DG =>
  obtain ⟨Ds, gs⟩ := DG
  simp only [hk, Bool.and_eq_true] at hK
  obtain ⟨⟨hDs0, hid⟩, hroots⟩ := hK
  by_cases hz : (toPoly (Ds.foldr mul [1])).eval l = 0
  · rw [toPoly_foldr_mul, eval_list_prod, List.prod_eq_zero_iff, List.map_map] at hz
    obtain ⟨D, hD, hDz⟩ := List.mem_map.mp hz
    have hD0 : toPoly D ≠ 0 := fun h0 ↦ by
      have := List.all_eq_true.mp hDs0 D hD
      simp [(isZero_iff _).mpr h0] at this
    have hlr := ratRootsF_spec hD0 hDz
    have hnr := List.all_eq_true.mp (List.all_eq_true.mp hroots D hD) l hlr
    exact nonRatVals_false ιQ hsQ0' hsqS hnr key
  · obtain ⟨p, hp, hps, hnot⟩ := nonRatVals_spec ιQ hsQ0' hsqS hnr₁
    obtain ⟨q, hq⟩ := key p hp hps
    have hIS := Polynomial.map_dvd ιQ (identCheck_spec hid l)
    rw [Polynomial.map_sub, Polynomial.map_mul, map_C, Polynomial.map_comp] at hIS
    set d := (toPoly (Ds.foldr mul [1])).eval l with hd
    set Γ := (gammaL l gs).map ιQ with hΓ
    have ha : (C l * toPoly w₁ + toPoly w₂).map ιQ = (toPoly (add (smul l w₁) w₂)).map ιQ := by
      rw [toPoly_add, toPoly_smul]
    rw [ha] at hIS
    set a' := (toPoly (add (smul l w₁) w₂)).map ιQ with ha'
    have hsub := sub_dvd_eval_sub a' (C (ιQ q)) (Γ.map C)
    rw [eval_map, eval_map] at hsub
    change a' - C (ιQ q) ∣ Γ.comp a' - Γ.comp (C (ιQ q)) at hsub
    rw [comp_C] at hsub
    have h3 : p ∣ C (ιQ d) * (toPoly w₁).map ιQ - C (Γ.eval (ιQ q)) := by
      have := dvd_add (hps.trans hIS) (hq.trans hsub)
      rwa [sub_add_sub_cancel] at this
    have hΓe : Γ.eval (ιQ q) = ιQ ((gammaL l gs).eval q) := by rw [hΓ, eval_map, eval₂_at_apply]
    have hdS : ιQ d ≠ 0 := (map_ne_zero_iff _ ιQ.injective).mpr hz
    have e : C (ιQ d) * (toPoly w₁).map ιQ - C (Γ.eval (ιQ q)) =
        C (ιQ d) * ((toPoly w₁).map ιQ - C (ιQ ((gammaL l gs).eval q / d))) := by
      rw [hΓe, mul_sub, ← C_mul, ← map_mul, mul_div_cancel₀ _ hz]
    rw [e] at h3
    exact hnot _ ((hp.prime.dvd_or_dvd h3).resolve_left fun hd' ↦
      hp.not_isUnit (isUnit_of_dvd_unit hd' (isUnit_C.mpr hdS.isUnit)))

end Q

section R

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [HasRatRoots R]

lemma toRatL_spec : ∀ {p : CPoly R} {p' : CPoly ℚ}, toRatL p = some p' →
    p = p'.map fun q : ℚ ↦ (q : R)
  | [], p', h => by
    simp only [toRatL, List.mapM_nil, pure, Option.some.injEq] at h
    subst h; rfl
  | r :: p, p', h => by
    simp only [toRatL, List.mapM_cons] at h
    obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨p'', hp'', h⟩ := Option.bind_eq_some_iff.mp h
    simp only [pure, Option.some.injEq] at h
    subst h
    have hqr : (q : R) = r := by
      have := List.find?_some hq
      simpa using this
    rw [List.map_cons, hqr, ← toRatL_spec (p := p) hp'']

lemma toPoly_toRatL {p : CPoly R} {p' : CPoly ℚ} (h : toRatL p = some p') :
    toPoly p = (toPoly p').map (Rat.castHom R) := by
  rw [toRatL_spec h, ← toPoly_map']
  rfl

end R

end CPoly

namespace Differential

section Residue

variable {C' K : Type*} [Field C'] [CharZero C'] [Differential C'[X]] [Field K] [Algebra C'[X] K]
variable [IsFractionRing C'[X] K] [Differential K] [DifferentialAlgebra C'[X] K]

local notation "φ" => algebraMap C'[X] K

/-- **Integer residues of a logarithmic derivative**: if `y′ = (G / s) y`, `y ≠ 0`, then at every
prime `p ∣ s`, `p ∣ G - n s′` for some integer `n` (the order of `y` at `p`). -/
theorem residue_int_of_logDeriv (hD : ∀ P : C'[X], P′ = derivative P) (G s : C'[X]) (hs0 : s ≠ 0)
    (y : K) (hy0 : y ≠ 0) (h : y′ = φ G / φ s * y) (p : C'[X]) (hp : Irreducible p)
    (hps : p ∣ s) : ∃ n : ℤ, p ∣ G - (n : C'[X]) * derivative s := by
  have hinj : Function.Injective φ := IsFractionRing.injective C'[X] K
  obtain ⟨n, u, hu, hy₀⟩ := exists_zpow_mul_isUnitAt hp.prime hy0
  have hy : y = u * φ p ^ n := by rw [hy₀, mul_comm]
  have h1 := deriv_mul_zpow_mul hp.prime u n
  rw [← hy, h, hy, hD] at h1
  have hu0 : u ≠ 0 := fun h0 ↦ hy0 (by rw [hy, h0, zero_mul])
  have hp0 : φ p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp.ne_zero
  have hpn : φ p ^ n ≠ 0 := zpow_ne_zero _ hp0
  have hloc : φ p * (u′ / u) + (n : K) * φ (derivative p) = φ G / φ s * φ p := by
    have := mul_right_cancel₀ hpn (by rw [← h1]; ring :
      φ G / φ s * φ p * u * φ p ^ n = (u′ * φ p + (n : K) * u * φ (derivative p)) * φ p ^ n)
    apply mul_right_cancel₀ hu0
    rw [this, add_mul, mul_assoc, div_mul_cancel₀ _ hu0]
    ring
  obtain ⟨c₁, hc₁⟩ := hps
  have hc₁0 : φ c₁ ≠ 0 := (map_ne_zero_iff _ hinj).mpr fun h0 ↦ hs0 (by rw [hc₁, h0, mul_zero])
  have hreg : u′ / u ∈ regularAt K p hp.prime := by
    rw [div_eq_mul_inv]
    exact mul_mem (deriv_mem_regularAt hp.prime (hu.mem_regularAt hp.prime))
      (hu.inv_mem_regularAt hp.prime)
  have hkey : φ (G - (n : C'[X]) * derivative p * c₁) = φ p * (φ c₁ * (u′ / u)) := by
    rw [hc₁, map_mul] at hloc
    simp only [map_sub, map_mul, map_intCast]
    field_simp at hloc ⊢
    linear_combination -hloc
  have h2 := dvd_of_map_eq_mul_regular hp.prime (mul_mem (algebraMap_mem_regularAt _ c₁) hreg) hkey
  refine ⟨n, ?_⟩
  rw [hc₁, derivative_mul]
  have : G - (n : C'[X]) * (derivative p * c₁ + p * derivative c₁) =
      (G - (n : C'[X]) * derivative p * c₁) - p * ((n : C'[X]) * derivative c₁) := by ring
  rw [this]
  exact dvd_sub h2 (dvd_mul_right p _)

end Residue

end Differential

namespace CPoly

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [HasRatRoots R] [HasNatTest R]
variable {S K : Type*} [Field S] [CharZero S] [Differential S] [Differential S[X]] [Field K]
variable [CharZero K] [Algebra S[X] K] [Differential K[X]]
variable [IsFractionRing S[X] K] [Differential K] [DifferentialAlgebra S[X] K]

local notation "φ" => algebraMap S[X] K

lemma dvd_of_rem_zero' {s e : CPoly R} (h : isZero (divMod e s).2 = true) :
    toPoly e = toPoly (divMod e s).1 * toPoly s := by
  rw [divMod_spec e s, (isZero_iff _).mp h, add_zero]

set_option maxHeartbeats 1600000 in
/-- **The degenerate-pair certificate gives uniqueness**: `y′ + (c η₂ + z η₁) y = 0` has only the
zero solution in `S(x)`, for integers `c ≠ 0` and `z`. -/
theorem hexpDegen_hom (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {Hn₁ Hd₁ Hn₂ Hd₂ : CPoly R} (hHd10 : toPoly Hd₁ ≠ 0) (hHd20 : toPoly Hd₂ ≠ 0)
    (hdeg : hexpDegen Hn₁ Hd₁ Hn₂ Hd₂ = true) (c : ℤ) (hc : c ≠ 0) (z : ℤ) (y : K)
    (h : y′ + (ev K ι (smul (c : R) Hn₂, Hd₂) +
      (z : K) * (φ ((toPoly Hn₁).map ι) / φ ((toPoly Hd₁).map ι))) * y = 0) : y = 0 := by
  have hιinj : Function.Injective ι := ι.injective
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  have hcS : (c : S) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hcK : (c : K) ≠ 0 := Int.cast_ne_zero.mpr hc
  set η₁ := Tower.ηh (K₁ := K) ι Hn₁ Hd₁ with hη₁
  set η₂ := Tower.ηh (K₁ := K) ι Hn₂ Hd₂ with hη₂
  have hev₂ : ev K ι (smul (c : R) Hn₂, Hd₂) = (c : K) * η₂ := by
    rw [ev, toPoly_smul, Polynomial.map_mul, map_C, map_mul, map_intCast, mul_div_assoc,
      C_eq_intCast, map_intCast]
  rw [hev₂] at h
  by_contra hy0
  have hyi0 : y⁻¹ ≠ 0 := inv_ne_zero hy0
  have hlog : logDeriv y⁻¹ = (z : K) * η₁ + (c : K) * η₂ := by
    rw [logDeriv, Derivation.leibniz_inv, smul_eq_mul]
    field_simp
    linear_combination -h
  -- Hermite decompositions: `z η₁ + c η₂ = z r₁ / s₁ + c r₂ / s₂`
  obtain ⟨G₁, hG₁, hsq₁, hdeg₁, -⟩ := hermite_decomp (K := K) ι hD Hn₁ Hd₁ hHd10
  obtain ⟨G₂, hG₂, hsq₂, hdeg₂, -⟩ := hermite_decomp (K := K) ι hD Hn₂ Hd₂ hHd20
  set I₁ := integrateRational Hn₁ Hd₁ with hI₁
  set I₂ := integrateRational Hn₂ Hd₂ with hI₂
  have hdegz : (C (z : S) * (toPoly I₁.r).map ι).degree < ((toPoly I₁.s).map ι).degree :=
    lt_of_le_of_lt (show degree (C (z : S) * (toPoly I₁.r).map ι) ≤ degree ((toPoly I₁.r).map ι)
      by rw [← smul_eq_C_mul]; exact degree_smul_le _ _) hdeg₁
  have hdegc : (C (c : S) * (toPoly I₂.r).map ι).degree < ((toPoly I₂.s).map ι).degree :=
    lt_of_le_of_lt (show degree (C (c : S) * (toPoly I₂.r).map ι) ≤ degree ((toPoly I₂.r).map ι)
      by rw [← smul_eq_C_mul]; exact degree_smul_le _ _) hdeg₂
  have hW := Differential.deriv_eq_zero_of_add_proper₂_eq_logDeriv hD _ _ _ _ hsq₁ hsq₂ hdegz hdegc
    ((z : K) * G₁ + (c : K) * G₂) y⁻¹ hyi0 (by
      rw [hlog, map_add, Derivation.leibniz, Derivation.leibniz, hG₁, hG₂,
        Derivation.map_intCast, Derivation.map_intCast, map_mul, map_mul, C_eq_intCast,
        C_eq_intCast, map_intCast, map_intCast]
      simp only [smul_eq_mul]
      ring)
  rw [map_add, Derivation.leibniz, Derivation.leibniz, hG₁, hG₂,
    Derivation.map_intCast, Derivation.map_intCast] at hW
  simp only [smul_eq_mul] at hW
  have hsimple : logDeriv y⁻¹ = (z : K) * (φ ((toPoly I₁.r).map ι) / φ ((toPoly I₁.s).map ι)) +
      (c : K) * (φ ((toPoly I₂.r).map ι) / φ ((toPoly I₂.s).map ι)) := by
    rw [hlog]; linear_combination hW
  -- unpack the certificate
  unfold hexpDegen at hdeg
  simp only [Bool.and_eq_true] at hdeg
  rw [← hI₁, ← hI₂] at hdeg
  generalize hs : lcmSq I₁.s I₂.s = s at hdeg
  generalize hN₁ : mul I₁.r (divMod s I₁.s).1 = N₁ at hdeg
  generalize hN₂ : mul I₂.r (divMod s I₂.s).1 = N₂ at hdeg
  generalize hρ₁ : resPoly s N₁ = ρ₁ at hdeg
  generalize hρ₂ : resPoly s N₂ = ρ₂ at hdeg
  obtain ⟨⟨⟨⟨hd₁, hd₂⟩, hr₁⟩, hr₂⟩, hQ⟩ := hdeg
  -- the rational coefficients
  cases hsQ : toRatL s with
  | none => simp [hsQ] at hQ
  | some sQ =>
  cases hq₁ : toRatL ρ₁ with
  | none => simp [hsQ, hq₁] at hQ
  | some q₁ =>
  cases hq₂ : toRatL ρ₂ with
  | none => simp [hsQ, hq₁, hq₂] at hQ
  | some q₂ =>
  simp only [hsQ, hq₁, hq₂] at hQ
  set ιQ : ℚ →+* S := ι.comp (Rat.castHom R) with hιQ
  have hmapQ : ∀ {p : CPoly R} {p' : CPoly ℚ}, toRatL p = some p' →
      (toPoly p).map ι = (toPoly p').map ιQ := fun hp ↦ by
    rw [toPoly_toRatL hp, Polynomial.map_map]
  have hQ' : ((!isZero sQ) = true ∧ squarefreeCheck sQ = true) ∧
      (degenCertQ sQ q₁ q₂ = true ∨ Kron.genResCertHead sQ [q₂, q₁] = true) := by
    rw [Bool.or_eq_true] at hQ
    rcases hQ with hQ | hQ
    · refine ⟨?_, Or.inl hQ⟩
      unfold degenCertQ at hQ
      simp only [Bool.and_eq_true] at hQ
      exact hQ.1.1
    · simp only [Bool.and_eq_true] at hQ
      exact ⟨hQ.1, Or.inr hQ.2⟩
  obtain ⟨⟨hsQ0, hsqf⟩, hQ⟩ := hQ'
  have hsQ0' : toPoly sQ ≠ 0 := fun h0 ↦ by simp [(isZero_iff _).mpr h0] at hsQ0
  -- `s` over `S`: separable
  set st := (toPoly sQ).map ιQ with hst
  have hsep : st.Separable :=
    (PerfectField.separable_iff_squarefree.mpr (squarefreeCheck_sound hsqf)).map
  have hsqS : Squarefree st := hsep.squarefree
  have hst0 : st ≠ 0 := (Polynomial.map_ne_zero_iff ιQ.injective).mpr hsQ0'
  have hsS : (toPoly s).map ι = st := hmapQ hsQ
  have hs0 : toPoly s ≠ 0 := fun h0 ↦ hst0 (by rw [← hsS, h0, Polynomial.map_zero])
  -- `ηᵢ = Nᵢ / s`
  have hfrac : ∀ {r sᵢ N : CPoly R}, isZero (divMod s sᵢ).2 = true → mul r (divMod s sᵢ).1 = N →
      Squarefree ((toPoly sᵢ).map ι) →
      φ ((toPoly r).map ι) / φ ((toPoly sᵢ).map ι) = φ ((toPoly N).map ι) / φ st := by
    intro r sᵢ N hd hN hsq
    have e1 := dvd_of_rem_zero' hd
    have hq0 : toPoly (divMod s sᵢ).1 ≠ 0 := fun h0 ↦ hs0 (by rw [e1, h0, zero_mul])
    have hφq : φ ((toPoly (divMod s sᵢ).1).map ι) ≠ 0 := map_toPoly_ne_zero ι hq0
    have hφs : φ ((toPoly sᵢ).map ι) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr hsq.ne_zero
    rw [← hsS, e1, ← hN, toPoly_mul]
    simp only [Polynomial.map_mul, map_mul]
    field_simp
  rw [hfrac hd₁ hN₁ hsq₁, hfrac hd₂ hN₂ hsq₂] at hsimple
  set G := C (z : S) * (toPoly N₁).map ι + C (c : S) * (toPoly N₂).map ι with hG
  have hφst : φ st ≠ 0 := (map_ne_zero_iff _ hinj).mpr hst0
  have hy' : (y⁻¹)′ = φ G / φ st * y⁻¹ := by
    rw [logDeriv] at hsimple
    rw [hG, map_add, map_mul, map_mul, C_eq_intCast, C_eq_intCast, map_intCast, map_intCast]
    field_simp at hsimple ⊢
    linear_combination hsimple
  have hres := fun p hp hps ↦
    Differential.residue_int_of_logDeriv hD G st hst0 y⁻¹ hyi0 hy' p hp hps
  -- the residue polynomials over `S`
  have hρS : ∀ {ρ N : CPoly R} {q : CPoly ℚ}, toRatL ρ = some q →
      isZero (divMod (sub (mul ρ (deriv s)) N) s).2 = true →
      st ∣ (toPoly q).map ιQ * derivative st - (toPoly N).map ι := by
    intro ρ N q hq hr
    have := Polynomial.map_dvd ι (⟨_, by rw [dvd_of_rem_zero' hr, mul_comm]⟩ :
      toPoly s ∣ toPoly (sub (mul ρ (deriv s)) N))
    rw [toPoly_sub, toPoly_mul, toPoly_deriv, Polynomial.map_sub, Polynomial.map_mul,
      ← derivative_map, hsS, hmapQ hq] at this
    exact this
  have hρ₁S := hρS hq₁ hr₁
  have hρ₂S := hρS hq₂ hr₂
  -- `a = λ ρ₁ + ρ₂` is rational modulo every prime of `s`
  set l : ℚ := (z : ℚ) / c with hl
  have hcQ : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc
  have key : ∀ p : S[X], Irreducible p → p ∣ st →
      ∃ q : ℚ, p ∣ (toPoly (add (smul l q₁) q₂)).map ιQ - C (ιQ q) := by
    intro p hp hps
    obtain ⟨n, hn⟩ := hres p hp hps
    have h1 : p ∣ (C (z : S) * (toPoly q₁).map ιQ + C (c : S) * (toPoly q₂).map ιQ - (n : S[X])) *
        derivative st := by
      have : (C (z : S) * (toPoly q₁).map ιQ + C (c : S) * (toPoly q₂).map ιQ - (n : S[X])) *
          derivative st = C (z : S) * ((toPoly q₁).map ιQ * derivative st - (toPoly N₁).map ι) +
            C (c : S) * ((toPoly q₂).map ιQ * derivative st - (toPoly N₂).map ι) +
            (G - (n : S[X]) * derivative st) := by rw [hG]; ring
      rw [this]
      exact dvd_add (dvd_add (dvd_mul_of_dvd_right (hps.trans hρ₁S) _)
        (dvd_mul_of_dvd_right (hps.trans hρ₂S) _)) hn
    have hpd : ¬p ∣ derivative st := fun hd ↦ hp.not_isUnit (hsep.isUnit_of_dvd' hps hd)
    have h2 := (hp.prime.dvd_or_dvd h1).resolve_right hpd
    refine ⟨(n : ℚ) / c, ?_⟩
    have hιl : ιQ l = (z : S) / c := by rw [hl, map_div₀, map_intCast, map_intCast]
    have hιn : ιQ ((n : ℚ) / c) = (n : S) / c := by rw [map_div₀, map_intCast, map_intCast]
    have e : C (z : S) * (toPoly q₁).map ιQ + C (c : S) * (toPoly q₂).map ιQ - (n : S[X]) =
        C (c : S) * ((toPoly (add (smul l q₁) q₂)).map ιQ - C (ιQ ((n : ℚ) / c))) := by
      rw [toPoly_add, toPoly_smul, Polynomial.map_add, Polynomial.map_mul, map_C, hιl, hιn,
        ← C_eq_intCast]
      rw [mul_sub, mul_add, ← mul_assoc, ← C_mul, ← C_mul, mul_div_cancel₀ _ hcS,
        mul_div_cancel₀ _ hcS]
    rw [e] at h2
    exact (hp.prime.dvd_or_dvd h2).resolve_left fun hd ↦
      hp.not_isUnit (isUnit_of_dvd_unit hd (isUnit_C.mpr hcS.isUnit))
  rcases hQ with hQ | hH
  · refine degenCertQ_sound ιQ hQ l 1 (Or.inr one_ne_zero) fun p hp hps ↦ ?_
    obtain ⟨q, hq⟩ := key p hp hps
    refine ⟨q, ?_⟩
    rwa [map_one, C_1, one_mul, ← map_C, ← Polynomial.map_mul, ← Polynomial.map_add, ← toPoly_smul,
      ← toPoly_add]
  · have := Kron.genResCertHead_sound ιQ sQ [q₂, q₁] hH [1, l] rfl fun p hp hps ↦ by
      obtain ⟨q, hq⟩ := key p hp hps
      have e : lcomb [1, l] [q₂, q₁] = toPoly (add (smul l q₁) q₂) := by
        rw [Kron.lcomb_two, toPoly_add, toPoly_smul]
        simp only [List.getD_cons_zero, List.getD_cons_succ, C_1, one_mul]
        ring
      exact ⟨q, by rw [e]; exact hq⟩
    simp at this

/-- **The complete independence certificate** for two hyperexponentials: `hexpHexpIndepFull`
(coprime denominators, or Hermite parts), or the degenerate-pair certificate `hexpDegen`. -/
def hexpHexpIndepAll (Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ : CPoly R) : Bool :=
  hexpHexpIndepFull Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ || hexpDegen Hn₁ Hd₁ Hn₂ Hd₂

/-- **The complete certificate gives uniqueness.** -/
theorem hexpHexpIndepAll_hom (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ : CPoly R}
    (hHn10 : toPoly Hn₁ ≠ 0) (hHd10 : toPoly Hd₁ ≠ 0)
    (hcop₁ : IsCoprime (toPoly Hn₁) (toPoly Hd₁)) (hcert₁ : hyperexpMonomialCheck Hn₁ Hd₁ μ₁ = true)
    (hHn20 : toPoly Hn₂ ≠ 0) (hHd20 : toPoly Hd₂ ≠ 0)
    (hcop₂ : IsCoprime (toPoly Hn₂) (toPoly Hd₂)) (hcert₂ : hyperexpMonomialCheck Hn₂ Hd₂ μ₂ = true)
    (hind : hexpHexpIndepAll Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ = true) (c : ℤ) (hc : c ≠ 0) (z : ℤ) (y : K)
    (h : y′ + (ev K ι (smul (c : R) Hn₂, Hd₂) +
      (z : K) * (φ ((toPoly Hn₁).map ι) / φ ((toPoly Hd₁).map ι))) * y = 0) : y = 0 := by
  rw [hexpHexpIndepAll, Bool.or_eq_true] at hind
  rcases hind with hind | hind
  · exact hexpHexpIndepFull_hom ι hD hHn10 hHd10 hcop₁ hcert₁ hHn20 hHd20 hcop₂ hcert₂ hind c hc z
      y h
  · exact hexpDegen_hom ι hD hHd10 hHd20 hind c hc z y h

end CPoly
