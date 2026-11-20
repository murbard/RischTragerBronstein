import RischTragerBronstein.Mixed.NKBasisExists

/-!
# Non-constant curves over an exponential level: the derivation along branches

`S : CurveData C L` over a differential field `C` with `x′ = a′ x` (`a′ ∈ C`; an exponential level
`x = t = eᵃ` over `C = Fₘ`).

* Above infinity (`x = s⁻ᴺ`) the derivation is `δ − (a′/N) s d/ds` (`infSpeedE`): it keeps the
  orders (`infOrd_derivE`) and acts on the coefficients by `cₖ ↦ cₖ′ − (k a′/N) cₖ`
  (`coeff_embG_deriv_infE`).
* Above `x = 0` (`x = sᴺ`) it is `δ + (a′/N) s d/ds` (`zeroSpeedE`), so derivatives of elements
  without finite poles have no pole above `0` either (`regular_zero_deriv`).
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section Speed

variable {C K : Type*} [Field C] [CharZero C] [Field K] [CharZero K] [Algebra C K] [Differential C]
  [Differential K]

/-- The speed of the branch `x = s⁻ᴺ` for `x′ = a′ x`: `−(a′/N) s`. -/
noncomputable def infSpeedE (b : C) (N : ℕ) : LaurentSeries K :=
  single (1 : ℤ) (-(algebraMap C K b) / N)

lemma dS_infSpeedE (b : C) (N : ℕ) (hN : 0 < N) :
    dS (infSpeedE (K := K) b N) (single (-(N : ℤ)) 1) =
      substHom (single (-(N : ℤ)) (1 : K)) (Polynomial.C b * X) := by
  have hN' : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  rw [map_mul, SuperData.substHom_C, substHom_apply, Polynomial.map_X, aeval_X, dS_apply,
    coefDeriv_single, Differential.deriv.map_one_eq_zero, HahnSeries.single_eq_zero, zero_add]
  have hd : derivative K (single (-(N : ℤ)) (1 : K)) = single (-(N : ℤ) - 1) (-(N : K)) := by
    have := Differential.derivation_single (K := K) (-(N : ℤ))
    rw [LaurentSeries.derivation_apply] at this
    rw [this]; push_cast; rfl
  rw [hd, infSpeedE, HahnSeries.single_mul_single, HahnSeries.C_mul_eq_smul]
  have e : (1 : ℤ) + (-(N : ℤ) - 1) = -(N : ℤ) := by ring
  rw [e]
  ext k
  rw [HahnSeries.coeff_smul, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs
  · field_simp; simp
  · simp

/-- **Along a branch above infinity**: `(z′)ₖ = zₖ′ − (k a′/N) zₖ`. -/
lemma coeff_dS_infSpeedE (b : C) (N : ℕ) (E : LaurentSeries K) (k : ℤ) :
    (dS (infSpeedE (K := K) b N) E).coeff k =
      (E.coeff k)′ - algebraMap C K b * (k / N) * E.coeff k := by
  rw [dS_apply, HahnSeries.coeff_add, coeff_coefDeriv, infSpeedE]
  have e := HahnSeries.coeff_single_mul_add (r := -(algebraMap C K b) / N) (b := (1 : ℤ))
    (a := k - 1) (x := derivative K E)
  rw [sub_add_cancel] at e
  rw [e, derivative_coeff, sub_add_cancel]
  push_cast
  ring

lemma lowerBd_dS_infSpeedE (b : C) (N : ℕ) {E : LaurentSeries K} {m : ℤ} (hE : LowerBd E m) :
    LowerBd (dS (infSpeedE (K := K) b N) E) m := fun k hk ↦ by
  rw [coeff_dS_infSpeedE, hE k hk, Differential.deriv.map_zero]; ring

/-- The speed of the branch `x = sᴺ` above `0` for `x′ = a′ x`: `(a′/N) s`. -/
noncomputable def zeroSpeedE (b : C) (N : ℕ) : LaurentSeries K :=
  single (1 : ℤ) (algebraMap C K b / N)

lemma dS_zeroSpeedE (b : C) (N : ℕ) (hN : 0 < N) :
    dS (zeroSpeedE (K := K) b N) (HahnSeries.C 0 + single (N : ℤ) 1) =
      substHom (HahnSeries.C 0 + single (N : ℤ) (1 : K)) (Polynomial.C b * X) := by
  have hN' : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  rw [map_mul, SuperData.substHom_C, substHom_apply, Polynomial.map_X, aeval_X, dS_apply,
    map_add, coefDeriv_C, coefDeriv_single, Differential.deriv.map_one_eq_zero,
    HahnSeries.single_eq_zero, Differential.deriv.map_zero, HahnSeries.C_zero, zero_add, zero_add,
    zero_add]
  have hd : derivative K (single (N : ℤ) (1 : K)) = single ((N : ℤ) - 1) (N : K) := by
    have := Differential.derivation_single (K := K) (N : ℤ)
    rw [LaurentSeries.derivation_apply] at this
    rw [this, Int.cast_natCast]
  rw [hd, zeroSpeedE, HahnSeries.single_mul_single, HahnSeries.C_mul_eq_smul]
  have e : (1 : ℤ) + ((N : ℤ) - 1) = (N : ℤ) := by ring
  rw [e]
  ext k
  rw [HahnSeries.coeff_smul, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs
  · field_simp; simp
  · simp

lemma lowerBd_dS_zeroSpeedE (b : C) (N : ℕ) {E : LaurentSeries K} (hE : LowerBd E 0) :
    LowerBd (dS (zeroSpeedE (K := K) b N) E) 0 := by
  rw [dS_apply]
  refine LowerBd.add (CurveData.lowerBd_coefDeriv hE) ?_
  have := (lowerBd_single (1 : ℤ) (algebraMap C K b / N)).mul hE.derivative
  exact this.mono (by omega)

end Speed

namespace CurveData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K]

variable (S : CurveData C L) (b : C) (hx : S.x′ = aeval S.x (Polynomial.C b * X))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

include hx hK in
/-- **Along a branch above infinity** (exponential level): `(z′)ₖ = zₖ′ − (k a′/N) zₖ`. -/
lemma embG_deriv_infE (N : ℕ) (hN : 0 < N) (r : LaurentSeries K)
    (hr : (S.F.map (infSub N)).eval r = 0) (z : C⟮S.x⟯⟮S.y⟯) :
    S.embG (infSub N) (infSub_injective N hN) r hr
      ⟨(z : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx z z.2⟩ =
      dS (infSpeedE b N) (S.embG (infSub N) (infSub_injective N hN) r hr z) := by
  have hd := S.embG_dSW' (Polynomial.C b * X) hx hK (infSpeedE b N) (single (-(N : ℤ)) 1)
    (dS_infSpeedE b N hN) (infSub N) (infSub_injective N hN)
    (fun P ↦ by rw [SuperData.infSub_eq_subst]) r hr (z : L) z.2
  simpa only [Subtype.coe_eta] using hd

include hx hK in
/-- **The derivation keeps the orders above infinity** (exponential level). -/
theorem infOrd_derivE (z : C⟮S.x⟯⟮S.y⟯) (k : ℤ) (hz : S.InfOrd K z k) :
    S.InfOrd K ⟨(z : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx z z.2⟩ k := by
  intro N hN l hl r hr
  rw [S.embG_deriv_infE b hx hK N (Nat.pos_of_ne_zero hN) r (S.root_of_mem hl hr) z]
  exact lowerBd_dS_infSpeedE b N (hz N hN l hl r hr)

include hx hK in
/-- **Derivatives have no pole above `x = 0`** (exponential level). -/
theorem regular_zero_deriv (z : C⟮S.x⟯⟮S.y⟯) (hz : S.RegularFinite K z) (N : ℕ) (hN : N ≠ 0)
    (l : List (LaurentSeries K))
    (hl : S.F.map (branchSub N (0 : K)) = (l.map fun r ↦ X - Polynomial.C r).prod)
    (r : LaurentSeries K) (hr : r ∈ l) :
    0 ≤ (S.embG (branchSub N 0) (branchSub_injective N (Nat.pos_of_ne_zero hN) 0) r
      (S.root_of_mem hl hr) ⟨(z : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx z z.2⟩).order := by
  have hN0 := Nat.pos_of_ne_zero hN
  have hd := S.embG_dSW' (Polynomial.C b * X) hx hK (zeroSpeedE b N)
    (HahnSeries.C 0 + single (N : ℤ) 1) (dS_zeroSpeedE b N hN0) (branchSub N 0)
    (branchSub_injective N hN0 0) (fun P ↦ by rw [SuperData.branchSub_eq_subst])
    r (S.root_of_mem hl hr) (z : L) z.2
  simp only [Subtype.coe_eta] at hd
  rw [hd]
  refine order_nonneg_of_lowerBd _ (lowerBd_dS_zeroSpeedE b N ?_)
  exact lowerBd_of_order_nonneg (hz 0 N hN l hl r hr)

/-- The numerators of the rescaled derivation matrix at an exponential level (denominators
`x^{rᵢ} S₀`). -/
noncomputable def pqE {m : ℕ} (r : Fin m → ℕ) (P : Fin m → Fin m → C[X]) (S0 : C[X]) (i j : Fin m) :
    C[X] :=
  X ^ r j * P i j - if i = j then Polynomial.C ((r i : C) * b) * X ^ r i * S0 else 0

include hx in
/-- **The derivation matrix of the rescaled basis** `x^{−rᵢ} wᵢ` (exponential level). -/
lemma deriv_wTilE {m : ℕ} (w : Fin m → C⟮S.x⟯⟮S.y⟯) (r : Fin m → ℕ) (S0 : C[X])
    (P : Fin m → Fin m → C[X])
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
      S.polyE S0 = ∑ j, S.polyE (P i j) * w j) (i : Fin m) :
    (S.wTil w r i : L)′ * aeval S.x (X ^ r i * S0) =
      ∑ j, aeval S.x (pqE b r P S0 i j) * (S.wTil w r j : L) := by
  classical
  have hx0 : S.x ≠ 0 := S.htr.ne_zero
  have hPi : (w i : L)′ * aeval S.x S0 = ∑ j, aeval S.x (P i j) * (w j : L) := by
    have := congrArg (fun t : C⟮S.x⟯⟮S.y⟯ ↦ (t : L)) (hP i)
    simpa [polyE] using this
  have hxe : S.x′ = algebraMap C L b * S.x := by rw [hx, map_mul, aeval_C, aeval_X]
  have hwt : ∀ j, (S.wTil w r j : L) = (S.x ^ r j)⁻¹ * (w j : L) := fun j ↦ by
    simp [wTil, polyE]
  have hR : ∑ j, aeval S.x (pqE b r P S0 i j) * (S.wTil w r j : L) =
      ∑ j, aeval S.x (P i j) * (w j : L) -
        (r i : L) * algebraMap C L b * aeval S.x S0 * (w i : L) := by
    simp only [pqE, hwt, map_sub, sub_mul, Finset.sum_sub_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [map_mul, map_pow, aeval_X]
      field_simp
    · rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [Ne.symm hj]) (by simp)]
      simp only [ite_true, map_mul, map_pow, aeval_X, aeval_C, map_natCast]
      field_simp
  have hL : (S.wTil w r i : L)′ * aeval S.x (X ^ r i * S0) =
      (w i : L)′ * aeval S.x S0 - (r i : L) * algebraMap C L b * aeval S.x S0 * (w i : L) := by
    rw [hwt, Derivation.leibniz, Derivation.leibniz_inv, Derivation.leibniz_pow, hxe]
    simp only [smul_eq_mul, nsmul_eq_mul, map_mul, map_pow, aeval_X]
    rcases Nat.eq_zero_or_pos (r i) with h0 | hpos
    · rw [h0]; simp
    · have e : S.x ^ (r i - 1) = S.x ^ r i / S.x := by
        rw [eq_div_iff hx0, ← pow_succ]; congr 1; omega
      rw [e]
      field_simp
      ring
  rw [hR, hL, hPi]

include hx hK in
/-- Dropping a factor `x` from the multiplier: derivatives have no pole above `0`. -/
lemma regularFinite_dropX [IsAlgClosed K] (z : C⟮S.x⟯⟮S.y⟯) (hz : S.RegularFinite K z) (R S0 : C[X])
    (hRS : R = X * S0)
    (hR : S.RegularFinite K (S.polyE R * ⟨(z : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx z z.2⟩)) :
    S.RegularFinite K (S.polyE S0 * ⟨(z : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx z z.2⟩) := by
  intro a N hN l hl r hr
  have hN0 := Nat.pos_of_ne_zero hN
  by_cases ha : a = 0
  · subst ha
    rw [map_mul, S.embG_polyX]
    refine order_nonneg_of_lowerBd _ ?_
    have h1 := lowerBd_of_order_nonneg (S.regular_zero_deriv b hx hK z hz N hN l hl r hr)
    have := (lowerBd_branchSub_nonneg (C := C) N (0 : K) S0).mul h1
    rwa [zero_add] at this
  · have h := hR a N hN l hl r hr
    rw [hRS, S.polyE_mul, mul_assoc, map_mul, S.embG_polyX] at h
    have hX0 : (branchSub (C := C) (K := K) N a X).order = 0 := by
      have := order_branchSub (C := C) (K := K) N hN0 a X X_ne_zero
      rw [this]
      have : (X.map (algebraMap C K)).rootMultiplicity a = 0 := by
        rw [Polynomial.map_X, rootMultiplicity_eq_zero]
        simp [ha]
      rw [this]; simp
    have hX0' : branchSub (C := C) (K := K) N a X ≠ 0 :=
      (map_ne_zero_iff _ (branchSub_injective N hN0 a)).mpr X_ne_zero
    by_cases hz0 : S.embG (branchSub N a) (branchSub_injective N hN0 a) r (S.root_of_mem hl hr)
        (S.polyE S0 * ⟨(z : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx z z.2⟩) = 0
    · rw [hz0, HahnSeries.order_zero]
    · rw [HahnSeries.order_mul hX0' hz0, hX0, zero_add] at h
      exact h

include hK in
/-- `γ′ = γ c′/(n c)` for the leading coefficient `γ` of a root above infinity (`γⁿ = −c`). -/
lemma deriv_root_lead_gen (n : ℕ) (hn0 : 0 < n) (γ : K) (c : C) (hc : c ≠ 0)
    (hγ : γ ^ n = -algebraMap C K c) (j : ℕ) :
    (γ ^ j)′ = (j : K) * γ ^ j * algebraMap C K (c′ / (n * c)) := by
  have hn' : (n : K) ≠ 0 := by exact_mod_cast hn0.ne'
  have hcK : algebraMap C K c ≠ 0 := (map_ne_zero_iff _ (algebraMap C K).injective).mpr hc
  have hγ0 : γ ≠ 0 := by
    intro h0; rw [h0, zero_pow hn0.ne'] at hγ; exact hcK (neg_eq_zero.mp hγ.symm)
  have h1 : (γ ^ n)′ = -algebraMap C K c′ := by rw [hγ, map_neg, hK]
  rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at h1
  have hγ' : γ′ = γ * algebraMap C K (c′ / (n * c)) := by
    rw [map_div₀, map_mul, map_natCast]
    have hpow : γ ^ n = γ * γ ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    field_simp
    have h2 : (n : K) * γ ^ (n - 1) * γ′ * γ = -algebraMap C K c′ * γ := by rw [← h1]; ring
    have h3 : (n : K) * γ′ * γ ^ n = -algebraMap C K c′ * γ := by rw [hpow, ← h2]; ring
    rw [hγ] at h3
    linear_combination -h3
  rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, hγ']
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · have : γ ^ j = γ ^ (j - 1) * γ := by rw [← pow_succ]; congr 1; omega
    rw [this]; ring

include hx hK in
/-- **The limit of the derivation matrix at the single place at infinity** (exponential level). -/
theorem nk_inf_struct_exp (n d : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natDegree = d)
    (hw : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ n * (S.F.coeff i).natDegree < d * (n - i))
    (hcop : Nat.Coprime n d) (N : ℕ) (hN : 0 < N) (r : LaurentSeries K)
    (hr : (S.F.map (infSub N)).eval r = 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → C⟮S.x⟯⟮S.y⟯) (W : ι → C[X][X]) (Q : ι → C[X]) (hQ : ∀ i, Q i ≠ 0)
    (hWQ : ∀ i, (w i : L) * aeval S.x (Q i) = S.evXY (W i)) (hW0 : ∀ i, W i ≠ 0)
    (hWn : ∀ i, (W i).natDegree < n)
    (hwin : ∀ i, -(n : ℤ) < (wtW n d (W i) : ℤ) - n * (Q i).natDegree ∧
      (wtW n d (W i) : ℤ) - n * (Q i).natDegree ≤ 0)
    (hdist : ∀ i j, (wtW n d (W i) : ℤ) - n * (Q i).natDegree =
      (wtW n d (W j) : ℤ) - n * (Q j).natDegree → i = j)
    (R : ι → C[X]) (hR : ∀ i, R i ≠ 0) (P : ι → ι → C[X])
    (hPR : ∀ i j, (P i j).natDegree ≤ (R i).natDegree)
    (hD : ∀ i, (w i : L)′ * aeval S.x (R i) = ∑ j, aeval S.x (P i j) * (w j : L)) :
    (∀ i j, (P i j).coeff (R i).natDegree / (R i).leadingCoeff ≠ 0 →
      (wtW n d (W j) : ℤ) - n * (Q j).natDegree ≤ (wtW n d (W i) : ℤ) - n * (Q i).natDegree) ∧
    (∀ i, ∃ j0 < n, (W i).coeff j0 ≠ 0 ∧
      wtW n d (W i) = n * ((W i).coeff j0).natDegree + j0 * d ∧
      (P i i).coeff (R i).natDegree / (R i).leadingCoeff =
        (((W i).coeff j0).leadingCoeff / (Q i).leadingCoeff)′ /
          (((W i).coeff j0).leadingCoeff / (Q i).leadingCoeff) +
        (j0 : C) * ((S.F.coeff 0).leadingCoeff′ / (n * (S.F.coeff 0).leadingCoeff)) +
        (((wtW n d (W i) : ℤ) - n * (Q i).natDegree : ℤ) : C) / n * b) := by
  classical
  set Λ : ι → ι → C := fun i j ↦ (P i j).coeff (R i).natDegree / (R i).leadingCoeff with hΛ
  set v : ι → ℤ := fun i ↦ (wtW n d (W i) : ℤ) - n * (Q i).natDegree with hv
  set E : ι → LaurentSeries K := fun i ↦ S.embG (infSub N) (infSub_injective N hN) r hr (w i)
    with hE
  have hlead := fun i ↦ S.embG_lead_inf n d hn hn0 ha0 hd hw hcop N hN r hr (w i) (W i) (Q i) (hQ i)
    (hWQ i) (hW0 i) (hWn i)
  have hE0 : ∀ i, E i ≠ 0 := fun i ↦ (hlead i).1
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hn0
  have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
  -- the orders `oᵢ ∈ [0, N)`
  set o : ι → ℤ := fun i ↦ (E i).order with ho
  have hno : ∀ i, (n : ℤ) * o i = -((N : ℤ) * v i) := fun i ↦ (hlead i).2.1
  have ho0 : ∀ i, 0 ≤ o i := fun i ↦ by
    have := hno i; have := (hwin i).2; nlinarith
  have hoN : ∀ i, o i < N := fun i ↦ by
    have := hno i; have := (hwin i).1; nlinarith
  have hoinj : ∀ i j, o i = o j → i = j := fun i j hij ↦ by
    refine hdist i j ?_
    have h1 := hno i; have h2 := hno j
    rw [hij] at h1
    have : (N : ℤ) * v i = N * v j := by linarith
    exact mul_left_cancel₀ hNpos.ne' this
  have hvo : ∀ i j, v j ≤ v i ↔ o i ≤ o j := fun i j ↦ by
    have h1 := hno i; have h2 := hno j
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have hLB : ∀ i, LowerBd (E i) 0 := fun i k hk ↦
    HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hk (ho0 i))
  have hlc : ∀ i, (E i).coeff (o i) ≠ 0 := fun i ↦ by
    rw [ho]; dsimp only
    rw [← HahnSeries.leadingCoeff_eq]
    exact HahnSeries.leadingCoeff_ne_zero.mpr (hE0 i)
  have hbelow : ∀ i k, k < o i → (E i).coeff k = 0 := fun i k hk ↦
    HahnSeries.coeff_eq_zero_of_lt_order hk
  -- the key identity
  have hkey : ∀ i, ∀ k : ℤ, 0 ≤ k → k < N →
      ((E i).coeff k)′ - algebraMap C K b * (k / N) * (E i).coeff k =
        ∑ j, algebraMap C K (Λ i j) * (E j).coeff k := by
    intro i k hk0 hkN
    have hmem := S.derivClosedXYW' (Polynomial.C b * X) hx (w i) (w i).2
    have hid : (⟨(w i : L)′, hmem⟩ : C⟮S.x⟯⟮S.y⟯) * ⟨aeval S.x (R i), S.aeval_mem _⟩ =
        ∑ j, ⟨aeval S.x (P i j), S.aeval_mem _⟩ * w j := Subtype.ext (by
      push_cast
      exact hD i)
    have hemb := congrArg (S.embG (infSub N) (infSub_injective N hN) r hr) hid
    rw [map_mul, map_sum, S.embG_polyX] at hemb
    simp only [map_mul, S.embG_polyX] at hemb
    have hR0 := infSub_ne_zero (K := K) N hN (R i) (hR i)
    have hdiv : S.embG (infSub N) (infSub_injective N hN) r hr ⟨(w i : L)′, hmem⟩ =
        ∑ j, (infSub N (P i j) * (infSub N (R i))⁻¹) * E j := by
      have : S.embG (infSub N) (infSub_injective N hN) r hr ⟨(w i : L)′, hmem⟩ =
          (∑ j, infSub N (P i j) * E j) * (infSub N (R i))⁻¹ := by
        rw [← hemb, mul_assoc, mul_inv_cancel₀ hR0, mul_one]
      rw [this, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have hL : (S.embG (infSub N) (infSub_injective N hN) r hr ⟨(w i : L)′, hmem⟩).coeff k =
        ((E i).coeff k)′ - algebraMap C K b * (k / N) * (E i).coeff k := by
      rw [S.embG_deriv_infE b hx hK N hN r hr (w i), coeff_dS_infSpeedE]
    rw [← hL, hdiv, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hρ := lowerBd_infSub_div (K := K) N hN (P i j) (R i) (hR i) (hPR i j)
    have e : infSub N (P i j) * (infSub N (R i))⁻¹ * E j =
        HahnSeries.C (algebraMap C K (Λ i j)) * E j +
        (infSub N (P i j) * (infSub N (R i))⁻¹ -
          HahnSeries.C (algebraMap C K (Λ i j))) * E j := by ring
    rw [e, HahnSeries.coeff_add, LaurentSeries.coeff_C_mul, (hρ.mul (hLB j)) k (by omega), add_zero]
  -- triangularity
  have htri : ∀ i j, Λ i j ≠ 0 → o i ≤ o j := by
    intro i j hij
    by_contra hcon
    have hlt : o j < o i := by push Not at hcon; exact hcon
    -- the nonzero entry of least order
    set J := Finset.univ.filter fun j ↦ Λ i j ≠ 0 with hJ
    have hJne : J.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
    obtain ⟨j1, hj1J, hj1min⟩ := J.exists_min_image o hJne
    have hj1 : Λ i j1 ≠ 0 := (Finset.mem_filter.mp hj1J).2
    have hle : o j1 ≤ o j := hj1min j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
    have h := hkey i (o j1) (ho0 j1) (hoN j1)
    rw [hbelow i (o j1) (by omega), Derivation.map_zero (Differential.deriv (R := K)), mul_zero,
      sub_zero, Finset.sum_eq_single j1] at h
    · exact mul_ne_zero ((map_ne_zero_iff _ (algebraMap C K).injective).mpr hj1) (hlc j1) h.symm
    · intro j2 _ hj2
      by_cases h2 : Λ i j2 = 0
      · rw [h2, map_zero, zero_mul]
      · have h3 : o j1 ≤ o j2 := hj1min j2 (by simp [hJ, h2])
        have h4 : o j1 < o j2 := lt_of_le_of_ne h3 fun h5 ↦ hj2 (hoinj _ _ h5).symm
        rw [hbelow j2 _ h4, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j1) h
  -- the expansion matrix
  refine ⟨fun i j hij ↦ (hvo i j).mpr (htri i j hij), ?_⟩
  · -- the diagonal
    intro i
    obtain ⟨-, -, j0, hj0n, hj0, hwt, hlcE⟩ := hlead i
    refine ⟨j0, hj0n, hj0, hwt, ?_⟩
    obtain ⟨β, hβ⟩ : ∃ β : C, β = ((W i).coeff j0).leadingCoeff / (Q i).leadingCoeff := ⟨_, rfl⟩
    rw [← hβ] at hlcE ⊢
    have hβ0 : β ≠ 0 := hβ ▸ div_ne_zero (leadingCoeff_ne_zero.mpr hj0) (leadingCoeff_ne_zero.mpr (hQ i))
    set c : C := (S.F.coeff 0).leadingCoeff with hc
    have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr ha0
    have hγ := root_lead_inf S.F S.monic n d N hn hn0 hN ha0 hd hw r hr
    have h := hkey i (o i) (ho0 i) (hoN i)
    rw [Finset.sum_eq_single i] at h
    · have hEi : (E i).coeff (o i) = algebraMap C K β * r.leadingCoeff ^ j0 := by
        rw [← hlcE, HahnSeries.leadingCoeff_eq]
      rw [hEi, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hK,
        deriv_root_lead_gen (C := C) hK n hn0 r.leadingCoeff c hc0 hγ j0] at h
      have hγ0 : r.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr
        (root_order_inf S.F S.monic n d N hn hn0 hN ha0 hd hw r hr).1
      have hβK : algebraMap C K β ≠ 0 := (map_ne_zero_iff _ (algebraMap C K).injective).mpr hβ0
      apply (algebraMap C K).injective
      have hpow : r.leadingCoeff ^ j0 ≠ 0 := pow_ne_zero _ hγ0
      have hov : ((o i : ℤ) : K) / N = -((v i : ℤ) : K) / n := by
        have := hno i
        have hnK : (n : K) ≠ 0 := by exact_mod_cast hn0.ne'
        have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
        rw [div_eq_div_iff hNK hnK]
        have e : ((n : ℤ) * o i : ℤ) = -((N : ℤ) * v i) := this
        have e2 := congrArg (fun z : ℤ ↦ (z : K)) e
        push_cast at e2
        linear_combination e2
      have h' : algebraMap C K (Λ i i) * (algebraMap C K β * r.leadingCoeff ^ j0) =
          (algebraMap C K (β′ / β + (j0 : C) * (c′ / (n * c)) +
            (((wtW n d (W i) : ℤ) - n * (Q i).natDegree : ℤ) : C) / n * b)) *
            (algebraMap C K β * r.leadingCoeff ^ j0) := by
        rw [← h]
        simp only [map_add, map_div₀, map_mul, map_natCast, map_intCast]
        rw [show (((o i : ℤ) : K) / N) = -((v i : ℤ) : K) / n from hov]
        field_simp
        ring
      exact mul_right_cancel₀ (mul_ne_zero hβK hpow) h'
    · intro j _ hji
      by_cases h2 : Λ i j = 0
      · rw [h2, map_zero, zero_mul]
      · have h3 := htri i j h2
        have h4 : o i < o j := lt_of_le_of_ne h3 fun h5 ↦ hji (hoinj _ _ h5).symm
        rw [hbelow j _ h4, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

end CurveData

namespace CurveData

section MainE

variable {C L K : Type*} [Field C] [CharZero C] [DecidableEq C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

variable (S : CurveData C L) (b : C) (hx : S.x′ = aeval S.x (Polynomial.C b * X))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
  (n d : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
  (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natDegree = d)
  (hw : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ n * (S.F.coeff i).natDegree < d * (n - i))
  (hcop : Nat.Coprime n d)

include hx hK hn hn0 ha0 hd hw hcop in
/-- **Echelon integral bases of non-constant curves over an exponential level** (single place at
infinity; `S₀(0) ≠ 0`). -/
theorem exists_nkBasisE :
    ∃ (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (r : Fin S.F.natDegree → ℕ) (S0 : C[X])
      (P : Fin S.F.natDegree → Fin S.F.natDegree → C[X]) (W : Fin S.F.natDegree → C[X][X])
      (Q : Fin S.F.natDegree → C[X]),
      S.IBasis K w ∧ (∀ c : Fin S.F.natDegree → C⟮S.x⟯,
        ∑ j, algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (c j) * w j = 0 → ∀ j, c j = 0) ∧
      S0 ≠ 0 ∧ Squarefree S0 ∧ S0.coeff 0 ≠ 0 ∧
      (∀ i, (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
        S.polyE S0 = ∑ j, S.polyE (P i j) * w j) ∧
      (∀ i j, (pqE b r P S0 i j).natDegree ≤ (X ^ r i * S0).natDegree) ∧
      (∀ i, Q i ≠ 0 ∧ (S.wTil w r i : L) * aeval S.x (Q i) = S.evXY (W i) ∧ W i ≠ 0 ∧
        (W i).natDegree < n) ∧
      (∀ i, -(n : ℤ) < (wtW n d (W i) : ℤ) - n * (Q i).natDegree ∧
        (wtW n d (W i) : ℤ) - n * (Q i).natDegree ≤ 0) ∧
      (∀ i j, (wtW n d (W i) : ℤ) - n * (Q i).natDegree =
        (wtW n d (W j) : ℤ) - n * (Q j).natDegree → i = j) ∧
      (∀ i j0, j0 < n → (W i).coeff j0 ≠ 0 →
        wtW n d (W i) = n * ((W i).coeff j0).natDegree + j0 * d →
        ((W i).coeff j0).leadingCoeff = (Q i).leadingCoeff) := by
  classical
  -- a branch above infinity
  obtain ⟨N, hN, l, hlen, hl, -⟩ := S.hasBranchesInfB (K := K)
  have hN0 := Nat.pos_of_ne_zero hN
  have hlne : l ≠ [] := by
    intro h; rw [h, List.length_nil, hn] at hlen; omega
  obtain ⟨ρ, hρl⟩ := List.exists_mem_of_ne_nil l hlne
  set hρ := S.root_of_mem hl hρl
  -- an echelon integral basis
  obtain ⟨w0, hw0⟩ := S.exists_IBasis K
  obtain ⟨w1, r1, hw1, hr1, hred1⟩ := S.exists_reduced K w0 hw0
  obtain ⟨w2, r, hw2, hr2, hred2, hdist2⟩ := S.exists_echelon n d hn hn0 ha0 hd hw hcop N hN l hl ρ
    hρl _ w1 r1 hw1 hr1 hred1 rfl
  have hw20 := IBasis.ne_zero S hw2
  have hF1 : S.F ≠ 1 := fun h ↦ by rw [h, natDegree_one] at hn; omega
  -- representations of the rescaled elements
  have hrep : ∀ i, ∃ (W : C[X][X]) (Q : C[X]), Q ≠ 0 ∧
      (S.wTil w2 r i : L) * aeval S.x Q = S.evXY W ∧ W ≠ 0 ∧ W.natDegree < n := by
    intro i
    obtain ⟨W, Q, hQ, hWQ, hWn⟩ := S.exists_repr_lt (S.wTil w2 r i) hF1
    rw [hn] at hWn
    refine ⟨W, Q, hQ, hWQ, ?_, hWn⟩
    intro h0
    rw [h0, evXY, Polynomial.map_zero, eval_zero] at hWQ
    have hx0 : aeval S.x Q ≠ 0 := fun h ↦ hQ ((transcendental_iff.mp S.htr) Q h)
    exact S.wTil_ne_zero w2 r i (hw20 i) (Subtype.ext (by simpa [hx0] using hWQ))
  choose W' Q' hQ' hWQ' hW0' hWn' using hrep
  have hlead := fun i ↦ S.embG_lead_inf n d hn hn0 ha0 hd hw hcop N hN0 ρ hρ (S.wTil w2 r i) (W' i)
    (Q' i) (hQ' i) (hWQ' i) (hW0' i) (hWn' i)
  choose hE0 hord j0 hj0n hj0 hwt hlc using hlead
  set β : Fin S.F.natDegree → C := fun i ↦ ((W' i).coeff (j0 i)).leadingCoeff / (Q' i).leadingCoeff
    with hβ
  have hβ0 : ∀ i, β i ≠ 0 := fun i ↦
    div_ne_zero (leadingCoeff_ne_zero.mpr (hj0 i)) (leadingCoeff_ne_zero.mpr (hQ' i))
  -- the normalized basis
  set w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯ := fun i ↦ S.polyE (Polynomial.C (β i)⁻¹) * w2 i with hwdef
  have hwB : S.IBasis K w := IBasis.scale S hw2 _ fun i ↦ inv_ne_zero (hβ0 i)
  have hrw : ∀ j, S.InfOrd K (w j) (r j) := fun j ↦ InfOrd.scale S (hr2 j) _
  have hredw : S.Reduced K w r := Reduced.scale S hred2 _ fun i ↦ inv_ne_zero (hβ0 i)
  have hwt_eq : ∀ i, S.wTil w r i = S.polyE (Polynomial.C (β i)⁻¹) * S.wTil w2 r i := fun i ↦ by
    simp only [wTil, hwdef]; ring
  -- `S₀ wᵢ′` is a polynomial combination
  have hderiv : ∀ i, ∃ (Wd : C[X][X]) (Qd : C[X]), Qd ≠ 0 ∧
      ((w i : L))′ * aeval S.x Qd = S.evXY Wd := fun i ↦
    S.exists_repr ⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx _ (w i).2⟩
  choose Wd Qd hQd hWQd using hderiv
  set R := UniqueFactorizationMonoid.radical (∏ i, Qd i) with hRdef
  have hQprod : ∏ i, Qd i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ hQd i
  have hR0 : R ≠ 0 := radical_ne_zero' _
  have hRsq : Squarefree R := UniqueFactorizationMonoid.squarefree_radical
  obtain ⟨S0, hRS, hS0X⟩ : ∃ S0 : C[X], (R = X * S0 ∨ R = S0) ∧ ¬ X ∣ S0 := by
    by_cases hX : X ∣ R
    · obtain ⟨S0, hS0⟩ := hX
      refine ⟨S0, Or.inl hS0, fun hX2 ↦ ?_⟩
      obtain ⟨T0, hT0⟩ := hX2
      have := hRsq X ⟨T0, by rw [hS0, hT0]; ring⟩
      exact not_isUnit_X this
    · exact ⟨R, Or.inr rfl, hX⟩
  have hS00 : S0 ≠ 0 := by
    rintro rfl; rcases hRS with h | h <;> simp [h] at hR0
  have hsq0 : Squarefree S0 := by
    rcases hRS with h | h
    · rw [h] at hRsq; exact hRsq.of_mul_right
    · rw [← h]; exact hRsq
  have hcoord : ∀ i, ∃ c : Fin S.F.natDegree → C[X],
      (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
        S.polyE S0 = ∑ j, S.polyE (c j) * w j := by
    intro i
    have hreg := S.regularFinite_rad_derivW (K := K) (Polynomial.C b * X) hx hK (w i) (hwB.1 i) (Wd i)
      (Qd i) (hQd i) (hWQd i)
    obtain ⟨T, hT⟩ : UniqueFactorizationMonoid.radical (Qd i) ∣ R :=
      UniqueFactorizationMonoid.radical_dvd_radical (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
        hQprod
    have hreg2 := S.regularFinite_polyE_mul (K := K) T hreg
    have hreg3 : S.RegularFinite K (S.polyE R *
        ⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx _ (w i).2⟩) := by
      convert hreg2 using 1
      rw [hT, S.polyE_mul]; ring
    have hreg4 : S.RegularFinite K (S.polyE S0 *
        ⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C b * X) hx _ (w i).2⟩) := by
      rcases hRS with h | h
      · exact S.regularFinite_dropX b hx hK (w i) (hwB.1 i) R S0 h hreg3
      · rw [← h]; exact hreg3
    obtain ⟨c, hc⟩ := hwB.2.1 _ hreg4
    exact ⟨c, by rw [← hc]; ring⟩
  choose P hP using hcoord
  -- normality at infinity: the rescaled matrix is bounded
  have hdeg : ∀ i j, (pqE b r P S0 i j).natDegree ≤ (X ^ r i * S0).natDegree := by
    intro i
    have hwt0 : S.InfOrd K (S.wTil w r i) 0 := S.infOrd_wTil w r i (hrw i)
    have hu := S.infOrd_derivE b hx hK (S.wTil w r i) 0 hwt0
    have hq : (X ^ r i * S0 : C[X]) ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hS00
    have hid := S.deriv_wTilE b hx w r S0 P hP i
    refine S.reduced_normal (K := K) w r hrw hredw _ hu (fun j ↦ pqE b r P S0 i j)
      (X ^ r i * S0) hq ?_
    have hqL : aeval S.x (X ^ r i * S0) ≠ 0 := fun h ↦ hq ((transcendental_iff.mp S.htr) _ h)
    apply Subtype.ext
    have e : ((∑ j, S.polyE (pqE b r P S0 i j) * (S.polyE (X ^ r i * S0))⁻¹ *
        ((S.polyE (X ^ r j))⁻¹ * w j) : C⟮S.x⟯⟮S.y⟯) : L) =
        (∑ j, aeval S.x (pqE b r P S0 i j) * (S.wTil w r j : L)) / aeval S.x (X ^ r i * S0) := by
      rw [Finset.sum_div]
      push_cast
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [polyE, wTil]
      push_cast
      ring
    rw [e, eq_div_iff hqL]
    exact hid
  refine ⟨w, r, S0, P, W', fun i ↦ Q' i * Polynomial.C (β i), hwB, ?_, hS00, hsq0,
    fun h0' ↦ hS0X (Polynomial.X_dvd_iff.mpr h0'), hP, hdeg, fun i ↦ ⟨?_, ?_, hW0' i, hWn' i⟩,
    fun i ↦ ?_, fun i j hij ↦ ?_, fun i j1 hj1n hj1 hwt1 ↦ ?_⟩
  · -- independence over `C(x)`: clear denominators
    intro c hc
    letI := algebraAdjoinSimple (F := C) S.x
    haveI := isFractionRing_adjoin_simple S.x S.htr
    have hpoly : ∀ p : C[X], S.polyE p =
        algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (algebraMap C[X] C⟮S.x⟯ p) := fun p ↦ Subtype.ext (by
      show aeval S.x p = ((algebraMap C[X] C⟮S.x⟯ p : C⟮S.x⟯) : L)
      rw [algebraMap_adjoinSimple])
    obtain ⟨⟨dd, hdd⟩, hdc⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors C[X]) (Finset.univ.image c)
    choose p hp using fun j ↦ hdc (c j) (Finset.mem_image_of_mem c (Finset.mem_univ j))
    have hd0 : dd ≠ 0 := nonZeroDivisors.ne_zero hdd
    have h0 := hwB.2.2 p (by
      have : ∑ j, S.polyE (p j) * w j =
          algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (algebraMap C[X] C⟮S.x⟯ dd) *
            ∑ j, algebraMap C⟮S.x⟯ (C⟮S.x⟯⟮S.y⟯) (c j) * w j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hpoly, hp j, Algebra.smul_def, map_mul]
        ring
      rw [this, hc, mul_zero])
    intro j
    have := hp j
    rw [h0 j, map_zero, Algebra.smul_def] at this
    have hdne : algebraMap C[X] C⟮S.x⟯ dd ≠ 0 := fun h ↦ hd0 (IsFractionRing.injective C[X] C⟮S.x⟯
      (by rw [h, map_zero]))
    exact (mul_eq_zero.mp this.symm).resolve_left hdne
  · exact mul_ne_zero (hQ' i) (Polynomial.C_ne_zero.mpr (hβ0 i))
  · rw [hwt_eq, map_mul, ← hWQ' i]
    simp only [polyE, IntermediateField.coe_mul, map_mul, aeval_C]
    have : algebraMap C L (β i) ≠ 0 := (map_ne_zero_iff _ (algebraMap C L).injective).mpr (hβ0 i)
    rw [map_inv₀]
    field_simp
  · -- the window
    have hwin := S.ordR_wTil_window n d hn hn0 ha0 hd hw hcop N hN l hl ρ hρl w2 r hw20 hr2 hred2 i
    have ho := hord i
    simp only [ordR] at hwin
    rw [natDegree_mul_C (hβ0 i)]
    have hnpos : (0 : ℤ) < n := by exact_mod_cast hn0
    have hNpos : (0 : ℤ) < N := by exact_mod_cast hN0
    constructor <;> nlinarith
  · -- distinct weights
    rw [natDegree_mul_C (hβ0 i), natDegree_mul_C (hβ0 j)] at hij
    refine hdist2 i j ?_
    simp only [ordR]
    have h1 := hord i
    have h2 := hord j
    rw [hij] at h1
    have hnpos : (0 : ℤ) < n := by exact_mod_cast hn0
    have : (n : ℤ) * (S.embG (infSub N) (infSub_injective N hN0) ρ hρ (S.wTil w2 r i)).order =
      n * (S.embG (infSub N) (infSub_injective N hN0) ρ hρ (S.wTil w2 r j)).order := by linarith
    exact mul_left_cancel₀ hnpos.ne' this
  · -- leading coefficients `1`
    have hj := S.j0_unique n d hn hn0 ha0 hd hw hcop j1 (j0 i) ((W' i).coeff j1).natDegree
      ((W' i).coeff (j0 i)).natDegree 0 0 hj1n (hj0n i) (by
        have := hwt1.symm.trans (hwt i); push_cast at this ⊢; linarith)
    subst hj
    rw [Polynomial.leadingCoeff_mul, leadingCoeff_C, hβ]
    dsimp only
    rw [mul_div_cancel₀ _ (leadingCoeff_ne_zero.mpr (hQ' i))]

end MainE

end CurveData

end Curves
