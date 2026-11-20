import RischTragerBronstein.Mixed.NKInfStruct
import RischTragerBronstein.Mixed.NKExp0Gauge
import RischTragerBronstein.Mixed.NKUnitsInfLog

/-!
# Residues at infinity over a logarithmic level

Along a branch `x = s⁻ᴺ` above infinity of a curve over a differential field with `x′ = η`, the
derivation is `dS (infSpeed η N)` (`δ − (η/N) s^{N+1} d/ds`). Its coefficient at `s^N`:
* of a derivative is a derivative: `(dS g).coeff N = (g.coeff N)′` (`coeff_dS_infSpeed_top`);
* of a logarithmic derivative `dS U / U` is `β′ − (η/N) ord U` for some `β` (`coeff_logDeriv_top`,
  via a truncated logarithm `truncLog`).
So for a Liouville form `f = v′ + ∑ cᵢ uᵢ′/uᵢ` the coefficient `f_N` satisfies
`f_N + ρ η ∈ K′` with `ρ = (1/N) ∑ cᵢ ord uᵢ`, and `ρ` is unique when `η` is not a derivative
(`residue_unique`).
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section Laurent

variable {C K : Type*} [Field C] [CharZero C] [Field K] [CharZero K] [Algebra C K] [Differential C]
  [Differential K]

/-- **(A)** The coefficient at `s^N` of `dS g` along `x = s⁻ᴺ` is the derivative of the coefficient. -/
lemma coeff_dS_infSpeed_top (η : C) (N : ℕ) (g : LaurentSeries K) :
    (dS (infSpeed (K := K) η N) g).coeff (N : ℤ) = (g.coeff (N : ℤ))′ := by
  rw [dS_apply, HahnSeries.coeff_add, coeff_coefDeriv, infSpeed]
  have key := HahnSeries.coeff_single_mul_add (r := -(algebraMap C K η) / N)
    (x := LaurentSeries.derivative K g) (a := (-1 : ℤ)) (b := (N : ℤ) + 1)
  rw [show (-1 : ℤ) + ((N : ℤ) + 1) = N by ring] at key
  rw [key, derivative_coeff]
  simp

/-- The truncated logarithm `∑_{j=1}^{N} (−1)^{j+1} zʲ/j`. -/
noncomputable def truncLog (N : ℕ) (z : LaurentSeries K) : LaurentSeries K :=
  ∑ j ∈ Finset.range N, HahnSeries.C ((-1 : K) ^ j / ((j : K) + 1)) * z ^ (j + 1)

lemma coefDeriv_pow (z : LaurentSeries K) (n : ℕ) :
    coefDeriv (z ^ (n + 1)) = ((n : LaurentSeries K) + 1) * z ^ n * coefDeriv z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Derivation.leibniz, ih, smul_eq_mul, smul_eq_mul]
    push_cast
    ring

lemma coefDeriv_truncLog (N : ℕ) (z : LaurentSeries K) :
    coefDeriv (truncLog N z) =
      coefDeriv z * ∑ j ∈ Finset.range N, HahnSeries.C ((-1 : K) ^ j) * z ^ j := by
  unfold truncLog
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Derivation.leibniz, coefDeriv_C, coefDeriv_pow, smul_eq_mul, smul_eq_mul]
  have hc : ((-1 : K) ^ j / ((j : K) + 1))′ = 0 := by
    have h1 : ((-1 : K) ^ j)′ = 0 := by
      have : ((-1 : K))′ = 0 := by rw [Derivation.map_neg, Derivation.map_one_eq_zero, neg_zero]
      simp [Derivation.leibniz_pow, this]
    have h2 : (((j : K) + 1))′ = 0 := by
      rw [Derivation.map_add, Derivation.map_natCast, Derivation.map_one_eq_zero, add_zero]
    rw [Derivation.leibniz_div, h1, h2]; simp
  rw [hc, HahnSeries.C_zero, mul_zero, add_zero]
  have hj : ((j : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have e : ((j : LaurentSeries K) + 1) = HahnSeries.C ((j : K) + 1) := by
    rw [map_add, map_natCast, map_one]
  rw [e]
  calc HahnSeries.C ((-1 : K) ^ j / ((j : K) + 1)) * (HahnSeries.C ((j : K) + 1) * z ^ j * coefDeriv z)
      = HahnSeries.C ((-1 : K) ^ j / ((j : K) + 1) * ((j : K) + 1)) * z ^ j * coefDeriv z := by
        rw [map_mul]; ring
    _ = coefDeriv z * (HahnSeries.C ((-1 : K) ^ j) * z ^ j) := by
        rw [div_mul_cancel₀ _ hj]; ring

/-- **The truncated logarithm**: for `z` without constant term, the coefficient at `s^N` of
`coefDeriv z / (1 + z)` is the derivative of the coefficient of `truncLog N z`. -/
lemma coeff_coefDeriv_div_top (N : ℕ) (z : LaurentSeries K) (hz : LowerBd z 1) :
    (coefDeriv z * (1 + z)⁻¹).coeff (N : ℤ) = ((truncLog N z).coeff (N : ℤ))′ := by
  have h1z : (1 + z) ≠ 0 := by
    intro h0
    have := congrArg (fun w : LaurentSeries K ↦ w.coeff 0) h0
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero] at this
    rw [hz 0 (by norm_num), add_zero] at this
    simp at this
  have hgeoM : ∀ M : ℕ, (∑ j ∈ Finset.range M, HahnSeries.C ((-1 : K) ^ j) * z ^ j) * (1 + z) =
      1 - (-z) ^ M := by
    intro M
    induction M with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
      have : HahnSeries.C ((-1 : K) ^ n) * z ^ n = (-z) ^ n := by
        rw [neg_pow z, map_pow, map_neg, map_one]
      rw [this]
      ring
  set G := ∑ j ∈ Finset.range N, HahnSeries.C ((-1 : K) ^ j) * z ^ j with hG
  have hG' : G = (1 - (-z) ^ N) * (1 + z)⁻¹ := by
    rw [← hgeoM N, ← hG, mul_assoc, mul_inv_cancel₀ h1z, mul_one]
  have hsplit : coefDeriv z * (1 + z)⁻¹ = coefDeriv (truncLog N z) +
      coefDeriv z * (-z) ^ N * (1 + z)⁻¹ := by
    rw [coefDeriv_truncLog, ← hG, hG']
    ring
  rw [hsplit, HahnSeries.coeff_add, coeff_coefDeriv]
  have hcd : LowerBd (coefDeriv z) 1 := fun k hk ↦ by rw [coeff_coefDeriv, hz k hk, Derivation.map_zero]
  have hinv : LowerBd (1 + z)⁻¹ 0 := by
    have hc0 : (1 + z).coeff 0 = 1 := by
      rw [HahnSeries.coeff_add, hz 0 (by norm_num), add_zero]; simp
    have hle : (1 + z).order ≤ 0 := HahnSeries.order_le_of_coeff_ne_zero (by rw [hc0]; exact one_ne_zero)
    have hge : 0 ≤ (1 + z).order := by
      refine order_nonneg_of_lowerBd _ fun k hk ↦ ?_
      rw [HahnSeries.coeff_add, hz k (by omega), add_zero]
      simp [HahnSeries.coeff_one, hk.ne]
    have h := lowerBd_inv (1 + z) h1z
    rwa [show (1 + z).order = 0 by omega, neg_zero] at h
  have hlb := (hcd.mul (hz.neg.pow N)).mul hinv
  rw [hlb (N : ℤ) (by push_cast; omega), add_zero]

lemma derivative_single' (k : ℤ) (c : K) :
    LaurentSeries.derivative K (single k c) = single (k - 1) ((k : K) * c) := by
  ext m
  rw [derivative_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single]
  by_cases h : m = k - 1
  · rw [if_pos (by omega), if_pos h, h]; push_cast; ring
  · rw [if_neg (by omega), if_neg h, mul_zero]

lemma inv_single_K (k : ℤ) {c : K} (hc : c ≠ 0) :
    (single k c : LaurentSeries K)⁻¹ = single (-k) c⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [HahnSeries.single_mul_single, add_neg_cancel, mul_inv_cancel₀ hc, ← HahnSeries.C_apply,
    map_one]

/-- **(B)** The coefficient at `s^N` of a logarithmic derivative along `x = s⁻ᴺ`. -/
lemma coeff_logDeriv_top (η : C) (N : ℕ) (hN : 0 < N) (U : LaurentSeries K) (hU : U ≠ 0) :
    ∃ β : K, (dS (infSpeed (K := K) η N) U * U⁻¹).coeff (N : ℤ) =
      β′ - algebraMap C K η / N * (U.order : K) := by
  classical
  set s := infSpeed (K := K) η N with hs
  set k := U.order with hk
  set w0 := U.coeff k with hw0
  have hw00 : w0 ≠ 0 := fun h ↦ hU (HahnSeries.coeff_order_eq_zero.mp h)
  set z : LaurentSeries K := single (-k) w0⁻¹ * U - 1 with hz
  have hUz : U = single k w0 * (1 + z) := by
    rw [hz, add_sub_cancel, ← mul_assoc, HahnSeries.single_mul_single, add_neg_cancel,
      mul_inv_cancel₀ hw00, ← HahnSeries.C_apply, map_one, one_mul]
  have hzlb : LowerBd z 1 := by
    intro m hm
    rw [hz, HahnSeries.coeff_sub]
    have e : (single (-k) w0⁻¹ * U).coeff m = w0⁻¹ * U.coeff (m + k) := by
      have := HahnSeries.coeff_single_mul_add (r := w0⁻¹) (x := U) (a := m + k) (b := -k)
      rw [show m + k + -k = m by ring] at this
      exact this
    rw [e]
    rcases lt_or_eq_of_le (show m ≤ 0 by omega) with hlt | heq
    · rw [HahnSeries.coeff_eq_zero_of_lt_order (by rw [← hk]; omega), mul_zero]
      simp [HahnSeries.coeff_one, hlt.ne]
    · rw [heq, zero_add, ← hw0, inv_mul_cancel₀ hw00]; simp
  have h1z : (1 + z) ≠ 0 := by
    intro h0; apply hU; rw [hUz, h0, mul_zero]
  have hs0 : single k w0 ≠ 0 := by simpa using hw00
  -- the logarithmic derivative of a product
  have hprod : dS s U * U⁻¹ = dS s (single k w0) * (single k w0)⁻¹ + dS s (1 + z) * (1 + z)⁻¹ := by
    rw [hUz, Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_inv]
    field_simp
    ring
  have hA : dS s (single k w0) * (single k w0)⁻¹ = single 0 (w0′ / w0) +
      single (N : ℤ) (-(algebraMap C K η) / N * (k : K)) := by
    rw [dS_apply, coefDeriv_single, derivative_single', hs, infSpeed, HahnSeries.single_mul_single,
      add_mul, inv_single_K k hw00, HahnSeries.single_mul_single, HahnSeries.single_mul_single]
    congr 1
    · rw [show k + -k = 0 by ring, div_eq_mul_inv]
    · rw [show (N : ℤ) + 1 + (k - 1) + -k = N by ring]
      congr 1
      field_simp
  have hB : dS s (1 + z) = coefDeriv z + s * LaurentSeries.derivative K z := by
    rw [Derivation.map_add, Derivation.map_one_eq_zero, zero_add, dS_apply]
  refine ⟨(truncLog N z).coeff (N : ℤ), ?_⟩
  rw [hprod, HahnSeries.coeff_add, hA, hB, add_mul, HahnSeries.coeff_add, HahnSeries.coeff_add,
    coeff_coefDeriv_div_top N z hzlb]
  have h1 : (single (0 : ℤ) (w0′ / w0) : LaurentSeries K).coeff (N : ℤ) = 0 := by
    rw [HahnSeries.coeff_single, if_neg (by exact_mod_cast hN.ne')]
  have h2 : (single (N : ℤ) (-(algebraMap C K η) / N * (k : K)) : LaurentSeries K).coeff (N : ℤ) =
      -(algebraMap C K η) / N * (k : K) := by
    rw [HahnSeries.coeff_single, if_pos rfl]
  have hinv : LowerBd (1 + z)⁻¹ 0 := by
    have hc0 : (1 + z).coeff 0 = 1 := by
      rw [HahnSeries.coeff_add, hzlb 0 (by norm_num), add_zero]; simp
    have hle : (1 + z).order ≤ 0 :=
      HahnSeries.order_le_of_coeff_ne_zero (by rw [hc0]; exact one_ne_zero)
    have hge : 0 ≤ (1 + z).order := by
      refine order_nonneg_of_lowerBd _ fun j hj ↦ ?_
      rw [HahnSeries.coeff_add, hzlb j (by omega), add_zero]
      simp [HahnSeries.coeff_one, hj.ne]
    have h := lowerBd_inv (1 + z) h1z
    rwa [show (1 + z).order = 0 by omega, neg_zero] at h
  have h3 : (s * LaurentSeries.derivative K z * (1 + z)⁻¹).coeff (N : ℤ) = 0 := by
    have hlb := ((lowerBd_infSpeed (K := K) η N).mul (hzlb.derivative)).mul hinv
    exact hlb _ (by omega)
  rw [h1, h2, h3]
  ring

/-- **(C) Uniqueness of the residue**: if `η` is not a derivative, `a′ + ρ η = b′ + ρ' η` with
constants `ρ, ρ'` forces `ρ = ρ'`. -/
lemma residue_unique (η : C) (hnd : ∀ a : K, a′ ≠ algebraMap C K η) (a b ρ ρ' : K)
    (hρ : ρ′ = 0) (hρ' : ρ'′ = 0) (h : a′ + ρ * algebraMap C K η = b′ + ρ' * algebraMap C K η) :
    ρ = ρ' := by
  by_contra hne
  have hd : ρ - ρ' ≠ 0 := sub_ne_zero.mpr hne
  apply hnd ((b - a) / (ρ - ρ'))
  have hc : (ρ - ρ')′ = 0 := by rw [Derivation.map_sub, hρ, hρ', sub_zero]
  have hci : ((ρ - ρ')⁻¹)′ = 0 := by rw [Derivation.leibniz_inv, hc, smul_zero]
  have hba : (b - a)′ = (ρ - ρ') * algebraMap C K η := by
    rw [Derivation.map_sub]; linear_combination -h
  rw [div_eq_mul_inv, Derivation.leibniz, hci, smul_zero, zero_add, smul_eq_mul, hba]
  field_simp

end Laurent

namespace CurveData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

variable (S : CurveData C L) (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

include hx hK in
/-- The derivation along a branch above infinity. -/
lemma embG_deriv_inf (N : ℕ) (hN : 0 < N) (r : LaurentSeries K)
    (hr : (S.F.map (infSub N)).eval r = 0) (z : C⟮S.x⟯⟮S.y⟯) :
    S.embG (infSub N) (infSub_injective N hN) r hr
      ⟨(z : L)′, S.derivClosedXYW' (Polynomial.C η) hx z z.2⟩ =
      dS (infSpeed η N) (S.embG (infSub N) (infSub_injective N hN) r hr z) := by
  have hd := S.embG_dSW' (Polynomial.C η) hx hK (infSpeed η N) (single (-(N : ℤ)) 1)
    (dS_infSpeed η N hN) (infSub N) (infSub_injective N hN)
    (fun P ↦ by rw [SuperData.infSub_eq_subst]) r hr (z : L) z.2
  simpa only [Subtype.coe_eta] using hd

include hx hK in
/-- **The residue at a place above infinity of a Liouville form.** For
`f = v′ + ∑ cᵢ uᵢ′/uᵢ` (`cᵢ` constants of `C`), the coefficient at `s^N` of `f` along the branch
`x = s⁻ᴺ` plus `ρ η`, `ρ = (1/N) ∑ cᵢ ord uᵢ`, is a derivative. -/
theorem coeff_liouville_top (N : ℕ) (hN : 0 < N) (r : LaurentSeries K)
    (hr : (S.F.map (infSub N)).eval r = 0) {ι : Type*} (s : Finset ι) (c : ι → C)
    (hc : ∀ i ∈ s, (c i)′ = 0) (u : ι → C⟮S.x⟯⟮S.y⟯) (hu : ∀ i ∈ s, u i ≠ 0)
    (v f : C⟮S.x⟯⟮S.y⟯)
    (hf : (f : L) = (v : L)′ + ∑ i ∈ s, algebraMap C L (c i) * ((u i : L)′ / (u i : L))) :
    ∃ β : K, (S.embG (infSub N) (infSub_injective N hN) r hr f).coeff (N : ℤ) +
      (∑ i ∈ s, algebraMap C K (c i) *
        ((S.embG (infSub N) (infSub_injective N hN) r hr (u i)).order : K)) / N *
        algebraMap C K η = β′ := by
  classical
  set φ := S.embG (infSub N) (infSub_injective N hN) r hr with hφ
  have hcl := fun z : C⟮S.x⟯⟮S.y⟯ ↦ S.derivClosedXYW' (Polynomial.C η) hx z z.2
  have hdφ : ∀ z : C⟮S.x⟯⟮S.y⟯, φ ⟨(z : L)′, hcl z⟩ = dS (infSpeed η N) (φ z) :=
    fun z ↦ S.embG_deriv_inf η hx hK N hN r hr z
  -- `f` as an element of the subfield
  have hfe : f = ⟨(v : L)′, hcl v⟩ + ∑ i ∈ s, algebraMap C C⟮S.x⟯⟮S.y⟯ (c i) *
      (⟨(u i : L)′, hcl (u i)⟩ / u i) := by
    apply Subtype.ext
    rw [hf]
    push_cast
    rfl
  have hCφ : ∀ c : C, φ (algebraMap C C⟮S.x⟯⟮S.y⟯ c) = HahnSeries.C (algebraMap C K c) := by
    intro c
    have := congrArg (fun g ↦ g c) (S.embG_algebraMapC (infSub N) (infSub_injective N hN)
      (fun c ↦ by simp [infSub]) r hr)
    simpa using this
  have hex : ∀ i, ∃ β : K, φ (u i) ≠ 0 →
      (dS (infSpeed η N) (φ (u i)) * (φ (u i))⁻¹).coeff (N : ℤ) =
        β′ - algebraMap C K η / N * ((φ (u i)).order : K) := by
    intro i
    by_cases h : φ (u i) = 0
    · exact ⟨0, fun h' ↦ absurd h h'⟩
    · obtain ⟨β, hβ⟩ := coeff_logDeriv_top (K := K) η N hN (φ (u i)) h
      exact ⟨β, fun _ ↦ hβ⟩
  choose β hβ using hex
  have hcK : ∀ i ∈ s, (algebraMap C K (c i))′ = 0 := fun i hi ↦ by rw [hK, hc i hi, map_zero]
  have hterm : ∀ i ∈ s, (φ (algebraMap C C⟮S.x⟯⟮S.y⟯ (c i) *
      (⟨(u i : L)′, hcl (u i)⟩ / u i))).coeff (N : ℤ) =
      algebraMap C K (c i) * ((β i)′ - algebraMap C K η / N * ((φ (u i)).order : K)) := by
    intro i hi
    have hne : φ (u i) ≠ 0 := (map_ne_zero_iff _ φ.injective).mpr (hu i hi)
    rw [map_mul, map_div₀, hdφ, hCφ, div_eq_mul_inv, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
      hβ i hne, smul_eq_mul]
  refine ⟨(φ v).coeff (N : ℤ) + ∑ i ∈ s, algebraMap C K (c i) * β i, ?_⟩
  rw [hfe, map_add, map_sum, HahnSeries.coeff_add, hdφ, coeff_dS_infSpeed_top,
    HahnSeries.coeff_sum, Finset.sum_congr rfl hterm, Derivation.map_add, map_sum]
  have hd2 : ∀ i ∈ s, (algebraMap C K (c i) * β i)′ = algebraMap C K (c i) * (β i)′ := by
    intro i hi
    rw [Derivation.leibniz, hcK i hi, smul_zero, add_zero, smul_eq_mul]
  rw [Finset.sum_congr rfl hd2]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_mul]
  have : ∀ i ∈ s, algebraMap C K (c i) * (algebraMap C K η / N * ((φ (u i)).order : K)) =
      algebraMap C K (c i) * ((φ (u i)).order : K) / N * algebraMap C K η := fun i _ ↦ by ring
  rw [Finset.sum_congr rfl this]
  ring

include hx hK in
/-- **Zero residues at infinity: no logarithms.** For a Liouville form
`f = v′ + ∑ cᵢ uᵢ′/uᵢ` with `f` regular at the finite places, if the coefficient at `s^N` of `f`
along every branch above infinity is a derivative (zero residue), then `f = v′ + ℓ` with `ℓ ∈ C`. -/
theorem nk_liouville_noRes (hnd : ∀ a : K, a′ ≠ algebraMap C K η)
    (hgeo : Irreducible (S.F.map (mapRingHom (algebraMap C K))))
    (Ni : ℕ) (hNi : 0 < Ni) (li : List (LaurentSeries K))
    (hli : S.F.map (infSub Ni) = (li.map fun r ↦ X - Polynomial.C r).prod)
    (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (f : L) (hf : f ∈ C⟮S.x⟯⟮S.y⟯) (hreg : S.RegularFinite K ⟨f, hf⟩)
    (hzero : ∀ r (hr : r ∈ li), ∃ γ : K, (S.embG (infSub Ni) (infSub_injective Ni hNi) r
      (S.root_of_mem hli hr) ⟨f, hf⟩).coeff (Ni : ℤ) = γ′)
    {ι' : Type*} [DecidableEq ι'] (s : Finset ι') (c u : ι' → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ ℓ : C, f = v′ + algebraMap C L ℓ := by
  classical
  obtain ⟨k, d, w, ⟨hd', hw, hind⟩, hsum⟩ :=
    logSum_qindep (C⟮S.x⟯⟮S.y⟯).toSubfield s c u hc (fun i hi ↦ hu i hi)
  set d' : ℕ → C := fun jj ↦ if h : jj < k then Classical.choose (hconstC (d jj) (hd' jj h)) else 0
    with hd'def
  have hdd : ∀ jj < k, algebraMap C L (d' jj) = d jj := fun jj hjj ↦ by
    simp only [hd'def, dif_pos hjj]
    exact Classical.choose_spec (hconstC (d jj) (hd' jj hjj))
  have hd'c : ∀ jj < k, (d' jj)′ = 0 := fun jj hjj ↦ by
    apply (algebraMap C L).injective
    rw [← deriv_algebraMap, hdd jj hjj, hd' jj hjj, map_zero]
  have hind' : ∀ q : ℕ → ℚ, ∑ jj ∈ Finset.range k, (q jj : C) * d' jj = 0 →
      ∀ jj < k, q jj = 0 := by
    intro q hq
    apply hind q
    rw [← map_zero (algebraMap C L), ← hq, map_sum]
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [map_mul, map_ratCast, hdd jj (Finset.mem_range.mp hjj)]
  have hww : ∀ jj < k, w jj ∈ C⟮S.x⟯⟮S.y⟯ ∧ w jj ≠ 0 := fun jj hjj ↦ ⟨(hw jj hjj).2, (hw jj hjj).1⟩
  have heq' : f = v′ + ∑ jj ∈ Finset.range k, algebraMap C L (d' jj) * ((w jj)′ / w jj) := by
    rw [heq, hsum]
    congr 1
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [hdd jj (Finset.mem_range.mp hjj), logDeriv]
  -- the logarithms have no zeros or poles at the finite places
  have hgoodη : ∀ a : K, a′ ≠ ((Polynomial.C η).map (algebraMap C K)).eval a := fun a ↦ by
    rw [Polynomial.map_C, eval_C]; exact hnd a
  have hfinw : ∀ jj (hjj : jj < k) (a : K) (N : ℕ) (hN : N ≠ 0) (l : List (LaurentSeries K))
      (hl : S.F.map (branchSub N a) = (l.map fun r ↦ X - Polynomial.C r).prod)
      (r : LaurentSeries K) (hr : r ∈ l),
      (S.embG (branchSub N a) (branchSub_injective N (Nat.pos_of_ne_zero hN) a) r
        (S.root_of_mem hl hr) ⟨w jj, (hww jj hjj).1⟩).order = 0 :=
    fun jj hjj a N hN l hl r hr ↦
      S.logs_zero_branchW (Polynomial.C η) hx hK k d' w hww hind' v f hv hf heq' a (hgoodη a) N
        (Nat.pos_of_ne_zero hN) r (S.root_of_mem hl hr) (Or.inr (hreg a N hN l hl r hr)) jj hjj
  -- the logarithms have no zeros or poles above infinity (zero residues)
  have hinfw : ∀ jj (hjj : jj < k) r (hr : r ∈ li),
      (S.embG (infSub Ni) (infSub_injective Ni hNi) r (S.root_of_mem hli hr)
        ⟨w jj, (hww jj hjj).1⟩).order = 0 := by
    intro jj0 hjj0 r hr
    obtain ⟨γ, hγ⟩ := hzero r hr
    set φ := S.embG (infSub Ni) (infSub_injective Ni hNi) r (S.root_of_mem hli hr) with hφ
    obtain ⟨β, hβ⟩ := S.coeff_liouville_top η hx hK Ni hNi r (S.root_of_mem hli hr)
      (Finset.range k) d' (fun jj hjj ↦ hd'c jj (Finset.mem_range.mp hjj))
      (fun jj ↦ if h : jj < k then ⟨w jj, (hww jj h).1⟩ else 1)
      (fun jj hjj ↦ by
        rw [dif_pos (Finset.mem_range.mp hjj)]
        exact fun h0 ↦ (hww jj (Finset.mem_range.mp hjj)).2 (congrArg Subtype.val h0))
      ⟨v, hv⟩ ⟨f, hf⟩ (by
        show f = _
        rw [heq']
        congr 1
        refine Finset.sum_congr rfl fun jj hjj ↦ ?_
        rw [dif_pos (Finset.mem_range.mp hjj)])
    rw [hγ] at hβ
    set ρ : K := (∑ jj ∈ Finset.range k, algebraMap C K (d' jj) *
      ((φ (if h : jj < k then ⟨w jj, (hww jj h).1⟩ else 1)).order : K)) / Ni with hρ
    have hsum' : (∑ jj ∈ Finset.range k, algebraMap C K (d' jj) *
        ((φ (if h : jj < k then ⟨w jj, (hww jj h).1⟩ else 1)).order : K))′ = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun jj hjj ↦ ?_
      rw [Derivation.leibniz, hK, hd'c jj (Finset.mem_range.mp hjj), map_zero, smul_zero, add_zero,
        smul_eq_mul]
      rw [show ((φ (if h : jj < k then ⟨w jj, (hww jj h).1⟩ else 1)).order : K) =
        (((φ (if h : jj < k then ⟨w jj, (hww jj h).1⟩ else 1)).order : ℤ) : K) from rfl,
        Derivation.map_intCast, mul_zero]
    have hρ' : ρ′ = 0 := by
      have hn : ((Ni : K))′ = 0 := Derivation.map_natCast _ _
      rw [hρ, Derivation.leibniz_div, hsum', hn]
      simp
    have hρ0 : ρ = 0 := residue_unique η hnd γ β ρ 0 hρ' (Derivation.map_zero _) (by
      rw [zero_mul, add_zero]; exact hβ)
    -- `∑ (ord : ℚ) d' = 0` in `C`
    have hN0 : (Ni : K) ≠ 0 := by exact_mod_cast hNi.ne'
    have hsum0 : ∑ jj ∈ Finset.range k,
        ((((φ (if h : jj < k then ⟨w jj, (hww jj h).1⟩ else 1)).order : ℤ) : ℚ) : C) * d' jj = 0 := by
      apply (algebraMap C K).injective
      rw [map_zero, map_sum]
      have := hρ0
      rw [hρ, div_eq_zero_iff, or_iff_left hN0] at this
      rw [← this]
      refine Finset.sum_congr rfl fun jj _ ↦ ?_
      rw [map_mul, map_ratCast]
      push_cast
      ring
    have h0 := hind' (fun jj ↦ (((φ (if h : jj < k then ⟨w jj, (hww jj h).1⟩ else 1)).order : ℤ) : ℚ))
      hsum0 jj0 hjj0
    simp only [dif_pos hjj0, Int.cast_eq_zero] at h0
    exact h0
  -- hence the logarithms are constants
  have hconst : ∀ jj < k, ∃ cj : C, w jj = algebraMap C L cj := by
    intro jj hjj
    have hregw : S.RegularFinite K ⟨w jj, (hww jj hjj).1⟩ :=
      fun a N hN l hl r hr ↦ (hfinw jj hjj a N hN l hl r hr).ge
    obtain ⟨M0, hM0, hwM⟩ := S.algebraic_of_regular_l ⟨w jj, (hww jj hjj).1⟩ hregw Ni hNi li hli
      fun r hr ↦ (hinfw jj hjj r hr).ge
    exact S.mem_const_of_alg_geo hgeo ⟨w jj, (hww jj hjj).1⟩ M0 hM0 hwM
  choose! cj hcj using hconst
  refine ⟨∑ jj ∈ Finset.range k, d' jj * ((cj jj)′ / cj jj), ?_⟩
  rw [heq', map_sum]
  congr 1
  refine Finset.sum_congr rfl fun jj hjj ↦ ?_
  rw [hcj jj (Finset.mem_range.mp hjj), map_mul, map_div₀, deriv_algebraMap]

end CurveData

end Curves

