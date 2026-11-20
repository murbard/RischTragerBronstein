import RischTragerBronstein.Jacobian.Divisor
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Localization.Integer

/-!
# Existence of functions with prescribed zeros, and primitive scaling

* `exists_vanishing` (over a field): if the number of conditions `deg Γ` is smaller than the
  dimension of the Riemann–Roch space `L(N·∞)` (`⌊N/2⌋ + 1` coefficients of `a` plus the admissible
  coefficients of `b`), some non-zero `a + b y` with pole order `≤ N` vanishes on `Γ`.
* `VanishAt.of_map`: vanishing descends along an injective ring map (e.g. `O → K`).
* `exists_primitive_pair` (over a discrete valuation ring): a non-zero pair is `ϖᵐ` times a pair
  not divisible by `ϖ`.
-/

open Polynomial

namespace Jac

section Lin

variable {K : Type*} [Field K]

lemma jet_smul (c : K) (a b : K[X]) (x₀ : K) (V : K[X]) :
    jet (c • a) (c • b) x₀ V = C c * jet a b x₀ V := by
  rw [smul_eq_C_mul, smul_eq_C_mul, jet_C_mul]

/-- The jet conditions as a linear map. -/
noncomputable def jetMap (Γ : EDiv K) (V : Fin Γ.length → K[X]) :
    (K[X] × K[X]) →ₗ[K] ((Σ i : Fin Γ.length, Fin (Γ.get i).2.2) → K) where
  toFun ψ := fun ij ↦ (jet ψ.1 ψ.2 (Γ.get ij.1).1 (V ij.1)).coeff ij.2
  map_add' ψ φ := by
    funext ij
    simp only [Prod.fst_add, Prod.snd_add, jet_add, coeff_add, Pi.add_apply]
  map_smul' c ψ := by
    funext ij
    simp only [Prod.smul_fst, Prod.smul_snd, jet_smul, coeff_C_mul, RingHom.id_apply,
      Pi.smul_apply, smul_eq_mul]

lemma sum_get_mult (Γ : EDiv K) : ∑ i : Fin Γ.length, Γ[(i : ℕ)].2.2 = edeg Γ := by
  unfold edeg
  rw [← List.sum_ofFn]
  congr 1
  rw [show (List.ofFn fun i : Fin Γ.length ↦ Γ[(i : ℕ)].2.2) =
    (List.ofFn fun i : Fin Γ.length ↦ Γ[(i : ℕ)]).map (fun q ↦ q.2.2) by rw [List.map_ofFn]; rfl,
    List.ofFn_getElem]

/-- **Functions with prescribed zeros exist** when there are fewer conditions than coefficients. -/
theorem exists_vanishing (f : K[X]) (g N : ℕ) (Γ : EDiv K) (hon : OnCurve f Γ) (A B : ℕ)
    (hA : 2 * (A - 1) ≤ N) (hB : B = 0 ∨ 2 * (B - 1) + 2 * g + 1 ≤ N) (hdim : edeg Γ < A + B) :
    ∃ ψ : K[X] × K[X], ψ ≠ (0, 0) ∧ PoleLE g ψ N ∧ Vanishes f ψ Γ := by
  classical
  have hbr : ∀ i : Fin Γ.length, ∃ V, IsBranch f (Γ.get i).1 (Γ.get i).2.1 (Γ.get i).2.2 V :=
    fun i ↦ exists_branch (hon _ (List.get_mem _ _)).1 (hon _ (List.get_mem _ _)).2 _
  choose V hV using hbr
  have : Module.Finite K (degreeLT K A) := Module.Finite.equiv (degreeLTEquiv K A).symm
  have : Module.Finite K (degreeLT K B) := Module.Finite.equiv (degreeLTEquiv K B).symm
  let ι : (degreeLT K A) × (degreeLT K B) →ₗ[K] K[X] × K[X] :=
    LinearMap.prodMap (degreeLT K A).subtype (degreeLT K B).subtype
  let L := jetMap Γ V ∘ₗ ι
  have hfin1 : Module.finrank K ((degreeLT K A) × (degreeLT K B)) = A + B := by
    rw [Module.finrank_prod, (degreeLTEquiv K A).finrank_eq, (degreeLTEquiv K B).finrank_eq]
    simp
  have hfin2 : Module.finrank K ((Σ i : Fin Γ.length, Fin (Γ.get i).2.2) → K) = edeg Γ := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma]
    simp [sum_get_mult]
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := L) (by rw [hfin1, hfin2]; exact hdim)
  obtain ⟨⟨a, b⟩, hmem, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨(a.1, b.1), ?_, ?_, ?_⟩
  · intro h
    apply hne
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
  · have ha := a.2
    have hb := b.2
    rw [mem_degreeLT] at ha hb
    constructor
    · by_cases h0 : a.1 = 0
      · simp [h0]
      · rw [degree_eq_natDegree h0] at ha
        have : a.1.natDegree < A := by exact_mod_cast ha
        simp only; omega
    · by_cases h0 : b.1 = 0
      · left; exact h0
      · right
        rw [degree_eq_natDegree h0] at hb
        have : b.1.natDegree < B := by exact_mod_cast hb
        rcases hB with hB | hB
        · omega
        · simp only; omega
  · intro q hq
    obtain ⟨i, rfl⟩ := List.get_of_mem hq
    refine ⟨V i, hV i, ?_⟩
    rw [X_pow_dvd_iff]
    intro d hd
    have := congrFun (LinearMap.mem_ker.mp hmem) ⟨i, ⟨d, hd⟩⟩
    simpa [L, ι, jetMap] using this

end Lin

section Map

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **Vanishing descends along an injective ring map.** -/
lemma VanishAt.of_map {φ : R →+* S} (hφ : Function.Injective φ) {f a b : R[X]} {x₀ Y₀ : R}
    {k : ℕ} (h2Y : IsUnit (2 * Y₀)) (hY : Y₀ ^ 2 = f.eval x₀)
    (h : VanishAt (f.map φ) (a.map φ) (b.map φ) (φ x₀) (φ Y₀) k) : VanishAt f a b x₀ Y₀ k := by
  obtain ⟨V, hV⟩ := exists_branch h2Y hY k
  refine ⟨V, hV, ?_⟩
  have h2 : IsUnit (2 * φ Y₀) := by
    have := h2Y.map φ; rwa [map_mul, map_ofNat] at this
  have hd := h.jet_dvd h2 (hV.map φ) le_rfl
  rw [← jet_map, X_pow_dvd_iff] at hd
  rw [X_pow_dvd_iff]
  intro d hd'
  have := hd d hd'
  rw [coeff_map] at this
  exact hφ (by rw [this, map_zero])

/-- Dividing a vanishing function by a non-zero constant (over a domain). -/
lemma VanishAt.of_C_mul [IsDomain R] {f a b : R[X]} {x₀ Y₀ c : R} {k : ℕ} (hc : c ≠ 0)
    (h2Y : IsUnit (2 * Y₀)) (h : VanishAt f (C c * a) (C c * b) x₀ Y₀ k) :
    VanishAt f a b x₀ Y₀ k := by
  obtain ⟨V, hV, hj⟩ := h
  exact ⟨V, hV, X_pow_dvd_of_C_mul hc (by rwa [← jet_C_mul])⟩

lemma VanishAt.C_mul {f a b : R[X]} {x₀ Y₀ c : R} {k : ℕ} (h : VanishAt f a b x₀ Y₀ k) :
    VanishAt f (C c * a) (C c * b) x₀ Y₀ k := by
  obtain ⟨V, hV, hj⟩ := h
  exact ⟨V, hV, by rw [jet_C_mul]; exact Dvd.dvd.mul_left hj _⟩

end Map

section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- A non-zero pair of polynomials is `ϖᵐ` times a primitive pair. -/
theorem exists_primitive_pair {ϖ : O} (hϖ : Irreducible ϖ) {a b : O[X]} (h : (a, b) ≠ (0, 0)) :
    ∃ (m : ℕ) (a' b' : O[X]), a = C (ϖ ^ m) * a' ∧ b = C (ϖ ^ m) * b' ∧
      ¬ (C ϖ ∣ a' ∧ C ϖ ∣ b') := by
  classical
  -- a non-zero coefficient bounds the power of `ϖ`
  obtain ⟨z, hz, hzmem⟩ : ∃ z : O, z ≠ 0 ∧ (∀ m, C (ϖ ^ m) ∣ a ∧ C (ϖ ^ m) ∣ b → ϖ ^ m ∣ z) := by
    by_cases ha : a = 0
    · have hb : b ≠ 0 := fun hb ↦ h (by rw [ha, hb])
      obtain ⟨n, hn⟩ : ∃ n, b.coeff n ≠ 0 := by
        by_contra hc; push_neg at hc; exact hb (Polynomial.ext hc)
      exact ⟨b.coeff n, hn, fun m hm ↦ (C_dvd_iff_dvd_coeff _ _).mp hm.2 n⟩
    · obtain ⟨n, hn⟩ : ∃ n, a.coeff n ≠ 0 := by
        by_contra hc; push_neg at hc; exact ha (Polynomial.ext hc)
      exact ⟨a.coeff n, hn, fun m hm ↦ (C_dvd_iff_dvd_coeff _ _).mp hm.1 n⟩
  obtain ⟨N, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hϖ
  have hex : ∃ m, ¬ (C (ϖ ^ (m + 1)) ∣ a ∧ C (ϖ ^ (m + 1)) ∣ b) := by
    refine ⟨N, fun hm ↦ ?_⟩
    have := hzmem _ hm
    rw [hv, pow_succ, mul_comm (ϖ ^ N)] at this
    have h3 : ϖ ∣ (v : O) := (mul_dvd_mul_iff_right (pow_ne_zero N hϖ.ne_zero)).mp this
    exact hϖ.not_isUnit (isUnit_of_dvd_unit h3 v.isUnit)
  obtain ⟨m, hm1, hmin⟩ : ∃ m, ¬ (C (ϖ ^ (m + 1)) ∣ a ∧ C (ϖ ^ (m + 1)) ∣ b) ∧
      ∀ k < m, ¬¬ (C (ϖ ^ (k + 1)) ∣ a ∧ C (ϖ ^ (k + 1)) ∣ b) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk ↦ Nat.find_min hex hk⟩
  have hm : C (ϖ ^ m) ∣ a ∧ C (ϖ ^ m) ∣ b := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, pow_zero, C_1]; exact ⟨one_dvd _, one_dvd _⟩
    · have := hmin (m - 1) (by omega)
      push_neg at this
      rw [Nat.sub_add_cancel hpos] at this
      exact this
  obtain ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ := hm
  refine ⟨m, a', b', ha', hb', fun ⟨h1, h2⟩ ↦ hm1 ⟨?_, ?_⟩⟩
  · rw [ha', pow_succ, C_mul]; exact mul_dvd_mul_left _ h1
  · rw [hb', pow_succ, C_mul]; exact mul_dvd_mul_left _ h2

end DVR

end Jac
