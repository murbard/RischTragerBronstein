import RischTragerBronstein.Mixed.NKInfRDecide
import RischTragerBronstein.Mixed.KESem

/-!
# Code checks for S-units with zeros above `t = 0`

Over an exponential level the logarithms of a Liouville form may have zeros and poles above
`t = 0`. A unit `U/tʲ` is certified by `U V ≡ tᵏ` (`unitDC`, `U`, `V` polynomials in `t, θ`), so it
has order `0` at every finite place outside `t = 0` and inverse `V/t^{k−j}`; its logarithmic
derivative `g = U′/U − j a′` (`t′ = a′ t`) is certified by `g tᵏ + j a′ tᵏ ≡ U′ V` (`logDerDC`). The
denominator `tʲ` allows norm-`1` normalizations `Uⁿ/(c tᵏ)`. `unitsC0` bundles the checks
(with `τ(g) = 0`).
`indepC` certifies independence modulo `Fₘ₊₁` (`indepC_sound1`), hence of `t` together with the
units modulo `Fₘ` (`indepC_sound_t`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential GTors

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- `u v ≡ tᵏ` modulo `P` for `u = ∑ Uⱼ θʲ`, `v = ∑ Vⱼ θʲ`. -/
def unitDC (m : ℕ) (Pp : List (GPoly (LC m))) (U V : List (GPoly (LC m))) (k : ℕ) : Bool :=
  let O1 := MO Fc ks (m + 1)
  (remP O1 (nkPC Fc ks m Pp) (GPoly.sub O1 (GPoly.mul O1 (nkFl Fc ks m U) (nkFl Fc ks m V))
    (nkFl Fc ks m [monoG Fc ks m k]))).all O1.isZero

/-- `θ′ = dθ`, `wθ P_Y ≡ 1` and `g tᵏ + j η tᵏ ≡ U′ V` modulo `P` (`η` the code of `t′/t`). -/
def logDerDC (m : ℕ) (Pp : List (GPoly (LC m))) (U V : List (GPoly (LC m))) (k j : ℕ) (ηc : LC m)
    (gl dθ wθ : GPoly (LC (m + 1))) : Bool :=
  let O1 := MO Fc ks (m + 1)
  let P := nkPC Fc ks m Pp
  let u := nkFl Fc ks m U
  zeroModC Fc ks m Pp (GPoly.add O1 (GPoly.mul O1 dθ (GPoly.derivX O1 P)) (GPoly.mapD O1 P)) &&
  zeroModC Fc ks m Pp (GPoly.sub O1 (GPoly.mul O1 wθ (GPoly.derivX O1 P)) [O1.one]) &&
  zeroModC Fc ks m Pp (GPoly.sub O1 (GPoly.add O1 (GPoly.mul O1 gl (nkFl Fc ks m [monoG Fc ks m k]))
    (nkFl Fc ks m [GPoly.smul (MO Fc ks m) ((MO Fc ks m).mul (mcst Fc ks m (j : ℚ)) ηc)
      (monoG Fc ks m k)]))
    (GPoly.mul O1 (GPoly.add O1 (GPoly.mapD O1 u) (GPoly.mul O1 dθ (GPoly.derivX O1 u)))
      (nkFl Fc ks m V)))

/-- The S-unit checks for `uᵢ = Uᵢ/t^{jᵢ}`: `Uᵢ Vᵢ ≡ t^{kᵢ}`, `jᵢ ≤ kᵢ`,
`gᵢ t^{kᵢ} + jᵢ η t^{kᵢ} ≡ Uᵢ′ Vᵢ`, `deg gᵢ < n`, `τ(gᵢ) = 0`. -/
def unitsC0 (m : ℕ) (Pp : List (GPoly (LC m))) (Us Vs : List (List (GPoly (LC m))))
    (kk jj : List ℕ) (ηc : LC m)
    (gls : List (GPoly (LC (m + 1)))) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1))) : Bool :=
  (List.range gls.length).all fun i ↦
    unitDC Fc ks m Pp (Us.getD i []) (Vs.getD i []) (kk.getD i 0) &&
    decide (jj.getD i 0 ≤ kk.getD i 0) &&
    logDerDC Fc ks m Pp (Us.getD i []) (Vs.getD i []) (kk.getD i 0) (jj.getD i 0) ηc
      (gls.getD i []) dθ wθ &&
    decide ((gls.getD i []).length ≤ Pp.length) &&
    (MOr Fc ks (m + 1)).isZero (nkTau Fc ks m Pp.length (gls.getD i []) s)

end Codes

lemma unitsC0_spec {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {m : ℕ} {Pp : List (GPoly (LC m))}
    {Us Vs : List (List (GPoly (LC m)))} {kk jj : List ℕ} {ηc : LC m}
    {gls : List (GPoly (LC (m + 1)))} {dθ wθ : GPoly (LC (m + 1))} {s : List (LC (m + 1))}
    (h : unitsC0 Fc ks m Pp Us Vs kk jj ηc gls dθ wθ s = true) (i : ℕ) (hi : i < gls.length) :
    unitDC Fc ks m Pp (Us.getD i []) (Vs.getD i []) (kk.getD i 0) = true ∧
    logDerDC Fc ks m Pp (Us.getD i []) (Vs.getD i []) (kk.getD i 0) (jj.getD i 0) ηc
      (gls.getD i []) dθ wθ = true ∧
    (gls.getD i []).length ≤ Pp.length ∧
    (MOr Fc ks (m + 1)).isZero (nkTau Fc ks m Pp.length (gls.getD i []) s) = true ∧
    jj.getD i 0 ≤ kk.getD i 0 := by
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1.1.1, this.1.1.2, this.1.2, this.2, this.1.1.1.2⟩

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma evθ_monoG (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (k : ℕ) :
    T.evθ m h1 θ (nkFl Fc ks m [monoG Fc ks m k]) = T.ts m ^ k := by
  rw [T.evθ_nkFl m h1 θ]
  simp [T.evP_monoG m h1.of_succ]

lemma unitDC_sound (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp U V : List (GPoly (LC m))) (k : ℕ)
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0) (h : unitDC Fc ks m Pp U V k = true) :
    T.evθ m h1 θ (nkFl Fc ks m U) * T.evθ m h1 θ (nkFl Fc ks m V) = T.ts m ^ k := by
  have h0 := T.zeroModC_sound m h1 θ Pp _ hP h
  rw [evθ_MP, GPoly.toPoly_sub, GPoly.toPoly_mul, map_sub, map_mul, sub_eq_zero, ← evθ_MP,
    ← evθ_MP, ← evθ_MP, T.evθ_monoG m h1 θ k] at h0
  exact h0

lemma evP_smulG (m : ℕ) (h : T.Tr m) (c : LC m) (A : GPoly (LC m)) :
    T.evP m (GPoly.smul (MO Fc ks m) c A) = T.ev m c * T.evP m A := by
  rw [← T.aeval_toPoly (T.MP m h) (T.sem_MP m h), ← T.aeval_toPoly (T.MP m h) (T.sem_MP m h),
    GPoly.toPoly_smul, map_mul, aeval_C, IntermediateField.algebraMap_apply, T.sem_MP m h]

lemma evθ_smul_monoG (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (c : LC m) (k : ℕ) :
    T.evθ m h1 θ (nkFl Fc ks m [GPoly.smul (MO Fc ks m) c (monoG Fc ks m k)]) =
      T.ev m c * T.ts m ^ k := by
  rw [T.evθ_nkFl m h1 θ]
  simp [T.evP_smulG m h1.of_succ, T.evP_monoG m h1.of_succ]

lemma logDerDC_sound (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (Pp U V : List (GPoly (LC m)))
    (k j : ℕ) (ηc : LC m)
    (gl dθ wθ : GPoly (LC (m + 1))) (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0)
    (hts : T.ts m ≠ 0)
    (huv : T.evθ m h1 θ (nkFl Fc ks m U) * T.evθ m h1 θ (nkFl Fc ks m V) = T.ts m ^ k)
    (h : logDerDC Fc ks m Pp U V k j ηc gl dθ wθ = true) :
    T.evθ m h1 θ gl = (T.evθ m h1 θ (nkFl Fc ks m U))′ / T.evθ m h1 θ (nkFl Fc ks m U) -
      (j : L) * T.ev m ηc := by
  set O1 := MO Fc ks (m + 1)
  unfold logDerDC at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hd, hw⟩, hg⟩ := h
  have hθ' := T.deriv_θ_of_chk m h1 θ Pp dθ wθ hP hd hw
  have hg' := T.zeroModC_sound m h1 θ Pp _ hP hg
  have hev : ∀ a b : GPoly (LC (m + 1)), T.evθ m h1 θ (GPoly.add O1 a b) =
      T.evθ m h1 θ a + T.evθ m h1 θ b := fun a b ↦ by
    rw [evθ_MP, evθ_MP, evθ_MP, GPoly.toPoly_add, map_add]
  have hem : ∀ a b : GPoly (LC (m + 1)), T.evθ m h1 θ (GPoly.mul O1 a b) =
      T.evθ m h1 θ a * T.evθ m h1 θ b := fun a b ↦ by
    rw [evθ_MP, evθ_MP, evθ_MP, GPoly.toPoly_mul, map_mul]
  have hes : ∀ a b : GPoly (LC (m + 1)), T.evθ m h1 θ (GPoly.sub O1 a b) =
      T.evθ m h1 θ a - T.evθ m h1 θ b := fun a b ↦ by
    rw [evθ_MP, evθ_MP, evθ_MP, GPoly.toPoly_sub, map_sub]
  have hjη : T.ev m ((MO Fc ks m).mul (mcst Fc ks m (j : ℚ)) ηc) = (j : L) * T.ev m ηc := by
    rw [← T.sem_MP m h1.of_succ, (T.MP m h1.of_succ).sem_mul, T.sem_mcst m h1.of_succ,
      IntermediateField.coe_mul, T.sem_MP m h1.of_succ]
    push_cast; ring
  rw [hes, hev, hem, hem, hev, hem, sub_eq_zero, T.evθ_monoG m h1 θ k, T.evθ_smul_monoG m h1 θ,
    hjη] at hg'
  set uu := T.evθ m h1 θ (nkFl Fc ks m U)
  set vv := T.evθ m h1 θ (nkFl Fc ks m V)
  have htk : T.ts m ^ k ≠ 0 := pow_ne_zero _ hts
  have hu0 : uu ≠ 0 := fun h ↦ htk (by rw [← huv, h, zero_mul])
  have hu' : uu′ = T.evθ m h1 θ (GPoly.mapD O1 (nkFl Fc ks m U)) + T.evθ m h1 θ dθ *
      T.evθ m h1 θ (GPoly.derivX O1 (nkFl Fc ks m U)) := by
    rw [T.deriv_evθ_MO m h1 θ (nkFl Fc ks m U), hθ']; ring
  rw [← hu'] at hg'
  rw [eq_sub_iff_add_eq, eq_div_iff hu0]
  have : ((T.evθ m h1 θ gl + (j : L) * T.ev m ηc) * uu - uu′) * T.ts m ^ k = 0 := by
    linear_combination uu * hg' + uu′ * huv
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right htk)

/-- **Independence modulo `Fₘ₊₁`** from the certificate `indepC`. -/
theorem indepC_sound1 (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (n : ℕ)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range n, (a j : L) * θ ^ j = 0 →
      ∀ j < n, a j = 0)
    (gls : List (GPoly (LC (m + 1)))) (hlen : ∀ i < gls.length, (gls.getD i []).length ≤ n)
    (u : Fin gls.length → L) (hu : ∀ i, u i ≠ 0)
    (hlog : ∀ i : Fin gls.length, T.evθ m h1 θ (gls.getD i []) = (u i)′ / u i)
    (J : List ℕ) (H : List (List (LC (m + 1)))) (hc : indepC Fc ks m gls J H = true) :
    ∀ a : Fin gls.length → ℤ, (∃ c : T.F (m + 1), ∏ i, (u i) ^ (a i) = (c : L)) → a = 0 :=
  T.indepWC_sound m h1 θ n hind gls hlen u hu hlog J _ H hc

/-- **`t` and the units are independent modulo `Fₘ`** (from `indepC`). -/
theorem indepC_sound_t (m : ℕ) (h1 : T.Tr (m + 1)) (htr : Transcendental (T.F m) (T.ts m))
    (θ : L) (n : ℕ)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range n, (a j : L) * θ ^ j = 0 →
      ∀ j < n, a j = 0)
    (gls : List (GPoly (LC (m + 1)))) (hlen : ∀ i < gls.length, (gls.getD i []).length ≤ n)
    (u : Fin gls.length → L) (hu : ∀ i, u i ≠ 0)
    (hlog : ∀ i : Fin gls.length, T.evθ m h1 θ (gls.getD i []) = (u i)′ / u i)
    (J : List ℕ) (H : List (List (LC (m + 1)))) (hc : indepC Fc ks m gls J H = true) :
    ∀ (e0 : ℤ) (a : Fin gls.length → ℤ),
      (∃ c : T.F m, T.ts m ^ e0 * ∏ i, (u i) ^ (a i) = (c : L)) → e0 = 0 ∧ a = 0 := by
  rintro e0 a ⟨c, hc'⟩
  have hts0 : T.ts m ≠ 0 := fun h ↦ htr ⟨X, X_ne_zero, by rw [aeval_X]; exact h⟩
  have hc0 : (c : L) ≠ 0 := by
    rw [← hc']
    exact mul_ne_zero (zpow_ne_zero _ hts0)
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ (hu i))
  have hts1 : T.ts m ∈ T.F (m + 1) := T.ts_mem m
  have hcm : (c : L) ∈ T.F (m + 1) := T.le_succ m c.2
  set c1 : T.F (m + 1) := ⟨(c : L) * T.ts m ^ (-e0),
    mul_mem hcm (zpow_mem hts1 _)⟩ with hc1
  have ha : a = 0 := T.indepC_sound1 m h1 θ n hind gls hlen u hu hlog J H hc a ⟨c1, by
    rw [hc1]
    change _ = (c : L) * T.ts m ^ (-e0)
    rw [← hc', zpow_neg, mul_comm (T.ts m ^ e0), mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ hts0),
      mul_one]⟩
  refine ⟨?_, ha⟩
  subst ha
  simp only [Pi.zero_apply, zpow_zero, Finset.prod_const_one, mul_one] at hc'
  by_contra he
  -- `t^{|e0|}` would be algebraic over `Fₘ`
  have hc0' : c ≠ 0 := fun h ↦ hc0 (by rw [h]; rfl)
  rcases lt_or_gt_of_ne he with hlt | hgt
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, e0 = -((k + 1 : ℕ) : ℤ) := ⟨(-e0 - 1).toNat, by omega⟩
    subst hk
    rw [zpow_neg, zpow_natCast] at hc'
    apply htr
    refine ⟨X ^ (k + 1) - Polynomial.C c⁻¹, ?_, ?_⟩
    · exact X_pow_sub_C_ne_zero (Nat.succ_pos k) _
    · simp only [map_sub, map_pow, aeval_X, aeval_C, IntermediateField.algebraMap_apply,
        IntermediateField.coe_inv]
      rw [← inv_inv (T.ts m ^ (k + 1)), hc', sub_self]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, e0 = ((k + 1 : ℕ) : ℤ) := ⟨(e0 - 1).toNat, by omega⟩
    subst hk
    rw [zpow_natCast] at hc'
    apply htr
    refine ⟨X ^ (k + 1) - Polynomial.C c, X_pow_sub_C_ne_zero (Nat.succ_pos k) _, ?_⟩
    simp only [map_sub, map_pow, aeval_X, aeval_C, IntermediateField.algebraMap_apply]
    rw [hc', sub_self]

/-- **`t` and the units are independent modulo `Fₘ`** (from `indepWC`). -/
theorem indepWC_sound_t (m : ℕ) (h1 : T.Tr (m + 1)) (htr : Transcendental (T.F m) (T.ts m))
    (θ : L) (n : ℕ) (hn0 : 0 < n)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range n, (a j : L) * θ ^ j = 0 →
      ∀ j < n, a j = 0)
    (gls : List (GPoly (LC (m + 1)))) (hlen : ∀ i < gls.length, (gls.getD i []).length ≤ n)
    (u : Fin gls.length → L) (hu : ∀ i, u i ≠ 0)
    (hlog : ∀ i : Fin gls.length, T.evθ m h1 θ (gls.getD i []) = (u i)′ / u i)
    (J D : List ℕ) (H : List (List (LC (m + 1)))) (hc : indepWC Fc ks m gls J D H = true) :
    ∀ (e0 : ℤ) (a : Fin gls.length → ℤ),
      (∃ c : T.F m, T.ts m ^ e0 * ∏ i, (u i) ^ (a i) = (c : L)) → e0 = 0 ∧ a = 0 := by
  rintro e0 a ⟨c, hc'⟩
  have hts0 : T.ts m ≠ 0 := fun h ↦ htr ⟨X, X_ne_zero, by rw [aeval_X]; exact h⟩
  have hts1 : T.ts m ∈ T.F (m + 1) := T.ts_mem m
  have hcm : (c : L) ∈ T.F (m + 1) := T.le_succ m c.2
  set c1 : T.F (m + 1) := ⟨(c : L) * T.ts m ^ (-e0),
    mul_mem hcm (zpow_mem hts1 _)⟩ with hc1
  have ha : a = 0 := T.indepWC_sound1 m h1 θ n hn0 hind gls hlen u hu hlog J D H hc a ⟨c1, by
    rw [hc1]
    change _ = (c : L) * T.ts m ^ (-e0)
    rw [← hc', zpow_neg, mul_comm (T.ts m ^ e0), mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ hts0),
      mul_one]⟩
  obtain ⟨he, -⟩ := T.indepC_sound_t m h1 htr θ n hind [] (fun i hi ↦ absurd hi (by simp))
    (fun i ↦ absurd i.2 (by simp)) (fun i ↦ absurd i.2 (by simp)) (fun i ↦ absurd i.2 (by simp))
    [] [] (by simp [indepC, indepWC]) e0 (fun i ↦ absurd i.2 (by simp)) ⟨c, by
      subst ha
      simp only [Pi.zero_apply, zpow_zero, Finset.prod_const_one, mul_one] at hc'
      simpa using hc'⟩
  exact ⟨he, ha⟩

end MTower

end Curves.MT
