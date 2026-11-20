import RischTragerBronstein.Mixed.KPDecideMain
import RischTragerBronstein.Mixed.KPLiouville2

/-!
# Kummer radicals over a logarithmic level, with denominators `a(t)ᵏ`

**`kp_decides_pow`**: `∫ B(t) θʲ / a(t)ᵏ` (`θⁿ = a(t)` as in `kp_decides`, any `k`) has an elementary
integral iff the Risch equation `y′ + (j/n)(a′/a) y = B/aᵏ` has a solution at the top level
(`kpDecideK`). The only change from `kp_decides` is at the branch points, where the integrand may
now have poles: the residue argument runs on the class-`0` parts (`kp_liouville_kummer`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- **The decision** for `∫ B(t) a(t)^{j/n − k}` over a logarithmic level `t = tₘ`. -/
def kpDecideK (m : ℕ) (j n : ℕ) (a B : GPoly (LC m)) (k : ℕ) : Bool :=
  rdeOKFr Fc ks lv (m + 1) (kpFr Fc ks m j n a) ((B, powG (MO Fc ks m) a k) : LC (m + 1))

end Curves.MT

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- The value of a fraction code `(P, D)` of level `m + 1`. -/
lemma sem_frac_code (m : ℕ) (h : T.Tr (m + 1)) (P D : GPoly (LC m)) :
    (((T.MP (m + 1) h).sem ((P, D) : LC (m + 1)) : T.F (m + 1)) : L) = T.evP m P / T.evP m D :=
  T.sem_MP (m + 1) h _

lemma evP_powG (m : ℕ) (h : T.Tr m) (a : GPoly (LC m)) (k : ℕ) :
    T.evP m (powG (MO Fc ks m) a k) = T.evP m a ^ k := by
  rw [← T.aeval_toPoly (T.MP m h) (T.sem_MP m h), ← T.aeval_toPoly (T.MP m h) (T.sem_MP m h),
    toPoly_powG_XE, map_pow]

set_option maxHeartbeats 8000000 in
/-- **Kummer radicals over a logarithmic level are decided**, with the denominators `a(t)ᵏ`. -/
theorem kp_decides_pow (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (a : GPoly (LC m)) (nn : ℕ) (hnn : 0 < nn)
    (hsqc : GPoly.squarefreeCheck (MO Fc ks m) a = true) (hdegpos : 0 < degG (MO Fc ks m) a)
    (hcop : Nat.Coprime nn (degG (MO Fc ks m) a))
    (θ : L) (hθ : θ ^ nn = T.evP m a)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (j : ℕ) (hj0 : 0 < j) (hjn : j < nn) (B : GPoly (LC m)) (k : ℕ) :
    HasElementaryIntegral (T.evP m B / T.evP m a ^ k * θ ^ j) ↔
      kpDecideK Fc ks lv m j nn a B k = true := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hspec := MS.rde _ (T.kpFr_ok m hTr j nn a)
  have hiff := T.rdeOKFr_iff (lv := lv) (m + 1) hTr _ hspec
    ((B, powG (MO Fc ks m) a k) : LC (m + 1))
  unfold kpDecideK
  have hA0 : T.evP m a ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) a hdegpos
  constructor
  · ------------------------------------------------------------------------------------------
    -- `⇒`: a Liouville form in the elementary extension
    intro hf
    obtain ⟨E₁, _, _, _, _, hE₁, g, hg⟩ := hf
    haveI : CharZero E₁ := charZero_of_injective_algebraMap (algebraMap L E₁).injective
    obtain ⟨ι, s, c, u, v, hdata, hv, heqL⟩ := liouville_strong hE₁ _ g hg
    obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E₁
    set ψ := algebraMap L E₁ with hψ
    have MSE := TE.mspecs hmon hdeg lv (m + 1) (by omega) hc
    have hTE : TE.Tr (m + 1) := MSE.hyp.tr
    have hTEm : TE.Tr m := hTE.of_succ
    -- the values of the polynomial codes
    have hPE : ∀ P : GPoly (LC m), TE.evP m P = ψ (T.evP m P) := fun P ↦ by
      rw [← TE.sem_poly_code m hTE, ← T.sem_poly_code m hTr]
      exact (TE.sem_MP (m + 1) hTE _).trans ((hTEev (m + 1) _).trans
        (congrArg ψ (T.sem_MP (m + 1) hTr _).symm))
    -- the superelliptic curve over `C₁ = Fₘ` of the lifted tower
    set p₁ : (TE.F m)[X] := GPoly.toPoly (TE.MP m hTEm) a with hp₁
    have hsq₁ : Squarefree p₁ := GPoly.squarefreeCheck_sound (TE.MP m hTEm) hsqc
    have hdeg₁ : p₁.natDegree = degG (MO Fc ks m) a := (degG_eq (TE.MP m hTEm) a).symm
    have hy₁ : (ψ θ) ^ nn = aeval (TE.ts m) p₁ := by
      rw [hp₁, TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm), hPE, ← map_pow, hθ]
    let S₁ : SuperData (TE.F m) E₁ :=
      ⟨TE.ts m, ψ θ, nn, p₁, hTE m (by omega), hnn, hsq₁, by rw [hdeg₁]; exact hdegpos, hy₁,
        by exact_mod_cast hnn.ne'⟩
    -- the derivation of `x = tₘ`
    set η₁ : TE.F m := TE.val m η with hη₁
    have hx : S₁.x′ = algebraMap (TE.F m) E₁ η₁ := by
      change (TE.ts m)′ = _
      rw [TE.ht m (by omega), hk]
      rfl
    have hnd : ∀ α : AlgebraicClosure (TE.F m), α′ ≠ algebraMap (TE.F m) _ η₁ := fun α ↦
      not_deriv_of_integral η₁ (fun z hz ↦ MSE.hyp.nd m (by omega) η hk z hz) α
        (Algebra.IsIntegral.isIntegral α)
    have hK : ∀ c : TE.F m, (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c)′ =
        algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c′ := fun c ↦ deriv_algebraMap c
    have hcop₁ : Nat.Coprime S₁.n S₁.p.natDegree := by
      change Nat.Coprime nn p₁.natDegree
      rw [hdeg₁]; exact hcop
    have hconstC : ∀ z : E₁, z′ = 0 → z ∈ Set.range (algebraMap (TE.F m) E₁) := fun z hz ↦ by
      obtain ⟨c0, hc0⟩ := TE.hconst z hz
      exact ⟨⟨z, hc0 ▸ TE.const_mem m c0⟩, rfl⟩
    -- the field `C₁(x, y)` contains everything
    set T₁ := (TE.F m)⟮S₁.x⟯⟮S₁.y⟯ with hT₁
    have hxT : ∀ w ∈ TE.F (m + 1), w ∈ T₁ := fun w hw ↦ by
      exact IntermediateField.algebraMap_mem T₁ (⟨w, (TE.mem_F_succ).mp hw⟩ : (TE.F m)⟮S₁.x⟯)
    have hLT : ∀ z : L, ψ z ∈ T₁ := by
      intro z
      have hz := hgen z
      induction hz using IntermediateField.adjoin_induction with
      | mem w hw =>
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact mem_adjoin_simple_self _ _
      | algebraMap w => exact hxT _ (hTEmem (m + 1) _ w.2)
      | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
      | mul w₁ w₂ _ _ h₁ h₂ => rw [map_mul]; exact mul_mem h₁ h₂
      | inv w _ h₁ => rw [map_inv₀]; exact inv_mem h₁
    have hCT : ∀ w ∈ Differential.constField L E₁, w ∈ T₁ := by
      intro w hw
      induction hw using IntermediateField.adjoin_induction with
      | mem w hw =>
        obtain ⟨c0, hc0⟩ := hconstC w hw
        rw [← hc0]
        exact S₁.const_mem c0
      | algebraMap z => exact hLT z
      | add w₁ w₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
      | mul w₁ w₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂
      | inv w _ h₁ => exact inv_mem h₁
    -- the integrand `b yʲ`
    set b := ψ (T.evP m B / T.evP m a ^ k) with hb
    have hbE : b = TE.evP m B / TE.evP m a ^ k := by rw [hb, hPE, hPE, map_div₀, map_pow]
    have hbx : b ∈ (TE.F m)⟮S₁.x⟯ := by
      rw [hbE, ← TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm),
        ← TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm)]
      letI := algebraAdjoinSimple (F := TE.F m) S₁.x
      rw [← algebraMap_adjoinSimple (F := TE.F m) S₁.x, ← algebraMap_adjoinSimple (F := TE.F m) S₁.x]
      exact div_mem (SetLike.coe_mem _) (pow_mem (SetLike.coe_mem _) k)
    have hbm : b * S₁.y ^ j ∈ T₁ := mul_mem
      (IntermediateField.algebraMap_mem T₁ (⟨b, hbx⟩ : (TE.F m)⟮S₁.x⟯))
      (pow_mem (mem_adjoin_simple_self _ _) j)
    have hreg : ∀ α β : AlgebraicClosure (TE.F m), β ≠ 0 →
        β ^ S₁.n = (S₁.p.map (algebraMap (TE.F m) _)).eval α →
        0 ≤ S₁.ordAt (AlgebraicClosure (TE.F m)) ⟨b * S₁.y ^ j, hbm⟩ α β := by
      intro α β hβ hv'
      set PB := GPoly.toPoly (TE.MP m hTEm) B
      have hy0 : S₁.y ≠ 0 := fun h0 ↦ S₁.htr ⟨p₁, hsq₁.ne_zero, by
        rw [← hy₁]; change (ψ θ) ^ nn = 0; rw [show ψ θ = S₁.y from rfl, h0, zero_pow hnn.ne']⟩
      have hgen0 : AdjoinSimple.gen (TE.F m)⟮S₁.x⟯ S₁.y ≠ 0 := fun h ↦
        hy0 (congrArg Subtype.val h)
      have hp0 : S₁.polyX p₁ ≠ 0 := S₁.polyX_ne_zero hsq₁.ne_zero
      have e : (⟨b * S₁.y ^ j, hbm⟩ : T₁) =
          S₁.polyX PB * (S₁.polyX p₁ ^ k)⁻¹ * AdjoinSimple.gen (TE.F m)⟮S₁.x⟯ S₁.y ^ j := by
        apply Subtype.ext
        show b * S₁.y ^ j = ((S₁.polyX PB * (S₁.polyX p₁ ^ k)⁻¹ *
          AdjoinSimple.gen (TE.F m)⟮S₁.x⟯ S₁.y ^ j : T₁) : E₁)
        rw [IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_inv,
          IntermediateField.coe_pow, S₁.polyX_coe, S₁.polyX_coe, IntermediateField.coe_pow,
          AdjoinSimple.coe_gen, hbE, ← TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm),
          ← TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm), div_eq_mul_inv]
      rw [e]
      have hpα : (p₁.map (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)))).rootMultiplicity α = 0 := by
        refine Polynomial.rootMultiplicity_eq_zero fun hr ↦ hβ ?_
        have : β ^ S₁.n = 0 := by rw [hv']; exact hr
        exact pow_eq_zero_iff (n := S₁.n) S₁.hn.ne' |>.mp this
      by_cases hPB : PB = 0
      · obtain ⟨φ, hφ⟩ := S₁.ordAt_hom α β hv'
        rw [hPB, hφ]
        simp [SuperData.polyX]
      · rw [S₁.ordAt_mul hv' (mul_ne_zero (S₁.polyX_ne_zero hPB) (inv_ne_zero (pow_ne_zero _ hp0)))
          (pow_ne_zero _ hgen0), S₁.ordAt_mul hv' (S₁.polyX_ne_zero hPB)
          (inv_ne_zero (pow_ne_zero _ hp0)), S₁.ordAt_inv hv', S₁.ordAt_pow hv',
          S₁.ordAt_polyX PB hPB α β hv', S₁.ordAt_polyX p₁ hsq₁.ne_zero α β hv', S₁.ordAt_pow hv',
          S₁.ordAt_gen α β hv', if_neg hβ, if_neg hβ]
        rw [hpα]
        simp
    -- the Liouville form
    have heq : b * S₁.y ^ j = v′ + ∑ i ∈ s, c i * logDeriv (u i) := by
      change ψ (T.evP m B / T.evP m a ^ k) * (ψ θ) ^ j = _
      rw [← map_pow, ← map_mul, heqL, add_comm]
    obtain ⟨a₁, ha₁, hfa⟩ := S₁.kp_liouville_kummer η₁ hx hK hnd hcop₁ hconstC j hj0 hjn b hbx hbm hreg
      s c u (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hCT _ (hdata i hi).2.1⟩)
      v (hCT _ hv) heq
    -- the Risch equation in the lifted tower
    have hAE : TE.evP m a ≠ 0 := MTower.evP_ne_zero TE m hTE (by omega) a hdegpos
    have hyA : (ψ θ) ^ nn = TE.evP m a := by rw [hPE, ← map_pow, hθ]
    have hrde : a₁′ + ((j : ℚ) / nn : E₁) * logDeriv (TE.evP m a) * a₁ = b := by
      have h1 := deriv_mul_radical (ψ θ) (TE.evP m a) nn hnn hyA hAE a₁ j
      rw [← hfa] at h1
      have hy0 : (ψ θ) ^ j ≠ 0 := pow_ne_zero _ (fun h0 ↦ hAE (by rw [← hyA, h0, zero_pow hnn.ne']))
      exact (mul_right_cancel₀ hy0 h1).symm
    have hspecE := MSE.rde _ (TE.kpFr_ok m hTE j nn a)
    refine (TE.rdeOKFr_iff (lv := lv) (m + 1) hTE _ hspecE _).mp
      ⟨⟨a₁, (TE.mem_F_succ).mpr ha₁⟩, Subtype.ext ?_⟩
    rw [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv, TE.sem_kpFr m hTE,
      TE.sem_frac_code m hTE, TE.evP_powG m hTEm, ← hbE]
    exact hrde
  · ------------------------------------------------------------------------------------------
    -- `⇐`: the antiderivative `y θʲ`
    rw [← hiff]
    rintro ⟨z, hz⟩
    have hzL := congrArg Subtype.val hz
    rw [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv, T.sem_kpFr m hTr,
      T.sem_frac_code m hTr, T.evP_powG m hTr.of_succ] at hzL
    rw [show T.evP m B / T.evP m a ^ k * θ ^ j = ((z : L) * θ ^ j)′ by
      rw [deriv_mul_radical θ (T.evP m a) nn hnn hθ hA0, hzL]]
    exact hasElementaryIntegral_of_deriv _

end MTower

end Curves.MT
