import RischTragerBronstein.Mixed.KRLiouville
import RischTragerBronstein.Mixed.KRCodes
import RischTragerBronstein.Mixed.KEMain

/-!
# Radicals over an exponential level: the curve `yⁿ = A(x)` over `Fₘ`

`krS`: for a realization `T`, `θⁿ = A(t)` over the top level `t = tₘ`, the superelliptic data
`y = θ`, `yⁿ = A(x)` over `C = Fₘ`, `x = t`, with the hypotheses of `KRLiouville`: `x′ = η x`
(`krS_hx`), the good places (`keS_good`), the field (`krS_mem`), the regularity of
`B/(tᵏ Aˡ) · θʲ` over `x ≠ 0` (`krS_reg`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- The superelliptic data `y = θ`, `yⁿ = A(x)` over `C = Fₘ`, `x = tₘ`. -/
noncomputable def krS (m : ℕ) (h : T.Tr (m + 1)) (A : GPoly (LC m))
    (hsq : Squarefree (GPoly.toPoly (T.MP m h.of_succ) A))
    (hdeg : 0 < (GPoly.toPoly (T.MP m h.of_succ) A).natDegree)
    (n : ℕ) (hn : 0 < n) (θ : L) (hθ : θ ^ n = T.evP m A) : SuperData (T.F m) L where
  x := T.ts m
  y := θ
  n := n
  p := GPoly.toPoly (T.MP m h.of_succ) A
  htr := h m (Nat.lt_succ_self m)
  hn := hn
  hsq := hsq
  hp := hdeg
  hy := by rw [T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ), hθ]
  hnC := by exact_mod_cast hn.ne'

section Facts

variable (m : ℕ) (h : T.Tr (m + 1)) (A : GPoly (LC m))
  (hsq : Squarefree (GPoly.toPoly (T.MP m h.of_succ) A))
  (hdeg : 0 < (GPoly.toPoly (T.MP m h.of_succ) A).natDegree)
  (n : ℕ) (hn : 0 < n) (θ : L) (hθ : θ ^ n = T.evP m A)

lemma krS_hx (hmn : m < T.n) {g : LC m} (hk : ks m = .exp g) :
    (T.krS m h A hsq hdeg n hn θ hθ).x′ =
      aeval (T.krS m h A hsq hdeg n hn θ hθ).x (Polynomial.C (T.val m g)′ * X) := by
  change (T.ts m)′ = aeval (T.ts m) (Polynomial.C (T.val m g)′ * X)
  rw [T.ht m hmn, hk, map_mul, aeval_C, aeval_X]
  rfl

lemma krS_mem : ∀ w ∈ IntermediateField.adjoin (T.F (m + 1)) {θ},
    w ∈ (T.F m)⟮(T.krS m h A hsq hdeg n hn θ hθ).x⟯⟮(T.krS m h A hsq hdeg n hn θ hθ).y⟯ := by
  set S := T.krS m h A hsq hdeg n hn θ hθ
  set T₁ := (T.F m)⟮S.x⟯⟮S.y⟯
  have hxT : ∀ w ∈ T.F (m + 1), w ∈ T₁ := fun w hw ↦
    IntermediateField.algebraMap_mem T₁ (⟨w, (T.mem_F_succ).mp hw⟩ : (T.F m)⟮S.x⟯)
  have hθT : θ ∈ T₁ := mem_adjoin_simple_self _ _
  intro w hw
  induction hw using IntermediateField.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact hθT
  | algebraMap w => exact hxT _ w.2
  | add w₁ w₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
  | mul w₁ w₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂
  | inv w _ h₁ => exact inv_mem h₁

lemma krS_cop (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m h.of_succ) A).natDegree) :
    Nat.Coprime (T.krS m h A hsq hdeg n hn θ hθ).n (T.krS m h A hsq hdeg n hn θ hθ).p.natDegree :=
  hcopA

open Classical in
/-- **The integrand `B/(tᵏ Aˡ) · θʲ` has no pole at the ordinary places over `x ≠ 0`.** -/
lemma krS_reg (B : GPoly (LC m)) (k l j : ℕ)
    (hf : T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ ^ j ∈
      (T.F m)⟮(T.krS m h A hsq hdeg n hn θ hθ).x⟯⟮(T.krS m h A hsq hdeg n hn θ hθ).y⟯) :
    ∀ α β : AlgebraicClosure (T.F m), β ≠ 0 →
      β ^ (T.krS m h A hsq hdeg n hn θ hθ).n =
        ((T.krS m h A hsq hdeg n hn θ hθ).p.map (algebraMap (T.F m) _)).eval α → α ≠ 0 →
      0 ≤ (T.krS m h A hsq hdeg n hn θ hθ).ordAt (AlgebraicClosure (T.F m))
        ⟨T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ ^ j, hf⟩ α β := by
  set S := T.krS m h A hsq hdeg n hn θ hθ
  intro α β hβ hv hα
  set PB := GPoly.toPoly (T.MP m h.of_succ) B
  set PA := GPoly.toPoly (T.MP m h.of_succ) A
  have hPA0 : PA ≠ 0 := hsq.ne_zero
  have hD0 : X ^ k * PA ^ l ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hPA0)
  have hXk : S.polyX (X ^ k * PA ^ l) ≠ 0 := S.polyX_ne_zero hD0
  have hgen0 : AdjoinSimple.gen (T.F m)⟮S.x⟯ S.y ≠ 0 := fun h0 ↦ by
    have hy := congrArg Subtype.val h0
    exact S.y_ne_zero hy
  have e : (⟨T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ ^ j, hf⟩ : (T.F m)⟮S.x⟯⟮S.y⟯) =
      S.polyX PB * (S.polyX (X ^ k * PA ^ l))⁻¹ * AdjoinSimple.gen (T.F m)⟮S.x⟯ S.y ^ j := by
    apply Subtype.ext
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_inv,
      IntermediateField.coe_pow, S.polyX_coe, S.polyX_coe, AdjoinSimple.coe_gen]
    change T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ ^ j = aeval (T.ts m) PB *
      (aeval (T.ts m) (X ^ k * PA ^ l))⁻¹ * θ ^ j
    rw [map_mul, map_pow, map_pow, aeval_X, T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ),
      T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ), div_eq_mul_inv]
  rw [e]
  have hPAα : (PA.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval α ≠ 0 := by
    intro h0
    apply hβ
    change β ^ n = (PA.map _).eval α at hv
    rw [h0] at hv
    exact pow_eq_zero_iff hn.ne' |>.mp hv
  have hk0 : S.ordAt (AlgebraicClosure (T.F m)) (S.polyX (X ^ k * PA ^ l)) α β = 0 := by
    have hPAα' : aeval α PA ≠ 0 := by rwa [← eval_map_algebraMap]
    rw [S.ordAt_polyX _ hD0 α β hv, Polynomial.rootMultiplicity_eq_zero, Nat.cast_zero, mul_zero]
    simp [hα, hPAα']
  have hnn : ∀ P : (T.F m)[X], P ≠ 0 → 0 ≤ S.ordAt (AlgebraicClosure (T.F m)) (S.polyX P) α β :=
    fun P hP ↦ by rw [S.ordAt_polyX P hP α β hv]; positivity
  have hg0 : 0 ≤ S.ordAt (AlgebraicClosure (T.F m)) (AdjoinSimple.gen (T.F m)⟮S.x⟯ S.y) α β := by
    rw [S.ordAt_gen α β hv]; split_ifs <;> norm_num
  by_cases hPB : PB = 0
  · obtain ⟨φ, hφ⟩ := S.ordAt_hom α β hv
    rw [hPB, hφ]
    simp [SuperData.polyX]
  · rw [S.ordAt_mul hv (mul_ne_zero (S.polyX_ne_zero hPB) (inv_ne_zero hXk)) (pow_ne_zero _ hgen0),
      S.ordAt_mul hv (S.polyX_ne_zero hPB) (inv_ne_zero hXk), S.ordAt_inv hv, hk0, S.ordAt_pow hv]
    have := hnn PB hPB
    have h2 := hg0
    positivity

end Facts

end MTower

end Curves.MT
