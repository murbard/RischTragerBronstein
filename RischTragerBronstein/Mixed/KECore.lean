import RischTragerBronstein.Mixed.KESem
import RischTragerBronstein.Mixed.KETower

/-!
# Square roots over an exponential level: the Liouville form on the curve over `Fₘ`

`ke_setup`: for a realization `T` of a certified tower whose top level `t = tₘ` is an exponential,
`θ² = A(t)` and a scale `μ ∈ Fₘ` (`μ ≠ 0`), the superelliptic data `y = θ μ`, `y² = μ² A(x)` over
`C = Fₘ`, `x = t` satisfy every hypothesis of the Liouville theorems of `KELiouville`: `x′ = η x`,
the good places (`not_exp_of_integral`, `MixHyp.hom`), the constants, and the integrand
`B/tᵏ · θ = b y` with `b = B/(tᵏ μ)` has no pole over `x ≠ 0`.

`ke_core_nontors`: without torsion of `P₊ − ∞` (`P₊ = (0, β₀)`), a Liouville form for `B/tᵏ · θ`
gives `a ∈ Fₘ₊₁` with `a′ + ½ (A′/A) a = B/tᵏ`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- The superelliptic data `y = θ μ`, `y² = μ² A(x)` over `C = Fₘ`, `x = tₘ`. -/
noncomputable def keS (m : ℕ) (h : T.Tr (m + 1)) (A : GPoly (LC m))
    (hsq : Squarefree (GPoly.toPoly (T.MP m h.of_succ) A))
    (hdeg : 0 < (GPoly.toPoly (T.MP m h.of_succ) A).natDegree)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) (μ : T.F m) (hμ : μ ≠ 0) : SuperData (T.F m) L where
  x := T.ts m
  y := θ * μ
  n := 2
  p := Polynomial.C (μ ^ 2) * GPoly.toPoly (T.MP m h.of_succ) A
  htr := h m (Nat.lt_succ_self m)
  hn := two_pos
  hsq := fun x hx ↦ hsq x ((IsUnit.dvd_mul_left
    (Polynomial.isUnit_C.mpr (pow_ne_zero 2 hμ).isUnit)).mp hx)
  hp := by
    rw [natDegree_C_mul (pow_ne_zero 2 hμ)]; exact hdeg
  hy := by
    rw [map_mul, aeval_C, T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ), mul_pow, hθ]
    simp [IntermediateField.algebraMap_apply]
    ring
  hnC := two_ne_zero

section Facts

variable (m : ℕ) (h : T.Tr (m + 1)) (A : GPoly (LC m))
  (hsq : Squarefree (GPoly.toPoly (T.MP m h.of_succ) A))
  (hdeg : 0 < (GPoly.toPoly (T.MP m h.of_succ) A).natDegree)
  (θ : L) (hθ : θ ^ 2 = T.evP m A) (μ : T.F m) (hμ : μ ≠ 0)

/-- `x′ = η x` for an exponential level. -/
lemma keS_hx (hmn : m < T.n) {g : LC m} (hk : ks m = .exp g) :
    (T.keS m h A hsq hdeg θ hθ μ hμ).x′ =
      aeval (T.keS m h A hsq hdeg θ hθ μ hμ).x (Polynomial.C (T.val m g)′ * X) := by
  change (T.ts m)′ = aeval (T.ts m) (Polynomial.C (T.val m g)′ * X)
  rw [T.ht m hmn, hk, map_mul, aeval_C, aeval_X]
  rfl

/-- **The good places**: no non-zero algebraic `α` with `α′ = η α`. -/
lemma keS_good (hM : T.MixHyp (m + 1)) {g : LC m} (hk : ks m = .exp g) :
    ∀ α : AlgebraicClosure (T.F m), α ≠ 0 →
      α′ ≠ algebraMap (T.F m) (AlgebraicClosure (T.F m)) (T.val m g)′ * α := by
  intro α hα
  refine not_exp_of_integral ((T.val m g)′) (fun d hd z hz hzd ↦ ?_) α
    (Algebra.IsIntegral.isIntegral α) hα
  have := hM.hom m (Nat.lt_succ_self m) g hk (-(d : ℤ)) (by omega) z hz
  apply this
  rw [hzd]
  push_cast
  ring

/-- The field `C(x, y)` contains `Fₘ₊₁(θ)`. -/
lemma keS_mem : ∀ w ∈ IntermediateField.adjoin (T.F (m + 1)) {θ},
    w ∈ (T.F m)⟮(T.keS m h A hsq hdeg θ hθ μ hμ).x⟯⟮(T.keS m h A hsq hdeg θ hθ μ hμ).y⟯ := by
  set S := T.keS m h A hsq hdeg θ hθ μ hμ
  set T₁ := (T.F m)⟮S.x⟯⟮S.y⟯
  have hxT : ∀ w ∈ T.F (m + 1), w ∈ T₁ := fun w hw ↦
    IntermediateField.algebraMap_mem T₁ (⟨w, (T.mem_F_succ).mp hw⟩ : (T.F m)⟮S.x⟯)
  have hμT : ((μ : T.F m) : L) ∈ T₁ := S.const_mem μ
  have hθT : θ ∈ T₁ := by
    have hμ0 : ((μ : T.F m) : L) ≠ 0 := fun h0 ↦ hμ (Subtype.ext h0)
    have : θ = S.y * ((μ : T.F m) : L)⁻¹ := by
      change θ = θ * (μ : L) * (μ : L)⁻¹
      field_simp
    rw [this]
    exact mul_mem (mem_adjoin_simple_self _ _) (inv_mem hμT)
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

end Facts

section Reg

variable (m : ℕ) (h : T.Tr (m + 1)) (A : GPoly (LC m))
  (hsq : Squarefree (GPoly.toPoly (T.MP m h.of_succ) A))
  (hdeg : 0 < (GPoly.toPoly (T.MP m h.of_succ) A).natDegree)
  (θ : L) (hθ : θ ^ 2 = T.evP m A) (μ : T.F m) (hμ : μ ≠ 0)

open Classical in
/-- **The integrand `B/(tᵏ Aˡ) · θ` has no pole at the ordinary places over `x ≠ 0`.** -/
lemma keS_reg (B : GPoly (LC m)) (k l : ℕ)
    (hf : T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ ∈
      (T.F m)⟮(T.keS m h A hsq hdeg θ hθ μ hμ).x⟯⟮(T.keS m h A hsq hdeg θ hθ μ hμ).y⟯) :
    ∀ α β : AlgebraicClosure (T.F m), β ≠ 0 →
      β ^ (T.keS m h A hsq hdeg θ hθ μ hμ).n =
        ((T.keS m h A hsq hdeg θ hθ μ hμ).p.map (algebraMap (T.F m) _)).eval α → α ≠ 0 →
      0 ≤ (T.keS m h A hsq hdeg θ hθ μ hμ).ordAt (AlgebraicClosure (T.F m))
        ⟨T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ, hf⟩ α β := by
  set S := T.keS m h A hsq hdeg θ hθ μ hμ
  intro α β hβ hv hα
  set PB := GPoly.toPoly (T.MP m h.of_succ) B
  set PA := GPoly.toPoly (T.MP m h.of_succ) A
  have hμ0 : ((μ : T.F m) : L) ≠ 0 := fun h0 ↦ hμ (Subtype.ext h0)
  have hPA0 : PA ≠ 0 := hsq.ne_zero
  have hD0 : X ^ k * PA ^ l ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hPA0)
  have hXk : S.polyX (X ^ k * PA ^ l) ≠ 0 := S.polyX_ne_zero hD0
  have hc : S.cst μ⁻¹ ≠ 0 := fun h0 ↦ by
    have := congrArg Subtype.val h0
    simp [SuperData.cst] at this
    exact hμ this
  have hgen0 : AdjoinSimple.gen (T.F m)⟮S.x⟯ S.y ≠ 0 := fun h0 ↦ by
    have hy := congrArg Subtype.val h0
    change θ * μ = 0 at hy
    rcases mul_eq_zero.mp hy with h1 | h1
    · have : T.evP m A = 0 := by rw [← hθ, h1, zero_pow two_ne_zero]
      exact S.htr ⟨_, hsq.ne_zero, by
        change aeval (T.ts m) _ = 0
        rw [T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ)]; exact this⟩
    · exact hμ0 h1
  have e : (⟨T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ, hf⟩ : (T.F m)⟮S.x⟯⟮S.y⟯) =
      S.polyX PB * (S.polyX (X ^ k * PA ^ l))⁻¹ * S.cst μ⁻¹ * AdjoinSimple.gen (T.F m)⟮S.x⟯ S.y := by
    apply Subtype.ext
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_mul,
      IntermediateField.coe_inv, S.polyX_coe, S.polyX_coe, AdjoinSimple.coe_gen]
    change T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ = aeval (T.ts m) PB *
      (aeval (T.ts m) (X ^ k * PA ^ l))⁻¹ * (algebraMap (T.F m) L μ⁻¹) * (θ * μ)
    rw [map_mul, map_pow, map_pow, aeval_X, T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ),
      T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ)]
    simp only [map_inv₀]
    change _ = T.evP m B * (T.ts m ^ k * T.evP m A ^ l)⁻¹ * ((μ : L))⁻¹ * (θ * μ)
    field_simp
  rw [e]
  have hPAα : (PA.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval α ≠ 0 := by
    intro h0
    apply hβ
    have hp : S.p = Polynomial.C (μ ^ 2) * PA := rfl
    rw [hp, Polynomial.map_mul, eval_mul, h0, mul_zero] at hv
    exact pow_eq_zero_iff (n := S.n) S.hn.ne' |>.mp hv
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
  · rw [S.ordAt_mul hv (mul_ne_zero (mul_ne_zero (S.polyX_ne_zero hPB) (inv_ne_zero hXk)) hc)
      hgen0, S.ordAt_mul hv (mul_ne_zero (S.polyX_ne_zero hPB) (inv_ne_zero hXk)) hc,
      S.ordAt_mul hv (S.polyX_ne_zero hPB) (inv_ne_zero hXk), S.ordAt_inv hv, hk0,
      S.ordAt_cst _ (inv_ne_zero hμ) α β hv]
    have := hnn PB hPB
    omega

end Reg

section Core

variable (m : ℕ) (h : T.Tr (m + 1)) (A : GPoly (LC m))
  (hsq : Squarefree (GPoly.toPoly (T.MP m h.of_succ) A))
  (hdeg : 0 < (GPoly.toPoly (T.MP m h.of_succ) A).natDegree)
  (θ : L) (hθ : θ ^ 2 = T.evP m A) (μ : T.F m) (hμ : μ ≠ 0)

lemma keS_cop (hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m h.of_succ) A).natDegree) :
    Nat.Coprime (T.keS m h A hsq hdeg θ hθ μ hμ).n (T.keS m h A hsq hdeg θ hθ μ hμ).p.natDegree := by
  change Nat.Coprime 2 (Polynomial.C (μ ^ 2) * _).natDegree
  rw [natDegree_C_mul (pow_ne_zero 2 hμ)]; exact hcopA

lemma keS_constC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap (T.F m) L) := fun z hz ↦ by
  obtain ⟨c0, hc0⟩ := T.hconst z hz
  exact ⟨⟨z, hc0 ▸ T.const_mem m c0⟩, rfl⟩

/-- The integrand written `b y`, `b = B/(tᵏ μ)`. -/
lemma keS_b (B : GPoly (LC m)) (k l : ℕ) :
    T.evP m B / (T.ts m ^ k * T.evP m A ^ l) / ((μ : T.F m) : L) ∈ (T.F m)⟮(T.keS m h A hsq hdeg θ hθ μ hμ).x⟯ := by
  letI := algebraAdjoinSimple (F := T.F m) (T.keS m h A hsq hdeg θ hθ μ hμ).x
  have h1 : T.evP m B ∈ (T.F m)⟮(T.keS m h A hsq hdeg θ hθ μ hμ).x⟯ := by
    rw [← T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ),
      ← algebraMap_adjoinSimple (F := T.F m) (T.ts m)]
    exact SetLike.coe_mem _
  have h2 : T.ts m ∈ (T.F m)⟮(T.keS m h A hsq hdeg θ hθ μ hμ).x⟯ := mem_adjoin_simple_self _ _
  have h3 : T.evP m A ∈ (T.F m)⟮(T.keS m h A hsq hdeg θ hθ μ hμ).x⟯ := by
    rw [← T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ),
      ← algebraMap_adjoinSimple (F := T.F m) (T.ts m)]
    exact SetLike.coe_mem _
  exact div_mem (div_mem h1 (mul_mem (pow_mem h2 k) (pow_mem h3 l)))
    (IntermediateField.algebraMap_mem _ μ)

open Classical in
/-- **Without torsion, the Risch equation has a solution in `Fₘ₊₁`.** -/
theorem ke_core_nontors (hM : T.MixHyp (m + 1)) (hmn : m < T.n) {g : LC m} (hk : ks m = .exp g)
    (hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m h.of_succ) A).natDegree)
    (β₀ : AlgebraicClosure (T.F m))
    (hp0 : β₀ ^ 2 = algebraMap (T.F m) _ ((T.keS m h A hsq hdeg θ hθ μ hμ).p.eval 0))
    (hβ₀ : β₀ ≠ 0)
    (hnt : ∀ N : ℕ, 0 < N → ¬ (T.keS m h A hsq hdeg θ hθ μ hμ).IsPrincipalS
      (AlgebraicClosure (T.F m)) (SuperData.gammaP β₀) N)
    (B : GPoly (LC m)) (k l : ℕ) {ι : Type*} (s : Finset ι) (c u : ι → L)
    (hcd : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ a ∈ T.F (m + 1), a′ + (1 / 2 : L) * logDeriv (T.evP m A) * a = T.evP m B / (T.ts m ^ k * T.evP m A ^ l) := by
  classical
  set S := T.keS m h A hsq hdeg θ hθ μ hμ with hS
  have hμ0 : ((μ : T.F m) : L) ≠ 0 := fun h0 ↦ hμ (Subtype.ext h0)
  have hA0 : T.evP m A ≠ 0 := fun h0 ↦ S.htr ⟨_, hsq.ne_zero, by
    change aeval (T.ts m) _ = 0
    rw [T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ)]; exact h0⟩
  have hθ0 : θ ≠ 0 := fun h0 ↦ hA0 (by rw [← hθ, h0, zero_pow two_ne_zero])
  set b := T.evP m B / (T.ts m ^ k * T.evP m A ^ l) / ((μ : T.F m) : L) with hbdef
  have hb := T.keS_b m h A hsq hdeg θ hθ μ hμ B k l
  have hfm : T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ ∈ (T.F m)⟮S.x⟯⟮S.y⟯ :=
    T.keS_mem m h A hsq hdeg θ hθ μ hμ _ (mul_mem (IntermediateField.algebraMap_mem _
      (⟨T.evP m B / (T.ts m ^ k * T.evP m A ^ l), div_mem (T.evP_mem m (T.ev_mem m) B)
        (mul_mem (pow_mem (T.ts_mem m) k)
          (pow_mem (T.evP_mem m (T.ev_mem m) A) l))⟩ : T.F (m + 1)))
        (mem_adjoin_simple_self _ _))
  have hby : b * S.y = T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ := by
    change b * (θ * μ) = _
    rw [hbdef]; field_simp
  have hbm : b * S.y ∈ (T.F m)⟮S.x⟯⟮S.y⟯ := hby ▸ hfm
  have hreg0 := T.keS_reg m h A hsq hdeg θ hθ μ hμ B k l hfm
  have hreg : ∀ α β : AlgebraicClosure (T.F m), β ≠ 0 →
      β ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval α →
      α ≠ 0 → 0 ≤ S.ordAt (AlgebraicClosure (T.F m)) ⟨b * S.y, hbm⟩ α β := by
    intro α β hβ hv hα
    have e : (⟨b * S.y, hbm⟩ : (T.F m)⟮S.x⟯⟮S.y⟯) = ⟨_, hfm⟩ := Subtype.ext hby
    rw [e]; exact hreg0 α β hβ hv hα
  have heq' : b * S.y = v′ + ∑ i ∈ s, c i * logDeriv (u i) := by rw [hby]; exact heq
  obtain ⟨a, ha, hae⟩ := S.ke_liouville_nontors (K := AlgebraicClosure (T.F m)) rfl β₀ hp0 hβ₀
    (T.keS_cop m h A hsq hdeg θ hθ μ hμ hcopA) ((T.val m g)′) (T.keS_hx m h A hsq hdeg θ hθ μ hμ hmn hk)
    (fun c ↦ deriv_algebraMap c) (T.keS_good m hM hk) (T.keS_constC m) hnt b hb hbm hreg s c u hcd
    (fun i hi ↦ ⟨(hu i hi).1, T.keS_mem m h A hsq hdeg θ hθ μ hμ _ (hu i hi).2⟩) v
    (T.keS_mem m h A hsq hdeg θ hθ μ hμ _ hv) heq'
  refine ⟨a * μ, ?_, ?_⟩
  · have haF : a ∈ T.F (m + 1) := by
      rw [T.mem_F_succ]
      exact ha
    exact mul_mem haF (T.le_succ m μ.2)
  · have h1 := deriv_mul_radical θ (T.evP m A) 2 two_pos hθ hA0 (a * μ) 1
    simp only [pow_one] at h1
    have h2 : (a * S.y)′ = (a * μ * θ)′ := by
      change (a * (θ * μ))′ = _; ring_nf
    rw [hby, h2, h1] at hae
    have := mul_right_cancel₀ hθ0 hae
    rw [this]
    push_cast
    ring

open Classical in
/-- **With a torsion witness, the parametric Risch equation has a solution in `Fₘ₊₁`.** -/
theorem ke_core_tors (hM : T.MixHyp (m + 1)) (hmn : m < T.n) {g : LC m} (hk : ks m = .exp g)
    (hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m h.of_succ) A).natDegree)
    (hp0 : (T.keS m h A hsq hdeg θ hθ μ hμ).p.eval 0 = 1)
    (N : ℕ) (hN : 0 < N) (W : (T.F m)⟮(T.keS m h A hsq hdeg θ hθ μ hμ).x⟯⟮(T.keS m h A hsq hdeg θ hθ μ hμ).y⟯)
    (hW : W ≠ 0)
    (hWord : ∀ α β : AlgebraicClosure (T.F m),
      β ^ (T.keS m h A hsq hdeg θ hθ μ hμ).n =
        ((T.keS m h A hsq hdeg θ hθ μ hμ).p.map (algebraMap (T.F m) _)).eval α →
      (T.keS m h A hsq hdeg θ hθ μ hμ).ordAt (AlgebraicClosure (T.F m)) W α β =
        N * SuperData.gammaP (1 : AlgebraicClosure (T.F m)) (α, β))
    (W0 W1 : L) (hW0 : W0 ∈ (T.F m)⟮(T.keS m h A hsq hdeg θ hθ μ hμ).x⟯)
    (hW1 : W1 ∈ (T.F m)⟮(T.keS m h A hsq hdeg θ hθ μ hμ).x⟯)
    (hWe : (W : L) = W0 + W1 * (T.keS m h A hsq hdeg θ hθ μ hμ).y)
    (hNm : W0 ^ 2 - W1 ^ 2 * aeval (T.ts m) (T.keS m h A hsq hdeg θ hθ μ hμ).p ≠ 0)
    (B : GPoly (LC m)) (k l : ℕ) {ι : Type*} (s : Finset ι) (c u : ι → L)
    (hcd : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ a ∈ T.F (m + 1), ∃ e : L, e′ = 0 ∧ a′ + (1 / 2 : L) * logDeriv (T.evP m A) * a =
      T.evP m B / (T.ts m ^ k * T.evP m A ^ l) + e * ((W0 * (W1′ + W1 *
        (aeval (T.ts m) (mapCoeffs (T.keS m h A hsq hdeg θ hθ μ hμ).p +
          Polynomial.C (T.val m g)′ * X * derivative (T.keS m h A hsq hdeg θ hθ μ hμ).p) /
        ((2 : L) * aeval (T.ts m) (T.keS m h A hsq hdeg θ hθ μ hμ).p))) - W0′ * W1) /
        (W0 ^ 2 - W1 ^ 2 * aeval (T.ts m) (T.keS m h A hsq hdeg θ hθ μ hμ).p) * ((μ : T.F m) : L)) := by
  classical
  let S := T.keS m h A hsq hdeg θ hθ μ hμ
  have hμ0 : ((μ : T.F m) : L) ≠ 0 := fun h0 ↦ hμ (Subtype.ext h0)
  have hA0 : T.evP m A ≠ 0 := fun h0 ↦ S.htr ⟨_, hsq.ne_zero, by
    change aeval (T.ts m) _ = 0
    rw [T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ)]; exact h0⟩
  have hθ0 : θ ≠ 0 := fun h0 ↦ hA0 (by rw [← hθ, h0, zero_pow two_ne_zero])
  set b := T.evP m B / (T.ts m ^ k * T.evP m A ^ l) / ((μ : T.F m) : L) with hbdef
  have hb := T.keS_b m h A hsq hdeg θ hθ μ hμ B k l
  have hfm : T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ ∈ (T.F m)⟮S.x⟯⟮S.y⟯ :=
    T.keS_mem m h A hsq hdeg θ hθ μ hμ _ (mul_mem (IntermediateField.algebraMap_mem _
      (⟨T.evP m B / (T.ts m ^ k * T.evP m A ^ l), div_mem (T.evP_mem m (T.ev_mem m) B)
        (mul_mem (pow_mem (T.ts_mem m) k)
          (pow_mem (T.evP_mem m (T.ev_mem m) A) l))⟩ : T.F (m + 1)))
        (mem_adjoin_simple_self _ _))
  have hby : b * S.y = T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ := by
    change b * (θ * μ) = _
    rw [hbdef]; field_simp
  have hbm : b * S.y ∈ (T.F m)⟮S.x⟯⟮S.y⟯ := hby ▸ hfm
  have hreg0 := T.keS_reg m h A hsq hdeg θ hθ μ hμ B k l hfm
  have hreg : ∀ α β : AlgebraicClosure (T.F m), β ≠ 0 →
      β ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval α →
      α ≠ 0 → 0 ≤ S.ordAt (AlgebraicClosure (T.F m)) ⟨b * S.y, hbm⟩ α β := by
    intro α β hβ hv hα
    have e : (⟨b * S.y, hbm⟩ : (T.F m)⟮S.x⟯⟮S.y⟯) = ⟨_, hfm⟩ := Subtype.ext hby
    rw [e]; exact hreg0 α β hβ hv hα
  have heq' : b * S.y = v′ + ∑ i ∈ s, c i * logDeriv (u i) := by rw [hby]; exact heq
  have hp0' : (1 : AlgebraicClosure (T.F m)) ^ 2 = algebraMap (T.F m) _ (S.p.eval 0) := by
    rw [hp0, map_one, one_pow]
  have HT := S.ke_liouville_tors (K := AlgebraicClosure (T.F m)) rfl 1 hp0'
    one_ne_zero (T.keS_cop m h A hsq hdeg θ hθ μ hμ hcopA) ((T.val m g)′)
    (T.keS_hx m h A hsq hdeg θ hθ μ hμ hmn hk) (fun c ↦ deriv_algebraMap c) (T.keS_good m hM hk)
    (T.keS_constC m) N hN W hW hWord W0 W1 hW0 hW1 hWe hNm b hb hbm hreg s c u hcd
    (fun i hi ↦ ⟨(hu i hi).1, T.keS_mem m h A hsq hdeg θ hθ μ hμ _ (hu i hi).2⟩) v
    (T.keS_mem m h A hsq hdeg θ hθ μ hμ _ hv) heq'
  obtain ⟨a, ha, HT2⟩ := HT
  obtain ⟨e, HT3⟩ := HT2
  have he := HT3.1
  have hae := HT3.2
  refine ⟨a * μ, ?_, -algebraMap (T.F m) L e, by rw [map_neg, he, neg_zero], ?_⟩
  · have haF : a ∈ T.F (m + 1) := by
      rw [T.mem_F_succ]
      exact ha
    exact mul_mem haF (T.le_succ m μ.2)
  · have h1 := deriv_mul_radical θ (T.evP m A) 2 two_pos hθ hA0 (a * μ) 1
    simp only [pow_one] at h1
    have h2 : (a * S.y)′ = (a * μ * θ)′ := by
      change (a * (θ * μ))′ = _; ring_nf
    rw [hby, h2, h1] at hae
    have hSy : S.y = θ * μ := rfl
    rw [hSy] at hae
    have hn : ((S.n : ℕ) : L) = 2 := by show ((2 : ℕ) : L) = 2; norm_num
    rw [hn] at hae
    have hPx : aeval S.x S.p = aeval (T.ts m) (T.keS m h A hsq hdeg θ hθ μ hμ).p := rfl
    have hQx : aeval S.x (mapCoeffs S.p + Polynomial.C (T.val m g)′ * X * derivative S.p) =
        aeval (T.ts m) (mapCoeffs (T.keS m h A hsq hdeg θ hθ μ hμ).p +
          Polynomial.C (T.val m g)′ * X * derivative (T.keS m h A hsq hdeg θ hθ μ hμ).p) := rfl
    rw [hPx, hQx] at hae
    have hc : ((((1 : ℕ) : ℚ) : L) / ((2 : ℕ) : L)) = 1 / 2 := by push_cast; ring
    rw [hc] at hae
    apply mul_right_cancel₀ hθ0
    push_cast
    linear_combination (-1 : L) * hae

end Core

end MTower

end Curves.MT
