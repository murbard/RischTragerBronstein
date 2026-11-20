import RischTragerBronstein.Computable.LiExpBaseConst
import RischTragerBronstein.Computable.ExpExpBaseLaurent

/-!
# Non-elementary primitive over an exponential, level `0`: Laurent polynomials in `t₁ = exp a₁`

`K = R(x)(t₁)(t₂)`, `t₁ = exp a₁`, `t₂′ = W` with the proper part of `W` failing the residue test.
For a Laurent polynomial in `t₁` with coefficients in `R(x)`: if some Risch differential equation
`y′ + (j - k) a₁′ y = Aⱼ` has no solution in `R(x)`, there is no elementary integral over `K`.
Liouville's theorem at `t₂` leaves `c₀ W`; a Laurent polynomial minus `c₀ W` can have constant
residues only for `c₀ = 0` (`laurent_const_eq_zero`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

variable {R F₀ K : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K]

set_option maxHeartbeats 3200000 in
theorem not_elementary_liExpBaseLaurent (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (a₁ : CPoly R) (ha₁ : trim (deriv a₁) ≠ [])
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (derivative (toPoly a₁)) * t₁)
    (hgen₀ : adjoin R {x₀, t₁} = (⊤ : IntermediateField R F₀))
    (W : GFrac (GFrac R))
    (t : K) (hgen : adjoin F₀ {t} = (⊤ : IntermediateField F₀ K))
    (ht : t′ = algebraMap F₀ K (Tower.valG x₀ t₁ W))
    (hW0 : GPoly.isZero (Tower.ops₁g R) W.2 = false)
    (hWnd : Tower.isDerivExp a₁ W.1 W.2 = false)
    (hresW : GPoly.residueCheck (Tower.ops₁g R) (Tower.expW a₁) (Tower.expReduce a₁ W.1 W.2).r
      (Tower.expReduce a₁ W.1 W.2).s = false)
    (N k : ℕ) (A D : ℕ → CPoly R) (A₀ D₀ : CPoly R)
    (hD0 : ∀ j < N, toPoly (D j) ≠ 0)
    (j₀ : ℕ) (hj₀ : j₀ < N) (hj₀k : j₀ ≠ k)
    (hnone : rdeRational (expCoeffZ a₁ ((j₀ : ℤ) - k)) (A j₀) (D j₀) = none)
    (E : Type*) [Field E] [Differential E] [Algebra K E] [DifferentialAlgebra K E]
    [CharZero K] (hE : IsElementaryExtension K E) (g : E) :
    g′ ≠ algebraMap K E (algebraMap F₀ K (aeval x₀ (toPoly A₀) / aeval x₀ (toPoly D₀) +
      ∑ j ∈ (Finset.range N).erase k,
        aeval x₀ (toPoly (A j)) / aeval x₀ (toPoly (D j)) * t₁ ^ j / t₁ ^ k)) := by
  intro hg
  classical
  set ψ := algebraMap K E with hψ
  have hcharE : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  -- the field of constants of `E`, as a base field with the trivial derivation
  let Cc := constants E
  let _ : Differential Cc := ⟨0⟩
  have hCc0 : ∀ c : Cc, c′ = 0 := fun _ ↦ rfl
  have hDAc : DifferentialAlgebra Cc E := ⟨fun c ↦ c.2⟩
  have hcharC : CharZero Cc := ⟨fun m n h ↦ by
    have := congrArg (fun z : Cc ↦ (z : E)) h
    simpa using this⟩
  -- `F₀ → E`
  let j₀' : F₀ →+* E := ψ.comp (algebraMap F₀ K)
  have hj₀' : ∀ f : F₀, (j₀' f)′ = j₀' f′ := fun f ↦ by
    change (ψ (algebraMap F₀ K f))′ = ψ (algebraMap F₀ K f′)
    rw [hψ, deriv_algebraMap, deriv_algebraMap]
  have hRE : ∀ r : R, (j₀' (algebraMap R F₀ r))′ = 0 := fun r ↦ by
    rw [hj₀', hR, map_zero]
  -- `R → Const E`
  let ι : R →+* Cc :=
    { toFun := fun r ↦ ⟨j₀' (algebraMap R F₀ r), by rw [mem_constants]; exact hRE r⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ ↦ Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ ↦ Subtype.ext (by simp) }
  have hι : ∀ (P : R[X]) (z : F₀), aeval (j₀' z) (P.map ι) = j₀' (aeval z P) := fun P z ↦ by
    rw [aeval_def, eval₂_map, aeval_def, hom_eval₂]
    rfl
  set xE := j₀' x₀ with hxE
  set tE := ψ t with htE
  have hxE' : xE′ = 1 := by rw [hxE, hj₀', hx₀, map_one]
  -- (1) `x` is transcendental over the constants
  have htrx : Transcendental Cc xE :=
    transcendental_of_deriv_ne_zero hCc0 (by rw [hxE']; exact one_ne_zero)
  -- the field `F₁ = C'(x)`
  have hw : xE′ = aeval xE (1 : Cc[X]) := by rw [hxE', map_one]
  let _ := algebraAdjoinSimple (F := Cc) xE
  let _ : Differential Cc[X] := polynomialOfDeriv (1 : Cc[X])
  let _ : Differential Cc⟮xE⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple xE 1 hw)
  have hFR : IsFractionRing Cc[X] Cc⟮xE⟯ := isFractionRing_adjoin_simple xE htrx
  have hDA1 : DifferentialAlgebra Cc[X] Cc⟮xE⟯ := differentialAlgebra_adjoin_simple xE 1 hw
  have hDA1E : DifferentialAlgebra Cc⟮xE⟯ E :=
    differentialAlgebra_of_derivClosed (derivClosed_adjoin_simple xE 1 hw)
  have hchar1 : CharZero Cc⟮xE⟯ :=
    charZero_of_injective_algebraMap (algebraMap Cc Cc⟮xE⟯).injective
  have hD : ∀ P : Cc[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial hCc0 P
  have hvalE : ∀ P : R[X], algebraMap Cc⟮xE⟯ E (algebraMap Cc[X] Cc⟮xE⟯ (P.map ι)) =
      j₀' (aeval x₀ P) := fun P ↦ (algebraMap_adjoinSimple xE _).trans (hι _ x₀)
  have hKconst₁ : ∀ y : Cc⟮xE⟯, y′ = 0 → ∃ b : Cc, y = algebraMap Cc[X] Cc⟮xE⟯ (C b) :=
    fun y hy ↦ by
      have hyE : ((y : Cc⟮xE⟯) : E)′ = 0 := congrArg Subtype.val hy
      refine ⟨⟨(y : E), hyE⟩, ?_⟩
      apply Subtype.ext
      rw [algebraMap_adjoinSimple, aeval_C]
      rfl
  -- `η₁`, `η₂` in `F₁ = C'(x)`
  set A₁' : Cc[X] := (derivative (toPoly a₁)).map ι with hA₁'
  have hA₁'0 : A₁' ≠ 0 := by
    rw [hA₁', Ne, Polynomial.map_eq_zero_iff ι.injective, ← toPoly_deriv]
    exact fun h ↦ ha₁ ((trim_eq_nil_iff _).mpr h)
  set η₁' : Cc⟮xE⟯ := algebraMap Cc[X] Cc⟮xE⟯ A₁' with hη₁'
  set t1E := j₀' t₁ with ht1E
  have hη₁E : algebraMap Cc⟮xE⟯ E η₁' = j₀' (aeval x₀ (derivative (toPoly a₁))) := by
    rw [hη₁', hvalE]
  have ht1E' : t1E′ = algebraMap Cc⟮xE⟯ E η₁' * t1E := by
    rw [ht1E, hj₀', ht₁, hη₁E, map_mul]
  have ht1E0 : t1E ≠ 0 := fun h ↦ ht₁0 ((map_eq_zero_iff j₀' j₀'.injective).mp h)
  -- (2) `t₁` is transcendental over `F₁`
  have htr1 : Transcendental Cc⟮xE⟯ t1E := by
    refine transcendental_exponential η₁' ht1E0 ht1E' fun n hn b hb ↦ ?_
    refine rde_homogeneous' (K := Cc⟮xE⟯) hD (-(C (n : Cc) * A₁'))
      (neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)) hA₁'0)) b (by
        rw [hb, map_neg, map_mul, ← hη₁']
        have : algebraMap Cc[X] Cc⟮xE⟯ (C (n : Cc)) = (n : Cc⟮xE⟯) := by
          rw [show (C (n : Cc) : Cc[X]) = (n : Cc[X]) from map_natCast C n, map_natCast]
        rw [this]
        ring)
  -- the field `F₂ = F₁(t₁)`
  have hw1 : t1E′ = aeval t1E (C η₁' * X : (Cc⟮xE⟯)[X]) := by
    rw [map_mul, aeval_C, aeval_X, ht1E']
  let _ := algebraAdjoinSimple (F := Cc⟮xE⟯) t1E
  let _ : Differential (Cc⟮xE⟯)[X] := polynomialOfDeriv (C η₁' * X)
  let _ : Differential (Cc⟮xE⟯)⟮t1E⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple t1E (C η₁' * X) hw1)
  have hFR2 : IsFractionRing (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ := isFractionRing_adjoin_simple t1E htr1
  have hDA2 : DifferentialAlgebra (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ :=
    differentialAlgebra_adjoin_simple t1E (C η₁' * X) hw1
  have hDA2E : DifferentialAlgebra (Cc⟮xE⟯)⟮t1E⟯ E :=
    differentialAlgebra_of_derivClosed (derivClosed_adjoin_simple t1E (C η₁' * X) hw1)
  have hchar2 : CharZero (Cc⟮xE⟯)⟮t1E⟯ :=
    charZero_of_injective_algebraMap (algebraMap Cc⟮xE⟯ (Cc⟮xE⟯)⟮t1E⟯).injective
  have hconst1 : ∀ z ∈ (Cc⟮xE⟯)⟮t1E⟯, z′ = 0 → z ∈ Set.range (algebraMap Cc⟮xE⟯ E) :=
    fun z _ hz ↦ ⟨algebraMap Cc Cc⟮xE⟯ ⟨z, hz⟩, rfl⟩
  have hconst2 : ∀ z ∈ ((Cc⟮xE⟯)⟮t1E⟯)⟮tE⟯, z′ = 0 →
      z ∈ Set.range (algebraMap (Cc⟮xE⟯)⟮t1E⟯ E) :=
    fun z _ hz ↦ ⟨algebraMap Cc⟮xE⟯ (Cc⟮xE⟯)⟮t1E⟯ (algebraMap Cc Cc⟮xE⟯ ⟨z, hz⟩), rfl⟩
  -- (4) the strong Liouville theorem
  obtain ⟨κ, s, c, u, v, hdata, hv, heq⟩ := liouville_strong hE _ g hg
  set B₂ : IntermediateField (Cc⟮xE⟯)⟮t1E⟯ E := ((Cc⟮xE⟯)⟮t1E⟯)⟮tE⟯ with hB₂
  have hBconst : ∀ z : E, z′ = 0 → z ∈ B₂ := fun z hz ↦
    B₂.algebraMap_mem (algebraMap Cc⟮xE⟯ (Cc⟮xE⟯)⟮t1E⟯ (algebraMap Cc Cc⟮xE⟯ ⟨z, hz⟩))
  -- `F₀ = R(x₀, t₁)` maps into `F₂`
  have hxF₂ : xE ∈ (Cc⟮xE⟯)⟮t1E⟯ :=
    ((Cc⟮xE⟯)⟮t1E⟯).algebraMap_mem ⟨xE, mem_adjoin_simple_self Cc xE⟩
  have ht₁F₂ : t1E ∈ (Cc⟮xE⟯)⟮t1E⟯ := mem_adjoin_simple_self _ t1E
  have hF₀ : ∀ f : F₀, j₀' f ∈ (Cc⟮xE⟯)⟮t1E⟯ := by
    let T₀ : IntermediateField R F₀ :=
      { carrier := {f | j₀' f ∈ (Cc⟮xE⟯)⟮t1E⟯}
        mul_mem' := fun {k l} hk hl ↦ by
          change j₀' (k * l) ∈ (Cc⟮xE⟯)⟮t1E⟯; rw [map_mul]; exact mul_mem hk hl
        one_mem' := by change j₀' 1 ∈ (Cc⟮xE⟯)⟮t1E⟯; rw [map_one]; exact one_mem _
        add_mem' := fun {k l} hk hl ↦ by
          change j₀' (k + l) ∈ (Cc⟮xE⟯)⟮t1E⟯; rw [map_add]; exact add_mem hk hl
        zero_mem' := by change j₀' 0 ∈ (Cc⟮xE⟯)⟮t1E⟯; rw [map_zero]; exact zero_mem _
        algebraMap_mem' := fun r ↦
          ((Cc⟮xE⟯)⟮t1E⟯).algebraMap_mem (algebraMap Cc Cc⟮xE⟯ (ι r))
        inv_mem' := fun k hk ↦ by
          change j₀' k⁻¹ ∈ (Cc⟮xE⟯)⟮t1E⟯; rw [map_inv₀]; exact inv_mem hk }
    have hT₀ : T₀ = ⊤ := by
      rw [eq_top_iff, ← hgen₀, adjoin_le_iff]
      rintro k (rfl | rfl)
      · exact hxF₂
      · exact ht₁F₂
    intro f
    have : f ∈ T₀ := hT₀ ▸ IntermediateField.mem_top
    exact this
  let j : F₀ →+* (Cc⟮xE⟯)⟮t1E⟯ := j₀'.codRestrict _ hF₀
  let T : IntermediateField F₀ K :=
    { carrier := {k | ψ k ∈ B₂}
      mul_mem' := fun {k l} hk hl ↦ by
        change ψ (k * l) ∈ B₂; rw [map_mul]; exact mul_mem hk hl
      one_mem' := by change ψ 1 ∈ B₂; rw [map_one]; exact one_mem _
      add_mem' := fun {k l} hk hl ↦ by
        change ψ (k + l) ∈ B₂; rw [map_add]; exact add_mem hk hl
      zero_mem' := by change ψ 0 ∈ B₂; rw [map_zero]; exact zero_mem _
      algebraMap_mem' := fun f ↦ B₂.algebraMap_mem (j f)
      inv_mem' := fun k hk ↦ by
        change ψ k⁻¹ ∈ B₂; rw [map_inv₀]; exact inv_mem hk }
  have hT' : T = ⊤ := by
    rw [eq_top_iff, ← hgen, adjoin_le_iff]
    rintro k rfl
    exact mem_adjoin_simple_self _ tE
  have hKB : ∀ k : K, ψ k ∈ B₂ := fun k ↦ by
    have : k ∈ T := hT' ▸ IntermediateField.mem_top
    exact this
  have hcf : ∀ z ∈ constField K E, z ∈ B₂ := by
    let N : IntermediateField K E := { B₂.toSubfield with algebraMap_mem' := hKB }
    have : constField K E ≤ N := adjoin_le_iff.mpr fun z hz ↦ hBconst z hz
    exact fun z hz ↦ this hz
  -- (5) the limited-integration criterion over `F₂`
  let c' : κ → (Cc⟮xE⟯)⟮t1E⟯ := fun i ↦
    if hi : i ∈ s then algebraMap Cc⟮xE⟯ (Cc⟮xE⟯)⟮t1E⟯
      (algebraMap Cc Cc⟮xE⟯ ⟨c i, (hdata i hi).1⟩) else 0
  -- (6) the two-level model `F₁ ⊆ F₂`
  have hST : IsScalarTower Cc⟮xE⟯ (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      apply Subtype.ext
      rw [Polynomial.algebraMap_eq, algebraMap_adjoinSimple, aeval_C]
      rfl
  have hDA12 : DifferentialAlgebra Cc⟮xE⟯ (Cc⟮xE⟯)⟮t1E⟯ := ⟨fun a ↦ Subtype.ext rfl⟩
  have hηa : Tower.ηa (K₁ := Cc⟮xE⟯) ι a₁ = η₁' := rfl
  have hD₂ : ∀ P : (Cc⟮xE⟯)[X], P′ = implicitDeriv (C (Tower.ηa (K₁ := Cc⟮xE⟯) ι a₁) * X) P :=
    fun P ↦ by rw [hηa]; rfl
  have hdega : 1 ≤ ((toPoly a₁).map ι).natDegree := by
    by_contra hlt
    have h0' : derivative ((toPoly a₁).map ι) = 0 := by
      rw [eq_C_of_natDegree_eq_zero (by omega : ((toPoly a₁).map ι).natDegree = 0), derivative_C]
    rw [derivative_map] at h0'
    exact hA₁'0 h0'
  have hconst : ∀ (P : (Cc⟮xE⟯)[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ →
      ∃ e : Cc⟮xE⟯, P = C e * X ^ n :=
    exp_polynomial_no_new_constants hD ((toPoly a₁).map ι) hdega
      (fun P ↦ by rw [hD₂, hηa, hη₁', hA₁', derivative_map])
  have hK₂const : ∀ y : (Cc⟮xE⟯)⟮t1E⟯, y′ = 0 → ∃ b : Cc,
      y = algebraMap Cc⟮xE⟯ (Cc⟮xE⟯)⟮t1E⟯ (algebraMap Cc[X] Cc⟮xE⟯ (C b)) := fun y hy ↦ by
    have hyE : ((y : (Cc⟮xE⟯)⟮t1E⟯) : E)′ = 0 := congrArg Subtype.val hy
    refine ⟨⟨(y : E), hyE⟩, ?_⟩
    apply Subtype.ext
    change (y : E) = ((algebraMap Cc[X] Cc⟮xE⟯ (C (⟨(y : E), hyE⟩ : Cc)) : Cc⟮xE⟯) : E)
    rw [algebraMap_adjoinSimple, aeval_C]
    rfl
  -- values of codes in `F₂`
  have hvalP : ∀ q : GPoly (GFrac R), algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯
      (GPoly.toPoly (Tower.M₁In (K₁ := Cc⟮xE⟯) ι hCc0 hD) q) = j (Tower.valP x₀ t₁ q) := fun q ↦ by
    apply Subtype.ext
    rw [algebraMap_adjoinSimple, GPoly.toPoly_eq_sum_range _ q ([], [1])]
    change _ = j₀' (Tower.valP x₀ t₁ q)
    simp only [Tower.valP, map_sum, map_mul, map_pow, map_div₀, aeval_C, aeval_X,
      Tower.sem_M₁In, ev, hvalE]
    rfl
  have hM : Tower.ModelEW (K₁ := Cc⟮xE⟯) (K₂ := (Cc⟮xE⟯)⟮t1E⟯) ι a₁ :=
    { hD := hD
      ha := ha₁
      hD₂ := hD₂
      hconst := hconst
      hK₂const := fun y hy ↦ by
        obtain ⟨b, hb⟩ := hK₂const y hy
        exact ⟨b, by rw [hb, IsScalarTower.algebraMap_apply Cc⟮xE⟯ (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯,
          Polynomial.algebraMap_eq]⟩ }
  have hsemG : ∀ q : GFrac (GFrac R), (hM.cf ι hCc0).sem q = j (Tower.valG x₀ t₁ q) :=
      fun q ↦ by
    change algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (GPoly.toPoly (Tower.M₁In (K₁ := Cc⟮xE⟯) ι hCc0 hD) q.1) /
      algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (GPoly.toPoly (Tower.M₁In (K₁ := Cc⟮xE⟯) ι hCc0 hD) q.2) = _
    rw [hvalP, hvalP, Tower.valG, map_div₀]
  -- (3) `t₂` is transcendental over `F₂`: `W` is not a derivative
  set η₂'' : (Cc⟮xE⟯)⟮t1E⟯ := j (Tower.valG x₀ t₁ W) with hη₂''
  have htE'' : tE′ = algebraMap (Cc⟮xE⟯)⟮t1E⟯ E η₂'' := by
    rw [htE, hψ, deriv_algebraMap, ht]
    rfl
  have hW0' : GPoly.toPoly (Tower.M₁In (K₁ := Cc⟮xE⟯) ι hCc0 hD) W.2 ≠ 0 := fun hz ↦ by
    rw [(GPoly.isZero_iff (Tower.M₁In (K₁ := Cc⟮xE⟯) ι hCc0 hD) W.2).mpr hz] at hW0
    exact Bool.noConfusion hW0
  have hη₂nd : ∀ y : (Cc⟮xE⟯)⟮t1E⟯, y′ ≠ η₂'' := fun y hy ↦ by
    have := Tower.isDerivExp_complete (K₁ := Cc⟮xE⟯) (K₂ := (Cc⟮xE⟯)⟮t1E⟯) ι hCc0 hD a₁ ha₁
      hD₂ hconst W.1 W.2 hW0' y (by rw [hy, hη₂'', ← hsemG]; rfl)
    rw [hWnd] at this
    exact Bool.noConfusion this
  have htr2 : Transcendental (Cc⟮xE⟯)⟮t1E⟯ tE := transcendental_primitive η₂'' htE'' hη₂nd
  set fA : F₀ := aeval x₀ (toPoly A₀) / aeval x₀ (toPoly D₀) +
    ∑ j ∈ (Finset.range N).erase k,
      aeval x₀ (toPoly (A j)) / aeval x₀ (toPoly (D j)) * t₁ ^ j / t₁ ^ k with hfA
  -- (5) Liouville's theorem at the primitive step `t₂`
  obtain ⟨e, c₀, d₀, he, hc₀, hrel₀⟩ := liouville_step_primitive (F := (Cc⟮xE⟯)⟮t1E⟯) tE htr2 η₂''
    htE'' hconst2 s c' u (fun i hi ↦ ⟨hcf _ (hdata i hi).2.1, (hdata i hi).2.2⟩) v (hcf _ hv)
    (j fA) (by
      change j₀' fA = _
      have h1 : j₀' fA = ψ (algebraMap F₀ K fA) := rfl
      rw [h1, heq]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [c', dif_pos hi]
      rfl)
  have hc₀E : ((c₀ : (Cc⟮xE⟯)⟮t1E⟯) : E)′ = 0 := congrArg Subtype.val hc₀
  set cc : Cc := ⟨(c₀ : E), hc₀E⟩ with hcc
  have hcst : algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (C (algebraMap Cc[X] Cc⟮xE⟯ (C cc))) = c₀ := by
    apply Subtype.ext
    rw [algebraMap_adjoinSimple, aeval_C]
    change ((algebraMap Cc[X] Cc⟮xE⟯ (C cc) : Cc⟮xE⟯) : E) = _
    rw [algebraMap_adjoinSimple, aeval_C]
    rfl
  let c₁ : κ → Cc⟮xE⟯ := fun i ↦
    if hi : i ∈ s then algebraMap Cc Cc⟮xE⟯ ⟨c i, (hdata i hi).1⟩ else 0
  have hc₁ : ∀ i ∈ s, algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ (C (c₁ i)) = c' i := fun i hi ↦ by
    apply Subtype.ext
    rw [algebraMap_adjoinSimple, aeval_C]
    simp only [c₁, c', dif_pos hi]
    rfl
  have hc₁' : ∀ i ∈ s, (c₁ i)′ = 0 := fun i hi ↦ by
    simp only [c₁, dif_pos hi]
    exact Subtype.ext (hdata i hi).1
  have hj : ∀ a : F₀, j a′ = (j a)′ := fun a ↦ Subtype.ext (hj₀' a).symm
  -- `fA` is a Laurent polynomial in `t₁` over `F₁`
  let fr : CPoly R → CPoly R → Cc⟮xE⟯ := fun P Q ↦
    algebraMap Cc[X] Cc⟮xE⟯ ((toPoly P).map ι) / algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Q).map ι)
  have hfr : ∀ P Q : CPoly R, algebraMap Cc⟮xE⟯ E (fr P Q) =
      j₀' (aeval x₀ (toPoly P) / aeval x₀ (toPoly Q)) := fun P Q ↦ by
    simp only [fr]
    rw [map_div₀, hvalE, hvalE, map_div₀]
  let Ap₀ : (Cc⟮xE⟯)[X] := C (fr A₀ D₀) * X ^ k +
    ∑ j ∈ (Finset.range N).erase k, C (fr (A j) (D j)) * X ^ j
  have htn : t1E ^ k ≠ 0 := pow_ne_zero _ ht1E0
  have hAp₀ : aeval t1E Ap₀ / t1E ^ k = j₀' fA := by
    simp only [Ap₀, hfA, map_add, map_sum, map_mul, map_pow, aeval_C, aeval_X, hfr, map_div₀]
    rw [add_div, Finset.sum_div, mul_div_assoc, div_self htn, mul_one]
  have hjfA : j fA = algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ Ap₀ /
      algebraMap (Cc⟮xE⟯)[X] (Cc⟮xE⟯)⟮t1E⟯ X ^ k := by
    apply Subtype.ext
    rw [IntermediateField.coe_div, SubmonoidClass.coe_pow, algebraMap_adjoinSimple,
      algebraMap_adjoinSimple, aeval_X, hAp₀]
    rfl
  -- `c₀ = 0`: the proper part of `W` does not have constant residues
  have hcc0 : cc = 0 := Tower.laurent_const_eq_zero (K₁ := Cc⟮xE⟯) (K₂ := (Cc⟮xE⟯)⟮t1E⟯) ι hCc0 hM
    W hW0' hresW Ap₀ k cc s c₁ hc₁' e he d₀ (by
      rw [← hjfA, hsemG, hcst]
      change j fA - c₀ * η₂'' = _
      rw [Finset.sum_congr rfl fun i hi ↦ by rw [hc₁ i hi], hrel₀]
      ring)
  have hc₀0 : c₀ = 0 := by rw [← hcst, hcc0]; simp
  have hrel : j fA = ∑ i ∈ s, c' i * logDeriv (e i) + d₀′ := by
    rw [hrel₀, hc₀0, zero_mul, add_zero]
  set dd := d₀ with hdd
  -- the identity in `E`, over `F₁ = C'(x)`
  have hc₁E : ∀ i ∈ s, algebraMap Cc⟮xE⟯ E (c₁ i) = ((c' i : (Cc⟮xE⟯)⟮t1E⟯) : E) := fun i hi ↦ by
    simp only [c₁, c', dif_pos hi]
    rfl
  let u' : κ → E := fun i ↦ (e i : E)
  have heqE : j₀' fA = ∑ i ∈ s, algebraMap Cc⟮xE⟯ E (c₁ i) * logDeriv (u' i) + (dd : E)′ := by
    have hjE : algebraMap (Cc⟮xE⟯)⟮t1E⟯ E (j fA) = j₀' fA := rfl
    have hRHS : algebraMap (Cc⟮xE⟯)⟮t1E⟯ E (∑ i ∈ s, c' i * logDeriv (e i) + dd′) =
        ∑ i ∈ s, algebraMap Cc⟮xE⟯ E (c₁ i) * logDeriv (u' i) + (dd : E)′ := by
      rw [map_add, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [map_mul, hc₁E i hi]
      congr 1
    rw [← hjE, hrel, hRHS]
  have hu' : ∀ i ∈ s, u' i ∈ (Cc⟮xE⟯)⟮t1E⟯ ∧ u' i ≠ 0 := fun i hi ↦
    ⟨(e i).2, fun h0 ↦ he i hi (Subtype.ext h0)⟩
  have hv' : (dd : E) ∈ (Cc⟮xE⟯)⟮t1E⟯ := dd.2
  -- (6) the integrand as a Laurent polynomial in `t₁` over `C'(x)`
  let fr : CPoly R → CPoly R → Cc⟮xE⟯ := fun P Q ↦
    algebraMap Cc[X] Cc⟮xE⟯ ((toPoly P).map ι) / algebraMap Cc[X] Cc⟮xE⟯ ((toPoly Q).map ι)
  have hfr : ∀ P Q : CPoly R, algebraMap Cc⟮xE⟯ E (fr P Q) =
      j₀' (aeval x₀ (toPoly P) / aeval x₀ (toPoly Q)) := fun P Q ↦ by
    simp only [fr]
    rw [map_div₀, hvalE, hvalE, map_div₀]
  let Ap : (Cc⟮xE⟯)[X] := C (fr A₀ D₀) * X ^ k +
    ∑ j ∈ (Finset.range N).erase k, C (fr (A j) (D j)) * X ^ j
  have htn : t1E ^ k ≠ 0 := pow_ne_zero _ ht1E0
  have hAp : aeval t1E Ap / t1E ^ k = j₀' fA := by
    simp only [Ap, hfA, map_add, map_sum, map_mul, map_pow, aeval_C, aeval_X, hfr, map_div₀]
    rw [add_div, Finset.sum_div, mul_div_assoc, div_self htn, mul_one]
  have hcoeff : Ap.coeff j₀ = fr (A j₀) (D j₀) := by
    simp only [Ap, coeff_add, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [if_neg hj₀k, mul_zero, zero_add, Finset.sum_eq_single j₀]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), mul_zero]
    · intro h'
      exact absurd (Finset.mem_erase.mpr ⟨hj₀k, Finset.mem_range.mpr hj₀⟩) h'
  obtain ⟨y, hy⟩ := (rde_step_exponential_laurent (F := Cc⟮xE⟯) t1E htr1 η₁' ht1E' hconst1 s c₁ u'
    hu' (dd : E) hv' Ap k (by rw [hAp, heqE])).1 j₀ hj₀k
  rw [hcoeff] at hy
  have hz : (((j₀ : ℤ) - k : ℤ) : R) ≠ 0 :=
    Int.cast_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hj₀k))
  have hg0 : toPoly (expCoeffZ a₁ ((j₀ : ℤ) - k)) ≠ 0 := by
    rw [expCoeffZ, toPoly_smul]
    exact mul_ne_zero (C_ne_zero.mpr hz) fun h0 ↦ ha₁ ((trim_eq_nil_iff _).mpr h0)
  refine rdeRational_complete (K := Cc⟮xE⟯) ι hD (hD0 j₀ hj₀) hg0 hnone y ?_
  rw [expCoeffZ, toPoly_smul, toPoly_deriv, Polynomial.map_mul, map_C, map_mul, ← hA₁', ← hη₁']
  have hcast : algebraMap Cc[X] Cc⟮xE⟯ (C (ι (((j₀ : ℤ) - k : ℤ) : R))) =
      (j₀ : Cc⟮xE⟯) - k := by
    simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_natCast]
  rw [hcast]
  exact hy

end CPoly
