import RischTragerBronstein.Computable.LiExpBaseResidue
import RischTragerBronstein.Computable.LiExpBaseLaurent
import RischTragerBronstein.Computable.PrimExpBaseFull
import RischTragerBronstein.Computable.PrimExpLoopWPositive

/-!
# Non-elementary primitive over an exponential: every element of `R(x)(exp a₁)` at level `0`

`ρ ∈ R(x)(t₁)`, `t₁ = exp a₁`, viewed in `K = R(x)(t₁)(t₂)` with `t₂′ = W` (proper part of `W`
failing the residue test at `t₁`), has an elementary integral iff `nestedConstE` finds a constant
`c` and the height-two integrator `integrateExp` accepts `ρ - c W`; then `∫ ρ = c t₂ + ∫ (ρ - c W)`.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Tower

open Differential CPoly

section F0

variable {R F₀ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field F₀]
variable [Algebra R F₀] [Differential F₀]

set_option maxHeartbeats 1600000 in
theorem valG_subSmulCodeE_F₀ (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) {a : CPoly R} (ha : trim (deriv a) ≠ [])
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (derivative (toPoly a)) * t₁)
    (ρ W : GFrac (GFrac R)) (c : R) :
    GPoly.isZero (ops₁g R) (subSmulCodeE a ρ W c).2 = false ∧
    valG x₀ t₁ (subSmulCodeE a ρ W c) = valG x₀ t₁ ρ - algebraMap R F₀ c * valG x₀ t₁ W := by
  classical
  have hcharF₀ : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap R F₀).injective
  let _ : Differential R := ⟨0⟩
  have h0 : ∀ r : R, r′ = 0 := fun _ ↦ rfl
  have hDAR : DifferentialAlgebra R F₀ := ⟨fun r ↦ by rw [hR, h0, map_zero]⟩
  -- level one: `R(x₀) ⊆ F₀`
  have htr : Transcendental R x₀ :=
    transcendental_of_deriv_ne_zero h0 (by rw [hx₀]; exact one_ne_zero)
  have hw : x₀′ = aeval x₀ (1 : R[X]) := by rw [hx₀, map_one]
  let _ := algebraAdjoinSimple (F := R) x₀
  let _ : Differential R[X] := polynomialOfDeriv (1 : R[X])
  let _ : Differential R⟮x₀⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple x₀ 1 hw)
  have hFR : IsFractionRing R[X] R⟮x₀⟯ := isFractionRing_adjoin_simple x₀ htr
  have hDA : DifferentialAlgebra R[X] R⟮x₀⟯ := differentialAlgebra_adjoin_simple x₀ 1 hw
  have hDA' : DifferentialAlgebra R⟮x₀⟯ F₀ :=
    differentialAlgebra_of_derivClosed (derivClosed_adjoin_simple x₀ 1 hw)
  have hchar1 : CharZero R⟮x₀⟯ := charZero_of_injective_algebraMap (algebraMap R R⟮x₀⟯).injective
  have hD : ∀ P : R[X], P′ = derivative P := fun P ↦ implicitDeriv_one_of_trivial h0 P
  have hcoe : ∀ P : R[X], ((algebraMap R[X] R⟮x₀⟯ P : R⟮x₀⟯) : F₀) = aeval x₀ P :=
    algebraMap_adjoinSimple x₀
  have hevc : ∀ q : CPoly R × CPoly R, algebraMap R⟮x₀⟯ F₀ (ev R⟮x₀⟯ (RingHom.id R) q) =
      aeval x₀ (toPoly q.1) / aeval x₀ (toPoly q.2) := fun q ↦ by
    change ((ev R⟮x₀⟯ (RingHom.id R) q : R⟮x₀⟯) : F₀) = _
    simp only [ev, Polynomial.map_id, IntermediateField.coe_div, hcoe]
  set η₁' : R⟮x₀⟯ := algebraMap R[X] R⟮x₀⟯ (derivative (toPoly a)) with hη₁'
  have hη₁E : algebraMap R⟮x₀⟯ F₀ η₁' = aeval x₀ (derivative (toPoly a)) := hcoe _
  have ht₁' : t₁′ = algebraMap R⟮x₀⟯ F₀ η₁' * t₁ := by rw [ht₁, hη₁E]
  have hA'0 : derivative (toPoly a) ≠ 0 := fun h' ↦ ha ((trim_eq_nil_iff _).mpr (by
    rw [toPoly_deriv, h']))
  have htr1 : Transcendental R⟮x₀⟯ t₁ := by
    refine transcendental_exponential η₁' ht₁0 ht₁' fun n hn b hb ↦ ?_
    refine rde_homogeneous' (K := R⟮x₀⟯) hD (-(C (n : R) * derivative (toPoly a)))
      (neg_ne_zero.mpr (mul_ne_zero (C_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)) hA'0)) b (by
        rw [hb, map_neg, map_mul, ← hη₁']
        have : algebraMap R[X] R⟮x₀⟯ (C (n : R)) = (n : R⟮x₀⟯) := by
          rw [show (C (n : R) : R[X]) = (n : R[X]) from map_natCast C n, map_natCast]
        rw [this]
        ring)
  have hw1 : t₁′ = aeval t₁ (C η₁' * X : (R⟮x₀⟯)[X]) := by
    rw [map_mul, aeval_C, aeval_X, ht₁']
  let _ := algebraAdjoinSimple (F := R⟮x₀⟯) t₁
  let _ : Differential (R⟮x₀⟯)[X] := polynomialOfDeriv (C η₁' * X)
  let _ : Differential (R⟮x₀⟯)⟮t₁⟯ :=
    differentialOfDerivClosed (derivClosed_adjoin_simple t₁ (C η₁' * X) hw1)
  have hFR2 : IsFractionRing (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ := isFractionRing_adjoin_simple t₁ htr1
  have hDA2 : DifferentialAlgebra (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ :=
    differentialAlgebra_adjoin_simple t₁ (C η₁' * X) hw1
  have hηa : ηa (K₁ := R⟮x₀⟯) (RingHom.id R) a = η₁' := by
    rw [ηa, Polynomial.map_id]
  have hD₂ : ∀ P : (R⟮x₀⟯)[X], P′ = implicitDeriv (C (ηa (K₁ := R⟮x₀⟯) (RingHom.id R) a) * X) P :=
    fun P ↦ by rw [hηa]; rfl
  have hM : ModelEW (K₁ := R⟮x₀⟯) (K₂ := (R⟮x₀⟯)⟮t₁⟯) (RingHom.id R) a :=
    ModelEW.of (RingHom.id R) hD ha hD₂
  -- values of codes in `F₀`
  have hvalP : ∀ q : GPoly (GFrac R), ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯
      (GPoly.toPoly (M₁In (K₁ := R⟮x₀⟯) (RingHom.id R) h0 hD) q) : (R⟮x₀⟯)⟮t₁⟯) : F₀) =
      valP x₀ t₁ q := fun q ↦ by
    rw [algebraMap_adjoinSimple, GPoly.toPoly_eq_sum_range _ q ([], [1])]
    simp only [valP, map_sum, map_mul, map_pow, aeval_C, aeval_X, sem_M₁In, hevc]
  have hsemG : ∀ q : GFrac (GFrac R),
      (((hM.cf (RingHom.id R) h0).sem q : (R⟮x₀⟯)⟮t₁⟯) : F₀) = valG x₀ t₁ q := fun q ↦ by
    rw [ModelEW.cf, sem_M₂E, IntermediateField.coe_div, hvalP, hvalP, valG]
  obtain ⟨hden, hsem⟩ := subSmulCodeE_spec (K₂ := (R⟮x₀⟯)⟮t₁⟯) (RingHom.id R) h0 hD hD₂ ρ W c
  refine ⟨Bool.eq_false_iff.mpr fun hz ↦ hden ((GPoly.isZero_iff _ _).mp hz), ?_⟩
  have := congrArg (fun z : (R⟮x₀⟯)⟮t₁⟯ ↦ (z : F₀)) hsem
  have hcF : ((algebraMap (R⟮x₀⟯)[X] (R⟮x₀⟯)⟮t₁⟯ (C (algebraMap R[X] R⟮x₀⟯ (C (RingHom.id R c)))) :
      (R⟮x₀⟯)⟮t₁⟯) : F₀) = algebraMap R F₀ c := by
    rw [algebraMap_adjoinSimple, aeval_C]
    change ((algebraMap R[X] R⟮x₀⟯ (C c) : R⟮x₀⟯) : F₀) = _
    rw [hcoe, aeval_C]
  simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hcF] at this
  rw [ModelEW.cf] at hsemG
  simp only [hsemG] at this
  exact this

end F0

section Decide

variable {R : Type*} [Field R] [DecidableEq R]

/-- The level-`0` decision under a non-elementary primitive over an exponential. -/
def integrateLiExpBase (a₁ : CPoly R) (W ρ : GFrac (GFrac R)) : Bool :=
  match nestedConstE a₁ ρ W with
  | none => false
  | some c => integrateExp a₁ (subSmulCodeE a₁ ρ W c).1 (subSmulCodeE a₁ ρ W c).2

end Decide

end Tower

namespace CPoly

open Differential

universe u

variable {R F₀ : Type*} {K : Type u} [Field R] [DecidableEq R] [CharZero R] [Field F₀] [Field K]
variable [Algebra R F₀] [Algebra F₀ K] [Algebra R K] [IsScalarTower R F₀ K]
variable [Differential F₀] [Differential K] [DifferentialAlgebra F₀ K] [CharZero K]


/-- **Positive direction of the height-two integrator in any larger field.** -/
theorem hasElementaryIntegral_valG_of_integrateExp (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
    (x₀ t₁ : F₀) (hx₀ : x₀′ = 1) (a₁ : CPoly R) (ha₁ : trim (deriv a₁) ≠ [])
    (ht₁0 : t₁ ≠ 0) (ht₁ : t₁′ = aeval x₀ (derivative (toPoly a₁)) * t₁)
    (Gn Gd : GPoly (GFrac R)) (hGd : GPoly.isZero (Tower.ops₁g R) Gd = false)
    (hint : Tower.integrateExp a₁ Gn Gd = true) :
    HasElementaryIntegral (algebraMap F₀ K (Tower.valG x₀ t₁ (Gn, Gd))) := by
  classical
  obtain ⟨hid, hsqc, hXs, hlen, hBn⟩ := Tower.hermite_valG_exp_F₀ hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ Gn Gd
    hGd
  obtain ⟨hadd, hmul, hmono, hne0, hsq0⟩ := Tower.valP_ring_exp hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁
  simp only [Tower.integrateExp] at hint
  generalize GPoly.expSplit (Tower.ops₁g R) Gn Gd = sp at hid hsqc hXs hlen hBn hint
  generalize GPoly.hermite (Tower.ops₁g R) (Tower.expW a₁) sp.1 sp.2.2.2 = h
    at hid hsqc hXs hlen hBn hint
  generalize GPoly.divMod (Tower.ops₁g R) h.b h.s = qr at hid hlen hBn hint
  set k := sp.2.2.1 with hk
  set Λ := GPoly.add (Tower.ops₁g R)
    (GPoly.mul (Tower.ops₁g R) qr.1 (GPoly.monomial (Tower.ops₁g R) k (Tower.ops₁g R).one))
    sp.2.1 with hΛ
  set N := Λ.length + k + 1 with hN
  rw [hid, map_add, ← deriv_algebraMap, hasElementaryIntegral_deriv_add_iff, map_add]
  have hS0 : Tower.valP x₀ t₁ h.s ≠ 0 := hsq0 _ hsqc
  have htk : t₁ ^ k ≠ 0 := pow_ne_zero _ ht₁0
  set Lp : K := algebraMap F₀ K (Tower.valP x₀ t₁ Λ / t₁ ^ k) with hLp
  set Rp : K := algebraMap F₀ K (Tower.valP x₀ t₁ qr.2 / Tower.valP x₀ t₁ h.s) with hRp
  have hBnval : Tower.valP x₀ t₁ (GPoly.add (Tower.ops₁g R) (GPoly.mul (Tower.ops₁g R) Λ h.s)
      (GPoly.mul (Tower.ops₁g R) qr.2 (GPoly.monomial (Tower.ops₁g R) k (Tower.ops₁g R).one))) /
      (Tower.valP x₀ t₁ h.s * t₁ ^ k) =
      Tower.valP x₀ t₁ Λ / t₁ ^ k + Tower.valP x₀ t₁ qr.2 / Tower.valP x₀ t₁ h.s := by
    rw [hadd, hmul, hmul, hmono]
    field_simp
  have hLform : Lp = algebraMap F₀ K (aeval x₀ (toPoly (Tower.polyA Λ k)) /
      aeval x₀ (toPoly (Tower.polyD Λ k)) + ∑ j ∈ (Finset.range N).erase k,
        aeval x₀ (toPoly (Tower.polyA Λ j)) / aeval x₀ (toPoly (Tower.polyD Λ j)) * t₁ ^ j /
          t₁ ^ k) := by
    rw [hLp, valP_div_pow_eq x₀ t₁ ht₁0 Λ k]
  have hIn : GPoly.residueCheck (Tower.ops₁g R) (Tower.expW a₁) qr.2 h.s = true →
      HasElementaryIntegralIn Rp := fun hres ↦
    hasElementaryIntegralIn_expExpBaseResidue (K := K) hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ qr.2 h.s hsqc
      hXs hlen hres
  -- the Laurent part, positively
  have hRK : ∀ r : R, (algebraMap R K r)′ = 0 := fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R F₀ K, deriv_algebraMap, hR, map_zero]
  let _ : Differential R := ⟨0⟩
  have h0 : ∀ r : R, r′ = 0 := fun _ ↦ rfl
  have hDAR : DifferentialAlgebra R K := ⟨fun r ↦ by rw [hRK, h0, map_zero]⟩
  have haevx : ∀ P : R[X], aeval (algebraMap F₀ K x₀) P = algebraMap F₀ K (aeval x₀ P) :=
    fun P ↦ aeval_algebraMap_apply K x₀ P
  have hx' : (algebraMap F₀ K x₀)′ = 1 := by rw [deriv_algebraMap, hx₀, map_one]
  have ht₁' : (algebraMap F₀ K t₁)′ =
      aeval (algebraMap F₀ K x₀) (derivative (toPoly a₁)) * algebraMap F₀ K t₁ := by
    rw [deriv_algebraMap, ht₁, map_mul, haevx]
  have ht₁K : algebraMap F₀ K t₁ ≠ 0 := (_root_.map_ne_zero _).mpr ht₁0
  have hall := hint
  rw [Bool.and_eq_true, List.all_eq_true] at hall
  obtain ⟨hres, hall⟩ := hall
  have hsome : ∀ j < N, j ≠ k →
      (rdeRational (expCoeffZ a₁ ((j : ℤ) - k)) (Tower.polyA Λ j) (Tower.polyD Λ j)).isSome =
        true := fun j hj hjk ↦ by
    have := hall j (List.mem_range.mpr hj)
    rw [Bool.or_eq_true, decide_eq_true_eq] at this
    exact this.resolve_left hjk
  have hYG : ∀ j, ∃ Y G : CPoly R, j < N → j ≠ k →
      rdeRational (expCoeffZ a₁ ((j : ℤ) - k)) (Tower.polyA Λ j) (Tower.polyD Λ j) =
        some (Y, G) := fun j ↦ by
    by_cases hc : j < N ∧ j ≠ k
    · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hsome j hc.1 hc.2)
      exact ⟨p.1, p.2, fun _ _ ↦ hp⟩
    · exact ⟨[], [], fun h1 h2 ↦ absurd ⟨h1, h2⟩ hc⟩
  choose Y G hYG using hYG
  have hL := hasElementaryIntegral_expLaurentRat h0 (algebraMap F₀ K x₀) (algebraMap F₀ K t₁)
    hx' ht₁K a₁ ht₁' N k (Tower.polyA Λ) (Tower.polyD Λ) Y G (Tower.polyA Λ k)
    (Tower.polyD Λ k) (Tower.normFrac_den_ne_zero _) (fun j _ ↦ Tower.normFrac_den_ne_zero _)
    hYG
  have hL' : HasElementaryIntegral Lp := by
    rw [hLform]
    simpa only [map_add, map_sum, map_mul, map_pow, map_div₀, haevx] using hL
  exact hL'.add_in (hIn hres)

/-- **Level `0` under a non-elementary primitive over an exponential: decided.** -/
theorem integrateLiExpBase_decides (hR : ∀ r : R, (algebraMap R F₀ r)′ = 0)
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
    (ρ : GFrac (GFrac R)) (hρ0 : GPoly.isZero (Tower.ops₁g R) ρ.2 = false) :
    HasElementaryIntegral (algebraMap F₀ K (Tower.valG x₀ t₁ ρ)) ↔
      Tower.integrateLiExpBase a₁ W ρ = true := by
  classical
  have hsplit : ∀ c : R, algebraMap F₀ K (Tower.valG x₀ t₁ ρ) =
      (algebraMap F₀ K (algebraMap R F₀ c) * t)′ +
        algebraMap F₀ K (Tower.valG x₀ t₁ (Tower.subSmulCodeE a₁ ρ W c)) := fun c ↦ by
    obtain ⟨-, hval⟩ := Tower.valG_subSmulCodeE_F₀ hR x₀ t₁ hx₀ ha₁ ht₁0 ht₁ ρ W c
    rw [Derivation.leibniz, deriv_algebraMap, hR, map_zero, ht, hval]
    simp only [smul_eq_mul, mul_zero, add_zero, map_sub, map_mul]
    ring
  unfold Tower.integrateLiExpBase
  constructor
  · intro hf
    obtain ⟨E, _, _, _, _, hE, g, hg⟩ := hf
    obtain ⟨c, hc⟩ := liExpBase_const hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ hgen₀ W t hgen ht hW0 hWnd
      hresW ρ hρ0 E hE g hg
    rw [hc]
    simp only
    have hf : HasElementaryIntegral (algebraMap F₀ K (Tower.valG x₀ t₁ ρ)) :=
      ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, hE, g, hg⟩
    have hf' : HasElementaryIntegral
        (algebraMap F₀ K (Tower.valG x₀ t₁ (Tower.subSmulCodeE a₁ ρ W c))) := by
      have h1 := hf
      rw [hsplit c] at h1
      exact (hasElementaryIntegral_deriv_add_iff _ _).mp h1
    obtain ⟨hden, -⟩ := Tower.valG_subSmulCodeE_F₀ hR x₀ t₁ hx₀ ha₁ ht₁0 ht₁ ρ W c
    set ρ' := Tower.subSmulCodeE a₁ ρ W c with hρ'
    have hGd : GPoly.isZero (Tower.ops₁g R) ρ'.2 = false := hden
    obtain ⟨hid, hsqc, hXs, hlen, hBn⟩ := Tower.hermite_valG_exp_F₀ hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁
      ρ'.1 ρ'.2 hGd
    obtain ⟨hadd, hmul, hmono, hne0, hsq0⟩ := Tower.valP_ring_exp hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁
    rw [Prod.mk.eta] at hid
    simp only [Tower.integrateExp]
    generalize GPoly.expSplit (Tower.ops₁g R) ρ'.1 ρ'.2 = sp at hid hsqc hXs hlen hBn ⊢
    generalize GPoly.hermite (Tower.ops₁g R) (Tower.expW a₁) sp.1 sp.2.2.2 = h
      at hid hsqc hXs hlen hBn ⊢
    generalize GPoly.divMod (Tower.ops₁g R) h.b h.s = qr at hid hlen hBn ⊢
    set k := sp.2.2.1 with hk
    set Λ := GPoly.add (Tower.ops₁g R)
      (GPoly.mul (Tower.ops₁g R) qr.1 (GPoly.monomial (Tower.ops₁g R) k (Tower.ops₁g R).one))
      sp.2.1 with hΛ
    set N := Λ.length + k + 1 with hN
    have hS0 : Tower.valP x₀ t₁ h.s ≠ 0 := hsq0 _ hsqc
    have htk : t₁ ^ k ≠ 0 := pow_ne_zero _ ht₁0
    set Lp : K := algebraMap F₀ K (Tower.valP x₀ t₁ Λ / t₁ ^ k) with hLp
    set Rp : K := algebraMap F₀ K (Tower.valP x₀ t₁ qr.2 / Tower.valP x₀ t₁ h.s) with hRp
    have hBnval : Tower.valP x₀ t₁ (GPoly.add (Tower.ops₁g R) (GPoly.mul (Tower.ops₁g R) Λ h.s)
        (GPoly.mul (Tower.ops₁g R) qr.2 (GPoly.monomial (Tower.ops₁g R) k (Tower.ops₁g R).one))) /
        (Tower.valP x₀ t₁ h.s * t₁ ^ k) =
        Tower.valP x₀ t₁ Λ / t₁ ^ k + Tower.valP x₀ t₁ qr.2 / Tower.valP x₀ t₁ h.s := by
      rw [hadd, hmul, hmul, hmono]
      field_simp
    have hLform : Lp = algebraMap F₀ K (aeval x₀ (toPoly (Tower.polyA Λ k)) /
        aeval x₀ (toPoly (Tower.polyD Λ k)) + ∑ j ∈ (Finset.range N).erase k,
          aeval x₀ (toPoly (Tower.polyA Λ j)) / aeval x₀ (toPoly (Tower.polyD Λ j)) * t₁ ^ j /
            t₁ ^ k) := by
      rw [hLp, valP_div_pow_eq x₀ t₁ ht₁0 Λ k]
    have hIn : GPoly.residueCheck (Tower.ops₁g R) (Tower.expW a₁) qr.2 h.s = true →
        HasElementaryIntegralIn Rp := fun hres ↦
      hasElementaryIntegralIn_expExpBaseResidue (K := K) hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ qr.2 h.s
        hsqc hXs hlen hres
    have hres : GPoly.residueCheck (Tower.ops₁g R) (Tower.expW a₁) qr.2 h.s = true := by
      by_contra hcon
      rw [Bool.not_eq_true] at hcon
      refine not_elementary_liExpBaseResidue hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ hgen₀ W t hgen ht
        hW0 hWnd hresW ρ hρ0 c hc h.gn h.gd _ qr.2 h.s k hsqc hXs hBn hcon E hE g ?_ hg
      rw [hBnval, ← hρ', hid]
    have hf'' : HasElementaryIntegral (algebraMap F₀ K (Tower.valG x₀ t₁ (ρ'.1, ρ'.2))) := by
      rw [Prod.mk.eta]; exact hf'
    rw [hid, map_add, ← deriv_algebraMap, hasElementaryIntegral_deriv_add_iff, map_add] at hf''
    have hL : HasElementaryIntegral Lp := by
      have := hf''.sub_in (hIn hres)
      rwa [add_sub_cancel_right] at this
    rw [Bool.and_eq_true, List.all_eq_true]
    refine ⟨hres, fun j hj ↦ ?_⟩
    rw [List.mem_range] at hj
    rw [Bool.or_eq_true, decide_eq_true_eq]
    by_cases hjk : j = k
    · exact Or.inl hjk
    right
    by_contra hnone
    rw [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hnone
    obtain ⟨E', _, _, _, _, hE', g', hg'⟩ := hL
    rw [hLform] at hg'
    exact not_elementary_liExpBaseLaurent hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁ hgen₀ W t hgen ht hW0
      hWnd hresW N k (Tower.polyA Λ) (Tower.polyD Λ) (Tower.polyA Λ k) (Tower.polyD Λ k)
      (fun j _ ↦ Tower.normFrac_den_ne_zero _) j hj hjk hnone E' hE' g' hg'
  · intro h
    cases hc : Tower.nestedConstE a₁ ρ W with
    | none => rw [hc] at h; exact absurd h (by simp)
    | some c =>
      rw [hc] at h
      simp only at h
      obtain ⟨hden, -⟩ := Tower.valG_subSmulCodeE_F₀ hR x₀ t₁ hx₀ ha₁ ht₁0 ht₁ ρ W c
      rw [hsplit c, hasElementaryIntegral_deriv_add_iff]
      have := hasElementaryIntegral_valG_of_integrateExp (K := K) hR x₀ t₁ hx₀ a₁ ha₁ ht₁0 ht₁
        _ _ hden h
      rwa [Prod.mk.eta] at this

end CPoly
