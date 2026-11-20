import RischTragerBronstein.Computable.RDENonCancelExp
import RischTragerBronstein.Computable.DerivExpSol
import RischTragerBronstein.RDE.HomogeneousPolyPart

/-!
# The special-denominator bound at `t₁ = exp a₁` for a polynomial coefficient

`y′ + g y = A / (t₁^m D₁)` with `g ∈ R(x)[t₁]` of positive degree and constant term `g₀ = n / d`.
A pole of `y` at `t₁` of order `r > m` needs `e′ + (g₀ - r a₁′) e = 0` to have a non-zero solution
in `R(x)`, hence (`no_rde_homogeneous_of_polyPart`) the polynomial part `Q` of `g₀` must equal
`r a₁′`. Comparing leading coefficients, `r = lc Q / lc a₁′` — recognised as a natural number by
`HasNatTest` (a constant field in which integers are recognisable, e.g. `ℚ`). The bound is
`n₀ = max m r`, and `Tower.rdeNCExpB` solves with denominator `t₁^{n₀} D₁`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

/-- A field in which natural numbers are recognisable. -/
class HasNatTest (R : Type*) [Field R] where
  /-- `natTest x = some n` iff `x = n` -/
  natTest : R → Option ℕ
  natTest_spec : ∀ (x : R) (n : ℕ), natTest x = some n ↔ x = n

instance : HasNatTest ℚ where
  natTest x := if x.den = 1 ∧ 0 ≤ x.num then some x.num.toNat else none
  natTest_spec x n := by
    constructor
    · intro h
      split_ifs at h with hx
      · have hn : x.num.toNat = n := Option.some.inj h
        have hx' : (x.num : ℚ) = x := (Rat.den_eq_one_iff x).mp hx.1
        rw [← hx', ← hn]
        have : ((x.num.toNat : ℤ) : ℚ) = (x.num : ℚ) := by rw [Int.toNat_of_nonneg hx.2]
        rw [← this]
        push_cast
        rfl
    · rintro rfl
      simp

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R] [HasNatTest R]

/-- The bound on the pole order at `t₁`: `max m r` where `r a₁′` could be the polynomial part of
`g₀`. -/
def specialBound (a₁ : CPoly R) (g₀ : GFrac R) (m : ℕ) : ℕ :=
  let Q := CPoly.trim (CPoly.divMod g₀.1 g₀.2).1
  let η := CPoly.trim (CPoly.deriv a₁)
  if Q.length = η.length ∧ Q ≠ [] then
    match HasNatTest.natTest (CPoly.lead Q / CPoly.lead η) with
    | some r => max m r
    | none => m
  else m

/-- **The non-cancellation solver over `R(x)(exp a₁)` with the special-denominator bound**:
`y = Y / (t₁^{n₀} D₁)`, `n₀ = specialBound a₁ g₀ m`. -/
def rdeNCExpB (a₁ : CPoly R) (g A D : GPoly (GFrac R)) : Option (GPoly (GFrac R)) :=
  let sp := GPoly.splitX (ops₁g R) D
  let n₀ := specialBound a₁ (normFrac (GPoly.coeffAt (ops₁g R) g 0)) sp.1
  GPoly.rdeNC (ops₁g R) (expW a₁) (GPoly.sub (ops₁g R) g (mEta a₁ n₀))
    (GPoly.mul (ops₁g R) A (GPoly.monomial (ops₁g R) (n₀ - sp.1) (ops₁g R).one)) sp.2

lemma le_specialBound (a₁ : CPoly R) (g₀ : GFrac R) (m : ℕ) : m ≤ specialBound a₁ g₀ m := by
  unfold specialBound
  dsimp only
  split_ifs
  · split
    · exact le_max_left _ _
    · exact le_rfl
  · exact le_rfl

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [HasNatTest R] [Field S]
variable [DecidableEq S]
variable [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂
local notation "𝓜₁" => M₁In (K₁ := K₁) ι h0 hD

include h0 hD

/-- No cancellation above the bound: `e′ + (g₀ - r a₁′) e = 0` has no non-zero solution for
`r > specialBound a₁ g₀ m`. -/
theorem specialBound_spec (a₁ : CPoly R) (ha₁ : CPoly.trim (CPoly.deriv a₁) ≠ [])
    (g₀ : GFrac R) (hd : CPoly.toPoly g₀.2 ≠ 0) (m : ℕ) (r : ℕ)
    (hr : specialBound a₁ g₀ m < r) (e : K₁) (he : e ≠ 0) :
    e′ + (CPoly.ev K₁ ι g₀ - r * ηa ι a₁) * e ≠ 0 := by
  have hdm := CPoly.divMod_spec g₀.1 g₀.2
  have hdl := CPoly.divMod_degree_lt g₀.1 g₀.2 hd
  set Q := (CPoly.divMod g₀.1 g₀.2).1 with hQ
  set rem := (CPoly.divMod g₀.1 g₀.2).2 with hrem
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K₁
  have hφd : φ ((CPoly.toPoly g₀.2).map ι) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hd)
  have hη0 : CPoly.toPoly (CPoly.deriv a₁) ≠ 0 := fun h ↦ ha₁ ((CPoly.trim_eq_nil_iff _).mpr h)
  -- the polynomial part `Q - r a₁′` is non-zero
  have hP : (CPoly.toPoly Q).map ι - C (r : S) * (derivative (CPoly.toPoly a₁)).map ι ≠ 0 := by
    intro hP0
    have hQr : (CPoly.toPoly Q).map ι = C (r : S) * (CPoly.toPoly (CPoly.deriv a₁)).map ι := by
      rw [CPoly.toPoly_deriv]; exact sub_eq_zero.mp hP0
    have hr0 : (r : S) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hηS : (CPoly.toPoly (CPoly.deriv a₁)).map ι ≠ 0 :=
      (Polynomial.map_ne_zero_iff ι.injective).mpr hη0
    have hQ0 : CPoly.toPoly Q ≠ 0 := fun h ↦ by
      rw [h, Polynomial.map_zero] at hQr
      exact mul_ne_zero (C_ne_zero.mpr hr0) hηS hQr.symm
    have htQ : CPoly.trim Q ≠ [] := fun h ↦ hQ0 ((CPoly.trim_eq_nil_iff _).mp h)
    obtain ⟨hdQ, hlQ, hlQ0⟩ := CPoly.natDegree_toPoly_of_trim_ne_nil htQ
    obtain ⟨hdη, hlη, hlη0⟩ := CPoly.natDegree_toPoly_of_trim_ne_nil ha₁
    have hdegeq : (CPoly.toPoly Q).natDegree = (CPoly.toPoly (CPoly.deriv a₁)).natDegree := by
      have := congrArg natDegree hQr
      rwa [natDegree_map, natDegree_mul (C_ne_zero.mpr hr0) hηS, natDegree_C, zero_add,
        natDegree_map] at this
    have hlen : (CPoly.trim Q).length = (CPoly.trim (CPoly.deriv a₁)).length := by
      have h1 := List.length_pos_of_ne_nil htQ
      have h2 := List.length_pos_of_ne_nil ha₁
      omega
    have hlc : ι (CPoly.lead (CPoly.trim Q)) = r * ι (CPoly.lead (CPoly.trim (CPoly.deriv a₁))) := by
      have := congrArg leadingCoeff hQr
      rw [leadingCoeff_map, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_map,
        CPoly.leadingCoeff_toPoly hQ0, CPoly.leadingCoeff_toPoly hη0] at this
      exact this
    have hquot : CPoly.lead (CPoly.trim Q) / CPoly.lead (CPoly.trim (CPoly.deriv a₁)) = (r : R) := by
      apply ι.injective
      rw [map_div₀, hlc, map_natCast]
      have : ι (CPoly.lead (CPoly.trim (CPoly.deriv a₁))) ≠ 0 := (map_ne_zero ι).mpr hlη0
      field_simp
    have hnat : HasNatTest.natTest (CPoly.lead (CPoly.trim Q) /
        CPoly.lead (CPoly.trim (CPoly.deriv a₁))) = some r := (HasNatTest.natTest_spec _ _).mpr hquot
    have : specialBound a₁ g₀ m = max m r := by
      simp only [specialBound, ← hQ, if_pos (And.intro hlen htQ), hnat]
    rw [this] at hr
    omega
  -- the coefficient `g₀ - r a₁′` in the form `P + rem / d`
  have hform : CPoly.ev K₁ ι g₀ - r * ηa ι a₁ =
      φ ((CPoly.toPoly Q).map ι - C (r : S) * (derivative (CPoly.toPoly a₁)).map ι) +
        φ ((CPoly.toPoly rem).map ι) / φ ((CPoly.toPoly g₀.2).map ι) := by
    rw [CPoly.ev, hdm, ηa]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, map_add, map_mul,
      map_sub, map_C, map_natCast]
    field_simp
    ring
  rw [hform]
  refine no_rde_homogeneous_of_polyPart (K := K₁) hD _ _ _ hP
    ((Polynomial.map_ne_zero_iff ι.injective).mpr hd) ?_ e he
  by_cases hrem : CPoly.toPoly rem = 0
  · right; rw [hrem, Polynomial.map_zero]
  · left
    rw [natDegree_map, natDegree_map]
    exact natDegree_lt_natDegree hrem hdl

/-- **Soundness.** -/
theorem rdeNCExpB_sound (a₁ : CPoly R)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a₁) * X) P)
    (g A D : GPoly (GFrac R)) (hD0 : GPoly.toPoly 𝓜₁ D ≠ 0) {Y : GPoly (GFrac R)}
    (h : rdeNCExpB a₁ g A D = some Y) :
    (φ₂ (GPoly.toPoly 𝓜₁ Y) / (φ₂ X ^ specialBound a₁ (normFrac (GPoly.coeffAt (ops₁g R) g 0))
        (GPoly.splitX (ops₁g R) D).1 * φ₂ (GPoly.toPoly 𝓜₁ (GPoly.splitX (ops₁g R) D).2)))′ +
      φ₂ (GPoly.toPoly 𝓜₁ g) * (φ₂ (GPoly.toPoly 𝓜₁ Y) /
        (φ₂ X ^ specialBound a₁ (normFrac (GPoly.coeffAt (ops₁g R) g 0))
          (GPoly.splitX (ops₁g R) D).1 * φ₂ (GPoly.toPoly 𝓜₁ (GPoly.splitX (ops₁g R) D).2))) =
      φ₂ (GPoly.toPoly 𝓜₁ A) / φ₂ (GPoly.toPoly 𝓜₁ D) := by
  have hinj : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly 𝓜₁ (expW a₁)) P := fun P ↦ by
    rw [toPoly_expW_In]; exact hD₂ P
  have hsp := GPoly.toPoly_splitX 𝓜₁ D
  simp only [rdeNCExpB] at h
  generalize GPoly.splitX (ops₁g R) D = sp at h hsp ⊢
  have hge := le_specialBound a₁ (normFrac (GPoly.coeffAt (ops₁g R) g 0)) sp.1
  generalize specialBound a₁ (normFrac (GPoly.coeffAt (ops₁g R) g 0)) sp.1 = n₀ at h hge ⊢
  have hD₁0 : GPoly.toPoly 𝓜₁ sp.2 ≠ 0 := fun h0' ↦ hD0 (by rw [hsp, h0', mul_zero])
  have hs := GPoly.rdeNC_sound 𝓜₁ (expW a₁) _ _ sp.2 hDW h
  rw [GPoly.toPoly_sub, toPoly_mEta, GPoly.toPoly_mul, toPoly_monomial_one ι h0 hD] at hs
  have hφD₁ : φ₂ (GPoly.toPoly 𝓜₁ sp.2) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hD₁0
  have hX0 : φ₂ (X : K₁[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  have hXn : (φ₂ (X : K₁[X]) ^ n₀)′ = φ₂ (C ((n₀ : K₁) * ηa ι a₁)) * φ₂ X ^ n₀ := by
    rw [← map_pow, deriv_algebraMap, hD₂, deriv_X_pow, map_mul, map_pow]
  have := congrArg φ₂ hs
  simp only [map_add, map_mul, map_sub, map_pow] at this
  rw [hsp, map_mul, map_pow, Derivation.leibniz_div, Derivation.leibniz, hXn, deriv_algebraMap,
    deriv_algebraMap]
  simp only [smul_eq_mul]
  have hCm : φ₂ (C ((n₀ : K₁) * ηa ι a₁)) = φ₂ (C (n₀ : K₁)) * φ₂ (C (ηa ι a₁)) := by
    rw [C_mul, map_mul]
  rw [hCm]
  have hpow : φ₂ (X : K₁[X]) ^ n₀ = φ₂ X ^ (n₀ - sp.1) * φ₂ X ^ sp.1 := by
    rw [← pow_add, Nat.sub_add_cancel hge]
  rw [hpow]
  field_simp
  linear_combination this

/-- **Completeness.** -/
theorem rdeNCExpB_complete (a₁ : CPoly R) (ha₁ : CPoly.trim (CPoly.deriv a₁) ≠ [])
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηa ι a₁) * X) P)
    (hconst : ∀ (P : K₁[X]) (n : ℕ), P′ * X ^ n = P * (X ^ n)′ → ∃ e : K₁, P = C e * X ^ n)
    (g A D : GPoly (GFrac R)) (hg : 1 ≤ (GPoly.toPoly 𝓜₁ g).natDegree)
    (hD0 : GPoly.toPoly 𝓜₁ D ≠ 0) (y : K₂)
    (hy : y′ + φ₂ (GPoly.toPoly 𝓜₁ g) * y =
      φ₂ (GPoly.toPoly 𝓜₁ A) / φ₂ (GPoly.toPoly 𝓜₁ D)) :
    (rdeNCExpB a₁ g A D).isSome = true := by
  have hinj : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly 𝓜₁ (expW a₁)) P := fun P ↦ by
    rw [toPoly_expW_In]; exact hD₂ P
  have hnorm' := normal_of_hconst (ηa ι a₁) hD₂ hconst
  have hder : ∀ P : K₁[X], (P′).natDegree ≤ P.natDegree := fun P ↦ by
    rw [hD₂]; exact natDegree_implicitDeriv_C_mul_X_le _ P
  have hsp := GPoly.toPoly_splitX 𝓜₁ D
  have hXD₁ := GPoly.not_X_dvd_splitX 𝓜₁ D hD0
  simp only [rdeNCExpB]
  generalize GPoly.splitX (ops₁g R) D = sp at hsp hXD₁
  set g₀ := normFrac (GPoly.coeffAt (ops₁g R) g 0) with hg₀def
  have hge := le_specialBound a₁ g₀ sp.1
  have hg₀ev : CPoly.ev K₁ ι g₀ = (GPoly.toPoly 𝓜₁ g).coeff 0 := by
    rw [hg₀def, ev_normFrac, ← sem_M₁In, GPoly.sem_coeffAt]
  have hspec := specialBound_spec (K₁ := K₁) ι h0 hD a₁ ha₁ g₀ (normFrac_den_ne_zero _) sp.1
  generalize specialBound a₁ g₀ sp.1 = n₀ at hge hspec ⊢
  have hD₁0 : GPoly.toPoly 𝓜₁ sp.2 ≠ 0 := fun h0' ↦ hD0 (by rw [hsp, h0', mul_zero])
  have hX0 : φ₂ (X : K₁[X]) ≠ 0 := (map_ne_zero_iff _ hinj).mpr X_ne_zero
  have hy' : y′ + φ₂ (GPoly.toPoly 𝓜₁ g) * y =
      φ₂ (GPoly.toPoly 𝓜₁ A * X ^ (n₀ - sp.1)) / (φ₂ X ^ n₀ * φ₂ (GPoly.toPoly 𝓜₁ sp.2)) := by
    rw [hy, hsp, map_mul, map_pow, map_mul, map_pow]
    have hpow : φ₂ (X : K₁[X]) ^ n₀ = φ₂ X ^ (n₀ - sp.1) * φ₂ X ^ sp.1 := by
      rw [← pow_add, Nat.sub_add_cancel hge]
    rw [hpow]
    have := (map_ne_zero_iff _ hinj).mpr hD₁0
    field_simp
  obtain ⟨Y, -, hYode⟩ := rde_denominator_exp_poly (K := K₂) (ηa ι a₁) hD₂ hnorm' _ n₀
    (fun r hr e he ↦ by rw [← hg₀ev]; exact hspec r hr e he) _ _ hXD₁ y hy'
  have hg' : 1 ≤ (GPoly.toPoly 𝓜₁ (GPoly.sub (ops₁g R) g (mEta a₁ n₀))).natDegree := by
    rw [GPoly.toPoly_sub, toPoly_mEta, natDegree_sub_C]; exact hg
  have hg'0 : GPoly.toPoly 𝓜₁ (GPoly.sub (ops₁g R) g (mEta a₁ n₀)) ≠ 0 := fun h0' ↦ by
    rw [h0', natDegree_zero] at hg'; omega
  obtain ⟨Y', hY'⟩ := GPoly.rdeNC_complete 𝓜₁ (expW a₁) (GPoly.sub (ops₁g R) g (mEta a₁ n₀))
    (GPoly.mul (ops₁g R) A (GPoly.monomial (ops₁g R) (n₀ - sp.1) (ops₁g R).one)) sp.2 hDW hder
    hg' hg'0 hD₁0 Y (by
    rw [GPoly.toPoly_sub, toPoly_mEta, GPoly.toPoly_mul, toPoly_monomial_one ι h0 hD]
    exact hYode)
  rw [hY']
  rfl

end Tower
