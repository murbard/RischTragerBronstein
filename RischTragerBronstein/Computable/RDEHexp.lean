import RischTragerBronstein.Computable.RDEExp
import RischTragerBronstein.Computable.RDEPrimW
import RischTragerBronstein.Computable.HexpBase
import RischTragerBronstein.Computable.HexpExpIndep

/-!
# The Risch differential equation `y′ + g y = A / (t₁^m D₁)` over `R(x)(t₁)`, `t₁′ = η t₁`

`η = Hn / Hd ∈ R(x)` arbitrary (certified monomial), `g ∈ R[x]` (typically `g = k b′` for
`t₂ = exp b`). As in `RDEExp.lean`, `y = Y / (t₁^m D₁)` with
`D₁ Y′ + ((g - m η) D₁ - D₁′) Y = A D₁`, and `Y` is found from the top: the coefficient of
`t₁^{δ+d}` is `L² (z′ + (g + (d - m - δ) η) z)`, `y_d = L z`. The coefficient `g + z η` has
simple poles: the top equation is solved by the weakly normalised solver `rdeTopCoeffW` with the
coefficient `hexpGq Hn Hd g z` and the annihilator `hexpMuZ μ z` of its residues.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R] [CPoly.HasRatRoots R] [HasNatTest R]

/-- The coefficient `g + z η` as a fraction (`(g, 1)` for `z = 0`). -/
def hexpGq (Hn Hd g : CPoly R) (z : ℤ) : GFrac R :=
  if z = 0 then (g, [1]) else (CPoly.add (CPoly.mul g Hd) (CPoly.smul (z : R) Hn), Hd)

/-- An annihilator of the residues of `g + z η`: `μ_z` (`X` for `z = 0`). -/
def hexpMuZ (μ : CPoly R) (z : ℤ) : CPoly R := if z = 0 then [0, 1] else CPoly.scaleMu (z : R) μ

/-- The exponent shift `d - m - δ` of the top coefficient (`d = dA - d₁`, `δ = d₁`). -/
def hexpZ (dA d₁ m : ℕ) : ℤ := ((dA - d₁ : ℕ) : ℤ) - m - d₁

/-- The top-degree recursion for `D Y′ + P₀ Y = Ap` in a hyperexponential extension. -/
def rdePolyHexpAux (Hn Hd μ g : CPoly R) (m : ℕ) (D P₀ : GPoly (GFrac R)) :
    ℕ → GPoly (GFrac R) → GPoly (GFrac R) → Option (GPoly (GFrac R))
  | 0, Ap, acc => if GPoly.isZero (ops₁g R) Ap then some acc else none
  | fuel + 1, Ap, acc =>
    if GPoly.isZero (ops₁g R) Ap then some acc
    else
      let dA := (GPoly.trim (ops₁g R) Ap).length - 1
      let d₁ := (GPoly.trim (ops₁g R) D).length - 1
      if dA < d₁ then none
      else
        match rdeTopCoeffW (hexpGq Hn Hd g (hexpZ dA d₁ m)) (hexpMuZ μ (hexpZ dA d₁ m))
            (GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) D))
            (GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) Ap)) with
        | none => none
        | some yd =>
          let Yd := GPoly.monomial (ops₁g R) (dA - d₁) yd
          rdePolyHexpAux Hn Hd μ g m D P₀ fuel
            (GPoly.sub (ops₁g R) Ap (GPoly.add (ops₁g R)
              (GPoly.mul (ops₁g R) D (GPoly.derivT (ops₁g R) (hexpW Hn Hd) Yd))
              (GPoly.mul (ops₁g R) P₀ Yd)))
            (GPoly.add (ops₁g R) acc Yd)

/-- `P₀ = (g - m η) D₁ - D₁′`. -/
def rdeP₀H (Hn Hd g : CPoly R) (m : ℕ) (D : GPoly (GFrac R)) : GPoly (GFrac R) :=
  GPoly.sub (ops₁g R) (GPoly.smul (ops₁g R) (hexpGq Hn Hd g (-(m : ℤ))) D)
    (GPoly.derivT (ops₁g R) (hexpW Hn Hd) D)

/-- Solve `y′ + g y = A / (t₁^m D₁)` over `R(x)(t₁)`; the solution is `Y / (t₁^m D₁)`. -/
def rdeHexp (Hn Hd μ g : CPoly R) (A D₁ : GPoly (GFrac R)) (m : ℕ) : Option (GPoly (GFrac R)) :=
  rdePolyHexpAux Hn Hd μ g m D₁ (rdeP₀H Hn Hd g m D₁) ((GPoly.mul (ops₁g R) A D₁).length + 1)
    (GPoly.mul (ops₁g R) A D₁) []

end Defs

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [CPoly.HasRatRoots R] [HasNatTest R]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

variable (ι : R →+* S) (h0 : ∀ s : S, s′ = 0) (hD : ∀ P : S[X], P′ = derivative P)
  (Hn Hd : CPoly R)

section Coeff

/-- The value of `hexpGq`: `g + z η`. -/
lemma ev_hexpGq (hHd0 : CPoly.toPoly Hd ≠ 0) (g : CPoly R) (z : ℤ) :
    CPoly.ev K₁ ι (hexpGq Hn Hd g z) = φ ((CPoly.toPoly g).map ι) + (z : K₁) * ηh ι Hn Hd := by
  have hφHd : φ ((CPoly.toPoly Hd).map ι) ≠ 0 := CPoly.map_toPoly_ne_zero ι hHd0
  unfold hexpGq
  split_ifs with hz
  · subst hz
    simp [CPoly.ev, CPoly.toPoly]
  · simp only [CPoly.ev, CPoly.toPoly_add, CPoly.toPoly_mul, CPoly.toPoly_smul, Polynomial.map_add,
      Polynomial.map_mul, map_C, map_add, map_mul, ηh]
    rw [map_intCast, map_intCast, map_intCast]
    field_simp

/-- The denominator of `hexpGq` is nonzero. -/
lemma hexpGq_den_ne_zero (hHd0 : CPoly.toPoly Hd ≠ 0) (g : CPoly R) (z : ℤ) :
    CPoly.toPoly (hexpGq Hn Hd g z).2 ≠ 0 := by
  unfold hexpGq
  split_ifs
  · simp [CPoly.toPoly]
  · exact hHd0

/-- The numerator and denominator of `hexpGq` are coprime. -/
lemma hexpGq_coprime (hcop : IsCoprime (CPoly.toPoly Hn) (CPoly.toPoly Hd)) (g : CPoly R) (z : ℤ) :
    IsCoprime (CPoly.toPoly (hexpGq Hn Hd g z).1) (CPoly.toPoly (hexpGq Hn Hd g z).2) := by
  unfold hexpGq
  split_ifs with hz
  · have h1 : CPoly.toPoly ([1] : CPoly R) = 1 := by simp [CPoly.toPoly]
    simp only [h1]
    exact isCoprime_one_right
  · simp only [CPoly.toPoly_add, CPoly.toPoly_mul, CPoly.toPoly_smul]
    have hz' : (z : R) ≠ 0 := Int.cast_ne_zero.mpr hz
    have hu : IsUnit (C (z : R) : R[X]) := isUnit_C.mpr hz'.isUnit
    have h1 : IsCoprime (C (z : R) * CPoly.toPoly Hn) (CPoly.toPoly Hd) :=
      (isCoprime_mul_unit_left_left hu _ _).mpr hcop
    have := h1.add_mul_left_left (CPoly.toPoly g)
    rwa [add_comm, mul_comm] at this

/-- The numerator of `hexpGq` is nonzero when the coefficient is not a logarithmic derivative. -/
lemma hexpGq_num_ne_zero (hHd0 : CPoly.toPoly Hd ≠ 0) (g : CPoly R) (z : ℤ)
    (hhom : ∀ e : K₁, e′ + (φ ((CPoly.toPoly g).map ι) + (z : K₁) * ηh ι Hn Hd) * e = 0 → e = 0) :
    CPoly.toPoly (hexpGq Hn Hd g z).1 ≠ 0 := by
  intro h0
  have hev := ev_hexpGq (K₁ := K₁) ι Hn Hd hHd0 g z
  rw [CPoly.ev, h0] at hev
  simp only [Polynomial.map_zero, map_zero, zero_div] at hev
  have := hhom 1 (by rw [← hev]; simp)
  exact one_ne_zero this

/-- `hexpMuZ` is nonzero. -/
lemma hexpMuZ_ne_zero {μ : CPoly R} (hμ0 : CPoly.toPoly μ ≠ 0) (z : ℤ) :
    CPoly.toPoly (hexpMuZ μ z) ≠ 0 := by
  unfold hexpMuZ
  split_ifs with hz
  · simp [CPoly.toPoly]
  · exact CPoly.scaleMu_ne_zero (Int.cast_ne_zero.mpr hz) hμ0

/-- `hexpMuZ μ z` annihilates the residues of `hexpGq Hn Hd g z`. -/
lemma hexpMuZ_annihilates (hHd0 : CPoly.toPoly Hd ≠ 0) {μ : CPoly R}
    (hμ : ∃ q : R[X], (CPoly.toPoly μ).comp (CPoly.toPoly (CPoly.residuePolyW Hn Hd)) =
      CPoly.toPoly (CPoly.simplePart Hd) * q) (g : CPoly R) (z : ℤ) :
    ∃ q : R[X], (CPoly.toPoly (hexpMuZ μ z)).comp
      (CPoly.toPoly (CPoly.residuePolyW (hexpGq Hn Hd g z).1 (hexpGq Hn Hd g z).2)) =
        CPoly.toPoly (CPoly.simplePart (hexpGq Hn Hd g z).2) * q := by
  unfold hexpMuZ hexpGq
  split_ifs with hz
  · -- the denominator is `1`: its simple part is a unit
    simp only
    have h1 : CPoly.toPoly ([1] : CPoly R) ≠ 0 := by simp [CPoly.toPoly]
    obtain ⟨S₀, G₁, G, q₁, q₂, σ, τ, σ', τ', E1, E2, E3, E4, E5, E6⟩ := CPoly.simplePart_data _ h1
    obtain ⟨-, hSd, -, -, -, -⟩ := Differential.simplePart_props h1 E1 E2 E3 E4 E5 E6
    have hunit : IsUnit (CPoly.toPoly (CPoly.simplePart ([1] : CPoly R))) := by
      have : CPoly.toPoly ([1] : CPoly R) = 1 := by simp [CPoly.toPoly]
      rw [this] at hSd
      exact isUnit_of_dvd_one hSd
    exact hunit.dvd
  · simp only
    refine CPoly.dvd_scaleMu_comp hμ ?_
    have h1 := CPoly.residuePolyW_add_mul g (CPoly.smul (z : R) Hn) Hd hHd0
    have h2 := CPoly.residuePolyW_smul Hn Hd hHd0 (z : R)
    have := dvd_add h1 h2
    rwa [sub_add_sub_cancel] at this

end Coeff

include hD in
lemma toPoly_derivT_hexpW (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P)
    (p : GPoly (GFrac R)) :
    GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) (GPoly.derivT (ops₁g R) (hexpW Hn Hd) p) =
      (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) p)′ := by
  rw [GPoly.toPoly_derivT, hD₂, toPoly_hexpW_In]

include h0 hD in
/-- **Soundness of the recursion**: the invariant `D acc′ + P₀ acc + Ap` is preserved. -/
theorem rdePolyHexpAux_sound (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P)
    (μ g : CPoly R) (m : ℕ) (D P₀ : GPoly (GFrac R)) (fuel : ℕ) (Ap acc Y : GPoly (GFrac R))
    (h : rdePolyHexpAux Hn Hd μ g m D P₀ fuel Ap acc = some Y) :
    let M₁ := M₁In (K₁ := K₁) ι h0 hD
    GPoly.toPoly M₁ D * (GPoly.toPoly M₁ Y)′ + GPoly.toPoly M₁ P₀ * GPoly.toPoly M₁ Y =
      GPoly.toPoly M₁ D * (GPoly.toPoly M₁ acc)′ + GPoly.toPoly M₁ P₀ * GPoly.toPoly M₁ acc +
        GPoly.toPoly M₁ Ap := by
  intro M₁
  induction fuel generalizing Ap acc with
  | zero =>
    simp only [rdePolyHexpAux] at h
    split_ifs at h with hz
    rw [Option.some.injEq] at h
    subst h
    rw [(GPoly.isZero_iff M₁ Ap).mp hz, add_zero]
  | succ fuel ih =>
    simp only [rdePolyHexpAux] at h
    split_ifs at h with hz hlt
    · rw [Option.some.injEq] at h
      subst h
      rw [(GPoly.isZero_iff M₁ Ap).mp hz, add_zero]
    · revert h
      cases rdeTopCoeffW (hexpGq Hn Hd g
            (hexpZ ((GPoly.trim (ops₁g R) Ap).length - 1) ((GPoly.trim (ops₁g R) D).length - 1) m))
          (hexpMuZ μ
            (hexpZ ((GPoly.trim (ops₁g R) Ap).length - 1) ((GPoly.trim (ops₁g R) D).length - 1) m))
          (GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) D))
          (GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) Ap)) with
      | none => intro h; exact absurd h (by simp)
      | some yd =>
        intro h
        simp only at h
        have := ih _ _ h
        rw [this]
        simp only [GPoly.toPoly_add, GPoly.toPoly_sub, GPoly.toPoly_mul, map_add]
        rw [toPoly_derivT_hexpW ι h0 hD Hn Hd hD₂]
        ring

include h0 hD in
/-- **Soundness of `rdeHexp`**: `y = Y / (t₁^m D₁)` solves `y′ + g y = A / (t₁^m D₁)`. -/
theorem rdeHexp_sound (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P)
    (hHd0 : CPoly.toPoly Hd ≠ 0) (μ g : CPoly R) (A D₁ : GPoly (GFrac R)) (m : ℕ)
    (hD0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D₁ ≠ 0) {Y : GPoly (GFrac R)}
    (h : rdeHexp Hn Hd μ g A D₁ m = some Y) :
    (φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Y) /
        (φ₂ X ^ m * φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D₁)))′ +
        φ₂ (C (φ ((CPoly.toPoly g).map ι))) *
          (φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Y) /
            (φ₂ X ^ m * φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D₁))) =
      φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) A) /
        (φ₂ X ^ m * φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D₁)) := by
  set M₁ := M₁In (K₁ := K₁) ι h0 hD with hM₁
  have hinv := rdePolyHexpAux_sound ι h0 hD Hn Hd hD₂ μ g m D₁ (rdeP₀H Hn Hd g m D₁) _ _ [] Y h
  simp only [GPoly.toPoly_nil, map_zero, mul_zero, zero_add, GPoly.toPoly_mul] at hinv
  set gK : K₁ := φ ((CPoly.toPoly g).map ι) with hgK
  have hP₀ : GPoly.toPoly M₁ (rdeP₀H Hn Hd g m D₁) =
      C (gK - m * ηh ι Hn Hd) * GPoly.toPoly M₁ D₁ - (GPoly.toPoly M₁ D₁)′ := by
    rw [rdeP₀H, GPoly.toPoly_sub, GPoly.toPoly_smul, toPoly_derivT_hexpW ι h0 hD Hn Hd hD₂, hM₁,
      sem_M₁In, ev_hexpGq ι Hn Hd hHd0]
    congr 3
    rw [Int.cast_neg, Int.cast_natCast, hgK]
    ring
  rw [hP₀] at hinv
  have hinj₂ : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hφD : φ₂ (GPoly.toPoly M₁ D₁) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr hD0
  have hX0 : φ₂ (X : K₁[X]) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr X_ne_zero
  have hXm0 : φ₂ (X : K₁[X]) ^ m ≠ 0 := pow_ne_zero _ hX0
  have hXm' : (φ₂ (X : K₁[X]) ^ m)′ = φ₂ (C (m * ηh ι Hn Hd)) * φ₂ X ^ m := by
    rw [← map_pow, deriv_algebraMap, hD₂, deriv_X_pow, map_mul, map_pow]
  have h2 := congrArg φ₂ hinv
  simp only [map_add, map_mul, map_sub, ← deriv_algebraMap] at h2
  set W : K₂ := φ₂ X ^ m * φ₂ (GPoly.toPoly M₁ D₁) with hW
  have hW0 : W ≠ 0 := mul_ne_zero hXm0 hφD
  have hW' : W′ = φ₂ (C (m : K₁)) * φ₂ (C (ηh ι Hn Hd)) * W +
      φ₂ X ^ m * (φ₂ (GPoly.toPoly M₁ D₁))′ := by
    rw [hW, Derivation.leibniz, hXm', C_mul, map_mul]
    simp only [smul_eq_mul]
    ring
  rw [Derivation.leibniz_div]
  simp only [smul_eq_mul]
  rw [eq_div_iff hW0]
  have e1 : W⁻¹ ^ 2 * (W * (φ₂ (GPoly.toPoly M₁ Y))′ - φ₂ (GPoly.toPoly M₁ Y) * W′) * W =
      (W * (φ₂ (GPoly.toPoly M₁ Y))′ - φ₂ (GPoly.toPoly M₁ Y) * W′) / W := by
    field_simp
  have e2 : φ₂ (C gK) * (φ₂ (GPoly.toPoly M₁ Y) / W) * W = φ₂ (C gK) * φ₂ (GPoly.toPoly M₁ Y) := by
    field_simp
  rw [add_mul, e1, e2, div_add' _ _ _ hW0, div_eq_iff hW0, hW']
  rw [hW]
  linear_combination (φ₂ (X : K₁[X]) ^ m) * h2

end Tower
