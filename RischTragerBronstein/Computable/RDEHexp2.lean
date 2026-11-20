import RischTragerBronstein.Computable.RDEExp
import RischTragerBronstein.Computable.RDEPrimW
import RischTragerBronstein.Computable.HexpBase
import RischTragerBronstein.Computable.HexpExpIndep
import RischTragerBronstein.Computable.RDEHexp

/-!
# The Risch differential equation `y′ + g y = A / (t₁^m D₁)` over `R(x)(t₁)`, `g ∈ R(x)`

The variant of `RDEHexp.lean` with a rational coefficient `g = Gn / Gd ∈ R(x)` (typically
`g = c η₂` for a second hyperexponential `t₂′ = η₂ t₂`). The top coefficient equations have the
coefficients `g + z η = (Gn Hd + z Hn Gd) / (Hd Gd)`; their residue annihilators are computed by
`findMu` (`hexpMu₂`), so no annihilator has to be supplied.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

section Defs

variable {R : Type*} [Field R] [DecidableEq R] [CPoly.HasRatRoots R] [HasNatTest R]

/-- The coefficient `g + z η` as an unreduced fraction (`(Gn, Gd)` for `z = 0`). -/
def hexpGq₂Raw (Hn Hd Gn Gd : CPoly R) (z : ℤ) : GFrac R :=
  if z = 0 then (Gn, Gd)
  else (CPoly.add (CPoly.mul Gn Hd) (CPoly.smul (z : R) (CPoly.mul Hn Gd)), CPoly.mul Hd Gd)

/-- The coefficient `g + z η` as a reduced fraction, `g = Gn / Gd`. -/
def hexpGq₂ (Hn Hd Gn Gd : CPoly R) (z : ℤ) : GFrac R :=
  CPoly.normCoeff (hexpGq₂Raw Hn Hd Gn Gd z)

/-- An annihilator of the residues of `g + z η`, by `findMu`. -/
def hexpMu₂ (Hn Hd Gn Gd : CPoly R) (z : ℤ) : CPoly R :=
  CPoly.findMu (CPoly.simplePart (hexpGq₂ Hn Hd Gn Gd z).2)
    (CPoly.residuePolyW (hexpGq₂ Hn Hd Gn Gd z).1 (hexpGq₂ Hn Hd Gn Gd z).2)

/-- The top-degree recursion for `D Y′ + P₀ Y = Ap` in a hyperexponential extension. -/
def rdePolyHexpAux₂ (Hn Hd Gn Gd : CPoly R) (m : ℕ) (D P₀ : GPoly (GFrac R)) :
    ℕ → GPoly (GFrac R) → GPoly (GFrac R) → Option (GPoly (GFrac R))
  | 0, Ap, acc => if GPoly.isZero (ops₁g R) Ap then some acc else none
  | fuel + 1, Ap, acc =>
    if GPoly.isZero (ops₁g R) Ap then some acc
    else
      let dA := (GPoly.trim (ops₁g R) Ap).length - 1
      let d₁ := (GPoly.trim (ops₁g R) D).length - 1
      if dA < d₁ then none
      else
        match rdeTopCoeffW (hexpGq₂ Hn Hd Gn Gd (hexpZ dA d₁ m))
            (hexpMu₂ Hn Hd Gn Gd (hexpZ dA d₁ m))
            (GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) D))
            (GPoly.lead (ops₁g R) (GPoly.trim (ops₁g R) Ap)) with
        | none => none
        | some yd =>
          let Yd := GPoly.monomial (ops₁g R) (dA - d₁) yd
          rdePolyHexpAux₂ Hn Hd Gn Gd m D P₀ fuel
            (GPoly.sub (ops₁g R) Ap (GPoly.add (ops₁g R)
              (GPoly.mul (ops₁g R) D (GPoly.derivT (ops₁g R) (hexpW Hn Hd) Yd))
              (GPoly.mul (ops₁g R) P₀ Yd)))
            (GPoly.add (ops₁g R) acc Yd)

/-- `P₀ = (g - m η) D₁ - D₁′`. -/
def rdeP₀H₂ (Hn Hd Gn Gd : CPoly R) (m : ℕ) (D : GPoly (GFrac R)) : GPoly (GFrac R) :=
  GPoly.sub (ops₁g R) (GPoly.smul (ops₁g R) (hexpGq₂ Hn Hd Gn Gd (-(m : ℤ))) D)
    (GPoly.derivT (ops₁g R) (hexpW Hn Hd) D)

/-- Solve `y′ + g y = A / (t₁^m D₁)` over `R(x)(t₁)`; the solution is `Y / (t₁^m D₁)`. -/
def rdeHexp₂ (Hn Hd Gn Gd : CPoly R) (A D₁ : GPoly (GFrac R)) (m : ℕ) : Option (GPoly (GFrac R)) :=
  rdePolyHexpAux₂ Hn Hd Gn Gd m D₁ (rdeP₀H₂ Hn Hd Gn Gd m D₁) ((GPoly.mul (ops₁g R) A D₁).length + 1)
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

variable (Gn Gd : CPoly R)

/-- The value of `hexpGq₂`: `g + z η`. -/
lemma ev_hexpGq₂ (hHd0 : CPoly.toPoly Hd ≠ 0) (hGd0 : CPoly.toPoly Gd ≠ 0) (z : ℤ) :
    CPoly.ev K₁ ι (hexpGq₂ Hn Hd Gn Gd z) = CPoly.ev K₁ ι (Gn, Gd) + (z : K₁) * ηh ι Hn Hd := by
  have hφHd : φ ((CPoly.toPoly Hd).map ι) ≠ 0 := CPoly.map_toPoly_ne_zero ι hHd0
  have hφGd : φ ((CPoly.toPoly Gd).map ι) ≠ 0 := CPoly.map_toPoly_ne_zero ι hGd0
  have hn : CPoly.ev K₁ ι (hexpGq₂ Hn Hd Gn Gd z) = CPoly.ev K₁ ι (hexpGq₂Raw Hn Hd Gn Gd z) :=
    CPoly.normCoeff_spec ((algebraMap S[X] K₁).comp (mapRingHom ι))
      ((IsFractionRing.injective S[X] K₁).comp (Polynomial.map_injective ι ι.injective)) _
  rw [hn]
  unfold hexpGq₂Raw
  split_ifs with hz
  · subst hz
    simp
  · simp only [CPoly.ev, CPoly.toPoly_add, CPoly.toPoly_mul, CPoly.toPoly_smul, Polynomial.map_add,
      Polynomial.map_mul, map_C, map_add, map_mul, ηh]
    rw [map_intCast, map_intCast, map_intCast]
    field_simp

/-- The denominator of `hexpGq₂` is nonzero. -/
lemma hexpGq₂_den_ne_zero (z : ℤ) : CPoly.toPoly (hexpGq₂ Hn Hd Gn Gd z).2 ≠ 0 :=
  CPoly.normCoeff_den_ne_zero _

/-- The numerator and denominator of `hexpGq₂` are coprime. -/
lemma hexpGq₂_coprime (z : ℤ) :
    IsCoprime (CPoly.toPoly (hexpGq₂ Hn Hd Gn Gd z).1) (CPoly.toPoly (hexpGq₂ Hn Hd Gn Gd z).2) :=
  CPoly.normCoeff_coprime _

/-- The numerator of `hexpGq₂` is nonzero when the coefficient is not a logarithmic derivative. -/
lemma hexpGq₂_num_ne_zero (hHd0 : CPoly.toPoly Hd ≠ 0) (hGd0 : CPoly.toPoly Gd ≠ 0) (z : ℤ)
    (hhom : ∀ e : K₁, e′ + (CPoly.ev K₁ ι (Gn, Gd) + (z : K₁) * ηh ι Hn Hd) * e = 0 → e = 0) :
    CPoly.toPoly (hexpGq₂ Hn Hd Gn Gd z).1 ≠ 0 := by
  intro h0
  have hev := ev_hexpGq₂ (K₁ := K₁) ι Hn Hd Gn Gd hHd0 hGd0 z
  rw [CPoly.ev, h0] at hev
  simp only [Polynomial.map_zero, map_zero, zero_div] at hev
  have := hhom 1 (by rw [← hev]; simp)
  exact one_ne_zero this

/-- `hexpMu₂` is a nonzero annihilator of the residues of `hexpGq₂`. -/
lemma hexpMu₂_spec (hHd0 : CPoly.toPoly Hd ≠ 0) (hGd0 : CPoly.toPoly Gd ≠ 0) (z : ℤ) :
    CPoly.toPoly (hexpMu₂ Hn Hd Gn Gd z) ≠ 0 ∧
      ∃ q : R[X], (CPoly.toPoly (hexpMu₂ Hn Hd Gn Gd z)).comp
        (CPoly.toPoly (CPoly.residuePolyW (hexpGq₂ Hn Hd Gn Gd z).1 (hexpGq₂ Hn Hd Gn Gd z).2)) =
          CPoly.toPoly (CPoly.simplePart (hexpGq₂ Hn Hd Gn Gd z).2) * q := by
  have hden := hexpGq₂_den_ne_zero Hn Hd Gn Gd z
  obtain ⟨S₀, G₁, G, q₁, q₂, σ, τ, σ', τ', E1, E2, E3, E4, E5, E6⟩ := CPoly.simplePart_data _ hden
  obtain ⟨hS0, -, -, -, -, -⟩ := Differential.simplePart_props hden E1 E2 E3 E4 E5 E6
  exact CPoly.muCheck_spec (CPoly.muCheck_findMu _ _ hS0)

end Coeff

include h0 hD in
/-- **Soundness of the recursion**: the invariant `D acc′ + P₀ acc + Ap` is preserved. -/
theorem rdePolyHexpAux₂_sound (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P)
    (Gn Gd : CPoly R) (m : ℕ) (D P₀ : GPoly (GFrac R)) (fuel : ℕ) (Ap acc Y : GPoly (GFrac R))
    (h : rdePolyHexpAux₂ Hn Hd Gn Gd m D P₀ fuel Ap acc = some Y) :
    let M₁ := M₁In (K₁ := K₁) ι h0 hD
    GPoly.toPoly M₁ D * (GPoly.toPoly M₁ Y)′ + GPoly.toPoly M₁ P₀ * GPoly.toPoly M₁ Y =
      GPoly.toPoly M₁ D * (GPoly.toPoly M₁ acc)′ + GPoly.toPoly M₁ P₀ * GPoly.toPoly M₁ acc +
        GPoly.toPoly M₁ Ap := by
  intro M₁
  induction fuel generalizing Ap acc with
  | zero =>
    simp only [rdePolyHexpAux₂] at h
    split_ifs at h with hz
    rw [Option.some.injEq] at h
    subst h
    rw [(GPoly.isZero_iff M₁ Ap).mp hz, add_zero]
  | succ fuel ih =>
    simp only [rdePolyHexpAux₂] at h
    split_ifs at h with hz hlt
    · rw [Option.some.injEq] at h
      subst h
      rw [(GPoly.isZero_iff M₁ Ap).mp hz, add_zero]
    · revert h
      cases rdeTopCoeffW (hexpGq₂ Hn Hd Gn Gd
            (hexpZ ((GPoly.trim (ops₁g R) Ap).length - 1) ((GPoly.trim (ops₁g R) D).length - 1) m))
          (hexpMu₂ Hn Hd Gn Gd
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
theorem rdeHexp₂_sound (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (ηh ι Hn Hd) * X) P)
    (hHd0 : CPoly.toPoly Hd ≠ 0) (Gn Gd : CPoly R) (hGd0 : CPoly.toPoly Gd ≠ 0)
    (A D₁ : GPoly (GFrac R)) (m : ℕ)
    (hD0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D₁ ≠ 0) {Y : GPoly (GFrac R)}
    (h : rdeHexp₂ Hn Hd Gn Gd A D₁ m = some Y) :
    (φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Y) /
        (φ₂ X ^ m * φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D₁)))′ +
        φ₂ (C (CPoly.ev K₁ ι (Gn, Gd))) *
          (φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) Y) /
            (φ₂ X ^ m * φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D₁))) =
      φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) A) /
        (φ₂ X ^ m * φ₂ (GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) D₁)) := by
  set M₁ := M₁In (K₁ := K₁) ι h0 hD with hM₁
  have hinv := rdePolyHexpAux₂_sound ι h0 hD Hn Hd hD₂ Gn Gd m D₁ (rdeP₀H₂ Hn Hd Gn Gd m D₁) _ _ [] Y h
  simp only [GPoly.toPoly_nil, map_zero, mul_zero, zero_add, GPoly.toPoly_mul] at hinv
  set gK : K₁ := CPoly.ev K₁ ι (Gn, Gd) with hgK
  have hP₀ : GPoly.toPoly M₁ (rdeP₀H₂ Hn Hd Gn Gd m D₁) =
      C (gK - m * ηh ι Hn Hd) * GPoly.toPoly M₁ D₁ - (GPoly.toPoly M₁ D₁)′ := by
    rw [rdeP₀H₂, GPoly.toPoly_sub, GPoly.toPoly_smul, toPoly_derivT_hexpW ι h0 hD Hn Hd hD₂, hM₁,
      sem_M₁In, ev_hexpGq₂ ι Hn Hd Gn Gd hHd0 hGd0]
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
