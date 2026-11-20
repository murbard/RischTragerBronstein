import RischTragerBronstein.Computable.HexpHexpIndep
import RischTragerBronstein.Computable.HexpSpecialBound
import RischTragerBronstein.Computable.NormCoeff

/-!
# Two general hyperexponentials: independence when the denominators share poles

`hexpHexpComb Hn₁ Hd₁ Hn₂ Hd₂` certifies that `zη₁ + cη₂` is never a logarithmic derivative in
`S(x)` for integers `c ≠ 0`, `z`. Write `ηᵢ = ηᵢᴴ + bᵢ / sᵢ` (Hermite part plus proper simple-pole
part). If `zη₁ + cη₂ = e′ / e` then `z η₁ᴴ + c η₂ᴴ = 0`
(`deriv_eq_zero_of_add_proper₂_eq_logDeriv`), so:

* if exactly one Hermite part vanishes, the relation is impossible;
* if both are nonzero and not proportional (`linSolve` fails), it is impossible;
* if `η₁ᴴ = -(1/k) η₂ᴴ`, then `zη₁ + cη₂ = c (k η₁ + η₂)` must have only rational residues;
  a non-rational residue of the reduced fraction `k η₁ + η₂` refutes it.

Only the case `η₁ᴴ = η₂ᴴ = 0` (both with only simple poles and no polynomial part) is not covered.
`hexpHexpIndepFull` = `hexpHexpIndep` ∨ `hexpHexpComb`, with the same consequence
(`hexpHexpIndepFull_hom`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace CPoly

section Defs

variable {R : Type*} [Field R] [DecidableEq R] [HasRatRoots R] [HasNatTest R]

/-- The combined fraction `k η₁ + η₂`, reduced. -/
def combFrac (k : R) (Hn₁ Hd₁ Hn₂ Hd₂ : CPoly R) : CPoly R × CPoly R :=
  normCoeff (add (mul (smul k Hn₁) Hd₂) (mul Hn₂ Hd₁), mul Hd₁ Hd₂)

/-- A residue of `n / d` at a simple pole is not rational. -/
def nonRatResidue (F : CPoly R × CPoly R) : Bool :=
  !isZero (divMod (ratShiftProd (residuePolyW F.1 F.2)
    (HasRatRoots.ratRoots (findMu (simplePart F.2) (residuePolyW F.1 F.2)))) (simplePart F.2)).2

/-- **The Hermite-part certificate** for two hyperexponentials. -/
def hexpHexpComb (Hn₁ Hd₁ Hn₂ Hd₂ : CPoly R) : Bool :=
  if isZero (Tower.hermPartH Hn₁ Hd₁).1 then !isZero (Tower.hermPartH Hn₂ Hd₂).1
  else if isZero (Tower.hermPartH Hn₂ Hd₂).1 then true
  else
    match linSolve [mul (Tower.hermPartH Hn₁ Hd₁).1 (Tower.hermPartH Hn₂ Hd₂).2]
        (smul (-1) (mul (Tower.hermPartH Hn₂ Hd₂).1 (Tower.hermPartH Hn₁ Hd₁).2)) with
    | none => true
    | some [k] => nonRatResidue (combFrac k Hn₁ Hd₁ Hn₂ Hd₂)
    | _ => false

/-- **The full independence certificate.** -/
def hexpHexpIndepFull (Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ : CPoly R) : Bool :=
  hexpHexpIndep Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ || hexpHexpComb Hn₁ Hd₁ Hn₂ Hd₂

end Defs

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R] [HasRatRoots R] [HasNatTest R]
variable {S K : Type*} [Field S] [CharZero S] [Differential S] [Differential S[X]] [Field K]
variable [CharZero K] [Algebra S[X] K] [Differential K[X]]
variable [IsFractionRing S[X] K] [Differential K] [DifferentialAlgebra S[X] K]

local notation "φ" => algebraMap S[X] K

/-- **Hermite decomposition** of `η = Hn / Hd` in `S(x)`: `η = G′ + b / s`. -/
lemma hermite_decomp (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P) (Hn Hd : CPoly R)
    (hHd0 : toPoly Hd ≠ 0) :
    ∃ G : K, G′ = Tower.ηh ι Hn Hd - φ ((toPoly (integrateRational Hn Hd).r).map ι) /
        φ ((toPoly (integrateRational Hn Hd).s).map ι) ∧
      Squarefree ((toPoly (integrateRational Hn Hd).s).map ι) ∧
      ((toPoly (integrateRational Hn Hd).r).map ι).degree <
        ((toPoly (integrateRational Hn Hd).s).map ι).degree ∧
      ev K ι (Tower.hermPartH Hn Hd) = Tower.ηh ι Hn Hd -
        φ ((toPoly (integrateRational Hn Hd).r).map ι) /
          φ ((toPoly (integrateRational Hn Hd).s).map ι) := by
  have hchk := rationalCheck_integrateRational Hn Hd hHd0
  obtain ⟨I, hI⟩ : ∃ I, I = integrateRational Hn Hd := ⟨_, rfl⟩
  rw [← hI] at hchk ⊢
  rw [rationalCheck, Bool.and_eq_true, decide_eq_true_eq, hermiteCheck_iff] at hchk
  obtain ⟨⟨-, hgd0, hs0, hid, hsqc⟩, hlen⟩ := hchk
  have hsq := squarefreeCheck_sound hsqc
  have hdeg := degree_lt_of_trim_length_lt hlen
  simp only [toPoly_add, toPoly_mul, toPoly_deriv] at hid
  have hφgd : φ ((toPoly I.gd).map ι) ≠ 0 := map_toPoly_ne_zero ι hgd0
  have hφs : φ ((toPoly I.s).map ι) ≠ 0 := map_toPoly_ne_zero ι hs0
  have hφHd : φ ((toPoly Hd).map ι) ≠ 0 := map_toPoly_ne_zero ι hHd0
  refine ⟨φ ((toPoly I.gn).map ι) / φ ((toPoly I.gd).map ι) + φ ((toPoly I.Q).map ι), ?_,
    ((PerfectField.separable_iff_squarefree.mpr hsq).map).squarefree,
    by rw [degree_map, degree_map]; exact hdeg, ?_⟩
  · have hidS := congrArg (fun P : R[X] ↦ φ (P.map ι)) hid
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, map_mul, map_add,
      map_sub, ← derivative_map] at hidS
    rw [map_add, Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap, deriv_algebraMap,
      hD, hD, hD, Tower.ηh]
    simp only [smul_eq_mul]
    field_simp
    linear_combination -hidS
  · simp only [ev, Tower.hermPartH, ← hI, toPoly_sub, toPoly_mul, Polynomial.map_sub,
      Polynomial.map_mul, map_sub, map_mul, Tower.ηh]
    field_simp

/-- A reduced fraction with zero numerator certifies no non-rational residue. -/
lemma nonRatResidue_num_ne_zero {F : CPoly R × CPoly R} (hcop : IsCoprime (toPoly F.1) (toPoly F.2))
    (hF2 : toPoly F.2 ≠ 0) (h : nonRatResidue F = true) : toPoly F.1 ≠ 0 := by
  intro h0
  rw [h0] at hcop
  have hunit : IsUnit (toPoly F.2) := isCoprime_zero_left.mp hcop
  obtain ⟨S₀, G₁, G, q₁, q₂, σ, τ, σ', τ', E1, E2, E3, E4, E5, E6⟩ := simplePart_data F.2 hF2
  obtain ⟨hS0, hSd, -, -, -, -⟩ := Differential.simplePart_props hF2 E1 E2 E3 E4 E5 E6
  have hSdeg : (toPoly (simplePart F.2)).natDegree = 0 := by
    have := natDegree_le_of_dvd hSd hF2
    rw [natDegree_eq_zero_of_isUnit hunit] at this
    omega
  unfold nonRatResidue at h
  have hlt := divMod_degree_lt (ratShiftProd (residuePolyW F.1 F.2) (HasRatRoots.ratRoots
    (findMu (simplePart F.2) (residuePolyW F.1 F.2)))) (simplePart F.2) hS0
  generalize (divMod (ratShiftProd (residuePolyW F.1 F.2) (HasRatRoots.ratRoots
    (findMu (simplePart F.2) (residuePolyW F.1 F.2)))) (simplePart F.2)).2 = Rm at h hlt
  rw [degree_eq_natDegree hS0, hSdeg] at hlt
  have hR0 : toPoly Rm = 0 := by
    by_contra hne
    rw [degree_eq_natDegree hne] at hlt
    exact absurd (WithBot.coe_lt_coe.mp hlt) (Nat.not_lt_zero _)
  rw [(isZero_iff _).mpr hR0] at h
  exact Bool.noConfusion h

set_option maxHeartbeats 1600000 in
/-- **The Hermite-part certificate gives uniqueness**: `y′ + (c η₂ + z η₁) y = 0` has only the
zero solution in `S(x)`, for integers `c ≠ 0` and `z`. -/
theorem hexpHexpComb_hom (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ : CPoly R}
    (hHn10 : toPoly Hn₁ ≠ 0) (hHd10 : toPoly Hd₁ ≠ 0)
    (hcop₁ : IsCoprime (toPoly Hn₁) (toPoly Hd₁)) (hcert₁ : hyperexpMonomialCheck Hn₁ Hd₁ μ₁ = true)
    (hHn20 : toPoly Hn₂ ≠ 0) (hHd20 : toPoly Hd₂ ≠ 0)
    (hcop₂ : IsCoprime (toPoly Hn₂) (toPoly Hd₂)) (hcert₂ : hyperexpMonomialCheck Hn₂ Hd₂ μ₂ = true)
    (hcomb : hexpHexpComb Hn₁ Hd₁ Hn₂ Hd₂ = true) (c : ℤ) (hc : c ≠ 0) (z : ℤ) (y : K)
    (h : y′ + (ev K ι (smul (c : R) Hn₂, Hd₂) +
      (z : K) * (φ ((toPoly Hn₁).map ι) / φ ((toPoly Hd₁).map ι))) * y = 0) : y = 0 := by
  have hιinj : Function.Injective ι := ι.injective
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  have hcS : (c : S) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hcK : (c : K) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hφHd₁ : φ ((toPoly Hd₁).map ι) ≠ 0 := map_toPoly_ne_zero ι hHd10
  have hφHd₂ : φ ((toPoly Hd₂).map ι) ≠ 0 := map_toPoly_ne_zero ι hHd20
  set η₁ := Tower.ηh (K₁ := K) ι Hn₁ Hd₁ with hη₁
  set η₂ := Tower.ηh (K₁ := K) ι Hn₂ Hd₂ with hη₂
  have hev₂ : ev K ι (smul (c : R) Hn₂, Hd₂) = (c : K) * η₂ := by
    rw [ev, toPoly_smul, Polynomial.map_mul, map_C, map_mul, map_intCast, mul_div_assoc,
      C_eq_intCast, map_intCast]
  rw [hev₂] at h
  by_contra hy0
  have hyi0 : y⁻¹ ≠ 0 := inv_ne_zero hy0
  have hlog : logDeriv y⁻¹ = (z : K) * η₁ + (c : K) * η₂ := by
    rw [logDeriv, Derivation.leibniz_inv, smul_eq_mul]
    field_simp
    linear_combination -h
  -- Hermite decompositions
  obtain ⟨G₁, hG₁, hsq₁, hdeg₁, hev₁⟩ := hermite_decomp (K := K) ι hD Hn₁ Hd₁ hHd10
  obtain ⟨G₂, hG₂, hsq₂, hdeg₂, hevH₂⟩ := hermite_decomp (K := K) ι hD Hn₂ Hd₂ hHd20
  set r₁ := (toPoly (integrateRational Hn₁ Hd₁).r).map ι
  set s₁ := (toPoly (integrateRational Hn₁ Hd₁).s).map ι
  set r₂ := (toPoly (integrateRational Hn₂ Hd₂).r).map ι
  set s₂ := (toPoly (integrateRational Hn₂ Hd₂).s).map ι
  have hdegz : (C (z : S) * r₁).degree < s₁.degree := lt_of_le_of_lt
    (show degree (C (z : S) * r₁) ≤ degree r₁ by rw [← smul_eq_C_mul]; exact degree_smul_le _ _)
    hdeg₁
  have hdegc : (C (c : S) * r₂).degree < s₂.degree := lt_of_le_of_lt
    (show degree (C (c : S) * r₂) ≤ degree r₂ by rw [← smul_eq_C_mul]; exact degree_smul_le _ _)
    hdeg₂
  have hW := Differential.deriv_eq_zero_of_add_proper₂_eq_logDeriv hD _ _ _ _ hsq₁ hsq₂ hdegz hdegc
    ((z : K) * G₁ + (c : K) * G₂) y⁻¹ hyi0 (by
      rw [hlog, map_add, Derivation.leibniz, Derivation.leibniz, hG₁, hG₂,
        Derivation.map_intCast, Derivation.map_intCast, map_mul, map_mul, C_eq_intCast,
        C_eq_intCast, map_intCast, map_intCast]
      simp only [smul_eq_mul, zero_mul, add_zero]
      ring)
  have hkey : (z : K) * ev K ι (Tower.hermPartH Hn₁ Hd₁) +
      (c : K) * ev K ι (Tower.hermPartH Hn₂ Hd₂) = 0 := by
    rw [hev₁, hevH₂]
    rw [map_add, Derivation.leibniz, Derivation.leibniz, hG₁, hG₂,
      Derivation.map_intCast, Derivation.map_intCast] at hW
    simp only [smul_eq_mul, zero_mul, add_zero] at hW
    linear_combination hW
  -- the codes of the Hermite parts
  set N₁ := (Tower.hermPartH Hn₁ Hd₁).1
  set D₁ := (Tower.hermPartH Hn₁ Hd₁).2
  set N₂ := (Tower.hermPartH Hn₂ Hd₂).1
  set D₂ := (Tower.hermPartH Hn₂ Hd₂).2
  have hD₁0 : toPoly D₁ ≠ 0 := by
    have hI := rationalCheck_integrateRational Hn₁ Hd₁ hHd10
    rw [rationalCheck, Bool.and_eq_true, hermiteCheck_iff] at hI
    simp only [D₁, Tower.hermPartH, toPoly_mul]; exact mul_ne_zero hHd10 hI.1.2.2.1
  have hD₂0 : toPoly D₂ ≠ 0 := by
    have hI := rationalCheck_integrateRational Hn₂ Hd₂ hHd20
    rw [rationalCheck, Bool.and_eq_true, hermiteCheck_iff] at hI
    simp only [D₂, Tower.hermPartH, toPoly_mul]; exact mul_ne_zero hHd20 hI.1.2.2.1
  have hφD₁ : φ ((toPoly D₁).map ι) ≠ 0 := map_toPoly_ne_zero ι hD₁0
  have hφD₂ : φ ((toPoly D₂).map ι) ≠ 0 := map_toPoly_ne_zero ι hD₂0
  have hev0 : ∀ {N D : CPoly R}, toPoly D ≠ 0 → (ev K ι (N, D) = 0 ↔ toPoly N = 0) := fun hD0 ↦ by
    constructor
    · intro h0
      rw [ev, div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · exact (Polynomial.map_eq_zero_iff hιinj).mp ((map_eq_zero_iff _ hinj).mp h0)
      · exact absurd h0 (map_toPoly_ne_zero ι hD0)
    · intro h0; rw [ev, h0, Polynomial.map_zero, map_zero, zero_div]
  have hev0₁ := hev0 (N := N₁) hD₁0
  have hev0₂ := hev0 (N := N₂) hD₂0
  unfold hexpHexpComb at hcomb
  split_ifs at hcomb with hz₁ hz₂
  · -- `η₁ᴴ = 0`: then `c η₂ᴴ = 0`
    have hN₁ : toPoly N₁ = 0 := (isZero_iff _).mp hz₁
    have hH₁ : ev K ι (N₁, D₁) = 0 := hev0₁.mpr hN₁
    rw [show Tower.hermPartH Hn₁ Hd₁ = (N₁, D₁) from rfl, hH₁, mul_zero, zero_add,
      show Tower.hermPartH Hn₂ Hd₂ = (N₂, D₂) from rfl] at hkey
    have hH₂ := (mul_eq_zero.mp hkey).resolve_left hcK
    have h2 : isZero (Tower.hermPartH Hn₂ Hd₂).1 = true := (isZero_iff _).mpr (hev0₂.mp hH₂)
    rw [h2] at hcomb
    exact absurd hcomb (by decide)
  · -- `η₂ᴴ = 0`, `η₁ᴴ ≠ 0`: then `z = 0`
    have hN₁ : toPoly N₁ ≠ 0 := fun h0 ↦ hz₁ ((isZero_iff _).mpr h0)
    have hH₂ : ev K ι (N₂, D₂) = 0 := hev0₂.mpr ((isZero_iff _).mp hz₂)
    rw [show Tower.hermPartH Hn₂ Hd₂ = (N₂, D₂) from rfl, hH₂, mul_zero, add_zero,
      show Tower.hermPartH Hn₁ Hd₁ = (N₁, D₁) from rfl] at hkey
    have hzK : (z : K) = 0 :=
      (mul_eq_zero.mp hkey).resolve_right fun h0 ↦ hN₁ (hev0₁.mp h0)
    rw [hzK, zero_mul, add_zero] at h
    refine hy0 (hyperexpW_homogeneous (K := K) ι hD hHn20 hHd20 hcop₂ hcert₂ (-c)
      (neg_ne_zero.mpr hc) y ?_)
    rw [Int.cast_neg, C_neg, map_neg, C_eq_intCast, map_intCast]
    change y′ = -(c : K) * η₂ * y
    linear_combination h
  · -- both nonzero: `z / c` is the coefficient found by `linSolve`
    have hN₁ : toPoly N₁ ≠ 0 := fun h0 ↦ hz₁ ((isZero_iff _).mpr h0)
    have hN₂ : toPoly N₂ ≠ 0 := fun h0 ↦ hz₂ ((isZero_iff _).mpr h0)
    have hcross : C ((z : S) / c) * (toPoly (mul N₁ D₂)).map ι =
        (toPoly (smul (-1) (mul N₂ D₁))).map ι := by
      apply hinj
      rw [show Tower.hermPartH Hn₁ Hd₁ = (N₁, D₁) from rfl,
        show Tower.hermPartH Hn₂ Hd₂ = (N₂, D₂) from rfl, ev, ev] at hkey
      have hzc : φ (C ((z : S) / c)) = (z : K) / c := by
        rw [show φ (C ((z : S) / c)) = ((algebraMap S[X] K).comp C) ((z : S) / c) from rfl,
          map_div₀, map_intCast, map_intCast]
      simp only [toPoly_mul, toPoly_smul, Polynomial.map_mul, map_C, map_mul, map_neg, map_one,
        Polynomial.map_neg, Polynomial.map_one, C_neg, C_1, hzc]
      field_simp at hkey ⊢
      linear_combination hkey
    have hne := linSolve_complete_map ι [mul N₁ D₂] (smul (-1) (mul N₂ D₁)) [(z : S) / c] rfl (by
      simp only [lcombS, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons,
        List.sum_nil, add_zero]
      exact hcross)
    obtain ⟨cs, hcs⟩ := Option.ne_none_iff_exists'.mp hne
    rw [hcs] at hcomb
    obtain ⟨hlen1, hlc⟩ := linSolve_sound _ _ cs hcs
    obtain ⟨k, rfl⟩ : ∃ k, cs = [k] := List.length_eq_one_iff.mp hlen1
    simp only at hcomb
    simp only [lcomb, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons,
      List.sum_nil, add_zero] at hlc
    have hv0 : (toPoly (mul N₁ D₂)).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr (by
      rw [toPoly_mul]; exact mul_ne_zero hN₁ hD₂0)
    have hkz : ι k = (z : S) / c := by
      have h1 := congrArg (Polynomial.map ι) hlc
      rw [Polynomial.map_mul, map_C, ← hcross] at h1
      exact C_inj.mp (mul_right_cancel₀ hv0 h1)
    -- the combined fraction
    set F := combFrac k Hn₁ Hd₁ Hn₂ Hd₂ with hF
    have hF2 : toPoly F.2 ≠ 0 := normCoeff_den_ne_zero _
    have hFcop : IsCoprime (toPoly F.1) (toPoly F.2) := normCoeff_coprime _
    have hF1 : toPoly F.1 ≠ 0 := nonRatResidue_num_ne_zero hFcop hF2 hcomb
    have hevF : ev K ι F = φ (C (ι k)) * η₁ + η₂ := by
      have hn : ev K ι F = ev K ι (add (mul (smul k Hn₁) Hd₂) (mul Hn₂ Hd₁), mul Hd₁ Hd₂) :=
        normCoeff_spec ((algebraMap S[X] K).comp (mapRingHom ι))
          ((IsFractionRing.injective S[X] K).comp (Polynomial.map_injective ι ι.injective)) _
      rw [hn]
      simp only [ev, toPoly_add, toPoly_mul, toPoly_smul, Polynomial.map_add, Polynomial.map_mul,
        map_C, map_add, map_mul, hη₁, hη₂, Tower.ηh]
      field_simp
    have hιkK : φ (C (ι k)) = (z : K) / c := by
      rw [hkz, show φ (C ((z : S) / c)) = ((algebraMap S[X] K).comp C) ((z : S) / c) from rfl,
        map_div₀, map_intCast, map_intCast]
    -- apply the homogeneous theorem to the reduced fraction `F`
    obtain ⟨⟨hS0, hcopR⟩, hS0', hSd', hcop'', hScop', hS', hsqS⟩ := simplePart_props_map ι F.2 hF2
    obtain ⟨t, ht⟩ := residuePolyW_bezout F.1 F.2 hS0 hcopR.symm
    obtain ⟨hμ0, q, hq⟩ := muCheck_spec (muCheck_findMu (simplePart F.2) (residuePolyW F.1 F.2) hS0)
    have hrS : (toPoly (simplePart F.2)).map ι ∣
        (toPoly (residuePolyW F.1 F.2)).map ι * derivative ((toPoly F.2).map ι) -
          (toPoly F.1).map ι := by
      refine ⟨-(t.map ι), ?_⟩
      have := congrArg (Polynomial.map ι) ht
      simp only [Polynomial.map_add, Polynomial.map_mul, ← derivative_map] at this
      rw [← this]; ring
    have hμS : (toPoly (simplePart F.2)).map ι ∣
        ((toPoly (findMu (simplePart F.2) (residuePolyW F.1 F.2))).map ι).comp
          ((toPoly (residuePolyW F.1 F.2)).map ι) :=
      ⟨q.map ι, by rw [← Polynomial.map_comp, hq, Polynomial.map_mul]⟩
    have hres : isZero (divMod (ratShiftProd (residuePolyW F.1 F.2) (HasRatRoots.ratRoots
        (findMu (simplePart F.2) (residuePolyW F.1 F.2)))) (simplePart F.2)).2 = false := by
      rw [nonRatResidue, Bool.not_eq_true'] at hcomb; exact hcomb
    have halt := nonrational_residue_alt ι hF2 hμ0 hres
    refine hy0 (rde_homogeneous_W hD _ _ _ _ _ ((Polynomial.map_ne_zero_iff hιinj).mpr hF1)
      ((Polynomial.map_ne_zero_iff hιinj).mpr hF2) (hFcop.map (mapRingHom ι)) hSd' hScop' hrS hμS
      (Or.inr (Or.inr halt)) (-c) (neg_ne_zero.mpr hc) y ?_)
    have hevF' : φ ((toPoly F.1).map ι) / φ ((toPoly F.2).map ι) = (z : K) / c * η₁ + η₂ := by
      rw [← hιkK]; exact hevF
    rw [hevF', Int.cast_neg, C_neg, map_neg, C_eq_intCast, map_intCast]
    field_simp
    linear_combination h

/-- **The full certificate gives uniqueness.** -/
theorem hexpHexpIndepFull_hom (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ : CPoly R}
    (hHn10 : toPoly Hn₁ ≠ 0) (hHd10 : toPoly Hd₁ ≠ 0)
    (hcop₁ : IsCoprime (toPoly Hn₁) (toPoly Hd₁)) (hcert₁ : hyperexpMonomialCheck Hn₁ Hd₁ μ₁ = true)
    (hHn20 : toPoly Hn₂ ≠ 0) (hHd20 : toPoly Hd₂ ≠ 0)
    (hcop₂ : IsCoprime (toPoly Hn₂) (toPoly Hd₂)) (hcert₂ : hyperexpMonomialCheck Hn₂ Hd₂ μ₂ = true)
    (hind : hexpHexpIndepFull Hn₁ Hd₁ μ₁ Hn₂ Hd₂ μ₂ = true) (c : ℤ) (hc : c ≠ 0) (z : ℤ) (y : K)
    (h : y′ + (ev K ι (smul (c : R) Hn₂, Hd₂) +
      (z : K) * (φ ((toPoly Hn₁).map ι) / φ ((toPoly Hd₁).map ι))) * y = 0) : y = 0 := by
  rw [hexpHexpIndepFull, Bool.or_eq_true] at hind
  rcases hind with hind | hind
  · exact hexpHexpIndep_hom ι hD hHn10 hHd10 hcop₁ hcert₁ hHn20 hHd20 hcop₂ hcert₂ hind c hc z y h
  · exact hexpHexpComb_hom ι hD hHn10 hHd10 hcop₁ hcert₁ hHn20 hHd20 hcop₂ hcert₂ hind c hc z y h

end CPoly
