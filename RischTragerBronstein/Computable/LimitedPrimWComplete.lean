import RischTragerBronstein.Computable.LimitedPrimW

/-!
# Completeness of `limitedPrimW`

If `z′ = G - c W` has a solution `z ∈ S(x)(t₁)`, `c ∈ S`, over **any** extension `S ⊇ R` of the
constants, and the Hermite remainder of `W` is non-zero, then `limitedPrimW` succeeds and returns
(the preimage of) `c`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower

variable {R S K₁ K₂ : Type*} [Field R] [DecidableEq R] [CharZero R] [Field S] [CharZero S]
variable [Differential S] [Differential S[X]] [Field K₁] [CharZero K₁] [Algebra S[X] K₁]
variable [IsFractionRing S[X] K₁] [Differential K₁] [DifferentialAlgebra S[X] K₁]
variable [Differential K₁[X]] [Field K₂] [Differential K₂] [Algebra K₁[X] K₂]
variable [IsFractionRing K₁[X] K₂] [DifferentialAlgebra K₁[X] K₂]
variable [Algebra K₁ K₂] [IsScalarTower K₁ K₁[X] K₂] [DifferentialAlgebra K₁ K₂]

local notation "φ" => algebraMap S[X] K₁
local notation "φ₂" => algebraMap K₁[X] K₂

lemma getD_map_sem_zero {α K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)
    (q : GPoly α) (d : α) (hd : M.sem d = 0) :
    (q.map M.sem).getD 0 0 = M.sem (q.getD 0 d) := by
  cases q <;> simp [hd]

set_option maxHeartbeats 1600000 in
theorem limitedPrimW_complete (ι : R →+* S) (h0 : ∀ s : S, s′ = 0)
    (hD : ∀ P : S[X], P′ = derivative P)
    (hKconst : ∀ y : K₁, y′ = 0 → ∃ b : S, y = φ (C b))
    {En₁ Ed₁ : CPoly R} {Iη₁ : CPoly.RationalIntegral R}
    (hcη₁ : CPoly.rationalCheck En₁ Ed₁ Iη₁ = true) (hEd₁ : CPoly.toPoly Ed₁ ≠ 0)
    (hη0 : CPoly.isZero Iη₁.r = false)
    (hD₂ : ∀ P : K₁[X], P′ = implicitDeriv (C (CPoly.ev K₁ ι (En₁, Ed₁))) P)
    (hconst₂ : ∀ P : K₁[X], P′ = 0 → ∃ e : K₁, P = C e)
    (G W : GFrac (GFrac R))
    (hG0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) G.2 ≠ 0)
    (hW0 : GPoly.toPoly (M₁In (K₁ := K₁) ι h0 hD) W.2 ≠ 0)
    (hrW : GPoly.isZero (ops₁g R) (GPoly.divMod (ops₁g R)
      (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).b
      (GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2).s).2 = false)
    (z : K₂) (c : S)
    (hz : z′ = (M₂W (K₂ := K₂) ι h0 hD hD₂).sem G -
      φ₂ (C (φ (C c))) * (M₂W (K₂ := K₂) ι h0 hD hD₂).sem W) :
    ∃ c' hr P, limitedPrimW En₁ Ed₁ Iη₁ G W = some (c', hr, P) ∧ ι c' = c := by
  set M₁ := M₁In (K₁ := K₁) ι h0 hD with hM₁
  have hWη : GPoly.toPoly M₁ [(En₁, Ed₁)] = C (CPoly.ev K₁ ι (En₁, Ed₁)) := by
    rw [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero, hM₁, sem_M₁In]
  have hDW : ∀ P : K₁[X], P′ = implicitDeriv (GPoly.toPoly M₁ [(En₁, Ed₁)]) P := fun P ↦ by
    rw [hWη]; exact hD₂ P
  have hnorm : ∀ p : K₁[X], Irreducible p → ¬p ∣ p′ := fun p hp ↦
    not_dvd_deriv_of_irreducible_primitive (CPoly.ev K₁ ι (En₁, Ed₁)) hD₂ hconst₂ hp
  have hinj₂ : Function.Injective φ₂ := IsFractionRing.injective K₁[X] K₂
  have hinj₁ : Function.Injective φ := IsFractionRing.injective S[X] K₁
  -- Hermite reduction of `G` and `W`
  have hchkG := GPoly.hermiteCheck_hermite M₁ [(En₁, Ed₁)] G.1 G.2
    (fun p hp _ hdvd ↦ hnorm p hp (by rw [hDW]; exact hdvd)) hG0
  obtain ⟨hidG, hsqG⟩ := GPoly.hermiteCheck_sound_in (L := K₂) M₁ [(En₁, Ed₁)] G.1 G.2 _ hDW hchkG
  have hchkW := GPoly.hermiteCheck_hermite M₁ [(En₁, Ed₁)] W.1 W.2
    (fun p hp _ hdvd ↦ hnorm p hp (by rw [hDW]; exact hdvd)) hW0
  obtain ⟨hidW, hsqW⟩ := GPoly.hermiteCheck_sound_in (L := K₂) M₁ [(En₁, Ed₁)] W.1 W.2 _ hDW hchkW
  set hG := GPoly.hermite (ops₁g R) [(En₁, Ed₁)] G.1 G.2 with hhG
  set hW := GPoly.hermite (ops₁g R) [(En₁, Ed₁)] W.1 W.2 with hhW
  have hsG0 : GPoly.toPoly M₁ hG.s ≠ 0 := hsqG.ne_zero
  have hsW0 : GPoly.toPoly M₁ hW.s ≠ 0 := hsqW.ne_zero
  have hdmG := GPoly.divMod_spec M₁ hG.b hG.s
  have hdegG := GPoly.divMod_degree_lt M₁ hG.b hG.s hsG0
  have hdmW := GPoly.divMod_spec M₁ hW.b hW.s
  have hdegW := GPoly.divMod_degree_lt M₁ hW.b hW.s hsW0
  set qG := (GPoly.divMod (ops₁g R) hG.b hG.s).1 with hqG
  set rG := (GPoly.divMod (ops₁g R) hG.b hG.s).2 with hrG
  set qW := (GPoly.divMod (ops₁g R) hW.b hW.s).1 with hqW
  set rW := (GPoly.divMod (ops₁g R) hW.b hW.s).2 with hrWdef
  have hrW0 : GPoly.toPoly M₁ rW ≠ 0 := fun hz0 ↦ by
    rw [(GPoly.isZero_iff M₁ rW).mpr hz0] at hrW
    exact Bool.noConfusion hrW
  have hφsG : φ₂ (GPoly.toPoly M₁ hG.s) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr hsG0
  have hφsW : φ₂ (GPoly.toPoly M₁ hW.s) ≠ 0 := (map_ne_zero_iff _ hinj₂).mpr hsW0
  -- the constant, in `K₁`
  set ct : K₁ := φ (C c) with hct
  have hct' : (φ₂ (C ct))′ = 0 := by
    rw [deriv_algebraMap, hD₂, implicitDeriv_C, hct, deriv_algebraMap, hD, derivative_C, map_zero,
      C_0, map_zero]
  have eG : φ₂ (GPoly.toPoly M₁ hG.b) / φ₂ (GPoly.toPoly M₁ hG.s) =
      φ₂ (GPoly.toPoly M₁ qG) + φ₂ (GPoly.toPoly M₁ rG) / φ₂ (GPoly.toPoly M₁ hG.s) := by
    rw [hdmG, map_add, map_mul, add_div, mul_div_assoc, div_self hφsG, mul_one]
  have eW : φ₂ (GPoly.toPoly M₁ hW.b) / φ₂ (GPoly.toPoly M₁ hW.s) =
      φ₂ (GPoly.toPoly M₁ qW) + φ₂ (GPoly.toPoly M₁ rW) / φ₂ (GPoly.toPoly M₁ hW.s) := by
    rw [hdmW, map_add, map_mul, add_div, mul_div_assoc, div_self hφsW, mul_one]
  have hz₁ : (z - φ₂ (GPoly.toPoly M₁ hG.gn) / φ₂ (GPoly.toPoly M₁ hG.gd) +
      φ₂ (C ct) * (φ₂ (GPoly.toPoly M₁ hW.gn) / φ₂ (GPoly.toPoly M₁ hW.gd)))′ =
      φ₂ (GPoly.toPoly M₁ qG - C ct * GPoly.toPoly M₁ qW) +
        φ₂ (GPoly.toPoly M₁ rG) / φ₂ (GPoly.toPoly M₁ hG.s) +
        φ₂ (-(C ct * GPoly.toPoly M₁ rW)) / φ₂ (GPoly.toPoly M₁ hW.s) := by
    rw [map_add, map_sub, Derivation.leibniz, hct', hz, sem_M₂W, sem_M₂W, hidG, hidW, eG, eW]
    simp only [smul_eq_mul, map_sub, map_mul, map_neg, neg_div]
    ring
  have hdegW' : (-(C ct * GPoly.toPoly M₁ rW)).degree < (GPoly.toPoly M₁ hW.s).degree := by
    rw [degree_neg, C_mul']
    exact (degree_smul_le _ _).trans_lt hdegW
  obtain ⟨hcancel, -⟩ := deriv_eq_poly_add_two_proper (K := K₂) hnorm _ _ _ _ _ hsqG hsqW hdegG
    hdegW' _ hz₁
  -- the quotient is the constant
  set Pc := GPoly.mul (ops₁g R) rG hW.s with hPc
  set Qc := GPoly.mul (ops₁g R) rW hG.s with hQc
  have hPQ : GPoly.toPoly M₁ Pc = C ct * GPoly.toPoly M₁ Qc := by
    rw [hPc, hQc, GPoly.toPoly_mul, GPoly.toPoly_mul]
    linear_combination hcancel
  have hQc0 : GPoly.toPoly M₁ Qc ≠ 0 := by
    rw [hQc, GPoly.toPoly_mul]
    exact mul_ne_zero hrW0 hsG0
  have hdq := GPoly.divMod_spec M₁ Pc Qc
  have hdr := GPoly.divMod_degree_lt M₁ Pc Qc hQc0
  set q := (GPoly.divMod (ops₁g R) Pc Qc).1 with hq
  have hqC : GPoly.toPoly M₁ q = C ct := by
    by_contra hne
    have hne' : GPoly.toPoly M₁ q - C ct ≠ 0 := sub_ne_zero.mpr hne
    have hmul : (GPoly.toPoly M₁ q - C ct) * GPoly.toPoly M₁ Qc =
        -GPoly.toPoly M₁ (GPoly.divMod (ops₁g R) Pc Qc).2 := by
      linear_combination hPQ - hdq
    have hle : (GPoly.toPoly M₁ Qc).degree ≤
        (GPoly.toPoly M₁ (GPoly.divMod (ops₁g R) Pc Qc).2).degree := by
      rw [← degree_neg (GPoly.toPoly M₁ (GPoly.divMod (ops₁g R) Pc Qc).2), ← hmul, degree_mul]
      exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hne')
    exact absurd hdr (not_lt.mpr hle)
  have hsem0 : CPoly.ev K₁ ι (q.getD 0 ([], [1])) = ct := by
    have h1 := congrArg (fun P : K₁[X] ↦ P.coeff 0) hqC
    simp only [GPoly.coeff_toPoly, coeff_C_zero] at h1
    rw [← sem_M₁In (K₁ := K₁) ι h0 hD, ← h1]
    exact (getD_map_sem_zero M₁ q ([], [1]) (by
      rw [hM₁, sem_M₁In]; simp [CPoly.ev, CPoly.toPoly])).symm
  set nd := normFrac (q.getD 0 ([], [1])) with hnd
  have hnd2 : CPoly.toPoly nd.2 ≠ 0 := normFrac_den_ne_zero _
  have hnd2' : (CPoly.toPoly nd.2).map ι ≠ 0 :=
    (Polynomial.map_ne_zero_iff ι.injective).mpr hnd2
  have hndev : (CPoly.toPoly nd.1).map ι = C c * (CPoly.toPoly nd.2).map ι := by
    have h1 : CPoly.ev K₁ ι nd = ct := by rw [hnd, ev_normFrac, hsem0]
    apply hinj₁
    have hφd : φ ((CPoly.toPoly nd.2).map ι) ≠ 0 := (map_ne_zero_iff _ hinj₁).mpr hnd2'
    rw [map_mul, ← hct, ← h1, CPoly.ev]
    field_simp
  have hne := CPoly.linSolve_complete_map ι [nd.2] nd.1 [c] rfl (by
    simp [CPoly.lcombS, hndev])
  obtain ⟨cs, hcs⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨hlen, hcomb⟩ := CPoly.linSolve_sound _ _ _ hcs
  obtain ⟨c', rfl⟩ := List.length_eq_one_iff.mp hlen
  have hc' : ι c' = c := by
    have h1 : C c' * CPoly.toPoly nd.2 = CPoly.toPoly nd.1 := by
      simpa [CPoly.lcomb] using hcomb
    have h2 := congrArg (Polynomial.map ι) h1
    rw [Polynomial.map_mul, map_C, hndev] at h2
    exact C_injective (mul_right_cancel₀ hnd2' h2)
  have hconstW : limitedConstW En₁ Ed₁ G W = some c' := by
    simp only [limitedConstW, ← hhG, ← hhW, ← hrG, ← hrWdef, ← hPc, ← hQc, ← hq, ← hnd, hcs]
  -- in-field integration of `G - c' W`
  obtain ⟨hden, hsem⟩ := subSmulCode_spec (K₂ := K₂) ι h0 hD hD₂ G W c'
  have hder := isDerivPrim_complete (K₁ := K₁) (K₂ := K₂) ι h0 hD hKconst hcη₁ hEd₁ hη0 hD₂ hconst₂
    _ _ hden z (by rw [← sem_M₂W (K₂ := K₂) ι h0 hD hD₂, hsem, hc', hz])
  rw [← derivPrimSol_isSome] at hder
  obtain ⟨⟨hr, P⟩, hsol⟩ := Option.isSome_iff_exists.mp hder
  exact ⟨c', hr, P, by simp only [limitedPrimW, hconstW, hsol, Option.map_some], hc'⟩

end Tower
