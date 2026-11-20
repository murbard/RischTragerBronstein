import RischTragerBronstein.Algebraic.SupDecideC
import RischTragerBronstein.Rational.IntegrableIn

/-!
# The superelliptic decision procedure: sound and complete

`superDecideFull f n A D B fuel` decides `∫ ∑_{j<n} Aⱼ(x)/D(x) yʲ dx` on `yⁿ = f(x)` for
`f, Aⱼ, D ∈ ℚ[x]`, `f` squarefree of positive degree, `D ≠ 0`, any `n`:

* `n ≤ 1`: the integrand is rational in `x`; it always has an elementary integral.
* otherwise it first runs the fast procedure `superDecideSup` (search certificates), and if that
  does not answer, the complete procedure `superDecideCoverC` (cover, Möbius transformation, and
  the torsion oracle with global certificates).

**`superDecideFull_spec`**: every answer is correct.
**`superDecideFull_complete`**: there is `B₀` such that for every `B ≥ B₀` and every `fuel` it
answers. No hypothesis on the oracle remains: the global non-speciality certificates exist
(`exists_cert_lists`) and are found (`certSearch_complete`), and the global-certificate oracle
answers for large bounds (`torsOracleFB_eventually`).
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad Jac NFC

namespace Sup

/-- **`superDecideMobQC` answers for all large bounds.** -/
theorem superDecideMobQC_eventually (f : CPoly ℚ) {n : ℕ} (hn2 : 2 ≤ n)
    (hsq : Squarefree (toPoly f)) (hfd : (toPoly f).natDegree = f.length - 1)
    (hd1 : 1 ≤ (toPoly f).natDegree) (hnd : n ∣ (toPoly f).natDegree) (A : List (CPoly ℚ))
    (D : CPoly ℚ) (hD : toPoly D ≠ 0) :
    ∃ B0, ∀ B, B0 ≤ B → superDecideMobQC f n A D B ≠ none := by
  have hn : 0 < n := by omega
  set cs := candQ f (candCount f n D) with hcsdef
  have hcsl : cs.length = candCount f n D := candQ_length f hsq.ne_zero _
  have hfl := natDegree_toPoly_le' f
  have hSl := natDegree_toPoly_le' (nbPartK f D)
  have hDl := natDegree_toPoly_le' D
  obtain ⟨M, hM, hbuild, hMF, hcr⟩ := buildFieldAll_spec f (nbPartK f D) hn hsq hfd hd1
    (squarefree_nbPartK f D hD) (isCoprime_nbPartK f D hD) cs (candQ_nodup f _) (candQ_ne f _)
    (candFuel f n D) (by unfold candFuel; omega) (by unfold candFuel; omega)
    (by unfold candFuel; omega) (by rw [hcsl]; unfold candFuel; omega)
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  obtain ⟨B0, hB0⟩ := superDecideMobMC_eventually M hM f hn2 hsq hfd hd1 hnd A D hD hMF cs
    (candQ_nodup f _) (candQ_ne f _) hcr (by
      rw [hcsl]; unfold candCount
      have h1 : n * (toPoly f).natDegree ≤ n * f.length := Nat.mul_le_mul_left _ (by omega)
      have h2 : n * ((toPoly D).natDegree + 1) ≤ n * (D.length + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega)
  refine ⟨B0, fun B hB ↦ ?_⟩
  unfold superDecideMobQC
  rw [hbuild]
  exact hB0 B hB

/-- **The complete cover procedure answers for all large bounds** (any `n ≥ 2`). -/
theorem superDecideCoverC_eventually (f : CPoly ℚ) {n : ℕ} (hn2 : 2 ≤ n)
    (hsq : Squarefree (toPoly f)) (hfd : (toPoly f).natDegree = f.length - 1)
    (hpd : 0 < f.length - 1) (A : List (CPoly ℚ)) (D : CPoly ℚ) (hD : toPoly D ≠ 0) :
    ∃ B0, ∀ B, B0 ≤ B → superDecideCoverC f n A D B ≠ none := by
  have hn : 0 < n := by omega
  set k := coverK f n with hkdef
  set c := coverC f with hcdef
  have hk : 0 < k := Nat.div_pos (Nat.gcd_le_left _ hn) (Nat.gcd_pos_of_pos_left _ hn)
  have hc : (toPoly f).eval c ≠ 0 := coverC_spec f hsq.ne_zero
  have hsqg : Squarefree (toPoly (compShiftPow f c k)) := by
    rw [toPoly_compShiftPow]; exact squarefree_comp_shiftPow hsq hc hk
  have hdeg : (toPoly (compShiftPow f c k)).natDegree = (f.length - 1) * k := by
    rw [natDegree_shiftPow f c hk, hfd]
  have hnd : n ∣ (toPoly (compShiftPow f c k)).natDegree := by
    rw [hdeg, hkdef, coverK]
    have hg : Nat.gcd n (f.length - 1) ∣ f.length - 1 := Nat.gcd_dvd_right _ _
    have hgn : Nat.gcd n (f.length - 1) ∣ n := Nat.gcd_dvd_left _ _
    have hgpos : 0 < Nat.gcd n (f.length - 1) := Nat.gcd_pos_of_pos_left _ hn
    rw [← Nat.mul_div_assoc _ hgn]
    set g := Nat.gcd n (f.length - 1)
    obtain ⟨d', hd'⟩ := hg
    rw [hd', Nat.mul_assoc, Nat.mul_div_cancel_left _ hgpos]
    exact dvd_mul_left _ _
  have hd1 : 1 ≤ (toPoly (compShiftPow f c k)).natDegree := by
    rw [hdeg]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hk.ne')
  exact superDecideMobQC_eventually (compShiftPow f c k) hn2 hsqg
    (shiftPow_length hsq.ne_zero c hk) hd1 hnd _ _ (toPoly_shiftPow_ne hD c hk)

/-- **The superelliptic decision procedure.** -/
noncomputable def superDecideFull (f : CPoly ℚ) (n : ℕ) (A : List (CPoly ℚ)) (D : CPoly ℚ)
    (B fuel : ℕ) : Option Bool :=
  if n ≤ 1 then some true
  else
    match superDecideSup f n A D B fuel with
    | some b => some b
    | none => superDecideCoverC f n A D B

/-- **Completeness**: for all large bounds (and any fuel) the procedure answers. -/
theorem superDecideFull_complete (f : CPoly ℚ) (n : ℕ) (hsq : Squarefree (toPoly f))
    (hfd : (toPoly f).natDegree = f.length - 1) (hpd : 0 < f.length - 1) (A : List (CPoly ℚ))
    (D : CPoly ℚ) (hD : toPoly D ≠ 0) :
    ∃ B0, ∀ B fuel, B0 ≤ B → superDecideFull f n A D B fuel ≠ none := by
  by_cases hn : n ≤ 1
  · exact ⟨0, fun B fuel _ ↦ by simp [superDecideFull, hn]⟩
  obtain ⟨B0, hB0⟩ := superDecideCoverC_eventually f (n := n) (by omega) hsq hfd hpd A D hD
  refine ⟨B0, fun B fuel hB ↦ ?_⟩
  unfold superDecideFull
  rw [if_neg hn]
  cases hs : superDecideSup f n A D B fuel with
  | some b => simp
  | none => simpa using hB0 B hB

section Spec

open Differential IntermediateField

universe u

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
  [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **Correctness**: every answer is correct. -/
theorem superDecideFull_spec [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1)
    (f : CPoly ℚ) (n : ℕ) (hsq : Squarefree (toPoly f))
    (hdeg : (toPoly f).natDegree = f.length - 1) (hpd : 0 < f.length - 1)
    (hy : y ^ n = aeval x ((toPoly f).map (algebraMap ℚ Kc)))
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) (A : List (CPoly ℚ)) (D : CPoly ℚ) (hD : toPoly D ≠ 0)
    (B fuel : ℕ) (ans : Bool) (h : superDecideFull f n A D B fuel = some ans) :
    ans = true ↔ HasElementaryIntegral (∑ j ∈ Finset.range n,
      aeval x ((toPoly (A.getD j [])).map (algebraMap ℚ Kc)) /
        aeval x ((toPoly D).map (algebraMap ℚ Kc)) * y ^ j) := by
  unfold superDecideFull at h
  split_ifs at h with hn
  · cases h
    simp only [true_iff]
    interval_cases n
    · simpa using hasElementaryIntegral_of_deriv (0 : E)
    · rw [Finset.sum_range_one, pow_zero, mul_one]
      have hD' : (toPoly D).map (algebraMap ℚ Kc) ≠ 0 :=
        (Polynomial.map_ne_zero_iff (algebraMap ℚ Kc).injective).mpr hD
      have h1 := hasElementaryIntegral_rational_in (R := Kc) hC x hx
        ((toPoly (A.getD 0 [])).map (algebraMap ℚ Kc)) _ hD' 0
      rwa [map_zero, zero_add] at h1
  · have hn0 : 0 < n := by omega
    cases hs : superDecideSup f n A D B fuel with
    | some b =>
      rw [hs] at h
      cases h
      exact superDecideSup_spec hC x y hx f hn0 hsq hdeg hpd hy hgen A D hD B fuel _ hs
    | none =>
      rw [hs] at h
      exact superDecideCoverC_spec hC x y hx f hn0 hy hgen A D B ans h

end Spec

end Sup
