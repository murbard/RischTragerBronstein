import RischTragerBronstein.Jacobian.HypCertOdd
import RischTragerBronstein.Jacobian.PrincipalTake
import RischTragerBronstein.Jacobian.AbelHyp

/-!
# A complete decision procedure in any genus (integral poles)

For `y² = f(x)`, `f ∈ ℤ[x]` squarefree of degree `2g + 1`, and integrands

  `(B(x) + ∑ᵢ (zᵢ / D) bᵢ / (x − aᵢ)) / y`,   `aᵢ, bᵢ, zᵢ ∈ ℤ`, `bᵢ² = f(aᵢ)`, `B ∈ ℚ[x]`,

`hypDecideG` decides elementarity (`hypDecideG_iff`):

* if the residue divisor `∑ zᵢ ([Pᵢ] − [σPᵢ])` is not torsion (`torsionDecideU`), the integral is
  not elementary (Abel's direction `hyp_principal_of_elementary`);
* otherwise a function `A + B y` with divisor `n Γ` is computed by `principalC`, the logarithmic
  part `1/(nD) · log(A + B y)` is split off (`certCheck`, valid by `certCheck_ok_odd`), and the
  residue-free remainder is decided by `hypRed` (`hyp_decides`).
-/

open Polynomial CPoly CPoly.Kron EllAlgo

namespace Jac

/-- The points over `ℚ`. -/
def ptsQ' (pts : List (ℤ × ℤ × ℤ)) : List (ℚ × ℚ × ℤ) :=
  pts.map fun t ↦ ((t.1 : ℚ), (t.2.1 : ℚ), t.2.2)

/-- `Γ₁ = ∑ |zᵢ| (aᵢ, sign zᵢ · bᵢ)`. -/
def ptsDiv1 (pts : List (ℤ × ℤ × ℤ)) : EDiv ℤ :=
  pts.map fun t ↦ (t.1, t.2.2.sign * t.2.1, t.2.2.natAbs)

lemma escale_emap_ptsDiv1 (pts : List (ℤ × ℤ × ℤ)) (n : ℕ) :
    escale n (emap (Int.castRingHom ℚ) (ptsDiv1 pts)) = ptsQ (ptsQ' pts) n := by
  simp [escale, emap, ptsDiv1, ptsQ, ptsQ', Function.comp_def]

lemma edeg_ptsDiv1 (pts : List (ℤ × ℤ × ℤ)) (n : ℕ) :
    n * edeg (emap (Int.castRingHom ℚ) (ptsDiv1 pts)) = ((ptsQ (ptsQ' pts) n).map fun q ↦ q.2.2).sum := by
  rw [← edeg_escale, escale_emap_ptsDiv1]; rfl

lemma natDegree_of_list {f : List ℤ} {g : ℕ} (hlen : f.length = 2 * g + 2)
    (hlc : f.getD (2 * g + 1) 0 ≠ 0) : (toPoly f).natDegree = 2 * g + 1 := by
  have hcoef : ∀ n, (toPoly f).coeff n = f.getD n 0 := coeff_toPoly f
  refine le_antisymm ?_ (le_natDegree_of_ne_zero (by rw [hcoef]; exact hlc))
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [hcoef, List.getD_eq_default _ _ (by rw [hlen]; exact_mod_cast hn)]

/-- Degree bounds of `principalC` give the pole bound. -/
lemma poleLE_of_degree_lt {K : Type*} [Field K] {g N : ℕ} {ψ : K[X] × K[X]}
    (hA : ψ.1.degree < boundA N) (hB : ψ.2.degree < boundB g N) : PoleLE g ψ N := by
  refine ⟨?_, ?_⟩
  · have : ψ.1.natDegree < boundA N := by
      by_cases h1 : ψ.1 = 0
      · rw [h1, natDegree_zero]; unfold boundA; omega
      · exact (natDegree_lt_iff_degree_lt h1).mpr hA
    unfold boundA at this; omega
  · by_cases h2 : ψ.2 = 0
    · exact Or.inl h2
    · right
      have := (natDegree_lt_iff_degree_lt h2).mpr hB
      unfold boundB at this; omega

/-- **From branch vanishing to the local check of `certCheck`.** -/
lemma locVal_dvd_of_vanishAt {K : Type*} [Field K] [CharZero K] [DecidableEq K] (pC : CPoly K) (A B : K[X])
    (q : K × K × ℕ) (hy : q.2.1 ≠ 0) (hpα : (toPoly pC).eval q.1 = q.2.1 ^ 2)
    (h : VanishAt (toPoly pC) A B q.1 q.2.1 q.2.2) : X ^ q.2.2 ∣ locVal pC A B q := by
  rcases Nat.eq_zero_or_pos q.2.2 with h0 | h0
  · rw [h0, pow_zero]; exact one_dvd _
  have hbr : IsBranch (toPoly pC) q.1 q.2.1 q.2.2 (toPoly (Yq pC q)) := by
    refine ⟨coeff_zero_sqrtSeries _ _ _, ?_⟩
    have := sqrtSeries_dvd (shiftPoly pC q.1) q.2.1 hy (by
      rw [toPoly_shiftPoly, coeff_zero_eq_eval_zero, eval_comp]; simpa using hpα) q.2.2 h0
    rw [toPoly_shiftPoly] at this
    have := dvd_neg.mpr this
    rwa [neg_sub] at this
  have h2 : IsUnit (2 * q.2.1) := IsUnit.mk0 _ (mul_ne_zero two_ne_zero hy)
  have := h.jet_dvd h2 hbr le_rfl
  simpa [locVal, jet] using this

variable {f : List ℤ} {g : ℕ} {pts : List (ℤ × ℤ × ℤ)}

lemma hΓQ_of_hyp (H : Hyp f g (ptsDiv1 pts)) : ∀ n, ∀ q ∈ escale n (emap (Int.castRingHom ℚ)
    (ptsDiv1 pts)), 2 * q.2.1 ≠ 0 ∧ q.2.1 ^ 2 = (toPoly (f.map (Int.castRingHom ℚ))).eval q.1 := by
  intro n t ht
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
  obtain ⟨t'', ht'', rfl⟩ := List.mem_map.mp ht'
  obtain ⟨h1, h2⟩ := H.hΓ t'' ht''
  refine ⟨?_, ?_⟩
  · show (2 : ℚ) * ((t''.2.1 : ℤ) : ℚ) ≠ 0
    exact_mod_cast mul_ne_zero two_ne_zero h1
  · show ((t''.2.1 : ℤ) : ℚ) ^ 2 = (toPoly (f.map (Int.castRingHom ℚ))).eval
      (Int.castRingHom ℚ t''.1)
    rw [toPoly_map_list, eval_map, eval₂_at_apply, ← evalC_eq, ← h2]; simp

/-- Torsion gives a successful `principalC` search over `ℚ`. -/
lemma exists_principalC_of_torsion (H : Hyp f g (ptsDiv1 pts)) (ht : torsionDecideU H = true) :
    ∃ n, 1 ≤ n ∧ (principalC (f.map (Int.castRingHom ℚ))
      (escale n (emap (Int.castRingHom ℚ) (ptsDiv1 pts)))
      (boundA (n * edeg (emap (Int.castRingHom ℚ) (ptsDiv1 pts))))
      (boundB g (n * edeg (emap (Int.castRingHom ℚ) (ptsDiv1 pts))))).isSome := by
  obtain ⟨n, hn1, hn⟩ := (torsionDecideU_iff H).mp ht
  refine ⟨n, hn1, ?_⟩
  rw [← toPoly_map_list] at hn
  exact (principalMul_iff_principalC _ g _ (hΓQ_of_hyp H) n).mp hn

/-- **The decision procedure.** -/
def hypDecideG (H : Hyp f g (ptsDiv1 pts)) (B : CPoly ℚ) (D : ℕ) : Bool :=
  if ht : torsionDecideU H = true then
    let n := Nat.find (exists_principalC_of_torsion H ht)
    let ΓQ := emap (Int.castRingHom ℚ) (ptsDiv1 pts)
    let fQ : CPoly ℚ := f.map (Int.castRingHom ℚ)
    match principalC fQ (escale n ΓQ) (boundA (n * edeg ΓQ)) (boundB g (n * edeg ΓQ)) with
    | some jc =>
      let AB := ((jc.2.set jc.1 1).take (boundA (n * edeg ΓQ)),
        (jc.2.set jc.1 1).drop (boundA (n * edeg ΓQ)))
      let cc : ℚ := 1 / ((n : ℚ) * D)
      certCheck fQ AB (fracG B D (ptsQ' pts)) cc &&
        isZero (hypRed fQ (certR fQ AB (fracG B D (ptsQ' pts)) cc)).2
    | none => false
  else false

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

lemma ptsQ'_facts (H : Hyp f g (ptsDiv1 pts)) :
    (∀ q ∈ ptsQ' pts, (toPoly (f.map (Int.castRingHom ℚ))).eval q.1 = q.2.1 ^ 2 ∧ q.2.1 ≠ 0 ∧
      q.2.2 ≠ 0) ∧ ((ptsQ' pts).map Prod.fst).Nodup := by
  refine ⟨fun q hq ↦ ?_, ?_⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq
    obtain ⟨h1, h2⟩ := H.hΓ (t.1, t.2.2.sign * t.2.1, t.2.2.natAbs)
      (List.mem_map_of_mem (f := fun t : ℤ × ℤ × ℤ ↦ (t.1, t.2.2.sign * t.2.1, t.2.2.natAbs)) ht)
    have hz : t.2.2 ≠ 0 := fun h0 ↦ h1 (by simp [h0])
    have hb : t.2.1 ≠ 0 := fun h0 ↦ h1 (by simp [h0])
    have hs : t.2.2.sign ^ 2 = 1 := by
      rcases lt_trichotomy t.2.2 0 with h | h | h
      · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
      · exact absurd h hz
      · rw [Int.sign_eq_one_of_pos h]; norm_num
    refine ⟨?_, by show ((t.2.1 : ℤ) : ℚ) ≠ 0; exact_mod_cast hb, hz⟩
    rw [toPoly_map_list, eval_map, show ((t.1 : ℤ) : ℚ) = Int.castRingHom ℚ t.1 from rfl,
      eval₂_at_apply, ← evalC_eq]
    simp only at h2
    rw [← h2, mul_pow, hs, one_mul]; simp
  · have := H.hΓd
    simp only [ptsDiv1, List.pairwise_map] at this
    simp only [ptsQ', List.map_map, List.Nodup, List.pairwise_map, Function.comp_def]
    exact this.imp fun h he ↦ h (by exact_mod_cast he)

set_option maxHeartbeats 3200000 in
/-- **Correctness and completeness of `hypDecideG`.** -/
theorem hypDecideG_iff (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (H : Hyp f g (ptsDiv1 pts)) (B : CPoly ℚ) (D : ℕ) (hD : D ≠ 0)
    (hy : y ^ 2 = aeval x ((toPoly f).map (Int.castRingHom ℚ)))
    (hgen : ∀ z : E, InHyp Kc x y z) :
    hypDecideG H B D = true ↔ HasElementaryIntegral ((aeval x (toPoly B) +
      ((ptsQ' pts).map fun q ↦ (((q.2.2 : ℚ) / D * q.2.1 : ℚ) : E) /
        (x - ((q.1 : ℚ) : E))).sum) / y) := by
  classical
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hP ↦ by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hP)
  have hpf : toPoly (f.map (Int.castRingHom ℚ)) = (toPoly f).map (Int.castRingHom ℚ) :=
    toPoly_map_list _ _
  have hdegZ := natDegree_of_list H.hlen H.hlc
  have hpd : (toPoly (f.map (Int.castRingHom ℚ))).natDegree = 2 * g + 1 := by
    rw [hpf, natDegree_map_eq_of_injective (RingHom.injective_int _), hdegZ]
  have hsqQ : Squarefree (toPoly (f.map (Int.castRingHom ℚ))) := by rw [hpf]; exact H.hsq
  have hy' : y ^ 2 = aeval x (toPoly (f.map (Int.castRingHom ℚ))) := by rw [hpf]; exact hy
  obtain ⟨hon, hnd⟩ := ptsQ'_facts H
  unfold hypDecideG
  split_ifs with ht
  · obtain ⟨hn1, hsome⟩ := Nat.find_spec (exists_principalC_of_torsion H ht)
    obtain ⟨jc, hjc⟩ := Option.isSome_iff_exists.mp hsome
    dsimp only
    rw [hjc]
    dsimp only
    set n := Nat.find (exists_principalC_of_torsion H ht) with hn
    set ΓQ := emap (Int.castRingHom ℚ) (ptsDiv1 pts)
    set full := jc.2.set jc.1 1
    set AB : CPoly ℚ × CPoly ℚ := (full.take (boundA (n * edeg ΓQ)),
      full.drop (boundA (n * edeg ΓQ))) with hABdef
    set cc : ℚ := 1 / ((n : ℚ) * D)
    set p : CPoly ℚ := f.map (Int.castRingHom ℚ)
    obtain ⟨hψ0, hdA, hdB, hvan⟩ := principalC_sound_take p _ _ _ (hΓQ_of_hyp H n) hjc
    have hcert : certCheck p AB (fracG B D (ptsQ' pts)) cc = true := by
      apply certCheck_ok_odd p hpd (ptsQ' pts) (fun q hq ↦ ⟨(hon q hq).1, (hon q hq).2.1⟩) hnd
        D hD n hn1 AB
      · by_contra hc
        push_neg at hc
        exact hψ0 (Prod.ext hc.1 hc.2)
      · rw [← edeg_ptsDiv1]; exact poleLE_of_degree_lt hdA hdB
      · intro q hq
        rw [← escale_emap_ptsDiv1] at hq
        obtain ⟨h1, h2⟩ := hΓQ_of_hyp H n q hq
        exact locVal_dvd_of_vanishAt _ _ _ q (fun h0 ↦ h1 (by rw [h0, mul_zero])) h2.symm
          (hvan q hq)
    rw [hcert, Bool.true_and]
    have hcert' := hcert
    unfold certCheck at hcert'
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, certN, certM] at hcert'
    obtain ⟨⟨hN, hG⟩, hbeq⟩ := hcert'
    have hN' : toPoly AB.1 ^ 2 - toPoly AB.2 ^ 2 * toPoly p ≠ 0 := by
      intro h0; rw [← Bool.not_eq_true, isZero_iff] at hN; apply hN
      simp only [toPoly_sub, toPoly_mul]; linear_combination h0
    have hG' : toPoly (fracG B D (ptsQ' pts)).2 ≠ 0 := by
      intro h0; rw [← Bool.not_eq_true, isZero_iff] at hG; exact hG h0
    have hid := (beq_iff _ _).mp hbeq
    have h2 : toPoly ([2] : CPoly ℚ) = 2 := by
      rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
    simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_smul, toPoly_deriv, h2] at hid
    have hred := ell_log_reduce hC x y hx (toPoly p) hsqQ.ne_zero hy'
      (toPoly (fracG B D (ptsQ' pts)).1) (toPoly (fracG B D (ptsQ' pts)).2) (toPoly AB.1)
      (toPoly AB.2) (toPoly (certR p AB (fracG B D (ptsQ' pts)) cc)) cc hG' hN'
      (by linear_combination hid)
    have hdec := hyp_decides hC hCall x y hx p hsqQ ⟨g, hpd⟩ hy' hgen
      (certR p AB (fracG B D (ptsQ' pts)) cc)
    obtain ⟨_, hfr⟩ := fracG_spec x hne B D (ptsQ' pts)
    rw [← hfr, div_div, hred, hdec]
  · simp only [false_iff]
    intro hel
    apply ht
    rw [torsionDecideU_iff]
    obtain ⟨Λ, hΛ1⟩ := Module.Projective.exists_dual_eq_one ℚ (one_ne_zero : (1 : Kc) ≠ 0)
    set L := pts.length
    let a : Fin L → ℚ := fun i ↦ (pts[i].1 : ℚ)
    let b : Fin L → ℚ := fun i ↦ (pts[i].2.1 : ℚ)
    let z : Fin L → ℤ := fun i ↦ pts[i].2.2
    have hmemQ : ∀ i : Fin L, ((a i, b i, z i) : ℚ × ℚ × ℤ) ∈ ptsQ' pts := fun i ↦
      List.mem_map.mpr ⟨pts[i], List.getElem_mem _, rfl⟩
    have hel' : HasElementaryIntegral ((aeval x ((toPoly B).map (algebraMap ℚ Kc)) +
        ∑ i ∈ (Finset.univ : Finset (Fin L)),
        algebraMap Kc E (algebraMap ℚ Kc ((z i : ℚ) / D) * algebraMap ℚ Kc (b i)) /
          (x - algebraMap Kc E (algebraMap ℚ Kc (a i)))) / y) := by
      convert hel using 3
      · rw [aeval_map_algebraMap]
      · rw [ptsQ', List.map_map, sum_map_eq_fin (M := E)]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp [a, b, z]
    obtain ⟨m, hm1, hm⟩ := hyp_principal_of_elementary hC hCall x y hx (g := g)
      ((toPoly f).map (Int.castRingHom ℚ)) H.hsq (by
        rw [natDegree_map_eq_of_injective (RingHom.injective_int _), hdegZ]) hy hgen
      (algebraMap ℚ Kc) Finset.univ a b (fun i _ ↦ (hon _ (hmemQ i)).2.1)
      (fun i _ ↦ by
        rw [Algebra.algebraMap_self, Polynomial.map_id, ← (hon _ (hmemQ i)).1, hpf])
      (by
        intro i _ j _ hij
        have := (List.Nodup.getElem_inj_iff hnd (i := i) (j := j)
          (hi := by simp [ptsQ', L]) (hj := by simp [ptsQ', L])).mp (by simpa [ptsQ', a] using hij)
        exact Fin.ext this)
      ((toPoly B).map (algebraMap ℚ Kc)) (fun i ↦ algebraMap ℚ Kc ((z i : ℚ) / D)) hel' Λ z D hD
      (fun i _ ↦ by
        rw [Algebra.algebraMap_eq_smul_one, map_smul, hΛ1, smul_eq_mul, mul_one])
    rw [Algebra.algebraMap_self, Polynomial.map_id] at hm
    set ΓQ := emap (Int.castRingHom ℚ) (ptsDiv1 pts)
    have hmem : ∀ q ∈ escale 2 ΓQ, q ∈ resDiv (Finset.univ : Finset (Fin L)) a b z := by
      intro q hq
      obtain ⟨q1, hq1, rfl⟩ := List.mem_map.mp hq
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq1
      obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht'
      unfold resDiv
      refine List.mem_map.mpr ⟨⟨i, hi⟩, List.mem_filter.mpr ⟨Finset.mem_toList.mpr
        (Finset.mem_univ _), by simpa [z] using (hon _ (hmemQ ⟨i, hi⟩)).2.2⟩, ?_⟩
      simp [a, b, z]
    have hdeg : edeg (escale 2 ΓQ) = edeg (resDiv (Finset.univ : Finset (Fin L)) a b z) := by
      rw [edeg_resDiv, edeg_escale, edeg_emap]
      simp only [edeg, ptsDiv1, List.map_map]
      rw [sum_map_eq_fin (M := ℕ), Finset.mul_sum]
      rfl
    obtain ⟨ψ, h0, hp, hv⟩ := PrincipalMul.congr hmem hdeg hm
    refine ⟨m * 2, by omega, ψ, h0, ?_, ?_⟩
    · rw [edeg_escale] at hp; rwa [mul_assoc]
    · rwa [escale_escale] at hv

end Spec

end Jac
