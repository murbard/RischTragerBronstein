import RischTragerBronstein.Jacobian.HypDecideG
import RischTragerBronstein.Jacobian.TorsionDecideR

/-!
# The genus-`g` decision with poles at rational points

As `hypDecideG`, for integrands `(B(x) + ∑ (zᵢ/D) bᵢ/(x − aᵢ)) / y` with `(aᵢ, bᵢ)` rational
points of `y² = f(x)`, `f ∈ ℤ[x]`: the torsion test is `torsionDecideR` (rescaling to an integral
model); the certificate step works over `ℚ` directly. `hypDecideR_spec`: every answer is correct.
-/

open Polynomial CPoly CPoly.Kron EllAlgo

namespace Jac

/-- `Γ₁ = ∑ |zᵢ| (aᵢ, sign zᵢ · bᵢ)` over `ℚ`. -/
def ptsDivR (pts : List (ℚ × ℚ × ℤ)) : EDiv ℚ :=
  pts.map fun q ↦ (q.1, (q.2.2.sign : ℚ) * q.2.1, q.2.2.natAbs)

lemma escale_ptsDivR (pts : List (ℚ × ℚ × ℤ)) (n : ℕ) : escale n (ptsDivR pts) = ptsQ pts n := by
  simp [escale, ptsDivR, ptsQ, Function.comp_def]

lemma edeg_ptsDivR (pts : List (ℚ × ℚ × ℤ)) (n : ℕ) :
    n * edeg (ptsDivR pts) = ((ptsQ pts n).map fun q ↦ q.2.2).sum := by
  rw [← edeg_escale, escale_ptsDivR]; rfl

/-- The gcd of the residue numerators. -/
def zgcd (pts : List (ℚ × ℚ × ℤ)) : ℕ := (pts.map fun q ↦ q.2.2.natAbs).foldr Nat.gcd 0

/-- Residue numerators divided by their gcd (same torsion question, smaller divisors). -/
def ptsNorm (pts : List (ℚ × ℚ × ℤ)) : List (ℚ × ℚ × ℤ) :=
  pts.map fun q ↦ (q.1, q.2.1, q.2.2 / (zgcd pts : ℤ))

lemma zgcd_dvd {pts : List (ℚ × ℚ × ℤ)} {q : ℚ × ℚ × ℤ} (hq : q ∈ pts) :
    (zgcd pts : ℤ) ∣ q.2.2 := by
  have : zgcd pts ∣ q.2.2.natAbs := by
    unfold zgcd
    induction pts with
    | nil => simp at hq
    | cons a l ih =>
      rcases List.mem_cons.mp hq with rfl | h
      · exact Nat.gcd_dvd_left _ _
      · exact (Nat.gcd_dvd_right _ _).trans (ih h)
  exact Int.natCast_dvd.mpr this

lemma zgcd_pos {pts : List (ℚ × ℚ × ℤ)} {q : ℚ × ℚ × ℤ} (hq : q ∈ pts) (hz : q.2.2 ≠ 0) :
    0 < zgcd pts := by
  rcases Nat.eq_zero_or_pos (zgcd pts) with h | h
  · exfalso; have := zgcd_dvd hq; rw [h] at this; simp at this; exact hz this
  · exact h

lemma ptsDivR_norm {pts : List (ℚ × ℚ × ℤ)} (hz : ∀ q ∈ pts, q.2.2 ≠ 0) :
    ptsDivR pts = escale (zgcd pts) (ptsDivR (ptsNorm pts)) := by
  unfold ptsDivR ptsNorm escale
  simp only [List.map_map]
  refine List.map_congr_left fun q hq ↦ ?_
  obtain ⟨k, hk⟩ := zgcd_dvd hq
  have hpos := zgcd_pos hq (hz q hq)
  have hk0 : (0 : ℤ) < zgcd pts := by exact_mod_cast hpos
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  rw [hk, Int.mul_ediv_cancel_left _ hk0.ne', Int.sign_mul, Int.sign_natCast_of_ne_zero hpos.ne',
    one_mul, Int.natAbs_mul, Int.natAbs_natCast]
  exact ⟨rfl, rfl⟩

lemma principalMul_escale_iff {K : Type*} [Field K] {f : K[X]} {g : ℕ} {Γ : EDiv K} {k n : ℕ} :
    PrincipalMul f g (escale k Γ) n ↔ PrincipalMul f g Γ (n * k) := by
  unfold PrincipalMul
  rw [edeg_escale, escale_escale, mul_assoc]

/-- Well-formedness of the data (checked). -/
def wfR (f : List ℤ) (g : ℕ) (pts : List (ℚ × ℚ × ℤ)) : Bool :=
  decide (f.length = 2 * g + 2) && decide (f.getD (2 * g + 1) 0 ≠ 0) &&
    squarefreeCheck (f.map (Int.castRingHom ℚ)) &&
    decide (∀ q ∈ pts, evalC (f.map (Int.castRingHom ℚ)) q.1 = q.2.1 ^ 2 ∧ q.2.1 ≠ 0 ∧
      q.2.2 ≠ 0) &&
    decide ((pts.map Prod.fst).Nodup)

/-- The facts behind `wfR`. -/
structure WFR (f : List ℤ) (g : ℕ) (pts : List (ℚ × ℚ × ℤ)) : Prop where
  hdeg : ((toPoly f).map (Int.castRingHom ℚ)).natDegree = 2 * g + 1
  hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ))
  hon : ∀ q ∈ pts, ((toPoly f).map (Int.castRingHom ℚ)).eval q.1 = q.2.1 ^ 2 ∧ q.2.1 ≠ 0 ∧
    q.2.2 ≠ 0
  hnd : (pts.map Prod.fst).Nodup

variable {f : List ℤ} {g : ℕ} {pts : List (ℚ × ℚ × ℤ)}

lemma wfR_spec (h : wfR f g pts = true) : WFR f g pts := by
  simp only [wfR, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨?_, ?_, fun q hq ↦ ?_, h5⟩
  · rw [natDegree_map_eq_of_injective (RingHom.injective_int _), natDegree_of_list h1 h2]
  · have := squarefreeCheck_sound h3; rwa [toPoly_map_list] at this
  · obtain ⟨e1, e2, e3⟩ := h4 q hq
    exact ⟨by rw [← toPoly_map_list, ← evalC_eq, e1], e2, e3⟩

lemma hΓR (W : WFR f g pts) : ∀ n, ∀ q ∈ escale n (ptsDivR pts), 2 * q.2.1 ≠ 0 ∧
    q.2.1 ^ 2 = (toPoly (f.map (Int.castRingHom ℚ))).eval q.1 := by
  intro n t ht
  obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
  obtain ⟨t'', ht'', rfl⟩ := List.mem_map.mp ht'
  obtain ⟨h1, h2, h3⟩ := W.hon t'' ht''
  have hs : ((t''.2.2.sign : ℤ) : ℚ) ^ 2 = 1 := by
    rcases lt_trichotomy t''.2.2 0 with h | h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
    · exact absurd h h3
    · rw [Int.sign_eq_one_of_pos h]; norm_num
  refine ⟨?_, ?_⟩
  · simp only
    refine mul_ne_zero two_ne_zero (mul_ne_zero (fun h0 ↦ ?_) h2)
    rw [h0] at hs; norm_num at hs
  · simp only
    rw [mul_pow, hs, one_mul, toPoly_map_list, h1]

lemma exists_principalC_of_torsionR (W : WFR f g pts)
    (ht : torsionDecideR f g (ptsDivR (ptsNorm pts)) = some true) :
    ∃ n, 1 ≤ n ∧ (principalC (f.map (Int.castRingHom ℚ)) (escale n (ptsDivR pts))
      (boundA (n * edeg (ptsDivR pts))) (boundB g (n * edeg (ptsDivR pts)))).isSome := by
  obtain ⟨n, hn1, hn⟩ := (torsionDecideR_spec ht).mp rfl
  have hz : ∀ q ∈ pts, q.2.2 ≠ 0 := fun q hq ↦ (W.hon q hq).2.2
  have hon : OnCurve ((toPoly f).map (Int.castRingHom ℚ)) (ptsDivR (ptsNorm pts)) := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    obtain ⟨q'', hq'', rfl⟩ := List.mem_map.mp hq'
    have := hΓR W 1 (q''.1, (q''.2.2.sign : ℚ) * q''.2.1, 1 * q''.2.2.natAbs)
      (List.mem_map.mpr ⟨_, List.mem_map_of_mem hq'', rfl⟩)
    have hk := zgcd_dvd hq''
    have hpos := zgcd_pos hq'' (hz _ hq'')
    obtain ⟨k, hk'⟩ := hk
    have hs : ((q''.2.2 / (zgcd pts : ℤ)).sign : ℚ) = (q''.2.2.sign : ℚ) := by
      rw [hk', Int.mul_ediv_cancel_left _ (by exact_mod_cast hpos.ne'), Int.sign_mul,
        Int.sign_natCast_of_ne_zero hpos.ne', one_mul]
    simp only [hs]
    rw [← toPoly_map_list]
    exact ⟨IsUnit.mk0 _ this.1, this.2⟩
  have hm := hn.mul W.hdeg hon (zgcd pts)
  rw [← principalMul_escale_iff, ← ptsDivR_norm hz] at hm
  refine ⟨n, hn1, ?_⟩
  rw [← toPoly_map_list] at hm
  exact (principalMul_iff_principalC _ g _ (hΓR W) n).mp hm

/-- **The decision procedure** (`none`: ill-formed data). -/
def hypDecideR (f : List ℤ) (g : ℕ) (pts : List (ℚ × ℚ × ℤ)) (B : CPoly ℚ) (D : ℕ) :
    Option Bool :=
  if hw : wfR f g pts = true then
    match ht : torsionDecideR f g (ptsDivR (ptsNorm pts)) with
    | none => none
    | some false => some false
    | some true =>
      let n := Nat.find (exists_principalC_of_torsionR (wfR_spec hw) ht)
      let ΓQ := ptsDivR pts
      let fQ : CPoly ℚ := f.map (Int.castRingHom ℚ)
      match principalC fQ (escale n ΓQ) (boundA (n * edeg ΓQ)) (boundB g (n * edeg ΓQ)) with
      | some jc =>
        let AB := ((jc.2.set jc.1 1).take (boundA (n * edeg ΓQ)),
          (jc.2.set jc.1 1).drop (boundA (n * edeg ΓQ)))
        let cc : ℚ := 1 / ((n : ℚ) * D)
        some (certCheck fQ AB (fracG B D pts) cc &&
          isZero (hypRed fQ (certR fQ AB (fracG B D pts) cc)).2)
      | none => some false
  else none

lemma hypDecideR_wf {B : CPoly ℚ} {D : ℕ} {ans : Bool} (h : hypDecideR f g pts B D = some ans) :
    WFR f g pts := by
  unfold hypDecideR at h
  split_ifs at h with hw
  exact wfR_spec hw

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 3200000 in
/-- **Every answer of `hypDecideR` is correct.** -/
theorem hypDecideR_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    {B : CPoly ℚ} {D : ℕ} (hD : D ≠ 0) {ans : Bool} (h : hypDecideR f g pts B D = some ans)
    (hy : y ^ 2 = aeval x ((toPoly f).map (Int.castRingHom ℚ)))
    (hgen : ∀ z : E, InHyp Kc x y z) :
    ans = true ↔ HasElementaryIntegral ((aeval x (toPoly B) +
      (pts.map fun q ↦ (((q.2.2 : ℚ) / D * q.2.1 : ℚ) : E) /
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
  unfold hypDecideR at h
  split_ifs at h with hw
  have W := wfR_spec hw
  have hpd : (toPoly (f.map (Int.castRingHom ℚ))).natDegree = 2 * g + 1 := by
    rw [hpf]; exact W.hdeg
  have hsqQ : Squarefree (toPoly (f.map (Int.castRingHom ℚ))) := by rw [hpf]; exact W.hsq
  have hy' : y ^ 2 = aeval x (toPoly (f.map (Int.castRingHom ℚ))) := by rw [hpf]; exact hy
  have hon : ∀ q ∈ pts, (toPoly (f.map (Int.castRingHom ℚ))).eval q.1 = q.2.1 ^ 2 ∧
      q.2.1 ≠ 0 ∧ q.2.2 ≠ 0 := fun q hq ↦ by rw [hpf]; exact W.hon q hq
  split at h
  · cases h
  · -- not torsion
    rename_i ht
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.false_eq_true, false_iff]
    intro hel
    have hT := torsionDecideR_spec ht
    simp only [Bool.false_eq_true, false_iff] at hT
    apply hT
    obtain ⟨Λ, hΛ1⟩ := Module.Projective.exists_dual_eq_one ℚ (one_ne_zero : (1 : Kc) ≠ 0)
    set L := pts.length
    let a : Fin L → ℚ := fun i ↦ pts[i].1
    let b : Fin L → ℚ := fun i ↦ pts[i].2.1
    let z : Fin L → ℤ := fun i ↦ pts[i].2.2
    have hmemQ : ∀ i : Fin L, ((a i, b i, z i) : ℚ × ℚ × ℤ) ∈ pts := fun i ↦
      List.getElem_mem _
    have hel' : HasElementaryIntegral ((aeval x ((toPoly B).map (algebraMap ℚ Kc)) +
        ∑ i ∈ (Finset.univ : Finset (Fin L)),
        algebraMap Kc E (algebraMap ℚ Kc ((z i : ℚ) / D) * algebraMap ℚ Kc (b i)) /
          (x - algebraMap Kc E (algebraMap ℚ Kc (a i)))) / y) := by
      convert hel using 3
      · rw [aeval_map_algebraMap]
      · rw [sum_map_eq_fin (M := E)]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp [a, b, z]
    obtain ⟨m, hm1, hm⟩ := hyp_principal_of_elementary hC hCall x y hx (g := g)
      ((toPoly f).map (Int.castRingHom ℚ)) W.hsq W.hdeg hy hgen
      (algebraMap ℚ Kc) Finset.univ a b (fun i _ ↦ (W.hon _ (hmemQ i)).2.1)
      (fun i _ ↦ by
        rw [Algebra.algebraMap_self, Polynomial.map_id, ← (W.hon _ (hmemQ i)).1])
      (by
        intro i _ j _ hij
        have := (List.Nodup.getElem_inj_iff W.hnd (i := i) (j := j)
          (hi := by simp [L]) (hj := by simp [L])).mp (by simpa [a] using hij)
        exact Fin.ext this)
      ((toPoly B).map (algebraMap ℚ Kc)) (fun i ↦ algebraMap ℚ Kc ((z i : ℚ) / D)) hel' Λ z D hD
      (fun i _ ↦ by
        rw [Algebra.algebraMap_eq_smul_one, map_smul, hΛ1, smul_eq_mul, mul_one])
    rw [Algebra.algebraMap_self, Polynomial.map_id] at hm
    have hmem : ∀ q ∈ escale 2 (ptsDivR pts), q ∈ resDiv (Finset.univ : Finset (Fin L)) a b z := by
      intro q hq
      obtain ⟨q1, hq1, rfl⟩ := List.mem_map.mp hq
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq1
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
      unfold resDiv
      refine List.mem_map.mpr ⟨⟨i, hi⟩, List.mem_filter.mpr ⟨Finset.mem_toList.mpr
        (Finset.mem_univ _), by simpa [z] using (W.hon _ (hmemQ ⟨i, hi⟩)).2.2⟩, ?_⟩
      simp [a, b, z]
    have hdeg : edeg (escale 2 (ptsDivR pts)) =
        edeg (resDiv (Finset.univ : Finset (Fin L)) a b z) := by
      rw [edeg_resDiv, edeg_escale]
      simp only [edeg, ptsDivR, List.map_map]
      rw [sum_map_eq_fin (M := ℕ), Finset.mul_sum]
      rfl
    obtain ⟨ψ, h0, hp, hv⟩ := PrincipalMul.congr hmem hdeg hm
    have hP : PrincipalMul ((toPoly f).map (Int.castRingHom ℚ)) g (ptsDivR pts) (m * 2) := by
      refine ⟨ψ, h0, ?_, ?_⟩
      · rw [edeg_escale] at hp; rwa [mul_assoc]
      · rwa [escale_escale] at hv
    rw [ptsDivR_norm (fun q hq ↦ (W.hon q hq).2.2), principalMul_escale_iff] at hP
    rcases pts with _ | ⟨q, l⟩
    · exact ⟨1, le_rfl, (1, 0), by simp, ⟨by simp, Or.inl rfl⟩,
        by simp [Vanishes, escale, ptsDivR, ptsNorm]⟩
    · have hpos := zgcd_pos (pts := q :: l) List.mem_cons_self
        (W.hon q (List.mem_cons_self (l := l))).2.2
      exact ⟨m * 2 * zgcd (q :: l), Nat.one_le_iff_ne_zero.mpr (by positivity), hP⟩
  · -- torsion
    rename_i ht
    obtain ⟨hn1, hsome⟩ := Nat.find_spec (exists_principalC_of_torsionR W ht)
    obtain ⟨jc, hjc⟩ := Option.isSome_iff_exists.mp hsome
    simp only at h
    rw [hjc] at h
    simp only [Option.some.injEq] at h
    subst h
    set n := Nat.find (exists_principalC_of_torsionR W ht) with hn
    set ΓQ := ptsDivR pts
    set full := jc.2.set jc.1 1
    set AB : CPoly ℚ × CPoly ℚ := (full.take (boundA (n * edeg ΓQ)),
      full.drop (boundA (n * edeg ΓQ))) with hABdef
    set cc : ℚ := 1 / ((n : ℚ) * D)
    set p : CPoly ℚ := f.map (Int.castRingHom ℚ)
    obtain ⟨hψ0, hdA, hdB, hvan⟩ := principalC_sound_take p _ _ _ (hΓR W n) hjc
    have hcert : certCheck p AB (fracG B D pts) cc = true := by
      apply certCheck_ok_odd p hpd pts (fun q hq ↦ ⟨(hon q hq).1, (hon q hq).2.1⟩) W.hnd
        D hD n hn1 AB
      · by_contra hc
        push_neg at hc
        exact hψ0 (Prod.ext hc.1 hc.2)
      · rw [← edeg_ptsDivR]; exact poleLE_of_degree_lt hdA hdB
      · intro q hq
        rw [← escale_ptsDivR] at hq
        obtain ⟨h1, h2⟩ := hΓR W n q hq
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
    have hG' : toPoly (fracG B D pts).2 ≠ 0 := by
      intro h0; rw [← Bool.not_eq_true, isZero_iff] at hG; exact hG h0
    have hid := (beq_iff _ _).mp hbeq
    have h2 : toPoly ([2] : CPoly ℚ) = 2 := by
      rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
    simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_smul, toPoly_deriv, h2] at hid
    have hred := ell_log_reduce hC x y hx (toPoly p) hsqQ.ne_zero hy'
      (toPoly (fracG B D pts).1) (toPoly (fracG B D pts).2) (toPoly AB.1)
      (toPoly AB.2) (toPoly (certR p AB (fracG B D pts) cc)) cc hG' hN'
      (by linear_combination hid)
    have hdec := hyp_decides hC hCall x y hx p hsqQ ⟨g, hpd⟩ hy' hgen
      (certR p AB (fracG B D pts) cc)
    obtain ⟨_, hfr⟩ := fracG_spec x hne B D pts
    rw [← hfr, div_div, hred, hdec]

end Spec

end Jac
