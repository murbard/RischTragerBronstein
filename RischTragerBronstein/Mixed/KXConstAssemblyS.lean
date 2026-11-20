import RischTragerBronstein.Mixed.KXConstAssembly
import RischTragerBronstein.Mixed.KXConstSearchS

/-!
# Constant curves at the levels `m + 1`: side conditions and the decision

`const_sideS`: the side conditions of `kxMWSearchCKS_of` / `kxMWSearchTKS_of` from the data.
-/

open Polynomial Differential IntermediateField Classical

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

set_option maxHeartbeats 4000000 in
/-- **The side conditions of the level-`m + 1` constant-curve searches**, from the data. -/
theorem const_sideS (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (m : ℕ) (hn : T.n = m + 2) (hc : certC Fc ks lv (m + 2) = true) {g : LC (m + 1)}
    (hk : ks (m + 1) = .exp g)
    (A : GPoly (LC (m + 1))) (hsqc : GPoly.squarefreeCheck (MO Fc ks (m + 1)) A = true)
    (hdeg3 : degG (MO Fc ks (m + 1)) A = 3)
    (B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1))) (hok : kxOK Fc ks (m + 1) A B kt l cs = true)
    (hcst : kxConst Fc ks (m + 1) g A B kt l cs = true) (hrep : kxRepOK Fc ks (m + 1) g A B kt l cs = true)
    (c0f : CPoly ℚ) (hFc : Fc = [c0f, [1]])
    (hAw : ∀ a ∈ A, WFm (MO Fc ks m) a) (hBw : ∀ b ∈ B, WFm (MO Fc ks m) b)
    (hcsw : ∀ c ∈ cs, WFm (MO Fc ks m) c) (hgw : WFm (MO Fc ks m) g)
    (r : ℕ → ℚ) (hr : ∀ i < 4, T.ev (m + 1) (aCS Fc ks m A i) = (r i : L))
    (z : LC (m + 1)) (hz : kxZ Fc ks lv (m + 1) A = some z) (h0 : T.Tr (m + 1))
    (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length) :
    (∀ i < 4, okS (Fc := Fc) m (aCS Fc ks m A i) = true) ∧
    (∀ b ∈ B, okS (Fc := Fc) m b = true) ∧
    (∀ q < cs.length, okS (Fc := Fc) m (kqC Fc ks (m + 1) cs q) = true) ∧
    (∀ q < cs.length, okS (Fc := Fc) m (kxD Fc ks (m + 1) g cs q) = true) ∧
    (∀ i < 4, T.val (m + 1) (aCS Fc ks m A i) = (r i : T.F (m + 1))) ∧
    (∀ q < cs.length, (GPoly.toPoly (T.MP (m + 1) h0) B).eval (T.val (m + 1) (kqC Fc ks (m + 1) cs q)) ≠ 0) ∧
    kxKap Fc ks (m + 1) A z ≠ 0 ∧ sTS Fc ks m g A B kt l cs k ≠ 0 ∧
    T.val (m + 1) z ^ 2 * T.val (m + 1) (aCS Fc ks m A 0) = (kxKap Fc ks (m + 1) A z : T.F (m + 1)) ∧
    mGS Fc ks m g A B kt l cs k ≠ 0 ∧
    4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
      27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2 ≠ 0 := by
  have MS := T.mspecs hmon hdeg lv (m + 2) (by omega) hc
  have hvL : ∀ q : LC (m + 1), ((T.val (m + 1) q : T.F (m + 1)) : L) = T.ev (m + 1) q := fun q ↦ by
    rw [← T.sem_MP_F (m + 1) h0, T.sem_MP (m + 1) h0]
  have hok0 := T.kxOK_spec (m + 1) h0 A B kt l cs hok
  have ha0 : (MO Fc ks (m + 1)).isZero (A.getD 0 (MO Fc ks (m + 1)).zero) = false := by
    cases h : (MO Fc ks (m + 1)).isZero (A.getD 0 (MO Fc ks (m + 1)).zero)
    · rfl
    · exact absurd (((T.MP (m + 1) h0).isZero_iff _).mp h) hok0.1
  obtain ⟨q1, hq1⟩ := kxZ_some hz
  obtain ⟨-, hzκ, hκ0⟩ := T.ke_z_facts hmon hdeg (m + 1) hn hc A ha0 q1 z hq1
  have hr' : ∀ i < 4, T.val (m + 1) (aCS Fc ks m A i) = (r i : T.F (m + 1)) := fun i hi ↦
    Subtype.ext (by rw [hvL, hr i hi]; simp)
  -- the multiplicity gcd
  have hmG : mGS Fc ks m g A B kt l cs k ≠ 0 := by
    obtain ⟨q0, hq0, hq0T⟩ := kxCls_mem_rep (Fc := Fc) (ks := ks) (m + 1) g A B kt l cs _
      (List.getElem_mem (n := (k : ℕ)) k.2)
    have hm0 : kxMNm Fc ks (m + 1) g A B kt l cs q0 ≠ 0 := by
      intro h0'
      obtain ⟨-, hκ, hc0'⟩ := kxRep_spec (Fc := Fc) (ks := ks) (m + 1) g A B kt l cs hrep q0 hq0
      have hm := kxMNm_eq (Fc := Fc) (ks := ks) (m + 1) g A B kt l cs q0 hq0 hc0'
      rw [h0', Nat.cast_zero, eq_comm, mul_eq_zero] at hm
      rcases hm with h | h
      · exact (kxDenM_pos (Fc := Fc) (ks := ks) (m + 1) g A B kt l cs).ne' (by exact_mod_cast h)
      · rw [h] at hκ; simp at hκ
        exact T.kxK_ne (m + 1) MS.hyp hk A B kt l cs hok hcst q0 hq0 hκ
    intro h0'
    have := foldr_gcd_zero _ h0' (mKcS Fc ks m g A B kt l cs k q0)
      (List.mem_map.mpr ⟨q0, List.mem_range.mpr hq0, rfl⟩)
    unfold mKcS at this
    rw [if_pos (by rw [List.getD_eq_getElem _ _ k.2, hq0T]; exact beq_self_eq_true _)] at this
    exact hm0 (by exact_mod_cast this)
  -- the discriminant
  have hdisc : 4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
      27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2 ≠ 0 := by
    set P := GPoly.toPoly (T.MP (m + 1) h0) A with hP
    have hdeg3' : P.natDegree = 3 := by rw [hP, ← degG_eq (T.MP (m + 1) h0) A, hdeg3]
    have hcf : ∀ i < 4, P.coeff i = (r i : T.F (m + 1)) := fun i hi ↦ by
      rw [hP, Tower.PrimN.coeff_toPoly_getD, T.sem_MP_F (m + 1) h0]; exact hr' i hi
    have hPc := MTower.cubic_eq P hdeg3'
    rw [hcf 3 (by norm_num), hcf 2 (by norm_num), hcf 1 (by norm_num), hcf 0 (by norm_num)] at hPc
    have hsq := GPoly.squarefreeCheck_sound (T.MP (m + 1) h0) hsqc
    rw [← hP, hPc] at hsq
    have hP0 : P ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hdeg3'; omega
    have hc3 : ((r 3 : ℚ) : T.F (m + 1)) ≠ 0 := by
      rw [← hcf 3 (by norm_num)]
      have := leadingCoeff_ne_zero.mpr hP0
      rwa [leadingCoeff, hdeg3'] at this
    have hF := CubicDisc.short_disc_ne_zero _ _ _ _ hc3 hsq
    intro h
    apply hF
    have := congrArg (fun x : ℚ ↦ (x : T.F (m + 1))) h
    push_cast at this
    linear_combination this
  have hTm : T.Tr m := h0.of_succ
  refine ⟨fun i _ ↦ T.okS_of_WFm m hTm _ (T.WFm_getD m hTm A hAw i),
    fun b hb ↦ T.okS_of_WFm m hTm _ (hBw b hb),
    fun q _ ↦ T.okS_of_WFm m hTm _ (T.WFm_getD m hTm cs hcsw q),
    fun q _ ↦ T.okS_of_WFm m hTm _ (T.WFm_kxD m hTm g cs hgw hcsw q), hr',
    fun q hq ↦ ?_, hκ0, prodSub_ne _ (kxGens_spec (Fc := Fc) (ks := ks) (m + 1) g A B kt l cs).2 _,
    Subtype.ext ?_, hmG, hdisc⟩
  · rw [← T.sem_MP_F (m + 1) h0]; exact (hok0.2 q hq).2.2.2
  · push_cast; rw [hvL, hvL]; exact hzκ

end MTower

/-- **`kxDecideDL` at level `m + 1`, then the constant-curve certificate searches.** -/
def kxDecideDKS (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
    (lv : (m : ℕ) → LC m) (m : ℕ) (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ)
    (cs : List (LC (m + 1)))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ) : Option Bool :=
  match kxDecideDL Fc ks lv (m + 1) g A B kt l cs ps bound rs nmax with
  | some b => some b
  | none =>
    if kxMWOKCKS Fc ks lv m g A B kt l cs kmax then some false
    else if kxMWOKTKS Fc ks lv m g A B kt l cs kmax then some false else none

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The level-`m + 1` constant-curve branch proves non-elementarity.** -/
theorem not_elementary_of_MWOKCKS (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 2) (hc : certC Fc ks lv (m + 2) = true) {g : LC (m + 1)}
    (hk : ks (m + 1) = .exp g)
    (A : GPoly (LC (m + 1))) (hsqc : GPoly.squarefreeCheck (MO Fc ks (m + 1)) A = true)
    (hdegpos : 0 < degG (MO Fc ks (m + 1)) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks (m + 1)) A))
    (θ : L) (hθ : θ ^ 2 = T.evP (m + 1) A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 2)) {θ})
    (B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1))) (kmax : ℕ)
    (hok : kxMWOKCKS Fc ks lv m g A B kt l cs kmax = true) :
    ¬ HasElementaryIntegral (T.ev (m + 2) ((B, kxDen Fc ks (m + 1) A kt l cs) : LC (m + 2)) * θ) := by
  simp only [kxMWOKCKS, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨hFc, hdeg3⟩, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hok
  unfold kxMWSearchCKS at hq
  split at hq
  · exact absurd hq (by decide)
  rename_i z hz
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne] at hq
  obtain ⟨kc, hkc, hδ, mm, -, kk, -, hchk⟩ := hq
  have : Fact (¬ IsSquare (Rat.cast (sTS Fc ks m g A B kt l cs kc * kxKap Fc ks (m + 1) A z) :
      KF Fc m)) :=
    ⟨not_isSquare_KF_sqOK Fc hFc _ (not_isSquare_of_sqrt hδ) m⟩
  exact T.kx_not_elementary_mwC hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen
    B kt l cs hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
      intro cC xC βC hns hns0 N hN μ
      have h := TE.grp_of_chkCKS m g A B kt l cs _ _ _ _ _ kk _ _ hTm ⟨kc, hkc⟩ hchk rtsF hrl
        hrs b₀ hb₀ hns hns0 N hN μ
      convert h using 3)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The level-`m + 1` same-class constant-curve branch proves non-elementarity.** -/
theorem not_elementary_of_MWOKTKS (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 2) (hc : certC Fc ks lv (m + 2) = true) {g : LC (m + 1)}
    (hk : ks (m + 1) = .exp g)
    (A : GPoly (LC (m + 1))) (hsqc : GPoly.squarefreeCheck (MO Fc ks (m + 1)) A = true)
    (hdegpos : 0 < degG (MO Fc ks (m + 1)) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks (m + 1)) A))
    (θ : L) (hθ : θ ^ 2 = T.evP (m + 1) A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 2)) {θ})
    (B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1))) (kmax : ℕ)
    (hokT : kxMWOKTKS Fc ks lv m g A B kt l cs kmax = true) :
    ¬ HasElementaryIntegral (T.ev (m + 2) ((B, kxDen Fc ks (m + 1) A kt l cs) : LC (m + 2)) * θ) := by
  simp only [kxMWOKTKS, Bool.and_eq_true, beq_iff_eq] at hokT
  obtain ⟨⟨⟨⟨hdeg3, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hokT
  unfold kxMWSearchTKS at hq
  split at hq
  · exact absurd hq (by decide)
  rename_i z hz
  simp only [List.any_eq_true, List.mem_range] at hq
  obtain ⟨kc, hkc, mm, -, kk, -, hchk⟩ := hq
  exact T.kx_not_elementary_mwC hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen
    B kt l cs hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
      intro cC xC βC hns hns0 N hN μ
      have h := TE.grp_of_chkTKS m g A B kt l cs _ _ _ _ kk _ _ _ hTm ⟨kc, hkc⟩ hchk rtsF hrl
        hrs b₀ hb₀ hns hns0 N hN μ
      convert h using 3)

/-- **`kxDecideDKS` is correct.** -/
theorem kxDecideDKS_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (m : ℕ) (hn : T.n = m + 2) (hc : certC Fc ks lv (m + 2) = true) {g : LC (m + 1)}
    (hk : ks (m + 1) = .exp g)
    (A : GPoly (LC (m + 1))) (hsqc : GPoly.squarefreeCheck (MO Fc ks (m + 1)) A = true)
    (hdegpos : 0 < degG (MO Fc ks (m + 1)) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks (m + 1)) A))
    (θ : L) (hθ : θ ^ 2 = T.evP (m + 1) A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 2)) {θ})
    (B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1))) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (nmax kmax : ℕ) (b : Bool)
    (hdec : kxDecideDKS Fc ks lv m g A B kt l cs ps bound rs nmax kmax = some b) :
    HasElementaryIntegral (T.ev (m + 2) ((B, kxDen Fc ks (m + 1) A kt l cs) : LC (m + 2)) * θ) ↔ b = true := by
  unfold kxDecideDKS at hdec
  cases hD : kxDecideDL Fc ks lv (m + 1) g A B kt l cs ps bound rs nmax with
  | some b' =>
    rw [hD] at hdec
    cases hdec
    exact T.kxDecideDL_correct hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps bound
      rs nmax _ hD
  | none =>
    rw [hD] at hdec
    simp only at hdec
    split_ifs at hdec with hK hTK
    · cases hdec
      exact iff_of_false (T.not_elementary_of_MWOKCKS hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ
        hgen B kt l cs kmax hK) (by decide)
    · cases hdec
      exact iff_of_false (T.not_elementary_of_MWOKTKS hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ
        hgen B kt l cs kmax hTK) (by decide)

/-- Once a constant-curve search succeeds, `kxDecideDKS` answers. -/
lemma kxDecideDKS_isSome_of (m : ℕ) (g : LC (m + 1)) (A B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ)
    (h : kxMWOKCKS Fc ks lv m g A B kt l cs kmax = true ∨
      kxMWOKTKS Fc ks lv m g A B kt l cs kmax = true) :
    (kxDecideDKS Fc ks lv m g A B kt l cs ps bound rs nmax kmax).isSome := by
  unfold kxDecideDKS
  rcases kxDecideDL Fc ks lv (m + 1) g A B kt l cs ps bound rs nmax with _ | b
  · dsimp only
    rcases h with h | h
    · rw [if_pos h]; rfl
    · split_ifs <;> rfl
  · rfl

end MTower

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

set_option maxHeartbeats 16000000 in
/-- **Constant curves at the levels `m + 1` are decided.** For a cubic `A` with rational coefficients over a linear base
(well-formed codes), at suitable residues, for every large bound there is `N₀` such that for every
relation bound `nmax ≥ N₀` there is `K₀` such that for every height level `kmax ≥ K₀`,
`kxDecideDKS` answers, and correctly. -/
theorem kxDecideDKS_decides (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (m : ℕ) (hn : T.n = m + 2) (hc : certC Fc ks lv (m + 2) = true) {g : LC (m + 1)}
    (hk : ks (m + 1) = .exp g)
    (A : GPoly (LC (m + 1))) (hsqc : GPoly.squarefreeCheck (MO Fc ks (m + 1)) A = true)
    (hdegpos : 0 < degG (MO Fc ks (m + 1)) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks (m + 1)) A))
    (hdeg3 : degG (MO Fc ks (m + 1)) A = 3)
    (θ : L) (hθ : θ ^ 2 = T.evP (m + 1) A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 2)) {θ})
    (B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1))) (hr0 : cs.length ≠ 0)
    (hok : kxOK Fc ks (m + 1) A B kt l cs = true)
    (hrep : kxConst Fc ks (m + 1) g A B kt l cs = true → kxRepOK Fc ks (m + 1) g A B kt l cs = true)
    (c0f : CPoly ℚ) (hFc : Fc = [c0f, [1]])
    (hAw : ∀ a ∈ A, WFm (MO Fc ks m) a) (hBw : ∀ b ∈ B, WFm (MO Fc ks m) b)
    (hcsw : ∀ c ∈ cs, WFm (MO Fc ks m) c) (hgw : WFm (MO Fc ks m) g)
    (r : ℕ → ℚ) (hr : ∀ i < 4, T.ev (m + 1) (aCS Fc ks m A i) = (r i : L)) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd → ∃ N0, ∀ nmax, N0 ≤ nmax → ∃ K0, ∀ kmax, K0 ≤ kmax →
      ∃ b, kxDecideDKS Fc ks lv m g A B kt l cs (primesBelow Bd) Bd rs nmax kmax = some b ∧
        (HasElementaryIntegral (T.ev (m + 2) ((B, kxDen Fc ks (m + 1) A kt l cs) : LC (m + 2)) * θ) ↔ b = true) := by
  obtain ⟨rs, B0, hdec⟩ := T.kxDecideL_decides' hmon hdeg (m + 1) hn hc hk A hsqc hdegpos hcop B kt l cs
    hr0 hok hrep
  refine ⟨rs, B0, fun Bd hBd ↦ ?_⟩
  suffices h : ∃ N0, ∀ nmax, N0 ≤ nmax → ∃ K0, ∀ kmax, K0 ≤ kmax →
      (kxDecideDKS Fc ks lv m g A B kt l cs (primesBelow Bd) Bd rs nmax kmax).isSome by
    obtain ⟨N0, h⟩ := h
    refine ⟨N0, fun nmax hnm ↦ ?_⟩
    obtain ⟨K0, hK⟩ := h nmax hnm
    refine ⟨K0, fun kmax hkm ↦ ?_⟩
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hK kmax hkm)
    exact ⟨b, hb, T.kxDecideDKS_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs
      _ _ rs nmax kmax b hb⟩
  have hDL : ∀ nmax kmax,
      (kxDecideDL Fc ks lv (m + 1) g A B kt l cs (primesBelow Bd) Bd rs nmax).isSome →
      (kxDecideDKS Fc ks lv m g A B kt l cs (primesBelow Bd) Bd rs nmax kmax).isSome := by
    intro nmax kmax h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
    unfold kxDecideDKS; rw [hb]; rfl
  rcases hdec Bd hBd with h1 | ⟨⟨z, hz, ht0, -⟩, hallS, hcst⟩
  · refine ⟨0, fun nmax _ ↦ ⟨0, fun kmax _ ↦ hDL nmax kmax ?_⟩⟩
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h1
    unfold kxDecideDL
    rw [hb]; rfl
  have MS := T.mspecs hmon hdeg lv (m + 2) (by omega) hc
  have hTr : T.Tr (m + 2) := MS.hyp.tr
  have hTm : T.Tr (m + 1) := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP (m + 1) hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP (m + 1) hTm) A).natDegree = degG (MO Fc ks (m + 1)) A :=
    (degG_eq (T.MP (m + 1) hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP (m + 1) hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP (m + 1) hTm) A).natDegree := by rw [hdeg1]; exact hcop
  have hrep' := hrep hcst
  have hok0 := T.kxOK_spec (m + 1) hTm A B kt l cs hok
  have ha0 : (MO Fc ks (m + 1)).isZero (A.getD 0 (MO Fc ks (m + 1)).zero) = false := by
    cases h : (MO Fc ks (m + 1)).isZero (A.getD 0 (MO Fc ks (m + 1)).zero)
    · rfl
    · exact absurd (((T.MP (m + 1) hTm).isZero_iff _).mp h) hok0.1
  have hg0 := (kxGens_spec (Fc := Fc) (ks := ks) (m + 1) g A B kt l cs).2
  obtain ⟨q0, hq0⟩ := kxZ_some hz
  obtain ⟨-, -, hκ0⟩ := T.ke_z_facts hmon hdeg (m + 1) hn hc A ha0 q0 z hq0
  have hκs : ∀ κ' ∈ kxKap Fc ks (m + 1) A z :: kxGens Fc ks (m + 1) g A B kt l cs, κ' ≠ 0 := fun κ' h ↦ by
    rcases List.mem_cons.mp h with rfl | h
    · exact hκ0
    · exact hg0 κ' h
  -- a realization with the square roots
  obtain ⟨E, _, _, _, TE, ψ, rts0, hTEn, hev, hevP, hrl0, hrts0⟩ := T.lift_sqrts _ hκs
  obtain ⟨s, rts, hs2, hs', hrl, hrts⟩ := roots_cons _ _ rts0 hrl0 hrts0
  have hTEn1 : TE.n = m + 2 := by rw [hTEn, hn]
  set θE := ψ θ with hθEdef
  have hθE : θE ^ 2 = TE.evP (m + 1) A := by rw [hevP, ← map_pow, hθ]
  have MSE := TE.mspecs hmon hdeg lv (m + 2) (by omega) hc
  have hTrE : TE.Tr (m + 2) := MSE.hyp.tr
  have hsqE := GPoly.squarefreeCheck_sound (TE.MP (m + 1) hTrE.of_succ) hsqc
  have hdegAE : 0 < (GPoly.toPoly (TE.MP (m + 1) hTrE.of_succ) A).natDegree := by
    rw [← degG_eq (TE.MP (m + 1) hTrE.of_succ) A]; exact hdegpos
  obtain ⟨rtsF, hFl, hFv⟩ := TE.roots_F (m + 1) rts (fun i hi ↦ (hrts i hi (by omega)).2)
  have hrlF : rtsF.length = (kxGens Fc ks (m + 1) g A B kt l cs).length := by rw [hFl, hrl]
  have hrsF : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks (m + 1) g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks (m + 1) g A B kt l cs)[i] : TE.F (m + 1)) := fun i hi hi' ↦ Subtype.ext (by
    rw [IntermediateField.coe_pow, hFv i hi (by omega), (hrts i (by omega) hi').1]; simp)
  set cls := kxCls Fc ks (m + 1) g A B kt l cs with hcls
  have hDI := fun (k : Fin cls.length) htk ↦ TE.kx_dep_or_indep hmon hdeg (m + 1) hTEn1 hc hk A hsqc
    hdegpos hcop hdeg3 B kt l cs hok hcst hrep' (primesBelow Bd) Bd rs (fun fK ↦ localCert fK 2) k
    htk z s hz ht0 hs2 hs' θE hθE hTrE hsqE hdegAE rtsF hrlF hrsF c0f hFc
  by_cases hgood : ∀ k : Fin cls.length,
      kxTorsC Fc ks (m + 1) g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs cls[(k : ℕ)] =
        some none →
      ∃ (N M : ℕ) (b bt : KF Fc (m + 1)), 1 ≤ N ∧ 1 ≤ M ∧
        kxBt0 Fc ks (m + 1) g A B kt l cs cls[(k : ℕ)] z = some b ∧ (bt = b ∨ bt = -b) ∧
        kxWitD Fc ks (m + 1) g A B kt l cs cls[(k : ℕ)] bt N M ≠ none ∧
        bt * bt = (kxFKm Fc ks (m + 1) g A B kt l cs cls[(k : ℕ)]).getD 0 0 ∧ bt ≠ 0
  · -- every non-torsion class is dependent: the relation search answers
    have hNk : ∀ k : Fin cls.length, ∃ Nk : ℕ, ∀ nmax, Nk ≤ nmax →
        kxTorsC Fc ks (m + 1) g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs cls[(k : ℕ)] =
          some none → kxDepSearch Fc ks (m + 1) g A B kt l cs cls[(k : ℕ)] z nmax ≠ none := by
      intro k
      by_cases htk : kxTorsC Fc ks (m + 1) g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs
          cls[(k : ℕ)] = some none
      · obtain ⟨N, M, b, bt, hN1, hM1, hb, hpm, hw, h2, h0⟩ := hgood k htk
        exact ⟨max N M, fun nmax hnm _ ↦ kxDepSearch_ne_none (m + 1) g A B kt l cs _ z nmax N M b bt hN1
          hM1 (le_of_max_le_left hnm) (le_of_max_le_right hnm) hb hpm hw h2 h0⟩
      · exact ⟨0, fun _ _ h ↦ absurd h htk⟩
    choose Nk hNk using hNk
    refine ⟨∑ k, Nk k, fun nmax hnm ↦ ⟨0, fun kmax _ ↦ hDL nmax kmax ?_⟩⟩
    unfold kxDecideDL
    rcases hL : kxDecideL Fc ks lv (m + 1) g A B kt l cs (primesBelow Bd) Bd rs with _ | b
    swap
    · rfl
    dsimp only
    have hnone : ¬ (cls.map (kxTorsC Fc ks (m + 1) g A B kt l cs (fun fK ↦ localCert fK 2)
        (primesBelow Bd) Bd rs)).any (· == none) = true := by
      intro h
      obtain ⟨x, hx, hx0⟩ := List.any_eq_true.mp h
      obtain ⟨T', hT', rfl⟩ := List.mem_map.mp hx
      have := hallS T' hT'
      simp only [beq_iff_eq] at hx0
      rw [hx0] at this; exact absurd this (by simp)
    unfold kxDecideDepC
    dsimp only
    rw [if_neg hr0, if_neg (by simp [hok]), if_neg (by simp [hcst]), if_neg (by simp [hrep']),
      if_neg hnone]
    simp only [hz, ht0]
    refine T.kxSolveDepC_isSome (m + 1) MS.hyp hk A B hsq hdegA hcopA kt l cs hok hcst hrep' rs Bd z nmax
      fun T' hT' ↦ ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT'
    rcases h : kxTorsC Fc ks (m + 1) g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs cls[i]
      with _ | _ | N
    · have := hallS _ hT'; rw [h] at this; exact absurd this (by simp)
    · right
      refine ⟨rfl, hNk ⟨i, hi⟩ nmax ?_ h⟩
      exact le_trans (Finset.single_le_sum (fun k _ ↦ Nat.zero_le (Nk k)) (Finset.mem_univ _)) hnm
    · left; exact ⟨N, rfl⟩
  -- an independent class: a certificate search succeeds
  obtain ⟨k, hk'⟩ := not_forall.mp hgood
  obtain ⟨htk, hnl⟩ := Classical.not_imp.mp hk'
  obtain ⟨b₀, hb₀, hns, hns0, hgrp, hP0, hntF⟩ := (hDI k htk).resolve_left hnl
  have hrE : ∀ i < 4, TE.ev (m + 1) (aCS Fc ks m A i) = (r i : E) := fun i hi ↦ by
    rw [hev, hr i hi, map_ratCast]
  obtain ⟨hA4, hBok, hcs, hD, hrE', hBq, hκ, hs, hzκ, hmG, hdisc⟩ := TE.const_sideS hmon hdeg m hTEn1 hc hk
    A hsqc hdeg3 B kt l cs hok hcst hrep' c0f hFc hAw hBw hcsw hgw r hrE z hz hTrE.of_succ k
  have hFc' : Fc = [Fc.headD [], [1]] := by rw [hFc]; rfl
  refine ⟨0, fun nmax _ ↦ ?_⟩
  by_cases hsqr : IsSquare (kxKap Fc ks (m + 1) A z / sTS Fc ks m g A B kt l cs k)
  · obtain ⟨K0, hK⟩ := TE.kxMWSearchTKS_of m c0f hFc hTrE.of_succ g A B kt l cs z hz k hsqr
      hA4 hBok hcs hD r hrE' hBq hκ hs hzκ hmG hdisc rtsF hrlF hrsF b₀ hb₀ hns hns0 hgrp hP0
    refine ⟨K0, fun kmax hkm ↦ kxDecideDKS_isSome_of (lv := lv) m g A B kt l cs _ _ rs nmax kmax (Or.inr ?_)⟩
    simp only [kxMWOKTKS, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨⟨⟨hdeg3, hok⟩, hcst⟩, hrep'⟩, hK kmax hkm⟩
  · have hnsq : ¬ IsSquare (sTS Fc ks m g A B kt l cs k * kxKap Fc ks (m + 1) A z) := by
      rintro ⟨t, ht⟩
      refine hsqr ⟨t / sTS Fc ks m g A B kt l cs k, ?_⟩
      rw [div_mul_div_comm, ← ht, mul_comm (sTS Fc ks m g A B kt l cs k), mul_div_mul_right _ _ hs]
    obtain ⟨K0, hK⟩ := TE.kxMWSearchCKS_of m c0f hFc hTrE.of_succ g A B kt l cs z hz k hnsq
      hA4 hBok hcs hD r hrE' hBq hκ hs hzκ hmG hdisc rtsF hrlF hrsF b₀ hb₀ hns hns0 hntF
    refine ⟨K0, fun kmax hkm ↦ kxDecideDKS_isSome_of (lv := lv) m g A B kt l cs _ _ rs nmax kmax (Or.inl ?_)⟩
    simp only [kxMWOKCKS, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨⟨⟨⟨sqOK_of_linear Fc _ hFc, hdeg3⟩, hok⟩, hcst⟩, hrep'⟩, hK kmax hkm⟩

end MTower

end Curves.MT
