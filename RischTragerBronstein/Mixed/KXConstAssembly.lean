import RischTragerBronstein.Mixed.KXDepOrIndep
import RischTragerBronstein.Mixed.KXConstSearch
import RischTragerBronstein.Mixed.KXDepDecides
import RischTragerBronstein.Mixed.CubicDisc
import RischTragerBronstein.Mixed.CodeWF

/-!
# Constant curves: the combined decision answers

* `MTower.lift_sqrts`: a realization over an extension containing square roots of given nonzero
  rationals (constants) — no elementary integral needed (contrast `kqm_lift`).
* the side conditions of `kxMWSearchCK_of` / `kxMWSearchTK_of` from the data.
* `kxDecideDK0`: `kxDecideDL` at level `0`, then the constant-curve certificate searches;
  `kxDecideDK0_correct`, and **`kxDecideDK0_decides`**: for a cubic with rational coefficients over
  a linear base, at suitable residues, for every large bound, every large relation bound and every
  large height level, `kxDecideDK0` answers (correctly).
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

variable (T : MTower Fc ks Cc L)

/-- **A realization with constant square roots of given nonzero rationals.** -/
theorem lift_sqrts (κs : List ℚ) (hκ : ∀ κ ∈ κs, κ ≠ 0) :
    ∃ (E : Type u) (_ : Field E) (_ : Differential E) (_ : CharZero E)
      (TE : MTower Fc ks (constants E) E) (ψ : L →+* E) (rts : List E),
      TE.n = T.n ∧ (∀ m q, TE.ev m q = ψ (T.ev m q)) ∧ (∀ m P, TE.evP m P = ψ (T.evP m P)) ∧
      rts.length = κs.length ∧
      ∀ i (hi : i < rts.length) (hi' : i < κs.length), rts[i] ^ 2 = (κs[i] : E) ∧ rts[i]′ = 0 := by
  obtain ⟨E₂, _, _, _, _, -, -, rts, hrl, hrts⟩ := sqrts_ext L κs hκ
  haveI : CharZero E₂ := charZero_of_injective_algebraMap (algebraMap L E₂).injective
  obtain ⟨TE, hTEn, hTEts, hTEev, -⟩ := T.exists_lift E₂
  refine ⟨E₂, inferInstance, inferInstance, inferInstance, TE, algebraMap L E₂, rts, hTEn, hTEev,
    fun m P ↦ ?_, hrl, hrts⟩
  induction P with
  | nil => simp [evP, evPL]
  | cons a P ih =>
    simp only [evP, evPL, List.foldr_cons] at ih ⊢
    rw [ih, map_add, map_mul, hTEts m, ← hTEev m a]

end MTower

/-- A gcd fold vanishes only on zeros. -/
lemma foldr_gcd_zero : ∀ (l : List ℤ), l.foldr (fun a b ↦ Int.gcd a (b : ℤ)) 0 = 0 → ∀ x ∈ l, x = 0
  | [], _, x, hx => by simp at hx
  | a :: l, h, x, hx => by
    simp only [List.foldr_cons, Int.gcd_eq_zero_iff, Nat.cast_eq_zero] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact foldr_gcd_zero l h.2 x hx

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

lemma codeOKb_getD (l : List (LC 0)) (hl : ∀ a ∈ l, codeOKb a = true) (i : ℕ) :
    codeOKb (l.getD i (MO Fc ks 0).zero) = true := by
  rcases Nat.lt_or_ge i l.length with h | h
  · rw [List.getD_eq_getElem _ _ h]; exact hl _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ h]; rfl

set_option maxHeartbeats 4000000 in
/-- **The side conditions of the constant-curve searches**, from the data. -/
theorem const_side (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {g : LC 0} (hk : ks 0 = .exp g)
    (A : GPoly (LC 0)) (hsqc : GPoly.squarefreeCheck (MO Fc ks 0) A = true)
    (hdeg3 : degG (MO Fc ks 0) A = 3)
    (B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (hok : kxOK Fc ks 0 A B kt l cs = true)
    (hcst : kxConst Fc ks 0 g A B kt l cs = true) (hrep : kxRepOK Fc ks 0 g A B kt l cs = true)
    (c0f : CPoly ℚ) (hFc : Fc = [c0f, [1]])
    (hAw : ∀ a ∈ A, codeOKb a = true) (hBw : ∀ b ∈ B, codeOKb b = true)
    (hcsw : ∀ c ∈ cs, codeOKb c = true) (hgw : codeOKb g = true)
    (r : ℕ → ℚ) (hr : ∀ i < 4, T.ev 0 (aC Fc ks A i) = (r i : L))
    (z : LC 0) (hz : kxZ Fc ks lv 0 A = some z) (h0 : T.Tr 0)
    (k : Fin (kxCls Fc ks 0 g A B kt l cs).length) :
    (∀ i < 4, codeOKb (aC Fc ks A i) = true) ∧
    (∀ q < cs.length, codeOKb (kqC Fc ks 0 cs q) = true) ∧
    (∀ q < cs.length, codeOKb (kxD Fc ks 0 g cs q) = true) ∧
    (∀ i < 4, T.val 0 (aC Fc ks A i) = (r i : T.F 0)) ∧
    (∀ q < cs.length, (GPoly.toPoly (T.MP 0 h0) B).eval (T.val 0 (kqC Fc ks 0 cs q)) ≠ 0) ∧
    kxKap Fc ks 0 A z ≠ 0 ∧ sT Fc ks g A B kt l cs k ≠ 0 ∧
    T.val 0 z ^ 2 * T.val 0 (aC Fc ks A 0) = (kxKap Fc ks 0 A z : T.F 0) ∧
    mG Fc ks g A B kt l cs k ≠ 0 ∧
    4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
      27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2 ≠ 0 := by
  have MS := T.mspecs hmon hdeg lv 1 (by omega) hc
  have hvL : ∀ q : LC 0, ((T.val 0 q : T.F 0) : L) = T.ev 0 q := fun q ↦ by
    rw [← T.sem_MP_F 0 h0, T.sem_MP 0 h0]
  have hok0 := T.kxOK_spec 0 h0 A B kt l cs hok
  have ha0 : (MO Fc ks 0).isZero (A.getD 0 (MO Fc ks 0).zero) = false := by
    cases h : (MO Fc ks 0).isZero (A.getD 0 (MO Fc ks 0).zero)
    · rfl
    · exact absurd (((T.MP 0 h0).isZero_iff _).mp h) hok0.1
  obtain ⟨q1, hq1⟩ := kxZ_some hz
  obtain ⟨-, hzκ, hκ0⟩ := T.ke_z_facts hmon hdeg 0 hn hc A ha0 q1 z hq1
  have hr' : ∀ i < 4, T.val 0 (aC Fc ks A i) = (r i : T.F 0) := fun i hi ↦
    Subtype.ext (by rw [hvL, hr i hi]; simp)
  -- the multiplicity gcd
  have hmG : mG Fc ks g A B kt l cs k ≠ 0 := by
    obtain ⟨q0, hq0, hq0T⟩ := kxCls_mem_rep (Fc := Fc) (ks := ks) 0 g A B kt l cs _
      (List.getElem_mem (n := (k : ℕ)) k.2)
    have hm0 : kxMNm Fc ks 0 g A B kt l cs q0 ≠ 0 := by
      intro h0'
      obtain ⟨-, hκ, hc0'⟩ := kxRep_spec (Fc := Fc) (ks := ks) 0 g A B kt l cs hrep q0 hq0
      have hm := kxMNm_eq (Fc := Fc) (ks := ks) 0 g A B kt l cs q0 hq0 hc0'
      rw [h0', Nat.cast_zero, eq_comm, mul_eq_zero] at hm
      rcases hm with h | h
      · exact (kxDenM_pos (Fc := Fc) (ks := ks) 0 g A B kt l cs).ne' (by exact_mod_cast h)
      · rw [h] at hκ; simp at hκ
        exact T.kxK_ne 0 MS.hyp hk A B kt l cs hok hcst q0 hq0 hκ
    intro h0'
    have := foldr_gcd_zero _ h0' (mKc Fc ks g A B kt l cs k q0)
      (List.mem_map.mpr ⟨q0, List.mem_range.mpr hq0, rfl⟩)
    unfold mKc at this
    rw [if_pos (by rw [List.getD_eq_getElem _ _ k.2, hq0T]; exact beq_self_eq_true _)] at this
    exact hm0 (by exact_mod_cast this)
  -- the discriminant
  have hdisc : 4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
      27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2 ≠ 0 := by
    set P := GPoly.toPoly (T.MP 0 h0) A with hP
    have hdeg3' : P.natDegree = 3 := by rw [hP, ← degG_eq (T.MP 0 h0) A, hdeg3]
    have hcf : ∀ i < 4, P.coeff i = (r i : T.F 0) := fun i hi ↦ by
      rw [hP, Tower.PrimN.coeff_toPoly_getD, T.sem_MP_F 0 h0]; exact hr' i hi
    have hPc := MTower.cubic_eq P hdeg3'
    rw [hcf 3 (by norm_num), hcf 2 (by norm_num), hcf 1 (by norm_num), hcf 0 (by norm_num)] at hPc
    have hsq := GPoly.squarefreeCheck_sound (T.MP 0 h0) hsqc
    rw [← hP, hPc] at hsq
    have hP0 : P ≠ 0 := fun h ↦ by rw [h, natDegree_zero] at hdeg3'; omega
    have hc3 : ((r 3 : ℚ) : T.F 0) ≠ 0 := by
      rw [← hcf 3 (by norm_num)]
      have := leadingCoeff_ne_zero.mpr hP0
      rwa [leadingCoeff, hdeg3'] at this
    have hF := CubicDisc.short_disc_ne_zero _ _ _ _ hc3 hsq
    intro h
    apply hF
    have := congrArg (fun x : ℚ ↦ (x : T.F 0)) h
    push_cast at this
    linear_combination this
  refine ⟨fun i _ ↦ codeOKb_getD A hAw i, fun q _ ↦ codeOKb_getD cs hcsw q, fun q _ ↦ ?_, hr',
    fun q hq ↦ ?_, hκ0, prodSub_ne _ (kxGens_spec (Fc := Fc) (ks := ks) 0 g A B kt l cs).2 _,
    Subtype.ext ?_, hmG, hdisc⟩
  · subst hFc; exact codeOKb_kxD c0f ks g cs hgw hcsw q
  · rw [← T.sem_MP_F 0 h0]; exact (hok0.2 q hq).2.2.2
  · push_cast; rw [hvL, hvL]; exact hzκ

end MTower

/-- **`kxDecideDL` at level `0`, then the constant-curve certificate searches.** -/
def kxDecideDK0 (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
    (lv : (m : ℕ) → LC m) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ) : Option Bool :=
  match kxDecideDL Fc ks lv 0 g A B kt l cs ps bound rs nmax with
  | some b => some b
  | none =>
    if kxMWOKCK Fc ks lv (Fc.headD []) g A B kt l cs kmax then some false
    else if kxMWOKTK Fc ks lv (Fc.headD []) g A B kt l cs kmax then some false else none

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- **`kxDecideDK0` is correct.** -/
theorem kxDecideDK0_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {g : LC 0} (hk : ks 0 = .exp g)
    (A : GPoly (LC 0)) (hsqc : GPoly.squarefreeCheck (MO Fc ks 0) A = true)
    (hdegpos : 0 < degG (MO Fc ks 0) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks 0) A))
    (θ : L) (hθ : θ ^ 2 = T.evP 0 A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (nmax kmax : ℕ) (b : Bool)
    (hdec : kxDecideDK0 Fc ks lv g A B kt l cs ps bound rs nmax kmax = some b) :
    HasElementaryIntegral (T.ev 1 ((B, kxDen Fc ks 0 A kt l cs) : LC 1) * θ) ↔ b = true := by
  unfold kxDecideDK0 at hdec
  cases hD : kxDecideDL Fc ks lv 0 g A B kt l cs ps bound rs nmax with
  | some b' =>
    rw [hD] at hdec
    cases hdec
    exact T.kxDecideDL_correct hmon hdeg 0 hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps bound
      rs nmax _ hD
  | none =>
    rw [hD] at hdec
    simp only at hdec
    split_ifs at hdec with hK hTK
    · cases hdec
      exact iff_of_false (T.not_elementary_of_MWOKCK hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ
        hgen B kt l cs kmax hK) (by decide)
    · cases hdec
      exact iff_of_false (T.not_elementary_of_MWOKTK hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ
        hgen B kt l cs kmax hTK) (by decide)

/-- Once a constant-curve search succeeds, `kxDecideDK0` answers. -/
lemma kxDecideDK0_isSome_of (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (nmax kmax : ℕ)
    (h : kxMWOKCK Fc ks lv (Fc.headD []) g A B kt l cs kmax = true ∨
      kxMWOKTK Fc ks lv (Fc.headD []) g A B kt l cs kmax = true) :
    (kxDecideDK0 Fc ks lv g A B kt l cs ps bound rs nmax kmax).isSome := by
  unfold kxDecideDK0
  rcases kxDecideDL Fc ks lv 0 g A B kt l cs ps bound rs nmax with _ | b
  · dsimp only
    rcases h with h | h
    · rw [if_pos h]; rfl
    · split_ifs <;> rfl
  · rfl

end MTower

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

set_option maxHeartbeats 16000000 in
/-- **Constant curves are decided.** For a cubic `A` with rational coefficients over a linear base
(well-formed codes), at suitable residues, for every large bound there is `N₀` such that for every
relation bound `nmax ≥ N₀` there is `K₀` such that for every height level `kmax ≥ K₀`,
`kxDecideDK0` answers, and correctly. -/
theorem kxDecideDK0_decides (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {g : LC 0} (hk : ks 0 = .exp g)
    (A : GPoly (LC 0)) (hsqc : GPoly.squarefreeCheck (MO Fc ks 0) A = true)
    (hdegpos : 0 < degG (MO Fc ks 0) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks 0) A))
    (hdeg3 : degG (MO Fc ks 0) A = 3)
    (θ : L) (hθ : θ ^ 2 = T.evP 0 A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (hr0 : cs.length ≠ 0)
    (hok : kxOK Fc ks 0 A B kt l cs = true)
    (hrep : kxConst Fc ks 0 g A B kt l cs = true → kxRepOK Fc ks 0 g A B kt l cs = true)
    (c0f : CPoly ℚ) (hFc : Fc = [c0f, [1]])
    (hAw : ∀ a ∈ A, codeOKb a = true) (hBw : ∀ b ∈ B, codeOKb b = true)
    (hcsw : ∀ c ∈ cs, codeOKb c = true) (hgw : codeOKb g = true)
    (r : ℕ → ℚ) (hr : ∀ i < 4, T.ev 0 (aC Fc ks A i) = (r i : L)) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd → ∃ N0, ∀ nmax, N0 ≤ nmax → ∃ K0, ∀ kmax, K0 ≤ kmax →
      ∃ b, kxDecideDK0 Fc ks lv g A B kt l cs (primesBelow Bd) Bd rs nmax kmax = some b ∧
        (HasElementaryIntegral (T.ev 1 ((B, kxDen Fc ks 0 A kt l cs) : LC 1) * θ) ↔ b = true) := by
  obtain ⟨rs, B0, hdec⟩ := T.kxDecideL_decides' hmon hdeg 0 hn hc hk A hsqc hdegpos hcop B kt l cs
    hr0 hok hrep
  refine ⟨rs, B0, fun Bd hBd ↦ ?_⟩
  suffices h : ∃ N0, ∀ nmax, N0 ≤ nmax → ∃ K0, ∀ kmax, K0 ≤ kmax →
      (kxDecideDK0 Fc ks lv g A B kt l cs (primesBelow Bd) Bd rs nmax kmax).isSome by
    obtain ⟨N0, h⟩ := h
    refine ⟨N0, fun nmax hnm ↦ ?_⟩
    obtain ⟨K0, hK⟩ := h nmax hnm
    refine ⟨K0, fun kmax hkm ↦ ?_⟩
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hK kmax hkm)
    exact ⟨b, hb, T.kxDecideDK0_correct hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs
      _ _ rs nmax kmax b hb⟩
  have hDL : ∀ nmax kmax,
      (kxDecideDL Fc ks lv 0 g A B kt l cs (primesBelow Bd) Bd rs nmax).isSome →
      (kxDecideDK0 Fc ks lv g A B kt l cs (primesBelow Bd) Bd rs nmax kmax).isSome := by
    intro nmax kmax h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
    unfold kxDecideDK0; rw [hb]; rfl
  rcases hdec Bd hBd with h1 | ⟨⟨z, hz, ht0, -⟩, hallS, hcst⟩
  · refine ⟨0, fun nmax _ ↦ ⟨0, fun kmax _ ↦ hDL nmax kmax ?_⟩⟩
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h1
    unfold kxDecideDL
    rw [hb]; rfl
  have MS := T.mspecs hmon hdeg lv 1 (by omega) hc
  have hTr : T.Tr 1 := MS.hyp.tr
  have hTm : T.Tr 0 := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP 0 hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP 0 hTm) A).natDegree = degG (MO Fc ks 0) A :=
    (degG_eq (T.MP 0 hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP 0 hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP 0 hTm) A).natDegree := by rw [hdeg1]; exact hcop
  have hrep' := hrep hcst
  have hok0 := T.kxOK_spec 0 hTm A B kt l cs hok
  have ha0 : (MO Fc ks 0).isZero (A.getD 0 (MO Fc ks 0).zero) = false := by
    cases h : (MO Fc ks 0).isZero (A.getD 0 (MO Fc ks 0).zero)
    · rfl
    · exact absurd (((T.MP 0 hTm).isZero_iff _).mp h) hok0.1
  have hg0 := (kxGens_spec (Fc := Fc) (ks := ks) 0 g A B kt l cs).2
  obtain ⟨q0, hq0⟩ := kxZ_some hz
  obtain ⟨-, -, hκ0⟩ := T.ke_z_facts hmon hdeg 0 hn hc A ha0 q0 z hq0
  have hκs : ∀ κ' ∈ kxKap Fc ks 0 A z :: kxGens Fc ks 0 g A B kt l cs, κ' ≠ 0 := fun κ' h ↦ by
    rcases List.mem_cons.mp h with rfl | h
    · exact hκ0
    · exact hg0 κ' h
  -- a realization with the square roots
  obtain ⟨E, _, _, _, TE, ψ, rts0, hTEn, hev, hevP, hrl0, hrts0⟩ := T.lift_sqrts _ hκs
  obtain ⟨s, rts, hs2, hs', hrl, hrts⟩ := roots_cons _ _ rts0 hrl0 hrts0
  have hTEn1 : TE.n = 1 := by rw [hTEn, hn]
  set θE := ψ θ with hθEdef
  have hθE : θE ^ 2 = TE.evP 0 A := by rw [hevP, ← map_pow, hθ]
  have MSE := TE.mspecs hmon hdeg lv 1 (by omega) hc
  have hTrE : TE.Tr 1 := MSE.hyp.tr
  have hsqE := GPoly.squarefreeCheck_sound (TE.MP 0 hTrE.of_succ) hsqc
  have hdegAE : 0 < (GPoly.toPoly (TE.MP 0 hTrE.of_succ) A).natDegree := by
    rw [← degG_eq (TE.MP 0 hTrE.of_succ) A]; exact hdegpos
  obtain ⟨rtsF, hFl, hFv⟩ := TE.roots_F 0 rts (fun i hi ↦ (hrts i hi (by omega)).2)
  have hrlF : rtsF.length = (kxGens Fc ks 0 g A B kt l cs).length := by rw [hFl, hrl]
  have hrsF : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks 0 g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks 0 g A B kt l cs)[i] : TE.F 0) := fun i hi hi' ↦ Subtype.ext (by
    rw [IntermediateField.coe_pow, hFv i hi (by omega), (hrts i (by omega) hi').1]; simp)
  set cls := kxCls Fc ks 0 g A B kt l cs with hcls
  have hDI := fun (k : Fin cls.length) htk ↦ TE.kx_dep_or_indep hmon hdeg 0 hTEn1 hc hk A hsqc
    hdegpos hcop hdeg3 B kt l cs hok hcst hrep' (primesBelow Bd) Bd rs (fun fK ↦ localCert fK 2) k
    htk z s hz ht0 hs2 hs' θE hθE hTrE hsqE hdegAE rtsF hrlF hrsF c0f hFc
  by_cases hgood : ∀ k : Fin cls.length,
      kxTorsC Fc ks 0 g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs cls[(k : ℕ)] =
        some none →
      ∃ (N M : ℕ) (b bt : KF Fc 0), 1 ≤ N ∧ 1 ≤ M ∧
        kxBt0 Fc ks 0 g A B kt l cs cls[(k : ℕ)] z = some b ∧ (bt = b ∨ bt = -b) ∧
        kxWitD Fc ks 0 g A B kt l cs cls[(k : ℕ)] bt N M ≠ none ∧
        bt * bt = (kxFKm Fc ks 0 g A B kt l cs cls[(k : ℕ)]).getD 0 0 ∧ bt ≠ 0
  · -- every non-torsion class is dependent: the relation search answers
    have hNk : ∀ k : Fin cls.length, ∃ Nk : ℕ, ∀ nmax, Nk ≤ nmax →
        kxTorsC Fc ks 0 g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs cls[(k : ℕ)] =
          some none → kxDepSearch Fc ks 0 g A B kt l cs cls[(k : ℕ)] z nmax ≠ none := by
      intro k
      by_cases htk : kxTorsC Fc ks 0 g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs
          cls[(k : ℕ)] = some none
      · obtain ⟨N, M, b, bt, hN1, hM1, hb, hpm, hw, h2, h0⟩ := hgood k htk
        exact ⟨max N M, fun nmax hnm _ ↦ kxDepSearch_ne_none 0 g A B kt l cs _ z nmax N M b bt hN1
          hM1 (le_of_max_le_left hnm) (le_of_max_le_right hnm) hb hpm hw h2 h0⟩
      · exact ⟨0, fun _ _ h ↦ absurd h htk⟩
    choose Nk hNk using hNk
    refine ⟨∑ k, Nk k, fun nmax hnm ↦ ⟨0, fun kmax _ ↦ hDL nmax kmax ?_⟩⟩
    unfold kxDecideDL
    rcases hL : kxDecideL Fc ks lv 0 g A B kt l cs (primesBelow Bd) Bd rs with _ | b
    swap
    · rfl
    dsimp only
    have hnone : ¬ (cls.map (kxTorsC Fc ks 0 g A B kt l cs (fun fK ↦ localCert fK 2)
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
    refine T.kxSolveDepC_isSome 0 MS.hyp hk A B hsq hdegA hcopA kt l cs hok hcst hrep' rs Bd z nmax
      fun T' hT' ↦ ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT'
    rcases h : kxTorsC Fc ks 0 g A B kt l cs (fun fK ↦ localCert fK 2) (primesBelow Bd) Bd rs cls[i]
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
  have hrE : ∀ i < 4, TE.ev 0 (aC Fc ks A i) = (r i : E) := fun i hi ↦ by
    rw [hev, hr i hi, map_ratCast]
  obtain ⟨hA4, hcs, hD, hrE', hBq, hκ, hs, hzκ, hmG, hdisc⟩ := TE.const_side hmon hdeg hTEn1 hc hk
    A hsqc hdeg3 B kt l cs hok hcst hrep' c0f hFc hAw hBw hcsw hgw r hrE z hz hTrE.of_succ k
  have hFc' : Fc = [Fc.headD [], [1]] := by rw [hFc]; rfl
  refine ⟨0, fun nmax _ ↦ ?_⟩
  by_cases hsqr : IsSquare (kxKap Fc ks 0 A z / sT Fc ks g A B kt l cs k)
  · obtain ⟨K0, hK⟩ := TE.kxMWSearchTK_of (Fc.headD []) hFc' hTrE.of_succ g A B kt l cs z hz k hsqr
      hA4 hBw hcs hD r hrE' hBq hκ hs hzκ hmG hdisc rtsF hrlF hrsF b₀ hb₀ hns hns0 hgrp hP0
    refine ⟨K0, fun kmax hkm ↦ kxDecideDK0_isSome_of (lv := lv) g A B kt l cs _ _ rs nmax kmax (Or.inr ?_)⟩
    simp only [kxMWOKTK, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨⟨⟨⟨hFc', hdeg3⟩, hok⟩, hcst⟩, hrep'⟩, hK kmax hkm⟩
  · have hnsq : ¬ IsSquare (sT Fc ks g A B kt l cs k * kxKap Fc ks 0 A z) := by
      rintro ⟨t, ht⟩
      refine hsqr ⟨t / sT Fc ks g A B kt l cs k, ?_⟩
      rw [div_mul_div_comm, ← ht, mul_comm (sT Fc ks g A B kt l cs k), mul_div_mul_right _ _ hs]
    obtain ⟨K0, hK⟩ := TE.kxMWSearchCK_of (Fc.headD []) hFc' hTrE.of_succ g A B kt l cs z hz k hnsq
      hA4 hBw hcs hD r hrE' hBq hκ hs hzκ hmG hdisc rtsF hrlF hrsF b₀ hb₀ hns hns0 hntF
    refine ⟨K0, fun kmax hkm ↦ kxDecideDK0_isSome_of (lv := lv) g A B kt l cs _ _ rs nmax kmax (Or.inl ?_)⟩
    simp only [kxMWOKCK, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨⟨⟨⟨hFc', hdeg3⟩, hok⟩, hcst⟩, hrep'⟩, hK kmax hkm⟩

end MTower

end Curves.MT
