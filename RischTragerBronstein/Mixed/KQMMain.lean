import RischTragerBronstein.Mixed.KQMCodes
import RischTragerBronstein.Mixed.KQMulti
import RischTragerBronstein.Mixed.KQTwist
import RischTragerBronstein.Mixed.KQMBridge
import RischTragerBronstein.Mixed.KQMain

/-!
# Square roots over a logarithm with poles, several residue classes: the decision is correct

`kqmDecide_correct`: whenever `kqmDecide` answers `some b`, `∫ B(t) θ / (∏ (t − c_q) A(t)ˡ)` is
elementary iff `b = true`.

* `sqrts_ext`: a finite (hence elementary) extension with constant square roots of a list of
  nonzero rationals;
* the residues are `c_q √s_{T_q}` with `s_T = ∏_{i ∈ T} gᵢ` for independent generators `gᵢ`; the
  class values `∏_{i ∈ T} √gᵢ` are `ℚ`-independent (`SqrtIndep.prods_indep`);
* each class is tested for torsion on its twist `ỹ² = s_T A` over the code field, and read back on
  `y² = A` by `principalMulN_scale`, `vanishAtN_scale`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Differential

universe v

/-- **Adjoining square roots of several rationals**: a finite, hence elementary, extension. -/
theorem sqrts_ext (E : Type v) [Field E] [Differential E] [CharZero E] (κs : List ℚ)
    (hκ : ∀ κ ∈ κs, κ ≠ 0) :
    ∃ (E₂ : Type v) (_ : Field E₂) (_ : Differential E₂) (_ : Algebra E E₂)
      (_ : DifferentialAlgebra E E₂), IsElementaryExtension E E₂ ∧ Algebra.IsAlgebraic E E₂ ∧
        ∃ rts : List E₂, rts.length = κs.length ∧
          ∀ i (hi : i < rts.length) (hi' : i < κs.length), rts[i] ^ 2 = (κs[i] : E₂) ∧ rts[i]′ = 0 := by
  classical
  set q : E[X] := (κs.map fun κ : ℚ ↦ X ^ 2 - Polynomial.C ((κ : ℚ) : E)).prod
  letI : Differential (SplittingField q) := differentialFiniteDimensional E (SplittingField q)
  haveI : DifferentialAlgebra E (SplittingField q) := differentialAlgebraFiniteDimensional
  haveI : CharZero (SplittingField q) :=
    charZero_of_injective_algebraMap (algebraMap E (SplittingField q)).injective
  have hq0 : q.map (algebraMap E (SplittingField q)) ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff (algebraMap E _).injective]
    refine List.prod_ne_zero fun h0 ↦ ?_
    obtain ⟨κ, -, hκ0⟩ := List.mem_map.mp h0
    have := congrArg natDegree hκ0
    rw [natDegree_X_pow_sub_C, natDegree_zero] at this
    exact two_ne_zero this
  have hroot : ∀ κ ∈ κs, ∃ r : SplittingField q, r ^ 2 = (κ : SplittingField q) ∧ r′ = 0 := by
    intro κ hκm
    set f : E[X] := X ^ 2 - Polynomial.C ((κ : ℚ) : E)
    have hdvd : f.map (algebraMap E (SplittingField q)) ∣ q.map (algebraMap E (SplittingField q)) :=
      Polynomial.map_dvd _ (List.dvd_prod (List.mem_map.mpr ⟨κ, hκm, rfl⟩))
    have hs := (SplittingField.splits q).of_dvd hq0 hdvd
    have hdeg : (f.map (algebraMap E (SplittingField q))).degree ≠ 0 := by
      rw [degree_map, degree_X_pow_sub_C (by norm_num)]; norm_num
    obtain ⟨r, hr⟩ := hs.exists_eval_eq_zero hdeg
    have hr2 : r ^ 2 = (κ : SplittingField q) := by
      simp only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        eval_sub, eval_pow, eval_X, eval_C, map_ratCast] at hr
      linear_combination hr
    refine ⟨r, hr2, ?_⟩
    have hr0 : r ≠ 0 := fun h ↦ by
      rw [h, zero_pow two_ne_zero] at hr2
      exact hκ κ hκm (by exact_mod_cast hr2.symm)
    have hd := congrArg (fun w ↦ w′) hr2
    simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul] at hd
    rw [Tower.NestP.deriv_ratCastK (K := SplittingField q) κ] at hd
    have h2 : ((2 : ℕ) : SplittingField q) * r ^ (2 - 1) * r′ = 0 := by
      rw [← hd]; ring
    norm_num at h2
    rcases h2 with h2 | h2
    · exact absurd h2 hr0
    · exact h2
  choose! rt hrt using hroot
  refine ⟨SplittingField q, inferInstance, inferInstance, inferInstance, inferInstance,
    isElementaryExtension_of_finiteDimensional, Algebra.IsAlgebraic.of_finite _ _,
    κs.map rt, by simp, fun i hi hi' ↦ ?_⟩
  simp only [List.getElem_map]
  exact hrt _ (List.getElem_mem _)

end Differential

namespace SqrtIndep

variable {K : Type*} [Field K] [CharZero K]

/-- The product of the selected roots. -/
def prodRoots : List K → List Bool → K
  | y :: r, b :: T => (if b then y else 1) * prodRoots r T
  | _, _ => 1

/-- The position of a subset in `prods`. -/
def bidx : List Bool → ℕ
  | [] => 0
  | false :: T => bidx T
  | true :: T => 2 ^ T.length + bidx T

lemma bidx_lt : ∀ T : List Bool, bidx T < 2 ^ T.length
  | [] => by simp [bidx]
  | false :: T => by
    have := bidx_lt T
    simp only [bidx, List.length_cons, pow_succ]; omega
  | true :: T => by
    have := bidx_lt T
    simp only [bidx, List.length_cons, pow_succ]; omega

lemma bidx_inj : ∀ (T T' : List Bool), T.length = T'.length → bidx T = bidx T' → T = T'
  | [], [], _, _ => rfl
  | a :: T, b :: T', hl, h => by
    have hl' : T.length = T'.length := by simpa using hl
    have h1 := bidx_lt T
    have h2 := bidx_lt T'
    cases a <;> cases b <;> simp only [bidx] at h
    · rw [bidx_inj T T' hl' h]
    · rw [hl'] at h1; omega
    · exfalso; rw [hl'] at h; omega
    · rw [hl'] at h; rw [bidx_inj T T' hl' (by omega)]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

lemma prods_getD_bidx : ∀ (r : List K) (T : List Bool), T.length = r.length →
    (prods r).getD (bidx T) 0 = prodRoots r T
  | [], [], _ => by simp [prods, bidx, prodRoots]
  | y :: r, b :: T, hl => by
    have hl' : T.length = r.length := by simpa using hl
    have hlt := bidx_lt T
    have hP : (prods r).length = 2 ^ r.length := length_prods r
    cases b
    · simp only [prods, bidx, prodRoots]
      rw [List.getD_append _ _ _ _ (by rw [hP, ← hl']; exact hlt), prods_getD_bidx r T hl']
      simp
    · simp only [prods, bidx, prodRoots, if_true]
      rw [List.getD_append_right _ _ _ _ (by rw [hP, hl']; omega), hP, hl',
        Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ (by rw [List.length_map, hP, ← hl']; exact hlt),
        List.getElem_map, ← List.getD_eq_getElem _ 0 (by rw [hP, ← hl']; exact hlt),
        prods_getD_bidx r T hl']
  | [], _ :: _, hl => by simp at hl
  | _ :: _, [], hl => by simp at hl

lemma prodRoots_sq : ∀ (s : List ℚ) (r : List K), r.length = s.length →
    (∀ i (hi : i < r.length) (hi' : i < s.length), r[i] ^ 2 = (s[i] : K)) →
    ∀ T : List Bool, prodRoots r T ^ 2 = ((Curves.MT.prodSub s T : ℚ) : K)
  | [], [], _, _, T => by cases T <;> simp [prodRoots, Curves.MT.prodSub]
  | x :: s, y :: r, hl, hr, [] => by simp [prodRoots, Curves.MT.prodSub]
  | x :: s, y :: r, hl, hr, b :: T => by
    have hl' : r.length = s.length := by simpa using hl
    have hr' : ∀ i (hi : i < r.length) (hi' : i < s.length), r[i] ^ 2 = (s[i] : K) :=
      fun i hi hi' ↦ hr (i + 1) (by simp; omega) (by simp; omega)
    have hy : y ^ 2 = (x : K) := hr 0 (by simp) (by simp)
    simp only [prodRoots, Curves.MT.prodSub]
    rw [mul_pow, prodRoots_sq s r hl' hr' T]
    cases b <;> simp [hy]
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

/-- **Distinct subsets give `ℚ`-independent products of roots.** -/
theorem prodRoots_indep (s : List ℚ) (r : List K) (hl : r.length = s.length)
    (hr : ∀ i (hi : i < r.length) (hi' : i < s.length), r[i] ^ 2 = (s[i] : K)) (hm : MIndep s)
    {n : ℕ} (T : Fin n → List Bool) (hT : ∀ k, (T k).length = r.length) (hinj : Function.Injective T)
    (e : Fin n → ℚ) (he : ∑ k, (e k : K) * prodRoots r (T k) = 0) : ∀ k, e k = 0 := by
  classical
  set c : ℕ → ℚ := fun i ↦ ∑ k, if bidx (T k) = i then e k else 0 with hc
  have hP : (prods r).length = 2 ^ r.length := length_prods r
  have hlt : ∀ k, bidx (T k) < 2 ^ r.length := fun k ↦ by rw [← hT k]; exact bidx_lt _
  have hcomb : comb c (prods r) = 0 := by
    rw [← he]
    unfold comb
    simp only [hc, Rat.cast_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.sum_eq_single (bidx (T k))]
    · simp only [if_true]; rw [prods_getD_bidx r (T k) (hT k)]
    · intro i _ hi; rw [if_neg (Ne.symm hi)]; simp
    · intro h; exact absurd (Finset.mem_range.mpr (by rw [hP]; exact hlt k)) h
  intro k
  have h0 := prods_indep s r hl hr hm c hcomb (bidx (T k)) (by rw [hP]; exact hlt k)
  rw [hc] at h0
  simp only at h0
  rwa [Finset.sum_eq_single k (fun k' _ hk' ↦ if_neg fun h ↦ hk' (hinj
    (bidx_inj _ _ (by rw [hT, hT]) h))) (by simp), if_pos rfl] at h0

end SqrtIndep

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **Lifting an elementary integral** into an extension with constant square roots of `κs`. -/
theorem kqm_lift (m : ℕ) (hn : T.n = m + 1) (A : GPoly (LC m)) (θ : L)
    (hθ : θ ^ 2 = T.evP m A) (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (f : LC (m + 1)) (hf : HasElementaryIntegral (T.ev (m + 1) f * θ)) (κs : List ℚ)
    (hκ : ∀ κ ∈ κs, κ ≠ 0) :
    ∃ (E : Type u) (_ : Field E) (_ : Differential E) (_ : CharZero E)
      (TE : MTower Fc ks (constants E) E) (θE : E) (rts : List E) (ι : Type) (sI : Finset ι) (c u : ι → E)
      (v : E), TE.n = m + 1 ∧ θE ^ 2 = TE.evP m A ∧ rts.length = κs.length ∧
      (∀ i (hi : i < rts.length) (hi' : i < κs.length), rts[i] ^ 2 = (κs[i] : E) ∧ rts[i]′ = 0) ∧
      (∀ i ∈ sI, (c i)′ = 0) ∧
      (∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (TE.F (m + 1)) {θE}) ∧
      v ∈ IntermediateField.adjoin (TE.F (m + 1)) {θE} ∧
      TE.ev (m + 1) f * θE = v′ + ∑ i ∈ sI, c i * logDeriv (u i) := by
  classical
  obtain ⟨E₁, _, _, _, _, hE₁, g, hg⟩ := hf
  haveI : CharZero E₁ := charZero_of_injective_algebraMap (algebraMap L E₁).injective
  obtain ⟨E₂, _, _, _, _, hE₁₂, -, rts, hrl, hrts⟩ := sqrts_ext E₁ κs hκ
  haveI : CharZero E₂ := charZero_of_injective_algebraMap (algebraMap E₁ E₂).injective
  letI : Algebra L E₂ := ((algebraMap E₁ E₂).comp (algebraMap L E₁)).toAlgebra
  haveI : IsScalarTower L E₁ E₂ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI hDA₂ : DifferentialAlgebra L E₂ :=
    ⟨fun z ↦ by
      change (algebraMap E₁ E₂ (algebraMap L E₁ z))′ = algebraMap E₁ E₂ (algebraMap L E₁ z′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  have hE₂ : IsElementaryExtension L E₂ := hE₁.trans hE₁₂
  have hg₂ : (algebraMap E₁ E₂ g)′ = algebraMap L E₂ (T.ev (m + 1) f * θ) := by
    rw [deriv_algebraMap, hg]; rfl
  obtain ⟨ι, sI, c, u, v, hdata, hv, heqL⟩ := liouville_strong hE₂ _ _ hg₂
  obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E₂
  set ψ := algebraMap L E₂ with hψ
  have hPE : ∀ P : GPoly (LC m), TE.evP m P = ψ (T.evP m P) := fun P ↦ by
    induction P with
    | nil => simp [evP, evPL]
    | cons a P ih =>
      simp only [evP, evPL, List.foldr_cons] at ih ⊢
      rw [ih, map_add, map_mul, hTEts m, ← hTEev m a]
  set θE := ψ θ
  have hT1 : ∀ w ∈ TE.F (m + 1), w ∈ IntermediateField.adjoin (TE.F (m + 1)) {θE} :=
    fun w hw ↦ IntermediateField.algebraMap_mem _ (⟨w, hw⟩ : TE.F (m + 1))
  have hLT : ∀ z : L, ψ z ∈ IntermediateField.adjoin (TE.F (m + 1)) {θE} := by
    intro z
    have hz := hgen z
    induction hz using IntermediateField.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact mem_adjoin_simple_self _ _
    | algebraMap w => exact hT1 _ (hTEmem (m + 1) _ w.2)
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => rw [map_mul]; exact mul_mem h₁ h₂
    | inv w _ h₁ => rw [map_inv₀]; exact inv_mem h₁
  have hCT : ∀ w ∈ Differential.constField L E₂, w ∈ IntermediateField.adjoin (TE.F (m + 1)) {θE} := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem w hw =>
      obtain ⟨c0, hc0⟩ := TE.hconst w hw
      rw [← hc0]
      exact hT1 _ (TE.const_mem (m + 1) c0)
    | algebraMap z => exact hLT z
    | add w₁ w₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂
    | inv w _ h₁ => exact inv_mem h₁
  refine ⟨E₂, inferInstance, inferInstance, inferInstance, TE, θE, rts, ι, sI, c, u, v,
    by rw [hTEn, hn], by rw [hPE, ← map_pow, hθ], hrl, hrts, fun i hi ↦ (hdata i hi).1,
    fun i hi ↦ ⟨(hdata i hi).2.2, hCT _ (hdata i hi).2.1⟩, hCT _ hv, ?_⟩
  rw [hTEev (m + 1) f, show ψ (T.ev (m + 1) f) * θE = ψ (T.ev (m + 1) f * θ) from
    (map_mul ψ _ _).symm, heqL]
  ring


section MCodes

variable [Fact (Irreducible (toPoly (fKc Fc)))]
variable (m : ℕ) (hm : T.Tr m) (η : LC m) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))

omit [CharZero Cc] [CharZero L] in
lemma kqGens_spec :
    SqrtIndep.MIndep (kqGens Fc ks m η A B l cs) ∧ ∀ g ∈ kqGens Fc ks m η A B l cs, g ≠ 0 := by
  obtain ⟨h1, h2, -⟩ := gensOf_spec (kqKs Fc ks m η A B l cs)
  exact ⟨h1, h2⟩

omit [CharZero Cc] [CharZero L] in
lemma kqRep_spec (hrep : kqRepOK Fc ks m η A B l cs = true) (q : ℕ) (hq : q < cs.length) :
    (kqRep Fc ks m η A B l cs q).1.length = (kqGens Fc ks m η A B l cs).length ∧
      kqK Fc ks m η A B l cs q = (kqRep Fc ks m η A B l cs q).2 ^ 2 *
        kqS Fc ks m η A B l cs (kqRep Fc ks m η A B l cs q).1 ∧
      0 ≤ (kqRep Fc ks m η A B l cs q).2 := by
  have h := List.all_eq_true.mp hrep q (List.mem_range.mpr hq)
  obtain ⟨⟨T', c'⟩, hTc⟩ := Option.isSome_iff_exists.mp h
  have hr : kqRep Fc ks m η A B l cs q = (T', c') := by simp [kqRep, hTc]
  rw [hr]
  exact findRep_spec _ (kqGens_spec m η A B l cs).2 _ T' c' hTc

omit [CharZero Cc] [CharZero L] in
lemma kqMNm_eq (q : ℕ) (hq : q < cs.length) (h0 : 0 ≤ (kqRep Fc ks m η A B l cs q).2) :
    (kqMNm Fc ks m η A B l cs q : ℚ) =
      kqDenM Fc ks m η A B l cs * (kqRep Fc ks m η A B l cs q).2 := by
  set x := (kqRep Fc ks m η A B l cs q).2 with hx
  have hdvd : x.den ∣ kqDenM Fc ks m η A B l cs := by
    apply List.dvd_prod
    exact List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩
  obtain ⟨k, hk⟩ := hdvd
  have hk' : kqDenM Fc ks m η A B l cs / x.den = k := by
    rw [hk, Nat.mul_div_cancel_left _ x.den_pos]
  have hnn : 0 ≤ ((k : ℤ) * x.num) := mul_nonneg (by positivity) (Rat.num_nonneg.mpr h0)
  simp only [kqMNm, ← hx, hk']
  rw [show (((k : ℤ) * x.num).toNat : ℚ) = (((k : ℤ) * x.num : ℤ) : ℚ) by
    rw [← Int.toNat_of_nonneg hnn]; rfl]
  rw [hk]
  push_cast
  rw [mul_comm (x.den : ℚ), mul_assoc, mul_comm (x.den : ℚ), Rat.mul_den_eq_num]

omit [CharZero Cc] [CharZero L] in
lemma kqDenM_pos : 0 < kqDenM Fc ks m η A B l cs :=
  List.prod_pos fun x hx ↦ by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact Rat.den_pos _

lemma sem_kqBm (q : ℕ) :
    (T.MP m hm).sem (kqBm Fc ks m η A B l cs q) =
      ((kqS Fc ks m η A B l cs (kqRep Fc ks m η A B l cs q).1 * (kqRep Fc ks m η A B l cs q).2 : ℚ) :
        T.F m) * ((T.MP m hm).sem (kqD Fc ks m η cs q) * (T.MP m hm).sem (kqR Fc ks m A l cs q) /
          (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q))) := by
  simp only [kqBm]
  rw [T.sem_normC m hm, (T.MP m hm).sem_mul, T.sem_mcst, (T.MP m hm).sem_mul, (T.MP m hm).sem_mul,
    (T.MP m hm).sem_inv, T.sem_evalGC m hm]
  ring

lemma toPoly_kqFKm (T' : List Bool) :
    (toPoly (kqFKm Fc ks m η A B l cs T')).map (T.psiF m hm) =
      Polynomial.C ((kqS Fc ks m η A B l cs T' : ℚ) : T.F m) * GPoly.toPoly (T.MP m hm) A := by
  rw [kqFKm, CPoly.toPoly_trim, T.toPoly_trC_map m hm]
  have e : A.map ((MO Fc ks m).mul (mcst Fc ks m (kqS Fc ks m η A B l cs T'))) =
      GPoly.smul (MO Fc ks m) (mcst Fc ks m (kqS Fc ks m η A B l cs T')) A := rfl
  rw [e, GPoly.toPoly_smul, T.sem_mcst]

omit [CharZero Cc] [CharZero L] in
lemma mem_kqQs (T' : List Bool) (q : ℕ) :
    q ∈ kqQs Fc ks m η A B l cs T' ↔ q < cs.length ∧ (kqRep Fc ks m η A B l cs q).1 = T' := by
  simp [kqQs, List.mem_filter, List.mem_range]

omit [CharZero Cc] [CharZero L] in
lemma kqQs_nodup (T' : List Bool) : (kqQs Fc ks m η A B l cs T').Nodup :=
  (List.nodup_range).filter _

end MCodes

section Poles

variable [Fact (Irreducible (toPoly (fKc Fc)))]

open Classical in
/-- **The poles on `y² = A`**: `β_q = c_q μ_{T_q} (η − c_q′) R_q / B(c_q)` with
`μ_T = ∏_{i ∈ T} √gᵢ` is a point over `c_q` where the residue is `m_q μ_{T_q} / M`. -/
theorem kqm_pole (m : ℕ) (hM : T.MixHyp (m + 1)) {η : LC m} (hk : ks m = .prim η)
    (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))
    (hok : kqOK Fc ks m A B l cs = true) (hcst : kqConst Fc ks m η A B l cs = true)
    (hrep : kqRepOK Fc ks m η A B l cs = true)
    (rts : List (T.F m)) (hrl : rts.length = (kqGens Fc ks m η A B l cs).length)
    (hrs : ∀ i (hi : i < rts.length) (hi' : i < (kqGens Fc ks m η A B l cs).length),
      rts[i] ^ 2 = ((kqGens Fc ks m η A B l cs)[i] : T.F m)) (q : ℕ) (hq : q < cs.length) :
    let hm : T.Tr m := hM.tr.of_succ
    let μ := SqrtIndep.prodRoots rts (kqRep Fc ks m η A B l cs q).1
    let bq := ((kqRep Fc ks m η A B l cs q).2 : T.F m) * μ *
      ((T.MP m hm).sem (kqD Fc ks m η cs q) * (T.MP m hm).sem (kqR Fc ks m A l cs q) /
        (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q)))
    μ ^ 2 = ((kqS Fc ks m η A B l cs (kqRep Fc ks m η A B l cs q).1 : ℚ) : T.F m) ∧ μ ≠ 0 ∧
      bq ≠ 0 ∧ bq ^ 2 = (GPoly.toPoly (T.MP m hm) A).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) ∧
      (T.MP m hm).sem (kqBm Fc ks m η A B l cs q) = μ * bq ∧
      (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) * bq =
        (kqMNm Fc ks m η A B l cs q : T.F m) * (μ / (kqDenM Fc ks m η A B l cs : T.F m)) *
          (T.val m η - ((T.MP m hm).sem (kqC Fc ks m cs q))′) *
          (T.MP m hm).sem (kqR Fc ks m A l cs q) := by
  intro hm μ bq
  obtain ⟨hTl, hκ, hc0⟩ := kqRep_spec m η A B l cs hrep q hq
  obtain ⟨hmi, hg0⟩ := kqGens_spec (Fc := Fc) (ks := ks) m η A B l cs
  have hok' := T.kqOK_spec m hm A B l cs hok q hq
  have hQ := T.kqConst_spec m hm η A B l cs hcst q hq
  rw [T.sem_kqQ m hm] at hQ
  have hκ0 := T.kqK_ne m hM hk A B l cs hok hcst q hq
  have hμ2 : μ ^ 2 = ((kqS Fc ks m η A B l cs (kqRep Fc ks m η A B l cs q).1 : ℚ) : T.F m) :=
    SqrtIndep.prodRoots_sq _ rts hrl hrs _
  have hS0 : kqS Fc ks m η A B l cs (kqRep Fc ks m η A B l cs q).1 ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hκ; exact hκ0 hκ
  have hμ0 : μ ≠ 0 := fun h0 ↦ hS0 (by
    have := hμ2; rw [h0, zero_pow two_ne_zero] at this; exact_mod_cast this.symm)
  have hcq0 : (kqRep Fc ks m η A B l cs q).2 ≠ 0 := by
    intro h0; rw [h0] at hκ; simp at hκ; exact hκ0 hκ
  have hd0 : (T.MP m hm).sem (kqD Fc ks m η cs q) ≠ 0 := fun h0 ↦ by
    rw [T.sem_kqD m hm, T.sem_eq_val m hm η] at h0
    exact T.kqS_good m hM hk (algebraMap (T.F m) _ ((T.MP m hm).sem (kqC Fc ks m cs q)))
      (by rw [deriv_algebraMap, ← sub_eq_zero.mp h0])
  have hB0 := hok'.2.2
  have hR0 := hok'.1
  refine ⟨hμ2, hμ0, ?_, ?_, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hcq0) hμ0)
      (div_ne_zero (mul_ne_zero hd0 hR0) hB0)
  · have hκF : ((kqK Fc ks m η A B l cs q : ℚ) : T.F m) =
        ((kqRep Fc ks m η A B l cs q).2 : T.F m) ^ 2 * μ ^ 2 := by
      rw [hμ2, hκ]; push_cast; ring
    rw [hκF] at hQ
    simp only [bq]
    rw [show (((kqRep Fc ks m η A B l cs q).2 : T.F m) * μ * ((T.MP m hm).sem (kqD Fc ks m η cs q) *
      (T.MP m hm).sem (kqR Fc ks m A l cs q) / (GPoly.toPoly (T.MP m hm) B).eval
        ((T.MP m hm).sem (kqC Fc ks m cs q)))) ^ 2 = (((kqRep Fc ks m η A B l cs q).2 : T.F m) ^ 2 *
          μ ^ 2) * ((T.MP m hm).sem (kqD Fc ks m η cs q) * (T.MP m hm).sem (kqR Fc ks m A l cs q)) ^ 2 /
          (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) ^ 2 by ring, ← hQ]
    field_simp
  · rw [T.sem_kqBm m hm]
    push_cast
    rw [← hμ2]
    simp only [bq]
    ring
  · have hDen : (kqDenM Fc ks m η A B l cs : T.F m) ≠ 0 := by
      exact_mod_cast (kqDenM_pos (Fc := Fc) (ks := ks) m η A B l cs).ne'
    rw [show (kqMNm Fc ks m η A B l cs q : T.F m) = ((kqMNm Fc ks m η A B l cs q : ℚ) : T.F m) by
      push_cast; rfl, kqMNm_eq m η A B l cs q hq hc0, ← T.sem_eq_val m hm η, ← T.sem_kqD m hm]
    simp only [bq]
    push_cast
    field_simp

end Poles

section Classes

variable [Fact (Irreducible (toPoly (fKc Fc)))]
variable (m : ℕ) (η : LC m) (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))

omit [CharZero Cc] [CharZero L] in
lemma mem_kqCls (q : ℕ) (hq : q < cs.length) :
    (kqRep Fc ks m η A B l cs q).1 ∈ kqCls Fc ks m η A B l cs := by
  rw [kqCls, List.mem_dedup]
  exact List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩

omit [CharZero Cc] [CharZero L] in
lemma kqCls_nodup : (kqCls Fc ks m η A B l cs).Nodup := List.nodup_dedup _

omit [CharZero Cc] [CharZero L] in
lemma kqCls_mem_rep (T' : List Bool) (hT : T' ∈ kqCls Fc ks m η A B l cs) :
    ∃ q < cs.length, (kqRep Fc ks m η A B l cs q).1 = T' := by
  rw [kqCls, List.mem_dedup] at hT
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hT
  exact ⟨q, List.mem_range.mp hq, rfl⟩

/-- The class of a pole. -/
def kqCl (q : Fin cs.length) : Fin (kqCls Fc ks m η A B l cs).length :=
  ⟨(kqCls Fc ks m η A B l cs).idxOf (kqRep Fc ks m η A B l cs q).1,
    List.idxOf_lt_length_of_mem (mem_kqCls m η A B l cs q q.2)⟩

omit [CharZero Cc] [CharZero L] in
lemma kqCls_get_kqCl (q : Fin cs.length) :
    (kqCls Fc ks m η A B l cs)[(kqCl m η A B l cs q : ℕ)] = (kqRep Fc ks m η A B l cs q).1 :=
  List.getElem_idxOf _

omit [CharZero Cc] [CharZero L] in
lemma kqCl_eq_iff (q : Fin cs.length) (k : Fin (kqCls Fc ks m η A B l cs).length) :
    kqCl m η A B l cs q = k ↔ (kqRep Fc ks m η A B l cs q).1 = (kqCls Fc ks m η A B l cs)[(k : ℕ)] := by
  constructor
  · rintro rfl; exact (kqCls_get_kqCl m η A B l cs q).symm
  · intro h
    apply Fin.ext
    simp only [kqCl, h]
    exact (kqCls_nodup m η A B l cs).idxOf_getElem _ _

/-- The poles of the class `k`. -/
def kqIota (k : Fin (kqCls Fc ks m η A B l cs).length)
    (i : Fin (kqQs Fc ks m η A B l cs (kqCls Fc ks m η A B l cs)[(k : ℕ)]).length) :
    Fin cs.length :=
  ⟨(kqQs Fc ks m η A B l cs (kqCls Fc ks m η A B l cs)[(k : ℕ)])[i],
    ((mem_kqQs m η A B l cs _ _).mp (List.getElem_mem _)).1⟩

omit [CharZero Cc] [CharZero L] in
lemma kqIota_cl (k : Fin (kqCls Fc ks m η A B l cs).length) (i) :
    kqCl m η A B l cs (kqIota m η A B l cs k i) = k :=
  (kqCl_eq_iff m η A B l cs _ k).mpr ((mem_kqQs m η A B l cs _ _).mp (List.getElem_mem _)).2

omit [CharZero Cc] [CharZero L] in
lemma kqIota_surj (k : Fin (kqCls Fc ks m η A B l cs).length) (q : Fin cs.length)
    (hq : kqCl m η A B l cs q = k) : ∃ i, kqIota m η A B l cs k i = q := by
  have hmem : (q : ℕ) ∈ kqQs Fc ks m η A B l cs (kqCls Fc ks m η A B l cs)[(k : ℕ)] :=
    (mem_kqQs m η A B l cs _ _).mpr ⟨q.2, (kqCl_eq_iff m η A B l cs q k).mp hq⟩
  obtain ⟨i, hi, hiq⟩ := List.getElem_of_mem hmem
  exact ⟨⟨i, hi⟩, Fin.ext hiq⟩

omit [CharZero Cc] [CharZero L] in
lemma kqIota_inj (k : Fin (kqCls Fc ks m η A B l cs).length) :
    Function.Injective (kqIota m η A B l cs k) := fun i j h ↦ by
  have := congrArg Fin.val h
  simp only [kqIota] at this
  exact Fin.ext ((kqQs_nodup m η A B l cs _).getElem_inj_iff.mp this)

end Classes

section ClassKF

variable [Fact (Irreducible (toPoly (fKc Fc)))]

open Classical in
/-- **The data of a class over `Kₘ`.** -/
theorem kqm_class_KF (m : ℕ) (hM : T.MixHyp (m + 1)) {η : LC m} (hk : ks m = .prim η)
    (A B : GPoly (LC m)) (hsq : Squarefree (GPoly.toPoly (T.MP m hM.tr.of_succ) A))
    (hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hM.tr.of_succ) A).natDegree)
    (l : ℕ) (cs : List (LC m))
    (hok : kqOK Fc ks m A B l cs = true) (hcst : kqConst Fc ks m η A B l cs = true)
    (hrep : kqRepOK Fc ks m η A B l cs = true)
    (rts : List (T.F m)) (hrl : rts.length = (kqGens Fc ks m η A B l cs).length)
    (hrs : ∀ i (hi : i < rts.length) (hi' : i < (kqGens Fc ks m η A B l cs).length),
      rts[i] ^ 2 = ((kqGens Fc ks m η A B l cs)[i] : T.F m))
    (k : Fin (kqCls Fc ks m η A B l cs).length) :
    let hm : T.Tr m := hM.tr.of_succ
    let Tk := (kqCls Fc ks m η A B l cs)[(k : ℕ)]
    let μ := SqrtIndep.prodRoots rts Tk
    let fK := kqFKm Fc ks m η A B l cs Tk
    μ ≠ 0 ∧ Polynomial.C (μ ^ 2) * (Polynomial.C ((1 : T.F m) ^ 2) * GPoly.toPoly (T.MP m hm) A) =
        (toPoly fK).map (T.psiF m hm) ∧
      (toPoly fK).natDegree = fK.length - 1 ∧ Squarefree (toPoly fK) ∧
      Nat.Coprime 2 (fK.length - 1) ∧
      (∀ i, kqBem Fc ks m η A B l cs Tk i ≠ 0 ∧
        kqBem Fc ks m η A B l cs Tk i ^ 2 = (toPoly fK).eval (kqAlm Fc ks m η A B l cs Tk i)) ∧
      Function.Injective (fun i ↦ (kqAlm Fc ks m η A B l cs Tk i, kqBem Fc ks m η A B l cs Tk i)) ∧
      (∀ i, T.psiF m hm (kqAlm Fc ks m η A B l cs Tk i) =
        (T.MP m hm).sem (kqC Fc ks m cs (kqIota m η A B l cs k i))) ∧
      (∀ i, T.psiF m hm (kqBem Fc ks m η A B l cs Tk i) =
        μ * (((kqRep Fc ks m η A B l cs (kqIota m η A B l cs k i)).2 : T.F m) *
          SqrtIndep.prodRoots rts (kqRep Fc ks m η A B l cs (kqIota m η A B l cs k i)).1 *
          ((T.MP m hm).sem (kqD Fc ks m η cs (kqIota m η A B l cs k i)) *
            (T.MP m hm).sem (kqR Fc ks m A l cs (kqIota m η A B l cs k i)) /
            (GPoly.toPoly (T.MP m hm) B).eval
              ((T.MP m hm).sem (kqC Fc ks m cs (kqIota m η A B l cs k i)))))) := by
  intro hm Tk μ fK
  obtain ⟨q0, hq0, hq0T⟩ := kqCls_mem_rep m η A B l cs Tk (List.getElem_mem _)
  have hP0 := T.kqm_pole m hM hk A B l cs hok hcst hrep rts hrl hrs q0 hq0
  rw [hq0T] at hP0
  obtain ⟨hμ2, hμ0, -⟩ := hP0
  have hTi : ∀ i, (kqRep Fc ks m η A B l cs (kqIota m η A B l cs k i)).1 = Tk := fun i ↦
    ((mem_kqQs m η A B l cs _ _).mp (List.getElem_mem _)).2
  have hpf : Polynomial.C (μ ^ 2) * (Polynomial.C ((1 : T.F m) ^ 2) * GPoly.toPoly (T.MP m hm) A) =
      (toPoly fK).map (T.psiF m hm) := by
    rw [T.toPoly_kqFKm m hm, hμ2, one_pow, Polynomial.C_1, one_mul]
  have hsqp : Squarefree (Polynomial.C (μ ^ 2) * (Polynomial.C ((1 : T.F m) ^ 2) *
      GPoly.toPoly (T.MP m hm) A)) := by
    rw [one_pow, Polynomial.C_1, one_mul]
    exact fun x hx ↦ hsq x ((IsUnit.dvd_mul_left
      (Polynomial.isUnit_C.mpr (pow_ne_zero 2 hμ0).isUnit)).mp hx)
  have hcopp : Nat.Coprime 2 (Polynomial.C (μ ^ 2) * (Polynomial.C ((1 : T.F m) ^ 2) *
      GPoly.toPoly (T.MP m hm) A)).natDegree := by
    rw [one_pow, Polynomial.C_1, one_mul, natDegree_C_mul (pow_ne_zero 2 hμ0)]; exact hcopA
  obtain ⟨hd, hsqK, hcop2⟩ := fK_facts' (T.psiF m hm) fK (CPoly.trim_trim _) _ hpf
    hsqp.ne_zero hsqp hcopp
  have hA : ∀ i, T.psiF m hm (kqAlm Fc ks m η A B l cs Tk i) =
      (T.MP m hm).sem (kqC Fc ks m cs (kqIota m η A B l cs k i)) := fun i ↦ T.psiF_trC m hm _
  have hB : ∀ i, T.psiF m hm (kqBem Fc ks m η A B l cs Tk i) =
      μ * (((kqRep Fc ks m η A B l cs (kqIota m η A B l cs k i)).2 : T.F m) *
          SqrtIndep.prodRoots rts (kqRep Fc ks m η A B l cs (kqIota m η A B l cs k i)).1 *
          ((T.MP m hm).sem (kqD Fc ks m η cs (kqIota m η A B l cs k i)) *
            (T.MP m hm).sem (kqR Fc ks m A l cs (kqIota m η A B l cs k i)) /
            (GPoly.toPoly (T.MP m hm) B).eval
              ((T.MP m hm).sem (kqC Fc ks m cs (kqIota m η A B l cs k i))))) := fun i ↦ by
    have hPi := T.kqm_pole m hM hk A B l cs hok hcst hrep rts hrl hrs _ (kqIota m η A B l cs k i).2
    rw [kqBem, T.psiF_trC m hm]
    show (T.MP m hm).sem (kqBm Fc ks m η A B l cs (kqIota m η A B l cs k i : ℕ)) = _
    rw [hPi.2.2.2.2.1, hTi i]
  have hcinj := T.kq_cinj m hm A B l cs hok
  refine ⟨hμ0, hpf, hd, hsqK, hcop2, fun i ↦ ⟨fun h0 ↦ ?_, ?_⟩, fun i j hij ↦ ?_, hA, hB⟩
  · have hPi := T.kqm_pole m hM hk A B l cs hok hcst hrep rts hrl hrs _ (kqIota m η A B l cs k i).2
    have := hB i
    rw [h0, map_zero, hTi i] at this
    exact mul_ne_zero hμ0 (by rw [← hTi i]; exact hPi.2.2.1) this.symm
  · apply (T.psiF m hm).injective
    have hPi := T.kqm_pole m hM hk A B l cs hok hcst hrep rts hrl hrs _ (kqIota m η A B l cs k i).2
    rw [map_pow, hB i, ← eval₂_at_apply, ← eval_map, ← hpf, hA i, eval_mul, eval_C, eval_mul, eval_C,
      one_pow, one_mul, mul_pow, ← hPi.2.2.2.1, hTi i, hμ2]
  · apply kqIota_inj m η A B l cs k
    apply hcinj
    have h1 := congrArg (fun z ↦ T.psiF m hm z.1) hij
    simp only at h1
    rw [hA, hA] at h1
    exact h1

end ClassKF

section Abs

variable [Fact (Irreducible (toPoly (fKc Fc)))]

open Classical in
/-- **The hypotheses of the multi-class Liouville theorems** on `y² = A`, `y = θ`. -/
theorem kqm_abs (m : ℕ) (hM : T.MixHyp (m + 1)) {η : LC m} (hk : ks m = .prim η)
    (A B : GPoly (LC m)) (l : ℕ) (cs : List (LC m))
    (hok : kqOK Fc ks m A B l cs = true) (hcst : kqConst Fc ks m η A B l cs = true)
    (hrep : kqRepOK Fc ks m η A B l cs = true)
    (rts : List (T.F m)) (hrl : rts.length = (kqGens Fc ks m η A B l cs).length)
    (hrs : ∀ i (hi : i < rts.length) (hi' : i < (kqGens Fc ks m η A B l cs).length),
      rts[i] ^ 2 = ((kqGens Fc ks m η A B l cs)[i] : T.F m)) :
    let hm : T.Tr m := hM.tr.of_succ
    let β : Fin cs.length → T.F m := fun q ↦ ((kqRep Fc ks m η A B l cs q).2 : T.F m) *
      SqrtIndep.prodRoots rts (kqRep Fc ks m η A B l cs q).1 *
      ((T.MP m hm).sem (kqD Fc ks m η cs q) * (T.MP m hm).sem (kqR Fc ks m A l cs q) /
        (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q)))
    let ρ : Fin (kqCls Fc ks m η A B l cs).length → T.F m := fun k ↦
      SqrtIndep.prodRoots rts (kqCls Fc ks m η A B l cs)[(k : ℕ)] / (kqDenM Fc ks m η A B l cs : T.F m)
    let p := Polynomial.C ((1 : T.F m) ^ 2) * GPoly.toPoly (T.MP m hm) A
    (∀ q : Fin cs.length, β q ≠ 0 ∧ β q ^ 2 = p.eval ((T.MP m hm).sem (kqC Fc ks m cs q))) ∧
      (∀ q : Fin cs.length, (Polynomial.C ((1 : T.F m) ^ (2 * l) / 1) * GPoly.toPoly (T.MP m hm) B).eval
          ((T.MP m hm).sem (kqC Fc ks m cs q)) * β q =
        (kqMNm Fc ks m η A B l cs q : T.F m) * ρ (kqCl m η A B l cs q) *
          (T.val m η - ((T.MP m hm).sem (kqC Fc ks m cs q))′) *
          (GPoly.toPoly (T.MP m hm) (prodLinG Fc ks m (cs.eraseIdx q)) * p ^ l).eval
            ((T.MP m hm).sem (kqC Fc ks m cs q))) ∧
      (∀ e : Fin (kqCls Fc ks m η A B l cs).length → ℚ, ∑ kk, (e kk : T.F m) * ρ kk = 0 →
        ∀ kk, e kk = 0) := by
  intro hm β ρ p
  have hp : ∀ z, p.eval z = (GPoly.toPoly (T.MP m hm) A).eval z := fun z ↦ by
    simp [p]
  refine ⟨fun q ↦ ?_, fun q ↦ ?_, fun e he ↦ ?_⟩
  · have hP := T.kqm_pole m hM hk A B l cs hok hcst hrep rts hrl hrs q q.2
    exact ⟨hP.2.2.1, by rw [hp]; exact hP.2.2.2.1⟩
  · have hP := T.kqm_pole m hM hk A B l cs hok hcst hrep rts hrl hrs q q.2
    have hρq : ρ (kqCl m η A B l cs q) = SqrtIndep.prodRoots rts (kqRep Fc ks m η A B l cs q).1 /
        (kqDenM Fc ks m η A B l cs : T.F m) := by
      simp only [ρ]; rw [kqCls_get_kqCl]
    rw [hρq, eval_mul, eval_C, eval_mul, eval_pow, hp, ← T.sem_kqR m hm, one_pow, div_one, one_mul]
    exact hP.2.2.2.2.2
  · have hDen : (kqDenM Fc ks m η A B l cs : T.F m) ≠ 0 := by
      exact_mod_cast (kqDenM_pos (Fc := Fc) (ks := ks) m η A B l cs).ne'
    have he' : ∑ kk, (e kk : T.F m) * SqrtIndep.prodRoots rts (kqCls Fc ks m η A B l cs)[(kk : ℕ)] = 0 := by
      have : ∑ kk, (e kk : T.F m) * ρ kk =
          (∑ kk, (e kk : T.F m) * SqrtIndep.prodRoots rts (kqCls Fc ks m η A B l cs)[(kk : ℕ)]) /
            (kqDenM Fc ks m η A B l cs : T.F m) := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun kk _ ↦ by simp only [ρ]; ring
      rw [this, div_eq_zero_iff] at he
      exact he.resolve_right hDen
    obtain ⟨hmi, hg0⟩ := kqGens_spec (Fc := Fc) (ks := ks) m η A B l cs
    refine SqrtIndep.prodRoots_indep _ rts hrl hrs hmi (fun kk ↦ (kqCls Fc ks m η A B l cs)[(kk : ℕ)])
      (fun kk ↦ ?_) (fun i j hij ↦ Fin.ext ((kqCls_nodup m η A B l cs).getElem_inj_iff.mp hij)) e he'
    obtain ⟨q, hq, hqT⟩ := kqCls_mem_rep (Fc := Fc) (ks := ks) m η A B l cs _ (List.getElem_mem _)
    rw [← hqT, hrl]
    exact (kqRep_spec (Fc := Fc) (ks := ks) m η A B l cs hrep q hq).1

end Abs

section Forward

variable [Fact (Irreducible (toPoly (fKc Fc)))]

/-- The constant roots, as elements of `Fₘ`. -/
lemma roots_F (m : ℕ) (rts : List L) (h : ∀ i (hi : i < rts.length), (rts[i])′ = 0) :
    ∃ rtsF : List (T.F m), rtsF.length = rts.length ∧
      ∀ i (hi : i < rtsF.length) (hi' : i < rts.length), ((rtsF[i] : T.F m) : L) = rts[i] := by
  have hmem : ∀ i (hi : i < rts.length), rts[i] ∈ T.F m := fun i hi ↦ by
    obtain ⟨c0, hc0⟩ := T.hconst _ (h i hi)
    rw [← hc0]; exact T.const_mem m c0
  refine ⟨List.ofFn fun i : Fin rts.length ↦ (⟨rts[i], hmem i i.2⟩ : T.F m), by simp,
    fun i hi hi' ↦ ?_⟩
  simp

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Forward, a class without torsion**: no Liouville form. -/
theorem kqm_forward_nontors (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (hok : kqOK Fc ks m A B l cs = true)
    (hcst : kqConst Fc ks m η A B l cs = true) (hrep : kqRepOK Fc ks m η A B l cs = true)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (cpf : CPoly (KF Fc m) → CertProv (KF Fc m))
    (k : Fin (kqCls Fc ks m η A B l cs).length)
    (htors : kqTorsC Fc ks m η A B l cs cpf ps bound rs (kqCls Fc ks m η A B l cs)[(k : ℕ)] = some none)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) {ι : Type} (sI : Finset ι)
    (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
      (powG (MO Fc ks m) A l)) : LC (m + 1)) * θ = v′ + ∑ i ∈ sI, c i * logDeriv (u i))
    (rts : List L) (hrl : rts.length = (kqGens Fc ks m η A B l cs).length)
    (hrts : ∀ i (hi : i < rts.length) (hi' : i < (kqGens Fc ks m η A B l cs).length),
      rts[i] ^ 2 = ((kqGens Fc ks m η A B l cs)[i] : L) ∧ rts[i]′ = 0) : False := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  have hA0 : T.evP m A ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) A hdegpos
  obtain ⟨rtsF, hFl, hFv⟩ := T.roots_F m rts (fun i hi ↦ (hrts i hi (by omega)).2)
  have hrlF : rtsF.length = (kqGens Fc ks m η A B l cs).length := by rw [hFl, hrl]
  have hrsF : ∀ i (hi : i < rtsF.length) (hi' : i < (kqGens Fc ks m η A B l cs).length),
      rtsF[i] ^ 2 = ((kqGens Fc ks m η A B l cs)[i] : T.F m) := fun i hi hi' ↦ Subtype.ext (by
    rw [IntermediateField.coe_pow, hFv i hi (by omega), (hrts i (by omega) hi').1]; simp)
  obtain ⟨hb, hby, hbm, hDR, hDoff, hbP⟩ :=
    T.kq_data m hTr A hsq hdegA θ hθ 1 one_ne_zero (by omega) B l cs hA0
  set S := T.keS m hTr A hsq hdegA θ hθ 1 one_ne_zero with hS
  have hok' := fun q' (hq' : q' < cs.length) ↦ T.kqOK_spec m hTm A B l cs hok q' hq'
  have hRne : ∀ q' : Fin cs.length, (GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q'))).eval
      ((T.MP m hTm).sem (kqC Fc ks m cs q')) ≠ 0 := fun q' h0 ↦ by
    have := (hok' q' q'.2).1
    rw [T.sem_kqR m hTm, h0, zero_mul] at this
    exact this rfl
  have hcinj := T.kq_cinj m hTm A B l cs hok
  have hcopS := T.keS_cop m hTr A hsq hdegA θ hθ 1 one_ne_zero hcopA
  obtain ⟨hβ, hres, hρ⟩ := T.kqm_abs m MS.hyp hk A B l cs hok hcst hrep rtsF hrlF hrsF
  obtain ⟨hμ0, hpf, hd, hsqK, hcop2, hvK, hinjK, hA, hB⟩ :=
    T.kqm_class_KF m MS.hyp hk A B hsq hcopA l cs hok hcst hrep rtsF hrlF hrsF k
  have hspec := torsOracleC_spec (redAtKF Fc m rs)
    (cpf (kqFKm Fc ks m η A B l cs (kqCls Fc ks m η A B l cs)[(k : ℕ)]))
    (fun p _ R h ↦ redAtKF_valid Fc m rs p R h) ps bound hsqK hcop2
  have hnot := (hspec _ _ _ (kqMqm Fc ks m η A B l cs (kqCls Fc ks m η A B l cs)[(k : ℕ)]) hvK
    hinjK).2 htors
  set Tk := (kqCls Fc ks m η A B l cs)[(k : ℕ)] with hTk
  have hΓK : ∀ i : Fin (kqQs Fc ks m η A B l cs Tk).length,
      ((2 : ℕ) : KF Fc m) * kqBem Fc ks m η A B l cs Tk i ^ (2 - 1) ≠ 0 ∧
        kqBem Fc ks m η A B l cs Tk i ^ 2 =
          (toPoly (kqFKm Fc ks m η A B l cs Tk)).eval (kqAlm Fc ks m η A B l cs Tk i) := fun i ↦
    ⟨by rw [pow_one]; exact mul_ne_zero (by norm_num) (hvK i).1, (hvK i).2⟩
  have hnt := S.class_not_principal (K := AlgebraicClosure (T.F m)) rfl hcopS
    (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) _ hcinj
    (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) (fun q ↦ kqMNm Fc ks m η A B l cs q) (kqCl m η A B l cs) k
    (kqIota m η A B l cs k) (kqIota_cl m η A B l cs k) (kqIota_surj m η A B l cs k)
    (kqIota_inj m η A B l cs k) (T.psiF m hTm) _ _ hμ0 hpf hd _ _ hA hB _ (fun i ↦ rfl) hΓK hnot
  obtain ⟨q0, hq0, hq0T⟩ := kqCls_mem_rep (Fc := Fc) (ks := ks) m η A B l cs _ (List.getElem_mem _)
  have hk0 : ∃ q, kqCl m η A B l cs q = k ∧ kqMNm Fc ks m η A B l cs q ≠ 0 := by
    refine ⟨⟨q0, hq0⟩, (kqCl_eq_iff m η A B l cs _ k).mpr hq0T, fun h0 ↦ ?_⟩
    obtain ⟨-, hκ, hc0⟩ := kqRep_spec (Fc := Fc) (ks := ks) m η A B l cs hrep q0 hq0
    have hm := kqMNm_eq (Fc := Fc) (ks := ks) m η A B l cs q0 hq0 hc0
    rw [h0, Nat.cast_zero, eq_comm, mul_eq_zero] at hm
    rcases hm with h | h
    · exact (kqDenM_pos (Fc := Fc) (ks := ks) m η A B l cs).ne' (by exact_mod_cast h)
    · rw [h] at hκ; simp at hκ
      exact T.kqK_ne m MS.hyp hk A B l cs hok hcst q0 hq0 hκ
  exact S.kqm_liouville_nontors (K := AlgebraicClosure (T.F m)) (T.val m η)
    (T.kqS_hx m hTr A hsq hdegA θ hθ 1 one_ne_zero (by omega) hk) (fun c ↦ deriv_algebraMap c)
    (T.kqS_good m MS.hyp hk) (T.keS_constC m)
    (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) _ hcinj
    (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) (fun q ↦ kqMNm Fc ks m η A B l cs q) (kqCl m η A B l cs) _
    (Polynomial.C ((1 : T.F m) ^ (2 * l) / 1) * GPoly.toPoly (T.MP m hTm) B) l _ hb
    (GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m cs))
    (fun q' ↦ GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q'))) hDR hRne hDoff hbP
    hres rfl k hk0 hρ hnt hbm sI c u hcd
    (fun i hi ↦ ⟨(hu i hi).1, T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ (hu i hi).2⟩) v
    (T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ hv) (by rw [hby]; exact heq)

set_option maxHeartbeats 4000000 in
open Classical in
theorem kqm_forward_tors (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (hok : kqOK Fc ks m A B l cs = true)
    (hcst : kqConst Fc ks m η A B l cs = true) (hrep : kqRepOK Fc ks m η A B l cs = true)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (cpf : CPoly (KF Fc m) → CertProv (KF Fc m))
    (Ns : Fin (kqCls Fc ks m η A B l cs).length → ℕ)
    (htors : ∀ k : Fin (kqCls Fc ks m η A B l cs).length,
      kqTorsC Fc ks m η A B l cs cpf ps bound rs (kqCls Fc ks m η A B l cs)[(k : ℕ)] = some (some (Ns k)))
    (Wbs : Fin (kqCls Fc ks m η A B l cs).length → BPoly (KF Fc m))
    (hwit : ∀ k : Fin (kqCls Fc ks m η A B l cs).length,
      kqWit Fc ks m η A B l cs (kqCls Fc ks m η A B l cs)[(k : ℕ)] (Ns k) = some (Wbs k))
    (θ : L) (hθ : θ ^ 2 = T.evP m A) {ι : Type} (sI : Finset ι)
    (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
      (powG (MO Fc ks m) A l)) : LC (m + 1)) * θ = v′ + ∑ i ∈ sI, c i * logDeriv (u i))
    (rts : List L) (hrl : rts.length = (kqGens Fc ks m η A B l cs).length)
    (hrts : ∀ i (hi : i < rts.length) (hi' : i < (kqGens Fc ks m η A B l cs).length),
      rts[i] ^ 2 = ((kqGens Fc ks m η A B l cs)[i] : L) ∧ rts[i]′ = 0) :
    (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)
      (((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs) (powG (MO Fc ks m) A l)) : LC (m + 1)) ::
        List.ofFn fun k ↦ kqCol Fc ks m η A B l cs (kqCls Fc ks m η A B l cs)[(k : ℕ)] (Wbs k))).any
      (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) = true := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  have hA0 : T.evP m A ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) A hdegpos
  obtain ⟨rtsF, hFl, hFv⟩ := T.roots_F m rts (fun i hi ↦ (hrts i hi (by omega)).2)
  have hrlF : rtsF.length = (kqGens Fc ks m η A B l cs).length := by rw [hFl, hrl]
  have hrsF : ∀ i (hi : i < rtsF.length) (hi' : i < (kqGens Fc ks m η A B l cs).length),
      rtsF[i] ^ 2 = ((kqGens Fc ks m η A B l cs)[i] : T.F m) := fun i hi hi' ↦ Subtype.ext (by
    rw [IntermediateField.coe_pow, hFv i hi (by omega), (hrts i (by omega) hi').1]; simp)
  obtain ⟨hb, hby, hbm, hDR, hDoff, hbP⟩ :=
    T.kq_data m hTr A hsq hdegA θ hθ 1 one_ne_zero (by omega) B l cs hA0
  set S := T.keS m hTr A hsq hdegA θ hθ 1 one_ne_zero with hS
  have hok' := fun q' (hq' : q' < cs.length) ↦ T.kqOK_spec m hTm A B l cs hok q' hq'
  have hRne : ∀ q' : Fin cs.length, (GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q'))).eval
      ((T.MP m hTm).sem (kqC Fc ks m cs q')) ≠ 0 := fun q' h0 ↦ by
    have := (hok' q' q'.2).1
    rw [T.sem_kqR m hTm, h0, zero_mul] at this
    exact this rfl
  have hcinj := T.kq_cinj m hTm A B l cs hok
  have hcopS := T.keS_cop m hTr A hsq hdegA θ hθ 1 one_ne_zero hcopA
  obtain ⟨hβ, hres, hρ⟩ := T.kqm_abs m MS.hyp hk A B l cs hok hcst hrep rtsF hrlF hrsF
  have hKF := fun k ↦ T.kqm_class_KF m MS.hyp hk A B hsq hcopA l cs hok hcst hrep rtsF hrlF hrsF k
  set Tk : Fin (kqCls Fc ks m η A B l cs).length → List Bool := fun k ↦ (kqCls Fc ks m η A B l cs)[(k : ℕ)] with hTk
  set μ : Fin (kqCls Fc ks m η A B l cs).length → T.F m := fun k ↦ SqrtIndep.prodRoots rtsF (Tk k) with hμ
  -- the orders `N_k` and the witnesses
  have hN : ∀ k, 1 ≤ Ns k := fun k ↦ by
    obtain ⟨-, -, -, hsqK, hcop2, hvK, hinjK, -, -⟩ := hKF k
    have hspec := torsOracleC_spec (redAtKF Fc m rs) (cpf (kqFKm Fc ks m η A B l cs (Tk k)))
      (fun p _ R h ↦ redAtKF_valid Fc m rs p R h) ps bound hsqK hcop2
    exact ((hspec _ _ _ (kqMqm Fc ks m η A B l cs (Tk k)) hvK hinjK).1 (Ns k) (htors k)).1
  set Wp : Fin (kqCls Fc ks m η A B l cs).length → (T.F m)[X][X] := fun k ↦ (toB (Wbs k)).map (mapRingHom (T.psiF m hTm)) with hWp
  set Wk : Fin (kqCls Fc ks m η A B l cs).length → (T.F m)[X][X] := fun k ↦
    (Wp k).comp (Polynomial.C (Polynomial.C (μ k)) * X) with hWk
  have hWit : ∀ k, S.elemW (Wk k) ≠ 0 ∧ ∀ a b : AlgebraicClosure (T.F m),
      b ^ S.n = (S.p.map (algebraMap (T.F m) _)).eval a →
        S.ordAt (AlgebraicClosure (T.F m)) (S.elemW (Wk k)) a b =
          Ns k * Differential.SuperData.gammaQ (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) _
            (Differential.SuperData.mK (fun q ↦ kqMNm Fc ks m η A B l cs q) (kqCl m η A B l cs) k)
              (a, b) := fun k ↦ by
    obtain ⟨hμ0, hpf, hd, hsqK, hcop2, hvK, hinjK, hA, hB⟩ := hKF k
    have hΓK : ∀ i : Fin (kqQs Fc ks m η A B l cs (Tk k)).length,
        ((2 : ℕ) : KF Fc m) * kqBem Fc ks m η A B l cs (Tk k) i ^ (2 - 1) ≠ 0 ∧
          kqBem Fc ks m η A B l cs (Tk k) i ^ 2 =
            (toPoly (kqFKm Fc ks m η A B l cs (Tk k))).eval (kqAlm Fc ks m η A B l cs (Tk k) i) :=
      fun i ↦ ⟨by rw [pow_one]; exact mul_ne_zero (by norm_num) (hvK i).1, (hvK i).2⟩
    exact S.class_witness (K := AlgebraicClosure (T.F m)) rfl hcopS
      (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) _ hcinj
      (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) (fun q ↦ kqMNm Fc ks m η A B l cs q) (kqCl m η A B l cs) k
      (kqIota m η A B l cs k) (kqIota_cl m η A B l cs k) (kqIota_surj m η A B l cs k)
      (kqIota_inj m η A B l cs k) (T.psiF m hTm) _ _ hμ0 hpf hd _ _ hA hB _ (fun i ↦ rfl) hΓK
      (Ns k) (Wbs k) (hwit k)
  have hmemx : ∀ P : (T.F m)[X], aeval (T.ts m) P ∈ (T.F m)⟮S.x⟯ := fun P ↦ by
    letI := algebraAdjoinSimple (F := T.F m) S.x
    rw [show aeval (T.ts m) P = aeval S.x P from rfl, ← algebraMap_adjoinSimple (F := T.F m) S.x P]
    exact SetLike.coe_mem _
  set W0 : Fin (kqCls Fc ks m η A B l cs).length → L := fun k ↦ aeval (T.ts m) ((Wp k).coeff 0) with hW0
  set W1c : Fin (kqCls Fc ks m η A B l cs).length → L := fun k ↦ aeval (T.ts m) ((Wp k).coeff 1)
    with hW1c
  set W1 : Fin (kqCls Fc ks m η A B l cs).length → L := fun k ↦ ((μ k : T.F m) : L) * W1c k with hW1
  have hWe : ∀ k, ((S.elemW (Wk k) : (T.F m)⟮S.x⟯⟮S.y⟯) : L) = W0 k + W1 k * S.y := fun k ↦ by
    rw [T.elemW_two S rfl (Wk k)]
    simp only [hWk, comp_C_mul_X_coeff, pow_zero, mul_one, pow_one, hW0, hW1, hW1c]
    rw [map_mul, aeval_C]
    simp only [IntermediateField.algebraMap_apply]
    have hSx : S.x = T.ts m := rfl
    rw [hSx]
    ring
  have hW1m : ∀ k, W1 k ∈ (T.F m)⟮S.x⟯ := fun k ↦
    mul_mem (IntermediateField.algebraMap_mem _ (μ k)) (hmemx _)
  have hNm : ∀ k, W0 k ^ 2 - W1 k ^ 2 * aeval S.x S.p ≠ 0 := fun k h0 ↦ by
    have hWne := (hWit k).1
    have hy2 : S.y ^ 2 = aeval S.x S.p := S.hy
    have hodd : Odd S.p.natDegree := by
      rw [← Nat.coprime_two_left]; exact hcopS
    have hny := not_mem_of_sq_odd (C := T.F m) S.x S.y S.htr S.p hodd hy2
    have hfac : (W0 k + W1 k * S.y) * (W0 k - W1 k * S.y) = 0 := by rw [← h0, ← hy2]; ring
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact hWne (Subtype.ext (by rw [hWe k, h1]; rfl))
    · by_cases hw1 : W1 k = 0
      · apply hWne; apply Subtype.ext
        rw [hWe k, hw1, zero_mul, add_zero]
        rw [hw1, zero_mul, sub_zero] at h1
        rw [h1]; rfl
      · apply hny
        rw [show S.y = W0 k / W1 k by field_simp; linear_combination -h1]
        exact div_mem (hmemx _) (hW1m k)
  have hx := T.kqS_hx m hTr A hsq hdegA θ hθ 1 one_ne_zero (by omega) hk
  obtain ⟨aa, haa, e, he, hae⟩ := S.kqm_liouville_tors (K := AlgebraicClosure (T.F m)) (T.val m η)
    hx (fun c ↦ deriv_algebraMap c) (T.kqS_good m MS.hyp hk) (T.keS_constC m)
    (fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q)) _ hcinj
    (fun q ↦ ⟨(hβ q).1, (hβ q).2⟩) (fun q ↦ kqMNm Fc ks m η A B l cs q) (kqCl m η A B l cs)
    (fun k ↦ SqrtIndep.prodRoots rtsF (kqCls Fc ks m η A B l cs)[(k : ℕ)] /
      (kqDenM Fc ks m η A B l cs : T.F m))
    (Polynomial.C ((1 : T.F m) ^ (2 * l) / 1) * GPoly.toPoly (T.MP m hTm) B) l _ hb
    (GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m cs))
    (fun q' ↦ GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q'))) hDR hRne hDoff hbP
    hres rfl hcopS Ns (fun k ↦ hN k) (fun k ↦ S.elemW (Wk k)) (fun k ↦ (hWit k).1)
    (fun k ↦ (hWit k).2) W0 W1 (fun k ↦ hmemx _) hW1m hWe hNm hbm sI c u hcd
    (fun i hi ↦ ⟨(hu i hi).1, T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ (hu i hi).2⟩) v
    (T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ hv) (by rw [hby]; exact heq)
  rw [hby] at hae
  -- the constants `μ_k`
  have hμ2 : ∀ k, (μ k) ^ 2 = ((kqS Fc ks m η A B l cs (Tk k) : ℚ) : T.F m) := fun k ↦
    SqrtIndep.prodRoots_sq _ rtsF hrlF hrsF _
  have hμd : ∀ k, ((μ k : T.F m) : L)′ = 0 := fun k ↦ by
    have : ∀ (r' : List (T.F m)) (T' : List Bool), (∀ z ∈ r', ((z : T.F m) : L)′ = 0) →
        ((SqrtIndep.prodRoots r' T' : T.F m) : L)′ = 0 := by
      intro r' T' hr'
      induction r' generalizing T' with
      | nil => cases T' <;> simp [SqrtIndep.prodRoots]
      | cons y r' ih =>
        cases T' with
        | nil => simp [SqrtIndep.prodRoots]
        | cons b T' =>
          simp only [SqrtIndep.prodRoots, IntermediateField.coe_mul]
          rw [Derivation.leibniz, ih T' (fun z hz ↦ hr' z (List.mem_cons_of_mem _ hz))]
          split_ifs
          · rw [hr' y (List.mem_cons_self)]; simp
          · simp
    refine this rtsF _ fun z hz ↦ ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
    rw [hFv i hi (by omega)]
    exact (hrts i (by omega) (by omega)).2
  -- the value of the columns
  have hPd : (aeval (T.ts m) S.p)′ = aeval (T.ts m) (mapCoeffs S.p +
      Polynomial.C (T.val m η) * derivative S.p) := S.deriv_aeval_xW _ hx S.p
  have hPA : aeval (T.ts m) S.p = T.evP m A := by
    change aeval (T.ts m) (Polynomial.C ((1 : T.F m) ^ 2) * GPoly.toPoly (T.MP m hTm) A) = _
    rw [map_mul, aeval_C, T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]
    simp
  have hP0 : aeval (T.ts m) S.p ≠ 0 := by rw [hPA]; exact hA0
  have hcolv : ∀ k, ((μ k : T.F m) : L) *
      T.ev (m + 1) (kqCol Fc ks m η A B l cs (Tk k) (Wbs k)) =
      (W0 k * ((W1 k)′ + W1 k * (aeval S.x (mapCoeffs S.p + Polynomial.C (T.val m η) *
        derivative S.p) / ((S.n : L) * aeval S.x S.p))) - (W0 k)′ * W1 k) /
        (W0 k ^ 2 - W1 k ^ 2 * aeval S.x S.p) := fun k ↦ by
    have hW0c : T.evP m ((Wbs k).getD 0 [] |>.map (unTr Fc m)) = W0 k := by
      rw [T.evP_unTr_map m hTm, hW0, hWp]
      simp only [Polynomial.coeff_map, coe_mapRingHom, coeff_toB]
    have hW1c' : T.evP m ((Wbs k).getD 1 [] |>.map (unTr Fc m)) = W1c k := by
      rw [T.evP_unTr_map m hTm, hW1c, hWp]
      simp only [Polynomial.coeff_map, coe_mapRingHom, coeff_toB]
    have hAh : T.evP m (A.map ((MO Fc ks m).mul (mcst Fc ks m (kqS Fc ks m η A B l cs (Tk k))))) =
        ((kqS Fc ks m η A B l cs (Tk k) : ℚ) : L) * aeval (T.ts m) S.p := by
      rw [T.evP_mapMul m hTm, ← T.sem_MP m hTm, T.sem_mcst, hPA]; push_cast; rfl
    have hμL2 : ((μ k : T.F m) : L) ^ 2 = ((kqS Fc ks m η A B l cs (Tk k) : ℚ) : L) := by
      rw [← IntermediateField.coe_pow, hμ2 k]; push_cast; rfl
    have hs0 : ((kqS Fc ks m η A B l cs (Tk k) : ℚ) : L) ≠ 0 := by
      rw [← hμL2]; exact pow_ne_zero 2 (fun h ↦ (hKF k).1 (Subtype.ext h))
    rw [kqCol, T.ev_normC (m + 1) hTr, T.ev_logCol m hTr, hW0c, hW1c', hAh, T.ev_one_code m hTm,
      mul_one]
    have hSx : S.x = T.ts m := rfl
    have hn2' : ((S.n : ℕ) : L) = 2 := by show ((2 : ℕ) : L) = 2; norm_num
    have hsPd : (((kqS Fc ks m η A B l cs (Tk k) : ℚ) : L) * aeval (T.ts m) S.p)′ =
        ((kqS Fc ks m η A B l cs (Tk k) : ℚ) : L) * (aeval (T.ts m) S.p)′ := by
      rw [Derivation.leibniz, T.deriv_ratCast_E]; simp
    have hW1d : (W1 k)′ = ((μ k : T.F m) : L) * (W1c k)′ := by
      simp only [hW1]; rw [Derivation.leibniz, hμd k]; simp
    rw [hsPd, hSx, hn2', ← hPd, hW1d]
    simp only [hW1]
    rw [← hμL2]
    have hμ0 : ((μ k : T.F m) : L) ≠ 0 := fun h ↦ (hKF k).1 (Subtype.ext h)
    field_simp
  -- the constants of the columns
  have hconst' : ∀ k, ∃ c0 : Cc, algebraMap Cc L c0 =
      -(algebraMap (T.F m) L (e k) * ((μ k : T.F m) : L)) := fun k ↦ by
    refine T.hconst _ ?_
    rw [map_neg, Derivation.leibniz, he k, hμd k]; simp
  choose c0 hc0 using hconst'
  have hspecA := MS.rde _ (T.kpFr_ok m hTr 1 2 A)
  set rhs : LC (m + 1) := (B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
    (powG (MO Fc ks m) A l)) with hrhs
  set cols : List (LC (m + 1)) := List.ofFn fun k ↦ kqCol Fc ks m η A B l cs (Tk k) (Wbs k) with hcols
  have hθ0 : θ ≠ 0 := fun h0 ↦ hA0 (by rw [← hθ, h0, zero_pow two_ne_zero])
  have h1 := deriv_mul_radical θ (T.evP m A) 2 two_pos hθ hA0 aa 1
  simp only [pow_one] at h1
  have hSy : S.y = θ * ((1 : T.F m) : L) := rfl
  have h2 : (aa * S.y)′ = (aa * θ)′ := by rw [hSy]; simp
  rw [h2, h1] at hae
  have haaF : aa ∈ T.F (m + 1) := (T.mem_F_succ).mpr haa
  have hlen : (rhs :: cols).length = (kqCls Fc ks m η A B l cs).length + 1 := by simp [hcols]
  obtain ⟨βv, hβv, -⟩ := hspecA.complete (rhs :: cols) (1 :: List.ofFn c0) (fun i hi ↦ by
      rw [hlen] at hi
      rcases i with _ | i
      · simp at hi
      · simp only [List.getD_cons_succ]
        exact List.getD_eq_default _ _ (by simp; omega)) ⟨aa, haaF⟩ (by
    apply Subtype.ext
    simp only [sC, IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv]
    rw [hlen, Finset.sum_range_succ', IntermediateField.coe_add]
    simp only [List.getD_cons_zero, List.getD_cons_succ, map_one, one_mul]
    rw [T.sem_kpFr m hTr, T.sem_MP (m + 1) hTr]
    have hsum : ((∑ i ∈ Finset.range (kqCls Fc ks m η A B l cs).length,
        algebraMap Cc (T.F (m + 1)) ((List.ofFn c0).getD i 0) *
          (T.MP (m + 1) hTr).sem (cols.getD i (MO Fc ks (m + 1)).zero) : T.F (m + 1)) : L) =
        ∑ k, -(algebraMap (T.F m) L (e k) * ((μ k : T.F m) : L)) *
          T.ev (m + 1) (kqCol Fc ks m η A B l cs (Tk k) (Wbs k)) := by
      rw [show ((∑ i ∈ Finset.range (kqCls Fc ks m η A B l cs).length,
          algebraMap Cc (T.F (m + 1)) ((List.ofFn c0).getD i 0) *
            (T.MP (m + 1) hTr).sem (cols.getD i (MO Fc ks (m + 1)).zero) : T.F (m + 1)) : L) =
          ∑ i ∈ Finset.range (kqCls Fc ks m η A B l cs).length,
            ((algebraMap Cc (T.F (m + 1)) ((List.ofFn c0).getD i 0) *
              (T.MP (m + 1) hTr).sem (cols.getD i (MO Fc ks (m + 1)).zero) : T.F (m + 1)) : L) from
          map_sum (T.F (m + 1)).val _ _, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [IntermediateField.coe_mul, List.getD_eq_getElem _ _ (by simp),
        List.getD_eq_getElem _ _ (by simp [hcols]), List.getElem_ofFn]
      simp only [hcols, List.getElem_ofFn]
      rw [T.sem_MP (m + 1) hTr]
      change algebraMap Cc L (c0 k) * _ = _
      rw [hc0 k]
    rw [hsum]
    change aa′ + _ * aa = _
    rw [show (((1 : ℕ) : ℚ) / (2 : ℕ) : L) = (1 / 2 : L) by push_cast; ring]
    apply mul_right_cancel₀ hθ0
    have hcol2 : ∀ k, algebraMap (T.F m) L (e k) * ((W0 k * ((W1 k)′ + W1 k *
        (aeval S.x (mapCoeffs S.p + Polynomial.C (T.val m η) * derivative S.p) /
          ((S.n : L) * aeval S.x S.p))) - (W0 k)′ * W1 k) /
          (W0 k ^ 2 - W1 k ^ 2 * aeval S.x S.p) * (θ * ((1 : T.F m) : L))) =
        algebraMap (T.F m) L (e k) * ((μ k : T.F m) : L) *
          T.ev (m + 1) (kqCol Fc ks m η A B l cs (Tk k) (Wbs k)) * θ := fun k ↦ by
      rw [← hcolv k]; push_cast; ring
    rw [hSy] at hae
    simp only [hcol2] at hae
    rw [← Finset.sum_mul] at hae
    simp only [neg_mul, Finset.sum_neg_distrib]
    push_cast at hae ⊢
    linear_combination (-1 : L) * hae)
  have h0 := hβv 0
  simp only [List.getD_cons_zero] at h0
  by_contra hno
  simp only [List.any_eq_true, not_exists, not_and, decide_eq_true_eq, not_not] at hno
  apply one_ne_zero (α := Cc)
  rw [h0]
  refine Finset.sum_eq_zero fun kk hkk ↦ ?_
  have hmem : (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) (rhs :: cols)).getD kk
      ([], (MO Fc ks (m + 1)).zero) ∈ prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A) (rhs :: cols) := by
    rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hkk)]
    exact List.getElem_mem _
  rw [hno _ hmem, map_zero, mul_zero]

end Forward

section Backward

variable [Fact (Irreducible (toPoly (fKc Fc)))]

omit [CharZero Cc] [CharZero L] in
lemma prodSub_ne : ∀ (s : List ℚ), (∀ g ∈ s, g ≠ 0) → ∀ T' : List Bool, prodSub s T' ≠ 0
  | [], _, T' => by cases T' <;> simp [prodSub]
  | g :: s, h, [] => by simp [prodSub]
  | g :: s, h, b :: T' => by
    simp only [prodSub]
    refine mul_ne_zero ?_ (prodSub_ne s (fun g' hg' ↦ h g' (by simp [hg'])) T')
    split_ifs
    · exact h g (by simp)
    · exact one_ne_zero

lemma hei_sum {n : ℕ} (f : Fin n → L) (hf : ∀ k, HasElementaryIntegralIn (f k)) :
    HasElementaryIntegralIn (∑ k, f k) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    have : (0 : L) = (0 : L)′ := by simp
    rw [this]; exact hasElementaryIntegralIn_deriv 0
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    exact (hf 0).add (ih (fun k ↦ f k.succ) (fun k ↦ hf k.succ))

/-- **A solution of the multi-column equation gives an antiderivative.** -/
theorem kqm_backward (m : ℕ) (hTr : T.Tr (m + 1)) (η : LC m) (A B : GPoly (LC m)) (l : ℕ)
    (cs : List (LC m)) (θ : L) (hθ : θ ^ 2 = T.evP m A) (hA0 : T.evP m A ≠ 0)
    {n : ℕ} (Tc : Fin n → List Bool) (hTc : ∀ k, kqS Fc ks m η A B l cs (Tc k) ≠ 0)
    (Wbs : Fin n → BPoly (KF Fc m))
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m 1 2 A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)))
    (h : (prdeC Fc ks lv (m + 1) (kpFr Fc ks m 1 2 A)
      (((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs) (powG (MO Fc ks m) A l)) : LC (m + 1)) ::
        List.ofFn fun k ↦ kqCol Fc ks m η A B l cs (Tc k) (Wbs k))).any
      (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) = true) :
    HasElementaryIntegralIn (T.ev (m + 1) ((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
      (powG (MO Fc ks m) A l)) : LC (m + 1)) * θ) := by
  obtain ⟨r, hr, hr0⟩ := List.any_eq_true.mp h
  have hq0 : r.1.getD 0 0 ≠ 0 := of_decide_eq_true hr0
  set rhs : LC (m + 1) := (B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
    (powG (MO Fc ks m) A l)) with hrhs
  set cols : List (LC (m + 1)) := List.ofFn fun k ↦ kqCol Fc ks m η A B l cs (Tc k) (Wbs k)
    with hcols
  have hs := hspec.sound (rhs :: cols) r hr
  have hlen : (rhs :: cols).length = n + 1 := by simp [hcols]
  have hsQ : sQ (T.MP (m + 1) hTr) r.1 (rhs :: cols) =
      ((r.1.getD 0 0 : ℚ) : T.F (m + 1)) * (T.MP (m + 1) hTr).sem rhs +
        ∑ k : Fin n, ((r.1.getD (k + 1) 0 : ℚ) : T.F (m + 1)) *
          (T.MP (m + 1) hTr).sem (kqCol Fc ks m η A B l cs (Tc k) (Wbs k)) := by
    unfold sQ
    rw [hlen, Finset.sum_range_succ']
    refine (add_comm _ _).trans ?_
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hck : cols.getD (k : ℕ) (MO Fc ks (m + 1)).zero =
        kqCol Fc ks m η A B l cs (Tc k) (Wbs k) := by
      rw [hcols, List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [k.2]
    rw [hck]
  rw [hsQ] at hs
  have hsL := congrArg Subtype.val hs
  simp only [IntermediateField.coe_add, IntermediateField.coe_mul, MTower.coe_deriv,
    IntermediateField.coe_sum] at hsL
  rw [T.sem_kpFr m hTr] at hsL
  simp only [T.sem_MP (m + 1) hTr] at hsL
  set a : L := T.ev (m + 1) r.2
  set q0 : ℚ := r.1.getD 0 0
  have hq0L : (q0 : L) ≠ 0 := by exact_mod_cast hq0
  have h1 := deriv_mul_radical θ (T.evP m A) 2 two_pos hθ hA0 (a / q0) 1
  simp only [pow_one] at h1
  have hf : T.ev (m + 1) rhs * θ = ((a / q0) * θ)′ + ∑ k : Fin n,
      ((-(r.1.getD (k + 1) 0) / q0 : ℚ) : L) *
        (T.ev (m + 1) (kqCol Fc ks m η A B l cs (Tc k) (Wbs k)) * θ) := by
    rw [h1]
    have hq0d : ((q0 : L))′ = 0 := Tower.NestP.deriv_ratCastK (K := L) q0
    have hd : (a / (q0 : L))′ = a′ / q0 := by
      rw [div_eq_mul_inv a, Derivation.leibniz, Derivation.leibniz_inv, hq0d, div_eq_mul_inv]
      simp only [smul_zero, smul_eq_mul, mul_zero, zero_add, neg_zero]
      ring
    rw [hd]
    have hsum : ∑ k : Fin n, ((-(r.1.getD (k + 1) 0) / q0 : ℚ) : L) *
        (T.ev (m + 1) (kqCol Fc ks m η A B l cs (Tc k) (Wbs k)) * θ) =
        -(∑ k : Fin n, ((r.1.getD (k + 1) 0 : ℚ) : L) *
          T.ev (m + 1) (kqCol Fc ks m η A B l cs (Tc k) (Wbs k))) * θ / q0 := by
      rw [div_eq_mul_inv, neg_mul, neg_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      push_cast; field_simp
    rw [hsum]
    generalize T.ev (m + 1) rhs = R at hsL ⊢
    push_cast at hsL ⊢
    field_simp
    linear_combination (-2 * θ : L) * hsL
  rw [hf]
  refine (hasElementaryIntegralIn_deriv _).add (hei_sum _ fun k ↦ ?_)
  have := T.kq_hcolIn m hTr A θ hθ hA0 _ (hTc k) ((Wbs k).getD 0 [] |>.map (unTr Fc m))
    ((Wbs k).getD 1 [] |>.map (unTr Fc m)) (-(r.1.getD (k + 1) 0) / q0)
  rw [kqCol, T.ev_normC (m + 1) hTr]
  exact this

end Backward

lemma allSome_spec {α : Type*} : ∀ (l : List (Option α)) (l' : List α), l.allSome = some l' →
    l'.length = l.length ∧ ∀ i (h1 : i < l.length) (h2 : i < l'.length), l[i] = some l'[i]
  | [], l', h => by
    simp only [List.allSome, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | a :: l, l', h => by
    simp only [List.allSome, List.mapM_cons, id, Option.pure_def, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    obtain ⟨h1, h2⟩ := allSome_spec l bs hbs
    refine ⟨by simp [h1], fun i hi hi' ↦ ?_⟩
    rcases i with _ | i
    · simpa using hb
    · simpa using h2 i (by simpa using hi) (by simpa using hi')

section Main

variable [Fact (Irreducible (toPoly (fKc Fc)))]

set_option maxHeartbeats 1600000 in
open Classical in
/-- **`kqmDecide` is correct**: whenever it answers `some b`, the integral of
`B(t) θ / (∏_q (t − c_q) A(t)ˡ)` (`θ² = A(t)`, `t` a logarithmic level of a certified tower) is
elementary exactly when `b = true` — for residues in any number of classes `ℚ √s`. -/
theorem kqmDecideC_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (cpf : CPoly (KF Fc m) → CertProv (KF Fc m))
    (b : Bool) (hdec : kqmDecideC Fc ks lv m η A B l cs cpf ps bound rs = some b) :
    HasElementaryIntegral (T.ev (m + 1) ((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
      (powG (MO Fc ks m) A l)) : LC (m + 1)) * θ) ↔ b = true := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hA0 : T.evP m A ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) A hdegpos
  have hspecA := MS.rde _ (T.kpFr_ok m hTr 1 2 A)
  unfold kqmDecideC at hdec
  dsimp only at hdec
  by_cases hr0 : cs.length = 0
  · rw [if_pos hr0] at hdec; exact absurd hdec (by simp)
  rw [if_neg hr0] at hdec
  by_cases hok : kqOK Fc ks m A B l cs = true
  swap
  · rw [if_pos (by simpa using hok)] at hdec; exact absurd hdec (by simp)
  rw [if_neg (by simp [hok])] at hdec
  by_cases hcst : kqConst Fc ks m η A B l cs = true
  swap
  · rw [if_pos (by simpa using hcst)] at hdec
    obtain rfl := Option.some.inj hdec
    simp only [Bool.false_eq_true, iff_false]
    intro hf
    obtain ⟨E, _, _, _, TE, θE, -, ι, sI, c, u, v, hTEn, hθE, -, -, hcd, hu, hv, heq⟩ :=
      T.kq_lift m hn A θ hθ hgen _ hf 1 one_ne_zero
    exact hcst (TE.kq_forward_const hmon hdeg m hTEn hc hk A hsqc hdegpos hcop B l cs hok θE hθE
      sI c u hcd hu v hv heq)
  rw [if_neg (by simp [hcst])] at hdec
  by_cases hrep : kqRepOK Fc ks m η A B l cs = true
  swap
  · rw [if_pos (by simpa using hrep)] at hdec; exact absurd hdec (by simp)
  rw [if_neg (by simp [hrep])] at hdec
  have hg0 := (kqGens_spec (Fc := Fc) (ks := ks) m η A B l cs).2
  set cls := kqCls Fc ks m η A B l cs with hcls
  set tors := cls.map (kqTorsC Fc ks m η A B l cs cpf ps bound rs) with htorsdef
  by_cases hnone : tors.any (· == none) = true
  · rw [if_pos hnone] at hdec; exact absurd hdec (by simp)
  rw [if_neg hnone] at hdec
  by_cases hsn : tors.any (· == some none) = true
  · -- a class without torsion
    rw [if_pos hsn] at hdec
    obtain rfl := Option.some.inj hdec
    simp only [Bool.false_eq_true, iff_false]
    intro hf
    obtain ⟨x, hx, hx0⟩ := List.any_eq_true.mp hsn
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < cls.length := by simpa [htorsdef] using hi
    have htk : kqTorsC Fc ks m η A B l cs cpf ps bound rs cls[i] = some none := by
      have := hx0; simp only [beq_iff_eq] at this; simpa [htorsdef] using this
    obtain ⟨E, _, _, _, TE, θE, rts, ι, sI, c, u, v, hTEn, hθE, hrl, hrts, hcd, hu, hv, heq⟩ :=
      T.kqm_lift m hn A θ hθ hgen _ hf (kqGens Fc ks m η A B l cs) hg0
    exact TE.kqm_forward_nontors hmon hdeg m hTEn hc hk A hsqc hdegpos hcop B l cs hok hcst hrep
      ps bound rs cpf ⟨i, hi'⟩ htk θE hθE sI c u hcd hu v hv heq rts hrl hrts
  rw [if_neg hsn] at hdec
  -- every class is torsion
  have hall : ∀ k : Fin cls.length, ∃ N, kqTorsC Fc ks m η A B l cs cpf ps bound rs cls[(k : ℕ)] =
      some (some N) := by
    intro k
    rcases h : kqTorsC Fc ks m η A B l cs cpf ps bound rs cls[(k : ℕ)] with _ | _ | N
    · exfalso; apply hnone
      exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨_, List.getElem_mem k.2, h⟩, by simp⟩
    · exfalso; apply hsn
      exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨_, List.getElem_mem k.2, h⟩, by simp⟩
    · exact ⟨N, rfl⟩
  choose Ns hNs using hall
  have hNs' : ∀ k : Fin cls.length,
      ((tors[(k : ℕ)]'(by simp [htorsdef])).getD none).getD 0 = Ns k := fun k ↦ by
    simp [htorsdef, hNs k]
  generalize hw : ((List.zip cls tors).map fun p ↦
    kqWit Fc ks m η A B l cs p.1 ((p.2.getD none).getD 0)).allSome = ow at hdec
  rcases ow with _ | Wbl
  · exact absurd hdec (by simp)
  obtain ⟨hWl, hWv⟩ := allSome_spec _ Wbl hw
  have hlc : (List.zip cls tors).length = cls.length := by simp [htorsdef]
  have hWl' : Wbl.length = cls.length := by rw [hWl, List.length_map, hlc]
  set Wbs : Fin cls.length → BPoly (KF Fc m) := fun k ↦ Wbl[(k : ℕ)]'(by rw [hWl']; exact k.2)
    with hWbs
  have hwit : ∀ k : Fin cls.length,
      kqWit Fc ks m η A B l cs cls[(k : ℕ)] (Ns k) = some (Wbs k) := fun k ↦ by
    have := hWv k (by rw [List.length_map, hlc]; exact k.2) (by rw [hWl']; exact k.2)
    simp only [List.getElem_map, List.getElem_zip] at this
    rw [hNs' k] at this
    exact this
  have hcols : (List.zip cls Wbl).map (fun p ↦ kqCol Fc ks m η A B l cs p.1 p.2) =
      List.ofFn fun k : Fin cls.length ↦ kqCol Fc ks m η A B l cs cls[(k : ℕ)] (Wbs k) := by
    apply List.ext_getElem
    · simp [hWl']
    · intro i h1 h2
      simp [List.getElem_zip, hWbs]
  simp only at hdec
  obtain rfl := Option.some.inj hdec
  rw [hcols]
  constructor
  · intro hf
    obtain ⟨E, _, _, _, TE, θE, rts, ι, sI, c, u, v, hTEn, hθE, hrl, hrts, hcd, hu, hv, heq⟩ :=
      T.kqm_lift m hn A θ hθ hgen _ hf (kqGens Fc ks m η A B l cs) hg0
    exact TE.kqm_forward_tors hmon hdeg m hTEn hc hk A hsqc hdegpos hcop B l cs hok hcst hrep
      ps bound rs cpf Ns hNs Wbs hwit θE hθE sI c u hcd hu v hv heq rts hrl hrts
  · intro h
    refine (T.kqm_backward m hTr η A B l cs θ hθ hA0 (fun k ↦ cls[(k : ℕ)]) (fun k ↦ ?_) Wbs hspecA
      h).hasElementaryIntegral
    exact prodSub_ne _ hg0 _

open Classical in
/-- **`kqmDecide` is correct**: whenever it answers `some b`, the integral of
`B(t) θ / (∏_q (t − c_q) A(t)ˡ)` (`θ² = A(t)`, `t` a logarithmic level of a certified tower) is
elementary exactly when `b = true` — for residues in any number of classes `ℚ √s`. -/
theorem kqmDecide_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (b : Bool) (hdec : kqmDecide Fc ks lv m η A B l cs ps bound rs = some b) :
    HasElementaryIntegral (T.ev (m + 1) ((B, GPoly.mul (MO Fc ks m) (prodLinG Fc ks m cs)
      (powG (MO Fc ks m) A l)) : LC (m + 1)) * θ) ↔ b = true :=
  T.kqmDecideC_correct hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B l cs ps bound rs _ b hdec

end Main

end MTower

end Curves.MT
