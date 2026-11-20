import RischTragerBronstein.Mixed.NKExactWRE

/-!
# `exactWRE` answers in its regime

The checks of `exactWRE` pass when their semantic conditions hold (`annOK_of`, `qmatOK_of`,
`zeroOKE_of`); a code whose value has a rational limit `a′ λ` at infinity has that limit on its
numerator and denominator (`limit_of_sem`); the factors of a squarefree `q` with `q(0) ≠ 0` are
normal at an exponential level (`hpd_exp`). Hence **`exactWRE_isSome`**.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

lemma annOK_of (N N0 : ℕ) (Λ : ℕ → ℕ → ℚ) (hN0 : 0 < N0)
    (hP : aeval (Matrix.of fun i j : Fin N ↦ Λ i j)
      (Lagrange.nodal (Finset.range N0) (annNodes N0)) = 0) :
    annOK N N0 Λ = true := by
  unfold annOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    forall_const, beq_iff_eq]
  refine ⟨hN0, fun i j ↦ ?_⟩
  have hnodal : Lagrange.nodal (Finset.range N0) (annNodes N0) =
      ((List.range N0).map fun k ↦ X - Polynomial.C (annNodes N0 k)).prod := by
    rw [Lagrange.nodal, ← List.toFinset_range, List.prod_toFinset _ (List.nodup_range)]
  rw [hnodal, map_list_prod, List.map_map] at hP
  have := congrFun (congrFun hP i) j
  rw [Matrix.zero_apply] at this
  convert this using 3
  funext k
  simp only [Function.comp_apply, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]

lemma qmatOK_of (N : ℕ) (C Ci : List (List ℚ))
    (h1 : ∀ i < N, ∀ j < N, ∑ k ∈ Finset.range N, qget C i k * qget Ci k j = if i = j then 1 else 0)
    (h2 : ∀ i < N, ∀ j < N, ∑ k ∈ Finset.range N, qget Ci i k * qget C k j = if i = j then 1 else 0) :
    qmatOK N C Ci = true := by
  unfold qmatOK
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  exact fun i hi j hj ↦ ⟨h1 i hi j hj, h2 i hi j hj⟩

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **The checks at `t = 0` pass** when `A₀(0) = q(0) a′ Λ₀` with `Λ₀` annihilated by the nodal
polynomial and `C C⁻¹ = C⁻¹ C = 1`. -/
lemma zeroOKE_of (m : ℕ) (h0 : T.Tr m) (bc : LC m) (N N0 : ℕ) (q : GPoly (LC m))
    (A0 : Fin N → Fin N → GPoly (LC m)) (C Ci : List (List ℚ)) (lam : ℕ → ℕ → ℚ)
    (hq0 : (GPoly.toPoly (T.MP m h0) q).coeff 0 ≠ 0) (hb0 : (T.MP m h0).sem bc ≠ 0)
    (hA : ∀ i j : Fin N, (GPoly.toPoly (T.MP m h0) (A0 i j)).coeff 0 =
      (GPoly.toPoly (T.MP m h0) q).coeff 0 * (T.MP m h0).sem bc * ((lam i j : ℚ) : T.F m))
    (hN0 : 0 < N0) (hP : aeval (Matrix.of fun i j : Fin N ↦ lam i j)
      (Lagrange.nodal (Finset.range N0) (annNodes N0)) = 0)
    (h1 : ∀ i < N, ∀ j < N, ∑ k ∈ Finset.range N, qget C i k * qget Ci k j = if i = j then 1 else 0)
    (h2 : ∀ i < N, ∀ j < N, ∑ k ∈ Finset.range N, qget Ci i k * qget C k j = if i = j then 1 else 0) :
    zeroOKE Fc ks m bc N N0 q A0 C Ci = true := by
  set M := T.MP m h0
  have hlam : ∀ i j : Fin N, lam0E Fc ks m bc N q A0 i j = lam i j := by
    intro i j
    have hv : M.sem ((MO Fc ks m).mul ((A0 i j).getD 0 (MO Fc ks m).zero)
        ((MO Fc ks m).inv ((MO Fc ks m).mul (q.getD 0 (MO Fc ks m).zero) bc))) =
        ((lam i j : ℚ) : T.F m) := by
      rw [M.sem_mul, M.sem_inv, M.sem_mul, ← coeff_toPoly_sem, ← coeff_toPoly_sem, hA]
      field_simp
    simp only [lam0E, i.2, j.2, and_self, ↓reduceDIte, Fin.eta]
    rw [T.ratVal_spec m h0 _ _ hv, Option.getD_some]
  have hlamF : (Matrix.of fun i j : Fin N ↦ (lam0E Fc ks m bc N q A0 i j : ℚ)) =
      Matrix.of fun i j : Fin N ↦ lam i j := by
    ext i j; simp only [Matrix.of_apply, hlam]
  unfold zeroOKE
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const]
  refine ⟨⟨fun i j ↦ ?_, annOK_of N N0 _ hN0 (by rw [hlamF]; exact hP)⟩, qmatOK_of N C Ci h1 h2⟩
  rw [M.isZero_iff, M.sem_add, M.sem_neg, M.sem_mul, M.sem_mul, T.sem_mcst m h0,
    ← coeff_toPoly_sem, ← coeff_toPoly_sem, hA, hlam, add_neg_eq_zero]

/-- **The factors of a squarefree `q` with `q(0) ≠ 0` are normal at an exponential level.** -/
lemma hpd_exp (m : ℕ) (h : T.Tr m) (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m)) (q : GPoly (LC m))
    (hsq : Squarefree (GPoly.toPoly (T.MP m h) q)) (hq0 : (GPoly.toPoly (T.MP m h) q).coeff 0 ≠ 0) :
    ∀ p : (T.F m)[X], Irreducible p → p ∣ GPoly.toPoly (T.MP m h) q →
      ¬ p ∣ GPoly.toPoly (T.MP m h) (DzLC (MO Fc ks m) (MO Fc ks m).zero
        ((MO Fc ks m).deriv a) q) := by
  intro p hp hpq hdiv
  set b := (T.MP m h).sem ((MO Fc ks m).deriv a) with hb
  rw [toPoly_DzLC, (T.MP m h).sem_zero] at hdiv
  obtain ⟨r, hr⟩ := hpq
  rw [hr] at hdiv
  have hl : DzL 0 b (p * r) = p * DzL 0 b r + r * DzL 0 b p := by
    simp only [DzL, Derivation.leibniz, smul_eq_mul]
  rw [hl] at hdiv
  have h2 : p ∣ r * DzL 0 b p := (dvd_add_right (dvd_mul_right p _)).mp hdiv
  rcases hp.prime.dvd_or_dvd h2 with h3 | h3
  · obtain ⟨s, hs⟩ := h3
    have : p * p ∣ GPoly.toPoly (T.MP m h) q := ⟨s, by rw [hr, hs]; ring⟩
    exact hp.not_isUnit (hsq p this)
  · have hX : ¬ X ∣ p := by
      intro hX
      apply hq0
      rw [hr, ← X_dvd_iff]
      exact dvd_mul_of_dvd_left hX _
    have hbval : b = (T.val m a)′ := by
      rw [hb, (T.MP m h).sem_deriv, T.sem_MP_F m h]
    apply T.normal_exp m htr hk p hp hX
    rw [T.wPoly_exp hm hk, ← hbval]
    simpa [DzL] using h3

section Lim

variable {m : ℕ} (h1 : T.Tr (m + 1))

/-- **A code whose value has a limit at infinity**: if `e = A / B` with `deg A ≤ deg B` and
`A_{deg B} = c lc(B)`, the same holds for the numerator and denominator of `e`. -/
lemma limit_of_sem (htr : Transcendental (T.F m) (T.ts m)) (e : LC (m + 1))
    (he : GPoly.toPoly (T.MP m h1.of_succ) e.2 ≠ 0) (A B : (T.F m)[X]) (hB : B ≠ 0)
    (hAB : A.natDegree ≤ B.natDegree) (c : T.F m) (hc : A.coeff B.natDegree = c * B.leadingCoeff)
    (hval : (T.MPr (m + 1) h1).sem e = T.phi m A / T.phi m B) :
    (GPoly.toPoly (T.MP m h1.of_succ) e.1).natDegree ≤
        (GPoly.toPoly (T.MP m h1.of_succ) e.2).natDegree ∧
      (GPoly.toPoly (T.MP m h1.of_succ) e.1).coeff (GPoly.toPoly (T.MP m h1.of_succ) e.2).natDegree =
        c * (GPoly.toPoly (T.MP m h1.of_succ) e.2).leadingCoeff := by
  set M := T.MP m h1.of_succ
  rw [MPr_sem, T.sem_MP_succ] at hval
  change T.phi m (GPoly.toPoly M e.1) / T.phi m (GPoly.toPoly M e.2) = _ at hval
  have hφe : T.phi m (GPoly.toPoly M e.2) ≠ 0 := fun h0 ↦ he (T.phi_injective htr (by rw [h0, map_zero]))
  have hφB : T.phi m B ≠ 0 := fun h0 ↦ hB (T.phi_injective htr (by rw [h0, map_zero]))
  rw [div_eq_div_iff hφe hφB] at hval
  have heq : GPoly.toPoly M e.1 * B = A * GPoly.toPoly M e.2 :=
    T.phi_injective htr (by rw [map_mul, map_mul, hval])
  set e1 := GPoly.toPoly M e.1
  set e2 := GPoly.toPoly M e.2
  have hdeg : e1.natDegree ≤ e2.natDegree := by
    by_cases h0 : e1 = 0
    · rw [h0, natDegree_zero]; exact Nat.zero_le _
    have hn := congrArg natDegree heq
    rw [natDegree_mul h0 hB] at hn
    have := natDegree_mul_le (p := A) (q := e2)
    omega
  refine ⟨hdeg, ?_⟩
  have hk : (e1 * B).coeff (e2.natDegree + B.natDegree) =
      (A * e2).coeff (e2.natDegree + B.natDegree) := by rw [heq]
  rw [coeff_mul_of_natDegree_le' hdeg le_rfl, add_comm,
    coeff_mul_of_natDegree_le' hAB le_rfl, hc] at hk
  have hlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
  apply mul_right_cancel₀ hlc
  unfold leadingCoeff at *
  linear_combination hk

lemma getD_map_redC_of_lt (l : List (LC (m + 1))) (j : ℕ) (hj : j < l.length) :
    (l.map (redC Fc ks m)).getD j (MOr Fc ks (m + 1)).zero =
      redC Fc ks m (l.getD j (MOr Fc ks (m + 1)).zero) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getD_eq_getElem _ _ hj]

lemma conjM_row_length (N : ℕ) (C : List (List ℚ)) (Mr : List (List (LC (m + 1))))
    (Ci : List (List ℚ)) (i : ℕ) (hi : i < N) :
    ((conjM Fc ks m N C Mr Ci).getD i []).length = N := by
  rw [conjM, NestTower.getD_range_map _ _ hi, List.length_map, List.length_range]

lemma conjRed_entry (N : ℕ) (C : List (List ℚ)) (Mr : List (List (LC (m + 1))))
    (Ci : List (List ℚ)) (i j : ℕ) (hi : i < N) (hj : j < N) :
    ((((conjM Fc ks m N C Mr Ci).map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j
      (MOr Fc ks (m + 1)).zero) =
      redC Fc ks m (((conjM Fc ks m N C Mr Ci).getD i []).getD j (MOr Fc ks (m + 1)).zero) := by
  rw [getD_map_map_redC (Fc := Fc) (ks := ks) m,
    getD_map_redC_of_lt _ _ (by rw [conjM_row_length N C Mr Ci i hi]; exact hj)]

set_option maxHeartbeats 1600000 in
/-- **`exactWRE` answers** for squarefree matrix denominators prime to `t`, a rational limit
`a′ Λ₀` at `t = 0` annihilated by `∏_{k<N₀} (X − k/N₀)`, an invertible constant `C`, and a
conjugated rescaled matrix with an upper triangular rational limit `a′ Λ∞` at infinity. -/
theorem exactWRE_isSome (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m)) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hb0 : (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) ≠ 0)
    (N : ℕ) (hN : N ≠ 0) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (r : ℕ → ℤ)
    (N0 : ℕ) (C Ci : List (List ℚ))
    (hent : ∀ i < N, ∀ j < N,
      Squarefree (GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2) ∧
      (GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2).coeff 0 ≠ 0)
    (lam0 : ℕ → ℕ → ℚ)
    (hz : ∀ i < N, ∀ j < N,
      (GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).1).coeff 0 =
        (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * (lam0 j i : T.F m) *
          (GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2).coeff 0)
    (hN0 : 0 < N0) (hP : aeval (Matrix.of fun i j : Fin N ↦ lam0 i j)
      (Lagrange.nodal (Finset.range N0) (annNodes N0)) = 0)
    (hC1 : ∀ i < N, ∀ j < N, ∑ k ∈ Finset.range N, qget C i k * qget Ci k j = if i = j then 1 else 0)
    (hC2 : ∀ i < N, ∀ j < N, ∑ k ∈ Finset.range N, qget Ci i k * qget C k j = if i = j then 1 else 0)
    (lamI : ℕ → ℕ → ℚ)
    (hlim : ∀ i < N, ∀ j < N, ∃ A B : (T.F m)[X], B ≠ 0 ∧ A.natDegree ≤ B.natDegree ∧
      A.coeff B.natDegree = (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * (lamI j i : T.F m) *
        B.leadingCoeff ∧
      (T.MPr (m + 1) h1).sem (((conjM Fc ks m N C (rescaleME Fc ks m ((MO Fc ks m).deriv a) N Mc r)
        Ci).getD i []).getD j (MOr Fc ks (m + 1)).zero) = T.phi m A / T.phi m B)
    (htri : ∀ i < N, ∀ j < N, j < i → lamI i j = 0)
    (hf : ∀ c ∈ f, GPoly.toPoly (T.MP m h1.of_succ) c.2 ≠ 0) :
    (exactWRE Fc ks m a rdeD N Mc f r N0 C Ci).isSome := by
  set h0 := h1.of_succ with hh0
  set O := MO Fc ks m with hO
  set P := T.MP m h0 with hP'
  set O1 := MOr Fc ks (m + 1) with hO1
  set Mm : List (List (LC (m + 1))) := (List.range N).map fun i ↦
    (List.range N).map fun j ↦ (Mc.getD i []).getD j O1.zero with hMm
  have hmem : ∀ c ∈ Mm.flatten, ∃ i < N, ∃ j < N, c = (Mc.getD i []).getD j O1.zero := by
    intro c hc
    obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hcl
    exact ⟨i, List.mem_range.mp hi, j, List.mem_range.mp hj, rfl⟩
  have hent' : ∀ c ∈ Mm.flatten, GPoly.toPoly P c.2 ≠ 0 ∧ Squarefree (GPoly.toPoly P c.2) ∧
      (GPoly.toPoly P c.2).coeff 0 ≠ 0 := by
    intro c hc
    obtain ⟨i, hi, j, hj, rfl⟩ := hmem c hc
    exact ⟨(hent i hi j hj).1.ne_zero, hent i hi j hj⟩
  have hMmij : ∀ i < N, ∀ j < N, (Mm.getD i []).getD j O1.zero = (Mc.getD i []).getD j O1.zero :=
    fun i hi j hj ↦ by rw [hMm, NestTower.getD_range_map _ _ hi, NestTower.getD_range_map _ _ hj]
  have hMme : ∀ i < N, ∀ j < N, (Mm.getD i []).getD j O1.zero ∈ Mm.flatten := fun i hi j hj ↦ by
    rw [List.mem_flatten]
    refine ⟨Mm.getD i [], ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by simpa [hMm] using hi)]; exact List.getElem_mem _
    · have hlen : j < (Mm.getD i []).length := by
        rw [hMm, NestTower.getD_range_map _ _ hi]; simpa using hj
      rw [List.getD_eq_getElem (Mm.getD i []) _ hlen]; exact List.getElem_mem _
  set q := lcmGL O (Mm.flatten.map Prod.snd) with hq
  set hh := lcmGL O (f.map Prod.snd) with hhh
  have hdens : ∀ d ∈ Mm.flatten.map Prod.snd, GPoly.toPoly P d ≠ 0 := by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact (hent' c hc).1
  obtain ⟨hqm, hqd, hqs⟩ := lcmGL_spec P (Mm.flatten.map Prod.snd) hdens
  obtain ⟨hhm, hhd, -⟩ := lcmGL_spec P (f.map Prod.snd) (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact hf c hc)
  have hsq : Squarefree (GPoly.toPoly P q) := hqs (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact (hent' c hc).2.1)
  have hq0 : (GPoly.toPoly P q).coeff 0 ≠ 0 := by
    intro h0'
    rw [← X_dvd_iff] at h0'
    obtain ⟨d, hd, hXd⟩ := lcmGL_prime P _ hdens X prime_X h0'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
    exact (hent' c hc).2.2 (X_dvd_iff.mp hXd)
  have hcheck : ((Mm.flatten.map fun c ↦ cofC O q c.2).all Prod.fst &&
      (f.map fun c ↦ cofC O hh c.2).all Prod.fst && isMonicC O q && isMonicC O hh) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_map]
    refine ⟨⟨⟨?_, ?_⟩, isMonicC_of_monic P q hqm⟩, isMonicC_of_monic P hh hhm⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact cofC_fst P q c.2 (hent' c hc).1 (hqd _ (List.mem_map_of_mem hc))
    · rintro _ ⟨c, hc, rfl⟩
      exact cofC_fst P hh c.2 (hf c hc) (hhd _ (List.mem_map_of_mem hc))
  have hq0c : O.isZero (q.getD 0 O.zero) = false := by
    cases hz' : O.isZero (q.getD 0 O.zero)
    · rfl
    · exact absurd (by rw [coeff_toPoly_sem]; exact (P.isZero_iff _).mp hz') hq0
  set A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦
    GPoly.mul O ((Mm.getD i []).getD j O1.zero).1 (cofC O q ((Mm.getD i []).getD j O1.zero).2).2
    with hA0
  have hzc : zeroOKE Fc ks m (O.deriv a) N N0 q A0 C Ci = true := by
    refine T.zeroOKE_of m h0 _ N N0 q A0 C Ci lam0 hq0 hb0 (fun i j ↦ ?_) hN0 hP hC1 hC2
    have he := hMmij j j.2 i i.2
    have hqe := cofC_snd P q _ (hent' _ (hMme j j.2 i i.2)).1 (hqd _ (List.mem_map_of_mem (hMme j j.2 i i.2)))
    simp only [hA0]
    rw [GPoly.toPoly_mul, mul_coeff_zero, hqe, mul_coeff_zero, he, hz j j.2 i i.2]
    ring
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp
    (T.indBound2_isSome m h0 (degG O q) N q (DzLC O O.zero (O.deriv a) q) A0 hqm (degG_eq P q).symm
      (T.hpd_exp m h0 hm hk htr q hsq hq0))
  set R := ((List.range N).map fun i ↦ (-r i).toNat).foldr max 0 with hR
  set E := GPoly.mul O (GPoly.mul O hh (sysPowC O q B)) (sysPowC O (tX Fc ks m) R) with hE
  have hE0 : GPoly.toPoly P E ≠ 0 := by
    rw [hE, GPoly.toPoly_mul, GPoly.toPoly_mul, toPoly_sysPowC, toPoly_sysPowC, T.toPoly_tX]
    exact mul_ne_zero (mul_ne_zero hhm.ne_zero (pow_ne_zero _ hqm.ne_zero))
      (pow_ne_zero _ X_ne_zero)
  have hlim' : ∀ i < N, ∀ j < N, (GPoly.toPoly P ((((conjM Fc ks m N C (rescaleME Fc ks m (O.deriv a)
      N Mc r) Ci).map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j O1.zero).1).natDegree ≤
      (GPoly.toPoly P ((((conjM Fc ks m N C (rescaleME Fc ks m (O.deriv a)
      N Mc r) Ci).map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j O1.zero).2).natDegree ∧
      (GPoly.toPoly P ((((conjM Fc ks m N C (rescaleME Fc ks m (O.deriv a)
      N Mc r) Ci).map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j O1.zero).1).coeff
      (GPoly.toPoly P ((((conjM Fc ks m N C (rescaleME Fc ks m (O.deriv a)
      N Mc r) Ci).map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j O1.zero).2).natDegree =
      P.sem (O.deriv a) * (lamI j i : T.F m) * (GPoly.toPoly P ((((conjM Fc ks m N C
      (rescaleME Fc ks m (O.deriv a) N Mc r) Ci).map fun l ↦ l.map (redC Fc ks m)).getD i []).getD j
      O1.zero).2).leadingCoeff := by
    intro i hi j hj
    obtain ⟨A, B', hB', hAB, hc, hv⟩ := hlim i hi j hj
    rw [conjRed_entry N C _ Ci i j hi hj]
    exact T.limit_of_sem h1 htr _ (T.redC_den_ne_zero m h1 _) A B' hB' hAB _ hc
      (by rw [T.sem_redC m h1 htr]; exact hv)
  have hWE : (exactWE Fc ks m (fun n A0 q hh G0 ↦ expSysB Fc ks m a rdeD n A0 q hh G0 0) N
      ((conjM Fc ks m N C (rescaleME Fc ks m (O.deriv a) N Mc r) Ci).map fun l ↦ l.map (redC Fc ks m))
      ((vecCi Fc ks m N (rescaleF Fc ks m N f r) Ci).map (redC Fc ks m)) E).isSome :=
    T.exactWE_isSome_exp m h0 a rdeD hb0 N hN _ _
      (fun i hi j hj ↦ ⟨by rw [conjRed_entry N C _ Ci i j hi hj]; exact T.redC_den_ne_zero m h1 _,
        (hlim' i hi j hj).1⟩)
      lamI (fun i hi j hj ↦ (hlim' i hi j hj).2) htri
      (by
        intro c hc
        obtain ⟨c', -, rfl⟩ := List.mem_map.mp hc
        exact T.redC_den_ne_zero m h1 _)
      E hE0
  unfold exactWRE
  simp only [hN, ↓reduceIte]
  rw [← hO1, ← hO, ← hMm, ← hq, ← hhh]
  simp only [hcheck, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hq0c]
  rw [← hA0]
  simp only [hzc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hB]
  exact hWE

end Lim

end MTower

end Curves.MT
