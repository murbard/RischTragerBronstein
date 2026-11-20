import RischTragerBronstein.Jacobian.HypDecideNFC

/-!
# Completeness of the procedure for a curve over a number field

* `hypDecideADKF_eventually`: with valid splitting data over `K`, and an eventually answering
  family of torsion oracles, `hypDecideADKF` answers for every large bound.
* `hypDecideNFC_eventually`: for `f ∈ K[x]` squarefree of degree `2g + 1`, `D ≠ 0`, if the
  non-branch part `S` of `D` splits over `K = NF M`, `f` takes non-zero square values in `K` at
  its roots, and `K` contains `g` base points `(aᵢ, bᵢ)` (`aᵢ ∈ ℤ` distinct, `S(aᵢ) ≠ 0`,
  `bᵢ² = f(aᵢ) ≠ 0`), then `hypDecideNFC M f g A D B` answers for every large `B`.
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad QCoords

namespace Jac

section ADK

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K] [QCoords K]

/-- **Completeness of `hypDecideADKF`** for an eventually answering family of oracles. -/
theorem hypDecideADKF_eventually {f : CPoly K} {g : ℕ} (hdeg : (toPoly f).natDegree = 2 * g + 1)
    (tors : ℕ → List (K × K × ℤ) → Option (Option ℕ)) (htors : ∀ B, TorsSpecF f g (tors B))
    (A D : CPoly K) (hD0 : toPoly D ≠ 0) (pts : List (K × K))
    (hsplit : toPoly D = C (lead (trim D)) * ((pts.map Prod.fst).map fun r ↦ X - C r).prod)
    (hon : ∀ q ∈ pts, q.2 * q.2 = evalC f q.1 ∧ q.2 ≠ 0)
    (hnd : (pts.map Prod.fst).Nodup)
    (hev : ∀ l : List (K × K × ℤ), (∀ q ∈ l, (toPoly f).eval q.1 = q.2.1 ^ 2 ∧
      q.2.1 ≠ 0 ∧ q.2.2 ≠ 0) → (l.map Prod.fst).Nodup → (∀ q ∈ l, q.1 ∈ pts.map Prod.fst) →
      ∃ B0, ∀ B, B0 ≤ B → (tors B l).isSome) :
    ∃ B0, ∀ B, B0 ≤ B → hypDecideADKF f g (tors B) A D pts ≠ none := by
  classical
  set ptsR := pts.map fun q ↦ (q.1, q.2, evalC A q.1 / (evalC (CPoly.deriv D) q.1 * q.2))
  have honR : ∀ q ∈ ptsR, q.2.1 * q.2.1 = evalC f q.1 ∧ q.2.1 ≠ 0 := by
    intro q hq
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    exact hon q0 hq0
  have hfst : ptsR.map Prod.fst = pts.map Prod.fst := by
    simp [ptsR, List.map_map, Function.comp_def]
  have hndR : (ptsR.map Prod.fst).Nodup := hfst ▸ hnd
  have hB : ∀ j : Fin (dim K), ∃ B0, ∀ B, B0 ≤ B → (tors B (compPts j ptsR)).isSome := by
    intro j
    refine hev _ (fun q hq ↦ ?_) ?_ (fun q hq ↦ ?_)
    · obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
      obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq1
      obtain ⟨h1, h2⟩ := honR q0 hq0
      exact ⟨by rw [← evalC_eq, ← h1, sq], h2, by simpa using hq2⟩
    · refine List.Nodup.sublist ((List.filter_sublist).map _) ?_
      rw [PjK, intPtsK, List.map_map]; exact hndR
    · obtain ⟨hq1, -⟩ := List.mem_filter.mp hq
      obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq1
      rw [← hfst]
      exact List.mem_map_of_mem hq0
  choose Bj hBj using hB
  refine ⟨Finset.univ.sup Bj, fun B hB0 ↦ ?_⟩
  unfold hypDecideADKF
  rw [if_pos (by
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨by rcases h : isZero D with _ | _
              · rfl
              · exact absurd ((isZero_iff _).mp h) hD0, (splitCheckK_iff D _).mpr hsplit⟩)]
  refine hypDecideKF_ne_none hdeg (tors B) (htors B) _ ptsR ?_
    fun j ↦ hBj j B (le_trans (Finset.le_sup (Finset.mem_univ j)) hB0)
  simp only [validGF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨honR, hndR⟩

end ADK

section NF

open NFC

variable (M : CPoly ℚ) [Fact (Irreducible (toPoly M))]

lemma ordsGK_spec {f : CPoly (NF M)} : ∀ {rs : List (NF M)} {pts : List (NF M × NF M)},
    ordsGK M f rs = some pts → pts.map Prod.fst = rs ∧ ∀ q ∈ pts, q.2 * q.2 = evalC f q.1
  | [], pts, h => by simp only [ordsGK, Option.some.injEq] at h; subst h; simp
  | α :: t, pts, h => by
    simp only [ordsGK] at h
    split at h
    · rename_i β m h1 h2
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨e1, e2⟩ := ordsGK_spec h2
      refine ⟨by simp [e1], fun q hq ↦ ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact sqrtNF_spec M h1
      · exact e2 q hq
    · cases h

lemma ordsGK_ne_none {f : CPoly (NF M)} : ∀ {rs : List (NF M)},
    (∀ α ∈ rs, ∃ β : NF M, β ≠ 0 ∧ β * β = evalC f α) → ordsGK M f rs ≠ none
  | [], _ => by simp [ordsGK]
  | α :: t, h => by
    obtain ⟨β, hβ0, hβ⟩ := h α List.mem_cons_self
    obtain ⟨β', h1⟩ := Option.ne_none_iff_exists'.mp
      (sqrtNF_ne_none M hβ (by rw [← hβ]; exact mul_ne_zero hβ0 hβ0))
    obtain ⟨m, h2⟩ := Option.ne_none_iff_exists'.mp
      (ordsGK_ne_none fun α' hα' ↦ h α' (List.mem_cons_of_mem _ hα'))
    simp [ordsGK, h1, h2]

set_option maxHeartbeats 3200000 in
/-- **Completeness of `hypDecideNFC`.** -/
theorem hypDecideNFC_eventually (hMZ : ∀ q ∈ M, q.den = 1) {f : CPoly (NF M)} {g : ℕ}
    (hlen : f.length = 2 * g + 2) (hlcf : f.getD (2 * g + 1) 0 ≠ 0)
    (hsq : Squarefree (toPoly f)) (A D : CPoly (NF M)) (hD : toPoly D ≠ 0)
    (lc : NF M) (rs0 : List (NF M))
    (hsplitS : toPoly (nbPartK f D) = C lc * (rs0.map fun r ↦ X - C r).prod)
    (hpt : ∀ α : NF M, (toPoly (nbPartK f D)).eval α = 0 →
      ∃ β : NF M, β ≠ 0 ∧ β * β = evalC f α)
    (as bs : List (NF M)) (hasl : as.length = g) (hbsl : bs.length = g)
    (hab : ∀ i (hi : i < g), bs[i]'(by omega) * bs[i]'(by omega) =
      (toPoly f).eval (as[i]'(by omega)) ∧ bs[i]'(by omega) ≠ 0)
    (hasnd : as.Nodup) (hasS : ∀ a ∈ as, (toPoly (nbPartK f D)).eval a ≠ 0) :
    ∃ B0, ∀ B, B0 ≤ B → hypDecideNFC M f g A D B ≠ none := by
  classical
  have hM1 : 0 < (toPoly M).natDegree :=
    Irreducible.natDegree_pos (Fact.out : Irreducible (toPoly M))
  have hdeg : (toPoly f).natDegree = 2 * g + 1 := by
    have hcoef : ∀ n, (toPoly f).coeff n = f.getD n 0 := coeff_toPoly f
    refine le_antisymm ?_ (le_natDegree_of_ne_zero (by rw [hcoef]; exact hlcf))
    rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [hcoef, List.getD_eq_default _ _ (by rw [hlen]; exact_mod_cast hn)]
  set S := nbPartK f D
  have hS0 : toPoly S ≠ 0 := nbPartK_ne_zero f D hD
  have hSsq : Squarefree (toPoly S) := squarefree_nbPartK f D hD
  -- the Hermite system
  obtain ⟨cs, hcs⟩ := Option.ne_none_iff_exists'.mp (hermite_solve_ne_noneK f A D hsq
    (by rw [hdeg]; omega) hD f.length le_rfl)
  -- the roots of `S`
  obtain ⟨rs, hrs, hall⟩ := rootsIn_complete M S hSsq
  have hroot : ∀ α, (toPoly S).eval α = 0 ↔ α ∈ rs := fun α ↦
    ⟨hall α, rootsIn_sound M S hrs α⟩
  have hlc : lc ≠ 0 := by
    rintro rfl; rw [C_0, zero_mul] at hsplitS; exact hS0 hsplitS
  have hnd0 : rs0.Nodup := by
    rw [List.nodup_iff_sublist]
    intro r hr
    have hdvd : (X - C r) * (X - C r) ∣ toPoly S := by
      rw [hsplitS]
      refine Dvd.dvd.mul_left ?_ _
      simpa using (hr.map (fun r ↦ X - C r)).prod_dvd_prod
    exact (irreducible_X_sub_C r).not_isUnit (hSsq _ hdvd)
  have hmem0 : ∀ α, α ∈ rs0 ↔ α ∈ rs.dedup := by
    intro α
    rw [List.mem_dedup, ← hroot, hsplitS, eval_mul, eval_C, eval_list_prod, List.map_map]
    constructor
    · intro h
      apply mul_eq_zero_of_right
      apply List.prod_eq_zero
      exact List.mem_map.mpr ⟨α, h, by simp⟩
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hlc
      · obtain ⟨r, hr, hr0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h)
        simp only [Function.comp_apply, eval_sub, eval_X, eval_C, sub_eq_zero] at hr0
        rwa [hr0]
  have hperm : rs0.Perm rs.dedup := (List.perm_ext_iff_of_nodup hnd0 (List.nodup_dedup _)).mpr hmem0
  have hlcS : lc = lead (trim S) := by
    have hmon : (rs0.map fun r ↦ X - C r).prod.Monic := by
      have := monic_multiset_prod_of_monic (rs0 : Multiset (NF M)) (fun r ↦ X - C r)
        (fun r _ ↦ monic_X_sub_C r)
      simpa [Multiset.map_coe, Multiset.prod_coe] using this
    have h1 := congrArg leadingCoeff hsplitS
    rw [leadingCoeff_mul, leadingCoeff_C, hmon.leadingCoeff, mul_one] at h1
    rw [← h1]
    have htr : trim S ≠ [] := fun h ↦ hS0 ((trim_eq_nil_iff S).mp h)
    have hl := length_trim htr
    rw [leadingCoeff, ← toPoly_trim, coeff_toPoly, lead, List.getLastD_eq_getLast?,
      List.getLast?_eq_getElem?, hl]
    simp [List.getD_eq_getElem?_getD]
  obtain ⟨pts, hpts⟩ := Option.ne_none_iff_exists'.mp (ordsGK_ne_none M (f := f)
    fun α hα ↦ hpt α ((hroot α).mpr (List.mem_dedup.mp hα)))
  obtain ⟨e1, e2⟩ := ordsGK_spec M hpts
  have hmZ : toPoly M = (toPoly (M.map Rat.num)).map (Int.castRingHom ℚ) :=
    (Kron.polyZ_map M hMZ).symm
  obtain ⟨B0, hB0⟩ := hypDecideADKF_eventually hdeg
    (fun B ↦ torsNFF (M := M) (M.map Rat.num) f g B) (fun B ↦ torsNFF_spec hmZ hdeg B)
    (cs.drop (A.length + D.length)) S hS0 pts
    (by rw [e1, hsplitS, hlcS, hperm.map _ |>.prod_eq])
    (fun q hq ↦ ⟨e2 q hq, fun h0 ↦ by
      have hmem : q.1 ∈ rs.dedup := e1 ▸ List.mem_map_of_mem hq
      obtain ⟨β, hβ0, hβ⟩ := hpt q.1 ((hroot _).mpr (List.mem_dedup.mp hmem))
      have := e2 q hq
      rw [h0, zero_mul, ← hβ] at this
      exact hβ0 (mul_self_eq_zero.mp this.symm)⟩)
    (e1 ▸ List.nodup_dedup _)
    (fun l hl hnd hmem ↦ torsNFF_eventually hMZ hlen hlcf hsq hM1 l hl hnd as bs hasl hbsl hab
      hasnd fun q hq a ha heq ↦ by
        have h1 : q.1 ∈ rs.dedup := e1 ▸ hmem q hq
        have h2 := (hroot _).mpr (List.mem_dedup.mp h1)
        rw [heq] at h2
        exact hasS a ha h2)
  refine ⟨B0, fun B hB ↦ ?_⟩
  unfold hypDecideNFC
  rw [if_neg (fun h ↦ hD ((isZero_iff D).mp h))]
  simp only
  rw [hcs]
  simp only
  rw [hrs]
  simp only
  rw [hpts]
  exact hB0 B hB

end NF

end Jac
