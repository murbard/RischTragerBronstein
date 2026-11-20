import RischTragerBronstein.Jacobian.HypDecideNF
import RischTragerBronstein.Jacobian.TorsNFComplete

/-!
# Completeness of the number-field procedure

* `hypDecideADK_eventually`: with valid splitting data, and a family of torsion oracles that
  eventually answer, `hypDecideADK` answers for every large search bound.
* `hypDecideNF_eventually`: if `D` is squarefree and splits over `K = NF M`, `f` takes non-zero
  square values in `K` at its roots, and `K` contains `g` base points `(aᵢ, bᵢ)` with distinct
  `aᵢ ∈ ℤ` (not roots of `D`) and `bᵢ² = f(aᵢ) ≠ 0`, then `hypDecideNF M f g A D B` answers for
  every large `B`.
-/

open Polynomial CPoly CPoly.Kron EllAlgo EllQuad QCoords

namespace Jac

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K] [QCoords K]

/-- **Completeness of `hypDecideADK`** for an eventually answering family of torsion oracles. -/
theorem hypDecideADK_eventually {f : List ℤ} {g : ℕ}
    (hdeg : ((toPoly f).map (Int.castRingHom ℚ)).natDegree = 2 * g + 1)
    (tors : ℕ → List (K × K × ℤ) → Option (Option ℕ)) (htors : ∀ B, TorsSpec f g (tors B))
    (A D : CPoly ℚ) (hD0 : toPoly D ≠ 0) (pts : List (K × K))
    (hsplit : (toPoly D).map (algebraMap ℚ K) =
      C ((lead (trim D) : ℚ) : K) * ((pts.map Prod.fst).map fun r ↦ X - C r).prod)
    (hon : ∀ q ∈ pts, q.2 * q.2 = evalC (curveK f) q.1 ∧ q.2 ≠ 0)
    (hnd : (pts.map Prod.fst).Nodup)
    (hev : ∀ l : List (K × K × ℤ), (∀ q ∈ l, (toPoly (curveK (K := K) f)).eval q.1 = q.2.1 ^ 2 ∧
      q.2.1 ≠ 0 ∧ q.2.2 ≠ 0) → (l.map Prod.fst).Nodup → (∀ q ∈ l, q.1 ∈ pts.map Prod.fst) →
      ∃ B0, ∀ B, B0 ≤ B → (tors B l).isSome) :
    ∃ B0, ∀ B, B0 ≤ B → hypDecideADK f g (tors B) A D pts ≠ none := by
  classical
  set ptsR := pts.map fun q ↦ (q.1, q.2, evalQK A q.1 / (evalQK (CPoly.deriv D) q.1 * q.2))
  have honR : ∀ q ∈ ptsR, q.2.1 * q.2.1 = evalC (curveK f) q.1 ∧ q.2.1 ≠ 0 := by
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
  unfold hypDecideADK
  rw [if_pos (by
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨by rcases h : isZero D with _ | _
              · rfl
              · exact absurd ((isZero_iff _).mp h) hD0, (splitCheck_iff D hD0 _).mpr hsplit⟩)]
  refine hypDecideK_ne_none hdeg (tors B) (htors B) _ ptsR ?_
    fun j ↦ hBj j B (le_trans (Finset.le_sup (Finset.mem_univ j)) hB0)
  simp only [validG, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨honR, hndR⟩

section NF

open NFC

variable (M : CPoly ℚ) [Fact (Irreducible (toPoly M))]

lemma ordsG_spec {f : List ℤ} : ∀ {rs : List (NF M)} {pts : List (NF M × NF M)},
    ordsG M f rs = some pts → pts.map Prod.fst = rs ∧
      ∀ q ∈ pts, q.2 * q.2 = evalC (curveK f) q.1
  | [], pts, h => by simp only [ordsG, Option.some.injEq] at h; subst h; simp
  | α :: t, pts, h => by
    simp only [ordsG] at h
    split at h
    · rename_i β m h1 h2
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨e1, e2⟩ := ordsG_spec h2
      refine ⟨by simp [e1], fun q hq ↦ ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact sqrtNF_spec M h1
      · exact e2 q hq
    · cases h

lemma ordsG_ne_none {f : List ℤ} : ∀ {rs : List (NF M)},
    (∀ α ∈ rs, ∃ β : NF M, β ≠ 0 ∧ β * β = evalC (curveK f) α) → ordsG M f rs ≠ none
  | [], _ => by simp [ordsG]
  | α :: t, h => by
    obtain ⟨β, hβ0, hβ⟩ := h α List.mem_cons_self
    obtain ⟨β', h1⟩ := Option.ne_none_iff_exists'.mp
      (sqrtNF_ne_none M hβ (by rw [← hβ]; exact mul_ne_zero hβ0 hβ0))
    obtain ⟨m, h2⟩ := Option.ne_none_iff_exists'.mp
      (ordsG_ne_none fun α' hα' ↦ h α' (List.mem_cons_of_mem _ hα'))
    simp [ordsG, h1, h2]

set_option maxHeartbeats 1600000 in
/-- **Completeness of `hypDecideNF`**: if `D` is squarefree and splits over `K = NF M`, `f` takes
non-zero square values in `K` at the roots of `D`, and `g` base points `(aᵢ, bᵢ)` with distinct
`aᵢ ∈ ℤ`, `D(aᵢ) ≠ 0` and `bᵢ² = f(aᵢ) ≠ 0` exist in `K`, the procedure answers for every
large search bound. -/
theorem hypDecideNF_eventually (hMZ : ∀ q ∈ M, q.den = 1) {f : List ℤ} {g : ℕ}
    (hlen : f.length = 2 * g + 2) (hlcf : f.getD (2 * g + 1) 0 ≠ 0)
    (hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ)))
    (hdeg : ((toPoly f).map (Int.castRingHom ℚ)).natDegree = 2 * g + 1)
    (A D : CPoly ℚ) (hDsq : Squarefree (toPoly D)) (lc : NF M) (rs0 : List (NF M))
    (hsplit : (toPoly D).map (algebraMap ℚ (NF M)) = C lc * (rs0.map fun r ↦ X - C r).prod)
    (hpt : ∀ α : NF M, aeval α (toPoly D) = 0 →
      ∃ β : NF M, β ≠ 0 ∧ β * β = evalC (curveK f) α)
    (as : List ℤ) (bs : List (NF M)) (hasl : as.length = g) (hbsl : bs.length = g)
    (hab : ∀ i (hi : i < g), bs[i]'(by omega) * bs[i]'(by omega) =
      ((evalC f (as[i]'(by omega)) : ℤ) : NF M) ∧ bs[i]'(by omega) ≠ 0)
    (hasnd : as.Nodup) (hasD : ∀ a ∈ as, (toPoly D).eval (a : ℚ) ≠ 0) :
    ∃ B0, ∀ B, B0 ≤ B → hypDecideNF M f g A D B ≠ none := by
  classical
  have hM1 : 0 < (toPoly M).natDegree :=
    Irreducible.natDegree_pos (Fact.out : Irreducible (toPoly M))
  have hD0 : toPoly D ≠ 0 := hDsq.ne_zero
  have hgL : toPoly (liftK (K := NF M) D) = (toPoly D).map (algebraMap ℚ (NF M)) := toPoly_liftK D
  have hgsq : Squarefree (toPoly (liftK (K := NF M) D)) := by
    rw [hgL]; exact ((PerfectField.separable_iff_squarefree).mpr hDsq).map.squarefree
  obtain ⟨rs, hrs, hall⟩ := rootsIn_complete M _ hgsq
  have hroot : ∀ α, aeval α (toPoly D) = 0 ↔ α ∈ rs := by
    intro α
    constructor
    · intro h; apply hall; rw [hgL, eval_map_algebraMap]; exact h
    · intro h; have := rootsIn_sound M _ hrs α h; rwa [hgL, eval_map_algebraMap] at this
  have hsqK : Squarefree ((toPoly D).map (algebraMap ℚ (NF M))) :=
    ((PerfectField.separable_iff_squarefree).mpr hDsq).map.squarefree
  have hlc : lc ≠ 0 := by
    rintro rfl; rw [C_0, zero_mul, Polynomial.map_eq_zero_iff (algebraMap ℚ (NF M)).injective] at hsplit
    exact hD0 hsplit
  have hnd0 : rs0.Nodup := by
    rw [List.nodup_iff_sublist]
    intro r hr
    have hdvd : (X - C r) * (X - C r) ∣ (toPoly D).map (algebraMap ℚ (NF M)) := by
      rw [hsplit]
      refine Dvd.dvd.mul_left ?_ _
      simpa using (hr.map (fun r ↦ X - C r)).prod_dvd_prod
    exact (irreducible_X_sub_C r).not_isUnit (hsqK _ hdvd)
  have hmem0 : ∀ α, α ∈ rs0 ↔ α ∈ rs.dedup := by
    intro α
    rw [List.mem_dedup, ← hroot, ← eval_map_algebraMap, hsplit, eval_mul, eval_C,
      eval_list_prod, List.map_map]
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
  have hlcD : lc = (((lead (trim D) : ℚ)) : NF M) := by
    have hmon : (rs0.map fun r ↦ X - C r).prod.Monic := by
      have := monic_multiset_prod_of_monic (rs0 : Multiset (NF M)) (fun r ↦ X - C r)
        (fun r _ ↦ monic_X_sub_C r)
      simpa [Multiset.map_coe, Multiset.prod_coe] using this
    have := congrArg leadingCoeff hsplit
    rw [leadingCoeff_map_of_injective (algebraMap ℚ (NF M)).injective, leadingCoeff_mul,
      leadingCoeff_C, hmon.leadingCoeff, mul_one] at this
    rw [← this, show lead (trim D) = lcT D from rfl, lcT_eq]; rfl
  obtain ⟨pts, hpts⟩ := Option.ne_none_iff_exists'.mp (ordsG_ne_none M (f := f)
    fun α hα ↦ hpt α ((hroot α).mpr (List.mem_dedup.mp hα)))
  obtain ⟨e1, e2⟩ := ordsG_spec M hpts
  have hmZ : toPoly M = (toPoly (M.map Rat.num)).map (Int.castRingHom ℚ) :=
    (Kron.polyZ_map M hMZ).symm
  have hdegK : (toPoly (curveK (K := NF M) f)).natDegree = 2 * g + 1 := by
    rw [toPoly_curveK, natDegree_map_eq_of_injective (algebraMap ℚ (NF M)).injective, hdeg]
  obtain ⟨B0, hB0⟩ := hypDecideADK_eventually hdeg
    (fun B ↦ torsNF (M := M) (M.map Rat.num) f g B) (fun B ↦ torsNF_spec hmZ hdegK B) A D hD0 pts
    (by rw [e1, hsplit, hlcD, hperm.map _ |>.prod_eq])
    (fun q hq ↦ ⟨e2 q hq, fun h0 ↦ by
      have hmem : q.1 ∈ rs.dedup := e1 ▸ List.mem_map_of_mem hq
      obtain ⟨β, hβ0, hβ⟩ := hpt q.1 ((hroot _).mpr (List.mem_dedup.mp hmem))
      have := e2 q hq
      rw [h0, zero_mul, ← hβ] at this
      exact hβ0 (mul_self_eq_zero.mp this.symm)⟩)
    (e1 ▸ List.nodup_dedup _)
    (fun l hl hnd hmem ↦ torsNF_eventually hMZ hlen hlcf hsq hM1 l hl hnd as bs hasl hbsl hab
      hasnd fun q hq a ha heq ↦ by
        have h1 : q.1 ∈ rs.dedup := e1 ▸ hmem q hq
        have h2 := (hroot _).mpr (List.mem_dedup.mp h1)
        rw [heq, show ((a : ℤ) : NF M) = algebraMap ℚ (NF M) (a : ℚ) by simp,
          aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval] at h2
        exact hasD a ha ((algebraMap ℚ (NF M)).injective (by rw [h2, map_zero])))
  refine ⟨B0, fun B hB ↦ ?_⟩
  unfold hypDecideNF
  rw [hrs]
  simp only
  rw [hpts]
  exact hB0 B hB

end NF

end Jac
