import RischTragerBronstein.Algebraic.NFAdjoin
import RischTragerBronstein.Algebraic.EllDecideNF

/-!
# Splitting fields

`growStep`: over `K = ℚ[θ]/(f)`, divide `D` by the product of its roots in `K`, and adjoin a root
of the quotient (`adjoinStep`) in `K' = ℚ[γ]/(M)`, `M` an irreducible factor of the norm.
`growStep_spec`: if `D` is squarefree with `c < deg D` distinct roots in `K`, then `D` has at
least `c + 1` distinct roots in `K'`. Iterating (`splitLoop`) gives a number field over which
`D` splits (`splitLoop_spec`).
-/

open Polynomial CPoly

namespace NFC

variable (f : CPoly ℚ) [hf : Fact (Irreducible (toPoly f))]

/-- The part of `D` without the roots `rs`. -/
def remPart (D : CPoly ℚ) (rs : List (NF f)) : CPoly (NF f) :=
  (divMod (EllQuad.liftK (K := NF f) D) (EllQuad.prodLin rs)).1

/-- The first admissible shift. -/
def firstGood (h : CPoly (NF f)) : Option ℚ :=
  (List.range (sBound f h)).findSome? fun i : ℕ ↦
    if squarefreeCheck (normPoly f h ((i : ℚ) + 1)) then some ((i : ℚ) + 1) else none

/-- **One growth step**: the defining polynomial of the next field. -/
noncomputable def growStep (D : CPoly ℚ) : Option (Σ' M : CPoly ℚ, Kron.irredQ M = true) :=
  match rootsIn f (EllQuad.liftK (K := NF f) D) with
  | none => none
  | some rs =>
    match firstGood f (remPart f D rs.dedup) with
    | none => none
    | some t =>
      match (Kron.factorQ (Kron.degC (normPoly f (remPart f D rs.dedup) t) + 1)
          (normPoly f (remPart f D rs.dedup) t)).head? with
      | none => none
      | some M => if hM : Kron.irredQ M = true then some ⟨M, hM⟩ else none

lemma firstGood_spec {h : CPoly (NF f)} {t : ℚ} (ht : firstGood f h = some t) :
    Squarefree (toPoly (normPoly f h t)) := by
  unfold firstGood at ht
  obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some ht
  split_ifs at hi with hc
  simp only [Option.some.injEq] at hi
  subst hi
  exact squarefreeCheck_sound hc

lemma firstGood_ne_none {h : CPoly (NF f)} (hsq : Squarefree (toPoly h)) :
    firstGood f h ≠ none := by
  obtain ⟨i, hi, hs⟩ := exists_good_s f h hsq
  intro h0
  unfold firstGood at h0
  rw [List.findSome?_eq_none_iff] at h0
  have := h0 i (List.mem_range.mpr hi)
  rw [if_pos (squarefreeCheck_complete' hs)] at this
  exact Option.some_ne_none _ this


/-- `D` has at least `k` distinct roots in `ℚ[x]/(M)`. -/
def HasRoots (M : CPoly ℚ) (hM : Kron.irredQ M = true) (D : CPoly ℚ) (k : ℕ) : Prop :=
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  ∃ l : List (NF M), l.Nodup ∧ k ≤ l.length ∧ ∀ a ∈ l, aeval a (toPoly D) = 0

omit hf in
lemma aeval_ringHom_rat {A B : Type*} [Field A] [Field B] [CharZero A] [CharZero B] (φ : A →+* B)
    (a : A) (P : ℚ[X]) : φ (aeval a P) = aeval (φ a) P :=
  (Polynomial.aeval_algHom_apply φ.toRatAlgHom a P).symm

set_option maxHeartbeats 3200000 in
/-- **The growth step adds a root.** -/
theorem growStep_spec (D : CPoly ℚ) (hDsq : Squarefree (toPoly D)) (rs : List (NF f))
    (hrs : rootsIn f (EllQuad.liftK (K := NF f) D) = some rs)
    (hlt : rs.dedup.length < (toPoly D).natDegree) :
    ∃ M hM, growStep f D = some ⟨M, hM⟩ ∧ HasRoots M hM D (rs.dedup.length + 1) ∧
      (letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      ∃ θ' : NF M, aeval θ' (toPoly f) = 0) := by
  classical
  set Dk := toPoly (EllQuad.liftK (K := NF f) D) with hDkdef
  have hDk : Dk = (toPoly D).map (algebraMap ℚ (NF f)) := EllQuad.toPoly_liftK D
  have hDksq : Squarefree Dk := by
    rw [hDk]; exact ((PerfectField.separable_iff_squarefree).mpr hDsq).map.squarefree
  have hDk0 : Dk ≠ 0 := hDksq.ne_zero
  have hroot : ∀ a ∈ rs, Dk.eval a = 0 := rootsIn_sound f _ hrs
  set P := EllQuad.prodLin rs.dedup
  have hP : toPoly P = (rs.dedup.map fun r ↦ X - C r).prod := EllQuad.toPoly_prodLin _
  have hPmon : (toPoly P).Monic := by
    rw [hP]
    have := monic_multiset_prod_of_monic (rs.dedup : Multiset (NF f)) (fun r ↦ X - C r)
      (fun r _ ↦ monic_X_sub_C r)
    simpa [Multiset.map_coe, Multiset.prod_coe] using this
  have hPdvd : toPoly P ∣ Dk := by
    have hle : (rs.dedup : Multiset (NF f)) ≤ Dk.roots := by
      rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (List.nodup_dedup rs))]
      intro a ha
      exact (mem_roots hDk0).mpr (hroot a (List.mem_dedup.mp ha))
    have := (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hle (f := fun r ↦ X - C r))).trans
      (prod_multiset_X_sub_C_dvd Dk)
    rw [hP]; simpa [Multiset.map_coe, Multiset.prod_coe] using this
  set h := remPart f D rs.dedup
  have hsplitK : Dk = toPoly h * toPoly P := by
    have hsp := divMod_spec (EllQuad.liftK (K := NF f) D) P
    have hr : toPoly (divMod (EllQuad.liftK (K := NF f) D) P).2 = 0 := by
      have hdr : toPoly P ∣ toPoly (divMod (EllQuad.liftK (K := NF f) D) P).2 := by
        have : toPoly (divMod (EllQuad.liftK (K := NF f) D) P).2 =
            Dk - toPoly (divMod (EllQuad.liftK (K := NF f) D) P).1 * toPoly P := by
          rw [hDkdef, hsp]; ring
        rw [this]; exact dvd_sub hPdvd (dvd_mul_left _ _)
      exact eq_zero_of_dvd_of_degree_lt hdr (divMod_degree_lt _ _ hPmon.ne_zero)
    rw [hDkdef, hsp, hr, add_zero]; rfl
  have hh0 : toPoly h ≠ 0 := fun h0 ↦ hDk0 (by rw [hsplitK, h0, zero_mul])
  have hhsq : Squarefree (toPoly h) := hDksq.squarefree_of_dvd ⟨toPoly P, hsplitK⟩
  have hPdeg : (toPoly P).natDegree = rs.dedup.length := by
    have := natDegree_multiset_prod_X_sub_C_eq_card (rs.dedup : Multiset (NF f))
    rw [hP]; simpa [Multiset.map_coe, Multiset.prod_coe] using this
  have hDkdeg : Dk.natDegree = (toPoly D).natDegree := by
    rw [hDk, natDegree_map_eq_of_injective (algebraMap ℚ (NF f)).injective]
  have hhpos : 0 < (toPoly h).natDegree := by
    have := congrArg natDegree hsplitK
    rw [natDegree_mul hh0 hPmon.ne_zero, hPdeg, hDkdeg] at this
    omega
  -- the shift
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp (firstGood_ne_none f hhsq)
  have hN := firstGood_spec f ht
  set N := normPoly f h t
  have hN0 : toPoly N ≠ 0 := hN.ne_zero
  -- `N` is not constant: it has a root in `ℚ̄`
  have hNpos : 0 < (toPoly N).natDegree := by
    obtain ⟨θ, hθ⟩ := exists_root_fL f
    have hθr := root_of_mem f hθ
    have hhθ : (toPoly (h.map (evAt f θ))).natDegree = (toPoly h).natDegree := by
      rw [← map_rho f h hθr, natDegree_map_eq_of_injective (rho f hθr).injective]
    obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root (toPoly (h.map (evAt f θ))) (by
      rw [degree_eq_natDegree (fun h0 ↦ by rw [h0, natDegree_zero] at hhθ; omega), hhθ]
      exact_mod_cast hhpos.ne')
    by_contra h0
    push_neg at h0
    have hc : toPoly N = C ((toPoly N).coeff 0) := eq_C_of_natDegree_le_zero h0
    have hev : ((toPoly N).map (algebraMap ℚ QB)).eval (β + algebraMap ℚ QB t * θ) = 0 := by
      rw [normPoly_map f (fL_splits f), eval_mul, eval_multiset_prod]
      apply mul_eq_zero_of_right
      apply Multiset.prod_eq_zero
      refine Multiset.mem_map.mpr ⟨_, Multiset.mem_map_of_mem _ hθ, ?_⟩
      simp only [eval_comp, eval_sub, eval_X, eval_C, add_sub_cancel_right]
      exact hβ
    rw [hc, Polynomial.map_C, eval_C, map_eq_zero_iff _ (algebraMap ℚ QB).injective] at hev
    exact hN0 (by rw [hc, hev, C_0])
  obtain ⟨hirr, k, hk, hNk⟩ := Kron.factorQ_spec (Kron.degC N + 1) N hNpos
    (by rw [Kron.degC_eq N hN0]; omega)
  obtain ⟨M, hMhead⟩ : ∃ M, (Kron.factorQ (Kron.degC N + 1) N).head? = some M := by
    cases hl : Kron.factorQ (Kron.degC N + 1) N with
    | nil =>
      rw [hl] at hNk
      simp at hNk
      rw [hNk, natDegree_C] at hNpos; omega
    | cons M t => exact ⟨M, rfl⟩
  have hMmem : M ∈ Kron.factorQ (Kron.degC N + 1) N := List.mem_of_mem_head? hMhead
  have hMirr : Kron.irredQ M = true := hirr M hMmem
  have hMdvd : toPoly M ∣ toPoly N := by
    rw [hNk]; exact Dvd.dvd.mul_left (List.dvd_prod (List.mem_map_of_mem hMmem)) _
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hMirr⟩
  obtain ⟨⟨θ'0, α'0⟩, hstep0⟩ := Option.ne_none_iff_exists'.mp (adjoinStep_complete f M h t hN hMdvd)
  refine ⟨M, hMirr, ?_, ?_, θ'0, (adjoinStep_sound f M h t hstep0).1⟩
  · unfold growStep
    rw [hrs]
    simp only
    rw [ht]
    simp only
    rw [hMhead]
    simp only [dif_pos hMirr]
  · letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hMirr⟩
    obtain ⟨⟨θ', α'⟩, hstep⟩ := Option.ne_none_iff_exists'.mp (adjoinStep_complete f M h t hN hMdvd)
    obtain ⟨hθ', hα'⟩ := adjoinStep_sound f M h t hstep
    set e := emb f M hθ'
    have hDM : (toPoly D).map (algebraMap ℚ (NF M)) = ((toPoly h).map e) * ((toPoly P).map e) := by
      rw [← Polynomial.map_mul, ← hsplitK, hDkdef, emb_liftK, EllQuad.toPoly_liftK]
    have hDMsq : Squarefree ((toPoly D).map (algebraMap ℚ (NF M))) :=
      ((PerfectField.separable_iff_squarefree).mpr hDsq).map.squarefree
    have hα'root : ((toPoly h).map e).eval α' = 0 := by rw [map_emb_eq]; exact hα'
    refine ⟨rs.dedup.map e ++ [α'], ?_, by simp, ?_⟩
    · rw [List.nodup_append]
      refine ⟨(List.nodup_dedup rs).map e.injective, List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      rw [List.mem_singleton] at hb
      subst hb
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
      have hd1 : X - C (e r) ∣ (toPoly h).map e := by rw [hab]; exact dvd_iff_isRoot.mpr hα'root
      have hd2 : X - C (e r) ∣ (toPoly P).map e := by
        rw [hP, Polynomial.map_list_prod, List.map_map]
        apply List.dvd_prod
        exact List.mem_map.mpr ⟨r, hr, by simp⟩
      have := hDMsq (X - C (e r)) (by rw [hDM]; exact mul_dvd_mul hd1 hd2)
      exact (irreducible_X_sub_C _).not_isUnit this
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
        have h0 := hroot r (List.mem_dedup.mp hr)
        rw [hDk, eval_map_algebraMap] at h0
        rw [← aeval_ringHom_rat e r, h0, map_zero]
      · rw [List.mem_singleton] at ha
        subst ha
        rw [← eval_map_algebraMap, hDM, eval_mul, hα'root, zero_mul]



section Ext

variable (f : CPoly ℚ) [hf : Fact (Irreducible (toPoly f))]

/-- **Adjoin a root of `h ∈ K[x]`**: the defining polynomial of the extension. -/
def extStep (h : CPoly (NF f)) : Option (Σ' M : CPoly ℚ, Kron.irredQ M = true) :=
  match firstGood f h with
  | none => none
  | some t =>
    match (Kron.factorQ (Kron.degC (normPoly f h t) + 1) (normPoly f h t)).head? with
    | none => none
    | some M => if hM : Kron.irredQ M = true then some ⟨M, hM⟩ else none

/-- In `ℚ[x]/(M)` there is an embedding of `K` under which `h` has a root. -/
def ExtProp (M : CPoly ℚ) (hM : Kron.irredQ M = true) (h : CPoly (NF f)) : Prop :=
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  ∃ (θ' : NF M) (hθ' : aeval θ' (toPoly f) = 0) (α' : NF M),
    ((toPoly h).map (emb f M hθ')).eval α' = 0

set_option maxHeartbeats 3200000 in
theorem extStep_spec (h : CPoly (NF f)) (hsq : Squarefree (toPoly h))
    (hpos : 0 < (toPoly h).natDegree) :
    ∃ M hM, extStep f h = some ⟨M, hM⟩ ∧ ExtProp f M hM h := by
  classical
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp (firstGood_ne_none f hsq)
  have hN := firstGood_spec f ht
  set N := normPoly f h t
  have hN0 : toPoly N ≠ 0 := hN.ne_zero
  have hNpos : 0 < (toPoly N).natDegree := by
    obtain ⟨θ, hθ⟩ := exists_root_fL f
    have hθr := root_of_mem f hθ
    have hhθ : (toPoly (h.map (evAt f θ))).natDegree = (toPoly h).natDegree := by
      rw [← map_rho f h hθr, natDegree_map_eq_of_injective (rho f hθr).injective]
    obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root (toPoly (h.map (evAt f θ))) (by
      rw [degree_eq_natDegree (fun h0 ↦ by rw [h0, natDegree_zero] at hhθ; omega), hhθ]
      exact_mod_cast hpos.ne')
    by_contra h0
    push_neg at h0
    have hc : toPoly N = C ((toPoly N).coeff 0) := eq_C_of_natDegree_le_zero h0
    have hev : ((toPoly N).map (algebraMap ℚ QB)).eval (β + algebraMap ℚ QB t * θ) = 0 := by
      rw [normPoly_map f (fL_splits f), eval_mul, eval_multiset_prod]
      apply mul_eq_zero_of_right
      apply Multiset.prod_eq_zero
      refine Multiset.mem_map.mpr ⟨_, Multiset.mem_map_of_mem _ hθ, ?_⟩
      simp only [eval_comp, eval_sub, eval_X, eval_C, add_sub_cancel_right]
      exact hβ
    rw [hc, Polynomial.map_C, eval_C, map_eq_zero_iff _ (algebraMap ℚ QB).injective] at hev
    exact hN0 (by rw [hc, hev, C_0])
  obtain ⟨hirr, k, hk, hNk⟩ := Kron.factorQ_spec (Kron.degC N + 1) N hNpos
    (by rw [Kron.degC_eq N hN0]; omega)
  obtain ⟨M, hMhead⟩ : ∃ M, (Kron.factorQ (Kron.degC N + 1) N).head? = some M := by
    cases hl : Kron.factorQ (Kron.degC N + 1) N with
    | nil =>
      rw [hl] at hNk
      simp at hNk
      rw [hNk, natDegree_C] at hNpos; omega
    | cons M t => exact ⟨M, rfl⟩
  have hMmem : M ∈ Kron.factorQ (Kron.degC N + 1) N := List.mem_of_mem_head? hMhead
  have hMirr : Kron.irredQ M = true := hirr M hMmem
  have hMdvd : toPoly M ∣ toPoly N := by
    rw [hNk]; exact Dvd.dvd.mul_left (List.dvd_prod (List.mem_map_of_mem hMmem)) _
  refine ⟨M, hMirr, ?_, ?_⟩
  · unfold extStep
    rw [ht]
    simp only
    rw [hMhead]
    simp only [dif_pos hMirr]
  · letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hMirr⟩
    obtain ⟨⟨θ', α'⟩, hstep⟩ := Option.ne_none_iff_exists'.mp (adjoinStep_complete f M h t hN hMdvd)
    obtain ⟨hθ', hα'⟩ := adjoinStep_sound f M h t hstep
    exact ⟨θ', hθ', α', by rw [map_emb_eq]; exact hα'⟩

end Ext

end NFC

namespace NFC

/-- **The splitting loop**: grow the field until `D` splits. -/
noncomputable def splitLoop (D : CPoly ℚ) : ℕ → (M : CPoly ℚ) → Kron.irredQ M = true →
    Option (Σ' M : CPoly ℚ, Kron.irredQ M = true)
  | 0, _, _ => none
  | n + 1, M, hM =>
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    match rootsIn M (EllQuad.liftK (K := NF M) D) with
    | none => none
    | some rs =>
      if rs.dedup.length = Kron.degC D then some ⟨M, hM⟩
      else
        match growStep M D with
        | some ⟨M', hM'⟩ => splitLoop D n M' hM'
        | none => none

lemma length_le_natDegree {K : Type*} [Field K] {p : K[X]} (hp : p ≠ 0) {l : List K}
    (hl : l.Nodup) (hr : ∀ a ∈ l, p.eval a = 0) : l.length ≤ p.natDegree := by
  have hle : (l : Multiset K) ≤ p.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hl)]
    intro a ha; exact (mem_roots hp).mpr (hr a ha)
  have := Multiset.card_le_card hle
  simp only [Multiset.coe_card] at this
  exact this.trans (card_roots' p)

/-- **The loop ends with a field over which `D` splits.** -/
theorem splitLoop_spec (D : CPoly ℚ) (hDsq : Squarefree (toPoly D)) :
    ∀ (n : ℕ) (M : CPoly ℚ) (hM : Kron.irredQ M = true) (k : ℕ), HasRoots M hM D k →
      (toPoly D).natDegree < n + k →
      ∃ M' hM', splitLoop D n M hM = some ⟨M', hM'⟩ ∧ HasRoots M' hM' D (toPoly D).natDegree
  | 0, M, hM, k, hk, hn => by
    exfalso
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    obtain ⟨l, hl, hlen, hr⟩ := hk
    have := length_le_natDegree ((Polynomial.map_ne_zero_iff (algebraMap ℚ (NF M)).injective).mpr
      hDsq.ne_zero) hl (fun a ha ↦ by rw [eval_map_algebraMap]; exact hr a ha)
    rw [natDegree_map_eq_of_injective (algebraMap ℚ (NF M)).injective] at this
    omega
  | n + 1, M, hM, k, hk, hn => by
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    have hgL : toPoly (EllQuad.liftK (K := NF M) D) = (toPoly D).map (algebraMap ℚ (NF M)) :=
      EllQuad.toPoly_liftK D
    have hgsq : Squarefree (toPoly (EllQuad.liftK (K := NF M) D)) := by
      rw [hgL]; exact ((PerfectField.separable_iff_squarefree).mpr hDsq).map.squarefree
    obtain ⟨rs, hrs, hall⟩ := rootsIn_complete M _ hgsq
    have hsound := rootsIn_sound M _ hrs
    have hD0 : (toPoly D).map (algebraMap ℚ (NF M)) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap ℚ (NF M)).injective).mpr hDsq.ne_zero
    have hdegM : ((toPoly D).map (algebraMap ℚ (NF M))).natDegree = (toPoly D).natDegree :=
      natDegree_map_eq_of_injective (algebraMap ℚ (NF M)).injective _
    -- `rs` contains at least `k` distinct roots
    have hk' : k ≤ rs.dedup.length := by
      obtain ⟨l, hl, hlen, hr⟩ := hk
      have hsub : l ⊆ rs.dedup := fun a ha ↦ List.mem_dedup.mpr
        (hall a (by rw [hgL, eval_map_algebraMap]; exact hr a ha))
      exact hlen.trans ((List.Subperm.length_le (List.subperm_of_subset hl hsub)))
    have hle : rs.dedup.length ≤ (toPoly D).natDegree := by
      rw [← hdegM]
      exact length_le_natDegree hD0 (List.nodup_dedup rs) (fun a ha ↦ by
        rw [← hgL]; exact hsound a (List.mem_dedup.mp ha))
    have hdegC : Kron.degC D = (toPoly D).natDegree := Kron.degC_eq D hDsq.ne_zero
    by_cases heq : rs.dedup.length = (toPoly D).natDegree
    · refine ⟨M, hM, ?_, ?_⟩
      · simp only [splitLoop]
        rw [hrs]
        simp only
        rw [if_pos (by rw [hdegC]; exact heq)]
      · exact ⟨rs.dedup, List.nodup_dedup rs, heq.ge, fun a ha ↦ by
          have := hsound a (List.mem_dedup.mp ha)
          rwa [hgL, eval_map_algebraMap] at this⟩
    · have hlt : rs.dedup.length < (toPoly D).natDegree := lt_of_le_of_ne hle heq
      obtain ⟨M', hM', hgrow, hroots, -⟩ := growStep_spec M D hDsq rs hrs hlt
      obtain ⟨M'', hM'', hloop, hfin⟩ := splitLoop_spec D hDsq n M' hM' _ hroots (by omega)
      refine ⟨M'', hM'', ?_, hfin⟩
      simp only [splitLoop]
      rw [hrs]
      simp only
      rw [if_neg (by rw [hdegC]; exact heq), hgrow]
      exact hloop


/-- `p(α) = α³ + aα² + bα + c`. -/
def pVal {K : Type*} [Field K] (a b c : ℤ) (α : K) : K := α ^ 3 + (a : K) * α ^ 2 + (b : K) * α + (c : K)

lemma map_pVal {K L : Type*} [Field K] [Field L] (φ : K →+* L) (a b c : ℤ) (α : K) :
    φ (pVal a b c α) = pVal a b c (φ α) := by
  simp [pVal, map_add, map_mul, map_pow, map_intCast]

/-- `D` has `k` distinct roots `α` in `ℚ[x]/(M)` at which `p(α)` is a square. -/
def SqRoots (M : CPoly ℚ) (hM : Kron.irredQ M = true) (a b c : ℤ) (D : CPoly ℚ) (k : ℕ) : Prop :=
  letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  ∃ l : List (NF M), l.Nodup ∧ k ≤ l.length ∧
    ∀ α ∈ l, aeval α (toPoly D) = 0 ∧ ∃ β : NF M, β * β = pVal a b c α

/-- **The square-root loop**: adjoin `√p(α)` until `p` is a square at every root of `D`. -/
noncomputable def sqLoop (a b c : ℤ) (D : CPoly ℚ) : ℕ → (M : CPoly ℚ) → Kron.irredQ M = true →
    Option (Σ' M : CPoly ℚ, Kron.irredQ M = true)
  | 0, _, _ => none
  | n + 1, M, hM =>
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    match rootsIn M (EllQuad.liftK (K := NF M) D) with
    | none => none
    | some rs =>
      match rs.dedup.find? (fun α ↦ (EllQuad.sqrtNF M (pVal a b c α)).isNone) with
      | none => some ⟨M, hM⟩
      | some α0 =>
        match extStep M (EllQuad.sqPoly M (pVal a b c α0)) with
        | some ⟨M', hM'⟩ => sqLoop a b c D n M' hM'
        | none => none

set_option maxHeartbeats 3200000 in
/-- **The loop ends with a field in which `p` is a non-zero square at every root of `D`.** -/
theorem sqLoop_spec (a b c : ℤ) (D : CPoly ℚ) (hDsq : Squarefree (toPoly D))
    (hcop : IsCoprime (toPoly D) (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ))) :
    ∀ (n : ℕ) (M : CPoly ℚ) (hM : Kron.irredQ M = true) (k : ℕ),
      HasRoots M hM D (toPoly D).natDegree → SqRoots M hM a b c D k →
      (toPoly D).natDegree < n + k →
      ∃ M' hM', sqLoop a b c D n M hM = some ⟨M', hM'⟩ ∧ HasRoots M' hM' D (toPoly D).natDegree ∧
        (letI : Fact (Irreducible (toPoly M')) := ⟨Kron.irredQ_sound M' hM'⟩
        ∀ α : NF M', aeval α (toPoly D) = 0 → ∃ β : NF M', β ≠ 0 ∧ β * β = pVal a b c α)
  | 0, M, hM, k, _, hk, hn => by
    exfalso
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    obtain ⟨l, hl, hlen, hr⟩ := hk
    have := length_le_natDegree ((Polynomial.map_ne_zero_iff (algebraMap ℚ (NF M)).injective).mpr
      hDsq.ne_zero) hl (fun a ha ↦ by rw [eval_map_algebraMap]; exact (hr a ha).1)
    rw [natDegree_map_eq_of_injective (algebraMap ℚ (NF M)).injective] at this
    omega
  | n + 1, M, hM, k, hsplit, hk, hn => by
    classical
    letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
    -- `p` does not vanish at the roots of `D`
    have hpne : ∀ α : NF M, aeval α (toPoly D) = 0 → pVal a b c α ≠ 0 := by
      intro α hα hp
      have := aeval_ne_zero_of_isCoprime hcop α
      apply this.elim (fun h ↦ h hα)
      intro h; apply h
      simpa [pVal] using hp
    have hgL : toPoly (EllQuad.liftK (K := NF M) D) = (toPoly D).map (algebraMap ℚ (NF M)) :=
      EllQuad.toPoly_liftK D
    have hgsq : Squarefree (toPoly (EllQuad.liftK (K := NF M) D)) := by
      rw [hgL]; exact ((PerfectField.separable_iff_squarefree).mpr hDsq).map.squarefree
    obtain ⟨rs, hrs, hall⟩ := rootsIn_complete M _ hgsq
    have hsound := rootsIn_sound M _ hrs
    have hrootiff : ∀ α : NF M, aeval α (toPoly D) = 0 ↔ α ∈ rs.dedup := by
      intro α; rw [List.mem_dedup]
      constructor
      · intro h; exact hall α (by rw [hgL, eval_map_algebraMap]; exact h)
      · intro h; have := hsound α h; rwa [hgL, eval_map_algebraMap] at this
    cases hfind : rs.dedup.find? (fun α ↦ (EllQuad.sqrtNF M (pVal a b c α)).isNone) with
    | none =>
      refine ⟨M, hM, ?_, hsplit, ?_⟩
      · simp only [sqLoop]; rw [hrs]; simp only; rw [hfind]
      · intro α hα
        have hmem := (hrootiff α).mp hα
        have := List.find?_eq_none.mp hfind α hmem
        simp only [Option.isNone_iff_eq_none, Bool.not_eq_true, decide_eq_false_iff_not] at this
        obtain ⟨β, hβ⟩ := Option.ne_none_iff_exists'.mp (by simpa using this)
        refine ⟨β, fun h0 ↦ hpne α hα ?_, EllQuad.sqrtNF_spec M hβ⟩
        rw [← EllQuad.sqrtNF_spec M hβ, h0, zero_mul]
    | some α0 =>
      have hα0mem : α0 ∈ rs.dedup := List.mem_of_find?_eq_some hfind
      have hα0none : EllQuad.sqrtNF M (pVal a b c α0) = none := by
        have := List.find?_some hfind; simpa using this
      have hα0root : aeval α0 (toPoly D) = 0 := (hrootiff α0).mpr hα0mem
      have hw0 : pVal a b c α0 ≠ 0 := hpne α0 hα0root
      have hnotsq : ∀ β : NF M, β * β ≠ pVal a b c α0 := fun β hβ ↦
        EllQuad.sqrtNF_ne_none M hβ hw0 hα0none
      have hsqp : Squarefree (toPoly (EllQuad.sqPoly M (pVal a b c α0))) :=
        EllQuad.sqPoly_squarefree M hw0
      have hsqe : toPoly (EllQuad.sqPoly M (pVal a b c α0)) = X ^ 2 - C (pVal a b c α0) := by
        simp [EllQuad.sqPoly, CPoly.toPoly]; ring
      obtain ⟨M', hM', hext, θ', hθ', α', hα'⟩ := extStep_spec M _ hsqp
        (by rw [hsqe, natDegree_sub_C, natDegree_X_pow]; norm_num)
      letI : Fact (Irreducible (toPoly M')) := ⟨Kron.irredQ_sound M' hM'⟩
      set e := emb M M' hθ'
      rw [hsqe, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eval_sub, eval_pow, eval_X,
        eval_C, sub_eq_zero, map_pVal] at hα'
      have heroot : ∀ α : NF M, aeval α (toPoly D) = 0 → aeval (e α) (toPoly D) = 0 := by
        intro α hα; rw [← aeval_ringHom_rat e α, hα, map_zero]
      -- the new field
      have hsplit' : HasRoots M' hM' D (toPoly D).natDegree := by
        obtain ⟨l, hl, hlen, hr⟩ := hsplit
        exact ⟨l.map e, hl.map e.injective, by simpa using hlen, fun α hα ↦ by
          obtain ⟨β, hβ, rfl⟩ := List.mem_map.mp hα; exact heroot β (hr β hβ)⟩
      have hk' : SqRoots M' hM' a b c D (k + 1) := by
        obtain ⟨l, hl, hlen, hr⟩ := hk
        have hα0l : α0 ∉ l := fun h ↦ by
          obtain ⟨β, hβ⟩ := (hr α0 h).2; exact hnotsq β hβ
        refine ⟨(α0 :: l).map e, (List.nodup_cons.mpr ⟨hα0l, hl⟩).map e.injective,
          by simp; omega, ?_⟩
        intro α hα
        obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hα
        rcases List.mem_cons.mp hγ with rfl | hγ
        · exact ⟨heroot _ hα0root, α', by rw [← sq]; exact hα'⟩
        · obtain ⟨hr1, β, hβ⟩ := hr γ hγ
          exact ⟨heroot _ hr1, e β, by rw [← map_mul, hβ, map_pVal]⟩
      obtain ⟨M'', hM'', hloop, hfin, hsq⟩ :=
        sqLoop_spec a b c D hDsq hcop n M' hM' (k + 1) hsplit' hk' (by omega)
      refine ⟨M'', hM'', ?_, hfin, hsq⟩
      simp only [sqLoop]
      rw [hrs]
      simp only
      rw [hfind]
      simp only
      rw [hext]
      exact hloop

end NFC

namespace NFC

lemma irredQ_X : Kron.irredQ ([0, 1] : CPoly ℚ) = true := by decide +kernel

/-- **The field for `D` and `p`**: `D` splits, and `p` is a non-zero square at its roots. -/
noncomputable def splitField (a b c : ℤ) (D : CPoly ℚ) : Option (Σ' M : CPoly ℚ, Kron.irredQ M = true) :=
  match splitLoop D (Kron.degC D + 1) [0, 1] irredQ_X with
  | some ⟨M, hM⟩ => sqLoop a b c D (Kron.degC D + 1) M hM
  | none => none

theorem splitField_spec (a b c : ℤ) (D : CPoly ℚ) (hDsq : Squarefree (toPoly D))
    (hcop : IsCoprime (toPoly D) (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ))) :
    ∃ M hM, splitField a b c D = some ⟨M, hM⟩ ∧ HasRoots M hM D (toPoly D).natDegree ∧
      (letI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      ∀ α : NF M, aeval α (toPoly D) = 0 → ∃ β : NF M, β ≠ 0 ∧ β * β = pVal a b c α) := by
  have hdeg : Kron.degC D = (toPoly D).natDegree := Kron.degC_eq D hDsq.ne_zero
  have h0 : HasRoots [0, 1] irredQ_X D 0 := ⟨[], List.nodup_nil, le_rfl, by simp⟩
  obtain ⟨M, hM, hloop, hsplit⟩ := splitLoop_spec D hDsq (Kron.degC D + 1) [0, 1] irredQ_X 0 h0
    (by rw [hdeg]; omega)
  have hsq0 : SqRoots M hM a b c D 0 := ⟨[], List.nodup_nil, le_rfl, by simp⟩
  obtain ⟨M', hM', hsq, hsplit', hfin⟩ := sqLoop_spec a b c D hDsq hcop (Kron.degC D + 1) M hM 0
    hsplit hsq0 (by rw [hdeg]; omega)
  refine ⟨M', hM', ?_, hsplit', hfin⟩
  unfold splitField
  rw [hloop]
  exact hsq

end NFC
