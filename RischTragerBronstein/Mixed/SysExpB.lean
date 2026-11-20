import RischTragerBronstein.Mixed.SysExpT

/-!
# Coupled Risch systems at an exponential level with a known denominator

`expSysB … B`: `expSysT` with the denominator `Den = h q^B` supplied (no indicial bound and no
analysis at `t = 0`, so `q(0) = 0` is allowed): sound (`expSysB_sound`), complete for the solutions
whose denominator divides `h q^B` (`expSysB_complete`), and answering when `q`, `h` are monic,
`deg A₀ ≤ deg q` and the limit of `A₀ / q` at infinity is `a′ Λ` with `Λ` rational upper triangular
(`expSysB_isSome`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The exponential-level solver with denominator `h q^B`** (triangular rational limit at infinity). -/
def expSysB (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m)) (n : ℕ)
    (A0 : Fin n → Fin n → GPoly (LC m)) (q h : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m)))
    (B : ℕ) :
    Option (GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))) :=
  let O := MO Fc ks m
  let cst := mcst Fc ks m
  let bc := O.deriv a
  if !(isMonicC O q && isMonicC O h) then none else
  let W := wSysE Fc ks m bc n A0 q h G0 B
  let δ := degG O W.a
  let dD := degG O W.Den
  let Ll := lamList Fc ks m bc n W.BW δ dD
  let Λ : Fin n → Fin n → ℚ := fun i j ↦ (Ll.getD i []).getD j 0
  let okB := (List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
    decide ((GPoly.trim O (W.BW i j)).length ≤ δ + 1) &&
    O.isZero (O.add ((W.BW i j).getD δ O.zero)
      (O.neg (O.mul (cst (Λ i j - if i = j then (dD : ℚ) else 0)) bc))) &&
    (decide ((j : ℕ) < i) → Λ i j == 0)
  if !okB then none else
  let Ncl := (W.Cl.flatMap fun v ↦ (List.finRange n).map fun i ↦ (v i).length).foldr max 0
  let N' := max (triBd dD ((List.finRange n).map fun i ↦ Λ i i)) (Ncl - δ)
  let PA : Fin n → Fin n → LC m := fun i j ↦ if i = j then O.inv (leadG O W.a) else O.zero
  some (W.Den, polySysC O O.zero bc (fun i j ↦ if i = j then W.a else []) W.BW cst W.Cl δ false
    PA PA (fun k ws ↦ triSys O cst (fun i ↦ rdeD (O.mul (cst ((k : ℚ) - dD + Λ i i)) a))
      (fun i j ↦ O.mul (cst (Λ i j)) bc) ws) (mrel Fc ks m) (N' + 1))

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)
variable (m : ℕ) (h : T.Tr m) (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m))
  (q hh : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m))) (B : ℕ)

/-- **Soundness at an exponential level (triangular limit)**: every output `(e, W)` gives the solution `W / Den`
of `Y′ + (A₀/q) Y = ∑ eₗ G₀ₗ / h`, in the cleared form `SysSol` (`t′ = a′ t`). -/
theorem expSysB_sound (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (Den : GPoly (LC m)) (out : List (List ℚ × (Fin n → GPoly (LC m))))
    (hres : expSysB Fc ks m a rdeD n A0 q hh G0 B = some (Den, out)) :
    ∀ r ∈ out, SysSol 0 ((T.MP m h).sem ((MO Fc ks m).deriv a)) (GPoly.toPoly (T.MP m h) q)
      (GPoly.toPoly (T.MP m h) hh) (semMat (T.MP m h) A0)
      (fun i ↦ ∑ l ∈ Finset.range G0.length, C ((r.1.getD l 0 : ℚ) : T.F m) *
        GPoly.toPoly (T.MP m h) ((G0.getD l fun _ ↦ []) i))
      (semV (T.MP m h) r.2) (GPoly.toPoly (T.MP m h) Den) := by
  unfold expSysB at hres
  simp only at hres
  split_ifs at hres with h1 hok
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hres)
  intro r hr
  have hs := polySysC_sound (algebraMap Cc (T.F m)) (T.MP m h) (MO Fc ks m).zero
    ((MO Fc ks m).deriv a) _ _ (mcst Fc ks m) (T.sem_mcst m h) _ _ false _ _ _ (mrel Fc ks m)
    (T.mrel_relSpec m h) (T.algebraMap_ratCast) _ r hr
  intro i
  have hi := congrFun hs i
  rw [resQV, Pi.sub_apply, Pi.zero_apply, sub_eq_zero, (T.MP m h).sem_zero,
    T.wSysE_LopV m h ((MO Fc ks m).deriv a) n A0 q hh G0 B, SqV, List.length_map] at hi
  simp only [T.wSysE_Cl m h ((MO Fc ks m).deriv a) n A0 q hh G0 B] at hi
  apply mul_left_cancel₀ (X_ne_zero : (X : (T.F m)[X]) ≠ 0)
  rw [hi, show (wSysE Fc ks m ((MO Fc ks m).deriv a) n A0 q hh G0 B).Cl.length = G0.length by
    simp [WSys.Cl, wSysE], Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  ring

set_option maxHeartbeats 1600000 in
/-- **Completeness of `expSysB`** for the solutions with denominator dividing `h q^B` (`t = exp a`): every solution `Z / d` of
`Y′ + (A₀/q) Y = ∑ cₗ G₀ₗ / h` (constants `cₗ`) is `W / Den` with `(c, W)` a constant
combination of the outputs. `hom`: no nonzero `z` with `z′ + j a′ z = 0`, `j ≠ 0`; `hrdeD`: the
Risch solver one level down. -/
theorem expSysB_complete (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hrdeD : ∀ c : LC m, RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h) ((T.MP m h).sem c)′ (rdeD c))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (Den : GPoly (LC m)) (out : List (List ℚ × (Fin n → GPoly (LC m))))
    (hres : expSysB Fc ks m a rdeD n A0 q hh G0 B = some (Den, out))
    (c : List Cc) (hc : ∀ l, G0.length ≤ l → c.getD l 0 = 0) (Z : Fin n → (T.F m)[X])
    (d : (T.F m)[X]) (hd : d ≠ 0)
    (hsol : SysSol 0 ((T.MP m h).sem ((MO Fc ks m).deriv a)) (GPoly.toPoly (T.MP m h) q)
      (GPoly.toPoly (T.MP m h) hh) (semMat (T.MP m h) A0)
      (fun i ↦ ∑ l ∈ Finset.range G0.length, C (algebraMap Cc (T.F m) (c.getD l 0)) *
        GPoly.toPoly (T.MP m h) ((G0.getD l fun _ ↦ []) i)) Z d)
    (hdvd : ∀ i, d ∣ GPoly.toPoly (T.MP m h) hh * GPoly.toPoly (T.MP m h) q ^ B * Z i) :
    ∃ β : List Cc, (∀ l, c.getD l 0 = ∑ k ∈ Finset.range out.length,
        β.getD k 0 * algebraMap ℚ Cc ((out.getD k ([], fun _ ↦ [])).1.getD l 0)) ∧
      ∀ i, GPoly.toPoly (T.MP m h) Den * Z i = d * ∑ k ∈ Finset.range out.length,
        C (algebraMap Cc (T.F m) (β.getD k 0)) *
          semV (T.MP m h) (out.getD k ([], fun _ ↦ [])).2 i := by
  classical
  unfold expSysB at hres
  simp only at hres
  split_ifs at hres with hmon hok
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hres)
  set bcode := (MO Fc ks m).deriv a with hbcode
  simp only [Bool.not_eq_false, Bool.not_eq_true, Bool.not_eq_true', List.all_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, List.mem_finRange, forall_const, true_implies] at hok
  have hWa := T.wSysE_a m h bcode n A0 q hh G0 B
  have hWCl := T.wSysE_Cl m h bcode n A0 q hh G0 B
  have hWLop := T.wSysE_LopV m h bcode n A0 q hh G0 B
  have hWDen := T.wSysE_Den m h bcode n A0 q hh G0 B
  set O := MO Fc ks m with hO
  set M := T.MP m h with hM
  set W := wSysE Fc ks m bcode n A0 q hh G0 B with hW
  set ι := algebraMap Cc (T.F m) with hι
  set b := M.sem bcode with hb
  have hz0 : M.sem O.zero = 0 := M.sem_zero
  have hmon' : (isMonicC O q && isMonicC O hh) = true := by
    revert hmon; cases (isMonicC O q && isMonicC O hh) <;> simp
  rw [Bool.and_eq_true] at hmon'
  have hqM := isMonicC_spec M q hmon'.1
  have hhM := isMonicC_spec M hh hmon'.2
  set qs := GPoly.toPoly M q with hqs
  set hs := GPoly.toPoly M hh with hhs
  set Ds := GPoly.toPoly M W.Den with hDs
  have hDs' : Ds = hs * qs ^ B := hWDen
  have hbval : b = (T.val m a)′ := by
    rw [hb, hbcode, M.sem_deriv, T.sem_MP_F m h]
  -- the denominator
  choose Wv hWv using fun i ↦ hdvd i
  have hDZ : ∀ i, Ds * Z i = d * Wv i := fun i ↦ by rw [hDs', ← hWv i]
  have hsolW : SysSol 0 b qs hs (semMat M A0) (fun i ↦ ∑ l ∈ Finset.range G0.length,
      C (ι (c.getD l 0)) * GPoly.toPoly M ((G0.getD l fun _ ↦ []) i)) Wv Ds := by
    have h1 := sysSol_scale 0 b qs hs (semMat M A0) _ Z d Ds hsol
    have e1 : (fun i ↦ Ds * Z i) = fun i ↦ d * Wv i := funext hDZ
    rw [e1, mul_comm Ds d] at h1
    exact sysSol_cancel 0 b qs hs (semMat M A0) _ Wv Ds d hd h1
  -- the `W`-system
  set AW : Fin n → Fin n → GPoly (LC m) := fun i j ↦ if i = j then W.a else [] with hAW
  set G : Fin n → (T.F m)[X] := fun i ↦ ∑ l ∈ Finset.range (W.Cl.map (semV M)).length,
    C (ι (c.getD l 0)) * (W.Cl.map (semV M)).getD l 0 i with hG
  have hClen : W.Cl.length = G0.length := by simp [hW, WSys.Cl, wSysE]
  have hLop : LopV 0 b (semPM M AW) (semPM M W.BW) Wv = G := by
    funext i
    rw [hWLop Wv i, hsolW i, hG, List.length_map, hClen, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [hWCl]
    ring
  -- the leading coefficient
  set δ := degG O W.a with hδ
  set dD := degG O W.Den with hdD
  have haM : (GPoly.toPoly M W.a).Monic := by
    rw [hWa]
    exact monic_X.mul (hqM.mul (hhM.mul (by rw [hDs']; exact hhM.mul (hqM.pow B))))
  have hδa : (GPoly.toPoly M W.a).natDegree = δ := (degG_eq M W.a).symm
  have hlead : M.sem (leadG O W.a) = 1 := by
    rw [leadG, ← GPoly.leadingCoeff_toPoly M haM.ne_zero]; exact haM.leadingCoeff
  have hla : M.sem (O.inv (leadG O W.a)) = 1 := by rw [M.sem_inv, hlead, inv_one]
  set PA : Fin n → Fin n → LC m := fun i j ↦ if i = j then O.inv (leadG O W.a) else O.zero with hPA
  have hPAs : (fun i j ↦ M.sem (PA i j)) = fun i j ↦ if i = j then (1 : T.F m) else 0 := by
    funext i j; rw [hPA]; dsimp only; split_ifs
    · exact hla
    · exact M.sem_zero
  have hAδ : (fun i j ↦ (semPM M AW i j).coeff δ) = fun i j ↦ if i = j then (1 : T.F m) else 0 := by
    funext i j; simp only [semPM, hAW]; split_ifs
    · rw [← hδa]; exact haM.leadingCoeff
    · simp
  have hAδ' : ∀ i j, (semPM M AW i j).coeff δ = if i = j then (1 : T.F m) else 0 := fun i j ↦
    congrFun (congrFun hAδ i) j
  -- `B_W` from the check
  set Ll := lamList Fc ks m bcode n W.BW δ dD with hLl
  have hBchk := hok
  have hBnat : ∀ i j, (semPM M W.BW i j).natDegree ≤ δ := by
    intro i j
    by_cases htr0 : GPoly.trim O (W.BW i j) = []
    · rw [semPM, (GPoly.trim_eq_nil_iff M _).mp htr0, natDegree_zero]; exact Nat.zero_le _
    · have := (hBchk i j).1.1
      have e : (GPoly.trim O (W.BW i j)).length = (GPoly.trim (MO Fc ks m) (W.BW i j)).length := rfl
      rw [semPM, (GPoly.natDegree_toPoly_of_trim_ne_nil M htr0).1]; omega
  have hBδ : ∀ i j, (semPM M W.BW i j).coeff δ =
      b * ((((Ll.getD i []).getD j 0 : ℚ) : T.F m) - if i = j then (dD : T.F m) else 0) := by
    intro i j
    have h0 := (M.isZero_iff _).mp (hBchk i j).1.2
    rw [M.sem_add, M.sem_neg, M.sem_mul, T.sem_mcst m h] at h0
    rw [semPM, coeff_toPoly_sem, hb]
    split_ifs at h0 ⊢ <;> push_cast at h0 ⊢ <;> linear_combination h0
  have htri : ∀ i j : Fin n, j < i → (Ll.getD i []).getD j 0 = 0 := fun i j hji ↦ by
    have := (hBchk i j).2 hji
    simpa using this
  -- `G` vanishes from `Ncl` on
  set Ncl := (W.Cl.flatMap fun v ↦ (List.finRange n).map fun i ↦ (v i).length).foldr max 0 with hNcl
  have hClL : ∀ l < W.Cl.length, ∀ i, ((W.Cl.getD l fun _ ↦ []) i).length ≤ Ncl := fun l hl i ↦ by
    refine Tower.Sys.le_foldr_max _ _ (List.mem_flatMap.mpr ⟨W.Cl.getD l fun _ ↦ [], ?_, ?_⟩)
    · rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem _
    · exact List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩
  have hClc : ∀ l < W.Cl.length, ∀ i, ∀ d', Ncl ≤ d' →
      (semV M (W.Cl.getD l fun _ ↦ []) i).coeff d' = 0 := fun l hl i d' hd' ↦ by
    rw [semV, coeff_toPoly_sem, List.getD_eq_default _ _ ((hClL l hl i).trans hd'), M.sem_zero]
  have hGz : ∀ i d', Ncl ≤ d' → (G i).coeff d' = 0 := by
    intro i d' hd'
    rw [hG, finsetSum_coeff]
    refine Finset.sum_eq_zero fun l hl ↦ ?_
    rw [List.length_map] at hl
    rw [coeff_C_mul, getD_semCl, hClc l (Finset.mem_range.mp hl) i d' hd', mul_zero]
  have hA1 : ∀ i j, (semPM M AW i j).natDegree ≤ δ := fun i j ↦ by
    simp only [semPM, hAW]; split_ifs
    · rw [hδa]
    · simp
  have hdegW := fun j ↦ sys_deg_tri b (semPM M AW) (semPM M W.BW) δ hA1 hBnat hAδ' dD
    (fun i j : Fin n ↦ (Ll.getD i []).getD j 0) htri hBδ hom Ncl Wv G hGz hLop
    (triBd dD ((List.finRange n).map fun i : Fin n ↦ (Ll.getD i []).getD i 0))
    (fun i D hD ↦ triBd_spec dD _ D ((Ll.getD i []).getD i 0)
      (List.mem_map_of_mem (List.mem_finRange i)) hD) j
  -- the polynomial system
  have hmv1 : ∀ v : Fin n → T.F m, mv (fun i j ↦ if i = j then (1 : T.F m) else 0) v = v := fun v ↦ by
    funext i; simp [mv]
  have hsolres : resCV (M.sem O.zero) (M.sem bcode) (semPM M AW) (semPM M W.BW) (W.Cl.map (semV M)) ι
      c Wv = 0 := by
    funext i
    rw [resCV, hz0, ← hb, hLop]
    simp [hG]
  have hderiv : ∀ r : ℚ, (M.sem (O.mul (mcst Fc ks m r) a))′ = (r : T.F m) * b := fun r ↦ by
    rw [M.sem_mul, T.sem_mcst m h, Derivation.leibniz, T.deriv_ratCast, smul_zero, add_zero,
      smul_eq_mul, hb, hbcode, M.sem_deriv]
  have hsemF : ∀ i j : Fin n, M.sem (O.mul (mcst Fc ks m ((Ll.getD i []).getD j 0)) bcode) =
      (((Ll.getD i []).getD j 0 : ℚ) : T.F m) * b := fun i j ↦ by
    rw [M.sem_mul, T.sem_mcst m h, hb]
  obtain ⟨γ, hγc, hγW⟩ := polySysC_complete ι M O.zero bcode AW W.BW (mcst Fc ks m) (T.sem_mcst m h)
    W.Cl δ T.deriv_algebraMap_Cc T.algebraMap_ratCast hA1 hBnat false PA PA
    (fun k ws ↦ triSys O (mcst Fc ks m)
      (fun i : Fin n ↦ rdeD (O.mul (mcst Fc ks m ((k : ℚ) - dD + (Ll.getD i []).getD i 0)) a))
      (fun i j : Fin n ↦ O.mul (mcst Fc ks m ((Ll.getD i []).getD j 0)) bcode) ws)
    (fun h ↦ absurd h (by simp))
    (fun _ ↦ ⟨fun v ↦ by rw [hAδ, hPAs, hmv1, hmv1], fun v ↦ by rw [hAδ, hPAs, hmv1, hmv1],
      fun k ↦ ⟨triF M (fun i : Fin n ↦ (M.sem (O.mul (mcst Fc ks m ((k : ℚ) - dD + (Ll.getD i []).getD i 0))
          a))′) (fun i j : Fin n ↦ O.mul (mcst Fc ks m ((Ll.getD i []).getD j 0)) bcode),
        fun z i ↦ by
          simp only [hAδ', hBδ, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
            Finset.sum_ite_eq, Finset.mem_univ, if_true]
          rw [mv_triF, hderiv]
          have hsplit : ∑ x : Fin n, b * ((((Ll.getD i []).getD x 0 : ℚ) : T.F m) -
              if i = x then (dD : T.F m) else 0) * z x =
              b * ((((Ll.getD i []).getD i 0 : ℚ) : T.F m) - dD) * z i +
                offV M (fun i j : Fin n ↦ O.mul (mcst Fc ks m ((Ll.getD i []).getD j 0)) bcode) z i := by
            rw [offV, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_comm]
            congr 1
            · simp
            · rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
              simp only [lt_irrefl, if_false, add_zero]
              refine Finset.sum_congr rfl fun k' hk ↦ ?_
              have hki : k' ≠ i := Finset.ne_of_mem_erase hk
              rcases lt_or_gt_of_ne hki with hlt | hgt
              · rw [if_neg (not_lt.mpr hlt.le), if_neg (Ne.symm hki), htri i k' hlt]
                push_cast; ring
              · rw [if_pos hgt, if_neg (Ne.symm hki), hsemF]
                push_cast; ring
          rw [hsplit]
          push_cast
          ring,
        fun wsC ↦ triSys_spec _ M (mcst Fc ks m) (T.sem_mcst m h) _ _ wsC _ (fun i ↦ hrdeD _)
          T.algebraMap_ratCast⟩⟩)
    (mrel Fc ks m) (T.mrel_relSpec m h)
    (max (triBd dD ((List.finRange n).map fun i : Fin n ↦ (Ll.getD i []).getD i 0)) (Ncl - δ))
    (fun l hl i ↦ by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro d' hd'
      exact hClc l hl i d' (by
        have : max (triBd dD ((List.finRange n).map fun i : Fin n ↦ (Ll.getD i []).getD i 0)) (Ncl - δ) + δ <
          d' := by exact_mod_cast hd'
        omega))
    c (fun l hl ↦ hc l (by omega)) Wv hdegW hsolres
  refine ⟨γ, hγc, fun i ↦ ?_⟩
  rw [hDZ i, hγW i]

lemma lamList_getD (bc : LC m) (BW : Fin n → Fin n → GPoly (LC m)) (δ dD : ℕ) (i j : Fin n) :
    ((lamList Fc ks m bc n BW δ dD).getD i []).getD j 0 =
      ((ratValC Fc ks m ((MO Fc ks m).mul ((BW i j).getD δ (MO Fc ks m).zero)
        ((MO Fc ks m).inv bc))).getD 0) + (if i = j then (dD : ℚ) else 0) := by
  simp [lamList, List.getD_eq_getElem?_getD]

lemma coeff_mul_of_natDegree_le' {R : Type*} [CommRing R] {p q : R[X]} {a c : ℕ}
    (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ c) : (p * q).coeff (a + c) = p.coeff a * q.coeff c := by
  rw [coeff_mul, Finset.sum_eq_single (a, c)]
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    by_cases hi : a < i
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
    · have hj : c < j := by
        by_contra hj
        exact hne (Prod.ext (by simp; omega) (by simp; omega))
      rw [coeff_eq_zero_of_natDegree_lt (p := q) (by omega), mul_zero]
  · intro h; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (rfl : a + c = a + c)) h

/-- `D(P) = P^D + b t P′` keeps the degree of a monic `P`, with leading coefficient `b deg P`. -/
lemma DzL_exp_monic {K : Type*} [Field K] [Differential K] [CharZero K] (b : K) (P : K[X])
    (hP : P.Monic) : (DzL 0 b P).natDegree ≤ P.natDegree ∧
      (DzL 0 b P).coeff P.natDegree = b * P.natDegree := by
  rw [DzL_eq, map_zero, zero_add]
  have h1 : (mapCoeffs P).natDegree ≤ P.natDegree := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_mapCoeffs, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hk), map_zero]
  have h2 : (C b * X * derivative P).natDegree ≤ P.natDegree := by
    rcases Nat.eq_zero_or_pos P.natDegree with h0 | hpos
    · have hd : derivative P = 0 := by rw [eq_C_of_natDegree_eq_zero h0, derivative_C]
      rw [hd, mul_zero, natDegree_zero]; exact Nat.zero_le _
    · refine (natDegree_mul_le).trans ?_
      have := natDegree_derivative_lt (p := P) (by omega)
      have h3 : (C b * X).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by rw [natDegree_X])
      omega
  refine ⟨(natDegree_add_le _ _).trans (max_le h1 h2), ?_⟩
  rw [coeff_add, coeff_mapCoeffs, ← leadingCoeff, hP.leadingCoeff, Derivation.map_one_eq_zero,
    zero_add, mul_assoc, coeff_C_mul]
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hpos
  · rw [h0, coeff_X_mul_zero]; simp
  · rw [show P.natDegree = (P.natDegree - 1) + 1 by omega, coeff_X_mul, coeff_derivative,
      show P.natDegree - 1 + 1 = P.natDegree by omega, ← leadingCoeff, hP.leadingCoeff]
    have : (P.natDegree : K) = ((P.natDegree - 1 : ℕ) : K) + 1 := by norm_cast; omega
    rw [this]; push_cast; ring

set_option maxHeartbeats 1600000 in
/-- **`expSysB` answers** for monic `q`, `h`, `deg A₀ ≤ deg q` and a rational upper triangular
limit `A₀/q → a′ Λ` at infinity. -/
theorem expSysB_isSome (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hmon : (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hh) = true)
    (hA : ∀ i j, (GPoly.toPoly (T.MP m h) (A0 i j)).natDegree ≤
      (GPoly.toPoly (T.MP m h) q).natDegree)
    (lam : Fin n → Fin n → ℚ)
    (hlam : ∀ i j, (GPoly.toPoly (T.MP m h) (A0 i j)).coeff (GPoly.toPoly (T.MP m h) q).natDegree =
      (T.MP m h).sem ((MO Fc ks m).deriv a) * (lam i j : T.F m))
    (htri : ∀ i j : Fin n, j < i → lam i j = 0)
    (hb0 : (T.MP m h).sem ((MO Fc ks m).deriv a) ≠ 0) :
    (expSysB Fc ks m a rdeD n A0 q hh G0 B).isSome := by
  classical
  set O := MO Fc ks m with hO
  set M := T.MP m h with hM
  set bc := O.deriv a with hbc
  set b := M.sem bc with hb
  rw [Bool.and_eq_true] at hmon
  have hqM := isMonicC_spec M q hmon.1
  have hhM := isMonicC_spec M hh hmon.2
  set W := wSysE Fc ks m bc n A0 q hh G0 B with hW
  set qs := GPoly.toPoly M q with hqs
  set hs := GPoly.toPoly M hh with hhs
  set Ds := GPoly.toPoly M W.Den with hDs
  have hDen : Ds = hs * qs ^ B := T.wSysE_Den m h bc n A0 q hh G0 B
  have hDmon : Ds.Monic := by rw [hDen]; exact hhM.mul (hqM.pow B)
  have hWa := T.wSysE_a m h bc n A0 q hh G0 B
  have haM : (GPoly.toPoly M W.a).Monic := by
    rw [hWa]; exact monic_X.mul (hqM.mul (hhM.mul hDmon))
  set δ := degG O W.a with hδ
  set dD := degG O W.Den with hdD
  have hdDs : Ds.natDegree = dD := (degG_eq M W.Den).symm
  have hδv : δ = qs.natDegree + (hs.natDegree + dD) + 1 := by
    rw [hδ, degG_eq M, hWa, monic_X.natDegree_mul (hqM.mul (hhM.mul hDmon)),
      hqM.natDegree_mul (hhM.mul hDmon), hhM.natDegree_mul hDmon, hdDs, natDegree_X]
    ring
  -- the entries of `B_W`
  have hent : ∀ i j, (semPM M W.BW i j).natDegree ≤ δ ∧
      (semPM M W.BW i j).coeff δ = b * ((lam i j : T.F m) - if i = j then (dD : T.F m) else 0) := by
    intro i j
    have hBW := T.wSysE_BW m h bc n A0 q hh G0 B i j
    rw [hBW]
    obtain ⟨hD1, hD2⟩ := DzL_exp_monic b Ds hDmon
    set inner := hs * Ds * semMat M A0 i j -
      (if i = j then qs * (hs * DzL 0 b Ds) else 0) with hinner
    have hk : qs.natDegree + (hs.natDegree + dD) = (hs * Ds).natDegree + qs.natDegree := by
      rw [hhM.natDegree_mul hDmon, hdDs]; ring
    have hAij : (semMat M A0 i j).natDegree ≤ qs.natDegree := by
      simp only [semMat, Matrix.of_apply]; exact hA i j
    have hin : inner.natDegree ≤ qs.natDegree + (hs.natDegree + dD) := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · rw [hk]
        exact natDegree_mul_le.trans (by rw [hhM.natDegree_mul hDmon] at *; omega)
      · split_ifs
        · refine natDegree_mul_le.trans ?_
          have := natDegree_mul_le (p := hs) (q := DzL 0 b Ds)
          rw [hdDs] at hD1
          omega
        · simp
    refine ⟨?_, ?_⟩
    · refine natDegree_mul_le.trans ?_
      rw [natDegree_X]; omega
    · rw [hδv, coeff_X_mul, coeff_sub]
      have e1 : (hs * Ds * semMat M A0 i j).coeff (qs.natDegree + (hs.natDegree + dD)) =
          b * (lam i j : T.F m) := by
        rw [hk, coeff_mul_of_natDegree_le' le_rfl hAij, (hhM.mul hDmon).coeff_natDegree, one_mul]
        simp only [semMat, Matrix.of_apply]
        exact hlam i j
      rw [e1]
      split_ifs with hij
      · have e2 : (qs * (hs * DzL 0 b Ds)).coeff (qs.natDegree + (hs.natDegree + dD)) =
            b * dD := by
          rw [coeff_mul_of_natDegree_le' le_rfl (natDegree_mul_le.trans (by rw [hdDs] at hD1; omega)),
            hqM.coeff_natDegree, one_mul, coeff_mul_of_natDegree_le' le_rfl (by rw [hdDs] at hD1; exact hD1),
            hhM.coeff_natDegree, one_mul, ← hdDs, hD2]
        rw [e2]; ring
      · simp
  -- the check passes
  have hlamL : ∀ i j : Fin n,
      ((lamList Fc ks m bc n W.BW δ dD).getD i []).getD j 0 = lam i j := by
    intro i j
    rw [lamList_getD]
    have hr : ratValC Fc ks m (O.mul ((W.BW i j).getD δ O.zero) (O.inv bc)) =
        some (lam i j - if i = j then (dD : ℚ) else 0) := by
      refine T.ratVal_spec m h _ _ ?_
      rw [M.sem_mul, M.sem_inv, ← hb, ← coeff_toPoly_sem]
      change (semPM M W.BW i j).coeff δ * b⁻¹ = _
      rw [(hent i j).2]
      field_simp
      split_ifs <;> push_cast <;> ring
    rw [hr, Option.getD_some]
    ring
  have hokB : ((List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
      decide ((GPoly.trim O (W.BW i j)).length ≤ δ + 1) &&
      O.isZero (O.add ((W.BW i j).getD δ O.zero)
        (O.neg (O.mul (mcst Fc ks m (((lamList Fc ks m bc n W.BW δ dD).getD i []).getD j 0 -
          if i = j then (dD : ℚ) else 0)) bc))) &&
      (decide ((j : ℕ) < i) → ((lamList Fc ks m bc n W.BW δ dD).getD i []).getD j 0 == 0)) = true := by
    simp only [List.all_eq_true, List.mem_finRange, forall_const, Bool.and_eq_true,
      decide_eq_true_eq]
    intro i j
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · by_cases hz : GPoly.toPoly M (W.BW i j) = 0
      · rw [(GPoly.trim_eq_nil_iff M _).mpr hz]; exact Nat.zero_le _
      · have hne : GPoly.trim O (W.BW i j) ≠ [] := fun h0 ↦ hz ((GPoly.trim_eq_nil_iff M _).mp h0)
        rw [GPoly.length_trim M hne]
        have := (hent i j).1
        simp only [semPM] at this
        omega
    · refine (M.isZero_iff _).mpr ?_
      rw [M.sem_add, M.sem_neg, M.sem_mul, T.sem_mcst m h, hlamL, ← hb, ← coeff_toPoly_sem]
      change (semPM M W.BW i j).coeff δ + -(_ * b) = 0
      rw [(hent i j).2]
      split_ifs <;> push_cast <;> ring
    · intro hji
      rw [hlamL, htri i j (by exact_mod_cast hji)]
      rfl
  unfold expSysB
  simp only
  rw [if_neg (by simp only [hO] at hmon; simp [hmon.1, hmon.2])]
  rw [← hW, if_neg (by rw [hokB]; decide)]
  rfl

end MTower

end Curves.MT
