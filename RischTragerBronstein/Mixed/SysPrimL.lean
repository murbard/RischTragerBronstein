import RischTragerBronstein.Mixed.SysPrimSome
import RischTragerBronstein.Mixed.SysSpecialLSome
import RischTragerBronstein.Mixed.SysPrimK

/-!
# Coupled Risch systems at a primitive level with a limit matrix at infinity

`primSysBL … B` is `primSysB` for matrices that do not vanish at infinity: `Λ = lim BW / a`
(`lamCL`) may be non-zero. The coefficients are found one degree at a time by a solver `lowG Λ`
for `y′ + Λ y = ∑ cₗ wₗ` one level down (e.g. `triSys` for triangular `Λ`), and the special
degrees are bounded by `specBoundL` with the same solver. Sound (`primSysBL_sound`), and complete
for the solutions with denominator dividing `h q^B` when `lowG Λ` meets its specification
(`primSysBL_complete`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The limit matrix `Λ = lc(a)⁻¹ (BW)_δ` of the `W`-system. -/
def lamCL (m : ℕ) (η : LC m) (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m)) (q h : GPoly (LC m))
    (G0 : List (Fin n → GPoly (LC m))) (B : ℕ) : Fin n → Fin n → LC m :=
  let O := MO Fc ks m
  let W := wSys Fc ks m η n A0 q h G0 B
  fun i j ↦ O.mul (O.inv (leadG O W.a)) ((W.BW i j).getD (degG O W.a) O.zero)

/-- **The system solver at a primitive level with denominator `h q^B` and a limit matrix.** -/
def primSysBL (m : ℕ) (η : LC m) (n : ℕ)
    (lowG : (Fin n → Fin n → LC m) → List (Fin n → LC m) → List (List ℚ × (Fin n → LC m)))
    (A0 : Fin n → Fin n → GPoly (LC m)) (q h : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m)))
    (B : ℕ) :
    Option (GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))) :=
  let O := MO Fc ks m
  let cst := mcst Fc ks m
  if !(isMonicC O q && isMonicC O h) then none else
  let W := wSys Fc ks m η n A0 q h G0 B
  let δ := degG O W.a
  let la := O.inv (leadG O W.a)
  let PA : Fin n → Fin n → LC m := fun i j ↦ if i = j then la else O.zero
  let Λc := matFn (matData (lamCL Fc ks m η n A0 q h G0 B)) O.zero
  let β : Fin n → Fin n → LC m := matFn (matData fun i j ↦
    O.mul la (O.add ((W.BW i j).getD (δ - 1) O.zero)
      (O.neg (O.mul (W.a.getD (δ - 1) O.zero) (Λc i j))))) O.zero
  let okB := (List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
    decide ((GPoly.trim O (W.BW i j)).length ≤ δ + 1)
  if !okB then none else
  match specBoundL O cst (mrel Fc ks m) (lowG Λc) η β with
  | none => none
  | some Bs =>
    let Ncl := (W.Cl.flatMap fun v ↦ (List.finRange n).map fun i ↦ (v i).length).foldr max 0
    let N' := max Bs (Ncl - (δ - 1))
    some (W.Den, polySysC O η O.zero (fun i j ↦ if i = j then W.a else []) W.BW cst W.Cl δ false
      PA PA (fun _ ws ↦ lowG Λc ws) (mrel Fc ks m) (N' + 1))

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable (m : ℕ) (h : T.Tr m) (η : LC m) (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m))
  (q hh : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m))) (B : ℕ)

/-- **Soundness** (any solver one level down). -/
theorem primSysBL_sound
    (lowG : (Fin n → Fin n → LC m) → List (Fin n → LC m) → List (List ℚ × (Fin n → LC m)))
    (Den : GPoly (LC m)) (out : List (List ℚ × (Fin n → GPoly (LC m))))
    (hres : primSysBL Fc ks m η n lowG A0 q hh G0 B = some (Den, out)) :
    ∀ r ∈ out, SysSol ((T.MP m h).sem η) 0 (GPoly.toPoly (T.MP m h) q)
      (GPoly.toPoly (T.MP m h) hh) (semMat (T.MP m h) A0)
      (fun i ↦ ∑ l ∈ Finset.range G0.length, C ((r.1.getD l 0 : ℚ) : T.F m) *
        GPoly.toPoly (T.MP m h) ((G0.getD l fun _ ↦ []) i))
      (semV (T.MP m h) r.2) (GPoly.toPoly (T.MP m h) Den) := by
  unfold primSysBL at hres
  simp only [matFn_matData] at hres
  split_ifs at hres with hmon hok
  split at hres
  · exact absurd hres (by simp)
  rename_i Bs hBs
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hres)
  intro r hr
  have hs := polySysC_sound (algebraMap Cc (T.F m)) (T.MP m h) η (MO Fc ks m).zero _ _
    (mcst Fc ks m) (T.sem_mcst m h) _ _ false _ _ _ (mrel Fc ks m) (T.mrel_relSpec m h)
    (T.algebraMap_ratCast) _ r hr
  intro i
  have hi := congrFun hs i
  rw [resQV, Pi.sub_apply, Pi.zero_apply, sub_eq_zero, (T.MP m h).sem_zero,
    T.wSys_LopV m h η n A0 q hh G0 B, SqV, List.length_map] at hi
  simp only [T.wSys_Cl m h η n A0 q hh G0 B] at hi
  apply mul_left_cancel₀ (X_ne_zero : (X : (T.F m)[X]) ≠ 0)
  rw [hi, show (wSys Fc ks m η n A0 q hh G0 B).Cl.length = G0.length by simp [WSys.Cl, wSys],
    Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  ring

set_option maxHeartbeats 800000 in
/-- **Completeness** for solutions with denominator dividing `h q^B`, given the specification of
the solver one level down. -/
theorem primSysBL_complete
    (lowG : (Fin n → Fin n → LC m) → List (Fin n → LC m) → List (List ℚ × (Fin n → LC m)))
    (hlow : ∀ ws, SysSpecAt (algebraMap Cc (T.F m))
      (fun i j ↦ (T.MP m h).sem (lamCL Fc ks m η n A0 q hh G0 B i j)) (ws.map (semVa (T.MP m h)))
      (semR (T.MP m h) (lowG (lamCL Fc ks m η n A0 q hh G0 B) ws)))
    (Den : GPoly (LC m)) (out : List (List ℚ × (Fin n → GPoly (LC m))))
    (hres : primSysBL Fc ks m η n lowG A0 q hh G0 B = some (Den, out))
    (c : List Cc) (hc : ∀ l, G0.length ≤ l → c.getD l 0 = 0) (Z : Fin n → (T.F m)[X])
    (d : (T.F m)[X]) (hd : d ≠ 0)
    (hsol : SysSol ((T.MP m h).sem η) 0 (GPoly.toPoly (T.MP m h) q)
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
  unfold primSysBL at hres
  simp only [matFn_matData] at hres
  split_ifs at hres with hmon hok
  split at hres
  · exact absurd hres (by simp)
  rename_i Bs hBs
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hres)
  have hall : ((List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
      decide ((GPoly.trim (MO Fc ks m) ((wSys Fc ks m η n A0 q hh G0 B).BW i j)).length ≤
        degG (MO Fc ks m) (wSys Fc ks m η n A0 q hh G0 B).a + 1)) = true := by
    revert hok; cases ((List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
      decide ((GPoly.trim (MO Fc ks m) ((wSys Fc ks m η n A0 q hh G0 B).BW i j)).length ≤
        degG (MO Fc ks m) (wSys Fc ks m η n A0 q hh G0 B).a + 1)) <;> simp
  have hWa := T.wSys_a m h η n A0 q hh G0 B
  have hWCl := T.wSys_Cl m h η n A0 q hh G0 B
  have hWLop := T.wSys_LopV m h η n A0 q hh G0 B
  have hWDen := T.wSys_Den m h η n A0 q hh G0 B
  set O := MO Fc ks m with hO
  set M := T.MP m h with hM
  set W := wSys Fc ks m η n A0 q hh G0 B with hW
  set ι := algebraMap Cc (T.F m) with hι
  set w := M.sem η with hw
  have hmon' : (isMonicC O q && isMonicC O hh) = true := by
    revert hmon; cases (isMonicC O q && isMonicC O hh) <;> simp
  rw [Bool.and_eq_true] at hmon'
  have hqM := isMonicC_spec M q hmon'.1
  have hhM := isMonicC_spec M hh hmon'.2
  set qs := GPoly.toPoly M q with hqs
  set hs := GPoly.toPoly M hh with hhs
  set Ds := GPoly.toPoly M W.Den with hDs
  have hDs' : Ds = hs * qs ^ B := hWDen
  -- the denominator
  choose Wv hWv using fun i ↦ hdvd i
  have hDZ : ∀ i, Ds * Z i = d * Wv i := fun i ↦ by rw [hDs', ← hWv i]
  have hsolW : SysSol w 0 qs hs (semMat M A0) (fun i ↦ ∑ l ∈ Finset.range G0.length,
      C (ι (c.getD l 0)) * GPoly.toPoly M ((G0.getD l fun _ ↦ []) i)) Wv Ds := by
    have h1 := sysSol_scale w 0 qs hs (semMat M A0) _ Z d Ds hsol
    have e1 : (fun i ↦ Ds * Z i) = fun i ↦ d * Wv i := funext hDZ
    rw [e1, mul_comm Ds d] at h1
    exact sysSol_cancel w 0 qs hs (semMat M A0) _ Wv Ds d hd h1
  -- the `W`-system
  set AW : Fin n → Fin n → GPoly (LC m) := fun i j ↦ if i = j then W.a else [] with hAW
  set G : Fin n → (T.F m)[X] := fun i ↦ ∑ l ∈ Finset.range (W.Cl.map (semV M)).length,
    C (ι (c.getD l 0)) * (W.Cl.map (semV M)).getD l 0 i with hG
  have hClen : W.Cl.length = G0.length := by simp [hW, WSys.Cl, wSys]
  have hLop : LopV w 0 (semPM M AW) (semPM M W.BW) Wv = G := by
    funext i
    rw [hWLop Wv i, hsolW i, hG, List.length_map, hClen, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [hWCl]
    ring
  -- the leading coefficient
  set δ := degG O W.a with hδ
  have haM : (GPoly.toPoly M W.a).Monic := by
    rw [hWa]
    exact monic_X.mul (hqM.mul (hhM.mul (by rw [hDs']; exact hhM.mul (hqM.pow B))))
  have hδa : (GPoly.toPoly M W.a).natDegree = δ := (degG_eq M W.a).symm
  have hδ1 : 1 ≤ δ := by
    rw [← hδa, hWa,
      monic_X.natDegree_mul (hqM.mul (hhM.mul (by rw [hDs']; exact hhM.mul (hqM.pow B)))),
      natDegree_X]
    omega
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
  have hPAs' : ∀ i j, M.sem (PA i j) = if i = j then (1 : T.F m) else 0 := fun i j ↦
    congrFun (congrFun hPAs i) j
  have hAδ' : ∀ i j, (semPM M AW i j).coeff δ = if i = j then (1 : T.F m) else 0 := fun i j ↦
    congrFun (congrFun hAδ i) j
  -- the degrees of `B_W`
  have hBnat : ∀ i j, (semPM M W.BW i j).natDegree ≤ δ := by
    intro i j
    have hij := List.all_eq_true.mp (List.all_eq_true.mp hall i (List.mem_finRange _)) j
      (List.mem_finRange _)
    rw [decide_eq_true_eq] at hij
    by_cases htr0 : GPoly.trim O (W.BW i j) = []
    · rw [semPM, (GPoly.trim_eq_nil_iff M _).mp htr0, natDegree_zero]; exact Nat.zero_le _
    · have e : (GPoly.trim O (W.BW i j)).length = (GPoly.trim (MO Fc ks m) (W.BW i j)).length := rfl
      rw [semPM, (GPoly.natDegree_toPoly_of_trim_ne_nil M htr0).1]; omega
  -- the limit matrix
  set Λc := lamCL Fc ks m η n A0 q hh G0 B with hΛcdef
  have hΛ : ∀ i j, M.sem (Λc i j) = (semPM M W.BW i j).coeff δ := fun i j ↦ by
    simp only [hΛcdef, lamCL, M.sem_mul, semPM, coeff_toPoly_sem]
    change M.sem (O.inv (leadG O W.a)) * M.sem ((W.BW i j).getD δ O.zero) = _
    rw [hla, one_mul]
  have hΛm : lamML (semPM M W.BW) (fun i j ↦ M.sem (PA i j)) (δ - 1) =
      Matrix.of fun i j ↦ M.sem (Λc i j) := by
    ext i j
    simp only [lamML, Matrix.mul_apply, Matrix.of_apply, hPAs', Nat.sub_add_cancel hδ1, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, hΛ]
  -- the special degrees
  set β : Fin n → Fin n → LC m := fun i j ↦
    O.mul (O.inv (leadG O W.a)) (O.add ((W.BW i j).getD (δ - 1) O.zero)
      (O.neg (O.mul (W.a.getD (δ - 1) O.zero) (Λc i j)))) with hβdef
  have hAd1 : ∀ i j, (semPM M AW i j).coeff (δ - 1) =
      if i = j then M.sem (W.a.getD (δ - 1) O.zero) else 0 := fun i j ↦ by
    simp only [semPM, hAW]; split_ifs
    · rw [coeff_toPoly_sem]
    · simp
  have hβm : betaML (semPM M AW) (semPM M W.BW) (fun i j ↦ M.sem (PA i j)) (δ - 1) =
      Matrix.of fun i j ↦ M.sem (β i j) := by
    unfold betaML
    rw [hΛm]
    ext i j
    have hBc : (semPM M W.BW i j).coeff (δ - 1) = M.sem ((W.BW i j).getD (δ - 1) O.zero) :=
      coeff_toPoly_sem M _ _
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.of_apply, hPAs', hAd1, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [hBc]
    congr 1
    have e : M.sem (β i j) = M.sem (O.mul (O.inv (leadG O W.a)) (O.add ((W.BW i j).getD (δ - 1) O.zero)
        (O.neg (O.mul (W.a.getD (δ - 1) O.zero) (Λc i j))))) := by
      rw [hβdef]
    rw [e, M.sem_mul, hla, one_mul, M.sem_add, M.sem_neg, M.sem_mul]
    ring
  have hSp : ∀ D, 1 ≤ D → SpecialDegL w (lamML (semPM M W.BW) (fun i j ↦ M.sem (PA i j)) (δ - 1))
      (betaML (semPM M AW) (semPM M W.BW) (fun i j ↦ M.sem (PA i j)) (δ - 1)) D → D ≤ Bs :=
    fun D _ hD ↦ specBoundL_spec ι M (mcst Fc ks m) (T.sem_mcst m h) (mrel Fc ks m)
      (T.mrel_relSpec m h) _ (lowG Λc) hlow T.algebraMap_ratCast η β Bs hBs D
      (by rw [hΛm, hβm] at hD; exact hD)
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
  have hdegW := fun j ↦ sys_deg_primL w (semPM M AW) (semPM M W.BW) (δ - 1)
    (fun i j ↦ by rw [Nat.sub_add_cancel hδ1]; exact hA1 i j)
    (fun i j ↦ by rw [Nat.sub_add_cancel hδ1]; exact hBnat i j) (fun i j ↦ M.sem (PA i j))
    (fun i l ↦ by
      rw [Nat.sub_add_cancel hδ1]
      simp only [hPAs', hAδ', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true])
    Bs Ncl hSp Wv G hGz hLop j
  -- the polynomial system
  have hmv1 : ∀ v : Fin n → T.F m, mv (fun i j ↦ if i = j then (1 : T.F m) else 0) v = v := fun v ↦ by
    funext i; simp [mv]
  have hsolres : resCV (M.sem η) (M.sem O.zero) (semPM M AW) (semPM M W.BW) (W.Cl.map (semV M)) ι c
      Wv = 0 := by
    funext i
    rw [resCV, M.sem_zero, hLop]
    simp [hG]
  obtain ⟨γ, hγc, hγW⟩ := polySysC_complete ι M η O.zero AW W.BW (mcst Fc ks m) (T.sem_mcst m h) W.Cl
    δ T.deriv_algebraMap_Cc T.algebraMap_ratCast hA1 hBnat
    false PA PA (fun _ ws ↦ lowG Λc ws) (fun h ↦ absurd h (by simp))
    (fun _ ↦ ⟨fun v ↦ by rw [hAδ, hPAs, hmv1, hmv1], fun v ↦ by rw [hAδ, hPAs, hmv1, hmv1],
      fun k ↦ ⟨fun i j ↦ M.sem (Λc i j), fun z i ↦ by
        have hz0 : M.sem O.zero = 0 := M.sem_zero
        simp only [hAδ', hz0, mul_zero, zero_mul, add_zero, ite_mul, one_mul, mv, hΛ,
          Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_add],
        fun wsC ↦ hlow wsC⟩⟩)
    (mrel Fc ks m) (T.mrel_relSpec m h) (max Bs (Ncl - (δ - 1)))
    (fun l hl i ↦ by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro d' hd'
      exact hClc l hl i d' (by
        have : max Bs (Ncl - (δ - 1)) + δ < d' := by exact_mod_cast hd'
        omega))
    c (fun l hl ↦ hc l (by omega)) Wv hdegW hsolres
  refine ⟨γ, hγc, fun i ↦ ?_⟩
  rw [hDZ i, hγW i]


/-- **`primSysBL` answers** for monic `q`, `h`, a matrix bounded at infinity, a solver one level
down meeting its specification, and a non-degenerate limit system (no non-zero homogeneous
solution `c` has `η c` in the image). -/
theorem primSysBL_isSome
    (lowG : (Fin n → Fin n → LC m) → List (Fin n → LC m) → List (List ℚ × (Fin n → LC m)))
    (hlow : ∀ ws, SysSpecAt (algebraMap Cc (T.F m))
      (fun i j ↦ (T.MP m h).sem (lamCL Fc ks m η n A0 q hh G0 B i j)) (ws.map (semVa (T.MP m h)))
      (semR (T.MP m h) (lowG (lamCL Fc ks m η n A0 q hh G0 B) ws)))
    (hmon : (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hh) = true)
    (hA : ∀ i j, (GPoly.toPoly (T.MP m h) (A0 i j)).degree ≤ (GPoly.toPoly (T.MP m h) q).degree)
    (hnd : ∀ c : Fin n → T.F m, c ≠ 0 →
      (∀ i, (c i)′ + mv (fun i j ↦ (T.MP m h).sem (lamCL Fc ks m η n A0 q hh G0 B i j)) c i = 0) →
      ¬ ∃ y : Fin n → T.F m, ∀ i, (y i)′ +
        mv (fun i j ↦ (T.MP m h).sem (lamCL Fc ks m η n A0 q hh G0 B i j)) y i =
          (T.MP m h).sem η * c i) :
    (primSysBL Fc ks m η n lowG A0 q hh G0 B).isSome := by
  set O := MO Fc ks m with hO
  set M := T.MP m h with hM
  rw [Bool.and_eq_true] at hmon
  have hqM := isMonicC_spec M q hmon.1
  have hhM := isMonicC_spec M hh hmon.2
  set W := wSys Fc ks m η n A0 q hh G0 B with hW
  have hDen := T.wSys_Den m h η n A0 q hh G0 B
  have hDmon : (GPoly.toPoly M W.Den).Monic := by rw [hDen]; exact hhM.mul (hqM.pow B)
  have hokB : ((List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
      decide ((GPoly.trim O (W.BW i j)).length ≤ degG O W.a + 1)) = true := by
    simp only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]
    intro i j
    have hBW := T.wSys_BW m h η n A0 q hh G0 B i j
    simp only [semPM] at hBW
    rw [degG_eq M, T.wSys_a m h η n A0 q hh G0 B]
    set qs := GPoly.toPoly M q
    set hs := GPoly.toPoly M hh
    set Ds := GPoly.toPoly M W.Den
    have hqhD : (qs * (hs * Ds)).Monic := hqM.mul (hhM.mul hDmon)
    have hhD0 : (hs * Ds).degree ≠ ⊥ := by
      rw [Ne, degree_eq_bot]; exact (hhM.mul hDmon).ne_zero
    have hin : (hs * Ds * semMat M A0 i j - if i = j then qs * (hs * DzL (M.sem η) 0 Ds) else 0).degree
        ≤ (qs * (hs * Ds)).degree := by
      refine (degree_sub_le _ _).trans (max_le ?_ ?_)
      · rw [show qs * (hs * Ds) = hs * Ds * qs by ring, degree_mul, degree_mul (p := hs * Ds)]
        exact add_le_add_right (hA i j) _
      · refine le_of_lt ?_
        split_ifs
        · rw [degree_mul, degree_mul, degree_mul, degree_mul]
          have hq0 : qs.degree ≠ ⊥ := by rw [Ne, degree_eq_bot]; exact hqM.ne_zero
          have hh0 : hs.degree ≠ ⊥ := by rw [Ne, degree_eq_bot]; exact hhM.ne_zero
          exact WithBot.add_lt_add_left hq0 (WithBot.add_lt_add_left hh0
            (degree_DzL_lt (M.sem η) Ds hDmon))
        · rw [degree_zero]
          exact bot_lt_iff_ne_bot.mpr (by rw [Ne, degree_eq_bot]; exact hqhD.ne_zero)
    set inner := hs * Ds * semMat M A0 i j - if i = j then qs * (hs * DzL (M.sem η) 0 Ds) else 0
    by_cases hz : GPoly.toPoly M (W.BW i j) = 0
    · rw [(GPoly.trim_eq_nil_iff M _).mpr hz]
      exact Nat.zero_le _
    · have hne : GPoly.trim O (W.BW i j) ≠ [] := fun h0 ↦ hz ((GPoly.trim_eq_nil_iff M _).mp h0)
      rw [GPoly.length_trim M hne, hBW]
      have hi0 : inner ≠ 0 := fun h0 ↦ hz (by rw [hBW, h0, mul_zero])
      rw [natDegree_mul X_ne_zero hi0, natDegree_mul X_ne_zero hqhD.ne_zero, natDegree_X]
      have := natDegree_le_natDegree hin
      omega
  unfold primSysBL
  simp only [matFn_matData]
  rw [if_neg (by simp only [hO] at hmon; simp [hmon.1, hmon.2])]
  rw [← hW, if_neg (by rw [hokB]; decide)]
  obtain ⟨Bs, hBs⟩ := Option.isSome_iff_exists.mp
    (specBoundL_isSome (algebraMap Cc (T.F m)) M (mcst Fc ks m) (T.sem_mcst m h) (mrel Fc ks m)
      (T.mrel_relSpec m h) _ _ hlow T.algebraMap_ratCast η _ hnd)
  rw [hBs]
  rfl

end MTower

end Curves.MT
