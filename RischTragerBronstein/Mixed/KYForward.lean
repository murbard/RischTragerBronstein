import RischTragerBronstein.Mixed.KYZeroSem

/-!
# Radicals with poles over an exponential: the forward direction

* `ky_dl_coords`: for a witness `W` over `Kₘ ⊗ N` read on the twist `ỹ = μ y` (`μ = z/s`), the
  coordinates of `W′/W` and the value of its column `zʲ Dⱼ/g` (`kyColM`): `Eⱼ = col/sʲ`.
-/

open Polynomial Differential IntermediateField CPoly Ramanujan

set_option linter.unusedSectionVars false

namespace Differential.SuperData

variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
  [Differential C] [Differential L] [DifferentialAlgebra C L] (S : SuperData C L)
  (ω : C[X]) (hx : S.x′ = aeval S.x ω)

/-- **A factor from `C(x)`** changes only the coordinate `y⁰` of `W′/W`. -/
lemma dl_mul_base (W : C⟮S.x⟯⟮S.y⟯) (hW0 : W ≠ 0) (v : C⟮S.x⟯) (hv : v ≠ 0)
    (E : Fin S.n → C⟮S.x⟯)
    (hE : S.dl ω hx W = ∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (E i) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ)) :
    ∃ E' : Fin S.n → C⟮S.x⟯, S.dl ω hx (W * algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ v) =
      ∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (E' i) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ) ∧
      ∀ i : Fin S.n, (i : ℕ) ≠ 0 → E' i = E i := by
  classical
  have hcl := S.derivClosedXW ω hx
  have hvL : (v : L) ≠ 0 := fun h ↦ hv (Subtype.ext h)
  have hwm : logDeriv (v : L) ∈ C⟮S.x⟯ := div_mem (hcl _ v.2) v.2
  have hV0 : algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ v ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯).injective).mpr hv
  set w : C⟮S.x⟯ := ⟨logDeriv (v : L), hwm⟩ with hw
  refine ⟨fun i ↦ E i + (if (i : ℕ) = 0 then w else 0), ?_, fun i hi ↦ by simp [hi]⟩
  rw [S.dl_mul _ _ _ _ hW0 hV0, hE]
  have hdlv : S.dl ω hx (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ v) = algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ w :=
    Subtype.ext (by rw [S.coe_dl]; rfl)
  rw [hdlv]
  simp only [map_add, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single (⟨0, S.hn⟩ : Fin S.n) (fun i _ hi ↦ by
      rw [if_neg (fun h ↦ hi (Fin.ext h)), map_zero, zero_mul]) (fun h ↦ absurd (Finset.mem_univ _) h)]
  simp

end Differential.SuperData

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable [Fact (Irreducible (toPoly (fKc Fc)))]

/-- A root of a rational polynomial is a constant. -/
lemma deriv_root_rat (x : L) (P : ℚ[X]) (hP : P ≠ 0) (hx : aeval x P = 0) : x′ = 0 := by
  have hint : IsIntegral ℚ x := ⟨_, monic_mul_leadingCoeff_inv hP, by
    rw [eval₂_mul, ← aeval_def, hx, zero_mul]⟩
  set μ := minpoly ℚ x
  have hsep : μ.Separable := (minpoly.irreducible hint).separable
  refine deriv_eq_zero_of_aeval_eq_zero (A := L) (μ.map (algebraMap ℚ L)) (fun i ↦ ?_) x ?_ ?_
  · rw [coeff_map, eq_ratCast]; exact Tower.NestP.deriv_ratCastK (K := L) _
  · rw [aeval_map_algebraMap]; exact minpoly.aeval ℚ x
  · rw [derivative_map, aeval_map_algebraMap]; exact hsep.aeval_derivative_ne_zero (minpoly.aeval ℚ x)

omit [Fact (Irreducible (toPoly (fKc Fc)))] in
lemma nfm_len' [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] (htrim : CPoly.trim M = M) (hlen : 1 < M.length)
    (a : NFM Fc m M) : a.1.length ≤ M.length - 1 := by
  by_cases h0 : a.1 = []
  · rw [h0]; simp
  have htr : CPoly.trim a.1 = a.1 := by rw [← a.2, NFK.norm, CPoly.trim_trim]
  have hl := CPoly.length_trim (p := a.1) (by rw [htr]; exact h0)
  rw [htr] at hl
  have hdv := NFK.degree_val (liftQ Fc m M) a
  have hne : toPoly a.1 ≠ 0 := fun h1 ↦ h0 (by
    have := (CPoly.trim_eq_nil_iff a.1).mpr h1; rwa [htr] at this)
  have hMne : M ≠ [] := fun h ↦ by rw [h] at hlen; simp at hlen
  have hMdeg : (toPoly M).natDegree = M.length - 1 := by
    have := CPoly.length_trim (p := M) (by rw [htrim]; exact hMne)
    rw [htrim] at this; omega
  have hLdeg : (toPoly (liftQ Fc m M)).natDegree = M.length - 1 := by
    rw [toPoly_liftQ, natDegree_map_eq_of_injective (algebraMap ℚ _).injective, hMdeg]
  rw [degree_eq_natDegree hne, degree_eq_natDegree (Irreducible.ne_zero Fact.out), hLdeg] at hdv
  have : (toPoly a.1).natDegree < M.length - 1 := by exact_mod_cast hdv
  omega

section Coords

variable (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
  (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
  (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
  (n : ℕ) (hn : 0 < n) (θ : L) (hθ : θ ^ n = T.evP m A) (hmn : m < T.n) {g : LC m}
  (hk : ks m = .exp g)
  (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
  [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (htrim : CPoly.trim M = M)
  (hlen : 1 < M.length) (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0)

lemma liftNFM_mem (x : NFM Fc (m + 1) M) (hroot : (toPoly (liftQ Fc (m + 1) M)).eval₂
    ((algebraMap L L).comp ((algebraMap (T.F (m + 1)) L).comp (T.psiF (m + 1) hTr))) (ρ : L) = 0) :
    liftNFM (m + 1) M ((algebraMap L L).comp ((algebraMap (T.F (m + 1)) L).comp
      (T.psiF (m + 1) hTr))) (ρ : L) hroot x ∈ T.F (m + 1) := by
  rw [liftNFM_val, eval₂_list_sum]
  refine sum_mem fun f _ ↦ mul_mem ?_ (pow_mem (T.le_succ m ρ.2) _)
  exact (T.psiF (m + 1) hTr (x.1.getD f 0)).2

/-- The polynomial read on `x = t`: `aeval t` of the image of a coefficient list. -/
lemma aeval_psiNFM_list (m : ℕ) (hm : T.Tr m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0) (d : ℕ)
    (hd : ∀ a : NFM Fc m M, a.1.length ≤ d) (c : CPoly (NFM Fc m M)) :
    aeval (T.ts m) ((toPoly c).map (T.psiNFM m hm M ρ hρ)) = ∑ f ∈ Finset.range d,
      T.evP m ((c.map fun a ↦ a.1.getD f 0).map (unTr Fc m)) * ((ρ : T.F m) : L) ^ f := by
  simp only [T.evP_unTr_map m hm]
  rw [aeval_def, eval₂_map, eval₂_list_sum]
  simp only [aeval_def, eval₂_map, eval₂_list_sum, List.length_map]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have haf : a < c.length := Finset.mem_range.mp ha
  rw [RingHom.comp_apply, T.psiNFM_val, eval₂_list_sum' _ _ _ d (hd _), map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun f _ ↦ ?_
  have e1 : (c.map fun a ↦ a.1.getD f 0).getD a 0 = (c.getD a 0).1.getD f 0 := by
    rw [List.getD_eq_getElem (c.map fun a ↦ a.1.getD f 0) 0 (by simpa using haf), List.getElem_map,
      List.getD_eq_getElem c 0 haf]
  rw [e1]
  simp only [map_mul, map_pow, RingHom.comp_apply, IntermediateField.algebraMap_apply]
  ring

set_option maxHeartbeats 1600000 in
include hmn hk htrim hlen in
/-- **The coordinates of `W′/W`** for a witness over `Kₘ ⊗ N` read on the twist `ỹ = μ y`,
`μ = z/s`, and the value of its `j`-th coordinate through the column code. -/
theorem ky_dl_coords (Ah : GPoly (LC m)) (z : LC m) (sF : T.F m) (hsF0 : sF ≠ 0)
    (hAh : T.ev (m + 1) (pcP Fc ks m Ah) = (T.ev m z / (sF : L)) ^ n * T.evP m A)
    (hz0 : T.ev m z ≠ 0) (W0b : BPoly (NFM Fc m M))
    (hWdeg : ∀ i a, ((toB W0b).coeff i).coeff a ≠ 0 → i < n)
    (hWt0 : (T.krS m hTr A hsq hdegA n hn θ hθ).elemW (((toB W0b).map
      (mapRingHom (T.psiNFM m hTr.of_succ M ρ hρ))).comp
        (Polynomial.C (Polynomial.C ((T.MP m hTr.of_succ).sem z / sF)) * X)) ≠ 0)
    (j : ℕ) (hj : j < n) (cols : List (LC (m + 1)))
    (hcol : kyColM Fc ks m n M Ah z j W0b = some cols) :
    ∃ E' : Fin n → (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯,
      (T.krS m hTr A hsq hdegA n hn θ hθ).dl (Polynomial.C (T.val m g)′ * X)
          (T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk)
          ((T.krS m hTr A hsq hdegA n hn θ hθ).elemW (((toB W0b).map
            (mapRingHom (T.psiNFM m hTr.of_succ M ρ hρ))).comp
              (Polynomial.C (Polynomial.C ((T.MP m hTr.of_succ).sem z / sF)) * X))) =
        ∑ i, algebraMap (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯
          (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯ (E' i) *
            AdjoinSimple.gen (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯
              (T.krS m hTr A hsq hdegA n hn θ hθ).y ^ (i : ℕ) ∧
      ((E' ⟨j, hj⟩ : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯) : L) =
        (∑ f ∈ Finset.range (M.length - 1),
          T.ev (m + 1) (cols.getD f (MO Fc ks (m + 1)).zero) * ((ρ : T.F m) : L) ^ f) /
            (sF : L) ^ j := by
  classical
  have hTm : T.Tr m := hTr.of_succ
  set S := T.krS m hTr A hsq hdegA n hn θ hθ with hS
  have hx := T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk
  set ψ := T.psiNFM m hTm M ρ hρ with hψ
  set μ : T.F m := (T.MP m hTm).sem z / sF with hμdef
  have hμL : ((μ : T.F m) : L) = T.ev m z / (sF : L) := by
    rw [hμdef, IntermediateField.coe_div, T.sem_MP m hTm]
  have hsFL : ((sF : T.F m) : L) ≠ 0 := fun h ↦ hsF0 (Subtype.ext h)
  have hMne : M ≠ [] := fun h ↦ by rw [h] at hlen; simp at hlen
  have hM0 : toPoly M ≠ 0 := fun h ↦ hMne (by
    have := (CPoly.trim_eq_nil_iff M).mpr h; rwa [htrim] at this)
  have hρL : aeval ((ρ : T.F m) : L) (toPoly M) = 0 := by
    rw [show ((ρ : T.F m) : L) = algebraMap (T.F m) L ρ from rfl, aeval_algebraMap_apply, hρ,
      map_zero]
  have hρd : ((ρ : T.F m) : L)′ = 0 := MTower.deriv_root_rat _ _ hM0 hρL
  obtain ⟨Wd, s1, s2, Q, D, gg, hgg, hWd, hbez, hdiv, hD, hcolv, D', g', hroot, hDD, hgg'⟩ :=
    T.kyColM_spec m n hn hTr M htrim hlen Ah z j W0b cols hcol (E := L) ((ρ : T.F m) : L) hρL hρd
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hWd hbez hdiv hcolv
  set d := M.length - 1 with hd
  set Wl : L[X] := toPoly (W0b.map fun c ↦ ∑ f ∈ Finset.range d,
    T.ev (m + 1) (pcP Fc ks m ((c.map fun a ↦ a.1.getD f 0).map (unTr Fc m))) * ((ρ : T.F m) : L) ^ f)
    with hWl
  set Av : L := T.ev (m + 1) (pcP Fc ks m Ah) with hAv
  have hA0 : T.evP m A ≠ 0 := by
    rw [← T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]
    exact fun h0 ↦ S.htr ⟨_, hsq.ne_zero, h0⟩
  have hAv0 : Av ≠ 0 := by
    rw [hAh]; exact mul_ne_zero (pow_ne_zero _ (div_ne_zero hz0 hsFL)) hA0
  set Y : L := (μ : L) * θ with hY
  have hYn : Y ^ n = Av := by rw [hY, mul_pow, hμL, hθ, hAh]
  have hYd : Y′ = ((1 / n : ℚ) : L) * (Av′ * Av⁻¹) * Y := deriv_of_pow_eq n hn Y _ hYn hAv0
  obtain ⟨-, hWY⟩ := twist_dlog n Wl Wd s1 s2 Q D Av _ gg Y hYn hYd hWd hbez hgg hdiv
  -- `W = W(Y)`
  set Qp : (T.F m)[X][X] := ((toB W0b).map (mapRingHom ψ)).comp (Polynomial.C (Polynomial.C μ) * X)
    with hQp
  have hel : S.evalW Qp = S.elemW Qp := by
    refine S.evalW_eq_elemW _ fun i hi ↦ ?_
    rw [hQp, comp_C_mul_X_coeff, coeff_map]
    by_cases h0 : (toB W0b).coeff i = 0
    · simp [h0]
    · obtain ⟨a, ha⟩ : ∃ a, ((toB W0b).coeff i).coeff a ≠ 0 := by
        by_contra hc; push Not at hc; exact h0 (Polynomial.ext hc)
      exact absurd hi (not_le.mpr (hWdeg i a ha))
  set Fc' : CPoly (NFM Fc m M) → L := fun c ↦ ∑ f ∈ Finset.range d, T.ev (m + 1) (pcP Fc ks m
      ((c.map fun a ↦ a.1.getD f 0).map (unTr Fc m))) * ((ρ : T.F m) : L) ^ f with hFc'
  have hFc : ∀ c : CPoly (NFM Fc m M), Fc' c = aeval (T.ts m) ((toPoly c).map ψ) := fun c ↦ by
    rw [hFc', hψ, T.aeval_psiNFM_list m hTm M ρ hρ d (fun a ↦ nfm_len' m M htrim hlen a) c]
    refine Finset.sum_congr rfl fun f _ ↦ ?_
    congr 1
    rw [← T.sem_MP (m + 1) hTr]
    exact T.sem_poly_code m hTr _
  have hpoly : ((toB W0b).map (mapRingHom ψ)).map (aeval S.x).toRingHom = Wl := by
    ext i : 1
    rw [coeff_map, coeff_map, coe_mapRingHom, coeff_toB, hWl, coeff_toPoly]
    change _ = (W0b.map Fc').getD i 0
    by_cases hi : i < W0b.length
    · rw [List.getD_eq_getElem (W0b.map Fc') 0 (by simpa using hi), List.getElem_map, hFc,
        List.getD_eq_getElem W0b [] hi]
      rfl
    · rw [List.getD_eq_default (W0b.map Fc') 0 (by simpa using hi),
        List.getD_eq_default W0b [] (by omega)]
      simp
  have hWtY : ((S.elemW Qp : (T.F m)⟮S.x⟯⟮S.y⟯) : L) = Wl.eval Y := by
    rw [← hel, S.coe_evalW, hQp, Polynomial.map_comp, eval_comp, hpoly]
    congr 1
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_mul, eval_C, eval_X,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, IntermediateField.algebraMap_apply]
    rfl
  -- the coordinates
  have hmx : ∀ w : T.F (m + 1), (w : L) ∈ (T.F m)⟮S.x⟯ := fun w ↦ (T.mem_F_succ).mp w.2
  have hmc : ∀ w : T.F m, (w : L) ∈ (T.F m)⟮S.x⟯ := fun w ↦ IntermediateField.algebraMap_mem _ w
  have hDm : ∀ i, D.coeff i ∈ (T.F m)⟮S.x⟯ := fun i ↦ by
    rw [hDD, coeff_map]
    exact (T.mem_F_succ).mp (T.liftNFM_mem m hTr M ρ _ hroot)
  have hgm : gg ∈ (T.F m)⟮S.x⟯ := by
    rw [hgg']; exact (T.mem_F_succ).mp (T.liftNFM_mem m hTr M ρ _ hroot)
  obtain ⟨E', hE'v⟩ : ∃ E' : Fin n → (T.F m)⟮S.x⟯, ∀ i : Fin n,
      ((E' i : (T.F m)⟮S.x⟯) : L) = D.coeff i * (μ : L) ^ (i : ℕ) / gg :=
    ⟨fun i ↦ ⟨D.coeff i * (μ : L) ^ (i : ℕ) / gg, div_mem (mul_mem (hDm i) (pow_mem (hmc μ) _)) hgm⟩,
      fun i ↦ rfl⟩
  have hDev : D.eval Y = ∑ i ∈ Finset.range n, D.coeff i * Y ^ i := by
    rw [eval_eq_sum_range' (n := n)]
    by_contra hc
    push Not at hc
    by_cases hD0 : D = 0
    · rw [hD0] at hc; simp at hc; omega
    exact (leadingCoeff_ne_zero.mpr hD0) (hD _ hc)
  refine ⟨E', ?_, ?_⟩
  · apply Subtype.ext
    rw [S.coe_dl, hWtY, hWY, IntermediateField.coe_sum]
    change _ = ∑ i : Fin n, ((E' i : (T.F m)⟮S.x⟯) : L) * S.y ^ (i : ℕ)
    simp_rw [hE'v]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ D.coeff i * (μ : L) ^ i / gg * S.y ^ i), hDev,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hY, mul_pow]
    have hSy : S.y = θ := rfl
    rw [hSy]
    ring
  · rw [hE'v, hcolv]
    have e2 : T.ev (m + 1) (pcP Fc ks m [powC (MO Fc ks m) z j]) = T.ev m z ^ j := by
      rw [← T.sem_MP (m + 1) hTr]; exact T.coe_pcP_pow m hTr z j
    rw [e2, hμL, div_pow]
    field_simp

end Coords

lemma zipWith_sum_fin {α β : Type*} (F : α → β → L) : ∀ (ws : List α) (cs : List β)
    (h : ws.length = cs.length),
    (List.zipWith F ws cs).sum = ∑ i : Fin cs.length, F (ws[(i : ℕ)]'(by rw [h]; exact i.2)) cs[i]
  | [], [], _ => by simp
  | w :: ws, c :: cs, h => by
    simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons]
    rw [Fin.sum_univ_succ, zipWith_sum_fin F ws cs (by simpa using h)]
    rfl

variable [Fact (Irreducible (toPoly (fKc Fc)))] in
/-- **Forward, with list weights.** -/
theorem prde_forward_listN (m n j : ℕ) (hn : 0 < n) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
    (hA0 : T.evP m A ≠ 0) (θ : L) (hθ : θ ^ n = T.evP m A)
    (hspecA : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m j n A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)))
    (rhs : LC (m + 1)) (cols : List (LC (m + 1))) (aa : L) (haa : aa ∈ T.F (m + 1))
    (ws : List L) (hlen : ws.length = cols.length) (hws : ∀ w ∈ ws, w′ = 0)
    (hrep : T.ev (m + 1) rhs * θ ^ j = (aa * θ ^ j)′ +
      (List.zipWith (fun w c ↦ w * T.ev (m + 1) c * θ ^ j) ws cols).sum) :
    (prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A) (rhs :: cols)).any
      (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) = true := by
  refine T.prde_forward_genN m n j hn hTr A hA0 θ hθ hspecA rhs cols aa haa
    (fun i ↦ ws[(i : ℕ)]'(by rw [hlen]; exact i.2)) (fun i ↦ hws _ (List.getElem_mem _)) ?_
  rw [hrep, zipWith_sum_fin _ ws cols hlen]

omit [CharZero Cc] [CharZero L] in
/-- **The parametric equation of `kySolve`**: all components torsion, with witnesses and
columns. -/
lemma kySolve_spec (m n j : ℕ) (g : LC m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)}
    (extra : List (LC (m + 1))) (b : Bool)
    (hall : ∀ f ∈ (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length),
      ∃ N, kyTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs f = some (some N))
    (h : kySolveC Fc ks lv m n j g M zN gs A B kt l cs cpf ps bound rs extra = some b) :
    let comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length)
    ∃ (Ns : Fin comps.length → ℕ) (Wbs : Fin comps.length → BPoly (NFM Fc m M))
      (colss : Fin comps.length → List (LC (m + 1))),
      (∀ t : Fin comps.length,
        kyTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs comps[(t : ℕ)] = some (some (Ns t))) ∧
      (∀ t : Fin comps.length,
        kyWit Fc ks m n j M g A B kt l cs zN gs comps[(t : ℕ)] (Ns t) = some (Wbs t)) ∧
      (∀ t : Fin comps.length, kyColM Fc ks m n M A (MO Fc ks m).one j (Wbs t) = some (colss t)) ∧
      b = (prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)
        (((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) :: (extra ++ (List.ofFn colss).flatten))).any
          (fun r ↦ decide (r.1.getD 0 0 ≠ 0)) := by
  intro comps
  set tors := comps.map (kyTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs) with htorsdef
  have hall' : ∀ t : Fin comps.length, ∃ N,
      kyTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs comps[(t : ℕ)] = some (some N) :=
    fun t ↦ hall _ (List.getElem_mem t.2)
  choose Ns hNs using hall'
  have hNs' : ∀ t : Fin comps.length,
      ((tors[(t : ℕ)]'(by simp [htorsdef])).getD none).getD 0 = Ns t := fun t ↦ by
    simp [htorsdef, hNs t]
  unfold kySolveC at h
  dsimp only at h
  generalize hw : ((List.zip comps tors).map fun p ↦
    kyWit Fc ks m n j M g A B kt l cs zN gs p.1 ((p.2.getD none).getD 0)).allSome = ow at h
  rcases ow with _ | Wbl
  · exact absurd h (by simp)
  obtain ⟨hWl, hWv⟩ := allSome_spec _ Wbl hw
  have hlc : (List.zip comps tors).length = comps.length := by simp [htorsdef]
  have hWl' : Wbl.length = comps.length := by rw [hWl, List.length_map, hlc]
  set Wbs : Fin comps.length → BPoly (NFM Fc m M) := fun t ↦ Wbl[(t : ℕ)]'(by rw [hWl']; exact t.2)
    with hWbs
  have hwit : ∀ t : Fin comps.length,
      kyWit Fc ks m n j M g A B kt l cs zN gs comps[(t : ℕ)] (Ns t) = some (Wbs t) := fun t ↦ by
    have := hWv t (by rw [List.length_map, hlc]; exact t.2) (by rw [hWl']; exact t.2)
    simp only [List.getElem_map, List.getElem_zip] at this
    rw [hNs' t] at this
    exact this
  simp only at h
  generalize hc : (Wbl.map (kyColM Fc ks m n M A (MO Fc ks m).one j)).allSome = oc at h
  rcases oc with _ | cll
  · exact absurd h (by simp)
  obtain ⟨hcl, hcv⟩ := allSome_spec _ cll hc
  have hcl' : cll.length = comps.length := by rw [hcl, List.length_map, hWl']
  set colss : Fin comps.length → List (LC (m + 1)) := fun t ↦ cll[(t : ℕ)]'(by rw [hcl']; exact t.2)
    with hcolss
  have hcol : ∀ t : Fin comps.length,
      kyColM Fc ks m n M A (MO Fc ks m).one j (Wbs t) = some (colss t) := fun t ↦ by
    have := hcv t (by rw [List.length_map, hWl']; exact t.2) (by rw [hcl']; exact t.2)
    simp only [List.getElem_map] at this
    exact this
  have hofn : List.ofFn colss = cll := by
    apply List.ext_getElem
    · simp [hcl']
    · intro i h1 h2; simp [hcolss]
  refine ⟨Ns, Wbs, colss, hNs, hwit, hcol, ?_⟩
  rw [hofn]
  exact (Option.some.inj h).symm

/-- The residue coordinates over the non-zero components only. -/
lemma ky_res_comps {F : Type*} [Field F] (n j : ℕ) (M zN : CPoly ℚ) (gs : List (CPoly ℚ)) (r : ℕ)
    (ν : ℕ → F) (i : ℕ) (hi : i < r * n) :
    ∑ f ∈ Finset.range (M.length - 1), (kyR n j M zN gs f i : F) * ν f =
      ∑ t : Fin ((List.range (M.length - 1)).filter (kyNZ n j M zN gs r)).length,
        (kyR n j M zN gs ((List.range (M.length - 1)).filter (kyNZ n j M zN gs r))[(t : ℕ)] i : F) *
          ν ((List.range (M.length - 1)).filter (kyNZ n j M zN gs r))[(t : ℕ)] := by
  classical
  set comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs r) with hcomps
  have hz : ∀ f ∈ Finset.range (M.length - 1), ¬ f ∈ comps → (kyR n j M zN gs f i : F) * ν f = 0 := by
    intro f hf hfc
    have hnz : kyNZ n j M zN gs r f = false := by
      by_contra h
      exact hfc (List.mem_filter.mpr ⟨List.mem_range.mpr (Finset.mem_range.mp hf), by simpa using h⟩)
    simp only [kyNZ, List.any_eq_false, List.mem_range, bne_iff_ne, ne_eq, not_not] at hnz
    rw [hnz i hi]; simp
  rw [← Finset.sum_filter_of_ne (p := fun f ↦ f ∈ comps) (fun f hf h ↦ by
    by_contra hc; exact h (hz f hf hc))]
  have hnd : comps.Nodup := (List.nodup_range).filter _
  have hset : (Finset.range (M.length - 1)).filter (fun f ↦ f ∈ comps) = comps.toFinset := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
    constructor
    · exact fun h ↦ h.2
    · intro h
      exact ⟨List.mem_range.mp (List.mem_filter.mp h).1, h⟩
  rw [hset, List.sum_toFinset _ hnd, ← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp; rfl
  · intro k h1 h2; simp; rfl

omit [CharZero Cc] [CharZero L] in
lemma kyColM_length (m n : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (Ah : GPoly (LC m)) (z : LC m) (j : ℕ)
    (W : BPoly (NFM Fc m M)) (cols : List (LC (m + 1)))
    (h : kyColM Fc ks m n M Ah z j W = some cols) : cols.length = M.length - 1 := by
  unfold kyColM at h
  simp only at h
  split_ifs at h
  obtain rfl := (Option.some.inj h).symm
  simp

lemma zipWith_flatten_sum {α β γ : Type*} [AddCommMonoid γ] (F : α → β → γ) :
    ∀ (ws : List (List α)) (cs : List (List β)), ws.length = cs.length →
      (∀ i (h1 : i < ws.length) (h2 : i < cs.length), ws[i].length = cs[i].length) →
      (List.zipWith F ws.flatten cs.flatten).sum =
        (List.zipWith (fun w c ↦ (List.zipWith F w c).sum) ws cs).sum
  | [], [], _, _ => by simp
  | w :: ws, c :: cs, hl, hi => by
    simp only [List.flatten_cons, List.zipWith_cons_cons, List.sum_cons]
    have h0 : w.length = c.length := hi 0 (by simp) (by simp)
    rw [List.zipWith_append h0, List.sum_append,
      zipWith_flatten_sum F ws cs (by simpa using hl) (fun i h1 h2 ↦ hi (i + 1) (by simpa using h1)
        (by simpa using h2))]


lemma zipWith_ofFn {α β γ : Type*} {k : ℕ} (G : α → β → γ) (a : Fin k → α) (b : Fin k → β) :
    List.zipWith G (List.ofFn a) (List.ofFn b) = List.ofFn fun t ↦ G (a t) (b t) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2; simp

lemma zipWith_range_sum {α : Type*} (d : ℕ) (g : ℕ → L) (ev : α → L) (y : L)
    (cols : List α) (z : α) (hl : cols.length = d) :
    (List.zipWith (fun w c ↦ w * ev c * y) ((List.range d).map g) cols).sum =
      ∑ f ∈ Finset.range d, g f * ev (cols.getD f z) * y := by
  rw [zipWith_sum_fin _ _ _ (by simp [hl]), ← Fin.sum_univ_eq_sum_range (fun f ↦ g f * ev (cols.getD f z) * y)]
  rw [← Fin.sum_congr' _ hl]
  refine Finset.sum_congr rfl fun f _ ↦ ?_
  simp [List.getD_eq_getElem _ _ f.2]

set_option maxHeartbeats 4000000 in
open Classical in
/-- **Forward, every component torsion**: given the zero-fibre data (`W₀`, its `j`-th coordinate
as a combination of the `extra` columns), a Liouville form makes the parametric equation of
`kySolve` solvable with a non-zero coefficient of the integrand. -/
theorem ky_forward_pos (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
    (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (n : ℕ) (hn : 0 < n) (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (θ : L) (hθ : θ ^ n = T.evP m A) (hM : T.MixHyp (m + 1)) (hmn : m < T.n)
    {g : LC m} (hk : ks m = .exp g) (j : ℕ) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n)
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]
    (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0) (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (hζ : IsPrimitiveRoot (aeval ρ (toPoly zN)) n)
    (hok : kxOK Fc ks m A B kt l cs = true) (hc : kyConst Fc ks m n j g A B kt l cs = true)
    (hF : kyFieldOK Fc ks m n j g A B kt l cs M zN gs = true)
    (hspec : RdeSpecK (algebraMap Cc (T.F (m + 1))) (T.MP (m + 1) hTr)
      ((T.MP (m + 1) hTr).sem (fCode (MO Fc ks (m + 1)) (kpFr Fc ks m j n A)))
      (prdeC Fc ks lv (m + 1) (kpFr Fc ks m j n A)))
    (W₀ : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯)
    (hZ : ∀ U : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯,
      U ≠ 0 → (T.krS m hTr A hsq hdegA n hn θ hθ).Supp (K := AlgebraicClosure (T.F m)) U →
      ∃ e : T.F m, e′ = 0 ∧
        (T.krS m hTr A hsq hdegA n hn θ hθ).four (aeval ρ (toPoly zN)) hζ ⟨j, hjn⟩
          ((T.krS m hTr A hsq hdegA n hn θ hθ).dl (Polynomial.C (T.val m g)′ * X)
            (T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk) U) =
        (T.krS m hTr A hsq hdegA n hn θ hθ).cst e *
          (T.krS m hTr A hsq hdegA n hn θ hθ).four (aeval ρ (toPoly zN)) hζ ⟨j, hjn⟩
          ((T.krS m hTr A hsq hdegA n hn θ hθ).dl (Polynomial.C (T.val m g)′ * X)
            (T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk) W₀))
    (E0 : Fin n → (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯)
    (hE0 : (T.krS m hTr A hsq hdegA n hn θ hθ).dl (Polynomial.C (T.val m g)′ * X)
        (T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk) W₀ =
      ∑ i, algebraMap (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯
        (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯ (E0 i) *
          AdjoinSimple.gen (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯
            (T.krS m hTr A hsq hdegA n hn θ hθ).y ^ (i : ℕ))
    (extra : List (LC (m + 1))) (wx : List L) (hwx : wx.length = extra.length)
    (hwxc : ∀ w ∈ wx, w′ = 0)
    (hE0j : ((E0 ⟨j, hjn⟩ : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯) : L) =
      (List.zipWith (fun w c ↦ w * T.ev (m + 1) c) wx extra).sum)
    {ι : Type*} (sI : Finset ι) (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ ^ j =
      v′ + ∑ i ∈ sI, c i * logDeriv (u i))
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)}
    (hall : ∀ f ∈ (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length),
      ∃ N, kyTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs f = some (some N))
    (b : Bool) (hsolve : kySolveC Fc ks lv m n j g M zN gs A B kt l cs cpf ps bound rs extra = some b) :
    b = true := by
  classical
  have hTm : T.Tr m := hTr.of_succ
  set K := AlgebraicClosure (T.F m)
  set comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length) with hcomps
  obtain ⟨Ns, Wbs, colss, hNs, hwit, hcol, rfl⟩ :=
    kySolve_spec (lv := lv) m n j g M zN gs A B kt l cs ps bound rs extra b hall hsolve
  obtain ⟨htrim, hlen, -, -, -, -⟩ := kyFieldOK_spec hF
  have hmin : ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree → aeval ρ P ≠ 0 :=
    hmin_of_irr M ρ hρ (K := KF Fc m) (by rw [← toPoly_liftQ]; exact Fact.out)
  have hok' := T.kxOK_spec m hTm A B kt l cs hok
  have hD0 : ∀ q < cs.length, (T.MP m hTm).sem (kxD Fc ks m g cs q) ≠ 0 := fun q hq ↦
    T.kxD_ne m hM hk cs q (hok'.2 q hq).1
  obtain ⟨-, hβf, hresf⟩ := T.ky_points m hTm n j hn hjc g A B kt l cs M ρ hρ zN gs hok hc hF hmin hD0
  set ψ := T.psiNFM m hTm M ρ hρ with hψ
  -- the witnesses of the components
  have hW : ∀ t : Fin comps.length, ∃ W : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯, W ≠ 0 ∧
      (∀ q < cs.length, ∀ k < n, ((T.krS m hTr A hsq hdegA n hn θ hθ).ordAt K W
        (algebraMap (T.F m) K ((T.MP m hTm).sem (kqC Fc ks m cs q)))
        (algebraMap (T.F m) K (aeval ρ (toPoly zN) ^ k *
          ψ (kyBeta Fc ks m n j M g A B kt l cs gs q))) : ℚ) =
          Ns t * kyDen n j M zN gs cs.length comps[(t : ℕ)] * kyR n j M zN gs comps[(t : ℕ)] (q * n + k)) ∧
      (∀ a b : K, b ^ n = ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) K)).eval a → a ≠ 0 →
        (∀ q < cs.length, a ≠ algebraMap (T.F m) K ((T.MP m hTm).sem (kqC Fc ks m cs q))) →
        (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt K W a b = 0) ∧
      ∃ EW : Fin n → (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯,
        (T.krS m hTr A hsq hdegA n hn θ hθ).dl (Polynomial.C (T.val m g)′ * X) (T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk) W =
          ∑ i, algebraMap (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯ (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯ (EW i) *
            AdjoinSimple.gen (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯ (T.krS m hTr A hsq hdegA n hn θ hθ).y ^ (i : ℕ) ∧
        ((EW ⟨j, hjn⟩ : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯) : L) = ∑ f ∈ Finset.range (M.length - 1),
          T.ev (m + 1) ((colss t).getD f (MO Fc ks (m + 1)).zero) * ((ρ : T.F m) : L) ^ f := by
    intro t
    obtain ⟨hWdeg, W, hW0, ⟨uu, huu, hWe⟩, hWo, hWz⟩ := T.ky_comp_wit m hTr A hsq hdegA n hn hcopA θ hθ j hjc g
      B kt l cs M ρ hρ zN gs hok hc hF hmin hD0 comps[(t : ℕ)] (Ns t) (Wbs t) (hwit t)
    refine ⟨W, hW0, hWo, hWz, ?_⟩
    have hone : (T.MP m hTm).sem (MO Fc ks m).one / (1 : T.F m) = 1 := by
      rw [(T.MP m hTm).sem_one, div_one]
    have hel0 : (T.krS m hTr A hsq hdegA n hn θ hθ).elemW (((toB (Wbs t)).map (mapRingHom ψ)).comp
        (Polynomial.C (Polynomial.C ((T.MP m hTm).sem (MO Fc ks m).one / 1)) * X)) ≠ 0 := by
      rw [hone]
      intro h0
      apply hW0
      rw [hWe, h0, zero_mul]
    have hAh : T.ev (m + 1) (pcP Fc ks m A) = (T.ev m (MO Fc ks m).one / ((1 : T.F m) : L)) ^ n *
        T.evP m A := by
      rw [T.ev_one_code m hTm]
      change T.evP m A / T.evP m [(MO Fc ks m).one] = _
      rw [T.evP_single, T.ev_one_code m hTm]
      simp
    obtain ⟨E', hE', hE'j⟩ := T.ky_dl_coords m hTr A hsq hdegA n hn θ hθ hmn hk M htrim hlen ρ hρ A
      (MO Fc ks m).one 1 one_ne_zero hAh (by rw [T.ev_one_code m hTm]; exact one_ne_zero) (Wbs t)
      hWdeg hel0 j hjn (colss t) (hcol t)
    have hel0' : (T.krS m hTr A hsq hdegA n hn θ hθ).elemW (((toB (Wbs t)).map (mapRingHom ψ)).comp
        (Polynomial.C (Polynomial.C 1) * X)) ≠ 0 := by rw [← hone]; exact hel0
    rw [hone] at hE'
    obtain ⟨EW, hEW, hEWj⟩ := (T.krS m hTr A hsq hdegA n hn θ hθ).dl_mul_base _ (T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk) _ hel0'
      uu huu E' hE'
    refine ⟨EW, ?_, ?_⟩
    · rw [hWe]; exact hEW
    · have h1 := congrArg Subtype.val (hEWj ⟨j, hjn⟩ (by simp; omega))
      refine h1.trans (hE'j.trans ?_)
      simp
  choose Wt hWt0 hWo hWz EWc hEWc hEWj using hW
  -- the data of `ky_liouville`
  have hx := T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk
  obtain ⟨hb, hbm, hDR, hDoff, hbP⟩ := T.ky_data m hTr A hsq hdegA n hn θ hθ B kt l cs j
  set cq : Fin cs.length → T.F m := fun q ↦ (T.MP m hTm).sem (kqC Fc ks m cs q) with hcq
  set βq : Fin cs.length → T.F m := fun q ↦ ψ (kyBeta Fc ks m n j M g A B kt l cs gs q) with hβq
  set ν : Fin comps.length → T.F m := fun t ↦ ρ ^ comps[(t : ℕ)] with hν
  set rr : Fin cs.length → ℕ → Fin comps.length → ℚ := fun q kk t ↦
    kyR n j M zN gs comps[(t : ℕ)] (q * n + kk % n) with hrr
  have hc0 : ∀ q : Fin cs.length, cq q ≠ 0 := fun q ↦ (hok'.2 q q.2).1
  have hRne : ∀ q : Fin cs.length, (X ^ kt * GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q))).eval
      (cq q) ≠ 0 := fun q ↦ T.kx_Rne m hTm A B kt l cs hok q
  have hβq' : ∀ q : Fin cs.length, βq q ≠ 0 ∧ βq q ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n = (T.krS m hTr A hsq hdegA n hn θ hθ).p.eval (cq q) := fun q ↦ hβf q q.2
  have hres : ∀ (q : Fin cs.length) (kk : ℕ), (GPoly.toPoly (T.MP m hTm) B).eval (cq q) *
      (aeval ρ (toPoly zN) ^ kk * βq q) ^ j =
      (∑ t, (rr q kk t : T.F m) * ν t) * (((T.val m g)′ * cq q - (cq q)′) *
        (X ^ kt * GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q)) * (T.krS m hTr A hsq hdegA n hn θ hθ).p ^ l).eval (cq q)) := by
    intro q kk
    have h1 := hresf q q.2 kk
    have hi : (q : ℕ) * n + kk % n < cs.length * n := by
      have := Nat.mod_lt kk hn
      nlinarith [q.2]
    have hMne : M ≠ [] := fun h ↦ by rw [h] at hlen; simp at hlen
    have hMdeg : (toPoly M).natDegree = M.length - 1 := by
      have := CPoly.length_trim (p := M) (by rw [htrim]; exact hMne)
      rw [htrim] at this; omega
    rw [hMdeg, ky_res_comps n j M zN gs cs.length (fun f ↦ (ρ : T.F m) ^ f) _ hi] at h1
    rw [h1, T.sem_kxD m hTm, T.sem_kxR m hTm, T.sem_eq_val m hTm g]
    simp only [hrr, hν, hcq]
    congr 1
    have hSp : (T.krS m hTr A hsq hdegA n hn θ hθ).p = GPoly.toPoly (T.MP m hTm) A := rfl
    rw [hSp]
    simp only [eval_mul, eval_pow, eval_X]
    ring
  have hme : ∀ t : Fin comps.length, 0 < Ns t * kyDen n j M zN gs cs.length comps[(t : ℕ)] := by
    intro t
    refine Nat.mul_pos (T.ky_comp_pos m hTr A hsq hdegA n hn hcopA θ hθ j hjc g B kt l cs M ρ hρ zN
      gs hok hc hF hmin hD0 ps bound rs _ _ (hNs t)) ?_
    exact lcmL_pos fun x hx ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact Rat.den_pos _
  have hWo' : ∀ t (q : Fin cs.length) (kk : Fin (T.krS m hTr A hsq hdegA n hn θ hθ).n), ((T.krS m hTr A hsq hdegA n hn θ hθ).ordAt K (Wt t)
      (Differential.SuperData.pq (K := K) (aeval ρ (toPoly zN)) cq βq q kk).1
      (Differential.SuperData.pq (K := K) (aeval ρ (toPoly zN)) cq βq q kk).2 : ℚ) =
      ((Ns t * kyDen n j M zN gs cs.length comps[(t : ℕ)] : ℕ) : ℚ) * rr q kk t := by
    intro t q kk
    have := hWo t q q.2 kk kk.2
    simp only [Differential.SuperData.pq, hrr]
    rw [this, show (kk : ℕ) % n = kk from Nat.mod_eq_of_lt kk.2]; push_cast; ring
  have hWz' : ∀ t (a b : K), b ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n = ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) K)).eval a → a ≠ 0 →
      (∀ q : Fin cs.length, a ≠ algebraMap (T.F m) K (cq q)) → (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt K (Wt t) a b = 0 :=
    fun t a b hv ha hq ↦ hWz t a b hv ha (fun q hq' ↦ hq ⟨q, hq'⟩)
  have hu' : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯ := fun i hi ↦
    ⟨(hu i hi).1, T.krS_mem m hTr A hsq hdegA n hn θ hθ _ (hu i hi).2⟩
  obtain ⟨a, ha, ee, e0, hee, he0, hae⟩ := (T.krS m hTr A hsq hdegA n hn θ hθ).ky_liouville (K := K) _ hx (aeval ρ (toPoly zN)) hζ
    ⟨j, hjn⟩ (fun c ↦ deriv_algebraMap c) (T.keS_good m hM hk) (T.keS_constC m) cq hc0
    (GPoly.toPoly (T.MP m hTm) B) l _ hb _ _ hDR hRne hDoff hbP βq hβq' ν rr hres hj0 hbm sI c u hcd
    hu' v (T.krS_mem m hTr A hsq hdegA n hn θ hθ _ hv) heq Wt hWt0 _ hme hWo' hWz' W₀ hZ EWc hEWc E0 hE0
  -- the parametric equation
  have hA0 : T.evP m A ≠ 0 := by
    rw [← T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]
    exact fun h0 ↦ (T.krS m hTr A hsq hdegA n hn θ hθ).htr ⟨_, hsq.ne_zero, h0⟩
  have hMne : M ≠ [] := fun h ↦ by rw [h] at hlen; simp at hlen
  have hM0 : toPoly M ≠ 0 := fun h ↦ hMne (by
    have := (CPoly.trim_eq_nil_iff M).mpr h; rwa [htrim] at this)
  have hρL : aeval ((ρ : T.F m) : L) (toPoly M) = 0 := by
    rw [show ((ρ : T.F m) : L) = algebraMap (T.F m) L ρ from rfl, aeval_algebraMap_apply, hρ,
      map_zero]
  have hρd : ((ρ : T.F m) : L)′ = 0 := MTower.deriv_root_rat _ _ hM0 hρL
  set wsc : Fin comps.length → List L := fun t ↦
    (List.range (M.length - 1)).map fun f ↦ algebraMap (T.F m) L (ee t) * ((ρ : T.F m) : L) ^ f with hwsc
  have hcl : ∀ t, (colss t).length = M.length - 1 := fun t ↦ kyColM_length (Fc := Fc) (ks := ks) m n M A _ j _ _ (hcol t)
  have hflat : (List.ofFn wsc).flatten.length = (List.ofFn colss).flatten.length := by
    simp only [List.length_flatten, List.map_ofFn]
    congr 1
    apply List.ext_getElem
    · simp <;> rfl
    · intro i h1 h2; simp [hwsc, hcl]
  refine T.prde_forward_listN (lv := lv) m n j hn hTr A hA0 θ hθ hspec _
    (extra ++ (List.ofFn colss).flatten) a ((T.mem_F_succ).mpr ha)
    ((wx.map fun w ↦ algebraMap (T.F m) L e0 * w) ++ (List.ofFn wsc).flatten)
    (by simp only [List.length_append, List.length_map, hwx, hflat]) ?_ ?_
  · intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
      rw [Derivation.leibniz, hwxc w' hw', deriv_algebraMap, he0]; simp
    · obtain ⟨lst, hl, hwl⟩ := List.mem_flatten.mp hw
      obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hl
      obtain ⟨f, -, rfl⟩ := List.mem_map.mp hwl
      rw [Derivation.leibniz, Derivation.leibniz_pow, hρd, deriv_algebraMap, hee t]; simp
  · have hy : (T.krS m hTr A hsq hdegA n hn θ hθ).y = θ := rfl
    rw [hy] at hae
    rw [hae, List.zipWith_append (by simp [hwx]), List.sum_append,
      zipWith_flatten_sum _ _ _ (by simp <;> rfl) (fun i h1 h2 ↦ by simp [hwsc, hcl])]
    have hx1 : (List.zipWith (fun w c ↦ w * T.ev (m + 1) c * θ ^ j)
        (wx.map fun w ↦ algebraMap (T.F m) L e0 * w) extra).sum =
        algebraMap (T.F m) L e0 * (((E0 ⟨j, hjn⟩ : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯) : L) *
          θ ^ j) := by
      rw [hE0j, List.zipWith_map_left, zipWith_sum_fin _ _ _ hwx, zipWith_sum_fin _ _ _ hwx,
        Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    have hx2 : (List.zipWith (fun w c ↦ (List.zipWith (fun w c ↦ w * T.ev (m + 1) c * θ ^ j) w c).sum)
        (List.ofFn wsc) (List.ofFn colss)).sum = ∑ t, algebraMap (T.F m) L (ee t) *
          (((EWc t ⟨j, hjn⟩ : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯) : L) * θ ^ j) := by
      rw [zipWith_ofFn, List.sum_ofFn]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      rw [zipWith_range_sum _ _ _ _ _ (MO Fc ks (m + 1)).zero (hcl t), hEWj t, Finset.sum_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ ↦ ?_
      ring
    rw [hx1, hx2]
    ring_nf
    rfl

set_option maxHeartbeats 4000000 in
open Classical in
/-- **Forward, a component not torsion**: when the orders over `x = 0` can be killed (`hkill`), a
Liouville form is impossible. -/
theorem ky_forward_neg (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
    (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (n : ℕ) (hn : 0 < n) (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (θ : L) (hθ : θ ^ n = T.evP m A) (hM : T.MixHyp (m + 1)) (hmn : m < T.n)
    {g : LC m} (hk : ks m = .exp g) (j : ℕ) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n)
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0) (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (hζ : IsPrimitiveRoot (aeval ρ (toPoly zN)) n)
    (hok : kxOK Fc ks m A B kt l cs = true) (hc : kyConst Fc ks m n j g A B kt l cs = true)
    (hF : kyFieldOK Fc ks m n j g A B kt l cs M zN gs = true)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)} (f0 : ℕ)
    (hf0 : f0 ∈ (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length))
    (htors : kyTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs f0 = some none)
    (hkill : ∀ V : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯,
      V ≠ 0 → (∀ α β' : AlgebraicClosure (T.F m), β' ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
        ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) _)).eval α → α ≠ 0 →
        (∀ q : Fin cs.length, α ≠ algebraMap (T.F m) _ ((T.MP m hTr.of_succ).sem (kqC Fc ks m cs q))) →
        (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt (AlgebraicClosure (T.F m)) V α β' = 0) →
      ∃ V' : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯,
        V' ≠ 0 ∧ ∃ M' : ℕ, 0 < M' ∧
        (∀ α β' : AlgebraicClosure (T.F m), β' ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
          ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) _)).eval α → α ≠ 0 →
          (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt (AlgebraicClosure (T.F m)) V' α β' =
            M' * (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt (AlgebraicClosure (T.F m)) V α β') ∧
        (∀ β' : AlgebraicClosure (T.F m), β' ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
          ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) _)).eval 0 →
          (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt (AlgebraicClosure (T.F m)) V' 0 β' = 0))
    {ι : Type*} (sI : Finset ι) (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ ^ j =
      v′ + ∑ i ∈ sI, c i * logDeriv (u i)) : False := by
  classical
  have hTm : T.Tr m := hTr.of_succ
  set K := AlgebraicClosure (T.F m)
  set comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length) with hcomps
  obtain ⟨htrim, hlen, -, -, -, -⟩ := kyFieldOK_spec hF
  have hmin : ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree → aeval ρ P ≠ 0 :=
    hmin_of_irr M ρ hρ (K := KF Fc m) (by rw [← toPoly_liftQ]; exact Fact.out)
  have hok' := T.kxOK_spec m hTm A B kt l cs hok
  have hD0 : ∀ q < cs.length, (T.MP m hTm).sem (kxD Fc ks m g cs q) ≠ 0 := fun q hq ↦
    T.kxD_ne m hM hk cs q (hok'.2 q hq).1
  obtain ⟨-, hβf, hresf⟩ := T.ky_points m hTm n j hn hjc g A B kt l cs M ρ hρ zN gs hok hc hF hmin hD0
  set ψ := T.psiNFM m hTm M ρ hρ with hψ
  have hx := T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk
  obtain ⟨hb, hbm, hDR, hDoff, hbP⟩ := T.ky_data m hTr A hsq hdegA n hn θ hθ B kt l cs j
  set cq : Fin cs.length → T.F m := fun q ↦ (T.MP m hTm).sem (kqC Fc ks m cs q) with hcq
  set βq : Fin cs.length → T.F m := fun q ↦ ψ (kyBeta Fc ks m n j M g A B kt l cs gs q) with hβq
  set ν : Fin comps.length → T.F m := fun t ↦ ρ ^ comps[(t : ℕ)] with hν
  set rr : Fin cs.length → ℕ → Fin comps.length → ℚ := fun q kk t ↦
    kyR n j M zN gs comps[(t : ℕ)] (q * n + kk % n) with hrr
  have hc0 : ∀ q : Fin cs.length, cq q ≠ 0 := fun q ↦ (hok'.2 q q.2).1
  have hRne : ∀ q : Fin cs.length, (X ^ kt * GPoly.toPoly (T.MP m hTm)
      (prodLinG Fc ks m (cs.eraseIdx q))).eval (cq q) ≠ 0 := fun q ↦ T.kx_Rne m hTm A B kt l cs hok q
  have hβq' : ∀ q : Fin cs.length, βq q ≠ 0 ∧ βq q ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
      (T.krS m hTr A hsq hdegA n hn θ hθ).p.eval (cq q) := fun q ↦ hβf q q.2
  have hMne : M ≠ [] := fun h ↦ by rw [h] at hlen; simp at hlen
  have hMdeg : (toPoly M).natDegree = M.length - 1 := by
    have := CPoly.length_trim (p := M) (by rw [htrim]; exact hMne)
    rw [htrim] at this; omega
  have hres : ∀ (q : Fin cs.length) (kk : ℕ), (GPoly.toPoly (T.MP m hTm) B).eval (cq q) *
      (aeval ρ (toPoly zN) ^ kk * βq q) ^ j =
      (∑ t, (rr q kk t : T.F m) * ν t) * (((T.val m g)′ * cq q - (cq q)′) *
        (X ^ kt * GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q)) *
          (T.krS m hTr A hsq hdegA n hn θ hθ).p ^ l).eval (cq q)) := by
    intro q kk
    have h1 := hresf q q.2 kk
    have hi : (q : ℕ) * n + kk % n < cs.length * n := by
      have := Nat.mod_lt kk hn
      nlinarith [q.2]
    rw [hMdeg, ky_res_comps n j M zN gs cs.length (fun f ↦ (ρ : T.F m) ^ f) _ hi] at h1
    rw [h1, T.sem_kxD m hTm, T.sem_kxR m hTm, T.sem_eq_val m hTm g]
    simp only [hrr, hν, hcq]
    congr 1
    have hSp : (T.krS m hTr A hsq hdegA n hn θ hθ).p = GPoly.toPoly (T.MP m hTm) A := rfl
    rw [hSp]
    simp only [eval_mul, eval_pow, eval_X]
    ring
  -- the independence of the coordinates
  have hnd : comps.Nodup := (List.nodup_range).filter _
  have hlt : ∀ t : Fin comps.length, comps[(t : ℕ)] < (toPoly M).natDegree := fun t ↦ by
    have := List.mem_filter.mp (List.getElem_mem t.2)
    rw [hMdeg]; exact List.mem_range.mp this.1
  have hνi : ∀ tt : Fin comps.length → ℚ, ∑ e, (tt e : T.F m) * ν e = 0 → ∀ e, tt e = 0 := by
    intro tt htt e
    set t' : ℕ → ℚ := fun f ↦ ∑ e' : Fin comps.length, if comps[(e' : ℕ)] = f then tt e' else 0 with ht'
    have hsum : ∑ f ∈ Finset.range (toPoly M).natDegree, (t' f : T.F m) * ρ ^ f = 0 := by
      rw [← htt]
      simp only [ht', Rat.cast_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e' _ ↦ ?_
      rw [Finset.sum_eq_single comps[(e' : ℕ)] (fun f _ hf ↦ by
          rw [if_neg (Ne.symm hf)]; simp)
        (fun h ↦ absurd (Finset.mem_range.mpr (hlt e')) h), if_pos rfl]
    have := pow_indep M ρ hmin (by intro h; exact hMne (by
      have := (CPoly.trim_eq_nil_iff M).mpr h; rwa [htrim] at this)) t' hsum _ (hlt e)
    simp only [ht'] at this
    rwa [Finset.sum_eq_single e (fun e' _ he' ↦ by
        rw [if_neg]; intro h; exact he' (Fin.ext (hnd.getElem_inj_iff.mp h)))
      (fun h ↦ absurd (Finset.mem_univ e) h), if_pos rfl] at this
  obtain ⟨e0, he0l, he0⟩ := List.mem_iff_getElem.mp hf0
  have hu' : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯ :=
    fun i hi ↦ ⟨(hu i hi).1, T.krS_mem m hTr A hsq hdegA n hn θ hθ _ (hu i hi).2⟩
  obtain ⟨V, hV0, Mv, hMv, hVo, hVz, hV0z⟩ := (T.krS m hTr A hsq hdegA n hn θ hθ).ky_nontors (K := K)
    _ hx (aeval ρ (toPoly zN)) hζ ⟨j, hjn⟩ (fun c ↦ deriv_algebraMap c) (T.keS_good m hM hk)
    (T.keS_constC m) cq hc0 (GPoly.toPoly (T.MP m hTm) B) l _ hb _ _ hDR hRne hDoff hbP βq hβq' ν rr
    hres hj0 hbm hνi hkill sI c u hcd hu' v (T.krS_mem m hTr A hsq hdegA n hn θ hθ _ hv) heq
    ⟨e0, he0l⟩
  -- the points and the oracle
  set ζ' := aeval ρ (toPoly zN) with hζ'
  have hin : ∀ i : Fin (cs.length * n), (i : ℕ) / n < cs.length :=
    fun i ↦ (Nat.div_lt_iff_lt_mul hn).mpr i.2
  set α : Fin (cs.length * n) → T.F m := fun i ↦ (T.MP m hTm).sem (kqC Fc ks m cs (i / n)) with hαdef
  set β : Fin (cs.length * n) → T.F m := fun i ↦ ζ' ^ ((i : ℕ) % n) *
    ψ (kyBeta Fc ks m n j M g A B kt l cs gs (i / n)) with hβdef
  have hcinj := T.kx_cinj m hTm A B kt l cs hok
  have hβ : ∀ i, β i ≠ 0 ∧ β i ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
      (T.krS m hTr A hsq hdegA n hn θ hθ).p.eval (α i) := fun i ↦ by
    obtain ⟨h0, hpw⟩ := hβf _ (hin i)
    refine ⟨mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hn.ne')) h0, ?_⟩
    show _ ^ n = (GPoly.toPoly (T.MP m hTm) A).eval _
    rw [mul_pow, ← pow_mul, mul_comm _ n, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hpw]
  have hP : Function.Injective fun i ↦ (α i, β i) := by
    intro i i' h
    have h1 : (i : ℕ) / n = i' / n := by
      have := congrArg Prod.fst h
      exact congrArg Fin.val (hcinj (a₁ := ⟨_, hin i⟩) (a₂ := ⟨_, hin i'⟩) this)
    have h2 := congrArg Prod.snd h
    simp only [hβdef, h1] at h2
    have h3 := mul_right_cancel₀ (hβf _ (hin i')).1 h2
    have h4 := hζ.pow_inj (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) h3
    apply Fin.ext
    rw [← Nat.div_add_mod i n, ← Nat.div_add_mod i' n, h1, h4]
  have hpf : Polynomial.C ((1 : T.F m) ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n) *
      (T.krS m hTr A hsq hdegA n hn θ hθ).p = (toPoly (kyFA Fc m M A)).map ψ := by
    rw [one_pow, map_one, one_mul, hψ, T.kyFA_map m hTm M ρ hρ]; rfl
  have hp0 : Polynomial.C ((1 : T.F m) ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n) *
      (T.krS m hTr A hsq hdegA n hn θ hθ).p ≠ 0 := by rw [one_pow, map_one, one_mul]; exact hsq.ne_zero
  have hsqp : Squarefree (Polynomial.C ((1 : T.F m) ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n) *
      (T.krS m hTr A hsq hdegA n hn θ hθ).p) := by rw [one_pow, map_one, one_mul]; exact hsq
  have hcopp : Nat.Coprime n (Polynomial.C ((1 : T.F m) ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n) *
      (T.krS m hTr A hsq hdegA n hn θ hθ).p).natDegree := by
    rw [one_pow, map_one, one_mul]; exact hcopA
  obtain ⟨hd, hsqK, hcop2⟩ := fK_factsN ψ (kyFA Fc m M A) (CPoly.trim_trim _) _ hpf hp0 hsqp n hcopp
  have hα : ∀ i, ψ (kyAl Fc ks m n M cs i) = α i := fun i ↦ by
    simp only [kyAl, hψ, T.psiNFM_embM, T.psiF_trC m hTm, hαdef]
  have hβ' : ∀ i, ψ (kyBe Fc ks m n j M g A B kt l cs zN gs i) = 1 * β i := fun i ↦ by
    simp only [kyBe, map_mul, map_pow, hψ, T.psiNFM_ofQ, one_mul, hβdef, hζ']
  have hΓK : ∀ i, (((T.krS m hTr A hsq hdegA n hn θ hθ).n : ℕ) : NFM Fc m M) *
      (kyBe Fc ks m n j M g A B kt l cs zN gs i) ^ ((T.krS m hTr A hsq hdegA n hn θ hθ).n - 1) ≠ 0 ∧
      (kyBe Fc ks m n j M g A B kt l cs zN gs i) ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
        (toPoly (kyFA Fc m M A)).eval (kyAl Fc ks m n M cs i) := fun i ↦ by
    constructor
    · intro h0
      have := congrArg ψ h0
      rw [map_mul, map_pow, hβ' i, one_mul, map_natCast, map_zero] at this
      exact mul_ne_zero (by exact_mod_cast hn.ne') (pow_ne_zero _ (hβ i).1) this
    · apply ψ.injective
      rw [map_pow, hβ' i, one_mul, (hβ i).2, ← eval₂_at_apply, ← eval_map, ← hpf, hα i, one_pow,
        map_one, one_mul]
  have hspecT := torsOracleC_specY (redAtNFM Fc m M rs) cpf
    (fun p _ R h ↦ redAtNFM_valid Fc m M rs p R h) ps bound hsqK hcop2
  have hvK : ∀ i, kyBe Fc ks m n j M g A B kt l cs zN gs i ≠ 0 ∧
      (kyBe Fc ks m n j M g A B kt l cs zN gs i) ^ n =
        (toPoly (kyFA Fc m M A)).eval (kyAl Fc ks m n M cs i) := fun i ↦ by
    refine ⟨fun h0 ↦ ?_, (hΓK i).2⟩
    have := congrArg ψ h0
    rw [hβ' i, one_mul, map_zero] at this
    exact (hβ i).1 this
  have hinjK : Function.Injective fun i ↦ (kyAl Fc ks m n M cs i, kyBe Fc ks m n j M g A B kt l cs zN gs i) := by
    intro i i' h
    apply hP
    simp only [Prod.ext_iff] at h ⊢
    refine ⟨?_, ?_⟩
    · rw [← hα i, ← hα i', h.1]
    · have := congrArg ψ h.2
      rw [hβ' i, hβ' i', one_mul, one_mul] at this
      exact this
  have hnot := (hspecT (cs.length * n) _ _ (kyMult n j M zN gs cs.length f0) hvK hinjK).2 htors
  have hnp := (T.krS m hTr A hsq hdegA n hn θ hθ).pts_not_principal (K := K) hcopA α β hP hβ
    (kyMult n j M zN gs cs.length f0) ψ (kyFA Fc m M A) 1 one_ne_zero hpf hd _ _ hα hβ' hΓK hnot
  apply hnp Mv hMv
  -- `V^{L} ∏ (x − c_q)^{M sh_q}` has divisor `M Γ`
  set Lf : ℕ := kyDen n j M zN gs cs.length f0 with hLf
  set sh : ℕ → ℤ := fun q ↦ kySh n j M zN gs cs.length f0 q with hsh
  set U : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯ :=
    ∏ q : Fin cs.length, (T.krS m hTr A hsq hdegA n hn θ hθ).polyX (X - Polynomial.C (cq q)) ^
      ((Mv : ℤ) * sh q) with hU
  have hU0 : U ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q _ ↦
    zpow_ne_zero _ ((T.krS m hTr A hsq hdegA n hn θ hθ).polyX_ne_zero (X_sub_C_ne_zero _))
  have hVL : V ^ (Lf : ℤ) ≠ 0 := zpow_ne_zero _ hV0
  have hordU : ∀ a b : K, b ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
      ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) K)).eval a →
      (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt K U a b =
        ∑ q : Fin cs.length, (Mv : ℤ) * sh q *
          (if a = algebraMap (T.F m) K (cq q) then (if b = 0 then ((T.krS m hTr A hsq hdegA n hn θ hθ).n : ℤ) else 1) else 0) := by
    intro a b hv
    rw [hU, (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt_prod hv _ _ (fun q _ ↦ zpow_ne_zero _
      ((T.krS m hTr A hsq hdegA n hn θ hθ).polyX_ne_zero (X_sub_C_ne_zero _)))]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [(T.krS m hTr A hsq hdegA n hn θ hθ).ordAt_zpow hv,
      (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt_X_sub _ a b hv]
  have hgam0 : ∀ a b : K, (∀ q : Fin cs.length, a ≠ algebraMap (T.F m) K (cq q)) →
      Differential.SuperData.gammaPts (K := K) α β (kyMult n j M zN gs cs.length f0) (a, b) = 0 := by
    intro a b ha
    rw [Differential.SuperData.gammaPts]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [if_neg]
    intro h
    exact ha ⟨_, hin i⟩ (by simpa [hαdef, hcq] using (Prod.ext_iff.mp h).1)
  have hord : ∀ a b : K, b ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
      ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) K)).eval a →
      (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt K (V ^ (Lf : ℤ) * U) a b =
        Mv * Differential.SuperData.gammaPts (K := K) α β (kyMult n j M zN gs cs.length f0) (a, b) := by
    intro a b hv
    rw [(T.krS m hTr A hsq hdegA n hn θ hθ).ordAt_mul hv hVL hU0,
      (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt_zpow hv, hordU a b hv]
    by_cases hq : ∃ q : Fin cs.length, a = algebraMap (T.F m) K (cq q)
    · obtain ⟨q, rfl⟩ := hq
      have hb0 : algebraMap (T.F m) K (βq q) ≠ 0 := (_root_.map_ne_zero _).mpr (hβq' q).1
      have hv0 : (algebraMap (T.F m) K (βq q)) ^ (T.krS m hTr A hsq hdegA n hn θ hθ).n =
          ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) K)).eval
            (algebraMap (T.F m) K (cq q)) := by
        rw [← map_pow, (hβq' q).2, eval_map, eval₂_at_apply]
      obtain ⟨kk, hkk0, rfl⟩ := (T.krS m hTr A hsq hdegA n hn θ hθ).over_k ζ' hζ _ _ hb0 hv0 b hv
      have hkk : kk < n := hkk0
      have hbb : algebraMap (T.F m) K ζ' ^ kk * algebraMap (T.F m) K (βq q) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ ((_root_.map_ne_zero _).mpr (hζ.ne_zero hn.ne'))) hb0
      set i : Fin (cs.length * n) := ⟨q * n + kk, by nlinarith [q.2]⟩ with hi
      have hiq : (i : ℕ) / n = q := by
        simp only [hi]
        rw [Nat.add_div_of_dvd_right (Dvd.intro_left _ rfl), Nat.mul_div_cancel _ hn,
          Nat.div_eq_of_lt hkk, add_zero]
      have hik : (i : ℕ) % n = kk := by
        simp only [hi]; rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hkk]
      have hpti : (algebraMap (T.F m) K (cq q), algebraMap (T.F m) K ζ' ^ kk * algebraMap (T.F m) K (βq q)) =
          (algebraMap (T.F m) K (α i), algebraMap (T.F m) K (β i)) := by
        simp [hαdef, hβdef, hiq, hik, hcq, hβq]
      have hgi : Differential.SuperData.gammaPts (K := K) α β (kyMult n j M zN gs cs.length f0)
          (algebraMap (T.F m) K (cq q), algebraMap (T.F m) K ζ' ^ kk * algebraMap (T.F m) K (βq q)) =
          kyMult n j M zN gs cs.length f0 i := by
        rw [hpti, Differential.SuperData.gammaPts, Finset.sum_eq_single i]
        · simp
        · intro i' _ hi'
          rw [if_neg]
          intro h
          apply hi'
          apply hP
          simp only [Prod.ext_iff] at h ⊢
          exact ⟨((algebraMap (T.F m) K).injective h.1).symm, ((algebraMap (T.F m) K).injective h.2).symm⟩
        · simp
      rw [hgi, Finset.sum_eq_single q (fun q' _ hq' ↦ by
          rw [if_neg, mul_zero]; intro h; apply hq'; apply hcinj
          exact ((algebraMap (T.F m) K).injective h).symm) (fun h ↦ absurd (Finset.mem_univ _) h),
        if_pos rfl, if_neg hbb, mul_one]
      -- the orders of `V` and the multiplicity
      have hVq := hVo q ⟨kk, hkk⟩
      simp only [Differential.SuperData.pq, map_mul, map_pow] at hVq
      have hzc := Differential.SuperData.rat_mul_den_int (kyR n j M zN gs f0 i) Lf
        (dvd_lcmL (List.mem_map.mpr ⟨i, List.mem_range.mpr i.2, rfl⟩))
      have hshq : -kyZc n j M zN gs cs.length f0 i ≤ kySh n j M zN gs cs.length f0 q := by
        simp only [kySh]
        refine foldr_max_ge _ _ (List.mem_map.mpr ⟨kk, List.mem_range.mpr hkk, ?_⟩)
        simp only [hi]
      have hmult : (kyMult n j M zN gs cs.length f0 i : ℤ) =
          kyZc n j M zN gs cs.length f0 i + kySh n j M zN gs cs.length f0 q := by
        rw [kyMult, hiq, Int.toNat_of_nonneg (by omega)]
      have hrrq : rr q kk ⟨e0, he0l⟩ = kyR n j M zN gs f0 i := by
        simp only [hrr, he0, hi]
        rw [Nat.mod_eq_of_lt hkk]
      rw [hrrq] at hVq
      have hfin : ((Lf : ℤ) * (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt K V
          (algebraMap (T.F m) K (cq q)) (algebraMap (T.F m) K ζ' ^ kk * algebraMap (T.F m) K (βq q)) : ℚ) =
          Mv * kyZc n j M zN gs cs.length f0 i := by
        push_cast
        rw [hVq, kyZc, ← hzc]
        ring
      have hfin' : (Lf : ℤ) * (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt K V
          (algebraMap (T.F m) K (cq q)) (algebraMap (T.F m) K ζ' ^ kk * algebraMap (T.F m) K (βq q)) =
          Mv * kyZc n j M zN gs cs.length f0 i := by exact_mod_cast hfin
      rw [hfin', hmult, hsh]
      ring
    · push Not at hq
      rw [hgam0 a b hq, Finset.sum_eq_zero fun q _ ↦ by rw [if_neg (hq q), mul_zero]]
      by_cases ha : a = 0
      · subst ha; rw [hV0z b hv]; simp
      · rw [hVz a b hv ha hq]; simp
  refine ⟨V ^ (Lf : ℤ) * U, mul_ne_zero hVL hU0, fun a b hv ↦ ?_, fun Q hQ ↦ hord Q.1 Q.2 hQ⟩
  rw [hord a b hv]
  positivity

open Classical in
/-- **Forward, the residues**: a Liouville form makes every `ρ_qⁿ A(c_q)ʲ` constant. -/
theorem ky_forward_const (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
    (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
    (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
    (n : ℕ) (hn : 0 < n) (θ : L) (hθ : θ ^ n = T.evP m A) (hM : T.MixHyp (m + 1)) (hmn : m < T.n)
    {g : LC m} (hk : ks m = .exp g) (j : ℕ) (hj0 : 0 < j) (hjn : j < n)
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hok : kxOK Fc ks m A B kt l cs = true)
    {ι : Type*} (sI : Finset ι) (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ ^ j =
      v′ + ∑ i ∈ sI, c i * logDeriv (u i)) :
    kyConst Fc ks m n j g A B kt l cs = true := by
  have hTm : T.Tr m := hTr.of_succ
  have hok' := T.kxOK_spec m hTm A B kt l cs hok
  have hx := T.krS_hx m hTr A hsq hdegA n hn θ hθ hmn hk
  obtain ⟨hb, hbm, hDR, hDoff, hbP⟩ := T.ky_data m hTr A hsq hdegA n hn θ hθ B kt l cs j
  set cq : Fin cs.length → T.F m := fun q ↦ (T.MP m hTm).sem (kqC Fc ks m cs q) with hcq
  have hRne : ∀ q : Fin cs.length, (X ^ kt * GPoly.toPoly (T.MP m hTm)
      (prodLinG Fc ks m (cs.eraseIdx q))).eval (cq q) ≠ 0 := fun q ↦ T.kx_Rne m hTm A B kt l cs hok q
  have hbadc : ∀ q : Fin cs.length, ¬ (algebraMap (T.F m) (AlgebraicClosure (T.F m)) (cq q) = 0) :=
    fun q h ↦ (hok'.2 q q.2).1 ((algebraMap (T.F m) _).injective (by rw [h, map_zero]))
  have hpc : ∀ q : Fin cs.length, (T.krS m hTr A hsq hdegA n hn θ hθ).p.eval (cq q) ≠ 0 :=
    fun q ↦ (hok'.2 q q.2).2.2.1
  have hu' : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯ :=
    fun i hi ↦ ⟨(hu i hi).1, T.krS_mem m hTr A hsq hdegA n hn θ hθ _ (hu i hi).2⟩
  refine T.kyConst_of m hTm n j g A B kt l cs fun q hq ↦ ?_
  obtain ⟨ξ, hξ, hξe⟩ := (T.krS m hTr A hsq hdegA n hn θ hθ).ky_resid_const
    (K := AlgebraicClosure (T.F m)) _ hx (fun c ↦ deriv_algebraMap c) (· = 0) (T.kxS_good m hM hk)
    (T.keS_constC m) cq hbadc (GPoly.toPoly (T.MP m hTm) B) l _ hb _ _ hDR hRne hDoff hbP hpc j hj0 hjn
    hbm sI c u hcd hu' v (T.krS_mem m hTr A hsq hdegA n hn θ hθ _ hv) heq ⟨q, hq⟩
  have hden : (T.MP m hTm).sem (kxD Fc ks m g cs q) * (T.MP m hTm).sem (kxR Fc ks m A kt l cs q) =
      (((Polynomial.C (T.val m g)′ * X).eval (cq ⟨q, hq⟩) - (cq ⟨q, hq⟩)′) *
        (X ^ kt * GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q)) *
          (T.krS m hTr A hsq hdegA n hn θ hθ).p ^ l).eval (cq ⟨q, hq⟩)) := by
    rw [T.sem_kxD m hTm, T.sem_kxR m hTm, T.sem_eq_val m hTm g]
    have hSp : (T.krS m hTr A hsq hdegA n hn θ hθ).p = GPoly.toPoly (T.MP m hTm) A := rfl
    rw [hSp]
    simp only [eval_mul, eval_pow, eval_X, eval_C, hcq]
    ring
  have hD0 : (T.MP m hTm).sem (kxD Fc ks m g cs q) ≠ 0 := T.kxD_ne m hM hk cs q (hok'.2 q hq).1
  have hR0 := (hok'.2 q hq).2.1
  have hval : (T.MP m hTm).sem (kyQ Fc ks m n j g A B kt l cs q) = ξ := by
    rw [T.sem_kyQ m hTm, T.sem_kyRho m hTm, div_pow]
    have hdn : ((T.MP m hTm).sem (kxD Fc ks m g cs q) * (T.MP m hTm).sem (kxR Fc ks m A kt l cs q)) ^ n
        ≠ 0 := pow_ne_zero _ (mul_ne_zero hD0 hR0)
    field_simp
    rw [hden]
    have hSp : (T.krS m hTr A hsq hdegA n hn θ hθ).p = GPoly.toPoly (T.MP m hTm) A := rfl
    have := hξe
    have hSn : (T.krS m hTr A hsq hdegA n hn θ hθ).n = n := rfl
    rw [hSp, hSn] at this
    rw [hSp]
    simp only [hcq] at this ⊢
    linear_combination this
  rw [hval, hξ]

end MTower

end Curves.MT
