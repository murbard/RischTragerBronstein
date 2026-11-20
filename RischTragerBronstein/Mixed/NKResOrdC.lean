import RischTragerBronstein.Mixed.NKResOrd

/-!
# Code-level certificate: residues at infinity matched by units, several segments

`multiMatchCk`: the place data of `multiResCk`, units `Uᵢ/dᵢ` (codes), their `τ`-orders `oₖₚᵢ`
along every place (`segResCK` coefficient windows: zero below `o`, non-zero at `o`), rationals
`κᵢ`, and the derivative test on `resₖₚ(f) + (∑ κᵢ (oₖₚᵢ + e deg dᵢ)/e) η`. `res_match_multiC`:
then `[T^N] f + (∑ κᵢ ord wᵢ)/N · η` is a derivative along a branch system above infinity
(`res_match_multi`).
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Tower.PrimN GTors Differential

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- The coefficient window `∑ⱼ ∑ₗ uⱼₗ [τ^{κ + e l + s j}] Θʲ` (`0` at negative indices). -/
def segResCK (m e : ℕ) (s κ : ℤ) (fp : List (GPoly (LC m))) (Θ : GPoly (LC m)) : LC m :=
  lsumC (MO Fc ks m) ((List.range fp.length).map fun j ↦
    lsumC (MO Fc ks m) ((List.range (fp.getD j []).length).map fun l ↦
      (MO Fc ks m).mul ((fp.getD j []).getD l (MO Fc ks m).zero)
        (if 0 ≤ κ + e * l + s * j then
          (powG (MO Fc ks m) Θ j).getD (κ + e * l + s * j).toNat (MO Fc ks m).zero
        else (MO Fc ks m).zero)))

/-- A lower bound below which every window index is negative. -/
def segLowC (e : ℕ) (s : ℤ) (fp : List (GPoly (LC m))) : ℤ :=
  -((e : ℤ) * ((fp.map List.length).sum : ℕ) + |s| * fp.length) - 1

/-- **The order check** of a unit code `U` along a place: zero windows on `[low, o)`, non-zero at
`o`, and enough precision. -/
def ordCk (m e : ℕ) (s : ℤ) (M : ℕ) (U : List (GPoly (LC m))) (Θ : GPoly (LC m)) (o : ℤ) : Bool :=
  !(MO Fc ks m).isZero (segResCK Fc ks m e s o U Θ) &&
  (List.range (o - segLowC e s U).toNat).all (fun t ↦
    (MO Fc ks m).isZero (segResCK Fc ks m e s (segLowC e s U + t) U Θ)) &&
  (List.range U.length).all fun j ↦ (List.range (max 1 (U.getD j []).length)).all fun l ↦
    decide (o + e * l + s * j < M)

/-- **The residue-matching certificate for several segments.** -/
def multiMatchCk (m : ℕ) (η : LC m) (Pp : List (GPoly (LC m))) (segs : List (SegRC m))
    (βs : List (List (LC m))) (Θs : List (List (GPoly (LC m)))) (M : ℕ)
    (fp : List (GPoly (LC m))) (Us : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
    (os : List (List (List ℤ))) (κs : List ℚ) : Bool :=
  let O := MO Fc ks m
  let n := Pp.length
  (List.range Us.length).all (fun i ↦ 0 < (ds.getD i []).length &&
    !O.isZero ((ds.getD i []).getD ((ds.getD i []).length - 1) O.zero)) &&
  (List.range segs.length).all fun k ↦
    let sg := segs.getD k (segRD Fc ks m)
    decide ((βs.getD k []).length = sg.2.2.2.2.length) &&
    (List.range sg.2.2.2.2.length).all (fun p ↦
      let β := (βs.getD k []).getD p O.zero
      let Θ := (Θs.getD k []).getD p []
      let o := (os.getD k []).getD p []
      let corr : LC m := lsumC O ((List.range Us.length).map fun i ↦
        mcst Fc ks m ((κs.getD i 0) * ((o.getD i 0 + sg.1 * ((ds.getD i []).length - 1) : ℤ) : ℚ) /
          sg.1))
      O.isZero (O.add (powC O β sg.1) (O.neg (sg.2.2.2.2.getD p O.zero))) &&
      O.isZero (O.add (Θ.getD 0 O.zero) (O.neg β)) &&
      truncOKC Fc ks m M (segEvalC Fc ks m sg.1 sg.2.1 sg.2.2.1 Pp Θ) &&
      !O.isZero (evalLC Fc ks m (GPoly.derivX O (segResidC Fc ks m sg.1 sg.2.1 sg.2.2.1 Pp)) β) &&
      derivTestC Fc ks lv m (O.add (segResC Fc ks m sg.1 sg.2.1 n fp Θ) (O.mul corr η)) &&
      (List.range Us.length).all fun i ↦
        ordCk Fc ks m sg.1 sg.2.1 M (Us.getD i []) Θ (o.getD i 0)) &&
    (List.range n).all fun j ↦ (List.range (max 1 (fp.getD j []).length)).all fun l ↦
      decide ((sg.1 : ℤ) + sg.1 * l + sg.2.1 * j < M)

end Codes

section Sem

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {m : ℕ} {F : Type*} [Field F] [Differential F] (M : CField (LC m) F (MO Fc ks m))

lemma sem_segResCK (e : ℕ) (s κ : ℤ) (fp : List (GPoly (LC m))) (Θ : GPoly (LC m)) :
    M.sem (segResCK Fc ks m e s κ fp Θ) = ∑ j ∈ Finset.range fp.length,
      ∑ l ∈ Finset.range (fp.getD j []).length, M.sem ((fp.getD j []).getD l (MO Fc ks m).zero) *
        (if 0 ≤ κ + e * l + s * j then
          ((GPoly.toPoly M Θ) ^ j).coeff (κ + e * l + s * j).toNat else 0) := by
  unfold segResCK
  rw [sem_lsumC, List.map_map, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Function.comp_apply]
  rw [sem_lsumC, List.map_map, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  simp only [Function.comp_apply]
  rw [M.sem_mul]
  congr 1
  split_ifs
  · rw [← coeff_toPoly_sem, toPoly_powGXP]
  · exact M.sem_zero

lemma segLowC_neg (e : ℕ) (s κ : ℤ) (fp : List (GPoly (LC m))) (hκ : κ < segLowC e s fp)
    (j : ℕ) (hj : j < fp.length) (l : ℕ) (hl : l < (fp.getD j []).length) :
    κ + e * l + s * j < 0 := by
  have hlen : (fp.getD j []).length ≤ (fp.map List.length).sum := by
    apply List.le_sum_of_mem
    rw [List.mem_map]
    exact ⟨fp.getD j [], by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj, rfl⟩
  have h1 : (e : ℤ) * l ≤ e * ((fp.map List.length).sum : ℕ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast (show l ≤ _ by omega)) (by positivity)
  have h2 : s * j ≤ |s| * fp.length := by
    calc s * j ≤ |s| * j := mul_le_mul_of_nonneg_right (le_abs_self s) (by positivity)
      _ ≤ |s| * fp.length := mul_le_mul_of_nonneg_left (by exact_mod_cast hj.le) (abs_nonneg s)
  unfold segLowC at hκ
  linarith

/-- The `θ`-polynomial of a list of codes. -/
noncomputable def thetaP (U : List (GPoly (LC m))) : F[X][X] :=
  ∑ j ∈ Finset.range U.length, Polynomial.C (GPoly.toPoly M (U.getD j [])) * X ^ j

lemma coeff_thetaP (U : List (GPoly (LC m))) (j : ℕ) :
    (thetaP M U).coeff j = if j < U.length then GPoly.toPoly M (U.getD j []) else 0 := by
  classical
  rw [thetaP, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

lemma sum_thetaP (U : List (GPoly (LC m))) (g : ℕ → ℕ → F) :
    ∑ j ∈ Finset.range U.length, ∑ l ∈ Finset.range (U.getD j []).length,
      M.sem ((U.getD j []).getD l (MO Fc ks m).zero) * g j l =
    ∑ j ∈ Finset.range ((thetaP M U).natDegree + 1),
      ∑ l ∈ Finset.range (((thetaP M U).coeff j).natDegree + 1),
        ((thetaP M U).coeff j).coeff l * g j l := by
  classical
  have hstep : ∀ j ∈ Finset.range U.length,
      ∑ l ∈ Finset.range (U.getD j []).length, M.sem ((U.getD j []).getD l (MO Fc ks m).zero) *
        g j l = ∑ l ∈ Finset.range (((thetaP M U).coeff j).natDegree + 1),
          ((thetaP M U).coeff j).coeff l * g j l := by
    intro j hj
    rw [coeff_thetaP, if_pos (Finset.mem_range.mp hj)]
    exact sum_toPoly_coeff M _ _
  rw [Finset.sum_congr rfl hstep]
  have hzero : ∀ j, U.length ≤ j → ∑ l ∈ Finset.range (((thetaP M U).coeff j).natDegree + 1),
      ((thetaP M U).coeff j).coeff l * g j l = 0 := by
    intro j hj
    rw [coeff_thetaP, if_neg (by omega)]
    simp
  rcases Nat.eq_zero_or_pos U.length with h0 | hpos
  · rw [h0, Finset.sum_range_zero]
    symm
    refine Finset.sum_eq_zero fun j _ ↦ hzero j (by omega)
  · have hd : (thetaP M U).natDegree < U.length := by
      refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := U.length - 1) fun j hj ↦ ?_)
        (by omega)
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [natDegree_X_pow]; have := Finset.mem_range.mp hj; omega
    symm
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j hj hnj ↦ ?_
    rw [coeff_eq_zero_of_natDegree_lt (by simpa using hnj)]
    simp

end Sem

universe u

section Tower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 1000000 in
/-- **A passing residue-matching certificate**: along a branch system above infinity,
`[T^N] f + (∑ κᵢ ord wᵢ)/N · η` is a derivative, `wᵢ = Uᵢ/dᵢ` the unit codes. -/
theorem res_match_multiC (m : ℕ) (h : T.Tr m) {L' : Type*} [Field L'] [CharZero L']
    [Algebra (T.F m) L'] [Differential L'] [DifferentialAlgebra (T.F m) L']
    (S : CurveData (T.F m) L') (Pp : List (GPoly (LC m))) (hSF : S.F = T.nkF m h Pp)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true)
    (βs : List (List (LC m))) (Θs : List (List (GPoly (LC m)))) (M : ℕ) (fp : List (GPoly (LC m)))
    (η : LC m) (Us : List (List (GPoly (LC m)))) (ds : List (GPoly (LC m)))
    (os : List (List (List ℤ))) (κs : List ℚ)
    (hck : multiMatchCk Fc ks lv m η Pp segs βs Θs M fp Us ds os κs = true)
    (hU0 : ∀ i : Fin Us.length, S.evT (thetaP (T.MP m h) (Us.getD i [])) ≠ 0)
    {Cs : Type*} [Field Cs] [CharZero Cs] (ι : Cs →+* T.F m)
    (hrde : RdeSpecK ι (T.MP m h) ((T.MP m h).sem (fCode (MO Fc ks m) ⟨(MO Fc ks m).one, []⟩))
      (prdeC Fc ks lv m ⟨(MO Fc ks m).one, []⟩))
    {Kb : Type*} [Field Kb] [CharZero Kb] [Algebra (T.F m) Kb] [Differential Kb] [IsAlgClosed Kb]
    (hK : ∀ c : T.F m, (algebraMap (T.F m) Kb c)′ = algebraMap (T.F m) Kb c′) :
    ∃ (N : ℕ) (hN : 0 < N) (li : List (LaurentSeries Kb)) (hli : S.F.map (infSub (K := Kb) N) =
      (li.map fun r ↦ X - Polynomial.C r).prod),
      ∀ r (hr : r ∈ li), ∃ b : Kb, (S.embG (infSub N) (infSub_injective N hN) r
        (S.root_of_mem hli hr) (S.evT (∑ j ∈ Finset.range Pp.length,
          Polynomial.C (GPoly.toPoly (T.MP m h) (fp.getD j [])) * X ^ j))).coeff (N : ℤ) +
        (∑ i : Fin Us.length, ((κs.getD i 0 : ℚ) : Kb) * ((S.embG (infSub N) (infSub_injective N hN) r
          (S.root_of_mem hli hr) (S.evT (thetaP (T.MP m h) (Us.getD i [])) /
            S.evT (Polynomial.C (GPoly.toPoly (T.MP m h) (ds.getD i []))))).order : Kb)) / N *
          algebraMap (T.F m) Kb ((T.MP m h).sem η) = b′ := by
  classical
  obtain ⟨q, hq, hn0, hePos, hgcd, hdecS, hcne, hΓ, hbd, hres, htop, hchain, hlast⟩ :=
    T.multiShapeR_spec m h Pp segs hms
  simp only [multiMatchCk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true'] at hck
  obtain ⟨hds, hck⟩ := hck
  set sg : Fin (q + 1) → SegRC m := fun k ↦ segs.getD k (segRD Fc ks m) with hsg
  set n := Pp.length with hn
  set Q : (T.F m)[X][X] := ∑ j ∈ Finset.range n,
    Polynomial.C (GPoly.toPoly (T.MP m h) (fp.getD j [])) * X ^ j with hQ
  have hQc : ∀ j, Q.coeff j = if j < n then GPoly.toPoly (T.MP m h) (fp.getD j []) else 0 := by
    intro j
    rw [hQ, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  have hQd : Q.natDegree < n := by
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := n - 1) fun j hj ↦ ?_)
      (by omega)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_X_pow]; have := Finset.mem_range.mp hj; omega
  have hk : ∀ k : Fin (q + 1), (k : ℕ) < segs.length := fun k ↦ by rw [hq]; exact k.2
  -- the data per place
  set Γ : Fin (q + 1) → List (T.F m) := fun k ↦ (sg k).2.2.2.2.map (T.MP m h).sem with hΓdef
  have hΓlen : ∀ k, (Γ k).length = (sg k).2.2.2.2.length := fun k ↦ List.length_map _
  set β : ∀ k, Fin (Γ k).length → T.F m := fun k i ↦ (T.MP m h).sem ((βs.getD k []).getD i (MO Fc ks m).zero) with hβ
  set Θt : ∀ k, Fin (Γ k).length → (T.F m)[X] := fun k i ↦
    GPoly.toPoly (T.MP m h) ((Θs.getD k []).getD i []) with hΘt
  have hplace : ∀ k (i : Fin (Γ k).length), _ := fun k i ↦
    (hck k (hk k)).1.2 i (by rw [← hΓlen]; exact i.2)
  have hβe : ∀ k (i : Fin (Γ k).length), β k i ^ (sg k).1 = (Γ k)[(i : ℕ)] := by
    intro k i
    have A := (hplace k i).1.1.1.1.1
    rw [(T.MP m h).isZero_iff, (T.MP m h).sem_add, (T.MP m h).sem_neg, sem_powC, add_neg_eq_zero] at A
    simp only [hβ, hΓdef]
    rw [A, List.getElem_map, List.getD_eq_getElem]
  have hΘ0s : ∀ k (i : Fin (Γ k).length),
      (T.MP m h).sem (((Θs.getD k []).getD i []).getD 0 (MO Fc ks m).zero) = β k i := by
    intro k i
    have B := (hplace k i).1.1.1.1.2
    rw [(T.MP m h).isZero_iff, (T.MP m h).sem_add, (T.MP m h).sem_neg, add_neg_eq_zero] at B
    exact B
  have hΘ0 : ∀ k (i : Fin (Γ k).length), (Θt k i).coeff 0 = β k i := fun k i ↦ by
    rw [hΘt, coeff_toPoly_sem]; exact hΘ0s k i
  have hu : ∀ k (i : Fin (Γ k).length),
      ((derivative (segPoly (sg k).1 (sg k).2.1 (sg k).2.2.1 S.F)).eval (Θt k i)).coeff 0 ≠ 0 := by
    intro k i
    have D := (hplace k i).1.1.2
    rw [hSF, hΘt]
    beta_reduce
    rw [T.deriv_segPoly_nkF m h Pp, sem_evalLC, hΘ0s k i, hβ]
    rw [← sem_evalLC]
    intro h0
    rw [← (T.MP m h).isZero_iff] at h0
    rw [h0] at D
    exact absurd D (by simp)
  have hM : ∀ k (i : Fin (Γ k).length), ∀ n' < M,
      ((segPoly (sg k).1 (sg k).2.1 (sg k).2.2.1 S.F).eval (Θt k i)).coeff n' = 0 := by
    intro k i n' hn'
    have C := (hplace k i).1.1.1.2
    rw [hSF, hΘt]
    beta_reduce
    rw [T.eval_segPoly_nkF m h Pp, coeff_toPoly_sem]
    exact ((T.MP m h).isZero_iff _).mp (List.all_eq_true.mp C n' (List.mem_range.mpr hn'))
  have hMb : ∀ k, ∀ j ≤ Q.natDegree, ∀ l ≤ (Q.coeff j).natDegree,
      ((sg k).1 : ℤ) + (sg k).1 * l + (sg k).2.1 * j < M := by
    intro k j hj l hl
    have hjn : j < n := lt_of_le_of_lt hj hQd
    rw [hQc, if_pos hjn] at hl
    have h1 := natDegree_toPoly_le (T.MP m h) (fp.getD j [])
    exact (hck k (hk k)).2 j hjn l (by omega)
  -- the units
  set Uu : Fin Us.length → (T.F m)[X][X] := fun i ↦ thetaP (T.MP m h) (Us.getD i []) with hUu
  set dd : Fin Us.length → (T.F m)[X] := fun i ↦ GPoly.toPoly (T.MP m h) (ds.getD i []) with hdd
  have hdsi : ∀ i : Fin Us.length, 0 < (ds.getD i []).length ∧
      (T.MP m h).sem ((ds.getD i []).getD ((ds.getD i []).length - 1) (MO Fc ks m).zero) ≠ 0 :=
    fun i ↦ by
      obtain ⟨h1, h2⟩ := hds i i.2
      refine ⟨h1, fun h0 ↦ ?_⟩
      rw [← (T.MP m h).isZero_iff] at h0
      rw [h0] at h2
      exact absurd h2 (by simp)
  have hddeg : ∀ i : Fin Us.length, (dd i).natDegree = (ds.getD i []).length - 1 := fun i ↦ by
    refine le_antisymm (natDegree_toPoly_le _ _) (le_natDegree_of_ne_zero ?_)
    rw [hdd]; beta_reduce
    rw [coeff_toPoly_sem]; exact (hdsi i).2
  have hdd0 : ∀ i : Fin Us.length, dd i ≠ 0 := fun i h0 ↦ by
    have := congrArg (fun p ↦ p.coeff ((ds.getD i []).length - 1)) h0
    simp only [hdd, coeff_toPoly_sem, Polynomial.coeff_zero] at this
    exact (hdsi i).2 this
  set o : ∀ k, Fin (Γ k).length → Fin Us.length → ℤ := fun k p i ↦
    ((os.getD k []).getD p []).getD i 0 with ho
  have hUlen : ∀ i : Fin Us.length, 0 < (Us.getD i []).length := fun i ↦ by
    by_contra h0
    have hnil : Us.getD i [] = [] := List.length_eq_zero_iff.mp (by omega)
    apply hU0 i
    rw [thetaP, hnil, List.length_nil, Finset.sum_range_zero, CurveData.evT, Polynomial.map_zero,
      eval_zero]
  have hord : ∀ k (p : Fin (Γ k).length) (i : Fin Us.length),
      ordCk Fc ks m (sg k).1 (sg k).2.1 M (Us.getD i []) ((Θs.getD k []).getD p []) (o k p i) =
        true := fun k p i ↦ (hplace k p).2 i i.2
  have hprec : ∀ k p i, ∀ j ≤ (Uu i).natDegree, ∀ l ≤ ((Uu i).coeff j).natDegree,
      o k p i + (sg k).1 * l + (sg k).2.1 * j < M := by
    intro k p i j hj l hl
    have hc := hord k p i
    simp only [ordCk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
    have hjl : j < (Us.getD i []).length := by
      have hd : (Uu i).natDegree < (Us.getD i []).length := by
        refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _
          (n := (Us.getD i []).length - 1) fun j hj ↦ ?_) (by have := hUlen i; omega)
        refine (natDegree_C_mul_le _ _).trans ?_
        rw [natDegree_X_pow]; have := Finset.mem_range.mp hj; omega
      omega
    rw [hUu] at hl; beta_reduce at hl
    rw [coeff_thetaP, if_pos hjl] at hl
    have h1 := natDegree_toPoly_le (T.MP m h) ((Us.getD i []).getD j [])
    exact hc.2 j hjl l (by omega)
  have hwin : ∀ k p i (κ : ℤ), ∑ j ∈ Finset.range ((Uu i).natDegree + 1),
      ∑ l ∈ Finset.range (((Uu i).coeff j).natDegree + 1), ((Uu i).coeff j).coeff l *
        (if 0 ≤ κ + (sg k).1 * l + (sg k).2.1 * j then
          ((Θt k p) ^ j).coeff (κ + (sg k).1 * l + (sg k).2.1 * j).toNat else 0) =
      (T.MP m h).sem (segResCK Fc ks m (sg k).1 (sg k).2.1 κ (Us.getD i [])
        ((Θs.getD k []).getD p [])) := by
    intro k p i κ
    rw [sem_segResCK, hUu]
    beta_reduce
    rw [← sum_thetaP]
  have ho1 : ∀ k p i, ∑ j ∈ Finset.range ((Uu i).natDegree + 1),
      ∑ l ∈ Finset.range (((Uu i).coeff j).natDegree + 1), ((Uu i).coeff j).coeff l *
        (if 0 ≤ o k p i + (sg k).1 * l + (sg k).2.1 * j then
          ((Θt k p) ^ j).coeff (o k p i + (sg k).1 * l + (sg k).2.1 * j).toNat else 0) ≠ 0 := by
    intro k p i
    rw [hwin]
    have hc := hord k p i
    simp only [ordCk, Bool.and_eq_true, Bool.not_eq_true'] at hc
    intro h0
    rw [← (T.MP m h).isZero_iff] at h0
    rw [h0] at hc
    exact absurd hc.1.1 (by simp)
  have ho0 : ∀ k p i, ∀ κ < o k p i, ∑ j ∈ Finset.range ((Uu i).natDegree + 1),
      ∑ l ∈ Finset.range (((Uu i).coeff j).natDegree + 1), ((Uu i).coeff j).coeff l *
        (if 0 ≤ κ + (sg k).1 * l + (sg k).2.1 * j then
          ((Θt k p) ^ j).coeff (κ + (sg k).1 * l + (sg k).2.1 * j).toNat else 0) = 0 := by
    intro k p i κ hκ
    rw [hwin]
    by_cases hlow : κ < segLowC (sg k).1 (sg k).2.1 (Us.getD i [])
    · rw [sem_segResCK]
      refine Finset.sum_eq_zero fun j hj ↦ Finset.sum_eq_zero fun l hl ↦ ?_
      rw [if_neg (by
        have := segLowC_neg (sg k).1 (sg k).2.1 κ (Us.getD i []) hlow j (Finset.mem_range.mp hj) l
          (Finset.mem_range.mp hl)
        omega), mul_zero]
    · push_neg at hlow
      have hc := hord k p i
      simp only [ordCk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
      have ht := hc.1.2 (κ - segLowC (sg k).1 (sg k).2.1 (Us.getD i [])).toNat (by omega)
      rw [Int.toNat_of_nonneg (by omega), add_sub_cancel] at ht
      exact ((T.MP m h).isZero_iff _).mp ht
  have hz : ∀ k (i : Fin (Γ k).length), ∃ z : T.F m,
      z′ = (T.MP m h).sem (segResC Fc ks m (sg k).1 (sg k).2.1 n fp ((Θs.getD k []).getD i [])) +
        (∑ ii : Fin Us.length, (((κs.getD ii 0 : ℚ) * ((o k i ii + (sg k).1 * ((ds.getD ii []).length - 1) : ℤ) : ℚ) /
          (sg k).1 : ℚ) : T.F m)) * (T.MP m h).sem η := by
    intro k i
    obtain ⟨z, hz⟩ := derivTestC_sound ι (T.MP m h) hrde _ (hplace k i).1.2
    refine ⟨z, ?_⟩
    rw [hz, (T.MP m h).sem_add, (T.MP m h).sem_mul, sem_lsumC, List.map_map,
      ← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
      ← Fin.sum_univ_eq_sum_range (fun ii ↦ ((T.MP m h).sem ∘ fun ii ↦ mcst Fc ks m _) ii)]
    congr 2
    refine Finset.sum_congr rfl fun ii _ ↦ ?_
    simp only [Function.comp_apply]
    rw [T.sem_mcst m h]
  choose z hz using hz
  have hz' : ∀ k (i : Fin (Γ k).length), (z k i)′ = ∑ j ∈ Finset.range (Q.natDegree + 1),
      ∑ l ∈ Finset.range ((Q.coeff j).natDegree + 1), (Q.coeff j).coeff l *
        (if 0 ≤ ((sg k).1 : ℤ) + (sg k).1 * l + (sg k).2.1 * j then
          ((Θt k i) ^ j).coeff (((sg k).1 : ℤ) + (sg k).1 * l + (sg k).2.1 * j).toNat else 0) +
      (∑ ii : Fin Us.length, (((κs.getD ii 0 : ℚ)) : T.F m) * ((o k i ii + (sg k).1 * (dd ii).natDegree : ℤ) : T.F m)) /
        ((sg k).1 : T.F m) * (T.MP m h).sem η := by
    intro k i
    rw [hz k i]
    congr 1
    swap
    · congr 1
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun ii _ ↦ ?_
      rw [hddeg ii]
      have he0 : ((sg k).1 : T.F m) ≠ 0 := by exact_mod_cast (hePos k).ne'
      have hle := (hdsi ii).1
      push_cast
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [sem_segResC]
    have hstep : ∀ j ∈ Finset.range n,
        ∑ l ∈ Finset.range (fp.getD j []).length, (T.MP m h).sem ((fp.getD j []).getD l (MO Fc ks m).zero) *
          (if 0 ≤ ((sg k).1 : ℤ) + (sg k).1 * l + (sg k).2.1 * j then
            ((Θt k i) ^ j).coeff (((sg k).1 : ℤ) + (sg k).1 * l + (sg k).2.1 * j).toNat else 0) =
        ∑ l ∈ Finset.range ((Q.coeff j).natDegree + 1), (Q.coeff j).coeff l *
          (if 0 ≤ ((sg k).1 : ℤ) + (sg k).1 * l + (sg k).2.1 * j then
            ((Θt k i) ^ j).coeff (((sg k).1 : ℤ) + (sg k).1 * l + (sg k).2.1 * j).toNat else 0) := by
      intro j hj
      rw [hQc, if_pos (Finset.mem_range.mp hj)]
      exact sum_toPoly_coeff (T.MP m h) _ _
    rw [Finset.sum_congr rfl hstep]
    symm
    refine Finset.sum_subset (Finset.range_subset_range.mpr (show Q.natDegree + 1 ≤ n by omega))
      fun j _ hnj ↦ ?_
    rw [coeff_eq_zero_of_natDegree_lt (by simpa using hnj)]
    simp
  have hbd' : ∀ k : Fin (q + 1), ∀ i ≤ S.F.natDegree, S.F.coeff i ≠ 0 →
      ((sg k).1 : ℤ) * (S.F.coeff i).natDegree + i * (sg k).2.1 ≤ (sg k).2.2.1 := by
    rw [hSF]; exact hbd
  have hres' : ∀ k : Fin (q + 1), ∑ i ∈ Finset.range (S.F.natDegree + 1),
      Polynomial.C (coeffZe (S.F.coeff i) (sg k).1 ((sg k).2.2.1 - i * (sg k).2.1)) * X ^ i =
        Polynomial.C ((T.MP m h).sem (sg k).2.2.2.1) * X ^ (loRC segs k) *
          ((Γ k).map fun γ ↦ X ^ (sg k).1 - Polynomial.C γ).prod := by
    rw [hSF]; exact hres
  have htop' : loRC segs ((0 : Fin (q + 1)) : ℕ) + (sg 0).1 * (Γ 0).length = S.F.natDegree := by
    rw [hSF]; exact htop
  obtain ⟨N, hN, li, hli, hzr⟩ := S.res_match_multi (Kb := Kb) (fun k ↦ (sg k).1) hePos
    (fun k ↦ (sg k).2.1) hgcd hdecS (fun k ↦ (sg k).2.2.1) (fun k ↦ (T.MP m h).sem (sg k).2.2.2.1) hcne
    (fun k ↦ loRC segs k) Γ hΓ hbd' hres' htop' hchain hlast β hβe Θt hΘ0 hu M hM Q hMb z Uu dd
    hdd0 hU0 o hprec ho1 ho0 (fun i ↦ κs.getD i 0) ((T.MP m h).sem η) hz' hK
  exact ⟨N, hN, li, hli, hzr⟩


end MTower

end Tower

end Curves.MT
