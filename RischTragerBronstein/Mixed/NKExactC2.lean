import RischTragerBronstein.Mixed.NKExact

/-!
# The exact-part test with a parameter

`exactC2 P f g`: is `f − c g` exact (`= (∑ Yᵢ θⁱ)′`) for some constant `c`? The coupled system is
solved with the two right-hand sides `f, g` (`primSysC` returns a basis of the solutions
`(e₀, e₁, Y)` of `Y′ + A Y = e₀ f + e₁ g`); the answer is `true` iff a basis element has `e₀ ≠ 0`
(`exactC2_correct`). Used for the logarithmic part `c u₀′/u₀` of a curve with a non-constant unit.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM CPoly

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The exact-part test with a parameter** at a logarithmic level. -/
def exactC2 (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (P : GPoly (LC (m + 1))) (f g : List (LC (m + 1))) : Option Bool :=
  let O1 := (MO Fc ks (m + 1)).normalizeBy (redL Fc ks (m + 1))
  let O := MO Fc ks m
  let N := P.length - 1
  if !(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || N = 0 then none else
  match dThetaC O1 P with
  | none => none
  | some dθ =>
    let M : List (List (LC (m + 1))) := (List.range N).map fun i ↦
      (List.range N).map fun j ↦ (dPowC O1 P dθ i).getD j O1.zero
    let ent : List (LC (m + 1)) := M.flatten ++ f ++ g
    let q := lcmGL O (ent.map Prod.snd)
    let cofs := ent.map fun c ↦ cofC O q c.2
    if !(cofs.all Prod.fst) then none else
    let num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2
    let A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦ num ((M.getD i []).getD j O1.zero)
    let G : Fin N → GPoly (LC m) := fun j ↦ num (f.getD j O1.zero)
    let Gg : Fin N → GPoly (LC m) := fun j ↦ num (g.getD j O1.zero)
    match primSysC Fc ks m η lim N A0 q q [G, Gg] with
    | none => none
    | some r => some (r.2.any fun b ↦ b.1.getD 0 0 != 0)

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) (m : ℕ)

set_option maxHeartbeats 4000000 in
/-- **Correctness of the parametric exact-part test.** -/
theorem exactC2_correct (hm : m < T.n) (h1 : T.Tr (m + 1)) (htr : Transcendental (T.F m) (T.ts m))
    {η : LC m} (hk : ks m = .prim η) (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h1.of_succ) lim)
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range (P.length - 1), (a j : L) * θ ^ j = 0 →
      ∀ j < P.length - 1, a j = 0)
    (g : List (LC (m + 1))) (res : Bool) (hres : exactC2 Fc ks m η lim P f g = some res) :
    res = true ↔ ∃ (c : Cc) (Y : ℕ → T.F (m + 1)),
      (∑ i ∈ Finset.range (P.length - 1), (Y i : L) * θ ^ i)′ =
        ∑ j ∈ Finset.range (P.length - 1),
          (((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) -
            algebraMap Cc L c * ((T.MPr (m + 1) h1).sem (g.getD j (MOr Fc ks (m + 1)).zero) : L)) *
            θ ^ j := by
  classical
  unfold exactC2 at hres
  simp only at hres
  split_ifs at hres with hPc
  split at hres
  · exact absurd hres (by simp)
  rename_i dθ hd
  split_ifs at hres with hcof
  split at hres
  · exact absurd hres (by simp)
  rename_i r hr
  obtain rfl := Option.some.inj hres
  set O1 := MOr Fc ks (m + 1) with hO1
  set O := MO Fc ks m with hO
  set M1 := T.MPr (m + 1) h1 with hM1
  set h0 := h1.of_succ with hh0
  set M := T.MP m h0 with hM
  -- `P` is monic of degree `(P.length - 1)`
  have hPc' : O1.isZero (O1.add (P.getD (P.length - 1) O1.zero) (O1.neg O1.one)) = true ∧ (P.length - 1) ≠ 0 := by
    revert hPc
    cases O1.isZero (O1.add (P.getD (P.length - 1) O1.zero) (O1.neg O1.one)) <;> simp
  have hlead : M1.sem (P.getD (P.length - 1) O1.zero) = 1 := by
    have := (M1.isZero_iff _).mp hPc'.1
    rw [M1.sem_add, M1.sem_neg, M1.sem_one, add_neg_eq_zero] at this
    exact this
  have hPlen : P.length = (P.length - 1) + 1 := by
    have : P ≠ [] := fun h0' ↦ by rw [h0'] at hPc'; exact hPc'.2 rfl
    have := List.length_pos_of_ne_nil this
    omega
  have hPdeg : (GPoly.toPoly M1 P).natDegree = (P.length - 1) := by
    apply le_antisymm
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [coeff_toPoly_sem, List.getD_eq_default _ _ (by
        have : (P.length - 1) < k := by exact_mod_cast hk
        omega), M1.sem_zero]
    · exact le_natDegree_of_ne_zero (by rw [coeff_toPoly_sem, hlead]; exact one_ne_zero)
  have hPm : (GPoly.toPoly M1 P).Monic := by
    rw [Monic, leadingCoeff, hPdeg, coeff_toPoly_sem, hlead]
  set Ml : List (List (LC (m + 1))) := (List.range (P.length - 1)).map fun i ↦
    (List.range (P.length - 1)).map fun j ↦ (dPowC O1 P dθ i).getD j O1.zero with hMl
  set ent : List (LC (m + 1)) := Ml.flatten ++ f ++ g with hent
  set q := lcmGL O (ent.map Prod.snd) with hq
  set num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2 with hnum
  have hqmon := isMonicC_spec M q (primSysC_monic hr).1
  set qs := GPoly.toPoly M q with hqs
  have hqs0 : qs ≠ 0 := hqmon.ne_zero
  have hcofs : ∀ c ∈ ent, (cofC O q c.2).1 = true := by
    have hall : (ent.map fun c ↦ cofC O q c.2).all Prod.fst = true := by
      revert hcof; cases (ent.map fun c ↦ cofC O q c.2).all Prod.fst <;> simp
    intro c hc
    exact List.all_eq_true.mp hall _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hval : ∀ c ∈ ent, (M1.sem c : T.F (m + 1)) = T.phi m (GPoly.toPoly M (num c)) / T.phi m qs :=
    fun c hc ↦ T.sem_cof m h1 htr q hqs0 c (hcofs c hc)
  have hMe : ∀ i < (P.length - 1), ∀ j < (P.length - 1), (Ml.getD i []).getD j O1.zero ∈ ent := fun i hi j hj ↦ by
    rw [hent]
    apply List.mem_append_left
    apply List.mem_append_left
    rw [List.mem_flatten]
    refine ⟨Ml.getD i [], ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by simpa [hMl] using hi)]; exact List.getElem_mem _
    · have hlen : j < (Ml.getD i []).length := by
        rw [hMl, NestTower.getD_range_map _ _ hi]; simpa using hj
      rw [List.getD_eq_getElem (Ml.getD i []) _ hlen]; exact List.getElem_mem _
  have hMθ : ∀ i < (P.length - 1), ∀ j < (P.length - 1), T.Mθ m h1 P dθ i j =
      T.phi m (GPoly.toPoly M (num ((Ml.getD i []).getD j O1.zero))) / T.phi m qs := by
    intro i hi j hj
    rw [← hval _ (hMe i hi j hj), Mθ, hMl, NestTower.getD_range_map _ _ hi,
      NestTower.getD_range_map _ _ hj]
  have hfv : ∀ j, (M1.sem (f.getD j O1.zero) : T.F (m + 1)) =
      T.phi m (GPoly.toPoly M (num (f.getD j O1.zero))) / T.phi m qs := by
    intro j
    by_cases hj : j < f.length
    · refine hval _ ?_
      rw [hent]
      apply List.mem_append_left
      apply List.mem_append_right
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
    · rw [List.getD_eq_default _ _ (by omega)]
      have hz : O1.zero.1 = [] := rfl
      rw [M1.sem_zero, hnum]
      simp only [hz, GPoly.mul, GPoly.toPoly_nil, map_zero, zero_div]
  have hgv : ∀ j, (M1.sem (g.getD j O1.zero) : T.F (m + 1)) =
      T.phi m (GPoly.toPoly M (num (g.getD j O1.zero))) / T.phi m qs := by
    intro j
    by_cases hj : j < g.length
    · refine hval _ ?_
      rw [hent]
      apply List.mem_append_right
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
    · rw [List.getD_eq_default _ _ (by omega)]
      have hz : O1.zero.1 = [] := rfl
      rw [M1.sem_zero, hnum]
      simp only [hz, GPoly.mul, GPoly.toPoly_nil, map_zero, zero_div]
  set A0f : Fin (P.length - 1) → Fin (P.length - 1) → GPoly (LC m) := fun j i ↦ num ((Ml.getD i []).getD j O1.zero) with hA0f
  set Gf : Fin (P.length - 1) → GPoly (LC m) := fun j ↦ num (f.getD j O1.zero) with hGf
  set Gg : Fin (P.length - 1) → GPoly (LC m) := fun j ↦ num (g.getD j O1.zero) with hGg
  -- the coordinate equations
  have hcoord : ∀ Y R : ℕ → T.F (m + 1),
      ((∑ i ∈ Finset.range (P.length - 1), (Y i : L) * θ ^ i)′ = ∑ j ∈ Finset.range (P.length - 1),
        ((R j : T.F (m + 1)) : L) * θ ^ j) ↔
      ∀ j < (P.length - 1), (Y j)′ + ∑ i ∈ Finset.range (P.length - 1), T.Mθ m h1 P dθ i j * Y i =
        R j := by
    intro Y R
    have hdc := T.deriv_coords m h1 θ P hP hPm dθ hd Y
    rw [hPdeg] at hdc
    rw [hdc]
    constructor
    · intro hE j hj
      have h0 := hind (fun j ↦ (Y j)′ + ∑ i ∈ Finset.range (P.length - 1), T.Mθ m h1 P dθ i j * Y i -
        R j) (by
          push_cast
          simp only [sub_mul, Finset.sum_sub_distrib]
          rw [← hE]
          push_cast
          simp only [add_mul, Finset.sum_mul]
          ring) j hj
      exact sub_eq_zero.mp h0
    · intro hE
      exact Finset.sum_congr rfl fun j hj ↦ by rw [hE j (Finset.mem_range.mp hj)]
  -- the right-hand side `f − c g`
  have hRc : ∀ c : Cc, ∑ j ∈ Finset.range (P.length - 1),
      (((M1.sem (f.getD j O1.zero) : T.F (m + 1)) : L) -
        algebraMap Cc L c * ((M1.sem (g.getD j O1.zero) : T.F (m + 1)) : L)) * θ ^ j =
      ∑ j ∈ Finset.range (P.length - 1), (((M1.sem (f.getD j O1.zero) -
        algebraMap Cc (T.F (m + 1)) c * M1.sem (g.getD j O1.zero) : T.F (m + 1)) : L)) * θ ^ j :=
    fun c ↦ Finset.sum_congr rfl fun j _ ↦ by push_cast; rfl
  constructor
  · intro hany
    obtain ⟨b, hb, he⟩ := List.any_eq_true.mp hany
    simp only [bne_iff_ne, ne_eq] at he
    set e0 : ℚ := b.1.getD 0 0 with he0
    set e1 : ℚ := b.1.getD 1 0 with he1
    have hs := T.primSysC_sound m h0 η (P.length - 1) A0f q q [Gf, Gg] lim r.1 r.2 (by simpa using hr) b
      hb
    obtain ⟨B, hB⟩ := primSysC_den hr
    have hDs : GPoly.toPoly M r.1 ≠ 0 := by
      rw [hB, T.wSys_Den m h0 η (P.length - 1) A0f q q [Gf, Gg] B]
      exact mul_ne_zero hqs0 (pow_ne_zero _ hqs0)
    have hphiD : T.phi m (GPoly.toPoly M r.1) ≠ 0 := fun h0' ↦ hDs (T.phi_injective htr
      (by rw [h0', map_zero]))
    have hphiq : T.phi m qs ≠ 0 := fun h0' ↦ hqs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hE : ((e0 : ℚ) : T.F (m + 1)) ≠ 0 := by exact_mod_cast he
    set Y : ℕ → T.F (m + 1) := fun i ↦ if hi : i < P.length - 1 then
      T.phi m (semV M b.2 ⟨i, hi⟩) / (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1))) else 0
      with hY
    refine ⟨algebraMap ℚ Cc (-(e1 / e0)), Y, ?_⟩
    rw [hRc]
    refine (hcoord Y _).mpr fun j hj ↦ ?_
    have hcF : algebraMap Cc (T.F (m + 1)) (algebraMap ℚ Cc (-(e1 / e0))) =
        ((-(e1 / e0) : ℚ) : T.F (m + 1)) := by
      rw [← IsScalarTower.algebraMap_apply]; exact eq_ratCast _ _
    rw [hcF]
    have hphi := T.sysSol_phi m hm hk h0 qs qs (semMat M A0f) _ (semV M b.2) (GPoly.toPoly M r.1)
      ⟨j, hj⟩ hs
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.range_zero,
      Finset.sum_empty, zero_add, List.getD_cons_zero, List.getD_cons_succ, map_add, map_mul, semMat,
      Matrix.of_apply] at hphi
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦ T.Mθ m h1 P dθ i j * Y i)]
    have hMθ' : ∀ i : Fin (P.length - 1),
        T.Mθ m h1 P dθ i j = T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ i)) / T.phi m qs :=
      fun i ↦ hMθ i i.2 j hj
    have hYi : ∀ i : Fin (P.length - 1), Y i = T.phi m (semV M b.2 i) /
        (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1))) := fun i ↦ by
      rw [hY]; simp only [dif_pos i.2]
    simp only [hMθ', hYi]
    have hYj : Y j = T.phi m (semV M b.2 ⟨j, hj⟩) /
        (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1))) := by
      rw [hY]; simp only [dif_pos hj]
    rw [hYj, hfv, hgv]
    have hG' : GPoly.toPoly M (Gf ⟨j, hj⟩) = GPoly.toPoly M (num (f.getD j O1.zero)) := rfl
    have hGg' : GPoly.toPoly M (Gg ⟨j, hj⟩) = GPoly.toPoly M (num (g.getD j O1.zero)) := rfl
    rw [hG', hGg'] at hphi
    rw [Derivation.leibniz_div, Derivation.leibniz, T.deriv_ratCast, smul_zero, zero_add,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    rw [T.phi_C_ratCast, T.phi_C_ratCast] at hphi
    have hsum : ∑ x : Fin (P.length - 1), T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ x)) / T.phi m qs *
        (T.phi m (semV M b.2 x) / (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1)))) =
        (∑ x, T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ x)) * T.phi m (semV M b.2 x)) /
          (T.phi m qs * (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1)))) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun x _ ↦ by field_simp
    rw [hsum, smul_eq_mul]
    have hcast : ((b.1.getD 0 0 : ℚ) : T.F (m + 1)) * (((-(e1 / e0)) : ℚ) : T.F (m + 1)) +
        ((b.1.getD 1 0 : ℚ) : T.F (m + 1)) = 0 := by
      rw [← he0, ← he1]; push_cast; field_simp; ring
    field_simp
    apply mul_left_cancel₀ hphiq
    linear_combination hphi + (T.phi m qs * T.phi m (GPoly.toPoly M r.1) ^ 2 *
      T.phi m (GPoly.toPoly M (num (g.getD j O1.zero)))) * hcast
  · rintro ⟨c, Y, hY⟩
    rw [hRc] at hY
    have heq := (hcoord Y _).mp hY
    obtain ⟨Z, d, hd0, hZ⟩ := T.exists_common_den m htr (fun i : Fin (P.length - 1) ↦ Y i)
    have hphid : T.phi m d ≠ 0 := fun h0' ↦ hd0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hphiq : T.phi m qs ≠ 0 := fun h0' ↦ hqs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hYi : ∀ i : Fin (P.length - 1), Y i = T.phi m (Z i) / T.phi m d := fun i ↦ by
      rw [← hZ i, mul_div_cancel_right₀ _ hphid]
    have hsol : SysSol (M.sem η) 0 qs qs (semMat M A0f)
        (fun j ↦ ∑ l ∈ Finset.range [Gf, Gg].length,
          C (algebraMap Cc (T.F m) (([1, -c] : List Cc).getD l 0)) *
          GPoly.toPoly M (([Gf, Gg].getD l fun _ ↦ []) j)) Z d := by
      refine T.sysSol_of_phi m hm hk h0 htr qs qs (semMat M A0f) _ Z d fun j ↦ ?_
      have hj := heq j j.2
      simp only [List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.range_zero,
        Finset.sum_empty, zero_add, List.getD_cons_zero, List.getD_cons_succ, map_one, one_mul,
        map_neg]
      rw [← Fin.sum_univ_eq_sum_range (fun i ↦ T.Mθ m h1 P dθ i j * Y i)] at hj
      have hMθ' : ∀ i : Fin (P.length - 1), T.Mθ m h1 P dθ i j = T.phi m (GPoly.toPoly M (A0f j i)) / T.phi m qs :=
        fun i ↦ hMθ i i.2 j j.2
      simp only [hMθ', hYi, hfv, hgv] at hj
      rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul] at hj
      simp only [semMat, Matrix.of_apply]
      have hsum : ∑ x, T.phi m (GPoly.toPoly M (A0f j x)) / T.phi m qs *
          (T.phi m (Z x) / T.phi m d) =
          (∑ x, T.phi m (GPoly.toPoly M (A0f j x)) * T.phi m (Z x)) / (T.phi m qs * T.phi m d) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun x _ ↦ by field_simp
      rw [hsum, smul_eq_mul] at hj
      have hG' : GPoly.toPoly M (Gf j) = GPoly.toPoly M (num (f.getD (↑j) O1.zero)) := rfl
      have hGg' : GPoly.toPoly M (Gg j) = GPoly.toPoly M (num (g.getD (↑j) O1.zero)) := rfl
      rw [hG', hGg']
      have hphiC : T.phi m (C (algebraMap Cc (T.F m) c)) = algebraMap Cc (T.F (m + 1)) c := by
        rw [T.phi_C]; rfl
      simp only [map_add, map_mul, map_neg, hphiC]
      field_simp at hj
      linear_combination (T.phi m qs) * hj
    obtain ⟨β, hβc, -⟩ := T.primSysC_complete m h0 η (P.length - 1) A0f q q [Gf, Gg] hm htr hk lim hlim
      r.1 r.2 (by simpa using hr) [1, -c] (fun l hl ↦ by
        simp only [List.length_cons, List.length_nil] at hl
        exact List.getD_eq_default _ _ (by simpa using hl)) Z d hd0 hsol
    have h1' := hβc 0
    simp only [List.getD_cons_zero] at h1'
    by_contra hcon
    rw [Bool.not_eq_true, List.any_eq_false] at hcon
    have hz : ∀ k ∈ Finset.range r.2.length,
        β.getD k 0 * algebraMap ℚ Cc (((r.2.getD k ([], fun _ ↦ [])).1).getD 0 0) = 0 := by
      intro k hk
      have hmem : r.2.getD k ([], fun _ ↦ []) ∈ r.2 := by
        rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]; exact List.getElem_mem _
      have := hcon _ hmem
      simp only [bne_iff_ne, ne_eq, not_not] at this
      rw [this, map_zero, mul_zero]
    rw [Finset.sum_eq_zero hz] at h1'
    exact one_ne_zero h1'

end MTower

end Curves.MT
