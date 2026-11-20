import RischTragerBronstein.Mixed.NKExactW

/-!
# The exact-part test in any basis, with a parameter

`exactW2 f g`: is `f − c g` exact for some constant `c`? (`exactW2_correct`, for any solver with a
`SolverSpec`, so at logarithmic and exponential levels alike.)
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM CPoly

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The exact-part test in any basis, with a parameter.** -/
def exactW2 (m : ℕ) (solve : SysSolver m) (N : ℕ) (Mc : List (List (LC (m + 1))))
    (f g : List (LC (m + 1))) : Option Bool :=
  let O1 := (MO Fc ks (m + 1)).normalizeBy (redL Fc ks (m + 1))
  let O := MO Fc ks m
  if N = 0 then none else
    let M : List (List (LC (m + 1))) := (List.range N).map fun i ↦
      (List.range N).map fun j ↦ (Mc.getD i []).getD j O1.zero
    let ent : List (LC (m + 1)) := M.flatten
    let q := lcmGL O (ent.map Prod.snd)
    let hq := lcmGL O ((f ++ g).map Prod.snd)
    if !((ent.map fun c ↦ cofC O q c.2).all Prod.fst &&
        ((f ++ g).map fun c ↦ cofC O hq c.2).all Prod.fst) then none else
    let num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2
    let numF : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O hq c.2).2
    let A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦ num ((M.getD i []).getD j O1.zero)
    let G : Fin N → GPoly (LC m) := fun j ↦ numF (f.getD j O1.zero)
    let Gg : Fin N → GPoly (LC m) := fun j ↦ numF (g.getD j O1.zero)
    match solve N A0 q hq [G, Gg] with
    | none => none
    | some r => some (r.2.any fun b ↦ b.1.getD 0 0 != 0)

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) (m : ℕ)

set_option maxHeartbeats 1600000 in
/-- **Correctness of the exact-part test in any basis.** -/
theorem exactW2_correct (h1 : T.Tr (m + 1)) (htr : Transcendental (T.F m) (T.ts m))
    (solve : SysSolver m) (wD bD : T.F m) (S : T.SolverSpec m h1.of_succ wD bD solve)
    (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (θw : ℕ → L)
    (hw : ∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) * θw j)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * θw j = 0 →
      ∀ j < N, a j = 0)
    (g : List (LC (m + 1))) (res : Bool) (hres : exactW2 Fc ks m solve N Mc f g = some res) :
    res = true ↔ ∃ (c : Cc) (Y : ℕ → T.F (m + 1)),
      (∑ i ∈ Finset.range N, (Y i : L) * θw i)′ =
        ∑ j ∈ Finset.range N,
          (((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) -
            algebraMap Cc L c * ((T.MPr (m + 1) h1).sem (g.getD j (MOr Fc ks (m + 1)).zero) : L)) *
            θw j := by
  classical
  unfold exactW2 at hres
  simp only at hres
  split_ifs at hres with hN0 hcof
  split at hres
  · exact absurd hres (by simp)
  rename_i r hr
  obtain rfl := Option.some.inj hres
  set O1 := MOr Fc ks (m + 1) with hO1
  set O := MO Fc ks m with hO
  set M1 := T.MPr (m + 1) h1 with hM1
  set h0 := h1.of_succ with hh0
  set M := T.MP m h0 with hM
  set Ml : List (List (LC (m + 1))) := (List.range N).map fun i ↦
    (List.range N).map fun j ↦ (Mc.getD i []).getD j O1.zero with hMl
  set Mw : ℕ → ℕ → T.F (m + 1) := fun i j ↦ M1.sem ((Mc.getD i []).getD j O1.zero) with hMw
  set ent : List (LC (m + 1)) := Ml.flatten with hent
  set q := lcmGL O (ent.map Prod.snd) with hq
  set hq := lcmGL O ((f ++ g).map Prod.snd) with hhq
  set num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2 with hnum
  set numF : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O hq c.2).2 with hnumF
  obtain ⟨hDs, hqs0, hhs0⟩ := S.den _ _ _ _ _ r hr
  set qs := GPoly.toPoly M q with hqs
  set hs := GPoly.toPoly M hq with hhs
  have hcof2 : (ent.map fun c ↦ cofC O q c.2).all Prod.fst = true ∧
      ((f ++ g).map fun c ↦ cofC O hq c.2).all Prod.fst = true := by
    revert hcof
    cases (ent.map fun c ↦ cofC O q c.2).all Prod.fst <;>
      cases ((f ++ g).map fun c ↦ cofC O hq c.2).all Prod.fst <;> simp
  have hcofs : ∀ c ∈ ent, (cofC O q c.2).1 = true := fun c hc ↦
    List.all_eq_true.mp hcof2.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hcofsF : ∀ c ∈ f ++ g, (cofC O hq c.2).1 = true := fun c hc ↦
    List.all_eq_true.mp hcof2.2 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hval : ∀ c ∈ ent, (M1.sem c : T.F (m + 1)) = T.phi m (GPoly.toPoly M (num c)) / T.phi m qs :=
    fun c hc ↦ T.sem_cof m h1 htr q hqs0 c (hcofs c hc)
  have hvalF : ∀ c ∈ f ++ g, (M1.sem c : T.F (m + 1)) = T.phi m (GPoly.toPoly M (numF c)) / T.phi m hs :=
    fun c hc ↦ T.sem_cof m h1 htr hq hhs0 c (hcofsF c hc)
  have hMe : ∀ i < N, ∀ j < N, (Ml.getD i []).getD j O1.zero ∈ ent := fun i hi j hj ↦ by
    rw [hent, List.mem_flatten]
    refine ⟨Ml.getD i [], ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by simpa [hMl] using hi)]; exact List.getElem_mem _
    · have hlen : j < (Ml.getD i []).length := by
        rw [hMl, NestTower.getD_range_map _ _ hi]; simpa using hj
      rw [List.getD_eq_getElem (Ml.getD i []) _ hlen]; exact List.getElem_mem _
  have hMθ : ∀ i < N, ∀ j < N, Mw i j =
      T.phi m (GPoly.toPoly M (num ((Ml.getD i []).getD j O1.zero))) / T.phi m qs := by
    intro i hi j hj
    rw [← hval _ (hMe i hi j hj), hMl, NestTower.getD_range_map _ _ hi,
      NestTower.getD_range_map _ _ hj]
  have hfv : ∀ j, (M1.sem (f.getD j O1.zero) : T.F (m + 1)) =
      T.phi m (GPoly.toPoly M (numF (f.getD j O1.zero))) / T.phi m hs := by
    intro j
    by_cases hj : j < f.length
    · refine hvalF _ (List.mem_append_left _ ?_)
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
    · rw [List.getD_eq_default _ _ (by omega)]
      have hz : O1.zero.1 = [] := rfl
      rw [M1.sem_zero, hnumF]
      simp only [hz, GPoly.mul, GPoly.toPoly_nil, map_zero, zero_div]
  have hgv : ∀ j, (M1.sem (g.getD j O1.zero) : T.F (m + 1)) =
      T.phi m (GPoly.toPoly M (numF (g.getD j O1.zero))) / T.phi m hs := by
    intro j
    by_cases hj : j < g.length
    · refine hvalF _ (List.mem_append_right _ ?_)
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
    · rw [List.getD_eq_default _ _ (by omega)]
      have hz : O1.zero.1 = [] := rfl
      rw [M1.sem_zero, hnumF]
      simp only [hz, GPoly.mul, GPoly.toPoly_nil, map_zero, zero_div]
  set A0f : Fin N → Fin N → GPoly (LC m) := fun j i ↦ num ((Ml.getD i []).getD j O1.zero) with hA0f
  set Gf : Fin N → GPoly (LC m) := fun j ↦ numF (f.getD j O1.zero) with hGf
  set Gg : Fin N → GPoly (LC m) := fun j ↦ numF (g.getD j O1.zero) with hGg
  -- the coordinate equations
  have hcoord : ∀ Y R : ℕ → T.F (m + 1),
      ((∑ i ∈ Finset.range N, (Y i : L) * θw i)′ = ∑ j ∈ Finset.range N,
        ((R j : T.F (m + 1)) : L) * θw j) ↔
      ∀ j < N, (Y j)′ + ∑ i ∈ Finset.range N, Mw i j * Y i = R j := by
    intro Y R
    have hdc := T.deriv_coordsW m N θw Mw hw Y
    rw [hdc]
    constructor
    · intro hE j hj
      have h0 := hind (fun j ↦ (Y j)′ + ∑ i ∈ Finset.range N, Mw i j * Y i -
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
  have hRc : ∀ c : Cc, ∑ j ∈ Finset.range N,
      (((M1.sem (f.getD j O1.zero) : T.F (m + 1)) : L) -
        algebraMap Cc L c * ((M1.sem (g.getD j O1.zero) : T.F (m + 1)) : L)) * θw j =
      ∑ j ∈ Finset.range N, (((M1.sem (f.getD j O1.zero) -
        algebraMap Cc (T.F (m + 1)) c * M1.sem (g.getD j O1.zero) : T.F (m + 1)) : L)) * θw j :=
    fun c ↦ Finset.sum_congr rfl fun j _ ↦ by push_cast; rfl
  constructor
  · intro hany
    obtain ⟨b, hb, he⟩ := List.any_eq_true.mp hany
    simp only [bne_iff_ne, ne_eq] at he
    set e0 : ℚ := b.1.getD 0 0 with he0
    set e1 : ℚ := b.1.getD 1 0 with he1
    have hsS := S.sound _ _ _ _ _ r.1 r.2 (by simpa using hr) b hb
    have hphiD : T.phi m (GPoly.toPoly M r.1) ≠ 0 := fun h0' ↦ hDs (T.phi_injective htr
      (by rw [h0', map_zero]))
    have hphiq : T.phi m qs ≠ 0 := fun h0' ↦ hqs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hE : ((e0 : ℚ) : T.F (m + 1)) ≠ 0 := by exact_mod_cast he
    set Y : ℕ → T.F (m + 1) := fun i ↦ if hi : i < N then
      T.phi m (semV M b.2 ⟨i, hi⟩) / (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1))) else 0
      with hY
    refine ⟨algebraMap ℚ Cc (-(e1 / e0)), Y, ?_⟩
    rw [hRc]
    refine (hcoord Y _).mpr fun j hj ↦ ?_
    have hcF : algebraMap Cc (T.F (m + 1)) (algebraMap ℚ Cc (-(e1 / e0))) =
        ((-(e1 / e0) : ℚ) : T.F (m + 1)) := by
      rw [← IsScalarTower.algebraMap_apply]; exact eq_ratCast _ _
    rw [hcF]
    have hphi := T.sysSol_phiG m wD bD S.hD qs hs (semMat M A0f) _ (semV M b.2) (GPoly.toPoly M r.1)
      ⟨j, hj⟩ hsS
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.range_zero,
      Finset.sum_empty, zero_add, List.getD_cons_zero, List.getD_cons_succ, map_add, map_mul, semMat,
      Matrix.of_apply] at hphi
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦ Mw i j * Y i)]
    have hMθ' : ∀ i : Fin N,
        Mw i j = T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ i)) / T.phi m qs :=
      fun i ↦ hMθ i i.2 j hj
    have hYi : ∀ i : Fin N, Y i = T.phi m (semV M b.2 i) /
        (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1))) := fun i ↦ by
      rw [hY]; simp only [dif_pos i.2]
    simp only [hMθ', hYi]
    have hYj : Y j = T.phi m (semV M b.2 ⟨j, hj⟩) /
        (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1))) := by
      rw [hY]; simp only [dif_pos hj]
    rw [hYj, hfv, hgv]
    have hG' : GPoly.toPoly M (Gf ⟨j, hj⟩) = GPoly.toPoly M (numF (f.getD j O1.zero)) := rfl
    have hGg' : GPoly.toPoly M (Gg ⟨j, hj⟩) = GPoly.toPoly M (numF (g.getD j O1.zero)) := rfl
    rw [hG', hGg'] at hphi
    rw [Derivation.leibniz_div, Derivation.leibniz, T.deriv_ratCast, smul_zero, zero_add,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    rw [T.phi_C_ratCast, T.phi_C_ratCast] at hphi
    have hsum : ∑ x : Fin N, T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ x)) / T.phi m qs *
        (T.phi m (semV M b.2 x) / (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1)))) =
        (∑ x, T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ x)) * T.phi m (semV M b.2 x)) /
          (T.phi m qs * (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1)))) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun x _ ↦ by field_simp
    rw [hsum, smul_eq_mul]
    have hphih : T.phi m hs ≠ 0 := fun h0' ↦ hhs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hcast : ((b.1.getD 0 0 : ℚ) : T.F (m + 1)) * (((-(e1 / e0)) : ℚ) : T.F (m + 1)) +
        ((b.1.getD 1 0 : ℚ) : T.F (m + 1)) = 0 := by
      rw [← he0, ← he1]; push_cast; field_simp; ring
    field_simp
    linear_combination hphi + (T.phi m qs * T.phi m (GPoly.toPoly M r.1) ^ 2 *
      T.phi m (GPoly.toPoly M (numF (g.getD j O1.zero)))) * hcast
  · rintro ⟨c, Y, hY⟩
    rw [hRc] at hY
    have heq := (hcoord Y _).mp hY
    obtain ⟨Z, d, hd0, hZ⟩ := T.exists_common_den m htr (fun i : Fin N ↦ Y i)
    have hphid : T.phi m d ≠ 0 := fun h0' ↦ hd0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hphiq : T.phi m qs ≠ 0 := fun h0' ↦ hqs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hYi : ∀ i : Fin N, Y i = T.phi m (Z i) / T.phi m d := fun i ↦ by
      rw [← hZ i, mul_div_cancel_right₀ _ hphid]
    have hsol : SysSol wD bD qs hs (semMat M A0f)
        (fun j ↦ ∑ l ∈ Finset.range [Gf, Gg].length,
          C (algebraMap Cc (T.F m) (([1, -c] : List Cc).getD l 0)) *
          GPoly.toPoly M (([Gf, Gg].getD l fun _ ↦ []) j)) Z d := by
      refine T.sysSol_of_phiG m htr wD bD S.hD qs hs (semMat M A0f) _ Z d fun j ↦ ?_
      have hj := heq j j.2
      simp only [List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.range_zero,
        Finset.sum_empty, zero_add, List.getD_cons_zero, List.getD_cons_succ, map_one, one_mul,
        map_neg]
      rw [← Fin.sum_univ_eq_sum_range (fun i ↦ Mw i j * Y i)] at hj
      have hMθ' : ∀ i : Fin N, Mw i j = T.phi m (GPoly.toPoly M (A0f j i)) / T.phi m qs :=
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
      have hG' : GPoly.toPoly M (Gf j) = GPoly.toPoly M (numF (f.getD (↑j) O1.zero)) := rfl
      have hGg' : GPoly.toPoly M (Gg j) = GPoly.toPoly M (numF (g.getD (↑j) O1.zero)) := rfl
      rw [hG', hGg']
      have hphiC : T.phi m (C (algebraMap Cc (T.F m) c)) = algebraMap Cc (T.F (m + 1)) c := by
        rw [T.phi_C]; rfl
      simp only [map_add, map_mul, map_neg, hphiC]
      have hphih : T.phi m hs ≠ 0 := fun h0' ↦ hhs0 (T.phi_injective htr (by rw [h0', map_zero]))
      field_simp at hj
      linear_combination hj
    obtain ⟨β, hβc, -⟩ := S.complete _ _ _ _ _ r.1 r.2 (by simpa using hr) [1, -c] (fun l hl ↦ by
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
