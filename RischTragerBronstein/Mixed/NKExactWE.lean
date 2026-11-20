import RischTragerBronstein.Mixed.NKExactWSome
import RischTragerBronstein.Mixed.SysPrimK

/-!
# The exact-part test in a basis with a denominator bound

`exactWE … E`: as `exactW`, with the right-hand side denominator `h` a multiple of the extra
polynomial `E` (checked), for solvers that are complete only for the solutions whose denominator
divides `h` (`SolverSpecB`), such as `primSysB … 0` (`primSysB_specB`). It is sound, and finds
every antiderivative `∑ Yᵢ wᵢ` whose coordinates have denominators dividing `E`
(`exactWE_correct`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The exact-part test in a basis with a denominator bound `E`.** -/
def exactWE (m : ℕ) (solve : SysSolver m) (N : ℕ) (Mc : List (List (LC (m + 1))))
    (f : List (LC (m + 1))) (E : GPoly (LC m)) : Option Bool :=
  let O1 := (MO Fc ks (m + 1)).normalizeBy (redL Fc ks (m + 1))
  let O := MO Fc ks m
  if N = 0 then none else
    let M : List (List (LC (m + 1))) := (List.range N).map fun i ↦
      (List.range N).map fun j ↦ (Mc.getD i []).getD j O1.zero
    let ent : List (LC (m + 1)) := M.flatten
    let q := lcmGL O (ent.map Prod.snd)
    let hq := lcmGL O (f.map Prod.snd ++ [E])
    if !((ent.map fun c ↦ cofC O q c.2).all Prod.fst &&
        (f.map fun c ↦ cofC O hq c.2).all Prod.fst && (cofC O hq E).1) then none else
    let num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2
    let numF : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O hq c.2).2
    let A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦ num ((M.getD i []).getD j O1.zero)
    let G : Fin N → GPoly (LC m) := fun j ↦ numF (f.getD j O1.zero)
    match solve N A0 q hq [G] with
    | none => none
    | some r => some (r.2.any fun b ↦ b.1.getD 0 0 != 0)

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- A system solver complete for the solutions whose denominator divides the right-hand side
denominator `h`. -/
structure SolverSpecB (m : ℕ) (h0 : T.Tr m) (w b : T.F m) (solve : SysSolver m) : Prop where
  hD : ∀ P, T.phi m (DzL w b P) = (T.phi m P)′
  sound : ∀ (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m)) (q hh : GPoly (LC m))
    (G0 : List (Fin n → GPoly (LC m))) (Den : GPoly (LC m))
    (out : List (List ℚ × (Fin n → GPoly (LC m)))), solve n A0 q hh G0 = some (Den, out) →
    ∀ r ∈ out, SysSol w b (GPoly.toPoly (T.MP m h0) q)
      (GPoly.toPoly (T.MP m h0) hh) (semMat (T.MP m h0) A0)
      (fun i ↦ ∑ l ∈ Finset.range G0.length, C ((r.1.getD l 0 : ℚ) : T.F m) *
        GPoly.toPoly (T.MP m h0) ((G0.getD l fun _ ↦ []) i))
      (semV (T.MP m h0) r.2) (GPoly.toPoly (T.MP m h0) Den)
  den : ∀ (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m)) (q hh : GPoly (LC m))
    (G0 : List (Fin n → GPoly (LC m))) (r : GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))),
    solve n A0 q hh G0 = some r → GPoly.toPoly (T.MP m h0) r.1 ≠ 0 ∧
      GPoly.toPoly (T.MP m h0) q ≠ 0 ∧ GPoly.toPoly (T.MP m h0) hh ≠ 0
  complete : ∀ (n : ℕ) (A0 : Fin n → Fin n → GPoly (LC m)) (q hh : GPoly (LC m))
    (G0 : List (Fin n → GPoly (LC m))) (Den : GPoly (LC m))
    (out : List (List ℚ × (Fin n → GPoly (LC m)))), solve n A0 q hh G0 = some (Den, out) →
    ∀ (c : List Cc), (∀ l, G0.length ≤ l → c.getD l 0 = 0) → ∀ (Z : Fin n → (T.F m)[X])
    (d : (T.F m)[X]), d ≠ 0 →
    SysSol w b (GPoly.toPoly (T.MP m h0) q)
      (GPoly.toPoly (T.MP m h0) hh) (semMat (T.MP m h0) A0)
      (fun i ↦ ∑ l ∈ Finset.range G0.length, C (algebraMap Cc (T.F m) (c.getD l 0)) *
        GPoly.toPoly (T.MP m h0) ((G0.getD l fun _ ↦ []) i)) Z d →
    (∀ i, d ∣ GPoly.toPoly (T.MP m h0) hh * Z i) →
    ∃ β : List Cc, (∀ l, c.getD l 0 = ∑ k ∈ Finset.range out.length,
        β.getD k 0 * algebraMap ℚ Cc ((out.getD k ([], fun _ ↦ [])).1.getD l 0)) ∧
      ∀ i, GPoly.toPoly (T.MP m h0) Den * Z i = d * ∑ k ∈ Finset.range out.length,
        C (algebraMap Cc (T.F m) (β.getD k 0)) *
          semV (T.MP m h0) (out.getD k ([], fun _ ↦ [])).2 i

variable (m : ℕ)

set_option maxHeartbeats 1600000 in
/-- **Correctness of the exact-part test with a denominator bound `E`.** -/
theorem exactWE_correct (h1 : T.Tr (m + 1)) (htr : Transcendental (T.F m) (T.ts m))
    (solve : SysSolver m) (wD bD : T.F m) (S : T.SolverSpecB m h1.of_succ wD bD solve)
    (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (E : GPoly (LC m)) (θw : ℕ → L)
    (hw : ∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) * θw j)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * θw j = 0 →
      ∀ j < N, a j = 0)
    (res : Bool) (hres : exactWE Fc ks m solve N Mc f E = some res) :
    (res = true → ∃ Y : ℕ → T.F (m + 1),
      (∑ i ∈ Finset.range N, (Y i : L) * θw i)′ =
        ∑ j ∈ Finset.range N,
          ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) * θw j) ∧
    ((∃ (Y : ℕ → T.F (m + 1)) (z : ℕ → (T.F m)[X]),
      (∀ i < N, Y i * T.phi m (GPoly.toPoly (T.MP m h1.of_succ) E) = T.phi m (z i)) ∧
      (∑ i ∈ Finset.range N, (Y i : L) * θw i)′ =
        ∑ j ∈ Finset.range N,
          ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) * θw j) →
      res = true) := by
  classical
  unfold exactWE at hres
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
  set hq := lcmGL O (f.map Prod.snd ++ [E]) with hhq
  set num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2 with hnum
  set numF : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O hq c.2).2 with hnumF
  obtain ⟨hDs, hqs0, hhs0⟩ := S.den _ _ _ _ _ r hr
  set qs := GPoly.toPoly M q with hqs
  set hs := GPoly.toPoly M hq with hhs
  have hcof2 : (ent.map fun c ↦ cofC O q c.2).all Prod.fst = true ∧
      (f.map fun c ↦ cofC O hq c.2).all Prod.fst = true ∧ (cofC O hq E).1 = true := by
    revert hcof
    cases (ent.map fun c ↦ cofC O q c.2).all Prod.fst <;>
      cases (f.map fun c ↦ cofC O hq c.2).all Prod.fst <;> cases (cofC O hq E).1 <;> simp
  have hcofs : ∀ c ∈ ent, (cofC O q c.2).1 = true := fun c hc ↦
    List.all_eq_true.mp hcof2.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hcofsF : ∀ c ∈ f, (cofC O hq c.2).1 = true := fun c hc ↦
    List.all_eq_true.mp hcof2.2.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hval : ∀ c ∈ ent, (M1.sem c : T.F (m + 1)) = T.phi m (GPoly.toPoly M (num c)) / T.phi m qs :=
    fun c hc ↦ T.sem_cof m h1 htr q hqs0 c (hcofs c hc)
  have hvalF : ∀ c ∈ f, (M1.sem c : T.F (m + 1)) = T.phi m (GPoly.toPoly M (numF c)) / T.phi m hs :=
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
    · refine hvalF _ ?_
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
    · rw [List.getD_eq_default _ _ (by omega)]
      have hz : O1.zero.1 = [] := rfl
      rw [M1.sem_zero, hnumF]
      simp only [hz, GPoly.mul, GPoly.toPoly_nil, map_zero, zero_div]
  set A0f : Fin N → Fin N → GPoly (LC m) := fun j i ↦ num ((Ml.getD i []).getD j O1.zero) with hA0f
  set Gf : Fin N → GPoly (LC m) := fun j ↦ numF (f.getD j O1.zero) with hGf
  -- the coordinate equations
  have hcoord : ∀ Y : ℕ → T.F (m + 1),
      ((∑ i ∈ Finset.range N, (Y i : L) * θw i)′ = ∑ j ∈ Finset.range N,
        ((M1.sem (f.getD j O1.zero) : T.F (m + 1)) : L) * θw j) ↔
      ∀ j < N, (Y j)′ + ∑ i ∈ Finset.range N, Mw i j * Y i =
        M1.sem (f.getD j O1.zero) := by
    intro Y
    have hdc := T.deriv_coordsW m N θw Mw hw Y
    rw [hdc]
    constructor
    · intro hE j hj
      have h0 := hind (fun j ↦ (Y j)′ + ∑ i ∈ Finset.range N, Mw i j * Y i -
        M1.sem (f.getD j O1.zero)) (by
          push_cast
          simp only [sub_mul, Finset.sum_sub_distrib]
          rw [← hE]
          push_cast
          simp only [add_mul, Finset.sum_mul]
          ring) j hj
      exact sub_eq_zero.mp h0
    · intro hE
      exact Finset.sum_congr rfl fun j hj ↦ by rw [hE j (Finset.mem_range.mp hj)]
  -- `E` divides `h`
  have hEh : GPoly.toPoly M hq = GPoly.toPoly M (cofC O hq E).2 * GPoly.toPoly M E := by
    have hs := GPoly.divMod_spec M hq E
    have hr0 := (GPoly.isZero_iff M _).mp hcof2.2.2
    rw [hs]; simp only [cofC] at hr0 ⊢; rw [hr0, add_zero]
  constructor
  · intro hany
    obtain ⟨b, hb, he⟩ := List.any_eq_true.mp hany
    simp only [bne_iff_ne, ne_eq] at he
    set e0 : ℚ := b.1.getD 0 0 with he0
    have hsS := S.sound _ _ _ _ _ r.1 r.2 (by simpa using hr) b hb
    have hphiD : T.phi m (GPoly.toPoly M r.1) ≠ 0 := fun h0' ↦ hDs (T.phi_injective htr
      (by rw [h0', map_zero]))
    have hphiq : T.phi m qs ≠ 0 := fun h0' ↦ hqs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hE : ((e0 : ℚ) : T.F (m + 1)) ≠ 0 := by exact_mod_cast he
    set Y : ℕ → T.F (m + 1) := fun i ↦ if hi : i < N then
      T.phi m (semV M b.2 ⟨i, hi⟩) / (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1))) else 0
      with hY
    refine ⟨Y, (hcoord Y).mpr fun j hj ↦ ?_⟩
    have hphi := T.sysSol_phiG m wD bD S.hD qs hs (semMat M A0f) _ (semV M b.2) (GPoly.toPoly M r.1)
      ⟨j, hj⟩ hsS
    simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton, List.getD_cons_zero,
      map_mul, semMat, Matrix.of_apply] at hphi
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
    rw [hYj, hfv]
    have hG' : GPoly.toPoly M (Gf ⟨j, hj⟩) = GPoly.toPoly M (numF (f.getD j O1.zero)) := rfl
    rw [hG'] at hphi
    rw [Derivation.leibniz_div, Derivation.leibniz, T.deriv_ratCast, smul_zero, zero_add,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    rw [T.phi_C_ratCast] at hphi
    have hsum : ∑ x : Fin N, T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ x)) / T.phi m qs *
        (T.phi m (semV M b.2 x) / (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1)))) =
        (∑ x, T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ x)) * T.phi m (semV M b.2 x)) /
          (T.phi m qs * (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1)))) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun x _ ↦ by field_simp
    rw [hsum, smul_eq_mul]
    have hG'' : GPoly.toPoly (T.MP m h0) (Gf ⟨j, hj⟩) = GPoly.toPoly M (numF (f.getD j O1.zero)) := rfl
    rw [hG''] at hphi
    have hphih : T.phi m hs ≠ 0 := fun h0' ↦ hhs0 (T.phi_injective htr (by rw [h0', map_zero]))
    field_simp
    linear_combination hphi
  · rintro ⟨Y, z, hYz, hY⟩
    have heq := (hcoord Y).mp hY
    set d := GPoly.toPoly M E with hdE
    set Z : Fin N → (T.F m)[X] := fun i ↦ z i with hZdef
    have hd0 : d ≠ 0 := fun h0' ↦ hhs0 (by rw [hhs, hEh, h0', mul_zero])
    have hphid : T.phi m d ≠ 0 := fun h0' ↦ hd0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hphiq : T.phi m qs ≠ 0 := fun h0' ↦ hqs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hYi : ∀ i : Fin N, Y i = T.phi m (Z i) / T.phi m d := fun i ↦ by
      exact (eq_div_iff hphid).mpr (hYz i i.2)
    have hdvd : ∀ i, d ∣ hs * Z i := fun i ↦
      Dvd.dvd.mul_right ⟨_, by rw [hhs, hEh, mul_comm]⟩ _
    have hsol : SysSol wD bD qs hs (semMat M A0f)
        (fun j ↦ ∑ l ∈ Finset.range [Gf].length, C (algebraMap Cc (T.F m) (([1] : List Cc).getD l 0)) *
          GPoly.toPoly M (([Gf].getD l fun _ ↦ []) j)) Z d := by
      refine T.sysSol_of_phiG m htr wD bD S.hD qs hs (semMat M A0f) _ Z d fun j ↦ ?_
      have hj := heq j j.2
      simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton, List.getD_cons_zero,
        map_one, one_mul]
      rw [← Fin.sum_univ_eq_sum_range (fun i ↦ Mw i j * Y i)] at hj
      have hMθ' : ∀ i : Fin N, Mw i j = T.phi m (GPoly.toPoly M (A0f j i)) / T.phi m qs :=
        fun i ↦ hMθ i i.2 j j.2
      simp only [hMθ', hYi, hfv] at hj
      rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul] at hj
      simp only [semMat, Matrix.of_apply]
      have hsum : ∑ x, T.phi m (GPoly.toPoly M (A0f j x)) / T.phi m qs *
          (T.phi m (Z x) / T.phi m d) =
          (∑ x, T.phi m (GPoly.toPoly M (A0f j x)) * T.phi m (Z x)) / (T.phi m qs * T.phi m d) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun x _ ↦ by field_simp
      rw [hsum, smul_eq_mul] at hj
      have hG' : GPoly.toPoly M (Gf j) = GPoly.toPoly M (numF (f.getD (↑j) O1.zero)) := rfl
      rw [hG']
      have hphih : T.phi m hs ≠ 0 := fun h0' ↦ hhs0 (T.phi_injective htr (by rw [h0', map_zero]))
      field_simp at hj
      linear_combination hj
    obtain ⟨β, hβc, -⟩ := S.complete _ _ _ _ _ r.1 r.2 (by simpa using hr) [1] (fun l hl ↦ by
        simp only [List.length_singleton] at hl
        exact List.getD_eq_default _ _ (by simpa using hl)) Z d hd0 hsol hdvd
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


/-- A successful `primSysB` has monic `q`, `h`. -/
lemma primSysB_monic {m : ℕ} {η : LC m} {lim : List (LC m) → List (List ℚ × LC m)} {n : ℕ}
    {A0 : Fin n → Fin n → GPoly (LC m)} {q hq : GPoly (LC m)} {G0 : List (Fin n → GPoly (LC m))}
    {B : ℕ} {r : GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))}
    (hres : primSysB Fc ks m η lim n A0 q hq G0 B = some r) :
    isMonicC (MO Fc ks m) q = true ∧ isMonicC (MO Fc ks m) hq = true := by
  unfold primSysB at hres
  simp only at hres
  split_ifs at hres with hmon
  have : (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hq) = true := by
    revert hmon; cases (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hq) <;> simp
  exact Bool.and_eq_true_iff.mp this

/-- A successful `primSysB` returns the `W`-system denominator. -/
lemma primSysB_den {m : ℕ} {η : LC m} {lim : List (LC m) → List (List ℚ × LC m)} {n : ℕ}
    {A0 : Fin n → Fin n → GPoly (LC m)} {q hq : GPoly (LC m)} {G0 : List (Fin n → GPoly (LC m))}
    {B : ℕ} {r : GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))}
    (hres : primSysB Fc ks m η lim n A0 q hq G0 B = some r) :
    r.1 = (wSys Fc ks m η n A0 q hq G0 B).Den := by
  unfold primSysB at hres
  simp only at hres
  split_ifs at hres
  split at hres
  · exact absurd hres (by simp)
  rw [← Option.some.inj hres]

variable {m}

/-- `primSysB … 0` meets the solver specification with known denominators (primitive level). -/
theorem primSpecB (hm : m < T.n) (h0 : T.Tr m) {η : LC m} (hk : ks m = .prim η)
    (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h0) lim) :
    T.SolverSpecB m h0 ((T.MP m h0).sem η) 0
      (fun n A0 q hh G0 ↦ primSysB Fc ks m η lim n A0 q hh G0 0) where
  hD := T.phi_DzL m hm hk h0
  sound := fun n A0 q hh G0 Den out hres ↦
    T.primSysB_sound m h0 η n A0 q hh G0 0 lim Den out hres
  den := fun n A0 q hh G0 r hres ↦ by
    have hB := primSysB_den hres
    have hmo := primSysB_monic hres
    have hq := (isMonicC_spec (T.MP m h0) q hmo.1).ne_zero
    have hh' := (isMonicC_spec (T.MP m h0) hh hmo.2).ne_zero
    refine ⟨?_, hq, hh'⟩
    rw [hB, T.wSys_Den m h0 η n A0 q hh G0 0]
    exact mul_ne_zero hh' (pow_ne_zero _ hq)
  complete := fun n A0 q hh G0 Den out hres c hc Z d hd hsol hdvd ↦
    T.primSysB_complete m h0 η n A0 q hh G0 0 lim hlim Den out hres c hc Z d hd hsol
      (fun i ↦ by rw [pow_zero, mul_one]; exact hdvd i)

/-- **`exactWE` answers** with the solver `primSysB … 0` for a basis whose derivation matrix vanishes
at infinity (any non-zero denominators). -/
theorem exactWE_isSome (m : ℕ) (h : T.Tr m) (η : LC m)
    (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h) lim)
    (hη : ∀ y : T.F m, y′ ≠ (T.MP m h).sem η)
    (N : ℕ) (hN : N ≠ 0) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (hent : ∀ i < N, ∀ j < N,
      GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2 ≠ 0 ∧
      (GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).1).degree <
        (GPoly.toPoly (T.MP m h) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2).degree)
    (hf : ∀ c ∈ f, GPoly.toPoly (T.MP m h) c.2 ≠ 0) (E : GPoly (LC m))
    (hE : GPoly.toPoly (T.MP m h) E ≠ 0) :
    (exactWE Fc ks m (fun n A0 q hh G0 ↦ primSysB Fc ks m η lim n A0 q hh G0 0) N Mc f E).isSome := by
  set O := MO Fc ks m with hO
  set P := T.MP m h with hP
  set O1 := MOr Fc ks (m + 1) with hO1
  set Mm : List (List (LC (m + 1))) := (List.range N).map fun i ↦
    (List.range N).map fun j ↦ (Mc.getD i []).getD j O1.zero with hMm
  have hmem : ∀ c ∈ Mm.flatten, ∃ i < N, ∃ j < N, c = (Mc.getD i []).getD j O1.zero := by
    intro c hc
    obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hcl
    exact ⟨i, List.mem_range.mp hi, j, List.mem_range.mp hj, rfl⟩
  have hent' : ∀ c ∈ Mm.flatten, GPoly.toPoly P c.2 ≠ 0 ∧
      (GPoly.toPoly P c.1).degree < (GPoly.toPoly P c.2).degree := by
    intro c hc
    obtain ⟨i, hi, j, hj, rfl⟩ := hmem c hc
    exact hent i hi j hj
  set q := lcmGL O (Mm.flatten.map Prod.snd) with hq
  set hh := lcmGL O (f.map Prod.snd ++ [E]) with hhh
  obtain ⟨hqm, hqd, -⟩ := lcmGL_spec P (Mm.flatten.map Prod.snd) (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact (hent' c hc).1)
  obtain ⟨hhm, hhd, -⟩ := lcmGL_spec P (f.map Prod.snd ++ [E]) (by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact hf c hc
    · rw [List.mem_singleton.mp hd]; exact hE)
  have hcheck : ((Mm.flatten.map fun c ↦ cofC O q c.2).all Prod.fst &&
      (f.map fun c ↦ cofC O hh c.2).all Prod.fst && (cofC O hh E).1) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_map]
    refine ⟨⟨?_, ?_⟩, cofC_fst P hh E hE (hhd _ (List.mem_append_right _ (List.mem_singleton_self _)))⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact cofC_fst P q c.2 (hent' c hc).1 (hqd _ (List.mem_map_of_mem hc))
    · rintro _ ⟨c, hc, rfl⟩
      exact cofC_fst P hh c.2 (hf c hc) (hhd _ (List.mem_append_left _ (List.mem_map_of_mem hc)))
  set A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦
    GPoly.mul O ((Mm.getD i []).getD j O1.zero).1 (cofC O q ((Mm.getD i []).getD j O1.zero).2).2
    with hA0
  set G : Fin N → GPoly (LC m) := fun j ↦
    GPoly.mul O (f.getD j O1.zero).1 (cofC O hh (f.getD j O1.zero).2).2 with hG
  have hA : ∀ i j, (GPoly.toPoly P (A0 i j)).degree < (GPoly.toPoly P q).degree := by
    intro j i
    set c := (Mm.getD i []).getD j O1.zero with hc
    have hcm : c ∈ Mm.flatten := by
      rw [hc, hMm, NestTower.getD_range_map _ _ i.2, NestTower.getD_range_map _ _ j.2]
      exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr i.2, rfl⟩,
        List.mem_map.mpr ⟨j, List.mem_range.mpr j.2, rfl⟩⟩
    obtain ⟨h0, hdeg⟩ := hent' c hcm
    have hqc := cofC_snd P q c.2 h0 (hqd _ (List.mem_map_of_mem hcm))
    have hcof0 : GPoly.toPoly P (cofC O q c.2).2 ≠ 0 := fun hz ↦
      hqm.ne_zero (by rw [hqc, hz, zero_mul])
    show (GPoly.toPoly P (GPoly.mul O c.1 (cofC O q c.2).2)).degree < _
    rw [GPoly.toPoly_mul, hqc, degree_mul, degree_mul, add_comm]
    exact WithBot.add_lt_add_left (by rw [Ne, degree_eq_bot]; exact hcof0) hdeg
  have hmon : (isMonicC O q && isMonicC O hh) = true := by
    rw [isMonicC_of_monic P q hqm, isMonicC_of_monic P hh hhm]; rfl
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
    (T.primSysB_isSome m h η N A0 q hh [G] 0 lim hlim hmon hA hη)
  unfold exactWE
  simp only
  simp only [hN, ↓reduceIte]
  split_ifs with hc
  · rw [Bool.not_eq_true'] at hc
    exact absurd (hc.symm.trans hcheck) (by decide)
  split
  · rename_i heq
    exact absurd (heq.symm.trans hr) (by simp)
  · rfl

end MTower

end Curves.MT
