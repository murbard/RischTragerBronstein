import RischTragerBronstein.Mixed.NKExact

/-!
# The exact part with separate denominators for the matrix and the right-hand side

`exactG` is `exactC` for any system solver `solve` (given with its specification `SolverSpec`),
clearing the derivation matrix of the power basis by the lcm `q` of its own denominators and the
integrand by the lcm `h` of its denominators: `Y′ + (A₀/q) Y = G/h`. Poles of `f` at places where the
matrix is regular (e.g. `f = 1/log² x`) then do not enter `q`, where they would make the indicial
norm vanish identically. `exactG_correct`: `some res` decides the existence of `∑ Yᵢ θⁱ` with
`(∑ Yᵢ θⁱ)′ = ∑ fⱼ θʲ`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

/-- A system solver at level `m`: `(n, A₀, q, h, [G₀ₗ]) ↦ (Den, [(cₗ, W)])`. -/
abbrev SysSolver (m : ℕ) : Type :=
  (n : ℕ) → (Fin n → Fin n → GPoly (LC m)) → GPoly (LC m) → GPoly (LC m) →
    List (Fin n → GPoly (LC m)) → Option (GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m))))

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- **The exact-part test with separate denominators.** -/
def exactG (m : ℕ) (solve : SysSolver m) (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) :
    Option Bool :=
  let O1 := (MO Fc ks (m + 1)).normalizeBy (redL Fc ks (m + 1))
  let O := MO Fc ks m
  let N := P.length - 1
  if !(O1.isZero (O1.add (P.getD N O1.zero) (O1.neg O1.one))) || N = 0 then none else
  match dThetaC O1 P with
  | none => none
  | some dθ =>
    let M : List (List (LC (m + 1))) := (List.range N).map fun i ↦
      (List.range N).map fun j ↦ (dPowC O1 P dθ i).getD j O1.zero
    let ent : List (LC (m + 1)) := M.flatten
    let q := lcmGL O (ent.map Prod.snd)
    let hq := lcmGL O (f.map Prod.snd)
    if !((ent.map fun c ↦ cofC O q c.2).all Prod.fst &&
        (f.map fun c ↦ cofC O hq c.2).all Prod.fst) then none else
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

/-- **The specification of a system solver** at level `m` for `t′ = w + b t`. -/
structure SolverSpec (m : ℕ) (h0 : T.Tr m) (w b : T.F m) (solve : SysSolver m) : Prop where
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
    ∃ β : List Cc, (∀ l, c.getD l 0 = ∑ k ∈ Finset.range out.length,
        β.getD k 0 * algebraMap ℚ Cc ((out.getD k ([], fun _ ↦ [])).1.getD l 0)) ∧
      ∀ i, GPoly.toPoly (T.MP m h0) Den * Z i = d * ∑ k ∈ Finset.range out.length,
        C (algebraMap Cc (T.F m) (β.getD k 0)) *
          semV (T.MP m h0) (out.getD k ([], fun _ ↦ [])).2 i

variable (m : ℕ)

set_option maxHeartbeats 1600000 in
/-- **Correctness of the exact-part test with separate denominators.** -/
theorem exactG_correct (h1 : T.Tr (m + 1)) (htr : Transcendental (T.F m) (T.ts m))
    (solve : SysSolver m) (wD bD : T.F m) (S : T.SolverSpec m h1.of_succ wD bD solve)
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range (P.length - 1), (a j : L) * θ ^ j = 0 →
      ∀ j < P.length - 1, a j = 0)
    (res : Bool) (hres : exactG Fc ks m solve P f = some res) :
    res = true ↔ ∃ Y : ℕ → T.F (m + 1),
      (∑ i ∈ Finset.range (P.length - 1), (Y i : L) * θ ^ i)′ =
        ∑ j ∈ Finset.range (P.length - 1),
          ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j := by
  classical
  unfold exactG at hres
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
  set ent : List (LC (m + 1)) := Ml.flatten with hent
  set q := lcmGL O (ent.map Prod.snd) with hq
  set hq := lcmGL O (f.map Prod.snd) with hhq
  set num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2 with hnum
  set numF : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O hq c.2).2 with hnumF
  obtain ⟨hDs, hqs0, hhs0⟩ := S.den _ _ _ _ _ r hr
  set qs := GPoly.toPoly M q with hqs
  set hs := GPoly.toPoly M hq with hhs
  have hcof2 : (ent.map fun c ↦ cofC O q c.2).all Prod.fst = true ∧
      (f.map fun c ↦ cofC O hq c.2).all Prod.fst = true := by
    revert hcof
    cases (ent.map fun c ↦ cofC O q c.2).all Prod.fst <;>
      cases (f.map fun c ↦ cofC O hq c.2).all Prod.fst <;> simp
  have hcofs : ∀ c ∈ ent, (cofC O q c.2).1 = true := fun c hc ↦
    List.all_eq_true.mp hcof2.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hcofsF : ∀ c ∈ f, (cofC O hq c.2).1 = true := fun c hc ↦
    List.all_eq_true.mp hcof2.2 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hval : ∀ c ∈ ent, (M1.sem c : T.F (m + 1)) = T.phi m (GPoly.toPoly M (num c)) / T.phi m qs :=
    fun c hc ↦ T.sem_cof m h1 htr q hqs0 c (hcofs c hc)
  have hvalF : ∀ c ∈ f, (M1.sem c : T.F (m + 1)) = T.phi m (GPoly.toPoly M (numF c)) / T.phi m hs :=
    fun c hc ↦ T.sem_cof m h1 htr hq hhs0 c (hcofsF c hc)
  have hMe : ∀ i < (P.length - 1), ∀ j < (P.length - 1), (Ml.getD i []).getD j O1.zero ∈ ent := fun i hi j hj ↦ by
    rw [hent, List.mem_flatten]
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
      T.phi m (GPoly.toPoly M (numF (f.getD j O1.zero))) / T.phi m hs := by
    intro j
    by_cases hj : j < f.length
    · refine hvalF _ ?_
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
    · rw [List.getD_eq_default _ _ (by omega)]
      have hz : O1.zero.1 = [] := rfl
      rw [M1.sem_zero, hnumF]
      simp only [hz, GPoly.mul, GPoly.toPoly_nil, map_zero, zero_div]
  set A0f : Fin (P.length - 1) → Fin (P.length - 1) → GPoly (LC m) := fun j i ↦ num ((Ml.getD i []).getD j O1.zero) with hA0f
  set Gf : Fin (P.length - 1) → GPoly (LC m) := fun j ↦ numF (f.getD j O1.zero) with hGf
  -- the coordinate equations
  have hcoord : ∀ Y : ℕ → T.F (m + 1),
      ((∑ i ∈ Finset.range (P.length - 1), (Y i : L) * θ ^ i)′ = ∑ j ∈ Finset.range (P.length - 1),
        ((M1.sem (f.getD j O1.zero) : T.F (m + 1)) : L) * θ ^ j) ↔
      ∀ j < (P.length - 1), (Y j)′ + ∑ i ∈ Finset.range (P.length - 1), T.Mθ m h1 P dθ i j * Y i =
        M1.sem (f.getD j O1.zero) := by
    intro Y
    have hdc := T.deriv_coords m h1 θ P hP hPm dθ hd Y
    rw [hPdeg] at hdc
    rw [hdc]
    constructor
    · intro hE j hj
      have h0 := hind (fun j ↦ (Y j)′ + ∑ i ∈ Finset.range (P.length - 1), T.Mθ m h1 P dθ i j * Y i -
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
    set Y : ℕ → T.F (m + 1) := fun i ↦ if hi : i < P.length - 1 then
      T.phi m (semV M b.2 ⟨i, hi⟩) / (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1))) else 0
      with hY
    refine ⟨Y, (hcoord Y).mpr fun j hj ↦ ?_⟩
    have hphi := T.sysSol_phiG m wD bD S.hD qs hs (semMat M A0f) _ (semV M b.2) (GPoly.toPoly M r.1)
      ⟨j, hj⟩ hsS
    simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton, List.getD_cons_zero,
      map_mul, semMat, Matrix.of_apply] at hphi
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
    rw [hYj, hfv]
    have hG' : GPoly.toPoly M (Gf ⟨j, hj⟩) = GPoly.toPoly M (numF (f.getD j O1.zero)) := rfl
    rw [hG'] at hphi
    rw [Derivation.leibniz_div, Derivation.leibniz, T.deriv_ratCast, smul_zero, zero_add,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    rw [T.phi_C_ratCast] at hphi
    have hsum : ∑ x : Fin (P.length - 1), T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ x)) / T.phi m qs *
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
  · rintro ⟨Y, hY⟩
    have heq := (hcoord Y).mp hY
    obtain ⟨Z, d, hd0, hZ⟩ := T.exists_common_den m htr (fun i : Fin (P.length - 1) ↦ Y i)
    have hphid : T.phi m d ≠ 0 := fun h0' ↦ hd0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hphiq : T.phi m qs ≠ 0 := fun h0' ↦ hqs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hYi : ∀ i : Fin (P.length - 1), Y i = T.phi m (Z i) / T.phi m d := fun i ↦ by
      rw [← hZ i, mul_div_cancel_right₀ _ hphid]
    have hsol : SysSol wD bD qs hs (semMat M A0f)
        (fun j ↦ ∑ l ∈ Finset.range [Gf].length, C (algebraMap Cc (T.F m) (([1] : List Cc).getD l 0)) *
          GPoly.toPoly M (([Gf].getD l fun _ ↦ []) j)) Z d := by
      refine T.sysSol_of_phiG m htr wD bD S.hD qs hs (semMat M A0f) _ Z d fun j ↦ ?_
      have hj := heq j j.2
      simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton, List.getD_cons_zero,
        map_one, one_mul]
      rw [← Fin.sum_univ_eq_sum_range (fun i ↦ T.Mθ m h1 P dθ i j * Y i)] at hj
      have hMθ' : ∀ i : Fin (P.length - 1), T.Mθ m h1 P dθ i j = T.phi m (GPoly.toPoly M (A0f j i)) / T.phi m qs :=
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


variable {m}

/-- `primSysC` meets the solver specification (primitive level). -/
theorem primSpec (hm : m < T.n) (h0 : T.Tr m) (htr : Transcendental (T.F m) (T.ts m))
    {η : LC m} (hk : ks m = .prim η) (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h0) lim) :
    T.SolverSpec m h0 ((T.MP m h0).sem η) 0 (primSysC Fc ks m η lim) where
  hD := T.phi_DzL m hm hk h0
  sound := fun n A0 q hh G0 Den out hres ↦ T.primSysC_sound m h0 η n A0 q hh G0 lim Den out hres
  den := fun n A0 q hh G0 r hres ↦ by
    obtain ⟨B, hB⟩ := primSysC_den hres
    have hmo := primSysC_monic hres
    have hq := (isMonicC_spec (T.MP m h0) q hmo.1).ne_zero
    have hh' := (isMonicC_spec (T.MP m h0) hh hmo.2).ne_zero
    refine ⟨?_, hq, hh'⟩
    rw [hB, T.wSys_Den m h0 η n A0 q hh G0 B]
    exact mul_ne_zero hh' (pow_ne_zero _ hq)
  complete := fun n A0 q hh G0 Den out hres c hc Z d hd hsol ↦
    T.primSysC_complete m h0 η n A0 q hh G0 hm htr hk lim hlim Den out hres c hc Z d hd hsol

/-- `expSysC` meets the solver specification (exponential level). -/
theorem expSpec (hm : m < T.n) (h0 : T.Tr m) (htr : Transcendental (T.F m) (T.ts m))
    {a : LC m} (hk : ks m = .exp a) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hrdeD : ∀ c : LC m, RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h0) ((T.MP m h0).sem c)′ (rdeD c))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h0).sem ((MO Fc ks m).deriv a) * z ≠ 0) :
    T.SolverSpec m h0 0 ((T.MP m h0).sem ((MO Fc ks m).deriv a)) (expSysC Fc ks m a rdeD) where
  hD := T.phi_DzL_exp m hm hk h0
  sound := fun n A0 q hh G0 Den out hres ↦ T.expSysC_sound m h0 n A0 q hh G0 a rdeD Den out hres
  den := fun n A0 q hh G0 r hres ↦ by
    obtain ⟨B, hB⟩ := expSysC_den hres
    have hmo := expSysC_monic hres
    have hq := (isMonicC_spec (T.MP m h0) q hmo.1).ne_zero
    have hh' := (isMonicC_spec (T.MP m h0) hh hmo.2).ne_zero
    refine ⟨?_, hq, hh'⟩
    rw [hB, T.wSysE_Den m h0 ((MO Fc ks m).deriv a) n A0 q hh G0 B]
    exact mul_ne_zero hh' (pow_ne_zero _ hq)
  complete := fun n A0 q hh G0 Den out hres c hc Z d hd hsol ↦
    T.expSysC_complete m h0 n A0 q hh G0 hm htr a hk rdeD hrdeD hom Den out hres c hc Z d hd hsol

/-- `expSysT` meets the solver specification (exponential level, triangular limits). -/
theorem expTSpec (hm : m < T.n) (h0 : T.Tr m) (htr : Transcendental (T.F m) (T.ts m))
    {a : LC m} (hk : ks m = .exp a) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hrdeD : ∀ c : LC m, RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h0) ((T.MP m h0).sem c)′ (rdeD c))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h0).sem ((MO Fc ks m).deriv a) * z ≠ 0) :
    T.SolverSpec m h0 0 ((T.MP m h0).sem ((MO Fc ks m).deriv a)) (expSysT Fc ks m a rdeD) where
  hD := T.phi_DzL_exp m hm hk h0
  sound := fun n A0 q hh G0 Den out hres ↦ T.expSysT_sound m h0 n A0 q hh G0 a rdeD Den out hres
  den := fun n A0 q hh G0 r hres ↦ by
    obtain ⟨B, hB⟩ := expSysT_den hres
    have hmo := expSysT_monic hres
    have hq := (isMonicC_spec (T.MP m h0) q hmo.1).ne_zero
    have hh' := (isMonicC_spec (T.MP m h0) hh hmo.2).ne_zero
    refine ⟨?_, hq, hh'⟩
    rw [hB, T.wSysE_Den m h0 ((MO Fc ks m).deriv a) n A0 q hh G0 B]
    exact mul_ne_zero hh' (pow_ne_zero _ hq)
  complete := fun n A0 q hh G0 Den out hres c hc Z d hd hsol ↦
    T.expSysT_complete m h0 n A0 q hh G0 hm htr a hk rdeD hrdeD hom Den out hres c hc Z d hd hsol

end MTower

end Curves.MT
