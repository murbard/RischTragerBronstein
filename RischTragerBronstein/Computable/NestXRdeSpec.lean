import RischTragerBronstein.Computable.NestXCert
import RischTragerBronstein.RDE.LogBounds

/-!
# Mixed towers: the coefficients `f = h′ + ∑ cⱼ wⱼ′ / wⱼ` of the Risch equations

`FRepOK M fr`: the coefficients `cⱼ` of the logarithmic part are constants. `sem_fCode`: the value
of the code of `f`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.NestX

open Tower.NestP Tower.NestM

section Generic

variable {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

/-- The logarithmic part of `fr` has constant coefficients. -/
def FRepOK (fr : FRep α) : Prop := ∀ cw ∈ fr.logs, (M.sem cw.1)′ = 0

/-- The value of the logarithmic part. -/
noncomputable def logSumV (logs : List (α × α)) : K :=
  (logs.map fun cw ↦ M.sem cw.1 * logDeriv (M.sem cw.2)).sum

lemma sem_fCode (fr : FRep α) : M.sem (fCode O fr) = (M.sem fr.h)′ + logSumV M fr.logs := by
  unfold fCode logSumV
  induction fr.logs with
  | nil => simp [M.sem_deriv]
  | cons cw l ih =>
    rw [List.foldr_cons, M.sem_add, M.sem_mul, M.sem_mul, M.sem_deriv, M.sem_inv, ih,
      List.map_cons, List.sum_cons, logDeriv, div_eq_mul_inv]
    ring

end Generic

/-! ### Integer vectors and the logarithmic bound -/

lemma mem_intVecs : ∀ (ds : List ℕ) (v : List ℤ), v.length = ds.length →
    (∀ j < ds.length, |v.getD j 0| ≤ (ds.getD j 0 : ℤ)) → v ∈ intVecs ds
  | [], v, hl, _ => by
    rw [List.length_nil, List.length_eq_zero_iff] at hl
    subst hl; simp [intVecs]
  | d :: ds, v, hl, hb => by
    obtain ⟨x, v', rfl⟩ : ∃ x v', v = x :: v' := by
      cases v with
      | nil => simp at hl
      | cons x v' => exact ⟨x, v', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hv' : v' ∈ intVecs ds := mem_intVecs ds v' hl fun j hj ↦ by
      simpa using hb (j + 1) (by simp; omega)
    have hx : |x| ≤ (d : ℤ) := by simpa using hb 0 (by simp)
    rw [abs_le] at hx
    rw [intVecs]
    simp only [List.mem_flatMap, List.mem_map]
    refine ⟨v', hv', ?_⟩
    simp
    exact ⟨(x + d).toNat, by omega, by omega⟩

/-- A fold of `max` dominates each of its values. -/
lemma le_foldr_max_of_mem {β : Type*} (g : β → Option ℕ) :
    ∀ (l : List β) (x : β), x ∈ l → ∀ n, g x = some n →
      n ≤ l.foldr (fun v acc ↦ match g v with | some k => max acc k | none => acc) 0
  | [], _, hx, _, _ => by simp at hx
  | y :: l, x, hx, n, hn => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [hn]; exact le_max_right _ _
    · have := le_foldr_max_of_mem g l x hx n hn
      split
      · exact this.trans (le_max_left _ _)
      · exact this

end Tower.NestX

namespace Tower.NestM

open Tower.NestP Tower.NestX

namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : (m : ℕ) → KindN m}
variable (T : NestMTower Kc E ks)

/-- **`ratVal` recognizes rational values.** -/
theorem ratVal_spec (m : ℕ) (h : T.Tr m) (c : Code (m + 1)) (q : ℚ)
    (hc : (T.MP m h).sem c = (q : T.F m)) : ratVal ks m c = some q := by
  classical
  set vs : List (Code (m + 1)) := [c, (opsM ks m).one] with hvs
  have hrel : (List.zipWith (fun c v ↦ algebraMap Kc (T.F m) c * (T.MP m h).sem v)
      [(1 : Kc), -((q : ℚ) : Kc)] vs).sum = 0 := by
    simp only [hvs, List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_cons, List.sum_nil,
      (T.MP m h).sem_one, hc, map_one, map_neg, map_ratCast]
    ring
  obtain ⟨u, hu, hu0⟩ := T.exists_coeff0_ne m h vs _ rfl hrel (by simp)
  unfold ratVal
  obtain ⟨u', hu'⟩ : ∃ u', (consys ks m vs).find? (fun u ↦ u.getD 0 0 ≠ 0) = some u' := by
    rcases hf : (consys ks m vs).find? (fun u ↦ u.getD 0 0 ≠ 0) with _ | u'
    · exact absurd (List.find?_eq_none.mp hf u hu) (by simpa using hu0)
    · exact ⟨u', hf⟩
  rw [← hvs, hu']
  simp only
  have hmem := List.mem_of_find?_eq_some hu'
  have hne : u'.getD 0 0 ≠ 0 := by simpa using List.find?_some hu'
  have hs := T.consys_sound m h vs u' hmem
  simp only [hvs, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append,
    List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_cons, List.sum_nil,
    (T.MP m h).sem_one, hc, mul_one, add_zero] at hs
  congr 1
  have hq : ((u'.getD 0 0 * q + u'.getD 1 0 : ℚ) : T.F m) = 0 := by
    rw [← map_ratCast (algebraMap Kc (T.F m)), ← map_ratCast (algebraMap ℚ Kc)]
    simp only [map_ratCast] at hs ⊢
    rw [← hs]
    simp only [eq_ratCast]
    push_cast
    ring
  have hq' : u'.getD 0 0 * q + u'.getD 1 0 = 0 := by exact_mod_cast hq
  field_simp
  linarith

end NestMTower

end Tower.NestM
