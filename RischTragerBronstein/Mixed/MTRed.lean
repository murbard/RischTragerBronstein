import RischTragerBronstein.Mixed.MTBasics
import RischTragerBronstein.Computable.GReduce

/-!
# Mixed towers: reducing codes

`redL m q`: the code `q` of level `m` with every fraction reduced by its gcd (at level `0` the
coefficients in `ℚ(x)`, at level `m + 1` the fraction over level `m`, recursively). The value is
unchanged (`ev_redL`). The algorithms use it to keep the codes small.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.NestM

variable {α : Type} {K Cs : Type*} [Field K] [Differential K] [CharZero K] [Field Cs] [CharZero Cs]
variable (ι : Cs →+* K) {O : COps α} (M : CField α K O)

lemma sQ_map (g : α → α) (hg : ∀ a, M.sem (g a) = M.sem a) (e : List ℚ) (ws : List α) :
    Tower.NestP.sQ M e (ws.map g) = Tower.NestP.sQ M e ws := by
  unfold Tower.NestP.sQ
  rw [List.length_map]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [List.getD_eq_getElem (ws.map g) _ (by simpa using Finset.mem_range.mp hi),
    List.getD_eq_getElem ws _ (Finset.mem_range.mp hi), List.getElem_map, hg]

lemma sC_map (g : α → α) (hg : ∀ a, M.sem (g a) = M.sem a) (c : List Cs) (ws : List α) :
    Tower.NestP.sC ι M c (ws.map g) = Tower.NestP.sC ι M c ws := by
  unfold Tower.NestP.sC
  rw [List.length_map]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [List.getD_eq_getElem (ws.map g) _ (by simpa using Finset.mem_range.mp hi),
    List.getD_eq_getElem ws _ (Finset.mem_range.mp hi), List.getElem_map, hg]

/-- **A solver fed with value-preserving rewrites of its inputs keeps its specification.** -/
lemma RdeSpecK.map_input {f : K} {lk : List α → List (List ℚ × α)} (h : RdeSpecK ι M f lk)
    (g : α → α) (hg : ∀ a, M.sem (g a) = M.sem a) : RdeSpecK ι M f (fun ws ↦ lk (ws.map g)) where
  sound ws r hr := by
    rw [h.sound _ r hr, sQ_map M g hg]
  complete ws c hc z hz := by
    have := h.complete (ws.map g) c (fun i hi ↦ hc i (by simpa using hi)) z
      (by rw [sC_map ι M g hg]; exact hz)
    simpa using this

end Tower.NestM

namespace Curves.MT

open CPoly Sup Curves.LT

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- Reduce all fractions of a code. -/
def redL : (m : ℕ) → LC m → LC m
  | 0, q => (q : GPoly (GFrac ℚ)).map (GPoly.redFrac (COps.ofDecidableField ℚ))
  | m + 1, q =>
    let q' := GPoly.redFrac (MO Fc ks m) q
    ((q'.1.map (redL m), q'.2.map (redL m)) : LC (m + 1))

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma evP_map_eq (m : ℕ) (f : LC m → LC m) (hf : ∀ q, T.ev m (f q) = T.ev m q)
    (p : GPoly (LC m)) : T.evP m (p.map f) = T.evP m p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [evP, evPL, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih]
    congr 1
    exact hf a

lemma ev_redL_zero (q : LC 0) : T.ev 0 (redL Fc ks 0 q) = T.ev 0 q := by
  change (GPoly.toPoly (xM T.hC T.S T.hx) ((q : GPoly (GFrac ℚ)).map
      (GPoly.redFrac (COps.ofDecidableField ℚ)))).eval T.S.y =
    (GPoly.toPoly (xM T.hC T.S T.hx) (q : GPoly (GFrac ℚ))).eval T.S.y
  congr 1
  set M0 := CField.ofHom (algebraMap ℚ Cc) T.hC
  induction (q : GPoly (GFrac ℚ)) with
  | nil => rfl
  | cons a p ih =>
    rw [List.map_cons, GPoly.toPoly_cons, GPoly.toPoly_cons, ih]
    congr 2
    rw [sem_xModel, sem_xModel]
    by_cases ha : GPoly.toPoly M0 a.2 = 0
    · have hz : GPoly.isZero (COps.ofDecidableField ℚ) a.2 = true := (GPoly.isZero_iff M0 _).mpr ha
      simp [GPoly.redFrac, hz]
    · obtain ⟨h1, h2⟩ := GPoly.redFrac_spec M0 a ha
      rw [toPoly_ofHom_list, toPoly_ofHom_list, toPoly_ofHom_list, toPoly_ofHom_list] at h1
      rw [toPoly_ofHom_list] at h2 ha
      have hne : ∀ Q : Cc[X], Q ≠ 0 → aeval T.S.x Q ≠ 0 := fun Q hQ h0 ↦ T.S.htr ⟨Q, hQ, h0⟩
      have h1' := congrArg (aeval T.S.x) h1
      rw [map_mul, map_mul] at h1'
      rw [div_eq_div_iff (hne _ h2) (hne _ ha)]
      linear_combination h1'

/-- **Reducing keeps the value.** -/
theorem ev_redL : ∀ (m : ℕ), T.Tr m → ∀ q : LC m, T.ev m (redL Fc ks m q) = T.ev m q
  | 0, _, q => T.ev_redL_zero q
  | m + 1, h, q => by
    have hm : T.Tr m := fun i hi ↦ h i (by omega)
    have ih := ev_redL m hm
    show T.evP m ((GPoly.redFrac (MO Fc ks m) q).1.map (redL Fc ks m)) /
        T.evP m ((GPoly.redFrac (MO Fc ks m) q).2.map (redL Fc ks m)) = T.evP m q.1 / T.evP m q.2
    rw [T.evP_map_eq m _ ih, T.evP_map_eq m _ ih]
    by_cases hq : GPoly.toPoly (T.MP m hm) q.2 = 0
    · have hz : GPoly.isZero (MO Fc ks m) q.2 = true := (GPoly.isZero_iff (T.MP m hm) _).mpr hq
      simp [GPoly.redFrac, hz]
    · obtain ⟨h1, h2⟩ := GPoly.redFrac_spec (T.MP m hm) q hq
      have hne : ∀ Q : (T.F m)[X], Q ≠ 0 → aeval (T.ts m) Q ≠ 0 := fun Q hQ h0 ↦
        (h m (Nat.lt_succ_self m)) ⟨Q, hQ, h0⟩
      have h1' := congrArg (aeval (T.ts m)) h1
      rw [map_mul, map_mul] at h1'
      simp only [T.aeval_toPoly (T.MP m hm) (T.sem_MP m hm)] at h1'
      have hd2 : T.evP m (GPoly.redFrac (MO Fc ks m) q).2 ≠ 0 := by
        rw [← T.aeval_toPoly (T.MP m hm) (T.sem_MP m hm)]; exact hne _ h2
      have hdq : T.evP m q.2 ≠ 0 := by
        rw [← T.aeval_toPoly (T.MP m hm) (T.sem_MP m hm)]; exact hne _ hq
      rw [div_eq_div_iff hd2 hdq]
      linear_combination h1'

end MTower

end Curves.MT
