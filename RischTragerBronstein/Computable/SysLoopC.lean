import RischTragerBronstein.Computable.SysLoop
import RischTragerBronstein.Computable.SysIndC

/-!
# Coupled Risch systems: the coefficient loop on codes

The loop of `SysLoop` on vectors of polynomial codes over a computable field (`stepAlgC`,
`stepDiffC`, `loopC`). Every step denotes the corresponding semantic step (`semBs_stepAlgC`,
`semBs_stepDiffC`), so the stage invariants carry over (`loopC_stage`), given a code-level solver
one level down (`SysSpecKC`) and verified inverses of the leading matrices.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

open Tower.NestM Tower.NestP

section Codes

variable {α : Type*} (O : COps α) {n : ℕ}

/-- A vector read from a list (not inlined, so that the list is evaluated before the call). -/
@[noinline] def vecOfList {β : Type*} (l : List β) (h : l.length = n) : Fin n → β :=
  fun i ↦ l[i]'(by rw [h]; exact i.2)

/-- Materialize a vector (evaluate every entry once; not inlined, so that the list is shared). -/
@[inline] def vecM {β : Type*} (v : Fin n → β) : Fin n → β :=
  let l := List.ofFn v
  vecOfList l (List.length_ofFn)

lemma vecM_eq {β : Type*} (v : Fin n → β) : vecM v = v := by
  funext i; simp [vecM, vecOfList]

/-- `∑_{l ∈ L} f l` on polynomial codes. -/
def sumC (L : List ℕ) (f : ℕ → GPoly α) : GPoly α := L.foldr (fun x acc ↦ GPoly.add O (f x) acc) []

/-- `∑ⱼ f j` on polynomial codes. -/
def sumF (f : Fin n → GPoly α) : GPoly α :=
  (List.finRange n).foldr (fun j acc ↦ GPoly.add O (f j) acc) []

/-- `∑ⱼ f j` on codes. -/
def sumFa (f : Fin n → α) : α := (List.finRange n).foldr (fun j acc ↦ O.add (f j) acc) O.zero

/-- The derivation `t′ = w0 + b t` on polynomial codes. -/
def DzLC (w0 b : α) (P : GPoly α) : GPoly α :=
  GPoly.add O (GPoly.mapD O P) (GPoly.mul O [w0, b] (GPoly.derivX O P))

variable (w0 b : α) (A B : Fin n → Fin n → GPoly α) (cst : ℚ → α) (Cl : List (Fin n → GPoly α))
  (δ : ℕ)

/-- `A Y′ + B Y` on codes. -/
def LopVC (Y : Fin n → GPoly α) (i : Fin n) : GPoly α :=
  sumF O fun j ↦ GPoly.add O (GPoly.mul O (A i j) (DzLC O w0 b (Y j))) (GPoly.mul O (B i j) (Y j))

/-- `∑ eₗ Cₗ` on codes. -/
def SqVC (e : List ℚ) (i : Fin n) : GPoly α :=
  sumC O (List.range Cl.length) fun l ↦ GPoly.smul O (cst (e.getD l 0)) ((Cl.getD l fun _ ↦ []) i)

/-- The residual on codes. -/
def resQVC (e : List ℚ) (Y : Fin n → GPoly α) (i : Fin n) : GPoly α :=
  GPoly.sub O (LopVC O w0 b A B Y i) (SqVC O cst Cl e i)

/-- The right-hand side at degree `k + δ` on codes. -/
def rkVC (k : ℕ) (bb : List ℚ × (Fin n → GPoly α)) : Fin n → α :=
  vecM fun i ↦ O.neg ((resQVC O w0 b A B cst Cl bb.1 bb.2 i).getD (k + δ) O.zero)

/-- Matrix times vector on codes. -/
def mvC (P : Fin n → Fin n → α) (v : Fin n → α) : Fin n → α :=
  vecM fun i ↦ sumFa O fun j ↦ O.mul (P i j) (v j)

/-- A vector read from a list (the list is data, so it is evaluated once). -/
@[noinline] def listFn {β : Type*} (l : List β) (d : β) : Fin n → β := fun i ↦ l.getD i d

lemma listFn_ofFn {β : Type*} (v : Fin n → β) (d : β) : listFn (List.ofFn v) d = v := by
  funext i
  simp [listFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.2]

/-- The entries of a vector, as data. -/
@[noinline] def matL {β : Type*} (v : Fin n → β) : List β := List.ofFn v

lemma listFn_matL {β : Type*} (v : Fin n → β) (d : β) : listFn (matL v) d = v := listFn_ofFn v d

/-- A matrix as data (evaluated once). -/
@[noinline] def matData {β : Type} {n : ℕ} (f : Fin n → Fin n → β) : List (List β) :=
  List.ofFn fun i ↦ List.ofFn (f i)

/-- A matrix read from data. Partially applied to evaluated data, it does not recompute the entries
(a definition returning a function is eta-expanded by the compiler, so `vecM` alone does not
memoize). -/
@[noinline] def matFn {β : Type} {n : ℕ} (L : List (List β)) (d : β) : Fin n → Fin n → β :=
  fun i j ↦ (L.getD i []).getD j d

@[simp] lemma matFn_matData {β : Type} {n : ℕ} (f : Fin n → Fin n → β) (d : β) :
    matFn (matData f) d = f := by
  funext i j
  simp [matFn, matData, List.getD_eq_getElem?_getD, i.2, j.2]

/-- `rkVC` as data. -/
@[noinline] def rkL (k : ℕ) (bb : List ℚ × (Fin n → GPoly α)) : List α :=
  matL fun i ↦ O.neg ((resQVC O w0 b A B cst Cl bb.1 bb.2 i).getD (k + δ) O.zero)

lemma listFn_rkL (k : ℕ) (bb : List ℚ × (Fin n → GPoly α)) :
    listFn (rkL O w0 b A B cst Cl δ k bb) O.zero = rkVC O w0 b A B cst Cl δ k bb := by
  rw [rkL, listFn_matL, rkVC, vecM_eq]

/-- `mvC` as data. -/
@[noinline] def mvL (P : Fin n → Fin n → α) (v : List α) : List α :=
  matL fun i ↦ sumFa O fun j ↦ O.mul (P i j) (v.getD j O.zero)

lemma listFn_mvL (P : Fin n → Fin n → α) (v : List α) :
    listFn (mvL O P v) O.zero = mvC O P (listFn v O.zero) := by
  rw [mvL, listFn_matL, mvC, vecM_eq]; rfl

/-- The new vector of the algebraic step, as data. -/
@[noinline] def algNew (k : ℕ) (Y : Fin n → GPoly α) (r : List α) : List (GPoly α) :=
  matL fun i ↦ GPoly.add O (Y i) (GPoly.monomial O k (r.getD i O.zero))

/-- **The algebraic step** on codes. -/
def stepAlgC (PB : Fin n → Fin n → α) (k : ℕ) (Bs : List (List ℚ × (Fin n → GPoly α))) :
    List (List ℚ × (Fin n → GPoly α)) :=
  (Bs.map fun bb ↦ (bb.1, algNew O k bb.2 (mvL O PB (rkL O w0 b A B cst Cl δ k bb)))).map
    fun p ↦ (p.1, listFn p.2 [])

lemma stepAlgC_eq (PB : Fin n → Fin n → α) (k : ℕ) (Bs : List (List ℚ × (Fin n → GPoly α))) :
    stepAlgC O w0 b A B cst Cl δ PB k Bs =
      Bs.map fun bb ↦ (bb.1, let r := mvC O PB (rkVC O w0 b A B cst Cl δ k bb)
        fun i ↦ GPoly.add O (bb.2 i) (GPoly.monomial O k (r i))) := by
  rw [stepAlgC, List.map_map]
  refine List.map_congr_left fun bb _ ↦ ?_
  simp only [Function.comp_apply, algNew, listFn_matL]
  rw [← listFn_rkL, ← listFn_mvL]
  rfl

/-- The new vector of the differential step, as data. -/
@[noinline] def diffNew (k : ℕ) (Bs : List (List ℚ × (Fin n → GPoly α))) (r : List ℚ × (Fin n → α)) :
    List (GPoly α) :=
  matL fun i ↦ GPoly.add O (sumC O (List.range Bs.length) fun l ↦
    GPoly.smul O (cst (r.1.getD l 0)) ((Bs.getD l ([], fun _ ↦ [])).2 i)) (GPoly.monomial O k (r.2 i))

/-- **The differential step** on codes. -/
def stepDiffC (PA : Fin n → Fin n → α)
    (lowerC : ℕ → List (Fin n → α) → List (List ℚ × (Fin n → α))) (k : ℕ)
    (Bs : List (List ℚ × (Fin n → GPoly α))) : List (List ℚ × (Fin n → GPoly α)) :=
  ((lowerC k ((Bs.map fun bb ↦ mvL O PA (rkL O w0 b A B cst Cl δ k bb)).map fun l ↦
      listFn l O.zero)).map fun r ↦
    (vcomb Cl.length r.1 (Bs.map Prod.fst), diffNew O cst k Bs r)).map fun p ↦ (p.1, listFn p.2 [])

lemma stepDiffC_eq (PA : Fin n → Fin n → α)
    (lowerC : ℕ → List (Fin n → α) → List (List ℚ × (Fin n → α))) (k : ℕ)
    (Bs : List (List ℚ × (Fin n → GPoly α))) :
    stepDiffC O w0 b A B cst Cl δ PA lowerC k Bs =
      (lowerC k (Bs.map fun bb ↦ mvC O PA (rkVC O w0 b A B cst Cl δ k bb))).map fun r ↦
        (vcomb Cl.length r.1 (Bs.map Prod.fst), fun i ↦
          GPoly.add O (sumC O (List.range Bs.length) fun l ↦
            GPoly.smul O (cst (r.1.getD l 0)) ((Bs.getD l ([], fun _ ↦ [])).2 i))
            (GPoly.monomial O k (r.2 i))) := by
  have hws : ((Bs.map fun bb ↦ mvL O PA (rkL O w0 b A B cst Cl δ k bb)).map fun l ↦
      listFn l O.zero) = Bs.map fun bb ↦ mvC O PA (rkVC O w0 b A B cst Cl δ k bb) := by
    rw [List.map_map]
    refine List.map_congr_left fun bb _ ↦ ?_
    simp only [Function.comp_apply, listFn_mvL, listFn_rkL]
  rw [stepDiffC, hws, List.map_map]
  refine List.map_congr_left fun r _ ↦ ?_
  simp only [Function.comp_apply, diffNew, listFn_matL]

/-- **The loop** on codes, `k = N, …, 0`. -/
def loopC (alg : Bool) (PA PB : Fin n → Fin n → α)
    (lowerC : ℕ → List (Fin n → α) → List (List ℚ × (Fin n → α))) :
    ℕ → List (List ℚ × (Fin n → GPoly α)) → List (List ℚ × (Fin n → GPoly α))
  | 0, Bs => Bs
  | k + 1, Bs => loopC alg PA PB lowerC k
      (if alg then stepAlgC O w0 b A B cst Cl δ PB k Bs
       else stepDiffC O w0 b A B cst Cl δ PA lowerC k Bs)

/-- The initial basis on codes. -/
def initC (L : ℕ) : List (List ℚ × (Fin n → GPoly α)) :=
  (List.range L).map fun l ↦ (unitV L l, fun _ ↦ [])

end Codes

section Sem

variable {α K : Type*} [Field K] [Differential K] [CharZero K] {O : COps α} (M : CField α K O)
  {n : ℕ}

/-- Semantics of a vector of polynomial codes. -/
noncomputable def semV (Y : Fin n → GPoly α) : Fin n → K[X] := fun i ↦ GPoly.toPoly M (Y i)

/-- Semantics of a matrix of polynomial codes. -/
noncomputable def semPM (A : Fin n → Fin n → GPoly α) : Fin n → Fin n → K[X] :=
  fun i j ↦ GPoly.toPoly M (A i j)

/-- Semantics of a basis. -/
noncomputable def semBs (Bs : List (List ℚ × (Fin n → GPoly α))) : List (List ℚ × (Fin n → K[X])) :=
  Bs.map fun bb ↦ (bb.1, semV M bb.2)

/-- Semantics of the solutions one level down. -/
noncomputable def semR (R : List (List ℚ × (Fin n → α))) : List (List ℚ × (Fin n → K)) :=
  R.map fun r ↦ (r.1, fun i ↦ M.sem (r.2 i))

lemma toPoly_sumC (L : List ℕ) (f : ℕ → GPoly α) :
    GPoly.toPoly M (sumC O L f) = (L.map fun x ↦ GPoly.toPoly M (f x)).sum := by
  induction L with
  | nil => simp [sumC]
  | cons a L ih => simp only [sumC, List.foldr_cons, GPoly.toPoly_add] at ih ⊢; rw [ih]; simp

lemma toPoly_sumC_range (N : ℕ) (f : ℕ → GPoly α) :
    GPoly.toPoly M (sumC O (List.range N) f) = ∑ l ∈ Finset.range N, GPoly.toPoly M (f l) := by
  rw [toPoly_sumC, sum_map_range]

lemma toPoly_sumF (f : Fin n → GPoly α) :
    GPoly.toPoly M (sumF O f) = ∑ j, GPoly.toPoly M (f j) := by
  rw [Fin.sum_univ_def]
  unfold sumF
  induction (List.finRange n) with
  | nil => simp
  | cons a L ih => simp only [List.foldr_cons, GPoly.toPoly_add, ih, List.map_cons, List.sum_cons]

lemma sem_sumFa (f : Fin n → α) : M.sem (sumFa O f) = ∑ j, M.sem (f j) := by
  rw [Fin.sum_univ_def]
  unfold sumFa
  induction (List.finRange n) with
  | nil => simp [M.sem_zero]
  | cons a L ih => simp only [List.foldr_cons, M.sem_add, ih, List.map_cons, List.sum_cons]

lemma DzL_eq (w0 b : K) (P : K[X]) :
    DzL w0 b P = mapCoeffs P + (C w0 + C b * X) * derivative P := by
  simp only [DzL, implicitDeriv, Derivation.coe_add, Derivation.coe_smul, Pi.add_apply,
    Pi.smul_apply, Derivation.restrictScalars_apply, derivative'_apply, smul_eq_mul]

lemma toPoly_DzLC (w0 b : α) (P : GPoly α) :
    GPoly.toPoly M (DzLC O w0 b P) = DzL (M.sem w0) (M.sem b) (GPoly.toPoly M P) := by
  rw [DzL_eq, DzLC, GPoly.toPoly_add, GPoly.toPoly_mapD, GPoly.toPoly_mul, GPoly.toPoly_derivX]
  simp only [GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero]
  ring

variable (w0 b : α) (A B : Fin n → Fin n → GPoly α) (cst : ℚ → α)
  (hcst : ∀ q, M.sem (cst q) = q) (Cl : List (Fin n → GPoly α)) (δ : ℕ)

lemma toPoly_LopVC (Y : Fin n → GPoly α) (i : Fin n) :
    GPoly.toPoly M (LopVC O w0 b A B Y i) =
      LopV (M.sem w0) (M.sem b) (semPM M A) (semPM M B) (semV M Y) i := by
  rw [LopVC, toPoly_sumF, LopV]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [GPoly.toPoly_add, GPoly.toPoly_mul, GPoly.toPoly_mul, toPoly_DzLC]
  rfl

lemma getD_semCl (l : ℕ) :
    (Cl.map (semV M)).getD l 0 = semV M (Cl.getD l fun _ ↦ []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases Cl[l]? with
  | none => funext i; simp [semV]
  | some v => rfl

include hcst in
lemma toPoly_SqVC (e : List ℚ) (i : Fin n) :
    GPoly.toPoly M (SqVC O cst Cl e i) = SqV (Cl.map (semV M)) e i := by
  rw [SqVC, toPoly_sumC_range, SqV, List.length_map]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [GPoly.toPoly_smul, hcst, getD_semCl]
  rfl

include hcst in
lemma toPoly_resQVC (e : List ℚ) (Y : Fin n → GPoly α) (i : Fin n) :
    GPoly.toPoly M (resQVC O w0 b A B cst Cl e Y i) =
      resQV (M.sem w0) (M.sem b) (semPM M A) (semPM M B) (Cl.map (semV M)) e (semV M Y) i := by
  rw [resQVC, GPoly.toPoly_sub, toPoly_LopVC, toPoly_SqVC M cst hcst]
  rfl

include hcst in
lemma sem_rkVC (k : ℕ) (bb : List ℚ × (Fin n → GPoly α)) (i : Fin n) :
    M.sem (rkVC O w0 b A B cst Cl δ k bb i) =
      rkV (M.sem w0) (M.sem b) (semPM M A) (semPM M B) (Cl.map (semV M)) δ k (bb.1, semV M bb.2) i := by
  rw [rkVC, vecM_eq, M.sem_neg, rkV, ← coeff_toPoly_sem, toPoly_resQVC M w0 b A B cst hcst]

lemma sem_mvC (P : Fin n → Fin n → α) (v : Fin n → α) (i : Fin n) :
    M.sem (mvC O P v i) = mv (fun i j ↦ M.sem (P i j)) (fun j ↦ M.sem (v j)) i := by
  rw [mvC, vecM_eq, sem_sumFa, mv]
  exact Finset.sum_congr rfl fun j _ ↦ M.sem_mul _ _

include hcst in
/-- **The algebraic step denotes the semantic one.** -/
theorem semBs_stepAlgC (PB : Fin n → Fin n → α) (k : ℕ) (Bs : List (List ℚ × (Fin n → GPoly α)))
    (PA : Fin n → Fin n → K) (lower : ℕ → List (Fin n → K) → List (List ℚ × (Fin n → K))) :
    semBs M (stepAlgC O w0 b A B cst Cl δ PB k Bs) =
      sStep (M.sem w0) (M.sem b) (semPM M A) (semPM M B) (Cl.map (semV M)) δ true PA
        (fun i j ↦ M.sem (PB i j)) lower k (semBs M Bs) := by
  rw [stepAlgC_eq]
  simp only [semBs, sStep, if_true, List.map_map]
  refine List.map_congr_left fun bb _ ↦ ?_
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  funext i
  simp only [semV, vecM_eq, Pi.add_apply, GPoly.toPoly_add, GPoly.toPoly_monomial, sem_mvC]
  rw [show (fun j ↦ M.sem (rkVC O w0 b A B cst Cl δ k bb j)) = _ from
    funext fun j ↦ sem_rkVC M w0 b A B cst hcst Cl δ k bb j]

include hcst in
/-- **The differential step denotes the semantic one** (with the solutions one level down). -/
theorem semBs_stepDiffC (PA : Fin n → Fin n → α)
    (lowerC : ℕ → List (Fin n → α) → List (List ℚ × (Fin n → α))) (k : ℕ)
    (Bs : List (List ℚ × (Fin n → GPoly α))) :
    semBs M (stepDiffC O w0 b A B cst Cl δ PA lowerC k Bs) =
      sStepR (Cl.map (semV M)) k
        (semR M (lowerC k (Bs.map fun bb ↦ mvC O PA (rkVC O w0 b A B cst Cl δ k bb))))
        (semBs M Bs) := by
  rw [stepDiffC_eq]
  simp only [semBs, sStepR, semR, List.map_map, List.length_map]
  refine List.map_congr_left fun r _ ↦ ?_
  simp only [Function.comp_apply, Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  funext i
  simp only [semV, vecM_eq, Pi.add_apply, GPoly.toPoly_add, GPoly.toPoly_monomial, toPoly_sumC_range]
  congr 1
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  rw [GPoly.toPoly_smul, hcst]
  congr 1
  rw [NestTower.getD_map' _ _ ([], fun _ ↦ []) ([], 0) (Finset.mem_range.mp hl)]
  rfl

/-- Semantics of a vector of codes. -/
noncomputable def semVa (w : Fin n → α) : Fin n → K := fun i ↦ M.sem (w i)

lemma semBs_initC (L : ℕ) : semBs M (initC (n := n) L) = sInit L := by
  simp only [semBs, initC, sInit, List.map_map]
  refine List.map_congr_left fun l _ ↦ ?_
  simp only [Function.comp_apply, Prod.mk.injEq, true_and]
  funext i; simp [semV]

include hcst in
lemma ws_eq (PA : Fin n → Fin n → α) (k : ℕ) (Bs : List (List ℚ × (Fin n → GPoly α))) :
    (Bs.map fun bb ↦ mvC O PA (rkVC O w0 b A B cst Cl δ k bb)).map (semVa M) =
      (semBs M Bs).map fun bb ↦ mv (fun i j ↦ M.sem (PA i j))
        (rkV (M.sem w0) (M.sem b) (semPM M A) (semPM M B) (Cl.map (semV M)) δ k bb) := by
  simp only [semBs, List.map_map]
  refine List.map_congr_left fun bb _ ↦ ?_
  funext i
  simp only [Function.comp_apply, semVa, sem_mvC]
  rw [show (fun j ↦ M.sem (rkVC O w0 b A B cst Cl δ k bb j)) = _ from
    funext fun j ↦ sem_rkVC M w0 b A B cst hcst Cl δ k bb j]

variable {Cs : Type*} [Field Cs] [CharZero Cs] (ι : Cs →+* K)

/-- **The specification of a solver one level down at one right-hand side.** -/
def SysSpecAt (F : Fin n → Fin n → K) (ws : List (Fin n → K)) (R : List (List ℚ × (Fin n → K))) :
    Prop :=
  (∀ r ∈ R, ∀ i, (r.2 i)′ + mv F r.2 i =
    ∑ l ∈ Finset.range ws.length, ((r.1.getD l 0 : ℚ) : K) * (ws.getD l 0) i) ∧
  ∀ c : List Cs, (∀ l, ws.length ≤ l → c.getD l 0 = 0) → ∀ z : Fin n → K,
    (∀ i, (z i)′ + mv F z i = ∑ l ∈ Finset.range ws.length, ι (c.getD l 0) * (ws.getD l 0) i) →
    ∃ β : List Cs,
      (∀ l, c.getD l 0 = ∑ k ∈ Finset.range R.length,
        β.getD k 0 * algebraMap ℚ Cs ((R.getD k ([], 0)).1.getD l 0)) ∧
      ∀ i, z i = ∑ k ∈ Finset.range R.length, ι (β.getD k 0) * (R.getD k ([], 0)).2 i

variable (hιd : ∀ κ : Cs, (ι κ)′ = 0) (hιrat : ∀ q : ℚ, ι (algebraMap ℚ Cs q) = (q : K))

include hcst hιd hιrat in
/-- **The code loop satisfies the stage invariants**: from stage `j` to stage `0`, when the
leading matrices have verified inverses and the solver one level down meets its specification. -/
theorem loopC_stage (hA : ∀ i j, (semPM M A i j).natDegree ≤ δ)
    (hB : ∀ i j, (semPM M B i j).natDegree ≤ δ) (alg : Bool) (PA PB : Fin n → Fin n → α)
    (lowerC : ℕ → List (Fin n → α) → List (List ℚ × (Fin n → α)))
    (halg : alg = true → (∀ i j, (semPM M A i j).coeff δ = 0) ∧
      (∀ v, mv (fun i j ↦ (semPM M B i j).coeff δ) (mv (fun i j ↦ M.sem (PB i j)) v) = v) ∧
      (∀ v, mv (fun i j ↦ M.sem (PB i j)) (mv (fun i j ↦ (semPM M B i j).coeff δ) v) = v))
    (hdiff : alg = false →
      (∀ v, mv (fun i j ↦ (semPM M A i j).coeff δ) (mv (fun i j ↦ M.sem (PA i j)) v) = v) ∧
      (∀ v, mv (fun i j ↦ M.sem (PA i j)) (mv (fun i j ↦ (semPM M A i j).coeff δ) v) = v) ∧
      ∀ k : ℕ, ∃ F : Fin n → Fin n → K, (∀ z : Fin n → K, ∀ i,
        ∑ j, ((semPM M A i j).coeff δ * ((z j)′ + k * M.sem b * z j) +
          (semPM M B i j).coeff δ * z j) =
          ∑ j, (semPM M A i j).coeff δ * ((z j)′ + mv F z j)) ∧
        ∀ wsC, SysSpecAt ι F (wsC.map (semVa M)) (semR M (lowerC k wsC)))
    (N : ℕ) : ∀ (j : ℕ) (Bs : List (List ℚ × (Fin n → GPoly α))),
      SStageSound (M.sem w0) (M.sem b) (semPM M A) (semPM M B) (Cl.map (semV M)) δ j (semBs M Bs) →
      SStageComplete (M.sem w0) (M.sem b) (semPM M A) (semPM M B) (Cl.map (semV M)) δ ι N j
        (semBs M Bs) →
      SStageSound (M.sem w0) (M.sem b) (semPM M A) (semPM M B) (Cl.map (semV M)) δ 0
          (semBs M (loopC O w0 b A B cst Cl δ alg PA PB lowerC j Bs)) ∧
        SStageComplete (M.sem w0) (M.sem b) (semPM M A) (semPM M B) (Cl.map (semV M)) δ ι N 0
          (semBs M (loopC O w0 b A B cst Cl δ alg PA PB lowerC j Bs))
  | 0, Bs, hs, hc => ⟨hs, hc⟩
  | j + 1, Bs, hs, hc => by
    cases alg with
    | true =>
      obtain ⟨hAδ, hPB, hPBl⟩ := halg rfl
      have e := semBs_stepAlgC M w0 b A B cst hcst Cl δ PB j Bs (fun _ _ ↦ 0) (fun _ _ ↦ [])
      refine loopC_stage hA hB true PA PB lowerC halg hdiff N j _ ?_ ?_
      · simp only [if_true]
        rw [e]
        exact sStep_sound_alg _ _ _ _ _ δ hA hB hAδ _ _ hPB _ j _ hs
      · simp only [if_true]
        rw [e]
        exact sStep_complete_alg _ _ _ _ _ δ ι hιd hιrat hA hB hAδ _ _ hPBl _ j N _ hc
    | false =>
      obtain ⟨hPA, hPAl, hf⟩ := hdiff rfl
      obtain ⟨F, hff, hspec⟩ := hf j
      have e := semBs_stepDiffC M w0 b A B cst hcst Cl δ PA lowerC j Bs
      have hsp := hspec (Bs.map fun bb ↦ mvC O PA (rkVC O w0 b A B cst Cl δ j bb))
      rw [ws_eq M w0 b A B cst hcst Cl δ PA j Bs] at hsp
      refine loopC_stage hA hB false PA PB lowerC halg hdiff N j _ ?_ ?_
      · simp only [Bool.false_eq_true, if_false]
        rw [e]
        exact sStepR_sound_diff _ _ _ _ _ δ hA hB _ hPA j F hff _ _ hsp.1 hs
      · simp only [Bool.false_eq_true, if_false]
        rw [e]
        exact sStepR_complete_diff _ _ _ _ _ δ ι hιd hιrat hA hB _ hPAl j F hff N _ _ hsp.2 hc

end Sem

end Tower.Sys
