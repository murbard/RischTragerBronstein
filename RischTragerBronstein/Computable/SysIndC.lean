import RischTragerBronstein.Computable.DetF
import RischTragerBronstein.Computable.GEuclidDegree

/-!
# Coupled Risch systems: the indicial norm, computed

For a system with codes `q`, `dq` (the tower derivative of `q`, `q` monic of degree `d`) and a
matrix of codes `A₀`, the indicial norm `ρ = indNorm' q dq A₀` has degree `≤ d n`. Its values at
`0, …, d n` are determinants of multiplication matrices (`indValC`: a determinant over polynomial
codes, remainders by `divMod`, a determinant over codes), and its coefficients are recovered by
Lagrange interpolation (`indCoeffsC`, `sem_indCoeffsC`, checked by `vandCheck`). Every natural
indicial root `e` then satisfies `∑ eʲ cⱼ = 0` for the coefficient codes (`indCoeffsC_root`).
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace Tower.Sys

variable {α K : Type*} [Field K] [Differential K] (O : COps α)

/-- The determinant of a matrix of polynomial codes. -/
def pdetC (n : ℕ) (A : Fin n → Fin n → GPoly α) : GPoly α :=
  detF [] [O.one] (GPoly.add O) (GPoly.mul O) (GPoly.neg O) n A

/-- The multiplication matrix of `P` modulo `q` (size `d`), in codes. -/
def multMatC (d : ℕ) (q P : GPoly α) : Fin d → Fin d → α :=
  fun i j ↦ (GPoly.divMod O (GPoly.mul O P (GPoly.monomial O j O.one)) q).2.getD i O.zero

/-- The matrix `A₀ − k dq I` in codes. -/
def indMatC {n : ℕ} (dq : GPoly α) (A0 : Fin n → Fin n → GPoly α) (k : ℕ) :
    Fin n → Fin n → GPoly α :=
  fun i j ↦ if i = j then GPoly.sub O (A0 i j) (GPoly.mul O [O.natCast k] dq) else A0 i j

/-- The value `ρ(k)` of the indicial norm. -/
def indValC (d n : ℕ) (q dq : GPoly α) (A0 : Fin n → Fin n → GPoly α) (k : ℕ) : α :=
  detF O.zero O.one O.add O.mul O.neg d (multMatC O d q (pdetC O n (indMatC O dq A0 k)))

/-- **The coefficients of the indicial norm** by interpolation at `0, …, d n`
(`rc` embeds the rationals). -/
def indCoeffsC (rc : ℚ → α) (d n : ℕ) (q dq : GPoly α) (A0 : Fin n → Fin n → GPoly α) : List α :=
  let vals := (List.range (d * n + 1)).map (indValC O d n q dq A0)
  (List.range (d * n + 1)).map fun j ↦
    ((List.range (d * n + 1)).map fun k ↦
      O.mul (rc ((lagrangeL (d * n) k).getD j 0)) (vals.getD k O.zero)).foldr O.add O.zero

variable {O} (M : CField α K O)

lemma sem_getD (l : List α) (i : ℕ) : (l.map M.sem).getD i 0 = M.sem (l.getD i O.zero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [M.sem_zero]

lemma coeff_toPoly_sem (p : GPoly α) (i : ℕ) : (GPoly.toPoly M p).coeff i = M.sem (p.getD i O.zero) := by
  rw [GPoly.coeff_toPoly, sem_getD]

lemma sem_foldr_add (l : List α) : M.sem (l.foldr O.add O.zero) = (l.map M.sem).sum := by
  induction l with
  | nil => simp [M.sem_zero]
  | cons a l ih => simp [M.sem_add, ih]

lemma toPoly_pdetC (n : ℕ) (A : Fin n → Fin n → GPoly α) :
    GPoly.toPoly M (pdetC O n A) = (Matrix.of fun i j ↦ GPoly.toPoly M (A i j)).det :=
  detF_spec _ _ _ _ _ (GPoly.toPoly M) rfl (by simp [M.sem_one]) (GPoly.toPoly_add M)
    (GPoly.toPoly_mul M) (GPoly.toPoly_neg M) n A

/-- The code remainder is the remainder by a monic divisor. -/
lemma toPoly_divMod_snd (p q : GPoly α) (hq : (GPoly.toPoly M q).Monic) :
    GPoly.toPoly M (GPoly.divMod O p q).2 = GPoly.toPoly M p %ₘ GPoly.toPoly M q := by
  have hs := GPoly.divMod_spec M p q
  have hlt := GPoly.divMod_degree_lt M p q hq.ne_zero
  have h : GPoly.toPoly M q ∣ (GPoly.toPoly M (GPoly.divMod O p q).1 * GPoly.toPoly M q +
      GPoly.toPoly M (GPoly.divMod O p q).2) - GPoly.toPoly M (GPoly.divMod O p q).2 :=
    ⟨GPoly.toPoly M (GPoly.divMod O p q).1, by ring⟩
  rw [hs, modByMonic_eq_of_dvd_sub hq h, (modByMonic_eq_self_iff hq).mpr hlt]

lemma sem_multMatC (q P : GPoly α) (hq : (GPoly.toPoly M q).Monic) (i j : Fin (GPoly.toPoly M q).natDegree) :
    M.sem (multMatC O (GPoly.toPoly M q).natDegree q P i j) =
      multMat (GPoly.toPoly M q) (GPoly.toPoly M P) i j := by
  rw [multMatC, ← coeff_toPoly_sem, toPoly_divMod_snd M _ _ hq, GPoly.toPoly_mul,
    GPoly.toPoly_monomial, M.sem_one, C_1, one_mul]
  rfl

lemma sum_map_range {γ : Type*} [AddCommMonoid γ] (f : ℕ → γ) :
    ∀ N, ((List.range N).map f).sum = ∑ k ∈ Finset.range N, f k
  | 0 => by simp
  | N + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_map_range f N,
      Finset.sum_range_succ]; simp

variable {n : ℕ}

/-- The semantic matrix of a matrix of codes. -/
noncomputable def semMat (A : Fin n → Fin n → GPoly α) : Matrix (Fin n) (Fin n) K[X] :=
  Matrix.of fun i j ↦ GPoly.toPoly M (A i j)

lemma sem_indValC (d : ℕ) (q dq : GPoly α) (A0 : Fin n → Fin n → GPoly α) (k : ℕ)
    (hq : (GPoly.toPoly M q).Monic) (hd : (GPoly.toPoly M q).natDegree = d) :
    M.sem (indValC O d n q dq A0 k) =
      (indNorm' (GPoly.toPoly M q) (GPoly.toPoly M dq) (semMat M A0)).eval (k : K) := by
  subst hd
  rw [indNorm'_eval, indValC, detF_spec _ _ _ _ _ M.sem M.sem_zero M.sem_one M.sem_add M.sem_mul
    M.sem_neg]
  congr 1
  ext i j
  rw [Matrix.of_apply, sem_multMatC M _ _ hq, toPoly_pdetC]
  congr 3
  ext i' j'
  simp only [Matrix.of_apply, indMatC, semMat]
  split_ifs <;> simp [M.sem_natCast]

/-- **The interpolated coefficients are the coefficients of the indicial norm.** -/
theorem sem_indCoeffsC (rc : ℚ → α) (hrc : ∀ r, M.sem (rc r) = r) [CharZero K] (d : ℕ)
    (q dq : GPoly α) (A0 : Fin n → Fin n → GPoly α)
    (hq : (GPoly.toPoly M q).Monic) (hd : (GPoly.toPoly M q).natDegree = d)
    (hv : vandCheck (d * n) = true) (j : ℕ) :
    M.sem ((indCoeffsC O rc d n q dq A0).getD j O.zero) =
      (indNorm' (GPoly.toPoly M q) (GPoly.toPoly M dq) (semMat M A0)).coeff j := by
  have hdeg := natDegree_indNorm' (GPoly.toPoly M q) (GPoly.toPoly M dq) (semMat M A0)
  rw [hd] at hdeg
  by_cases hj : j ≤ d * n
  · rw [coeff_eq_interp (d * n) hv _ hdeg j hj, indCoeffsC]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range,
      sem_foldr_add, List.map_map, sum_map_range]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' := Finset.mem_range.mp hk
    simp only [Function.comp_apply, M.sem_mul, hrc]
    have hl : k < ((List.range (d * n + 1)).map (indValC O d n q dq A0)).length := by simp; omega
    rw [List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_range,
      sem_indValC M d q dq A0 k hq hd]
  · rw [List.getD_eq_default _ _ (by simp [indCoeffsC]; omega), M.sem_zero,
      coeff_eq_zero_of_natDegree_lt (by omega)]

lemma length_indCoeffsC (rc : ℚ → α) (d : ℕ) (q dq : GPoly α) (A0 : Fin n → Fin n → GPoly α) :
    (indCoeffsC O rc d n q dq A0).length = d * n + 1 := by
  simp [indCoeffsC]

/-- **A root of the indicial norm is a root of the coded coefficient list.** -/
theorem indCoeffsC_root (rc : ℚ → α) (hrc : ∀ r, M.sem (rc r) = r) [CharZero K] (d : ℕ)
    (q dq : GPoly α) (A0 : Fin n → Fin n → GPoly α)
    (hq : (GPoly.toPoly M q).Monic) (hd : (GPoly.toPoly M q).natDegree = d)
    (hv : vandCheck (d * n) = true) (e : K)
    (he : (indNorm' (GPoly.toPoly M q) (GPoly.toPoly M dq) (semMat M A0)).eval e = 0) :
    ∑ j ∈ Finset.range (indCoeffsC O rc d n q dq A0).length,
      e ^ j * M.sem ((indCoeffsC O rc d n q dq A0).getD j O.zero) = 0 := by
  have hdeg := natDegree_indNorm' (GPoly.toPoly M q) (GPoly.toPoly M dq) (semMat M A0)
  rw [hd] at hdeg
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)] at he
  rw [length_indCoeffsC, ← he]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [sem_indCoeffsC M rc hrc d q dq A0 hq hd hv, mul_comm]

end Tower.Sys
