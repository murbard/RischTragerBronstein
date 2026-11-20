import RischTragerBronstein.Jacobian.TorsionBound
import RischTragerBronstein.Computable.LinSolve
import RischTragerBronstein.Computable.NullSpace

/-!
# A computable test for principal divisors

For a computable field `F` and an effective divisor `Γ` (points `(x_Q, y_Q)` with `2 y_Q ≠ 0` on
`y² = f`, multiplicities `k_Q`), `principalC f Γ A B` looks for a non-zero `a + b y` with
`deg a < A`, `deg b < B` vanishing on `Γ`: the jets of the basis functions `xⁱ`, `xʲ y` at every
point (branch jets by Newton's iteration, `branchC`) are the columns of a linear system, solved by
the verified `CPoly.linSolve`.

* `principalC_sound`: an answer is a function with the required zeros;
* `principalC_complete`: if such a function exists over any extension field of `F`, the test
  answers (`linSolve_complete_map`).
-/

open Polynomial CPoly

namespace Jac

variable {F : Type*} [Field F] [DecidableEq F]

/-- `p(X + x₀)`, computed by Horner's rule. -/
def taylorC (x₀ : F) : CPoly F → CPoly F
  | [] => []
  | a :: p => add [a] (mul [x₀, 1] (taylorC x₀ p))

lemma toPoly_taylorC (x₀ : F) (p : CPoly F) :
    toPoly (taylorC x₀ p) = (toPoly p).comp (X + C x₀) := by
  induction p with
  | nil => simp [taylorC]
  | cons a p ih =>
    simp only [taylorC, toPoly_add, toPoly_mul, ih, toPoly_cons, toPoly_nil, mul_zero, add_zero,
      add_comp, C_comp, mul_comp, X_comp, map_one, mul_one]
    ring

/-- The first `n` coefficients. -/
def truncC (n : ℕ) (p : CPoly F) : CPoly F := (List.range n).map fun t ↦ p.getD t 0

lemma length_truncC (n : ℕ) (p : CPoly F) : (truncC n p).length = n := by simp [truncC]

lemma coeff_truncC (n : ℕ) (p : CPoly F) (t : ℕ) :
    (toPoly (truncC n p)).coeff t = if t < n then (toPoly p).coeff t else 0 := by
  rw [coeff_toPoly, coeff_toPoly]
  unfold truncC
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : t < n
  · rw [List.getElem?_range h, if_pos h]; rfl
  · rw [List.getElem?_eq_none (by simp; omega), if_neg h]; rfl

/-- One Newton step for the branch jet: fix the coefficient of `Xᵗ`. -/
def branchStep (F₀ : CPoly F) (y₀ : F) (V : CPoly F) (t : ℕ) : CPoly F :=
  sub V (monomial t ((sub (mul V V) F₀).getD t 0 / (2 * y₀)))

/-- The branch jet of order `n + 1` of `√f` at `(x₀, y₀)`. -/
def branchC (f : CPoly F) (x₀ y₀ : F) : ℕ → CPoly F
  | 0 => [y₀]
  | n + 1 => branchStep (taylorC x₀ f) y₀ (branchC f x₀ y₀ n) (n + 1)

theorem branchC_spec (f : CPoly F) (x₀ y₀ : F) (hy : 2 * y₀ ≠ 0)
    (hf : y₀ ^ 2 = (toPoly f).eval x₀) :
    ∀ n, IsBranch (toPoly f) x₀ y₀ (n + 1) (toPoly (branchC f x₀ y₀ n)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨by simp [branchC], ?_⟩
    rw [zero_add, pow_one, X_dvd_iff]
    simp [branchC, coeff_zero_eq_eval_zero, eval_comp, hf]
  | succ n ih =>
    obtain ⟨hV0, G, hG⟩ := ih
    set V := toPoly (branchC f x₀ y₀ n)
    set c : F := (sub (mul (branchC f x₀ y₀ n) (branchC f x₀ y₀ n)) (taylorC x₀ f)).getD
      (n + 1) 0 / (2 * y₀)
    have hstep : toPoly (branchC f x₀ y₀ (n + 1)) = V - C c * X ^ (n + 1) := by
      simp [branchC, branchStep, V, c]
    have hcoef : (V ^ 2 - (toPoly f).comp (X + C x₀)).coeff (n + 1) = c * (2 * y₀) := by
      simp only [c]
      rw [← coeff_toPoly, toPoly_sub, toPoly_mul, toPoly_taylorC, div_mul_cancel₀ _ hy, sq]
    refine ⟨?_, ?_⟩
    · rw [hstep, coeff_sub, coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero, sub_zero, hV0]
    · rw [hstep]
      have e : (V - C c * X ^ (n + 1)) ^ 2 - (toPoly f).comp (X + C x₀) =
          X ^ (n + 1) * (G - C (2 * c) * V) + C (c ^ 2) * X ^ (2 * (n + 1)) := by
        rw [show (V - C c * X ^ (n + 1)) ^ 2 - (toPoly f).comp (X + C x₀) =
          (V ^ 2 - (toPoly f).comp (X + C x₀)) - C (2 * c) * X ^ (n + 1) * V +
            C (c ^ 2) * X ^ (2 * (n + 1)) by simp only [map_mul, map_pow, map_ofNat]; ring, hG]
        ring
      rw [e]
      refine dvd_add ?_ ?_
      · rw [pow_succ]
        refine mul_dvd_mul_left _ ?_
        rw [X_dvd_iff, coeff_sub, coeff_C_mul, hV0]
        have hG1 : G.coeff 0 = (V ^ 2 - (toPoly f).comp (X + C x₀)).coeff (n + 1) := by
          rw [hG, coeff_X_pow_mul', if_pos (by omega), Nat.sub_self]
        rw [hG1, hcoef]; ring
      · exact Dvd.dvd.mul_left (pow_dvd_pow X (by omega)) _

/-- A point of the divisor: `(x₀, y₀, k)`. -/
def jetBlock (f : CPoly F) (pt : F × F × ℕ) (e : CPoly F × CPoly F) : CPoly F :=
  truncC pt.2.2 (add (taylorC pt.1 e.1) (mul (taylorC pt.1 e.2) (branchC f pt.1 pt.2.1 pt.2.2)))

lemma toPoly_jetBlock_coeff (f : CPoly F) (pt : F × F × ℕ) (e : CPoly F × CPoly F) (t : ℕ) :
    (toPoly (jetBlock f pt e)).coeff t = if t < pt.2.2 then
      (jet (toPoly e.1) (toPoly e.2) pt.1 (toPoly (branchC f pt.1 pt.2.1 pt.2.2))).coeff t
      else 0 := by
  unfold jetBlock
  rw [coeff_truncC]
  simp [jet, toPoly_taylorC]

/-- The jet block with a precomputed branch `V`. -/
def jetBlockV (pt : F × F × ℕ) (V : CPoly F) (e : CPoly F × CPoly F) : CPoly F :=
  truncC pt.2.2 (add (taylorC pt.1 e.1) (mul (taylorC pt.1 e.2) V))

/-- The column of a basis function with precomputed branches. -/
def colOfV (Γ : EDiv F) (Vs : List (CPoly F)) (e : CPoly F × CPoly F) : CPoly F :=
  (List.zipWith (fun pt V ↦ jetBlockV pt V e) Γ Vs).flatten

/-! ### Semantics of the columns -/

section Sem

variable {L : Type*} [Field L]

/-- `∑_{t < n} p_t Xᵗ`. -/
noncomputable def truncX (n : ℕ) (p : L[X]) : L[X] := ∑ t ∈ Finset.range n, C (p.coeff t) * X ^ t

lemma coeff_truncX (n : ℕ) (p : L[X]) (t : ℕ) :
    (truncX n p).coeff t = if t < n then p.coeff t else 0 := by
  simp only [truncX, finset_sum_coeff, coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single t (fun b _ hb ↦ if_neg (Ne.symm hb)) (by simp [h])]; simp
  · exact Finset.sum_eq_zero fun b hb ↦ if_neg (by simp at hb; omega)

lemma truncX_add (n : ℕ) (p q : L[X]) : truncX n (p + q) = truncX n p + truncX n q := by
  ext t; simp [coeff_truncX]; split_ifs <;> simp

lemma truncX_C_mul (n : ℕ) (c : L) (p : L[X]) : truncX n (C c * p) = C c * truncX n p := by
  ext t; simp only [coeff_truncX, coeff_C_mul]; split_ifs <;> simp

lemma truncX_eq_zero_iff (n : ℕ) (p : L[X]) : truncX n p = 0 ↔ X ^ n ∣ p := by
  rw [X_pow_dvd_iff]
  constructor
  · intro h t ht; have := congrArg (coeff · t) h; simpa [coeff_truncX, ht] using this
  · intro h; ext t; rw [coeff_truncX]; split_ifs with ht
    · simpa using h t ht
    · simp

lemma natDegree_truncX_lt (n : ℕ) (p : L[X]) (t : ℕ) (ht : n ≤ t) : (truncX n p).coeff t = 0 := by
  rw [coeff_truncX, if_neg (by omega)]

/-- The semantics of a column: the truncated jets, one block per point. -/
noncomputable def colSem : EDiv L → List L[X] → L[X] → L[X] → L[X]
  | q :: Γ, V :: Vs, a, b => truncX q.2.2 (jet a b q.1 V) + X ^ q.2.2 * colSem Γ Vs a b
  | _, _, _, _ => 0

lemma colSem_add : ∀ (Γ : EDiv L) (Vs : List L[X]) (a b a' b' : L[X]),
    colSem Γ Vs (a + a') (b + b') = colSem Γ Vs a b + colSem Γ Vs a' b'
  | [], _, _, _, _, _ => by simp [colSem]
  | _ :: _, [], _, _, _, _ => by simp [colSem]
  | q :: Γ, V :: Vs, a, b, a', b' => by
    simp only [colSem, jet_add, truncX_add, colSem_add Γ Vs]; ring

lemma colSem_C_mul : ∀ (Γ : EDiv L) (Vs : List L[X]) (c : L) (a b : L[X]),
    colSem Γ Vs (C c * a) (C c * b) = C c * colSem Γ Vs a b
  | [], _, _, _, _ => by simp [colSem]
  | _ :: _, [], _, _, _ => by simp [colSem]
  | q :: Γ, V :: Vs, c, a, b => by
    simp only [colSem, jet_C_mul, truncX_C_mul, colSem_C_mul Γ Vs]; ring

lemma colSem_zero_of_zero : ∀ (Γ : EDiv L) (Vs : List L[X]), colSem Γ Vs 0 0 = 0
  | [], _ => by simp [colSem]
  | _ :: _, [] => by simp [colSem]
  | q :: Γ, V :: Vs => by simp [colSem, jet, truncX, colSem_zero_of_zero Γ Vs]

lemma colSem_zero_iff : ∀ (Γ : EDiv L) (Vs : List L[X]) (a b : L[X]), Vs.length = Γ.length →
    (colSem Γ Vs a b = 0 ↔ ∀ i : Fin Γ.length, X ^ Γ[i].2.2 ∣ jet a b Γ[i].1 Vs[i]!)
  | [], _, _, _, _ => by simp [colSem]
  | q :: Γ, [], _, _, h => by simp at h
  | q :: Γ, V :: Vs, a, b, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have ih := colSem_zero_iff Γ Vs a b h
    simp only [colSem]
    constructor
    · intro h0 i
      have h1 : truncX q.2.2 (jet a b q.1 V) = 0 := by
        ext t
        have := congrArg (coeff · t) h0
        simp only [coeff_add, coeff_zero] at this ⊢
        rw [coeff_truncX] at this ⊢
        split_ifs with ht
        · rwa [if_pos ht, coeff_X_pow_mul', if_neg (by omega), add_zero] at this
        · rfl
      have h2 : colSem Γ Vs a b = 0 := by
        rw [h1, zero_add] at h0
        exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ X_ne_zero)
      rcases i with ⟨i, hi⟩
      cases i with
      | zero => exact (truncX_eq_zero_iff _ _).mp h1
      | succ i =>
        have := (ih.mp h2) ⟨i, by simpa using hi⟩
        simpa using this
    · intro hall
      have h1 := (truncX_eq_zero_iff _ _).mpr (by simpa using hall ⟨0, by simp⟩)
      have h2 := ih.mpr fun i ↦ by simpa using hall ⟨i.1 + 1, by simp⟩
      rw [h1, h2]; simp

lemma colSem_map {K' : Type*} [Field K'] (φ : L →+* K') : ∀ (Γ : EDiv L) (Vs : List L[X])
    (a b : L[X]), (colSem Γ Vs a b).map φ =
      colSem (Γ.map fun q ↦ (φ q.1, φ q.2.1, q.2.2)) (Vs.map (Polynomial.map φ)) (a.map φ)
        (b.map φ)
  | [], _, _, _ => by simp [colSem]
  | _ :: _, [], _, _ => by simp [colSem]
  | q :: Γ, V :: Vs, a, b => by
    simp only [colSem, List.map_cons, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, colSem_map φ Γ Vs, ← jet_map]
    congr 1
    simp only [truncX, Polynomial.map_sum, Polynomial.map_mul, map_C, Polynomial.map_pow,
      Polynomial.map_X, coeff_map]

end Sem

/-- The branches used by the columns. -/
def branchesC (f : CPoly F) (Γ : EDiv F) : List (CPoly F) :=
  Γ.map fun pt ↦ branchC f pt.1 pt.2.1 pt.2.2

lemma toPoly_truncC (n : ℕ) (p : CPoly F) : toPoly (truncC n p) = truncX n (toPoly p) := by
  ext t; rw [coeff_truncC, coeff_truncX]

/-- The column of a basis function: all jet blocks, concatenated. -/
def colOf (f : CPoly F) (Γ : EDiv F) (e : CPoly F × CPoly F) : CPoly F :=
  colOfV Γ (branchesC f Γ) e

lemma toPoly_colOfV : ∀ (Γ : EDiv F) (Vs : List (CPoly F)) (e : CPoly F × CPoly F),
    toPoly (colOfV Γ Vs e) = colSem Γ (Vs.map toPoly) (toPoly e.1) (toPoly e.2)
  | [], _, e => by simp [colOfV, colSem]
  | _ :: _, [], e => by simp [colOfV, colSem]
  | q :: Γ, V :: Vs, e => by
    rw [colOfV, List.zipWith_cons_cons, List.flatten_cons, toPoly_append,
      show (List.zipWith (fun pt V ↦ jetBlockV pt V e) Γ Vs).flatten = colOfV Γ Vs e from rfl,
      toPoly_colOfV Γ Vs e]
    simp only [List.map_cons, colSem]
    congr 1
    · unfold jetBlockV; rw [toPoly_truncC]; simp [jet, toPoly_taylorC]
    · simp [jetBlockV, length_truncC]

lemma toPoly_colOf (f : CPoly F) (Γ : EDiv F) (e : CPoly F × CPoly F) :
    toPoly (colOf f Γ e) = colSem Γ ((branchesC f Γ).map toPoly) (toPoly e.1) (toPoly e.2) :=
  toPoly_colOfV Γ _ e

/-! ### The test -/

/-- The basis `xⁱ` (`i < A`) and `xʲ y` (`j < B`). -/
def basisC (A B : ℕ) : List (CPoly F × CPoly F) :=
  (List.range A).map (fun i ↦ (CPoly.monomial i (1 : F), [])) ++
    (List.range B).map fun j ↦ ([], CPoly.monomial j (1 : F))

/-- The columns. -/
def colsC (f : CPoly F) (Γ : EDiv F) (A B : ℕ) : List (CPoly F) :=
  let Vs := branchesC f Γ
  (basisC A B).map (colOfV Γ Vs)

/-- **The principal-divisor test**: an index `j` and coefficients with `ψ_j = 1`. -/
def principalC (f : CPoly F) (Γ : EDiv F) (A B : ℕ) : Option (ℕ × List F) :=
  (List.range (A + B)).findSome? fun j ↦
    (linSolve ((colsC f Γ A B).set j []) (neg ((colsC f Γ A B).getD j []))).map fun cs ↦ (j, cs)

lemma length_colsC (f : CPoly F) (Γ : EDiv F) (A B : ℕ) : (colsC f Γ A B).length = A + B := by
  simp [colsC, basisC]

section Lin

variable {S : Type*} [Field S] (φ : F →+* S)

/-- `∑ cᵢ pᵢ`. -/
noncomputable def lsum (cs : List S) (ps : List S[X]) : S[X] :=
  (List.zipWith (fun c p ↦ C c * p) cs ps).sum

lemma lcombS_eq_colSem (f : CPoly F) (Γ : EDiv F) : ∀ (cs : List S) (es : List (CPoly F × CPoly F)),
    lcombS φ cs (es.map (colOf f Γ)) =
      colSem (Γ.map fun q ↦ (φ q.1, φ q.2.1, q.2.2))
        (((branchesC f Γ).map toPoly).map (Polynomial.map φ))
        (lsum cs (es.map fun e ↦ (toPoly e.1).map φ)) (lsum cs (es.map fun e ↦ (toPoly e.2).map φ))
  | [], es => by simp [lcombS, lsum, colSem_zero_of_zero]
  | c :: cs, [] => by simp [lcombS, lsum, colSem_zero_of_zero]
  | c :: cs, e :: es => by
    have ih := lcombS_eq_colSem f Γ cs es
    simp only [lcombS, lsum, List.map_cons, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih, colSem_add, colSem_C_mul, toPoly_colOf, colSem_map]

lemma lsum_eq_sum : ∀ (cs : List S) (ps : List S[X]), cs.length = ps.length →
    lsum cs ps = ∑ i ∈ Finset.range ps.length, C (cs.getD i 0) * ps.getD i 0
  | [], [], _ => by simp [lsum]
  | c :: cs, p :: ps, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [← lsum_eq_sum cs ps h]
    simp [lsum, add_comm]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

lemma basis_fst_getD (A B i : ℕ) :
    ((basisC (F := F) A B).map fun e ↦ (toPoly e.1).map φ).getD i 0 =
      if i < A then X ^ i else 0 := by
  simp only [basisC, List.map_append, List.map_map, Function.comp_def]
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD]

lemma basis_snd_getD (A B i : ℕ) :
    ((basisC (F := F) A B).map fun e ↦ (toPoly e.2).map φ).getD i 0 =
      if A ≤ i ∧ i < A + B then X ^ (i - A) else 0 := by
  simp only [basisC, List.map_append, List.map_map, Function.comp_def]
  split_ifs with h
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, show i - A < B by omega]
  · by_cases hi : i < A
    · rw [List.getD_append _ _ _ _ (by simpa using hi)]
      simp [List.getD_eq_getElem?_getD, hi]
    · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      exact List.getD_eq_default _ _ (by simp; omega)

lemma lsum_basis_fst (A B : ℕ) (cs : List S) (hcs : cs.length = A + B) (t : ℕ) :
    (lsum cs ((basisC (F := F) A B).map fun e ↦ (toPoly e.1).map φ)).coeff t =
      if t < A then cs.getD t 0 else 0 := by
  have hlen : (basisC (F := F) A B).length = A + B := by simp [basisC]
  rw [lsum_eq_sum _ _ (by simp [hlen, hcs]), finset_sum_coeff]
  simp only [List.length_map, hlen, basis_fst_getD]
  rw [Finset.sum_eq_single t]
  · split_ifs with ht <;> simp [coeff_C_mul_X_pow]
  · intro b _ hb
    split_ifs <;> simp [coeff_C_mul_X_pow, Ne.symm hb]
  · intro h
    rw [Finset.mem_range, not_lt] at h
    have ht : ¬ t < A := by omega
    simp [ht]

lemma lsum_basis_snd (A B : ℕ) (cs : List S) (hcs : cs.length = A + B) (t : ℕ) :
    (lsum cs ((basisC (F := F) A B).map fun e ↦ (toPoly e.2).map φ)).coeff t =
      if t < B then cs.getD (A + t) 0 else 0 := by
  have hlen : (basisC (F := F) A B).length = A + B := by simp [basisC]
  rw [lsum_eq_sum _ _ (by simp [hlen, hcs]), finset_sum_coeff]
  simp only [List.length_map, hlen, basis_snd_getD]
  by_cases ht : t < B
  · rw [if_pos ht, Finset.sum_eq_single (A + t)]
    · rw [if_pos (by omega), show A + t - A = t by omega]; simp [coeff_C_mul_X_pow]
    · intro b _ hb
      split_ifs with h1
      · rw [coeff_C_mul_X_pow, if_neg (by omega)]
      · simp
    · intro h; simp at h; omega
  · rw [if_neg ht]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    split_ifs with h1
    · rw [coeff_C_mul_X_pow, if_neg (by omega)]
    · simp

lemma lcombS_set : ∀ (cs : List S) (vs : List (CPoly F)) (j : ℕ) (c : S),
    cs.length = vs.length → j < vs.length →
    lcombS φ (cs.set j c) vs = lcombS φ cs (vs.set j []) + C c * (toPoly (vs.getD j [])).map φ
  | [], [], _, _, _, h => by simp at h
  | c₀ :: cs, v :: vs, 0, c, _, _ => by
    simp [lcombS]; ring
  | c₀ :: cs, v :: vs, j + 1, c, hl, hj => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl hj
    have ih := lcombS_set cs vs j c hl (by omega)
    simp only [lcombS] at ih ⊢
    simp only [List.set_cons_succ, List.zipWith_cons_cons, List.sum_cons, List.getD_cons_succ]
    rw [ih]; ring
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h

end Lin

lemma lcombS_id (cs : List F) (vs : List (CPoly F)) : lcombS (RingHom.id F) cs vs = lcomb cs vs := by
  simp [lcombS, lcomb]

/-- **Soundness of the test.** -/
theorem principalC_sound (f : CPoly F) (Γ : EDiv F) (A B : ℕ)
    (hΓ : ∀ q ∈ Γ, 2 * q.2.1 ≠ 0 ∧ q.2.1 ^ 2 = (toPoly f).eval q.1) {j : ℕ} {cs : List F}
    (h : principalC f Γ A B = some (j, cs)) :
    ∃ ψ : F[X] × F[X], ψ ≠ (0, 0) ∧ ψ.1.degree < A ∧ ψ.2.degree < B ∧ Vanishes (toPoly f) ψ Γ := by
  classical
  obtain ⟨j', hj', hjs⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨cs', hcs', he⟩ := Option.map_eq_some_iff.mp hjs
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hjA : j' < A + B := List.mem_range.mp hj'
  set cols := colsC f Γ A B
  obtain ⟨hlen, hlc⟩ := linSolve_sound _ _ _ hcs'
  rw [List.length_set, length_colsC] at hlen
  set full := cs'.set j' 1
  have hfl : full.length = A + B := by simp [full, hlen]
  have h0 : lcombS (RingHom.id F) full cols = 0 := by
    rw [lcombS_set (RingHom.id F) cs' cols j' 1 (by rw [hlen, length_colsC])
      (by rw [length_colsC]; exact hjA), lcombS_id, hlc]
    simp
  rw [show cols = (basisC A B).map (colOf f Γ) from rfl, lcombS_eq_colSem] at h0
  simp only [Polynomial.map_id, List.map_id', RingHom.id_apply] at h0
  set ψ : F[X] × F[X] := (lsum full ((basisC A B).map fun e ↦ toPoly e.1),
    lsum full ((basisC A B).map fun e ↦ toPoly e.2))
  have hc1 : ∀ t, ψ.1.coeff t = if t < A then full.getD t 0 else 0 := fun t ↦ by
    have := lsum_basis_fst (RingHom.id F) A B full hfl t; simpa using this
  have hc2 : ∀ t, ψ.2.coeff t = if t < B then full.getD (A + t) 0 else 0 := fun t ↦ by
    have := lsum_basis_snd (RingHom.id F) A B full hfl t; simpa using this
  have hfj : full.getD j' 0 = 1 := by
    simp [full, List.getD_eq_getElem?_getD, List.getElem?_set, hlen, hjA]
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · intro hψ
    by_cases hjA' : j' < A
    · have := hc1 j'; rw [if_pos hjA', hfj, show ψ.1 = 0 from congrArg Prod.fst hψ] at this
      simp at this
    · have := hc2 (j' - A)
      rw [if_pos (by omega), show A + (j' - A) = j' by omega, hfj,
        show ψ.2 = 0 from congrArg Prod.snd hψ] at this
      simp at this
  · refine (degree_lt_iff_coeff_zero _ _).mpr fun t ht ↦ ?_
    rw [hc1, if_neg (by exact_mod_cast not_lt.mpr ht)]
  · refine (degree_lt_iff_coeff_zero _ _).mpr fun t ht ↦ ?_
    rw [hc2, if_neg (by exact_mod_cast not_lt.mpr ht)]
  · intro q hq
    obtain ⟨i, rfl⟩ := List.get_of_mem hq
    have h0' : colSem Γ ((branchesC f Γ).map toPoly) ψ.1 ψ.2 = 0 := by
      convert h0 using 2
      simp
    have hz := (colSem_zero_iff Γ ((branchesC f Γ).map toPoly) ψ.1 ψ.2
      (by simp [branchesC])).mp h0' ⟨i, by simpa using i.2⟩
    obtain ⟨h2, hy⟩ := hΓ _ (List.get_mem _ _)
    refine ⟨_, (branchC_spec f _ _ h2 hy _).mono (Nat.le_succ _), ?_⟩
    simpa [branchesC] using hz

/-- **Completeness of the test over extension fields.** -/
theorem principalC_complete {S : Type*} [Field S] (φ : F →+* S) (f : CPoly F) (Γ : EDiv F)
    (A B : ℕ) (hΓ : ∀ q ∈ Γ, 2 * q.2.1 ≠ 0 ∧ q.2.1 ^ 2 = (toPoly f).eval q.1)
    (ψ : S[X] × S[X]) (hψ0 : ψ ≠ (0, 0)) (hA : ψ.1.degree < A) (hB : ψ.2.degree < B)
    (hv : Vanishes ((toPoly f).map φ) ψ (emap φ Γ)) : principalC f Γ A B ≠ none := by
  classical
  set cols := colsC f Γ A B
  set cL : List S := (List.range A).map ψ.1.coeff ++ (List.range B).map ψ.2.coeff
  have hcL : cL.length = A + B := by simp [cL]
  have hL1 : lsum cL ((basisC A B).map fun e ↦ (toPoly e.1).map φ) = ψ.1 := by
    ext t
    rw [lsum_basis_fst φ A B cL hcL]
    split_ifs with ht
    · simp [cL, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [ht] : t < ((List.range A).map ψ.1.coeff).length), ht]
    · exact (coeff_eq_zero_of_degree_lt (hA.trans_le (by exact_mod_cast not_lt.mp ht))).symm
  have hL2 : lsum cL ((basisC A B).map fun e ↦ (toPoly e.2).map φ) = ψ.2 := by
    ext t
    rw [lsum_basis_snd φ A B cL hcL]
    split_ifs with ht
    · simp [cL, List.getD_eq_getElem?_getD, List.getElem?_append_right, ht]
    · exact (coeff_eq_zero_of_degree_lt (hB.trans_le (by exact_mod_cast not_lt.mp ht))).symm
  have h0 : lcombS φ cL cols = 0 := by
    rw [show cols = (basisC A B).map (colOf f Γ) from rfl, lcombS_eq_colSem, hL1, hL2]
    refine (colSem_zero_iff _ _ _ _ (by simp [branchesC])).mpr fun i ↦ ?_
    simp only [List.getElem_map, List.getElem!_eq_getElem?_getD, List.getElem?_map,
      branchesC]
    obtain ⟨h2, hy⟩ := hΓ _ (List.getElem_mem (by simpa using i.2))
    have hbr := (branchC_spec f _ _ h2 hy (Γ[i.1]'(by simpa using i.2)).2.2).map φ
    have h2S : IsUnit (2 * φ (Γ[i.1]'(by simpa using i.2)).2.1) := by
      refine IsUnit.mk0 _ ?_
      rw [← map_ofNat φ 2, ← map_mul]; exact (map_ne_zero_iff φ φ.injective).mpr h2
    have := (hv _ (List.mem_map_of_mem (List.getElem_mem _))).jet_dvd h2S hbr (Nat.le_succ _)
    simpa [List.getElem?_eq_getElem (by simpa using i.2)] using this
  -- a non-zero coordinate
  obtain ⟨j, hj, hcj⟩ : ∃ j < A + B, cL.getD j 0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hψ0
    refine Prod.ext ?_ ?_
    · rw [← hL1, lsum_eq_sum _ _ (by simp [basisC, hcL])]
      refine Finset.sum_eq_zero fun b hb ↦ ?_
      rw [hall b (by simpa [basisC] using hb)]; simp
    · rw [← hL2, lsum_eq_sum _ _ (by simp [basisC, hcL])]
      refine Finset.sum_eq_zero fun b hb ↦ ?_
      rw [hall b (by simpa [basisC] using hb)]; simp
  set c := cL.getD j 0
  set cL' := cL.map (c⁻¹ * ·)
  have h0' : lcombS φ cL' cols = 0 := by rw [lcombS_mapMul, h0, mul_zero]
  have hcj' : cL'.getD j 0 = 1 := by
    simp only [cL', List.getD_eq_getElem?_getD, List.getElem?_map]
    have : j < cL.length := by rw [hcL]; exact hj
    rw [List.getElem?_eq_getElem this]
    simp only [Option.map_some, Option.getD_some]
    have hc : cL[j] = c := by simp [c, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
    rw [hc, inv_mul_cancel₀ hcj]
  have hset := lcombS_set φ (cL'.set j 0) cols j 1 (by simp [cL', hcL, cols, length_colsC])
    (by rw [show cols = colsC f Γ A B from rfl, length_colsC]; exact hj)
  have hlin : linSolve (cols.set j []) (neg (cols.getD j [])) ≠ none := by
    refine linSolve_complete_map φ _ _ (cL'.set j 0) (by simp [cL', hcL, cols, length_colsC]) ?_
    have hset' := lcombS_set φ cL' cols j 0 (by simp [cL', hcL, cols, length_colsC])
      (by rw [show cols = colsC f Γ A B from rfl, length_colsC]; exact hj)
    have hss : cL'.set j 1 = cL' := by
      apply List.ext_getElem (by simp)
      intro n h1 h2
      rw [List.getElem_set]
      split_ifs with hn
      · subst hn
        have := hcj'
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2] at this
        exact this.symm
      · rfl
    have e1 := lcombS_set φ cL' cols j 1 (by simp [cL', hcL, cols, length_colsC])
      (by rw [show cols = colsC f Γ A B from rfl, length_colsC]; exact hj)
    rw [hss, h0', C_1, one_mul] at e1
    -- `lcombS (cL'.set j 0) (cols.set j []) = lcombS cL' (cols.set j [])`
    have hz : lcombS φ (cL'.set j 0) (cols.set j []) = lcombS φ cL' (cols.set j []) := by
      have := lcombS_set φ cL' (cols.set j []) j 0 (by simp [cL', hcL, cols, length_colsC])
        (by simp [cols, length_colsC, hj])
      rw [this, List.set_set]
      simp [List.getD_eq_getElem?_getD, List.getElem?_set, length_colsC, hj]
    rw [hz, toPoly_neg, Polynomial.map_neg]
    linear_combination -e1
  intro hnone
  rw [principalC, List.findSome?_eq_none_iff] at hnone
  have := hnone j (List.mem_range.mpr hj)
  rw [Option.map_eq_none_iff] at this
  exact hlin this

end Jac
