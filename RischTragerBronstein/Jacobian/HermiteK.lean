import RischTragerBronstein.Jacobian.HypDecideQComplete

/-!
# Hermite reduction over a field `K` (char. 0)

The linear-algebra Hermite reduction of `EllQuad` (`colsG`, `nbPart`, `hermite_of_linSolve`,
`hermite_solve_ne_none`) for polynomials over any field `K` of characteristic zero:
`2 A D S = S L_D(W) + 2 D² T` is solved by `linSolve` over `K`, and it is always solvable
(`hermite_solve_ne_noneK`, through the algebraic closure of `K`).
-/

open Polynomial CPoly EllAlgo EllQuad

namespace Jac

variable {K : Type*} [Field K] [DecidableEq K]

/-- `L_D(W)`, executable. -/
def LDcK (p D W : CPoly K) : CPoly K :=
  add (mul [2] (mul (sub (mul (deriv W) D) (mul W (deriv D))) p)) (mul (mul W D) (deriv p))

lemma toPoly_twoK : toPoly ([2] : CPoly K) = 2 := by
  rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2

lemma toPoly_LDcK (p D W : CPoly K) :
    toPoly (LDcK p D W) = LDK (toPoly p) (toPoly D) (toPoly W) := by
  simp only [LDcK, LDK, toPoly_add, toPoly_mul, toPoly_sub, toPoly_deriv, toPoly_twoK]; ring

lemma LDK_mapK {S : Type*} [Field S] (ι : K →+* S) (p D W : K[X]) :
    (LDK p D W).map ι = LDK (p.map ι) (D.map ι) (W.map ι) := by
  simp only [LDK, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, derivative_map,
    Polynomial.map_ofNat]

/-- The part of the squarefree part of `D` coprime to `p`. -/
def nbPartK (p D : CPoly K) : CPoly K := div (sqfreePart D) (gcd (sqfreePart D) p)

/-- The columns: `S L_D(xⁱ)` (`i < dW`), then `2 D² xʲ` (`j < nT`). -/
def colsGK (p D S : CPoly K) (dW nT : ℕ) : List (CPoly K) :=
  (List.range dW).map (fun i ↦ mul S (LDcK p D (monomial i 1))) ++
    (List.range nT).map fun j ↦ mul [2] (mul (mul D D) (monomial j 1))

section Lin

variable {S : Type*} [Field S] (ι : K →+* S)

lemma lcombS_append_takeK (w : List S) (L₁ L₂ : List (CPoly K)) :
    lcombS ι w (L₁ ++ L₂) = lcombS ι (w.take L₁.length) L₁ + lcombS ι (w.drop L₁.length) L₂ := by
  induction L₁ generalizing w with
  | nil => simp [lcombS]
  | cons v L₁ ih =>
    cases w with
    | nil => simp [lcombS]
    | cons c w =>
      have := ih w
      simp only [lcombS, List.cons_append, List.zipWith_cons_cons, List.sum_cons, List.length_cons,
        List.take_succ_cons, List.drop_succ_cons] at this ⊢
      rw [this]; ring

lemma lcombS_range_linK (f : ℕ → CPoly K) (Φ : S[X] →ₗ[S] S[X])
    (hf : ∀ i, (toPoly (f i)).map ι = Φ (X ^ i)) :
    ∀ (n : ℕ) (w : List S), lcombS ι w ((List.range n).map f) = Φ (toPoly (w.take n)) := by
  classical
  intro n
  induction n with
  | zero => intro w; simp [lcombS]
  | succ n ih =>
    intro w
    rw [List.range_succ, List.map_append, lcombS_append_takeK, ih, List.length_map,
      List.length_range]
    rcases Nat.lt_or_ge n w.length with hn | hn
    · have hd : w.drop n = w[n] :: w.drop (n + 1) := List.drop_eq_getElem_cons hn
      rw [hd, List.map_singleton, List.take_add_one, List.getElem?_eq_getElem hn, toPoly_append]
      simp only [lcombS, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons,
        List.sum_nil, add_zero, hf, Option.toList_some, List.length_take, min_eq_left hn.le,
        toPoly_cons, toPoly_nil, mul_zero, map_add]
      rw [← smul_eq_C_mul, ← map_smul, smul_eq_C_mul, List.take_take, min_self, mul_comm (X ^ n)]
    · rw [List.drop_eq_nil_of_le hn]
      simp [lcombS, List.take_of_length_le hn,
        List.take_of_length_le (show w.length ≤ n + 1 by omega)]

/-- `W ↦ M · L_D(W)` as a linear map. -/
noncomputable def ldLinK (M p D : S[X]) : S[X] →ₗ[S] S[X] where
  toFun W := M * LDK p D W
  map_add' W₁ W₂ := by simp only [LDK, derivative_add]; ring
  map_smul' c W := by
    simp only [LDK, smul_eq_C_mul, derivative_mul, derivative_C, zero_mul, zero_add,
      RingHom.id_apply]
    ring

lemma lcombS_colsGK (p D M : CPoly K) (dW nT : ℕ) (w : List S) :
    lcombS ι w (colsGK p D M dW nT) =
      (toPoly M).map ι * LDK ((toPoly p).map ι) ((toPoly D).map ι) (toPoly (w.take dW)) +
        2 * ((toPoly D).map ι) ^ 2 * toPoly ((w.drop dW).take nT) := by
  rw [colsGK, lcombS_append_takeK, List.length_map, List.length_range]
  rw [lcombS_range_linK ι _ (ldLinK ((toPoly M).map ι) ((toPoly p).map ι) ((toPoly D).map ι))
      (fun i ↦ by
        simp only [ldLinK, LinearMap.coe_mk, AddHom.coe_mk, toPoly_mul, toPoly_LDcK,
          toPoly_monomial, map_one, one_mul, Polynomial.map_mul, LDK_mapK, Polynomial.map_pow,
          Polynomial.map_X]),
    lcombS_range_linK ι _ (LinearMap.mulLeft S (2 * ((toPoly D).map ι) ^ 2))
      (fun j ↦ by
        simp only [LinearMap.mulLeft_apply, toPoly_mul, toPoly_twoK, toPoly_monomial, map_one,
          one_mul, Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_pow,
          Polynomial.map_X]
        ring)]
  simp only [ldLinK, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mulLeft_apply, List.take_take,
    min_self]

end Lin

section NB

variable (p D : CPoly K) (hD : toPoly D ≠ 0)
include hD

lemma nbPartK_facts :
    toPoly (sqfreePart D) ≠ 0 ∧ toPoly (gcd (sqfreePart D) p) ≠ 0 ∧
      toPoly (gcd (sqfreePart D) p) ∣ toPoly p ∧
      toPoly (sqfreePart D) = toPoly (nbPartK p D) * toPoly (gcd (sqfreePart D) p) := by
  have hS0 : toPoly (sqfreePart D) ≠ 0 := fun h ↦ hD (by rw [sqfreePart_mul D hD, h, zero_mul])
  have hg := egcd_dvd (sqfreePart D) p
  rw [← toPoly_gcd] at hg
  have hg0 : toPoly (gcd (sqfreePart D) p) ≠ 0 := by
    intro h; rw [h] at hg; exact hS0 (zero_dvd_iff.mp hg.1)
  exact ⟨hS0, hg0, hg.2, div_mul_of_dvd _ _ hg0 hg.1⟩

lemma nbPartK_ne_zero : toPoly (nbPartK p D) ≠ 0 := by
  obtain ⟨hS0, -, -, he⟩ := nbPartK_facts p D hD
  exact fun h ↦ hS0 (by rw [he, h, zero_mul])

lemma squarefree_nbPartK : Squarefree (toPoly (nbPartK p D)) := by
  obtain ⟨-, -, -, he⟩ := nbPartK_facts p D hD
  have := squarefree_sqfreePart D hD
  rw [he] at this
  exact this.of_mul_left

lemma isCoprime_nbPartK : IsCoprime (toPoly (nbPartK p D)) (toPoly p) := by
  obtain ⟨hS0, -, -, he⟩ := nbPartK_facts p D hD
  have hsq := squarefree_sqfreePart D hD
  refine isCoprime_of_irreducible_dvd (fun h ↦ nbPartK_ne_zero p D hD h.1) fun z hz h1 h2 ↦ ?_
  have hzS0 : z ∣ toPoly (sqfreePart D) := by rw [he]; exact h1.mul_right _
  have hzg : z ∣ toPoly (gcd (sqfreePart D) p) := by rw [toPoly_gcd]; exact dvd_egcd _ _ hzS0 h2
  have : z * z ∣ toPoly (sqfreePart D) := by rw [he]; exact mul_dvd_mul h1 hzg
  exact hz.not_isUnit (hsq z this)

/-- Every non-branch root of `D` (in any extension) is a root of `S`. -/
lemma isRoot_nbPartK {L : Type*} [Field L] [CharZero L] (ι : K →+* L) (α : L)
    (hα : ((toPoly D).map ι).IsRoot α) (hpα : ¬((toPoly p).map ι).IsRoot α) :
    ((toPoly (nbPartK p D)).map ι).IsRoot α := by
  obtain ⟨-, -, hgp, he⟩ := nbPartK_facts p D hD
  have hDq : (toPoly D).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hD
  have hGd : toPoly (gcd D (deriv D)) ∣ derivative (toPoly D) := by
    rw [toPoly_gcd, ← toPoly_deriv]; exact (egcd_dvd D (deriv D)).2
  have h1 : X - C α ∣ (toPoly (sqfreePart D)).map ι := by
    refine Differential.irreducible_dvd_sqfreePart hDq (G := (toPoly (gcd D (deriv D))).map ι) ?_ ?_
      (irreducible_X_sub_C α) (dvd_iff_isRoot.mpr hα)
    · rw [sqfreePart_mul D hD, Polynomial.map_mul, mul_comm]
    · rw [derivative_map]; exact Polynomial.map_dvd ι hGd
  rw [he, Polynomial.map_mul] at h1
  rcases (prime_X_sub_C α).dvd_or_dvd h1 with h | h
  · exact dvd_iff_isRoot.mp h
  · exact absurd (dvd_iff_isRoot.mp (h.trans (Polynomial.map_dvd ι hgp))) hpα

end NB

/-- The Hermite identity from a solution of the system. -/
lemma hermite_of_linSolveK (p A D M : CPoly K) (dW nT : ℕ) (cs : List K)
    (h : linSolve (colsGK p D M dW nT) (mul [2] (mul (mul A D) M)) = some cs) :
    2 * toPoly A * toPoly D * toPoly M = toPoly M * LDK (toPoly p) (toPoly D)
      (toPoly (cs.take dW)) + 2 * toPoly D ^ 2 * toPoly (cs.drop dW) := by
  obtain ⟨hlen, hl⟩ := linSolve_sound _ _ _ h
  have e := lcombS_colsGK (RingHom.id K) p D M dW nT cs
  rw [show lcombS (RingHom.id K) cs (colsGK p D M dW nT) = lcomb cs (colsGK p D M dW nT) by
    simp [lcombS, lcomb], hl] at e
  simp only [Polynomial.map_id] at e
  have hlen' : (cs.drop dW).length ≤ nT := by
    rw [List.length_drop, hlen, colsGK, List.length_append, List.length_map, List.length_range,
      List.length_map, List.length_range]; omega
  rw [List.take_of_length_le hlen'] at e
  rw [← e]
  simp only [toPoly_mul, toPoly_twoK]; ring


theorem hermite_solve_ne_noneK [CharZero K] (p A D : CPoly K) (hsq : Squarefree (toPoly p))
    (hp1 : 1 ≤ (toPoly p).natDegree) (hD : toPoly D ≠ 0) (e : ℕ) (he : p.length ≤ e) :
    linSolve (colsGK p D (nbPartK p D) (A.length + D.length)
      (A.length + 2 * D.length + (nbPartK p D).length + e + 3))
      (mul [2] (mul (mul A D) (nbPartK p D))) ≠ none := by
  classical
  set M := nbPartK p D
  set dW := A.length + D.length
  set nT := A.length + 2 * D.length + M.length + e + 3
  set ι := algebraMap K (AlgebraicClosure K)
  have hinj : Function.Injective ι := ι.injective
  have hsqQ : Squarefree ((toPoly p).map ι) :=
    ((PerfectField.separable_iff_squarefree.mpr hsq).map).squarefree
  have hp1' : 1 ≤ ((toPoly p).map ι).natDegree := by
    rw [natDegree_map_eq_of_injective hinj]; exact hp1
  have hDq : (toPoly D).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hD
  obtain ⟨W, B₀, T, cf, hT, hB, hid⟩ := hermite_polyK ((toPoly p).map ι) hsqQ hp1'
    ((toPoly A).map ι) ((toPoly D).map ι) hDq (IsAlgClosed.splits _)
  have hWd := hermite_deg_boundK _ hp1' _ _ W B₀ T cf hDq hB hid
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj] at hWd
  have hdvd : ∏ α ∈ T, (X - C α) ∣ (toPoly M).map ι := by
    refine Finset.prod_dvd_of_coprime
      ((pairwise_coprime_X_sub_C (s := fun α : AlgebraicClosure K ↦ α)
        Function.injective_id).set_pairwise _)
      fun α hα ↦ dvd_iff_isRoot.mpr (isRoot_nbPartK p D hD ι α (hT α hα).1 (hT α hα).2)
  obtain ⟨Q, hQ⟩ := hdvd
  set TQ := Q * ((∏ α ∈ T, (X - C α)) * B₀ + ∑ α ∈ T, C (cf α) * ∏ β ∈ T.erase α, (X - C β))
  have hidQ : 2 * (toPoly A).map ι * (toPoly D).map ι * (toPoly M).map ι =
      (toPoly M).map ι * LDK ((toPoly p).map ι) ((toPoly D).map ι) W +
        2 * ((toPoly D).map ι) ^ 2 * TQ := by
    rw [hQ]; simp only [TQ]; linear_combination Q * hid
  have hAl := CPoly.natDegree_toPoly_le_length A
  have hDl' := CPoly.natDegree_toPoly_le_length D
  have hMl := CPoly.natDegree_toPoly_le_length M
  have hpl := CPoly.natDegree_toPoly_le_length p
  have hD1 : 1 ≤ D.length := by
    rcases D with _ | ⟨d, D⟩
    · exact absurd (by simp) hD
    · simp
  have hW : W = 0 ∨ W.natDegree < dW := Or.inr (by
    rcases le_total (toPoly A).natDegree (toPoly D).natDegree with h | h
    · rw [max_eq_right h] at hWd; omega
    · rw [max_eq_left h] at hWd; omega)
  have hTQ : TQ = 0 ∨ TQ.natDegree < nT := by
    rcases eq_or_ne TQ 0 with h0 | h0
    · exact Or.inl h0
    right
    have e' : 2 * ((toPoly D).map ι) ^ 2 * TQ = 2 * (toPoly A).map ι * (toPoly D).map ι *
        (toPoly M).map ι - (toPoly M).map ι * LDK ((toPoly p).map ι) ((toPoly D).map ι) W := by
      rw [hidQ]; ring
    have hprod : (2 * ((toPoly D).map ι) ^ 2 * TQ).natDegree =
        2 * (toPoly D).natDegree + TQ.natDegree := by
      rw [natDegree_mul (mul_ne_zero two_ne_zero (pow_ne_zero _ hDq)) h0,
        natDegree_mul two_ne_zero (pow_ne_zero _ hDq), natDegree_pow,
        natDegree_map_eq_of_injective hinj]
      simp
    rw [e'] at hprod
    have hc0 : (2 : (AlgebraicClosure K)[X]).natDegree ≤ 0 := by simp
    have h1 := nd_mulK (nd_mulK (nd_mulK hc0 (natDegree_map_le (f := ι) (p := toPoly A)))
      (natDegree_map_le (f := ι) (p := toPoly D))) (natDegree_map_le (f := ι) (p := toPoly M))
    have h3 := nd_mulK (natDegree_map_le (f := ι) (p := toPoly M))
      (natDegree_LD_leK ((toPoly p).map ι) ((toPoly D).map ι) W hp1')
    simp only [natDegree_map_eq_of_injective hinj] at h1 h3
    have h5 := natDegree_sub_le (2 * (toPoly A).map ι * (toPoly D).map ι * (toPoly M).map ι)
      ((toPoly M).map ι * LDK ((toPoly p).map ι) ((toPoly D).map ι) W)
    rw [hprod] at h5
    simp only [nT]
    rcases le_total (toPoly A).natDegree (toPoly D).natDegree with h | h
    · rw [max_eq_right h] at hWd
      have h6 : 2 * (toPoly D).natDegree + TQ.natDegree ≤
          (toPoly M).natDegree + ((toPoly D).natDegree + (toPoly D).natDegree +
            (toPoly p).natDegree) := by
        refine h5.trans (max_le (h1.trans (by omega)) (h3.trans (by omega)))
      omega
    · rw [max_eq_left h] at hWd
      have h6 : 2 * (toPoly D).natDegree + TQ.natDegree ≤
          (toPoly M).natDegree + ((toPoly A).natDegree + (toPoly D).natDegree +
            (toPoly p).natDegree) := by
        refine h5.trans (max_le (h1.trans (by omega)) (h3.trans (by omega)))
      omega
  refine linSolve_complete_map ι _ _ ((List.range dW).map W.coeff ++ (List.range nT).map TQ.coeff)
    (by simp [colsGK]) ?_
  rw [lcombS_colsGK, List.take_left' (by simp), List.drop_left' (by simp),
    List.take_of_length_le (by simp), toPoly_range_coeff W dW hW, toPoly_range_coeff TQ nT hTQ]
  simp only [toPoly_mul, toPoly_twoK, Polynomial.map_mul, Polynomial.map_ofNat]
  rw [← hidQ]; ring


end Jac
