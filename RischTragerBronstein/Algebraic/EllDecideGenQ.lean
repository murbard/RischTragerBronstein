import RischTragerBronstein.Algebraic.EllDecideQ
import RischTragerBronstein.Algebraic.EllGen
import RischTragerBronstein.Algebraic.HermiteBoundK
import RischTragerBronstein.Computable.SquarefreePart
import RischTragerBronstein.Computable.KerElim

/-!
# The automatic decision for arbitrary `∫ A dx / (D √p)` over `ℚ`

`ellDecideGenQ a b c A D B` (`p = x³ + ax² + bx + c` squarefree, `D ≠ 0` arbitrary):
1. `S` = the part of the squarefree part of `D` coprime to `p` (`nbPart`);
2. the Hermite reduction `2 A D S = S L_D(W) + 2 D² T` (`L_D(W) = 2(W′D − WD′)p + WDp′`) is a
   linear system for the coefficients of `W` and `T`, solved over `ℚ` (`linSolve`); it gives
   `A / (D y) = (W/D · y)′ + T / (S y)`;
3. `ellDecideQ` decides `∫ T / (S y)` (simple poles away from the branch points).

`ellDecideGenQ_spec`: every answer is correct (constants algebraically closed).
`ellDecideGenQ_complete`: for every `D ≠ 0`, every large enough search bound gives an answer
(the Hermite decomposition exists over `ℚ̄`, `hermite_polyK`, with bounded degrees,
`hermite_deg_boundK`, hence the rational system is solvable, `linSolve_complete_map`).
-/

open Polynomial Differential

namespace EllQuad

open CPoly EllAlgo

/-- `L_D(W)`, executable. -/
def LDc (p D W : CPoly ℚ) : CPoly ℚ :=
  add (mul [2] (mul (sub (mul (deriv W) D) (mul W (deriv D))) p)) (mul (mul W D) (deriv p))

lemma toPoly_two : toPoly ([2] : CPoly ℚ) = 2 := by
  rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2

lemma toPoly_LDc (p D W : CPoly ℚ) :
    toPoly (LDc p D W) = LDK (toPoly p) (toPoly D) (toPoly W) := by
  simp only [LDc, LDK, toPoly_add, toPoly_mul, toPoly_sub, toPoly_deriv, toPoly_two]; ring

lemma LDK_map {S : Type*} [Field S] (ι : ℚ →+* S) (p D W : ℚ[X]) :
    (LDK p D W).map ι = LDK (p.map ι) (D.map ι) (W.map ι) := by
  simp only [LDK, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, derivative_map,
    Polynomial.map_ofNat]

/-- The part of the squarefree part of `D` coprime to `p`. -/
def nbPart (p D : CPoly ℚ) : CPoly ℚ := div (sqfreePart D) (gcd (sqfreePart D) p)

/-- The columns: `S L_D(xⁱ)` (`i < dW`), then `2 D² xʲ` (`j < nT`). -/
def colsG (p D S : CPoly ℚ) (dW nT : ℕ) : List (CPoly ℚ) :=
  (List.range dW).map (fun i ↦ mul S (LDc p D (monomial i 1))) ++
    (List.range nT).map fun j ↦ mul [2] (mul (mul D D) (monomial j 1))

/-- **The procedure** (`B`: the bound for the auxiliary prime of `ellDecideQ`). -/
noncomputable def ellDecideGenQ (a b c : ℤ) (A D : CPoly ℚ) (B : ℕ) : Option Bool :=
  if isZero D then none
  else
    let S := nbPart (pOf a b c) D
    let dW := A.length + D.length
    let nT := A.length + 2 * D.length + S.length + 3
    match linSolve (colsG (pOf a b c) D S dW nT) (mul [2] (mul (mul A D) S)) with
    | none => none
    | some cs => ellDecideQ a b c (cs.drop dW) S B

/-! ### Linear algebra of the columns -/

section Lin

variable {S : Type*} [Field S] (ι : ℚ →+* S)

lemma lcombS_append_take (w : List S) (L₁ L₂ : List (CPoly ℚ)) :
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

lemma lcombS_range_lin (f : ℕ → CPoly ℚ) (Φ : S[X] →ₗ[S] S[X])
    (hf : ∀ i, (toPoly (f i)).map ι = Φ (X ^ i)) :
    ∀ (n : ℕ) (w : List S), lcombS ι w ((List.range n).map f) = Φ (toPoly (w.take n)) := by
  classical
  intro n
  induction n with
  | zero => intro w; simp [lcombS]
  | succ n ih =>
    intro w
    rw [List.range_succ, List.map_append, lcombS_append_take, ih, List.length_map,
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
noncomputable def ldLin (M p D : S[X]) : S[X] →ₗ[S] S[X] where
  toFun W := M * LDK p D W
  map_add' W₁ W₂ := by simp only [LDK, derivative_add]; ring
  map_smul' c W := by
    simp only [LDK, smul_eq_C_mul, derivative_mul, derivative_C, zero_mul, zero_add,
      RingHom.id_apply]
    ring

lemma lcombS_colsG (p D M : CPoly ℚ) (dW nT : ℕ) (w : List S) :
    lcombS ι w (colsG p D M dW nT) =
      (toPoly M).map ι * LDK ((toPoly p).map ι) ((toPoly D).map ι) (toPoly (w.take dW)) +
        2 * ((toPoly D).map ι) ^ 2 * toPoly ((w.drop dW).take nT) := by
  rw [colsG, lcombS_append_take, List.length_map, List.length_range]
  rw [lcombS_range_lin ι _ (ldLin ((toPoly M).map ι) ((toPoly p).map ι) ((toPoly D).map ι))
      (fun i ↦ by
        simp only [ldLin, LinearMap.coe_mk, AddHom.coe_mk, toPoly_mul, toPoly_LDc,
          toPoly_monomial, map_one, one_mul, Polynomial.map_mul, LDK_map, Polynomial.map_pow,
          Polynomial.map_X]),
    lcombS_range_lin ι _ (LinearMap.mulLeft S (2 * ((toPoly D).map ι) ^ 2))
      (fun j ↦ by
        simp only [LinearMap.mulLeft_apply, toPoly_mul, toPoly_two, toPoly_monomial, map_one,
          one_mul, Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_pow,
          Polynomial.map_X]
        ring)]
  simp only [ldLin, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mulLeft_apply, List.take_take,
    min_self]

end Lin

/-! ### The non-branch squarefree part -/

section NB

variable (p D : CPoly ℚ) (hD : toPoly D ≠ 0)
include hD

lemma nbPart_facts :
    toPoly (sqfreePart D) ≠ 0 ∧ toPoly (gcd (sqfreePart D) p) ≠ 0 ∧
      toPoly (gcd (sqfreePart D) p) ∣ toPoly p ∧
      toPoly (sqfreePart D) = toPoly (nbPart p D) * toPoly (gcd (sqfreePart D) p) := by
  have hS0 : toPoly (sqfreePart D) ≠ 0 := fun h ↦ hD (by rw [sqfreePart_mul D hD, h, zero_mul])
  have hg := egcd_dvd (sqfreePart D) p
  rw [← toPoly_gcd] at hg
  have hg0 : toPoly (gcd (sqfreePart D) p) ≠ 0 := by
    intro h; rw [h] at hg; exact hS0 (zero_dvd_iff.mp hg.1)
  exact ⟨hS0, hg0, hg.2, div_mul_of_dvd _ _ hg0 hg.1⟩

lemma nbPart_ne_zero : toPoly (nbPart p D) ≠ 0 := by
  obtain ⟨hS0, -, -, he⟩ := nbPart_facts p D hD
  exact fun h ↦ hS0 (by rw [he, h, zero_mul])

lemma squarefree_nbPart : Squarefree (toPoly (nbPart p D)) := by
  obtain ⟨-, -, -, he⟩ := nbPart_facts p D hD
  have := squarefree_sqfreePart D hD
  rw [he] at this
  exact this.of_mul_left

lemma isCoprime_nbPart : IsCoprime (toPoly (nbPart p D)) (toPoly p) := by
  obtain ⟨hS0, -, -, he⟩ := nbPart_facts p D hD
  have hsq := squarefree_sqfreePart D hD
  refine isCoprime_of_irreducible_dvd (fun h ↦ nbPart_ne_zero p D hD h.1) fun z hz h1 h2 ↦ ?_
  have hzS0 : z ∣ toPoly (sqfreePart D) := by rw [he]; exact h1.mul_right _
  have hzg : z ∣ toPoly (gcd (sqfreePart D) p) := by rw [toPoly_gcd]; exact dvd_egcd _ _ hzS0 h2
  have : z * z ∣ toPoly (sqfreePart D) := by rw [he]; exact mul_dvd_mul h1 hzg
  exact hz.not_isUnit (hsq z this)

/-- Every non-branch root of `D` (in any extension) is a root of `S`. -/
lemma isRoot_nbPart {L : Type*} [Field L] [CharZero L] (ι : ℚ →+* L) (α : L)
    (hα : ((toPoly D).map ι).IsRoot α) (hpα : ¬((toPoly p).map ι).IsRoot α) :
    ((toPoly (nbPart p D)).map ι).IsRoot α := by
  obtain ⟨-, -, hgp, he⟩ := nbPart_facts p D hD
  have hDq : (toPoly D).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hD
  have hGd : toPoly (gcd D (deriv D)) ∣ derivative (toPoly D) := by
    rw [toPoly_gcd, ← toPoly_deriv]; exact (egcd_dvd D (deriv D)).2
  have h1 : X - C α ∣ (toPoly (sqfreePart D)).map ι := by
    refine irreducible_dvd_sqfreePart hDq (G := (toPoly (gcd D (deriv D))).map ι) ?_ ?_
      (irreducible_X_sub_C α) (dvd_iff_isRoot.mpr hα)
    · rw [sqfreePart_mul D hD, Polynomial.map_mul, mul_comm]
    · rw [derivative_map]; exact Polynomial.map_dvd ι hGd
  rw [he, Polynomial.map_mul] at h1
  rcases (prime_X_sub_C α).dvd_or_dvd h1 with h | h
  · exact dvd_iff_isRoot.mp h
  · exact absurd (dvd_iff_isRoot.mp (h.trans (Polynomial.map_dvd ι hgp))) hpα

end NB

/-! ### Correctness -/

section Spec

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- The Hermite identity from a solution of the system. -/
lemma hermite_of_linSolve (p A D M : CPoly ℚ) (dW nT : ℕ) (cs : List ℚ)
    (h : linSolve (colsG p D M dW nT) (mul [2] (mul (mul A D) M)) = some cs) :
    2 * toPoly A * toPoly D * toPoly M = toPoly M * LDK (toPoly p) (toPoly D)
      (toPoly (cs.take dW)) + 2 * toPoly D ^ 2 * toPoly (cs.drop dW) := by
  obtain ⟨hlen, hl⟩ := linSolve_sound _ _ _ h
  have e := lcombS_colsG (RingHom.id ℚ) p D M dW nT cs
  rw [Tower.MixN.lcombS_id', hl] at e
  simp only [Polynomial.map_id] at e
  have hlen' : (cs.drop dW).length ≤ nT := by
    rw [List.length_drop, hlen, colsG, List.length_append, List.length_map, List.length_range,
      List.length_map, List.length_range]; omega
  rw [List.take_of_length_le hlen'] at e
  rw [← e]
  simp only [toPoly_mul, toPoly_two]; ring

set_option maxHeartbeats 800000 in
/-- **Correctness of `ellDecideGenQ`** (algebraically closed constants). -/
theorem ellDecideGenQ_spec [IsAlgClosed Kc] (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (B : ℕ) (ans : Bool) (h : ellDecideGenQ a b c A D B = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hP ↦ by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hP)
  have hp : toPoly (pOf a b c) = X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ) :=
    toPoly_pOf a b c
  have hy' : y ^ 2 = aeval x (toPoly (pOf a b c)) := by rw [hp, hy]; simp
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hne _ (show toPoly (pOf a b c) ≠ 0 by rw [hp]; exact hsq.ne_zero)
    rw [← hy']; ring
  unfold ellDecideGenQ at h
  split_ifs at h with hDz
  have hD : toPoly D ≠ 0 := fun h0 ↦ hDz ((isZero_iff D).mpr h0)
  simp only at h
  split at h
  · cases h
  rename_i cs hls
  have hid := hermite_of_linSolve _ _ _ _ _ _ _ hls
  set M := nbPart (pOf a b c) D
  have hM := nbPart_ne_zero (pOf a b c) D hD
  have e := gen_identity x y hx (toPoly (pOf a b c)) (toPoly A) (toPoly D)
    (toPoly (cs.take (A.length + D.length))) (toPoly D)
    (toPoly (cs.drop (A.length + D.length))) (toPoly M) hy' hy0 (hne _ hD) (hne _ hD)
    (hne _ hM) (by unfold LDK at hid; linear_combination toPoly D * hid)
  rw [e, hasElementaryIntegral_deriv_add_iff', div_div]
  exact ellDecideQ_spec hC hCall x y hx a b c hsq hy hgen _ _ B ans h

end Spec

/-- **Completeness of `ellDecideGenQ`**: for every `D ≠ 0`, every large enough search bound
gives an answer. -/
theorem ellDecideGenQ_complete (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) :
    ∃ B0, ∀ B, B0 ≤ B → ellDecideGenQ a b c A D B ≠ none := by
  classical
  set p := pOf a b c with hpdef
  have hp : toPoly p = X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ) := toPoly_pOf a b c
  have hpdeg : (toPoly p).natDegree = 3 := by rw [hp]; compute_degree!
  set M := nbPart p D
  set dW := A.length + D.length
  set nT := A.length + 2 * D.length + M.length + 3
  set ι := algebraMap ℚ (AlgebraicClosure ℚ)
  have hinj : Function.Injective ι := ι.injective
  have hDl : 1 ≤ D.length := by
    rcases D with _ | ⟨d, D⟩
    · exact absurd (by simp) hD
    · simp
  -- the Hermite decomposition over `ℚ̄`
  have hsqQ : Squarefree ((toPoly p).map ι) :=
    ((PerfectField.separable_iff_squarefree.mpr (by rw [hp]; exact hsq)).map).squarefree
  have hp1 : 1 ≤ ((toPoly p).map ι).natDegree := by
    rw [natDegree_map_eq_of_injective hinj, hpdeg]; norm_num
  have hDq : (toPoly D).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hD
  obtain ⟨W, B₀, T, cf, hT, hB, hid⟩ := hermite_polyK ((toPoly p).map ι) hsqQ hp1
    ((toPoly A).map ι) ((toPoly D).map ι) hDq (IsAlgClosed.splits _)
  have hWd := hermite_deg_boundK _ hp1 _ _ W B₀ T cf hDq hB hid
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj] at hWd
  -- `∏_T (x − α)` divides `S`
  have hdvd : ∏ α ∈ T, (X - C α) ∣ (toPoly M).map ι := by
    refine Finset.prod_dvd_of_coprime
      ((pairwise_coprime_X_sub_C (s := fun α : AlgebraicClosure ℚ ↦ α) Function.injective_id).set_pairwise _)
      fun α hα ↦ dvd_iff_isRoot.mpr (isRoot_nbPart p D hD ι α (hT α hα).1 (hT α hα).2)
  obtain ⟨Q, hQ⟩ := hdvd
  set TQ := Q * ((∏ α ∈ T, (X - C α)) * B₀ + ∑ α ∈ T, C (cf α) * ∏ β ∈ T.erase α, (X - C β))
  have hidQ : 2 * (toPoly A).map ι * (toPoly D).map ι * (toPoly M).map ι =
      (toPoly M).map ι * LDK ((toPoly p).map ι) ((toPoly D).map ι) W +
        2 * ((toPoly D).map ι) ^ 2 * TQ := by
    rw [hQ]; simp only [TQ]; linear_combination Q * hid
  -- degree bounds
  have hAl := CPoly.natDegree_toPoly_le_length A
  have hDl' := CPoly.natDegree_toPoly_le_length D
  have hMl := CPoly.natDegree_toPoly_le_length M
  have hW : W = 0 ∨ W.natDegree < dW := Or.inr (by
    rcases le_total (toPoly A).natDegree (toPoly D).natDegree with h | h
    · rw [max_eq_right h] at hWd; omega
    · rw [max_eq_left h] at hWd; omega)
  have hTQ : TQ = 0 ∨ TQ.natDegree < nT := by
    rcases eq_or_ne TQ 0 with h0 | h0
    · exact Or.inl h0
    right
    have e : 2 * ((toPoly D).map ι) ^ 2 * TQ = 2 * (toPoly A).map ι * (toPoly D).map ι *
        (toPoly M).map ι - (toPoly M).map ι * LDK ((toPoly p).map ι) ((toPoly D).map ι) W := by
      rw [hidQ]; ring
    have h2 : (2 * ((toPoly D).map ι) ^ 2 * TQ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ hDq)) h0
    have hle := natDegree_le_of_dvd (dvd_mul_left TQ _) h2
    rw [e] at hle
    have hWd' : W.natDegree ≤ A.length + D.length := by
      rcases hW with h | h
      · rw [h]; simp
      · omega
    have hc0 : (2 : (AlgebraicClosure ℚ)[X]).natDegree ≤ 0 := by simp
    have h1 := nd_mulK (nd_mulK (nd_mulK hc0 (natDegree_map_le (f := ι) (p := toPoly A)))
      (natDegree_map_le (f := ι) (p := toPoly D))) (natDegree_map_le (f := ι) (p := toPoly M))
    have h3 := nd_mulK (natDegree_map_le (f := ι) (p := toPoly M))
      (natDegree_LD_leK ((toPoly p).map ι) ((toPoly D).map ι) W hp1)
    simp only [natDegree_map_eq_of_injective hinj, hpdeg] at h1 h3
    have hsub : (2 * (toPoly A).map ι * (toPoly D).map ι * (toPoly M).map ι -
        (toPoly M).map ι * LDK ((toPoly p).map ι) ((toPoly D).map ι) W).natDegree ≤
        max (2 * (toPoly A).map ι * (toPoly D).map ι * (toPoly M).map ι).natDegree
          ((toPoly M).map ι * LDK ((toPoly p).map ι) ((toPoly D).map ι) W).natDegree :=
      natDegree_sub_le _ _
    have h1' := h1.trans (show _ ≤ A.length + 2 * D.length + M.length + 2 by omega)
    have h3' := h3.trans (show _ ≤ A.length + 2 * D.length + M.length + 2 by omega)
    have := hle.trans (hsub.trans (max_le h1' h3'))
    simp only [nT]
    omega
  -- the rational system is solvable
  have hsol : linSolve (colsG p D M dW nT) (mul [2] (mul (mul A D) M)) ≠ none := by
    refine linSolve_complete_map ι _ _ ((List.range dW).map W.coeff ++ (List.range nT).map TQ.coeff)
      (by simp [colsG]) ?_
    rw [lcombS_colsG, List.take_left' (by simp), List.drop_left' (by simp),
      List.take_of_length_le (by simp), toPoly_range_coeff W dW hW, toPoly_range_coeff TQ nT hTQ]
    simp only [toPoly_mul, toPoly_two, Polynomial.map_mul, Polynomial.map_ofNat]
    rw [← hidQ]; ring
  obtain ⟨cs, hcs⟩ := Option.ne_none_iff_exists'.mp hsol
  obtain ⟨B0, hB0⟩ := ellDecideQ_complete a b c hsq (cs.drop dW) M (squarefree_nbPart p D hD)
    (by rw [← hp]; exact isCoprime_nbPart p D hD)
  refine ⟨B0, fun B hB ↦ ?_⟩
  unfold ellDecideGenQ
  split_ifs with hz
  · exact absurd ((isZero_iff D).mp hz) hD
  simp only
  rw [← hpdef, hcs]
  exact hB0 B hB

/-- **The decision**: for `∫ A dx / (D √p)` with `D ≠ 0` and algebraically closed constants,
`ellDecideGenQ` answers for all large search bounds, and the answer is the truth. -/
theorem ellDecideGenQ_decides {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc]
    [Differential E] [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E] [IsAlgClosed Kc]
    (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) :
    ∃ B0, ∀ B, B0 ≤ B → ∃ ans : Bool, ellDecideGenQ a b c A D B = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
  obtain ⟨B0, hB0⟩ := ellDecideGenQ_complete a b c hsq A D hD
  refine ⟨B0, fun B hB ↦ ?_⟩
  obtain ⟨ans, h⟩ := Option.ne_none_iff_exists'.mp (hB0 B hB)
  exact ⟨ans, h, ellDecideGenQ_spec hC hCall x y hx a b c hsq hy hgen A D B ans h⟩

end EllQuad
