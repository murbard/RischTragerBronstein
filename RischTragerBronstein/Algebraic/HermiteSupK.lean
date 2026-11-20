import RischTragerBronstein.Algebraic.HermitePolySup
import RischTragerBronstein.Jacobian.HermiteK

/-!
# The superelliptic Hermite reduction by linear algebra

`A D S = S L_D(W) + D² T` (`L_D(W) = (W′D − WD′)p + μ W D p′`, `S` the non-branch part of the
squarefree part of `D`) is solved by `linSolve` over `K` (`colsS`); a solution gives the identity
(`hermiteS_of_linSolve`), and one always exists (`hermiteS_solve_ne_none`, through the algebraic
closure, with `W` reduced modulo `D`).
-/

open Polynomial CPoly EllAlgo EllQuad

namespace Jac

variable {K : Type*} [Field K] [DecidableEq K]

/-- `L_D(W)`, executable. -/
def LDcS (μ : K) (p D W : CPoly K) : CPoly K :=
  add (mul (sub (mul (deriv W) D) (mul W (deriv D))) p) (smul μ (mul (mul W D) (deriv p)))

omit [DecidableEq K] in
lemma toPoly_LDcS (μ : K) (p D W : CPoly K) :
    toPoly (LDcS μ p D W) = LDS μ (toPoly p) (toPoly D) (toPoly W) := by
  simp only [LDcS, LDS, toPoly_add, toPoly_mul, toPoly_sub, toPoly_deriv, toPoly_smul]; ring

omit [DecidableEq K] in
lemma LDS_map {S : Type*} [Field S] (ι : K →+* S) (μ : K) (p D W : K[X]) :
    (LDS μ p D W).map ι = LDS (ι μ) (p.map ι) (D.map ι) (W.map ι) := by
  simp only [LDS, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, derivative_map,
    Polynomial.map_C]

/-- The columns: `S L_D(xⁱ)` (`i < dW`), then `D² xʲ` (`j < nT`). -/
def colsS (μ : K) (p D S : CPoly K) (dW nT : ℕ) : List (CPoly K) :=
  (List.range dW).map (fun i ↦ mul S (LDcS μ p D (monomial i 1))) ++
    (List.range nT).map fun j ↦ mul (mul D D) (monomial j 1)

section Lin

variable {S : Type*} [Field S] (ι : K →+* S)

/-- `W ↦ M · L_D(W)` as a linear map. -/
noncomputable def ldLinS (μ : S) (M p D : S[X]) : S[X] →ₗ[S] S[X] where
  toFun W := M * LDS μ p D W
  map_add' W₁ W₂ := by simp only [LDS, derivative_add]; ring
  map_smul' c W := by
    simp only [LDS, smul_eq_C_mul, derivative_mul, derivative_C, zero_mul, zero_add,
      RingHom.id_apply]
    ring

lemma lcombS_colsS (μ : K) (p D M : CPoly K) (dW nT : ℕ) (w : List S) :
    lcombS ι w (colsS μ p D M dW nT) =
      (toPoly M).map ι * LDS (ι μ) ((toPoly p).map ι) ((toPoly D).map ι) (toPoly (w.take dW)) +
        ((toPoly D).map ι) ^ 2 * toPoly ((w.drop dW).take nT) := by
  rw [colsS, lcombS_append_takeK, List.length_map, List.length_range]
  rw [lcombS_range_linK ι _ (ldLinS (ι μ) ((toPoly M).map ι) ((toPoly p).map ι) ((toPoly D).map ι))
      (fun i ↦ by
        simp only [ldLinS, LinearMap.coe_mk, AddHom.coe_mk, toPoly_mul, toPoly_LDcS,
          toPoly_monomial, map_one, one_mul, Polynomial.map_mul, LDS_map, Polynomial.map_pow,
          Polynomial.map_X]),
    lcombS_range_linK ι _ (LinearMap.mulLeft S (((toPoly D).map ι) ^ 2))
      (fun j ↦ by
        simp only [LinearMap.mulLeft_apply, toPoly_mul, toPoly_monomial, map_one,
          one_mul, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
        ring)]
  simp only [ldLinS, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mulLeft_apply, List.take_take,
    min_self]

end Lin

/-- The Hermite identity from a solution of the system. -/
lemma hermiteS_of_linSolve (μ : K) (p A D M : CPoly K) (dW nT : ℕ) (cs : List K)
    (h : linSolve (colsS μ p D M dW nT) (mul (mul A D) M) = some cs) :
    toPoly A * toPoly D * toPoly M = toPoly M * LDS μ (toPoly p) (toPoly D)
      (toPoly (cs.take dW)) + toPoly D ^ 2 * toPoly (cs.drop dW) := by
  obtain ⟨hlen, hl⟩ := linSolve_sound _ _ _ h
  have e := lcombS_colsS (RingHom.id K) μ p D M dW nT cs
  rw [show lcombS (RingHom.id K) cs (colsS μ p D M dW nT) = lcomb cs (colsS μ p D M dW nT) by
    simp [lcombS, lcomb], hl] at e
  simp only [Polynomial.map_id, RingHom.id_apply] at e
  have hlen' : (cs.drop dW).length ≤ nT := by
    rw [List.length_drop, hlen, colsS, List.length_append, List.length_map, List.length_range,
      List.length_map, List.length_range]; omega
  rw [List.take_of_length_le hlen'] at e
  rw [← e]
  simp only [toPoly_mul]

lemma natDegree_LDS_le [CharZero K] (μ : K) (p D W : K[X]) (hp1 : 1 ≤ p.natDegree) :
    (LDS μ p D W).natDegree ≤ W.natDegree + D.natDegree + p.natDegree - 1 := by
  set N := W.natDegree + D.natDegree + p.natDegree - 1
  have hW' := natDegree_derivative_le W
  have hD' := natDegree_derivative_le D
  have hp' := natDegree_derivative_le p
  have h1 : (derivative W * D * p).natDegree ≤ N := by
    rcases Nat.eq_zero_or_pos W.natDegree with h0 | hpos
    · rw [show derivative W = 0 by rw [eq_C_of_natDegree_eq_zero h0]; exact derivative_C]
      simp
    · exact (nd_mulK (nd_mulK hW' le_rfl) le_rfl).trans (by omega)
  have h2 : (W * derivative D * p).natDegree ≤ N := by
    rcases Nat.eq_zero_or_pos D.natDegree with h0 | hpos
    · rw [show derivative D = 0 by rw [eq_C_of_natDegree_eq_zero h0]; exact derivative_C]
      simp
    · exact (nd_mulK (nd_mulK le_rfl hD') le_rfl).trans (by omega)
  have h3 : (W * D * derivative p).natDegree ≤ N :=
    (nd_mulK (nd_mulK le_rfl le_rfl) hp').trans (by omega)
  have e : LDS μ p D W = (derivative W * D * p) - (W * derivative D * p) +
      C μ * (W * D * derivative p) := by
    rw [LDS]; ring
  rw [e]
  exact (natDegree_add_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le h1 h2))
    ((natDegree_C_mul_le _ _).trans h3))

theorem hermiteS_solve_ne_none [CharZero K] (μ : K) (hμ : ∀ k : ℕ, μ ≠ k + 1) (p A D : CPoly K)
    (hsq : Squarefree (toPoly p)) (hp1 : 1 ≤ (toPoly p).natDegree) (hD : toPoly D ≠ 0) :
    linSolve (colsS μ p D (nbPartK p D) D.length
      (A.length + D.length + (nbPartK p D).length + p.length + 3))
      (mul (mul A D) (nbPartK p D)) ≠ none := by
  classical
  set M := nbPartK p D
  set dW := D.length
  set nT := A.length + D.length + M.length + p.length + 3
  set ι := algebraMap K (AlgebraicClosure K)
  have hinj : Function.Injective ι := ι.injective
  have hsqQ : Squarefree ((toPoly p).map ι) :=
    ((PerfectField.separable_iff_squarefree.mpr hsq).map).squarefree
  have hp1' : 1 ≤ ((toPoly p).map ι).natDegree := by
    rw [natDegree_map_eq_of_injective hinj]; exact hp1
  have hDq : (toPoly D).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hD
  have hμ' : ∀ k : ℕ, ι μ ≠ k + 1 := fun k h ↦ hμ k (hinj (by rw [h]; simp))
  obtain ⟨W, B₀, T, cf, hT, hid⟩ := hermite_polyS ((toPoly p).map ι) hsqQ (ι μ) hμ'
    ((toPoly A).map ι) ((toPoly D).map ι) hDq (IsAlgClosed.splits _)
  have hdvd : ∏ α ∈ T, (X - C α) ∣ (toPoly M).map ι := by
    refine Finset.prod_dvd_of_coprime
      ((pairwise_coprime_X_sub_C (s := fun α : AlgebraicClosure K ↦ α)
        Function.injective_id).set_pairwise _)
      fun α hα ↦ dvd_iff_isRoot.mpr (isRoot_nbPartK p D hD ι α (hT α hα).1 (hT α hα).2)
  obtain ⟨Q, hQ⟩ := hdvd
  -- reduce `W` modulo `D`
  set Dq := (toPoly D).map ι
  set V := W / Dq
  set W₀ := W % Dq
  have hWVD : W = V * Dq + W₀ := (EuclideanDomain.div_add_mod' W Dq).symm
  have hLV : LDS (ι μ) ((toPoly p).map ι) Dq W =
      LDS (ι μ) ((toPoly p).map ι) Dq W₀ +
        Dq ^ 2 * (derivative V * (toPoly p).map ι + C (ι μ) * V * derivative ((toPoly p).map ι)) := by
    rw [hWVD]; simp only [LDS, derivative_add, derivative_mul]; ring
  set Pm := (toPoly p).map ι
  set TQ := Q * ((∏ α ∈ T, (X - C α)) * B₀ + ∑ α ∈ T, C (cf α) * ∏ β ∈ T.erase α, (X - C β)) +
    (toPoly M).map ι * (derivative V * Pm + C (ι μ) * V * derivative Pm)
  have hidQ : (toPoly A).map ι * Dq * (toPoly M).map ι =
      (toPoly M).map ι * LDS (ι μ) Pm Dq W₀ + Dq ^ 2 * TQ := by
    simp only [TQ]; rw [hQ]
    rw [hLV] at hid
    linear_combination Q * hid
  have hAl := CPoly.natDegree_toPoly_le_length A
  have hDl' := CPoly.natDegree_toPoly_le_length D
  have hMl := CPoly.natDegree_toPoly_le_length M
  have hpl := CPoly.natDegree_toPoly_le_length p
  have hW₀ : W₀ = 0 ∨ W₀.natDegree < dW := by
    rcases eq_or_ne W₀ 0 with h0 | h0
    · exact Or.inl h0
    right
    have := EuclideanDomain.mod_lt W hDq
    have hdeg := natDegree_lt_natDegree h0 this
    rw [natDegree_map_eq_of_injective hinj] at hdeg
    omega
  have hTQ : TQ = 0 ∨ TQ.natDegree < nT := by
    rcases eq_or_ne TQ 0 with h0 | h0
    · exact Or.inl h0
    right
    have e' : Dq ^ 2 * TQ = (toPoly A).map ι * Dq * (toPoly M).map ι -
        (toPoly M).map ι * LDS (ι μ) Pm Dq W₀ := by
      rw [hidQ]; ring
    have hprod : (Dq ^ 2 * TQ).natDegree = 2 * (toPoly D).natDegree + TQ.natDegree := by
      rw [natDegree_mul (pow_ne_zero _ hDq) h0, natDegree_pow,
        natDegree_map_eq_of_injective hinj]
    rw [e'] at hprod
    have h1 := nd_mulK (nd_mulK (natDegree_map_le (f := ι) (p := toPoly A))
      (natDegree_map_le (f := ι) (p := toPoly D))) (natDegree_map_le (f := ι) (p := toPoly M))
    have h3 := nd_mulK (natDegree_map_le (f := ι) (p := toPoly M))
      (natDegree_LDS_le (ι μ) Pm Dq W₀ hp1')
    simp only [Pm, Dq, natDegree_map_eq_of_injective hinj] at h1 h3
    have h5 := natDegree_sub_le ((toPoly A).map ι * Dq * (toPoly M).map ι)
      ((toPoly M).map ι * LDS (ι μ) Pm Dq W₀)
    rw [hprod] at h5
    have hW0d : W₀.natDegree ≤ (toPoly D).natDegree := by
      rcases hW₀ with h | h
      · rw [h]; simp
      · rcases eq_or_ne W₀ 0 with h' | h'
        · rw [h']; simp
        have := EuclideanDomain.mod_lt W hDq
        have hdeg := natDegree_lt_natDegree h' this
        rw [natDegree_map_eq_of_injective hinj] at hdeg
        omega
    have h6 : 2 * (toPoly D).natDegree + TQ.natDegree ≤
        max ((toPoly A).natDegree + (toPoly D).natDegree + (toPoly M).natDegree)
          ((toPoly M).natDegree + (W₀.natDegree + (toPoly D).natDegree +
            (toPoly p).natDegree - 1)) := h5.trans (max_le_max h1 h3)
    simp only [nT]
    rcases le_total ((toPoly A).natDegree + (toPoly D).natDegree + (toPoly M).natDegree)
      ((toPoly M).natDegree + (W₀.natDegree + (toPoly D).natDegree + (toPoly p).natDegree - 1))
      with h | h
    · rw [max_eq_right h] at h6; omega
    · rw [max_eq_left h] at h6; omega
  refine linSolve_complete_map ι _ _ ((List.range dW).map W₀.coeff ++ (List.range nT).map TQ.coeff)
    (by simp [colsS]) ?_
  rw [lcombS_colsS, List.take_left' (by simp), List.drop_left' (by simp),
    List.take_of_length_le (by simp), toPoly_range_coeff W₀ dW hW₀, toPoly_range_coeff TQ nT hTQ]
  simp only [toPoly_mul, Polynomial.map_mul]
  rw [← hidQ]

end Jac
