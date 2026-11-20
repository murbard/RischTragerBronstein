import RischTragerBronstein.Computable.PrimNPoly

/-!
# Completeness of `polyDown`

Let `P = ∑ pₖ tᵏ ∈ K[t]` be a **true** solution of the polynomial-part equations,
`pₖ′ + (k + 1) pₖ₊₁ η = Pₖ` for `k ≥ 1`, with constants in a subfield `Kc` (the constants of `K`)
and `η` not a derivative in `K`. Then `polyDown` never fails, provided its solver is sound and
complete, and the particular values it keeps differ from the true `pₖ` by constants only:
at each step the constant of integration `c` is forced (`(Y - pₖ)′ = c η` implies `c = 0`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.PrimN

variable {α : Type} {K Kc : Type*} [Field K] [Differential K] [CharZero K] [Field Kc]
variable [Algebra Kc K] {O : COps α} (M : CField α K O)

/-- **Uniqueness of the constant**: two solutions of `y′ + c η = G` with constant `c` differ by
a constant, and have the same `c`, when `η` is not a derivative. -/
lemma sub_const_of_same_rhs {η Y p a b : K} (ha : a′ = 0) (hb : b′ = 0)
    (hηnd : ∀ y : K, y′ ≠ η) (hconst : ∀ y : K, y′ = 0 → ∃ κ : Kc, y = algebraMap Kc K κ)
    (h : Y′ + a * η = p′ + b * η) : ∃ κ : Kc, Y = p + algebraMap Kc K κ := by
  by_cases hab : b - a = 0
  · obtain ⟨κ, hκ⟩ := hconst (Y - p) (by
      rw [map_sub]; linear_combination h + η * hab)
    exact ⟨κ, by rw [← hκ]; ring⟩
  · exfalso
    refine hηnd ((Y - p) / (b - a)) ?_
    have hd : (b - a)′ = 0 := by rw [map_sub, ha, hb, sub_zero]
    have hY : Y′ - p′ = (b - a) * η := by linear_combination h
    rw [Derivation.leibniz_div, hd, map_sub, hY]
    simp only [smul_eq_mul, mul_zero, sub_zero]
    field_simp

/-- **Completeness of `polyDown`.** -/
theorem polyDown_complete (η : α) (ηc : Code 1) (lv : Code 1 → K)
    (solve : α → List (Code 1) → Option (List ℚ × α)) (cst : ℚ → α)
    (hsolve : ∀ G W r, solve G W = some r → r.1.length = W.length ∧
      (M.sem r.2)′ + (List.zipWith (fun (c : ℚ) w ↦ (c : K) * lv w) r.1 W).sum = M.sem G)
    (hcomp : ∀ G W (y : K) (c : List Kc), c.length = W.length →
      y′ + (List.zipWith (fun (c : Kc) w ↦ algebraMap Kc K c * lv w) c W).sum = M.sem G →
        solve G W ≠ none)
    (hη : lv ηc = M.sem η) (hηnd : ∀ y : K, y′ ≠ M.sem η)
    (hconst : ∀ y : K, y′ = 0 → ∃ κ : Kc, y = algebraMap Kc K κ)
    (hKc : ∀ κ : Kc, (algebraMap Kc K κ)′ = 0) (hc' : ∀ c : ℚ, (c : K)′ = 0)
    (Pc : GPoly α) (P : K[X])
    (hP : ∀ k, 1 ≤ k → (P.coeff k)′ + ((k : K) + 1) * P.coeff (k + 1) * M.sem η =
      M.sem (Pc.getD k O.zero)) :
    ∀ (j : ℕ) (Q : α) (Ys : List α), (∃ κ : Kc, M.sem Q = P.coeff (j + 1) + algebraMap Kc K κ) →
      ∃ Q' Ys', polyDown O η ηc solve cst Pc j Q Ys = some (Q', Ys') ∧
        ∃ κ : Kc, M.sem Q' = P.coeff 1 + algebraMap Kc K κ := by
  intro j
  induction j with
  | zero =>
    intro Q Ys hQ
    exact ⟨Q, Ys, rfl, hQ⟩
  | succ k ih =>
    intro Q Ys ⟨κ, hκ⟩
    set G := O.add (Pc.getD (k + 1) O.zero) (O.neg (O.mul (O.mul (O.natCast (k + 2)) Q) η))
      with hG
    have hGv : M.sem G = M.sem (Pc.getD (k + 1) O.zero) - ((k : K) + 2) * M.sem Q * M.sem η := by
      rw [hG, M.sem_add, M.sem_neg, M.sem_mul, M.sem_mul, M.sem_natCast]
      push_cast
      ring
    -- the true solution of the limited problem
    have hwit : (P.coeff (k + 1))′ + (List.zipWith (fun (c : Kc) w ↦ algebraMap Kc K c * lv w)
        [-(((k : Kc) + 2) * κ)] [ηc]).sum = M.sem G := by
      have h1 := hP (k + 1) (by omega)
      simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil,
        add_zero, hη, map_neg, map_mul, map_add, map_natCast, map_ofNat, hGv, hκ]
      push_cast at h1
      linear_combination h1
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (hcomp G [ηc] _ _ rfl hwit)
    obtain ⟨hlen, hY⟩ := hsolve _ _ _ hr
    obtain ⟨cs, Y⟩ := r
    match cs, hlen, hY, hr with
    | [e], _, hY, hr =>
      simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil,
        add_zero, hη] at hY
      simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil,
        add_zero, hη] at hwit
      obtain ⟨κ', hκ'⟩ := sub_const_of_same_rhs (Kc := Kc) (hc' e) (hKc _) hηnd hconst
        (hY.trans hwit.symm)
      obtain ⟨Q', Ys', hpd, hQ'⟩ := ih Y (O.add Q (cst (e / (k + 2 : ℚ))) :: Ys) ⟨κ', hκ'⟩
      refine ⟨Q', Ys', ?_, hQ'⟩
      simp only [polyDown]
      rw [← hG, hr]
      exact hpd

end Tower.PrimN
