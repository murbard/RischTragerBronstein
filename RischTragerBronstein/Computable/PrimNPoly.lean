import RischTragerBronstein.Computable.PrimN

/-!
# Soundness of `polyDown`

`polyDown` solves, from the top coefficient down, `Yₖ′ + (k + 1) Yₖ₊₁ η = Pₖ` (`k ≥ 1`) for the
polynomial part `P = ∑ Pₖ tᵏ` of an integrand in `K(t)`, `t′ = η`. The invariant at the state
`(j, Q, Ys)` (`Q` the particular value of `Y_{j+1}`, `Ys = [Y_{j+2}, …]`):

  `D (X^(j+1) (Q + X Ys)) = X^(j+1) P_{≥ j+1} + (j + 1) Q η X^j`,

where `D = implicitDeriv (C η)` and `P_{≥ j+1}` is `P` with its first `j + 1` coefficients dropped.
At the end (`j = 0`) this says `D (X (Q + X Ys)) = X P_{≥ 1} + Q η`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.PrimN

variable {α : Type} {K : Type*} [Field K] [Differential K] [CharZero K] {O : COps α} (M : CField α K O)

lemma implicitDeriv_C_mul_X_pow_succ (η a : K) (n : ℕ) :
    implicitDeriv (C η) (C a * X ^ (n + 1)) =
      C a′ * X ^ (n + 1) + C (((n : K) + 1) * a * η) * X ^ n := by
  rw [Derivation.leibniz, implicitDeriv_C, Derivation.leibniz_pow, implicitDeriv_X]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  have : ((n + 1 : ℕ) : K[X]) = C ((n : K) + 1) := by simp
  rw [this]
  simp only [C_mul]
  ring

lemma toPoly_drop (P : GPoly α) (n : ℕ) :
    GPoly.toPoly M (P.drop n) =
      C (M.sem (P.getD n O.zero)) + X * GPoly.toPoly M (P.drop (n + 1)) := by
  by_cases hn : n < P.length
  · rw [List.drop_eq_getElem_cons hn, GPoly.toPoly_cons, List.getD_eq_getElem _ _ hn]
  · rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega),
      List.getD_eq_default _ _ (by omega), M.sem_zero]
    simp

/-- **Soundness of `polyDown`**: the invariant is preserved down to `j = 0`. -/
theorem polyDown_sound (η : α) (ηc : Code 1) (lv : Code 1 → K)
    (solve : α → List (Code 1) → Option (List ℚ × α)) (cst : ℚ → α)
    (hsolve : ∀ G W r, solve G W = some r → r.1.length = W.length ∧
      (M.sem r.2)′ + (List.zipWith (fun (c : ℚ) w ↦ (c : K) * lv w) r.1 W).sum = M.sem G)
    (hη : lv ηc = M.sem η) (hcst : ∀ c, M.sem (cst c) = (c : K))
    (hc' : ∀ c : ℚ, (c : K)′ = 0) (P : GPoly α) :
    ∀ (j : ℕ) (Q : α) (Ys : List α) (Q' : α) (Ys' : List α),
      implicitDeriv (C (M.sem η)) (X ^ (j + 1) * GPoly.toPoly M (Q :: Ys)) =
        X ^ (j + 1) * GPoly.toPoly M (P.drop (j + 1)) +
          C (((j : K) + 1) * M.sem Q * M.sem η) * X ^ j →
      polyDown O η ηc solve cst P j Q Ys = some (Q', Ys') →
      implicitDeriv (C (M.sem η)) (X * GPoly.toPoly M (Q' :: Ys')) =
        X * GPoly.toPoly M (P.drop 1) + C (M.sem Q' * M.sem η) := by
  intro j
  induction j with
  | zero =>
    intro Q Ys Q' Ys' hinv hpd
    simp only [polyDown, Option.some.injEq, Prod.mk.injEq] at hpd
    obtain ⟨rfl, rfl⟩ := hpd
    simpa using hinv
  | succ k ih =>
    intro Q Ys Q' Ys' hinv hpd
    simp only [polyDown] at hpd
    generalize hs : solve (O.add (P.getD (k + 1) O.zero)
      (O.neg (O.mul (O.mul (O.natCast (k + 2)) Q) η))) [ηc] = r at hpd
    match r, hs, hpd with
    | some ([e], Y), hs, hpd =>
      obtain ⟨-, hY⟩ := hsolve _ _ _ hs
      simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, List.sum_nil,
        add_zero, hη, M.sem_add, M.sem_neg, M.sem_mul, M.sem_natCast] at hY
      refine ih Y _ Q' Ys' ?_ hpd
      -- the new invariant
      set ηv := M.sem η
      have hd : implicitDeriv (C ηv) (X ^ (k + 1) * GPoly.toPoly M
          (Y :: O.add Q (cst (e / (k + 2 : ℚ))) :: Ys)) =
          implicitDeriv (C ηv) (C (M.sem Y) * X ^ (k + 1)) +
          implicitDeriv (C ηv) (X ^ (k + 1 + 1) * GPoly.toPoly M (Q :: Ys)) +
          implicitDeriv (C ηv) (C (M.sem (cst (e / (k + 2 : ℚ)))) * X ^ (k + 1 + 1)) := by
        rw [← map_add, ← map_add]
        congr 1
        simp only [GPoly.toPoly_cons, M.sem_add, C_add]
        ring
      rw [hd, hinv, implicitDeriv_C_mul_X_pow_succ, implicitDeriv_C_mul_X_pow_succ, hcst, hc',
        toPoly_drop M P (k + 1)]
      have hY' : (M.sem Y)′ = M.sem (P.getD (k + 1) O.zero) - ((k : K) + 1 + 1) * M.sem Q * ηv -
          (e : K) * ηv := by
        push_cast at hY
        linear_combination hY
      rw [hY']
      simp only [C_0, zero_mul, C_sub, C_mul]
      have h2 : ((k + 1 : ℕ) : K) = (k : K) + 1 := by push_cast; ring
      rw [h2]
      have hk : ((k : K) + 1 + 1) * ((e / (k + 2 : ℚ) : ℚ) : K) = (e : K) := by
        rw [Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat]
        have : (k : K) + 2 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (k + 1))
        field_simp
        ring
      have hC' : C ((k : K) + 1 + 1) * C ((e / (k + 2 : ℚ) : ℚ) : K) = C (e : K) := by
        rw [← C_mul, hk]
      linear_combination (C ηv * X ^ (k + 1)) * hC'
    | some ([], _), _, hpd => simp at hpd
    | some (_ :: _ :: _, _), _, hpd => simp at hpd
    | none, _, hpd => simp at hpd

end Tower.PrimN
