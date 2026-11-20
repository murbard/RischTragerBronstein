import RischTragerBronstein.Mixed.KQMMain

/-!
# Independence of the choice of square roots

The residue points of `kxDecide` use products of square roots of the constant generators
(`SqrtIndep.prodRoots rts T` for a subset `T`). Another choice `rts'` (same squares) changes each
product by a sign that depends only on `T` (`prodRoots_sign`), so all points of one class flip
together, `Δ_k ↦ ±Δ_k`; and the Mordell–Weil condition `∀ N > 0, μ, 2N D + 2μ Z ≠ 0` is invariant
under `D ↦ −D` (`grp_neg`). Hence a certificate for one root choice serves every choice.
-/

namespace SqrtIndep

variable {K : Type*} [Field K] [CharZero K]

/-- **Changing the square roots changes each product by a sign.** -/
theorem prodRoots_sign : ∀ (rts rts' : List K), rts'.length = rts.length →
    (∀ i (h : i < rts.length) (h' : i < rts'.length), rts'[i] ^ 2 = rts[i] ^ 2) →
    ∀ T : List Bool, prodRoots rts' T = prodRoots rts T ∨ prodRoots rts' T = -prodRoots rts T
  | [], [], _, _, T => by cases T <;> simp [prodRoots]
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | y :: r, y' :: r', hl, hsq, T => by
    cases T with
    | nil => simp [prodRoots]
    | cons b T =>
      have hy : y' = y ∨ y' = -y := by
        have := hsq 0 (by simp) (by simp)
        simp only [List.getElem_cons_zero] at this
        have h2 : (y' - y) * (y' + y) = 0 := by linear_combination this
        rcases mul_eq_zero.mp h2 with h | h
        · exact Or.inl (sub_eq_zero.mp h)
        · exact Or.inr (by linear_combination h)
      have ih := prodRoots_sign r r' (by simpa using hl)
        (fun i h h' ↦ by
          have := hsq (i + 1) (by simp; omega) (by simp; omega)
          simpa only [List.getElem_cons_succ] using this) T
      simp only [prodRoots]
      cases b
      · simp only [Bool.false_eq_true, if_false, one_mul]; exact ih
      · simp only [if_true]
        rcases hy with rfl | rfl <;> rcases ih with h | h <;> rw [h]
        · left; rfl
        · right; ring
        · right; ring
        · left; ring

/-- Ring homomorphisms commute with `prodRoots`. -/
theorem map_prodRoots {K' : Type*} [Field K'] (f : K →+* K') :
    ∀ (rts : List K) (T : List Bool), f (prodRoots rts T) = prodRoots (rts.map f) T
  | [], T => by cases T <;> simp [prodRoots]
  | y :: r, [] => by simp [prodRoots]
  | y :: r, b :: T => by
    simp only [prodRoots, List.map_cons, map_mul, map_prodRoots f r T]
    cases b <;> simp

end SqrtIndep

/-- **The group condition is invariant under `D ↦ −D`.** -/
theorem grp_neg {G : Type*} [AddCommGroup G] (D Z : G)
    (h : ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • D + (2 * μ) • Z ≠ 0) :
    ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • (-D) + (2 * μ) • Z ≠ 0 := by
  intro N hN μ hrel
  apply h N hN (-μ)
  have : (2 * (N : ℤ)) • D + (2 * -μ) • Z = -((2 * (N : ℤ)) • (-D) + (2 * μ) • Z) := by
    simp only [smul_neg, neg_add, neg_neg, mul_neg, neg_smul]
  rw [this, hrel, neg_zero]

/-- **Signs**: the group condition transfers to `±D, ±Z`. -/
theorem grp_signs {G : Type*} [AddCommGroup G] (D Z D' Z' : G) (hD : D' = D ∨ D' = -D)
    (hZ : Z' = Z ∨ Z' = -Z)
    (h : ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • D + (2 * μ) • Z ≠ 0) :
    ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • D' + (2 * μ) • Z' ≠ 0 := by
  have h1 : ∀ N : ℕ, 0 < N → ∀ μ : ℤ, (2 * (N : ℤ)) • D + (2 * μ) • (-Z) ≠ 0 := by
    intro N hN μ hrel
    apply h N hN (-μ)
    rw [← hrel]; simp only [smul_neg, mul_neg, neg_smul]
  rcases hD with hD | hD <;> rcases hZ with hZ | hZ <;> rw [hD, hZ]
  · exact h
  · exact h1
  · exact grp_neg D Z h
  · exact grp_neg D (-Z) h1
