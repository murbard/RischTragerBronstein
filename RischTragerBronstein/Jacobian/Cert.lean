import RischTragerBronstein.Jacobian.Orders

/-!
# Division-free certificates for principality, and exact orders

* `vanishCheck`: given a function `(a, b)`, a point `(x₀, y₀, k)` and a candidate branch jet `V`,
  checks `V(0) = y₀`, `V² ≡ f(x₀ + s)` and `a(x₀ + s) + b(x₀ + s) V ≡ 0 (mod sᵏ)` using ring
  operations only; `vanishCheck_sound` gives `VanishAt`.
* `principalCert` / `principalCert_sound`: a checked witness of `PrincipalMul`.
* `exact_order_of_prime_divisors`: `m D` principal and `(m / r) D` not principal for every prime
  `r ∣ m` make `m` the exact order (via closure under `gcd`).
-/

open Polynomial CPoly

namespace Jac

variable {F : Type*} [Field F] [DecidableEq F]

/-- Division-free check of vanishing to order `k` at `(x₀, y₀)` with branch jet `V`. -/
def vanishCheck (f a b : CPoly F) (pt : F × F × ℕ) (V : CPoly F) : Bool :=
  V.getD 0 0 == pt.2.1 &&
    isZero (truncC pt.2.2 (sub (mul V V) (taylorC pt.1 f))) &&
    isZero (truncC pt.2.2 (add (taylorC pt.1 a) (mul (taylorC pt.1 b) V)))

lemma isZero_truncC_iff (n : ℕ) (p : CPoly F) : isZero (truncC n p) = true ↔ X ^ n ∣ toPoly p := by
  rw [isZero_iff, toPoly_truncC, truncX_eq_zero_iff]

theorem vanishCheck_sound {f a b : CPoly F} {pt : F × F × ℕ} {V : CPoly F}
    (h : vanishCheck f a b pt V = true) :
    VanishAt (toPoly f) (toPoly a) (toPoly b) pt.1 pt.2.1 pt.2.2 := by
  simp only [vanishCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  rw [isZero_truncC_iff] at h1 h2
  refine ⟨toPoly V, ⟨by rw [coeff_toPoly, h0], ?_⟩, ?_⟩
  · simpa [toPoly_taylorC, sq] using h1
  · simpa [jet, toPoly_taylorC] using h2

/-- A checked witness that `n Γ` is principal: the function, degree bounds, and branch jets. -/
def principalCert (f : CPoly F) (g : ℕ) (Γ : EDiv F) (a b : CPoly F) (Vs : List (CPoly F)) :
    Bool :=
  !(isZero a && isZero b) && (2 * (a.length - 1) ≤ edeg Γ) &&
    (b.isEmpty || 2 * (b.length - 1) + 2 * g + 1 ≤ edeg Γ) &&
    (Γ.length == Vs.length) && (List.zipWith (fun pt V ↦ vanishCheck f a b pt V) Γ Vs).all id

theorem principalCert_sound {f : CPoly F} {g : ℕ} {Γ : EDiv F} {a b : CPoly F}
    {Vs : List (CPoly F)} (h : principalCert f g Γ a b Vs = true) :
    ∃ ψ : F[X] × F[X], ψ ≠ (0, 0) ∧ PoleLE g ψ (edeg Γ) ∧ Vanishes (toPoly f) ψ Γ := by
  simp only [principalCert, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    Bool.or_eq_true, List.isEmpty_iff, beq_iff_eq, List.all_eq_true, id_eq] at h
  obtain ⟨⟨⟨⟨hnz, ha⟩, hb⟩, hlen⟩, hv⟩ := h
  refine ⟨(toPoly a, toPoly b), ?_, ⟨?_, ?_⟩, ?_⟩
  · intro h0
    simp only [Prod.mk.injEq] at h0
    have h1 := (isZero_iff a).mpr h0.1
    have h2 := (isZero_iff b).mpr h0.2
    simp [h1, h2] at hnz
  · exact (Nat.mul_le_mul_left 2 (CPoly.natDegree_toPoly_le_length a)).trans ha
  · rcases hb with hb | hb
    · left; simp [hb]
    · right
      exact (Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.mul_le_mul_left 2 (CPoly.natDegree_toPoly_le_length b)) _) _).trans hb
  · intro q hq
    obtain ⟨i, rfl⟩ := List.get_of_mem hq
    have hi : i.1 < (List.zipWith (fun pt V ↦ vanishCheck f a b pt V) Γ Vs).length := by
      rw [List.length_zipWith, ← hlen, min_self]; exact i.2
    have := hv _ (List.getElem_mem hi)
    rw [List.getElem_zipWith] at this
    exact vanishCheck_sound this

section Order

variable {K : Type*} [Field K] {f : K[X]} {g : ℕ} {Γ : EDiv K}

/-- **Exact order from the prime divisors.** -/
theorem exact_order (hf : f.natDegree = 2 * g + 1) (hon : OnCurve f Γ)
    (hnd : (Γ.map Prod.fst).Nodup) {m : ℕ} (hm : PrincipalMul f g Γ m)
    (hdiv : ∀ r, r.Prime → r ∣ m → ¬ PrincipalMul f g Γ (m / r)) :
    ∀ m', 1 ≤ m' → m' < m → ¬ PrincipalMul f g Γ m' := by
  intro m' h1 h2 h3
  have hg := PrincipalMul.gcd hf hon hnd h3 hm
  set d := Nat.gcd m' m
  have hd1 : 1 ≤ d := Nat.gcd_pos_of_pos_left _ h1
  have hdm : d ∣ m := Nat.gcd_dvd_right _ _
  have hdlt : d < m := lt_of_le_of_lt (Nat.gcd_le_left _ h1) h2
  obtain ⟨k, hk⟩ := hdm
  have hk1 : k ≠ 1 := by rintro rfl; omega
  have hk0 : k ≠ 0 := by rintro rfl; omega
  obtain ⟨r, hr, hrk⟩ := Nat.exists_prime_and_dvd hk1
  apply hdiv r hr (hk ▸ Dvd.dvd.mul_left hrk d)
  refine hg.of_dvd hf hon ?_
  obtain ⟨k', rfl⟩ := hrk
  rw [hk, show d * (r * k') / r = d * k' by
    rw [show d * (r * k') = r * (d * k') by ring, Nat.mul_div_cancel_left _ hr.pos]]
  exact dvd_mul_right _ _

/-- A double point is never a principal divisor by itself (`g ≥ 1`). -/
theorem not_principal_double {x₀ y₀ : K} (hg : 1 ≤ g) (h2y : IsUnit (2 * y₀)) :
    ¬ PrincipalMul f g [(x₀, y₀, 2)] 1 := by
  rintro ⟨ψ, hψ0, hψp, hψv⟩
  simp only [edeg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    one_mul] at hψp
  have hb : ψ.2 = 0 := hψp.2.resolve_right (by omega)
  have hv := hψv (x₀, y₀, 1 * 2) (by simp [escale])
  simp only [one_mul] at hv
  obtain ⟨V, hV, hj⟩ := hv
  rw [jet, hb, zero_comp, zero_mul, add_zero] at hj
  have ha : (X - C x₀) ^ 2 ∣ ψ.1 := dvd_of_comp hj
  have hdeg : ψ.1.natDegree ≤ 1 := by have := hψp.1; omega
  have ha0 : ψ.1 = 0 := by
    by_contra h0
    have := natDegree_le_of_dvd ha h0
    rw [natDegree_pow, natDegree_X_sub_C] at this
    omega
  exact hψ0 (Prod.ext ha0 hb)

end Order

end Jac
