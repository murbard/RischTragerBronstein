import RischTragerBronstein.Algebraic.SupResidual
import RischTragerBronstein.Algebraic.SupDescend

/-!
# Prime-to-`p` torsion of superelliptic Jacobians is detected modulo `p`

* `principal_of_vanish` (over a perfect field): if `ψ` of pole order `≤ (n−1)(deg Γ + g) + g`
  vanishes on `σᵏΓ` (`k ≠ 0`) and on all `σᵏPᵢ`, then `Γ − (deg Γ)∞` is principal;
* `ell_power_function`: the auxiliary function `ψ^ℓ Ξ / ∏(x − α_q)^{ℓ m_q}` of the `ℓ`-th power step;
* `torsion_descends_N`: over a Henselian DVR, a divisor class of order prime to the residue
  characteristic that is trivial modulo `ϖ` is trivial.
-/

open Polynomial IntermediateField Differential Differential.SuperData

namespace Sup

section Field

variable {F : Type*} [Field F] [PerfectField F]

open Classical in
/-- **Principality from a function vanishing on the conjugates.** -/
theorem principal_of_vanish (f : F[X]) {n : ℕ} (hn : 0 < n) (hsq : Squarefree f)
    (hd : 0 < f.natDegree) (hcop : Nat.Coprime n f.natDegree) (hnF : (n : F) ≠ 0)
    (ζ : F) (hζ : IsPrimitiveRoot ζ n)
    {g r : ℕ} (x y : Fin g → F) (hx : Function.Injective x) (hy : ∀ i, y i ≠ 0)
    (hyf : ∀ i, y i ^ n = f.eval (x i))
    (α β : Fin r → F) (mq : Fin r → ℕ) (hP : Function.Injective fun q ↦ (α q, β q))
    (hβ : ∀ q, β q ≠ 0) (hβf : ∀ q, β q ^ n = f.eval (α q)) (hαx : ∀ q i, α q ≠ x i)
    (ψ : F[X][X]) (hψ0 : ψ ≠ 0)
    (hψs : ∀ j a, (ψ.coeff j).coeff a ≠ 0 → j < n ∧
      n * a + f.natDegree * j ≤ (n - 1) * (∑ q, mq q + g) + g)
    (hψΓ : ∀ q k, k < n → VanishAtN f n ψ (α q) (ζ ^ k * β q)
      (∑ q', if α q' = α q ∧ ¬ β q' = ζ ^ k * β q then mq q' else 0))
    (hψE : ∀ i k, k < n → VanishAtN f n ψ (x i) (ζ ^ k * y i) 1) :
    ∃ γ : F[X][X], γ ≠ 0 ∧
      (∀ j a, (γ.coeff j).coeff a ≠ 0 → j < n ∧ n * a + f.natDegree * j ≤ ∑ q, mq q) ∧
      ∀ q, VanishAtN f n γ (α q) (β q) (mq q) := by
  set S := stdSuper F f n hn hsq hd hnF with hS
  set Kb := AlgebraicClosure F
  set ι := algebraMap F Kb with hι_def
  have hιi : Function.Injective ι := ι.injective
  have hcopS : Nat.Coprime S.n S.p.natDegree := hcop
  have hpt : ∀ c d : F, d ^ n = f.eval c → (ι d) ^ S.n = (S.p.map ι).eval (ι c) :=
    fun c d h ↦ by
      show (ι d) ^ n = (f.map ι).eval (ι c)
      rw [← map_pow, h, eval_map, eval₂_hom]
  have hpow : ∀ k (c d : F), d ^ n = f.eval c → (ζ ^ k * d) ^ n = f.eval c := fun k c d h ↦ by
    rw [mul_pow, ← pow_mul, mul_comm k, pow_mul, hζ.pow_eq_one, one_pow, one_mul, h]
  have hne : ∀ k (d : F), d ≠ 0 → ι (ζ ^ k * d) ≠ 0 := fun k d hd ↦
    (map_ne_zero_iff _ hιi).mpr (mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hn.ne')) hd)
  have hζK : IsPrimitiveRoot (ι ζ) S.n := hζ.map_of_injective hιi
  have hψW : ∀ i, S.n ≤ i → ψ.coeff i = 0 := by
    intro i hi
    by_contra h0
    obtain ⟨a, ha⟩ : ∃ a, (ψ.coeff i).coeff a ≠ 0 := by
      by_contra h1; push_neg at h1; exact h0 (Polynomial.ext h1)
    have := (hψs i a ha).1
    change n ≤ i at hi
    omega
  have hΨ0 : S.elemW ψ ≠ 0 := S.elemW_ne_zero ψ hψ0 hψW
  set U : F[X] := ∏ i, (X - Polynomial.C (x i)) with hU_def
  set Wb : F[X] := ∏ q, (X - Polynomial.C (α q)) ^ mq q with hWb_def
  have hU : U ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ X_sub_C_ne_zero _
  have hWb : Wb ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
  have hpU := S.polyX_ne_zero hU
  have hpW := S.polyX_ne_zero hWb
  have hUe : U = ∏ i, (X - Polynomial.C (x i)) ^ (fun _ : Fin g ↦ 1) i := by simp [U]
  have hptinj : Function.Injective fun q ↦ (ι (α q), ι (β q)) := fun q q' h ↦
    hP (Prod.ext (hιi (Prod.ext_iff.mp h).1) (hιi (Prod.ext_iff.mp h).2))
  have hover : ∀ (c d : F), d ≠ 0 → d ^ n = f.eval c → ∀ b : Kb,
      b ^ S.n = (S.p.map ι).eval (ι c) → ∃ k < n, b = ι (ζ ^ k * d) := by
    intro c d hd hv b hb
    obtain ⟨k, hk, hbk⟩ := S.root_point (ι ζ) hζK (ι d) b ((map_ne_zero_iff _ hιi).mpr hd)
      (by rw [hb, hpt _ _ hv])
    exact ⟨k, hk, by rw [hbk, map_mul, map_pow]⟩
  -- lower bounds for the orders of `ψ`
  have hlow : ∀ a b : Kb, b ^ S.n = (S.p.map ι).eval a →
      ((∑ q, if ι (α q) = a ∧ ¬ ι (β q) = b then mq q else 0 : ℕ) : ℤ) ≤
        S.ordAt Kb (S.elemW ψ) a b := by
    intro a b hv
    by_cases hA : ∃ q, ι (α q) = a
    · obtain ⟨q, rfl⟩ := hA
      obtain ⟨k, hk, rfl⟩ := hover _ _ (hβ q) (hβf q) b hv
      have e : (∑ q', if ι (α q') = ι (α q) ∧ ¬ ι (β q') = ι (ζ ^ k * β q) then mq q' else 0) =
          ∑ q', if α q' = α q ∧ ¬ β q' = ζ ^ k * β q then mq q' else 0 :=
        Finset.sum_congr rfl fun q' _ ↦ by simp only [hιi.eq_iff]
      rw [e]
      exact (S.le_ordAt_iff_vanish ψ hψW hΨ0 _ _ (hne k _ (hβ q)) hv _).mpr ((hψΓ q k hk).mapR ι)
    · push_neg at hA
      rw [Finset.sum_eq_zero fun q _ ↦ if_neg fun h ↦ hA q h.1]
      exact_mod_cast S.elemW_integral (K := Kb) ψ a b hv
  -- `Ψ₃ = ψ / ∏(x − xᵢ)`
  set Ψ₃ := S.elemW ψ * (S.polyX U)⁻¹ with hΨ₃_def
  have hΨ₃0 : Ψ₃ ≠ 0 := mul_ne_zero hΨ0 (inv_ne_zero hpU)
  have hΨ₃o : ∀ a b : Kb, b ^ S.n = (S.p.map ι).eval a →
      S.ordAt Kb Ψ₃ a b = S.ordAt Kb (S.elemW ψ) a b - S.ordAt Kb (S.polyX U) a b := by
    intro a b hv
    rw [hΨ₃_def, S.ordAt_mul hv hΨ0 (inv_ne_zero hpU), S.ordAt_inv hv]; ring
  have hΨ₃low : ∀ a b : Kb, b ^ S.n = (S.p.map ι).eval a →
      ((∑ q, if ι (α q) = a ∧ ¬ ι (β q) = b then mq q else 0 : ℕ) : ℤ) ≤ S.ordAt Kb Ψ₃ a b := by
    intro a b hv
    rw [hΨ₃o a b hv]
    by_cases hB : ∃ i, a = ι (x i)
    · obtain ⟨i, rfl⟩ := hB
      obtain ⟨k, hk, rfl⟩ := hover _ _ (hy i) (hyf i) b hv
      have h1 := (S.le_ordAt_iff_vanish ψ hψW hΨ0 _ _ (hne k _ (hy i)) hv 1).mpr
        ((hψE i k hk).mapR ι)
      rw [hUe, S.ordAt_polyX_prod_at x hx _ i _ hv (hne k _ (hy i)),
        Finset.sum_eq_zero fun q _ ↦ if_neg fun h ↦ hαx q i (hιi h.1)]
      push_cast at h1 ⊢
      linarith
    · push_neg at hB
      rw [hUe, S.ordAt_polyX_prod_off x _ _ _ hv hB, sub_zero]
      exact hlow a b hv
  have hΨ₃int : S.IsIntegralS Kb Ψ₃ := fun a b hv ↦ le_trans (by positivity) (hΨ₃low a b hv)
  obtain ⟨φ, hφ⟩ := S.ordInf_hom (K := Kb) hcopS
  have hdegU : U.natDegree = g := by
    rw [hU_def, natDegree_prod _ _ fun q _ ↦ X_sub_C_ne_zero _]
    simp
  have hdegW : Wb.natDegree = ∑ q, mq q := by
    rw [hWb_def, natDegree_prod _ _ fun q _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)]
    simp [natDegree_pow]
  have hΨ₃inf : -(((n - 1) * ∑ q, mq q : ℕ) : ℤ) ≤ S.ordInf Kb Ψ₃ := by
    have h1 := S.elemW_ordInf (K := Kb) hcopS ψ _ hψs hΨ0
    rw [hΨ₃_def, S.ordInf_mul hcopS hΨ0 (inv_ne_zero hpU), hφ (S.polyX U)⁻¹, order_hom_inv, ← hφ,
      S.ordInf_polyX hcopS _ hU, hdegU]
    have hn1 : ((n - 1 : ℕ) : ℤ) = n - 1 := by
      push_cast [Nat.cast_sub (show 1 ≤ n by omega)]; ring
    push_cast [hn1] at h1 ⊢
    have e : ((S.n : ℕ) : ℤ) = (n : ℤ) := rfl
    rw [e]
    linarith
  -- the exact divisor of `Ψ₃`
  have hexact := S.exact_fiber_divisor hcopS (ι ζ) hζK (fun q ↦ ι (α q)) (fun q ↦ ι (β q)) mq
    (fun q ↦ (map_ne_zero_iff _ hιi).mpr (hβ q)) (fun q ↦ hpt _ _ (hβf q)) Ψ₃ hΨ₃0 hΨ₃int
    hΨ₃low hΨ₃inf
  -- `γ = ∏(x − α_q)^{m_q} / Ψ₃`
  set γF := S.polyX Wb * Ψ₃⁻¹ with hγF_def
  have hγF0 : γF ≠ 0 := mul_ne_zero hpW (inv_ne_zero hΨ₃0)
  have hγFo : ∀ a b : Kb, b ^ S.n = (S.p.map ι).eval a →
      S.ordAt Kb γF a b = S.ordAt Kb (S.polyX Wb) a b - S.ordAt Kb Ψ₃ a b := by
    intro a b hv
    rw [hγF_def, S.ordAt_mul hv hpW (inv_ne_zero hΨ₃0), S.ordAt_inv hv]; ring
  have hWo : ∀ a b : Kb, b ^ S.n = (S.p.map ι).eval a → b ≠ 0 →
      S.ordAt Kb (S.polyX Wb) a b = ((∑ q, if ι (α q) = a then mq q else 0 : ℕ) : ℤ) := by
    intro a b hv hb
    rw [hWb_def, S.ordAt_polyX_prod _ _ _ _ _ hv]
    push_cast
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [S.ordAt_polyX_lin _ _ _ hv, if_neg hb]
    by_cases h : a = ι (α q)
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  have hγFeq : ∀ a b : Kb, b ^ S.n = (S.p.map ι).eval a → b ≠ 0 →
      S.ordAt Kb γF a b = ((∑ q, if ι (α q) = a ∧ ι (β q) = b then mq q else 0 : ℕ) : ℤ) := by
    intro a b hv hb
    rw [hγFo a b hv, hWo a b hv hb, hexact.1 a b hv,
      sum_ite_split Finset.univ (fun q ↦ ι (α q) = a) (fun q ↦ ι (β q) = b) mq]
    push_cast; ring
  have hγFq : ∀ q, S.ordAt Kb γF (ι (α q)) (ι (β q)) = mq q := by
    intro q
    rw [hγFeq _ _ (hpt _ _ (hβf q)) ((map_ne_zero_iff _ hιi).mpr (hβ q)),
      Finset.sum_eq_single q (fun q' _ hq' ↦ if_neg fun h ↦ hq' (hptinj (Prod.ext h.1 h.2)))
        (fun h ↦ absurd (Finset.mem_univ q) h), if_pos ⟨rfl, rfl⟩]
  have hγFint : S.IsIntegralS Kb γF := by
    intro a b hv
    by_cases hb : b = 0
    · have hα' : ∀ q, a ≠ ι (α q) := by
        intro q ha
        have : (S.p.map ι).eval a = 0 := by rw [← hv, hb, zero_pow S.hn.ne']
        rw [ha, ← hpt _ _ (hβf q)] at this
        exact pow_ne_zero _ ((map_ne_zero_iff _ hιi).mpr (hβ q)) this
      rw [hγFo a b hv, hexact.1 a b hv, Finset.sum_eq_zero fun q _ ↦ if_neg fun h ↦ hα' q h.1.symm,
        hWb_def, S.ordAt_polyX_prod_off α _ _ _ hv hα']
      simp
    · rw [hγFeq a b hv hb]; positivity
  have hγFinf : -((∑ q, mq q : ℕ) : ℤ) ≤ S.ordInf Kb γF := by
    have hinf3 : S.ordInf Kb Ψ₃ = -(((n - 1) * ∑ q, mq q : ℕ) : ℤ) := hexact.2
    rw [hγF_def, S.ordInf_mul hcopS hpW (inv_ne_zero hΨ₃0), hφ Ψ₃⁻¹, order_hom_inv, ← hφ, hinf3,
      S.ordInf_polyX hcopS _ hWb, hdegW]
    have e : ((S.n : ℕ) : ℤ) = (n : ℤ) := rfl
    rw [e]
    have hn1 : ((n - 1 : ℕ) : ℤ) = n - 1 := by
      push_cast [Nat.cast_sub (show 1 ≤ n by omega)]; ring
    push_cast [hn1]
    linarith
  obtain ⟨γ, hγγ, hγ0, hγs⟩ := S.elem_repr (K := Kb) hcopS γF hγF0 hγFint _ hγFinf
  have hγW : ∀ i, S.n ≤ i → γ.coeff i = 0 := by
    intro i hi
    by_contra h0
    obtain ⟨a, ha⟩ : ∃ a, (γ.coeff i).coeff a ≠ 0 := by
      by_contra h1; push_neg at h1; exact h0 (Polynomial.ext h1)
    have := (hγs i a ha).1
    omega
  refine ⟨γ, hγ0, hγs, fun q ↦ ?_⟩
  have hv := hpt _ _ (hβf q)
  have hβK : ι (β q) ≠ 0 := (map_ne_zero_iff _ hιi).mpr (hβ q)
  have h1 := (S.le_ordAt_iff_vanish γ hγW (by rw [hγγ]; exact hγF0) _ _ hβK hv (mq q)).mp
    (by rw [hγγ, hγFq])
  obtain ⟨V, hV⟩ := exists_branchN f hn (IsUnit.mk0 _ (mul_ne_zero hnF (pow_ne_zero _ (hβ q))))
    (hβf q) (mq q)
  exact vanishAtN_of_map ι hιi hn (hV.mono (Nat.le_succ _)) (S.unit_branch _ hβK) h1

open Classical in
/-- **The `ℓ`-th power step.** From `ψ` (vanishing on `σᵏΓ`, `σᵏE`, `k ≠ 0`, and at points `Qᵢ`)
and `Ξ` (vanishing on `ℓΓ`, of pole order `≤ ℓ deg Γ`), the function `ψ^ℓ Ξ / ∏(x − α_q)^{ℓ m_q}`
has pole order `≤ ℓ n g` and vanishes to order `ℓ` at the `Qᵢ` and the `σᵏPᵢ`. -/
theorem ell_power_function (f : F[X]) {n : ℕ} (hn : 0 < n) (hsq : Squarefree f)
    (hd : 0 < f.natDegree) (hcop : Nat.Coprime n f.natDegree) (hnF : (n : F) ≠ 0)
    (ζ : F) (hζ : IsPrimitiveRoot ζ n)
    {g r : ℕ} (x y : Fin g → F) (hy : ∀ i, y i ≠ 0) (hyf : ∀ i, y i ^ n = f.eval (x i))
    (α β : Fin r → F) (mq : Fin r → ℕ) (hP : Function.Injective fun q ↦ (α q, β q))
    (hβ : ∀ q, β q ≠ 0)
    (hβf : ∀ q, β q ^ n = f.eval (α q)) (hαx : ∀ q i, α q ≠ x i)
    (z Y : Fin g → F) (hY : ∀ i, Y i ≠ 0) (hYf : ∀ i, Y i ^ n = f.eval (z i))
    (hαz : ∀ q i, α q ≠ z i)
    (ψ : F[X][X]) (hψ0 : ψ ≠ 0)
    (hψs : ∀ j a, (ψ.coeff j).coeff a ≠ 0 → j < n ∧
      n * a + f.natDegree * j ≤ (n - 1) * (∑ q, mq q + g) + g)
    (hψΓ : ∀ q k, k < n → VanishAtN f n ψ (α q) (ζ ^ k * β q)
      (∑ q', if α q' = α q ∧ ¬ β q' = ζ ^ k * β q then mq q' else 0))
    (hψE : ∀ i k, 1 ≤ k → k < n → VanishAtN f n ψ (x i) (ζ ^ k * y i) 1)
    (hψQ : ∀ i, evalW ψ (z i) (Y i) = 0)
    (ℓ : ℕ) (Ξ : F[X][X]) (hΞ0 : Ξ ≠ 0)
    (hΞs : ∀ j a, (Ξ.coeff j).coeff a ≠ 0 → j < n ∧ n * a + f.natDegree * j ≤ ℓ * ∑ q, mq q)
    (hΞv : ∀ q, VanishAtN f n Ξ (α q) (β q) (ℓ * mq q)) :
    ∃ W : F[X][X], W ≠ 0 ∧
      (∀ j a, (W.coeff j).coeff a ≠ 0 → j < n ∧ n * a + f.natDegree * j ≤ ℓ * n * g) ∧
      (∀ i, VanishAtN f n W (z i) (Y i) ℓ) ∧
      ∀ i k, 1 ≤ k → k < n → VanishAtN f n W (x i) (ζ ^ k * y i) ℓ := by
  set S := stdSuper F f n hn hsq hd hnF with hS
  set Kb := AlgebraicClosure F
  set ι := algebraMap F Kb with hι_def
  have hιi : Function.Injective ι := ι.injective
  have hcopS : Nat.Coprime S.n S.p.natDegree := hcop
  have hpt : ∀ c d : F, d ^ n = f.eval c → (ι d) ^ S.n = (S.p.map ι).eval (ι c) :=
    fun c d h ↦ by
      show (ι d) ^ n = (f.map ι).eval (ι c)
      rw [← map_pow, h, eval_map, eval₂_hom]
  have hpow : ∀ k (c d : F), d ^ n = f.eval c → (ζ ^ k * d) ^ n = f.eval c := fun k c d h ↦ by
    rw [mul_pow, ← pow_mul, mul_comm k, pow_mul, hζ.pow_eq_one, one_pow, one_mul, h]
  have hne : ∀ k (d : F), d ≠ 0 → ι (ζ ^ k * d) ≠ 0 := fun k d hd ↦
    (map_ne_zero_iff _ hιi).mpr (mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hn.ne')) hd)
  have hζK : IsPrimitiveRoot (ι ζ) S.n := hζ.map_of_injective hιi
  have hcoefW : ∀ (W : F[X][X]) (M : ℕ), (∀ j a, (W.coeff j).coeff a ≠ 0 → j < n ∧
      n * a + f.natDegree * j ≤ M) → ∀ i, S.n ≤ i → W.coeff i = 0 := by
    intro W M h i hi
    by_contra h0
    obtain ⟨a, ha⟩ : ∃ a, (W.coeff i).coeff a ≠ 0 := by
      by_contra h1; push_neg at h1; exact h0 (Polynomial.ext h1)
    have := (h i a ha).1
    change n ≤ i at hi
    omega
  have hψW := hcoefW ψ _ hψs
  have hΞW := hcoefW Ξ _ hΞs
  have hΨ0 : S.elemW ψ ≠ 0 := S.elemW_ne_zero ψ hψ0 hψW
  have hΞ'0 : S.elemW Ξ ≠ 0 := S.elemW_ne_zero Ξ hΞ0 hΞW
  set Wℓ : F[X] := ∏ q, (X - Polynomial.C (α q)) ^ (ℓ * mq q) with hWℓ_def
  have hWℓ : Wℓ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
  have hpW := S.polyX_ne_zero hWℓ
  have hover : ∀ (c d : F), d ≠ 0 → d ^ n = f.eval c → ∀ b : Kb,
      b ^ S.n = (S.p.map ι).eval (ι c) → ∃ k < n, b = ι (ζ ^ k * d) := by
    intro c d hd hv b hb
    obtain ⟨k, hk, hbk⟩ := S.root_point (ι ζ) hζK (ι d) b ((map_ne_zero_iff _ hιi).mpr hd)
      (by rw [hb, hpt _ _ hv])
    exact ⟨k, hk, by rw [hbk, map_mul, map_pow]⟩
  set Φ := S.elemW ψ ^ ℓ * S.elemW Ξ * (S.polyX Wℓ)⁻¹ with hΦ_def
  have hΦ0 : Φ ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ hΨ0) hΞ'0) (inv_ne_zero hpW)
  have hΦo : ∀ a b : Kb, b ^ S.n = (S.p.map ι).eval a →
      S.ordAt Kb Φ a b = ℓ * S.ordAt Kb (S.elemW ψ) a b + S.ordAt Kb (S.elemW Ξ) a b -
        S.ordAt Kb (S.polyX Wℓ) a b := by
    intro a b hv
    rw [hΦ_def, S.ordAt_mul hv (mul_ne_zero (pow_ne_zero _ hΨ0) hΞ'0) (inv_ne_zero hpW),
      S.ordAt_mul hv (pow_ne_zero _ hΨ0) hΞ'0, S.ordAt_pow hv, S.ordAt_inv hv]
    ring
  have hWoff : ∀ a b : Kb, b ^ S.n = (S.p.map ι).eval a → (∀ q, a ≠ ι (α q)) →
      S.ordAt Kb (S.polyX Wℓ) a b = 0 := fun a b hv ha ↦
    S.ordAt_polyX_prod_off α _ _ _ hv ha
  have hptinj : Function.Injective fun q ↦ (ι (α q), ι (β q)) := fun q q' h ↦
    hP (Prod.ext (hιi (Prod.ext_iff.mp h).1) (hιi (Prod.ext_iff.mp h).2))
  have hlow : ∀ a b : Kb, b ^ S.n = (S.p.map ι).eval a →
      ((∑ q, if ι (α q) = a ∧ ¬ ι (β q) = b then mq q else 0 : ℕ) : ℤ) ≤
        S.ordAt Kb (S.elemW ψ) a b := by
    intro a b hv
    by_cases hA : ∃ q, ι (α q) = a
    · obtain ⟨q, rfl⟩ := hA
      obtain ⟨k, hk, rfl⟩ := hover _ _ (hβ q) (hβf q) b hv
      have e : (∑ q', if ι (α q') = ι (α q) ∧ ¬ ι (β q') = ι (ζ ^ k * β q) then mq q' else 0) =
          ∑ q', if α q' = α q ∧ ¬ β q' = ζ ^ k * β q then mq q' else 0 :=
        Finset.sum_congr rfl fun q' _ ↦ by simp only [hιi.eq_iff]
      rw [e]
      exact (S.le_ordAt_iff_vanish ψ hψW hΨ0 _ _ (hne k _ (hβ q)) hv _).mpr ((hψΓ q k hk).mapR ι)
    · push_neg at hA
      rw [Finset.sum_eq_zero fun q _ ↦ if_neg fun h ↦ hA q h.1]
      exact_mod_cast S.elemW_integral (K := Kb) ψ a b hv
  have hΞlow : ∀ a b : Kb, b ^ S.n = (S.p.map ι).eval a →
      ((ℓ * ∑ q, if ι (α q) = a ∧ ι (β q) = b then mq q else 0 : ℕ) : ℤ) ≤
        S.ordAt Kb (S.elemW Ξ) a b := by
    intro a b hv
    by_cases hA : ∃ q, (a, b) = (ι (α q), ι (β q))
    · obtain ⟨q0, hq0⟩ := hA
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hq0
      rw [Finset.sum_eq_single q0 (fun q _ hq ↦ if_neg fun h ↦ hq (hptinj (Prod.ext h.1 h.2)))
        (fun h ↦ absurd (Finset.mem_univ q0) h), if_pos ⟨rfl, rfl⟩]
      exact (S.le_ordAt_iff_vanish Ξ hΞW hΞ'0 _ _ ((map_ne_zero_iff _ hιi).mpr (hβ q0))
        (hpt _ _ (hβf q0)) (ℓ * mq q0)).mpr ((hΞv q0).mapR ι)
    · push_neg at hA
      rw [Finset.sum_eq_zero fun q _ ↦ if_neg fun h ↦ hA q (by rw [h.1, h.2]), mul_zero]
      exact_mod_cast S.elemW_integral (K := Kb) Ξ a b hv
  have hWo : ∀ a b : Kb, b ^ S.n = (S.p.map ι).eval a → b ≠ 0 →
      S.ordAt Kb (S.polyX Wℓ) a b = ((ℓ * ∑ q, if ι (α q) = a then mq q else 0 : ℕ) : ℤ) := by
    intro a b hv hb
    rw [hWℓ_def, S.ordAt_polyX_prod _ _ _ _ _ hv, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [S.ordAt_polyX_lin _ _ _ hv, if_neg hb]
    by_cases h : a = ι (α q)
    · rw [if_pos h, if_pos h.symm]; push_cast; ring
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  have hΦint : S.IsIntegralS Kb Φ := by
    intro a b hv
    rw [hΦo a b hv]
    have h0 := hlow a b hv
    have h0' := hΞlow a b hv
    have hℓ0 : (0 : ℤ) ≤ ℓ := by positivity
    by_cases hb : b = 0
    · have hα' : ∀ q, a ≠ ι (α q) := by
        intro q ha
        have : (S.p.map ι).eval a = 0 := by rw [← hv, hb, zero_pow S.hn.ne']
        rw [ha, ← hpt _ _ (hβf q)] at this
        exact pow_ne_zero _ ((map_ne_zero_iff _ hιi).mpr (hβ q)) this
      rw [hWoff a b hv hα']
      have h1 := S.elemW_integral (K := Kb) ψ a b hv
      have h2 := S.elemW_integral (K := Kb) Ξ a b hv
      nlinarith
    · rw [hWo a b hv hb, sum_ite_split Finset.univ (fun q ↦ ι (α q) = a) (fun q ↦ ι (β q) = b) mq]
      push_cast at h0 h0' ⊢
      nlinarith
  obtain ⟨φ, hφ⟩ := S.ordInf_hom (K := Kb) hcopS
  have hdegW : Wℓ.natDegree = ℓ * ∑ q, mq q := by
    rw [hWℓ_def, natDegree_prod _ _ fun q _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)]
    simp [natDegree_pow, Finset.mul_sum]
  have hΦinf : -((ℓ * n * g : ℕ) : ℤ) ≤ S.ordInf Kb Φ := by
    have h1 := S.elemW_ordInf (K := Kb) hcopS ψ _ hψs hΨ0
    have h2 := S.elemW_ordInf (K := Kb) hcopS Ξ _ hΞs hΞ'0
    rw [hΦ_def, S.ordInf_mul hcopS (mul_ne_zero (pow_ne_zero _ hΨ0) hΞ'0) (inv_ne_zero hpW),
      S.ordInf_mul hcopS (pow_ne_zero _ hΨ0) hΞ'0, hφ (S.elemW ψ ^ ℓ), order_hom_pow, ← hφ,
      hφ (S.polyX Wℓ)⁻¹, order_hom_inv, ← hφ, S.ordInf_polyX hcopS _ hWℓ, hdegW]
    have e : ((S.n : ℕ) : ℤ) = (n : ℤ) := rfl
    rw [e]
    have hn1 : ((n - 1 : ℕ) : ℤ) = n - 1 := by
      push_cast [Nat.cast_sub (show 1 ≤ n by omega)]; ring
    push_cast [hn1] at h1 h2 ⊢
    have hℓ0 : (0 : ℤ) ≤ ℓ := by positivity
    nlinarith
  -- orders at the `Qᵢ` and the `σᵏPᵢ`
  have hΦQ : ∀ i, (ℓ : ℤ) ≤ S.ordAt Kb Φ (ι (z i)) (ι (Y i)) := by
    intro i
    have hv := hpt _ _ (hYf i)
    have hYK : ι (Y i) ≠ 0 := (map_ne_zero_iff _ hιi).mpr (hY i)
    have h1 := (S.le_ordAt_iff_vanish ψ hψW hΨ0 _ _ hYK hv 1).mpr
      ((vanish1_of_evalW (hYf i) (hψQ i)).mapR ι)
    rw [hΦo _ _ hv, hWoff _ _ hv fun q h ↦ hαz q i (hιi h).symm]
    have h0' := S.elemW_integral (K := Kb) Ξ _ _ hv
    push_cast at h1
    nlinarith
  have hΦE : ∀ i k, 1 ≤ k → k < n → (ℓ : ℤ) ≤ S.ordAt Kb Φ (ι (x i)) (ι (ζ ^ k * y i)) := by
    intro i k hk1 hk
    have hv := hpt _ _ (hpow k _ _ (hyf i))
    have h1 := (S.le_ordAt_iff_vanish ψ hψW hΨ0 _ _ (hne k _ (hy i)) hv 1).mpr
      ((hψE i k hk1 hk).mapR ι)
    rw [hΦo _ _ hv, hWoff _ _ hv fun q h ↦ hαx q i (hιi h).symm]
    have h0' := S.elemW_integral (K := Kb) Ξ _ _ hv
    push_cast at h1
    nlinarith
  obtain ⟨W, hWΦ, hW0, hWs⟩ := S.elem_repr (K := Kb) hcopS Φ hΦ0 hΦint _ hΦinf
  have hWW := hcoefW W _ hWs
  have hW0' : S.elemW W ≠ 0 := by rw [hWΦ]; exact hΦ0
  refine ⟨W, hW0, hWs, fun i ↦ ?_, fun i k hk1 hk ↦ ?_⟩
  · have hv := hpt _ _ (hYf i)
    have hYK : ι (Y i) ≠ 0 := (map_ne_zero_iff _ hιi).mpr (hY i)
    have h1 := (S.le_ordAt_iff_vanish W hWW hW0' _ _ hYK hv ℓ).mp (by rw [hWΦ]; exact hΦQ i)
    obtain ⟨V, hV⟩ := exists_branchN f hn (IsUnit.mk0 _ (mul_ne_zero hnF (pow_ne_zero _ (hY i))))
      (hYf i) ℓ
    exact vanishAtN_of_map ι hιi hn (hV.mono (Nat.le_succ _)) (S.unit_branch _ hYK) h1
  · have hv := hpt _ _ (hpow k _ _ (hyf i))
    have h1 := (S.le_ordAt_iff_vanish W hWW hW0' _ _ (hne k _ (hy i)) hv ℓ).mp
      (by rw [hWΦ]; exact hΦE i k hk1 hk)
    have hyk : ζ ^ k * y i ≠ 0 := mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hn.ne')) (hy i)
    obtain ⟨V, hV⟩ := exists_branchN f hn (IsUnit.mk0 _ (mul_ne_zero hnF (pow_ne_zero _ hyk)))
      (hpow k _ _ (hyf i)) ℓ
    exact vanishAtN_of_map ι hιi hn (hV.mono (Nat.le_succ _)) (S.unit_branch _ (hne k _ (hy i))) h1

end Field

section DVR

variable {O K : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [HenselianRing O (IsLocalRing.maximalIdeal O)] [Field K] [Algebra O K] [IsFractionRing O K]
  [PerfectField K] [PerfectField (IsLocalRing.ResidueField O)]

local notation "𝕜" => IsLocalRing.ResidueField O
local notation "ρ" => IsLocalRing.residue O
local notation "ι" => algebraMap O K

/-- **Prime-to-`p` torsion is detected modulo `p`** (superelliptic curves `yⁿ = f(x)`).

Let `O` be a Henselian discrete valuation ring with fraction field `K` and perfect residue field
`𝕜`, `n` a unit of `O`, `ζ ∈ O` a primitive `n`-th root of unity (also modulo `ϖ`), `f ∈ O[X]` with
unit leading coefficient, `gcd(n, deg f) = 1`, squarefree over `K` and modulo `ϖ`. Let
`E = ∑ Pᵢ` (`g` points, `(n − 1)(deg f − 1) ≤ 2g`) be non-special modulo `ϖ` and `Γ = ∑ m_q (α_q, β_q)`
with the `α_q`, `xᵢ` pairwise distinct modulo `ϖ` and `β_q`, `yᵢ` units. If

* modulo `ϖ` some non-zero `γ̄` of pole order `≤ deg Γ` vanishes on `Γ̄` (the reduction of the
  class of `Γ − (deg Γ)∞` is trivial), and
* over `K` some non-zero `Ξ` of pole order `≤ ℓ deg Γ` vanishes on `ℓΓ`, `ℓ` a unit of `O`
  (the class has order dividing `ℓ`),

then over `K` some non-zero `γ` of pole order `≤ deg Γ` vanishes on `Γ` (the class is trivial). -/
theorem torsion_descends_N {ϖ : O} (hϖ : Irreducible ϖ) (f : O[X]) {n : ℕ} (hn : 0 < n)
    (hlc : IsUnit f.leadingCoeff) (hd : 0 < f.natDegree) (hcop : Nat.Coprime n f.natDegree)
    (hsqk : Squarefree (f.map ρ)) (hsqK : Squarefree (f.map ι)) (hnu : IsUnit (n : O))
    (ζ : O) (hζ : IsPrimitiveRoot ζ n) (hζk : IsPrimitiveRoot (ρ ζ) n)
    {g r : ℕ} (hgen : (n - 1) * (f.natDegree - 1) ≤ 2 * g)
    (x y : Fin g → O) (hyu : ∀ i, IsUnit (y i)) (hyf : ∀ i, y i ^ n = f.eval (x i))
    (hx : ∀ i j, i ≠ j → IsUnit (x i - x j))
    (α β : Fin r → O) (mq : Fin r → ℕ) (hβu : ∀ q, IsUnit (β q))
    (hβf : ∀ q, β q ^ n = f.eval (α q)) (hα : ∀ q q', α q = α q' ∨ IsUnit (α q - α q'))
    (hβd : ∀ q q', q ≠ q' → α q = α q' → IsUnit (β q - β q'))
    (hαx : ∀ q i, IsUnit (α q - x i))
    (hNS : ∀ U : 𝕜[X][X], (∀ j a, (U.coeff j).coeff a ≠ 0 → j < n ∧
        n * a + f.natDegree * j ≤ n * g) →
      (∀ i k, 1 ≤ k → k < n → evalW U (ρ (x i)) (ρ ζ ^ k * ρ (y i)) = 0) →
      ∀ i, evalW U (ρ (x i)) (ρ (y i)) = 0)
    (γb : 𝕜[X][X]) (hγ0 : γb ≠ 0)
    (hγs : ∀ j a, (γb.coeff j).coeff a ≠ 0 → j < n ∧ n * a + f.natDegree * j ≤ ∑ q, mq q)
    (hγv : ∀ q, VanishAtN (f.map ρ) n γb (ρ (α q)) (ρ (β q)) (mq q))
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ : IsUnit (ℓ : O)) (Ξ : K[X][X]) (hΞ0 : Ξ ≠ 0)
    (hΞs : ∀ j a, (Ξ.coeff j).coeff a ≠ 0 → j < n ∧ n * a + f.natDegree * j ≤ ℓ * ∑ q, mq q)
    (hΞv : ∀ q, VanishAtN (f.map ι) n Ξ (ι (α q)) (ι (β q)) (ℓ * mq q)) :
    ∃ γ : K[X][X], γ ≠ 0 ∧
      (∀ j a, (γ.coeff j).coeff a ≠ 0 → j < n ∧ n * a + f.natDegree * j ≤ ∑ q, mq q) ∧
      ∀ q, VanishAtN (f.map ι) n γ (ι (α q)) (ι (β q)) (mq q) := by
  classical
  have hιi : Function.Injective ι := IsFractionRing.injective O K
  have hfK : (f.map ι).natDegree = f.natDegree := natDegree_map_eq_of_injective hιi f
  have hnK : (n : K) ≠ 0 := by
    rw [← map_natCast ι]; exact (map_ne_zero_iff _ hιi).mpr hnu.ne_zero
  have hevK : ∀ c d : O, d ^ n = f.eval c → ι d ^ n = (f.map ι).eval (ι c) := fun c d h ↦ by
    rw [← map_pow, h, eval_map, eval₂_hom]
  have hpowO : ∀ k (c d : O), d ^ n = f.eval c → (ζ ^ k * d) ^ n = f.eval c := fun k c d h ↦ by
    rw [mul_pow, ← pow_mul, mul_comm k, pow_mul, hζ.pow_eq_one, one_pow, one_mul, h]
  have hζu : IsUnit ζ := hζ.isUnit hn.ne'
  have hneK : ∀ d : O, IsUnit d → ι d ≠ 0 := fun d hd ↦ (map_ne_zero_iff _ hιi).mpr hd.ne_zero
  have hinjK : ∀ {m : ℕ} (v : Fin m → O), (∀ a b, a ≠ b → IsUnit (v a - v b)) →
      Function.Injective fun a ↦ ι (v a) := by
    intro m v hv a b hab
    by_contra hne
    have := (hv a b hne).ne_zero
    rw [← sub_eq_zero.mpr (hιi hab)] at this
    exact this rfl
  set M := (n - 1) * (∑ q, mq q + g) + g with hM_def
  -- S1: a function over `K` vanishing on `∑ m_q (F_q − P_q)` and on `σᵏE`, `k ≠ 0`
  set TK : Finset (K × K) := (Finset.univ ×ˢ Finset.range n).image
    (fun p : Fin r × ℕ ↦ (ι (α p.1), ι ζ ^ p.2 * ι (β p.1))) with hTK_def
  set needK : K × K → ℕ := fun Q ↦ ∑ q, if ι (α q) = Q.1 ∧ ¬ ι (β q) = Q.2 then mq q else 0
    with hneedK_def
  set ΓL : List (K × K × ℕ) :=
    (TK.toList.map fun Q ↦ (Q.1, Q.2, needK Q)) ++
    ((List.finRange g).flatMap fun i ↦ (List.range' 1 (n - 1)).map fun k ↦
      (ι (x i), ι (ζ ^ k * y i), 1)) with hΓL_def
  have hΓL : ∀ P ∈ ΓL, IsUnit ((n : K) * P.2.1 ^ (n - 1)) ∧ P.2.1 ^ n = (f.map ι).eval P.1 := by
    intro P hP
    simp only [ΓL, List.mem_append, List.mem_map, Finset.mem_toList, List.mem_flatMap,
      List.mem_finRange, true_and] at hP
    rcases hP with ⟨Q, hQ, rfl⟩ | ⟨i, k, -, rfl⟩
    · obtain ⟨⟨q, k⟩, -, rfl⟩ := Finset.mem_image.mp hQ
      simp only
      rw [← map_pow, ← map_mul]
      exact ⟨IsUnit.mk0 _ (mul_ne_zero hnK (pow_ne_zero _ (hneK _ ((hζu.pow k).mul (hβu q))))),
        hevK _ _ (hpowO k _ _ (hβf q))⟩
    · exact ⟨IsUnit.mk0 _ (mul_ne_zero hnK (pow_ne_zero _ (hneK _ ((hζu.pow k).mul (hyu i))))),
        hevK _ _ (hpowO k _ _ (hyf i))⟩
  have hsumL : (ΓL.map fun P ↦ P.2.2).sum = (n - 1) * (∑ q, mq q + g) := by
    have h1 : ((TK.toList.map fun Q ↦ (Q.1, Q.2, needK Q)).map fun P ↦ P.2.2).sum =
        (n - 1) * ∑ q, mq q := by
      rw [List.map_map]
      have : ((TK.toList.map ((fun P : K × K × ℕ ↦ P.2.2) ∘ fun Q ↦ (Q.1, Q.2, needK Q)))).sum =
          ∑ Q ∈ TK, needK Q := by
        rw [Finset.sum_map_toList]; rfl
      rw [this]
      exact Sup.sum_need_image hn (ι ζ) (hζ.map_of_injective hιi) (fun q ↦ ι (α q))
        (fun q ↦ ι (β q)) mq (fun q ↦ hneK _ (hβu q)) (fun q q' h ↦ by
          rw [hevK _ _ (hβf q), hevK _ _ (hβf q'), h])
    have h2 : (((List.finRange g).flatMap fun i ↦ (List.range' 1 (n - 1)).map fun k ↦
        (ι (x i), ι (ζ ^ k * y i), 1)).map fun P : K × K × ℕ ↦ P.2.2).sum = (n - 1) * g := by
      simp [List.flatMap_def, List.sum_flatten, List.map_flatten, List.sum_ofFn,
        ← List.ofFn_eq_map, Function.comp_def, mul_comm]
    rw [hΓL_def, List.map_append, List.sum_append, h1, h2, mul_add]
  have hcount : (ΓL.map fun P ↦ P.2.2).sum < (basisN n f.natDegree M).length := by
    have h := card_basisN n f.natDegree M hn hcop
    rw [hsumL]
    have hn1 : ((n - 1 : ℕ) : ℤ) = n - 1 := by
      push_cast [Nat.cast_sub (show 1 ≤ n by omega)]; ring
    have hd1 : ((f.natDegree - 1 : ℕ) : ℤ) = f.natDegree - 1 := by
      push_cast [Nat.cast_sub (show 1 ≤ f.natDegree by omega)]; ring
    have hg : (((n - 1) * (f.natDegree - 1) : ℕ) : ℤ) ≤ 2 * g := by exact_mod_cast hgen
    push_cast [hn1, hd1] at hg
    have : (((n - 1) * (∑ q, mq q + g) : ℕ) : ℤ) < (basisN n f.natDegree M).length := by
      rw [hM_def] at h
      push_cast [hn1] at h ⊢
      nlinarith
    exact_mod_cast this
  obtain ⟨ψK, hψK0, hψKs, hψKv⟩ := exists_vanishing_list (f.map ι) hn f.natDegree M ΓL hΓL hcount
  have hneedO : ∀ q k, needK (ι (α q), ι (ζ ^ k * β q)) =
      ∑ q', if α q' = α q ∧ ¬ β q' = ζ ^ k * β q then mq q' else 0 := fun q k ↦
    Finset.sum_congr rfl fun q' _ ↦ by simp only [hιi.eq_iff]
  have hmemΓ : ∀ q k, k < n →
      (ι (α q), ι (ζ ^ k * β q), needK (ι (α q), ι (ζ ^ k * β q))) ∈ ΓL := by
    intro q k hk
    refine List.mem_append_left _ (List.mem_map.mpr ⟨(ι (α q), ι (ζ ^ k * β q)),
      Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨(q, k), Finset.mem_product.mpr
        ⟨Finset.mem_univ _, Finset.mem_range.mpr hk⟩, by simp [map_mul, map_pow]⟩), rfl⟩)
  have hmemE : ∀ i k, 1 ≤ k → k < n → (ι (x i), ι (ζ ^ k * y i), 1) ∈ ΓL := by
    intro i k hk1 hk
    simp only [ΓL, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and,
      List.mem_range'_1]
    exact Or.inr ⟨i, k, ⟨hk1, by omega⟩, rfl⟩
  -- S2: descent to a primitive function over `O`
  have hdesc : ∀ (W : O[X][X]) (WK : K[X][X]) (c : K),
      W.map (mapRingHom ι) = Polynomial.C (Polynomial.C c) * WK →
      ∀ (a b : O) (m : ℕ), IsUnit b → b ^ n = f.eval a →
      VanishAtN (f.map ι) n WK (ι a) (ι b) m → VanishAtN f n W a b m := by
    intro W WK c hW a b m hb hv h
    obtain ⟨V, hV⟩ := exists_branchN f hn (hnu.mul (hb.pow _)) hv m
    exact vanishAtN_of_map ι hιi hn (hV.mono (Nat.le_succ _))
      (IsUnit.mk0 _ (mul_ne_zero hnK (pow_ne_zero _ (hneK _ hb)))) (by rw [hW]; exact h.C_mul c)
  have hsupp : ∀ (W : O[X][X]) (WK : K[X][X]) (c : K),
      W.map (mapRingHom ι) = Polynomial.C (Polynomial.C c) * WK → ∀ j a,
      (W.coeff j).coeff a ≠ 0 → (WK.coeff j).coeff a ≠ 0 := by
    intro W WK c hW j a h h0
    apply h
    have e := congrArg (fun V : K[X][X] ↦ (V.coeff j).coeff a) hW
    simp only [coeff_map, coe_mapRingHom, coeff_C_mul, h0, mul_zero] at e
    exact (map_eq_zero_iff _ hιi).mp e
  obtain ⟨ψ, c, hc, hψmap, hprim⟩ := descend_bivar hϖ ψK hψK0
  have hψs : ∀ j a, (ψ.coeff j).coeff a ≠ 0 → j < n ∧ n * a + f.natDegree * j ≤ M :=
    fun j a h ↦ hψKs j a (hsupp ψ ψK c hψmap j a h)
  have hψΓ : ∀ q k, k < n → VanishAtN f n ψ (α q) (ζ ^ k * β q)
      (∑ q', if α q' = α q ∧ ¬ β q' = ζ ^ k * β q then mq q' else 0) := fun q k hk ↦ by
    have := hdesc ψ ψK c hψmap _ _ _ ((hζu.pow k).mul (hβu q)) (hpowO k _ _ (hβf q))
      (hψKv _ (hmemΓ q k hk))
    rwa [hneedO] at this
  have hψE : ∀ i k, 1 ≤ k → k < n → VanishAtN f n ψ (x i) (ζ ^ k * y i) 1 :=
    fun i k hk1 hk ↦ hdesc ψ ψK c hψmap _ _ _ ((hζu.pow k).mul (hyu i)) (hpowO k _ _ (hyf i))
      (hψKv _ (hmemE i k hk1 hk))
  -- S3: the residual zeros `Qᵢ ≡ Pᵢ`
  have hres := residual_zeros_N hϖ f hn hlc hd hcop hsqk hsqK hnu ζ hζ hζk x y hyu hyf hx α β mq
    hβu hβf hα hβd hαx hNS γb hγ0 hγs hγv ψ hprim hψs hψΓ hψE
  choose z Y hzx hYy hYf hψQ using hres
  have hmax : ∀ z : O, ϖ ∣ z → z ∈ IsLocalRing.maximalIdeal O := fun z h ↦
    (mem_max_iff_dvd' hϖ z).mpr h
  have hYu : ∀ i, IsUnit (Y i) := fun i ↦ by
    have := unit_add_mem (hyu i) (hmax _ (hYy i)); rwa [add_sub_cancel] at this
  have hαz : ∀ q i, IsUnit (α q - z i) := fun q i ↦ by
    have := unit_add_mem (hαx q i) ((IsLocalRing.maximalIdeal O).neg_mem (hmax _ (hzx i)))
    rwa [show α q - x i + -(z i - x i) = α q - z i by ring] at this
  -- S4: the `ℓ`-th power argument over `K`
  set ψ₁ : K[X][X] := ψ.map (mapRingHom ι) with hψ₁_def
  have hψ₁0 : ψ₁ ≠ 0 := by
    rw [hψmap]
    exact mul_ne_zero (C_ne_zero.mpr (C_ne_zero.mpr hc)) hψK0
  have hψ₁s : ∀ j a, (ψ₁.coeff j).coeff a ≠ 0 → j < n ∧
      n * a + (f.map ι).natDegree * j ≤ (n - 1) * (∑ q, mq q + g) + g := by
    intro j a h
    rw [hfK]
    refine hψs j a fun h0 ↦ h ?_
    simp [ψ₁, h0]
  have hαxK : ∀ q i, ι (α q) ≠ ι (x i) := fun q i h ↦
    (hαx q i).ne_zero (hιi (by rw [map_sub, h, sub_self, map_zero]))
  have hψ₁Γ : ∀ q k, k < n →
      VanishAtN (f.map ι) n ψ₁ (ι (α q)) (ι ζ ^ k * ι (β q))
        (∑ q', if ι (α q') = ι (α q) ∧ ¬ ι (β q') = ι ζ ^ k * ι (β q) then mq q' else 0) :=
    fun q k hk ↦ by
      have := ((hψΓ q k hk).mapR ι).mono (need_reduce ι α β mq ζ hα q k)
      simpa [ψ₁] using this
  have hψ₁E : ∀ i k, 1 ≤ k → k < n →
      VanishAtN (f.map ι) n ψ₁ (ι (x i)) (ι ζ ^ k * ι (y i)) 1 := fun i k hk1 hk ↦ by
    simpa [ψ₁] using (hψE i k hk1 hk).mapR ι
  obtain ⟨Wφ, hWφ0, hWφs, hWφQ, hWφE⟩ := ell_power_function (f.map ι) hn hsqK
    (by rw [hfK]; exact hd) (by rw [hfK]; exact hcop) hnK (ι ζ) (hζ.map_of_injective hιi)
    (fun i ↦ ι (x i)) (fun i ↦ ι (y i)) (fun i ↦ hneK _ (hyu i)) (fun i ↦ hevK _ _ (hyf i))
    (fun q ↦ ι (α q)) (fun q ↦ ι (β q)) mq ((points_reduce ι α β hα hβd).2) (fun q ↦ hneK _ (hβu q))
    (fun q ↦ hevK _ _ (hβf q)) hαxK (fun i ↦ ι (z i)) (fun i ↦ ι (Y i)) (fun i ↦ hneK _ (hYu i))
    (fun i ↦ hevK _ _ (hYf i))
    (fun q i h ↦ (hαz q i).ne_zero (hιi (by rw [map_sub, h, sub_self, map_zero])))
    ψ₁ hψ₁0 hψ₁s hψ₁Γ hψ₁E (fun i ↦ by rw [hψ₁_def, evalW_map, hψQ i, map_zero]) ℓ Ξ hΞ0
    (by rw [hfK]; exact hΞs) hΞv
  -- S5: descend and apply the kernel lemma
  obtain ⟨Ψ₂, c₂, hc₂, hΨ₂map, hprim₂⟩ := descend_bivar hϖ Wφ hWφ0
  have hΨ₂s : ∀ j a, (Ψ₂.coeff j).coeff a ≠ 0 → j < n ∧ n * a + f.natDegree * j ≤ ℓ * n * g := by
    intro j a h
    have := hWφs j a (hsupp Ψ₂ Wφ c₂ hΨ₂map j a h)
    rwa [hfK] at this
  have hΨ₂0 : Ψ₂ ≠ 0 := fun h0 ↦ hprim₂ (by simp [h0])
  have hΨ₂n : Ψ₂.natDegree < n := by
    by_contra h
    push_neg at h
    have hlc2 := leadingCoeff_ne_zero.mpr hΨ₂0
    obtain ⟨a, ha⟩ : ∃ a, (Ψ₂.coeff Ψ₂.natDegree).coeff a ≠ 0 := by
      by_contra h1; push_neg at h1; exact hlc2 (Polynomial.ext h1)
    have := (hΨ₂s _ a ha).1
    omega
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  have ht := kernel_no_torsion_N hϖ hn hd hζ hζk hnu hℓ f x y (fun i ↦ z i - x i) Y hyu hx hzx hYy
    Ψ₂ hΨ₂n hprim₂
    (fun j hj ↦ by
      obtain ⟨a, ha⟩ : ∃ a, (Ψ₂.coeff j).coeff a ≠ 0 ∧ a = (Ψ₂.coeff j).natDegree :=
        ⟨_, leadingCoeff_ne_zero.mpr hj, rfl⟩
      have := (hΨ₂s j _ ha.1).2
      rw [← ha.2]; exact this)
    (fun i ↦ by
      rw [add_sub_cancel]
      exact hdesc Ψ₂ Wφ c₂ hΨ₂map _ _ _ (hYu i) (hYf i) (hWφQ i))
    (fun i k hk1 hk ↦ hdesc Ψ₂ Wφ c₂ hΨ₂map _ _ _ ((hζu.pow k).mul (hyu i)) (hpowO k _ _ (hyf i))
      (by rw [map_mul, map_pow]; exact hWφE i k hk1 hk))
    (fun U hUn hUb hUv ↦ hNS U (fun j a h ↦ by
      have hj : U.coeff j ≠ 0 := fun h0 ↦ h (by rw [h0, Polynomial.coeff_zero])
      refine ⟨lt_of_le_of_lt (le_natDegree_of_ne_zero hj) hUn, ?_⟩
      have h1 := hUb j hj
      have h2 := le_natDegree_of_ne_zero h
      nlinarith) hUv)
  -- S6: `Qᵢ = Pᵢ`, so `ψ` vanishes on all of `E + σE + ⋯`
  have hzx' : ∀ i, z i = x i := fun i ↦ sub_eq_zero.mp (ht i)
  have hYy' : ∀ i, Y i = y i := fun i ↦ eq_of_pow_eq (hnu.mul ((hyu i).pow _))
    (by rw [hYf i, hzx' i, hyf i]) (hmax _ (hYy i))
  have hψP : ∀ i, evalW ψ (x i) (y i) = 0 := fun i ↦ by
    rw [← hzx' i, ← hYy' i]; exact hψQ i
  have hψ₁all : ∀ i k, k < n → VanishAtN (f.map ι) n ψ₁ (ι (x i)) (ι ζ ^ k * ι (y i)) 1 := by
    intro i k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [pow_zero, one_mul]
      exact vanish1_of_evalW (hevK _ _ (hyf i)) (by rw [hψ₁_def, evalW_map, hψP i, map_zero])
    · exact hψ₁E i k hk1 hk
  have := principal_of_vanish (f.map ι) hn hsqK (by rw [hfK]; exact hd) (by rw [hfK]; exact hcop)
    hnK (ι ζ) (hζ.map_of_injective hιi) (fun i ↦ ι (x i)) (fun i ↦ ι (y i)) (hinjK x hx)
    (fun i ↦ hneK _ (hyu i)) (fun i ↦ hevK _ _ (hyf i)) (fun q ↦ ι (α q)) (fun q ↦ ι (β q)) mq
    ((points_reduce ι α β hα hβd).2) (fun q ↦ hneK _ (hβu q)) (fun q ↦ hevK _ _ (hβf q)) hαxK ψ₁ hψ₁0 hψ₁s hψ₁Γ
    hψ₁all
  rwa [hfK] at this

end DVR

end Sup
