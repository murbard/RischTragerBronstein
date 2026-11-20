import RischTragerBronstein.Algebraic.SupVanish

/-!
# The residual zeros of the auxiliary function

* `reduced_structure` (over a perfect field `C`): if `γ` has divisor `≥ Γ` and pole order `≤ deg Γ`
  and `ψ` (pole order `≤ M = (n−1)(deg Γ + g) + g`) vanishes on the conjugates `σᵏΓ`, `σᵏE`
  (`k ≠ 0`) of `Γ` and of a non-special `E = ∑ Pᵢ`, then the norm of `ψ` is
  `λ ∏(x − α_q)^{(n−1) m_q} ∏(x − xᵢ)ⁿ` and `ψ` vanishes simply at each `σᵏPᵢ`;
* `norm_lower`, `base_vanish` (over a perfect field): divisibility of the norm from vanishing, and
  a zero at `Pᵢ` from a zero of order `n` of the norm;
* `residual_zeros_N` (Henselian DVR): a function over `O` whose reduction is as in
  `reduced_structure` has zeros `Qᵢ ≡ Pᵢ` (Hensel on the cofactor `R = N / W`, `R̄ = λ ∏(x − xᵢ)`,
  and `disc_unique_N` on the conjugate branches).
-/

open Polynomial IntermediateField Differential Differential.SuperData

namespace Sup

section Field

variable {C : Type*} [Field C] [PerfectField C]

open Classical in
/-- **The structure of the reduced auxiliary function.** -/
theorem reduced_structure (f : C[X]) {n : ℕ} (hn : 0 < n) (hsq : Squarefree f)
    (hd : 0 < f.natDegree) (hcop : Nat.Coprime n f.natDegree) (hnC : (n : C) ≠ 0)
    (ζ : C) (hζ : IsPrimitiveRoot ζ n)
    {g r : ℕ} (x y : Fin g → C) (hx : Function.Injective x) (hy : ∀ i, y i ≠ 0)
    (hyf : ∀ i, y i ^ n = f.eval (x i))
    (α β : Fin r → C) (mq : Fin r → ℕ) (hP : Function.Injective fun q ↦ (α q, β q))
    (hβ : ∀ q, β q ≠ 0)
    (hβf : ∀ q, β q ^ n = f.eval (α q)) (hαx : ∀ q i, α q ≠ x i)
    (hNS : ∀ U : C[X][X], (∀ j a, (U.coeff j).coeff a ≠ 0 → j < n ∧
        n * a + f.natDegree * j ≤ n * g) →
      (∀ i k, 1 ≤ k → k < n → evalW U (x i) (ζ ^ k * y i) = 0) → ∀ i, evalW U (x i) (y i) = 0)
    (γ : C[X][X]) (hγ0 : γ ≠ 0)
    (hγs : ∀ j a, (γ.coeff j).coeff a ≠ 0 → j < n ∧ n * a + f.natDegree * j ≤ ∑ q, mq q)
    (hγv : ∀ q, VanishAtN f n γ (α q) (β q) (mq q))
    (ψ : C[X][X]) (hψ0 : ψ ≠ 0)
    (hψs : ∀ j a, (ψ.coeff j).coeff a ≠ 0 → j < n ∧
      n * a + f.natDegree * j ≤ (n - 1) * (∑ q, mq q + g) + g)
    (hψΓ : ∀ q k, k < n → VanishAtN f n ψ (α q) (ζ ^ k * β q)
      (∑ q', if α q' = α q ∧ ¬ β q' = ζ ^ k * β q then mq q' else 0))
    (hψE : ∀ i k, 1 ≤ k → k < n → VanishAtN f n ψ (x i) (ζ ^ k * y i) 1) :
    (resN f n ψ ≠ 0 ∧ resN f n ψ = Polynomial.C (resN f n ψ).leadingCoeff *
      ((∏ q, (X - Polynomial.C (α q)) ^ ((n - 1) * mq q)) * ∏ i, (X - Polynomial.C (x i)) ^ n)) ∧
      ∀ i k, 1 ≤ k → k < n → ¬ VanishAtN f n ψ (x i) (ζ ^ k * y i) 2 := by
  set S := stdSuper C f n hn hsq hd hnC with hS
  set K := AlgebraicClosure C
  set ι := algebraMap C K with hι_def
  have hιi : Function.Injective ι := ι.injective
  have hcopS : Nat.Coprime S.n S.p.natDegree := hcop
  have hpt : ∀ c d : C, d ^ n = f.eval c → (ι d) ^ S.n = (S.p.map ι).eval (ι c) :=
    fun c d h ↦ by
      show (ι d) ^ n = (f.map ι).eval (ι c)
      rw [← map_pow, h, eval_map, eval₂_hom]
  have hW : ∀ (W : C[X][X]) (M : ℕ), (∀ j a, (W.coeff j).coeff a ≠ 0 → j < n ∧
      n * a + f.natDegree * j ≤ M) → ∀ i, S.n ≤ i → W.coeff i = 0 := by
    intro W M h i hi
    by_contra h0
    obtain ⟨a, ha⟩ : ∃ a, (W.coeff i).coeff a ≠ 0 := by
      by_contra h1; push_neg at h1; exact h0 (Polynomial.ext h1)
    have := (h i a ha).1
    change n ≤ i at hi
    omega
  have hψW := hW ψ _ hψs
  have hγW := hW γ _ hγs
  have hΨ0 : S.elemW ψ ≠ 0 := S.elemW_ne_zero ψ hψ0 hψW
  have hG0 : S.elemW γ ≠ 0 := S.elemW_ne_zero γ hγ0 hγW
  -- the exact divisor of `G`
  set pt : Fin r → K × K := fun q ↦ (ι (α q), ι (β q)) with hpt_def
  have hptinj : Function.Injective pt := fun q q' h ↦
    hP (Prod.ext (hιi (Prod.ext_iff.mp h).1) (hιi (Prod.ext_iff.mp h).2))
  set T : Finset (K × K) := Finset.univ.image pt
  set e : K × K → ℤ := fun Q ↦ ∑ q, if Q = pt q then (mq q : ℤ) else 0
  have he : ∀ q, e (pt q) = mq q := fun q ↦ by
    simp only [e]
    rw [Finset.sum_eq_single q (fun q' _ hq' ↦ if_neg fun h ↦ hq' (hptinj h).symm)
      (fun h ↦ absurd (Finset.mem_univ q) h), if_pos rfl]
  have hTv : ∀ Q ∈ T, Q.2 ^ S.n = (S.p.map ι).eval Q.1 := by
    intro Q hQ
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hQ
    exact hpt _ _ (hβf q)
  have hGv : ∀ q, (mq q : ℤ) ≤ S.ordAt K (S.elemW γ) (ι (α q)) (ι (β q)) := fun q ↦
    (S.le_ordAt_iff_vanish γ hγW hG0 _ _ ((map_ne_zero_iff _ hιi).mpr (hβ q))
      (hpt _ _ (hβf q)) (mq q)).mpr ((hγv q).mapR ι)
  obtain ⟨hGT, hGz, -⟩ := S.exact_divisor hcopS (S.elemW γ) hG0 (S.elemW_integral γ)
    (∑ q, mq q : ℕ) (S.elemW_ordInf hcopS γ _ hγs hG0) T hTv e
    (fun Q hQ ↦ by
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hQ
      rw [he]; exact hGv q)
    (by
      rw [Finset.sum_image fun q _ q' _ h ↦ hptinj h]
      simp only [he]; push_cast; rfl)
  have hG : ∀ q, S.ordAt K (S.elemW γ) (ι (α q)) (ι (β q)) = mq q := fun q ↦ by
    have := hGT (pt q) (Finset.mem_image_of_mem _ (Finset.mem_univ q))
    rw [he] at this; exact this
  have hGz' : ∀ a b : K, b ^ S.n = (S.p.map ι).eval a →
      (∀ q, (a, b) ≠ (ι (α q), ι (β q))) → S.ordAt K (S.elemW γ) a b = 0 := by
    intro a b hv hne
    refine hGz a b hv fun hmem ↦ ?_
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hmem
    exact hne q hq.symm
  have hpow : ∀ k (c d : C), d ^ n = f.eval c → (ζ ^ k * d) ^ n = f.eval c := fun k c d h ↦ by
    rw [mul_pow, ← pow_mul, mul_comm k, pow_mul, hζ.pow_eq_one, one_pow, one_mul, h]
  have hne : ∀ k (d : C), d ≠ 0 → ι (ζ ^ k * d) ≠ 0 := fun k d hd ↦
    (map_ne_zero_iff _ hιi).mpr (mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hn.ne')) hd)
  -- order one and values
  have hone : ∀ (W : C[X][X]) (hWn : ∀ i, S.n ≤ i → W.coeff i = 0) (hW0 : S.elemW W ≠ 0)
      (a b : C), b ≠ 0 → b ^ n = f.eval a →
      (1 ≤ S.ordAt K (S.elemW W) (ι a) (ι b) ↔ evalW W a b = 0) := by
    intro W hWn hW0 a b hb hv
    have h := S.le_ordAt_iff_vanish W hWn hW0 (ι a) (ι b) ((map_ne_zero_iff _ hιi).mpr hb)
      (hpt _ _ hv) 1
    rw [Nat.cast_one] at h
    rw [h]
    constructor
    · intro hv1
      have := evalW_of_vanish le_rfl hv1
      rw [evalW_map] at this
      exact (map_eq_zero_iff _ hιi).mp this
    · intro he
      refine vanish1_of_evalW (hpt _ _ hv) ?_
      rw [evalW_map, he, map_zero]
  have hNS' : ∀ V : C⟮S.x⟯⟮S.y⟯, V ≠ 0 → S.IsIntegralS K V →
      -((S.n * g : ℕ) : ℤ) ≤ S.ordInf K V →
      (∀ i k, 1 ≤ k → k < S.n → 1 ≤ S.ordAt K V (ι (x i)) (ι (ζ ^ k * y i))) →
      ∀ i, 1 ≤ S.ordAt K V (ι (x i)) (ι (y i)) := by
    intro V hV0 hVint hVinf hVE i
    obtain ⟨W, hWV, hW0, hWs⟩ := S.elem_repr (K := K) hcopS V hV0 hVint (S.n * g) hVinf
    have hWn := hW W _ hWs
    subst hWV
    have hev : ∀ i k, 1 ≤ k → k < n → evalW W (x i) (ζ ^ k * y i) = 0 := fun i k hk1 hk ↦
      (hone W hWn hV0 _ _ (mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hn.ne')) (hy i))
        (hpow k _ _ (hyf i))).mp (hVE i k hk1 hk)
    exact (hone W hWn hV0 _ _ (hy i) (hyf i)).mpr (hNS W hWs hev i)
  have hΨΓ : ∀ a b : K, b ^ S.n = (S.p.map ι).eval a →
      ((∑ q, if ι (α q) = a ∧ ¬ ι (β q) = b then mq q else 0 : ℕ) : ℤ) ≤
        S.ordAt K (S.elemW ψ) a b := by
    intro a b hv
    by_cases hA : ∃ q, ι (α q) = a
    · obtain ⟨q, rfl⟩ := hA
      obtain ⟨k, hk, hbk⟩ := S.root_point (ι ζ) (hζ.map_of_injective hιi) (ι (β q)) b
        ((map_ne_zero_iff _ hιi).mpr (hβ q)) (by rw [hv, hpt _ _ (hβf q)])
      have hb : b = ι (ζ ^ k * β q) := by rw [hbk, map_mul, map_pow]
      subst hb
      have e : (∑ q', if ι (α q') = ι (α q) ∧ ¬ ι (β q') = ι (ζ ^ k * β q) then mq q' else 0) =
          ∑ q', if α q' = α q ∧ ¬ β q' = ζ ^ k * β q then mq q' else 0 :=
        Finset.sum_congr rfl fun q' _ ↦ by simp only [hιi.eq_iff]
      rw [e]
      exact (S.le_ordAt_iff_vanish ψ hψW hΨ0 _ _ (hne k _ (hβ q)) (hpt _ _ (hpow k _ _ (hβf q)))
        _).mpr ((hψΓ q k hk).mapR ι)
    · push_neg at hA
      rw [Finset.sum_eq_zero fun q _ ↦ if_neg fun h ↦ hA q h.1]
      exact_mod_cast S.elemW_integral (K := K) ψ a b hv
  have hΨE : ∀ i k, 1 ≤ k → k < S.n →
      1 ≤ S.ordAt K (S.elemW ψ) (ι (x i)) (ι (ζ ^ k * y i)) := fun i k hk1 hk ↦ by
    have := (S.le_ordAt_iff_vanish ψ hψW hΨ0 _ _ (hne k _ (hy i))
      (hpt _ _ (hpow k _ _ (hyf i))) 1).mpr ((hψE i k hk1 hk).mapR ι)
    exact_mod_cast this
  obtain ⟨c, hc, hstr⟩ := S.structure_k (K := K) hcopS ζ hζ x y hx hy hyf α β mq hP hβ hβf hαx
    (S.elemW γ) hG0 (S.elemW_integral γ) hG hGz' (S.elemW ψ) hΨ0 (S.elemW_integral ψ)
    (S.elemW_ordInf hcopS ψ _ hψs hΨ0) hΨΓ hΨE hNS'
  have hψn : ψ.natDegree < S.n := by
    by_contra h
    push_neg at h
    exact hψ0 (leadingCoeff_eq_zero.mp (hψW _ h))
  have hζK : IsPrimitiveRoot (ι ζ) S.n := hζ.map_of_injective hιi
  refine ⟨⟨S.resN_ne_zero hcopS (ι ζ) hζK ψ hψn hΨ0,
    S.norm_structure (K := K) hcopS ζ hζ x y hx hy hyf α β mq hP hβ hβf hαx (S.elemW γ) hG0
      (S.elemW_integral γ) hG hGz' ψ hψn hΨ0 c hc hstr⟩, ?_⟩
  -- the order at `σᵏPᵢ` is exactly one
  intro i k hk1 hk hv2
  have hv := hpt _ _ (hpow k _ _ (hyf i))
  have h2 := (S.le_ordAt_iff_vanish ψ hψW hΨ0 _ _ (hne k _ (hy i)) hv 2).mpr (hv2.mapR ι)
  set U : C[X] := ∏ i, (X - Polynomial.C (x i)) with hU_def
  set Wb : C[X] := ∏ q, (X - Polynomial.C (α q)) ^ mq q with hWb_def
  have hU : U ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ X_sub_C_ne_zero _
  have hWb : Wb ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
  have hUe : U = ∏ i, (X - Polynomial.C (x i)) ^ (fun _ : Fin g ↦ 1) i := by simp [U]
  have hC0 : Polynomial.C c ≠ 0 := C_ne_zero.mpr hc
  have h : S.ordAt K (S.elemW ψ * S.elemW γ) (ι (x i)) (ι (ζ ^ k * y i)) =
      S.ordAt K (S.cst c * (S.polyX U * S.polyX Wb)) (ι (x i)) (ι (ζ ^ k * y i)) := by
    rw [hstr]
  rw [S.ordAt_mul hv hΨ0 hG0, S.cst_eq_polyX,
    S.ordAt_mul hv (S.polyX_ne_zero hC0) (mul_ne_zero (S.polyX_ne_zero hU) (S.polyX_ne_zero hWb)),
    S.ordAt_mul hv (S.polyX_ne_zero hU) (S.polyX_ne_zero hWb),
    S.ordAt_polyX _ hC0 _ _ hv, Polynomial.map_C, rootMultiplicity_C, hUe,
    S.ordAt_polyX_prod_at x hx _ i _ hv (hne k _ (hy i)),
    S.ordAt_polyX_prod_off α _ _ _ hv fun q h ↦ hαx q i (hιi h).symm,
    hGz' _ _ hv fun q h ↦ hαx q i (hιi (Prod.ext_iff.mp h).1).symm] at h
  push_cast at h h2
  linarith

open Classical in
/-- **Lower bound for the norm.** A function vanishing on `σᵏΓ`, `σᵏE` (`k ≠ 0`) has norm divisible
by `∏(x − α_q)^{(n−1) m_q} ∏(x − xᵢ)^{n−1}`, of degree at most its pole order. -/
theorem norm_lower (f : C[X]) {n : ℕ} (hn : 0 < n) (hsq : Squarefree f)
    (hd : 0 < f.natDegree) (hcop : Nat.Coprime n f.natDegree) (hnC : (n : C) ≠ 0)
    (ζ : C) (hζ : IsPrimitiveRoot ζ n)
    {g r : ℕ} (x y : Fin g → C) (hx : Function.Injective x) (hy : ∀ i, y i ≠ 0)
    (hyf : ∀ i, y i ^ n = f.eval (x i))
    (α β : Fin r → C) (mq : Fin r → ℕ) (hβ : ∀ q, β q ≠ 0)
    (hβf : ∀ q, β q ^ n = f.eval (α q)) (hαx : ∀ q i, α q ≠ x i)
    (ψ : C[X][X]) (hψ0 : ψ ≠ 0) (M : ℕ)
    (hψs : ∀ j a, (ψ.coeff j).coeff a ≠ 0 → j < n ∧ n * a + f.natDegree * j ≤ M)
    (hψΓ : ∀ q k, k < n → VanishAtN f n ψ (α q) (ζ ^ k * β q)
      (∑ q', if α q' = α q ∧ ¬ β q' = ζ ^ k * β q then mq q' else 0))
    (hψE : ∀ i k, 1 ≤ k → k < n → VanishAtN f n ψ (x i) (ζ ^ k * y i) 1) :
    resN f n ψ ≠ 0 ∧ (resN f n ψ).natDegree ≤ M ∧
      (∏ q, (X - Polynomial.C (α q)) ^ ((n - 1) * mq q)) *
        ∏ i, (X - Polynomial.C (x i)) ^ (n - 1) ∣ resN f n ψ := by
  set S := stdSuper C f n hn hsq hd hnC with hS
  set K := AlgebraicClosure C
  set ι := algebraMap C K with hι_def
  have hιi : Function.Injective ι := ι.injective
  have hcopS : Nat.Coprime S.n S.p.natDegree := hcop
  have hpt : ∀ c d : C, d ^ n = f.eval c → (ι d) ^ S.n = (S.p.map ι).eval (ι c) :=
    fun c d h ↦ by
      show (ι d) ^ n = (f.map ι).eval (ι c)
      rw [← map_pow, h, eval_map, eval₂_hom]
  have hψW : ∀ i, S.n ≤ i → ψ.coeff i = 0 := by
    intro i hi
    by_contra h0
    obtain ⟨a, ha⟩ : ∃ a, (ψ.coeff i).coeff a ≠ 0 := by
      by_contra h1; push_neg at h1; exact h0 (Polynomial.ext h1)
    have := (hψs i a ha).1
    change n ≤ i at hi
    omega
  have hΨ0 : S.elemW ψ ≠ 0 := S.elemW_ne_zero ψ hψ0 hψW
  have hψn : ψ.natDegree < S.n := by
    by_contra h
    push_neg at h
    exact hψ0 (leadingCoeff_eq_zero.mp (hψW _ h))
  have hζK : IsPrimitiveRoot (ι ζ) S.n := hζ.map_of_injective hιi
  have hpow : ∀ k (c d : C), d ^ n = f.eval c → (ζ ^ k * d) ^ n = f.eval c := fun k c d h ↦ by
    rw [mul_pow, ← pow_mul, mul_comm k, pow_mul, hζ.pow_eq_one, one_pow, one_mul, h]
  have hne : ∀ k (d : C), d ≠ 0 → ι (ζ ^ k * d) ≠ 0 := fun k d hd ↦
    (map_ne_zero_iff _ hιi).mpr (mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hn.ne')) hd)
  have hN0 := S.resN_ne_zero hcopS (ι ζ) hζK ψ hψn hΨ0
  refine ⟨hN0, ?_, ?_⟩
  · have h := S.natDegree_resN hcopS (ι ζ) hζK ψ hψn hΨ0
    have h2 := S.elemW_ordInf (K := K) hcopS ψ M hψs hΨ0
    have : ((resN f n ψ).natDegree : ℤ) ≤ M := by
      show ((resN S.p S.n ψ).natDegree : ℤ) ≤ M
      linarith
    exact_mod_cast this
  have hNK0 : (resN f n ψ).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιi).mpr hN0
  set Q : C[X] := (∏ q, (X - Polynomial.C (α q)) ^ ((n - 1) * mq q)) *
    ∏ i, (X - Polynomial.C (x i)) ^ (n - 1) with hQ_def
  have hQm : Q.Monic := (monic_prod_of_monic _ _ fun q _ ↦ (monic_X_sub_C _).pow _).mul
    (monic_prod_of_monic _ _ fun i _ ↦ (monic_X_sub_C _).pow _)
  have hQK0 : Q.map ι ≠ 0 := (hQm.map ι).ne_zero
  have hQmap : Q.map ι = (∏ q, (X - Polynomial.C (ι (α q))) ^ ((n - 1) * mq q)) *
      ∏ i, (X - Polynomial.C (ι (x i))) ^ (n - 1) := by
    simp [Q, Polynomial.map_mul, Polynomial.map_prod]
  obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  -- the lower bounds for the orders of `ψ` over `K`
  have hlowK : ∀ a b : K, b ^ S.n = (S.p.map ι).eval a →
      ((∑ q, if ι (α q) = a ∧ ¬ ι (β q) = b then mq q else 0 : ℕ) : ℤ) ≤
        S.ordAt K (S.elemW ψ) a b := by
    intro a b hv
    by_cases hA : ∃ q, ι (α q) = a
    · obtain ⟨q, rfl⟩ := hA
      obtain ⟨k, hk, hbk⟩ := S.root_point (ι ζ) hζK (ι (β q)) b
        ((map_ne_zero_iff _ hιi).mpr (hβ q)) (by rw [hv, hpt _ _ (hβf q)])
      have hb : b = ι (ζ ^ k * β q) := by rw [hbk, map_mul, map_pow]
      subst hb
      have e : (∑ q', if ι (α q') = ι (α q) ∧ ¬ ι (β q') = ι (ζ ^ k * β q) then mq q' else 0) =
          ∑ q', if α q' = α q ∧ ¬ β q' = ζ ^ k * β q then mq q' else 0 :=
        Finset.sum_congr rfl fun q' _ ↦ by simp only [hιi.eq_iff]
      rw [e]
      exact (S.le_ordAt_iff_vanish ψ hψW hΨ0 _ _ (hne k _ (hβ q)) (hpt _ _ (hpow k _ _ (hβf q)))
        _).mpr ((hψΓ q k hk).mapR ι)
    · push_neg at hA
      rw [Finset.sum_eq_zero fun q _ ↦ if_neg fun h ↦ hA q h.1]
      exact_mod_cast S.elemW_integral (K := K) ψ a b hv
  have hdvdK : Q.map ι ∣ (resN f n ψ).map ι := by
    rw [IsAlgClosed.dvd_iff_roots_le_roots hQK0 hNK0, Multiset.le_iff_count]
    intro a
    rw [hQmap, roots_mul (by rw [← hQmap]; exact hQK0), Multiset.count_add,
      Sup.count_roots_prod_pow, Sup.count_roots_prod_pow, count_roots]
    by_cases hA : ∃ q, ι (α q) = a
    · obtain ⟨q0, rfl⟩ := hA
      have hx0 : (∑ i, if ι (x i) = ι (α q0) then n - 1 else 0) = 0 :=
        Finset.sum_eq_zero fun i _ ↦ if_neg fun h ↦ hαx q0 i (hιi h).symm
      rw [hx0, add_zero]
      have hb := (map_ne_zero_iff _ hιi).mpr (hβ q0)
      have hv := hpt _ _ (hβf q0)
      have h := S.rootMult_resN (ι ζ) hζK ψ hψn hΨ0 (ι (α q0)) (ι (β q0)) hb hv
      have hk : ∀ k ∈ Finset.range S.n,
          ((∑ q, if ι (α q) = ι (α q0) then mq q else 0 : ℕ) : ℤ) -
            ((∑ q, if ι (α q) = ι (α q0) ∧ ι (β q) = ι ζ ^ k * ι (β q0) then mq q else 0 : ℕ) :
              ℤ) ≤ S.ordAt K (S.elemW ψ) (ι (α q0)) (ι ζ ^ k * ι (β q0)) := by
        intro k _
        have hvk : (ι ζ ^ k * ι (β q0)) ^ S.n = (S.p.map ι).eval (ι (α q0)) := by
          rw [mul_pow, ← pow_mul, mul_comm k, pow_mul, hζK.pow_eq_one, one_pow, one_mul, hv]
        have := hlowK _ _ hvk
        rw [sum_ite_split Finset.univ (fun q ↦ ι (α q) = ι (α q0))
          (fun q ↦ ι (β q) = ι ζ ^ k * ι (β q0)) mq]
        push_cast at this ⊢
        linarith
      have hsum := Finset.sum_le_sum hk
      rw [← h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range] at hsum
      have hfib := Sup.fiber_sum S.hn (ι ζ) hζK (fun q ↦ ι (α q)) (fun q ↦ ι (β q)) mq
        (ι (α q0)) (ι (β q0)) hb (fun q hq ↦ by rw [hpt _ _ (hβf q), hq, ← hv])
      have hfib' : (∑ k ∈ Finset.range S.n, ((∑ q, if ι (α q) = ι (α q0) ∧
          ι (β q) = ι ζ ^ k * ι (β q0) then mq q else 0 : ℕ) : ℤ)) =
          ((∑ q, if ι (α q) = ι (α q0) then mq q else 0 : ℕ) : ℤ) := by
        rw [← hfib]; push_cast; rfl
      rw [hfib', nsmul_eq_mul] at hsum
      have hsum2 : (∑ q, if ι (α q) = ι (α q0) then (n - 1) * mq q else 0) =
          (n - 1) * ∑ q, if ι (α q) = ι (α q0) then mq q else 0 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ ↦ by split_ifs <;> simp
      rw [hsum2]
      have hSn : ((S.n : ℕ) : ℤ) = (n : ℤ) := rfl
      have h2 : (((n - 1) * ∑ q, if ι (α q) = ι (α q0) then mq q else 0 : ℕ) : ℤ) ≤
          ((((resN S.p S.n ψ).map (algebraMap C K)).rootMultiplicity (ι (α q0)) : ℕ) : ℤ) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega)]
        rw [hSn] at hsum
        push_cast at hsum ⊢
        linarith
      exact_mod_cast h2
    · push_neg at hA
      rw [Finset.sum_eq_zero fun q _ ↦ if_neg (hA q), zero_add]
      by_cases hB : ∃ i, ι (x i) = a
      · obtain ⟨i0, rfl⟩ := hB
        rw [Finset.sum_eq_single i0 (fun i _ hi ↦ if_neg fun h ↦ hi (hx (hιi h)))
          (fun h ↦ absurd (Finset.mem_univ i0) h), if_pos rfl]
        have hb := (map_ne_zero_iff _ hιi).mpr (hy i0)
        have hv := hpt _ _ (hyf i0)
        have h := S.rootMult_resN (ι ζ) hζK ψ hψn hΨ0 (ι (x i0)) (ι (y i0)) hb hv
        have hterm : ∀ k ∈ Finset.range n', (1 : ℤ) ≤ S.ordAt K (S.elemW ψ) (ι (x i0))
            (ι ζ ^ (k + 1) * ι (y i0)) := by
          intro k hk
          have hk' := Finset.mem_range.mp hk
          have := (S.le_ordAt_iff_vanish ψ hψW hΨ0 _ _ (hne (k + 1) _ (hy i0))
            (hpt _ _ (hpow (k + 1) _ _ (hyf i0))) 1).mpr
            ((hψE i0 (k + 1) (by omega) (by omega)).mapR ι)
          rw [map_mul, map_pow] at this
          exact_mod_cast this
        have hsum : ((n' : ℕ) : ℤ) ≤
            ∑ k ∈ Finset.range S.n, S.ordAt K (S.elemW ψ) (ι (x i0)) (ι ζ ^ k * ι (y i0)) := by
          show _ ≤ ∑ k ∈ Finset.range n, _
          rw [hn', Finset.sum_range_succ', pow_zero, one_mul]
          have h0 := S.elemW_integral (K := K) ψ (ι (x i0)) (ι (y i0)) hv
          have h1 := Finset.sum_le_sum hterm
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h1
          linarith
        rw [← h] at hsum
        have hn1 : n - 1 = n' := by omega
        rw [hn1]
        exact_mod_cast hsum
      · push_neg at hB
        rw [Finset.sum_eq_zero fun i _ ↦ if_neg (hB i)]
        exact Nat.zero_le _
  exact (Polynomial.map_dvd_map ι hιi hQm).mp hdvdK

/-- **A zero at the base point.** If the norm has a zero of order `n` at `xᵢ` and `ψ` vanishes
at most simply at the conjugates `σᵏPᵢ` (`k ≠ 0`), then `ψ(Pᵢ) = 0`. -/
theorem base_vanish (f : C[X]) {n : ℕ} (hn : 0 < n) (hsq : Squarefree f)
    (hd : 0 < f.natDegree) (hcop : Nat.Coprime n f.natDegree) (hnC : (n : C) ≠ 0)
    (ζ : C) (hζ : IsPrimitiveRoot ζ n) (x₀ y₀ : C) (hy : y₀ ≠ 0) (hyf : y₀ ^ n = f.eval x₀)
    (ψ : C[X][X]) (hψ0 : ψ ≠ 0) (hψW : ∀ i, n ≤ i → ψ.coeff i = 0)
    (hdvd : (X - Polynomial.C x₀) ^ n ∣ resN f n ψ)
    (hsimple : ∀ k, 1 ≤ k → k < n → ¬ VanishAtN f n ψ x₀ (ζ ^ k * y₀) 2) :
    evalW ψ x₀ y₀ = 0 := by
  set S := stdSuper C f n hn hsq hd hnC with hS
  set K := AlgebraicClosure C
  set ι := algebraMap C K with hι_def
  have hιi : Function.Injective ι := ι.injective
  have hcopS : Nat.Coprime S.n S.p.natDegree := hcop
  have hpt : ∀ c d : C, d ^ n = f.eval c → (ι d) ^ S.n = (S.p.map ι).eval (ι c) :=
    fun c d h ↦ by
      show (ι d) ^ n = (f.map ι).eval (ι c)
      rw [← map_pow, h, eval_map, eval₂_hom]
  have hΨ0 : S.elemW ψ ≠ 0 := S.elemW_ne_zero ψ hψ0 hψW
  have hψn : ψ.natDegree < S.n := by
    by_contra h
    push_neg at h
    exact hψ0 (leadingCoeff_eq_zero.mp (hψW _ h))
  have hζK : IsPrimitiveRoot (ι ζ) S.n := hζ.map_of_injective hιi
  have hpow : ∀ k (c d : C), d ^ n = f.eval c → (ζ ^ k * d) ^ n = f.eval c := fun k c d h ↦ by
    rw [mul_pow, ← pow_mul, mul_comm k, pow_mul, hζ.pow_eq_one, one_pow, one_mul, h]
  have hne' : ∀ k, ζ ^ k * y₀ ≠ 0 := fun k ↦ mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hn.ne')) hy
  have hN0 : resN f n ψ ≠ 0 := S.resN_ne_zero hcopS (ι ζ) hζK ψ hψn hΨ0
  have hmK : n ≤ ((resN f n ψ).map ι).rootMultiplicity (ι x₀) := by
    rw [le_rootMultiplicity_iff ((Polynomial.map_ne_zero_iff hιi).mpr hN0)]
    have := Polynomial.map_dvd ι hdvd
    simpa using this
  have h := S.rootMult_resN (ι ζ) hζK ψ hψn hΨ0 (ι x₀) (ι y₀) ((map_ne_zero_iff _ hιi).mpr hy)
    (hpt _ _ hyf)
  obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hle : ∀ k ∈ Finset.range n', S.ordAt K (S.elemW ψ) (ι x₀) (ι ζ ^ (k + 1) * ι y₀) ≤ 1 := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    by_contra hlt
    push_neg at hlt
    have h2 : ((2 : ℕ) : ℤ) ≤ S.ordAt K (S.elemW ψ) (ι x₀) (ι (ζ ^ (k + 1) * y₀)) := by
      rw [map_mul, map_pow]; push_cast; omega
    have hv2 := (S.le_ordAt_iff_vanish ψ hψW hΨ0 _ _ ((map_ne_zero_iff _ hιi).mpr (hne' _))
      (hpt _ _ (hpow (k + 1) _ _ hyf)) 2).mp h2
    have hu : IsUnit ((n : C) * (ζ ^ (k + 1) * y₀) ^ (n - 1)) :=
      IsUnit.mk0 _ (mul_ne_zero hnC (pow_ne_zero _ (hne' _)))
    obtain ⟨V, hV⟩ := exists_branchN f hn hu (hpow (k + 1) _ _ hyf) 1
    have huK : IsUnit ((n : K) * ι (ζ ^ (k + 1) * y₀) ^ (n - 1)) :=
      IsUnit.mk0 _ (mul_ne_zero (S.hnK K) (pow_ne_zero _ ((map_ne_zero_iff _ hιi).mpr (hne' _))))
    exact hsimple (k + 1) (by omega) (by omega) (vanishAtN_of_map ι hιi hn hV huK hv2)
  have hsum := Finset.sum_le_sum hle
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hsum
  have h1 : 1 ≤ S.ordAt K (S.elemW ψ) (ι x₀) (ι y₀) := by
    have e1 := h
    change _ = ∑ k ∈ Finset.range n, _ at e1
    rw [hn', Finset.sum_range_succ', pow_zero, one_mul] at e1
    have h3 : ((n : ℕ) : ℤ) ≤ ((((resN S.p S.n ψ).map (algebraMap C K)).rootMultiplicity (ι x₀) :
        ℕ) : ℤ) := by exact_mod_cast hmK
    have h4 : ((n : ℕ) : ℤ) = n' + 1 := by exact_mod_cast hn'
    linarith
  have hv1 := (S.le_ordAt_iff_vanish ψ hψW hΨ0 _ _ ((map_ne_zero_iff _ hιi).mpr hy)
    (hpt _ _ hyf) 1).mp (by exact_mod_cast h1)
  have := evalW_of_vanish le_rfl hv1
  rw [evalW_map] at this
  exact (map_eq_zero_iff _ hιi).mp this

end Field


section Reduce

variable {R S' : Type*} [CommRing R] [CommRing S'] [Nontrivial S']

/-- Points with abscissae equal or distinct modulo units stay distinct under ring maps. -/
lemma points_reduce (φ : R →+* S') {r : ℕ} (α β : Fin r → R)
    (hα : ∀ q q', α q = α q' ∨ IsUnit (α q - α q'))
    (hβd : ∀ q q', q ≠ q' → α q = α q' → IsUnit (β q - β q')) :
    (∀ q q', φ (α q) = φ (α q') → α q = α q') ∧ Function.Injective fun q ↦ (φ (α q), φ (β q)) := by
  have hαeq : ∀ q q', φ (α q) = φ (α q') → α q = α q' := by
    intro q q' h
    rcases hα q q' with h' | h'
    · exact h'
    · exact absurd (by rw [map_sub, h, sub_self]) ((h'.map φ).ne_zero)
  refine ⟨hαeq, fun q q' h ↦ ?_⟩
  have h1 : φ (α q) = φ (α q') := congrArg Prod.fst h
  have h2 : φ (β q) = φ (β q') := congrArg Prod.snd h
  by_contra hne
  exact ((hβd q q' hne (hαeq q q' h1)).map φ).ne_zero (by rw [map_sub, h2, sub_self])

open Classical in
/-- The vanishing requirements only decrease under ring maps. -/
lemma need_reduce (φ : R →+* S') {r : ℕ} (α β : Fin r → R) (mq : Fin r → ℕ) (ζ : R)
    (hα : ∀ q q', α q = α q' ∨ IsUnit (α q - α q')) (q : Fin r) (k : ℕ) :
    (∑ q', if φ (α q') = φ (α q) ∧ ¬ φ (β q') = φ ζ ^ k * φ (β q) then mq q' else 0) ≤
      ∑ q', if α q' = α q ∧ ¬ β q' = ζ ^ k * β q then mq q' else 0 := by
  refine Finset.sum_le_sum fun q' _ ↦ ?_
  by_cases hc : φ (α q') = φ (α q) ∧ ¬ φ (β q') = φ ζ ^ k * φ (β q)
  · have hαe : α q' = α q := by
      rcases hα q' q with h' | h'
      · exact h'
      · exact absurd (by rw [map_sub, hc.1, sub_self]) ((h'.map φ).ne_zero)
    rw [if_pos hc, if_pos ⟨hαe, fun h ↦ hc.2 (by rw [h, map_mul, map_pow])⟩]
  · rw [if_neg hc]; exact Nat.zero_le _

end Reduce

section DVR

variable {O K : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [HenselianRing O (IsLocalRing.maximalIdeal O)] [Field K] [Algebra O K] [IsFractionRing O K]
  [PerfectField K] [PerfectField (IsLocalRing.ResidueField O)]

local notation "𝕜" => IsLocalRing.ResidueField O
local notation "ρ" => IsLocalRing.residue O
local notation "ι" => algebraMap O K

omit [HenselianRing O (IsLocalRing.maximalIdeal O)] [PerfectField K]
  [PerfectField (IsLocalRing.ResidueField O)] in
lemma mem_max_iff_dvd' {ϖ : O} (hϖ : Irreducible ϖ) (z : O) :
    z ∈ IsLocalRing.maximalIdeal O ↔ ϖ ∣ z := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton]

omit [IsDiscreteValuationRing O] [HenselianRing O (IsLocalRing.maximalIdeal O)] [PerfectField K]
  [PerfectField (IsLocalRing.ResidueField O)] in
lemma derivative_prod_X_sub_C_eval {F : Type*} [CommRing F] {g : ℕ} (x : Fin g → F) (i : Fin g) :
    (∏ j, (X - Polynomial.C (x j))).derivative.eval (x i) =
      ∏ j ∈ Finset.univ.erase i, (x i - x j) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), derivative_mul]
  simp [eval_prod]

open Classical in
/-- **The residual zeros.** If the reduction of the auxiliary function `ψ` has the structure of
`reduced_structure`, then for every base point `Pᵢ` there is a zero `Qᵢ ≡ Pᵢ` of `ψ` over `O`. -/
theorem residual_zeros_N {ϖ : O} (hϖ : Irreducible ϖ) (f : O[X]) {n : ℕ} (hn : 0 < n)
    (hlc : IsUnit f.leadingCoeff) (hd : 0 < f.natDegree) (hcop : Nat.Coprime n f.natDegree)
    (hsqk : Squarefree (f.map ρ)) (hsqK : Squarefree (f.map ι)) (hnu : IsUnit (n : O))
    (ζ : O) (hζ : IsPrimitiveRoot ζ n) (hζk : IsPrimitiveRoot (ρ ζ) n)
    {g r : ℕ} (x y : Fin g → O) (hyu : ∀ i, IsUnit (y i)) (hyf : ∀ i, y i ^ n = f.eval (x i))
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
    (ψ : O[X][X]) (hprim : ¬ ∀ j, Polynomial.C ϖ ∣ ψ.coeff j)
    (hψs : ∀ j a, (ψ.coeff j).coeff a ≠ 0 → j < n ∧
      n * a + f.natDegree * j ≤ (n - 1) * (∑ q, mq q + g) + g)
    (hψΓ : ∀ q k, k < n → VanishAtN f n ψ (α q) (ζ ^ k * β q)
      (∑ q', if α q' = α q ∧ ¬ β q' = ζ ^ k * β q then mq q' else 0))
    (hψE : ∀ i k, 1 ≤ k → k < n → VanishAtN f n ψ (x i) (ζ ^ k * y i) 1) :
    ∀ i, ∃ z Y : O, ϖ ∣ z - x i ∧ ϖ ∣ Y - y i ∧ Y ^ n = f.eval z ∧ evalW ψ z Y = 0 := by
  classical
  have hιi : Function.Injective ι := IsFractionRing.injective O K
  have hres0 : ∀ z : O, ρ z = 0 ↔ ϖ ∣ z := Jac.res_eq_zero_iff hϖ
  have hunitk : ∀ z : O, IsUnit z → ρ z ≠ 0 := fun z hz ↦ (hz.map ρ).ne_zero
  have hfk : (f.map ρ).natDegree = f.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero _ (hunitk _ hlc)
  have hfK : (f.map ι).natDegree = f.natDegree := natDegree_map_eq_of_injective hιi f
  have hnk : (n : 𝕜) ≠ 0 := by rw [← map_natCast ρ]; exact hunitk _ hnu
  have hnK : (n : K) ≠ 0 := by
    rw [← map_natCast ι]; exact (map_ne_zero_iff _ hιi).mpr hnu.ne_zero
  have hinjk : ∀ {m : ℕ} (v : Fin m → O), (∀ a b, a ≠ b → IsUnit (v a - v b)) →
      Function.Injective fun a ↦ ρ (v a) := by
    intro m v hv a b hab
    by_contra hne
    have := hunitk _ (hv a b hne)
    rw [map_sub, show ρ (v a) = ρ (v b) from hab, sub_self] at this
    exact this rfl
  have hinjK : ∀ {m : ℕ} (v : Fin m → O), (∀ a b, a ≠ b → IsUnit (v a - v b)) →
      Function.Injective fun a ↦ ι (v a) := by
    intro m v hv a b hab
    by_contra hne
    have := (hv a b hne).ne_zero
    rw [← sub_eq_zero.mpr (hιi hab)] at this
    exact this rfl
  have hevk : ∀ c d : O, d ^ n = f.eval c → ρ d ^ n = (f.map ρ).eval (ρ c) := fun c d h ↦ by
    rw [← map_pow, h, eval_map, eval₂_hom]
  have hevK : ∀ c d : O, d ^ n = f.eval c → ι d ^ n = (f.map ι).eval (ι c) := fun c d h ↦ by
    rw [← map_pow, h, eval_map, eval₂_hom]
  -- the reduction
  set ψb : 𝕜[X][X] := ψ.map (mapRingHom ρ) with hψb_def
  have hψb0 : ψb ≠ 0 := by
    intro h0
    apply hprim
    intro j
    rw [Jac.C_dvd_iff_map hϖ]
    have := congrArg (fun W ↦ W.coeff j) h0
    simpa [ψb] using this
  have hψbs : ∀ j a, (ψb.coeff j).coeff a ≠ 0 → j < n ∧
      n * a + (f.map ρ).natDegree * j ≤ (n - 1) * (∑ q, mq q + g) + g := by
    intro j a h
    rw [hfk]
    refine hψs j a fun h0 ↦ h ?_
    simp [ψb, h0]
  obtain ⟨⟨hNb0, hNb⟩, hsimple⟩ := reduced_structure (f.map ρ) hn hsqk (by rw [hfk]; exact hd)
    (by rw [hfk]; exact hcop) hnk (ρ ζ) hζk (fun i ↦ ρ (x i)) (fun i ↦ ρ (y i)) (hinjk x hx)
    (fun i ↦ hunitk _ (hyu i)) (fun i ↦ hevk _ _ (hyf i)) (fun q ↦ ρ (α q)) (fun q ↦ ρ (β q)) mq
    ((points_reduce ρ α β hα hβd).2) (fun q ↦ hunitk _ (hβu q)) (fun q ↦ hevk _ _ (hβf q))
    (fun q i h ↦ hunitk _ (hαx q i) (by rw [map_sub, h, sub_self]))
    (by rw [hfk]; exact hNS) γb hγ0 (by rw [hfk]; exact hγs) hγv ψb hψb0 hψbs
    (fun q k hk ↦ by
      have := ((hψΓ q k hk).mapR ρ).mono (need_reduce ρ α β mq ζ hα q k)
      simpa [ψb] using this)
    (fun i k hk1 hk ↦ by simpa [ψb] using (hψE i k hk1 hk).mapR ρ)
  -- over the fraction field
  set ψ₁ : K[X][X] := ψ.map (mapRingHom ι) with hψ₁_def
  have hψ0 : ψ ≠ 0 := fun h0 ↦ hψb0 (by simp [ψb, h0])
  have hψ₁0 : ψ₁ ≠ 0 := fun h0 ↦ hψ0 (Polynomial.map_injective _
    (Polynomial.map_injective _ hιi) (by rw [← hψ₁_def, h0, Polynomial.map_zero]))
  have hψ₁s : ∀ j a, (ψ₁.coeff j).coeff a ≠ 0 → j < n ∧
      n * a + (f.map ι).natDegree * j ≤ (n - 1) * (∑ q, mq q + g) + g := by
    intro j a h
    rw [hfK]
    refine hψs j a fun h0 ↦ h ?_
    simp [ψ₁, h0]
  obtain ⟨-, hNdegK, hWNK⟩ := norm_lower (f.map ι) hn hsqK (by rw [hfK]; exact hd)
    (by rw [hfK]; exact hcop) hnK (ι ζ) (hζ.map_of_injective hιi) (fun i ↦ ι (x i))
    (fun i ↦ ι (y i)) (hinjK x hx) (fun i ↦ (map_ne_zero_iff _ hιi).mpr (hyu i).ne_zero)
    (fun i ↦ hevK _ _ (hyf i)) (fun q ↦ ι (α q)) (fun q ↦ ι (β q)) mq
    (fun q ↦ (map_ne_zero_iff _ hιi).mpr (hβu q).ne_zero) (fun q ↦ hevK _ _ (hβf q))
    (fun q i h ↦ (hαx q i).ne_zero (hιi (by rw [map_sub, h, sub_self, map_zero])))
    ψ₁ hψ₁0 _ hψ₁s
    (fun q k hk ↦ by
      have := ((hψΓ q k hk).mapR ι).mono (need_reduce ι α β mq ζ hα q k)
      simpa [ψ₁] using this)
    (fun i k hk1 hk ↦ by simpa [ψ₁] using (hψE i k hk1 hk).mapR ι)
  -- the factorisation `N = W R` over `O`
  set N := resN f n ψ with hN_def
  set W : O[X] := (∏ q, (X - Polynomial.C (α q)) ^ ((n - 1) * mq q)) *
    ∏ i, (X - Polynomial.C (x i)) ^ (n - 1) with hW_def
  have hWm : W.Monic := (monic_prod_of_monic _ _ fun q _ ↦ (monic_X_sub_C _).pow _).mul
    (monic_prod_of_monic _ _ fun i _ ↦ (monic_X_sub_C _).pow _)
  have hNK : N.map ι = resN (f.map ι) n ψ₁ := resN_map ι f n ψ
  have hWN : W ∣ N := by
    rw [← Polynomial.map_dvd_map ι hιi hWm, hNK]
    convert hWNK using 1
    simp [W, Polynomial.map_mul, Polynomial.map_prod]
  have hNdeg : N.natDegree ≤ (n - 1) * (∑ q, mq q + g) + g := by
    rw [← natDegree_map_eq_of_injective hιi, hNK]; exact hNdegK
  obtain ⟨R, hR⟩ := hWN
  have hWdeg : W.natDegree = (n - 1) * (∑ q, mq q + g) := by
    rw [hW_def, natDegree_mul
      (Finset.prod_ne_zero_iff.mpr fun q _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _))
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)),
      natDegree_prod _ _ fun q _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _),
      natDegree_prod _ _ fun q _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)]
    simp only [natDegree_pow, natDegree_X_sub_C, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    rw [mul_add, Finset.mul_sum]; ring
  have hNk : N.map ρ = resN (f.map ρ) n ψb := resN_map ρ f n ψ
  have hN0 : N ≠ 0 := fun h0 ↦ hNb0 (by rw [← hNk, h0, Polynomial.map_zero])
  have hR0 : R ≠ 0 := fun h0 ↦ hN0 (by rw [hR, h0, mul_zero])
  have hRdeg : R.natDegree ≤ g := by
    have := congrArg natDegree hR
    rw [natDegree_mul hWm.ne_zero hR0, hWdeg] at this
    omega
  -- the reduction of `R`
  set ub : 𝕜[X] := ∏ i, (X - Polynomial.C (ρ (x i))) with hub_def
  set Wk : 𝕜[X] := (∏ q, (X - Polynomial.C (ρ (α q))) ^ ((n - 1) * mq q)) *
    ∏ i, (X - Polynomial.C (ρ (x i))) ^ (n - 1) with hWk_def
  have hWk : W.map ρ = Wk := by simp [W, Wk, Polynomial.map_mul, Polynomial.map_prod]
  have hWk0 : Wk ≠ 0 := by rw [← hWk]; exact (hWm.map ρ).ne_zero
  have hQk : (∏ q, (X - Polynomial.C (ρ (α q))) ^ ((n - 1) * mq q)) *
      ∏ i, (X - Polynomial.C (ρ (x i))) ^ n = Wk * ub := by
    rw [hWk_def, hub_def, mul_assoc, ← Finset.prod_mul_distrib]
    congr 2
    ext1 i
    rw [← pow_succ, Nat.sub_add_cancel hn]
  set lc := (resN (f.map ρ) n ψb).leadingCoeff with hlc_def
  have hlc0 : lc ≠ 0 := leadingCoeff_ne_zero.mpr hNb0
  have hRk : R.map ρ = Polynomial.C lc * ub := by
    have e := congrArg (Polynomial.map ρ) hR
    rw [hNk, Polynomial.map_mul, hWk, hNb, hQk] at e
    apply mul_left_cancel₀ hWk0
    rw [← e]; ring
  have hubm : ub.Monic := monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C _
  have hubd : ub.natDegree = g := by
    rw [hub_def, natDegree_prod _ _ fun i _ ↦ X_sub_C_ne_zero _]
    simp
  have hρu : ρ (R.coeff g) = lc := by
    rw [← coeff_map, hRk, coeff_C_mul, ← hubd, hubm.coeff_natDegree, mul_one]
  have hRu : IsUnit (R.coeff g) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [hρu]; exact hlc0)
  set R' := Polynomial.C (↑hRu.unit⁻¹ : O) * R with hR'_def
  have hR'map : R'.map ρ = ub := by
    have hinv : ρ (↑hRu.unit⁻¹ : O) * lc = 1 := by
      rw [← hρu, ← map_mul]; simp
    rw [hR'_def, Polynomial.map_mul, Polynomial.map_C, hRk, ← mul_assoc, ← Polynomial.C_mul, hinv,
      Polynomial.C_1, one_mul]
  have hR'm : R'.Monic := by
    have hRnd : R.natDegree = g := le_antisymm hRdeg (le_natDegree_of_ne_zero hRu.ne_zero)
    rw [Monic, leadingCoeff, hR'_def, natDegree_C_mul (Units.ne_zero _), hRnd, coeff_C_mul]
    simp
  -- the first-order coefficient at `σᵏPᵢ` is a unit
  have hxk := hinjk x hx
  have hpowO : ∀ k (c d : O), d ^ n = f.eval c → (ζ ^ k * d) ^ n = f.eval c := fun k c d h ↦ by
    rw [mul_pow, ← pow_mul, mul_comm k, pow_mul, hζ.pow_eq_one, one_pow, one_mul, h]
  have hζu : IsUnit ζ := hζ.isUnit hn.ne'
  have hbu : ∀ k i, IsUnit ((n : O) * (ζ ^ k * y i) ^ (n - 1)) := fun k i ↦
    hnu.mul (((hζu.pow k).mul (hyu i)).pow _)
  have hunit1 : ∀ i k, 1 ≤ k → k < n → ∀ V, IsBranchN f n (x i) (ζ ^ k * y i) 2 V →
      IsUnit ((jetN ψ (x i) V).coeff 1) := by
    intro i k hk1 hk V hV
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro hc
    apply hsimple i k hk1 hk
    refine ⟨V.map ρ, by simpa using hV.mapR ρ, ?_⟩
    show X ^ 2 ∣ jetN ψb (ρ (x i)) (V.map ρ)
    rw [hψb_def, ← jetN_map, X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · rw [coeff_map, jetN_coeff_zero, hV.1, evalW_of_vanish le_rfl (hψE i k hk1 hk), map_zero]
    · rw [coeff_map]; exact hc
  have hψdeg : ψ.natDegree ≤ n - 1 := by
    by_contra h
    push_neg at h
    have hc := leadingCoeff_ne_zero.mpr hψ0
    obtain ⟨a, ha⟩ : ∃ a, (ψ.coeff ψ.natDegree).coeff a ≠ 0 := by
      by_contra h1; push_neg at h1; exact hc (Polynomial.ext h1)
    have := (hψs _ a ha).1
    omega
  have hψ₁W : ∀ j, n ≤ j → ψ₁.coeff j = 0 := by
    intro j hj
    by_contra h0
    obtain ⟨a, ha⟩ : ∃ a, (ψ₁.coeff j).coeff a ≠ 0 := by
      by_contra h1; push_neg at h1; exact h0 (Polynomial.ext h1)
    have := (hψ₁s j a ha).1
    omega
  intro i
  -- Hensel: a root `z ≡ xᵢ` of `R`
  have hH1 : R'.eval (x i) ∈ IsLocalRing.maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff,
      show ρ (R'.eval (x i)) = (R'.map ρ).eval (ρ (x i)) by rw [eval_map, eval₂_hom], hR'map,
      hub_def, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hH2 : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)
      (R'.derivative.eval (x i))) := by
    show IsUnit (ρ (R'.derivative.eval (x i)))
    rw [show ρ (R'.derivative.eval (x i)) = (R'.map ρ).derivative.eval (ρ (x i)) by
      rw [derivative_map, eval_map, eval₂_hom], hR'map, hub_def]
    rw [derivative_prod_X_sub_C_eval (fun j ↦ ρ (x j)) i]
    refine (Finset.prod_ne_zero_iff.mpr fun j hj ↦ ?_).isUnit
    exact sub_ne_zero.mpr fun he ↦ (Finset.ne_of_mem_erase hj) (hxk he).symm
  obtain ⟨z, hzr, hzx⟩ := HenselianRing.is_henselian R' hR'm (x i) hH1 hH2
  have hRz : R.eval z = 0 := by
    have : R'.eval z = 0 := hzr
    rw [hR'_def, eval_mul, eval_C] at this
    exact (mul_eq_zero.mp this).resolve_left (Units.ne_zero _)
  -- Hensel again: `Yⁿ = f(z)`, `Y ≡ yᵢ`
  have hfz : f.eval z - f.eval (x i) ∈ IsLocalRing.maximalIdeal O :=
    Ideal.mem_of_dvd _ (sub_dvd_eval_sub z (x i) f) hzx
  set P2 : O[X] := X ^ n - Polynomial.C (f.eval z) with hP2_def
  have hP2m : P2.Monic := monic_X_pow_sub_C _ hn.ne'
  have hP21 : P2.eval (y i) ∈ IsLocalRing.maximalIdeal O := by
    simp only [P2, eval_sub, eval_pow, eval_X, eval_C, hyf i]
    have := (IsLocalRing.maximalIdeal O).neg_mem hfz
    rwa [neg_sub] at this
  have hP22 : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)
      (P2.derivative.eval (y i))) := by
    have e : P2.derivative.eval (y i) = (n : O) * y i ^ (n - 1) := by
      simp [P2, derivative_X_pow]
    rw [e]
    exact (hnu.mul ((hyu i).pow _)).map _
  obtain ⟨Y, hYr, hYy⟩ := HenselianRing.is_henselian P2 hP2m (y i) hP21 hP22
  have hY : Y ^ n = f.eval z := by
    have : P2.eval Y = 0 := hYr
    simp only [P2, eval_sub, eval_pow, eval_X, eval_C] at this
    exact sub_eq_zero.mp this
  -- a zero of `ψ` above `z`
  have hNz : N.eval z = 0 := by rw [hR, eval_mul, hRz, mul_zero]
  have hprod := resN_eval f hn hζ ψ hψdeg z Y hY
  rw [← hN_def, hNz] at hprod
  obtain ⟨k, hk, hk0⟩ := Finset.prod_eq_zero_iff.mp hprod.symm
  have hk' := Finset.mem_range.mp hk
  by_cases hk1 : k = 0
  · subst hk1
    refine ⟨z, Y, (mem_max_iff_dvd' hϖ _).mp hzx, (mem_max_iff_dvd' hϖ _).mp hYy, hY, ?_⟩
    simpa using hk0
  -- otherwise the zero lies on a conjugate branch: the disc argument
  obtain ⟨V, hV⟩ := exists_branchN f hn (hbu k i) (hpowO k _ _ (hyf i)) 1
  have h0 : (jetN ψ (x i) V).coeff 0 = 0 := by
    rw [jetN_coeff_zero, hV.1]; exact evalW_of_vanish le_rfl (hψE i k (by omega) hk')
  have ht := disc_unique_N f hn ψ hV (hbu k i) h0 (hunit1 i k (by omega) hk' V hV)
    (t := z - x i) (Y := ζ ^ k * Y) hzx
    (by rw [← mul_sub]; exact Ideal.mul_mem_left _ _ hYy)
    (by rw [add_sub_cancel]; exact hpowO k _ _ hY) (by rw [add_sub_cancel]; exact hk0)
  have hzx' : z = x i := sub_eq_zero.mp ht
  -- `(x − xᵢ)ⁿ ∣ N`, hence `ψ(Pᵢ) = 0`
  have hdvdN : (X - Polynomial.C (x i)) ^ n ∣ N := by
    rw [hR, ← Nat.sub_add_cancel hn, pow_succ]
    refine mul_dvd_mul (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem
      (fun j ↦ (X - Polynomial.C (x j)) ^ (n - 1)) (Finset.mem_univ i)) _) ?_
    rw [dvd_iff_isRoot, IsRoot, ← hzx']; exact hRz
  have hdvdK : (X - Polynomial.C (ι (x i))) ^ n ∣ resN (f.map ι) n ψ₁ := by
    rw [← hNK]; simpa using Polynomial.map_dvd ι hdvdN
  have hsimpleK : ∀ k, 1 ≤ k → k < n →
      ¬ VanishAtN (f.map ι) n ψ₁ (ι (x i)) (ι ζ ^ k * ι (y i)) 2 := by
    intro k hk1 hk hv2
    obtain ⟨V', hV'⟩ := exists_branchN f hn (hbu k i) (hpowO k _ _ (hyf i)) 1
    have huK : IsUnit ((n : K) * ι (ζ ^ k * y i) ^ (n - 1)) := IsUnit.mk0 _ (mul_ne_zero hnK
      (pow_ne_zero _ ((map_ne_zero_iff _ hιi).mpr ((hζu.pow k).mul (hyu i)).ne_zero)))
    have hvO := vanishAtN_of_map ι hιi hn hV' huK (by rw [map_mul, map_pow]; exact hv2)
    have hd2 := vanish_along hn hV' (hbu k i) hvO
    rw [X_pow_dvd_iff] at hd2
    exact (hunit1 i k hk1 hk V' hV').ne_zero (hd2 1 (by norm_num))
  have hev := base_vanish (f.map ι) hn hsqK (by rw [hfK]; exact hd) (by rw [hfK]; exact hcop) hnK
    (ι ζ) (hζ.map_of_injective hιi) (ι (x i)) (ι (y i))
    ((map_ne_zero_iff _ hιi).mpr (hyu i).ne_zero) (hevK _ _ (hyf i)) ψ₁ hψ₁0 hψ₁W hdvdK hsimpleK
  rw [hψ₁_def, evalW_map] at hev
  exact ⟨x i, y i, by simp, by simp, hyf i, (map_eq_zero_iff _ hιi).mp hev⟩

end DVR

end Sup
