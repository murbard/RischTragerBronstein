import RischTragerBronstein.Algebraic.SupStructure

/-!
# Bridges between bivariate polynomials and the function field

* `stdSuper`: the curve `yⁿ = p(x)` over any field `C` (with `p` squarefree, `n` invertible);
* `le_ordAt_iff_vanish`: at an ordinary point, `ord ≥ m` for `∑ Wᵢ(x) yⁱ` is `VanishAtN … m`;
* `exact_divisor`: an integral function of pole order `≤ B` with `≥ B` prescribed zeros has
  exactly these zeros (degree theorem);
* `prod_dvd_of_rootMult`, `eq_C_mul_of_dvd`: polynomials with prescribed root multiplicities.
-/

open Polynomial IntermediateField

namespace Sup

/-- Root multiplicities of a product of powers of linear factors. -/
lemma count_roots_prod_pow {F ι : Type*} [Field F] [DecidableEq F] (s : Finset ι) (c : ι → F)
    (e : ι → ℕ) (a : F) :
    ((∏ i ∈ s, (X - C (c i)) ^ e i).roots).count a = ∑ i ∈ s, if c i = a then e i else 0 := by
  classical
  rw [roots_prod _ _ (Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)),
    Multiset.count_bind]
  change ∑ i ∈ s, ((X - C (c i)) ^ e i).roots.count a = _
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [roots_pow, roots_X_sub_C, Multiset.count_nsmul, Multiset.count_singleton]
  by_cases h : c i = a
  · rw [if_pos h.symm, if_pos h, mul_one]
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]

/-- Each point of a fibre is `ζᵏ b` for exactly one `k < n`. -/
lemma fiber_count {F : Type*} [Field F] [DecidableEq F] {n : ℕ} (hn : 0 < n) (ζ : F) (hζ : IsPrimitiveRoot ζ n)
    (b c : F) (hb : b ≠ 0) (hc : c ^ n = b ^ n) :
    (∑ k ∈ Finset.range n, if c = ζ ^ k * b then 1 else 0 : ℕ) = 1 := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨k0, hk0, hkc⟩ := hζ.eq_pow_of_pow_eq_one (ξ := c / b) (by
    rw [div_pow, hc, div_self (pow_ne_zero _ hb)])
  have hc0 : c = ζ ^ k0 * b := by rw [hkc, div_mul_cancel₀ _ hb]
  rw [Finset.sum_eq_single k0 (fun k hk hne ↦ if_neg fun h ↦ hne ?_)
    (fun h ↦ absurd (Finset.mem_range.mpr hk0) h), if_pos hc0]
  rw [hc0] at h
  exact (hζ.pow_inj (Finset.mem_range.mp hk) hk0 (mul_right_cancel₀ hb h.symm))

/-- Summing an indicator over the points of a fibre. -/
lemma fiber_sum {F : Type*} [Field F] [DecidableEq F] {n r : ℕ} (hn : 0 < n) (ζ : F) (hζ : IsPrimitiveRoot ζ n)
    (A B : Fin r → F) (m : Fin r → ℕ) (a b : F) (hb : b ≠ 0)
    (hB : ∀ q, A q = a → B q ^ n = b ^ n) :
    (∑ k ∈ Finset.range n, ∑ q, if A q = a ∧ B q = ζ ^ k * b then m q else 0 : ℕ) =
      ∑ q, if A q = a then m q else 0 := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  by_cases hA : A q = a
  · simp only [hA, true_and, if_true]
    have := fiber_count hn ζ hζ b (B q) hb (hB q hA)
    calc (∑ k ∈ Finset.range n, if B q = ζ ^ k * b then m q else 0)
        = m q * ∑ k ∈ Finset.range n, if B q = ζ ^ k * b then 1 else 0 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ ↦ by split_ifs <;> simp
      _ = m q := by rw [this, mul_one]
  · simp [hA]

/-- A product of powers of distinct linear factors divides a polynomial with at least these root
multiplicities. -/
theorem prod_dvd_of_rootMult {F ι : Type*} [Field F] [Fintype ι] {P : F[X]} (hP : P ≠ 0)
    (r : ι → F) (hr : Function.Injective r) (e : ι → ℕ)
    (h : ∀ j, e j ≤ P.rootMultiplicity (r j)) : ∏ j, (X - C (r j)) ^ e j ∣ P := by
  classical
  apply Finset.prod_dvd_of_coprime
  · intro i _ j _ hij
    exact ((pairwise_coprime_X_sub_C hr) hij).pow
  · intro j _
    exact (le_rootMultiplicity_iff hP).mp (h j)

/-- A polynomial divisible by a monic polynomial of at least its degree is a constant multiple. -/
theorem eq_C_mul_of_dvd {R : Type*} [CommRing R] [IsDomain R] {P Q : R[X]} (hQ : Q.Monic)
    (hP : P ≠ 0) (hdvd : Q ∣ P) (hdeg : P.natDegree ≤ Q.natDegree) :
    P = C P.leadingCoeff * Q := by
  obtain ⟨H, rfl⟩ := hdvd
  have hH : H ≠ 0 := right_ne_zero_of_mul hP
  rw [natDegree_mul hQ.ne_zero hH] at hdeg
  have hH0 : H.natDegree = 0 := by omega
  rw [eq_C_of_natDegree_eq_zero hH0, leadingCoeff_mul, hQ.leadingCoeff, one_mul, leadingCoeff_C,
    mul_comm]

open Classical in
/-- The total vanishing requirement on the fibres of `Γ`: `∑_{P ∈ T} need(P) = (n − 1) ∑ m_q`. -/
lemma sum_need_image {F : Type*} [Field F] {n r : ℕ} (hn : 0 < n) (ζ : F)
    (hζ : IsPrimitiveRoot ζ n) (A B : Fin r → F) (mq : Fin r → ℕ) (hB : ∀ q, B q ≠ 0)
    (hfib : ∀ q q', A q = A q' → B q ^ n = B q' ^ n) :
    (∑ Q ∈ (Finset.univ ×ˢ Finset.range n).image (fun p : Fin r × ℕ ↦ (A p.1, ζ ^ p.2 * B p.1)),
      ∑ q, if A q = Q.1 ∧ ¬ B q = Q.2 then mq q else 0) = (n - 1) * ∑ q, mq q := by
  set T := (Finset.univ ×ˢ Finset.range n).image (fun p : Fin r × ℕ ↦ (A p.1, ζ ^ p.2 * B p.1))
  have hroot : ∀ q (c : F), c ^ n = B q ^ n → ∃ k < n, c = ζ ^ k * B q := by
    intro q c hc
    haveI : NeZero n := ⟨hn.ne'⟩
    obtain ⟨k, hk, hkc⟩ := hζ.eq_pow_of_pow_eq_one (ξ := c / B q) (by
      rw [div_pow, hc, div_self (pow_ne_zero _ (hB q))])
    exact ⟨k, hk, by rw [hkc, div_mul_cancel₀ _ (hB q)]⟩
  have hcard : ∀ q, (T.filter fun Q ↦ Q.1 = A q).card = n := by
    intro q
    have heq : T.filter (fun Q ↦ Q.1 = A q) =
        (Finset.range n).image fun k ↦ (A q, ζ ^ k * B q) := by
      ext Q
      simp only [T, Finset.mem_filter, Finset.mem_image, Finset.mem_range, Finset.mem_product,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨⟨q', k'⟩, hk', rfl⟩, hQ1⟩
        simp only at hQ1 hk' ⊢
        obtain ⟨k, hk, hck⟩ := hroot q (ζ ^ k' * B q') (by
          rw [mul_pow, ← pow_mul, mul_comm k', pow_mul, hζ.pow_eq_one, one_pow, one_mul,
            hfib q' q hQ1])
        exact ⟨k, hk, by rw [hQ1, hck]⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨(q, k), hk, rfl⟩, rfl⟩
    rw [heq, Finset.card_image_of_injOn, Finset.card_range]
    intro k hk k' hk' h
    have h2 := (Prod.ext_iff.mp h).2
    exact hζ.pow_inj (Finset.mem_range.mp hk) (Finset.mem_range.mp hk')
      (mul_right_cancel₀ (hB q) h2)
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  congr 1
  have hpq : (A q, B q) ∈ T.filter (fun Q ↦ Q.1 = A q) :=
    Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(q, 0), Finset.mem_product.mpr
      ⟨Finset.mem_univ _, Finset.mem_range.mpr hn⟩, by simp⟩, rfl⟩
  have e1 : T.filter (fun Q ↦ A q = Q.1 ∧ ¬ B q = Q.2) =
      (T.filter fun Q ↦ Q.1 = A q).erase (A q, B q) := by
    ext Q
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hQ, h1, h2⟩
      exact ⟨fun h ↦ h2 (by rw [h]), hQ, h1.symm⟩
    · rintro ⟨hne, hQ, h1⟩
      exact ⟨hQ, h1.symm, fun h2 ↦ hne (Prod.ext h1 h2.symm)⟩
  rw [e1, Finset.card_erase_of_mem hpq, hcard]

end Sup

namespace Differential

namespace SuperData

open Sup

/-- **The standard superelliptic curve** `yⁿ = p(x)` over a field `C`, with function field inside
the algebraic closure of `C(x)`. -/
noncomputable def stdSuper (C : Type*) [Field C] (p : C[X]) (n : ℕ) (hn : 0 < n)
    (hsq : Squarefree p) (hp : 0 < p.natDegree) (hnC : (n : C) ≠ 0) :
    SuperData C (AlgebraicClosure (RatFunc C)) where
  x := algebraMap (RatFunc C) (AlgebraicClosure (RatFunc C)) RatFunc.X
  y := Classical.choose (IsAlgClosed.exists_pow_nat_eq
    (aeval (algebraMap (RatFunc C) (AlgebraicClosure (RatFunc C)) RatFunc.X) p) hn)
  n := n
  p := p
  htr := (transcendental_algebraMap_iff (algebraMap (RatFunc C) _).injective).mpr
    RatFunc.transcendental_X
  hn := hn
  hsq := hsq
  hp := hp
  hy := Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    (aeval (algebraMap (RatFunc C) (AlgebraicClosure (RatFunc C)) RatFunc.X) p) hn)
  hnC := hnC

@[simp] lemma stdSuper_n {C : Type*} [Field C] (p : C[X]) (n : ℕ) (hn hsq hp hnC) :
    (stdSuper C p n hn hsq hp hnC).n = n := rfl
@[simp] lemma stdSuper_p {C : Type*} [Field C] (p : C[X]) (n : ℕ) (hn hsq hp hnC) :
    (stdSuper C p n hn hsq hp hnC).p = p := rfl

variable {C L K : Type*} [Field C] [PerfectField C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K] [IsAlgClosed K]

variable (S : SuperData C L)

/-- **Order and vanishing** of `∑ Wᵢ(x) yⁱ` at an ordinary point. -/
theorem le_ordAt_iff_vanish (W : C[X][X]) (hW : ∀ i, S.n ≤ i → W.coeff i = 0)
    (h0 : S.elemW W ≠ 0) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) (m : ℕ) :
    (m : ℤ) ≤ S.ordAt K (S.elemW W) α β ↔
      VanishAtN (S.p.map (algebraMap C K)) S.n (W.map (mapRingHom (algebraMap C K))) α β m := by
  rw [S.ordAt_nb _ α β hβ hβp]
  have hne := S.embXY_ne_zero α β hβ hβp h0
  constructor
  · intro h
    apply S.vanish_of_orderTop_ge α β hβ hβp W hW m
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hne]
    exact_mod_cast h
  · intro h
    have := S.orderTop_ge_of_vanish α β hβ hβp W hW m h
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hne] at this
    exact_mod_cast this

/-- **Exact divisors from the degree theorem.** -/
theorem exact_divisor (hcop : Nat.Coprime S.n S.p.natDegree) (F : C⟮S.x⟯⟮S.y⟯) (hF0 : F ≠ 0)
    (hint : S.IsIntegralS K F) (B : ℤ) (hinf : -B ≤ S.ordInf K F) (T : Finset (K × K))
    (hT : ∀ Q ∈ T, Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1) (e : K × K → ℤ)
    (he : ∀ Q ∈ T, e Q ≤ S.ordAt K F Q.1 Q.2) (hsum : ∑ Q ∈ T, e Q = B) :
    (∀ Q ∈ T, S.ordAt K F Q.1 Q.2 = e Q) ∧
      (∀ a b : K, b ^ S.n = (S.p.map (algebraMap C K)).eval a → (a, b) ∉ T →
        S.ordAt K F a b = 0) ∧ S.ordInf K F = -B := by
  classical
  have h1 := S.degree_le' K hcop F hF0 hint T hT
  have hle : ∑ Q ∈ T, e Q ≤ ∑ Q ∈ T, S.ordAt K F Q.1 Q.2 := Finset.sum_le_sum he
  have heq : ∑ Q ∈ T, e Q = ∑ Q ∈ T, S.ordAt K F Q.1 Q.2 := by linarith
  refine ⟨fun Q hQ ↦ ((Finset.sum_eq_sum_iff_of_le he).mp heq Q hQ).symm, fun a b hv hn ↦ ?_,
    by linarith⟩
  have h2 := S.degree_le' K hcop F hF0 hint (insert (a, b) T) (by
    intro Q hQ
    rcases Finset.mem_insert.mp hQ with rfl | hQ
    exacts [hv, hT Q hQ])
  rw [Finset.sum_insert hn] at h2
  linarith [hint a b hv]

/-- The norm of a non-zero function is non-zero. -/
theorem resN_ne_zero (hcop : Nat.Coprime S.n S.p.natDegree) (ζ : K) (hζ : IsPrimitiveRoot ζ S.n)
    (ψ : C[X][X]) (hψ : ψ.natDegree < S.n) (hψ0 : S.elemW ψ ≠ 0) : resN S.p S.n ψ ≠ 0 := by
  obtain ⟨lam, hlam, hlp⟩ := S.exists_lam (K := K)
  set Y := S.infY lam hlam hlp
  have hY := S.infY_pow lam hlam hlp
  have h := S.subst_resN (infSub S.n) (infSub_injective S.n S.hn) _ (infSub_eq_eval S.n) ζ hζ ψ hψ
    Y hY
  have hne : ∀ k ∈ Finset.range S.n, S.embG (infSub S.n) (infSub_injective S.n S.hn)
      (HahnSeries.C (ζ ^ k) * Y) (by rw [mul_pow, ← map_pow, ← pow_mul, mul_comm k, pow_mul,
        hζ.pow_eq_one, one_pow, map_one, one_mul, hY]) (S.elemW ψ) ≠ 0 := fun k _ ↦
    (map_ne_zero_iff _ (RingHom.injective _)).mpr hψ0
  intro h0
  rw [h0, map_zero] at h
  exact (Finset.prod_ne_zero_iff.mpr hne) h.symm

lemma cst_eq_polyX (c : C) : S.cst c = S.polyX (Polynomial.C c) :=
  Subtype.ext (by rw [S.polyX_coe, aeval_C]; rfl)

/-- The order of `∏ (x − c_j)^{m_j}` at a point above `c_q`. -/
lemma ordAt_polyX_prod_at {r : ℕ} (c : Fin r → C) (hc : Function.Injective c) (m : Fin r → ℕ)
    (q : Fin r) (b : K) (hv : b ^ S.n = (S.p.map (algebraMap C K)).eval (algebraMap C K (c q)))
    (hb : b ≠ 0) :
    S.ordAt K (S.polyX (∏ j, (X - Polynomial.C (c j)) ^ m j)) (algebraMap C K (c q)) b = m q := by
  classical
  rw [S.ordAt_polyX_prod _ _ _ _ _ hv, Finset.sum_eq_single q]
  · rw [S.ordAt_polyX_lin _ _ _ hv, if_pos rfl, if_neg hb, mul_one]
  · intro q' _ hq'
    rw [S.ordAt_polyX_lin _ _ _ hv,
      if_neg (fun h ↦ hq' (hc ((algebraMap C K).injective h)).symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ q) h

/-- The order of `∏ (x − c_j)^{m_j}` away from the `c_j`. -/
lemma ordAt_polyX_prod_off {r : ℕ} (c : Fin r → C) (m : Fin r → ℕ) (a b : K)
    (hv : b ^ S.n = (S.p.map (algebraMap C K)).eval a) (ha : ∀ j, a ≠ algebraMap C K (c j)) :
    S.ordAt K (S.polyX (∏ j, (X - Polynomial.C (c j)) ^ m j)) a b = 0 := by
  classical
  rw [S.ordAt_polyX_prod _ _ _ _ _ hv]
  exact Finset.sum_eq_zero fun j _ ↦ by rw [S.ordAt_polyX_lin _ _ _ hv, if_neg (ha j), mul_zero]

open Classical in
/-- **The norm of the reduced auxiliary function.** In the situation of `structure_k`, with
`ψ G = c ∏(x − xᵢ) ∏(x − α_q)^{m_q}`, the norm of `ψ` is `λ ∏(x − α_q)^{(n−1) m_q} ∏(x − xᵢ)ⁿ`. -/
theorem norm_structure (hcop : Nat.Coprime S.n S.p.natDegree) (ζ : C) (hζ : IsPrimitiveRoot ζ S.n)
    {g r : ℕ} (x y : Fin g → C) (hx : Function.Injective x) (hy : ∀ i, y i ≠ 0)
    (hyf : ∀ i, y i ^ S.n = S.p.eval (x i))
    (α β : Fin r → C) (mq : Fin r → ℕ) (hP : Function.Injective fun q ↦ (α q, β q))
    (hβ : ∀ q, β q ≠ 0) (hβf : ∀ q, β q ^ S.n = S.p.eval (α q)) (hαx : ∀ q i, α q ≠ x i)
    (G : C⟮S.x⟯⟮S.y⟯) (hG0 : G ≠ 0) (hGint : S.IsIntegralS K G)
    (hG : ∀ q, S.ordAt K G (algebraMap C K (α q)) (algebraMap C K (β q)) = mq q)
    (hGz : ∀ a b : K, b ^ S.n = (S.p.map (algebraMap C K)).eval a →
      (∀ q, (a, b) ≠ (algebraMap C K (α q), algebraMap C K (β q))) → S.ordAt K G a b = 0)
    (ψ : C[X][X]) (hψn : ψ.natDegree < S.n) (hψ0 : S.elemW ψ ≠ 0) (c : C) (hc : c ≠ 0)
    (hstr : S.elemW ψ * G = S.cst c * (S.polyX (∏ i, (X - Polynomial.C (x i))) *
      S.polyX (∏ q, (X - Polynomial.C (α q)) ^ mq q))) :
    resN S.p S.n ψ = Polynomial.C (resN S.p S.n ψ).leadingCoeff *
      ((∏ q, (X - Polynomial.C (α q)) ^ ((S.n - 1) * mq q)) *
        ∏ i, (X - Polynomial.C (x i)) ^ S.n) := by
  set ι := algebraMap C K with hι_def
  have hιi : Function.Injective ι := ι.injective
  have hζK : IsPrimitiveRoot (ι ζ) S.n := hζ.map_of_injective hιi
  have hpt : ∀ c d : C, d ^ S.n = S.p.eval c → ∀ k,
      (ι ζ ^ k * ι d) ^ S.n = (S.p.map ι).eval (ι c) := fun c d h k ↦ by
    rw [← map_pow, ← map_mul, ← map_pow, mul_pow, ← pow_mul, mul_comm k, pow_mul, hζ.pow_eq_one,
      one_pow, one_mul, h, eval_map, eval₂_hom]
  have hpt0 : ∀ c d : C, d ^ S.n = S.p.eval c → (ι d) ^ S.n = (S.p.map ι).eval (ι c) :=
    fun c d h ↦ by simpa using hpt c d h 0
  have hbne : ∀ d : C, d ≠ 0 → ∀ k, ι ζ ^ k * ι d ≠ 0 := fun d hd k ↦
    mul_ne_zero (pow_ne_zero _ (hζK.ne_zero S.hn.ne')) ((map_ne_zero_iff _ hιi).mpr hd)
  set U : C[X] := ∏ i, (X - Polynomial.C (x i)) with hU_def
  set Wb : C[X] := ∏ q, (X - Polynomial.C (α q)) ^ mq q with hWb_def
  have hU : U ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ X_sub_C_ne_zero _
  have hWb : Wb ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
  have hpU := S.polyX_ne_zero hU
  have hpW := S.polyX_ne_zero hWb
  have hUe : U = ∏ i, (X - Polynomial.C (x i)) ^ (fun _ : Fin g ↦ 1) i := by simp [U]
  have hC0 : Polynomial.C c ≠ 0 := C_ne_zero.mpr hc
  have hptinj : Function.Injective fun q ↦ (ι (α q), ι (β q)) := fun q q' h ↦ by
    have h1 := Prod.ext_iff.mp h
    exact hP (Prod.ext (hιi h1.1) (hιi h1.2))
  set Ψ := S.elemW ψ with hΨ_def
  have hΨo : ∀ a b : K, b ^ S.n = (S.p.map ι).eval a →
      S.ordAt K Ψ a b = S.ordAt K (S.polyX U) a b + S.ordAt K (S.polyX Wb) a b -
        S.ordAt K G a b := by
    intro a b hv
    have h : S.ordAt K (Ψ * G) a b = S.ordAt K (S.cst c * (S.polyX U * S.polyX Wb)) a b := by
      rw [hstr]
    rw [S.ordAt_mul hv hψ0 hG0, S.cst_eq_polyX,
      S.ordAt_mul hv (S.polyX_ne_zero hC0) (mul_ne_zero hpU hpW), S.ordAt_mul hv hpU hpW,
      S.ordAt_polyX _ hC0 a b hv, Polynomial.map_C, rootMultiplicity_C] at h
    push_cast at h
    linarith
  have hWo : ∀ a b : K, b ^ S.n = (S.p.map ι).eval a → b ≠ 0 →
      S.ordAt K (S.polyX Wb) a b = ((∑ q, if ι (α q) = a then mq q else 0 : ℕ) : ℤ) := by
    intro a b hv hb
    rw [hWb_def, S.ordAt_polyX_prod _ _ _ _ _ hv]
    push_cast
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [S.ordAt_polyX_lin _ _ _ hv, if_neg hb]
    by_cases h : a = ι (α q)
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  have hUo : ∀ a b : K, b ^ S.n = (S.p.map ι).eval a → b ≠ 0 →
      S.ordAt K (S.polyX U) a b = ((∑ i, if ι (x i) = a then 1 else 0 : ℕ) : ℤ) := by
    intro a b hv hb
    rw [hUe, S.ordAt_polyX_prod _ _ _ _ _ hv]
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [S.ordAt_polyX_lin _ _ _ hv, if_neg hb]
    by_cases h : a = ι (x i)
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  have hGpt : ∀ a b : K, b ^ S.n = (S.p.map ι).eval a →
      S.ordAt K G a b = ((∑ q, if ι (α q) = a ∧ ι (β q) = b then mq q else 0 : ℕ) : ℤ) := by
    intro a b hv
    by_cases hA : ∃ q, (a, b) = (ι (α q), ι (β q))
    · obtain ⟨q0, hq0⟩ := hA
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hq0
      rw [hG q0, Finset.sum_eq_single q0 (fun q _ hq ↦ if_neg fun h ↦ hq (hptinj
        (Prod.ext h.1 h.2))) (fun h ↦ absurd (Finset.mem_univ q0) h), if_pos ⟨rfl, rfl⟩]
    · push_neg at hA
      rw [hGz a b hv hA, Finset.sum_eq_zero fun q _ ↦ if_neg fun h ↦ hA q (by rw [h.1, h.2])]
      simp
  -- the order at infinity
  obtain ⟨φ, hφ⟩ := S.ordInf_hom (K := K) hcop
  have hGinf : S.ordInf K G = -(∑ q, mq q : ℕ) := by
    set T : Finset (K × K) := Finset.univ.image fun q ↦ (ι (α q), ι (β q))
    have hT : ∀ Q ∈ T, Q.2 ^ S.n = (S.p.map ι).eval Q.1 := by
      intro Q hQ
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hQ
      exact hpt0 _ _ (hβf q)
    have h := S.degree_eq' K hcop G hG0 hGint T hT fun a b hv hn ↦
      hGz a b hv fun q h ↦ hn (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, h.symm⟩)
    rw [Finset.sum_image fun q _ q' _ h ↦ hptinj h] at h
    simp only [hG] at h
    push_cast
    linarith
  have hdegW : Wb.natDegree = ∑ q, mq q := by
    rw [hWb_def, natDegree_prod _ _ fun q _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)]
    simp [natDegree_pow]
  have hdegU : U.natDegree = g := by
    rw [hU_def, natDegree_prod _ _ fun q _ ↦ X_sub_C_ne_zero _]
    simp
  have hΨinf : S.ordInf K Ψ = -(S.n * g + S.n * (∑ q, mq q : ℕ) - (∑ q, mq q : ℕ) : ℤ) := by
    have h := congrArg (S.ordInf K) hstr
    rw [S.ordInf_mul hcop hψ0 hG0, S.cst_eq_polyX,
      S.ordInf_mul hcop (S.polyX_ne_zero hC0) (mul_ne_zero hpU hpW), S.ordInf_mul hcop hpU hpW,
      S.ordInf_polyX hcop _ hC0, S.ordInf_polyX hcop _ hU, S.ordInf_polyX hcop _ hWb, hdegU, hdegW,
      natDegree_C, hGinf] at h
    push_cast at h ⊢
    linarith
  have hN0 := S.resN_ne_zero hcop (ι ζ) hζK ψ hψn hψ0
  have hNdeg := S.natDegree_resN hcop (ι ζ) hζK ψ hψn hψ0
  -- the target polynomial
  set Q : C[X] := (∏ q, (X - Polynomial.C (α q)) ^ ((S.n - 1) * mq q)) *
    ∏ i, (X - Polynomial.C (x i)) ^ S.n with hQ_def
  have hQm : Q.Monic := (monic_prod_of_monic _ _ fun q _ ↦ (monic_X_sub_C _).pow _).mul
    (monic_prod_of_monic _ _ fun i _ ↦ (monic_X_sub_C _).pow _)
  have hQdeg : Q.natDegree = (S.n - 1) * (∑ q, mq q) + S.n * g := by
    rw [hQ_def, natDegree_mul
      (Finset.prod_ne_zero_iff.mpr fun q _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _))
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)),
      natDegree_prod _ _ fun q _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _),
      natDegree_prod _ _ fun q _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)]
    simp [natDegree_pow, mul_comm, Finset.sum_mul]
  have hNK0 : (resN S.p S.n ψ).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιi).mpr hN0
  have hQK0 : Q.map ι ≠ 0 := (hQm.map ι).ne_zero
  have hQmap : Q.map ι = (∏ q, (X - Polynomial.C (ι (α q))) ^ ((S.n - 1) * mq q)) *
      ∏ i, (X - Polynomial.C (ι (x i))) ^ S.n := by
    simp [Q, Polynomial.map_mul, Polynomial.map_prod]
  obtain ⟨n', hn'⟩ : ∃ n', S.n = n' + 1 := ⟨S.n - 1, by have := S.hn; omega⟩
  have hdvdK : Q.map ι ∣ (resN S.p S.n ψ).map ι := by
    rw [IsAlgClosed.dvd_iff_roots_le_roots hQK0 hNK0, Multiset.le_iff_count]
    intro a
    rw [hQmap, roots_mul (by rw [← hQmap]; exact hQK0), Multiset.count_add,
      Sup.count_roots_prod_pow, Sup.count_roots_prod_pow, count_roots]
    -- lower bound for the root multiplicity of the norm at `a`
    by_cases hA : ∃ q, ι (α q) = a
    · obtain ⟨q0, rfl⟩ := hA
      have hx0 : (∑ i, if ι (x i) = ι (α q0) then S.n else 0) = 0 :=
        Finset.sum_eq_zero fun i _ ↦ if_neg fun h ↦ hαx q0 i (hιi h).symm
      rw [hx0, add_zero]
      have hb := (map_ne_zero_iff _ hιi).mpr (hβ q0)
      have hv := hpt0 _ _ (hβf q0)
      have h := S.rootMult_resN (ι ζ) hζK ψ hψn hψ0 (ι (α q0)) (ι (β q0)) hb hv
      have hk : ∀ k ∈ Finset.range S.n, S.ordAt K Ψ (ι (α q0)) (ι ζ ^ k * ι (β q0)) =
          ((∑ q, if ι (α q) = ι (α q0) then mq q else 0 : ℕ) : ℤ) -
            ((∑ q, if ι (α q) = ι (α q0) ∧ ι (β q) = ι ζ ^ k * ι (β q0) then mq q else 0 : ℕ) :
              ℤ) := by
        intro k _
        have hvk := hpt _ _ (hβf q0) k
        rw [hΨo _ _ hvk, hUo _ _ hvk (hbne _ (hβ q0) k), hWo _ _ hvk (hbne _ (hβ q0) k),
          hGpt _ _ hvk, Finset.sum_eq_zero fun i _ ↦ if_neg fun h ↦ hαx q0 i (hιi h).symm]
        simp
      rw [Finset.sum_congr rfl hk, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
        at h
      have hfib := Sup.fiber_sum S.hn (ι ζ) hζK (fun q ↦ ι (α q)) (fun q ↦ ι (β q)) mq
        (ι (α q0)) (ι (β q0)) hb (fun q hq ↦ by rw [hpt0 _ _ (hβf q), hq, hv])
      have hfib' : (∑ k ∈ Finset.range S.n, ((∑ q, if ι (α q) = ι (α q0) ∧
          ι (β q) = ι ζ ^ k * ι (β q0) then mq q else 0 : ℕ) : ℤ)) =
          ((∑ q, if ι (α q) = ι (α q0) then mq q else 0 : ℕ) : ℤ) := by
        rw [← hfib]; push_cast; rfl
      rw [hfib', nsmul_eq_mul] at h
      have hsum : (∑ q, if ι (α q) = ι (α q0) then (S.n - 1) * mq q else 0) =
          (S.n - 1) * ∑ q, if ι (α q) = ι (α q0) then mq q else 0 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ ↦ by split_ifs <;> simp
      rw [hsum]
      have h2 : (((S.n - 1) * ∑ q, if ι (α q) = ι (α q0) then mq q else 0 : ℕ) : ℤ) =
          ((((resN S.p S.n ψ).map ι).rootMultiplicity (ι (α q0)) : ℕ) : ℤ) := by
        rw [h, hn']; push_cast; ring
      exact_mod_cast h2.le
    · push_neg at hA
      have hα0 : (∑ q, if ι (α q) = a then (S.n - 1) * mq q else 0) = 0 :=
        Finset.sum_eq_zero fun q _ ↦ if_neg (hA q)
      rw [hα0, zero_add]
      by_cases hB : ∃ i, ι (x i) = a
      · obtain ⟨i0, rfl⟩ := hB
        have hb := (map_ne_zero_iff _ hιi).mpr (hy i0)
        have hv := hpt0 _ _ (hyf i0)
        have h := S.rootMult_resN (ι ζ) hζK ψ hψn hψ0 (ι (x i0)) (ι (y i0)) hb hv
        have hk : ∀ k ∈ Finset.range S.n,
            S.ordAt K Ψ (ι (x i0)) (ι ζ ^ k * ι (y i0)) = 1 := by
          intro k _
          have hvk := hpt _ _ (hyf i0) k
          rw [hΨo _ _ hvk, hUo _ _ hvk (hbne _ (hy i0) k), hWo _ _ hvk (hbne _ (hy i0) k),
            hGpt _ _ hvk, Finset.sum_eq_single i0 (fun i _ hi ↦ if_neg fun h ↦ hi (hx (hιi h)))
              (fun h ↦ absurd (Finset.mem_univ i0) h), if_pos rfl,
            Finset.sum_eq_zero fun q _ ↦ if_neg fun h ↦ hA q h,
            Finset.sum_eq_zero fun q _ ↦ if_neg fun h ↦ hA q h.1]
          simp
        rw [Finset.sum_congr rfl hk, Finset.sum_const, Finset.card_range] at h
        rw [Finset.sum_eq_single i0 (fun i _ hi ↦ if_neg fun h ↦ hi (hx (hιi h)))
          (fun h ↦ absurd (Finset.mem_univ i0) h), if_pos rfl]
        have h2 : ((S.n : ℕ) : ℤ) = ((((resN S.p S.n ψ).map ι).rootMultiplicity (ι (x i0)) : ℕ) : ℤ) := by
          rw [h]; simp
        exact_mod_cast h2.le
      · push_neg at hB
        rw [Finset.sum_eq_zero fun i _ ↦ if_neg (hB i)]
        exact Nat.zero_le _
  have hdvd : Q ∣ resN S.p S.n ψ := (Polynomial.map_dvd_map ι hιi hQm).mp hdvdK
  refine Sup.eq_C_mul_of_dvd hQm hN0 hdvd ?_
  have h1 : ((resN S.p S.n ψ).natDegree : ℤ) = (Q.natDegree : ℤ) := by
    rw [hNdeg, hΨinf, hQdeg, hn']
    push_cast
    ring
  exact_mod_cast h1.le

open Classical in
/-- **Exact divisors on unions of fibres.** An integral function with order `≥ ∑_{A_q = a,
B_q ≠ b} m_q` at every point `(a, b)` and pole order `≤ (n − 1) ∑ m_q` has exactly these orders. -/
theorem exact_fiber_divisor (hcop : Nat.Coprime S.n S.p.natDegree) (ζ : K)
    (hζ : IsPrimitiveRoot ζ S.n) {r : ℕ} (A B : Fin r → K) (mq : Fin r → ℕ)
    (hB : ∀ q, B q ≠ 0) (hAB : ∀ q, B q ^ S.n = (S.p.map (algebraMap C K)).eval (A q))
    (F : C⟮S.x⟯⟮S.y⟯) (hF0 : F ≠ 0) (hint : S.IsIntegralS K F)
    (hle : ∀ a b : K, b ^ S.n = (S.p.map (algebraMap C K)).eval a →
      ((∑ q, if A q = a ∧ ¬ B q = b then mq q else 0 : ℕ) : ℤ) ≤ S.ordAt K F a b)
    (hinf : -(((S.n - 1) * ∑ q, mq q : ℕ) : ℤ) ≤ S.ordInf K F) :
    (∀ a b : K, b ^ S.n = (S.p.map (algebraMap C K)).eval a →
      S.ordAt K F a b = ((∑ q, if A q = a ∧ ¬ B q = b then mq q else 0 : ℕ) : ℤ)) ∧
      S.ordInf K F = -(((S.n - 1) * ∑ q, mq q : ℕ) : ℤ) := by
  set e : K × K → ℤ := fun Q ↦ ((∑ q, if A q = Q.1 ∧ ¬ B q = Q.2 then mq q else 0 : ℕ) : ℤ)
    with he_def
  set T : Finset (K × K) := (Finset.univ ×ˢ Finset.range S.n).image
    fun p : Fin r × ℕ ↦ (A p.1, ζ ^ p.2 * B p.1) with hT_def
  have hTv : ∀ Q ∈ T, Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1 := by
    intro Q hQ
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hQ
    show (ζ ^ p.2 * B p.1) ^ S.n = _
    rw [mul_pow, ← pow_mul, mul_comm p.2, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hAB]
  -- every point over some `A q` lies in `T`
  have hfib : ∀ q (b : K), b ^ S.n = (S.p.map (algebraMap C K)).eval (A q) → (A q, b) ∈ T := by
    intro q b hv
    obtain ⟨k, hk, hbk⟩ := S.root_point ζ hζ (B q) b (hB q) (by rw [hv, hAB])
    exact Finset.mem_image.mpr ⟨(q, k), Finset.mem_product.mpr ⟨Finset.mem_univ _,
      Finset.mem_range.mpr hk⟩, by rw [hbk]⟩
  -- the fibre over `A q` inside `T` has `n` points
  have hcard : ∀ q, (T.filter fun Q ↦ Q.1 = A q).card = S.n := by
    intro q
    have heq : T.filter (fun Q ↦ Q.1 = A q) =
        (Finset.range S.n).image fun k ↦ (A q, ζ ^ k * B q) := by
      ext Q
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hQ, hQ1⟩
        obtain ⟨Q1, Q2⟩ := Q
        simp only at hQ1
        subst hQ1
        obtain ⟨k, hk, hbk⟩ := S.root_point ζ hζ (B q) Q2 (hB q) (by rw [hTv _ hQ, hAB])
        exact ⟨k, hk, by rw [hbk]⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨Finset.mem_image.mpr ⟨(q, k), Finset.mem_product.mpr ⟨Finset.mem_univ _,
          Finset.mem_range.mpr hk⟩, rfl⟩, rfl⟩
    rw [heq, Finset.card_image_of_injOn, Finset.card_range]
    intro k hk k' hk' h
    have h2 := (Prod.ext_iff.mp h).2
    exact hζ.pow_inj (Finset.mem_range.mp hk) (Finset.mem_range.mp hk')
      (mul_right_cancel₀ (hB q) h2)
  have hsum : ∑ Q ∈ T, e Q = (((S.n - 1) * ∑ q, mq q : ℕ) : ℤ) := by
    simp only [he_def]
    rw [← Nat.cast_sum, Finset.sum_comm]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    congr 1
    have hpq : (A q, B q) ∈ T.filter (fun Q ↦ Q.1 = A q) :=
      Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(q, 0), Finset.mem_product.mpr
        ⟨Finset.mem_univ _, Finset.mem_range.mpr S.hn⟩, by simp⟩, rfl⟩
    have e1 : T.filter (fun Q ↦ A q = Q.1 ∧ ¬ B q = Q.2) =
        (T.filter fun Q ↦ Q.1 = A q).erase (A q, B q) := by
      ext Q
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hQ, h1, h2⟩
        exact ⟨fun h ↦ h2 (by rw [h]), hQ, h1.symm⟩
      · rintro ⟨hne, hQ, h1⟩
        exact ⟨hQ, h1.symm, fun h2 ↦ hne (Prod.ext h1 h2.symm)⟩
    rw [e1, Finset.card_erase_of_mem hpq, hcard]
  have hle' : ∀ Q ∈ T, e Q ≤ S.ordAt K F Q.1 Q.2 := fun Q hQ ↦ hle Q.1 Q.2 (hTv Q hQ)
  obtain ⟨hT, hoff, hinfF⟩ := S.exact_divisor hcop F hF0 hint _ hinf T hTv e hle' hsum
  refine ⟨fun a b hv ↦ ?_, hinfF⟩
  by_cases hQ : (a, b) ∈ T
  · exact hT _ hQ
  · rw [hoff a b hv hQ]
    symm
    rw [Nat.cast_eq_zero]
    refine Finset.sum_eq_zero fun q _ ↦ if_neg fun h ↦ hQ ?_
    rw [← h.1] at hv ⊢
    exact hfib q b hv

end SuperData

end Differential

