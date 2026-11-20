import RischTragerBronstein.Algebraic.SupNormOrd
import RischTragerBronstein.Algebraic.SupBranchR
import RischTragerBronstein.Algebraic.SuperSecondKind

/-!
# The residual zeros of the auxiliary function, over an algebraically closed field

* `elem_repr`: an integral element with pole order `≤ M` at infinity is `∑ Wᵢ(x) yⁱ` with
  `n deg Wᵢ + d i ≤ M`;
* `vanish1_iff`: `W` vanishes at an ordinary point iff its value there is `0`;
* `structure_k`: under the non-speciality hypothesis, the auxiliary function `Ψ` has exactly the
  prescribed zeros: `Ψ G = c ∏(x − xᵢ) ∏(x − α_q)^{m_q}`.
-/

open Polynomial IntermediateField HahnSeries

namespace Differential

namespace SuperData

open Sup

variable {C L K : Type*} [Field C] [PerfectField C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K] [IsAlgClosed K]

variable (S : SuperData C L)

/-- **Integral elements of bounded pole order are polynomial combinations of `xᵃ yⁱ`.** -/
theorem elem_repr (hcop : Nat.Coprime S.n S.p.natDegree) (w : C⟮S.x⟯⟮S.y⟯) (hw0 : w ≠ 0)
    (hint : S.IsIntegralS K w) (M : ℕ) (hinfM : -(M : ℤ) ≤ S.ordInf K w) :
    ∃ W : C[X][X], S.elemW W = w ∧ W ≠ 0 ∧
      ∀ i a, (W.coeff i).coeff a ≠ 0 → i < S.n ∧ S.n * a + S.p.natDegree * i ≤ M := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  obtain ⟨a, ha, hpoly⟩ := S.integral_of_regular' K w hint
  choose P hP using hpoly
  set W : C[X][X] := ∑ i : Fin S.n, Polynomial.monomial (i : ℕ) (P i)
  have hWc : ∀ i : ℕ, W.coeff i = if h : i < S.n then P ⟨i, h⟩ else 0 := fun i ↦ by
    simp only [W, finsetSum_coeff, coeff_monomial]
    split_ifs with hi
    · rw [Finset.sum_eq_single ⟨i, hi⟩ (fun b _ hb ↦ by
        rw [if_neg (fun h ↦ hb (Fin.ext h))]) (fun h ↦ absurd (Finset.mem_univ _) h), if_pos rfl]
    · exact Finset.sum_eq_zero fun b _ ↦ by rw [if_neg (fun h ↦ hi (by rw [← h]; exact b.2))]
  have hWn : ∀ i, S.n ≤ i → W.coeff i = 0 := fun i hi ↦ by rw [hWc, dif_neg (by omega)]
  have haP : ∀ i, a i = algebraMap C[X] C⟮S.x⟯ (P i) := fun i ↦
    Subtype.ext (by rw [hP i, algebraMap_adjoinSimple])
  have hwW : S.elemW W = w := by
    rw [ha, elemW, ← Fin.sum_univ_eq_sum_range (fun i ↦ S.polyX (W.coeff i) *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ i)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hWc, dif_pos i.2, haP]
    rfl
  have hW0 : W ≠ 0 := fun h0 ↦ hw0 (by rw [← hwW, h0]; simp [elemW, polyX])
  obtain ⟨lam, hlam, hlp⟩ := S.exists_lam (K := K)
  have hinf : ((-(M : ℤ) : ℤ) : WithTop ℤ) ≤
      (S.embI lam hlam hlp (∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) *
        AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ))).orderTop := by
    rw [← ha, ← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero_iff _ (RingHom.injective _)).mpr
      hw0), ← S.ordInf_eq hcop w lam hlam hlp]
    exact WithTop.coe_le_coe.mpr hinfM
  have hb := S.inf_bound hcop lam hlam hlp a _ hinf
  refine ⟨W, hwW, hW0, fun i b hib ↦ ?_⟩
  have hi : i < S.n := by
    by_contra hni
    exact hib (by rw [hWn i (not_lt.mp hni), Polynomial.coeff_zero])
  rw [hWc, dif_pos hi] at hib
  have hPi : P ⟨i, hi⟩ ≠ 0 := fun h0 ↦ hib (by rw [h0, Polynomial.coeff_zero])
  have hai : a ⟨i, hi⟩ ≠ 0 := by
    rw [haP]; exact fun h0 ↦ hPi ((map_eq_zero_iff _ (IsFractionRing.injective C[X] C⟮S.x⟯)).mp h0)
  have h1 := hb ⟨i, hi⟩ hai
  rw [haP, S.embXG_inf_poly _ hPi] at h1
  have hbd : b ≤ (P ⟨i, hi⟩).natDegree := le_natDegree_of_ne_zero hib
  refine ⟨hi, ?_⟩
  have : (S.n : ℤ) * b ≤ S.n * (P ⟨i, hi⟩).natDegree := by
    exact_mod_cast Nat.mul_le_mul_left _ hbd
  have h2 : (S.n : ℤ) * b + S.p.natDegree * i ≤ M := by linarith
  exact_mod_cast h2

omit [IsAlgClosed K] in
/-- **Vanishing to order one at an ordinary point is the vanishing of the value.** -/
theorem vanish1_iff (W : C[X][X]) (hW : W.natDegree < S.n) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    ((1 : ℤ) : WithTop ℤ) ≤ (S.embXY α β hβ hβp (S.elemW W)).orderTop ↔
      evalW (W.map (mapRingHom (algebraMap C K))) α β = 0 := by
  have hWn : ∀ i, S.n ≤ i → W.coeff i = 0 := fun i hi ↦
    coeff_eq_zero_of_natDegree_lt (by omega)
  constructor
  · intro h
    obtain ⟨V, hV, hdv⟩ := S.vanish_of_orderTop_ge α β hβ hβp W hWn 1 (by exact_mod_cast h)
    rw [pow_one, X_dvd_iff, jetN_coeff_zero, hV.1] at hdv
    exact hdv
  · intro h
    have hu := S.unit_branch β hβ
    obtain ⟨V, hV⟩ := exists_branchN _ S.hn hu hβp 0
    have := S.orderTop_ge_of_vanish α β hβ hβp W hWn 1 ⟨V, hV, by
      rw [pow_one, X_dvd_iff, jetN_coeff_zero, hV.1]; exact h⟩
    exact_mod_cast this

/-- A point above `x₀` is `(x₀, ζᵏ y₀)`. -/
lemma root_point (ζ : K) (hζ : IsPrimitiveRoot ζ S.n) (y₀ b : K) (hy : y₀ ≠ 0)
    (h : b ^ S.n = y₀ ^ S.n) : ∃ k < S.n, b = ζ ^ k * y₀ := by
  haveI : NeZero S.n := ⟨S.hn.ne'⟩
  obtain ⟨k, hk, hkx⟩ := hζ.eq_pow_of_pow_eq_one (ξ := b / y₀) (by
    rw [div_pow, h, div_self (pow_ne_zero _ hy)])
  exact ⟨k, hk, by rw [hkx, div_mul_cancel₀ _ hy]⟩

open Classical in
/-- The order of a linear polynomial `x − c`. -/
lemma ordAt_polyX_lin (c : C) (a b : K) (hv : b ^ S.n = (S.p.map (algebraMap C K)).eval a) :
    S.ordAt K (S.polyX (X - Polynomial.C c)) a b =
      if a = algebraMap C K c then (if b = 0 then (S.n : ℤ) else 1) else 0 := by
  rw [S.ordAt_polyX _ (X_sub_C_ne_zero c) a b hv, Polynomial.map_sub, map_X, Polynomial.map_C,
    rootMultiplicity_X_sub_C]
  split_ifs <;> simp

/-- The order of a product of powers of linear polynomials. -/
lemma ordAt_polyX_prod {ι : Type*} (s : Finset ι) (c : ι → C) (m : ι → ℕ) (a b : K)
    (hv : b ^ S.n = (S.p.map (algebraMap C K)).eval a) :
    S.ordAt K (S.polyX (∏ i ∈ s, (X - Polynomial.C (c i)) ^ m i)) a b =
      ∑ i ∈ s, (m i : ℤ) * S.ordAt K (S.polyX (X - Polynomial.C (c i))) a b := by
  have hprod : S.polyX (∏ i ∈ s, (X - Polynomial.C (c i)) ^ m i) =
      ∏ i ∈ s, S.polyX (X - Polynomial.C (c i)) ^ m i := by
    simp only [polyX, map_prod, map_pow]
  rw [hprod, S.ordAt_prod hv _ _ fun i _ ↦ pow_ne_zero _ (S.polyX_ne_zero (X_sub_C_ne_zero _))]
  exact Finset.sum_congr rfl fun i _ ↦ S.ordAt_pow hv _ _

/-- Splitting a sum along a second condition. -/
lemma sum_ite_split {ι : Type*} (s : Finset ι) (A B : ι → Prop) [DecidablePred A]
    [∀ q, Decidable (A q ∧ B q)] [∀ q, Decidable (A q ∧ ¬ B q)] (m : ι → ℕ) :
    (∑ q ∈ s, if A q then m q else 0) =
      (∑ q ∈ s, if A q ∧ B q then m q else 0) + ∑ q ∈ s, if A q ∧ ¬ B q then m q else 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  by_cases hA : A q <;> by_cases hB : B q <;> simp [hA, hB]

open Classical in
/-- **The structure of the auxiliary function over an algebraically closed field.** Let `G` have
divisor exactly `Γ − (deg Γ) ∞` (`Γ = ∑ m_q (α_q, β_q)`, distinct non-branch points, possibly in
the same fibres), and let `Ψ` (pole order `≤ M`, `M = (n−1)(deg Γ + g) + g`) vanish on
`∑_q m_q (F_q − P_q)` (`F_q` the fibre over `α_q`, i.e. order `≥ ∑_{α_q = a, β_q ≠ b} m_q` at
`(a, b)`) and at the `(xᵢ, ζᵏyᵢ)`, `k ≠ 0`. If the base points `(xᵢ, yᵢ)` are non-special
(`hNS`), then `Ψ G = c ∏(x − xᵢ) ∏(x − α_q)^{m_q}`. -/
theorem structure_k (hcop : Nat.Coprime S.n S.p.natDegree) (ζ : C) (hζ : IsPrimitiveRoot ζ S.n)
    {g r : ℕ} (x y : Fin g → C) (hx : Function.Injective x) (hy : ∀ i, y i ≠ 0)
    (hyf : ∀ i, y i ^ S.n = S.p.eval (x i))
    (α β : Fin r → C) (mq : Fin r → ℕ) (hP : Function.Injective fun q ↦ (α q, β q))
    (hβ : ∀ q, β q ≠ 0) (hβf : ∀ q, β q ^ S.n = S.p.eval (α q)) (hαx : ∀ q i, α q ≠ x i)
    (G : C⟮S.x⟯⟮S.y⟯) (hG0 : G ≠ 0) (hGint : S.IsIntegralS K G)
    (hG : ∀ q, S.ordAt K G (algebraMap C K (α q)) (algebraMap C K (β q)) = mq q)
    (hGz : ∀ a b : K, b ^ S.n = (S.p.map (algebraMap C K)).eval a →
      (∀ q, (a, b) ≠ (algebraMap C K (α q), algebraMap C K (β q))) → S.ordAt K G a b = 0)
    (Ψ : C⟮S.x⟯⟮S.y⟯) (hΨ0 : Ψ ≠ 0) (hΨint : S.IsIntegralS K Ψ)
    (hΨinf : -(((S.n - 1) * (∑ q, mq q + g) + g : ℕ) : ℤ) ≤ S.ordInf K Ψ)
    (hΨΓ : ∀ a b : K, b ^ S.n = (S.p.map (algebraMap C K)).eval a →
      ((∑ q, if algebraMap C K (α q) = a ∧ ¬ algebraMap C K (β q) = b then mq q else 0 : ℕ) : ℤ) ≤
        S.ordAt K Ψ a b)
    (hΨE : ∀ i k, 1 ≤ k → k < S.n →
      1 ≤ S.ordAt K Ψ (algebraMap C K (x i)) (algebraMap C K (ζ ^ k * y i)))
    (hNS : ∀ V : C⟮S.x⟯⟮S.y⟯, V ≠ 0 → S.IsIntegralS K V → -((S.n * g : ℕ) : ℤ) ≤ S.ordInf K V →
      (∀ i k, 1 ≤ k → k < S.n →
        1 ≤ S.ordAt K V (algebraMap C K (x i)) (algebraMap C K (ζ ^ k * y i))) →
      ∀ i, 1 ≤ S.ordAt K V (algebraMap C K (x i)) (algebraMap C K (y i))) :
    ∃ c : C, c ≠ 0 ∧ Ψ * G = S.cst c * (S.polyX (∏ i, (X - Polynomial.C (x i))) *
      S.polyX (∏ q, (X - Polynomial.C (α q)) ^ mq q)) := by
  set ι := algebraMap C K with hι_def
  have hιi : Function.Injective ι := ι.injective
  have hζK : IsPrimitiveRoot (ι ζ) S.n := hζ.map_of_injective hιi
  have hpt : ∀ c d : C, d ^ S.n = S.p.eval c → ∀ k,
      (ι (ζ ^ k * d)) ^ S.n = (S.p.map ι).eval (ι c) := fun c d h k ↦ by
    rw [← map_pow, mul_pow, ← pow_mul, mul_comm k, pow_mul, hζ.pow_eq_one, one_pow, one_mul, h,
      eval_map, eval₂_hom]
  have hpt0 : ∀ c d : C, d ^ S.n = S.p.eval c → (ι d) ^ S.n = (S.p.map ι).eval (ι c) :=
    fun c d h ↦ by simpa using hpt c d h 0
  set U : C[X] := ∏ i, (X - Polynomial.C (x i)) with hU_def
  set Wb : C[X] := ∏ q, (X - Polynomial.C (α q)) ^ mq q with hWb_def
  have hU : U ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ X_sub_C_ne_zero _
  have hWb : Wb ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
  have hpU := S.polyX_ne_zero hU
  have hpW := S.polyX_ne_zero hWb
  have hUe : U = ∏ i ∈ Finset.univ, (X - Polynomial.C (x i)) ^ (fun _ : Fin g ↦ 1) i := by
    simp [U]
  -- orders of `U` and `Wb`
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
  have hWbX : ∀ a b : K, b ^ S.n = (S.p.map ι).eval a → (∀ q, a ≠ ι (α q)) →
      S.ordAt K (S.polyX Wb) a b = 0 := by
    intro a b hv ha
    rw [hWb_def, S.ordAt_polyX_prod _ _ _ _ _ hv]
    exact Finset.sum_eq_zero fun q _ ↦ by rw [S.ordAt_polyX_lin _ _ _ hv, if_neg (ha q), mul_zero]
  have hUX : ∀ i (b : K), b ^ S.n = (S.p.map ι).eval (ι (x i)) → b ≠ 0 →
      S.ordAt K (S.polyX U) (ι (x i)) b = 1 := by
    intro i b hv hb
    rw [hUe, S.ordAt_polyX_prod _ _ _ _ _ hv, Finset.sum_eq_single i]
    · rw [S.ordAt_polyX_lin _ _ _ hv, if_pos rfl, if_neg hb]; simp
    · intro i' _ hi'
      rw [S.ordAt_polyX_lin _ _ _ hv, if_neg (fun h ↦ hi' (hx (hιi h)).symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hUA : ∀ a b : K, b ^ S.n = (S.p.map ι).eval a → (∀ i, a ≠ ι (x i)) →
      S.ordAt K (S.polyX U) a b = 0 := by
    intro a b hv ha
    rw [hUe, S.ordAt_polyX_prod _ _ _ _ _ hv]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [S.ordAt_polyX_lin _ _ _ hv, if_neg (ha i), mul_zero]
  have hptinj : Function.Injective fun q ↦ (ι (α q), ι (β q)) := fun q q' h ↦ by
    have h1 := Prod.ext_iff.mp h
    exact hP (Prod.ext (hιi h1.1) (hιi h1.2))
  -- the divisor of `G`
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
  -- the auxiliary functions
  set V := Ψ * G * (S.polyX Wb)⁻¹ with hV_def
  set Φ := V * (S.polyX U)⁻¹ with hΦ_def
  have hV0 : V ≠ 0 := mul_ne_zero (mul_ne_zero hΨ0 hG0) (inv_ne_zero hpW)
  have hΦ0 : Φ ≠ 0 := mul_ne_zero hV0 (inv_ne_zero hpU)
  have hVo : ∀ a b : K, b ^ S.n = (S.p.map ι).eval a →
      S.ordAt K V a b = S.ordAt K Ψ a b + S.ordAt K G a b - S.ordAt K (S.polyX Wb) a b := by
    intro a b hv
    rw [hV_def, S.ordAt_mul hv (mul_ne_zero hΨ0 hG0) (inv_ne_zero hpW), S.ordAt_mul hv hΨ0 hG0,
      S.ordAt_inv hv]
    ring
  have hΦo : ∀ a b : K, b ^ S.n = (S.p.map ι).eval a →
      S.ordAt K Φ a b = S.ordAt K V a b - S.ordAt K (S.polyX U) a b := by
    intro a b hv
    rw [hΦ_def, S.ordAt_mul hv hV0 (inv_ne_zero hpU), S.ordAt_inv hv]
    ring
  -- `V` is integral, and vanishes on the conjugates of the base points
  have hVint : S.IsIntegralS K V := by
    intro a b hv
    rw [hVo a b hv]
    have h1 := hΨint a b hv
    have h2 := hGint a b hv
    by_cases hb : b = 0
    · have hα' : ∀ q, a ≠ ι (α q) := by
        intro q ha
        have : (S.p.map ι).eval a = 0 := by rw [← hv, hb, zero_pow S.hn.ne']
        rw [ha, ← hpt0 _ _ (hβf q)] at this
        exact pow_ne_zero _ ((map_ne_zero_iff _ hιi).mpr (hβ q)) this
      rw [hWbX a b hv hα']; linarith
    · have h3 := hΨΓ a b hv
      rw [hWo a b hv hb, hGpt a b hv]
      rw [sum_ite_split Finset.univ (fun q ↦ ι (α q) = a) (fun q ↦ ι (β q) = b) mq]
      push_cast at h3 ⊢
      linarith
  have hV1 : ∀ i k, 1 ≤ k → k < S.n → 1 ≤ S.ordAt K V (ι (x i)) (ι (ζ ^ k * y i)) := by
    intro i k hk1 hk
    have hv := hpt _ _ (hyf i) k
    rw [hVo _ _ hv, hWbX _ _ hv fun q h ↦ hαx q i (hιi h).symm]
    linarith [hΨE i k hk1 hk, hGint _ _ hv]
  -- orders at infinity
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
  have hVinf : S.ordInf K V = S.ordInf K Ψ + S.ordInf K G + S.n * (∑ q, mq q : ℕ) := by
    rw [hV_def, S.ordInf_mul hcop (mul_ne_zero hΨ0 hG0) (inv_ne_zero hpW),
      S.ordInf_mul hcop hΨ0 hG0, hφ (S.polyX Wb)⁻¹, order_hom_inv, ← hφ, S.ordInf_polyX hcop _ hWb,
      hdegW]
    ring
  have hΦinf : S.ordInf K Φ = S.ordInf K V + S.n * g := by
    rw [hΦ_def, S.ordInf_mul hcop hV0 (inv_ne_zero hpU), hφ (S.polyX U)⁻¹, order_hom_inv, ← hφ,
      S.ordInf_polyX hcop _ hU, hdegU]
    ring
  have hVinf' : -((S.n * g : ℕ) : ℤ) ≤ S.ordInf K V := by
    rw [hVinf, hGinf]
    have hn1 : ((S.n - 1 : ℕ) : ℤ) = S.n - 1 := by
      have := S.hn; push_cast [Nat.cast_sub (show 1 ≤ S.n by omega)]; ring
    have := hΨinf
    push_cast [hn1] at this ⊢
    nlinarith
  have hNSi := hNS V hV0 hVint hVinf' hV1
  -- `Φ` has no poles, hence is constant
  have hΦint : S.IsIntegralS K Φ := by
    intro a b hv
    rw [hΦo a b hv]
    have h1 := hVint a b hv
    by_cases hB : ∃ i, a = ι (x i)
    · obtain ⟨i, rfl⟩ := hB
      obtain ⟨k, hk, hbk⟩ := S.root_point (ι ζ) hζK (ι (y i)) b
        ((map_ne_zero_iff _ hιi).mpr (hy i)) (by rw [hv, hpt0 _ _ (hyf i)])
      have hb : b = ι (ζ ^ k * y i) := by rw [hbk, map_mul, map_pow]
      subst hb
      rw [hUX i _ hv ((map_ne_zero_iff _ hιi).mpr
        (mul_ne_zero (pow_ne_zero _ (hζ.ne_zero S.hn.ne')) (hy i)))]
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · have := hNSi i
        rw [pow_zero, one_mul] at *
        linarith
      · linarith [hV1 i k hk1 hk]
    · push_neg at hB
      rw [hUA _ _ hv hB]; linarith
  have hΦinf0 : 0 ≤ S.ordInf K Φ := by
    rw [hΦinf]; push_cast at hVinf'; linarith
  have h0 : ∀ a b : K, b ^ S.n = (S.p.map ι).eval a → S.ordAt K Φ a b = 0 := by
    intro a b hv
    have h := S.degree_le' K hcop Φ hΦ0 hΦint {(a, b)}
      (fun Q hQ ↦ by rw [Finset.mem_singleton.mp hQ]; exact hv)
    rw [Finset.sum_singleton] at h
    linarith [hΦint a b hv]
  obtain ⟨c, hc⟩ := S.const_of_ordAt_zero K hcop Φ hΦ0 h0
  have hΦc : Φ = S.cst c := Subtype.ext hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hΦ0 (by rw [hΦc]; exact Subtype.ext (by simp [cst]))
  refine ⟨c, hc0, ?_⟩
  rw [← hΦc, hΦ_def, hV_def]
  field_simp

end SuperData

end Differential
