import RischTragerBronstein.Algebraic.SupTorsion
import RischTragerBronstein.Algebraic.SuperPrincipalIff

/-!
# Multiples of divisors on superelliptic curves

`PrincipalMulN f n d α β m s`: the divisor `s Γ − (s deg Γ)∞` (`Γ = ∑ m_q (α_q, β_q)`) is
principal, witnessed by `∑ Wᵢ(x) yⁱ` with `n deg + d i ≤ s deg Γ` vanishing to order `s m_q` at each
`(α_q, β_q)`.

* `PrincipalMulN.map`, `principalMulN_descend`: field embeddings (descent through the
  linear-algebra test `supPrincipalC`);
* `divisor_of_vanish`: the divisor of such a witness is exactly `s Γ − (s deg Γ)∞`;
* `PrincipalMulN.lincomb` (over a perfect field): `a Γ`, `b Γ` principal ⇒ `(x a + y b) Γ`
  principal for integers `x, y`; hence `PrincipalMulN.mul_left`, `PrincipalMulN.of_dvd`,
  `PrincipalMulN.gcd`;
* `principal_of_reduction_N` (Henselian DVR): if `(s ℓ) Γ` is principal over `K` (`ℓ` a unit)
  and `m Γ̄` over the residue field, then `(m s) Γ` is principal over `K`.
-/

open Polynomial IntermediateField Differential Differential.SuperData

namespace Sup

/-- `s Γ − (s deg Γ)∞` is principal (in `ψ`-form). -/
def PrincipalMulN {R : Type*} [CommRing R] (f : R[X]) (n d : ℕ) {r : ℕ} (α β : Fin r → R)
    (mq : Fin r → ℕ) (s : ℕ) : Prop :=
  ∃ W : R[X][X], W ≠ 0 ∧
    (∀ j a, (W.coeff j).coeff a ≠ 0 → j < n ∧ n * a + d * j ≤ s * ∑ q, mq q) ∧
    ∀ q, VanishAtN f n W (α q) (β q) (s * mq q)

lemma toPoly_coeffs {F : Type*} [CommRing F] (f : F[X]) :
    CPoly.toPoly ((List.range (f.natDegree + 1)).map f.coeff) = f := by
  ext k
  rw [CPoly.coeff_toPoly]
  rcases Nat.lt_or_ge k (f.natDegree + 1) with hk | hk
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- Principality is preserved by field embeddings. -/
lemma PrincipalMulN.map {F S : Type*} [Field F] [Field S] (φ : F →+* S) {f : F[X]} {n d r : ℕ}
    {α β : Fin r → F} {mq : Fin r → ℕ} {s : ℕ} (h : PrincipalMulN f n d α β mq s) :
    PrincipalMulN (f.map φ) n d (fun q ↦ φ (α q)) (fun q ↦ φ (β q)) mq s := by
  obtain ⟨W, hW0, hWs, hWv⟩ := h
  refine ⟨W.map (mapRingHom φ), fun h0 ↦ hW0 (Polynomial.map_injective _
    (Polynomial.map_injective _ φ.injective) (by rw [h0, Polynomial.map_zero])), ?_,
    fun q ↦ (hWv q).mapR φ⟩
  intro j a h
  refine hWs j a fun h0 ↦ h ?_
  simp [h0]

/-- **Descent of principality** along a field embedding. -/
theorem principalMulN_descend {F S : Type*} [Field F] [DecidableEq F] [Field S] (φ : F →+* S)
    (f : F[X]) {n : ℕ} (hn : 0 < n) (d : ℕ) {r : ℕ} (α β : Fin r → F) (mq : Fin r → ℕ)
    (hΓ : ∀ q, (n : F) * β q ^ (n - 1) ≠ 0 ∧ β q ^ n = f.eval (α q)) (s : ℕ)
    (h : PrincipalMulN (f.map φ) n d (fun q ↦ φ (α q)) (fun q ↦ φ (β q)) mq s) :
    PrincipalMulN f n d α β mq s := by
  classical
  obtain ⟨W, hW0, hWs, hWv⟩ := h
  set fC : CPoly F := (List.range (f.natDegree + 1)).map f.coeff
  have hfC : CPoly.toPoly fC = f := toPoly_coeffs f
  set Γ : List (F × F × ℕ) := List.ofFn fun q ↦ (α q, β q, s * mq q)
  have hΓ' : ∀ P ∈ Γ, (n : F) * P.2.1 ^ (n - 1) ≠ 0 ∧ P.2.1 ^ n = (CPoly.toPoly fC).eval P.1 := by
    intro P hP
    obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hP
    rw [hfC]; exact hΓ q
  have hne := supPrincipalC_complete φ fC n hn d Γ (s * ∑ q, mq q) hΓ' W hW0 hWs (by
    intro P hP
    obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hP
    rw [hfC]; exact hWv q)
  obtain ⟨⟨j, cs⟩, hjc⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨V, hV0, hVs, hVv⟩ := supPrincipalC_sound fC n hn d Γ _ hΓ' hjc
  refine ⟨V, hV0, hVs, fun q ↦ ?_⟩
  have := hVv (α q, β q, s * mq q) (List.mem_ofFn.mpr ⟨q, rfl⟩)
  rwa [hfC] at this

end Sup

namespace Differential.SuperData

variable {C L K : Type*} [Field C] [PerfectField C] [Field L] [Algebra C L]
variable [Field K] [Algebra C K] [IsAlgClosed K]

variable (S : SuperData C L)

open Classical in
/-- **The exact divisor of a witness**: a function of pole order `≤ deg Γ` vanishing on `Γ` has
divisor exactly `Γ − (deg Γ)∞`. -/
theorem divisor_of_vanish (hcop : Nat.Coprime S.n S.p.natDegree) {r : ℕ} (α β : Fin r → C)
    (mq : Fin r → ℕ) (hP : Function.Injective fun q ↦ (α q, β q)) (hβ : ∀ q, β q ≠ 0)
    (hβf : ∀ q, β q ^ S.n = S.p.eval (α q)) (W : C[X][X]) (hW0 : W ≠ 0)
    (hWs : ∀ j a, (W.coeff j).coeff a ≠ 0 → j < S.n ∧ S.n * a + S.p.natDegree * j ≤ ∑ q, mq q)
    (hWv : ∀ q, Sup.VanishAtN S.p S.n W (α q) (β q) (mq q)) :
    S.elemW W ≠ 0 ∧ S.IsIntegralS K (S.elemW W) ∧
      (∀ q, S.ordAt K (S.elemW W) (algebraMap C K (α q)) (algebraMap C K (β q)) = mq q) ∧
      (∀ a b : K, b ^ S.n = (S.p.map (algebraMap C K)).eval a →
        (∀ q, (a, b) ≠ (algebraMap C K (α q), algebraMap C K (β q))) →
        S.ordAt K (S.elemW W) a b = 0) ∧
      S.ordInf K (S.elemW W) = -((∑ q, mq q : ℕ) : ℤ) := by
  set ι := algebraMap C K with hι_def
  have hιi : Function.Injective ι := ι.injective
  have hpt : ∀ c d : C, d ^ S.n = S.p.eval c → (ι d) ^ S.n = (S.p.map ι).eval (ι c) :=
    fun c d h ↦ by rw [← map_pow, h, eval_map, eval₂_hom]
  have hWW : ∀ i, S.n ≤ i → W.coeff i = 0 := by
    intro i hi
    by_contra h0
    obtain ⟨a, ha⟩ : ∃ a, (W.coeff i).coeff a ≠ 0 := by
      by_contra h1; push_neg at h1; exact h0 (Polynomial.ext h1)
    have := (hWs i a ha).1
    omega
  have hG0 : S.elemW W ≠ 0 := S.elemW_ne_zero W hW0 hWW
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
  have hGv : ∀ q, (mq q : ℤ) ≤ S.ordAt K (S.elemW W) (ι (α q)) (ι (β q)) := fun q ↦
    (S.le_ordAt_iff_vanish W hWW hG0 _ _ ((map_ne_zero_iff _ hιi).mpr (hβ q))
      (hpt _ _ (hβf q)) (mq q)).mpr ((hWv q).mapR ι)
  obtain ⟨hGT, hGz, hGinf⟩ := S.exact_divisor hcop (S.elemW W) hG0 (S.elemW_integral W)
    (∑ q, mq q : ℕ) (S.elemW_ordInf hcop W _ hWs hG0) T hTv e
    (fun Q hQ ↦ by
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hQ
      rw [he]; exact hGv q)
    (by
      rw [Finset.sum_image fun q _ q' _ h ↦ hptinj h]
      simp only [he]; push_cast; rfl)
  refine ⟨hG0, S.elemW_integral W, fun q ↦ ?_, fun a b hv hne ↦ ?_, hGinf⟩
  · have := hGT (pt q) (Finset.mem_image_of_mem _ (Finset.mem_univ q))
    rw [he] at this; exact this
  · refine hGz a b hv fun hmem ↦ ?_
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hmem
    exact hne q hq.symm

end Differential.SuperData

namespace Sup

section Field

variable {F : Type*} [Field F] [PerfectField F]

/-- **Integer combinations of principal multiples.** -/
theorem PrincipalMulN.lincomb (f : F[X]) {n : ℕ} (hn : 0 < n) (hsq : Squarefree f)
    (hd : 0 < f.natDegree) (hcop : Nat.Coprime n f.natDegree) (hnF : (n : F) ≠ 0)
    {r : ℕ} (α β : Fin r → F) (mq : Fin r → ℕ) (hP : Function.Injective fun q ↦ (α q, β q)) (hβ : ∀ q, β q ≠ 0)
    (hβf : ∀ q, β q ^ n = f.eval (α q)) {a b c : ℕ} (x y : ℤ)
    (hc : x * a + y * b = c) (ha : PrincipalMulN f n f.natDegree α β mq a)
    (hb : PrincipalMulN f n f.natDegree α β mq b) : PrincipalMulN f n f.natDegree α β mq c := by
  classical
  set S := stdSuper F f n hn hsq hd hnF with hS
  set Kb := AlgebraicClosure F
  set ι := algebraMap F Kb with hι_def
  have hιi : Function.Injective ι := ι.injective
  have hcopS : Nat.Coprime S.n S.p.natDegree := hcop
  have hpt : ∀ c d : F, d ^ n = f.eval c → (ι d) ^ S.n = (S.p.map ι).eval (ι c) :=
    fun c d h ↦ by
      show (ι d) ^ n = (f.map ι).eval (ι c)
      rw [← map_pow, h, eval_map, eval₂_hom]
  have hdiv : ∀ s : ℕ, PrincipalMulN f n f.natDegree α β mq s → ∃ W : F[X][X],
      S.elemW W ≠ 0 ∧ S.IsIntegralS Kb (S.elemW W) ∧
      (∀ q, S.ordAt Kb (S.elemW W) (ι (α q)) (ι (β q)) = s * mq q) ∧
      (∀ a b : Kb, b ^ S.n = (S.p.map ι).eval a → (∀ q, (a, b) ≠ (ι (α q), ι (β q))) →
        S.ordAt Kb (S.elemW W) a b = 0) ∧
      S.ordInf Kb (S.elemW W) = -((s * ∑ q, mq q : ℕ) : ℤ) := by
    intro s ⟨W, hW0, hWs, hWv⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := S.divisor_of_vanish (K := Kb) hcopS α β (fun q ↦ s * mq q) hP
      hβ hβf W hW0 (by rw [← Finset.mul_sum]; exact hWs) hWv
    refine ⟨W, h1, h2, fun q ↦ by rw [h3 q]; push_cast; ring, h4, ?_⟩
    rw [h5, Finset.mul_sum]
  obtain ⟨Wa, hGa0, -, hGaq, hGaz, hGainf⟩ := hdiv a ha
  obtain ⟨Wb, hGb0, -, hGbq, hGbz, hGbinf⟩ := hdiv b hb
  set G := S.elemW Wa ^ x * S.elemW Wb ^ y with hG_def
  have hG0 : G ≠ 0 := mul_ne_zero (zpow_ne_zero _ hGa0) (zpow_ne_zero _ hGb0)
  have hGo : ∀ a' b' : Kb, b' ^ S.n = (S.p.map ι).eval a' →
      S.ordAt Kb G a' b' = x * S.ordAt Kb (S.elemW Wa) a' b' +
        y * S.ordAt Kb (S.elemW Wb) a' b' := by
    intro a' b' hv
    rw [hG_def, S.ordAt_mul hv (zpow_ne_zero _ hGa0) (zpow_ne_zero _ hGb0), S.ordAt_zpow hv,
      S.ordAt_zpow hv]
  have hGq : ∀ q, S.ordAt Kb G (ι (α q)) (ι (β q)) = c * mq q := by
    intro q
    rw [hGo _ _ (hpt _ _ (hβf q)), hGaq, hGbq, ← hc]; ring
  have hGint : S.IsIntegralS Kb G := by
    intro a' b' hv
    by_cases hA : ∃ q, (a', b') = (ι (α q), ι (β q))
    · obtain ⟨q, hq⟩ := hA
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hq
      rw [hGq]; positivity
    · push_neg at hA
      rw [hGo _ _ hv, hGaz _ _ hv hA, hGbz _ _ hv hA]; simp
  obtain ⟨φ, hφ⟩ := S.ordInf_hom (K := Kb) hcopS
  have hGinf : -((c * ∑ q, mq q : ℕ) : ℤ) ≤ S.ordInf Kb G := by
    rw [hG_def, S.ordInf_mul hcopS (zpow_ne_zero _ hGa0) (zpow_ne_zero _ hGb0),
      hφ (S.elemW Wa ^ x), order_hom_zpow, hφ (S.elemW Wb ^ y), order_hom_zpow, ← hφ, ← hφ,
      hGainf, hGbinf]
    push_cast
    rw [← hc]
    linarith
  obtain ⟨W, hWG, hW0, hWs⟩ := S.elem_repr (K := Kb) hcopS G hG0 hGint _ hGinf
  have hWW : ∀ i, S.n ≤ i → W.coeff i = 0 := by
    intro i hi
    by_contra h0
    obtain ⟨a', ha'⟩ : ∃ a', (W.coeff i).coeff a' ≠ 0 := by
      by_contra h1; push_neg at h1; exact h0 (Polynomial.ext h1)
    have := (hWs i a' ha').1
    omega
  refine ⟨W, hW0, hWs, fun q ↦ ?_⟩
  have hβK : ι (β q) ≠ 0 := (map_ne_zero_iff _ hιi).mpr (hβ q)
  have h1 := (S.le_ordAt_iff_vanish W hWW (by rw [hWG]; exact hG0) _ _ hβK (hpt _ _ (hβf q))
    (c * mq q)).mp (by rw [hWG, hGq]; push_cast; rfl)
  obtain ⟨V, hV⟩ := exists_branchN f hn (IsUnit.mk0 _ (mul_ne_zero hnF (pow_ne_zero _ (hβ q))))
    (hβf q) (c * mq q)
  exact vanishAtN_of_map ι hιi hn (hV.mono (Nat.le_succ _)) (S.unit_branch _ hβK) h1

theorem PrincipalMulN.mul_left (f : F[X]) {n : ℕ} (hn : 0 < n) (hsq : Squarefree f)
    (hd : 0 < f.natDegree) (hcop : Nat.Coprime n f.natDegree) (hnF : (n : F) ≠ 0)
    {r : ℕ} (α β : Fin r → F) (mq : Fin r → ℕ) (hP : Function.Injective fun q ↦ (α q, β q)) (hβ : ∀ q, β q ≠ 0)
    (hβf : ∀ q, β q ^ n = f.eval (α q)) {s : ℕ} (k : ℕ)
    (h : PrincipalMulN f n f.natDegree α β mq s) : PrincipalMulN f n f.natDegree α β mq (k * s) :=
  PrincipalMulN.lincomb f hn hsq hd hcop hnF α β mq hP hβ hβf (k : ℤ) 0 (by push_cast; ring) h h

theorem PrincipalMulN.of_dvd (f : F[X]) {n : ℕ} (hn : 0 < n) (hsq : Squarefree f)
    (hd : 0 < f.natDegree) (hcop : Nat.Coprime n f.natDegree) (hnF : (n : F) ≠ 0)
    {r : ℕ} (α β : Fin r → F) (mq : Fin r → ℕ) (hP : Function.Injective fun q ↦ (α q, β q)) (hβ : ∀ q, β q ≠ 0)
    (hβf : ∀ q, β q ^ n = f.eval (α q)) {a b : ℕ} (hab : a ∣ b)
    (h : PrincipalMulN f n f.natDegree α β mq a) : PrincipalMulN f n f.natDegree α β mq b := by
  obtain ⟨k, rfl⟩ := hab
  rw [mul_comm]
  exact PrincipalMulN.mul_left f hn hsq hd hcop hnF α β mq hP hβ hβf k h

theorem PrincipalMulN.gcd (f : F[X]) {n : ℕ} (hn : 0 < n) (hsq : Squarefree f)
    (hd : 0 < f.natDegree) (hcop : Nat.Coprime n f.natDegree) (hnF : (n : F) ≠ 0)
    {r : ℕ} (α β : Fin r → F) (mq : Fin r → ℕ) (hP : Function.Injective fun q ↦ (α q, β q)) (hβ : ∀ q, β q ≠ 0)
    (hβf : ∀ q, β q ^ n = f.eval (α q)) {a b : ℕ}
    (ha : PrincipalMulN f n f.natDegree α β mq a) (hb : PrincipalMulN f n f.natDegree α β mq b) :
    PrincipalMulN f n f.natDegree α β mq (Nat.gcd a b) :=
  PrincipalMulN.lincomb f hn hsq hd hcop hnF α β mq hP hβ hβf (Nat.gcdA a b) (Nat.gcdB a b)
    (by rw [Nat.gcd_eq_gcd_ab]; ring) ha hb

end Field

section DVR

variable {O K : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [HenselianRing O (IsLocalRing.maximalIdeal O)] [Field K] [Algebra O K] [IsFractionRing O K]
  [PerfectField K] [PerfectField (IsLocalRing.ResidueField O)]

local notation "𝕜" => IsLocalRing.ResidueField O
local notation "ρ" => IsLocalRing.residue O
local notation "ι" => algebraMap O K

/-- **The one-prime torsion bound.** If `(s ℓ) Γ` is principal over `K` (`ℓ` a unit of `O`) and
`m Γ̄` is principal over the residue field, then `(m s) Γ` is principal over `K`. -/
theorem principal_of_reduction_N {ϖ : O} (hϖ : Irreducible ϖ) (f : O[X]) {n : ℕ} (hn : 0 < n)
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
    {s ℓ m : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓ : IsUnit (ℓ : O))
    (hsℓ : PrincipalMulN (f.map ι) n f.natDegree (fun q ↦ ι (α q)) (fun q ↦ ι (β q)) mq (s * ℓ))
    (hm : PrincipalMulN (f.map ρ) n f.natDegree (fun q ↦ ρ (α q)) (fun q ↦ ρ (β q)) mq m) :
    PrincipalMulN (f.map ι) n f.natDegree (fun q ↦ ι (α q)) (fun q ↦ ι (β q)) mq (m * s) := by
  classical
  have hιi : Function.Injective ι := IsFractionRing.injective O K
  have hunitk : ∀ z : O, IsUnit z → ρ z ≠ 0 := fun z hz ↦ (hz.map ρ).ne_zero
  have hfk : (f.map ρ).natDegree = f.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero _ (hunitk _ hlc)
  have hfK : (f.map ι).natDegree = f.natDegree := natDegree_map_eq_of_injective hιi f
  have hnk : (n : 𝕜) ≠ 0 := by rw [← map_natCast ρ]; exact hunitk _ hnu
  have hnK : (n : K) ≠ 0 := by
    rw [← map_natCast ι]; exact (map_ne_zero_iff _ hιi).mpr hnu.ne_zero
  have hinjk := (points_reduce ρ α β hα hβd).2
  have hinjK := (points_reduce ι α β hα hβd).2
  -- the multiple `s m Γ̄` over the residue field
  have hm' := PrincipalMulN.mul_left (f.map ρ) hn hsqk (by rw [hfk]; exact hd)
    (by rw [hfk]; exact hcop) hnk (fun q ↦ ρ (α q)) (fun q ↦ ρ (β q)) mq hinjk
    (fun q ↦ hunitk _ (hβu q)) (fun q ↦ by rw [← map_pow, hβf q, eval_map, eval₂_hom]) s
    (by rw [hfk]; exact hm)
  rw [hfk] at hm'
  obtain ⟨γb, hγ0, hγs, hγv⟩ := hm'
  -- the multiple `m s ℓ Γ` over `K`
  have hΞ := PrincipalMulN.mul_left (f.map ι) hn hsqK (by rw [hfK]; exact hd)
    (by rw [hfK]; exact hcop) hnK (fun q ↦ ι (α q)) (fun q ↦ ι (β q)) mq hinjK
    (fun q ↦ (map_ne_zero_iff _ hιi).mpr (hβu q).ne_zero)
    (fun q ↦ by rw [← map_pow, hβf q, eval_map, eval₂_hom]) m (by rw [hfK]; exact hsℓ)
  rw [hfK] at hΞ
  obtain ⟨Ξ, hΞ0, hΞs, hΞv⟩ := hΞ
  set mq' : Fin r → ℕ := fun q ↦ m * s * mq q with hmq'_def
  have hsum' : ∑ q, mq' q = m * s * ∑ q, mq q := by simp [mq', Finset.mul_sum]
  obtain ⟨γ, hγK0, hγKs, hγKv⟩ := torsion_descends_N hϖ f hn hlc hd hcop hsqk hsqK hnu ζ hζ hζk
    hgen x y hyu hyf hx α β mq' hβu hβf hα hβd hαx hNS γb hγ0
    (fun j a h ↦ by rw [hsum']; have := hγs j a h; rw [show s * m = m * s by ring] at this; exact this)
    (fun q ↦ by
      have := hγv q
      rwa [show s * m * mq q = mq' q by simp only [mq']; ring] at this)
    ℓ hℓ1 hℓ Ξ hΞ0
    (fun j a h ↦ by
      rw [hsum']; have := hΞs j a h
      rw [show m * (s * ℓ) = ℓ * (m * s) by ring, mul_assoc] at this; exact this)
    (fun q ↦ by
      have := hΞv q
      rwa [show m * (s * ℓ) * mq q = ℓ * mq' q by simp only [mq']; ring] at this)
  refine ⟨γ, hγK0, fun j a h ↦ by rw [← hsum']; exact hγKs j a h, fun q ↦ ?_⟩
  have := hγKv q
  rwa [show mq' q = m * s * mq q from rfl] at this

end DVR

end Sup
