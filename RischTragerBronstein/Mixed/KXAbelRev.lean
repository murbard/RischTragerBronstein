import RischTragerBronstein.Mixed.KXAbel
import RischTragerBronstein.Mixed.KXDepConj

/-!
# The converse of `hnorel_of_group`: a group relation gives a principal divisor

If `2N ∑_q m_q P_q + 2μ P₊ = 0` in `W'(K)` (points over `C`), Abel's construction on the base change
(`exists_hG` on `S.base K`, the sum being `0`) gives a function with divisor `N Δ + μ δ₀` over `K`;
times `∏ (x − c_q)^{N m_q} x^{|μ|}` (`ordAt_unzD` on `S.base K`) it is integral with divisor
`2N Γ + 2|μ| P_±`, so `PrincipalMulN` holds over `K` and descends to `C`
(`principalMulN_descend`): **`pm_of_group`**.
-/

open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine Sup

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

open scoped Classical

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L)

lemma dK_base {r nk : ℕ} (c β : Fin r → C) (m : Fin r → ℕ) (cl : Fin r → Fin nk) (k : Fin nk) :
    dK (C := K) (K := K) (fun q ↦ algebraMap C K (c q)) (fun q ↦ algebraMap C K (β q)) m cl k =
      dK (K := K) c β m cl k := by
  funext Q; simp [dK]

lemma gammaQ_base {r : ℕ} (c β : Fin r → C) (m : Fin r → ℕ) :
    gammaQ (C := K) (K := K) (fun q ↦ algebraMap C K (c q)) (fun q ↦ algebraMap C K (β q)) m =
      gammaQ (K := K) c β m := by
  funext Q; simp [gammaQ]

section Group

variable {r nk : ℕ} (c β : Fin r → C) (m : Fin r → ℕ) (cl : Fin r → Fin nk) (k0 : Fin nk)
  (c3 c2 c1 c0 : C)

local notation "WK" => WG (algebraMap C K c3) (algebraMap C K c2) (algebraMap C K c1) (algebraMap C K c0)

/-- **A group relation gives `PrincipalMulN` over `C`.** -/
theorem pm_of_group (hn2 : S.n = 2) (hc3 : c3 ≠ 0)
    (hpE : S.p = Polynomial.C c3 * X ^ 3 + Polynomial.C c2 * X ^ 2 + Polynomial.C c1 * X +
      Polynomial.C c0)
    (hcop : Nat.Coprime S.n S.p.natDegree) (hc : Function.Injective c) (hc0 : ∀ q, c q ≠ 0)
    (hβ : ∀ q, β q ≠ 0 ∧ β q ^ S.n = S.p.eval (c q)) (b₀ : C) (hb₀ : b₀ ≠ 0)
    (hv0 : b₀ ^ S.n = S.p.eval 0)
    (hnsq : ∀ q, (WK).Nonsingular (algebraMap C K c3 * algebraMap C K (c q))
      (algebraMap C K c3 * algebraMap C K (β q)))
    (hns0 : (WK).Nonsingular (algebraMap C K c3 * 0) (algebraMap C K c3 * algebraMap C K b₀))
    (N : ℕ) (μ : ℤ)
    (hrel : (2 * (N : ℤ)) • (∑ q, (mK m cl k0 q : ℤ) • Point.some _ _ (hnsq q)) +
        (2 * μ) • Point.some _ _ hns0 = 0) :
    PrincipalMulN S.p S.n S.p.natDegree (Fin.cons 0 c) (Fin.cons (if 0 ≤ μ then b₀ else -b₀) β)
      (Fin.cons (2 * μ.natAbs) fun q ↦ (2 * N) * mK m cl k0 q) 1 := by
  have hc3K : algebraMap C K c3 ≠ 0 := (map_ne_zero_iff _ (algebraMap C K).injective).mpr hc3
  set Pq : Fin r → (WK).Point := fun q ↦ Point.some _ _ (hnsq q)
  set P0 : (WK).Point := Point.some _ _ hns0
  set l : List (ℤ × (WK).Point) :=
    (List.finRange r).flatMap (fun q ↦ [((N : ℤ) * mK m cl k0 q, Pq q),
      (-((N : ℤ) * mK m cl k0 q), -Pq q)]) ++ [(μ, P0), (-μ, -P0)] with hl
  have hn2' : (S.base K).n = 2 := by rw [base_n, hn2]
  have hpE' : (S.base K).p = Polynomial.C (algebraMap C K c3) * X ^ 3 +
      Polynomial.C (algebraMap C K c2) * X ^ 2 + Polynomial.C (algebraMap C K c1) * X +
      Polynomial.C (algebraMap C K c0) := by
    rw [base_p, hpE]; simp
  -- the sum of `l` vanishes
  have happS : ∀ (l1 l2 : List (ℤ × (WK).Point)), sumLG (l1 ++ l2) = sumLG l1 + sumLG l2 := by
    intro l1 l2; induction l1 with
    | nil => simp [sumLG]
    | cons e l1 ih => simp only [List.cons_append, sumLG, ih]; abel
  have hsum : sumLG l = 0 := by
    rw [← hrel, hl, happS, sumLG_flatMap, ← Fin.sum_univ_def]
    simp only [sumLG, add_zero, neg_smul, smul_neg, neg_neg]
    rw [Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [smul_smul, ← add_smul]; congr 1; ring
    · rw [← add_smul]; congr 1; ring
  obtain ⟨h, hh, hd⟩ := exists_hG (S := S.base K) hn2' hc3K hpE' l
  rw [hsum] at hd
  have hd' : (S.base K).DivIs h (divLG l) := divIs_congr hd (by funext z; simp [δG])
  -- the divisor of `h`: `N Δ + μ δ₀`
  set β₀ := algebraMap C K b₀ with hβ₀def
  have hβ₀ : β₀ ≠ 0 := (map_ne_zero_iff _ (algebraMap C K).injective).mpr hb₀
  have hdiv : ∀ α β' : K, β' ^ (S.base K).n = ((S.base K).p.map (algebraMap K K)).eval α →
      ((S.base K).ordAt K h α β' : ℚ) =
        N * dK (C := K) (K := K) (fun q ↦ algebraMap C K (c q)) (fun q ↦ algebraMap C K (β q)) m
          cl k0 (α, β') + μ * dZ β₀ (α, β') := by
    intro α β' hv
    rw [hd' α β' hv, dK_base]
    have happ : ∀ (l1 l2 : List (ℤ × (WK).Point)), divLG (l1 ++ l2) = divLG l1 + divLG l2 := by
      intro l1 l2; induction l1 with
      | nil => simp [divLG]
      | cons e l1 ih => simp only [List.cons_append, divLG, ih]; ring
    rw [hl, happ, divLG_flatMap, ← Fin.sum_univ_def]
    simp only [divLG, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_zero, Finset.sum_apply]
    push_cast
    rw [dK, dZ, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [show Pq q = Point.some _ _ (hnsq q) from rfl, δG_some_div hc3K, δG_neg_some_div hc3K]
      have hbq : algebraMap C K (β q) ≠ -algebraMap C K (β q) := by
        intro h; apply (hβ q).1
        have : (2 : K) * algebraMap C K (β q) = 0 := by linear_combination h
        rcases mul_eq_zero.mp this with h2 | h2
        · exact absurd h2 two_ne_zero
        · exact (map_eq_zero_iff _ (algebraMap C K).injective).mp h2
      by_cases e1 : (α, β') = (algebraMap C K (c q), algebraMap C K (β q))
      · have e2 : ¬(α, β') = (algebraMap C K (c q), -algebraMap C K (β q)) := by
          rw [e1]; simp [hbq]
        simp [e1, hbq]
      · by_cases e2 : (α, β') = (algebraMap C K (c q), -algebraMap C K (β q))
        · simp [e1, e2, Ne.symm hbq]
        · simp [e1, e2]
    · rw [show P0 = Point.some _ _ hns0 from rfl]
      have h0a := δG_some_div hc3K 0 β₀ hns0 (α, β')
      have h0b := δG_neg_some_div hc3K 0 β₀ hns0 (α, β')
      rw [h0a, h0b]
      have hb0 : β₀ ≠ -β₀ := by
        intro h; apply hβ₀
        have : (2 : K) * β₀ = 0 := by linear_combination h
        rcases mul_eq_zero.mp this with h2 | h2
        · exact absurd h2 two_ne_zero
        · exact h2
      by_cases e1 : (α, β') = (0, β₀)
      · have e2 : ¬(α, β') = (0, -β₀) := by rw [e1]; simp [hb0]
        simp [e1, hb0]
      · by_cases e2 : (α, β') = (0, -β₀)
        · simp [e1, e2, Ne.symm hb0]
        · simp [e1, e2]
  -- the base data over `K`
  set cK : Fin r → K := fun q ↦ algebraMap C K (c q) with hcK
  set βK : Fin r → K := fun q ↦ algebraMap C K (β q) with hβK
  have hcKi : Function.Injective cK := fun i j e ↦ hc ((algebraMap C K).injective e)
  have hcK0 : ∀ q, cK q ≠ 0 := fun q ↦ (map_ne_zero_iff _ (algebraMap C K).injective).mpr (hc0 q)
  have hevK : ∀ a : C, (S.base K).p.eval (algebraMap C K a) = algebraMap C K (S.p.eval a) := fun a ↦ by
    rw [base_p, eval_map, eval₂_at_apply]
  have hβKb : ∀ q, βK q ≠ 0 ∧ βK q ^ (S.base K).n = (S.base K).p.eval (cK q) := fun q ↦
    ⟨(map_ne_zero_iff _ (algebraMap C K).injective).mpr (hβ q).1, by
      simp only [βK, cK, base_n]; rw [hevK, ← map_pow, (hβ q).2]⟩
  have hv0K : β₀ ^ (S.base K).n = ((S.base K).p.map (algebraMap K K)).eval 0 := by
    rw [base_eval, base_n, hβ₀def, ← map_pow, hv0, eval_map, ← map_zero (algebraMap C K),
      eval₂_at_apply]
  -- the integral function `w` on the base (zero derivations: the `ordAt` lemmas ignore them)
  obtain ⟨w, hw0, hwo⟩ : ∃ w : K⟮(S.base K).x⟯⟮(S.base K).y⟯, w ≠ 0 ∧
      ∀ α β' : K, β' ^ (S.base K).n = ((S.base K).p.map (algebraMap K K)).eval α →
        (S.base K).ordAt K w α β' = (2 * N : ℕ) * gammaQ (C := K) cK βK (mK m cl k0) (α, β') +
          (2 * μ.natAbs : ℕ) * gammaP (if 0 ≤ μ then β₀ else -β₀) (α, β') := by
    letI : Differential K := ⟨0⟩
    letI : Differential (BaseL K) := ⟨0⟩
    haveI : DifferentialAlgebra K (BaseL K) := ⟨fun a ↦ by
      change (0 : Derivation ℤ (BaseL K) (BaseL K)) _ = algebraMap K (BaseL K)
        ((0 : Derivation ℤ K K) a)
      simp⟩
    have hu := (S.base K).ordAt_unzD (K := K) hn2' β₀ hβ₀ hv0K cK βK hcKi hcK0 hβKb m cl k0 h hh N μ
      hdiv
    exact ⟨_, hu.1, hu.2⟩
  set σ : C := if 0 ≤ μ then b₀ else -b₀ with hσ
  have hσK : algebraMap C K σ = if 0 ≤ μ then β₀ else -β₀ := by
    simp only [hσ]; split_ifs <;> simp [hβ₀def]
  have hσ0 : σ ≠ 0 := by simp only [hσ]; split_ifs <;> simp [hb₀]
  have hσv : σ ^ S.n = S.p.eval 0 := by
    rw [← hv0, hn2]; simp only [hσ]; split_ifs <;> ring
  set mq : Fin (r + 1) → ℕ := Fin.cons (2 * μ.natAbs) fun q ↦ (2 * N) * mK m cl k0 q with hmq
  have hIP : (S.base K).IsPrincipalS K
      (gammaQ (C := K) (Fin.cons 0 cK) (Fin.cons (algebraMap C K σ) βK) mq) 1 := by
    refine ⟨w, hw0, fun α β' hv ↦ by rw [hwo α β' hv]; positivity, fun Q hv ↦ ?_⟩
    have key : gammaQ (C := K) (Fin.cons 0 cK) (Fin.cons (algebraMap C K σ) βK) mq Q =
        (2 * N) * gammaQ (C := K) cK βK (mK m cl k0) Q +
          (2 * μ.natAbs) * gammaP (if 0 ≤ μ then β₀ else -β₀) Q := by
      rw [hmq, gammaQ_cons, hσK]
      congr 1
      simp only [gammaQ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      split_ifs <;> simp
    rw [hwo Q.1 Q.2 hv, key]
    push_cast
    ring
  -- `PrincipalMulN` over `K`, then over `C`
  have hcopK : Nat.Coprime (S.base K).n (S.base K).p.natDegree := by
    rw [base_n, base_p, natDegree_map_eq_of_injective (algebraMap C K).injective]; exact hcop
  have hinjK : Function.Injective fun q : Fin (r + 1) ↦
      ((Fin.cons 0 cK : Fin (r + 1) → K) q, (Fin.cons (algebraMap C K σ) βK : Fin (r + 1) → K) q) :=
    fun i j e ↦ cons_inj cK hcKi hcK0 (Prod.ext_iff.mp e).1
  have hPK := (S.base K).principalMulN_of_isPrincipalS (K := K) hcopK (Fin.cons 0 cK)
    (Fin.cons (algebraMap C K σ) βK) mq hinjK
    (fun q ↦ by
      induction q using Fin.cases
      · exact (map_ne_zero_iff _ (algebraMap C K).injective).mpr hσ0
      · exact (hβKb _).1)
    (fun q ↦ by
      induction q using Fin.cases
      · simp only [Fin.cons_zero, base_n]
        rw [← map_pow, hσv, ← map_zero (algebraMap C K), hevK]
      · exact (hβKb _).2)
    _ (fun Q _ ↦ by simp [gammaQ]) 1 hIP
  rw [base_n, base_p, natDegree_map_eq_of_injective (algebraMap C K).injective] at hPK
  have e1 : (Fin.cons 0 cK : Fin (r + 1) → K) =
      fun q ↦ algebraMap C K ((Fin.cons 0 c : Fin (r + 1) → C) q) := by
    funext q; induction q using Fin.cases <;> simp [cK]
  have e2 : (Fin.cons (algebraMap C K σ) βK : Fin (r + 1) → K) =
      fun q ↦ algebraMap C K ((Fin.cons σ β : Fin (r + 1) → C) q) := by
    funext q; induction q using Fin.cases <;> simp [βK]
  rw [e1, e2] at hPK
  refine principalMulN_descend (algebraMap C K) S.p (by rw [hn2]; norm_num) _ _ _ mq
    (fun q ↦ ?_) 1 hPK
  induction q using Fin.cases
  · simp only [Fin.cons_zero]
    refine ⟨mul_ne_zero (by rw [hn2]; norm_num) (pow_ne_zero _ hσ0), hσv⟩
  · simp only [Fin.cons_succ]
    exact ⟨mul_ne_zero (by rw [hn2]; norm_num) (pow_ne_zero _ (hβ _).1), (hβ _).2⟩

/-- **A relation over `C` gives `PrincipalMulN`** (through the embedding into `W'(K)`). -/
theorem pm_of_groupC (hn2 : S.n = 2) (hc3 : c3 ≠ 0)
    (hpE : S.p = Polynomial.C c3 * X ^ 3 + Polynomial.C c2 * X ^ 2 + Polynomial.C c1 * X +
      Polynomial.C c0)
    (hcop : Nat.Coprime S.n S.p.natDegree) (hc : Function.Injective c) (hc0 : ∀ q, c q ≠ 0)
    (hβ : ∀ q, β q ≠ 0 ∧ β q ^ S.n = S.p.eval (c q)) (b₀ : C) (hb₀ : b₀ ≠ 0)
    (hv0 : b₀ ^ S.n = S.p.eval 0)
    (hnsC : ∀ q, (WG c3 c2 c1 c0).Nonsingular (c3 * c q) (c3 * β q))
    (hns0C : (WG c3 c2 c1 c0).Nonsingular (c3 * 0) (c3 * b₀))
    (hnsq : ∀ q, (WK).Nonsingular (algebraMap C K c3 * algebraMap C K (c q))
      (algebraMap C K c3 * algebraMap C K (β q)))
    (hns0 : (WK).Nonsingular (algebraMap C K c3 * 0) (algebraMap C K c3 * algebraMap C K b₀))
    (N : ℕ) (μ : ℤ)
    (hrelC : (2 * (N : ℤ)) • (∑ q, (mK m cl k0 q : ℤ) • Point.some _ _ (hnsC q)) +
        (2 * μ) • Point.some _ _ hns0C = 0) :
    PrincipalMulN S.p S.n S.p.natDegree (Fin.cons 0 c) (Fin.cons (if 0 ≤ μ then b₀ else -b₀) β)
      (Fin.cons (2 * μ.natAbs) fun q ↦ (2 * N) * mK m cl k0 q) 1 := by
  refine S.pm_of_group (K := K) c β m cl k0 c3 c2 c1 c0 hn2 hc3 hpE hcop hc hc0 hβ b₀ hb₀ hv0
    hnsq hns0 N μ ?_
  have hself : WG c3 c2 c1 c0 = ((WG c3 c2 c1 c0)⁄C) := by
    simp [WG, FFHeight.longF, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  set ι := (FFHeight.castHom (WG_baseChange (K := K) c3 c2 c1 c0)).comp
    ((Point.map (W' := WG c3 c2 c1 c0) (Algebra.ofId C K)).comp (FFHeight.castHom hself))
  have hq : ∀ q, ι (Point.some _ _ (hnsC q)) = Point.some _ _ (hnsq q) := fun q ↦ by
    simp only [ι, AddMonoidHom.comp_apply, FFHeight.castHom_some, Point.map_some]
    simp [Algebra.ofId_apply]
  have h0 : ι (Point.some _ _ hns0C) = Point.some _ _ hns0 := by
    simp only [ι, AddMonoidHom.comp_apply, FFHeight.castHom_some, Point.map_some]
    simp [Algebra.ofId_apply]
  have := congrArg ι hrelC
  rw [map_add, map_zsmul, map_zsmul, map_sum, map_zero] at this
  simp only [map_zsmul, hq, h0] at this
  exact this

end Group

end SuperData

end Differential
