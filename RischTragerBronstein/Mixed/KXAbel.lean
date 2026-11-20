import RischTragerBronstein.Mixed.AbelGen
import RischTragerBronstein.Mixed.KXNoRel
import RischTragerBronstein.Mixed.EllTwist

/-!
# The no-relation hypothesis of `kxe_norel` from the group law (step 2)

For `θ² = p(t)`, `p = c₃t³ + c₂t² + c₁t + c₀`, the divisor `N Δ_{k₀} + μ δ₀` of `kxe_norel` is the
affine divisor `∑_q N m_q ((P_q) − (−P_q)) + μ ((P₊) − (−P₊))` with `P_q = (c_q, β_q)`,
`P₊ = (0, β₀)`, read as points of Mathlib's model `W'` (`(X, Y) = (c₃t, c₃θ)`). By Abel's theorem
on the base change to `K` (`abel_sumG` through `tau`, `ordAt_tau`), a function with this divisor
forces `2N ∑_q m_q P_q + 2μ P₊ = 0` in `W'(K)` (`rel_of_div`). Hence **if no such group relation
holds, `hnorel` holds** (`hnorel_of_group`), and `kxe_norel` applies: independence in the group
— certified by heights (`EllNT`, `EllTwist`) — proves non-elementarity.
-/

open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

open scoped Classical

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L)

/-- The sum of `divLG` over a `flatMap`. -/
lemma divLG_flatMap {c3 c2 c1 c0 : K} {ι : Type*} (f : ι → List (ℤ × (WG c3 c2 c1 c0).Point)) :
    ∀ L : List ι, divLG (L.flatMap f) = (L.map fun i ↦ divLG (f i)).sum
  | [] => by simp [divLG]
  | i :: L => by
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← divLG_flatMap f L]
    induction f i with
    | nil => simp [divLG]
    | cons e l ih => simp only [List.cons_append, divLG, ih]; ring

lemma sumLG_flatMap {c3 c2 c1 c0 : K} {ι : Type*} (f : ι → List (ℤ × (WG c3 c2 c1 c0).Point)) :
    ∀ L : List ι, sumLG (L.flatMap f) = (L.map fun i ↦ sumLG (f i)).sum
  | [] => by simp [sumLG]
  | i :: L => by
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← sumLG_flatMap f L]
    induction f i with
    | nil => simp [sumLG]
    | cons e l ih => simp only [List.cons_append, sumLG, ih]; abel

section Group

variable {r nk : ℕ} (c β : Fin r → C) (m : Fin r → ℕ) (cl : Fin r → Fin nk) (k0 : Fin nk) (β₀ : K)
  (c3 c2 c1 c0 : C)

local notation "WK" => WG (algebraMap C K c3) (algebraMap C K c2) (algebraMap C K c1) (algebraMap C K c0)

lemma δG_some_div {c3' c2' c1' c0' : K} (hc : c3' ≠ 0) (x y : K)
    (h : (WG c3' c2' c1' c0').Nonsingular (c3' * x) (c3' * y)) (z : K × K) :
    δG c3' c2' c1' c0' (Point.some _ _ h) z = if z = (x, y) then 1 else 0 := by
  simp only [δG]
  rw [mul_div_cancel_left₀ _ hc, mul_div_cancel_left₀ _ hc]

lemma δG_neg_some_div {c3' c2' c1' c0' : K} (hc : c3' ≠ 0) (x y : K)
    (h : (WG c3' c2' c1' c0').Nonsingular (c3' * x) (c3' * y)) (z : K × K) :
    δG c3' c2' c1' c0' (-Point.some _ _ h) z = if z = (x, -y) then 1 else 0 := by
  simp only [Point.neg_some, δG, negY_G]
  rw [mul_div_cancel_left₀ _ hc, neg_div, mul_div_cancel_left₀ _ hc]

/-- **Step 2: no group relation ⇒ the no-relation hypothesis of `kxe_norel`.** -/
theorem hnorel_of_group (hn2 : S.n = 2) (hc3 : c3 ≠ 0)
    (hpE : S.p = Polynomial.C c3 * X ^ 3 + Polynomial.C c2 * X ^ 2 + Polynomial.C c1 * X +
      Polynomial.C c0)
    (hβ : ∀ q, β q ≠ 0) (hβ₀ : β₀ ≠ 0)
    (hnsq : ∀ q, (WK).Nonsingular (algebraMap C K c3 * algebraMap C K (c q))
      (algebraMap C K c3 * algebraMap C K (β q)))
    (hns0 : (WK).Nonsingular (algebraMap C K c3 * 0) (algebraMap C K c3 * β₀))
    (hgrp : ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
      (2 * (N : ℤ)) • (∑ q, (mK m cl k0 q : ℤ) • Point.some _ _ (hnsq q)) +
        (2 * μ) • Point.some _ _ hns0 ≠ 0) :
    ∀ f : C⟮S.x⟯⟮S.y⟯, f ≠ 0 → ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
      ¬ ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
        (S.ordAt K f α β' : ℚ) = N * dK c β m cl k0 (α, β') + μ * dZ β₀ (α, β') := by
  intro f hf N hN μ hdiv
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
  -- the divisor of `τ f` is `divLG l`
  have hD : (S.base K).DivIs (S.tau K f) (divLG l) := by
    intro α β' hv
    have hv' : β' ^ S.n = (S.p.map (algebraMap C K)).eval α := by rw [← base_eval]; exact hv
    rw [S.ordAt_tau K f α β' hv']
    have h1 := hdiv α β' hv'
    have hdl : (divLG l (α, β') : ℚ) = N * dK c β m cl k0 (α, β') + μ * dZ β₀ (α, β') := by
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
          intro h; apply hβ q
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
    exact_mod_cast h1.trans hdl.symm
  have hsum := abel_sumG hn2' hc3K hpE' l (S.tau K f) (S.tau_ne_zero K hf) hD
  apply hgrp N hN μ
  rw [← hsum]
  have happ : ∀ (l1 l2 : List (ℤ × (WK).Point)), sumLG (l1 ++ l2) = sumLG l1 + sumLG l2 := by
    intro l1 l2; induction l1 with
    | nil => simp [sumLG]
    | cons e l1 ih => simp only [List.cons_append, sumLG, ih]; abel
  rw [hl, happ, sumLG_flatMap, ← Fin.sum_univ_def]
  simp only [sumLG, add_zero, neg_smul, smul_neg, neg_neg]
  rw [Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [smul_smul, ← add_smul]; congr 1; ring
  · rw [← add_smul]; congr 1; ring

end Group

section ExpMain2

variable (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η * X))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
  (hgood : ∀ α : K, ¬ α = 0 → α′ ≠ ((Polynomial.C η * X).map (algebraMap C K)).eval α)
  (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
  {r nk : ℕ} (c β : Fin r → C) (hc : Function.Injective c) (hc0 : ∀ q, c q ≠ 0)
  (hβ : ∀ q, β q ≠ 0 ∧ β q ^ S.n = S.p.eval (c q)) (m : Fin r → ℕ) (cl : Fin r → Fin nk)
  (ρ : Fin nk → C)
  (P : C[X]) (l : ℕ) (b : L) (hb : b ∈ C⟮S.x⟯)
  (D : C[X]) (R : Fin r → C[X]) (hDR : ∀ q, D = (X - Polynomial.C (c q)) * R q)
  (hRne : ∀ q, (R q).eval (c q) ≠ 0)
  (hDoff : ∀ α : K, ¬ α = 0 → (∀ q, α ≠ algebraMap C K (c q)) → (D.map (algebraMap C K)).eval α ≠ 0)
  (hbP : b * aeval S.x (D * S.p ^ l) = aeval S.x P)
  (hres : ∀ q, P.eval (c q) * β q = m q * ρ (cl q) * ((Polynomial.C η * X).eval (c q) - (c q)′) *
    (R q * S.p ^ l).eval (c q))
  (hn2 : S.n = 2) (hcop : Nat.Coprime S.n S.p.natDegree) (β₀ : K) (hβ₀ : β₀ ≠ 0)
  (hv0 : β₀ ^ S.n = (S.p.map (algebraMap C K)).eval 0)

include hx hK hgood hconstC hc hc0 hβ hb hDR hRne hDoff hbP hres hn2 hβ₀ hv0 in
/-- **No group relation ⇒ no Liouville form**: `kxe_norel` with its hypothesis discharged by Abel's
theorem (`hnorel_of_group`). The remaining input is the independence of `∑ m_q P_q` and `P₊` in
`W'(K)`, certified by heights. -/
theorem kxe_norel_group (k0 : Fin nk) (hk0 : ∃ q, cl q = k0 ∧ m q ≠ 0)
    (hρ : ∀ e : Fin nk → ℚ, ∑ kk, (e kk : C) * ρ kk = 0 → ∀ kk, e kk = 0)
    (c3 c2 c1 c0 : C) (hc3 : c3 ≠ 0)
    (hpE : S.p = Polynomial.C c3 * X ^ 3 + Polynomial.C c2 * X ^ 2 + Polynomial.C c1 * X +
      Polynomial.C c0)
    (hnsq : ∀ q, (WG (algebraMap C K c3) (algebraMap C K c2) (algebraMap C K c1)
      (algebraMap C K c0)).Nonsingular (algebraMap C K c3 * algebraMap C K (c q))
      (algebraMap C K c3 * algebraMap C K (β q)))
    (hns0 : (WG (algebraMap C K c3) (algebraMap C K c2) (algebraMap C K c1)
      (algebraMap C K c0)).Nonsingular (algebraMap C K c3 * 0) (algebraMap C K c3 * β₀))
    (hgrp : ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
      (2 * (N : ℤ)) • (∑ q, (mK m cl k0 q : ℤ) • Point.some _ _ (hnsq q)) +
        (2 * μ) • Point.some _ _ hns0 ≠ 0)
    (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) : False :=
  S.kxe_norel η hx hK hgood hconstC c β hc hc0 hβ m cl ρ P l b hb D R hDR hRne hDoff hbP hres hn2 β₀ hβ₀ hv0
    k0 hk0 hρ (S.hnorel_of_group c β m cl k0 β₀ c3 c2 c1 c0 hn2 hc3 hpE (fun q ↦ (hβ q).1) hβ₀
      hnsq hns0 hgrp) hbm s cs u hcs hu v hv heq

end ExpMain2

section Descent

variable {r nk : ℕ} (c β : Fin r → C) (m : Fin r → ℕ) (cl : Fin r → Fin nk) (k0 : Fin nk)
  (c3 c2 c1 c0 b₀ : C)

lemma WG_baseChange (c3 c2 c1 c0 : C) :
    ((WG c3 c2 c1 c0)⁄K) = WG (algebraMap C K c3) (algebraMap C K c2) (algebraMap C K c1)
      (algebraMap C K c0) := by
  simp [WG, FFHeight.longF, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- **Step 3: descent of the relation from `K` to `C`.** If the points are defined over `C`
(`β₀ = b₀ ∈ C`), a relation in `W'(K)` is a relation in `W'(C)`. -/
theorem hgrp_of_C (hnsC : ∀ q, (WG c3 c2 c1 c0).Nonsingular (c3 * c q) (c3 * β q))
    (hns0C : (WG c3 c2 c1 c0).Nonsingular (c3 * 0) (c3 * b₀))
    (hgrpC : ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
      (2 * (N : ℤ)) • (∑ q, (mK m cl k0 q : ℤ) • Point.some _ _ (hnsC q)) +
        (2 * μ) • Point.some _ _ hns0C ≠ 0)
    (hnsq : ∀ q, (WG (algebraMap C K c3) (algebraMap C K c2) (algebraMap C K c1)
      (algebraMap C K c0)).Nonsingular (algebraMap C K c3 * algebraMap C K (c q))
      (algebraMap C K c3 * algebraMap C K (β q)))
    (hns0 : (WG (algebraMap C K c3) (algebraMap C K c2) (algebraMap C K c1)
      (algebraMap C K c0)).Nonsingular (algebraMap C K c3 * 0) (algebraMap C K c3 * algebraMap C K b₀)) :
    ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
      (2 * (N : ℤ)) • (∑ q, (mK m cl k0 q : ℤ) • Point.some _ _ (hnsq q)) +
        (2 * μ) • Point.some _ _ hns0 ≠ 0 := by
  intro N hN μ hrel
  have hself : WG c3 c2 c1 c0 = ((WG c3 c2 c1 c0)⁄C) := by
    simp [WG, FFHeight.longF, Affine.baseChange, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  set ι := (FFHeight.castHom (WG_baseChange (K := K) c3 c2 c1 c0)).comp
    ((Point.map (W' := WG c3 c2 c1 c0) (Algebra.ofId C K)).comp (FFHeight.castHom hself))
  have hι : Function.Injective ι :=
    (FFHeight.castHom_injective _).comp ((Point.map_injective _).comp (FFHeight.castHom_injective _))
  have hq : ∀ q, ι (Point.some _ _ (hnsC q)) = Point.some _ _ (hnsq q) := fun q ↦ by
    simp only [ι, AddMonoidHom.comp_apply, FFHeight.castHom_some, Point.map_some]
    simp [Algebra.ofId_apply]
  have h0 : ι (Point.some _ _ hns0C) = Point.some _ _ hns0 := by
    simp only [ι, AddMonoidHom.comp_apply, FFHeight.castHom_some, Point.map_some]
    simp [Algebra.ofId_apply]
  apply hgrpC N hN μ
  apply hι
  rw [map_add, map_zsmul, map_zsmul, map_sum, map_zero]
  simp only [map_zsmul, hq, h0]
  exact hrel

end Descent

end SuperData

end Differential
