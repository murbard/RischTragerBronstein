import RischTragerBronstein.Mixed.KRFourier
import RischTragerBronstein.Mixed.KPBranchClass
import RischTragerBronstein.Algebraic.Ramanujan

/-!
# The points over `x = 0` of `yⁿ = p(x)` and the action of `σ`

`ζ ∈ C` a primitive `n`-th root of unity, `β₀ⁿ = p(0) ≠ 0`; the points over `x = 0` are
`P_k = (0, ζᵏ β₀)` (`over_zero_k`). For `w ∈ C(x, y)`:

* `ordAt_conj_br`: `σ` does not change the orders at the branch points
  (`embB ∘ σ = scaleL ∘ embB`);
* `Supp w`: `w` has order `0` at every place over `x ≠ 0`; `rv w k = ord_{P_k} w`;
  `rv (σ_m w) k = rv w (k + m)` (`rv_cj`), `Supp` is stable under `σ`, products, powers;
* `const_of_rv`: `Supp w` and `rv w = 0` make `w` an element of `C`, so `four j (dl w) = 0`.
-/

open Polynomial IntermediateField LaurentSeries

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L) (ω : C[X]) (hx : S.x′ = aeval S.x ω)
variable (ζ : C) (hζ : IsPrimitiveRoot ζ S.n)

include hζ in
lemma algζ_ne : algebraMap C K ζ ≠ 0 := by
  intro h
  have : (algebraMap C K ζ) ^ S.n = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  rw [h, zero_pow S.hn.ne'] at this; exact zero_ne_one this

include hζ in
lemma algζ_prim : IsPrimitiveRoot (algebraMap C K ζ) S.n :=
  hζ.map_of_injective (algebraMap C K).injective

include hζ in
/-- **`σ` at a branch point**: `embB ∘ σ_m = scaleL ζᵐ ∘ embB`. -/
lemma embB_conj (m : ℕ) (e γ : K) (he : (S.p.map (algebraMap C K)).eval e = 0) (hγ : γ ≠ 0)
    (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e) :
    (S.embB e γ he hγ hγp).comp (S.cj ζ hζ m) =
      (scaleL (algebraMap C K ζ ^ m) (pow_ne_zero _ (S.algζ_ne ζ hζ))).comp
        (S.embB e γ he hγ hγp) := by
  have hzn : (algebraMap C K ζ ^ m) ^ S.n = 1 := by
    rw [← map_pow, ← map_pow, hpowζ S ζ hζ m, map_one]
  refine S.ringHom_ext_XY _ _ (fun a ↦ ?_) ?_
  · rw [RingHom.comp_apply, RingHom.comp_apply, cj, S.conj_algebraMap, embB, S.embG_algebraMap,
      S.scaleL_embXG_branch _ _ hzn]
  · rw [RingHom.comp_apply, RingHom.comp_apply, cj, S.conj_gen', map_mul, embB, S.embG_gen,
      S.scaleL_branchYe _ _ hzn]
    congr 1
    rw [S.cst_eq, S.embG_algebraMap]
    have hthis : (⟨algebraMap C L (ζ ^ m), IntermediateField.algebraMap_mem _ _⟩ : C⟮S.x⟯) =
        ⟨aeval S.x (Polynomial.C (ζ ^ m)), by rw [aeval_C]; exact IntermediateField.algebraMap_mem _ _⟩ :=
      Subtype.ext (aeval_C S.x _).symm
    letI := algebraAdjoinSimple (F := C) S.x
    have h2 : (⟨aeval S.x (Polynomial.C (ζ ^ m)), by rw [aeval_C]; exact IntermediateField.algebraMap_mem _ _⟩ :
        C⟮S.x⟯) = algebraMap C[X] C⟮S.x⟯ (Polynomial.C (ζ ^ m)) :=
      Subtype.ext (algebraMap_adjoinSimple S.x _).symm
    rw [hthis, h2, S.embXG_algebraMap]
    simp [branchSub, map_pow]

include hζ in
/-- **Orders at the branch points are `σ`-invariant.** -/
lemma ordAt_conj_br (m : ℕ) (w : C⟮S.x⟯⟮S.y⟯) (e : K) (he : (S.p.map (algebraMap C K)).eval e = 0) :
    S.ordAt K (S.cj ζ hζ m w) e 0 = S.ordAt K w e 0 := by
  obtain ⟨γ, hγ, hγp⟩ := S.exists_gamma e he
  rw [S.ordAt_br _ e γ he hγ hγp, S.ordAt_br _ e γ he hγ hγp, ← RingHom.comp_apply,
    S.embB_conj ζ hζ m e γ he hγ hγp, RingHom.comp_apply, order_scaleL]

include hζ in
/-- **Orders of `σ_m w`**: `ord_{(α, β)} σ_m w = ord_{(α, ζᵐ β)} w` (`β ≠ 0`). -/
lemma ordAt_cj (m : ℕ) (w : C⟮S.x⟯⟮S.y⟯) (α β : K) (hβ : β ≠ 0)
    (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    S.ordAt K (S.cj ζ hζ m w) α β = S.ordAt K w α (algebraMap C K ζ ^ m * β) := by
  rw [cj, S.ordAt_conj, map_pow]
  exact hβ
  exact hβp

section Zero

variable (β₀ : K) (hβ₀ : β₀ ≠ 0) (hv0 : β₀ ^ S.n = (S.p.map (algebraMap C K)).eval 0)

/-- The point `P_k = (0, ζᵏ β₀)`. -/
noncomputable def bk (k : ℕ) : K := algebraMap C K ζ ^ k * β₀

include hζ hβ₀ in
lemma bk_ne (k : ℕ) : bk (K := K) ζ β₀ k ≠ 0 := mul_ne_zero (pow_ne_zero _ (S.algζ_ne ζ hζ)) hβ₀

include hζ hv0 in
lemma bk_v (k : ℕ) : bk ζ β₀ k ^ S.n = (S.p.map (algebraMap C K)).eval 0 := by
  rw [bk, mul_pow, ← pow_mul, mul_comm k, pow_mul, ← map_pow, hζ.pow_eq_one, map_one, one_pow,
    one_mul, hv0]

lemma bk_add (k m : ℕ) : algebraMap C K ζ ^ m * bk ζ β₀ k = bk ζ β₀ (k + m) := by
  simp only [bk, pow_add]; ring

include hζ in
lemma bk_mod (k : ℕ) : bk ζ β₀ (k % S.n) = bk ζ β₀ k := by
  have h := (S.algζ_prim (K := K) ζ hζ).pow_eq_one
  simp only [bk]
  conv_rhs => rw [← Nat.mod_add_div k S.n, pow_add, pow_mul, h, one_pow, mul_one]

include hζ hβ₀ hv0 in
/-- **The points over `x = 0`** are the `P_k`, `k < n`. -/
lemma over_zero_k (β : K) (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval 0) :
    ∃ k < S.n, β = bk ζ β₀ k := by
  haveI : NeZero S.n := ⟨S.hn.ne'⟩
  have h1 : (β / β₀) ^ S.n = 1 := by
    rw [div_pow, hv, ← hv0, div_self (pow_ne_zero _ hβ₀)]
  obtain ⟨k, hk, hkeq⟩ := (S.algζ_prim (K := K) ζ hζ).eq_pow_of_pow_eq_one h1
  exact ⟨k, hk, by rw [bk, hkeq, div_mul_cancel₀ _ hβ₀]⟩

/-- `w` has order `0` at every place over `x ≠ 0`. -/
def Supp (w : C⟮S.x⟯⟮S.y⟯) : Prop :=
  ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 → S.ordAt K w α β = 0

/-- The orders at the points over `x = 0`. -/
noncomputable def rv (w : C⟮S.x⟯⟮S.y⟯) (k : ℕ) : ℤ := S.ordAt K w 0 (bk ζ β₀ k)

include hζ hβ₀ hv0 in
lemma rv_cj (m : ℕ) (w : C⟮S.x⟯⟮S.y⟯) (k : ℕ) :
    S.rv ζ β₀ (S.cj ζ hζ m w) k = S.rv ζ β₀ w (k + m) := by
  rw [rv, rv, S.ordAt_cj ζ hζ m w 0 _ (S.bk_ne ζ hζ β₀ hβ₀ k) (S.bk_v ζ hζ β₀ hv0 k), bk_add]

include hζ in
lemma supp_cj (m : ℕ) (w : C⟮S.x⟯⟮S.y⟯) (hw : S.Supp (K := K) w) :
    S.Supp (K := K) (S.cj ζ hζ m w) := by
  intro α β hv hα
  by_cases hβ : β = 0
  · subst hβ
    have he : (S.p.map (algebraMap C K)).eval α = 0 := by rw [← hv, zero_pow S.hn.ne']
    rw [S.ordAt_conj_br ζ hζ m w α he]
    exact hw α 0 hv hα
  · rw [S.ordAt_cj ζ hζ m w α β hβ hv]
    exact hw α _ (by rw [mul_pow, ← pow_mul, mul_comm m, pow_mul, ← map_pow, hζ.pow_eq_one,
      map_one, one_pow, one_mul, hv]) hα

lemma supp_mul (u w : C⟮S.x⟯⟮S.y⟯) (hu0 : u ≠ 0) (hw0 : w ≠ 0) (hu : S.Supp (K := K) u)
    (hw : S.Supp (K := K) w) : S.Supp (K := K) (u * w) := fun α β hv hα ↦ by
  rw [S.ordAt_mul hv hu0 hw0, hu α β hv hα, hw α β hv hα, add_zero]

lemma supp_zpow (w : C⟮S.x⟯⟮S.y⟯) (hw : S.Supp (K := K) w) (m : ℤ) :
    S.Supp (K := K) (w ^ m) := fun α β hv hα ↦ by
  rw [S.ordAt_zpow hv, hw α β hv hα, mul_zero]

lemma supp_prod {ι : Type*} (t : Finset ι) (w : ι → C⟮S.x⟯⟮S.y⟯) (hw0 : ∀ i ∈ t, w i ≠ 0)
    (hw : ∀ i ∈ t, S.Supp (K := K) (w i)) : S.Supp (K := K) (∏ i ∈ t, w i) :=
  fun α β hv hα ↦ by
    rw [S.ordAt_prod hv _ _ hw0]
    exact Finset.sum_eq_zero fun i hi ↦ hw i hi α β hv hα

include hζ hv0 in
lemma rv_mul (u w : C⟮S.x⟯⟮S.y⟯) (hu0 : u ≠ 0) (hw0 : w ≠ 0) (k : ℕ) :
    S.rv ζ β₀ (u * w) k = S.rv ζ β₀ u k + S.rv ζ β₀ w k := by
  rw [rv, rv, rv]
  exact S.ordAt_mul (S.bk_v ζ hζ β₀ hv0 k) hu0 hw0

include hζ hv0 in
lemma rv_zpow (w : C⟮S.x⟯⟮S.y⟯) (m : ℤ) (k : ℕ) :
    S.rv ζ β₀ (w ^ m) k = m * S.rv ζ β₀ w k := by
  rw [rv, rv]
  exact S.ordAt_zpow (S.bk_v ζ hζ β₀ hv0 k) w m

include hζ hv0 in
lemma rv_prod {ι : Type*} (t : Finset ι) (w : ι → C⟮S.x⟯⟮S.y⟯) (hw0 : ∀ i ∈ t, w i ≠ 0) (k : ℕ) :
    S.rv ζ β₀ (∏ i ∈ t, w i) k = ∑ i ∈ t, S.rv ζ β₀ (w i) k := by
  simp only [rv]
  exact S.ordAt_prod (S.bk_v ζ hζ β₀ hv0 k) _ _ hw0

include hζ in
lemma rv_mod (w : C⟮S.x⟯⟮S.y⟯) (k : ℕ) : S.rv ζ β₀ w (k % S.n) = S.rv ζ β₀ w k := by
  rw [rv, rv, S.bk_mod ζ hζ β₀ k]

include hζ hβ₀ hv0 in
/-- **An element without zeros and poles at finite places is in `C`.** -/
lemma const_of_rv (hcop : Nat.Coprime S.n S.p.natDegree) (w : C⟮S.x⟯⟮S.y⟯) (hw0 : w ≠ 0)
    (hw : S.Supp (K := K) w) (hr : ∀ k < S.n, S.rv ζ β₀ w k = 0) :
    ∃ γ : C, γ ≠ 0 ∧ w = S.cst γ := by
  obtain ⟨γ, hγ⟩ := S.const_of_ordAt_zero K hcop w hw0 (fun α β hv ↦ by
    by_cases hα : α = 0
    · subst hα
      obtain ⟨k, hk, rfl⟩ := S.over_zero_k ζ hζ β₀ hβ₀ hv0 β hv
      exact hr k hk
    · exact hw α β hv hα)
  refine ⟨γ, fun h ↦ hw0 (Subtype.ext (by rw [hγ, h, map_zero]; rfl)), Subtype.ext hγ⟩

include hζ hβ₀ hv0 in
/-- **The projection of `dl w` vanishes when `w` has no divisor.** -/
lemma four_dl_zero (hcop : Nat.Coprime S.n S.p.natDegree) (j : Fin S.n) (hj : (j : ℕ) ≠ 0)
    (w : C⟮S.x⟯⟮S.y⟯) (hw0 : w ≠ 0) (hw : S.Supp (K := K) w)
    (hr : ∀ k < S.n, S.rv ζ β₀ w k = 0) : S.four ζ hζ j (S.dl ω hx w) = 0 := by
  obtain ⟨γ, -, rfl⟩ := S.const_of_rv ζ hζ β₀ hβ₀ hv0 hcop w hw0 hw hr
  rw [S.dl_cst ω hx, S.four_cst ζ hζ j hj]

end Zero

end SuperData

end Differential
