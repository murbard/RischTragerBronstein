import RischTragerBronstein.Mixed.KRBasic
import RischTragerBronstein.Mixed.KWProj

/-!
# The `yʲ`-projection on `C(x, y)`, `yⁿ = p(x)`, and logarithmic derivatives

`ζ ∈ C` a primitive `n`-th root of unity, `σ_k = conj ζᵏ` (`y ↦ ζᵏ y`).

* `four j F = ∑_k ζ^{k(n−j)} σ_k F`: `four j (∑ aᵢ yⁱ) = n aⱼ yʲ` (`four_repr`), so
  `four j (σ_m F) = ζ^{mj} four j F` (`four_cj`), `four j (c) = 0` for `j ≠ 0` (`four_cst`), and
  `four j` commutes with the derivation (`four_dTW`);
* `dl w = w′/w` on `C(x, y)`: multiplicative (`dl_mul`, `dl_zpow`, `dl_prod`), `σ`-equivariant.
-/

open Polynomial IntermediateField

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable (S : SuperData C L) (ω : C[X]) (hx : S.x′ = aeval S.x ω)
variable (ζ : C) (hζ : IsPrimitiveRoot ζ S.n)

include hζ in
lemma hpowζ (k : ℕ) : (ζ ^ k) ^ S.n = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

/-- `σ_k : y ↦ ζᵏ y`. -/
noncomputable def cj (k : ℕ) : C⟮S.x⟯⟮S.y⟯ →+* C⟮S.x⟯⟮S.y⟯ := S.conj (ζ ^ k) (hpowζ S ζ hζ k)

/-- **The projection on the `yʲ`-component** (times `n`). -/
noncomputable def four (j : Fin S.n) (F : C⟮S.x⟯⟮S.y⟯) : C⟮S.x⟯⟮S.y⟯ :=
  ∑ k : Fin S.n, S.cst ((ζ ^ (k : ℕ)) ^ (S.n - j)) * S.cj ζ hζ k F

lemma four_repr (a : Fin S.n → C⟮S.x⟯) (j : Fin S.n) :
    S.four ζ hζ j (∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ)) =
      (S.n : C⟮S.x⟯⟮S.y⟯) * (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a j) *
        AdjoinSimple.gen C⟮S.x⟯ S.y ^ (j : ℕ)) :=
  S.fourier ζ hζ a j

lemma four_add (j : Fin S.n) (F G : C⟮S.x⟯⟮S.y⟯) :
    S.four ζ hζ j (F + G) = S.four ζ hζ j F + S.four ζ hζ j G := by
  simp only [four, map_add, mul_add, Finset.sum_add_distrib]

lemma four_sub (j : Fin S.n) (F G : C⟮S.x⟯⟮S.y⟯) :
    S.four ζ hζ j (F - G) = S.four ζ hζ j F - S.four ζ hζ j G := by
  simp only [four, map_sub, mul_sub, Finset.sum_sub_distrib]

lemma four_zero (j : Fin S.n) : S.four ζ hζ j 0 = 0 := by simp [four]

lemma four_sum (j : Fin S.n) {ι : Type*} (t : Finset ι) (F : ι → C⟮S.x⟯⟮S.y⟯) :
    S.four ζ hζ j (∑ i ∈ t, F i) = ∑ i ∈ t, S.four ζ hζ j (F i) := by
  simp only [four, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma four_cst_mul (j : Fin S.n) (e : C) (F : C⟮S.x⟯⟮S.y⟯) :
    S.four ζ hζ j (S.cst e * F) = S.cst e * S.four ζ hζ j F := by
  simp only [four, map_mul, cj, S.conj_cst, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

lemma four_intCast_mul (j : Fin S.n) (e : ℤ) (F : C⟮S.x⟯⟮S.y⟯) :
    S.four ζ hζ j ((e : C⟮S.x⟯⟮S.y⟯) * F) = (e : C⟮S.x⟯⟮S.y⟯) * S.four ζ hζ j F := by
  have h : ((e : C⟮S.x⟯⟮S.y⟯)) = S.cst (e : C) := Subtype.ext (by simp [cst])
  rw [h, four_cst_mul]

/-- **Equivariance**: `four j (σ_m F) = ζ^{mj} four j F`. -/
lemma four_cj (j : Fin S.n) (m : ℕ) (F : C⟮S.x⟯⟮S.y⟯) :
    S.four ζ hζ j (S.cj ζ hζ m F) = S.cst (ζ ^ (m * (j : ℕ))) * S.four ζ hζ j F := by
  obtain ⟨a, rfl⟩ := S.power_repr F
  have e1 : S.cj ζ hζ m (∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ)) = ∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯
        (⟨algebraMap C L (ζ ^ (m * (i : ℕ))), IntermediateField.algebraMap_mem _ _⟩ * a i) *
        AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ) := by
    rw [cj, S.conj_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, ← S.cst_eq, ← pow_mul]
    ring
  rw [e1, four_repr, four_repr, map_mul, ← S.cst_eq]
  ring

lemma four_cst (j : Fin S.n) (hj : (j : ℕ) ≠ 0) (e : C) : S.four ζ hζ j (S.cst e) = 0 := by
  letI := algebraAdjoinSimple (F := C) S.x
  have h0 : 0 < S.n := S.hn
  set a : Fin S.n → C⟮S.x⟯ := fun i ↦ if (i : ℕ) = 0 then
    ⟨algebraMap C L e, IntermediateField.algebraMap_mem _ _⟩ else 0 with ha
  have hrepr : S.cst e = ∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ) := by
    rw [Finset.sum_eq_single ⟨0, h0⟩]
    · simp [ha, S.cst_eq]
    · intro i _ hi
      have : (i : ℕ) ≠ 0 := fun h ↦ hi (Fin.ext h)
      simp [ha, this]
    · simp
  rw [hrepr, four_repr]
  simp [ha, hj]

include hx in
/-- `four j` commutes with the derivation. -/
lemma four_dTW (j : Fin S.n) (V : C⟮S.x⟯⟮S.y⟯) :
    S.four ζ hζ j (S.dTW ω hx V) = S.dTW ω hx (S.four ζ hζ j V) := by
  simp only [four, S.dTW_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [S.dTW_cst_mul ω hx _ (LaurentSeries.deriv_root_of_unity S.hn (by
    rw [← pow_mul, mul_comm, pow_mul, hpowζ S ζ hζ, one_pow])), cj, S.conj_derivW ω hx]

/-- The logarithmic derivative on `C(x, y)`. -/
noncomputable def dl (w : C⟮S.x⟯⟮S.y⟯) : C⟮S.x⟯⟮S.y⟯ := S.dTW ω hx w * w⁻¹

lemma coe_dl (w : C⟮S.x⟯⟮S.y⟯) : ((S.dl ω hx w : C⟮S.x⟯⟮S.y⟯) : L) = logDeriv (w : L) := by
  simp [dl, coe_dTW, logDeriv, div_eq_mul_inv]

lemma dl_ext {u w : C⟮S.x⟯⟮S.y⟯} (h : logDeriv (u : L) = logDeriv (w : L)) :
    S.dl ω hx u = S.dl ω hx w := Subtype.ext (by rw [coe_dl, coe_dl, h])

lemma dl_mul (u w : C⟮S.x⟯⟮S.y⟯) (hu : u ≠ 0) (hw : w ≠ 0) :
    S.dl ω hx (u * w) = S.dl ω hx u + S.dl ω hx w := by
  have huL : (u : L) ≠ 0 := fun h ↦ hu (Subtype.ext h)
  have hwL : (w : L) ≠ 0 := fun h ↦ hw (Subtype.ext h)
  apply Subtype.ext
  rw [IntermediateField.coe_add, coe_dl, coe_dl, coe_dl, IntermediateField.coe_mul,
    logDeriv_mul _ _ huL hwL]

lemma dl_zpow (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0) (m : ℤ) :
    S.dl ω hx (w ^ m) = (m : C⟮S.x⟯⟮S.y⟯) * S.dl ω hx w := by
  have hwL : (w : L) ≠ 0 := fun h ↦ hw (Subtype.ext h)
  apply Subtype.ext
  rw [IntermediateField.coe_mul, coe_dl, coe_dl,
    show ((w ^ m : C⟮S.x⟯⟮S.y⟯) : L) = (w : L) ^ m from map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val w m,
    logDeriv_zpow' _ hwL]
  simp

lemma dl_prod {ι : Type*} (t : Finset ι) (w : ι → C⟮S.x⟯⟮S.y⟯) (hw : ∀ i ∈ t, w i ≠ 0) :
    S.dl ω hx (∏ i ∈ t, w i) = ∑ i ∈ t, S.dl ω hx (w i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    apply Subtype.ext; simp [coe_dl]
  | insert a t hat ih =>
    rw [Finset.prod_insert hat, Finset.sum_insert hat,
      S.dl_mul ω hx _ _ (hw a (Finset.mem_insert_self a t))
        (Finset.prod_ne_zero_iff.mpr fun i hi ↦ hw i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hw i (Finset.mem_insert_of_mem hi)]

include hx in
lemma dl_cj (m : ℕ) (w : C⟮S.x⟯⟮S.y⟯) :
    S.dl ω hx (S.cj ζ hζ m w) = S.cj ζ hζ m (S.dl ω hx w) := by
  simp only [dl, cj, map_mul, map_inv₀, S.conj_derivW ω hx]

lemma dl_cst (γ : C) : S.dl ω hx (S.cst γ) = S.cst (logDeriv γ) := by
  apply Subtype.ext
  rw [coe_dl]
  change logDeriv (algebraMap C L γ) = algebraMap C L (logDeriv γ)
  rw [logDeriv_algebraMap]

lemma cj_ne_zero (m : ℕ) (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0) : S.cj ζ hζ m w ≠ 0 :=
  (_root_.map_ne_zero _).mpr hw

end SuperData

end Differential
