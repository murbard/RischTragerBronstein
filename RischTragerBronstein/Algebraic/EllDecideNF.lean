import RischTragerBronstein.Algebraic.EllDecideADK
import RischTragerBronstein.Algebraic.NFRoots

/-!
# Elliptic integrals `∫ A dx / (D y)` over a given number field, automatically

`ellDecideNF` computes the splitting data inside `K = ℚ[θ]/(f)` itself: the roots of `D` in `K`
(`rootsIn`, Trager's norm method) and, for each root `α`, a square root of `p(α)` in `K`
(`rootsIn` on `Y² − p(α)`), then runs `ellDecideADK`. `ellDecideNF_spec`: every answer is
correct. `ellDecideNF_ne_none`: if `D` is squarefree and splits over `K`, and `p` takes non-zero
square values in `K` at the roots of `D`, the procedure answers.
-/

open Polynomial Differential

namespace EllQuad

open CPoly EllDV NFC

variable (f : CPoly ℚ) [hf : Fact (Irreducible (toPoly f))]

/-- `Y² − w`. -/
def sqPoly (w : NF f) : CPoly (NF f) := [-w, 0, 1]

/-- A square root of `w` in `K`, if any. -/
noncomputable def sqrtNF (w : NF f) : Option (NF f) := (rootsIn f (sqPoly f w)).bind List.head?

/-- The ordinates `β` with `β² = p(α)`. -/
noncomputable def ordsNF (a b c : ℤ) : List (NF f) → Option (List (NF f × NF f))
  | [] => some []
  | α :: t =>
    match sqrtNF f (α ^ 3 + (a : NF f) * α ^ 2 + (b : NF f) * α + (c : NF f)), ordsNF a b c t with
    | some β, some m => some ((α, β) :: m)
    | _, _ => none

/-- **The procedure over `K`** (`N`: the torsion bound at an auxiliary prime). -/
noncomputable def ellDecideNF (a b c : ℤ) (A D : CPoly ℚ) (N : ℕ) : Option Bool :=
  match rootsIn f (liftK D) with
  | none => none
  | some rs =>
    match ordsNF f a b c rs.dedup with
    | some pts => ellDecideADK a b c A D pts N
    | none => none


/-! ### Correctness -/

section Spec

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **Correctness of `ellDecideNF`.** -/
theorem ellDecideNF_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    (a b c : ℤ) (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (hy : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) (hgen : ∀ z : E, InHyp Kc x y z)
    (ι : NF f →+* Kc) (A D : CPoly ℚ) (p0 : ℕ) [Fact p0.Prime]
    (hp02 : p0 ≠ 2) (hgood : goodRedMod p0 a b c) (φ : NF f →ₐ[ℚ] ℚ_[p0]) (N : ℕ)
    (hN : Fintype.card (Option (RedPts p0 a b c)) ≤ N)
    (ans : Bool) (h : ellDecideNF f a b c A D N = some ans) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  unfold ellDecideNF at h
  split at h
  · cases h
  split at h
  · exact ellDecideADK_spec hC hCall x y hx a b c hsq hy hgen ι A D _ p0 hp02 hgood φ N hN ans h
  · cases h

end Spec

/-! ### Completeness -/

lemma sqPoly_squarefree {w : NF f} (hw : w ≠ 0) : Squarefree (toPoly (sqPoly f w)) := by
  have he : toPoly (sqPoly f w) = X ^ 2 - C w := by simp [sqPoly, CPoly.toPoly]; ring
  rw [he]
  exact (separable_X_pow_sub_C w (by norm_num) hw).squarefree

lemma sqrtNF_spec {w β : NF f} (h : sqrtNF f w = some β) : β * β = w := by
  unfold sqrtNF at h
  obtain ⟨rs, hrs, hβ⟩ := Option.bind_eq_some_iff.mp h
  have hmem := List.mem_of_mem_head? hβ
  have := rootsIn_sound f (sqPoly f w) hrs β hmem
  simp [sqPoly, CPoly.toPoly] at this
  linear_combination this

lemma sqrtNF_ne_none {w β : NF f} (hβ : β * β = w) (hw : w ≠ 0) : sqrtNF f w ≠ none := by
  obtain ⟨rs, hrs, hall⟩ := rootsIn_complete f (sqPoly f w) (sqPoly_squarefree f hw)
  have hmem : β ∈ rs := hall β (by simp [sqPoly, CPoly.toPoly]; linear_combination hβ)
  unfold sqrtNF
  rw [hrs]
  simp only [Option.bind_some, ne_eq]
  cases rs with
  | nil => simp at hmem
  | cons r t => simp

lemma ordsNF_spec {a b c : ℤ} : ∀ {rs : List (NF f)} {pts : List (NF f × NF f)},
    ordsNF f a b c rs = some pts → pts.map Prod.fst = rs ∧
      ∀ q ∈ pts, q.2 * q.2 = q.1 ^ 3 + (a : NF f) * q.1 ^ 2 + (b : NF f) * q.1 + (c : NF f)
  | [], pts, h => by simp only [ordsNF, Option.some.injEq] at h; subst h; simp
  | α :: t, pts, h => by
    simp only [ordsNF] at h
    split at h
    · rename_i β m h1 h2
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨e1, e2⟩ := ordsNF_spec h2
      refine ⟨by simp [e1], fun q hq ↦ ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact sqrtNF_spec f h1
      · exact e2 q hq
    · cases h

lemma ordsNF_ne_none {a b c : ℤ} : ∀ {rs : List (NF f)},
    (∀ α ∈ rs, ∃ β : NF f, β ≠ 0 ∧
      β * β = α ^ 3 + (a : NF f) * α ^ 2 + (b : NF f) * α + (c : NF f)) →
    ordsNF f a b c rs ≠ none
  | [], _ => by simp [ordsNF]
  | α :: t, h => by
    obtain ⟨β, hβ0, hβ⟩ := h α List.mem_cons_self
    obtain ⟨β', h1⟩ := Option.ne_none_iff_exists'.mp
      (sqrtNF_ne_none f hβ (by rw [← hβ]; exact mul_ne_zero hβ0 hβ0))
    obtain ⟨m, h2⟩ := Option.ne_none_iff_exists'.mp
      (ordsNF_ne_none fun α' hα' ↦ h α' (List.mem_cons_of_mem _ hα'))
    simp [ordsNF, h1, h2]

/-- **Completeness of `ellDecideNF`**: if `D` is squarefree and splits over `K`, and `p` takes
non-zero square values in `K` at its roots, the procedure answers. -/
theorem ellDecideNF_ne_none (a b c : ℤ)
    (hsq : Squarefree (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)))
    (A D : CPoly ℚ) (hDsq : Squarefree (toPoly D)) (lc : NF f) (rs0 : List (NF f))
    (hsplit : (toPoly D).map (algebraMap ℚ (NF f)) = C lc * (rs0.map fun r ↦ X - C r).prod)
    (hpt : ∀ α : NF f, aeval α (toPoly D) = 0 →
      ∃ β : NF f, β ≠ 0 ∧ β * β = α ^ 3 + (a : NF f) * α ^ 2 + (b : NF f) * α + (c : NF f))
    (N : ℕ) : ellDecideNF f a b c A D N ≠ none := by
  classical
  have hD0 : toPoly D ≠ 0 := hDsq.ne_zero
  have hgL : toPoly (liftK (K := NF f) D) = (toPoly D).map (algebraMap ℚ (NF f)) := toPoly_liftK D
  have hgsq : Squarefree (toPoly (liftK (K := NF f) D)) := by
    rw [hgL]; exact ((PerfectField.separable_iff_squarefree).mpr hDsq).map.squarefree
  obtain ⟨rs, hrs, hall⟩ := rootsIn_complete f _ hgsq
  have hroot : ∀ α, aeval α (toPoly D) = 0 ↔ α ∈ rs := by
    intro α
    constructor
    · intro h; apply hall; rw [hgL, eval_map_algebraMap]; exact h
    · intro h; have := rootsIn_sound f _ hrs α h; rwa [hgL, eval_map_algebraMap] at this
  have hsqK : Squarefree ((toPoly D).map (algebraMap ℚ (NF f))) :=
    ((PerfectField.separable_iff_squarefree).mpr hDsq).map.squarefree
  -- the given splitting has distinct roots, equal to the found ones
  have hlc : lc ≠ 0 := by
    rintro rfl; rw [C_0, zero_mul, Polynomial.map_eq_zero_iff (algebraMap ℚ (NF f)).injective] at hsplit
    exact hD0 hsplit
  have hnd0 : rs0.Nodup := by
    rw [List.nodup_iff_sublist]
    intro r hr
    have hdvd : (X - C r) * (X - C r) ∣ (toPoly D).map (algebraMap ℚ (NF f)) := by
      rw [hsplit]
      refine Dvd.dvd.mul_left ?_ _
      simpa using (hr.map (fun r ↦ X - C r)).prod_dvd_prod
    exact (irreducible_X_sub_C r).not_isUnit (hsqK _ hdvd)
  have hmem0 : ∀ α, α ∈ rs0 ↔ α ∈ rs.dedup := by
    intro α
    rw [List.mem_dedup, ← hroot, ← eval_map_algebraMap, hsplit, eval_mul, eval_C,
      eval_list_prod, List.map_map]
    constructor
    · intro h
      apply mul_eq_zero_of_right
      apply List.prod_eq_zero
      exact List.mem_map.mpr ⟨α, h, by simp⟩
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hlc
      · obtain ⟨r, hr, hr0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h)
        simp only [Function.comp_apply, eval_sub, eval_X, eval_C, sub_eq_zero] at hr0
        rwa [hr0]
  have hperm : rs0.Perm rs.dedup := (List.perm_ext_iff_of_nodup hnd0 (List.nodup_dedup _)).mpr hmem0
  -- the leading coefficient
  have hlcD : lc = (((lead (trim D) : ℚ)) : NF f) := by
    have hmon : (rs0.map fun r ↦ X - C r).prod.Monic := by
      have := monic_multiset_prod_of_monic (rs0 : Multiset (NF f)) (fun r ↦ X - C r)
        (fun r _ ↦ monic_X_sub_C r)
      simpa [Multiset.map_coe, Multiset.prod_coe] using this
    have := congrArg leadingCoeff hsplit
    rw [leadingCoeff_map_of_injective (algebraMap ℚ (NF f)).injective, leadingCoeff_mul,
      leadingCoeff_C, hmon.leadingCoeff, mul_one] at this
    rw [← this, show lead (trim D) = lcT D from rfl, lcT_eq]; rfl
  -- run the procedure
  unfold ellDecideNF
  rw [hrs]
  simp only
  obtain ⟨pts, hpts⟩ := Option.ne_none_iff_exists'.mp (ordsNF_ne_none f (a := a) (b := b) (c := c)
    fun α hα ↦ hpt α ((hroot α).mpr (List.mem_dedup.mp hα)))
  rw [hpts]
  simp only
  obtain ⟨e1, e2⟩ := ordsNF_spec f hpts
  refine ellDecideADK_ne_none a b c hsq A D hD0 pts ?_ (fun q hq ↦ ⟨e2 q hq, fun h0 ↦ ?_⟩) ?_ N
  · rw [e1, hsplit, hlcD, hperm.map _ |>.prod_eq]
  · have hmem : q.1 ∈ rs.dedup := e1 ▸ List.mem_map_of_mem hq
    obtain ⟨β, hβ0, hβ⟩ := hpt q.1 ((hroot _).mpr (List.mem_dedup.mp hmem))
    have := e2 q hq
    rw [h0, zero_mul, ← hβ] at this
    exact hβ0 (mul_self_eq_zero.mp this.symm)
  · rw [e1]; exact List.nodup_dedup _

end EllQuad
