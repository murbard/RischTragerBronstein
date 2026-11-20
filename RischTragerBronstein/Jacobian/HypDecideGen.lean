import RischTragerBronstein.Jacobian.HypDecideR
import RischTragerBronstein.Jacobian.HypDecideRComplete
import RischTragerBronstein.Algebraic.EllGenComplete

/-!
# The genus-`g` decision for `∫ A dx / (D √f)` with `D` split over `ℚ`

`hypDecideGen f g A D`: the Hermite solver of `EllGen` (`ellHermite`, generic in the degree of
`f`: Hermite reduction and partial fractions in one linear system, re-checked by `genCheck`),
then `hypDecideR` on the residues.

* `hypDecideGen_spec`: every answer is correct;
* `hypDecideGen_ne_none`: for `D` split over `ℚ` whose roots off the branch points lie under
  rational points, the procedure answers;
* `hypDecideGen_decides`: hence a decision procedure on this class.
-/

open Polynomial CPoly CPoly.Kron EllAlgo

namespace Jac

/-- **The procedure.** -/
def hypDecideGen (f : List ℤ) (g : ℕ) (A D : CPoly ℚ) : Option Bool :=
  let p : CPoly ℚ := f.map (Int.castRingHom ℚ)
  match ellHermite p A D with
  | some (W, B₀, pts, D') =>
    if genCheck p A D W (fracG B₀ D' pts) && decide (D' ≠ 0) then hypDecideR f g pts B₀ D'
    else none
  | none => none

section Spec

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **Every answer of `hypDecideGen` is correct.** -/
theorem hypDecideGen_spec (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    {f : List ℤ} {g : ℕ} {A D : CPoly ℚ} {ans : Bool} (h : hypDecideGen f g A D = some ans)
    (hy : y ^ 2 = aeval x ((toPoly f).map (Int.castRingHom ℚ)))
    (hgen : ∀ z : E, InHyp Kc x y z) :
    ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y)) := by
  have htrK : Transcendental Kc x :=
    transcendental_of_deriv_ne_zero hC (by rw [hx]; exact one_ne_zero)
  have hne : ∀ Q : ℚ[X], Q ≠ 0 → aeval x Q ≠ 0 := fun Q hP ↦ by
    rw [← aeval_map_algebraMap Kc]
    exact aeval_ne_zero_of_tr x htrK ((Polynomial.map_ne_zero_iff
      (algebraMap ℚ Kc).injective).mpr hP)
  have hpf : toPoly (f.map (Int.castRingHom ℚ)) = (toPoly f).map (Int.castRingHom ℚ) :=
    toPoly_map_list _ _
  have hy' : y ^ 2 = aeval x (toPoly (f.map (Int.castRingHom ℚ))) := by rw [hpf]; exact hy
  unfold hypDecideGen at h
  dsimp only at h
  split at h
  · rename_i W B₀ pts D' _
    split_ifs at h with hchk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨hchk, hD'⟩ := hchk
    have W' := hypDecideR_wf h
    have hy0 : y ≠ 0 := by
      rintro rfl
      apply hne _ W'.hsq.ne_zero
      rw [← hy]; ring
    have hans := hypDecideR_spec hC hCall x y hx hD' h hy hgen
    unfold genCheck at hchk
    simp only [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, isZero_iff] at hchk
    obtain ⟨⟨hD0, hG0⟩, hbeq⟩ := hchk
    have hid := (beq_iff _ _).mp hbeq
    have h2 : toPoly ([2] : CPoly ℚ) = 2 := by
      rw [toPoly_cons, toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
    simp only [toPoly_mul, toPoly_add, toPoly_sub, toPoly_deriv, h2] at hid
    have e := gen_identity x y hx (toPoly (f.map (Int.castRingHom ℚ))) (toPoly A) (toPoly D)
      (toPoly W) (toPoly D) (toPoly (fracG B₀ D' pts).1) (toPoly (fracG B₀ D' pts).2) hy' hy0
      (hne _ hD0) (hne _ hD0) (hne _ hG0) (by linear_combination hid)
    obtain ⟨_, hfr⟩ := fracG_spec x hne B₀ D' pts
    rw [e, hasElementaryIntegral_deriv_add_iff', hfr]
    exact hans
  · exact absurd h (by simp)

end Spec

/-- **Completeness of `hypDecideGen`**: for `D` split over `ℚ` whose roots off the branch points
lie under rational points of the curve, the procedure answers. -/
theorem hypDecideGen_ne_none {f : List ℤ} {g : ℕ} (hlen : f.length = 2 * g + 2)
    (hlc : f.getD (2 * g + 1) 0 ≠ 0) (hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ)))
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (hsplit : (toPoly D).Splits)
    (hrat : ∀ α : ℚ, (toPoly D).eval α = 0 → ((toPoly f).map (Int.castRingHom ℚ)).eval α ≠ 0 →
      ∃ β : ℚ, β ^ 2 = ((toPoly f).map (Int.castRingHom ℚ)).eval α) :
    hypDecideGen f g A D ≠ none := by
  set p : CPoly ℚ := f.map (Int.castRingHom ℚ) with hpdef
  have hpf : toPoly p = (toPoly f).map (Int.castRingHom ℚ) := toPoly_map_list _ _
  have hev : ∀ α : ℚ, residuePts.evalQ p α = (toPoly p).eval α := evalQ_eq' p
  have hp1 : 1 ≤ (toPoly p).natDegree := by
    rw [hpf, natDegree_map_eq_of_injective (RingHom.injective_int _), natDegree_of_list hlen hlc]
    omega
  obtain ⟨⟨W, B₀, αs, cs⟩, hH⟩ := Option.ne_none_iff_exists'.mp
    (ellHermiteRaw_ne_none p A D (by rw [hpf]; exact hsq) hp1 hD hsplit)
  obtain ⟨hαs, hl, hid⟩ := ellHermiteRaw_spec _ _ _ _ _ _ _ hD hH
  have hnd : αs.Nodup := hαs ▸ (List.nodup_dedup _).filter _
  obtain ⟨pts, D', hR, hD'0, hon, hfst, hres⟩ := residuePts_ok p αs cs (fun q hq _ ↦ by
    have hα := List.of_mem_zip hq
    obtain ⟨h1, h2⟩ := mem_αs (hαs ▸ hα.1)
    rw [hpf] at h2
    obtain ⟨β, hβ⟩ := hrat q.1 h1 h2
    exact ⟨β, by rw [hev, hpf, hβ], by rw [hev, hpf]; exact h2⟩)
  have hHerm : ellHermite p A D = some (W, B₀, pts, D') := by
    rw [ellHermite_eq, hH]; simp [hR]
  obtain ⟨hG2, hG⟩ := fracG_poly B₀ D' pts αs cs hl (hres ▸ List.Perm.refl _)
  have hchk := genCheck_of_poly p A D W B₀ (fracG B₀ D' pts) αs cs hD hG2 hid hG
  unfold hypDecideGen
  dsimp only
  rw [hHerm]
  dsimp only
  rw [if_pos (by rw [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hchk, hD'0⟩)]
  refine hypDecideR_ne_none B₀ D' hlen hlc hsq (fun q hq ↦ ?_) ?_
  · obtain ⟨h1, h2⟩ := hon q hq
    refine ⟨by rw [← hpf, ← hev, h1], h2, fun hz ↦ ?_⟩
    have hm : ((q.2.2 : ℚ) / D' * q.2.1, q.1) ∈
        ((αs.zip cs).filter fun q ↦ q.2 ≠ 0).map fun q ↦ (q.2, q.1) := by
      rw [← hres]; exact List.mem_map_of_mem hq
    obtain ⟨r, hr, hre⟩ := List.mem_map.mp hm
    have hr0 : r.2 ≠ 0 := by simpa using (List.mem_filter.mp hr).2
    simp only [Prod.mk.injEq] at hre
    apply hr0
    rw [hre.1, hz]; simp
  · rw [hfst]; exact nodup_data αs cs hnd hl

section Decision

open Differential

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

/-- **The decision theorem in any genus**: for `y² = f(x)`, `f ∈ ℤ[x]` squarefree of degree
`2g + 1`, and `∫ A dx / (D √f)` with `D` split over `ℚ` and every root of `D` off the branch
points under a rational point, `hypDecideGen` answers `some b`, and `b = true` iff the integral is
elementary. -/
theorem hypDecideGen_decides (hC : ∀ c : Kc, c′ = 0)
    (hCall : ∀ z : E, z′ = 0 → z ∈ Set.range (algebraMap Kc E)) (x y : E) (hx : x′ = 1)
    {f : List ℤ} {g : ℕ} (hlen : f.length = 2 * g + 2) (hlc : f.getD (2 * g + 1) 0 ≠ 0)
    (hsq : Squarefree ((toPoly f).map (Int.castRingHom ℚ)))
    (hy : y ^ 2 = aeval x ((toPoly f).map (Int.castRingHom ℚ))) (hgen : ∀ z : E, InHyp Kc x y z)
    (A D : CPoly ℚ) (hD : toPoly D ≠ 0) (hsplit : (toPoly D).Splits)
    (hrat : ∀ α : ℚ, (toPoly D).eval α = 0 → ((toPoly f).map (Int.castRingHom ℚ)).eval α ≠ 0 →
      ∃ β : ℚ, β ^ 2 = ((toPoly f).map (Int.castRingHom ℚ)).eval α) :
    ∃ ans : Bool, hypDecideGen f g A D = some ans ∧
      (ans = true ↔ HasElementaryIntegral (aeval x (toPoly A) / (aeval x (toPoly D) * y))) := by
  obtain ⟨ans, hans⟩ := Option.ne_none_iff_exists'.mp
    (hypDecideGen_ne_none hlen hlc hsq A D hD hsplit hrat)
  exact ⟨ans, hans, hypDecideGen_spec hC hCall x y hx hans hy hgen⟩

end Decision

end Jac
