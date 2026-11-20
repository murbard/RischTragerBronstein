import RischTragerBronstein.Jacobian.TorsionDecideK

/-!
# Good reduction of a curve and a divisor over a number field

For `K = NF M`, a curve `y² = f(x)` with `f ∈ K[x]`, a prime `p`, a simple root `s` of `mZ`
modulo `p`, and a divisor `Γ` over `K`, `baseCheckKF` checks: the coefficients of `f` are
`p`-integral and the reduced curve `redF p s f` has degree `2g + 1`; base points `E₀` with
integer abscissae are good modulo `p`; the coordinates of `Γ` are `p`-integral with good
reductions. `baseCheckKF_spec` gives the lifted curve `F ∈ ℤ_p[x]` and the data used by
`torsion_iff_two_primes` / `not_torsion_of_orders`, and `residue_iff_principalCF` relates
principality over the residue field to `principalC` over `𝔽_p`.
-/

open Polynomial CPoly CPoly.Kron

namespace Jac

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

/-- The reduced curve over `𝔽_p`. -/
def redF (p : ℕ) (s : ZMod p) (f : CPoly (NFC.NF M)) : CPoly (ZMod p) :=
  f.map fun c ↦ redL p s c.1

/-- The good-reduction conditions at `p` for a curve and a divisor over `K = NF M`. -/
abbrev baseCheckKF (p : ℕ) [Fact p.Prime] (mZ : List ℤ) (s : ZMod p) (f : CPoly (NFC.NF M))
    (g : ℕ) (Γ : EDiv (NFC.NF M)) (xs ys : List ℤ) : Prop :=
  p ≠ 2 ∧ f.length = 2 * g + 2 ∧ (∀ c ∈ f, pIntL p c.1 = true) ∧
    redL p s (f.getD (2 * g + 1) 0).1 ≠ 0 ∧ xs.length = g ∧ ys.length = g ∧
    (∀ i ∈ List.range g, ((ys.getD i 0 : ℤ) : ZMod p) ^ 2 =
      evalC (redF p s f) ((xs.getD i 0 : ℤ) : ZMod p) ∧ ((ys.getD i 0 : ℤ) : ZMod p) ≠ 0) ∧
    xs.Pairwise (fun u v ↦ ((u : ℤ) : ZMod p) ≠ v) ∧
    evalC (castL p mZ) s = 0 ∧ evalC (deriv (castL p mZ)) s ≠ 0 ∧
    (∀ q ∈ Γ, pIntL p q.1.1 = true ∧ pIntL p q.2.1.1 = true ∧ 2 * redL p s q.2.1.1 ≠ 0 ∧
      ∀ x ∈ xs, redL p s q.1.1 - (x : ZMod p) ≠ 0) ∧
    Γ.Pairwise (fun u v ↦ redL p s u.1.1 ≠ redL p s v.1.1)

lemma toZMod_eval {p : ℕ} [Fact p.Prime] (F : ℤ_[p][X]) (a : ℤ_[p]) :
    PadicInt.toZMod (F.eval a) = (F.map PadicInt.toZMod).eval (PadicInt.toZMod a) := by
  rw [eval_map, eval₂_hom]

set_option maxHeartbeats 1600000 in
/-- **The lifted data at a good prime.** -/
theorem baseCheckKF_spec {p : ℕ} [Fact p.Prime] {mZ : List ℤ}
    (hmZ : toPoly M = (toPoly mZ).map (Int.castRingHom ℚ)) {s : ZMod p} {f : CPoly (NFC.NF M)}
    {g : ℕ} {Γ : EDiv (NFC.NF M)} {xs ys : List ℤ} (h : baseCheckKF p mZ s f g Γ xs ys)
    (hK : ∀ q ∈ Γ, q.2.1 ^ 2 = (toPoly f).eval q.1) :
    ∃ (φ : NFC.NF M →+* ℚ_[p]) (F : ℤ_[p][X]) (Γp : EDiv ℤ_[p]) (xp yp : Fin g → ℤ_[p]),
      (toPoly f).map φ = F.map (algebraMap ℤ_[p] ℚ_[p]) ∧
      F.natDegree = 2 * g + 1 ∧ IsUnit F.leadingCoeff ∧
      F.map PadicInt.toZMod = toPoly (redF p s f) ∧
      emap φ Γ = emap (algebraMap ℤ_[p] ℚ_[p]) Γp ∧
      OnCurve F Γp ∧
      Γp.Pairwise (fun r r' ↦ IsUnit (r.1 - r'.1)) ∧
      (∀ i, IsUnit (yp i)) ∧ (∀ i, yp i ^ 2 = F.eval (xp i)) ∧
      (∀ i j, i ≠ j → IsUnit (xp i - xp j)) ∧ (∀ r ∈ Γp, ∀ i, IsUnit (r.1 - xp i)) ∧
      emap PadicInt.toZMod Γp = redΓ p s Γ := by
  classical
  obtain ⟨hp2, hlen, hfint, hlc, hxl, hyl, hE, hxd, hs, hs', hΓ, hΓd⟩ := h
  -- the Hensel root and the embedding
  set Fm := toPoly mZ
  have hsF : (Fm.map (Int.castRingHom (ZMod p))).eval s = 0 := by
    rw [← castL_eq, ← evalC_eq]; exact hs
  have hsF' : ((derivative Fm).map (Int.castRingHom (ZMod p))).eval s ≠ 0 := by
    rw [← derivative_map, ← castL_eq, ← toPoly_deriv, ← evalC_eq]; exact hs'
  obtain ⟨z, hz, hzs⟩ := hensel_root_red Fm s hsF hsF'
  set φ := embedZ Fm hmZ z hz
  have hl : ∀ x : NFC.NF M, pIntL p x.1 = true → ∃ w : ℤ_[p], (w : ℚ_[p]) = φ x ∧
      PadicInt.toZMod w = redL p s x.1 := fun x hx ↦ by
    obtain ⟨w, h1, h2⟩ := exists_lift_NF Fm hmZ z hz x hx
    exact ⟨w, h1, by rw [h2, hzs]⟩
  choose! lf hlf1 hlf2 using hl
  -- the lifted curve
  set F : ℤ_[p][X] := toPoly (f.map lf) with hFdef
  have hFmap : (toPoly f).map φ = F.map (algebraMap ℤ_[p] ℚ_[p]) := by
    rw [← toPoly_map_list, hFdef, ← toPoly_map_list, List.map_map]
    congr 1
    refine List.map_congr_left fun c hc ↦ ?_
    exact (hlf1 c (hfint c hc)).symm
  have hFred : F.map PadicInt.toZMod = toPoly (redF p s f) := by
    rw [hFdef, ← toPoly_map_list, List.map_map, redF]
    congr 1
    refine List.map_congr_left fun c hc ↦ ?_
    exact hlf2 c (hfint c hc)
  have hlt : 2 * g + 1 < f.length := by omega
  have hcoef : ∀ n, F.coeff n = (f.map lf).getD n 0 := fun n ↦ coeff_toPoly _ n
  have hlcF : F.coeff (2 * g + 1) = lf f[2 * g + 1] := by
    rw [hcoef, List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map]
  have hlcU : IsUnit (F.coeff (2 * g + 1)) := by
    rw [hlcF]
    refine isUnit_of_toZMod ?_
    rw [hlf2 _ (hfint _ (List.getElem_mem hlt))]
    rwa [List.getD_eq_getElem _ _ hlt] at hlc
  have hdeg : F.natDegree = 2 * g + 1 := by
    refine le_antisymm ?_ (le_natDegree_of_ne_zero hlcU.ne_zero)
    rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [hcoef, List.getD_eq_default _ _ (by rw [List.length_map, hlen]; exact_mod_cast hn)]
  have hlcF' : IsUnit F.leadingCoeff := by rw [leadingCoeff, hdeg]; exact hlcU
  -- the divisor
  set Γp : EDiv ℤ_[p] := Γ.map fun q ↦ (lf q.1, lf q.2.1, q.2.2)
  -- the base points
  have hex : ∀ i : Fin g, ∃ y : ℤ_[p],
      y ^ 2 = F.eval ((xs.getD i 0 : ℤ) : ℤ_[p]) ∧ IsUnit y := by
    intro i
    obtain ⟨hsq, hnu⟩ := hE i (List.mem_range.mpr i.2)
    have hu : IsUnit ((ys.getD i 0 : ℤ) : ℤ_[p]) :=
      isUnit_of_toZMod (by rw [map_intCast]; exact hnu)
    obtain ⟨y, hy, hyu, -⟩ := exists_sqrt hp2 (F.eval ((xs.getD i 0 : ℤ) : ℤ_[p]))
      (ys.getD i 0 : ℤ) hu (by
        have : ‖(((((ys.getD i 0 : ℤ) : ℤ_[p]) ^ 2 - F.eval ((xs.getD i 0 : ℤ) : ℤ_[p])) :
            ℤ_[p]) : ℚ_[p])‖ < 1 := by
          rw [EllDV.norm_lt_one_iff_toZMod, map_sub, map_pow, map_intCast, toZMod_eval,
            map_intCast, hFred, ← evalC_eq, hsq, sub_self]
        exact this)
    exact ⟨y, hy, hyu⟩
  choose yp hyp hyu using hex
  refine ⟨φ, F, Γp, fun i ↦ ((xs.getD i 0 : ℤ) : ℤ_[p]), yp, hFmap, hdeg, hlcF', hFred, ?_, ?_, ?_,
    hyu, hyp, ?_, ?_, ?_⟩
  · unfold emap
    rw [List.map_map]
    refine List.map_congr_left fun q hq ↦ ?_
    obtain ⟨h1, h2, -, -⟩ := hΓ q hq
    simp only [Function.comp_apply, Prod.mk.injEq, and_true]
    exact ⟨(hlf1 _ h1).symm, (hlf1 _ h2).symm⟩
  · intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    obtain ⟨h1, h2, h3, -⟩ := hΓ q hq
    refine ⟨isUnit_of_toZMod (by rw [map_mul, map_ofNat, hlf2 _ h2]; exact h3), ?_⟩
    apply Subtype.ext
    show algebraMap ℤ_[p] ℚ_[p] (lf q.2.1) ^ 2 = algebraMap ℤ_[p] ℚ_[p] (F.eval (lf q.1))
    have e1 : algebraMap ℤ_[p] ℚ_[p] (F.eval (lf q.1)) =
        (F.map (algebraMap ℤ_[p] ℚ_[p])).eval (algebraMap ℤ_[p] ℚ_[p] (lf q.1)) := by
      rw [eval_map, eval₂_hom]
    rw [e1, ← hFmap]
    change (lf q.2.1 : ℚ_[p]) ^ 2 = ((toPoly f).map φ).eval (lf q.1 : ℚ_[p])
    rw [hlf1 _ h1, hlf1 _ h2, eval_map, eval₂_hom, ← hK q hq, map_pow]
  · unfold Γp
    rw [List.pairwise_map]
    refine hΓd.imp_of_mem fun {u v} hu hv huv ↦ isUnit_of_toZMod ?_
    rw [map_sub, hlf2 _ (hΓ u hu).1, hlf2 _ (hΓ v hv).1]
    exact sub_ne_zero.mpr huv
  · intro i j hij
    refine isUnit_of_toZMod ?_
    have hi : (i : ℕ) < xs.length := by rw [hxl]; exact i.2
    have hj : (j : ℕ) < xs.length := by rw [hxl]; exact j.2
    rw [map_sub, map_intCast, map_intCast, List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ hj, sub_ne_zero]
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
    · exact List.pairwise_iff_getElem.mp hxd _ _ hi hj hlt
    · exact (List.pairwise_iff_getElem.mp hxd _ _ hj hi hlt).symm
  · intro r hr i
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    obtain ⟨h1, -, -, h4⟩ := hΓ q hq
    have hi : (i : ℕ) < xs.length := by rw [hxl]; exact i.2
    refine isUnit_of_toZMod ?_
    rw [map_sub, hlf2 _ h1, map_intCast, List.getD_eq_getElem _ _ hi]
    exact h4 _ (List.getElem_mem hi)
  · unfold emap redΓ
    rw [List.map_map]
    refine List.map_congr_left fun q hq ↦ ?_
    obtain ⟨h1, h2, -, -⟩ := hΓ q hq
    simp only [Function.comp_apply, Prod.mk.injEq, and_true]
    exact ⟨hlf2 _ h1, hlf2 _ h2⟩

/-- `𝔽_p`-principality of the reduction, via `principalC`, for a lifted curve `F`. -/
lemma residue_iff_principalCF {p : ℕ} [Fact p.Prime] {F : ℤ_[p][X]} {fb : CPoly (ZMod p)}
    {g : ℕ} (ef : F.map PadicInt.toZMod = toPoly fb) {Γp : EDiv ℤ_[p]} (hon : OnCurve F Γp)
    {Γb : EDiv (ZMod p)} (hred : emap PadicInt.toZMod Γp = Γb) (m : ℕ) :
    PrincipalMul (F.map (IsLocalRing.residue ℤ_[p])) g (emap (IsLocalRing.residue ℤ_[p]) Γp) m ↔
    (principalC fb (escale m Γb) (boundA (m * edeg Γb)) (boundB g (m * edeg Γb))).isSome := by
  have honZ := OnCurve.map (φ := PadicInt.toZMod) hon
  rw [ef, hred] at honZ
  have hΓ : ∀ n, ∀ q ∈ escale n Γb, 2 * q.2.1 ≠ 0 ∧ q.2.1 ^ 2 = (toPoly fb).eval q.1 := by
    intro n q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact ⟨(honZ q' hq').1.ne_zero, (honZ q' hq').2⟩
  rw [← principalMul_iff_principalC fb g Γb hΓ m]
  constructor
  · intro hP
    have := principal_zmod_of_residue _ _ hP
    rwa [ef, hred] at this
  · intro hP
    apply principal_residue_of_zmod
    rwa [ef, hred]

end Jac
