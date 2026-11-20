import RischTragerBronstein.Jacobian.NFEmbed
import RischTragerBronstein.Jacobian.HypDecideK
import RischTragerBronstein.Elliptic.DV.GoodRed

/-!
# Good reduction of divisors over a number field

For `K = NF M` (`M = mZ` over `ℤ`), a prime `p`, a simple root `s` of `mZ` modulo `p`, and a
divisor `Γ` over `K`, `baseCheckK` checks: the curve and the base points `E₀` are good at `p`
(`baseCheck` with empty divisor), the coordinates of `Γ` are `p`-integral, and their reductions
(`redL p s`) are non-branch, distinct and away from `E₀`. `baseCheckK_spec` provides the data
used by `torsion_iff_two_primes` / `not_torsion_of_orders` over `K`, with the embedding `embedZ`
and the reduced divisor `redΓ p s Γ` over `𝔽_p`.
-/

open Polynomial CPoly CPoly.Kron

namespace Jac

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

/-- The reduced divisor over `𝔽_p`. -/
def redΓ (p : ℕ) (s : ZMod p) (Γ : EDiv (NFC.NF M)) : EDiv (ZMod p) :=
  Γ.map fun q ↦ (redL p s q.1.1, redL p s q.2.1.1, q.2.2)

/-- The good-reduction conditions at `p` for a divisor over `K = NF M`. -/
abbrev baseCheckK (p : ℕ) [Fact p.Prime] (mZ : List ℤ) (s : ZMod p) (f : List ℤ) (g : ℕ)
    (Γ : EDiv (NFC.NF M)) (xs ys : List ℤ) : Prop :=
  baseCheck p f g [] xs ys ∧ evalC (castL p mZ) s = 0 ∧ evalC (deriv (castL p mZ)) s ≠ 0 ∧
    (∀ q ∈ Γ, pIntL p q.1.1 = true ∧ pIntL p q.2.1.1 = true ∧ 2 * redL p s q.2.1.1 ≠ 0 ∧
      ∀ x ∈ xs, redL p s q.1.1 - (x : ZMod p) ≠ 0) ∧
    Γ.Pairwise (fun u v ↦ redL p s u.1.1 ≠ redL p s v.1.1)

lemma isUnit_of_toZMod {p : ℕ} [Fact p.Prime] {w : ℤ_[p]} (h : PadicInt.toZMod w ≠ 0) :
    IsUnit w := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt ↦ h ?_)
  exact (EllDV.norm_lt_one_iff_toZMod w).mp hlt

/-- **Hensel** with the reduction of the root. -/
lemma hensel_root_red {p : ℕ} [Fact p.Prime] (F : ℤ[X]) (s : ZMod p)
    (hs : (F.map (Int.castRingHom (ZMod p))).eval s = 0)
    (hs' : ((derivative F).map (Int.castRingHom (ZMod p))).eval s ≠ 0) :
    ∃ z : ℤ_[p], F.aeval z = 0 ∧ PadicInt.toZMod z = s := by
  set a : ℤ_[p] := (s.val : ℤ_[p])
  have ha : PadicInt.toZMod a = s := by
    simp only [a, map_natCast, ZMod.natCast_zmod_val]
  have hev : ∀ G : ℤ[X], PadicInt.toZMod (G.aeval a) = (G.map (Int.castRingHom (ZMod p))).eval s := by
    intro G
    rw [aeval_def, eval_map, ← ha, hom_eval₂]
    congr 1
    ext n
    simp
  have h1 : ‖(F.aeval a : ℚ_[p])‖ < 1 := by
    rw [EllDV.norm_lt_one_iff_toZMod, hev]; exact hs
  have h2 : ‖((derivative F).aeval a : ℚ_[p])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp ?_)
    rw [EllDV.norm_lt_one_iff_toZMod, hev]; exact hs'
  obtain ⟨z, hz, hza, -⟩ := hensels_lemma (F := F) (a := a) (by
    change ‖(F.aeval a : ℚ_[p])‖ < ‖((derivative F).aeval a : ℚ_[p])‖ ^ 2
    rw [h2, one_pow]; exact h1)
  refine ⟨z, hz, ?_⟩
  have hlt : ‖((z - a : ℤ_[p]) : ℚ_[p])‖ < 1 := by
    have : ‖z - a‖ < 1 := by
      calc ‖z - a‖ < ‖(derivative F).aeval a‖ := hza
        _ = 1 := h2
    exact this
  rw [EllDV.norm_lt_one_iff_toZMod, map_sub, sub_eq_zero, ha] at hlt
  exact hlt

/-- **The facts behind `baseCheckK`.** -/
theorem baseCheckK_spec {p : ℕ} [Fact p.Prime] {mZ : List ℤ}
    (hmZ : toPoly M = (toPoly mZ).map (Int.castRingHom ℚ)) {s : ZMod p} {f : List ℤ} {g : ℕ}
    {Γ : EDiv (NFC.NF M)} {xs ys : List ℤ} (h : baseCheckK p mZ s f g Γ xs ys)
    (hK : ∀ q ∈ Γ, q.2.1 ^ 2 = (toPoly (curveK (K := NFC.NF M) f)).eval q.1) :
    ∃ (φ : NFC.NF M →+* ℚ_[p]) (Γp : EDiv ℤ_[p]) (xp yp : Fin g → ℤ_[p]),
      (toPoly (curveK (K := NFC.NF M) f)).map φ =
        ((toPoly f).map (Int.castRingHom ℤ_[p])).map (algebraMap ℤ_[p] ℚ_[p]) ∧
      emap φ Γ = emap (algebraMap ℤ_[p] ℚ_[p]) Γp ∧
      OnCurve ((toPoly f).map (Int.castRingHom ℤ_[p])) Γp ∧
      Γp.Pairwise (fun r r' ↦ IsUnit (r.1 - r'.1)) ∧
      (∀ i, IsUnit (yp i)) ∧
      (∀ i, yp i ^ 2 = ((toPoly f).map (Int.castRingHom ℤ_[p])).eval (xp i)) ∧
      (∀ i j, i ≠ j → IsUnit (xp i - xp j)) ∧ (∀ r ∈ Γp, ∀ i, IsUnit (r.1 - xp i)) ∧
      emap PadicInt.toZMod Γp = redΓ p s Γ := by
  classical
  obtain ⟨hb, hs, hs', hΓ, hΓd⟩ := h
  obtain ⟨hp2, hlen, hlc, hxl, hyl, hE, hxd, -, -⟩ := hb
  set ιp := Int.castRingHom ℤ_[p]
  have heval : ∀ t : ℤ, ((toPoly f).map ιp).eval (t : ℤ_[p]) = ((evalC f t : ℤ) : ℤ_[p]) := by
    intro t
    rw [evalC_eq, eval_map, show (t : ℤ_[p]) = ιp t from rfl, eval₂_at_apply]; rfl
  -- the Hensel root
  set F := toPoly mZ
  have hsF : (F.map (Int.castRingHom (ZMod p))).eval s = 0 := by
    rw [← castL_eq, ← evalC_eq]; exact hs
  have hsF' : ((derivative F).map (Int.castRingHom (ZMod p))).eval s ≠ 0 := by
    rw [← derivative_map, ← castL_eq, ← toPoly_deriv, ← evalC_eq]; exact hs'
  obtain ⟨z, hz, hzs⟩ := hensel_root_red F s hsF hsF'
  set φ := embedZ F hmZ z hz
  have hl : ∀ x : NFC.NF M, pIntL p x.1 = true → ∃ w : ℤ_[p], (w : ℚ_[p]) = φ x ∧
      PadicInt.toZMod w = redL p s x.1 := fun x hx ↦ by
    obtain ⟨w, h1, h2⟩ := exists_lift_NF F hmZ z hz x hx
    exact ⟨w, h1, by rw [h2, hzs]⟩
  choose! lf hlf1 hlf2 using hl
  set Γp : EDiv ℤ_[p] := Γ.map fun q ↦ (lf q.1, lf q.2.1, q.2.2)
  -- the base points
  have hex : ∀ i : Fin g, ∃ y : ℤ_[p],
      y ^ 2 = ((toPoly f).map ιp).eval ((xs.getD i 0 : ℤ) : ℤ_[p]) ∧ IsUnit y := by
    intro i
    obtain ⟨hdv, hnu⟩ := hE i (List.mem_range.mpr i.2)
    obtain ⟨y, hy, hyu, -⟩ := exists_sqrt hp2
      (((toPoly f).map ιp).eval ((xs.getD i 0 : ℤ) : ℤ_[p]))
      (ys.getD i 0 : ℤ) (isUnit_intCast hnu) (by
        rw [heval, ← Int.cast_pow, ← Int.cast_sub]
        exact (PadicInt.norm_int_lt_one_iff_dvd _).mpr hdv)
    exact ⟨y, hy, hyu⟩
  choose yp hyp hyu using hex
  have hmap : (toPoly (curveK (K := NFC.NF M) f)).map φ =
      ((toPoly f).map ιp).map (algebraMap ℤ_[p] ℚ_[p]) := by
    rw [toPoly_curveK, Polynomial.map_map, Polynomial.map_map, Polynomial.map_map]
    congr 1; exact RingHom.ext_int _ _
  refine ⟨φ, Γp, fun i ↦ ((xs.getD i 0 : ℤ) : ℤ_[p]), yp, hmap, ?_, ?_, ?_, hyu, hyp, ?_, ?_, ?_⟩
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
    show algebraMap ℤ_[p] ℚ_[p] (lf q.2.1) ^ 2 =
      algebraMap ℤ_[p] ℚ_[p] (((toPoly f).map ιp).eval (lf q.1))
    have e1 : algebraMap ℤ_[p] ℚ_[p] (((toPoly f).map ιp).eval (lf q.1)) =
        (((toPoly f).map ιp).map (algebraMap ℤ_[p] ℚ_[p])).eval (algebraMap ℤ_[p] ℚ_[p] (lf q.1)) := by
      rw [eval_map (f := algebraMap ℤ_[p] ℚ_[p]), eval₂_at_apply]
    rw [e1, ← hmap]
    change (lf q.2.1 : ℚ_[p]) ^ 2 = ((toPoly (curveK f)).map φ).eval (lf q.1 : ℚ_[p])
    rw [hlf1 _ h1, hlf1 _ h2, eval_map, eval₂_at_apply, ← hK q hq, map_pow]
  · unfold Γp
    rw [List.pairwise_map]
    refine hΓd.imp_of_mem fun {u v} hu hv huv ↦ isUnit_of_toZMod ?_
    rw [map_sub, hlf2 _ (hΓ u hu).1, hlf2 _ (hΓ v hv).1]
    exact sub_ne_zero.mpr huv
  · intro i j hij
    apply isUnit_intCast_sub
    have hi : (i : ℕ) < xs.length := by rw [hxl]; exact i.2
    have hj : (j : ℕ) < xs.length := by rw [hxl]; exact j.2
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
    · exact List.pairwise_iff_getElem.mp hxd _ _ hi hj hlt
    · intro hd
      exact List.pairwise_iff_getElem.mp hxd _ _ hj hi hlt ((dvd_sub_comm).mp hd)
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

end Jac
