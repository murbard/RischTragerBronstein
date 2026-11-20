import RischTragerBronstein.Mixed.MTCert
import RischTragerBronstein.Computable.NestXRdeE

/-!
# Mixed towers over a curve: the exponential Risch equation, soundness

Ported from `Tower.NestX` (`NestXRdeE`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u


namespace MTower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]
variable (T : MTower Fc ks Cc L)


section IdentityXE

variable (m : ℕ) (h : T.Tr (m + 1))

lemma sem_peFX_XE (fc : GPoly (LC m) × GPoly (LC m)) (Q : GPoly (LC m)) :
    T.σX m h (peFX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fc Q).1 /
      T.σX m h (peFX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fc Q).2 =
      (T.M1X m h).sem fc - (T.σX m h Q)′ / T.σX m h Q := by
  rw [← T.semX, peFX, T.semX_cleanG, (T.M1X m h).sem_add, (T.M1X m h).sem_neg,
    (T.M1X m h).sem_mul, (T.M1X m h).sem_deriv, (T.M1X m h).sem_inv, T.semX_poly]
  ring

lemma peFX_ne_XE (fc : GPoly (LC m) × GPoly (LC m)) (Q : GPoly (LC m)) :
    T.σX m h (peFX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fc Q).2 ≠ 0 :=
  T.σX_cleanG_ne m h _

lemma peRsX_ne_XE (Wc : List (GPoly (LC m) × GPoly (LC m)))
    (Q : GPoly (LC m)) :
    ∀ p ∈ peRsX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) Wc Q,
      T.σX m h p.2 ≠ 0 := fun p hp ↦ by
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hp
  exact T.σX_cleanG_ne m h _

/-- **The identity behind `prdeExpC`**: the polynomial equation is the Risch equation for `Y / Q`
times the non-zero factor `F₂ P Q`. -/
lemma pe_identityXE (fc : GPoly (LC m) × GPoly (LC m))
    (Wc : List (GPoly (LC m) × GPoly (LC m))) (Q : GPoly (LC m))
    (hQ : T.σX m h Q ≠ 0) (Y : (T.F m)[X]) (c : ℕ → Cc) :
    T.phi m (GPoly.toPoly (T.MX m h) (peA (MO Fc ks m)
        (peFX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fc Q)
        (peRsX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) Wc Q)) *
          implicitDeriv (T.wPoly m) Y +
      GPoly.toPoly (T.MX m h) (peB (MO Fc ks m)
        (peFX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fc Q)
        (peRsX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) Wc Q)) * Y -
      ∑ i ∈ Finset.range Wc.length, C (algebraMap Cc (T.F m) (c i)) *
        GPoly.toPoly (T.MX m h) ((peCs (MO Fc ks m)
          (peFX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fc Q)
          (peRsX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) Wc Q)).getD i [])) =
    T.σX m h (peFX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fc Q).2 *
      T.σX m h (prodD (GPoly.mul (MO Fc ks m)) [(MO Fc ks m).one]
        (peRsX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) Wc Q)) * T.σX m h Q *
      ((T.phi m Y / T.σX m h Q)′ + (T.M1X m h).sem fc * (T.phi m Y / T.σX m h Q) -
        ∑ i ∈ Finset.range Wc.length, algebraMap Cc (T.F (m + 1)) (c i) *
          (T.M1X m h).sem (Wc.getD i ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))).zero)) := by
  set O := MO Fc ks m with hO
  set O' := O.monomial (wKC O (ks m)) with hO'
  set F := peFX O O' fc Q with hF
  set Rs := peRsX O O' Wc Q with hRs
  set P := prodD (GPoly.mul O) [O.one] Rs with hP
  have hsF := T.sem_peFX_XE m h fc Q
  rw [← hF] at hsF
  have hF2 : T.σX m h F.2 ≠ 0 := T.peFX_ne_XE m h fc Q
  have hRs2 := T.peRsX_ne_XE m h Wc Q
  rw [← hRs] at hRs2
  have hlR : Rs.length = Wc.length := by simp [hRs, peRsX]
  have hP0 : T.σX m h P ≠ 0 :=
    σ_prodD_ne_zero (GPoly.mul O) [O.one] (T.σX m h) (T.σX_mul m h) (T.σX_one m h) _ hRs2
  have hsum := sum_cross (GPoly.mul O) [O.one] (T.σX m h) (T.σX_mul m h) (T.σX_one m h) Rs
    ((List.range Wc.length).map fun i ↦ algebraMap Cc (T.F (m + 1)) (c i)) hRs2
  have hRsv : ∀ i < Wc.length, T.σX m h (Rs.getD i ([], [])).1 / T.σX m h (Rs.getD i ([], [])).2 =
      T.σX m h Q * (T.M1X m h).sem (Wc.getD i O'.zero) := by
    intro i hi
    have hRi : Rs.getD i ([], []) = cleanG O (O'.mul (Q, [O.one]) (Wc.getD i O'.zero)) := by
      simp only [List.getD_eq_getElem?_getD, hRs, peRsX, List.getElem?_map,
        List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
    rw [hRi, ← T.semX, T.semX_cleanG, (T.M1X m h).sem_mul, T.semX_poly]
  have hRHS : ∑ i ∈ Finset.range Wc.length, T.phi m (C (algebraMap Cc (T.F m) (c i))) *
      T.phi m (GPoly.toPoly (T.MX m h) ((peCs O F Rs).getD i [])) =
      T.σX m h F.2 * T.σX m h P * (T.σX m h Q * ∑ i ∈ Finset.range Wc.length,
        algebraMap Cc (T.F (m + 1)) (c i) * (T.M1X m h).sem (Wc.getD i O'.zero)) := by
    have e1 : ∀ i ∈ Finset.range Wc.length, T.phi m (C (algebraMap Cc (T.F m) (c i))) *
        T.phi m (GPoly.toPoly (T.MX m h) ((peCs O F Rs).getD i [])) =
        T.σX m h F.2 * (algebraMap Cc (T.F (m + 1)) (c i) *
          T.σX m h ((cross (GPoly.mul O) [O.one] Rs).getD i [])) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [← T.algebraMap_succ, peCs, NestTower.getD_map' _ _ [] [] (by
        rw [length_cross, hlR]; exact hi'), GPoly.toPoly_mul, map_mul]
      ring
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
    have e2 : ∑ i ∈ Finset.range Wc.length, algebraMap Cc (T.F (m + 1)) (c i) *
        T.σX m h ((cross (GPoly.mul O) [O.one] Rs).getD i []) =
        (List.zipWith (fun c y ↦ c * T.σX m h y) ((List.range Wc.length).map fun i ↦
          algebraMap Cc (T.F (m + 1)) (c i)) (cross (GPoly.mul O) [O.one] Rs)).sum := by
      rw [NestTower.zipWith_sum_range _ 0 [] _ _ (by rw [length_cross, hlR]; simp)]
      rw [List.length_map, List.length_range]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hi)]
    have e3 : (List.zipWith (fun c p ↦ c * (T.σX m h p.1 / T.σX m h p.2)) ((List.range Wc.length).map
        fun i ↦ algebraMap Cc (T.F (m + 1)) (c i)) Rs).sum =
        T.σX m h Q * ∑ i ∈ Finset.range Wc.length, algebraMap Cc (T.F (m + 1)) (c i) *
          (T.M1X m h).sem (Wc.getD i O'.zero) := by
      rw [NestTower.zipWith_sum_range _ 0 ([], []) _ _ (by rw [hlR]; simp), Finset.mul_sum]
      rw [List.length_map, List.length_range]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hi), hRsv i (Finset.mem_range.mp hi)]
      ring
    rw [e2, hsum, e3]
    ring
  have hA' : T.phi m (GPoly.toPoly (T.MX m h) (peA O F Rs)) = T.σX m h F.2 * T.σX m h P :=
    T.σX_mul m h _ _
  have hB' : T.phi m (GPoly.toPoly (T.MX m h) (peB O F Rs)) = T.σX m h F.1 * T.σX m h P :=
    T.σX_mul m h _ _
  simp only [map_sub, map_add, map_mul, map_sum]
  rw [hA', hB', ← T.deriv_phi, hRHS, Derivation.leibniz_div]
  simp only [smul_eq_mul]
  have hF1 : T.σX m h F.1 = ((T.M1X m h).sem fc - (T.σX m h Q)′ / T.σX m h Q) * T.σX m h F.2 := by
    rw [← hsF]; field_simp
  rw [hF1]
  field_simp
  ring

end IdentityXE

section SoundXE

variable (m : ℕ) (h : T.Tr (m + 1))

/-- **Soundness of the final constant system**: every output of `peOutC` solves the Risch equation
`y′ + f y = ∑ cᵢ wᵢ` (whatever the basis `Bs`). -/
theorem peOut_soundXE (DS : DShape (T.F m)) (hDS : DS.W = T.wPoly m)
    (fc : GPoly (LC m) × GPoly (LC m))
    (W : List (GPoly (LC m) × GPoly (LC m))) (Q : GPoly (LC m))
    (hQ0 : T.σX m h Q ≠ 0) (Bs : List (List ℚ × GPoly (LC m))) :
    ∀ r ∈ peOutC Fc ks m (wKC (MO Fc ks m) (ks m))
      (peA (MO Fc ks m) (peFX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fc Q)
        (peRsX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
          (W.map (cleanG (MO Fc ks m))) Q))
      (peB (MO Fc ks m) (peFX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fc Q)
        (peRsX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
          (W.map (cleanG (MO Fc ks m))) Q))
      (peCs (MO Fc ks m) (peFX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m))) fc Q)
        (peRsX (MO Fc ks m) ((MO Fc ks m).monomial (wKC (MO Fc ks m) (ks m)))
          (W.map (cleanG (MO Fc ks m))) Q))
      (W.map (cleanG (MO Fc ks m))).length Q Bs,
      ((T.M1X m h).sem r.2)′ + (T.M1X m h).sem fc * (T.M1X m h).sem r.2 =
        sQ (T.M1X m h) r.1 W := by
  intro r hr
  set O := MO Fc ks m with hO
  set O' := O.monomial (wKC O (ks m)) with hO'
  obtain ⟨Wc, hWc⟩ : ∃ Wc, Wc = W.map (cleanG O) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = peFX O O' fc Q := ⟨_, rfl⟩
  obtain ⟨Rs, hRs⟩ : ∃ Rs, Rs = peRsX O O' Wc Q := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = peA O F Rs := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = peB O F Rs := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ Cs, Cs = peCs O F Rs := ⟨_, rfl⟩
  rw [← hWc, ← hF, ← hRs, ← hA, ← hB, ← hCs] at hr
  unfold peOutC at hr
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
  set β := (List.range Bs.length).map (u.getD · 0) with hβ
  have hβD : ∀ l < Bs.length, β.getD l 0 = u.getD l 0 := fun l hl ↦
    NestTower.getD_range_map _ _ hl
  have hqK : ∀ q : ℚ, algebraMap Cc (T.F (m + 1)) (algebraMap ℚ Cc q) = (q : T.F (m + 1)) :=
    fun q ↦ T.algebraMap_ratX q
  have hqK' : ∀ q : ℚ, algebraMap Cc (T.F m) (algebraMap ℚ Cc q) = (q : T.F m) :=
    fun q ↦ T.algebraMap_ratX q
  have hw : GPoly.toPoly (T.MX m h) (wKC O (ks m)) = DS.W := by rw [hDS, T.toPoly_wKX]
  have hcst : ∀ q, (T.MX m h).sem (mcst Fc ks m q) = (q : T.F m) := T.sem_cstX m h
  -- the constant system gives `∑ uₗ resₗ = 0`
  have hres0 : ∑ l ∈ Finset.range Bs.length, C ((u.getD l 0 : ℚ) : T.F m) *
      resQX (T.MX m h) DS A B Cs (Bs.getD l ([], [])).1
        (GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2) = 0 := by
    have := T.consys_poly_relX m h _ Bs.length
      (fun l ↦ residE O (mcst Fc ks m) (wKC O (ks m)) A B Cs (Bs.getD l ([], []))) (List.length_map _)
      (fun l hl ↦ NestTower.getD_map' _ _ ([], []) _ hl) u hu
    rw [← this]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [toPoly_residEX DS A B Cs hcst (wKC O (ks m)) hw]
  set c := vcomb Wc.length β (Bs.map Prod.fst) with hcdef
  set Y := GPoly.toPoly (T.MX m h) (lcombGP O (mcst Fc ks m) β (Bs.map Prod.snd)) with hY
  have hYs : Y = ∑ l ∈ Finset.range Bs.length, C ((β.getD l 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2 := by
    rw [hY, toPoly_lcombGP (T.MX m h) (mcst Fc ks m) hcst,
      zipWith_sum_getD (fun (q : ℚ) (p : GPoly (LC m)) ↦
        C (q : T.F m) * GPoly.toPoly (T.MX m h) p) 0 [] (by simp), List.length_map]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [NestTower.getD_map' _ _ ([], []) [] (Finset.mem_range.mp hl)]
  have hlCs : Cs.length = Wc.length := by simp [hCs, peCs, length_cross, hRs, peRsX]
  have hpoly : resQX (T.MX m h) DS A B Cs c Y = 0 := by
    have := resQ_combX (M := T.MX m h) DS A B Cs Bs β 0
    rw [add_zero, ← hYs, hlCs, ← hcdef] at this
    rw [this, show LopX (T.MX m h) DS A B 0 = 0 by simp [LopX, DzX], add_zero, ← hres0]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [hβD l (Finset.mem_range.mp hl)]
  have hQ0' : T.σX m h Q ≠ 0 := hQ0
  have hid := T.pe_identityXE m h fc Wc Q hQ0 Y (fun i ↦ algebraMap ℚ Cc (c.getD i 0))
  rw [← hF, ← hRs, ← hA, ← hB, ← hCs] at hid
  have hlhs : GPoly.toPoly (T.MX m h) A * implicitDeriv (T.wPoly m) Y +
      GPoly.toPoly (T.MX m h) B * Y -
      ∑ i ∈ Finset.range Wc.length, C (algebraMap Cc (T.F m) (algebraMap ℚ Cc (c.getD i 0))) *
        GPoly.toPoly (T.MX m h) (Cs.getD i []) = 0 := by
    have h' := hpoly
    unfold resQX DzX at h'
    rw [hlCs, hDS] at h'
    have hs2 : ∑ i ∈ Finset.range Wc.length, C (algebraMap Cc (T.F m) (algebraMap ℚ Cc (c.getD i 0))) *
        GPoly.toPoly (T.MX m h) (Cs.getD i []) = ∑ i ∈ Finset.range Wc.length,
          C ((c.getD i 0 : ℚ) : T.F m) * GPoly.toPoly (T.MX m h) (Cs.getD i []) :=
      Finset.sum_congr rfl fun i _ ↦ by rw [hqK']
    rw [hs2]
    exact h'
  rw [hlhs, map_zero] at hid
  have hne : T.σX m h F.2 * T.σX m h (prodD (GPoly.mul O) [O.one] Rs) * T.σX m h Q ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by rw [hF]; exact T.peFX_ne_XE m h _ _) ?_) hQ0
    exact σ_prodD_ne_zero (GPoly.mul O) [O.one] (T.σX m h) (T.σX_mul m h) (T.σX_one m h) _
      (by rw [hRs]; exact T.peRsX_ne_XE m h Wc Q)
  have hbr := (mul_eq_zero.mp hid.symm).resolve_left hne
  have hsol : (T.M1X m h).sem (lcombGP O (mcst Fc ks m) β (Bs.map Prod.snd), Q) =
      T.phi m Y / T.σX m h Q := T.semX m h _
  simp only
  rw [hsol]
  unfold sQ
  have e : ∀ i ∈ Finset.range W.length, ((c.getD i 0 : ℚ) : T.F (m + 1)) *
      (T.M1X m h).sem (W.getD i O'.zero) =
      algebraMap Cc (T.F (m + 1)) (algebraMap ℚ Cc (c.getD i 0)) *
        (T.M1X m h).sem (Wc.getD i O'.zero) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hwc : (T.M1X m h).sem (Wc.getD i O'.zero) = (T.M1X m h).sem (W.getD i O'.zero) := by
      rw [hWc, NestTower.getD_map' _ _ O'.zero _ hi', T.semX_cleanG]
    rw [hqK, hwc]
  rw [Finset.sum_congr rfl e, show W.length = Wc.length by simp [hWc]]
  linear_combination hbr

end SoundXE


end MTower

end Curves.MT
