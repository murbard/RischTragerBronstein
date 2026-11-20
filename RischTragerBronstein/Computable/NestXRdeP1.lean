import RischTragerBronstein.Computable.NestXRdeSpec

/-!
# The Risch equation in mixed towers: the identity, soundness and the final constant system

Generic in the level `m` of a mixed tower (any kind of monomial `tₘ`), for coefficients
`f` given by a code `fc` of level `m + 1` and the denominator `Q`:

* `sem_peFXP`, `pe_identityXP`: the polynomial equation `A Y′ + B Y = ∑ cᵢ Cᵢ` is the Risch
  equation for `Y / Q` times the non-zero factor `F₂ P Q`;
* `peOut_soundXP`: every output of the final constant system `peOut` solves the Risch equation;
* `peOut_completeXP`: the final constant system is complete.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP Tower.NestX CPoly

namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : (m : ℕ) → KindN m}
variable (T : NestMTower Kc E ks)

section Identity

variable (m : ℕ) (h : T.Tr (m + 1))

lemma sem_peFXP (fc : GPoly (Code (m + 1)) × GPoly (Code (m + 1))) (Q : GPoly (Code (m + 1))) :
    T.σX m h (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q).1 /
      T.σX m h (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q).2 =
      (T.M1X m h).sem fc - (T.σX m h Q)′ / T.σX m h Q := by
  rw [← T.semX, peFX, T.semX_cleanG, (T.M1X m h).sem_add, (T.M1X m h).sem_neg,
    (T.M1X m h).sem_mul, (T.M1X m h).sem_deriv, (T.M1X m h).sem_inv, T.semX_poly]
  ring

lemma σX_peFX_ne (fc : GPoly (Code (m + 1)) × GPoly (Code (m + 1))) (Q : GPoly (Code (m + 1))) :
    T.σX m h (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q).2 ≠ 0 :=
  T.σX_cleanG_ne m h _

/-- **The identity behind the Risch equation solvers**: the polynomial equation is the Risch
equation for `Y / Q` times the non-zero factor `F₂ P Q`. -/
lemma pe_identityXP (fc : GPoly (Code (m + 1)) × GPoly (Code (m + 1)))
    (Wc : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1)))) (Q : GPoly (Code (m + 1)))
    (hQ : T.σX m h Q ≠ 0) (Y : (T.F m)[X]) (c : ℕ → Kc) :
    T.phi m (GPoly.toPoly (T.MX m h) (peA (opsM ks m)
        (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q)
        (peRsX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) Wc Q)) *
          implicitDeriv (T.wPoly m) Y +
      GPoly.toPoly (T.MX m h) (peB (opsM ks m)
        (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q)
        (peRsX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) Wc Q)) * Y -
      ∑ i ∈ Finset.range Wc.length, C (algebraMap Kc (T.F m) (c i)) *
        GPoly.toPoly (T.MX m h) ((peCs (opsM ks m)
          (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q)
          (peRsX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) Wc Q)).getD i [])) =
    T.σX m h (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q).2 *
      T.σX m h (prodD (GPoly.mul (opsM ks m)) [(opsM ks m).one]
        (peRsX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) Wc Q)) * T.σX m h Q *
      ((T.phi m Y / T.σX m h Q)′ + (T.M1X m h).sem fc * (T.phi m Y / T.σX m h Q) -
        ∑ i ∈ Finset.range Wc.length, algebraMap Kc (T.F (m + 1)) (c i) *
          (T.M1X m h).sem (Wc.getD i ((opsM ks m).monomial (wK (opsM ks m) (ks m))).zero)) := by
  set O := opsM ks m with hO
  set O' := O.monomial (wK O (ks m)) with hO'
  set F := peFX O O' fc Q with hF
  set Rs := peRsX O O' Wc Q with hRs
  set P := prodD (GPoly.mul O) [O.one] Rs with hP
  have hmul : ∀ a b, (T.M1X m h).sem (O'.mul a b) = (T.M1X m h).sem a * (T.M1X m h).sem b :=
    (T.M1X m h).sem_mul
  have hsF : T.σX m h F.1 / T.σX m h F.2 = (T.M1X m h).sem fc - (T.σX m h Q)′ / T.σX m h Q :=
    T.sem_peFXP m h fc Q
  have hF2 : T.σX m h F.2 ≠ 0 := T.σX_cleanG_ne m h _
  have hRs2 : ∀ p ∈ Rs, T.σX m h p.2 ≠ 0 := fun p hp ↦ by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hp
    exact T.σX_cleanG_ne m h _
  have hlR : Rs.length = Wc.length := by simp [hRs, peRsX]
  have hP0 : T.σX m h P ≠ 0 :=
    σ_prodD_ne_zero (GPoly.mul O) [O.one] (T.σX m h) (T.σX_mul m h) (T.σX_one m h) _ hRs2
  have hsum := sum_cross (GPoly.mul O) [O.one] (T.σX m h) (T.σX_mul m h) (T.σX_one m h) Rs
    ((List.range Wc.length).map fun i ↦ algebraMap Kc (T.F (m + 1)) (c i)) hRs2
  have hRsv : ∀ i < Wc.length, T.σX m h (Rs.getD i ([], [])).1 / T.σX m h (Rs.getD i ([], [])).2 =
      T.σX m h Q * (T.M1X m h).sem (Wc.getD i O'.zero) := by
    intro i hi
    have hRi : Rs.getD i ([], []) = cleanG O (O'.mul (Q, [O.one]) (Wc.getD i O'.zero)) := by
      simp only [List.getD_eq_getElem?_getD, hRs, peRsX, List.getElem?_map,
        List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
    rw [hRi, ← T.semX, T.semX_cleanG, hmul, T.semX_poly]
  have hRHS : ∑ i ∈ Finset.range Wc.length, T.phi m (C (algebraMap Kc (T.F m) (c i))) *
      T.phi m (GPoly.toPoly (T.MX m h) ((peCs O F Rs).getD i [])) =
      T.σX m h F.2 * T.σX m h P * (T.σX m h Q * ∑ i ∈ Finset.range Wc.length,
        algebraMap Kc (T.F (m + 1)) (c i) * (T.M1X m h).sem (Wc.getD i O'.zero)) := by
    have e1 : ∀ i ∈ Finset.range Wc.length, T.phi m (C (algebraMap Kc (T.F m) (c i))) *
        T.phi m (GPoly.toPoly (T.MX m h) ((peCs O F Rs).getD i [])) =
        T.σX m h F.2 * (algebraMap Kc (T.F (m + 1)) (c i) *
          T.σX m h ((cross (GPoly.mul O) [O.one] Rs).getD i [])) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [← T.algebraMap_succ, peCs, NestTower.getD_map' _ _ [] [] (by
        rw [length_cross, hlR]; exact hi'), GPoly.toPoly_mul, map_mul]
      ring
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
    have e2 : ∑ i ∈ Finset.range Wc.length, algebraMap Kc (T.F (m + 1)) (c i) *
        T.σX m h ((cross (GPoly.mul O) [O.one] Rs).getD i []) =
        (List.zipWith (fun c y ↦ c * T.σX m h y) ((List.range Wc.length).map fun i ↦
          algebraMap Kc (T.F (m + 1)) (c i)) (cross (GPoly.mul O) [O.one] Rs)).sum := by
      rw [NestTower.zipWith_sum_range _ 0 [] _ _ (by rw [length_cross, hlR]; simp)]
      rw [List.length_map, List.length_range]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [NestTower.getD_range_map _ _ (Finset.mem_range.mp hi)]
    have e3 : (List.zipWith (fun c p ↦ c * (T.σX m h p.1 / T.σX m h p.2)) ((List.range Wc.length).map
        fun i ↦ algebraMap Kc (T.F (m + 1)) (c i)) Rs).sum =
        T.σX m h Q * ∑ i ∈ Finset.range Wc.length, algebraMap Kc (T.F (m + 1)) (c i) *
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
  rw [hA', hB', ← T.deriv_phi m, hRHS, Derivation.leibniz_div]
  simp only [smul_eq_mul]
  have hF1 : T.σX m h F.1 = ((T.M1X m h).sem fc - (T.σX m h Q)′ / T.σX m h Q) * T.σX m h F.2 := by
    rw [← hsF]; field_simp
  rw [hF1]
  field_simp
  ring

end Identity

section Sound

variable (m : ℕ) (h : T.Tr (m + 1)) (DS : DShape (T.F m)) (hDS : T.wPoly m = DS.W)

include hDS in
lemma toPoly_wK_DS : GPoly.toPoly (T.MX m h) (wK (opsM ks m) (ks m)) = DS.W := by
  rw [T.toPoly_wKX, hDS]

include hDS in
/-- **Soundness of the final constant system**: whatever the basis `Bs`, every output solves
`y′ + f y = ∑ cᵢ wᵢ`. -/
theorem peOut_soundXP (fc : GPoly (Code (m + 1)) × GPoly (Code (m + 1)))
    (Wc : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1)))) (Q : GPoly (Code (m + 1)))
    (hQ0 : T.σX m h Q ≠ 0) (Bs : List (List ℚ × GPoly (Code (m + 1))))
    (r : List ℚ × Code (m + 2))
    (hr : r ∈ peOut ks m (wK (opsM ks m) (ks m))
      (peA (opsM ks m) (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q)
        (peRsX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) Wc Q))
      (peB (opsM ks m) (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q)
        (peRsX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) Wc Q))
      (peCs (opsM ks m) (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q)
        (peRsX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) Wc Q))
      Wc.length Q Bs) :
    ((T.M1X m h).sem r.2)′ + (T.M1X m h).sem fc * (T.M1X m h).sem r.2 =
      sQ (T.M1X m h) r.1 Wc := by
  set O := opsM ks m with hO
  set O' := O.monomial (wK O (ks m)) with hO'
  set F := peFX O O' fc Q with hF
  set Rs := peRsX O O' Wc Q with hRs
  set A := peA O F Rs with hA
  set B := peB O F Rs with hB
  set Cs := peCs O F Rs with hCs
  unfold peOut at hr
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
  set β := (List.range Bs.length).map (u.getD · 0) with hβ
  have hβD : ∀ l < Bs.length, β.getD l 0 = u.getD l 0 := fun l hl ↦
    NestTower.getD_range_map _ _ hl
  have hcst : ∀ q, (T.MX m h).sem (cstN m q) = (q : T.F m) := T.sem_cstX m h
  have hw := T.toPoly_wK_DS m h DS hDS
  have hres0 : ∑ l ∈ Finset.range Bs.length, C ((u.getD l 0 : ℚ) : T.F m) *
      resQX (T.MX m h) DS A B Cs (Bs.getD l ([], [])).1
        (GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2) = 0 := by
    have := T.consys_poly_relX m h _ Bs.length
      (fun l ↦ residE O (cstN m) (wK O (ks m)) A B Cs (Bs.getD l ([], []))) (List.length_map _)
      (fun l hl ↦ NestTower.getD_map' _ _ ([], []) _ hl) u hu
    rw [← this]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [toPoly_residEX DS A B Cs hcst (wK O (ks m)) hw]
  set c := vcomb Wc.length β (Bs.map Prod.fst) with hcdef
  set Y := GPoly.toPoly (T.MX m h) (lcombGP O (cstN m) β (Bs.map Prod.snd)) with hY
  have hYs : Y = ∑ l ∈ Finset.range Bs.length, C ((β.getD l 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2 := by
    rw [hY, toPoly_lcombGP (T.MX m h) (cstN m) hcst,
      zipWith_sum_getD (fun (q : ℚ) (p : GPoly (Code (m + 1))) ↦
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
  have hid : T.phi m (GPoly.toPoly (T.MX m h) A * implicitDeriv (T.wPoly m) Y +
      GPoly.toPoly (T.MX m h) B * Y -
      ∑ i ∈ Finset.range Wc.length, C (algebraMap Kc (T.F m) (algebraMap ℚ Kc (c.getD i 0))) *
        GPoly.toPoly (T.MX m h) (Cs.getD i [])) =
      T.σX m h F.2 * T.σX m h (prodD (GPoly.mul O) [O.one] Rs) * T.σX m h Q *
      ((T.phi m Y / T.σX m h Q)′ + (T.M1X m h).sem fc * (T.phi m Y / T.σX m h Q) -
        ∑ i ∈ Finset.range Wc.length, algebraMap Kc (T.F (m + 1)) (algebraMap ℚ Kc (c.getD i 0)) *
          (T.M1X m h).sem (Wc.getD i O'.zero)) :=
    T.pe_identityXP m h fc Wc Q hQ0 Y (fun i ↦ algebraMap ℚ Kc (c.getD i 0))
  have hlhs : GPoly.toPoly (T.MX m h) A * implicitDeriv (T.wPoly m) Y +
      GPoly.toPoly (T.MX m h) B * Y -
      ∑ i ∈ Finset.range Wc.length, C (algebraMap Kc (T.F m) (algebraMap ℚ Kc (c.getD i 0))) *
        GPoly.toPoly (T.MX m h) (Cs.getD i []) = 0 := by
    have h' := hpoly
    unfold resQX at h'
    rw [hlCs] at h'
    have hs2 : ∑ i ∈ Finset.range Wc.length, C (algebraMap Kc (T.F m) (algebraMap ℚ Kc (c.getD i 0))) *
        GPoly.toPoly (T.MX m h) (Cs.getD i []) = ∑ i ∈ Finset.range Wc.length,
          C ((c.getD i 0 : ℚ) : T.F m) * GPoly.toPoly (T.MX m h) (Cs.getD i []) :=
      Finset.sum_congr rfl fun i _ ↦ by rw [T.algebraMap_ratX]
    rw [hs2, hDS]
    exact h'
  rw [hlhs, map_zero] at hid
  have hne : T.σX m h F.2 * T.σX m h (prodD (GPoly.mul O) [O.one] Rs) * T.σX m h Q ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by rw [hF]; exact T.σX_cleanG_ne m h _) ?_) hQ0
    exact σ_prodD_ne_zero (GPoly.mul O) [O.one] (T.σX m h) (T.σX_mul m h) (T.σX_one m h) _
      (fun p hp ↦ by
        rw [hRs] at hp
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hp
        exact T.σX_cleanG_ne m h _)
  have hbr := (mul_eq_zero.mp hid.symm).resolve_left hne
  have hsol : (T.M1X m h).sem (lcombGP O (cstN m) β (Bs.map Prod.snd), Q) =
      T.phi m Y / T.σX m h Q := T.semX m h _
  simp only
  rw [hsol]
  unfold sQ
  have e : ∀ i ∈ Finset.range Wc.length, ((c.getD i 0 : ℚ) : T.F (m + 1)) *
      (T.M1X m h).sem (Wc.getD i O'.zero) =
      algebraMap Kc (T.F (m + 1)) (algebraMap ℚ Kc (c.getD i 0)) *
        (T.M1X m h).sem (Wc.getD i O'.zero) := fun i _ ↦ by rw [T.algebraMap_ratX]
  rw [Finset.sum_congr rfl e]
  linear_combination hbr

end Sound

section Final

variable (m : ℕ) (h : T.Tr (m + 1)) (DS : DShape (T.F m)) (hDS : T.wPoly m = DS.W)

include hDS in
set_option maxHeartbeats 1600000 in
/-- **The final constant system is complete**: a solution `y = Yv / Q` whose polynomial `Yv` is a
constant combination of the basis `Bs` with vanishing residual is a combination of the output. -/
theorem peOut_completeXP (A B : GPoly (Code (m + 1))) (Cs : List (GPoly (Code (m + 1)))) (n : ℕ)
    (Q : GPoly (Code (m + 1))) (hQ0 : T.σX m h Q ≠ 0)
    (Bs : List (List ℚ × GPoly (Code (m + 1)))) (c : List Kc)
    (hcn : ∀ i, n ≤ i → c.getD i 0 = 0) (β : List Kc)
    (hβc : ∀ i, c.getD i 0 = ∑ k ∈ Finset.range Bs.length,
      β.getD k 0 * algebraMap ℚ Kc ((Bs.getD k ([], [])).1.getD i 0))
    (Yv : (T.F m)[X])
    (hYv : Yv = ∑ l ∈ Finset.range Bs.length, C (algebraMap Kc (T.F m) (β.getD l 0)) *
      GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2)
    (hres : ∑ l ∈ Finset.range Bs.length, C (algebraMap Kc (T.F m) (β.getD l 0)) *
        resQX (T.MX m h) DS A B Cs (Bs.getD l ([], [])).1
          (GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2) = 0)
    (y : T.F (m + 1)) (hy : y * T.σX m h Q = T.phi m Yv) :
    ∃ γ : List Kc,
      (∀ i, c.getD i 0 = ∑ k ∈ Finset.range
          (peOut ks m (wK (opsM ks m) (ks m)) A B Cs n Q Bs).length,
        γ.getD k 0 * algebraMap ℚ Kc (((peOut ks m (wK (opsM ks m) (ks m)) A B Cs n Q
          Bs).getD k ([], ((opsM ks m).monomial (wK (opsM ks m) (ks m))).zero)).1.getD i 0)) ∧
      y = ∑ k ∈ Finset.range (peOut ks m (wK (opsM ks m) (ks m)) A B Cs n Q Bs).length,
        algebraMap Kc (T.F (m + 1)) (γ.getD k 0) *
          (T.M1X m h).sem ((peOut ks m (wK (opsM ks m) (ks m)) A B Cs n Q Bs).getD k
            ([], ((opsM ks m).monomial (wK (opsM ks m) (ks m))).zero)).2 := by
  classical
  set O := opsM ks m with hO
  have hcst : ∀ q, (T.MX m h).sem (cstN m q) = (q : T.F m) := T.sem_cstX m h
  have hw := T.toPoly_wK_DS m h DS hDS
  have hqK : ∀ q : ℚ, algebraMap Kc (T.F (m + 1)) (algebraMap ℚ Kc q) = (q : T.F (m + 1)) :=
    fun q ↦ T.algebraMap_ratX q
  have hphiq : ∀ q : ℚ, T.phi m (C (q : T.F m)) = (q : T.F (m + 1)) := T.phi_C_ratX m
  obtain ⟨vs, hvs⟩ : ∃ vs : List (Code (m + 2)), vs = Bs.map fun b ↦
      ((residE O (cstN m) (wK O (ks m)) A B Cs b, [O.one]) : Code (m + 2)) := ⟨_, rfl⟩
  have hlv : vs.length = Bs.length := by rw [hvs]; exact List.length_map _
  obtain ⟨U, hU⟩ : ∃ U, U = consys ks (m + 1) vs := ⟨_, rfl⟩
  set f : CPoly ℚ → List ℚ × Code (m + 2) := fun u ↦
    (vcomb n ((List.range Bs.length).map (u.getD · 0)) (Bs.map Prod.fst),
      ((lcombGP O (cstN m) ((List.range Bs.length).map (u.getD · 0)) (Bs.map Prod.snd), Q) :
        Code (m + 2))) with hf
  have hout : peOut ks m (wK O (ks m)) A B Cs n Q Bs = U.map f := by
    rw [hU, hvs]; rfl
  rw [hout]
  set βt := (List.range Bs.length).map (β.getD · 0) with hβt
  have hsemv : ∀ l < Bs.length, (T.MP (m + 1) h).sem (vs.getD l (opsM ks (m + 1)).zero) =
      T.phi m (resQX (T.MX m h) DS A B Cs (Bs.getD l ([], [])).1
        (GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2)) := fun l hl ↦ by
    have hvl : vs.getD l (opsM ks (m + 1)).zero =
        ((residE O (cstN m) (wK O (ks m)) A B Cs (Bs.getD l ([], [])), [O.one]) : Code (m + 2)) := by
      rw [hvs]; exact NestTower.getD_map' _ Bs ([], []) _ hl
    rw [hvl]
    change T.σX m h _ / T.σX m h [O.one] = _
    rw [T.σX_one, div_one, σX, toPoly_residEX DS A B Cs hcst (wK O (ks m)) hw]
  have h0 : (List.zipWith (fun c v ↦ algebraMap Kc (T.F (m + 1)) c * (T.MP (m + 1) h).sem v)
      βt vs).sum = 0 := by
    rw [NestTower.zipWith_sum_range _ 0 (opsM ks (m + 1)).zero _ _ (by simp [hβt, hlv])]
    have e : ∀ l ∈ Finset.range βt.length, algebraMap Kc (T.F (m + 1)) (βt.getD l 0) *
        (T.MP (m + 1) h).sem (vs.getD l (opsM ks (m + 1)).zero) =
        T.phi m (C (algebraMap Kc (T.F m) (β.getD l 0)) *
          resQX (T.MX m h) DS A B Cs (Bs.getD l ([], [])).1
            (GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2)) := fun l hl ↦ by
      have hl' : l < Bs.length := by simpa [hβt] using hl
      rw [hsemv l hl', NestTower.getD_range_map _ _ hl', map_mul, ← T.algebraMap_succ]
    rw [Finset.sum_congr rfl e, ← map_sum, show βt.length = Bs.length by simp [hβt], hres, map_zero]
  obtain ⟨γ, hγl, hγ⟩ := T.consys_complete (m + 1) h vs βt (by simp [hβt, hlv]) h0
  rw [← hU] at hγl hγ
  have hβγ : ∀ l < Bs.length, β.getD l 0 = ∑ k ∈ Finset.range U.length,
      γ.getD k 0 * algebraMap ℚ Kc ((U.getD k []).getD l 0) := fun l hl ↦ by
    have := hγ l
    rw [NestTower.getD_range_map _ _ hl, NestTower.zipWith_sum_range _ 0 [] _ _ hγl, hγl] at this
    exact this
  have hlen : (U.map f).length = U.length := List.length_map _
  have hgetD : ∀ k < U.length, (U.map f).getD k ([], (O.monomial (wK O (ks m))).zero) =
      f (U.getD k []) := fun k hk ↦ NestTower.getD_map' _ _ [] _ hk
  refine ⟨γ, fun i ↦ ?_, ?_⟩
  · rw [hlen]
    have e : ∀ k ∈ Finset.range U.length, γ.getD k 0 * algebraMap ℚ Kc
        (((U.map f).getD k ([], (O.monomial (wK O (ks m))).zero)).1.getD i 0) =
        γ.getD k 0 * algebraMap ℚ Kc ((vcomb n ((List.range Bs.length).map ((U.getD k []).getD · 0))
          (Bs.map Prod.fst)).getD i 0) := fun k hk ↦ by
      rw [hgetD k (Finset.mem_range.mp hk)]
    rw [Finset.sum_congr rfl e]
    by_cases hi : i < n
    · rw [hβc i]
      simp only [getD_vcomb, if_pos hi, map_sum, map_mul, Finset.mul_sum, List.length_map]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      have hl' := Finset.mem_range.mp hl
      rw [hβγ l hl', Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [NestTower.getD_range_map _ _ hl', NestTower.getD_map' _ _ ([], []) [] hl']
      ring
    · rw [hcn i (by omega)]
      symm
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [getD_vcomb, if_neg hi, map_zero, mul_zero]
  · set g : ℕ → T.F (m + 1) := fun l ↦ T.phi m (GPoly.toPoly (T.MX m h) (Bs.getD l ([], [])).2) /
      T.σX m h Q with hg
    have hyv : y = ∑ l ∈ Finset.range Bs.length, algebraMap Kc (T.F (m + 1)) (β.getD l 0) * g l := by
      rw [eq_div_iff hQ0 |>.mpr hy, hYv, map_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [map_mul, ← T.algebraMap_succ, hg, mul_div_assoc]
    have hsk : ∀ k < U.length, (T.M1X m h).sem (f (U.getD k [])).2 =
        ∑ l ∈ Finset.range Bs.length, (((U.getD k []).getD l 0 : ℚ) : T.F (m + 1)) * g l :=
      fun k hk ↦ by
      rw [hf]
      simp only
      rw [T.semX, σX, toPoly_lcombGP (T.MX m h) (cstN m) hcst,
        zipWith_sum_getD (fun (q : ℚ) (p : GPoly (Code (m + 1))) ↦
          C (q : T.F m) * GPoly.toPoly (T.MX m h) p) 0 [] (by simp), List.length_map, map_sum,
        Finset.sum_div]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      have hl' := Finset.mem_range.mp hl
      rw [NestTower.getD_range_map _ _ hl', NestTower.getD_map' _ _ ([], []) [] hl', map_mul,
        hphiq, hg, mul_div_assoc]
    rw [hlen, hyv]
    have e : ∀ k ∈ Finset.range U.length, algebraMap Kc (T.F (m + 1)) (γ.getD k 0) *
        (T.M1X m h).sem ((U.map f).getD k ([], (O.monomial (wK O (ks m))).zero)).2 =
        ∑ l ∈ Finset.range Bs.length, algebraMap Kc (T.F (m + 1)) (γ.getD k 0 *
          algebraMap ℚ Kc ((U.getD k []).getD l 0)) * g l := fun k hk ↦ by
      have hk' := Finset.mem_range.mp hk
      rw [hgetD k hk', hsk k hk', Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [map_mul, hqK]
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [hβγ l (Finset.mem_range.mp hl), map_sum, Finset.sum_mul]

end Final

end NestMTower

end Tower.NestM
