import RischTragerBronstein.Computable.NestXRdeSpec

/-!
# The Risch equation over an exponential level of a mixed tower: identity and soundness

`prdeExpX` at level `m + 1` (`t = tₘ = exp aₘ`) for `f = h′ + ∑ cⱼ wⱼ′ / wⱼ`: the equation for
`y = Y / Q` is the polynomial equation `A Y′ + B Y = ∑ cᵢ Cᵢ` times a non-zero factor
(`pe_identityXE`), and the final constant system forces it (`peOut_soundXE`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP Tower.NestX CPoly

section GenericXE

variable {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

lemma sem_leadG_XE (p : GPoly α) : M.sem (leadG O p) = (GPoly.toPoly M p).leadingCoeff := by
  by_cases hp : GPoly.toPoly M p = 0
  · rw [hp, leadingCoeff_zero, leadG, (GPoly.trim_eq_nil_iff M p).mpr hp]
    simp [GPoly.lead, M.sem_zero]
  · exact sem_leadG M p hp

lemma sem_lcC_XE (q : GPoly α × GPoly α) :
    M.sem (lcC O q) = (GPoly.toPoly M q.1).leadingCoeff / (GPoly.toPoly M q.2).leadingCoeff := by
  rw [lcC, M.sem_mul, M.sem_inv, sem_leadG_XE, sem_leadG_XE, div_eq_mul_inv]

lemma toPoly_powG_XE (p : GPoly α) : ∀ N, GPoly.toPoly M (powG O p N) = GPoly.toPoly M p ^ N
  | 0 => by simp [powG, M.sem_one]
  | N + 1 => by rw [powG, GPoly.toPoly_mul, toPoly_powG_XE p N, pow_succ, mul_comm]

lemma toPoly_nrmP_XE (p : GPoly α) (hp : GPoly.toPoly M p ≠ 0) :
    GPoly.toPoly M (nrmP O true p) = GPoly.toPoly M (p.drop (lowZ O p)) := by
  have : GPoly.isZero O p = false := by
    cases hb : GPoly.isZero O p
    · rfl
    · exact absurd ((GPoly.isZero_iff M _).mp hb) hp
  simp [nrmP, this]

lemma toPoly_nrmP_ne_XE (b : Bool) (p : GPoly α) : GPoly.toPoly M (nrmP O b p) ≠ 0 := by
  unfold nrmP
  split_ifs with h1 h2
  · simp [M.sem_one]
  · intro h0
    have hp : GPoly.toPoly M p ≠ 0 := fun h' ↦ h1 ((GPoly.isZero_iff M _).mpr h')
    exact not_X_dvd_drop_lowZ M p hp (h0 ▸ dvd_zero _)
  · exact fun h0 ↦ h1 ((GPoly.isZero_iff M _).mpr h0)

lemma toPoly_logPoly_ne_XE (b : Bool) :
    ∀ logs : List ((GPoly α × GPoly α) × (GPoly α × GPoly α)),
      GPoly.toPoly M (logPoly O b logs) ≠ 0
  | [] => by simp [logPoly, M.sem_one]
  | cw :: l => by
    rw [logPoly, List.foldr_cons, GPoly.toPoly_mul, GPoly.toPoly_mul]
    exact mul_ne_zero (mul_ne_zero (toPoly_nrmP_ne_XE M b _) (toPoly_nrmP_ne_XE M b _))
      (toPoly_logPoly_ne_XE b l)

/-- Every normal part of a logarithm divides `logPoly`. -/
lemma dvd_logPoly_XE : ∀ (logs : List ((GPoly α × GPoly α) × (GPoly α × GPoly α))) (cw)
    (_ : cw ∈ logs), GPoly.toPoly M (nrmP O true cw.2.1) * GPoly.toPoly M (nrmP O true cw.2.2) ∣
      GPoly.toPoly M (logPoly O true logs)
  | [], _, hx => by simp at hx
  | x :: l, cw, hx => by
    rw [logPoly, List.foldr_cons, GPoly.toPoly_mul, GPoly.toPoly_mul]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (dvd_logPoly_XE l cw hx) _

end GenericXE

namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : (m : ℕ) → KindN m}
variable (T : NestMTower Kc E ks)

section IdentityXE

variable (m : ℕ) (h : T.Tr (m + 1))

lemma sem_peFX_XE (fc : GPoly (Code (m + 1)) × GPoly (Code (m + 1))) (Q : GPoly (Code (m + 1))) :
    T.σX m h (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q).1 /
      T.σX m h (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q).2 =
      (T.M1X m h).sem fc - (T.σX m h Q)′ / T.σX m h Q := by
  rw [← T.semX, peFX, T.semX_cleanG, (T.M1X m h).sem_add, (T.M1X m h).sem_neg,
    (T.M1X m h).sem_mul, (T.M1X m h).sem_deriv, (T.M1X m h).sem_inv, T.semX_poly]
  ring

lemma peFX_ne_XE (fc : GPoly (Code (m + 1)) × GPoly (Code (m + 1))) (Q : GPoly (Code (m + 1))) :
    T.σX m h (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q).2 ≠ 0 :=
  T.σX_cleanG_ne m h _

lemma peRsX_ne_XE (Wc : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1))))
    (Q : GPoly (Code (m + 1))) :
    ∀ p ∈ peRsX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) Wc Q,
      T.σX m h p.2 ≠ 0 := fun p hp ↦ by
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hp
  exact T.σX_cleanG_ne m h _

/-- **The identity behind `prdeExpX`**: the polynomial equation is the Risch equation for `Y / Q`
times the non-zero factor `F₂ P Q`. -/
lemma pe_identityXE (fc : GPoly (Code (m + 1)) × GPoly (Code (m + 1)))
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
  have hsF := T.sem_peFX_XE m h fc Q
  rw [← hF] at hsF
  have hF2 : T.σX m h F.2 ≠ 0 := T.peFX_ne_XE m h fc Q
  have hRs2 := T.peRsX_ne_XE m h Wc Q
  rw [← hRs] at hRs2
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
    rw [hRi, ← T.semX, T.semX_cleanG, (T.M1X m h).sem_mul, T.semX_poly]
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

/-- **Soundness of the final constant system**: every output of `peOut` solves the Risch equation
`y′ + f y = ∑ cᵢ wᵢ` (whatever the basis `Bs`). -/
theorem peOut_soundXE (DS : DShape (T.F m)) (hDS : DS.W = T.wPoly m)
    (fc : GPoly (Code (m + 1)) × GPoly (Code (m + 1)))
    (W : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1)))) (Q : GPoly (Code (m + 1)))
    (hQ0 : T.σX m h Q ≠ 0) (Bs : List (List ℚ × GPoly (Code (m + 1)))) :
    ∀ r ∈ peOut ks m (wK (opsM ks m) (ks m))
      (peA (opsM ks m) (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q)
        (peRsX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m)))
          (W.map (cleanG (opsM ks m))) Q))
      (peB (opsM ks m) (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q)
        (peRsX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m)))
          (W.map (cleanG (opsM ks m))) Q))
      (peCs (opsM ks m) (peFX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fc Q)
        (peRsX (opsM ks m) ((opsM ks m).monomial (wK (opsM ks m) (ks m)))
          (W.map (cleanG (opsM ks m))) Q))
      (W.map (cleanG (opsM ks m))).length Q Bs,
      ((T.M1X m h).sem r.2)′ + (T.M1X m h).sem fc * (T.M1X m h).sem r.2 =
        sQ (T.M1X m h) r.1 W := by
  intro r hr
  set O := opsM ks m with hO
  set O' := O.monomial (wK O (ks m)) with hO'
  obtain ⟨Wc, hWc⟩ : ∃ Wc, Wc = W.map (cleanG O) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = peFX O O' fc Q := ⟨_, rfl⟩
  obtain ⟨Rs, hRs⟩ : ∃ Rs, Rs = peRsX O O' Wc Q := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = peA O F Rs := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = peB O F Rs := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ Cs, Cs = peCs O F Rs := ⟨_, rfl⟩
  rw [← hWc, ← hF, ← hRs, ← hA, ← hB, ← hCs] at hr
  unfold peOut at hr
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
  set β := (List.range Bs.length).map (u.getD · 0) with hβ
  have hβD : ∀ l < Bs.length, β.getD l 0 = u.getD l 0 := fun l hl ↦
    NestTower.getD_range_map _ _ hl
  have hqK : ∀ q : ℚ, algebraMap Kc (T.F (m + 1)) (algebraMap ℚ Kc q) = (q : T.F (m + 1)) :=
    fun q ↦ T.algebraMap_ratX q
  have hqK' : ∀ q : ℚ, algebraMap Kc (T.F m) (algebraMap ℚ Kc q) = (q : T.F m) :=
    fun q ↦ T.algebraMap_ratX q
  have hw : GPoly.toPoly (T.MX m h) (wK O (ks m)) = DS.W := by rw [hDS, T.toPoly_wKX]
  have hcst : ∀ q, (T.MX m h).sem (cstN m q) = (q : T.F m) := T.sem_cstX m h
  -- the constant system gives `∑ uₗ resₗ = 0`
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
  have hQ0' : T.σX m h Q ≠ 0 := hQ0
  have hid := T.pe_identityXE m h fc Wc Q hQ0 Y (fun i ↦ algebraMap ℚ Kc (c.getD i 0))
  rw [← hF, ← hRs, ← hA, ← hB, ← hCs] at hid
  have hlhs : GPoly.toPoly (T.MX m h) A * implicitDeriv (T.wPoly m) Y +
      GPoly.toPoly (T.MX m h) B * Y -
      ∑ i ∈ Finset.range Wc.length, C (algebraMap Kc (T.F m) (algebraMap ℚ Kc (c.getD i 0))) *
        GPoly.toPoly (T.MX m h) (Cs.getD i []) = 0 := by
    have h' := hpoly
    unfold resQX DzX at h'
    rw [hlCs, hDS] at h'
    have hs2 : ∑ i ∈ Finset.range Wc.length, C (algebraMap Kc (T.F m) (algebraMap ℚ Kc (c.getD i 0))) *
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
  have hsol : (T.M1X m h).sem (lcombGP O (cstN m) β (Bs.map Prod.snd), Q) =
      T.phi m Y / T.σX m h Q := T.semX m h _
  simp only
  rw [hsol]
  unfold sQ
  have e : ∀ i ∈ Finset.range W.length, ((c.getD i 0 : ℚ) : T.F (m + 1)) *
      (T.M1X m h).sem (W.getD i O'.zero) =
      algebraMap Kc (T.F (m + 1)) (algebraMap ℚ Kc (c.getD i 0)) *
        (T.M1X m h).sem (Wc.getD i O'.zero) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hwc : (T.M1X m h).sem (Wc.getD i O'.zero) = (T.M1X m h).sem (W.getD i O'.zero) := by
      rw [hWc, NestTower.getD_map' _ _ O'.zero _ hi', T.semX_cleanG]
    rw [hqK, hwc]
  rw [Finset.sum_congr rfl e, show W.length = Wc.length by simp [hWc]]
  linear_combination hbr

end SoundXE

end NestMTower

end Tower.NestM
