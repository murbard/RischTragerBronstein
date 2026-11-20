import RischTragerBronstein.Computable.NestPElemPoly
import RischTragerBronstein.Computable.NestPParamStep
import RischTragerBronstein.Computable.PrimNElem
import RischTragerBronstein.Computable.GHermiteComplete

/-!
# Parametric elementary integration in towers with nested primitives

`paramElem ηs m W` returns a list of vectors `β ∈ ℚⁿ` such that

* (`PESound`) every `∑ βᵢ wᵢ` has an elementary integral over every elementary extension;
* (`PEComplete`) whenever `∑ cᵢ wᵢ` (`cᵢ` constants) has a Liouville form over `Kₘ`, `c` is a
  constant combination of the returned vectors.

At the base `ℚ(x)` everything is elementary. At level `m + 1` (`t′ = ηₘ`) every weight is
Hermite-reduced, `wᵢ = gᵢ′ + Pᵢ + Nᵢ / S` over a common squarefree denominator `S` (the lcm of the
Hermite denominators); the logarithmic part forces the residue test `S ∣ T(∑ cᵢ Rᵢ, S)`, which is
linear in `c` — a constant system at level `m + 1` — and the polynomial part is the parametric
elementary polynomial problem (`polyElem`), whose degree-`0` equation is solved by `paramElem` one
level down.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestP

open Tower.PrimN

/-! ### Least common multiples -/

namespace GPolyLcm

variable {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

lemma lcmG_spec (a b : GPoly α) (ha : GPoly.toPoly M a ≠ 0) (hb : GPoly.toPoly M b ≠ 0) :
    GPoly.toPoly M a ∣ GPoly.toPoly M (lcmG O a b) ∧ GPoly.toPoly M b ∣ GPoly.toPoly M (lcmG O a b) ∧
      GPoly.toPoly M (lcmG O a b) ≠ 0 ∧
      (Squarefree (GPoly.toPoly M a) → Squarefree (GPoly.toPoly M b) →
        Squarefree (GPoly.toPoly M (lcmG O a b))) := by
  obtain ⟨hga, hgb⟩ := GPoly.egcd_dvd M a b
  set g := (GPoly.egcd O a b).1 with hg
  have hg0 : GPoly.toPoly M g ≠ 0 := fun h0 ↦ hb (zero_dvd_iff.mp (h0 ▸ hgb))
  have hbq := GPoly.div_mul_of_dvd M b g hg0 hgb
  set bq := GPoly.toPoly M (GPoly.divMod O b g).1 with hbqd
  have hlcm : GPoly.toPoly M (lcmG O a b) = GPoly.toPoly M a * bq := by
    rw [lcmG, GPoly.toPoly_mul]
  have hbq0 : bq ≠ 0 := fun h0 ↦ hb (by rw [hbq, h0, zero_mul])
  obtain ⟨a', ha'⟩ := hga
  refine ⟨⟨bq, hlcm⟩, ⟨a', by rw [hlcm, ha', hbq]; ring⟩, by rw [hlcm]; exact mul_ne_zero ha hbq0,
    fun hsa hsb ↦ ?_⟩
  rw [hlcm]
  have hsbq : Squarefree bq := hsb.squarefree_of_dvd ⟨GPoly.toPoly M g, hbq⟩
  refine (squarefree_mul_iff).mpr ⟨fun d hda hdbq ↦ ?_, hsa, hsbq⟩
  have hdb : d ∣ GPoly.toPoly M b := hdbq.trans ⟨GPoly.toPoly M g, hbq⟩
  have hdg : d ∣ GPoly.toPoly M g := GPoly.dvd_egcd M a b hda hdb
  exact hsb d (by rw [hbq]; exact mul_dvd_mul hdbq hdg)

lemma lcmList_spec : ∀ l : List (GPoly α), (∀ p ∈ l, GPoly.toPoly M p ≠ 0) →
    (∀ p ∈ l, GPoly.toPoly M p ∣ GPoly.toPoly M (lcmList O l)) ∧
      GPoly.toPoly M (lcmList O l) ≠ 0 ∧
      ((∀ p ∈ l, Squarefree (GPoly.toPoly M p)) → Squarefree (GPoly.toPoly M (lcmList O l)))
  | [], _ => ⟨by simp, by simp [lcmList, M.sem_one], fun _ ↦ by simp [lcmList, M.sem_one]⟩
  | p :: l, h0 => by
    obtain ⟨ih1, ih2, ih3⟩ := lcmList_spec l fun q hq ↦ h0 q (List.mem_cons_of_mem _ hq)
    obtain ⟨h1, h2, h3, h4⟩ := lcmG_spec M p (lcmList O l) (h0 p List.mem_cons_self) ih2
    refine ⟨fun q hq ↦ ?_, h3, fun hsq ↦ h4 (hsq p List.mem_cons_self)
      (ih3 fun q hq ↦ hsq q (List.mem_cons_of_mem _ hq))⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h1
    · exact (ih1 q hq).trans h2

end GPolyLcm

/-! ### The residue test is linear in the residue polynomial -/

lemma mapCoeffs_C_mul_const {F : Type*} [Field F] [Differential F] {c : F} (hc : c′ = 0)
    (P : F[X]) : mapCoeffs (C c * P) = C c * mapCoeffs P := by
  ext n
  rw [coeff_mapCoeffs, coeff_C_mul, coeff_C_mul, coeff_mapCoeffs, Derivation.leibniz, hc]
  simp

lemma residueTest_sum {F : Type*} [Field F] [Differential F] (n : ℕ) (a : ℕ → F)
    (ha : ∀ i, (a i)′ = 0) (R : ℕ → F[X]) (S : F[X]) :
    residueTest (∑ i ∈ Finset.range n, C (a i) * R i) S =
      ∑ i ∈ Finset.range n, C (a i) * residueTest (R i) S := by
  simp only [residueTest, map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mapCoeffs_C_mul_const (ha i), derivative_mul, derivative_C]
  ring

/-! ### Liouville forms -/

lemma liouvilleIn_deriv_add {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] (M : IntermediateField F E)
    (y : E) (hy : y ∈ M) (b : E) (hb : LiouvilleIn M b) : LiouvilleIn M (y′ + b) := by
  obtain ⟨ι, s, c, u, v, hd, hv, rfl⟩ := hb
  exact ⟨ι, s, c, u, v + y, hd, add_mem hv hy, by rw [map_add]; ring⟩

/-! ### The data of the inductive step -/

open NestTower

variable {ηs : (m : ℕ) → Code (m + 1)}

/-- The common denominator `S` of the simple parts at level `m + 1`. -/
def lcmS (m : ℕ) (W : List (Code (m + 2))) : GPoly (Code (m + 1)) :=
  lcmList (opsQ ηs m) ((W.map (hermW (ηs := ηs) m)).map fun h ↦ h.s)

/-- The numerators `Nᵢ` of the simple parts over `S`. -/
def numL (m : ℕ) (W : List (Code (m + 2))) : List (GPoly (Code (m + 1))) :=
  (List.zip ((W.map (hermW (ηs := ηs) m)).map fun h ↦ GPoly.divMod (opsQ ηs m) h.b h.s)
    (W.map (hermW (ηs := ηs) m))).map fun p ↦
      GPoly.mul (opsQ ηs m) p.1.2 (GPoly.divMod (opsQ ηs m) (lcmS (ηs := ηs) m W) p.2.s).1

/-- The residue test polynomial of `Nᵢ / S`, reduced modulo `S`. -/
def ttCode (m : ℕ) (W : List (Code (m + 2))) (Ni : GPoly (Code (m + 1))) :
    GPoly (Code (m + 1)) :=
  (GPoly.divMod (opsQ ηs m) (residueTestCode (opsQ ηs m)
    (GPoly.residuePoly (opsQ ηs m) [ηs m] Ni (lcmS (ηs := ηs) m W)) (lcmS (ηs := ηs) m W))
    (lcmS (ηs := ηs) m W)).2

/-- The residue test polynomials, as codes of level `m + 1`. -/
def resCodes (m : ℕ) (W : List (Code (m + 2))) : List (Code (m + 2)) :=
  ((numL (ηs := ηs) m W).map (ttCode (ηs := ηs) m W)).map fun T ↦
    ((T, [(opsQ ηs m).one]) : Code (m + 2))

/-- The basis of the solutions of the residue condition. -/
def E1 (m : ℕ) (W : List (Code (m + 2))) : List (List ℚ) :=
  (consys ηs (m + 1) (resCodes (ηs := ηs) m W)).map (vecOf W.length)

/-- The check that `S` is a squarefree common multiple. -/
def lcmCheck (m : ℕ) (W : List (Code (m + 2))) : Bool :=
  GPoly.squarefreeCheck (opsQ ηs m) (lcmS (ηs := ηs) m W) &&
    (W.map (hermW (ηs := ηs) m)).all
      (fun h ↦ GPoly.isZero (opsQ ηs m) (GPoly.divMod (opsQ ηs m) (lcmS (ηs := ηs) m W) h.s).2)

/-- The polynomial parts of the reduced parametric problem. -/
def PuE (m : ℕ) (W : List (Code (m + 2))) : List (GPoly (Code (m + 1))) :=
  (E1 (ηs := ηs) m W).map fun e ↦ lcombGP (opsQ ηs m) (cstN m) e
    (((W.map (hermW (ηs := ηs) m)).map fun h ↦ GPoly.divMod (opsQ ηs m) h.b h.s).map Prod.fst)

lemma paramElem_succ_eq (m : ℕ) (W : List (Code (m + 2))) :
    paramElem ηs (m + 1) W =
      if lcmCheck (ηs := ηs) m W then
        (polyElem (opsQ ηs m) (cstN m) (ηs m) (paramLim ηs m) (paramElem ηs m)
          (PuE (ηs := ηs) m W)).map fun δ ↦ vcomb W.length δ (E1 (ηs := ηs) m W)
      else [] := rfl

lemma length_numL (m : ℕ) (W : List (Code (m + 2))) : (numL (ηs := ηs) m W).length = W.length :=
  len_zip_map _ _ _ W

lemma getD_numL (m : ℕ) (W : List (Code (m + 2))) {i : ℕ} (hi : i < W.length) :
    (numL (ηs := ηs) m W).getD i [] = GPoly.mul (opsQ ηs m)
      (GPoly.divMod (opsQ ηs m) (hermW (ηs := ηs) m (W.getD i (zc ηs (m + 1)))).b
        (hermW (ηs := ηs) m (W.getD i (zc ηs (m + 1)))).s).2
      (GPoly.divMod (opsQ ηs m) (lcmS (ηs := ηs) m W)
        (hermW (ηs := ηs) m (W.getD i (zc ηs (m + 1)))).s).1 :=
  getD_zip_map _ _ _ W (zc ηs (m + 1)) [] hi

lemma length_resCodes (m : ℕ) (W : List (Code (m + 2))) :
    (resCodes (ηs := ηs) m W).length = W.length := by
  unfold resCodes
  exact (List.length_map _).trans ((List.length_map _).trans (length_numL m W))

lemma getD_resCodes (m : ℕ) (W : List (Code (m + 2))) {i : ℕ} (hi : i < W.length) :
    (resCodes (ηs := ηs) m W).getD i (zc ηs (m + 1)) =
      ((ttCode (ηs := ηs) m W ((numL (ηs := ηs) m W).getD i []), [(opsQ ηs m).one]) :
        Code (m + 2)) :=
  getD_map_map _ _ _ [] _ (by rw [length_numL]; exact hi)

lemma length_E1 (m : ℕ) (W : List (Code (m + 2))) :
    (E1 (ηs := ηs) m W).length = (consys ηs (m + 1) (resCodes (ηs := ηs) m W)).length := by
  simp [E1]

namespace NestTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc]
variable (T : NestTower Kc E ηs)

/-- Soundness of a parametric elementary integration basis. -/
def PESound (m : ℕ) (h : T.Tr m) (W : List (Code (m + 1))) (out : List (List ℚ)) : Prop :=
  ∀ β ∈ out, HasElementaryIntegralIn ((T.sumQ m h β W : T.F m) : E)

/-- Completeness of a parametric elementary integration basis. -/
def PEComplete (m : ℕ) (h : T.Tr m) (W : List (Code (m + 1))) (out : List (List ℚ)) : Prop :=
  ∀ c : List Kc, (∀ i, W.length ≤ i → c.getD i 0 = 0) →
    LiouvilleIn (T.F m) ((T.sumK m h c W : T.F m) : E) →
    ∃ γ : List Kc, ∀ i, c.getD i 0 = ∑ k ∈ Finset.range out.length,
      γ.getD k 0 * algebraMap ℚ Kc ((out.getD k []).getD i 0)

/-! ### The base `ℚ(x)` -/

/-- Every element of `Kc(x)` given by a rational code has an elementary integral. -/
theorem rational_in (q : GFrac ℚ) : HasElementaryIntegralIn (evx Kc T.x q) := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
  by_cases hq : (CPoly.toPoly q.2).map (algebraMap ℚ Kc) = 0
  · have : evx Kc T.x q = (0 : E)′ := by simp [evx, hq]
    rw [this]
    exact hasElementaryIntegralIn_deriv 0
  intro E' _ _ _ _ _
  let _ : Algebra Kc E' := ((algebraMap E E').comp (algebraMap Kc E)).toAlgebra
  have hDA : DifferentialAlgebra Kc E' :=
    ⟨fun a ↦ by
      change (algebraMap E E' (algebraMap Kc E a))′ = algebraMap E E' (algebraMap Kc E a′)
      rw [deriv_algebraMap, deriv_algebraMap]⟩
  have hx : (algebraMap E E' T.x)′ = 1 := by rw [deriv_algebraMap, T.hx, map_one]
  have haev : ∀ P : Kc[X], algebraMap E E' (aeval T.x P) = aeval (algebraMap E E' T.x) P :=
    fun P ↦ by
      rw [aeval_def, aeval_def, hom_eval₂]
      rfl
  have := hasElementaryIntegral_rational_in T.hC (algebraMap E E' T.x) hx
    ((CPoly.toPoly q.1).map (algebraMap ℚ Kc)) _ hq 0
  rw [map_zero, zero_add] at this
  rw [evx, map_div₀, haev, haev]
  exact this

lemma sumQ_eq_sem (m : ℕ) (h : T.Tr m) (β : List ℚ) (W : List (Code (m + 1))) :
    T.sumQ m h β W = (T.MP m h).sem (lcombCode (opsQ ηs m) (cstN m) β W) := by
  rw [sem_lcombCode (T.MP m h) (cstN m) (T.sem_cstN m h),
    zipWith_sum_getD (fun (q : ℚ) (a : Code (m + 1)) ↦ ((q : ℚ) : T.F m) * (T.MP m h).sem a) 0
      (zc ηs m) (by simp)]
  rfl

theorem paramElem_zero (h : T.Tr 0) (W : List (Code 1)) :
    T.PESound 0 h W (paramElem ηs 0 W) ∧ T.PEComplete 0 h W (paramElem ηs 0 W) := by
  refine ⟨fun β _ ↦ ?_, fun c hc _ ↦ ?_⟩
  · rw [T.sumQ_eq_sem, T.sem_MP]
    exact T.rational_in _
  · refine ⟨(List.range W.length).map fun i ↦ c.getD i 0, fun i ↦ ?_⟩
    simp only [paramElem, List.length_map, List.length_range]
    have e : ∀ k ∈ Finset.range W.length, ((List.range W.length).map fun i ↦ c.getD i 0).getD k 0 *
        algebraMap ℚ Kc ((((List.range W.length).map (unitV W.length)).getD k []).getD i 0) =
        if i = k then (if i < W.length then c.getD i 0 else 0) else 0 := fun k hk ↦ by
      have hk' := Finset.mem_range.mp hk
      rw [getD_range_map _ _ hk', getD_range_map _ _ hk', getD_unitV]
      by_cases hik : i = k
      · subst hik; simp [hk']
      · simp [hik]
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq]
    by_cases hi : i < W.length
    · simp [hi]
    · simp only [Finset.mem_range, hi, if_false]
      exact hc i (by omega)

/-! ### The data of the inductive step, as values -/

lemma degree_sum_C_mul_lt {F : Type*} [Field F] (n : ℕ) (a : ℕ → F) (N : ℕ → F[X]) (S : F[X])
    (hS : S ≠ 0) (h : ∀ i < n, (N i).degree < S.degree) :
    (∑ i ∈ Finset.range n, C (a i) * N i).degree < S.degree := by
  induction n with
  | zero => simpa using bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hS)
  | succ n ih =>
    rw [Finset.sum_range_succ]
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt (ih fun i hi ↦ h i (by omega)) ?_)
    exact lt_of_le_of_lt (by rw [← smul_eq_C_mul]; exact degree_smul_le _ _) (h n (by omega))

lemma getD_mem_of_lt {γ : Type*} (l : List γ) (d : γ) {i : ℕ} (hi : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _

/-- **The common denominator**: squarefree, and every weight is `gᵢ′ + Pᵢ + Nᵢ / S`. -/
lemma lcm_data (m : ℕ) (h : T.Tr (m + 1)) (hm : T.Tr m) (W : List (Code (m + 2)))
    (hchk : lcmCheck (ηs := ηs) m W = true) :
    Squarefree (GPoly.toPoly (T.MP m hm) (lcmS (ηs := ηs) m W)) ∧
    ∀ i < W.length, (T.MP (m + 1) h).sem (W.getD i (zc ηs (m + 1))) =
      ((T.MP (m + 1) h).sem (gCode (ηs := ηs) m (W.getD i (zc ηs (m + 1)))))′ +
      T.phi m (GPoly.toPoly (T.MP m hm) (pPart (ηs := ηs) m (W.getD i (zc ηs (m + 1))))) +
      T.phi m (GPoly.toPoly (T.MP m hm) ((numL (ηs := ηs) m W).getD i [])) /
        T.phi m (GPoly.toPoly (T.MP m hm) (lcmS (ηs := ηs) m W)) ∧
      (GPoly.toPoly (T.MP m hm) ((numL (ηs := ηs) m W).getD i [])).degree <
        (GPoly.toPoly (T.MP m hm) (lcmS (ηs := ηs) m W)).degree := by
  set M := T.MP m hm with hM
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hinj := T.phi_injective htr
  simp only [lcmCheck, Bool.and_eq_true] at hchk
  obtain ⟨hsqc, hall⟩ := hchk
  have hsq : Squarefree (GPoly.toPoly M (lcmS (ηs := ηs) m W)) := GPoly.squarefreeCheck_sound M hsqc
  refine ⟨hsq, fun i hi ↦ ?_⟩
  set w := W.getD i (zc ηs (m + 1)) with hw
  have hdec := T.weight_decomp m h w
  obtain ⟨hval, hsqs, hdeg⟩ := hdec
  have hz := List.all_eq_true.mp hall (hermW (ηs := ηs) m w)
    (List.mem_map.mpr ⟨w, getD_mem_of_lt W _ hi, rfl⟩)
  have hr0 := (GPoly.isZero_iff M _).mp hz
  have hdm := GPoly.divMod_spec M (lcmS (ηs := ηs) m W) (hermW (ηs := ηs) m w).s
  rw [hr0, add_zero] at hdm
  set d := GPoly.toPoly M (GPoly.divMod (opsQ ηs m) (lcmS (ηs := ηs) m W) (hermW (ηs := ηs) m w).s).1
    with hd
  set sv := GPoly.toPoly M (hermW (ηs := ηs) m w).s with hsv
  set rv := GPoly.toPoly M
    (GPoly.divMod (opsQ ηs m) (hermW (ηs := ηs) m w).b (hermW (ηs := ηs) m w).s).2 with hrv
  have hd0 : d ≠ 0 := fun h0 ↦ hsq.ne_zero (by rw [hdm, h0, zero_mul])
  have hN : GPoly.toPoly M ((numL (ηs := ηs) m W).getD i []) = rv * d := by
    rw [getD_numL m W hi, GPoly.toPoly_mul]
  refine ⟨?_, ?_⟩
  · rw [hval, hN, hdm]
    have hφd : T.phi m d ≠ 0 := (map_ne_zero_iff _ hinj).mpr hd0
    have hφs : T.phi m sv ≠ 0 := (map_ne_zero_iff _ hinj).mpr hsqs.ne_zero
    simp only [map_mul, gCode, pPart]
    field_simp
    simp only [hM]
    ring
  · rw [hN, hdm, degree_mul, degree_mul, add_comm]
    exact WithBot.add_lt_add_left (degree_ne_bot.mpr hd0) hdeg

lemma toPoly_residueTestCode {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α}
    (M : CField α K O) (r s : GPoly α) :
    GPoly.toPoly M (residueTestCode O r s) = residueTest (GPoly.toPoly M r) (GPoly.toPoly M s) := by
  rw [residueTestCode, residueTest, GPoly.toPoly_sub, GPoly.toPoly_mul, GPoly.toPoly_mul,
    GPoly.toPoly_mapD, GPoly.toPoly_mapD, GPoly.toPoly_derivX, GPoly.toPoly_derivX]

/-- **The residue data**: the residue polynomial of `Nᵢ / S` and its reduced test polynomial. -/
lemma res_data (m : ℕ) (h : T.Tr (m + 1)) (hm : T.Tr m) (W : List (Code (m + 2)))
    (hS : Squarefree (GPoly.toPoly (T.MP m hm) (lcmS (ηs := ηs) m W))) (Ni : GPoly (Code (m + 1))) :
    GPoly.toPoly (T.MP m hm) (lcmS (ηs := ηs) m W) ∣
      GPoly.toPoly (T.MP m hm) (GPoly.residuePoly (opsQ ηs m) [ηs m] Ni (lcmS (ηs := ηs) m W)) *
        (mapCoeffs (GPoly.toPoly (T.MP m hm) (lcmS (ηs := ηs) m W)) +
          C (T.valN m (ηs m)) * derivative (GPoly.toPoly (T.MP m hm) (lcmS (ηs := ηs) m W))) -
        GPoly.toPoly (T.MP m hm) Ni ∧
    GPoly.toPoly (T.MP m hm) (lcmS (ηs := ηs) m W) ∣
      residueTest (GPoly.toPoly (T.MP m hm)
        (GPoly.residuePoly (opsQ ηs m) [ηs m] Ni (lcmS (ηs := ηs) m W)))
        (GPoly.toPoly (T.MP m hm) (lcmS (ηs := ηs) m W)) -
        GPoly.toPoly (T.MP m hm) (ttCode (ηs := ηs) m W Ni) ∧
    (GPoly.toPoly (T.MP m hm) (ttCode (ηs := ηs) m W Ni)).degree <
      (GPoly.toPoly (T.MP m hm) (lcmS (ηs := ηs) m W)).degree := by
  set M := T.MP m hm with hM
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hcop : IsCoprime (implicitDeriv (GPoly.toPoly M [ηs m]) (GPoly.toPoly M (lcmS (ηs := ηs) m W)))
      (GPoly.toPoly M (lcmS (ηs := ηs) m W)) := by
    rw [T.toPoly_wK]
    let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
    exact isCoprime_deriv_of_squarefree hS (fun p hp _ ↦ T.normal m htr p hp)
  have hrs := GPoly.residuePoly_spec M [ηs m] Ni _ hS.ne_zero hcop
  rw [T.toPoly_wK, wPoly, PrimN.PrimTower.implicitDeriv_C_eq] at hrs
  refine ⟨by simpa using hrs, ?_, GPoly.divMod_degree_lt M _ _ hS.ne_zero⟩
  have hdm := GPoly.divMod_spec M (residueTestCode (opsQ ηs m)
    (GPoly.residuePoly (opsQ ηs m) [ηs m] Ni (lcmS (ηs := ηs) m W)) (lcmS (ηs := ηs) m W))
    (lcmS (ηs := ηs) m W)
  rw [toPoly_residueTestCode] at hdm
  rw [ttCode, hdm]
  exact ⟨_, by ring⟩

/-- The relation given by a basis vector of the residue system. -/
lemma rel_res (m : ℕ) (h : T.Tr (m + 1)) (hm : T.Tr m) (W : List (Code (m + 2))) (u : CPoly ℚ)
    (hu : u ∈ consys ηs (m + 1) (resCodes (ηs := ηs) m W)) :
    ∑ i ∈ Finset.range W.length, C ((u.getD i 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.MP m hm) (ttCode (ηs := ηs) m W ((numL (ηs := ηs) m W).getD i [])) = 0 := by
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have := T.consys_sound (m + 1) h (resCodes (ηs := ηs) m W) u hu
  rw [zipWith_sum_range _ 0 (zc ηs (m + 1)) _ _ (by simp)] at this
  apply T.phi_injective htr
  rw [map_zero, ← this, map_sum]
  refine Finset.sum_congr (by rw [List.length_map, List.length_range, length_resCodes]) fun i hi ↦ ?_
  have hi' : i < W.length := by
    have := Finset.mem_range.mp hi
    rwa [List.length_map, List.length_range, length_resCodes] at this
  rw [getD_range_map (fun j ↦ algebraMap ℚ Kc (u.getD j 0)) 0
    (by rw [length_resCodes]; exact hi'), T.algebraMap_ratCast, getD_resCodes m W hi',
    map_mul, T.phi_C_ratCast]
  congr 1
  symm
  refine (T.sem_MP_succ m h _).trans ?_
  simp [(T.MP m hm).sem_one]

/-- The polynomial parts, recombined. -/
lemma sum_pv_eq (m : ℕ) (hm : T.Tr m) (W : List (Code (m + 2))) (δ : List ℚ) :
    ∑ i ∈ Finset.range W.length, C (((vcomb W.length δ (E1 (ηs := ηs) m W)).getD i 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.MP m hm) (pPart (ηs := ηs) m (W.getD i (zc ηs (m + 1)))) =
    polySumQ (T.MP m hm) δ (PuE (ηs := ηs) m W) := by
  rw [polySumQ]
  have hl : (PuE (ηs := ηs) m W).length = (E1 (ηs := ηs) m W).length := by simp [PuE]
  have e : ∀ k ∈ Finset.range (PuE (ηs := ηs) m W).length, C ((δ.getD k 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.MP m hm) ((PuE (ηs := ηs) m W).getD k []) = ∑ i ∈ Finset.range W.length,
        C (((δ.getD k 0 * ((E1 (ηs := ηs) m W).getD k []).getD i 0 : ℚ)) : T.F m) *
          GPoly.toPoly (T.MP m hm) (pPart (ηs := ηs) m (W.getD i (zc ηs (m + 1)))) := fun k hk ↦ by
    have hk' : k < (E1 (ηs := ηs) m W).length := by rw [← hl]; exact Finset.mem_range.mp hk
    rw [PuE, getD_map' _ _ [] [] hk', T.toPoly_Pu m hm W, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    push_cast
    rw [C_mul]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm, hl]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [getD_vcomb, if_pos (Finset.mem_range.mp hi), ← Finset.sum_mul]
  push_cast
  rw [map_sum]

/-- The test polynomials, recombined, vanish. -/
lemma sum_Tv_eq_zero (m : ℕ) (h : T.Tr (m + 1)) (hm : T.Tr m) (W : List (Code (m + 2)))
    (δ : List ℚ) :
    ∑ i ∈ Finset.range W.length, C (((vcomb W.length δ (E1 (ηs := ηs) m W)).getD i 0 : ℚ) : T.F m) *
      GPoly.toPoly (T.MP m hm) (ttCode (ηs := ηs) m W ((numL (ηs := ηs) m W).getD i [])) = 0 := by
  set U := consys ηs (m + 1) (resCodes (ηs := ηs) m W) with hU
  have e : ∀ i ∈ Finset.range W.length,
      C (((vcomb W.length δ (E1 (ηs := ηs) m W)).getD i 0 : ℚ) : T.F m) *
        GPoly.toPoly (T.MP m hm) (ttCode (ηs := ηs) m W ((numL (ηs := ηs) m W).getD i [])) =
      ∑ k ∈ Finset.range U.length, C ((δ.getD k 0 : ℚ) : T.F m) *
        (C (((U.getD k []).getD i 0 : ℚ) : T.F m) *
          GPoly.toPoly (T.MP m hm) (ttCode (ηs := ηs) m W ((numL (ηs := ηs) m W).getD i []))) :=
    fun i hi ↦ by
      have hi' := Finset.mem_range.mp hi
      rw [getD_vcomb, if_pos hi', length_E1, ← hU]
      push_cast
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [E1, ← hU, getD_map' _ U [] [] (Finset.mem_range.mp hk), getD_vecOf, if_pos hi', C_mul]
      ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  rw [← Finset.mul_sum, T.rel_res m h hm W _ (getD_mem_of_lt U [] (Finset.mem_range.mp hk)), mul_zero]

/-- **Soundness of the inductive step.** -/
theorem paramElem_succ_sound (m : ℕ) (h : T.Tr (m + 1))
    (IHL : ∀ W', T.PLSound m (fun i hi ↦ h i (by omega)) W' (paramLim ηs m W') ∧
      T.PLComplete m (fun i hi ↦ h i (by omega)) W' (paramLim ηs m W'))
    (IHE : ∀ W', T.PESound m (fun i hi ↦ h i (by omega)) W' (paramElem ηs m W'))
    (W : List (Code (m + 2))) : T.PESound (m + 1) h W (paramElem ηs (m + 1) W) := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
  set hm : T.Tr m := fun i hi ↦ h i (by omega) with hhm
  set M := T.MP m hm with hM
  set M' := T.MP (m + 1) h with hM'
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hinj := T.phi_injective htr
  have hspec := T.limSpec_of m hm IHL
  have hconstK : ∀ y : T.F m, y′ = 0 → ∃ κ : Kc, y = algebraMap Kc (T.F m) κ := fun y hy ↦
    T.const_F y hy
  intro v hv
  rw [paramElem_succ_eq] at hv
  split_ifs at hv with hchk
  swap
  · simp at hv
  obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hv
  obtain ⟨hsq, hdat⟩ := T.lcm_data m h hm W hchk
  set n := W.length with hn
  set Sv := GPoly.toPoly M (lcmS (ηs := ηs) m W) with hSv
  set vq : ℕ → ℚ := fun i ↦ (vcomb n δ (E1 (ηs := ηs) m W)).getD i 0 with hvq
  set Nq := ∑ i ∈ Finset.range n, C ((vq i : ℚ) : T.F m) *
    GPoly.toPoly M ((numL (ηs := ηs) m W).getD i []) with hNq
  set Rq := ∑ i ∈ Finset.range n, C ((vq i : ℚ) : T.F m) *
    GPoly.toPoly M (GPoly.residuePoly (opsQ ηs m) [ηs m] ((numL (ηs := ηs) m W).getD i [])
      (lcmS (ηs := ηs) m W)) with hRq
  set G := ∑ i ∈ Finset.range n, ((vq i : ℚ) : T.F (m + 1)) *
    M'.sem (gCode (ηs := ηs) m (W.getD i (zc ηs (m + 1)))) with hG
  -- the polynomial part
  obtain ⟨Q, b, hQb, hb⟩ := polyElem_sound (algebraMap Kc (T.F m)) (ηs m) (paramLim ηs m)
    (paramElem ηs m) (T.sem_cstN m hm) hspec hconstK (fun q ↦ T.algebraMap_ratCast q)
    (fun b ↦ HasElementaryIntegralIn ((b : T.F m) : E)) (fun ws β hβ ↦ IHE ws β hβ)
    (PuE (ηs := ηs) m W) δ hδ
  have hP : ∑ i ∈ Finset.range n, C ((vq i : ℚ) : T.F m) *
      GPoly.toPoly M (pPart (ηs := ηs) m (W.getD i (zc ηs (m + 1)))) =
      Dη M (ηs m) Q + C b := by
    rw [← hQb]
    exact T.sum_pv_eq m hm W δ
  -- the value
  have hA : T.sumQ (m + 1) h (vcomb n δ (E1 (ηs := ηs) m W)) W =
      (G + T.phi m Q)′ + T.phi m (C b) + T.phi m Nq / T.phi m Sv := by
    have hφS : T.phi m Sv ≠ 0 := (map_ne_zero_iff _ hinj).mpr hsq.ne_zero
    have hDQ : T.phi m (Dη M (ηs m) Q) = (T.phi m Q)′ := by
      rw [Dη, ← T.wPoly_eq m hm, ← T.deriv_phi]
    rw [map_add, ← hDQ, add_assoc (G′), ← map_add (T.phi m), ← hP, hG, T.deriv_sum_ratCast,
      map_sum, hNq, map_sum, Finset.sum_div, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, sumQ]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [(hdat i (Finset.mem_range.mp hi)).1, map_mul, map_mul, T.phi_C_ratCast]
    simp only [hvq, hM, hM']
    ring
  -- the logarithmic part
  have hlog : HasElementaryIntegralIn (aeval (T.ts m) Nq / aeval (T.ts m) Sv) := by
    have hst : aeval (T.ts m) Sv ≠ 0 := by
      rw [← T.coe_phi]
      exact fun h0 ↦ hsq.ne_zero (hinj ((Subtype.ext h0).trans (map_zero _).symm))
    have hdeg : Nq.degree < Sv.degree :=
      degree_sum_C_mul_lt n _ _ Sv hsq.ne_zero fun i hi ↦ (hdat i hi).2
    have hr : Sv ∣ Rq * (mapCoeffs Sv + (C (T.valN m (ηs m)) + C 0 * X) * derivative Sv) - Nq := by
      rw [C_0, zero_mul, add_zero, hRq, hNq, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.dvd_sum fun i _ ↦ ?_
      have := (T.res_data m h hm W hsq ((numL (ηs := ηs) m W).getD i [])).1
      rw [show ∀ a b c d : (T.F m)[X], a * b * c - a * d = a * (b * c - d) from
        fun _ _ _ _ ↦ by ring]
      exact dvd_mul_of_dvd_right this _
    have hT : Sv ∣ residueTest Rq Sv := by
      rw [hRq, residueTest_sum n _ (fun i ↦ T.deriv_ratCast _)]
      have h0 := T.sum_Tv_eq_zero m h hm W δ
      rw [← sub_zero (∑ i ∈ Finset.range n, _), ← h0, ← Finset.sum_sub_distrib]
      refine Finset.dvd_sum fun i _ ↦ ?_
      rw [← mul_sub]
      exact dvd_mul_of_dvd_right (T.res_data m h hm W hsq _).2.1 _
    exact hasElementaryIntegralIn_of_residueTest (F := T.F m) (T.ts m) (T.valN m (ηs m)) 0
      (by rw [map_zero, zero_mul, add_zero]; exact T.ht m) 1 one_ne_zero
      (by rw [logDeriv_one, map_zero]) Sv Nq Rq (PerfectField.separable_iff_squarefree.mpr hsq)
      hst hdeg hr hT
  have hAE : ((T.sumQ (m + 1) h (vcomb n δ (E1 (ηs := ηs) m W)) W : T.F (m + 1)) : E) =
      ((G + T.phi m Q : T.F (m + 1)) : E)′ + ((b : T.F m) : E) +
        aeval (T.ts m) Nq / aeval (T.ts m) Sv := by
    rw [hA, IntermediateField.coe_add, IntermediateField.coe_add, IntermediateField.coe_div,
      coe_deriv, T.coe_phi, T.coe_phi, T.coe_phi, aeval_C]
    rfl
  rw [hAE]
  exact ((hasElementaryIntegralIn_deriv _).add hb).add hlog

/-! ### Completeness -/

lemma const_mem (m : ℕ) (z : E) (hz : z′ = 0) : z ∈ T.F m := by
  obtain ⟨κ, rfl⟩ := T.hCall z hz
  exact (T.F m).algebraMap_mem κ

lemma coe_logDeriv_F {m : ℕ} (y : T.F m) : ((logDeriv y : T.F m) : E) = logDeriv (y : E) := by
  unfold logDeriv
  rw [IntermediateField.coe_div, coe_deriv]

/-- **The lcm check always passes** (given transcendence). -/
lemma lcmCheck_true (m : ℕ) (h : T.Tr (m + 1)) (hm : T.Tr m) (W : List (Code (m + 2))) :
    lcmCheck (ηs := ηs) m W = true := by
  set M := T.MP m hm with hM
  have hs : ∀ p ∈ (W.map (hermW (ηs := ηs) m)).map (fun h ↦ h.s),
      GPoly.toPoly M p ≠ 0 ∧ Squarefree (GPoly.toPoly M p) := by
    intro p hp
    obtain ⟨hr, hrm, rfl⟩ := List.mem_map.mp hp
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hrm
    have := (T.weight_decomp m h w).2.1
    exact ⟨this.ne_zero, this⟩
  obtain ⟨hdvd, -, hsqf⟩ := GPolyLcm.lcmList_spec M _ (fun p hp ↦ (hs p hp).1)
  simp only [lcmCheck, Bool.and_eq_true]
  refine ⟨GPoly.squarefreeCheck_complete M (hsqf fun p hp ↦ (hs p hp).2),
    List.all_eq_true.mpr fun hr hrm ↦ ?_⟩
  refine (GPoly.isZero_iff M _).mpr (GPoly.divMod_exact M _ _ ?_
    (hdvd _ (List.mem_map.mpr ⟨hr, hrm, rfl⟩)))
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hrm
  exact (T.weight_decomp m h w).2.1.ne_zero

set_option maxHeartbeats 3200000 in
/-- **Completeness of the inductive step.** -/
theorem paramElem_succ_complete (m : ℕ) (h : T.Tr (m + 1))
    (hη : ∀ y : T.F m, y′ ≠ T.valN m (ηs m))
    (IHL : ∀ W', T.PLSound m (fun i hi ↦ h i (by omega)) W' (paramLim ηs m W') ∧
      T.PLComplete m (fun i hi ↦ h i (by omega)) W' (paramLim ηs m W'))
    (IHE : ∀ W', T.PEComplete m (fun i hi ↦ h i (by omega)) W' (paramElem ηs m W'))
    (W : List (Code (m + 2))) : T.PEComplete (m + 1) h W (paramElem ηs (m + 1) W) := by
  classical
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap Kc E).injective
  set hm : T.Tr m := fun i hi ↦ h i (by omega) with hhm
  set M := T.MP m hm with hM
  set M' := T.MP (m + 1) h with hM'
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  have hinj := T.phi_injective htr
  have hspec := T.limSpec_of m hm IHL
  have hconstK : ∀ y : T.F m, y′ = 0 → ∃ κ : Kc, y = algebraMap Kc (T.F m) κ := fun y hy ↦
    T.const_F y hy
  have hη' : ∀ y : T.F m, y′ ≠ M.sem (ηs m) := by rw [hM, T.sem_MP_F]; exact hη
  intro c hc hL
  have hchk := T.lcmCheck_true m h hm W
  rw [paramElem_succ_eq, if_pos hchk]
  obtain ⟨hsq, hdat⟩ := T.lcm_data m h hm W hchk
  set n := W.length with hn
  set Sv := GPoly.toPoly M (lcmS (ηs := ηs) m W) with hSv
  set ac : ℕ → T.F m := fun i ↦ algebraMap Kc (T.F m) (c.getD i 0) with hac
  have hac' : ∀ i, (ac i)′ = 0 := fun i ↦ T.deriv_algebraMap_Kc _
  set pv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly M (pPart (ηs := ηs) m (W.getD i (zc ηs (m + 1))))
    with hpv
  set Nv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly M ((numL (ηs := ηs) m W).getD i []) with hNv
  set Rv : ℕ → (T.F m)[X] := fun i ↦ GPoly.toPoly M (GPoly.residuePoly (opsQ ηs m) [ηs m]
    ((numL (ηs := ηs) m W).getD i []) (lcmS (ηs := ηs) m W)) with hRv
  set Tv : ℕ → (T.F m)[X] := fun i ↦
    GPoly.toPoly M (ttCode (ηs := ηs) m W ((numL (ηs := ηs) m W).getD i [])) with hTv
  set A := ∑ i ∈ Finset.range n, C (ac i) * pv i with hA
  set Nc := ∑ i ∈ Finset.range n, C (ac i) * Nv i with hNc
  set Rc := ∑ i ∈ Finset.range n, C (ac i) * Rv i with hRc
  set G : T.F (m + 1) := ∑ i ∈ Finset.range n, algebraMap Kc (T.F (m + 1)) (c.getD i 0) *
    M'.sem (gCode (ηs := ηs) m (W.getD i (zc ηs (m + 1)))) with hG
  have hφS : T.phi m Sv ≠ 0 := (map_ne_zero_iff _ hinj).mpr hsq.ne_zero
  -- the value
  have hsum : T.sumK (m + 1) h c W = G′ + T.phi m A + T.phi m Nc / T.phi m Sv := by
    rw [hG, T.deriv_sum_Kc, hA, hNc, map_sum, map_sum, Finset.sum_div, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, sumK]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [(hdat i (Finset.mem_range.mp hi)).1, map_mul, map_mul, T.algebraMap_succ]
    simp only [hac, hM, hM', hpv, hNv]
    ring
  obtain ⟨ι, s, cc, u, v, hdata, hv, heq⟩ := hL
  set t := T.ts m with ht
  set η := T.valN m (ηs m) with hηdef
  have hw : t′ = aeval t (C η) := by rw [aeval_C]; exact T.ht m
  have hst : aeval t Sv ≠ 0 := by
    rw [ht, ← T.coe_phi]
    exact fun h0 ↦ hφS (Subtype.ext h0)
  have hval : ((T.sumK (m + 1) h c W : T.F (m + 1)) : E) =
      (G : E)′ + aeval t A + aeval t Nc / aeval t Sv := by
    rw [hsum, IntermediateField.coe_add, IntermediateField.coe_add, IntermediateField.coe_div,
      coe_deriv, T.coe_phi, T.coe_phi, T.coe_phi]
  -- the constants as elements of `F m`
  set c' : ι → T.F m := fun i ↦ if h : (cc i)′ = 0 then ⟨cc i, T.const_mem m _ h⟩ else 0 with hc'
  have hc'E : ∀ i ∈ s, ((c' i : T.F m) : E) = cc i := fun i hi ↦ by
    simp only [hc']
    rw [dif_pos (hdata i hi).1]
  have hc'd : ∀ i ∈ s, (c' i)′ = 0 := fun i hi ↦
    Subtype.ext (by rw [coe_deriv, hc'E i hi, (hdata i hi).1]; rfl)
  have hconst : ∀ z ∈ (T.F m)⟮t⟯, z′ = 0 → z ∈ Set.range (algebraMap (T.F m) E) :=
    fun z _ hz0 ↦ by
      obtain ⟨κ, rfl⟩ := T.hCall z hz0
      exact ⟨algebraMap Kc (T.F m) κ, rfl⟩
  have hvg : v - (G : E) ∈ (T.F m)⟮t⟯ := (T.mem_F_succ).mp (sub_mem hv G.2)
  have hsumc : ∑ i ∈ s, cc i * logDeriv (u i) =
      ∑ i ∈ s, algebraMap (T.F m) E (c' i) * logDeriv (u i) :=
    Finset.sum_congr rfl fun i hi ↦ by rw [← hc'E i hi]; rfl
  have hbv : aeval t (A * Sv + Nc) / aeval t Sv =
      ∑ i ∈ s, algebraMap (T.F m) E (c' i) * logDeriv (u i) + (v - (G : E))′ := by
    rw [← hsumc, map_sub, ← add_sub_assoc, ← heq, hval, map_add, map_mul]
    field_simp
    ring
  -- the residue condition
  have hr : Sv ∣ Rc * (mapCoeffs Sv + C η * derivative Sv) - (A * Sv + Nc) := by
    have e : Rc * (mapCoeffs Sv + C η * derivative Sv) - (A * Sv + Nc) =
        ∑ i ∈ Finset.range n, C (ac i) * (Rv i * (mapCoeffs Sv + C η * derivative Sv) - Nv i) -
          A * Sv := by
      have e2 : ∑ i ∈ Finset.range n,
          C (ac i) * (Rv i * (mapCoeffs Sv + C η * derivative Sv) - Nv i) =
          Rc * (mapCoeffs Sv + C η * derivative Sv) - Nc := by
        rw [hRc, hNc, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [e2]
      ring
    rw [e]
    refine dvd_sub (Finset.dvd_sum fun i _ ↦ dvd_mul_of_dvd_right ?_ _) (dvd_mul_left _ _)
    exact (T.res_data m h hm W hsq ((numL (ηs := ηs) m W).getD i [])).1
  have hT : Sv ∣ residueTest Rc Sv :=
    residueTest_step_primitive (F := T.F m) t htr η (T.ht m) hconst s c' u
      (fun i hi ↦ ⟨(T.mem_F_succ).mp (hdata i hi).2.1, (hdata i hi).2.2⟩) hc'd (v - (G : E))
      hvg _ _ _ hsq hr hbv
  have hT0 : ∑ i ∈ Finset.range n, C (ac i) * Tv i = 0 := by
    refine eq_zero_of_dvd_of_degree_lt ?_
      (degree_sum_C_mul_lt n _ _ Sv hsq.ne_zero fun i _ ↦ (T.res_data m h hm W hsq _).2.2)
    have e : ∑ i ∈ Finset.range n, C (ac i) * Tv i = residueTest Rc Sv -
        ∑ i ∈ Finset.range n, C (ac i) * (residueTest (Rv i) Sv - Tv i) := by
      rw [hRc, residueTest_sum n ac hac', ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [e]
    exact dvd_sub hT (Finset.dvd_sum fun i _ ↦
      dvd_mul_of_dvd_right (T.res_data m h hm W hsq _).2.1 _)
  -- the constant system at level `m + 1`
  set U := consys ηs (m + 1) (resCodes (ηs := ηs) m W) with hU
  have h0 : (List.zipWith (fun c v ↦ algebraMap Kc (T.F (m + 1)) c * M'.sem v)
      ((List.range (resCodes (ηs := ηs) m W).length).map fun i ↦ c.getD i 0)
      (resCodes (ηs := ηs) m W)).sum = 0 := by
    rw [zipWith_sum_range _ 0 (zc ηs (m + 1)) _ _ (by simp)]
    have e : ∀ i ∈ Finset.range ((List.range (resCodes (ηs := ηs) m W).length).map
        fun i ↦ c.getD i 0).length,
        algebraMap Kc (T.F (m + 1)) (((List.range (resCodes (ηs := ηs) m W).length).map
          fun i ↦ c.getD i 0).getD i 0) * M'.sem ((resCodes (ηs := ηs) m W).getD i (zc ηs (m + 1))) =
        T.phi m (C (ac i) * Tv i) := fun i hi ↦ by
      have hi' : i < n := by
        have := Finset.mem_range.mp hi
        rwa [List.length_map, List.length_range, length_resCodes] at this
      rw [getD_range_map (fun j ↦ c.getD j 0) 0 (by rw [length_resCodes]; exact hi'),
        getD_resCodes m W hi', map_mul, T.algebraMap_succ]
      congr 1
      refine (T.sem_MP_succ m h _).trans ?_
      simp [(T.MP m hm).sem_one, hTv, hM]
    rw [Finset.sum_congr rfl e, List.length_map, List.length_range, length_resCodes, ← map_sum,
      hT0, map_zero]
  obtain ⟨β, hβl, hβ⟩ := T.consys_complete (m + 1) h (resCodes (ηs := ηs) m W) _ (by simp) h0
  have hβc : ∀ i < n, c.getD i 0 = ∑ u ∈ Finset.range U.length,
      β.getD u 0 * algebraMap ℚ Kc ((U.getD u []).getD i 0) := fun i hi ↦ by
    have := hβ i
    rw [getD_range_map (fun j ↦ c.getD j 0) 0 (by rw [length_resCodes]; exact hi),
      zipWith_sum_range _ 0 [] _ _ hβl, hβl] at this
    exact this
  -- the polynomial problem
  set βt := (List.range U.length).map fun u ↦ β.getD u 0 with hβt
  have hβtD : ∀ u < U.length, βt.getD u 0 = β.getD u 0 := fun u hu ↦ getD_range_map _ _ hu
  have hlPu : (PuE (ηs := ηs) m W).length = U.length := by simp [PuE, E1, hU]
  have hPoly : A = polySumC (algebraMap Kc (T.F m)) M βt (PuE (ηs := ηs) m W) := by
    rw [polySumC, hA]
    have e : ∀ u ∈ Finset.range (PuE (ηs := ηs) m W).length,
        C (algebraMap Kc (T.F m) (βt.getD u 0)) * GPoly.toPoly M ((PuE (ηs := ηs) m W).getD u []) =
        ∑ i ∈ Finset.range n,
          C (algebraMap Kc (T.F m) (β.getD u 0 * algebraMap ℚ Kc ((U.getD u []).getD i 0))) *
            pv i := fun u hu ↦ by
      have hu' : u < U.length := by rw [← hlPu]; exact Finset.mem_range.mp hu
      rw [hβtD u hu', PuE, getD_map' _ (E1 (ηs := ηs) m W) [] []
        (by simpa [E1, hU] using hu'), T.toPoly_Pu m hm W, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [E1, ← hU, getD_map' _ U [] [] hu', getD_vecOf, if_pos (Finset.mem_range.mp hi), map_mul,
        T.algebraMap_ratCast, C_mul, mul_assoc]
    rw [Finset.sum_congr rfl e, Finset.sum_comm, hlPu]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [← Finset.sum_mul, ← map_sum, ← map_sum, ← hβc i (Finset.mem_range.mp hi)]
  -- the fraction field `F m (tₘ)` and the polynomial part of the Liouville form
  let _ := algebraAdjoinSimple (F := T.F m) t
  let _ : Differential (T.F m)[X] := polynomialOfDeriv (C η)
  let _ : Differential (T.F m)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮t⟯ := isFractionRing_adjoin_simple _ htr
  have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮t⟯ := differentialAlgebra_adjoin_simple _ _ hw
  have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ P : (T.F m)⟮t⟯) : E) = aeval t P :=
    algebraMap_adjoinSimple _
  have hcoeLog : ∀ y : (T.F m)⟮t⟯, ((logDeriv y : (T.F m)⟮t⟯) : E) = logDeriv (y : E) := by
    intro y
    unfold logDeriv
    rw [IntermediateField.coe_div]
    rfl
  set u'' : ι → (T.F m)⟮t⟯ := fun i ↦ if h : u i ∈ (T.F m)⟮t⟯ then ⟨u i, h⟩ else 1 with hu''d
  have hu'' : ∀ i ∈ s, ((u'' i : (T.F m)⟮t⟯) : E) = u i := fun i hi ↦ by
    simp only [hu''d]
    rw [dif_pos ((T.mem_F_succ).mp (hdata i hi).2.1)]
  have hdegN : Nc.degree < Sv.degree :=
    degree_sum_C_mul_lt n _ _ Sv hsq.ne_zero fun i hi ↦ (hdat i hi).2
  obtain ⟨e, Pv, he, hPv⟩ := poly_part_liouville (K := (T.F m)⟮t⟯) (fun _ ↦ rfl) s c' u''
    (fun i hi h0 ↦ (hdata i hi).2.2 (by rw [← hu'' i hi, h0]; rfl)) ⟨v - (G : E), hvg⟩
    A _ ⟨_, _, hsq.ne_zero, hdegN, rfl⟩ (Subtype.ext (by
      rw [IntermediateField.coe_add, IntermediateField.coe_div, hcoe, hcoe, hcoe,
        IntermediateField.coe_add, AddSubmonoidClass.coe_finset_sum]
      have h1 : aeval t A + aeval t Nc / aeval t Sv = aeval t (A * Sv + Nc) / aeval t Sv := by
        rw [map_add, map_mul]
        field_simp
      rw [h1, hbv]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [IntermediateField.coe_mul, hcoe, aeval_C, hcoeLog, hu'' i hi]))
  set SL := ∑ i ∈ s, c' i * logDeriv (e i) with hSL
  have hQ : polySumC (algebraMap Kc (T.F m)) M βt (PuE (ηs := ηs) m W) =
      Dη M (ηs m) Pv + C SL := by
    rw [← hPoly, Dη, T.sem_MP_F, ← hηdef]
    change _ = implicitDeriv (C η) Pv + C SL
    rw [hPv]
    ring
  have hLSL : LiouvilleIn (T.F m) ((SL : T.F m) : E) := by
    refine ⟨ι, s, cc, fun i ↦ (e i : E), 0, fun i hi ↦ ⟨(hdata i hi).1, (e i).2,
      fun h0 ↦ he i hi (Subtype.ext h0)⟩, zero_mem _, ?_⟩
    rw [map_zero, add_zero, hSL, AddSubmonoidClass.coe_finset_sum]
    exact Finset.sum_congr rfl fun i hi ↦ by
      rw [IntermediateField.coe_mul, hc'E i hi, T.coe_logDeriv_F]
  obtain ⟨γ, hγ⟩ := polyElem_complete (algebraMap Kc (T.F m)) (ηs m) (paramLim ηs m)
    (paramElem ηs m) (T.sem_cstN m hm) hspec hconstK (fun q ↦ T.algebraMap_ratCast q) hη'
    (fun b ↦ LiouvilleIn (T.F m) ((b : T.F m) : E))
    (fun y b hb ↦ by
      rw [IntermediateField.coe_add, coe_deriv]
      exact liouvilleIn_deriv_add _ _ y.2 _ hb)
    (fun ws c hc hL ↦ IHE ws c hc hL) (PuE (ηs := ηs) m W) βt
    (fun i hi ↦ List.getD_eq_default _ _ (by simp [hβt]; omega)) Pv SL hQ hLSL
  -- assemble
  set pe := polyElem (opsQ ηs m) (cstN m) (ηs m) (paramLim ηs m) (paramElem ηs m)
    (PuE (ηs := ηs) m W) with hpe
  refine ⟨γ, fun i ↦ ?_⟩
  rw [List.length_map]
  have e : ∀ k ∈ Finset.range pe.length, γ.getD k 0 * algebraMap ℚ Kc
      (((pe.map fun δ ↦ vcomb n δ (E1 (ηs := ηs) m W)).getD k []).getD i 0) =
      γ.getD k 0 * algebraMap ℚ Kc ((vcomb n (pe.getD k []) (E1 (ηs := ηs) m W)).getD i 0) :=
    fun k hk ↦ by rw [getD_map' _ _ [] [] (Finset.mem_range.mp hk)]
  rw [Finset.sum_congr rfl e]
  by_cases hi : i < n
  · have := recombine n U.length pe.length
      (fun u i ↦ (U.getD u []).getD i 0) (fun j u ↦ (pe.getD j []).getD u 0)
      (fun i ↦ c.getD i 0) (fun u ↦ β.getD u 0) (fun j ↦ γ.getD j 0) hβc
      (fun u hu ↦ by rw [← hβtD u hu, hγ u]) i hi
    rw [this]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [getD_vcomb, if_pos hi, length_E1, ← hU]
    refine congrArg (fun x ↦ γ.getD k 0 * algebraMap ℚ Kc x) (Finset.sum_congr rfl fun u hu ↦ ?_)
    show (pe.getD k []).getD u 0 * (U.getD u []).getD i 0 =
      (pe.getD k []).getD u 0 * ((E1 (ηs := ηs) m W).getD u []).getD i 0
    rw [E1, ← hU, getD_map' _ U [] [] (Finset.mem_range.mp hu), getD_vecOf, if_pos hi]
  · rw [hc i (by omega)]
    symm
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [getD_vcomb, if_neg hi, map_zero, mul_zero]

/-- **Parametric elementary integration at every level**: sound and complete, given that no
`ηᵢ` (`i < m`) is a derivative in `F i`. -/
theorem paramElem_spec : ∀ (m : ℕ) (h : T.Tr m), (∀ i < m, ∀ y : T.F i, y′ ≠ T.valN i (ηs i)) →
    ∀ W : List (Code (m + 1)),
      T.PESound m h W (paramElem ηs m W) ∧ T.PEComplete m h W (paramElem ηs m W)
  | 0, h, _, W => T.paramElem_zero h W
  | m + 1, h, hη, W =>
    have IHL := fun W' ↦ T.paramLim_spec m (fun i hi ↦ h i (by omega))
      (fun i hi ↦ hη i (by omega)) W'
    have IHE := fun W' ↦ paramElem_spec m (fun i hi ↦ h i (by omega))
      (fun i hi ↦ hη i (by omega)) W'
    ⟨T.paramElem_succ_sound m h IHL (fun W' ↦ (IHE W').1) W,
      T.paramElem_succ_complete m h (hη m (Nat.lt_succ_self m)) IHL (fun W' ↦ (IHE W').2) W⟩

end NestTower

end Tower.NestP
