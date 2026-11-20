import RischTragerBronstein.Computable.NestMRdeExp

/-!
# Completeness of the Risch equation over an exponential level

The degree bound: `deg Y` is bounded by the case analysis of `prdeExp` (`A` dominates, `B`
dominates, or balanced), the balanced case through values at infinity (`deg h ≤ 0` at infinity,
`lc B / lc A = (h(∞) - deg Q · a)′`) and the logarithmic-derivative bound of the structure theorem.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestM

open Tower.PrimN Tower.NestP CPoly

section GenericDeg

variable {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

lemma degG_eq (p : GPoly α) : degG O p = (GPoly.toPoly M p).natDegree := by
  unfold degG
  by_cases hp : GPoly.toPoly M p = 0
  · rw [(GPoly.trim_eq_nil_iff M p).mpr hp, hp]; simp
  · rw [GPoly.length_trim M (fun h0 ↦ hp ((GPoly.trim_eq_nil_iff M p).mp h0))]; simp

lemma sem_leadG (p : GPoly α) (hp : GPoly.toPoly M p ≠ 0) :
    M.sem (leadG O p) = (GPoly.toPoly M p).leadingCoeff := by
  rw [leadG, GPoly.leadingCoeff_toPoly M hp]

lemma le_foldr_max : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0
  | [], _, hx => by simp at hx
  | a :: l, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact (le_foldr_max l x hx).trans (le_max_right _ _)

lemma natDegree_le_R (Cs : List (GPoly α)) (i : ℕ) (hi : i < Cs.length) :
    (GPoly.toPoly M (Cs.getD i [])).natDegree ≤ (Cs.map (degG O)).foldr max 0 := by
  rw [← degG_eq M]
  refine le_foldr_max _ _ (List.mem_map.mpr ⟨_, ?_, rfl⟩)
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _

lemma natOfQ_natCast (n : ℕ) : natOfQ (n : ℚ) = some n := by
  simp [natOfQ]

lemma sem_peHinf (hc : GPoly α × GPoly α) (hd0 : GPoly.toPoly M hc.2 ≠ 0)
    (hle : (GPoly.toPoly M hc.1).natDegree ≤ (GPoly.toPoly M hc.2).natDegree) :
    M.sem (peHinf O hc) = (GPoly.toPoly M hc.1).coeff (GPoly.toPoly M hc.2).natDegree /
      (GPoly.toPoly M hc.2).leadingCoeff := by
  unfold peHinf
  rw [degG_eq M, degG_eq M]
  split_ifs with hcond
  · obtain ⟨hdeq, hz⟩ := hcond
    have hn0 : GPoly.toPoly M hc.1 ≠ 0 := fun h0 ↦ by
      rw [(GPoly.isZero_iff M _).mpr h0] at hz; exact Bool.noConfusion hz
    rw [M.sem_mul, M.sem_inv, sem_leadG M _ hn0, sem_leadG M _ hd0, ← hdeq, div_eq_mul_inv]
    rfl
  · rw [M.sem_zero]
    by_cases hn0 : GPoly.toPoly M hc.1 = 0
    · rw [hn0]; simp
    · have hz : GPoly.isZero O hc.1 = false := by
        cases hb : GPoly.isZero O hc.1
        · rfl
        · exact absurd ((GPoly.isZero_iff M _).mp hb) hn0
      have hlt : (GPoly.toPoly M hc.1).natDegree < (GPoly.toPoly M hc.2).natDegree :=
        lt_of_le_of_ne hle fun heq ↦ hcond ⟨heq, hz⟩
      rw [coeff_eq_zero_of_natDegree_lt hlt, zero_div]

lemma peNb_ge (pl : Option ℚ) (A B : GPoly α) (R dDk N : ℕ) (h : peNb O pl A B R dDk = some N) :
    R ≤ N + (if (!GPoly.isZero O B && decide (degG O A < degG O B)) = true then degG O B
      else degG O A) := by
  unfold peNb at h
  simp only at h
  by_cases hz : GPoly.isZero O B = true
  · rw [if_pos hz] at h
    cases h
    simp [hz]
    omega
  · rw [if_neg hz] at h
    have hz' : GPoly.isZero O B = false := by simpa using hz
    by_cases hlt : degG O A < degG O B
    · rw [if_pos hlt] at h
      split_ifs at h with hle
      cases h
      simp [hz', hlt]
      omega
    · rw [if_neg hlt] at h
      simp only [hz', hlt, Bool.not_false, decide_false, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte]
      split_ifs at h with hlt2
      · cases h; omega
      · split at h <;> cases h <;> omega

end GenericDeg

/-! ### The balanced case, generically -/

section BalGeneric

variable {F K : Type*} [Field F] [CharZero F] [Differential F] [Differential F[X]]
variable [Field K] [Algebra F[X] K] [IsFractionRing F[X] K] [Differential K]
variable [DifferentialAlgebra F[X] K]

local notation "φ" => algebraMap F[X] K

variable {b : F} (hDe : ∀ P : F[X], P′ = implicitDeriv (C b * X) P)
  (hhom : ∀ r : ℕ, r ≠ 0 → ∀ e : F, e ≠ 0 → e′ + r * b * e ≠ 0)

include hDe hhom in
/-- **The balanced case**: if `F₁ / F₂ = h′ - Q′ / Q` (`Q` monic) with `deg F₁ = deg F₂`, then
`h` has a value at infinity and `lc F₁ / lc F₂ = h(∞)′ - deg Q · b`. -/
lemma bal_core (hn hd Q F1 F2 : F[X]) (hd0 : hd ≠ 0) (hQ : Q.Monic) (hF2 : F2 ≠ 0)
    (hdeg : F1.natDegree = F2.natDegree)
    (hF : φ F1 / φ F2 = (φ hn / φ hd)′ - (φ Q)′ / φ Q) :
    hn.natDegree ≤ hd.natDegree ∧ F1.leadingCoeff / F2.leadingCoeff =
      (hn.coeff hd.natDegree / hd.leadingCoeff)′ - Q.natDegree * b := by
  have hlog := infVal_logDeriv (K := K) hDe Q hQ.ne_zero
  rw [hQ.leadingCoeff, Derivation.map_one_eq_zero, zero_div, add_zero] at hlog
  have hF' : InfVal (φ F1 / φ F2) (F1.leadingCoeff / F2.leadingCoeff) := by
    have := infVal_of (K := K) F1 F2 hF2 hdeg.le
    rwa [← hdeg] at this
  have hle : hn.natDegree ≤ hd.natDegree := by
    by_contra hlt
    push_neg at hlt
    have hn0 : hn ≠ 0 := by rintro rfl; simp at hlt
    have hr : hn.natDegree - hd.natDegree ≠ 0 := by omega
    have hpos : PosDeg F (φ hn / φ hd) (hn.natDegree - hd.natDegree) :=
      ⟨hn, hd, hd0, hn0, by omega, rfl⟩
    have h2 := posDeg_add hr (posDeg_deriv hDe hhom hr hpos) (infVal_neg hlog)
    rw [← sub_eq_add_neg, ← hF] at h2
    have := natDegree_lt_of_posDeg hr h2 hF2 rfl
    omega
  refine ⟨hle, ?_⟩
  have h1 := infVal_sub (infVal_deriv hDe (infVal_of (K := K) hn hd hd0 hle)) hlog
  rw [← hF] at h1
  exact infVal_unique hF' h1

end BalGeneric

namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {as : (m : ℕ) → Code (m + 1)}
variable (T : NestMTower Kc E (expK as))

section Bal

variable (m : ℕ) (h : T.Tr (m + 1))

lemma sem_peF (hc : GPoly (Code (m + 1)) × GPoly (Code (m + 1))) (Q : GPoly (Code (m + 1))) :
    T.σ1 m h (peF (opsM (expK as) m) (as m) hc Q).1 / T.σ1 m h (peF (opsM (expK as) m) (as m) hc Q).2 =
      ((T.M1 m h).sem hc)′ - (T.σ1 m h Q)′ / T.σ1 m h Q := by
  set O := opsM (expK as) m with hO
  set O' := O.monomial (peW O (as m)) with hO'
  have hadd : ∀ a b, (T.M1 m h).sem (O'.add a b) = (T.M1 m h).sem a + (T.M1 m h).sem b := (T.M1 m h).sem_add
  have hneg : ∀ a, (T.M1 m h).sem (O'.neg a) = -(T.M1 m h).sem a := (T.M1 m h).sem_neg
  have hmul : ∀ a b, (T.M1 m h).sem (O'.mul a b) = (T.M1 m h).sem a * (T.M1 m h).sem b := (T.M1 m h).sem_mul
  have hinv : ∀ a, (T.M1 m h).sem (O'.inv a) = ((T.M1 m h).sem a)⁻¹ := (T.M1 m h).sem_inv
  have hder : ∀ a, (T.M1 m h).sem (O'.deriv a) = ((T.M1 m h).sem a)′ := (T.M1 m h).sem_deriv
  have hQv : (T.M1 m h).sem (Q, [O.one]) = T.σ1 m h Q := by rw [T.sem1, T.σ1_one, div_one]
  rw [← T.sem1, peF, T.sem1_cleanG, hadd, hder, hneg, hmul, hder, hinv, hQv]
  ring

variable (hc2 : ∀ u ∈ consys (expK as) m ((opsM (expK as) m).deriv (as m) :: dExps as m),
  u.getD 0 0 = 0)

include hc2 in
lemma hhom_exp : ∀ r : ℕ, r ≠ 0 → ∀ e : T.F m, e ≠ 0 → e′ + r * T.bE m h * e ≠ 0 := by
  intro r hr e he
  have hm : T.Tr m := fun i hi ↦ h i (by omega)
  have hbE : T.bE m h = (T.valN m (as m))′ := by rw [bE, T.sem_MP_F]
  have := T.no_hom_exp_int m hm hc2 r (by exact_mod_cast hr) e he
  rw [hbE]
  exact_mod_cast this

include hc2 in
set_option maxHeartbeats 800000 in
/-- **The balanced case at an exponential level.** -/
theorem pe_bal (hcl : GPoly (Code (m + 1)) × GPoly (Code (m + 1)))
    (hhcl : GPoly.toPoly (T.Mm m h) hcl.2 ≠ 0) (Q : GPoly (Code (m + 1)))
    (hQ : (GPoly.toPoly (T.Mm m h) Q).Monic)
    (hdeg : (GPoly.toPoly (T.Mm m h) (peF (opsM (expK as) m) (as m) hcl Q).1).natDegree =
      (GPoly.toPoly (T.Mm m h) (peF (opsM (expK as) m) (as m) hcl Q).2).natDegree) :
    (GPoly.toPoly (T.Mm m h) hcl.1).natDegree ≤ (GPoly.toPoly (T.Mm m h) hcl.2).natDegree ∧
      (GPoly.toPoly (T.Mm m h) (peF (opsM (expK as) m) (as m) hcl Q).1).leadingCoeff /
        (GPoly.toPoly (T.Mm m h) (peF (opsM (expK as) m) (as m) hcl Q).2).leadingCoeff =
      ((GPoly.toPoly (T.Mm m h) hcl.1).coeff (GPoly.toPoly (T.Mm m h) hcl.2).natDegree /
        (GPoly.toPoly (T.Mm m h) hcl.2).leadingCoeff)′ -
        (GPoly.toPoly (T.Mm m h) Q).natDegree * T.bE m h := by
  classical
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  obtain ⟨F, hF⟩ : ∃ F, F = peF (opsM (expK as) m) (as m) hcl Q := ⟨_, rfl⟩
  have hsF := T.sem_peF m h hcl Q
  rw [← hF] at hsF hdeg ⊢
  have hF2 : GPoly.toPoly (T.Mm m h) F.2 ≠ 0 := by
    rw [hF]; unfold peF; intro h0
    exact T.σ1_cleanG_ne m h _ (by rw [σ1, h0, map_zero])
  -- the setting `K = F m (t)`
  set t := T.ts m with ht
  have hw := T.deriv_ts_aeval m
  let _ := algebraAdjoinSimple (F := T.F m) t
  let _ : Differential (T.F m)[X] := polynomialOfDeriv (T.wPoly m)
  let _ : Differential (T.F m)⟮t⟯ := differentialOfDerivClosed (derivClosed_adjoin_simple t _ hw)
  have hFR : IsFractionRing (T.F m)[X] (T.F m)⟮t⟯ := isFractionRing_adjoin_simple _ htr
  have hDA : DifferentialAlgebra (T.F m)[X] (T.F m)⟮t⟯ := differentialAlgebra_adjoin_simple _ _ hw
  have hcoe : ∀ P, ((algebraMap (T.F m)[X] (T.F m)⟮t⟯ P : (T.F m)⟮t⟯) : E) = aeval t P :=
    algebraMap_adjoinSimple _
  have hDe : ∀ P : (T.F m)[X], P′ = implicitDeriv (C (T.bE m h) * X) P := fun P ↦ by
    change implicitDeriv (T.wPoly m) P = _
    rw [T.wPoly_eq_bE m h]
  refine bal_core (K := (T.F m)⟮t⟯) hDe (T.hhom_exp m h hc2) _ _ _ _ _ hhcl hQ hF2 hdeg (Subtype.ext ?_)
  have key := congrArg (fun z : T.F (m + 1) ↦ (z : E)) hsF
  simp only [T.sem1, IntermediateField.coe_div, AddSubgroupClass.coe_sub, coe_deriv, T.coe_phi]
    at key
  have hdK : ∀ z : (T.F m)⟮t⟯, ((z′ : (T.F m)⟮t⟯) : E) = (z : E)′ := fun z ↦ rfl
  simp only [IntermediateField.coe_div, AddSubgroupClass.coe_sub, hdK, hcoe]
  exact key

include hc2 in
/-- **The balanced case**: `h` has a value at infinity and `(h(∞) - deg Q · a)′ = lc B / lc A`. -/
theorem pe_bal_lead (hcl : GPoly (Code (m + 1)) × GPoly (Code (m + 1)))
    (hhcl : GPoly.toPoly (T.Mm m h) hcl.2 ≠ 0) (Q : GPoly (Code (m + 1)))
    (hQ : (GPoly.toPoly (T.Mm m h) Q).Monic) (dDk : ℕ)
    (hdDk : (GPoly.toPoly (T.Mm m h) Q).natDegree = dDk)
    (Rs : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1))))
    (hP : GPoly.toPoly (T.Mm m h) (prodD (GPoly.mul (opsM (expK as) m)) [(opsM (expK as) m).one] Rs) ≠ 0)
    (hB0 : GPoly.toPoly (T.Mm m h) (peB (opsM (expK as) m) (peF (opsM (expK as) m) (as m) hcl Q) Rs) ≠ 0)
    (hdeg : (GPoly.toPoly (T.Mm m h) (peA (opsM (expK as) m) (peF (opsM (expK as) m) (as m) hcl Q) Rs)).natDegree =
      (GPoly.toPoly (T.Mm m h) (peB (opsM (expK as) m) (peF (opsM (expK as) m) (as m) hcl Q) Rs)).natDegree) :
    (GPoly.toPoly (T.Mm m h) hcl.1).natDegree ≤ (GPoly.toPoly (T.Mm m h) hcl.2).natDegree ∧
      ((T.Mm m h).sem ((opsM (expK as) m).add (peHinf (opsM (expK as) m) hcl)
        ((opsM (expK as) m).mul (cstN m (-(dDk : ℚ))) (as m))))′ =
      (GPoly.toPoly (T.Mm m h) (peB (opsM (expK as) m) (peF (opsM (expK as) m) (as m) hcl Q) Rs)).leadingCoeff /
        (GPoly.toPoly (T.Mm m h) (peA (opsM (expK as) m) (peF (opsM (expK as) m) (as m) hcl Q) Rs)).leadingCoeff := by
  obtain ⟨F, hF⟩ : ∃ F, F = peF (opsM (expK as) m) (as m) hcl Q := ⟨_, rfl⟩
  obtain ⟨P, hPd⟩ : ∃ P, P = prodD (GPoly.mul (opsM (expK as) m)) [(opsM (expK as) m).one] Rs :=
    ⟨_, rfl⟩
  rw [← hF] at hB0 hdeg ⊢
  rw [← hPd] at hP
  have hA : GPoly.toPoly (T.Mm m h) (peA (opsM (expK as) m) F Rs) =
      GPoly.toPoly (T.Mm m h) F.2 * GPoly.toPoly (T.Mm m h) P := by
    rw [peA, GPoly.toPoly_mul, hPd]
  have hB : GPoly.toPoly (T.Mm m h) (peB (opsM (expK as) m) F Rs) =
      GPoly.toPoly (T.Mm m h) F.1 * GPoly.toPoly (T.Mm m h) P := by
    rw [peB, GPoly.toPoly_mul, hPd]
  have hF2 : GPoly.toPoly (T.Mm m h) F.2 ≠ 0 := by
    rw [hF]; unfold peF; intro h0
    exact T.σ1_cleanG_ne m h _ (by rw [σ1, h0, map_zero])
  have hF1 : GPoly.toPoly (T.Mm m h) F.1 ≠ 0 := fun h0 ↦ hB0 (by rw [hB, h0, zero_mul])
  rw [hA, hB, natDegree_mul hF2 hP, natDegree_mul hF1 hP] at hdeg
  have hdeg' : (GPoly.toPoly (T.Mm m h) F.1).natDegree = (GPoly.toPoly (T.Mm m h) F.2).natDegree := by
    omega
  rw [hF] at hdeg'
  obtain ⟨hle, hlc⟩ := T.pe_bal m h hc2 hcl hhcl Q hQ hdeg'
  rw [← hF] at hlc
  refine ⟨hle, ?_⟩
  have hcst : ∀ q, (T.Mm m h).sem (cstN m q) = (q : T.F m) := T.sem_cstN m _
  rw [(T.Mm m h).sem_add, (T.Mm m h).sem_mul, hcst, sem_peHinf (T.Mm m h) hcl hhcl hle,
    Derivation.map_add, Derivation.leibniz, deriv_ratCastK, hA, hB, leadingCoeff_mul,
    leadingCoeff_mul, mul_div_mul_right _ _ (leadingCoeff_ne_zero.mpr hP), hlc, hdDk, bE]
  simp only [smul_eq_mul, mul_zero, add_zero]
  push_cast
  ring

include hc2 in
set_option maxHeartbeats 1600000 in
/-- **The degree bound** `peNb`: `deg Y ≤ N`, or `Y = 0` when there is no bound. -/
theorem pe_Nb (hcl : GPoly (Code (m + 1)) × GPoly (Code (m + 1)))
    (hhcl : GPoly.toPoly (T.Mm m h) hcl.2 ≠ 0) (Q : GPoly (Code (m + 1)))
    (hQ : (GPoly.toPoly (T.Mm m h) Q).Monic) (dDk : ℕ)
    (hdDk : (GPoly.toPoly (T.Mm m h) Q).natDegree = dDk)
    (Rs : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1))))
    (hP : GPoly.toPoly (T.Mm m h) (prodD (GPoly.mul (opsM (expK as) m)) [(opsM (expK as) m).one] Rs) ≠ 0)
    (Y r : (T.F m)[X]) (R : ℕ) (hr : r.natDegree ≤ R)
    (heq : GPoly.toPoly (T.Mm m h) (peA (opsM (expK as) m) (peF (opsM (expK as) m) (as m) hcl Q) Rs) *
        implicitDeriv (C (T.bE m h) * X) Y +
      GPoly.toPoly (T.Mm m h) (peB (opsM (expK as) m) (peF (opsM (expK as) m) (as m) hcl Q) Rs) * Y = r) :
    (∀ N, peNb (opsM (expK as) m) (pld (expK as) m (peHinf (opsM (expK as) m) hcl) (as m))
        (peA (opsM (expK as) m) (peF (opsM (expK as) m) (as m) hcl Q) Rs)
        (peB (opsM (expK as) m) (peF (opsM (expK as) m) (as m) hcl Q) Rs) R dDk = some N →
        Y.natDegree ≤ N) ∧
      (peNb (opsM (expK as) m) (pld (expK as) m (peHinf (opsM (expK as) m) hcl) (as m))
        (peA (opsM (expK as) m) (peF (opsM (expK as) m) (as m) hcl Q) Rs)
        (peB (opsM (expK as) m) (peF (opsM (expK as) m) (as m) hcl Q) Rs) R dDk = none → Y = 0) := by
  have hm : T.Tr m := fun i hi ↦ h i (by omega)
  have hbal := T.pe_bal_lead m h hc2 hcl hhcl Q hQ dDk hdDk Rs hP
  have hhom := T.hhom_exp m h hc2
  have hA0 : GPoly.toPoly (T.Mm m h) (peA (opsM (expK as) m) (peF (opsM (expK as) m) (as m) hcl Q) Rs)
      ≠ 0 := by
    rw [peA, GPoly.toPoly_mul]
    refine mul_ne_zero ?_ hP
    unfold peF; intro h0
    exact T.σ1_cleanG_ne m h _ (by rw [σ1, h0, map_zero])
  obtain ⟨A, hAd⟩ : ∃ A, A = peA (opsM (expK as) m) (peF (opsM (expK as) m) (as m) hcl Q) Rs :=
    ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = peB (opsM (expK as) m) (peF (opsM (expK as) m) (as m) hcl Q) Rs :=
    ⟨_, rfl⟩
  rw [← hAd, ← hBd] at heq hbal ⊢
  rw [← hAd] at hA0
  obtain ⟨pl, hpl⟩ : ∃ pl, pl = pld (expK as) m (peHinf (opsM (expK as) m) hcl) (as m) := ⟨_, rfl⟩
  rw [← hpl]
  unfold peNb
  simp only [degG_eq (T.Mm m h)]
  split_ifs with hBz hlt hle' hlt2
  · have hB0 : GPoly.toPoly (T.Mm m h) B = 0 := (GPoly.isZero_iff _ _).mp hBz
    have := natDegree_le_of_rdeExp_A (T.bE m h) _ _ Y r R hr hA0 (Or.inl hB0) hhom heq
    exact ⟨fun N hN ↦ by cases hN; exact this, fun h' ↦ by cases h'⟩
  · have hB0 : GPoly.toPoly (T.Mm m h) B ≠ 0 := fun h0 ↦ by rw [h0] at hlt; simp at hlt
    rcases natDegree_le_of_rdeExp_B (T.bE m h) _ _ Y r R hr hB0 hlt heq with h0 | h1
    · refine ⟨fun N hN ↦ ?_, fun h' ↦ by cases h'⟩
      rw [h0, natDegree_zero]; exact Nat.zero_le _
    · exact ⟨fun N hN ↦ by cases hN; omega, fun h' ↦ by cases h'⟩
  · have hB0 : GPoly.toPoly (T.Mm m h) B ≠ 0 := fun h0 ↦ by rw [h0] at hlt; simp at hlt
    refine ⟨fun N hN ↦ (by cases hN), fun _ ↦ ?_⟩
    rcases natDegree_le_of_rdeExp_B (T.bE m h) _ _ Y r R hr hB0 hlt heq with h0 | h1
    · exact h0
    · omega
  · have := natDegree_le_of_rdeExp_A (T.bE m h) _ _ Y r R hr hA0 (Or.inr hlt2) hhom heq
    exact ⟨fun N hN ↦ by cases hN; exact this, fun h' ↦ by cases h'⟩
  · have hdAB : (GPoly.toPoly (T.Mm m h) A).natDegree = (GPoly.toPoly (T.Mm m h) B).natDegree := by
      omega
    have hB0 : GPoly.toPoly (T.Mm m h) B ≠ 0 := fun h0 ↦ hBz ((GPoly.isZero_iff _ _).mpr h0)
    rcases natDegree_le_of_rdeExp_bal (T.bE m h) _ _ Y r R hr hdAB heq with hle | ⟨hY0, htop⟩
    · refine ⟨fun N hN ↦ ?_, fun hN ↦ ?_⟩
      · split at hN <;> (cases hN) <;> omega
      · split at hN <;> cases hN
    -- the top coefficient cancels: the logarithmic-derivative bound applies
    obtain ⟨-, hlead⟩ := hbal hB0 hdAB
    have hcst : ∀ q, (T.Mm m h).sem (cstN m q) = (q : T.F m) := T.sem_cstN m _
    rw [(T.Mm m h).sem_add, (T.Mm m h).sem_mul, hcst] at hlead
    set s := (T.Mm m h).sem (peHinf (opsM (expK as) m) hcl) with hs
    set α := (T.Mm m h).sem (as m) with hα
    set y := Y.leadingCoeff with hy
    set lA := (GPoly.toPoly (T.Mm m h) A).leadingCoeff with hlA
    set lB := (GPoly.toPoly (T.Mm m h) B).leadingCoeff with hlB
    have hlA0 : lA ≠ 0 := leadingCoeff_ne_zero.mpr hA0
    have hy0 : y ≠ 0 := leadingCoeff_ne_zero.mpr hY0
    have hbE : T.bE m h = α′ := rfl
    have hsd : s′ = lB / lA + (dDk : T.F m) * α′ := by
      rw [Derivation.map_add, Derivation.leibniz, deriv_ratCastK] at hlead
      simp only [smul_eq_mul, mul_zero, add_zero] at hlead
      push_cast at hlead
      linear_combination hlead
    set M : ℤ := (Y.natDegree : ℤ) - dDk with hM
    have hMd : ((M : T.F m))′ = 0 := by
      have := deriv_ratCastK (K := T.F m) (M : ℚ)
      simpa using this
    have key : (s + (M : T.F m) * α)′ = (y⁻¹)′ / y⁻¹ := by
      rw [Derivation.map_add, Derivation.leibniz, hMd, show y⁻¹ = 1 / y by ring,
        Derivation.leibniz_div, Derivation.map_one_eq_zero, hsd]
      simp only [smul_eq_mul, mul_zero, add_zero, zero_sub]
      rw [hbE] at htop
      field_simp
      rw [hM]
      push_cast
      linear_combination htop
    have hyE : (((y⁻¹ : T.F m)) : E) ≠ 0 := fun h0 ↦ inv_ne_zero hy0 (Subtype.ext h0)
    have hd : (evN Kc T.x T.ts m (peHinf (opsM (expK as) m) hcl) + (M : E) * T.aE m)′ =
        logDeriv ((y⁻¹ : T.F m) : E) := by
      have e1 : evN Kc T.x T.ts m (peHinf (opsM (expK as) m) hcl) = ((s : T.F m) : E) :=
        (T.sem_MP m _ _).symm
      have e2 : T.aE m = ((α : T.F m) : E) := (T.sem_MP m _ _).symm
      rw [e1, e2]
      unfold logDeriv
      have key' := congrArg (fun z : T.F m ↦ (z : E)) key
      simp only [coe_deriv, IntermediateField.coe_add, IntermediateField.coe_mul,
        IntermediateField.coe_div] at key'
      push_cast at key'
      exact key'
    have hpld := T.pld_spec m hm hc2 _ M _ (y⁻¹ : T.F m).2 hyE hd
    rw [← hpl] at hpld
    rw [hpld]
    simp only [Option.bind_some]
    rw [show ((M : ℚ) + (dDk : ℚ)) = ((Y.natDegree : ℕ) : ℚ) by rw [hM]; push_cast; ring,
      natOfQ_natCast]
    exact ⟨fun N hN ↦ by cases hN; exact le_max_right _ _, fun h' ↦ by cases h'⟩

end Bal

section Final

variable (m : ℕ) (h : T.Tr (m + 1))

set_option maxHeartbeats 1600000 in
/-- **The final constant system is complete**: a solution `y = Yv / Q` whose polynomial `Yv` is a
constant combination of the basis `Bs` with vanishing residual is a combination of the output. -/
theorem peOut_complete (A B : GPoly (Code (m + 1))) (Cs : List (GPoly (Code (m + 1)))) (n : ℕ)
    (Q : GPoly (Code (m + 1))) (hQ0 : T.σ1 m h Q ≠ 0)
    (Bs : List (List ℚ × GPoly (Code (m + 1)))) (c : List Kc)
    (hcn : ∀ i, n ≤ i → c.getD i 0 = 0) (β : List Kc)
    (hβc : ∀ i, c.getD i 0 = ∑ k ∈ Finset.range Bs.length,
      β.getD k 0 * algebraMap ℚ Kc ((Bs.getD k ([], [])).1.getD i 0))
    (Yv : (T.F m)[X])
    (hYv : Yv = ∑ l ∈ Finset.range Bs.length, C (algebraMap Kc (T.F m) (β.getD l 0)) *
      GPoly.toPoly (T.Mm m h) (Bs.getD l ([], [])).2)
    (hres : ∑ l ∈ Finset.range Bs.length, C (algebraMap Kc (T.F m) (β.getD l 0)) *
        resQ (T.Mm m h) (T.bE m h) A B Cs (Bs.getD l ([], [])).1
          (GPoly.toPoly (T.Mm m h) (Bs.getD l ([], [])).2) = 0)
    (y : T.F (m + 1)) (hy : y * T.σ1 m h Q = T.phi m Yv) :
    ∃ γ : List Kc,
      (∀ i, c.getD i 0 = ∑ k ∈ Finset.range
          (peOut (expK as) m (peW (opsM (expK as) m) (as m)) A B Cs n Q Bs).length,
        γ.getD k 0 * algebraMap ℚ Kc (((peOut (expK as) m (peW (opsM (expK as) m) (as m)) A B Cs n Q
          Bs).getD k ([], ((opsM (expK as) m).monomial (peW (opsM (expK as) m) (as m))).zero)).1.getD
            i 0)) ∧
      y = ∑ k ∈ Finset.range (peOut (expK as) m (peW (opsM (expK as) m) (as m)) A B Cs n Q Bs).length,
        algebraMap Kc (T.F (m + 1)) (γ.getD k 0) *
          (T.M1 m h).sem ((peOut (expK as) m (peW (opsM (expK as) m) (as m)) A B Cs n Q Bs).getD k
            ([], ((opsM (expK as) m).monomial (peW (opsM (expK as) m) (as m))).zero)).2 := by
  classical
  set O := opsM (expK as) m with hO
  have hcst : ∀ q, (T.Mm m h).sem (cstN m q) = (q : T.F m) := T.sem_cstN m _
  have hw := T.toPoly_peW m h
  have hqK : ∀ q : ℚ, algebraMap Kc (T.F (m + 1)) (algebraMap ℚ Kc q) = (q : T.F (m + 1)) :=
    fun q ↦ by rw [← map_ratCast (algebraMap Kc (T.F (m + 1))), ← map_ratCast (algebraMap ℚ Kc)]; rfl
  have hphiq : ∀ q : ℚ, T.phi m (C (q : T.F m)) = (q : T.F (m + 1)) := fun q ↦ by
    rw [T.phi_C]; exact map_ratCast _ q
  obtain ⟨vs, hvs⟩ : ∃ vs : List (Code (m + 2)), vs = Bs.map fun b ↦
      ((residE O (cstN m) (peW O (as m)) A B Cs b, [O.one]) : Code (m + 2)) := ⟨_, rfl⟩
  have hlv : vs.length = Bs.length := by rw [hvs]; exact List.length_map _
  obtain ⟨U, hU⟩ : ∃ U, U = consys (expK as) (m + 1) vs := ⟨_, rfl⟩
  set f : CPoly ℚ → List ℚ × Code (m + 2) := fun u ↦
    (vcomb n ((List.range Bs.length).map (u.getD · 0)) (Bs.map Prod.fst),
      ((lcombGP O (cstN m) ((List.range Bs.length).map (u.getD · 0)) (Bs.map Prod.snd), Q) :
        Code (m + 2))) with hf
  have hout : peOut (expK as) m (peW O (as m)) A B Cs n Q Bs = U.map f := by
    rw [hU, hvs]; rfl
  rw [hout]
  -- the relation between the residuals
  set βt := (List.range Bs.length).map (β.getD · 0) with hβt
  have hsemv : ∀ l < Bs.length, (T.MP (m + 1) h).sem (vs.getD l (opsM (expK as) (m + 1)).zero) =
      T.phi m (resQ (T.Mm m h) (T.bE m h) A B Cs (Bs.getD l ([], [])).1
        (GPoly.toPoly (T.Mm m h) (Bs.getD l ([], [])).2)) := fun l hl ↦ by
    have hvl : vs.getD l (opsM (expK as) (m + 1)).zero =
        ((residE O (cstN m) (peW O (as m)) A B Cs (Bs.getD l ([], [])), [O.one]) : Code (m + 2)) := by
      rw [hvs]; exact NestTower.getD_map' _ Bs ([], []) _ hl
    rw [hvl]
    change T.σ1 m h _ / T.σ1 m h [O.one] = _
    rw [T.σ1_one, div_one, σ1, toPoly_residE (T.bE m h) A B Cs hcst (peW O (as m)) hw]
  have h0 : (List.zipWith (fun c v ↦ algebraMap Kc (T.F (m + 1)) c * (T.MP (m + 1) h).sem v)
      βt vs).sum = 0 := by
    rw [NestTower.zipWith_sum_range _ 0 (opsM (expK as) (m + 1)).zero _ _ (by simp [hβt, hlv])]
    have e : ∀ l ∈ Finset.range βt.length, algebraMap Kc (T.F (m + 1)) (βt.getD l 0) *
        (T.MP (m + 1) h).sem (vs.getD l (opsM (expK as) (m + 1)).zero) =
        T.phi m (C (algebraMap Kc (T.F m) (β.getD l 0)) *
          resQ (T.Mm m h) (T.bE m h) A B Cs (Bs.getD l ([], [])).1
            (GPoly.toPoly (T.Mm m h) (Bs.getD l ([], [])).2)) := fun l hl ↦ by
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
  have hgetD : ∀ k < U.length, (U.map f).getD k ([], (O.monomial (peW O (as m))).zero) =
      f (U.getD k []) := fun k hk ↦ NestTower.getD_map' _ _ [] _ hk
  refine ⟨γ, fun i ↦ ?_, ?_⟩
  · -- the coefficients
    rw [hlen]
    have e : ∀ k ∈ Finset.range U.length, γ.getD k 0 * algebraMap ℚ Kc
        (((U.map f).getD k ([], (O.monomial (peW O (as m))).zero)).1.getD i 0) =
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
  · -- the solution
    set g : ℕ → T.F (m + 1) := fun l ↦ T.phi m (GPoly.toPoly (T.Mm m h) (Bs.getD l ([], [])).2) /
      T.σ1 m h Q with hg
    have hyv : y = ∑ l ∈ Finset.range Bs.length, algebraMap Kc (T.F (m + 1)) (β.getD l 0) * g l := by
      rw [eq_div_iff hQ0 |>.mpr hy, hYv, map_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [map_mul, ← T.algebraMap_succ, hg, mul_div_assoc]
    have hsk : ∀ k < U.length, (T.M1 m h).sem (f (U.getD k [])).2 =
        ∑ l ∈ Finset.range Bs.length, (((U.getD k []).getD l 0 : ℚ) : T.F (m + 1)) * g l :=
      fun k hk ↦ by
      rw [hf]
      simp only
      rw [T.sem1, σ1, toPoly_lcombGP (T.Mm m h) (cstN m) hcst,
        zipWith_sum_getD (fun (q : ℚ) (p : GPoly (Code (m + 1))) ↦
          C (q : T.F m) * GPoly.toPoly (T.Mm m h) p) 0 [] (by simp), List.length_map, map_sum,
        Finset.sum_div]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      have hl' := Finset.mem_range.mp hl
      rw [NestTower.getD_range_map _ _ hl', NestTower.getD_map' _ _ ([], []) [] hl', map_mul,
        hphiq, hg, mul_div_assoc]
    rw [hlen, hyv]
    have e : ∀ k ∈ Finset.range U.length, algebraMap Kc (T.F (m + 1)) (γ.getD k 0) *
        (T.M1 m h).sem ((U.map f).getD k ([], (O.monomial (peW O (as m))).zero)).2 =
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

section Main

variable (m : ℕ) (h : T.Tr (m + 1))

set_option maxHeartbeats 3200000 in
/-- **Completeness of `prdeExp`**, given a complete solver one level down. -/
theorem prdeExp_complete
    (hc2 : ∀ u ∈ consys (expK as) m ((opsM (expK as) m).deriv (as m) :: dExps as m),
      u.getD 0 0 = 0)
    (lower : Code (m + 1) → List (Code (m + 1)) → List (List ℚ × Code (m + 1)))
    (hlow : ∀ f : Code (m + 1),
      RdeSpecK (algebraMap Kc (T.F m)) (T.Mm m h) ((T.Mm m h).sem f)′ (lower f))
    (hcode : GPoly (Code (m + 1)) × GPoly (Code (m + 1)))
    (W : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1)))) (c : List Kc)
    (hcW : ∀ i, W.length ≤ i → c.getD i 0 = 0) (y : T.F (m + 1))
    (hy : y′ + ((T.M1 m h).sem hcode)′ * y = sC (algebraMap Kc (T.F (m + 1))) (T.M1 m h) c W) :
    ∃ γ : List Kc,
      (∀ i, c.getD i 0 = ∑ k ∈ Finset.range (prdeExp (expK as) m (as m) lower hcode W).length,
        γ.getD k 0 * algebraMap ℚ Kc (((prdeExp (expK as) m (as m) lower hcode W).getD k
          ([], ((opsM (expK as) m).monomial (peW (opsM (expK as) m) (as m))).zero)).1.getD i 0)) ∧
      y = ∑ k ∈ Finset.range (prdeExp (expK as) m (as m) lower hcode W).length,
        algebraMap Kc (T.F (m + 1)) (γ.getD k 0) *
          (T.M1 m h).sem ((prdeExp (expK as) m (as m) lower hcode W).getD k
            ([], ((opsM (expK as) m).monomial (peW (opsM (expK as) m) (as m))).zero)).2 := by
  classical
  set O := opsM (expK as) m with hO
  have hm : T.Tr m := fun i hi ↦ h i (by omega)
  have hcst : ∀ q, (T.Mm m h).sem (cstN m q) = (q : T.F m) := T.sem_cstN m _
  have hw := T.toPoly_peW m h
  -- the pieces of the algorithm
  obtain ⟨Wc, hWc⟩ : ∃ Wc, Wc = W.map (cleanG O) := ⟨_, rfl⟩
  obtain ⟨hc, hhc⟩ : ∃ hc, hc = cleanG O hcode := ⟨_, rfl⟩
  obtain ⟨eps, heps⟩ : ∃ eps, eps = peEps O Wc := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = peD O (as m) (peE O Wc) := ⟨_, rfl⟩
  obtain ⟨kap, hkap⟩ : ∃ kap, kap = peKap (expK as) m (as m) hc eps := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = peQ O kap D := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = peF O (as m) hc Q := ⟨_, rfl⟩
  obtain ⟨Rs, hRs⟩ : ∃ Rs, Rs = peRs O (as m) Wc Q := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = peA O F Rs := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = peB O F Rs := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ Cs, Cs = peCs O F Rs := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = (Cs.map (degG O)).foldr max 0 := ⟨_, rfl⟩
  obtain ⟨dD, hdD⟩ : ∃ dD, dD = degG O D := ⟨_, rfl⟩
  obtain ⟨hInf, hhInf⟩ : ∃ hInf, hInf = peHinf O hc := ⟨_, rfl⟩
  obtain ⟨hBc, hhBc⟩ : ∃ hBc, hBc = O.add hInf (O.mul (cstN m (-((dD + kap : ℕ) : ℚ))) (as m)) :=
    ⟨_, rfl⟩
  obtain ⟨Nb, hNb⟩ : ∃ Nb, Nb = peNb O (pld (expK as) m hInf (as m)) A B R (dD + kap) := ⟨_, rfl⟩
  obtain ⟨alg, halg⟩ : ∃ alg, alg = (!GPoly.isZero O B && decide (degG O A < degG O B)) :=
    ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = if alg then degG O B else degG O A := ⟨_, rfl⟩
  obtain ⟨lower', hlower'⟩ : ∃ lower' : ℕ → List (Code (m + 1)) → List (List ℚ × Code (m + 1)),
      lower' = fun (k : ℕ) ws ↦ if GPoly.isZero O B || decide (degG O B < degG O A) then
        lower (O.mul (cstN m (k : ℚ)) (as m)) ws else lower (O.add hBc (O.mul (cstN m (k : ℚ)) (as m))) ws :=
    ⟨_, rfl⟩
  obtain ⟨init, hinit⟩ : ∃ init, init =
      (List.range Wc.length).map fun i ↦ (unitV Wc.length i, ([] : GPoly (Code (m + 1)))) := ⟨_, rfl⟩
  obtain ⟨Bs, hBs⟩ : ∃ Bs, Bs = match Nb with
      | none => init
      | some N => rdeLoop O (cstN m) (peW O (as m)) A B Cs Wc.length δ alg (leadG O A) (leadG O B)
          lower' (N + 1) init := ⟨_, rfl⟩
  have hunf : prdeExp (expK as) m (as m) lower hcode W =
      if (!GPoly.isZero O B && !alg && decide (degG O A = degG O B) &&
        !O.isZero (O.add (O.deriv hBc) (O.neg (O.mul (leadG O B) (O.inv (leadG O A)))))) = true then []
      else peOut (expK as) m (peW O (as m)) A B Cs Wc.length Q Bs := by
    subst hBs hinit hlower' hδ halg hNb hhBc hhInf hdD hR hCs hB hA hRs hF hQ hkap hD heps hhc hWc
    rfl
  rw [hunf]
  -- basic facts
  have hWc0 : ∀ q ∈ Wc, GPoly.toPoly (T.Mm m h) q.2 ≠ 0 := fun q hq ↦ by
    rw [hWc] at hq
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hq
    have := T.σ1_cleanG_ne m h v
    intro h0
    exact this (by rw [σ1, h0, map_zero])
  have hhc0 : GPoly.toPoly (T.Mm m h) hc.2 ≠ 0 := by
    have := T.σ1_cleanG_ne m h hcode
    rw [← hhc] at this
    intro h0; exact this (by rw [σ1, h0, map_zero])
  obtain ⟨he0, -⟩ := T.peE_spec m h Wc hWc0
  obtain ⟨hD0, hDm⟩ := T.peD_spec m h _ he0
  rw [← hD] at hD0 hDm
  have hQp : GPoly.toPoly (T.Mm m h) Q = X ^ kap * GPoly.toPoly (T.Mm m h) D := by
    rw [hQ, T.toPoly_peQ]
  have hQm : (GPoly.toPoly (T.Mm m h) Q).Monic := by rw [hQp]; exact (monic_X_pow kap).mul hDm
  have hQ0 : T.σ1 m h Q ≠ 0 := by
    rw [σ1, map_ne_zero_iff _ (T.phi_injective' m h)]; exact hQm.ne_zero
  have hdDk : (GPoly.toPoly (T.Mm m h) Q).natDegree = dD + kap := by
    rw [hQp, (monic_X_pow kap).natDegree_mul hDm, natDegree_X_pow, hdD, degG_eq (T.Mm m h)]; ring
  have hRs2 : ∀ p ∈ Rs, T.σ1 m h p.2 ≠ 0 := fun p hp ↦ by
    rw [hRs] at hp
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hp
    exact T.σ1_cleanG_ne m h _
  have hP : GPoly.toPoly (T.Mm m h) (prodD (GPoly.mul O) [O.one] Rs) ≠ 0 := by
    have := σ_prodD_ne_zero (GPoly.mul O) [O.one] (T.σ1 m h) (T.σ1_mul m h) (T.σ1_one m h) _ hRs2
    intro h0; exact this (by rw [σ1, h0, map_zero])
  have hF2 : GPoly.toPoly (T.Mm m h) F.2 ≠ 0 := by
    rw [hF]; unfold peF; intro h0
    exact T.σ1_cleanG_ne m h _ (by rw [σ1, h0, map_zero])
  have hA0 : GPoly.toPoly (T.Mm m h) A ≠ 0 := by
    rw [hA, peA, GPoly.toPoly_mul]; exact mul_ne_zero hF2 hP
  have hlW : Wc.length = W.length := by rw [hWc, List.length_map]
  have hlCs : Cs.length = Wc.length := by simp [hCs, peCs, length_cross, hRs, peRs]
  have hlead := T.pe_bal_lead m h hc2 hc hhc0 Q hQm (dD + kap) hdDk Rs hP
  rw [← hF, ← hA, ← hB, ← hhInf, ← hhBc] at hlead
  split_ifs with hbad
  · -- the balanced check always passes
    exfalso
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hbad
    obtain ⟨⟨⟨hBz, -⟩, hdeq⟩, hok⟩ := hbad
    have hB0 : GPoly.toPoly (T.Mm m h) B ≠ 0 := fun h0 ↦ by
      rw [(GPoly.isZero_iff (T.Mm m h) _).mpr h0] at hBz; exact Bool.noConfusion hBz
    rw [degG_eq (T.Mm m h), degG_eq (T.Mm m h)] at hdeq
    obtain ⟨-, hl⟩ := hlead hB0 hdeq
    have : O.isZero (O.add (O.deriv hBc) (O.neg (O.mul (leadG O B) (O.inv (leadG O A))))) = true := by
      rw [(T.Mm m h).isZero_iff, (T.Mm m h).sem_add, (T.Mm m h).sem_deriv, (T.Mm m h).sem_neg,
        (T.Mm m h).sem_mul, (T.Mm m h).sem_inv, sem_leadG _ _ hB0, sem_leadG _ _ hA0, hl]
      ring
    rw [this] at hok; exact Bool.noConfusion hok
  -- the equation with the cleaned data
  have hgd : ∀ i < Wc.length, Wc.getD i ((opsM (expK as) m).monomial (peW (opsM (expK as) m) (as m))).zero =
      Wc.getD i ([], []) := fun i hi ↦ by
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi]
  have hy' : y′ + ((T.M1 m h).sem hc)′ * y = ∑ i ∈ Finset.range Wc.length,
      algebraMap Kc (T.F (m + 1)) (c.getD i 0) * (T.M1 m h).sem (Wc.getD i ([], [])) := by
    have hhcs : (T.M1 m h).sem hcode = (T.M1 m h).sem hc := by rw [hhc, T.sem1_cleanG]
    rw [← hhcs, hy, sC, hlW]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.mp hi
    congr 1
    have hi2 : i < Wc.length := by rw [hlW]; exact hi'
    rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hi2]
    simp only [hWc, List.getElem_map]
    rw [T.sem1_cleanG]
  obtain ⟨Yv, hYv⟩ := T.pe_denominator m h hc2 hc hhc0 Wc hWc0 (fun i ↦ c.getD i 0) y hy'
  rw [← heps, ← hkap, ← hD, ← hQ] at hYv
  have hyQ : T.phi m Yv / T.σ1 m h Q = y := by rw [← hYv]; field_simp
  -- the polynomial equation
  have hid := T.pe_identity m h hc Wc Q hQ0 Yv (fun i ↦ c.getD i 0)
  rw [← hF, ← hRs, ← hA, ← hB, ← hCs, hyQ] at hid
  have hbr : y′ + ((T.M1 m h).sem hc)′ * y - ∑ i ∈ Finset.range Wc.length,
      algebraMap Kc (T.F (m + 1)) (c.getD i 0) *
        (T.M1 m h).sem (Wc.getD i ((opsM (expK as) m).monomial (peW (opsM (expK as) m) (as m))).zero)
      = 0 := by
    rw [hy', sub_eq_zero]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hgd i (Finset.mem_range.mp hi)]
  rw [hbr, mul_zero] at hid
  have hpoly := (map_eq_zero_iff _ (T.phi_injective' m h)).mp hid
  have hresC : resC (algebraMap Kc (T.F m)) (T.Mm m h) (T.bE m h) A B Cs c Yv = 0 := by
    unfold resC; rw [hlCs]; exact hpoly
  -- the degree bound
  obtain ⟨r, hr⟩ : ∃ r, r = ∑ i ∈ Finset.range Cs.length,
      C (algebraMap Kc (T.F m) (c.getD i 0)) * GPoly.toPoly (T.Mm m h) (Cs.getD i []) := ⟨_, rfl⟩
  have hrR : r.natDegree ≤ R := by
    rw [hr]
    refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ natDegree_C_mul_le _ _ |>.trans ?_
    rw [hR]; exact natDegree_le_R (T.Mm m h) Cs i (Finset.mem_range.mp hi)
  have heq : GPoly.toPoly (T.Mm m h) A * implicitDeriv (C (T.bE m h) * X) Yv +
      GPoly.toPoly (T.Mm m h) B * Yv = r := by
    rw [hr]; unfold resC at hresC; exact sub_eq_zero.mp hresC
  have hNbs := T.pe_Nb m h hc2 hc hhc0 Q hQm (dD + kap) hdDk Rs hP Yv r R hrR
    (by rw [← hF, ← hA, ← hB]; exact heq)
  rw [← hF, ← hA, ← hB, ← hhInf, ← hNb] at hNbs
  have hιd : ∀ κ : Kc, (algebraMap Kc (T.F m) κ)′ = 0 := fun κ ↦ Subtype.ext (by
    rw [coe_deriv]
    change (algebraMap Kc E κ)′ = 0
    rw [deriv_algebraMap, T.hC, map_zero])
  have hιrat : ∀ q : ℚ, algebraMap Kc (T.F m) (algebraMap ℚ Kc q) = (q : T.F m) :=
    fun q ↦ by rw [← map_ratCast (algebraMap Kc (T.F m)), ← map_ratCast (algebraMap ℚ Kc)]; rfl
  have hcCs : ∀ i, Cs.length ≤ i → c.getD i 0 = 0 := fun i hi ↦ hcW i (by omega)
  have hinit' : init = rdeInit (α := Code (m + 1)) Cs.length := by rw [hinit, hlCs]; rfl
  -- the basis spans the solutions
  have hstage : ∃ β : List Kc, (∀ i, c.getD i 0 = ∑ k ∈ Finset.range Bs.length,
      β.getD k 0 * algebraMap ℚ Kc ((Bs.getD k ([], [])).1.getD i 0)) ∧
      Yv = ∑ l ∈ Finset.range Bs.length, C (algebraMap Kc (T.F m) (β.getD l 0)) *
        GPoly.toPoly (T.Mm m h) (Bs.getD l ([], [])).2 := by
    cases hNbv : Nb with
    | none =>
      rw [hNbv] at hBs
      simp only at hBs
      have hY0 := hNbs.2 hNbv
      obtain ⟨β, hβc, -⟩ := rdeInit_complete (algebraMap Kc (T.F m)) (M := T.Mm m h) (T.bE m h) A B
        Cs δ 0 c hcCs Yv (by rw [hY0, natDegree_zero]) (fun d _ ↦ by rw [hresC, coeff_zero])
      rw [← hinit', ← hBs] at hβc
      refine ⟨β, hβc, ?_⟩
      rw [hY0]
      symm
      refine Finset.sum_eq_zero fun l hl ↦ ?_
      have hl' : l < Wc.length := by simpa [hBs, hinit] using hl
      rw [hBs, hinit, NestTower.getD_range_map _ _ hl']
      simp
    | some N =>
      rw [hNbv] at hBs
      simp only at hBs
      have hYN := hNbs.1 N hNbv
      have hge := peNb_ge _ _ _ _ _ _ (hNb.symm.trans hNbv)
      rw [← halg, ← hδ] at hge
      have hC : ∀ i < Cs.length, (GPoly.toPoly (T.Mm m h) (Cs.getD i [])).natDegree ≤ N + δ :=
        fun i hi ↦ (natDegree_le_R (T.Mm m h) Cs i hi).trans (by rw [← hR]; exact hge)
      have hδ' : δ = if alg then (GPoly.toPoly (T.Mm m h) B).natDegree
          else (GPoly.toPoly (T.Mm m h) A).natDegree := by
        rw [hδ, degG_eq (T.Mm m h), degG_eq (T.Mm m h)]
      rw [degG_eq (T.Mm m h), degG_eq (T.Mm m h)] at halg hlower'
      have hbE : T.bE m h = ((T.Mm m h).sem (as m))′ := rfl
      have hlowk : ∀ k : ℕ, (GPoly.isZero O B || decide ((GPoly.toPoly (T.Mm m h) B).natDegree <
          (GPoly.toPoly (T.Mm m h) A).natDegree)) = true →
          lower' k = lower (O.mul (cstN m (k : ℚ)) (as m)) := fun k hk ↦ by
        funext ws; simp only [hlower']; rw [if_pos hk]
      have hlowk' : ∀ k : ℕ, ¬(GPoly.isZero O B || decide ((GPoly.toPoly (T.Mm m h) B).natDegree <
          (GPoly.toPoly (T.Mm m h) A).natDegree)) = true →
          lower' k = lower (O.add hBc (O.mul (cstN m (k : ℚ)) (as m))) := fun k hk ↦ by
        funext ws; simp only [hlower']; rw [if_neg hk]
      rw [← hlCs, hinit'] at hBs
      have hlcA := sem_leadG (T.Mm m h) A hA0
      cases alg with
      | true =>
        simp only [if_true] at hδ'
        simp only [Bool.true_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at halg
        obtain ⟨hBz, hlt⟩ := halg
        have hB0 : GPoly.toPoly (T.Mm m h) B ≠ 0 := fun h0 ↦ by
          rw [(GPoly.isZero_iff (T.Mm m h) _).mpr h0] at hBz; exact Bool.noConfusion hBz
        have hlcB := sem_leadG (T.Mm m h) B hB0
        obtain ⟨-, hcomp⟩ := rdeLoop_stage (ι := algebraMap Kc (T.F m)) (M := T.Mm m h)
          (cst := cstN m) (b := T.bE m h) (A := A) (B := B) (Cl := Cs) (δ := δ) (hcst := hcst)
          (w := peW O (as m)) (hw := hw) (hιd := hιd) (hιrat := hιrat) (by rw [hδ']; exact hlt.le)
          (by rw [hδ']) true (leadG O A) (leadG O B) lower'
          (fun _ ↦ ⟨coeff_eq_zero_of_natDegree_lt (by rw [hδ']; exact hlt), by rw [hlcB, hδ']; rfl,
            by rw [hlcB]; exact leadingCoeff_ne_zero.mpr hB0⟩)
          (fun h' ↦ by cases h') N (N + 1) (rdeInit Cs.length)
          (rdeInit_sound (M := T.Mm m h) (T.bE m h) A B Cs δ N hC)
          (rdeInit_complete (algebraMap Kc (T.F m)) (M := T.Mm m h) (T.bE m h) A B Cs δ N)
        rw [← hBs] at hcomp
        obtain ⟨β, hβc, hcoef⟩ := hcomp c hcCs Yv hYN (fun d _ ↦ by rw [hresC, coeff_zero])
        refine ⟨β, hβc, ?_⟩
        ext i
        rw [hcoef i (Nat.zero_le _), finset_sum_coeff]
        simp only [coeff_C_mul]
      | false =>
        simp only [Bool.false_eq_true, if_false] at hδ'
        have hBle : (GPoly.toPoly (T.Mm m h) B).natDegree ≤ (GPoly.toPoly (T.Mm m h) A).natDegree := by
          by_cases hz : GPoly.isZero O B = true
          · rw [(GPoly.isZero_iff _ _).mp hz, natDegree_zero]; exact Nat.zero_le _
          · by_contra hlt
            push_neg at hlt
            simp [hz, hlt] at halg
        have hdiff : false = false → (T.Mm m h).sem (leadG O A) = (GPoly.toPoly (T.Mm m h) A).coeff δ ∧
            (T.Mm m h).sem (leadG O A) ≠ 0 ∧ ∀ k : ℕ, ∃ f : T.F m,
              (∀ z : T.F m, (GPoly.toPoly (T.Mm m h) A).coeff δ * (z′ + k * T.bE m h * z) +
                (GPoly.toPoly (T.Mm m h) B).coeff δ * z =
                  (GPoly.toPoly (T.Mm m h) A).coeff δ * (z′ + f * z)) ∧
              RdeSpecK (algebraMap Kc (T.F m)) (T.Mm m h) f (lower' k) := by
          intro _
          refine ⟨by rw [hlcA, hδ']; rfl, by rw [hlcA]; exact leadingCoeff_ne_zero.mpr hA0,
            fun k ↦ ?_⟩
          by_cases hcase : (GPoly.isZero O B || decide ((GPoly.toPoly (T.Mm m h) B).natDegree <
              (GPoly.toPoly (T.Mm m h) A).natDegree)) = true
          · refine ⟨((T.Mm m h).sem (O.mul (cstN m (k : ℚ)) (as m)))′, fun z ↦ ?_, ?_⟩
            · have hBc0 : (GPoly.toPoly (T.Mm m h) B).coeff δ = 0 := by
                simp only [Bool.or_eq_true, decide_eq_true_eq] at hcase
                rcases hcase with hz | hlt
                · rw [(GPoly.isZero_iff _ _).mp hz, coeff_zero]
                · rw [hδ']; exact coeff_eq_zero_of_natDegree_lt hlt
              rw [hBc0, (T.Mm m h).sem_mul, hcst, Derivation.leibniz, deriv_ratCastK, hbE]
              simp only [smul_eq_mul, mul_zero, add_zero]
              push_cast
              ring
            · rw [hlowk k hcase]; exact hlow _
          · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hcase
            obtain ⟨hz, hnlt⟩ := hcase
            have hB0 : GPoly.toPoly (T.Mm m h) B ≠ 0 := fun h0 ↦ hz ((GPoly.isZero_iff _ _).mpr h0)
            have hdeq : (GPoly.toPoly (T.Mm m h) A).natDegree = (GPoly.toPoly (T.Mm m h) B).natDegree := by
              omega
            obtain ⟨-, hl⟩ := hlead hB0 hdeq
            refine ⟨((T.Mm m h).sem (O.add hBc (O.mul (cstN m (k : ℚ)) (as m))))′, fun z ↦ ?_, ?_⟩
            · have hlA : (GPoly.toPoly (T.Mm m h) A).coeff δ = (GPoly.toPoly (T.Mm m h) A).leadingCoeff := by
                rw [hδ']; rfl
              have hlB : (GPoly.toPoly (T.Mm m h) B).coeff δ = (GPoly.toPoly (T.Mm m h) B).leadingCoeff := by
                rw [hδ', hdeq]; rfl
              have hA0' : (GPoly.toPoly (T.Mm m h) A).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA0
              rw [hlA, hlB, (T.Mm m h).sem_add, Derivation.map_add, hl, (T.Mm m h).sem_mul, hcst,
                Derivation.leibniz, deriv_ratCastK, hbE]
              simp only [smul_eq_mul, mul_zero, add_zero]
              field_simp
              push_cast
              ring
            · rw [hlowk' k (by simp [hz, hnlt])]; exact hlow _
        obtain ⟨-, hcomp⟩ := rdeLoop_stage (ι := algebraMap Kc (T.F m)) (M := T.Mm m h)
          (cst := cstN m) (b := T.bE m h) (A := A) (B := B) (Cl := Cs) (δ := δ) (hcst := hcst)
          (w := peW O (as m)) (hw := hw) (hιd := hιd) (hιrat := hιrat) (by rw [hδ'])
          (by rw [hδ']; exact hBle) false (leadG O A) (leadG O B) lower'
          (fun h' ↦ by cases h') hdiff N (N + 1) (rdeInit Cs.length)
          (rdeInit_sound (M := T.Mm m h) (T.bE m h) A B Cs δ N hC)
          (rdeInit_complete (algebraMap Kc (T.F m)) (M := T.Mm m h) (T.bE m h) A B Cs δ N)
        rw [← hBs] at hcomp
        obtain ⟨β, hβc, hcoef⟩ := hcomp c hcCs Yv hYN (fun d _ ↦ by rw [hresC, coeff_zero])
        refine ⟨β, hβc, ?_⟩
        ext i
        rw [hcoef i (Nat.zero_le _), finset_sum_coeff]
        simp only [coeff_C_mul]
  obtain ⟨β, hβc, hYvs⟩ := hstage
  have hres' : ∑ l ∈ Finset.range Bs.length, C (algebraMap Kc (T.F m) (β.getD l 0)) *
      resQ (T.Mm m h) (T.bE m h) A B Cs (Bs.getD l ([], [])).1
        (GPoly.toPoly (T.Mm m h) (Bs.getD l ([], [])).2) = 0 := by
    have := resC_comb (algebraMap Kc (T.F m)) (M := T.Mm m h) (T.bE m h) A B Cs hιd hιrat Bs c β
      hβc 0
    rw [add_zero, ← hYvs, hresC, show Lop (T.Mm m h) (T.bE m h) A B 0 = 0 by simp [Lop, Dz],
      add_zero] at this
    exact this.symm
  exact T.peOut_complete m h A B Cs Wc.length Q hQ0 Bs c (fun i hi ↦ hcW i (by omega)) β hβc Yv
    hYvs hres' y hYv

end Main

/-- **The parametric Risch equation is solved at every level of a certified exponential tower**:
`prde` is sound, and complete over the constants. -/
theorem prde_spec : ∀ (n : ℕ), expCertM (expK as) n = true → ∀ (h : T.Tr n) (f : Code (n + 1)),
    RdeSpecK (algebraMap Kc (T.F n)) (T.MP n h) ((T.MP n h).sem f)′ (prde (expK as) n f)
  | 0, _, h, f => ⟨fun ws r hr ↦ T.prde0_sound h f ws r hr,
      fun ws c hc z hz ↦ T.prde0_complete h f ws c hc z hz⟩
  | n + 1, hcert, h, f => by
    obtain ⟨hc1, hc2⟩ := expCert_succ hcert
    have hn : T.Tr n := fun i hi ↦ h i (by omega)
    have IH := prde_spec n hc1 hn
    exact ⟨fun ws r hr ↦ T.prdeExp_sound n h (prde (expK as) n) f ws r hr,
      fun ws c hc z hz ↦ T.prdeExp_complete n h hc2 (prde (expK as) n) (fun g ↦ IH g) f ws c hc z hz⟩

end NestMTower

end Tower.NestM
