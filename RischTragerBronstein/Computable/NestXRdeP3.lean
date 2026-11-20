import RischTragerBronstein.Computable.NestXRdeP2

/-!
# The Risch equation over a logarithmic level: the denominator

At a logarithmic level every irreducible polynomial is normal, and the denominator of a solution
of `y′ + (h′ + ∑ cⱼ wⱼ′ / wⱼ) y = ∑ cᵢ wᵢ` divides `D = gcd(e, e′) · Lᴺ` (`rde_log_denominator`),
`L` the product of the numerators and denominators of the `wⱼ` and `N = logBound` (every positive
integer residue `∑ cⱼ ordₚ wⱼ` is found by `ratVal` among the integer vectors `intVecs`).
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Tower.NestX

open Tower.NestP Tower.NestM

section Lists

lemma sum_map_getDXP {β M : Type*} [AddCommMonoid M] (f : β → M) (d : β) :
    ∀ l : List β, (l.map f).sum = ∑ j ∈ Finset.range l.length, f (l.getD j d)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, sum_map_getDXP f d l, List.length_cons,
      Finset.sum_range_succ']
    simp [add_comm]

lemma sum_zip_getDXP {β γ M : Type*} [AddCommMonoid M] (f : β × γ → M) (d1 : β) (d2 : γ) :
    ∀ (v : List β) (l : List γ), v.length = l.length →
      ((List.zip v l).map f).sum = ∑ j ∈ Finset.range l.length, f (v.getD j d1, l.getD j d2)
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: v, b :: l, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.zip_cons_cons, List.map_cons, List.sum_cons, sum_zip_getDXP f d1 d2 v l h,
      List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

variable {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

lemma sem_zipCodeXP (cst : ℚ → α) (hcst : ∀ q, M.sem (cst q) = (q : K)) :
    ∀ (v : List ℤ) (l : List (α × α)),
      M.sem ((List.zip v l).foldr (fun p acc2 ↦ O.add (O.mul (cst ((p.1 : ℤ) : ℚ)) p.2.1) acc2)
        O.zero) = ((List.zip v l).map fun p ↦ ((p.1 : ℤ) : K) * M.sem p.2.1).sum
  | [], _ => by simp [M.sem_zero]
  | _ :: _, [] => by simp [M.sem_zero]
  | x :: v, p :: l => by
    rw [List.zip_cons_cons, List.foldr_cons, M.sem_add, M.sem_mul, hcst, sem_zipCodeXP cst hcst v l,
      List.map_cons, List.sum_cons]
    push_cast
    rfl

end Lists

lemma mem_intVecs_mapXP {β : Type*} (l : List β) (d : β) (f : β → ℕ) (v : List ℤ)
    (hl : v.length = l.length) (hb : ∀ j < l.length, |v.getD j 0| ≤ (f (l.getD j d) : ℤ)) :
    v ∈ intVecs (l.map f) := by
  refine mem_intVecs _ v (by simp [hl]) fun j hj ↦ ?_
  rw [List.length_map] at hj
  rw [NestTower.getD_map' _ _ d 0 hj]
  exact hb j hj

/-- A fold of `max` over `natOfQ` of optional rationals dominates each value. -/
lemma le_foldr_ratXP {β : Type*} (f : β → Option ℚ) :
    ∀ (L : List β) (x : β), x ∈ L → ∀ q, f x = some q →
      (natOfQ q).getD 0 ≤ L.foldr (fun v acc ↦ match f v with
        | some q => max acc ((natOfQ q).getD 0)
        | none => acc) 0
  | [], _, hx, _, _ => by simp at hx
  | y :: L, x, hx, q, hq => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [hq]; exact le_max_right _ _
    · have := le_foldr_ratXP f L x hx q hq
      split
      · exact this.trans (le_max_left _ _)
      · exact this

lemma le_foldr_genXP {β : Type*} (g : β → ℕ → ℕ) (hmono : ∀ v acc, acc ≤ g v acc) :
    ∀ (L : List β) (x : β), x ∈ L → ∀ n, (∀ acc, n ≤ g x acc) → n ≤ L.foldr g 0
  | [], _, hx, _, _ => by simp at hx
  | y :: L, x, hx, n, hn => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hn _
    · exact (le_foldr_genXP g hmono L x hx n hn).trans (hmono _ _)

section GLemmas

variable {α : Type} {K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

lemma toPoly_powGXP (p : GPoly α) : ∀ N, GPoly.toPoly M (powG O p N) = GPoly.toPoly M p ^ N
  | 0 => by simp [powG, M.sem_one]
  | N + 1 => by rw [powG, GPoly.toPoly_mul, toPoly_powGXP p N, pow_succ, mul_comm]

lemma toPoly_nrmP_ne (p : GPoly α) : GPoly.toPoly M (nrmP O false p) ≠ 0 := by
  simp only [nrmP, Bool.false_eq_true, if_false]
  split_ifs with hz
  · simp [M.sem_one]
  · simpa [GPoly.isZero_iff M] using hz

lemma toPoly_nrmP_of_ne (p : GPoly α) (hp : GPoly.toPoly M p ≠ 0) :
    GPoly.toPoly M (nrmP O false p) = GPoly.toPoly M p := by
  unfold nrmP
  rw [if_neg (by rwa [GPoly.isZero_iff M]), if_neg (by simp)]

lemma toPoly_logPoly_ne (l : List ((GPoly α × GPoly α) × (GPoly α × GPoly α))) :
    GPoly.toPoly M (logPoly O false l) ≠ 0 := by
  induction l with
  | nil => simp [logPoly, M.sem_one]
  | cons cw l ih =>
    simp only [logPoly, List.foldr_cons] at ih ⊢
    rw [GPoly.toPoly_mul, GPoly.toPoly_mul]
    exact mul_ne_zero (mul_ne_zero (toPoly_nrmP_ne M _) (toPoly_nrmP_ne M _)) ih

lemma dvd_toPoly_logPoly (d : (GPoly α × GPoly α) × (GPoly α × GPoly α)) :
    ∀ (l : List ((GPoly α × GPoly α) × (GPoly α × GPoly α))) (j : ℕ), j < l.length →
      GPoly.toPoly M (l.getD j d).2.1 ≠ 0 → GPoly.toPoly M (l.getD j d).2.2 ≠ 0 →
      GPoly.toPoly M (l.getD j d).2.1 * GPoly.toPoly M (l.getD j d).2.2 ∣
        GPoly.toPoly M (logPoly O false l)
  | [], _, hj, _, _ => by simp at hj
  | cw :: l, j, hj, hN, hD => by
    simp only [logPoly, List.foldr_cons]
    rw [GPoly.toPoly_mul, GPoly.toPoly_mul]
    cases j with
    | zero =>
      simp only [List.getD_cons_zero] at hN hD ⊢
      rw [toPoly_nrmP_of_ne M _ hN, toPoly_nrmP_of_ne M _ hD]
      exact dvd_mul_right _ _
    | succ j =>
      simp only [List.getD_cons_succ] at hN hD ⊢
      have := dvd_toPoly_logPoly d l j (by simp at hj; omega) hN hD
      exact dvd_mul_of_dvd_right this _

end GLemmas

end Tower.NestX

namespace Tower.NestM

open Tower.PrimN Tower.NestP Tower.NestX CPoly

namespace NestMTower

variable {Kc E : Type*} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
variable [DifferentialAlgebra Kc E] [CharZero Kc] {ks : (m : ℕ) → KindN m}
variable (T : NestMTower Kc E ks)

section LogPart

variable (m : ℕ) (h : T.Tr (m + 1))

/-- A fraction over level `m`. -/
abbrev GPX := GPoly (Code (m + 1)) × GPoly (Code (m + 1))

/-- The default entry of a logarithmic part. -/
abbrev dLX : GPX m × GPX m := (([], []), ([], []))

/-- The constants of the logarithmic part. -/
lemma logs_constXP (logs : List (GPX m × GPX m)) (hok : ∀ cw ∈ logs, ((T.M1X m h).sem cw.1)′ = 0) :
    ∃ κ : ℕ → Kc, ∀ j < logs.length,
      (T.M1X m h).sem (logs.getD j (dLX m)).1 = algebraMap Kc (T.F (m + 1)) (κ j) := by
  classical
  have : ∀ j < logs.length, ∃ κ : Kc,
      (T.M1X m h).sem (logs.getD j (dLX m)).1 = algebraMap Kc (T.F (m + 1)) κ := by
    intro j hj
    have hmem : logs.getD j (dLX m) ∈ logs := by
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
    exact T.const_F _ (hok _ hmem)
  choose! κ hκ using this
  exact ⟨κ, hκ⟩

/-- The indices of the non-degenerate logarithms. -/
noncomputable def sLX (logs : List (GPX m × GPX m)) : Finset ℕ := by
  classical
  exact (Finset.range logs.length).filter fun j ↦
    GPoly.toPoly (T.MX m h) (logs.getD j (dLX m)).2.1 ≠ 0 ∧
      GPoly.toPoly (T.MX m h) (logs.getD j (dLX m)).2.2 ≠ 0

lemma mem_sLX (logs : List (GPX m × GPX m)) (j : ℕ) : j ∈ T.sLX m h logs ↔ j < logs.length ∧
    GPoly.toPoly (T.MX m h) (logs.getD j (dLX m)).2.1 ≠ 0 ∧
      GPoly.toPoly (T.MX m h) (logs.getD j (dLX m)).2.2 ≠ 0 := by
  classical
  unfold sLX
  simp

/-- The logarithmic part as a sum over the non-degenerate logarithms. -/
lemma logSumV_eqXP (logs : List (GPX m × GPX m)) (κ : ℕ → Kc)
    (hκ : ∀ j < logs.length,
      (T.M1X m h).sem (logs.getD j (dLX m)).1 = algebraMap Kc (T.F (m + 1)) (κ j)) :
    logSumV (T.M1X m h) logs = ∑ j ∈ T.sLX m h logs, algebraMap Kc (T.F (m + 1)) (κ j) *
      logDeriv (T.σX m h (logs.getD j (dLX m)).2.1 / T.σX m h (logs.getD j (dLX m)).2.2) := by
  classical
  unfold logSumV
  rw [sum_map_getDXP _ (dLX m), sLX, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' := Finset.mem_range.mp hj
  rw [hκ j hj', T.semX]
  split_ifs with hc
  · rfl
  · have h0 : T.σX m h (logs.getD j (dLX m)).2.1 / T.σX m h (logs.getD j (dLX m)).2.2 = 0 := by
      rw [not_and_or, not_not, not_not] at hc
      rcases hc with hc | hc
      · rw [σX, hc, map_zero, zero_div]
      · rw [σX, σX, hc, map_zero, div_zero]
    rw [h0]
    simp [logDeriv]

end LogPart

/-- **The logarithmic bound**: any `k` whose rational value is found by `ratVal` for an integer
vector `v` of `intVecs` is at most `logBound`. -/
lemma le_logBoundXP (m : ℕ) (logs : List (Code (m + 2) × Code (m + 2)))
    (v : List ℤ)
    (hv : v ∈ intVecs (logs.map fun cw ↦ degG (opsM ks m) cw.2.1 + degG (opsM ks m) cw.2.2))
    (k : ℕ) (hrat : ratVal ks (m + 1) ((List.zip v logs).foldr (fun p acc2 ↦
      (opsM ks (m + 1)).add ((opsM ks (m + 1)).mul (cstN (m + 1) ((p.1 : ℤ) : ℚ)) p.2.1) acc2)
        (opsM ks (m + 1)).zero) = some (k : ℚ)) :
    k ≤ logBound ks m logs := by
  unfold logBound
  refine le_foldr_genXP _ (fun v' acc ↦ ?_) _ v hv k (fun acc ↦ ?_)
  · dsimp only
    split
    · exact le_max_left _ _
    · exact le_rfl
  · dsimp only
    rw [hrat]
    dsimp only
    rw [natOfQ_natCast]
    exact le_max_right _ _

section Den

variable (m : ℕ) (h : T.Tr (m + 1)) {η : Code (m + 1)} (hk : ks m = .prim η)

include hk in
set_option maxHeartbeats 3200000 in
/-- **The denominator bound at a logarithmic level**: every solution of
`y′ + f y = ∑ cᵢ wᵢ` is `Yv / D`, `D = peDX … = gcd(e, e′) Lᴺ` (made monic). -/
theorem prim_denominatorXP (fr : FRep (GPX m)) (hok : FRepOK (T.M1X m h) fr)
    (Wc : List (GPoly (Code (m + 1)) × GPoly (Code (m + 1))))
    (hWc : ∀ q ∈ Wc, GPoly.toPoly (T.MX m h) q.2 ≠ 0) (c : ℕ → Kc) (y : T.F (m + 1))
    (hy : y′ + (T.M1X m h).sem (fCode ((opsM ks m).monomial (wK (opsM ks m) (ks m))) fr) * y =
      ∑ i ∈ Finset.range Wc.length,
        algebraMap Kc (T.F (m + 1)) (c i) * (T.M1X m h).sem (Wc.getD i ([], []))) :
    ∃ Yv : (T.F m)[X], y * T.σX m h (peDX (opsM ks m) (wK (opsM ks m) (ks m))
      (lcmList (opsM ks m) (Wc.map Prod.snd)) (logPoly (opsM ks m) false fr.logs)
        (logBound ks m fr.logs)) = T.phi m Yv := by
  classical
  set O := opsM ks m with hO
  have htr : Transcendental (T.F m) (T.ts m) := h m (by omega)
  -- the data
  set logs := fr.logs with hlogs
  obtain ⟨κ, hκ⟩ := T.logs_constXP m h logs hok
  set s := T.sLX m h logs with hs
  set Nw : ℕ → (T.F m)[X] := fun j ↦ GPoly.toPoly (T.MX m h) (logs.getD j (dLX m)).2.1 with hNw
  set Dw : ℕ → (T.F m)[X] := fun j ↦ GPoly.toPoly (T.MX m h) (logs.getD j (dLX m)).2.2 with hDw
  set cF : ℕ → T.F m := fun j ↦ algebraMap Kc (T.F m) (κ j) with hcF
  have hND : ∀ j ∈ s, Nw j ≠ 0 ∧ Dw j ≠ 0 := fun j hj ↦ ((T.mem_sLX m h logs j).mp hj).2
  set e := lcmList O (Wc.map Prod.snd) with he
  obtain ⟨hediv, he0, -⟩ := GPolyLcm.lcmList_spec (T.MX m h) (Wc.map Prod.snd) (fun p hp ↦ by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; exact hWc q hq)
  rw [← he] at hediv he0
  set g := (GPoly.egcd O e (GPoly.derivT O (wK O (ks m)) e)).1 with hg
  have hge : GPoly.toPoly (T.MX m h) g ∣ GPoly.toPoly (T.MX m h) e := (GPoly.egcd_dvd _ _ _).1
  have hg0 : GPoly.toPoly (T.MX m h) g ≠ 0 := fun h0 ↦ he0 (zero_dvd_iff.mp (h0 ▸ hge))
  have hbez := GPoly.egcd_spec (T.MX m h) e (GPoly.derivT O (wK O (ks m)) e)
  rw [GPoly.toPoly_derivT, T.toPoly_wKX, ← hg] at hbez
  set Lp := logPoly O false fr.logs with hLp
  have hL0 : GPoly.toPoly (T.MX m h) Lp ≠ 0 := toPoly_logPoly_ne (T.MX m h) _
  set N := logBound ks m fr.logs with hN
  have hGL : GPoly.toPoly (T.MX m h) (GPoly.mul O g (powG O Lp N)) =
      GPoly.toPoly (T.MX m h) g * GPoly.toPoly (T.MX m h) Lp ^ N := by
    rw [GPoly.toPoly_mul, toPoly_powGXP]
  have hGL0 : GPoly.toPoly (T.MX m h) (GPoly.mul O g (powG O Lp N)) ≠ 0 := by
    rw [hGL]; exact mul_ne_zero hg0 (pow_ne_zero _ hL0)
  obtain ⟨hDmon, -⟩ := toPoly_monicG (T.MX m h) _ hGL0
  have hDdef : peDX O (wK O (ks m)) e Lp N = monicG O (GPoly.mul O g (powG O Lp N)) := rfl
  rw [hDdef]
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
  set φK := algebraMap (T.F m)[X] (T.F m)⟮t⟯ with hφK
  have hinj : Function.Injective φK := IsFractionRing.injective _ _
  let toK : T.F (m + 1) →+* (T.F m)⟮t⟯ :=
    { toFun := fun z ↦ ⟨(z : E), (T.mem_F_succ).mp z.2⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have htoK_phi : ∀ P, toK (T.phi m P) = φK P := fun P ↦ Subtype.ext (by
    change ((T.phi m P : T.F (m + 1)) : E) = _
    rw [T.coe_phi, hφK, hcoe])
  have htoK_inj : ∀ a b, toK a = toK b → a = b := fun a b hab ↦
    Subtype.ext (congrArg Subtype.val hab)
  have htoK_d : ∀ z, toK (z′) = (toK z)′ := fun z ↦ rfl
  have htoK_ld : ∀ z, toK (logDeriv z) = logDeriv (toK z) := fun z ↦ by
    unfold logDeriv; rw [map_div₀, htoK_d]
  -- the equation in `K`
  set yK := toK y with hyK
  set hK := toK ((T.M1X m h).sem fr.h) with hhK
  set gK := toK (∑ i ∈ Finset.range Wc.length,
    algebraMap Kc (T.F (m + 1)) (c i) * (T.M1X m h).sem (Wc.getD i ([], []))) with hgK
  have hlogK : toK (logSumV (T.M1X m h) logs) = ∑ j ∈ s, φK (C (cF j)) *
      logDeriv (φK (Nw j) / φK (Dw j)) := by
    rw [T.logSumV_eqXP m h logs κ hκ, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, htoK_ld, map_div₀, T.algebraMap_succ, htoK_phi, htoK_phi, htoK_phi]
  have hrde : yK′ + (hK′ + ∑ j ∈ s, φK (C (cF j)) * logDeriv (φK (Nw j) / φK (Dw j))) * yK =
      gK := by
    have e0 := congrArg toK hy
    rw [map_add, map_mul, sem_fCode, map_add, htoK_d, htoK_d, hlogK] at e0
    exact e0
  -- `g e` is regular everywhere
  have hgreg : ∀ (p : (T.F m)[X]) (hp : Irreducible p),
      gK * φK (GPoly.toPoly (T.MX m h) e) ∈ regularAt (T.F m)⟮t⟯ p hp.prime := by
    intro p hp
    rw [hgK, map_sum, Finset.sum_mul]
    refine Subring.sum_mem _ fun i hi ↦ ?_
    have hi' := Finset.mem_range.mp hi
    have hmem : Wc.getD i ([], []) ∈ Wc := by
      rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem _
    obtain ⟨qq, hqq⟩ := hediv _ (List.mem_map.mpr ⟨_, hmem, rfl⟩)
    have hd0 := hWc _ hmem
    rw [map_mul, T.algebraMap_succ, htoK_phi, T.semX, map_div₀, htoK_phi, htoK_phi, mul_assoc]
    refine mul_mem (algebraMap_mem_regularAt _ _) ?_
    have hφd : φK (GPoly.toPoly (T.MX m h) (Wc.getD i ([], [])).2) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr hd0
    have e1 : φK (GPoly.toPoly (T.MX m h) (Wc.getD i ([], [])).1) /
        φK (GPoly.toPoly (T.MX m h) (Wc.getD i ([], [])).2) * φK (GPoly.toPoly (T.MX m h) e) =
        φK (GPoly.toPoly (T.MX m h) (Wc.getD i ([], [])).1 * qq) := by
      rw [hqq, map_mul, map_mul]; field_simp
    rw [e1]
    exact algebraMap_mem_regularAt _ _
  -- the logarithmic bound
  have hLdvd : ∀ (p : (T.F m)[X]), ∀ j ∈ s, p ∣ Nw j * Dw j → p ∣ GPoly.toPoly (T.MX m h) Lp :=
    fun p j hj hp ↦ hp.trans (by
      exact dvd_toPoly_logPoly (T.MX m h) (dLX m) logs j
        ((T.mem_sLX m h logs j).mp hj).1 (hND j hj).1 (hND j hj).2)
  have hNbound : ∀ (k : ℕ) (n : ℕ → ℤ), 0 < k →
      (∀ j ∈ s, |n j| ≤ (((Nw j).natDegree + (Dw j).natDegree : ℕ) : ℤ)) →
      (k : T.F m) = ∑ j ∈ s, cF j * n j → k ≤ N := by
    intro k n hk hn hkn
    set L := logs.length with hL
    set v : List ℤ := (List.range L).map fun j ↦ if j ∈ s then n j else 0 with hv
    have hvl : v.length = L := by simp [hv]
    have hvj : ∀ j < L, v.getD j 0 = if j ∈ s then n j else 0 := fun j hj ↦
      NestTower.getD_range_map _ _ hj
    refine le_logBoundXP m logs v (mem_intVecs_mapXP logs (dLX m) _ v hvl fun j hj ↦ ?_) k
      (T.ratVal_spec (m + 1) h _ k ?_)
    · rw [hvj j hj, degG_eq (T.MX m h), degG_eq (T.MX m h)]
      split_ifs with hjs
      · exact hn j hjs
      · simp only [abs_zero]; positivity
    · refine (sem_zipCodeXP (T.MP (m + 1) h) (cstN (m + 1)) (T.sem_cstN (m + 1) h) v logs).trans ?_
      refine (?_ : ((List.zip v logs).map fun p : ℤ × (GPX m × GPX m) ↦
        ((p.1 : ℤ) : T.F (m + 1)) * (T.M1X m h).sem p.2.1).sum = ((k : ℚ) : T.F (m + 1)))
      rw [sum_zip_getDXP _ 0 (dLX m) v logs hvl]
      have e1 : ∀ j ∈ Finset.range L, ((v.getD j 0 : ℤ) : T.F (m + 1)) *
          (T.M1X m h).sem (logs.getD j (dLX m)).1 =
          if j ∈ s then T.phi m (C (cF j * n j)) else 0 := by
        intro j hj
        have hj' := Finset.mem_range.mp hj
        rw [hvj j hj']
        split_ifs with hjs
        · rw [hκ j hj', T.algebraMap_succ, ← map_intCast (T.phi m), ← map_mul, ← C_eq_intCast,
            ← C_mul, mul_comm]
        · simp
      rw [Finset.sum_congr rfl e1, ← Finset.sum_filter, ← map_sum, ← map_sum]
      have hfs : (Finset.range L).filter (· ∈ s) = s := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨fun h' ↦ h'.2, fun h' ↦ ⟨((T.mem_sLX m h logs j).mp h').1, h'⟩⟩
      rw [hfs, ← hkn, ← T.phi_C_ratX m]
      push_cast
      rfl
  -- every monic irreducible `p`
  have hreg : ∀ (p : (T.F m)[X]) (_ : p.Monic) (hp : Irreducible p),
      yK * φK (GPoly.toPoly (T.MX m h) (monicG O (GPoly.mul O g (powG O Lp N)))) ∈
        regularAt (T.F m)⟮t⟯ p hp.prime := by
    intro p _ hp
    have hnorm : ¬p ∣ p′ := T.normal_prim m htr hk p hp
    have := rde_log_denominator hp hnorm hK yK gK s cF Nw Dw hND _ he0 (hgreg p hp) _ _ _ hbez
      _ (fun j hj hpj ↦ hLdvd p j hj hpj) N hNbound hrde
    rw [hDmon, hGL, map_mul, mul_comm (φK (C _)), ← mul_assoc]
    exact mul_mem this (algebraMap_mem_regularAt _ _)
  obtain ⟨Yv, hYv⟩ := exists_polynomial_of_regularAt _ hreg
  refine ⟨Yv, htoK_inj _ _ ?_⟩
  rw [map_mul, σX, htoK_phi, htoK_phi]
  exact hYv

end Den

end NestMTower

end Tower.NestM
