import RischTragerBronstein.Mixed.NKExactWE

/-!
# The exact part in a basis rescaled at infinity

For a basis `w` of `L` over `Fₘ₊₁ = Fₘ(t)` (`t′ = η`, a primitive level) with derivation matrix
`M` and integer shifts `rᵢ`, `exactWR`:

* bounds the denominators of the coordinates of any antiderivative `∑ Yᵢ wᵢ` by `h q^B`
  (`q`, `h` the common denominators of `M` and of the integrand, `B` the indicial bound at `q`);
* passes to the basis `w̃ᵢ = t^{−rᵢ} wᵢ`, whose matrix is
  `M̃ᵢⱼ = t^{rⱼ − rᵢ} Mᵢⱼ − δᵢⱼ rᵢ η / t` (`rescaleM`) and whose coordinates are `t^{rᵢ} Yᵢ`, with
  denominators dividing `E = h q^B t^R`, `R = max (−rᵢ)`;
* runs `exactWE` with the solver `primSysB … 0`, complete for these denominators.

It is correct for any basis and shifts (`exactWR_correct`); it answers whenever `q` is normal
and the rescaled matrix vanishes at infinity — the case of an integral basis normal at infinity
(`exactWR_isSome`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- `t^k c` for an integer `k`. -/
def tpowL (m : ℕ) (k : ℤ) (c : LC (m + 1)) : LC (m + 1) :=
  if 0 ≤ k then (GPoly.mul (MO Fc ks m) c.1 (sysPowC (MO Fc ks m) (tX Fc ks m) k.toNat), c.2)
  else (c.1, GPoly.mul (MO Fc ks m) c.2 (sysPowC (MO Fc ks m) (tX Fc ks m) (-k).toNat))

/-- `c + e / t`. -/
def addOverT (m : ℕ) (c : LC (m + 1)) (e : LC m) : LC (m + 1) :=
  (GPoly.add (MO Fc ks m) (GPoly.mul (MO Fc ks m) c.1 (tX Fc ks m)) (GPoly.mul (MO Fc ks m) [e] c.2),
    GPoly.mul (MO Fc ks m) c.2 (tX Fc ks m))

/-- The matrix of the rescaled basis `t^{−rᵢ} wᵢ`. -/
def rescaleM (m : ℕ) (η : LC m) (N : ℕ) (Mc : List (List (LC (m + 1)))) (r : ℕ → ℤ) :
    List (List (LC (m + 1))) :=
  (List.range N).map fun i ↦ (List.range N).map fun j ↦
    if i = j then
      addOverT Fc ks m (tpowL Fc ks m 0 ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero))
        ((MO Fc ks m).mul (mcst Fc ks m (-(r i : ℚ))) η)
    else tpowL Fc ks m (r j - r i) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero)

/-- The coordinates in the rescaled basis. -/
def rescaleF (m N : ℕ) (f : List (LC (m + 1))) (r : ℕ → ℤ) : List (LC (m + 1)) :=
  (List.range N).map fun j ↦ tpowL Fc ks m (r j) (f.getD j (MOr Fc ks (m + 1)).zero)

/-- **The exact-part test in the basis `w` rescaled by `t^{−r}`.** -/
def exactWR (m : ℕ) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m)) (N : ℕ)
    (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (r : ℕ → ℤ) : Option Bool :=
  let O1 := MOr Fc ks (m + 1)
  let O := MO Fc ks m
  if N = 0 then none else
    let M : List (List (LC (m + 1))) := (List.range N).map fun i ↦
      (List.range N).map fun j ↦ (Mc.getD i []).getD j O1.zero
    let ent : List (LC (m + 1)) := M.flatten
    let q := lcmGL O (ent.map Prod.snd)
    let hq := lcmGL O (f.map Prod.snd)
    if !((ent.map fun c ↦ cofC O q c.2).all Prod.fst && (f.map fun c ↦ cofC O hq c.2).all Prod.fst &&
        isMonicC O q && isMonicC O hq) then none
    else
    let A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦
      GPoly.mul O ((M.getD i []).getD j O1.zero).1 (cofC O q ((M.getD i []).getD j O1.zero).2).2
    match indBound2 Fc ks m (degG O q) N q (DzLC O η O.zero q) A0 with
    | none => none
    | some B =>
      let R := ((List.range N).map fun i ↦ (-r i).toNat).foldr max 0
      let E := GPoly.mul O (GPoly.mul O hq (sysPowC O q B)) (sysPowC O (tX Fc ks m) R)
      exactWE Fc ks m (fun n A0 q hh G0 ↦ primSysB Fc ks m η lim n A0 q hh G0 0) N
        (rescaleM Fc ks m η N Mc r) (rescaleF Fc ks m N f r) E

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable (m : ℕ) (h1 : T.Tr (m + 1))

/-- `t` as an element of `Fₘ₊₁`. -/
noncomputable abbrev tau : T.F (m + 1) := T.phi m X

lemma tau_ne_zero (htr : Transcendental (T.F m) (T.ts m)) : T.tau m ≠ 0 := fun h0 ↦
  X_ne_zero (T.phi_injective htr (by rw [map_zero]; exact h0))

lemma toPoly_tpow (k : ℕ) :
    GPoly.toPoly (T.MP m h1.of_succ) (sysPowC (MO Fc ks m) (tX Fc ks m) k) = X ^ k := by
  rw [toPoly_sysPowC, T.toPoly_tX m h1.of_succ]

lemma sem_tpowL (htr : Transcendental (T.F m) (T.ts m)) (k : ℤ) (c : LC (m + 1)) :
    (T.MPr (m + 1) h1).sem (tpowL Fc ks m k c) = (T.MPr (m + 1) h1).sem c * T.tau m ^ k := by
  have ht := T.tau_ne_zero m htr
  rw [MPr_sem, MPr_sem, T.sem_MP_succ, T.sem_MP_succ]
  have hX : T.phi m X = T.tau m := rfl
  by_cases hk : 0 ≤ k
  · have e : tpowL Fc ks m k c =
        (GPoly.mul (MO Fc ks m) c.1 (sysPowC (MO Fc ks m) (tX Fc ks m) k.toNat), c.2) := by
      unfold tpowL; simp only [hk, ↓reduceIte]; rfl
    rw [e]
    simp only [GPoly.toPoly_mul, toPoly_sysPowC, T.toPoly_tX, map_mul, map_pow, hX]
    rw [← zpow_natCast, Int.toNat_of_nonneg hk]
    ring
  · have e : tpowL Fc ks m k c =
        (c.1, GPoly.mul (MO Fc ks m) c.2 (sysPowC (MO Fc ks m) (tX Fc ks m) (-k).toNat)) := by
      unfold tpowL; simp only [hk, ↓reduceIte]; rfl
    rw [e]
    simp only [GPoly.toPoly_mul, toPoly_sysPowC, T.toPoly_tX, map_mul, map_pow, hX]
    have e2 : k = -((-k).toNat : ℤ) := by rw [Int.toNat_of_nonneg (by omega)]; ring
    conv_rhs => rw [e2, zpow_neg, zpow_natCast]
    rw [div_mul_eq_div_div, div_eq_mul_inv _ (T.tau m ^ _)]

lemma toPoly_single (e : LC m) :
    GPoly.toPoly (T.MP m h1.of_succ) [e] = C ((T.MP m h1.of_succ).sem e) := by
  simp [GPoly.toPoly]

lemma sem_addOverT (htr : Transcendental (T.F m) (T.ts m)) (c : LC (m + 1)) (e : LC m)
    (hc : T.phi m (GPoly.toPoly (T.MP m h1.of_succ) c.2) ≠ 0) :
    (T.MPr (m + 1) h1).sem (addOverT Fc ks m c e) = (T.MPr (m + 1) h1).sem c +
      T.phi m (C ((T.MP m h1.of_succ).sem e)) / T.tau m := by
  have ht := T.tau_ne_zero m htr
  have hX : T.phi m X = T.tau m := rfl
  rw [MPr_sem, MPr_sem, T.sem_MP_succ, T.sem_MP_succ]
  unfold addOverT
  simp only [GPoly.toPoly_mul, GPoly.toPoly_add, T.toPoly_tX, map_mul, map_add, hX]
  have hs : GPoly.toPoly (T.MP m (fun i hi ↦ h1 i (by omega))) [e] =
      C ((T.MP m h1.of_succ).sem e) := T.toPoly_single m h1 e
  rw [hs]
  field_simp

lemma tpowL_zero_snd (c : LC (m + 1)) : (tpowL Fc ks m 0 c).2 = c.2 := by
  unfold tpowL; simp

variable {m}

lemma deriv_tau (hm : m < T.n) {η : LC m} (hk : ks m = .prim η) (h0 : T.Tr m) :
    (T.tau m)′ = T.phi m (C ((T.MP m h0).sem η)) := by
  rw [← T.phi_DzL m hm hk h0 X, DzL_eq]
  simp

lemma deriv_tau_zpow (hm : m < T.n) {η : LC m} (hk : ks m = .prim η) (h0 : T.Tr m)
    (htr : Transcendental (T.F m) (T.ts m)) (k : ℤ) :
    (T.tau m ^ k)′ = (k : T.F (m + 1)) * T.tau m ^ k / T.tau m * T.phi m (C ((T.MP m h0).sem η)) := by
  have ht := T.tau_ne_zero m htr
  rw [Derivation.leibniz_zpow, T.deriv_tau hm hk h0, zpow_sub₀ ht, zpow_one, zsmul_eq_mul,
    smul_eq_mul]
  ring

/-- **The derivation matrix of the rescaled basis.** -/
lemma rescale_deriv (hm : m < T.n) {η : LC m} (hk : ks m = .prim η)
    (htr : Transcendental (T.F m) (T.ts m)) (N : ℕ) (Mc : List (List (LC (m + 1)))) (r : ℕ → ℤ)
    (θw : ℕ → L)
    (hw : ∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) * θw j)
    (hden : ∀ i < N, ∀ j < N,
      T.phi m (GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2) ≠ 0) :
    ∀ i < N, (((T.tau m ^ (-r i) : T.F (m + 1)) : L) * θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem (((rescaleM Fc ks m η N Mc r).getD i []).getD j
        (MOr Fc ks (m + 1)).zero) : L) * (((T.tau m ^ (-r j) : T.F (m + 1)) : L) * θw j) := by
  intro i hi
  have ht := T.tau_ne_zero m htr
  set h0 := h1.of_succ
  set M1 := T.MPr (m + 1) h1
  set a := (T.MP m h0).sem η
  set Mw : ℕ → ℕ → T.F (m + 1) := fun i j ↦ M1.sem ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero)
  -- the coefficients
  have hcoef : ∀ j < N, M1.sem (((rescaleM Fc ks m η N Mc r).getD i []).getD j
      (MOr Fc ks (m + 1)).zero) * T.tau m ^ (-r j) =
      T.tau m ^ (-r i) * Mw i j + if i = j then (T.tau m ^ (-r i))′ else 0 := by
    intro j hj
    rw [rescaleM, NestTower.getD_range_map _ _ hi, NestTower.getD_range_map _ _ hj]
    split_ifs with hij
    · subst hij
      rw [T.sem_addOverT m h1 htr _ _ (by rw [tpowL_zero_snd]; exact hden i hi i hi),
        T.sem_tpowL m h1 htr, (T.MP m h0).sem_mul, T.sem_mcst m h0, T.deriv_tau_zpow hm hk h0 htr]
      have e1 : T.phi m (C (((-(r i : ℚ) : ℚ) : T.F m) * a)) =
          ((-(r i : ℚ) : ℚ) : T.F (m + 1)) * T.phi m (C a) := by
        rw [C_mul, map_mul]; congr 1; simp
      rw [e1, zpow_zero]
      push_cast
      field_simp
      ring
    · rw [T.sem_tpowL m h1 htr, mul_assoc, ← zpow_add₀ ht, add_zero]
      rw [show r j - r i + -r j = -r i by ring]
      ring
  have hco : (((T.tau m ^ (-r i) : T.F (m + 1)) : L))′ =
      (((T.tau m ^ (-r i))′ : T.F (m + 1)) : L) := rfl
  rw [Derivation.leibniz, hco, hw i hi, smul_eq_mul, smul_eq_mul, Finset.mul_sum]
  have hR : ∀ j ∈ Finset.range N,
      ((M1.sem (((rescaleM Fc ks m η N Mc r).getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) *
        (((T.tau m ^ (-r j) : T.F (m + 1)) : L) * θw j)) =
      ((T.tau m ^ (-r i) * Mw i j : T.F (m + 1)) : L) * θw j +
        (((if i = j then (T.tau m ^ (-r i))′ else 0 : T.F (m + 1))) : L) * θw j := by
    intro j hj
    rw [← mul_assoc, ← IntermediateField.coe_mul, hcoef j (Finset.mem_range.mp hj),
      IntermediateField.coe_add, add_mul]
  have hsingle : ∑ j ∈ Finset.range N,
      (((if i = j then (T.tau m ^ (-r i))′ else 0 : T.F (m + 1))) : L) * θw j =
      (((T.tau m ^ (-r i))′ : T.F (m + 1)) : L) * θw i := by
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [Ne.symm hj])
      (fun h ↦ absurd (Finset.mem_range.mpr hi) h)]
    simp
  rw [Finset.sum_congr rfl hR, Finset.sum_add_distrib, hsingle, mul_comm (θw i)]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  push_cast
  ring

lemma rescale_ind (htr : Transcendental (T.F m) (T.ts m)) (N : ℕ) (r : ℕ → ℤ) (θw : ℕ → L)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * θw j = 0 → ∀ j < N, a j = 0) :
    ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) *
      (((T.tau m ^ (-r j) : T.F (m + 1)) : L) * θw j) = 0 → ∀ j < N, a j = 0 := by
  intro a ha j hj
  have ht := T.tau_ne_zero m htr
  have := hind (fun j ↦ a j * T.tau m ^ (-r j)) (by
    rw [← ha]; refine Finset.sum_congr rfl fun j _ ↦ ?_; push_cast; ring) j hj
  exact (mul_eq_zero.mp this).resolve_right (zpow_ne_zero _ ht)

lemma rescale_rhs (htr : Transcendental (T.F m) (T.ts m)) (N : ℕ) (f : List (LC (m + 1)))
    (r : ℕ → ℤ) (θw : ℕ → L) :
    ∑ j ∈ Finset.range N, ((T.MPr (m + 1) h1).sem ((rescaleF Fc ks m N f r).getD j
      (MOr Fc ks (m + 1)).zero) : L) * (((T.tau m ^ (-r j) : T.F (m + 1)) : L) * θw j) =
    ∑ j ∈ Finset.range N, ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) *
      θw j := by
  have ht := T.tau_ne_zero m htr
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [rescaleF, NestTower.getD_range_map _ _ (Finset.mem_range.mp hj), T.sem_tpowL m h1 htr,
    ← mul_assoc, ← IntermediateField.coe_mul, mul_assoc, ← zpow_add₀ ht, add_neg_cancel, zpow_zero,
    mul_one]

set_option maxHeartbeats 3200000 in
/-- **Correctness of `exactWR`**: for any basis `w` with derivation matrix `Mc` and any shifts `r`,
an answer `res` says whether `∑ fⱼ wⱼ` has an antiderivative `∑ Yᵢ wᵢ`. -/
theorem exactWR_correct (hm : m < T.n) {η : LC m} (hk : ks m = .prim η)
    (htr : Transcendental (T.F m) (T.ts m)) (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h1.of_succ) lim)
    (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (r : ℕ → ℤ) (θw : ℕ → L)
    (hw : ∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) * θw j)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * θw j = 0 →
      ∀ j < N, a j = 0)
    (res : Bool) (hres : exactWR Fc ks m η lim N Mc f r = some res) :
    res = true ↔ ∃ Y : ℕ → T.F (m + 1),
      (∑ i ∈ Finset.range N, (Y i : L) * θw i)′ =
        ∑ j ∈ Finset.range N,
          ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) * θw j := by
  classical
  unfold exactWR at hres
  simp only at hres
  split_ifs at hres with hN0 hcof
  split at hres
  · exact absurd hres (by simp)
  rename_i B hB
  set O1 := MOr Fc ks (m + 1) with hO1
  set O := MO Fc ks m with hO
  set M1 := T.MPr (m + 1) h1 with hM1
  set h0 := h1.of_succ with hh0
  set M := T.MP m h0 with hM
  set Ml : List (List (LC (m + 1))) := (List.range N).map fun i ↦
    (List.range N).map fun j ↦ (Mc.getD i []).getD j O1.zero with hMl
  set Mw : ℕ → ℕ → T.F (m + 1) := fun i j ↦ M1.sem ((Mc.getD i []).getD j O1.zero) with hMw
  set ent : List (LC (m + 1)) := Ml.flatten with hent
  set q := lcmGL O (ent.map Prod.snd) with hq
  set hq := lcmGL O (f.map Prod.snd) with hhq
  set num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2 with hnum
  set numF : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O hq c.2).2 with hnumF
  have hcof2 : (ent.map fun c ↦ cofC O q c.2).all Prod.fst = true ∧
      (f.map fun c ↦ cofC O hq c.2).all Prod.fst = true ∧ isMonicC O q = true ∧
      isMonicC O hq = true := by
    revert hcof
    cases (ent.map fun c ↦ cofC O q c.2).all Prod.fst <;>
      cases (f.map fun c ↦ cofC O hq c.2).all Prod.fst <;> cases isMonicC O q <;>
      cases isMonicC O hq <;> simp
  have hqM := isMonicC_spec M q hcof2.2.2.1
  have hhM := isMonicC_spec M hq hcof2.2.2.2
  set qs := GPoly.toPoly M q with hqs
  set hs := GPoly.toPoly M hq with hhs
  have hqs0 : qs ≠ 0 := hqM.ne_zero
  have hhs0 : hs ≠ 0 := hhM.ne_zero
  have hcofs : ∀ c ∈ ent, (cofC O q c.2).1 = true := fun c hc ↦
    List.all_eq_true.mp hcof2.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hcofsF : ∀ c ∈ f, (cofC O hq c.2).1 = true := fun c hc ↦
    List.all_eq_true.mp hcof2.2.1 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hval : ∀ c ∈ ent, (M1.sem c : T.F (m + 1)) = T.phi m (GPoly.toPoly M (num c)) / T.phi m qs :=
    fun c hc ↦ T.sem_cof m h1 htr q hqs0 c (hcofs c hc)
  have hvalF : ∀ c ∈ f, (M1.sem c : T.F (m + 1)) = T.phi m (GPoly.toPoly M (numF c)) / T.phi m hs :=
    fun c hc ↦ T.sem_cof m h1 htr hq hhs0 c (hcofsF c hc)
  have hMe : ∀ i < N, ∀ j < N, (Ml.getD i []).getD j O1.zero ∈ ent := fun i hi j hj ↦ by
    rw [hent, List.mem_flatten]
    refine ⟨Ml.getD i [], ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by simpa [hMl] using hi)]; exact List.getElem_mem _
    · have hlen : j < (Ml.getD i []).length := by
        rw [hMl, NestTower.getD_range_map _ _ hi]; simpa using hj
      rw [List.getD_eq_getElem (Ml.getD i []) _ hlen]; exact List.getElem_mem _
  have hMlij : ∀ i < N, ∀ j < N, (Ml.getD i []).getD j O1.zero = (Mc.getD i []).getD j O1.zero :=
    fun i hi j hj ↦ by rw [hMl, NestTower.getD_range_map _ _ hi, NestTower.getD_range_map _ _ hj]
  have hMθ : ∀ i < N, ∀ j < N, Mw i j =
      T.phi m (GPoly.toPoly M (num ((Ml.getD i []).getD j O1.zero))) / T.phi m qs := by
    intro i hi j hj
    rw [← hval _ (hMe i hi j hj), hMlij i hi j hj]
  have hfv : ∀ j, (M1.sem (f.getD j O1.zero) : T.F (m + 1)) =
      T.phi m (GPoly.toPoly M (numF (f.getD j O1.zero))) / T.phi m hs := by
    intro j
    by_cases hj : j < f.length
    · refine hvalF _ ?_
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
    · rw [List.getD_eq_default _ _ (by omega)]
      have hz : O1.zero.1 = [] := rfl
      rw [M1.sem_zero, hnumF]
      simp only [hz, GPoly.mul, GPoly.toPoly_nil, map_zero, zero_div]
  -- the denominators of the matrix entries
  have hden : ∀ i < N, ∀ j < N,
      T.phi m (GPoly.toPoly M ((Mc.getD i []).getD j O1.zero).2) ≠ 0 := by
    intro i hi j hj h0'
    have hc := hcofs _ (hMe i hi j hj)
    rw [hMlij i hi j hj] at hc
    have hd0 : GPoly.toPoly M ((Mc.getD i []).getD j O1.zero).2 = 0 :=
      T.phi_injective htr (by rw [h0', map_zero])
    have hs' := GPoly.divMod_spec M q ((Mc.getD i []).getD j O1.zero).2
    have hr0 := (GPoly.isZero_iff M _).mp hc
    rw [hr0, add_zero, hd0, mul_zero] at hs'
    exact hqs0 hs'
  set A0f : Fin N → Fin N → GPoly (LC m) := fun j i ↦ num ((Ml.getD i []).getD j O1.zero) with hA0f
  set Gf : Fin N → GPoly (LC m) := fun j ↦ numF (f.getD j O1.zero) with hGf
  -- the rescaled basis
  set θt : ℕ → L := fun i ↦ ((T.tau m ^ (-r i) : T.F (m + 1)) : L) * θw i with hθt
  have hwt := T.rescale_deriv h1 hm hk htr N Mc r θw hw hden
  have hindt := T.rescale_ind htr N r θw hind
  have hspec := T.primSpecB hm h0 hk lim hlim
  obtain ⟨ha, hb⟩ := T.exactWE_correct m h1 htr _ ((T.MP m h0).sem η) 0 hspec N
    (rescaleM Fc ks m η N Mc r) (rescaleF Fc ks m N f r) _ θt hwt hindt res hres
  have hrhs := T.rescale_rhs h1 htr N f r θw
  have hsumY : ∀ Y : ℕ → T.F (m + 1), ∑ i ∈ Finset.range N, (Y i : L) * θt i =
      ∑ i ∈ Finset.range N, ((Y i * T.tau m ^ (-r i) : T.F (m + 1)) : L) * θw i := fun Y ↦
    Finset.sum_congr rfl fun i _ ↦ by simp only [hθt]; push_cast; ring
  constructor
  · intro hrt
    obtain ⟨Y, hY⟩ := ha hrt
    refine ⟨fun i ↦ Y i * T.tau m ^ (-r i), ?_⟩
    rw [← hsumY, ← hrhs]
    exact hY
  · rintro ⟨Y, hY⟩
    -- the denominator bound in the basis `w`
    have hcoord : ∀ j < N, (Y j)′ + ∑ i ∈ Finset.range N, Mw i j * Y i =
        M1.sem (f.getD j O1.zero) := by
      have hdc := T.deriv_coordsW m N θw Mw hw Y
      rw [hdc] at hY
      intro j hj
      have h0' := hind (fun j ↦ (Y j)′ + ∑ i ∈ Finset.range N, Mw i j * Y i -
        M1.sem (f.getD j O1.zero)) (by
          push_cast
          simp only [sub_mul, Finset.sum_sub_distrib]
          rw [← hY]
          push_cast
          simp only [add_mul, Finset.sum_mul]
          ring) j hj
      exact sub_eq_zero.mp h0'
    obtain ⟨Z, d, hd0, hZ⟩ := T.exists_common_den m htr (fun i : Fin N ↦ Y i)
    have hphid : T.phi m d ≠ 0 := fun h0' ↦ hd0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hphiq : T.phi m qs ≠ 0 := fun h0' ↦ hqs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hphih : T.phi m hs ≠ 0 := fun h0' ↦ hhs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hYi : ∀ i : Fin N, Y i = T.phi m (Z i) / T.phi m d := fun i ↦ by
      rw [← hZ i, mul_div_cancel_right₀ _ hphid]
    have hsol : SysSol ((T.MP m h0).sem η) 0 qs hs (semMat M A0f) (fun j ↦ GPoly.toPoly M (Gf j)) Z d := by
      refine T.sysSol_of_phiG m htr _ 0 (T.phi_DzL m hm hk h0) qs hs (semMat M A0f) _ Z d fun j ↦ ?_
      have hj := hcoord j j.2
      rw [← Fin.sum_univ_eq_sum_range (fun i ↦ Mw i j * Y i)] at hj
      have hMθ' : ∀ i : Fin N, Mw i j = T.phi m (GPoly.toPoly M (A0f j i)) / T.phi m qs :=
        fun i ↦ hMθ i i.2 j j.2
      simp only [hMθ', hYi, hfv] at hj
      rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul] at hj
      simp only [semMat, Matrix.of_apply]
      have hsum : ∑ x, T.phi m (GPoly.toPoly M (A0f j x)) / T.phi m qs *
          (T.phi m (Z x) / T.phi m d) =
          (∑ x, T.phi m (GPoly.toPoly M (A0f j x)) * T.phi m (Z x)) / (T.phi m qs * T.phi m d) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun x _ ↦ by field_simp
      rw [hsum, smul_eq_mul] at hj
      have hG' : GPoly.toPoly M (Gf j) = GPoly.toPoly M (numF (f.getD (↑j) O1.zero)) := rfl
      rw [hG']
      field_simp at hj
      linear_combination hj
    have hindB : ∀ (p : (T.F m)[X]) (e : ℕ), Irreducible p → p ∣ qs →
        p ∣ (Matrix.of fun i j ↦ semMat M A0f i j - if i = j then
          C (e : T.F m) * DzL ((T.MP m h0).sem η) 0 qs else 0).det → e ≤ B :=
      fun p e hp hpq hdet ↦ T.indBound2_spec m h0 (degG O q) N q (DzLC O η O.zero q) A0f hqM
        (degG_eq M q).symm B hB e p hp hpq (by rwa [toPoly_DzLC, M.sem_zero])
    have hdvd := fun i ↦ sys_den_bound ((T.MP m h0).sem η) 0 qs hs hhs0 (semMat M A0f) _ B hindB
      Z d hd0 hsol 1 (fun p e hp hpd _ ↦ absurd hpd (T.not_dvd_DzL m h0 η hm htr hk p hp)) i
    choose u hu using hdvd
    -- the bound for the rescaled coordinates
    set R := ((List.range N).map fun i ↦ (-r i).toNat).foldr max 0 with hR
    have hRi : ∀ i < N, (-r i).toNat ≤ R := fun i hi ↦
      Tower.Sys.le_foldr_max _ _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    refine hb ⟨fun i ↦ Y i * T.tau m ^ r i, fun i ↦ if hi : i < N then
      u ⟨i, hi⟩ * X ^ (R - (-r i).toNat + (r i).toNat) else 0, fun i hi ↦ ?_, ?_⟩
    · simp only [dif_pos hi]
      have hE : GPoly.toPoly M (GPoly.mul O (GPoly.mul O hq (sysPowC O q B))
          (sysPowC O (tX Fc ks m) R)) = hs * qs ^ B * X ^ R := by
        rw [GPoly.toPoly_mul, GPoly.toPoly_mul, toPoly_sysPowC, toPoly_sysPowC, T.toPoly_tX]
      rw [hE, map_mul, map_mul, map_pow, map_mul, map_pow, map_pow]
      have hui := hu ⟨i, hi⟩
      rw [mul_one] at hui
      have hX : T.phi m X = T.tau m := rfl
      rw [hX, hYi ⟨i, hi⟩]
      have e1 : T.phi m (Z ⟨i, hi⟩) * (T.phi m hs * T.phi m qs ^ B) = T.phi m d * T.phi m (u ⟨i, hi⟩) := by
        rw [← map_pow, ← map_mul, ← map_mul, ← map_mul, ← hui]; ring_nf
      have ht := T.tau_ne_zero m htr
      have e2 : T.tau m ^ r i * T.tau m ^ R = T.tau m ^ (R - (-r i).toNat + (r i).toNat) := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ht]
        congr 1
        have := hRi i hi
        omega
      calc T.phi m (Z ⟨i, hi⟩) / T.phi m d * T.tau m ^ r i * (T.phi m hs * T.phi m qs ^ B * T.tau m ^ R)
          = (T.phi m (Z ⟨i, hi⟩) * (T.phi m hs * T.phi m qs ^ B)) / T.phi m d *
            (T.tau m ^ r i * T.tau m ^ R) := by ring
        _ = T.phi m (u ⟨i, hi⟩) * T.tau m ^ (R - (-r i).toNat + (r i).toNat) := by
          rw [e1, e2]; field_simp
    · rw [hsumY, hrhs]
      convert hY using 2
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [mul_assoc, ← zpow_add₀ (T.tau_ne_zero m htr), add_neg_cancel, zpow_zero, mul_one]

lemma tpowL_snd_ne_zero (k : ℤ) (c : LC (m + 1))
    (hc : GPoly.toPoly (T.MP m h1.of_succ) c.2 ≠ 0) :
    GPoly.toPoly (T.MP m h1.of_succ) (tpowL Fc ks m k c).2 ≠ 0 := by
  by_cases hk : 0 ≤ k
  · have e : (tpowL Fc ks m k c).2 = c.2 := by unfold tpowL; simp only [hk, ↓reduceIte]
    rw [e]; exact hc
  · have e : (tpowL Fc ks m k c).2 =
        GPoly.mul (MO Fc ks m) c.2 (sysPowC (MO Fc ks m) (tX Fc ks m) (-k).toNat) := by
      unfold tpowL; simp only [hk, ↓reduceIte]
    rw [e, GPoly.toPoly_mul, T.toPoly_tpow m h1]
    exact mul_ne_zero hc (pow_ne_zero _ X_ne_zero)

/-- **`exactWR` answers** when the denominators of the matrix of `w` are squarefree, the rescaled
matrix vanishes at infinity and `η` is not a derivative (an integral basis normal at infinity). -/
theorem exactWR_isSome (hm : m < T.n) {η : LC m} (hk : ks m = .prim η)
    (htr : Transcendental (T.F m) (T.ts m)) (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h1.of_succ) lim)
    (hη : ∀ y : T.F m, y′ ≠ (T.MP m h1.of_succ).sem η)
    (N : ℕ) (hN : N ≠ 0) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (r : ℕ → ℤ)
    (hent : ∀ i < N, ∀ j < N,
      GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2 ≠ 0 ∧
      Squarefree (GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2))
    (hprop : ∀ i < N, ∀ j < N,
      (GPoly.toPoly (T.MP m h1.of_succ)
        (((rescaleM Fc ks m η N Mc r).getD i []).getD j (MOr Fc ks (m + 1)).zero).1).degree <
      (GPoly.toPoly (T.MP m h1.of_succ)
        (((rescaleM Fc ks m η N Mc r).getD i []).getD j (MOr Fc ks (m + 1)).zero).2).degree)
    (hf : ∀ c ∈ f, GPoly.toPoly (T.MP m h1.of_succ) c.2 ≠ 0) :
    (exactWR Fc ks m η lim N Mc f r).isSome := by
  set h0 := h1.of_succ with hh0
  set O := MO Fc ks m with hO
  set P := T.MP m h0 with hP
  set O1 := MOr Fc ks (m + 1) with hO1
  set Mm : List (List (LC (m + 1))) := (List.range N).map fun i ↦
    (List.range N).map fun j ↦ (Mc.getD i []).getD j O1.zero with hMm
  have hent' : ∀ c ∈ Mm.flatten, GPoly.toPoly P c.2 ≠ 0 ∧ Squarefree (GPoly.toPoly P c.2) := by
    intro c hc
    obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hcl
    exact hent i (List.mem_range.mp hi) j (List.mem_range.mp hj)
  set q := lcmGL O (Mm.flatten.map Prod.snd) with hq
  set hh := lcmGL O (f.map Prod.snd) with hhh
  obtain ⟨hqm, hqd, hqs⟩ := lcmGL_spec P (Mm.flatten.map Prod.snd) (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact (hent' c hc).1)
  obtain ⟨hhm, hhd, -⟩ := lcmGL_spec P (f.map Prod.snd) (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact hf c hc)
  have hsq : Squarefree (GPoly.toPoly P q) := hqs (by
    intro d hd; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd; exact (hent' c hc).2)
  have hcheck : ((Mm.flatten.map fun c ↦ cofC O q c.2).all Prod.fst &&
      (f.map fun c ↦ cofC O hh c.2).all Prod.fst && isMonicC O q && isMonicC O hh) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_map]
    refine ⟨⟨⟨?_, ?_⟩, isMonicC_of_monic P q hqm⟩, isMonicC_of_monic P hh hhm⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact cofC_fst P q c.2 (hent' c hc).1 (hqd _ (List.mem_map_of_mem hc))
    · rintro _ ⟨c, hc, rfl⟩
      exact cofC_fst P hh c.2 (hf c hc) (hhd _ (List.mem_map_of_mem hc))
  set A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦
    GPoly.mul O ((Mm.getD i []).getD j O1.zero).1 (cofC O q ((Mm.getD i []).getD j O1.zero).2).2
    with hA0
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp
    (T.indBound2_isSome m h0 (degG O q) N q (DzLC O η O.zero q) A0 hqm (degG_eq P q).symm
      (T.not_dvd_DzLC_of_squarefree m h0 η hm htr hk q hsq))
  set R := ((List.range N).map fun i ↦ (-r i).toNat).foldr max 0 with hR
  set E := GPoly.mul O (GPoly.mul O hh (sysPowC O q B)) (sysPowC O (tX Fc ks m) R) with hE
  have hE0 : GPoly.toPoly P E ≠ 0 := by
    rw [hE, GPoly.toPoly_mul, GPoly.toPoly_mul, toPoly_sysPowC, toPoly_sysPowC, T.toPoly_tX]
    exact mul_ne_zero (mul_ne_zero hhm.ne_zero (pow_ne_zero _ hqm.ne_zero))
      (pow_ne_zero _ X_ne_zero)
  have hWE := T.exactWE_isSome m h0 η lim hlim hη N hN (rescaleM Fc ks m η N Mc r)
    (rescaleF Fc ks m N f r) (fun i hi j hj ↦ ⟨fun h0' ↦ by
        have := hprop i hi j hj
        rw [h0', degree_zero] at this
        exact absurd this (not_lt_bot), hprop i hi j hj⟩)
    (by
      intro c hc
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
      refine T.tpowL_snd_ne_zero h1 _ _ ?_
      by_cases hjf : j < f.length
      · exact hf _ (by rw [List.getD_eq_getElem _ _ hjf]; exact List.getElem_mem _)
      · rw [List.getD_eq_default _ _ (by omega)]
        show GPoly.toPoly P [O.one] ≠ 0
        simp only [GPoly.toPoly, hO, P.sem_one]; simp)
    E hE0
  unfold exactWR
  simp only [hN, ↓reduceIte]
  rw [← hO1, ← hO, ← hMm, ← hq, ← hhh]
  simp only [hcheck, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [← hA0, hB]
  exact hWE

end MTower

end Curves.MT
