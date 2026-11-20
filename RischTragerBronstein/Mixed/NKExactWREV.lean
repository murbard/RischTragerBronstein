import RischTragerBronstein.Mixed.NKExactWRE
import RischTragerBronstein.Mixed.SysExpV
import RischTragerBronstein.Computable.SysDenTV

/-!
# The exact part over an exponential level for non-constant curves

`exactWREV`: as `exactWRE`, for a basis whose limits are not rational:

* at `t = 0` the value `M₀ = A₀(0)/q(0)` is made upper triangular by a gauge transformation `C`
  (codes, inverse `C⁻¹` checked): `C M₀ C⁻¹ − C′ C⁻¹` upper triangular with diagonal
  `pᵢ a′ + qᵢ cᵢ′/cᵢ`, `pᵢ` not a positive integer (`zeroOKV`), so solutions have no pole at `t = 0`
  beyond the right-hand side (`sys_den_special_gauge`);
* at infinity the rescaled matrix (`rescaleME`) has an upper triangular limit with diagonal given by
  `dg`, handled by the solver `expSysV`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- An entry of a matrix of codes. -/
def cget (m : ℕ) (C : List (List (LC m))) (i j : ℕ) : LC m := (C.getD i []).getD j (MO Fc ks m).zero

/-- The value `A₀(0)/q(0)` at `t = 0`. -/
def m0E (m N : ℕ) (q : GPoly (LC m)) (A0 : Fin N → Fin N → GPoly (LC m)) (i j : Fin N) : LC m :=
  (MO Fc ks m).mul ((A0 i j).getD 0 (MO Fc ks m).zero) ((MO Fc ks m).inv (q.getD 0 (MO Fc ks m).zero))

/-- The gauge transform `C M₀ C⁻¹ − C′ C⁻¹`. -/
def gaugeT (m N : ℕ) (q : GPoly (LC m)) (A0 : Fin N → Fin N → GPoly (LC m))
    (C Ci : List (List (LC m))) (i j : Fin N) : LC m :=
  let O := MO Fc ks m
  O.add (lsumC O ((List.finRange N).map fun k : Fin N ↦ lsumC O ((List.finRange N).map fun l : Fin N ↦
      O.mul (O.mul (cget Fc ks m C i k) (m0E Fc ks m N q A0 k l)) (cget Fc ks m Ci l j))))
    (O.neg (lsumC O ((List.finRange N).map fun k : Fin N ↦
      O.mul (O.deriv (cget Fc ks m C i k)) (cget Fc ks m Ci k j))))

/-- `C C⁻¹ = C⁻¹ C = 1` on codes. -/
def cmatOK (m N : ℕ) (C Ci : List (List (LC m))) : Bool :=
  let O := MO Fc ks m
  (List.finRange N).all fun i : Fin N ↦ (List.finRange N).all fun j : Fin N ↦
    O.isZero (O.add (lsumC O ((List.finRange N).map fun k : Fin N ↦
      O.mul (cget Fc ks m C i k) (cget Fc ks m Ci k j))) (O.neg (if i = j then O.one else O.zero))) &&
    O.isZero (O.add (lsumC O ((List.finRange N).map fun k : Fin N ↦
      O.mul (cget Fc ks m Ci i k) (cget Fc ks m C k j))) (O.neg (if i = j then O.one else O.zero)))

/-- **The checks at `t = 0`**: `C` invertible, `C M₀ C⁻¹ − C′ C⁻¹` upper triangular with diagonal
`fCode (frE a 0 dg0ᵢ)`, `p⁰ᵢ` not a positive integer. -/
def zeroOKV (m : ℕ) (a : LC m) (N : ℕ) (q : GPoly (LC m)) (A0 : Fin N → Fin N → GPoly (LC m))
    (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m)) : Bool :=
  let O := MO Fc ks m
  cmatOK Fc ks m N C Ci &&
  (List.finRange N).all fun i : Fin N ↦ (List.finRange N).all fun j : Fin N ↦
    (decide (j < i) → O.isZero (gaugeT Fc ks m N q A0 C Ci i j)) &&
    (decide (i = j) → O.isZero (O.add (gaugeT Fc ks m N q A0 C Ci i i)
      (O.neg (fCode O (frE Fc ks m a 0 (dgEAt Fc ks m dg0 (i : ℕ))))))) &&
    decide ((dgEAt Fc ks m dg0 (i : ℕ)).1.den ≠ 1 ∨ (dgEAt Fc ks m dg0 (i : ℕ)).1 ≤ 0)

/-- **The exact-part test at an exponential level for non-constant curves.** -/
def exactWREV (m : ℕ) (a : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (ℚ × ℚ × LC m)) (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1)))
    (r : ℕ → ℤ) (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m)) : Option Bool :=
  let O1 := MOr Fc ks (m + 1)
  let O := MO Fc ks m
  let bc := O.deriv a
  if N = 0 then none else
    let M : List (List (LC (m + 1))) := (List.range N).map fun i ↦
      (List.range N).map fun j ↦ (Mc.getD i []).getD j O1.zero
    let ent : List (LC (m + 1)) := M.flatten
    let q := lcmGL O (ent.map Prod.snd)
    let hq := lcmGL O (f.map Prod.snd)
    if !((ent.map fun c ↦ cofC O q c.2).all Prod.fst && (f.map fun c ↦ cofC O hq c.2).all Prod.fst &&
        isMonicC O q && isMonicC O hq) then none
    else
    if O.isZero (q.getD 0 O.zero) then none else
    let A0 : Fin N → Fin N → GPoly (LC m) := fun j i ↦
      GPoly.mul O ((M.getD i []).getD j O1.zero).1 (cofC O q ((M.getD i []).getD j O1.zero).2).2
    if !(zeroOKV Fc ks m a N q A0 C Ci dg0) then none
    else
    match indBound2 Fc ks m (degG O q) N q (DzLC O O.zero bc q) A0 with
    | none => none
    | some B =>
      let R := ((List.range N).map fun i ↦ (-r i).toNat).foldr max 0
      let E := GPoly.mul O (GPoly.mul O hq (sysPowC O q B)) (sysPowC O (tX Fc ks m) R)
      exactWE Fc ks m (fun n A0 q hh G0 ↦ expSysV Fc ks m a rde dg n A0 q hh G0 0) N
        ((rescaleME Fc ks m bc N Mc r).map fun l ↦ l.map (redC Fc ks m))
        ((rescaleF Fc ks m N f r).map (redC Fc ks m)) E

/-- A successful `expSysV` has monic `q`, `h` and the `W`-system denominator. -/
lemma expSysV_some {m : ℕ} {a : LC m} {rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m)}
    {dg : List (ℚ × ℚ × LC m)} {n : ℕ}
    {A0 : Fin n → Fin n → GPoly (LC m)} {q hq : GPoly (LC m)} {G0 : List (Fin n → GPoly (LC m))}
    {B : ℕ} {r : GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))}
    (hres : expSysV Fc ks m a rde dg n A0 q hq G0 B = some r) :
    isMonicC (MO Fc ks m) q = true ∧ isMonicC (MO Fc ks m) hq = true ∧
      r.1 = (wSysE Fc ks m ((MO Fc ks m).deriv a) n A0 q hq G0 B).Den := by
  unfold expSysV at hres
  simp only [matFn_matData] at hres
  split_ifs at hres with hmon
  have : (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hq) = true := by
    revert hmon; cases (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hq) <;> simp
  exact ⟨(Bool.and_eq_true_iff.mp this).1, (Bool.and_eq_true_iff.mp this).2,
    by rw [← Option.some.inj hres]⟩

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable {m : ℕ}

/-- **`expSysV … 0` meets the solver specification with known denominators.** -/
theorem expSpecV (hm : m < T.n) (h0 : T.Tr m) {a : LC m} (hk : ks m = .exp a)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h0) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h0) ((T.MP m h0).sem (fCode (MO Fc ks m) fr))
        (rde fr))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h0).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (dg : List (ℚ × ℚ × LC m)) :
    T.SolverSpecB m h0 0 ((T.MP m h0).sem ((MO Fc ks m).deriv a))
      (fun n A0 q hh G0 ↦ expSysV Fc ks m a rde dg n A0 q hh G0 0) where
  hD := T.phi_DzL_exp m hm hk h0
  sound := fun n A0 q hh G0 Den out hres ↦
    T.expSysV_sound m h0 n A0 q hh G0 0 a rde dg Den out hres
  den := fun n A0 q hh G0 r hres ↦ by
    obtain ⟨hm1, hm2, hB⟩ := expSysV_some (Fc := Fc) (ks := ks) hres
    have hq := (isMonicC_spec (T.MP m h0) q hm1).ne_zero
    have hh' := (isMonicC_spec (T.MP m h0) hh hm2).ne_zero
    refine ⟨?_, hq, hh'⟩
    rw [hB, T.wSysE_Den m h0 ((MO Fc ks m).deriv a) n A0 q hh G0 0]
    exact mul_ne_zero hh' (pow_ne_zero _ hq)
  complete := fun n A0 q hh G0 Den out hres c hc Z d hd hsol hdvd ↦
    T.expSysV_complete m h0 n A0 q hh G0 0 a rde hrde dg hom Den out hres c hc Z d hd hsol
      (fun i ↦ by rw [pow_zero, mul_one]; exact hdvd i)

lemma sem_lsumC_finRange {N : ℕ} (h0 : T.Tr m) (g : Fin N → LC m) :
    (T.MP m h0).sem (lsumC (MO Fc ks m) ((List.finRange N).map g)) = ∑ k, (T.MP m h0).sem (g k) := by
  rw [sem_lsumC, List.map_map, Fin.sum_univ_def]
  rfl

/-- **The meaning of the checks at `t = 0`.** -/
lemma zeroOKV_spec (h0 : T.Tr m) (a : LC m) (N : ℕ) (q : GPoly (LC m))
    (A0 : Fin N → Fin N → GPoly (LC m)) (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m))
    (hz : zeroOKV Fc ks m a N q A0 C Ci dg0 = true)
    (hq0 : (GPoly.toPoly (T.MP m h0) q).coeff 0 ≠ 0) :
    (∀ i j, (GPoly.toPoly (T.MP m h0) (A0 i j)).coeff 0 =
      (GPoly.toPoly (T.MP m h0) q).coeff 0 * (T.MP m h0).sem (m0E Fc ks m N q A0 i j)) ∧
    (Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m Ci i j)) *
      (Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m C i j)) = 1 ∧
    (∀ i j, (T.MP m h0).sem (gaugeT Fc ks m N q A0 C Ci i j) =
      ((Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m C i j)) *
        Matrix.of (fun i j ↦ (T.MP m h0).sem (m0E Fc ks m N q A0 i j)) *
        (Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m Ci i j)) -
        (Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m C i j)).map (fun z ↦ z′) *
        (Matrix.of fun i j : Fin N ↦ (T.MP m h0).sem (cget Fc ks m Ci i j))) i j) ∧
    (∀ i j : Fin N, j < i → (T.MP m h0).sem (gaugeT Fc ks m N q A0 C Ci i j) = 0) ∧
    (∀ i : Fin N, (T.MP m h0).sem (gaugeT Fc ks m N q A0 C Ci i i) =
      ((dgEAt Fc ks m dg0 (i : ℕ)).1 : T.F m) * (T.MP m h0).sem ((MO Fc ks m).deriv a) +
      ((dgEAt Fc ks m dg0 (i : ℕ)).2.1 : T.F m) *
        (((T.MP m h0).sem (dgEAt Fc ks m dg0 (i : ℕ)).2.2)′ /
          (T.MP m h0).sem (dgEAt Fc ks m dg0 (i : ℕ)).2.2)) ∧
    (∀ (i : Fin N) (k : ℕ), 0 < k → (dgEAt Fc ks m dg0 (i : ℕ)).1 ≠ k) := by
  classical
  unfold zeroOKV at hz
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hz
  obtain ⟨hC, hz⟩ := hz
  unfold cmatOK at hC
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at hC
  refine ⟨fun i j ↦ ?_, ?_, fun i j ↦ ?_, fun i j hji ↦ ?_, fun i ↦ ?_, fun i k hk hpk ↦ ?_⟩
  · rw [m0E, (T.MP m h0).sem_mul, (T.MP m h0).sem_inv, coeff_toPoly_sem, coeff_toPoly_sem]
    rw [coeff_toPoly_sem] at hq0
    field_simp
  · refine Matrix.ext fun i j ↦ ?_
    have h := ((T.MP m h0).isZero_iff _).mp (hC i j).2
    rw [(T.MP m h0).sem_add, (T.MP m h0).sem_neg, T.sem_lsumC_finRange h0, add_neg_eq_zero] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply, ← (T.MP m h0).sem_mul]
    rw [h]
    split_ifs
    · exact (T.MP m h0).sem_one
    · exact (T.MP m h0).sem_zero
  · rw [gaugeT]
    rw [(T.MP m h0).sem_add, (T.MP m h0).sem_neg, T.sem_lsumC_finRange h0, T.sem_lsumC_finRange h0]
    simp only [T.sem_lsumC_finRange h0, (T.MP m h0).sem_mul, (T.MP m h0).sem_deriv, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.of_apply, Matrix.map_apply, Finset.sum_mul]
    rw [sub_eq_add_neg]
    congr 1
    rw [Finset.sum_comm]
  · have := (hz i j).1.1 hji
    exact ((T.MP m h0).isZero_iff _).mp this
  · have h := ((T.MP m h0).isZero_iff _).mp ((hz i i).1.2 rfl)
    rw [(T.MP m h0).sem_add, (T.MP m h0).sem_neg, add_neg_eq_zero, sem_fCode, frE] at h
    simp only [logSumV, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
    rw [h, (T.MP m h0).sem_mul, T.sem_mcst m h0, Derivation.leibniz, T.deriv_ratCast, smul_zero, add_zero,
      smul_eq_mul, T.sem_mcst m h0, Differential.logDeriv, (T.MP m h0).sem_deriv]
    push_cast; ring
  · have h := (hz i i).2
    rcases h with h | h
    · rw [hpk] at h; simp at h
    · rw [hpk] at h
      have : (0 : ℚ) < k := by exact_mod_cast hk
      linarith

variable (h1 : T.Tr (m + 1))

set_option maxHeartbeats 3200000 in
/-- **Correctness of `exactWREV`**: for any basis `w` with derivation matrix `Mc`, shifts `r`,
diagonal data and gauge `C` at `t = 0`, an answer `res` says whether `∑ fⱼ wⱼ` has an
antiderivative `∑ Yᵢ wᵢ`. -/
theorem exactWREV_correct (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m))
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h1.of_succ) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
        ((T.MP m h1.of_succ).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (dg : List (ℚ × ℚ × LC m))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (r : ℕ → ℤ)
    (C Ci : List (List (LC m))) (dg0 : List (ℚ × ℚ × LC m)) (θw : ℕ → L)
    (hw : ∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) * θw j)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * θw j = 0 →
      ∀ j < N, a j = 0)
    (res : Bool) (hres : exactWREV Fc ks m a rde dg N Mc f r C Ci dg0 = some res) :
    res = true ↔ ∃ Y : ℕ → T.F (m + 1),
      (∑ i ∈ Finset.range N, (Y i : L) * θw i)′ =
        ∑ j ∈ Finset.range N,
          ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) * θw j := by
  classical
  unfold exactWREV at hres
  simp only at hres
  split_ifs at hres with hN0 hcof hq0c hzc
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
  -- the checks at `t = 0`
  set b := (T.MP m h0).sem ((MO Fc ks m).deriv a) with hb
  have hq0 : qs.coeff 0 ≠ 0 := by
    rw [hqs, coeff_toPoly_sem]
    intro h0'
    exact hq0c ((M.isZero_iff _).mpr h0')
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hzc
  obtain ⟨hA0z, hCiC, hTg, htriT, hdiagT, hpT⟩ := T.zeroOKV_spec h0 a N q _ C Ci dg0 hzc hq0
  set A0f : Fin N → Fin N → GPoly (LC m) := fun j i ↦ num ((Ml.getD i []).getD j O1.zero) with hA0f
  set Gf : Fin N → GPoly (LC m) := fun j ↦ numF (f.getD j O1.zero) with hGf
  -- the rescaled basis
  set θt : ℕ → L := fun i ↦ ((T.tau m ^ (-r i) : T.F (m + 1)) : L) * θw i with hθt
  have hwt0 := T.rescale_derivE h1 hm hk htr N Mc r θw hw hden
  have hwt : ∀ k < N, (θt k)′ = ∑ l ∈ Finset.range N, ((T.MPr (m + 1) h1).sem
      ((((rescaleME Fc ks m ((MO Fc ks m).deriv a) N Mc r).map fun l ↦
        l.map (redC Fc ks m)).getD k []).getD l (MOr Fc ks (m + 1)).zero) : L) * θt l := by
    intro k hk
    rw [hwt0 k hk]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [getD_map_map_redC (Fc := Fc) (ks := ks) m, T.sem_getD_map_redC m h1 htr]
  have hindt := T.rescale_ind htr N r θw hind
  have hspec := T.expSpecV hm h0 hk rde hrde hom dg
  obtain ⟨ha, hb'⟩ := T.exactWE_correct m h1 htr _ 0 b hspec N _ _ _ θt hwt hindt res hres
  have hrhs : ∑ l ∈ Finset.range N, ((T.MPr (m + 1) h1).sem
      (((rescaleF Fc ks m N f r).map (redC Fc ks m)).getD l (MOr Fc ks (m + 1)).zero) : L) * θt l =
      ∑ j ∈ Finset.range N, ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) *
        θw j := by
    simp only [T.sem_getD_map_redC m h1 htr]
    exact T.rescale_rhs h1 htr N f r θw
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
    have hsol : SysSol 0 b qs hs (semMat M A0f) (fun j ↦ GPoly.toPoly M (Gf j)) Z d := by
      refine T.sysSol_of_phiG m htr 0 b (T.phi_DzL_exp m hm hk h0) qs hs (semMat M A0f) _ Z d fun j ↦ ?_
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
          Polynomial.C (e : T.F m) * DzL 0 b qs else 0).det → e ≤ B :=
      fun p e hp hpq hdet ↦ T.indBound2_spec m h0 (degG O q) N q (DzLC O O.zero ((MO Fc ks m).deriv a) q)
        A0f hqM (degG_eq M q).symm B hB e p hp hpq (by rwa [toPoly_DzLC, M.sem_zero])
    have hbval : b = (T.val m a)′ := by
      rw [hb, M.sem_deriv, T.sem_MP_F m h0]
    have hnormal : ∀ p : (T.F m)[X], Irreducible p → p ∣ DzL 0 b p → X ∣ p := by
      intro p hp hpd
      by_contra hX
      apply T.normal_exp m htr hk p hp hX
      rw [T.wPoly_exp hm hk, ← hbval]
      simpa [DzL] using hpd
    have hspecP := sys_den_special_gauge b qs hq0 (semMat M A0f)
      (fun i j ↦ M.sem (m0E Fc ks m N q A0f i j)) (fun i j ↦ hA0z i j) _ _ hCiC
      (fun i j ↦ M.sem (gaugeT Fc ks m N q A0f C Ci i j)) hTg htriT
      (fun i ↦ (dgEAt Fc ks m dg0 (i : ℕ)).1) (fun i ↦ (dgEAt Fc ks m dg0 (i : ℕ)).2.1)
      (fun i ↦ M.sem (dgEAt Fc ks m dg0 (i : ℕ)).2.2) hdiagT hpT
      (fun j ↦ GPoly.toPoly M (Gf j)) hom hnormal
    have hdvd := fun i ↦ sys_den_bound' 0 b qs hs hhs0 (semMat M A0f) _ B hindB
      Z d hd0 hsol hspecP i
    choose u hu using hdvd
    -- the bound for the rescaled coordinates
    set R := ((List.range N).map fun i ↦ (-r i).toNat).foldr max 0 with hR
    have hRi : ∀ i < N, (-r i).toNat ≤ R := fun i hi ↦
      Tower.Sys.le_foldr_max _ _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    -- each coordinate in the rescaled basis has denominator dividing `E`
    have hterm : ∀ i (hi : i < N), Y i * T.tau m ^ r i * T.phi m (GPoly.toPoly M (GPoly.mul O
        (GPoly.mul O hq (sysPowC O q B)) (sysPowC O (tX Fc ks m) R))) =
        T.phi m (u ⟨i, hi⟩ * X ^ (R - (-r i).toNat + (r i).toNat)) := by
      intro i hi
      have hE : GPoly.toPoly M (GPoly.mul O (GPoly.mul O hq (sysPowC O q B))
          (sysPowC O (tX Fc ks m) R)) = hs * qs ^ B * X ^ R := by
        rw [GPoly.toPoly_mul, GPoly.toPoly_mul, toPoly_sysPowC, toPoly_sysPowC, T.toPoly_tX]
      rw [hE, map_mul, map_mul, map_pow, map_mul, map_pow, map_pow]
      have hui := hu ⟨i, hi⟩
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
    refine hb' ⟨fun i ↦ Y i * T.tau m ^ r i, fun i ↦ if hi : i < N then
      u ⟨i, hi⟩ * X ^ (R - (-r i).toNat + (r i).toNat) else 0, fun i hi ↦ ?_, ?_⟩
    · show Y i * T.tau m ^ r i * _ = T.phi m (if hi : i < N then _ else 0)
      rw [dif_pos hi]
      exact hterm i hi
    · rw [hsumY, hrhs]
      convert hY using 2
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [mul_assoc, ← zpow_add₀ (T.tau_ne_zero m htr), add_neg_cancel, zpow_zero, mul_one]


end MTower

end Curves.MT
