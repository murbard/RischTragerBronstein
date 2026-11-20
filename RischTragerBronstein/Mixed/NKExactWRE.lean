import RischTragerBronstein.Mixed.NKExactWEE
import RischTragerBronstein.Mixed.NKExactWR
import RischTragerBronstein.Computable.SysDenAnn
import RischTragerBronstein.Mixed.NKExactTG
import RischTragerBronstein.Mixed.NKExactTR

/-!
# The exact part at an exponential level, in a basis rescaled at infinity

For a basis `w` of `L` over `Fₘ₊₁ = Fₘ(t)` (`t = exp a`, `t′ = a′ t`) with derivation matrix `M`,
`exactWRE`:

* bounds the denominators of the coordinates of any antiderivative `∑ Yᵢ wᵢ` by `h q^B`: the
  indicial bound at `q` (`q(0) ≠ 0` checked) and, at `t = 0`, the rational limit
  `A₀(0) = q(0) a′ Λ₀` with `∏_{k<N₀} (Λ₀ − k/N₀) = 0` (checked, `sys_den_zero_ann`);
* passes to the basis `w̃ = C t^{−r} w` (`C` a constant rational matrix with checked inverse): the
  matrix `C (t^{rⱼ−rᵢ} Mᵢⱼ − δᵢⱼ rᵢ a′) C⁻¹` (`rescaleME`, `conjM`);
* runs `exactWE` with the solver `expSysB … 0` and the bound `E = h q^B t^R`.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- `c + e` for a code `e` of level `m`. -/
def addConstC (m : ℕ) (c : LC (m + 1)) (e : LC m) : LC (m + 1) :=
  (GPoly.add (MO Fc ks m) c.1 (GPoly.mul (MO Fc ks m) [e] c.2), c.2)

/-- The matrix of `t^{−r} w` at an exponential level: `t^{rⱼ−rᵢ} Mᵢⱼ − δᵢⱼ rᵢ a′`. -/
def rescaleME (m : ℕ) (bc : LC m) (N : ℕ) (Mc : List (List (LC (m + 1)))) (r : ℕ → ℤ) :
    List (List (LC (m + 1))) :=
  (List.range N).map fun i ↦ (List.range N).map fun j ↦
    if i = j then
      addConstC Fc ks m (tpowL Fc ks m 0 ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero))
        ((MO Fc ks m).mul (mcst Fc ks m (-(r i : ℚ))) bc)
    else tpowL Fc ks m (r j - r i) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero)

/-- An entry of a rational matrix given as lists. -/
def qget (C : List (List ℚ)) (i j : ℕ) : ℚ := (C.getD i []).getD j 0

/-- The conjugate `C M C⁻¹` on codes. -/
def conjM (m N : ℕ) (C : List (List ℚ)) (Mr : List (List (LC (m + 1)))) (Ci : List (List ℚ)) :
    List (List (LC (m + 1))) :=
  (List.range N).map fun k ↦ (List.range N).map fun l ↦
    lsumC (MOr Fc ks (m + 1)) ((List.range N).map fun i ↦ lsumC (MOr Fc ks (m + 1))
      ((List.range N).map fun j ↦ (MOr Fc ks (m + 1)).mul
        ((MOr Fc ks (m + 1)).mul (mcst Fc ks (m + 1) (qget C k i))
          ((Mr.getD i []).getD j (MOr Fc ks (m + 1)).zero))
        (mcst Fc ks (m + 1) (qget Ci j l))))

/-- The coordinates `f C⁻¹` on codes. -/
def vecCi (m N : ℕ) (fr : List (LC (m + 1))) (Ci : List (List ℚ)) : List (LC (m + 1)) :=
  (List.range N).map fun l ↦ lsumC (MOr Fc ks (m + 1)) ((List.range N).map fun j ↦
    (MOr Fc ks (m + 1)).mul (fr.getD j (MOr Fc ks (m + 1)).zero) (mcst Fc ks (m + 1) (qget Ci j l)))

/-- `C Ci = Ci C = 1` (checked over `ℚ`). -/
def qmatOK (N : ℕ) (C Ci : List (List ℚ)) : Bool :=
  (List.range N).all fun i ↦ (List.range N).all fun j ↦
    decide (∑ k ∈ Finset.range N, qget C i k * qget Ci k j = if i = j then 1 else 0) &&
    decide (∑ k ∈ Finset.range N, qget Ci i k * qget C k j = if i = j then 1 else 0)

/-- `∏_{k<N₀} (Λ − k/N₀) = 0` (checked over `ℚ`). -/
def annOK (N N0 : ℕ) (Λ : ℕ → ℕ → ℚ) : Bool :=
  let A : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun i j ↦ Λ i j
  let P := ((List.range N0).map fun k ↦ A - (annNodes N0 k) • (1 : Matrix (Fin N) (Fin N) ℚ)).prod
  decide (0 < N0) && (List.finRange N).all fun i ↦ (List.finRange N).all fun j ↦ P i j == 0

/-- The rational limit `Λ₀ = A₀(0) / (q(0) a′)` at `t = 0`. -/
def lam0E (m : ℕ) (bc : LC m) (N : ℕ) (q : GPoly (LC m)) (A0 : Fin N → Fin N → GPoly (LC m)) :
    ℕ → ℕ → ℚ := fun i j ↦ if h : i < N ∧ j < N then
  (ratValC Fc ks m ((MO Fc ks m).mul ((A0 ⟨i, h.1⟩ ⟨j, h.2⟩).getD 0 (MO Fc ks m).zero)
    ((MO Fc ks m).inv ((MO Fc ks m).mul (q.getD 0 (MO Fc ks m).zero) bc)))).getD 0 else 0

/-- **The checks at `t = 0` and on the constant matrix**: `A₀(0) = q(0) a′ Λ₀`,
`∏_{k<N₀} (Λ₀ − k/N₀) = 0`, `C C⁻¹ = C⁻¹ C = 1`. -/
def zeroOKE (m : ℕ) (bc : LC m) (N N0 : ℕ) (q : GPoly (LC m)) (A0 : Fin N → Fin N → GPoly (LC m))
    (C Ci : List (List ℚ)) : Bool :=
  ((List.finRange N).all fun i ↦ (List.finRange N).all fun j ↦
    (MO Fc ks m).isZero ((MO Fc ks m).add ((A0 i j).getD 0 (MO Fc ks m).zero)
      ((MO Fc ks m).neg ((MO Fc ks m).mul ((MO Fc ks m).mul (q.getD 0 (MO Fc ks m).zero) bc)
        (mcst Fc ks m (lam0E Fc ks m bc N q A0 i j)))))) &&
  annOK N N0 (lam0E Fc ks m bc N q A0) && qmatOK N C Ci

/-- **The exact-part test at an exponential level, rescaled at infinity.** -/
def exactWRE (m : ℕ) (a : LC m) (rdeD : LC m → List (LC m) → List (List ℚ × LC m)) (N : ℕ)
    (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (r : ℕ → ℤ) (N0 : ℕ)
    (C Ci : List (List ℚ)) : Option Bool :=
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
    if !(zeroOKE Fc ks m bc N N0 q A0 C Ci) then none
    else
    match indBound2 Fc ks m (degG O q) N q (DzLC O O.zero bc q) A0 with
    | none => none
    | some B =>
      let R := ((List.range N).map fun i ↦ (-r i).toNat).foldr max 0
      let E := GPoly.mul O (GPoly.mul O hq (sysPowC O q B)) (sysPowC O (tX Fc ks m) R)
      exactWE Fc ks m (fun n A0 q hh G0 ↦ expSysB Fc ks m a rdeD n A0 q hh G0 0) N
        ((conjM Fc ks m N C (rescaleME Fc ks m bc N Mc r) Ci).map fun l ↦ l.map (redC Fc ks m))
        ((vecCi Fc ks m N (rescaleF Fc ks m N f r) Ci).map (redC Fc ks m)) E

lemma annOK_spec (N N0 : ℕ) (Λ : ℕ → ℕ → ℚ) (h : annOK N N0 Λ = true) :
    0 < N0 ∧ aeval (Matrix.of fun i j : Fin N ↦ Λ i j)
      (Lagrange.nodal (Finset.range N0) (annNodes N0)) = 0 := by
  unfold annOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    forall_const, beq_iff_eq] at h
  refine ⟨h.1, ?_⟩
  have hnodal : Lagrange.nodal (Finset.range N0) (annNodes N0) =
      ((List.range N0).map fun k ↦ X - Polynomial.C (annNodes N0 k)).prod := by
    rw [Lagrange.nodal, ← List.toFinset_range, List.prod_toFinset _ (List.nodup_range)]
  rw [hnodal, map_list_prod, List.map_map]
  refine Matrix.ext fun i j ↦ ?_
  have := h.2 i j
  convert this using 2
  · congr 1
    funext k
    simp only [Function.comp_apply, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  · rfl

lemma qmatOK_spec (N : ℕ) (C Ci : List (List ℚ)) (h : qmatOK N C Ci = true) :
    (∀ i < N, ∀ j < N, ∑ k ∈ Finset.range N, qget C i k * qget Ci k j = if i = j then 1 else 0) ∧
    (∀ i < N, ∀ j < N, ∑ k ∈ Finset.range N, qget Ci i k * qget C k j = if i = j then 1 else 0) := by
  unfold qmatOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨fun i hi j hj ↦ (h i hi j hj).1, fun i hi j hj ↦ (h i hi j hj).2⟩

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

variable (m : ℕ) (h1 : T.Tr (m + 1))

lemma sem_addConstC (htr : Transcendental (T.F m) (T.ts m)) (c : LC (m + 1)) (e : LC m)
    (hc : T.phi m (GPoly.toPoly (T.MP m h1.of_succ) c.2) ≠ 0) :
    (T.MPr (m + 1) h1).sem (addConstC Fc ks m c e) = (T.MPr (m + 1) h1).sem c +
      T.phi m (Polynomial.C ((T.MP m h1.of_succ).sem e)) := by
  rw [MPr_sem, MPr_sem, T.sem_MP_succ, T.sem_MP_succ]
  unfold addConstC
  simp only [GPoly.toPoly_mul, GPoly.toPoly_add, map_mul, map_add]
  have hs : GPoly.toPoly (T.MP m (fun i hi ↦ h1 i (by omega))) [e] =
      Polynomial.C ((T.MP m h1.of_succ).sem e) := T.toPoly_single m h1 e
  rw [hs]
  field_simp

variable {m}

lemma deriv_tau_exp (hm : m < T.n) {a : LC m} (hk : ks m = .exp a) (h0 : T.Tr m) :
    (T.tau m)′ = T.phi m (Polynomial.C ((T.MP m h0).sem ((MO Fc ks m).deriv a))) * T.tau m := by
  rw [← T.phi_DzL_exp m hm hk h0 X, DzL_eq]
  simp

lemma deriv_tau_zpow_exp (hm : m < T.n) {a : LC m} (hk : ks m = .exp a) (h0 : T.Tr m)
    (htr : Transcendental (T.F m) (T.ts m)) (k : ℤ) :
    (T.tau m ^ k)′ = (k : T.F (m + 1)) *
      T.phi m (Polynomial.C ((T.MP m h0).sem ((MO Fc ks m).deriv a))) * T.tau m ^ k := by
  have ht := T.tau_ne_zero m htr
  rw [Derivation.leibniz_zpow, T.deriv_tau_exp hm hk h0, zpow_sub₀ ht, zpow_one, zsmul_eq_mul,
    smul_eq_mul]
  field_simp

/-- **The derivation matrix of the rescaled basis** at an exponential level. -/
lemma rescale_derivE (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m)) (N : ℕ) (Mc : List (List (LC (m + 1)))) (r : ℕ → ℤ)
    (θw : ℕ → L)
    (hw : ∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) * θw j)
    (hden : ∀ i < N, ∀ j < N,
      T.phi m (GPoly.toPoly (T.MP m h1.of_succ) ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero).2) ≠ 0) :
    ∀ i < N, (((T.tau m ^ (-r i) : T.F (m + 1)) : L) * θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem (((rescaleME Fc ks m ((MO Fc ks m).deriv a) N Mc r).getD i []).getD j
        (MOr Fc ks (m + 1)).zero) : L) * (((T.tau m ^ (-r j) : T.F (m + 1)) : L) * θw j) := by
  intro i hi
  have ht := T.tau_ne_zero m htr
  set h0 := h1.of_succ
  set M1 := T.MPr (m + 1) h1
  set bF := T.phi m (Polynomial.C ((T.MP m h0).sem ((MO Fc ks m).deriv a)))
  set Mw : ℕ → ℕ → T.F (m + 1) := fun i j ↦ M1.sem ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero)
  have hcoef : ∀ j < N, M1.sem (((rescaleME Fc ks m ((MO Fc ks m).deriv a) N Mc r).getD i []).getD j
      (MOr Fc ks (m + 1)).zero) * T.tau m ^ (-r j) =
      T.tau m ^ (-r i) * Mw i j + if i = j then (T.tau m ^ (-r i))′ else 0 := by
    intro j hj
    rw [rescaleME, NestTower.getD_range_map _ _ hi, NestTower.getD_range_map _ _ hj]
    split_ifs with hij
    · subst hij
      rw [T.sem_addConstC m h1 htr _ _ (by rw [tpowL_zero_snd]; exact hden i hi i hi),
        T.sem_tpowL m h1 htr, (T.MP m h0).sem_mul, T.sem_mcst m h0, T.deriv_tau_zpow_exp hm hk h0 htr]
      have e1 : T.phi m (Polynomial.C (((-(r i : ℚ) : ℚ) : T.F m) *
          (T.MP m h0).sem ((MO Fc ks m).deriv a))) = ((-(r i : ℚ) : ℚ) : T.F (m + 1)) * bF := by
        rw [Polynomial.C_mul, map_mul]; congr 1; simp
      rw [e1, zpow_zero]
      push_cast
      ring
    · rw [T.sem_tpowL m h1 htr, mul_assoc, ← zpow_add₀ ht, add_zero]
      rw [show r j - r i + -r j = -r i by ring]
      ring
  have hco : (((T.tau m ^ (-r i) : T.F (m + 1)) : L))′ =
      (((T.tau m ^ (-r i))′ : T.F (m + 1)) : L) := rfl
  rw [Derivation.leibniz, hco, hw i hi, smul_eq_mul, smul_eq_mul, Finset.mul_sum]
  have hR : ∀ j ∈ Finset.range N,
      ((M1.sem (((rescaleME Fc ks m ((MO Fc ks m).deriv a) N Mc r).getD i []).getD j
        (MOr Fc ks (m + 1)).zero) : L) * (((T.tau m ^ (-r j) : T.F (m + 1)) : L) * θw j)) =
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


lemma sem_qcst (q : ℚ) : (((T.MPr (m + 1) h1).sem (mcst Fc ks (m + 1) q) : T.F (m + 1)) : L) = (q : L) := by
  rw [MPr_sem, T.sem_mcst (m + 1) h1 q]; push_cast; rfl

/-- **The derivation matrix of `C θt`.** -/
lemma conj_deriv (N : ℕ) (C Ci : List (List ℚ))
    (hCiC : ∀ i < N, ∀ j < N, ∑ k ∈ Finset.range N, qget Ci i k * qget C k j = if i = j then 1 else 0)
    (Mr : List (List (LC (m + 1)))) (θt : ℕ → L)
    (hw : ∀ i < N, (θt i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem ((Mr.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) * θt j) :
    ∀ k < N, (∑ i ∈ Finset.range N, (qget C k i : L) * θt i)′ = ∑ l ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem (((conjM Fc ks m N C Mr Ci).getD k []).getD l
        (MOr Fc ks (m + 1)).zero) : L) * ∑ i ∈ Finset.range N, (qget C l i : L) * θt i := by
  intro k hk
  set M1 := T.MPr (m + 1) h1
  set θc : ℕ → L := fun l ↦ ∑ i ∈ Finset.range N, (qget C l i : L) * θt i with hθc
  -- `θt = C⁻¹ θc`
  have hθt : ∀ j < N, θt j = ∑ l ∈ Finset.range N, (qget Ci j l : L) * θc l := by
    intro j hj
    have e1 : ∑ l ∈ Finset.range N, (qget Ci j l : L) * θc l =
        ∑ i ∈ Finset.range N, (∑ l ∈ Finset.range N, (qget Ci j l : L) * (qget C l i : L)) * θt i := by
      simp only [hθc, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
    rw [e1, Finset.sum_congr rfl fun i hi ↦ by
      rw [show ∑ l ∈ Finset.range N, (qget Ci j l : L) * (qget C l i : L) =
        ((if j = i then 1 else 0 : ℚ) : L) by
          rw [← hCiC j hj i (Finset.mem_range.mp hi)]; push_cast; rfl]]
    rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [if_neg (Ne.symm hij)]; simp)
      (fun h ↦ absurd (Finset.mem_range.mpr hj) h)]
    simp
  have hdq : ∀ c : ℚ, ((c : L))′ = 0 := fun c ↦
    Tower.Sys.derivation_ratCast_K (Differential.deriv : Derivation ℤ L L) c
  have hR : ∀ l ∈ Finset.range N, ((M1.sem (((conjM Fc ks m N C Mr Ci).getD k []).getD l
      (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (qget C k i : L) * (M1.sem ((Mr.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) *
        (qget Ci j l : L) := by
    intro l hl
    rw [conjM, NestTower.getD_range_map _ _ hk, NestTower.getD_range_map _ _ (Finset.mem_range.mp hl),
      T.sem_lsum_range m h1, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [T.sem_lsum_range m h1, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [(T.MPr (m + 1) h1).sem_mul, (T.MPr (m + 1) h1).sem_mul, IntermediateField.coe_mul,
      IntermediateField.coe_mul, T.sem_qcst h1, T.sem_qcst h1]
  have hL : (θc k)′ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
      (qget C k i : L) * (M1.sem ((Mr.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) *
        (qget Ci j l : L) * θc l := by
    rw [hθc, map_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Derivation.leibniz, hdq, smul_zero, add_zero, smul_eq_mul, hw i (Finset.mem_range.mp hi),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [hθt j (Finset.mem_range.mp hj), Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ ↦ by ring
  have hRHS : ∑ l ∈ Finset.range N, ((M1.sem (((conjM Fc ks m N C Mr Ci).getD k []).getD l
      (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θc l =
      ∑ l ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (qget C k i : L) * (M1.sem ((Mr.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) *
          (qget Ci j l : L) * θc l :=
    Finset.sum_congr rfl fun l hl ↦ by
      rw [hR l hl, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [Finset.sum_mul]
  show (θc k)′ = _
  rw [hL, hRHS]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  conv_rhs => rw [Finset.sum_comm]

omit h1 in
lemma conj_inv (N : ℕ) (C Ci : List (List ℚ))
    (hCiC : ∀ i < N, ∀ j < N, ∑ k ∈ Finset.range N, qget Ci i k * qget C k j = if i = j then 1 else 0)
    (θt : ℕ → L) (j : ℕ) (hj : j < N) :
    θt j = ∑ l ∈ Finset.range N, (qget Ci j l : L) * ∑ i ∈ Finset.range N, (qget C l i : L) * θt i := by
  have e1 : ∑ l ∈ Finset.range N, (qget Ci j l : L) * ∑ i ∈ Finset.range N, (qget C l i : L) * θt i =
      ∑ i ∈ Finset.range N, (∑ l ∈ Finset.range N, (qget Ci j l : L) * (qget C l i : L)) * θt i := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
  rw [e1, Finset.sum_congr rfl fun i hi ↦ by
    rw [show ∑ l ∈ Finset.range N, (qget Ci j l : L) * (qget C l i : L) =
      ((if j = i then 1 else 0 : ℚ) : L) by
        rw [← hCiC j hj i (Finset.mem_range.mp hi)]; push_cast; rfl]]
  rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [if_neg (Ne.symm hij)]; simp)
    (fun h ↦ absurd (Finset.mem_range.mpr hj) h)]
  simp

omit h1 in
lemma conj_ind (N : ℕ) (C Ci : List (List ℚ))
    (hCCi : ∀ i < N, ∀ j < N, ∑ k ∈ Finset.range N, qget C i k * qget Ci k j = if i = j then 1 else 0)
    (θt : ℕ → L)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * θt j = 0 → ∀ j < N, a j = 0) :
    ∀ a : ℕ → T.F (m + 1), ∑ l ∈ Finset.range N, (a l : L) *
      (∑ i ∈ Finset.range N, (qget C l i : L) * θt i) = 0 → ∀ j < N, a j = 0 := by
  intro a ha j hj
  set b : ℕ → T.F (m + 1) := fun i ↦ ∑ l ∈ Finset.range N, a l * (qget C l i : T.F (m + 1)) with hb
  have hbL : ∀ i, ((b i : T.F (m + 1)) : L) = ∑ l ∈ Finset.range N, (a l : L) * (qget C l i : L) :=
    fun i ↦ by simp [hb]
  have hb0 := hind b (by
    rw [← ha]
    simp only [hbL, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring)
  have : a j = ∑ i ∈ Finset.range N, b i * (qget Ci i j : T.F (m + 1)) := by
    simp only [hb, Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single j]
    · have h1' := hCCi j hj j hj
      rw [if_pos rfl] at h1'
      have : ∑ i ∈ Finset.range N, (qget C j i : T.F (m + 1)) * (qget Ci i j : T.F (m + 1)) = 1 := by
        exact_mod_cast h1'
      rw [show ∑ i ∈ Finset.range N, a j * (qget C j i : T.F (m + 1)) * (qget Ci i j : T.F (m + 1)) =
        a j * ∑ i ∈ Finset.range N, (qget C j i : T.F (m + 1)) * (qget Ci i j : T.F (m + 1)) by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring, this, mul_one]
    · intro l hl hlj
      have h1' := hCCi l (Finset.mem_range.mp hl) j hj
      rw [if_neg hlj] at h1'
      have : ∑ i ∈ Finset.range N, (qget C l i : T.F (m + 1)) * (qget Ci i j : T.F (m + 1)) = 0 := by
        exact_mod_cast h1'
      rw [show ∑ i ∈ Finset.range N, a l * (qget C l i : T.F (m + 1)) * (qget Ci i j : T.F (m + 1)) =
        a l * ∑ i ∈ Finset.range N, (qget C l i : T.F (m + 1)) * (qget Ci i j : T.F (m + 1)) by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring, this, mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr hj) h
  rw [this]
  exact Finset.sum_eq_zero fun i hi ↦ by rw [hb0 i (Finset.mem_range.mp hi), zero_mul]

lemma conj_rhs (N : ℕ) (C Ci : List (List ℚ))
    (hCiC : ∀ i < N, ∀ j < N, ∑ k ∈ Finset.range N, qget Ci i k * qget C k j = if i = j then 1 else 0)
    (fr : List (LC (m + 1))) (θt : ℕ → L) :
    ∑ l ∈ Finset.range N, ((T.MPr (m + 1) h1).sem ((vecCi Fc ks m N fr Ci).getD l
      (MOr Fc ks (m + 1)).zero) : L) * ∑ i ∈ Finset.range N, (qget C l i : L) * θt i =
    ∑ j ∈ Finset.range N, ((T.MPr (m + 1) h1).sem (fr.getD j (MOr Fc ks (m + 1)).zero) : L) *
      θt j := by
  have hv : ∀ l ∈ Finset.range N, ((T.MPr (m + 1) h1).sem ((vecCi Fc ks m N fr Ci).getD l
      (MOr Fc ks (m + 1)).zero) : L) = ∑ j ∈ Finset.range N,
        ((T.MPr (m + 1) h1).sem (fr.getD j (MOr Fc ks (m + 1)).zero) : L) * (qget Ci j l : L) := by
    intro l hl
    rw [vecCi, NestTower.getD_range_map _ _ (Finset.mem_range.mp hl), T.sem_lsum_range m h1,
      AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [(T.MPr (m + 1) h1).sem_mul, IntermediateField.coe_mul, T.sem_qcst h1]
  set θc : ℕ → L := fun l ↦ ∑ i ∈ Finset.range N, (qget C l i : L) * θt i with hθc
  rw [Finset.sum_congr rfl fun l hl ↦ by rw [hv l hl]]
  have e1 : ∑ l ∈ Finset.range N, (∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem (fr.getD j (MOr Fc ks (m + 1)).zero) : L) * (qget Ci j l : L)) * θc l =
      ∑ j ∈ Finset.range N, ((T.MPr (m + 1) h1).sem (fr.getD j (MOr Fc ks (m + 1)).zero) : L) *
        ∑ l ∈ Finset.range N, (qget Ci j l : L) * θc l := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
  rw [e1]
  exact Finset.sum_congr rfl fun j hj ↦ by
    rw [← conj_inv N C Ci hCiC θt j (Finset.mem_range.mp hj)]


omit h1 in
lemma zeroOKE_spec (m : ℕ) (h0 : T.Tr m) (bc : LC m) (N N0 : ℕ) (q : GPoly (LC m))
    (A0 : Fin N → Fin N → GPoly (LC m)) (C Ci : List (List ℚ))
    (hz : zeroOKE Fc ks m bc N N0 q A0 C Ci = true) :
    (∀ i j : Fin N, (GPoly.toPoly (T.MP m h0) (A0 i j)).coeff 0 =
      (GPoly.toPoly (T.MP m h0) q).coeff 0 * (T.MP m h0).sem bc *
        ((lam0E Fc ks m bc N q A0 i j : ℚ) : T.F m)) ∧
    0 < N0 ∧ aeval (Matrix.of fun i j : Fin N ↦ lam0E Fc ks m bc N q A0 i j)
      (Lagrange.nodal (Finset.range N0) (annNodes N0)) = 0 ∧
    (∀ i < N, ∀ j < N, ∑ k ∈ Finset.range N, qget C i k * qget Ci k j = if i = j then 1 else 0) ∧
    (∀ i < N, ∀ j < N, ∑ k ∈ Finset.range N, qget Ci i k * qget C k j = if i = j then 1 else 0) := by
  unfold zeroOKE at hz
  simp only [Bool.and_eq_true] at hz
  obtain ⟨⟨hA, hann⟩, hq⟩ := hz
  obtain ⟨hN0, hP⟩ := annOK_spec N N0 _ hann
  obtain ⟨hC1, hC2⟩ := qmatOK_spec N C Ci hq
  refine ⟨fun i j ↦ ?_, hN0, hP, hC1, hC2⟩
  simp only [List.all_eq_true, List.mem_finRange, forall_const] at hA
  have := ((T.MP m h0).isZero_iff _).mp (hA i j)
  rw [(T.MP m h0).sem_add, (T.MP m h0).sem_neg, (T.MP m h0).sem_mul, (T.MP m h0).sem_mul,
    T.sem_mcst m h0, add_neg_eq_zero] at this
  rw [coeff_toPoly_sem, coeff_toPoly_sem, this]

set_option maxHeartbeats 3200000 in
/-- **Correctness of `exactWRE`**: for any basis `w` with derivation matrix `Mc`, shifts `r`,
`N₀` and constant `C`, an answer `res` says whether `∑ fⱼ wⱼ` has an antiderivative `∑ Yᵢ wᵢ`. -/
theorem exactWRE_correct (hm : m < T.n) {a : LC m} (hk : ks m = .exp a)
    (htr : Transcendental (T.F m) (T.ts m)) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hrdeD : ∀ c : LC m, RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
      ((T.MP m h1.of_succ).sem c)′ (rdeD c))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (N : ℕ) (Mc : List (List (LC (m + 1)))) (f : List (LC (m + 1))) (r : ℕ → ℤ) (N0 : ℕ)
    (C Ci : List (List ℚ)) (θw : ℕ → L)
    (hw : ∀ i < N, (θw i)′ = ∑ j ∈ Finset.range N,
      ((T.MPr (m + 1) h1).sem ((Mc.getD i []).getD j (MOr Fc ks (m + 1)).zero) : L) * θw j)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range N, (a j : L) * θw j = 0 →
      ∀ j < N, a j = 0)
    (res : Bool) (hres : exactWRE Fc ks m a rdeD N Mc f r N0 C Ci = some res) :
    res = true ↔ ∃ Y : ℕ → T.F (m + 1),
      (∑ i ∈ Finset.range N, (Y i : L) * θw i)′ =
        ∑ j ∈ Finset.range N,
          ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) * θw j := by
  classical
  unfold exactWRE at hres
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
  obtain ⟨hA0z, hN0pos, hP, hCCi, hCiC⟩ := T.zeroOKE_spec m h0 _ N N0 q _ C Ci hzc
  set A0f : Fin N → Fin N → GPoly (LC m) := fun j i ↦ num ((Ml.getD i []).getD j O1.zero) with hA0f
  set Gf : Fin N → GPoly (LC m) := fun j ↦ numF (f.getD j O1.zero) with hGf
  -- the rescaled and conjugated basis
  set θt : ℕ → L := fun i ↦ ((T.tau m ^ (-r i) : T.F (m + 1)) : L) * θw i with hθt
  have hwt := T.rescale_derivE h1 hm hk htr N Mc r θw hw hden
  have hindt := T.rescale_ind htr N r θw hind
  set θc : ℕ → L := fun l ↦ ∑ i ∈ Finset.range N, (qget C l i : L) * θt i with hθc
  have hwc0 := T.conj_deriv h1 N C Ci hCiC _ θt hwt
  have hwc : ∀ k < N, (θc k)′ = ∑ l ∈ Finset.range N, ((T.MPr (m + 1) h1).sem
      ((((conjM Fc ks m N C (rescaleME Fc ks m ((MO Fc ks m).deriv a) N Mc r) Ci).map fun l ↦
        l.map (redC Fc ks m)).getD k []).getD l (MOr Fc ks (m + 1)).zero) : L) * θc l := by
    intro k hk
    rw [hwc0 k hk]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [getD_map_map_redC (Fc := Fc) (ks := ks) m, T.sem_getD_map_redC m h1 htr]
  have hindc := T.conj_ind N C Ci hCCi θt hindt
  have hspec := T.expSpecB hm h0 hk rdeD hrdeD hom
  obtain ⟨ha, hb'⟩ := T.exactWE_correct m h1 htr _ 0 b hspec N _ _ _ θc hwc hindc res hres
  have hrhs : ∑ l ∈ Finset.range N, ((T.MPr (m + 1) h1).sem (((vecCi Fc ks m N (rescaleF Fc ks m N f r)
      Ci).map (redC Fc ks m)).getD l (MOr Fc ks (m + 1)).zero) : L) * θc l =
      ∑ j ∈ Finset.range N, ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) *
        θw j := by
    simp only [T.sem_getD_map_redC m h1 htr]
    rw [T.conj_rhs h1 N C Ci hCiC _ θt, T.rescale_rhs h1 htr N f r θw]
  have hsumY : ∀ Y : ℕ → T.F (m + 1), ∑ l ∈ Finset.range N, (Y l : L) * θc l =
      ∑ i ∈ Finset.range N, ((∑ l ∈ Finset.range N, Y l * (qget C l i : T.F (m + 1)) *
        T.tau m ^ (-r i) : T.F (m + 1)) : L) * θw i := fun Y ↦ by
    simp only [hθc, hθt, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ ↦ by ring
  constructor
  · intro hrt
    obtain ⟨Y, hY⟩ := ha hrt
    refine ⟨fun i ↦ ∑ l ∈ Finset.range N, Y l * (qget C l i : T.F (m + 1)) * T.tau m ^ (-r i), ?_⟩
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
    have hspecP := sys_den_special_ann b qs hq0 (semMat M A0f) _
      (fun i j ↦ hA0z i j) N0 hN0pos hP
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
    refine hb' ⟨fun l ↦ ∑ i ∈ Finset.range N, (qget Ci i l : T.F (m + 1)) * (Y i * T.tau m ^ r i),
      fun l ↦ ∑ i ∈ Finset.range N, Polynomial.C ((qget Ci i l : ℚ) : T.F m) *
        (if hi : i < N then u ⟨i, hi⟩ * X ^ (R - (-r i).toNat + (r i).toNat) else 0),
      fun l hl ↦ ?_, ?_⟩
    · push_cast
      rw [Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hi' := Finset.mem_range.mp hi
      rw [dif_pos hi', map_mul, ← hterm i hi']
      have hc : T.phi m (Polynomial.C ((qget Ci i l : ℚ) : T.F m)) = ((qget Ci i l : ℚ) : T.F (m + 1)) := by
        rw [show ((qget Ci i l : ℚ) : T.F m) = algebraMap ℚ (T.F m) (qget Ci i l) from rfl,
          ← Polynomial.algebraMap_apply, ← RingHom.comp_apply]
        simp
      rw [hc]
      push_cast
      ring
    · -- the coordinates represent the same element
      have hsame : ∑ l ∈ Finset.range N, ((∑ i ∈ Finset.range N, (qget Ci i l : T.F (m + 1)) *
          (Y i * T.tau m ^ r i) : T.F (m + 1)) : L) * θc l =
          ∑ i ∈ Finset.range N, (Y i : L) * θw i := by
        have hθw : ∀ i < N, θw i = ((T.tau m ^ r i : T.F (m + 1)) : L) * θt i := fun i hi ↦ by
          simp only [hθt]
          rw [← mul_assoc, ← IntermediateField.coe_mul, ← zpow_add₀ (T.tau_ne_zero m htr),
            add_neg_cancel, zpow_zero, OneMemClass.coe_one, one_mul]
        have hR : ∑ i ∈ Finset.range N, (Y i : L) * θw i = ∑ i ∈ Finset.range N, (Y i : L) *
            (((T.tau m ^ r i : T.F (m + 1)) : L) * ∑ l ∈ Finset.range N, (qget Ci i l : L) * θc l) :=
          Finset.sum_congr rfl fun i hi ↦ by
            rw [hθw i (Finset.mem_range.mp hi), conj_inv N C Ci hCiC θt i (Finset.mem_range.mp hi)]
        rw [hR]
        push_cast
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
        ring
      rw [hsame, hrhs]
      exact hY

end MTower

end Curves.MT
