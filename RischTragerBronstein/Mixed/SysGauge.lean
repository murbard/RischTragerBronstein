import RischTragerBronstein.Mixed.SysPrimVG
import RischTragerBronstein.Mixed.NKExactWREV
import RischTragerBronstein.Mixed.NKExactWE

/-!
# A constant gauge for any coupled-system solver

For `Y′ + (A₀/q) Y = G₀/h` and a constant invertible matrix `C` (inverse `C⁻¹`), `Z = C Y` solves
`Z′ + (A₀′/q) Z = C G₀ / h` with `A₀′ = C A₀ C⁻¹ − q C′ C⁻¹` (`sysSol_gauge`, on the cleared
equations). `gaugeSolver solve C Ci` runs `solve` on the gauged system and maps the solutions back;
it meets the solver specification with known denominators whenever `solve` does
(`gaugeSolver_spec`), and it answers when `solve` answers on the gauged system. The limit at
infinity of `A₀′/q` is `C Λ C⁻¹ − C′ C⁻¹` (`gaugeA_coeff`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

variable {K : Type*} [Field K] [Differential K] [CharZero K] (w0 b : K) {n : ℕ}

/-- The gauged matrix `C A₀ C⁻¹ − q C′ C⁻¹`. -/
noncomputable def gaugeA (q : K[X]) (Cm Ci : Matrix (Fin n) (Fin n) K)
    (A0 : Matrix (Fin n) (Fin n) K[X]) : Matrix (Fin n) (Fin n) K[X] :=
  Cm.map Polynomial.C * A0 * Ci.map Polynomial.C -
    q • ((Cm.map fun z ↦ z′).map Polynomial.C * Ci.map Polynomial.C)

lemma DzL_C' (c : K) : DzL w0 b (Polynomial.C c) = Polynomial.C (c′) := by
  simp [DzL]

/-- **The gauge on the cleared equations.** -/
theorem sysSol_gauge (q h : K[X]) (Cm Ci : Matrix (Fin n) (Fin n) K) (hCiC : Ci * Cm = 1)
    (A0 : Matrix (Fin n) (Fin n) K[X]) (G0 : Fin n → K[X]) (Z : Fin n → K[X]) (d : K[X])
    (hs : SysSol w0 b q h A0 G0 Z d) :
    SysSol w0 b q h (gaugeA q Cm Ci A0) (fun i ↦ ∑ k, Polynomial.C (Cm i k) * G0 k)
      (fun i ↦ ∑ k, Polynomial.C (Cm i k) * Z k) d := by
  intro i
  set Cp := Cm.map Polynomial.C with hCp
  set Cip := Ci.map Polynomial.C with hCip
  have hCiCp : Cip * Cp = 1 := by
    rw [hCp, hCip, ← Matrix.map_mul, hCiC, Matrix.map_one _ (map_zero _) (map_one _)]
  have hv : (fun i ↦ ∑ k, Polynomial.C (Cm i k) * Z k) = Cp.mulVec Z := by
    funext i; simp [hCp, Matrix.mulVec, dotProduct]
  have hA : ∑ j, gaugeA q Cm Ci A0 i j * Cp.mulVec Z j =
      (Cp.mulVec (A0.mulVec Z)) i -
        q * ((Cm.map fun z ↦ z′).map Polynomial.C).mulVec Z i := by
    have : (gaugeA q Cm Ci A0).mulVec (Cp.mulVec Z) =
        Cp.mulVec (A0.mulVec Z) - q • ((Cm.map fun z ↦ z′).map Polynomial.C).mulVec Z := by
      rw [gaugeA, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
        hCiCp, Matrix.mul_one, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
      congr 2
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      erw [hCiCp]
      rw [Matrix.mul_one]
    have := congrFun this i
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    exact this
  have hD : DzL w0 b (Cp.mulVec Z i) =
      ((Cm.map fun z ↦ z′).map Polynomial.C).mulVec Z i + Cp.mulVec (fun k ↦ DzL w0 b (Z k)) i := by
    simp only [Matrix.mulVec, dotProduct, hCp, Matrix.map_apply, ← Finset.sum_add_distrib]
    unfold DzL
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, implicitDeriv_C]
    ring
  rw [hv, hD, hA]
  have hsum := congrArg (fun v ↦ Cp.mulVec v i) (funext hs)
  simp only [Matrix.mulVec, dotProduct, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib] at hsum ⊢
  have e : ∀ (f : Fin n → K[X]) (c : K[X]), ∑ k, Cp i k * (c * f k) = c * ∑ k, Cp i k * f k :=
    fun f c ↦ by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ ↦ by ring
  simp only [show ∀ k, Cp i k * (q * h * (d * DzL w0 b (Z k))) =
      q * h * d * (Cp i k * DzL w0 b (Z k)) from fun k ↦ by ring,
    show ∀ k, Cp i k * (q * h * (DzL w0 b d * Z k)) = q * h * DzL w0 b d * (Cp i k * Z k) from
      fun k ↦ by ring,
    show ∀ k, Cp i k * (h * d * ∑ l, A0 k l * Z l) = h * d * (Cp i k * ∑ l, A0 k l * Z l) from
      fun k ↦ by ring,
    show ∀ k, Cp i k * (q * d ^ 2 * G0 k) = q * d ^ 2 * (Cp i k * G0 k) from fun k ↦ by ring,
    ← Finset.mul_sum] at hsum
  have hG : ∑ k, Polynomial.C (Cm i k) * G0 k = ∑ k, Cp i k * G0 k := by simp [hCp]
  rw [hG]
  linear_combination hsum

lemma deriv_inv_rel (Cm Ci : Matrix (Fin n) (Fin n) K) (hCiC : Ci * Cm = 1) :
    Ci * Cm.map (fun z ↦ z′) + Ci.map (fun z ↦ z′) * Cm = 0 := by
  ext i j
  have := congrArg (fun M : Matrix (Fin n) (Fin n) K ↦ (M i j)′) hCiC
  have h0 : ((if i = j then (1 : K) else 0))′ = 0 := by split_ifs <;> simp
  simp only [Matrix.mul_apply, Matrix.one_apply, h0, map_sum, Derivation.leibniz,
    smul_eq_mul] at this
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply,
    ← Finset.sum_add_distrib]
  rw [← this]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- Gauging back with the inverse undoes the gauge. -/
theorem gaugeA_inv (q : K[X]) (Cm Ci : Matrix (Fin n) (Fin n) K) (hCiC : Ci * Cm = 1)
    (hCCi : Cm * Ci = 1) (A0 : Matrix (Fin n) (Fin n) K[X]) :
    gaugeA q Ci Cm (gaugeA q Cm Ci A0) = A0 := by
  have hm : ∀ X Y : Matrix (Fin n) (Fin n) K,
      (X * Y).map Polynomial.C = X.map Polynomial.C * Y.map Polynomial.C :=
    fun X Y ↦ Matrix.map_mul
  have h1 : Ci.map Polynomial.C * Cm.map Polynomial.C = 1 := by
    rw [← hm, hCiC, Matrix.map_one _ (map_zero _) (map_one _)]
  have h3 : Ci.map Polynomial.C * (Cm.map fun z ↦ z′).map Polynomial.C +
      (Ci.map fun z ↦ z′).map Polynomial.C * Cm.map Polynomial.C = 0 := by
    rw [← hm, ← hm, ← Matrix.map_add _ (map_add _), deriv_inv_rel Cm Ci hCiC,
      Matrix.map_zero _ (map_zero _)]
  unfold gaugeA
  set P := Cm.map Polynomial.C
  set Pi := Ci.map Polynomial.C
  set P' := (Cm.map fun z ↦ z′).map Polynomial.C
  set Pi' := (Ci.map fun z ↦ z′).map Polynomial.C
  calc Pi * (P * A0 * Pi - q • (P' * Pi)) * P - q • (Pi' * P)
      = (Pi * P) * A0 * (Pi * P) - q • ((Pi * P') * (Pi * P) + Pi' * P) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_assoc, smul_add]
        abel
    _ = A0 := by rw [h1, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, h3, smul_zero, sub_zero]

/-- **The limit at infinity of the gauged matrix**: `C Λ C⁻¹ − C′ C⁻¹` for `A₀/q → Λ`. -/
lemma gaugeA_lim (q : K[X]) (hq : q.Monic) (Cm Ci : Matrix (Fin n) (Fin n) K)
    (A0 : Matrix (Fin n) (Fin n) K[X]) (Λ : Fin n → Fin n → K)
    (hA : ∀ i j, (A0 i j).natDegree ≤ q.natDegree)
    (hΛ : ∀ i j, (A0 i j).coeff q.natDegree = Λ i j) (i j : Fin n) :
    (gaugeA q Cm Ci A0 i j).natDegree ≤ q.natDegree ∧
      (gaugeA q Cm Ci A0 i j).coeff q.natDegree = gaugeM Cm Ci Λ i j := by
  have he : gaugeA q Cm Ci A0 i j = ∑ k, ∑ l, Polynomial.C (Cm i k * Ci l j) * A0 k l -
      q * Polynomial.C (∑ k, (Cm i k)′ * Ci k j) := by
    simp only [gaugeA, Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply,
      smul_eq_mul, Finset.sum_mul, map_sum, Polynomial.C_mul]
    rw [Finset.sum_comm]
    exact congrArg₂ _ (Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring) rfl
  rw [he]
  refine ⟨(natDegree_sub_le _ _).trans (max_le ?_ ?_), ?_⟩
  · exact natDegree_sum_le_of_forall_le _ _ fun k _ ↦ natDegree_sum_le_of_forall_le _ _
      fun l _ ↦ (natDegree_C_mul_le _ _).trans (hA k l)
  · exact natDegree_mul_C_le _ _
  · rw [coeff_sub, coeff_mul_C, hq.coeff_natDegree, one_mul, finset_sum_coeff]
    simp_rw [finset_sum_coeff, coeff_C_mul, hΛ]
    simp only [gaugeM]
    exact congrArg₂ _ (Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring) rfl

end Tower.Sys

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- `∑ₖ f k` for polynomial codes. -/
def gsumF (m n : ℕ) (f : Fin n → GPoly (LC m)) : GPoly (LC m) :=
  ((List.finRange n).map f).foldr (GPoly.add (MO Fc ks m)) []

/-- The gauged matrix `C A₀ C⁻¹ − q C′ C⁻¹` on codes. -/
def gaugeAG (m n : ℕ) (C Ci : List (List (LC m))) (A0 : Fin n → Fin n → GPoly (LC m))
    (q : GPoly (LC m)) : Fin n → Fin n → GPoly (LC m) :=
  let O := MO Fc ks m
  fun i j ↦ GPoly.sub O (gsumF Fc ks m n fun k ↦ gsumF Fc ks m n fun l ↦
      GPoly.smul O (O.mul (cgV Fc ks m C i k) (cgV Fc ks m Ci l j)) (A0 k l))
    (GPoly.mul O q [lsumC O ((List.finRange n).map fun k : Fin n ↦
      O.mul (O.deriv (cgV Fc ks m C i k)) (cgV Fc ks m Ci k j))])

/-- `P v` on polynomial codes. -/
def mvGP (m n : ℕ) (P : List (List (LC m))) (v : Fin n → GPoly (LC m)) : Fin n → GPoly (LC m) :=
  fun i ↦ gsumF Fc ks m n fun k ↦ GPoly.smul (MO Fc ks m) (cgV Fc ks m P i k) (v k)

/-- **Any solver behind a constant gauge `C`** (inverse `C⁻¹`, checked): solve the gauged system
for `Z = C Y` and map the solutions back with `C⁻¹`. -/
def gaugeSolver (m : ℕ) (solve : SysSolver m) (C Ci : List (List (LC m))) : SysSolver m :=
  fun n A0 q hh G0 ↦
    if invOKG Fc ks m n C Ci then
      (solve n (matFn (matData (gaugeAG Fc ks m n C Ci A0 q)) []) q hh
        (G0.map fun g ↦ listFn (matL (mvGP Fc ks m n C g)) [])).map
        fun r ↦ (r.1, r.2.map fun w ↦ (w.1, mvGP Fc ks m n Ci w.2))
    else none

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) {m : ℕ}

/-- The semantic matrix of a constant code matrix. -/
noncomputable def cMat (h : T.Tr m) (n : ℕ) (C : List (List (LC m))) : Matrix (Fin n) (Fin n) (T.F m) :=
  Matrix.of fun i j ↦ (T.MP m h).sem (cgV Fc ks m C i j)

lemma toPoly_gsumF (h : T.Tr m) {n : ℕ} (f : Fin n → GPoly (LC m)) :
    GPoly.toPoly (T.MP m h) (gsumF Fc ks m n f) = ∑ k, GPoly.toPoly (T.MP m h) (f k) := by
  unfold gsumF
  rw [Fin.sum_univ_def]
  induction (List.finRange n) with
  | nil => simp
  | cons a l ih => simp [ih]

lemma sem_mvGP (h : T.Tr m) {n : ℕ} (P : List (List (LC m))) (v : Fin n → GPoly (LC m)) :
    semV (T.MP m h) (mvGP Fc ks m n P v) =
      fun i ↦ ∑ k, Polynomial.C (T.cMat h n P i k) * semV (T.MP m h) v k := by
  funext i
  simp [semV, mvGP, T.toPoly_gsumF h, cMat]

lemma semMat_gaugeAG (h : T.Tr m) {n : ℕ} (C Ci : List (List (LC m)))
    (A0 : Fin n → Fin n → GPoly (LC m)) (q : GPoly (LC m)) :
    semMat (T.MP m h) (gaugeAG Fc ks m n C Ci A0 q) =
      gaugeA (GPoly.toPoly (T.MP m h) q) (T.cMat h n C) (T.cMat h n Ci) (semMat (T.MP m h) A0) := by
  refine Matrix.ext fun i j ↦ ?_
  simp only [semMat, gaugeAG, Matrix.of_apply, GPoly.toPoly_sub, T.toPoly_gsumF h,
    GPoly.toPoly_smul, GPoly.toPoly_mul, GPoly.toPoly_cons, GPoly.toPoly_nil, mul_zero, add_zero,
    T.sem_lsumC_fin h, (T.MP m h).sem_mul, (T.MP m h).sem_deriv, gaugeA, Matrix.sub_apply,
    Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, cMat, map_sum,
    Polynomial.C_mul, Finset.sum_mul]
  rw [sub_left_inj, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring

lemma cMat_mul (h : T.Tr m) {n : ℕ} (C Ci : List (List (LC m)))
    (hinv : invOKG Fc ks m n C Ci = true) :
    T.cMat h n C * T.cMat h n Ci = 1 ∧ T.cMat h n Ci * T.cMat h n C = 1 := by
  obtain ⟨h1, h2⟩ := T.invOKC_spec h C Ci hinv
  have key : ∀ A B : List (List (LC m)), (∀ v, mv (fun i j : Fin n ↦ (T.MP m h).sem (cgV Fc ks m A i j))
      (mv (fun i j : Fin n ↦ (T.MP m h).sem (cgV Fc ks m B i j)) v) = v) →
      T.cMat h n A * T.cMat h n B = 1 := by
    intro A B hAB
    ext i j
    have := congrFun (hAB (Pi.single j 1)) i
    simp only [mv, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at this
    simp only [Matrix.mul_apply, cMat, Matrix.of_apply, Matrix.one_apply]
    rw [this]
  exact ⟨key C Ci h1, key Ci C h2⟩

lemma mat_inv_vec {n : ℕ} (P Pinv : Matrix (Fin n) (Fin n) (T.F m)) (hP : Pinv * P = 1)
    (v : Fin n → (T.F m)[X]) (i : Fin n) :
    ∑ j, Polynomial.C (Pinv i j) * ∑ k, Polynomial.C (P j k) * v k = v i := by
  have hid : ∀ k, ∑ j, Polynomial.C (Pinv i j) * Polynomial.C (P j k) =
      if i = k then 1 else 0 := fun k ↦ by
    simp_rw [← Polynomial.C_mul, ← map_sum]
    rw [← Matrix.mul_apply, hP, Matrix.one_apply]
    split_ifs <;> simp
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hid]
  simp

lemma rhs_fwd (h : T.Tr m) {n : ℕ} (P : List (List (LC m))) (G0 : List (Fin n → GPoly (LC m)))
    (cs : ℕ → T.F m) (k : Fin n) :
    ∑ l ∈ Finset.range (G0.map (mvGP Fc ks m n P)).length, Polynomial.C (cs l) *
        GPoly.toPoly (T.MP m h) (((G0.map (mvGP Fc ks m n P)).getD l fun _ ↦ []) k) =
      ∑ j, Polynomial.C (T.cMat h n P k j) * ∑ l ∈ Finset.range G0.length, Polynomial.C (cs l) *
        GPoly.toPoly (T.MP m h) ((G0.getD l fun _ ↦ []) j) := by
  rw [List.length_map]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hl' : l < G0.length := Finset.mem_range.mp hl
  rw [List.getD_eq_getElem _ _ (by simpa using hl'), List.getD_eq_getElem _ _ hl',
    List.getElem_map]
  have := congrFun (T.sem_mvGP h P G0[l]) k
  simp only [semV] at this
  rw [this, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

lemma gaugeSolver_some {n : ℕ} (solve : SysSolver m) (C Ci : List (List (LC m)))
    (A0 : Fin n → Fin n → GPoly (LC m)) (q hh : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m)))
    (r : GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m))))
    (hres : gaugeSolver Fc ks m solve C Ci n A0 q hh G0 = some r) :
    invOKG Fc ks m n C Ci = true ∧ ∃ out0, solve n (gaugeAG Fc ks m n C Ci A0 q) q hh
      (G0.map (mvGP Fc ks m n C)) = some (r.1, out0) ∧
      r.2 = out0.map fun w ↦ (w.1, mvGP Fc ks m n Ci w.2) := by
  unfold gaugeSolver at hres
  simp only [matFn_matData, listFn_matL] at hres
  split_ifs at hres with hinv
  refine ⟨hinv, ?_⟩
  obtain ⟨⟨D0, out0⟩, h1, h2⟩ := Option.map_eq_some_iff.mp hres
  subst h2
  exact ⟨out0, h1, rfl⟩

lemma gaugeSolver_isSome {n : ℕ} (solve : SysSolver m) (C Ci : List (List (LC m)))
    (A0 : Fin n → Fin n → GPoly (LC m)) (q hh : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m)))
    (hinv : invOKG Fc ks m n C Ci = true)
    (hs : (solve n (gaugeAG Fc ks m n C Ci A0 q) q hh (G0.map (mvGP Fc ks m n C))).isSome) :
    (gaugeSolver Fc ks m solve C Ci n A0 q hh G0).isSome := by
  unfold gaugeSolver
  simp only [matFn_matData, listFn_matL]
  rw [if_pos hinv, Option.isSome_map]
  exact hs

/-- **The gauged solver meets the solver specification** whenever the inner solver does. -/
theorem gaugeSolver_spec (h0 : T.Tr m) (w b : T.F m) (solve : SysSolver m)
    (S : T.SolverSpecB m h0 w b solve) (C Ci : List (List (LC m))) :
    T.SolverSpecB m h0 w b (gaugeSolver Fc ks m solve C Ci) where
  hD := S.hD
  sound := fun n A0 q hh G0 Den out hres r hr ↦ by
    obtain ⟨hinv, out0, h1, h2⟩ := gaugeSolver_some solve C Ci A0 q hh G0 _ hres
    obtain ⟨hCCi, hCiC⟩ := T.cMat_mul h0 C Ci hinv
    simp only at h2
    subst h2
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
    have hs := S.sound n _ q hh _ Den out0 h1 r0 hr0
    rw [T.semMat_gaugeAG h0] at hs
    have hg := sysSol_gauge w b _ _ (T.cMat h0 n Ci) (T.cMat h0 n C) hCCi _ _ _ _ hs
    rw [gaugeA_inv _ _ _ hCiC hCCi] at hg
    simp only [T.rhs_fwd h0, T.mat_inv_vec _ _ hCiC] at hg
    rw [T.sem_mvGP h0]
    exact hg
  den := fun n A0 q hh G0 r hres ↦ by
    obtain ⟨hinv, out0, h1, h2⟩ := gaugeSolver_some solve C Ci A0 q hh G0 _ hres
    exact S.den n _ q hh _ (r.1, out0) h1
  complete := fun n A0 q hh G0 Den out hres c hc Z d hd hsol hdvd ↦ by
    obtain ⟨hinv, out0, h1, h2⟩ := gaugeSolver_some solve C Ci A0 q hh G0 _ hres
    obtain ⟨hCCi, hCiC⟩ := T.cMat_mul h0 C Ci hinv
    simp only at h2
    subst h2
    have hg := sysSol_gauge w b _ _ (T.cMat h0 n C) (T.cMat h0 n Ci) hCiC _ _ _ _ hsol
    rw [← T.semMat_gaugeAG h0] at hg
    simp only [← T.rhs_fwd h0] at hg
    have hc' : ∀ l, (G0.map (mvGP Fc ks m n C)).length ≤ l → c.getD l 0 = 0 := by
      simpa using hc
    obtain ⟨β, hβ1, hβ2⟩ := S.complete n _ q hh _ Den out0 h1 c hc' _ d hd hg (fun i ↦ by
      rw [Finset.mul_sum]
      exact Finset.dvd_sum fun k _ ↦ by
        rw [mul_left_comm]; exact Dvd.dvd.mul_left (hdvd k) _)
    refine ⟨β, fun l ↦ ?_, fun i ↦ ?_⟩
    · rw [hβ1 l, List.length_map]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hk' : k < out0.length := Finset.mem_range.mp hk
      rw [List.getD_eq_getElem (out0.map _) _ (by simpa using hk'),
        List.getD_eq_getElem out0 _ hk', List.getElem_map]
    · rw [← T.mat_inv_vec _ _ hCiC Z i, Finset.mul_sum, List.length_map]
      have e : ∀ j, GPoly.toPoly (T.MP m h0) Den *
          (Polynomial.C (T.cMat h0 n Ci i j) * ∑ k, Polynomial.C (T.cMat h0 n C j k) * Z k) =
          Polynomial.C (T.cMat h0 n Ci i j) * (d * ∑ k ∈ Finset.range out0.length,
            Polynomial.C (algebraMap Cc (T.F m) (β.getD k 0)) *
              semV (T.MP m h0) (out0.getD k ([], fun _ ↦ [])).2 j) := fun j ↦ by
        rw [← hβ2 j]; ring
      simp_rw [e]
      have hR : ∀ k ∈ Finset.range out0.length, semV (T.MP m h0)
          ((out0.map fun w ↦ (w.1, mvGP Fc ks m n Ci w.2)).getD k ([], fun _ ↦ [])).2 i =
          ∑ x, Polynomial.C (T.cMat h0 n Ci i x) *
            semV (T.MP m h0) (out0.getD k ([], fun _ ↦ [])).2 x := fun k hk ↦ by
        have hk' := Finset.mem_range.mp hk
        rw [List.getD_eq_getElem (out0.map _) _ (by simpa using hk'),
          List.getD_eq_getElem out0 _ hk', List.getElem_map, T.sem_mvGP h0]
      have hR2 : ∑ k ∈ Finset.range out0.length, Polynomial.C (algebraMap Cc (T.F m) (β.getD k 0)) *
          semV (T.MP m h0)
            ((out0.map fun w ↦ (w.1, mvGP Fc ks m n Ci w.2)).getD k ([], fun _ ↦ [])).2 i =
          ∑ k ∈ Finset.range out0.length, Polynomial.C (algebraMap Cc (T.F m) (β.getD k 0)) *
            ∑ x, Polynomial.C (T.cMat h0 n Ci i x) *
              semV (T.MP m h0) (out0.getD k ([], fun _ ↦ [])).2 x :=
        Finset.sum_congr rfl fun k hk ↦ by rw [hR k hk]
      rw [hR2]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

end MTower

end Curves.MT
