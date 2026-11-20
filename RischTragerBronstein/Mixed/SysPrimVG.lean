import RischTragerBronstein.Mixed.SysPrimV
import RischTragerBronstein.Mixed.NKLogDecide

/-!
# Coupled systems at a primitive level with a gauged triangular limit matrix

`primSysVG … C Ci`: as `primSysV`, but the limit matrix `Λ` need only become upper triangular
after a constant gauge transformation `Λ ↦ C Λ C⁻¹ − C′ C⁻¹` (codes `C`, `C⁻¹`, checked). The
system one level down `y′ + Λ y = w` is solved as `z′ + (C Λ C⁻¹ − C′ C⁻¹) z = C w`, `y = C⁻¹ z`
(`sysSpecAt_gauge`). This covers curves with several places at infinity, where `Λ` is
gauge-equivalent (over the code values) to a triangular matrix but not triangular in the given
basis. It meets the solver specification with known denominators (`primSpecVG`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Tower.Sys

section Gauge

variable {K Cs : Type*} [Field K] [Differential K] [CharZero K] [Field Cs] [CharZero Cs]
  (ι : Cs →+* K) {n : ℕ}

/-- The gauged matrix `C F C⁻¹ − C′ C⁻¹`. -/
def gaugeM (C Ci F : Fin n → Fin n → K) : Fin n → Fin n → K :=
  fun i j ↦ ∑ k, ∑ l, C i k * F k l * Ci l j - ∑ k, (C i k)′ * Ci k j

lemma mv_sum_smul {ι' : Type*} (P : Fin n → Fin n → K) (s : Finset ι') (a : ι' → K)
    (w : ι' → Fin n → K) (i : Fin n) :
    mv P (fun j ↦ ∑ l ∈ s, a l * w l j) i = ∑ l ∈ s, a l * mv P (w l) i := by
  simp only [mv, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- The gauge identity: `(C y)′ + G (C y) = C (y′ + F y)`. -/
lemma gauge_eq (C Ci F : Fin n → Fin n → K) (hCiC : ∀ v, mv Ci (mv C v) = v) (y : Fin n → K)
    (i : Fin n) :
    (mv C y i)′ + mv (gaugeM C Ci F) (mv C y) i = mv C (fun k ↦ (y k)′ + mv F y k) i := by
  have hy : ∀ l, ∑ j, Ci l j * mv C y j = y l := fun l ↦ by
    have := congrFun (hCiC y) l
    simpa [mv] using this
  simp only [mv, gaugeM, map_sum, Derivation.leibniz, smul_eq_mul, sub_mul, Finset.sum_mul,
    Finset.sum_sub_distrib]
  have e1 : ∑ j, ∑ k, ∑ l, C i k * F k l * Ci l j * ∑ j', C j j' * y j' =
      ∑ k, ∑ l, C i k * F k l * y l := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [← hy l, Finset.mul_sum]
    simp only [mv]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have e2 : ∑ j, ∑ k, (C i k)′ * Ci k j * ∑ j', C j j' * y j' = ∑ k, (C i k)′ * y k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← hy k, Finset.mul_sum]
    simp only [mv]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [e1, e2]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have e3 : ∑ k, ∑ l, C i k * F k l * y l = ∑ k, ∑ l, C i k * (F k l * y l) :=
    Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
  rw [e3]
  have e4 : ∑ x, y x * (C i x)′ = ∑ k, (C i k)′ * y k :=
    Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [e4]
  ring

/-- **Gauge transformation of the system specification.** -/
theorem sysSpecAt_gauge (hιd : ∀ κ : Cs, (ι κ)′ = 0) (C Ci F : Fin n → Fin n → K)
    (hCCi : ∀ v, mv C (mv Ci v) = v) (hCiC : ∀ v, mv Ci (mv C v) = v)
    (ws : List (Fin n → K)) (R : List (List ℚ × (Fin n → K)))
    (hR : SysSpecAt ι (gaugeM C Ci F) (ws.map (mv C)) R) :
    SysSpecAt ι F ws (R.map fun r ↦ (r.1, mv Ci r.2)) := by
  classical
  obtain ⟨hs, hc⟩ := hR
  have hlen : (ws.map (mv C)).length = ws.length := List.length_map _
  have hget : ∀ l, (ws.map (mv C)).getD l 0 = mv C (ws.getD l 0) := fun l ↦ by
    by_cases hl : l < ws.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
        List.getD_eq_getElem _ _ hl]
    · rw [List.getD_eq_default _ _ (by simpa using hl), List.getD_eq_default _ _ (by omega)]
      funext i; simp [mv]
  -- the equation for `y` from the one for `z = C y`
  have hback : ∀ (y : Fin n → K) (rhs : Fin n → K),
      (∀ i, (mv C y i)′ + mv (gaugeM C Ci F) (mv C y) i = mv C rhs i) →
      ∀ i, (y i)′ + mv F y i = rhs i := by
    intro y rhs h i
    have h1 : mv C (fun k ↦ (y k)′ + mv F y k) = mv C rhs := funext fun i ↦ by
      rw [← gauge_eq C Ci F hCiC y i]; exact h i
    have := congrArg (mv Ci) h1
    rw [hCiC, hCiC] at this
    exact congrFun this i
  refine ⟨fun r hr i ↦ ?_, fun c hcl y hy ↦ ?_⟩
  · obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
    have h := hs r0 hr0
    dsimp only
    refine hback (mv Ci r0.2) (fun i ↦ ∑ l ∈ Finset.range ws.length,
      ((r0.1.getD l 0 : ℚ) : K) * ws.getD l 0 i) (fun i ↦ ?_) i
    rw [hCCi, h i, hlen]
    simp only [hget]
    rw [mv_sum_smul]
  · obtain ⟨β, hβ1, hβ2⟩ := hc c (by rwa [hlen]) (mv C y) (fun i ↦ by
      rw [gauge_eq C Ci F hCiC y i, hlen]
      simp only [hget]
      rw [← mv_sum_smul]
      congr 1
      funext k
      exact hy k)
    have hRk : ∀ k < R.length, (R.map fun r ↦ (r.1, mv Ci r.2)).getD k ([], 0) =
        ((R.getD k ([], 0)).1, mv Ci (R.getD k ([], 0)).2) := fun k hk ↦ by
      rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
        List.getD_eq_getElem _ _ hk]
    refine ⟨β, fun l ↦ ?_, fun i ↦ ?_⟩
    · rw [hβ1 l, List.length_map]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [hRk k (Finset.mem_range.mp hk)]
    · have h1 := congrArg (mv Ci) (funext hβ2)
      rw [hCiC] at h1
      rw [congrFun h1 i, mv_sum_smul, List.length_map]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [hRk k (Finset.mem_range.mp hk)]

end Gauge

end Tower.Sys

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- An entry of a code matrix. -/
def cgV (m : ℕ) (C : List (List (LC m))) (i j : ℕ) : LC m := (C.getD i []).getD j (MO Fc ks m).zero

/-- The gauged code matrix `C Λ C⁻¹ − C′ C⁻¹`. -/
def gaugeLG (m n : ℕ) (C Ci : List (List (LC m))) (Λc : Fin n → Fin n → LC m) :
    Fin n → Fin n → LC m :=
  let O := MO Fc ks m
  fun i j ↦ O.add (lsumC O ((List.finRange n).map fun k : Fin n ↦ lsumC O ((List.finRange n).map
      fun l : Fin n ↦ O.mul (O.mul (cgV Fc ks m C i k) (Λc k l)) (cgV Fc ks m Ci l j))))
    (O.neg (lsumC O ((List.finRange n).map fun k : Fin n ↦
      O.mul (O.deriv (cgV Fc ks m C i k)) (cgV Fc ks m Ci k j))))

/-- `P v` on codes. -/
def mvG (m n : ℕ) (P : List (List (LC m))) (v : Fin n → LC m) : Fin n → LC m :=
  fun i ↦ lsumC (MO Fc ks m) ((List.finRange n).map fun j : Fin n ↦
    (MO Fc ks m).mul (cgV Fc ks m P i j) (v j))

/-- The check `C C⁻¹ = C⁻¹ C = 1`. -/
def invOKG (m n : ℕ) (C Ci : List (List (LC m))) : Bool :=
  let O := MO Fc ks m
  (List.finRange n).all fun i : Fin n ↦ (List.finRange n).all fun j : Fin n ↦
    O.isZero (O.add (lsumC O ((List.finRange n).map fun k : Fin n ↦
      O.mul (cgV Fc ks m C i k) (cgV Fc ks m Ci k j))) (O.neg (if i = j then O.one else O.zero))) &&
    O.isZero (O.add (lsumC O ((List.finRange n).map fun k : Fin n ↦
      O.mul (cgV Fc ks m Ci i k) (cgV Fc ks m C k j))) (O.neg (if i = j then O.one else O.zero)))

/-- The gauged triangular solver one level down. -/
def gaugeLowG (m : ℕ) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (FRep (LC m))) (C Ci : List (List (LC m))) (n : ℕ) (Λc : Fin n → Fin n → LC m)
    (ws : List (Fin n → LC m)) : List (List ℚ × (Fin n → LC m)) :=
  (triLowC Fc ks m rde dg n (matFn (matData (gaugeLG Fc ks m n C Ci Λc)) (MO Fc ks m).zero)
    (ws.map fun w ↦ listFn (matL (mvG Fc ks m n C w)) (MO Fc ks m).zero)).map
    fun r ↦ (r.1, listFn (matL (mvG Fc ks m n Ci r.2)) (MO Fc ks m).zero)

/-- **The solver with a gauge at infinity**. -/
def primSysVG (m : ℕ) (η : LC m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (dg : List (FRep (LC m))) (C Ci : List (List (LC m))) (n : ℕ)
    (A0 : Fin n → Fin n → GPoly (LC m)) (q h : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m))) :
    Option (GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))) :=
  if invOKG Fc ks m n C Ci &&
      triOKC Fc ks m dg n (gaugeLG Fc ks m n C Ci (lamCL Fc ks m η n A0 q h G0 0)) then
    primSysBL Fc ks m η n (gaugeLowG Fc ks m rde dg C Ci n) A0 q h G0 0
  else none

universe u

variable {Fc ks} {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) {m : ℕ}

lemma sem_lsumC_fin (h : T.Tr m) {n : ℕ} (g : Fin n → LC m) :
    (T.MP m h).sem (lsumC (MO Fc ks m) ((List.finRange n).map g)) = ∑ k, (T.MP m h).sem (g k) := by
  rw [sem_lsumC, List.map_map, Fin.sum_univ_def]
  rfl

lemma sem_gaugeLC (h : T.Tr m) {n : ℕ} (C Ci : List (List (LC m))) (Λc : Fin n → Fin n → LC m) :
    (fun i j ↦ (T.MP m h).sem (gaugeLG Fc ks m n C Ci Λc i j)) =
      gaugeM (fun i j : Fin n ↦ (T.MP m h).sem (cgV Fc ks m C i j))
        (fun i j : Fin n ↦ (T.MP m h).sem (cgV Fc ks m Ci i j))
        (fun i j ↦ (T.MP m h).sem (Λc i j)) := by
  funext i j
  simp only [gaugeLG, gaugeM, (T.MP m h).sem_add, (T.MP m h).sem_neg, T.sem_lsumC_fin h,
    (T.MP m h).sem_mul, (T.MP m h).sem_deriv, sub_eq_add_neg]

lemma sem_mvC (h : T.Tr m) {n : ℕ} (P : List (List (LC m))) (v : Fin n → LC m) :
    semVa (T.MP m h) (mvG Fc ks m n P v) =
      mv (fun i j : Fin n ↦ (T.MP m h).sem (cgV Fc ks m P i j)) (semVa (T.MP m h) v) := by
  funext i
  simp only [semVa, mvG, mv, T.sem_lsumC_fin h, (T.MP m h).sem_mul]

lemma invOKC_spec (h : T.Tr m) {n : ℕ} (C Ci : List (List (LC m)))
    (hok : invOKG Fc ks m n C Ci = true) :
    (∀ v, mv (fun i j : Fin n ↦ (T.MP m h).sem (cgV Fc ks m C i j))
      (mv (fun i j : Fin n ↦ (T.MP m h).sem (cgV Fc ks m Ci i j)) v) = v) ∧
    (∀ v, mv (fun i j : Fin n ↦ (T.MP m h).sem (cgV Fc ks m Ci i j))
      (mv (fun i j : Fin n ↦ (T.MP m h).sem (cgV Fc ks m C i j)) v) = v) := by
  classical
  set M := T.MP m h with hM
  simp only [invOKG, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true] at hok
  have hprod : ∀ (A B : List (List (LC m))),
      (∀ i j : Fin n, (MO Fc ks m).isZero ((MO Fc ks m).add (lsumC (MO Fc ks m)
        ((List.finRange n).map fun k : Fin n ↦ (MO Fc ks m).mul (cgV Fc ks m A i k)
          (cgV Fc ks m B k j))) ((MO Fc ks m).neg
            (if i = j then (MO Fc ks m).one else (MO Fc ks m).zero))) = true) →
      ∀ v, mv (fun i j : Fin n ↦ M.sem (cgV Fc ks m A i j))
        (mv (fun i j : Fin n ↦ M.sem (cgV Fc ks m B i j)) v) = v := by
    intro A B hAB v
    have hid : ∀ i j : Fin n, ∑ k : Fin n, M.sem (cgV Fc ks m A i k) * M.sem (cgV Fc ks m B k j) =
        if i = j then 1 else 0 := by
      intro i j
      have := (M.isZero_iff _).mp (hAB i j)
      rw [M.sem_add, M.sem_neg, T.sem_lsumC_fin h, add_neg_eq_zero] at this
      simp only [(T.MP m h).sem_mul] at this
      rw [this]
      split_ifs
      · exact M.sem_one
      · exact M.sem_zero
    funext i
    simp only [mv, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [← mul_assoc, ← Finset.sum_mul, hid]
    simp
  exact ⟨hprod C Ci fun i j ↦ (hok i j).1, hprod Ci C fun i j ↦ (hok i j).2⟩

/-- **The gauged lower solver meets the system specification.** -/
theorem gaugeLowG_spec (h : T.Tr m) (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h) ((T.MP m h).sem (fCode (MO Fc ks m) fr)) (rde fr))
    (dg : List (FRep (LC m))) (C Ci : List (List (LC m))) (n : ℕ) (Λc : Fin n → Fin n → LC m)
    (hinv : invOKG Fc ks m n C Ci = true)
    (hok : triOKC Fc ks m dg n (gaugeLG Fc ks m n C Ci Λc) = true) (ws : List (Fin n → LC m)) :
    SysSpecAt (algebraMap Cc (T.F m)) (fun i j ↦ (T.MP m h).sem (Λc i j))
      (ws.map (semVa (T.MP m h))) (semR (T.MP m h) (gaugeLowG Fc ks m rde dg C Ci n Λc ws)) := by
  set M := T.MP m h with hM
  obtain ⟨hCCi, hCiC⟩ := T.invOKC_spec h C Ci hinv
  have hlow := T.triLowC_spec h rde hrde dg n _ hok (ws.map (mvG Fc ks m n C))
  rw [T.sem_gaugeLC h] at hlow
  have hws : (ws.map (mvG Fc ks m n C)).map (semVa M) =
      (ws.map (semVa M)).map (mv fun i j : Fin n ↦ M.sem (cgV Fc ks m C i j)) := by
    simp only [List.map_map]
    exact List.map_congr_left fun w _ ↦ T.sem_mvC h C w
  rw [hws] at hlow
  have hR : semR M (gaugeLowG Fc ks m rde dg C Ci n Λc ws) =
      (semR M (triLowC Fc ks m rde dg n (gaugeLG Fc ks m n C Ci Λc)
        (ws.map (mvG Fc ks m n C)))).map
        fun r ↦ (r.1, mv (fun i j : Fin n ↦ M.sem (cgV Fc ks m Ci i j)) r.2) := by
    simp only [gaugeLowG, semR, List.map_map, matFn_matData, listFn_matL]
    refine List.map_congr_left fun r _ ↦ ?_
    simp only [Function.comp_apply, Prod.mk.injEq, true_and]
    exact T.sem_mvC h Ci r.2
  rw [hR]
  exact sysSpecAt_gauge _ (fun κ ↦ by rw [deriv_algebraMap, T.hC, map_zero]) _ _ _
    hCCi hCiC _ _ hlow


/-- **`primSysVG` meets the solver specification with known denominators** (primitive level). -/
theorem primSpecVG (hm : m < T.n) (h0 : T.Tr m) {η : LC m} (hk : ks m = .prim η)
    (rde : FRep (LC m) → List (LC m) → List (List ℚ × LC m))
    (hrde : ∀ fr : FRep (LC m), FRepOK (T.MP m h0) fr →
      RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h0) ((T.MP m h0).sem (fCode (MO Fc ks m) fr))
        (rde fr))
    (dg : List (FRep (LC m))) (C Ci : List (List (LC m))) :
    T.SolverSpecB m h0 ((T.MP m h0).sem η) 0
      (fun n A0 q hh G0 ↦ primSysVG Fc ks m η rde dg C Ci n A0 q hh G0) where
  hD := T.phi_DzL m hm hk h0
  sound := fun n A0 q hh G0 Den out hres ↦ by
    have hres' := hres
    unfold primSysVG at hres'
    split_ifs at hres' with htri
    exact T.primSysBL_sound m h0 η n A0 q hh G0 0 _ Den out hres'
  den := fun n A0 q hh G0 r hres ↦ by
    have hres' := hres
    unfold primSysVG at hres'
    split_ifs at hres' with htri
    unfold primSysBL at hres'
    simp only at hres'
    split_ifs at hres' with hmon
    split at hres'
    · exact absurd hres' (by simp)
    have hmon' : (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hh) = true := by
      revert hmon; cases (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hh) <;> simp
    have hq := (isMonicC_spec (T.MP m h0) q (Bool.and_eq_true_iff.mp hmon').1).ne_zero
    have hh' := (isMonicC_spec (T.MP m h0) hh (Bool.and_eq_true_iff.mp hmon').2).ne_zero
    refine ⟨?_, hq, hh'⟩
    rw [← Option.some.inj hres', T.wSys_Den m h0 η n A0 q hh G0 0]
    exact mul_ne_zero hh' (pow_ne_zero _ hq)
  complete := fun n A0 q hh G0 Den out hres c hc Z d hd hsol hdvd ↦ by
    have hres' := hres
    unfold primSysVG at hres'
    split_ifs at hres' with htri
    obtain ⟨hinv, hok⟩ := Bool.and_eq_true_iff.mp htri
    exact T.primSysBL_complete m h0 η n A0 q hh G0 0 _
      (fun ws ↦ T.gaugeLowG_spec h0 rde hrde dg C Ci n _ hinv hok ws) Den out hres' c hc Z d hd
      hsol (fun i ↦ by rw [pow_zero, mul_one]; exact hdvd i)

end MTower

end Curves.MT
