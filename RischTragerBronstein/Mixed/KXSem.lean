import RischTragerBronstein.Mixed.KXCodes
import RischTragerBronstein.Mixed.KXGen
import RischTragerBronstein.Mixed.KXExp2

/-!
# Square roots over an exponential level with poles: the values of the codes of `kxDecide`

* `sem_kxR`, `sem_kxD`, `sem_kxQ`: `R_q = c_qᵏ ∏_{q' ≠ q} (c_q − c_{q'}) A(c_q)ˡ`,
  `η c_q − c_q′`, `Q_q = B(c_q)² A(c_q)/((η c_q − c_q′) R_q)²`;
* the classes of the poles (as for `kqmDecide`);
* `kx_data`: the data of the abstract theorems on `y² = A(x)`, `x = t`, for the integrand
  `B/(tᵏ ∏ (t − c_q) Aˡ) · θ`.
-/

open Polynomial Differential IntermediateField

set_option linter.unusedSectionVars false

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma toPoly_monoG (m : ℕ) (hm : T.Tr m) (k : ℕ) :
    GPoly.toPoly (T.MP m hm) (monoG Fc ks m k) = X ^ k := by
  induction k with
  | zero => simp [monoG, (T.MP m hm).sem_one]
  | succ k ih =>
    have e : monoG Fc ks m (k + 1) = (MO Fc ks m).zero :: monoG Fc ks m k := by
      simp [monoG, List.replicate_succ]
    rw [e, GPoly.toPoly_cons, ih, (T.MP m hm).sem_zero, map_zero, zero_add, pow_succ, mul_comm]

/-- **The good places** of an exponential level, in the form of the abstract theorems. -/
lemma kxS_good (m : ℕ) (hM : T.MixHyp (m + 1)) {g : LC m} (hk : ks m = .exp g) :
    ∀ α : AlgebraicClosure (T.F m), ¬ α = 0 →
      α′ ≠ ((Polynomial.C (T.val m g)′ * X).map (algebraMap (T.F m) _)).eval α := by
  intro α hα
  have := T.keS_good m hM hk α hα
  simpa [Polynomial.eval_map] using this

section XCodes

variable [Fact (Irreducible (toPoly (fKc Fc)))]
variable (m : ℕ) (hm : T.Tr m) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))

lemma kxOK_spec (hok : kxOK Fc ks m A B kt l cs = true) :
    (T.MP m hm).sem (A.getD 0 (MO Fc ks m).zero) ≠ 0 ∧ ∀ q < cs.length,
    (T.MP m hm).sem (kqC Fc ks m cs q) ≠ 0 ∧
    (T.MP m hm).sem (kxR Fc ks m A kt l cs q) ≠ 0 ∧
      (GPoly.toPoly (T.MP m hm) A).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) ≠ 0 ∧
      (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) ≠ 0 := by
  have ne : ∀ z : LC m, (MO Fc ks m).isZero z = false → (T.MP m hm).sem z ≠ 0 := fun z hz h0 ↦ by
    rw [← (T.MP m hm).isZero_iff] at h0; rw [h0] at hz; exact Bool.noConfusion hz
  simp only [kxOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hok
  refine ⟨ne _ hok.1, fun q hq ↦ ?_⟩
  have h := List.all_eq_true.mp hok.2 q (List.mem_range.mpr hq)
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  refine ⟨ne _ h0, ne _ h1, ?_, ?_⟩
  · rw [← T.sem_evalGC m hm]; exact ne _ h2
  · rw [← T.sem_evalGC m hm]; exact ne _ h3

lemma sem_kxR (q : ℕ) :
    (T.MP m hm).sem (kxR Fc ks m A kt l cs q) =
      (GPoly.toPoly (T.MP m hm) (prodLinG Fc ks m (cs.eraseIdx q))).eval
        ((T.MP m hm).sem (kqC Fc ks m cs q)) * (T.MP m hm).sem (kqC Fc ks m cs q) ^ kt *
      (GPoly.toPoly (T.MP m hm) A).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) ^ l := by
  rw [kxR, T.sem_normC m hm, (T.MP m hm).sem_mul, (T.MP m hm).sem_mul, T.sem_evalGC m hm, sem_powC,
    sem_powC, T.sem_evalGC m hm]

lemma sem_kxD (q : ℕ) :
    (T.MP m hm).sem (kxD Fc ks m g cs q) =
      ((T.MP m hm).sem g)′ * (T.MP m hm).sem (kqC Fc ks m cs q) -
        ((T.MP m hm).sem (kqC Fc ks m cs q))′ := by
  rw [kxD, subC, (T.MP m hm).sem_add, (T.MP m hm).sem_neg, (T.MP m hm).sem_mul,
    (T.MP m hm).sem_deriv, (T.MP m hm).sem_deriv, sub_eq_add_neg]

lemma sem_kxQ (q : ℕ) :
    (T.MP m hm).sem (kxQ Fc ks m g A B kt l cs q) =
      (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) ^ 2 *
        (GPoly.toPoly (T.MP m hm) A).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) /
        ((T.MP m hm).sem (kxD Fc ks m g cs q) * (T.MP m hm).sem (kxR Fc ks m A kt l cs q)) ^ 2 := by
  simp only [kxQ]
  rw [T.sem_normC m hm, (T.MP m hm).sem_mul, (T.MP m hm).sem_mul, (T.MP m hm).sem_mul,
    (T.MP m hm).sem_inv, (T.MP m hm).sem_mul, (T.MP m hm).sem_mul, T.sem_evalGC m hm,
    T.sem_evalGC m hm]
  ring

lemma kxConst_spec (hc : kxConst Fc ks m g A B kt l cs = true) (q : ℕ) (hq : q < cs.length) :
    (T.MP m hm).sem (kxQ Fc ks m g A B kt l cs q) = ((kxK Fc ks m g A B kt l cs q : ℚ) : T.F m) := by
  have h := List.all_eq_true.mp hc q (List.mem_range.mpr hq)
  have hd : ((T.MP m hm).sem (kxQ Fc ks m g A B kt l cs q))′ = 0 := by
    rw [← (T.MP m hm).sem_deriv]; exact ((T.MP m hm).isZero_iff _).mp h
  exact T.ratValC_of_const m hm _ hd

lemma kxConst_of (hq : ∀ q < cs.length,
    ((T.MP m hm).sem (kxQ Fc ks m g A B kt l cs q))′ = 0) : kxConst Fc ks m g A B kt l cs = true := by
  refine List.all_eq_true.mpr fun q hqm ↦ ?_
  rw [(T.MP m hm).isZero_iff, (T.MP m hm).sem_deriv]
  exact hq q (List.mem_range.mp hqm)

end XCodes

section XCodes

variable [Fact (Irreducible (toPoly (fKc Fc)))]
variable (m : ℕ) (hm : T.Tr m) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))

omit [CharZero Cc] [CharZero L] in
lemma kxGens_spec :
    SqrtIndep.MIndep (kxGens Fc ks m g A B kt l cs) ∧ ∀ x ∈ kxGens Fc ks m g A B kt l cs, x ≠ 0 := by
  obtain ⟨h1, h2, -⟩ := gensOf_spec (kxKs Fc ks m g A B kt l cs)
  exact ⟨h1, h2⟩

omit [CharZero Cc] [CharZero L] in
lemma kxRep_spec (hrep : kxRepOK Fc ks m g A B kt l cs = true) (q : ℕ) (hq : q < cs.length) :
    (kxRep Fc ks m g A B kt l cs q).1.length = (kxGens Fc ks m g A B kt l cs).length ∧
      kxK Fc ks m g A B kt l cs q = (kxRep Fc ks m g A B kt l cs q).2 ^ 2 *
        kxS Fc ks m g A B kt l cs (kxRep Fc ks m g A B kt l cs q).1 ∧
      0 ≤ (kxRep Fc ks m g A B kt l cs q).2 := by
  have h := List.all_eq_true.mp hrep q (List.mem_range.mpr hq)
  obtain ⟨⟨T', c'⟩, hTc⟩ := Option.isSome_iff_exists.mp h
  have hr : kxRep Fc ks m g A B kt l cs q = (T', c') := by simp [kxRep, hTc]
  rw [hr]
  exact findRep_spec _ (kxGens_spec m g A B kt l cs).2 _ T' c' hTc

omit [CharZero Cc] [CharZero L] in
lemma kxMNm_eq (q : ℕ) (hq : q < cs.length) (h0 : 0 ≤ (kxRep Fc ks m g A B kt l cs q).2) :
    (kxMNm Fc ks m g A B kt l cs q : ℚ) =
      kxDenM Fc ks m g A B kt l cs * (kxRep Fc ks m g A B kt l cs q).2 := by
  set x := (kxRep Fc ks m g A B kt l cs q).2 with hx
  have hdvd : x.den ∣ kxDenM Fc ks m g A B kt l cs := by
    apply List.dvd_prod
    exact List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩
  obtain ⟨k, hk⟩ := hdvd
  have hk' : kxDenM Fc ks m g A B kt l cs / x.den = k := by
    rw [hk, Nat.mul_div_cancel_left _ x.den_pos]
  have hnn : 0 ≤ ((k : ℤ) * x.num) := mul_nonneg (by positivity) (Rat.num_nonneg.mpr h0)
  simp only [kxMNm, ← hx, hk']
  rw [show (((k : ℤ) * x.num).toNat : ℚ) = (((k : ℤ) * x.num : ℤ) : ℚ) by
    rw [← Int.toNat_of_nonneg hnn]; rfl]
  rw [hk]
  push_cast
  rw [mul_comm (x.den : ℚ), mul_assoc, mul_comm (x.den : ℚ), Rat.mul_den_eq_num]

omit [CharZero Cc] [CharZero L] in
lemma kxDenM_pos : 0 < kxDenM Fc ks m g A B kt l cs :=
  List.prod_pos fun x hx ↦ by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact Rat.den_pos _

lemma sem_kxBm (q : ℕ) :
    (T.MP m hm).sem (kxBm Fc ks m g A B kt l cs q) =
      ((kxS Fc ks m g A B kt l cs (kxRep Fc ks m g A B kt l cs q).1 * (kxRep Fc ks m g A B kt l cs q).2 : ℚ) :
        T.F m) * ((T.MP m hm).sem (kxD Fc ks m g cs q) * (T.MP m hm).sem (kxR Fc ks m A kt l cs q) /
          (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q))) := by
  simp only [kxBm]
  rw [T.sem_normC m hm, (T.MP m hm).sem_mul, T.sem_mcst, (T.MP m hm).sem_mul, (T.MP m hm).sem_mul,
    (T.MP m hm).sem_inv, T.sem_evalGC m hm]
  ring

lemma toPoly_kxFKm (T' : List Bool) :
    (toPoly (kxFKm Fc ks m g A B kt l cs T')).map (T.psiF m hm) =
      Polynomial.C ((kxS Fc ks m g A B kt l cs T' : ℚ) : T.F m) * GPoly.toPoly (T.MP m hm) A := by
  rw [kxFKm, CPoly.toPoly_trim, T.toPoly_trC_map m hm]
  have e : A.map ((MO Fc ks m).mul (mcst Fc ks m (kxS Fc ks m g A B kt l cs T'))) =
      GPoly.smul (MO Fc ks m) (mcst Fc ks m (kxS Fc ks m g A B kt l cs T')) A := rfl
  rw [e, GPoly.toPoly_smul, T.sem_mcst]

omit [CharZero Cc] [CharZero L] in
lemma mem_kxQs (T' : List Bool) (q : ℕ) :
    q ∈ kxQs Fc ks m g A B kt l cs T' ↔ q < cs.length ∧ (kxRep Fc ks m g A B kt l cs q).1 = T' := by
  simp [kxQs, List.mem_filter, List.mem_range]

omit [CharZero Cc] [CharZero L] in
lemma kxQs_nodup (T' : List Bool) : (kxQs Fc ks m g A B kt l cs T').Nodup :=
  (List.nodup_range).filter _

end XCodes

section XClasses

variable [Fact (Irreducible (toPoly (fKc Fc)))]
variable (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))

omit [CharZero Cc] [CharZero L] in
lemma mem_kxCls (q : ℕ) (hq : q < cs.length) :
    (kxRep Fc ks m g A B kt l cs q).1 ∈ kxCls Fc ks m g A B kt l cs := by
  rw [kxCls, List.mem_dedup]
  exact List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩

omit [CharZero Cc] [CharZero L] in
lemma kxCls_nodup : (kxCls Fc ks m g A B kt l cs).Nodup := List.nodup_dedup _

omit [CharZero Cc] [CharZero L] in
lemma kxCls_mem_rep (T' : List Bool) (hT : T' ∈ kxCls Fc ks m g A B kt l cs) :
    ∃ q < cs.length, (kxRep Fc ks m g A B kt l cs q).1 = T' := by
  rw [kxCls, List.mem_dedup] at hT
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hT
  exact ⟨q, List.mem_range.mp hq, rfl⟩

/-- The class of a pole. -/
def kxCl (q : Fin cs.length) : Fin (kxCls Fc ks m g A B kt l cs).length :=
  ⟨(kxCls Fc ks m g A B kt l cs).idxOf (kxRep Fc ks m g A B kt l cs q).1,
    List.idxOf_lt_length_of_mem (mem_kxCls m g A B kt l cs q q.2)⟩

omit [CharZero Cc] [CharZero L] in
lemma kxCls_get_kxCl (q : Fin cs.length) :
    (kxCls Fc ks m g A B kt l cs)[(kxCl m g A B kt l cs q : ℕ)] = (kxRep Fc ks m g A B kt l cs q).1 :=
  List.getElem_idxOf _

omit [CharZero Cc] [CharZero L] in
lemma kxCl_eq_iff (q : Fin cs.length) (k : Fin (kxCls Fc ks m g A B kt l cs).length) :
    kxCl m g A B kt l cs q = k ↔ (kxRep Fc ks m g A B kt l cs q).1 = (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] := by
  constructor
  · rintro rfl; exact (kxCls_get_kxCl m g A B kt l cs q).symm
  · intro h
    apply Fin.ext
    simp only [kxCl, h]
    exact (kxCls_nodup m g A B kt l cs).idxOf_getElem _ _

/-- The poles of the class `k`. -/
def kxIota (k : Fin (kxCls Fc ks m g A B kt l cs).length)
    (i : Fin (kxQs Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)]).length) :
    Fin cs.length :=
  ⟨(kxQs Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)])[i],
    ((mem_kxQs m g A B kt l cs _ _).mp (List.getElem_mem _)).1⟩

omit [CharZero Cc] [CharZero L] in
lemma kxIota_cl (k : Fin (kxCls Fc ks m g A B kt l cs).length) (i) :
    kxCl m g A B kt l cs (kxIota m g A B kt l cs k i) = k :=
  (kxCl_eq_iff m g A B kt l cs _ k).mpr ((mem_kxQs m g A B kt l cs _ _).mp (List.getElem_mem _)).2

omit [CharZero Cc] [CharZero L] in
lemma kxIota_surj (k : Fin (kxCls Fc ks m g A B kt l cs).length) (q : Fin cs.length)
    (hq : kxCl m g A B kt l cs q = k) : ∃ i, kxIota m g A B kt l cs k i = q := by
  have hmem : (q : ℕ) ∈ kxQs Fc ks m g A B kt l cs (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] :=
    (mem_kxQs m g A B kt l cs _ _).mpr ⟨q.2, (kxCl_eq_iff m g A B kt l cs q k).mp hq⟩
  obtain ⟨i, hi, hiq⟩ := List.getElem_of_mem hmem
  exact ⟨⟨i, hi⟩, Fin.ext hiq⟩

omit [CharZero Cc] [CharZero L] in
lemma kxIota_inj (k : Fin (kxCls Fc ks m g A B kt l cs).length) :
    Function.Injective (kxIota m g A B kt l cs k) := fun i j h ↦ by
  have := congrArg Fin.val h
  simp only [kxIota] at this
  exact Fin.ext ((kxQs_nodup m g A B kt l cs _).getElem_inj_iff.mp this)

end XClasses

end MTower

end Curves.MT
