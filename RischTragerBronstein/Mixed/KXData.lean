import RischTragerBronstein.Mixed.KXSem

/-!
# Square roots over an exponential level with poles: the data on the curve

* `kx_data`: for `y = θ`, `y² = A(x)` over `Fₘ` (`x = t`), the integrand
  `B/(tᵏ ∏ (t − c_q) Aˡ) · θ` is `b y` with `D = xᵏ ∏ (x − c_q)`, `R_q = xᵏ ∏_{q' ≠ q} (x − c_{q'})`;
* `kx_cinj`, `kxK_ne`: the poles are distinct, the squared residues non-zero;
* `kx_forward_const`: an elementary integral forces constant squared residues;
* `kxm_pole`, `kxm_class_KF`, `kxm_abs`: the points of the poles and the classes, as for a
  logarithmic level.
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

section XData

variable [Fact (Irreducible (toPoly (fKc Fc)))]
variable (m : ℕ) (h : T.Tr (m + 1)) (A : GPoly (LC m))
  (hsq : Squarefree (GPoly.toPoly (T.MP m h.of_succ) A))
  (hdeg : 0 < (GPoly.toPoly (T.MP m h.of_succ) A).natDegree)
  (θ : L) (hθ : θ ^ 2 = T.evP m A)

include h in
/-- The value of the integrand's rational part. -/
lemma ev_rhsX (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) :
    T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) =
      T.evP m B / (T.ts m ^ kt * T.evP m (prodLinG Fc ks m cs) * T.evP m A ^ l) := by
  rw [show T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) =
      T.evP m B / T.evP m (kxDen Fc ks m A kt l cs) from rfl, kxDen,
    ← T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ) (GPoly.mul _ _ _),
    GPoly.toPoly_mul, GPoly.toPoly_mul, map_mul, map_mul, T.toPoly_monoG m h.of_succ,
    T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ),
    T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ), T.evP_powG m h.of_succ]
  simp

/-- **The data of the abstract theorems** for the curve `y = θ`, `y² = A(x)` over `Fₘ`:
`b = f`, `D = xᵏ ∏ (x − c_q)`, `R_q = xᵏ ∏_{q' ≠ q} (x − c_{q'})`, `P = B`. -/
theorem kx_data (hmn : m < T.n) (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (hA0 : T.evP m A ≠ 0) :
    let S := T.keS m h A hsq hdeg θ hθ 1 one_ne_zero
    let f : LC (m + 1) := (B, kxDen Fc ks m A kt l cs)
    let b := T.ev (m + 1) f / (((1 : T.F m) : T.F m) : L)
    let c : Fin cs.length → T.F m := fun q ↦ (T.MP m h.of_succ).sem (kqC Fc ks m cs q)
    let D := X ^ kt * GPoly.toPoly (T.MP m h.of_succ) (prodLinG Fc ks m cs)
    let R : Fin cs.length → (T.F m)[X] := fun q ↦
      X ^ kt * GPoly.toPoly (T.MP m h.of_succ) (prodLinG Fc ks m (cs.eraseIdx q))
    let P := Polynomial.C ((1 : T.F m) ^ (2 * l) / 1) * GPoly.toPoly (T.MP m h.of_succ) B
    b ∈ (T.F m)⟮S.x⟯ ∧ b * S.y = T.ev (m + 1) f * θ ∧ b * S.y ∈ (T.F m)⟮S.x⟯⟮S.y⟯ ∧
      (∀ q, D = (X - Polynomial.C (c q)) * R q) ∧
      (∀ α : AlgebraicClosure (T.F m), ¬ α = 0 → (∀ q, α ≠ algebraMap (T.F m) _ (c q)) →
        (D.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval α ≠ 0) ∧
      b * aeval S.x (D * S.p ^ l) = aeval S.x P := by
  intro S f b c D R P
  have hTm : T.Tr m := h.of_succ
  have hf : T.ev (m + 1) f =
      T.evP m B / (T.ts m ^ kt * T.evP m (prodLinG Fc ks m cs) * T.evP m A ^ l) :=
    T.ev_rhsX m h A B kt l cs
  have hxm : ∀ Q : (T.F m)[X], aeval (T.ts m) Q ∈ (T.F m)⟮S.x⟯ := fun Q ↦ by
    letI := algebraAdjoinSimple (F := T.F m) S.x
    rw [show aeval (T.ts m) Q = aeval S.x Q from rfl, ← algebraMap_adjoinSimple (F := T.F m) S.x Q]
    exact SetLike.coe_mem _
  have hev : ∀ Q : GPoly (LC m), T.evP m Q ∈ (T.F m)⟮S.x⟯ := fun Q ↦ by
    rw [← T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]; exact hxm _
  have hts : T.ts m ∈ (T.F m)⟮S.x⟯ := mem_adjoin_simple_self _ _
  have hb : b ∈ (T.F m)⟮S.x⟯ := by
    show T.ev (m + 1) f / (((1 : T.F m) : T.F m) : L) ∈ _
    rw [hf]
    exact div_mem (div_mem (hev B) (mul_mem (mul_mem (pow_mem hts kt) (hev _)) (pow_mem (hev A) l)))
      (IntermediateField.algebraMap_mem _ 1)
  have hby : b * S.y = T.ev (m + 1) f * θ := by
    change T.ev (m + 1) f / (((1 : T.F m) : T.F m) : L) * (θ * ((1 : T.F m) : L)) = _
    simp
  refine ⟨hb, hby, ?_, fun q ↦ ?_, fun α hα0 hα ↦ ?_, ?_⟩
  · rw [hby]
    refine T.keS_mem m h A hsq hdeg θ hθ 1 one_ne_zero _ (mul_mem (IntermediateField.algebraMap_mem _
      (⟨T.ev (m + 1) f, T.ev_mem (m + 1) f⟩ : T.F (m + 1))) (mem_adjoin_simple_self _ _))
  · simp only [D, R, T.prodLin_eraseIdx m hTm cs q q.2]
    ring
  · simp only [D, Polynomial.map_mul, Polynomial.map_pow, map_X, eval_mul, eval_pow, eval_X]
    refine mul_ne_zero (pow_ne_zero _ hα0) (T.eval_prodLin_ne m hTm cs α fun c' hc' ↦ ?_)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc'
    have := hα ⟨i, hi⟩
    simpa [c, kqC, List.getD_eq_getElem _ _ hi] using this
  · have hp : S.p = Polynomial.C ((1 : T.F m) ^ 2) * GPoly.toPoly (T.MP m hTm) A := rfl
    rw [hp]
    have hSx : S.x = T.ts m := rfl
    simp only [P, D, hSx, map_mul, map_pow, aeval_C, aeval_X, IntermediateField.algebraMap_apply]
    rw [T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm), T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm),
      T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]
    show T.ev (m + 1) f / (((1 : T.F m) : T.F m) : L) * _ = _
    rw [hf]
    have hts0 : T.ts m ≠ 0 := fun h0 ↦ (h m (Nat.lt_succ_self m)) ⟨X, X_ne_zero, by
      rw [aeval_X]; exact h0⟩
    have hDv : T.evP m (prodLinG Fc ks m cs) ≠ 0 := T.evP_prodLin_ne m h cs
    push_cast
    field_simp
    simp

end XData

section XFacts

variable [Fact (Irreducible (toPoly (fKc Fc)))]

lemma kx_cinj (m : ℕ) (hTm : T.Tr m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (hok : kxOK Fc ks m A B kt l cs = true) :
    Function.Injective fun q : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q) := by
  intro q q' hqq
  by_contra hne
  have h1 := ((T.kxOK_spec m hTm A B kt l cs hok).2 q q.2).2.1
  rw [T.sem_kxR m hTm] at h1
  have hR : (T.MP m hTm).sem (evalGC Fc ks m (prodLinG Fc ks m (cs.eraseIdx q)) (kqC Fc ks m cs q))
      ≠ 0 := by
    rw [T.sem_evalGC m hTm]; exact left_ne_zero_of_mul (left_ne_zero_of_mul h1)
  have hz : (MO Fc ks m).isZero (evalGC Fc ks m (prodLinG Fc ks m (cs.eraseIdx q))
      (kqC Fc ks m cs q)) = false := by
    cases h : (MO Fc ks m).isZero (evalGC Fc ks m (prodLinG Fc ks m (cs.eraseIdx q))
      (kqC Fc ks m cs q))
    · rfl
    · exact absurd (((T.MP m hTm).isZero_iff _).mp h) hR
  have := T.eval_prodLin_erase_ne m hTm cs q q.2 hz q' q'.2 (fun h ↦ hne (Fin.ext h).symm)
  apply this
  simp only [kqC, List.getD_eq_getElem _ _ q'.2] at hqq ⊢
  rw [← hqq]

/-- `η c − c′ ≠ 0` for `c ≠ 0`. -/
lemma kxD_ne (m : ℕ) (hM : T.MixHyp (m + 1)) {g : LC m} (hk : ks m = .exp g) (cs : List (LC m))
    (q : ℕ) (hc0 : (T.MP m hM.tr.of_succ).sem (kqC Fc ks m cs q) ≠ 0) :
    (T.MP m hM.tr.of_succ).sem (kxD Fc ks m g cs q) ≠ 0 := fun h0 ↦ by
  rw [T.sem_kxD m hM.tr.of_succ, T.sem_eq_val m hM.tr.of_succ g] at h0
  refine T.kxS_good m hM hk (algebraMap (T.F m) _ ((T.MP m hM.tr.of_succ).sem (kqC Fc ks m cs q)))
    (by rw [map_eq_zero_iff _ (algebraMap (T.F m) _).injective]; exact hc0) ?_
  rw [deriv_algebraMap, ← sub_eq_zero.mp h0]
  simp [Polynomial.eval_map]

lemma kxK_ne (m : ℕ) (hM : T.MixHyp (m + 1)) {g : LC m}
    (hk : ks m = .exp g) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (hok : kxOK Fc ks m A B kt l cs = true) (hcst : kxConst Fc ks m g A B kt l cs = true) (q : ℕ)
    (hq : q < cs.length) : kxK Fc ks m g A B kt l cs q ≠ 0 := by
  have hTm : T.Tr m := hM.tr.of_succ
  have hok' := (T.kxOK_spec m hTm A B kt l cs hok).2 q hq
  have hQ := T.kxConst_spec m hTm g A B kt l cs hcst q hq
  rw [T.sem_kxQ m hTm] at hQ
  intro h0
  rw [h0, Rat.cast_zero, div_eq_zero_iff] at hQ
  have hd0 := T.kxD_ne m hM hk cs q hok'.1
  rcases hQ with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hok'.2.2.2 (pow_eq_zero_iff two_ne_zero |>.mp h2)
    · exact hok'.2.2.1 h2
  · exact mul_ne_zero hd0 hok'.2.1 (pow_eq_zero_iff two_ne_zero |>.mp h1)

/-- `R_q(c_q) ≠ 0` for the polynomial `R_q = xᵏ ∏_{q' ≠ q} (x − c_{q'})`. -/
lemma kx_Rne (m : ℕ) (hTm : T.Tr m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (hok : kxOK Fc ks m A B kt l cs = true) (q : Fin cs.length) :
    (X ^ kt * GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q))).eval
      ((T.MP m hTm).sem (kqC Fc ks m cs q)) ≠ 0 := fun h0 ↦ by
  have := ((T.kxOK_spec m hTm A B kt l cs hok).2 q q.2).2.1
  rw [T.sem_kxR m hTm] at this
  rw [eval_mul, eval_pow, eval_X] at h0
  apply this
  rw [show (GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q))).eval
      ((T.MP m hTm).sem (kqC Fc ks m cs q)) * (T.MP m hTm).sem (kqC Fc ks m cs q) ^ kt =
    (T.MP m hTm).sem (kqC Fc ks m cs q) ^ kt * (GPoly.toPoly (T.MP m hTm)
      (prodLinG Fc ks m (cs.eraseIdx q))).eval ((T.MP m hTm).sem (kqC Fc ks m cs q)) by ring, h0,
    zero_mul]

open Classical in
/-- **Forward, the squared residues are constant.** -/
theorem kx_forward_const (hmon : (toB Fc).Monic)
    (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ) (hn : T.n = m + 1)
    (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks m) A))
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hok : kxOK Fc ks m A B kt l cs = true)
    (θ : L) (hθ : θ ^ 2 = T.evP m A) {ι : Type} (sI : Finset ι)
    (c u : ι → L) (hcd : ∀ i ∈ sI, (c i)′ = 0)
    (hu : ∀ i ∈ sI, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (heq : T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ =
      v′ + ∑ i ∈ sI, c i * logDeriv (u i)) :
    kxConst Fc ks m g A B kt l cs = true := by
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hA0 : T.evP m A ≠ 0 := MTower.evP_ne_zero T m hTr (by omega) A hdegpos
  obtain ⟨hb, hby, hbm, hDR, hDoff, hbP⟩ :=
    T.kx_data m hTr A hsq hdegA θ hθ (by omega) B kt l cs hA0
  set S := T.keS m hTr A hsq hdegA θ hθ 1 one_ne_zero with hS
  refine T.kxConst_of m hTm g A B kt l cs fun q hq ↦ ?_
  have hok' := (T.kxOK_spec m hTm A B kt l cs hok).2
  have hp : S.p = Polynomial.C ((1 : T.F m) ^ 2) * GPoly.toPoly (T.MP m hTm) A := rfl
  have hpc : ∀ q' : Fin cs.length, S.p.eval ((T.MP m hTm).sem (kqC Fc ks m cs q')) ≠ 0 := fun q' ↦ by
    rw [hp, eval_mul, eval_C, one_pow, one_mul]; exact (hok' q' q'.2).2.2.1
  have hbadc : ∀ q' : Fin cs.length,
      ¬ algebraMap (T.F m) (AlgebraicClosure (T.F m)) ((T.MP m hTm).sem (kqC Fc ks m cs q')) = 0 :=
    fun q' h0 ↦ (hok' q' q'.2).1 ((map_eq_zero_iff _ (algebraMap (T.F m) _).injective).mp h0)
  obtain ⟨ζ, hζ, hζe⟩ := S.kx_resid_const (K := AlgebraicClosure (T.F m))
    (Polynomial.C (T.val m g)′ * X)
    (T.keS_hx m hTr A hsq hdegA θ hθ 1 one_ne_zero (by omega) hk) (fun c ↦ deriv_algebraMap c)
    (fun α ↦ α = 0) (T.kxS_good m MS.hyp hk) (T.keS_constC m)
    (fun q' : Fin cs.length ↦ (T.MP m hTm).sem (kqC Fc ks m cs q')) hbadc
    (Polynomial.C ((1 : T.F m) ^ (2 * l) / 1) * GPoly.toPoly (T.MP m hTm) B) l _ hb
    _ (fun q' ↦ X ^ kt * GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q'))) hDR
    (T.kx_Rne m hTm A B kt l cs hok) hDoff hbP hpc
    rfl hbm sI c u hcd
    (fun i hi ↦ ⟨(hu i hi).1, T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ (hu i hi).2⟩) v
    (T.keS_mem m hTr A hsq hdegA θ hθ 1 one_ne_zero _ hv) (by rw [hby]; exact heq) ⟨q, hq⟩
  have hQ : (T.MP m hTm).sem (kxQ Fc ks m g A B kt l cs q) = ζ := by
    rw [T.sem_kxQ m hTm, T.sem_kxD m hTm, T.sem_kxR m hTm, T.sem_eq_val m hTm g]
    simp only [hp, eval_mul, eval_C, one_pow, div_one, one_mul, eval_pow, eval_X] at hζe
    have hne : ((T.val m g)′ * (T.MP m hTm).sem (kqC Fc ks m cs q) -
        ((T.MP m hTm).sem (kqC Fc ks m cs q))′) *
        ((GPoly.toPoly (T.MP m hTm) (prodLinG Fc ks m (cs.eraseIdx q))).eval
          ((T.MP m hTm).sem (kqC Fc ks m cs q)) * (T.MP m hTm).sem (kqC Fc ks m cs q) ^ kt *
        (GPoly.toPoly (T.MP m hTm) A).eval ((T.MP m hTm).sem (kqC Fc ks m cs q)) ^ l) ≠ 0 := by
      have h1 := (hok' q hq).2.1
      rw [T.sem_kxR m hTm] at h1
      have h2 := T.kxD_ne m MS.hyp hk cs q (hok' q hq).1
      rw [T.sem_kxD m hTm, T.sem_eq_val m hTm g] at h2
      exact mul_ne_zero h2 h1
    rw [div_eq_iff (pow_ne_zero 2 hne)]
    rw [hζe]
    ring
  rw [hQ, hζ]

end XFacts

section Poles

variable [Fact (Irreducible (toPoly (fKc Fc)))]

open Classical in
/-- **The poles on `y² = A`**: `β_q = c_q μ_{T_q} (η c_q − c_q′) R_q / B(c_q)` with
`μ_T = ∏_{i ∈ T} √gᵢ` is a point over `c_q` where the residue is `m_q μ_{T_q} / M`. -/
theorem kxm_pole (m : ℕ) (hM : T.MixHyp (m + 1)) {g : LC m} (hk : ks m = .exp g)
    (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (hok : kxOK Fc ks m A B kt l cs = true) (hcst : kxConst Fc ks m g A B kt l cs = true)
    (hrep : kxRepOK Fc ks m g A B kt l cs = true)
    (rts : List (T.F m)) (hrl : rts.length = (kxGens Fc ks m g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rts.length) (hi' : i < (kxGens Fc ks m g A B kt l cs).length),
      rts[i] ^ 2 = ((kxGens Fc ks m g A B kt l cs)[i] : T.F m)) (q : ℕ) (hq : q < cs.length) :
    let hm : T.Tr m := hM.tr.of_succ
    let μ := SqrtIndep.prodRoots rts (kxRep Fc ks m g A B kt l cs q).1
    let bq := ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) * μ *
      ((T.MP m hm).sem (kxD Fc ks m g cs q) * (T.MP m hm).sem (kxR Fc ks m A kt l cs q) /
        (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q)))
    μ ^ 2 = ((kxS Fc ks m g A B kt l cs (kxRep Fc ks m g A B kt l cs q).1 : ℚ) : T.F m) ∧ μ ≠ 0 ∧
      bq ≠ 0 ∧ bq ^ 2 = (GPoly.toPoly (T.MP m hm) A).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) ∧
      (T.MP m hm).sem (kxBm Fc ks m g A B kt l cs q) = μ * bq ∧
      (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) * bq =
        (kxMNm Fc ks m g A B kt l cs q : T.F m) * (μ / (kxDenM Fc ks m g A B kt l cs : T.F m)) *
          ((T.val m g)′ * (T.MP m hm).sem (kqC Fc ks m cs q) - ((T.MP m hm).sem (kqC Fc ks m cs q))′) *
          (T.MP m hm).sem (kxR Fc ks m A kt l cs q) := by
  intro hm μ bq
  obtain ⟨hTl, hκ, hc0⟩ := kxRep_spec m g A B kt l cs hrep q hq
  obtain ⟨hmi, hg0⟩ := kxGens_spec (Fc := Fc) (ks := ks) m g A B kt l cs
  have hok' := (T.kxOK_spec m hm A B kt l cs hok).2 q hq
  have hQ := T.kxConst_spec m hm g A B kt l cs hcst q hq
  rw [T.sem_kxQ m hm] at hQ
  have hκ0 := T.kxK_ne m hM hk A B kt l cs hok hcst q hq
  have hμ2 : μ ^ 2 = ((kxS Fc ks m g A B kt l cs (kxRep Fc ks m g A B kt l cs q).1 : ℚ) : T.F m) :=
    SqrtIndep.prodRoots_sq _ rts hrl hrs _
  have hS0 : kxS Fc ks m g A B kt l cs (kxRep Fc ks m g A B kt l cs q).1 ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hκ; exact hκ0 hκ
  have hμ0 : μ ≠ 0 := fun h0 ↦ hS0 (by
    have := hμ2; rw [h0, zero_pow two_ne_zero] at this; exact_mod_cast this.symm)
  have hcq0 : (kxRep Fc ks m g A B kt l cs q).2 ≠ 0 := by
    intro h0; rw [h0] at hκ; simp at hκ; exact hκ0 hκ
  have hd0 : (T.MP m hm).sem (kxD Fc ks m g cs q) ≠ 0 := T.kxD_ne m hM hk cs q hok'.1
  have hB0 := hok'.2.2.2
  have hR0 := hok'.2.1
  refine ⟨hμ2, hμ0, ?_, ?_, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hcq0) hμ0)
      (div_ne_zero (mul_ne_zero hd0 hR0) hB0)
  · have hκF : ((kxK Fc ks m g A B kt l cs q : ℚ) : T.F m) =
        ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) ^ 2 * μ ^ 2 := by
      rw [hμ2, hκ]; push_cast; ring
    rw [hκF] at hQ
    simp only [bq]
    rw [show (((kxRep Fc ks m g A B kt l cs q).2 : T.F m) * μ * ((T.MP m hm).sem (kxD Fc ks m g cs q) *
      (T.MP m hm).sem (kxR Fc ks m A kt l cs q) / (GPoly.toPoly (T.MP m hm) B).eval
        ((T.MP m hm).sem (kqC Fc ks m cs q)))) ^ 2 = (((kxRep Fc ks m g A B kt l cs q).2 : T.F m) ^ 2 *
          μ ^ 2) * ((T.MP m hm).sem (kxD Fc ks m g cs q) * (T.MP m hm).sem (kxR Fc ks m A kt l cs q)) ^ 2 /
          (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) ^ 2 by ring, ← hQ]
    field_simp
  · rw [T.sem_kxBm m hm]
    push_cast
    rw [← hμ2]
    simp only [bq]
    ring
  · have hDen : (kxDenM Fc ks m g A B kt l cs : T.F m) ≠ 0 := by
      exact_mod_cast (kxDenM_pos (Fc := Fc) (ks := ks) m g A B kt l cs).ne'
    rw [show (kxMNm Fc ks m g A B kt l cs q : T.F m) = ((kxMNm Fc ks m g A B kt l cs q : ℚ) : T.F m) by
      push_cast; rfl, kxMNm_eq m g A B kt l cs q hq hc0, ← T.sem_eq_val m hm g, ← T.sem_kxD m hm]
    simp only [bq]
    push_cast
    field_simp

end Poles



section ClassKF

variable [Fact (Irreducible (toPoly (fKc Fc)))]

open Classical in
/-- **The data of a class over `Kₘ`.** -/
theorem kxm_class_KF (m : ℕ) (hM : T.MixHyp (m + 1)) {g : LC m} (hk : ks m = .exp g)
    (A B : GPoly (LC m)) (hsq : Squarefree (GPoly.toPoly (T.MP m hM.tr.of_succ) A))
    (hcopA : Nat.Coprime 2 (GPoly.toPoly (T.MP m hM.tr.of_succ) A).natDegree)
    (kt l : ℕ) (cs : List (LC m))
    (hok : kxOK Fc ks m A B kt l cs = true) (hcst : kxConst Fc ks m g A B kt l cs = true)
    (hrep : kxRepOK Fc ks m g A B kt l cs = true)
    (rts : List (T.F m)) (hrl : rts.length = (kxGens Fc ks m g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rts.length) (hi' : i < (kxGens Fc ks m g A B kt l cs).length),
      rts[i] ^ 2 = ((kxGens Fc ks m g A B kt l cs)[i] : T.F m))
    (k : Fin (kxCls Fc ks m g A B kt l cs).length) :
    let hm : T.Tr m := hM.tr.of_succ
    let Tk := (kxCls Fc ks m g A B kt l cs)[(k : ℕ)]
    let μ := SqrtIndep.prodRoots rts Tk
    let fK := kxFKm Fc ks m g A B kt l cs Tk
    μ ≠ 0 ∧ Polynomial.C (μ ^ 2) * (Polynomial.C ((1 : T.F m) ^ 2) * GPoly.toPoly (T.MP m hm) A) =
        (toPoly fK).map (T.psiF m hm) ∧
      (toPoly fK).natDegree = fK.length - 1 ∧ Squarefree (toPoly fK) ∧
      Nat.Coprime 2 (fK.length - 1) ∧
      (∀ i, kxBem Fc ks m g A B kt l cs Tk i ≠ 0 ∧
        kxBem Fc ks m g A B kt l cs Tk i ^ 2 = (toPoly fK).eval (kxAlm Fc ks m g A B kt l cs Tk i)) ∧
      Function.Injective (fun i ↦ (kxAlm Fc ks m g A B kt l cs Tk i, kxBem Fc ks m g A B kt l cs Tk i)) ∧
      (∀ i, T.psiF m hm (kxAlm Fc ks m g A B kt l cs Tk i) =
        (T.MP m hm).sem (kqC Fc ks m cs (kxIota m g A B kt l cs k i))) ∧
      (∀ i, T.psiF m hm (kxBem Fc ks m g A B kt l cs Tk i) =
        μ * (((kxRep Fc ks m g A B kt l cs (kxIota m g A B kt l cs k i)).2 : T.F m) *
          SqrtIndep.prodRoots rts (kxRep Fc ks m g A B kt l cs (kxIota m g A B kt l cs k i)).1 *
          ((T.MP m hm).sem (kxD Fc ks m g cs (kxIota m g A B kt l cs k i)) *
            (T.MP m hm).sem (kxR Fc ks m A kt l cs (kxIota m g A B kt l cs k i)) /
            (GPoly.toPoly (T.MP m hm) B).eval
              ((T.MP m hm).sem (kqC Fc ks m cs (kxIota m g A B kt l cs k i)))))) := by
  intro hm Tk μ fK
  obtain ⟨q0, hq0, hq0T⟩ := kxCls_mem_rep m g A B kt l cs Tk (List.getElem_mem _)
  have hP0 := T.kxm_pole m hM hk A B kt l cs hok hcst hrep rts hrl hrs q0 hq0
  rw [hq0T] at hP0
  obtain ⟨hμ2, hμ0, -⟩ := hP0
  have hTi : ∀ i, (kxRep Fc ks m g A B kt l cs (kxIota m g A B kt l cs k i)).1 = Tk := fun i ↦
    ((mem_kxQs m g A B kt l cs _ _).mp (List.getElem_mem _)).2
  have hpf : Polynomial.C (μ ^ 2) * (Polynomial.C ((1 : T.F m) ^ 2) * GPoly.toPoly (T.MP m hm) A) =
      (toPoly fK).map (T.psiF m hm) := by
    rw [T.toPoly_kxFKm m hm, hμ2, one_pow, Polynomial.C_1, one_mul]
  have hsqp : Squarefree (Polynomial.C (μ ^ 2) * (Polynomial.C ((1 : T.F m) ^ 2) *
      GPoly.toPoly (T.MP m hm) A)) := by
    rw [one_pow, Polynomial.C_1, one_mul]
    exact fun x hx ↦ hsq x ((IsUnit.dvd_mul_left
      (Polynomial.isUnit_C.mpr (pow_ne_zero 2 hμ0).isUnit)).mp hx)
  have hcopp : Nat.Coprime 2 (Polynomial.C (μ ^ 2) * (Polynomial.C ((1 : T.F m) ^ 2) *
      GPoly.toPoly (T.MP m hm) A)).natDegree := by
    rw [one_pow, Polynomial.C_1, one_mul, natDegree_C_mul (pow_ne_zero 2 hμ0)]; exact hcopA
  obtain ⟨hd, hsqK, hcop2⟩ := fK_facts' (T.psiF m hm) fK (CPoly.trim_trim _) _ hpf
    hsqp.ne_zero hsqp hcopp
  have hA : ∀ i, T.psiF m hm (kxAlm Fc ks m g A B kt l cs Tk i) =
      (T.MP m hm).sem (kqC Fc ks m cs (kxIota m g A B kt l cs k i)) := fun i ↦ T.psiF_trC m hm _
  have hB : ∀ i, T.psiF m hm (kxBem Fc ks m g A B kt l cs Tk i) =
      μ * (((kxRep Fc ks m g A B kt l cs (kxIota m g A B kt l cs k i)).2 : T.F m) *
          SqrtIndep.prodRoots rts (kxRep Fc ks m g A B kt l cs (kxIota m g A B kt l cs k i)).1 *
          ((T.MP m hm).sem (kxD Fc ks m g cs (kxIota m g A B kt l cs k i)) *
            (T.MP m hm).sem (kxR Fc ks m A kt l cs (kxIota m g A B kt l cs k i)) /
            (GPoly.toPoly (T.MP m hm) B).eval
              ((T.MP m hm).sem (kqC Fc ks m cs (kxIota m g A B kt l cs k i))))) := fun i ↦ by
    have hPi := T.kxm_pole m hM hk A B kt l cs hok hcst hrep rts hrl hrs _ (kxIota m g A B kt l cs k i).2
    rw [kxBem, T.psiF_trC m hm]
    show (T.MP m hm).sem (kxBm Fc ks m g A B kt l cs (kxIota m g A B kt l cs k i : ℕ)) = _
    rw [hPi.2.2.2.2.1, hTi i]
  have hcinj := T.kx_cinj m hm A B kt l cs hok
  refine ⟨hμ0, hpf, hd, hsqK, hcop2, fun i ↦ ⟨fun h0 ↦ ?_, ?_⟩, fun i j hij ↦ ?_, hA, hB⟩
  · have hPi := T.kxm_pole m hM hk A B kt l cs hok hcst hrep rts hrl hrs _ (kxIota m g A B kt l cs k i).2
    have := hB i
    rw [h0, map_zero, hTi i] at this
    exact mul_ne_zero hμ0 (by rw [← hTi i]; exact hPi.2.2.1) this.symm
  · apply (T.psiF m hm).injective
    have hPi := T.kxm_pole m hM hk A B kt l cs hok hcst hrep rts hrl hrs _ (kxIota m g A B kt l cs k i).2
    rw [map_pow, hB i, ← eval₂_at_apply, ← eval_map, ← hpf, hA i, eval_mul, eval_C, eval_mul, eval_C,
      one_pow, one_mul, mul_pow, ← hPi.2.2.2.1, hTi i, hμ2]
  · apply kxIota_inj m g A B kt l cs k
    apply hcinj
    have h1 := congrArg (fun z ↦ T.psiF m hm z.1) hij
    simp only at h1
    rw [hA, hA] at h1
    exact h1

end ClassKF

section Abs

variable [Fact (Irreducible (toPoly (fKc Fc)))]

open Classical in
/-- **The hypotheses of the multi-class Liouville theorems** on `y² = A`, `y = θ`. -/
theorem kxm_abs (m : ℕ) (hM : T.MixHyp (m + 1)) {g : LC m} (hk : ks m = .exp g)
    (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (hok : kxOK Fc ks m A B kt l cs = true) (hcst : kxConst Fc ks m g A B kt l cs = true)
    (hrep : kxRepOK Fc ks m g A B kt l cs = true)
    (rts : List (T.F m)) (hrl : rts.length = (kxGens Fc ks m g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rts.length) (hi' : i < (kxGens Fc ks m g A B kt l cs).length),
      rts[i] ^ 2 = ((kxGens Fc ks m g A B kt l cs)[i] : T.F m)) :
    let hm : T.Tr m := hM.tr.of_succ
    let β : Fin cs.length → T.F m := fun q ↦ ((kxRep Fc ks m g A B kt l cs q).2 : T.F m) *
      SqrtIndep.prodRoots rts (kxRep Fc ks m g A B kt l cs q).1 *
      ((T.MP m hm).sem (kxD Fc ks m g cs q) * (T.MP m hm).sem (kxR Fc ks m A kt l cs q) /
        (GPoly.toPoly (T.MP m hm) B).eval ((T.MP m hm).sem (kqC Fc ks m cs q)))
    let ρ : Fin (kxCls Fc ks m g A B kt l cs).length → T.F m := fun k ↦
      SqrtIndep.prodRoots rts (kxCls Fc ks m g A B kt l cs)[(k : ℕ)] / (kxDenM Fc ks m g A B kt l cs : T.F m)
    let p := Polynomial.C ((1 : T.F m) ^ 2) * GPoly.toPoly (T.MP m hm) A
    (∀ q : Fin cs.length, β q ≠ 0 ∧ β q ^ 2 = p.eval ((T.MP m hm).sem (kqC Fc ks m cs q))) ∧
      (∀ q : Fin cs.length, (Polynomial.C ((1 : T.F m) ^ (2 * l) / 1) * GPoly.toPoly (T.MP m hm) B).eval
          ((T.MP m hm).sem (kqC Fc ks m cs q)) * β q =
        (kxMNm Fc ks m g A B kt l cs q : T.F m) * ρ (kxCl m g A B kt l cs q) *
          ((Polynomial.C (T.val m g)′ * X).eval ((T.MP m hm).sem (kqC Fc ks m cs q)) -
            ((T.MP m hm).sem (kqC Fc ks m cs q))′) *
          (X ^ kt * GPoly.toPoly (T.MP m hm) (prodLinG Fc ks m (cs.eraseIdx q)) * p ^ l).eval
            ((T.MP m hm).sem (kqC Fc ks m cs q))) ∧
      (∀ e : Fin (kxCls Fc ks m g A B kt l cs).length → ℚ, ∑ kk, (e kk : T.F m) * ρ kk = 0 →
        ∀ kk, e kk = 0) := by
  intro hm β ρ p
  have hp : ∀ z, p.eval z = (GPoly.toPoly (T.MP m hm) A).eval z := fun z ↦ by
    simp [p]
  refine ⟨fun q ↦ ?_, fun q ↦ ?_, fun e he ↦ ?_⟩
  · have hP := T.kxm_pole m hM hk A B kt l cs hok hcst hrep rts hrl hrs q q.2
    exact ⟨hP.2.2.1, by rw [hp]; exact hP.2.2.2.1⟩
  · have hP := T.kxm_pole m hM hk A B kt l cs hok hcst hrep rts hrl hrs q q.2
    have hρq : ρ (kxCl m g A B kt l cs q) = SqrtIndep.prodRoots rts (kxRep Fc ks m g A B kt l cs q).1 /
        (kxDenM Fc ks m g A B kt l cs : T.F m) := by
      simp only [ρ]; rw [kxCls_get_kxCl]
    have h5 := hP.2.2.2.2.2
    have hR : (X ^ kt * GPoly.toPoly (T.MP m hm) (prodLinG Fc ks m (cs.eraseIdx q)) * p ^ l).eval
        ((T.MP m hm).sem (kqC Fc ks m cs q)) = (T.MP m hm).sem (kxR Fc ks m A kt l cs q) := by
      simp only [eval_mul, eval_pow, eval_X, hp]
      rw [T.sem_kxR m hm]; ring
    rw [hρq, hR]
    simp only [eval_mul, eval_C, eval_X, one_pow, div_one, one_mul]
    exact h5
  · have hDen : (kxDenM Fc ks m g A B kt l cs : T.F m) ≠ 0 := by
      exact_mod_cast (kxDenM_pos (Fc := Fc) (ks := ks) m g A B kt l cs).ne'
    have he' : ∑ kk, (e kk : T.F m) * SqrtIndep.prodRoots rts (kxCls Fc ks m g A B kt l cs)[(kk : ℕ)] = 0 := by
      have : ∑ kk, (e kk : T.F m) * ρ kk =
          (∑ kk, (e kk : T.F m) * SqrtIndep.prodRoots rts (kxCls Fc ks m g A B kt l cs)[(kk : ℕ)]) /
            (kxDenM Fc ks m g A B kt l cs : T.F m) := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun kk _ ↦ by simp only [ρ]; ring
      rw [this, div_eq_zero_iff] at he
      exact he.resolve_right hDen
    obtain ⟨hmi, hg0⟩ := kxGens_spec (Fc := Fc) (ks := ks) m g A B kt l cs
    refine SqrtIndep.prodRoots_indep _ rts hrl hrs hmi (fun kk ↦ (kxCls Fc ks m g A B kt l cs)[(kk : ℕ)])
      (fun kk ↦ ?_) (fun i j hij ↦ Fin.ext ((kxCls_nodup m g A B kt l cs).getElem_inj_iff.mp hij)) e he'
    obtain ⟨q, hq, hqT⟩ := kxCls_mem_rep (Fc := Fc) (ks := ks) m g A B kt l cs _ (List.getElem_mem _)
    rw [← hqT, hrl]
    exact (kxRep_spec (Fc := Fc) (ks := ks) m g A B kt l cs hrep q hq).1

end Abs

end MTower

end Curves.MT
