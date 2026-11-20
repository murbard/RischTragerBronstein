import RischTragerBronstein.Mixed.KZCodes
import RischTragerBronstein.Mixed.KYMain

/-!
# Radicals with poles in `Kₘ ⊗ N`: the semantics of the codes

For a root `ρ ∈ Fₘ` of `M` (`ψ = psiNFM : Kₘ ⊗ N → Fₘ`, `X ↦ ρ`): `ψ (nfmD x) = (ψ x)′`,
`ψ (nfmEval P c) = P(ψ c)`, the product check `D = ∏ (t − ψ c_q)`, the data checks, and the
constancy of the residues.
-/

open Polynomial Differential IntermediateField CPoly

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

section Ops

variable (m : ℕ) (hm : T.Tr m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
  (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0)

include hρ in
lemma rho_deriv (hM0 : toPoly M ≠ 0) : ρ′ = 0 := by
  apply Subtype.ext
  rw [coe_deriv]
  refine MTower.deriv_root_rat _ _ hM0 ?_
  rw [show ((ρ : T.F m) : L) = algebraMap (T.F m) L ρ from rfl, aeval_algebraMap_apply, hρ, map_zero]

/-- **The derivation on the coordinates.** -/
lemma psi_nfmD (hM0 : toPoly M ≠ 0) (x : NFM Fc m M) :
    T.psiNFM m hm M ρ hρ (nfmD Fc ks m M x) = (T.psiNFM m hm M ρ hρ x)′ := by
  have hρd := T.rho_deriv m M ρ hρ hM0
  rw [nfmD, T.psiNFM_mk, T.psiNFM_val, eval₂_list_sum, eval₂_list_sum, List.length_map]
  rw [map_sum]
  refine Finset.sum_congr rfl fun f hf ↦ ?_
  have hf' : f < x.1.length := Finset.mem_range.mp hf
  rw [Derivation.leibniz, Derivation.leibniz_pow, hρd]
  simp only [smul_zero, mul_zero, nsmul_eq_mul, smul_eq_mul, zero_add]
  rw [List.getD_eq_getElem _ _ (by simpa using hf'), List.getElem_map,
    List.getD_eq_getElem _ _ hf', T.psiF_trC m hm, (T.MP m hm).sem_deriv, T.sem_unTr m hm]
  ring

/-- **Evaluation at `c ∈ Kₘ ⊗ N`.** -/
lemma psi_nfmEval (P : GPoly (LC m)) (c : NFM Fc m M) :
    T.psiNFM m hm M ρ hρ (nfmEval Fc m M P c) =
      (GPoly.toPoly (T.MP m hm) P).eval (T.psiNFM m hm M ρ hρ c) := by
  induction P with
  | nil => simp [nfmEval]
  | cons a P ih =>
    simp only [nfmEval, List.foldr_cons] at ih ⊢
    rw [map_add, map_mul, ih, T.psiNFM_embM, T.psiF_trC m hm, GPoly.toPoly_cons]
    simp

/-- **The product `∏ (X − c)`.** -/
lemma psi_nfmProd (cs : List (NFM Fc m M)) :
    (toPoly (nfmProd Fc m M cs)).map (T.psiNFM m hm M ρ hρ) =
      (cs.map fun c ↦ X - Polynomial.C (T.psiNFM m hm M ρ hρ c)).prod := by
  induction cs with
  | nil => simp [nfmProd]
  | cons c cs ih =>
    simp only [nfmProd, List.foldr_cons] at ih ⊢
    rw [CPoly.toPoly_mul, Polynomial.map_mul, ih, List.map_cons, List.prod_cons]
    congr 1
    simp [toPoly_cons, sub_eq_add_neg, add_comm]

/-- A representative of an element of `Kₘ ⊗ N` is short. -/
lemma nfm_len (x : NFM Fc m M) : x.1.length ≤ (toPoly (liftQ Fc m M)).natDegree := by
  by_cases h0 : x.1 = []
  · rw [h0]; simp
  have hx := x.2
  have hdeg := NFK.degree_val _ x
  have hne : trim (divMod x.1 (liftQ Fc m M)).2 ≠ [] := by
    change NFK.norm _ x.1 ≠ []; rw [hx]; exact h0
  have hl := CPoly.length_trim hne
  have hl' : (NFK.norm (liftQ Fc m M) x.1).length = _ := hl
  rw [hx] at hl'
  have hxd : (toPoly x.1).natDegree < (toPoly (liftQ Fc m M)).natDegree := by
    have hx0 : toPoly x.1 ≠ 0 := by
      intro h
      have := (trim_eq_nil_iff x.1).mpr h
      have hxx : NFK.norm (liftQ Fc m M) x.1 = x.1 := hx
      rw [NFK.norm] at hxx
      rw [← hxx, trim_trim] at this
      rw [hxx] at this; exact h0 this
    exact natDegree_lt_natDegree hx0 hdeg
  have htp : (toPoly (divMod x.1 (liftQ Fc m M)).2).natDegree = (toPoly x.1).natDegree := by
    have := congrArg (fun l ↦ (toPoly l).natDegree) hx
    simp only [NFK.norm, toPoly_trim] at this
    exact this
  omega

/-- **Zero coordinates**: a short list of coordinates representing `0` is zero. -/
lemma nfm_coords_zero (l : CPoly (KF Fc m))
    (hl : l.length ≤ (toPoly (liftQ Fc m M)).natDegree) (h : NFK.mk (liftQ Fc m M) l = 0) :
    ∀ f, l.getD f 0 = 0 := by
  have hdeg : (toPoly l).degree < (toPoly (liftQ Fc m M)).degree := by
    have hf0 := NFK.f_ne_zero (liftQ Fc m M)
    rw [degree_eq_natDegree hf0]
    refine (Polynomial.degree_lt_iff_coeff_zero _ _).mpr fun f hf ↦ ?_
    rw [coeff_toPoly, List.getD_eq_default]
    exact hl.trans (by exact_mod_cast hf)
  have h1 := congrArg Subtype.val h
  change NFK.norm _ l = NFK.norm _ [] at h1
  have h2 := congrArg toPoly h1
  rw [NFK.toPoly_norm_of_lt _ _ hdeg, NFK.toPoly_norm_of_lt _ _ (by
    simp only [toPoly_nil, degree_zero]
    exact bot_lt_iff_ne_bot.mpr (by rw [Ne, degree_eq_bot]; exact NFK.f_ne_zero _))] at h2
  intro f
  rw [← coeff_toPoly, h2]
  simp

end Ops

section Res

variable (m : ℕ) (hm : T.Tr m) (n j : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
  (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ)
  (cs : List (NFM Fc m M))

lemma psi_kzR (q : ℕ) :
    T.psiNFM m hm M ρ hρ (kzR Fc m M A kt l cs q) =
      T.psiNFM m hm M ρ hρ (kzC Fc m M cs q) ^ kt *
        ((cs.eraseIdx q).map fun c ↦ T.psiNFM m hm M ρ hρ (kzC Fc m M cs q) -
          T.psiNFM m hm M ρ hρ c).prod *
        (GPoly.toPoly (T.MP m hm) A).eval (T.psiNFM m hm M ρ hρ (kzC Fc m M cs q)) ^ l := by
  rw [kzR, map_mul, map_mul, map_pow, map_pow, map_list_prod, List.map_map, T.psi_nfmEval]
  congr 3
  exact List.map_congr_left fun c _ ↦ by simp

lemma psi_kzD (hM0 : toPoly M ≠ 0) (q : ℕ) :
    T.psiNFM m hm M ρ hρ (kzD Fc ks m M g cs q) =
      ((T.MP m hm).sem g)′ * T.psiNFM m hm M ρ hρ (kzC Fc m M cs q) -
        (T.psiNFM m hm M ρ hρ (kzC Fc m M cs q))′ := by
  rw [kzD, map_sub, map_mul, T.psiNFM_embM, T.psiF_trC m hm, (T.MP m hm).sem_deriv,
    T.psi_nfmD m hm M ρ hρ hM0]

lemma psi_kzRho (q : ℕ) :
    T.psiNFM m hm M ρ hρ (kzRho Fc ks m M g A B kt l cs q) =
      (GPoly.toPoly (T.MP m hm) B).eval (T.psiNFM m hm M ρ hρ (kzC Fc m M cs q)) /
        (T.psiNFM m hm M ρ hρ (kzD Fc ks m M g cs q) * T.psiNFM m hm M ρ hρ (kzR Fc m M A kt l cs q)) := by
  rw [kzRho, map_mul, map_inv₀, map_mul, T.psi_nfmEval, div_eq_mul_inv]

lemma psi_kzQ (q : ℕ) :
    T.psiNFM m hm M ρ hρ (kzQ Fc ks m n j M g A B kt l cs q) =
      T.psiNFM m hm M ρ hρ (kzRho Fc ks m M g A B kt l cs q) ^ n *
        (GPoly.toPoly (T.MP m hm) A).eval (T.psiNFM m hm M ρ hρ (kzC Fc m M cs q)) ^ j := by
  rw [kzQ, map_mul, map_pow, map_pow, T.psi_nfmEval]

/-- **The data checks.** -/
lemma kzOK_spec (dC : GPoly (LC m)) (hok : kzOK Fc ks m M A B kt l cs dC = true) :
    (T.MP m hm).sem (A.getD 0 (MO Fc ks m).zero) ≠ 0 ∧
    GPoly.toPoly (T.MP m hm) dC = (cs.map fun c ↦ X - Polynomial.C (T.psiNFM m hm M ρ hρ c)).prod ∧
    ∀ q < cs.length,
      T.psiNFM m hm M ρ hρ (kzC Fc m M cs q) ≠ 0 ∧ T.psiNFM m hm M ρ hρ (kzR Fc m M A kt l cs q) ≠ 0 ∧
      (GPoly.toPoly (T.MP m hm) A).eval (T.psiNFM m hm M ρ hρ (kzC Fc m M cs q)) ≠ 0 ∧
      (GPoly.toPoly (T.MP m hm) B).eval (T.psiNFM m hm M ρ hρ (kzC Fc m M cs q)) ≠ 0 := by
  simp only [kzOK, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq]
    at hok
  obtain ⟨⟨hA0, hprod⟩, hall⟩ := hok
  refine ⟨fun h0 ↦ ?_, ?_, fun q hq ↦ ?_⟩
  · rw [← (T.MP m hm).isZero_iff] at h0; rw [h0] at hA0; exact Bool.noConfusion hA0
  · rw [← T.kyFA_map m hm M ρ hρ dC, ← hprod, toPoly_trim, T.psi_nfmProd]
  · have h := List.all_eq_true.mp hall q (List.mem_range.mpr hq)
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨(_root_.map_ne_zero _).mpr h1, (_root_.map_ne_zero _).mpr h2, ?_, ?_⟩
    · rw [← T.psi_nfmEval]; exact (_root_.map_ne_zero _).mpr h3
    · rw [← T.psi_nfmEval]; exact (_root_.map_ne_zero _).mpr h4

/-- The poles are distinct. -/
lemma kz_cinj (dC : GPoly (LC m)) (hok : kzOK Fc ks m M A B kt l cs dC = true) :
    Function.Injective fun q : Fin cs.length ↦ T.psiNFM m hm M ρ hρ (kzC Fc m M cs q) := by
  intro q q' hqq
  by_contra hne
  have h1 := ((T.kzOK_spec m hm M ρ hρ A B kt l cs dC hok).2.2 q q.2).2.1
  rw [T.psi_kzR] at h1
  have h2 := right_ne_zero_of_mul (left_ne_zero_of_mul h1)
  apply h2
  refine List.prod_eq_zero (List.mem_map.mpr ⟨cs[(q' : ℕ)], ?_, ?_⟩)
  · rw [List.mem_eraseIdx_iff_getElem]
    exact ⟨q', q'.2, fun h ↦ hne (Fin.ext h).symm, rfl⟩
  · simp only [kzC, List.getD_eq_getElem _ _ q.2, List.getD_eq_getElem _ _ q'.2] at hqq ⊢
    rw [hqq, sub_self]

include hρ in
/-- **Constant residues are rational combinations of the powers of `ρ`.** -/
lemma kzConst_spec (hM0 : toPoly M ≠ 0) (hc : kzConst Fc ks m n j M g A B kt l cs = true) (q : ℕ)
    (hq : q < cs.length) :
    T.psiNFM m hm M ρ hρ (kzQ Fc ks m n j M g A B kt l cs q) =
      aeval ρ (toPoly (kzK Fc ks m n j M g A B kt l cs q)) := by
  have h := List.all_eq_true.mp hc q (List.mem_range.mpr hq)
  simp only [beq_iff_eq] at h
  set Q := kzQ Fc ks m n j M g A B kt l cs q with hQ
  have hz := nfm_coords_zero m M _ (by rw [List.length_map]; exact nfm_len m M Q) h
  rw [T.psiNFM_val, eval₂_list_sum, kzK, ← hQ, aeval_def, eval₂_list_sum, List.length_map]
  refine Finset.sum_congr rfl fun f hf ↦ ?_
  have hf' : f < Q.1.length := Finset.mem_range.mp hf
  congr 1
  have hzf := hz f
  rw [List.getD_eq_getElem _ _ (by simpa using hf'), List.getElem_map] at hzf
  rw [List.getD_eq_getElem (Q.1.map fun a ↦ (ratValC Fc ks m (unTr Fc m a)).getD 0) 0
    (by simpa using hf'), List.getElem_map, List.getD_eq_getElem Q.1 0 hf']
  have hd : ((T.MP m hm).sem (unTr Fc m Q.1[f]))′ = 0 := by
    rw [← (T.MP m hm).sem_deriv, ← T.psiF_trC m hm, hzf, map_zero]
  rw [← T.sem_unTr m hm, T.ratValC_of_const m hm _ hd]
  rfl

lemma kzConst_of (hM0 : toPoly M ≠ 0)
    (hq : ∀ q < cs.length, (T.psiNFM m hm M ρ hρ (kzQ Fc ks m n j M g A B kt l cs q))′ = 0) :
    kzConst Fc ks m n j M g A B kt l cs = true := by
  refine List.all_eq_true.mpr fun q hqm ↦ ?_
  simp only [beq_iff_eq]
  apply (T.psiNFM m hm M ρ hρ).injective
  rw [T.psi_nfmD m hm M ρ hρ hM0, hq q (List.mem_range.mp hqm), map_zero]

end Res

lemma kzFieldOK_spec {m n j : ℕ} {M : CPoly ℚ} [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    {g : LC m} {A B : GPoly (LC m)} {kt l : ℕ} {cs : List (NFM Fc m M)} {zN : CPoly ℚ}
    {gs : List (CPoly ℚ)} (h : kzFieldOK Fc ks m n j M g A B kt l cs zN gs = true) :
    CPoly.trim M = M ∧ 1 < M.length ∧ powQ M zN n = NFK.norm M [1] ∧
      (∀ k, 0 < k → k < n → powQ M zN k ≠ NFK.norm M [1]) ∧ gs.length = cs.length ∧
      ∀ q < cs.length, powQ M (gs.getD q []) n = NFK.norm M (kzK Fc ks m n j M g A B kt l cs q) := by
  simp only [kzFieldOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3, fun k hk0 hkn ↦ ?_,
    of_decide_eq_true h5, fun q hq ↦ of_decide_eq_true (List.all_eq_true.mp h6 q
      (List.mem_range.mpr hq))⟩
  have := List.all_eq_true.mp h4 k (List.mem_range.mpr hkn)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at this
  rcases this with h | h
  · omega
  · exact h

section ZData

variable (m : ℕ) (h : T.Tr (m + 1)) (A : GPoly (LC m))
  (hsq : Squarefree (GPoly.toPoly (T.MP m h.of_succ) A))
  (hdeg : 0 < (GPoly.toPoly (T.MP m h.of_succ) A).natDegree)
  (n : ℕ) (hn : 0 < n) (θ : L) (hθ : θ ^ n = T.evP m A)
  (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
  (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0)

include h in
/-- The value of the integrand's rational part. -/
lemma ev_rhsZ (B : GPoly (LC m)) (kt l : ℕ) (dC : GPoly (LC m)) :
    T.ev (m + 1) ((B, kzDen Fc ks m A kt l dC) : LC (m + 1)) =
      T.evP m B / (T.ts m ^ kt * T.evP m dC * T.evP m A ^ l) := by
  rw [show T.ev (m + 1) ((B, kzDen Fc ks m A kt l dC) : LC (m + 1)) =
      T.evP m B / T.evP m (kzDen Fc ks m A kt l dC) from rfl, kzDen,
    ← T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ) (GPoly.mul _ _ _),
    GPoly.toPoly_mul, GPoly.toPoly_mul, map_mul, map_mul, T.toPoly_monoG m h.of_succ,
    T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ),
    T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ), T.evP_powG m h.of_succ]
  simp

/-- **The data of the abstract theorems** with the poles `ψ c_q`. -/
theorem kz_data (B : GPoly (LC m)) (kt l : ℕ) (cs : List (NFM Fc m M)) (dC : GPoly (LC m))
    (hdC : GPoly.toPoly (T.MP m h.of_succ) dC =
      (cs.map fun c ↦ X - Polynomial.C (T.psiNFM m h.of_succ M ρ hρ c)).prod) (j : ℕ) :
    let S := T.krS m h A hsq hdeg n hn θ hθ
    let f : LC (m + 1) := (B, kzDen Fc ks m A kt l dC)
    let b := T.ev (m + 1) f
    let c : Fin cs.length → T.F m := fun q ↦ T.psiNFM m h.of_succ M ρ hρ (kzC Fc m M cs q)
    let D := X ^ kt * GPoly.toPoly (T.MP m h.of_succ) dC
    let R : Fin cs.length → (T.F m)[X] := fun q ↦
      X ^ kt * ((cs.eraseIdx q).map fun c ↦ X - Polynomial.C (T.psiNFM m h.of_succ M ρ hρ c)).prod
    let P := GPoly.toPoly (T.MP m h.of_succ) B
    b ∈ (T.F m)⟮S.x⟯ ∧ b * S.y ^ j ∈ (T.F m)⟮S.x⟯⟮S.y⟯ ∧
      (∀ q, D = (X - Polynomial.C (c q)) * R q) ∧
      (∀ α : AlgebraicClosure (T.F m), α ≠ 0 → (∀ q, α ≠ algebraMap (T.F m) _ (c q)) →
        (D.map (algebraMap (T.F m) (AlgebraicClosure (T.F m)))).eval α ≠ 0) ∧
      b * aeval S.x (D * S.p ^ l) = aeval S.x P := by
  intro S f b c D R P
  have hTm : T.Tr m := h.of_succ
  set ψ := T.psiNFM m hTm M ρ hρ with hψ
  have hf : T.ev (m + 1) f = T.evP m B / (T.ts m ^ kt * T.evP m dC * T.evP m A ^ l) :=
    T.ev_rhsZ m h A B kt l dC
  have hxm : ∀ Q : (T.F m)[X], aeval (T.ts m) Q ∈ (T.F m)⟮S.x⟯ := fun Q ↦ by
    letI := algebraAdjoinSimple (F := T.F m) S.x
    rw [show aeval (T.ts m) Q = aeval S.x Q from rfl, ← algebraMap_adjoinSimple (F := T.F m) S.x Q]
    exact SetLike.coe_mem _
  have hev : ∀ Q : GPoly (LC m), T.evP m Q ∈ (T.F m)⟮S.x⟯ := fun Q ↦ by
    rw [← T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]; exact hxm _
  have hts : T.ts m ∈ (T.F m)⟮S.x⟯ := mem_adjoin_simple_self _ _
  have hb : b ∈ (T.F m)⟮S.x⟯ := by
    show T.ev (m + 1) f ∈ _
    rw [hf]
    exact div_mem (hev B) (mul_mem (mul_mem (pow_mem hts kt) (hev _)) (pow_mem (hev A) l))
  have htr : Transcendental (T.F m) (T.ts m) := h m (Nat.lt_succ_self m)
  refine ⟨hb, ?_, fun q ↦ ?_, fun α hα0 hα ↦ ?_, ?_⟩
  · exact mul_mem (IntermediateField.algebraMap_mem _ (⟨b, hb⟩ : (T.F m)⟮S.x⟯))
      (pow_mem (mem_adjoin_simple_self _ _) j)
  · have hq' : (q : ℕ) < (cs.map fun c ↦ X - Polynomial.C (ψ c)).length := by simp
    simp only [D, R, hdC, ← List.eraseIdx_map]
    rw [← List.CommMonoid.mul_prod_eraseIdx hq', List.getElem_map]
    simp only [c, kzC, List.getD_eq_getElem _ _ q.2]
    ring
  · simp only [D, hdC, Polynomial.map_mul, Polynomial.map_pow, map_X, eval_mul, eval_pow, eval_X,
      Polynomial.map_list_prod, eval_list_prod, List.map_map]
    refine mul_ne_zero (pow_ne_zero _ hα0) (List.prod_ne_zero fun h0 ↦ ?_)
    obtain ⟨c', hc', hc0⟩ := List.mem_map.mp h0
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc'
    have := hα ⟨i, hi⟩
    simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C, eval_sub, eval_X, eval_C]
      at hc0
    apply this
    simp only [c, kzC, List.getD_eq_getElem _ _ hi]
    exact sub_eq_zero.mp hc0
  · have hp : S.p = GPoly.toPoly (T.MP m hTm) A := rfl
    rw [hp]
    have hSx : S.x = T.ts m := rfl
    simp only [P, D, hSx, map_mul, map_pow, aeval_X]
    rw [T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm), T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm),
      T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]
    show T.ev (m + 1) f * _ = _
    rw [hf]
    have hts0 : T.ts m ≠ 0 := fun h0 ↦ htr ⟨X, X_ne_zero, by rw [aeval_X]; exact h0⟩
    have hDv : T.evP m dC ≠ 0 := by
      rw [← T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm), hdC]
      intro h0
      have := transcendental_iff.mp htr _ h0
      exact (List.prod_ne_zero fun hm ↦ by
        obtain ⟨c', -, hc'⟩ := List.mem_map.mp hm
        exact X_sub_C_ne_zero _ hc') this
    have hA0 : T.evP m A ≠ 0 := by
      rw [← T.aeval_toPoly (T.MP m hTm) (T.sem_MP m hTm)]
      exact fun h0 ↦ S.htr ⟨_, hsq.ne_zero, h0⟩
    field_simp

end ZData

/-- `η c − c′ ≠ 0` for `c ≠ 0`. -/
lemma kzD_ne (m : ℕ) (hM : T.MixHyp (m + 1)) {g : LC m} (hk : ks m = .exp g) (M : CPoly ℚ)
    [Fact (Irreducible (toPoly (liftQ Fc m M)))] (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0)
    (hM0 : toPoly M ≠ 0) (cs : List (NFM Fc m M)) (q : ℕ)
    (hc0 : T.psiNFM m hM.tr.of_succ M ρ hρ (kzC Fc m M cs q) ≠ 0) :
    T.psiNFM m hM.tr.of_succ M ρ hρ (kzD Fc ks m M g cs q) ≠ 0 := fun h0 ↦ by
  rw [T.psi_kzD m hM.tr.of_succ M ρ hρ g cs hM0, T.sem_eq_val m hM.tr.of_succ g] at h0
  refine T.kxS_good m hM hk (algebraMap (T.F m) _ (T.psiNFM m hM.tr.of_succ M ρ hρ (kzC Fc m M cs q)))
    (by rw [map_eq_zero_iff _ (algebraMap (T.F m) _).injective]; exact hc0) ?_
  rw [deriv_algebraMap, ← sub_eq_zero.mp h0]
  simp [Polynomial.eval_map]

section ZPoints

variable (m : ℕ) (hm : T.Tr m) (n j : ℕ) (hn : 0 < n) (hjc : Nat.Coprime j n) (g : LC m)
  (A B : GPoly (LC m)) (kt l : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
  (cs : List (NFM Fc m M)) (dC : GPoly (LC m)) (ρ : T.F m) (hρ : aeval ρ (toPoly M) = 0)
  (zN : CPoly ℚ) (gs : List (CPoly ℚ))

include hn hjc hρ in
/-- **The points over the poles and their residues.** -/
theorem kz_points (hok : kzOK Fc ks m M A B kt l cs dC = true)
    (hc : kzConst Fc ks m n j M g A B kt l cs = true)
    (hF : kzFieldOK Fc ks m n j M g A B kt l cs zN gs = true)
    (hmin : ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree → aeval ρ P ≠ 0)
    (hD0 : ∀ q < cs.length, T.psiNFM m hm M ρ hρ (kzD Fc ks m M g cs q) ≠ 0) :
    let ψ := T.psiNFM m hm M ρ hρ
    let c : ℕ → T.F m := fun q ↦ T.psiNFM m hm M ρ hρ (kzC Fc m M cs q)
    let βq : ℕ → T.F m := fun q ↦ ψ (kzBeta Fc ks m n j M g A B kt l cs gs q)
    IsPrimitiveRoot (aeval ρ (toPoly zN)) n ∧
      (∀ q < cs.length, βq q ≠ 0 ∧ βq q ^ n = (GPoly.toPoly (T.MP m hm) A).eval (c q)) ∧
      ∀ q < cs.length, ∀ k,
        (GPoly.toPoly (T.MP m hm) B).eval (c q) * (aeval ρ (toPoly zN) ^ k * βq q) ^ j =
          (∑ f ∈ Finset.range (toPoly M).natDegree, (kyR n j M zN gs f (q * n + k % n) : T.F m) *
            ρ ^ f) * (T.psiNFM m hm M ρ hρ (kzD Fc ks m M g cs q) *
              T.psiNFM m hm M ρ hρ (kzR Fc m M A kt l cs q)) := by
  intro ψ c βq
  obtain ⟨htrim, hlen, hz1, hz2, hgl, hgn⟩ := kzFieldOK_spec hF
  have hM0 : toPoly M ≠ 0 := by
    intro h0
    have := (trim_eq_nil_iff M).mpr h0
    rw [htrim] at this; rw [this] at hlen; simp at hlen
  have hζ := zeta_prim M ρ hρ hmin hM0 n hn zN hz1 hz2
  have hok' := T.kzOK_spec m hm M ρ hρ A B kt l cs dC hok
  refine ⟨hζ, fun q hq ↦ ?_, fun q hq k ↦ ?_⟩ <;>
  · -- the root `β_q`
    have hAc : (GPoly.toPoly (T.MP m hm) A).eval (c q) ≠ 0 := (hok'.2.2 q hq).2.2.1
    have hBc : (GPoly.toPoly (T.MP m hm) B).eval (c q) ≠ 0 := (hok'.2.2 q hq).2.2.2
    have hR0 : T.psiNFM m hm M ρ hρ (kzR Fc m M A kt l cs q) ≠ 0 := (hok'.2.2 q hq).2.1
    set ρq := T.psiNFM m hm M ρ hρ (kzRho Fc ks m M g A B kt l cs q) with hρq
    have hρq0 : ρq ≠ 0 := by
      rw [hρq, T.psi_kzRho m hm M ρ hρ g A B kt l cs]
      exact div_ne_zero hBc (mul_ne_zero (hD0 q hq) hR0)
    set γ := aeval ρ (toPoly (gs.getD q [])) with hγ
    have hγn : γ ^ n = ρq ^ n * (GPoly.toPoly (T.MP m hm) A).eval (c q) ^ j := by
      rw [hγ, ← aeval_powQ M ρ hρ, hgn q hq, aeval_normQ M ρ hρ,
        ← T.kzConst_spec m hm n j M ρ hρ g A B kt l cs hM0 hc q hq, T.psi_kzQ]
    have hγ0 : γ ≠ 0 := fun h0 ↦ by
      rw [h0, zero_pow hn.ne'] at hγn
      exact mul_ne_zero (pow_ne_zero _ hρq0) (pow_ne_zero _ hAc) hγn.symm
    set u := γ * ρq⁻¹ with hu
    have hu0 : u ≠ 0 := mul_ne_zero hγ0 (inv_ne_zero hρq0)
    have hun : u ^ n = (GPoly.toPoly (T.MP m hm) A).eval (c q) ^ j := by
      rw [hu, mul_pow, hγn, inv_pow]; field_simp
    have hab : (Nat.gcdA j n : ℤ) * j + Nat.gcdB j n * n = 1 := by
      have := Nat.gcd_eq_gcd_ab j n
      rw [hjc] at this; push_cast at this; linarith
    have hβ : βq q = u ^ (Nat.gcdA j n) * (GPoly.toPoly (T.MP m hm) A).eval (c q) ^ (Nat.gcdB j n) := by
      simp only [βq, ψ, kzBeta, map_mul, map_zpow₀, map_inv₀, T.psiNFM_ofQ, T.psi_nfmEval]
      rfl
    obtain ⟨hβn, hβj⟩ := kummer_root u _ hu0 hAc n j _ _ hab hun
    first
    | exact ⟨by rw [hβ]; exact fun h0 ↦ hAc (by rw [← hβn, h0, zero_pow hn.ne']), by rw [hβ]; exact hβn⟩
    | rw [mul_pow, hβ, hβj, ← pow_mul]
      -- the coordinates
      have hcoord : aeval ρ (toPoly (kyRR j M zN gs q (k % n))) =
          ∑ f ∈ Finset.range (toPoly M).natDegree, (kyR n j M zN gs f (q * n + k % n) : T.F m) *
            ρ ^ f := by
        have hq' : (q * n + k % n) / n = q := by
          rw [Nat.add_div_of_dvd_right (Dvd.intro_left _ rfl), Nat.mul_div_cancel _ hn,
            Nat.div_eq_of_lt (Nat.mod_lt _ hn), add_zero]
        have hk' : (q * n + k % n) % n = k % n := by
          rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_mod]
        have hdeg : 0 < (toPoly M).natDegree := by
          have := CPoly.length_trim (p := M) (by rw [htrim]; intro h0; rw [h0] at hlen; simp at hlen)
          rw [htrim] at this; omega
        simp only [kyR, hq', hk']
        rw [kyRR, mulQ, aeval_coords M ρ hM0 hdeg]
      have hval : aeval ρ (toPoly (kyRR j M zN gs q (k % n))) = aeval ρ (toPoly zN) ^ (k * j) * γ := by
        rw [kyRR, aeval_mulQ M ρ hρ, aeval_powQ M ρ hρ, hγ]
        congr 1
        conv_rhs => rw [← Nat.mod_add_div k n]
        rw [add_mul, pow_add, mul_assoc, pow_mul (aeval ρ (toPoly zN)) n, hζ.pow_eq_one, one_pow,
          mul_one]
      rw [← hcoord, hval, hu, hρq, T.psi_kzRho m hm M ρ hρ g A B kt l cs]
      simp only [c] at hBc ⊢
      field_simp

end ZPoints

section ZWit

variable (m : ℕ) (hTr : T.Tr (m + 1)) (A : GPoly (LC m))
  (hsq : Squarefree (GPoly.toPoly (T.MP m hTr.of_succ) A))
  (hdegA : 0 < (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
  (n : ℕ) (hn : 0 < n) (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTr.of_succ) A).natDegree)
  (θ : L) (hθ : θ ^ n = T.evP m A)
  (j : ℕ) (hjc : Nat.Coprime j n) (g : LC m) (B : GPoly (LC m)) (kt l : ℕ)
  (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))] (cs : List (NFM Fc m M))
  (dC : GPoly (LC m)) (ρ : T.F m)
  (hρ : aeval ρ (toPoly M) = 0) (zN : CPoly ℚ) (gs : List (CPoly ℚ))

set_option maxHeartbeats 1600000 in
include hsq hdegA hcopA hjc hn hθ hρ in
/-- **The torsion order of a component is positive.** -/
theorem kz_comp_pos (hok : kzOK Fc ks m M A B kt l cs dC = true)
    (hc : kzConst Fc ks m n j M g A B kt l cs = true)
    (hF : kzFieldOK Fc ks m n j M g A B kt l cs zN gs = true)
    (hmin : ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree → aeval ρ P ≠ 0)
    (hD0 : ∀ q < cs.length, T.psiNFM m hTr.of_succ M ρ hρ (kzD Fc ks m M g cs q) ≠ 0)
    (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ) (f N : ℕ)
    {cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)}
    (hT : kzTorsC Fc ks m n j M g A B kt l cs zN gs cpf ps bound rs f = some (some N)) : 1 ≤ N := by
  classical
  have hTm : T.Tr m := hTr.of_succ
  set S := T.krS m hTr A hsq hdegA n hn θ hθ with hS
  set K := AlgebraicClosure (T.F m)
  set ψ := T.psiNFM m hTm M ρ hρ with hψ
  set r := cs.length with hr
  obtain ⟨hζ, hβf, -⟩ := T.kz_points m hTm n j hn hjc g A B kt l M cs dC ρ hρ zN gs hok hc hF hmin hD0
  set ζ' := aeval ρ (toPoly zN) with hζ'
  set c : ℕ → T.F m := fun q ↦ T.psiNFM m hTm M ρ hρ (kzC Fc m M cs q) with hcdef
  set βq : ℕ → T.F m := fun q ↦ ψ (kzBeta Fc ks m n j M g A B kt l cs gs q) with hβqdef
  have hin : ∀ i : Fin (r * n), (i : ℕ) / n < r := fun i ↦ (Nat.div_lt_iff_lt_mul hn).mpr i.2
  set α : Fin (r * n) → T.F m := fun i ↦ c (i / n) with hαdef
  set β : Fin (r * n) → T.F m := fun i ↦ ζ' ^ ((i : ℕ) % n) * βq (i / n) with hβdef
  have hcinj := T.kz_cinj m hTm M ρ hρ A B kt l cs dC hok
  have hSn : S.n = n := rfl
  have hSp : S.p = GPoly.toPoly (T.MP m hTm) A := rfl
  have hβ : ∀ i, β i ≠ 0 ∧ β i ^ S.n = S.p.eval (α i) := fun i ↦ by
    obtain ⟨h0, hpw⟩ := hβf _ (hin i)
    refine ⟨mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hn.ne')) h0, ?_⟩
    rw [hSn, hSp, mul_pow, ← pow_mul, mul_comm _ n, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hpw]
  have hP : Function.Injective fun i ↦ (α i, β i) := by
    intro i i' h
    have h1 : (i : ℕ) / n = i' / n := by
      have := congrArg Prod.fst h
      exact congrArg Fin.val (hcinj (a₁ := ⟨_, hin i⟩) (a₂ := ⟨_, hin i'⟩) this)
    have h2 := congrArg Prod.snd h
    simp only [hβdef, h1] at h2
    have h3 := mul_right_cancel₀ (hβf _ (hin i')).1 h2
    have h4 := hζ.pow_inj (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) h3
    apply Fin.ext
    rw [← Nat.div_add_mod i n, ← Nat.div_add_mod i' n, h1, h4]
  -- the curve over `Kₘ ⊗ N`
  have hpf : Polynomial.C ((1 : T.F m) ^ S.n) * S.p = (toPoly (kyFA Fc m M A)).map ψ := by
    rw [one_pow, map_one, one_mul, hSp, kyFA, toPoly_trim, ← toPoly_map', List.map_map,
      List.map_map, gtoPoly_eq]
    congr 1
    refine List.map_congr_left fun a _ ↦ ?_
    simp only [Function.comp_apply, hψ, T.psiNFM_embM, T.psiF_trC m hTm]
  have hp0 : Polynomial.C ((1 : T.F m) ^ S.n) * S.p ≠ 0 := by
    rw [one_pow, map_one, one_mul]; exact hsq.ne_zero
  have hsqp : Squarefree (Polynomial.C ((1 : T.F m) ^ S.n) * S.p) := by
    rw [one_pow, map_one, one_mul]; exact hsq
  have hcopp : Nat.Coprime n (Polynomial.C ((1 : T.F m) ^ S.n) * S.p).natDegree := by
    rw [one_pow, map_one, one_mul]; exact hcopA
  obtain ⟨hd, -, -⟩ := fK_factsN ψ (kyFA Fc m M A) (CPoly.trim_trim _) _ hpf hp0 hsqp n hcopp
  have hα : ∀ i, ψ (kzAl Fc m n M cs i) = α i := fun i ↦ by
    simp only [kzAl, hαdef, hcdef, hψ]
  have hβ' : ∀ i, ψ (kzBe Fc ks m n j M g A B kt l cs zN gs i) = 1 * β i := fun i ↦ by
    simp only [kzBe, map_mul, map_pow, hψ, T.psiNFM_ofQ, one_mul, hβdef, hβqdef, hζ']
  have hΓK : ∀ i, ((S.n : ℕ) : NFM Fc m M) * (kzBe Fc ks m n j M g A B kt l cs zN gs i) ^ (S.n - 1) ≠ 0 ∧
      (kzBe Fc ks m n j M g A B kt l cs zN gs i) ^ S.n =
        (toPoly (kyFA Fc m M A)).eval (kzAl Fc m n M cs i) := fun i ↦ by
    constructor
    · intro h0
      have := congrArg ψ h0
      rw [map_mul, map_pow, hβ' i, one_mul, map_natCast, map_zero] at this
      exact mul_ne_zero (by exact_mod_cast hn.ne') (pow_ne_zero _ (hβ i).1) this
    · apply ψ.injective
      rw [map_pow, hβ' i, one_mul, (hβ i).2, ← eval₂_at_apply, ← eval_map, ← hpf, hα i, one_pow,
        map_one, one_mul]
  obtain ⟨-, hsqK, hcop2⟩ := fK_factsN ψ (kyFA Fc m M A) (CPoly.trim_trim _) _ hpf hp0 hsqp n hcopp
  have hspecT := torsOracleC_specY (redAtNFM Fc m M rs) cpf
    (fun p _ R h ↦ redAtNFM_valid Fc m M rs p R h) ps bound hsqK hcop2
  have hvK : ∀ i, kzBe Fc ks m n j M g A B kt l cs zN gs i ≠ 0 ∧
      (kzBe Fc ks m n j M g A B kt l cs zN gs i) ^ n =
        (toPoly (kyFA Fc m M A)).eval (kzAl Fc m n M cs i) := fun i ↦ by
    refine ⟨fun h0 ↦ ?_, (hΓK i).2⟩
    have := congrArg ψ h0
    rw [hβ' i, one_mul, map_zero] at this
    exact (hβ i).1 this
  have hinjK : Function.Injective fun i ↦ (kzAl Fc m n M cs i, kzBe Fc ks m n j M g A B kt l cs zN gs i) := by
    intro i i' h
    apply hP
    simp only [Prod.ext_iff] at h ⊢
    refine ⟨?_, ?_⟩
    · rw [← hα i, ← hα i', h.1]
    · have := congrArg ψ h.2
      rw [hβ' i, hβ' i', one_mul, one_mul] at this
      exact this
  exact ((hspecT (cs.length * n) _ _ (kyMult n j M zN gs cs.length f) hvK hinjK).1 N hT).1

set_option maxHeartbeats 1600000 in
include hsq hdegA hcopA hjc in
/-- **The witness of a component**, read on `yⁿ = A`: divisor `N L_f D_f` away from `x = 0`. -/
theorem kz_comp_wit (hok : kzOK Fc ks m M A B kt l cs dC = true)
    (hc : kzConst Fc ks m n j M g A B kt l cs = true)
    (hF : kzFieldOK Fc ks m n j M g A B kt l cs zN gs = true)
    (hmin : ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree → aeval ρ P ≠ 0)
    (hD0 : ∀ q < cs.length, T.psiNFM m hTr.of_succ M ρ hρ (kzD Fc ks m M g cs q) ≠ 0)
    (f N : ℕ) (Wb : BPoly (NFM Fc m M))
    (hW : kzWit Fc ks m n j M g A B kt l cs zN gs f N = some Wb) :
    (∀ i a, ((toB Wb).coeff i).coeff a ≠ 0 → i < n) ∧
    ∃ W : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯⟮(T.krS m hTr A hsq hdegA n hn θ hθ).y⟯,
      W ≠ 0 ∧ (∃ u : (T.F m)⟮(T.krS m hTr A hsq hdegA n hn θ hθ).x⟯, u ≠ 0 ∧
        W = (T.krS m hTr A hsq hdegA n hn θ hθ).elemW (((toB Wb).map (mapRingHom
          (T.psiNFM m hTr.of_succ M ρ hρ))).comp (Polynomial.C (Polynomial.C 1) * X)) *
          algebraMap _ _ u) ∧
      (∀ q < cs.length, ∀ k < n, ((T.krS m hTr A hsq hdegA n hn θ hθ).ordAt
        (AlgebraicClosure (T.F m)) W
        (algebraMap (T.F m) _ (T.psiNFM m hTr.of_succ M ρ hρ (kzC Fc m M cs q)))
        (algebraMap (T.F m) _ (aeval ρ (toPoly zN) ^ k *
          T.psiNFM m hTr.of_succ M ρ hρ (kzBeta Fc ks m n j M g A B kt l cs gs q))) : ℚ) =
          N * kyDen n j M zN gs cs.length f * kyR n j M zN gs f (q * n + k)) ∧
      ∀ a b : AlgebraicClosure (T.F m), b ^ n =
        ((T.krS m hTr A hsq hdegA n hn θ hθ).p.map (algebraMap (T.F m) _)).eval a → a ≠ 0 →
        (∀ q < cs.length, a ≠ algebraMap (T.F m) _ (T.psiNFM m hTr.of_succ M ρ hρ (kzC Fc m M cs q))) →
        (T.krS m hTr A hsq hdegA n hn θ hθ).ordAt (AlgebraicClosure (T.F m)) W a b = 0 := by
  classical
  have hTm : T.Tr m := hTr.of_succ
  set S := T.krS m hTr A hsq hdegA n hn θ hθ with hS
  set K := AlgebraicClosure (T.F m)
  set ψ := T.psiNFM m hTm M ρ hρ with hψ
  set r := cs.length with hr
  obtain ⟨hζ, hβf, -⟩ := T.kz_points m hTm n j hn hjc g A B kt l M cs dC ρ hρ zN gs hok hc hF hmin hD0
  set ζ' := aeval ρ (toPoly zN) with hζ'
  set c : ℕ → T.F m := fun q ↦ T.psiNFM m hTm M ρ hρ (kzC Fc m M cs q) with hcdef
  set βq : ℕ → T.F m := fun q ↦ ψ (kzBeta Fc ks m n j M g A B kt l cs gs q) with hβqdef
  have hin : ∀ i : Fin (r * n), (i : ℕ) / n < r := fun i ↦ (Nat.div_lt_iff_lt_mul hn).mpr i.2
  set α : Fin (r * n) → T.F m := fun i ↦ c (i / n) with hαdef
  set β : Fin (r * n) → T.F m := fun i ↦ ζ' ^ ((i : ℕ) % n) * βq (i / n) with hβdef
  have hcinj := T.kz_cinj m hTm M ρ hρ A B kt l cs dC hok
  have hSn : S.n = n := rfl
  have hSp : S.p = GPoly.toPoly (T.MP m hTm) A := rfl
  have hβ : ∀ i, β i ≠ 0 ∧ β i ^ S.n = S.p.eval (α i) := fun i ↦ by
    obtain ⟨h0, hpw⟩ := hβf _ (hin i)
    refine ⟨mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hn.ne')) h0, ?_⟩
    rw [hSn, hSp, mul_pow, ← pow_mul, mul_comm _ n, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hpw]
  have hP : Function.Injective fun i ↦ (α i, β i) := by
    intro i i' h
    have h1 : (i : ℕ) / n = i' / n := by
      have := congrArg Prod.fst h
      exact congrArg Fin.val (hcinj (a₁ := ⟨_, hin i⟩) (a₂ := ⟨_, hin i'⟩) this)
    have h2 := congrArg Prod.snd h
    simp only [hβdef, h1] at h2
    have h3 := mul_right_cancel₀ (hβf _ (hin i')).1 h2
    have h4 := hζ.pow_inj (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) h3
    apply Fin.ext
    rw [← Nat.div_add_mod i n, ← Nat.div_add_mod i' n, h1, h4]
  -- the curve over `Kₘ ⊗ N`
  have hpf : Polynomial.C ((1 : T.F m) ^ S.n) * S.p = (toPoly (kyFA Fc m M A)).map ψ := by
    rw [one_pow, map_one, one_mul, hSp, kyFA, toPoly_trim, ← toPoly_map', List.map_map,
      List.map_map, gtoPoly_eq]
    congr 1
    refine List.map_congr_left fun a _ ↦ ?_
    simp only [Function.comp_apply, hψ, T.psiNFM_embM, T.psiF_trC m hTm]
  have hp0 : Polynomial.C ((1 : T.F m) ^ S.n) * S.p ≠ 0 := by
    rw [one_pow, map_one, one_mul]; exact hsq.ne_zero
  have hsqp : Squarefree (Polynomial.C ((1 : T.F m) ^ S.n) * S.p) := by
    rw [one_pow, map_one, one_mul]; exact hsq
  have hcopp : Nat.Coprime n (Polynomial.C ((1 : T.F m) ^ S.n) * S.p).natDegree := by
    rw [one_pow, map_one, one_mul]; exact hcopA
  obtain ⟨hd, -, -⟩ := fK_factsN ψ (kyFA Fc m M A) (CPoly.trim_trim _) _ hpf hp0 hsqp n hcopp
  have hα : ∀ i, ψ (kzAl Fc m n M cs i) = α i := fun i ↦ by
    simp only [kzAl, hαdef, hcdef, hψ]
  have hβ' : ∀ i, ψ (kzBe Fc ks m n j M g A B kt l cs zN gs i) = 1 * β i := fun i ↦ by
    simp only [kzBe, map_mul, map_pow, hψ, T.psiNFM_ofQ, one_mul, hβdef, hβqdef, hζ']
  have hΓK : ∀ i, ((S.n : ℕ) : NFM Fc m M) * (kzBe Fc ks m n j M g A B kt l cs zN gs i) ^ (S.n - 1) ≠ 0 ∧
      (kzBe Fc ks m n j M g A B kt l cs zN gs i) ^ S.n =
        (toPoly (kyFA Fc m M A)).eval (kzAl Fc m n M cs i) := fun i ↦ by
    constructor
    · intro h0
      have := congrArg ψ h0
      rw [map_mul, map_pow, hβ' i, one_mul, map_natCast, map_zero] at this
      exact mul_ne_zero (by exact_mod_cast hn.ne') (pow_ne_zero _ (hβ i).1) this
    · apply ψ.injective
      rw [map_pow, hβ' i, one_mul, (hβ i).2, ← eval₂_at_apply, ← eval_map, ← hpf, hα i, one_pow,
        map_one, one_mul]
  obtain ⟨hW0ne, hWord⟩ := S.pts_witness (K := K) hcopA α β hP hβ
    (kyMult n j M zN gs cs.length f) ψ (kyFA Fc m M A) 1 one_ne_zero hpf hd _ _ hα hβ' hΓK N Wb hW
  set W0 := S.elemW (((toB Wb).map (mapRingHom ψ)).comp (Polynomial.C (Polynomial.C 1) * X))
    with hW0def
  set sh : ℕ → ℤ := fun q ↦ kySh n j M zN gs cs.length f q with hsh
  letI := algebraAdjoinSimple (F := T.F m) S.x
  set u : (T.F m)⟮S.x⟯ := ∏ q : Fin r,
    (algebraMap (T.F m)[X] (T.F m)⟮S.x⟯ (X - Polynomial.C (c q))) ^ (-((N : ℤ) * sh q)) with hu
  have hlin0 : ∀ q : Fin r, algebraMap (T.F m)[X] (T.F m)⟮S.x⟯ (X - Polynomial.C (c q)) ≠ 0 :=
    fun q h0 ↦ S.polyX_ne_zero (X_sub_C_ne_zero (c q)) (by
      show algebraMap _ _ (algebraMap (T.F m)[X] (T.F m)⟮S.x⟯ _) = 0
      rw [h0, map_zero])
  have hu0 : u ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q _ ↦ zpow_ne_zero _ (hlin0 q)
  have huW : algebraMap (T.F m)⟮S.x⟯ (T.F m)⟮S.x⟯⟮S.y⟯ u =
      ∏ q : Fin r, S.polyX (X - Polynomial.C (c q)) ^ (-((N : ℤ) * sh q)) := by
    rw [hu, map_prod]
    simp only [map_zpow₀]
    rfl
  have hU0 : algebraMap (T.F m)⟮S.x⟯ (T.F m)⟮S.x⟯⟮S.y⟯ u ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (T.F m)⟮S.x⟯ (T.F m)⟮S.x⟯⟮S.y⟯).injective).mpr hu0
  have hordu : ∀ a b : K, b ^ S.n = (S.p.map (algebraMap (T.F m) K)).eval a → b ≠ 0 →
      S.ordAt K (algebraMap (T.F m)⟮S.x⟯ (T.F m)⟮S.x⟯⟮S.y⟯ u) a b =
        ∑ q : Fin r, if a = algebraMap (T.F m) K (c q) then -((N : ℤ) * sh q) else 0 := by
    intro a b hv hb
    rw [huW, S.ordAt_prod hv _ _ (fun q _ ↦ zpow_ne_zero _ (S.polyX_ne_zero (X_sub_C_ne_zero _)))]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [S.ordAt_zpow hv, S.ordAt_X_sub _ a b hv]
    split_ifs <;> simp
  -- the value of `gammaPts` at the points
  have hgam : ∀ i : Fin (r * n), Differential.SuperData.gammaPts (K := K) α β
      (kyMult n j M zN gs cs.length f) (algebraMap (T.F m) K (α i), algebraMap (T.F m) K (β i)) =
      kyMult n j M zN gs cs.length f i := fun i ↦ by
    rw [Differential.SuperData.gammaPts, Finset.sum_eq_single i]
    · simp
    · intro i' _ hi'
      rw [if_neg]
      intro h
      apply hi'
      apply hP
      simp only [Prod.ext_iff] at h ⊢
      exact ⟨((algebraMap (T.F m) K).injective h.1).symm, ((algebraMap (T.F m) K).injective h.2).symm⟩
    · simp
  obtain ⟨-, hWs, -⟩ := witW_spec (kyFA Fc m M A) S.n S.hn _ _ _ _ N hΓK hW
  refine ⟨fun i a h ↦ (hWs i a h).1, W0 * algebraMap _ _ u, mul_ne_zero hW0ne hU0, ⟨u, hu0, rfl⟩,
    fun q hq k hk ↦ ?_, fun a b hv ha hq ↦ ?_⟩
  · set i : Fin (r * n) := ⟨q * n + k, by nlinarith⟩ with hi
    have hiq : (i : ℕ) / n = q := by
      simp only [hi]
      rw [Nat.add_div_of_dvd_right (Dvd.intro_left _ rfl), Nat.mul_div_cancel _ hn,
        Nat.div_eq_of_lt hk, add_zero]
    have hik : (i : ℕ) % n = k := by
      simp only [hi]; rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hk]
    have hpt : algebraMap (T.F m) K (aeval ρ (toPoly zN) ^ k * ψ (kzBeta Fc ks m n j M g A B kt l cs gs q))
        = algebraMap (T.F m) K (β i) := by simp only [hβdef, hiq, hik, hβqdef, hζ']
    have hpc : algebraMap (T.F m) K (T.psiNFM m hTm M ρ hρ (kzC Fc m M cs q)) =
        algebraMap (T.F m) K (α i) := by simp only [hαdef, hiq, hcdef]
    have hv := (hβ i).2
    have hvK : (algebraMap (T.F m) K (β i)) ^ S.n =
        (S.p.map (algebraMap (T.F m) K)).eval (algebraMap (T.F m) K (α i)) := by
      rw [← map_pow, hv, eval_map, eval₂_at_apply]
    have hb0 : algebraMap (T.F m) K (β i) ≠ 0 := (_root_.map_ne_zero _).mpr (hβ i).1
    rw [hpt, hpc, S.ordAt_mul hvK hW0ne hU0, hWord _ _ hvK, hgam i, hordu _ _ hvK hb0,
      Finset.sum_eq_single ⟨q, hq⟩ (fun q' _ hq' ↦ by
        rw [if_neg]; intro h
        apply hq'
        apply hcinj
        have := (algebraMap (T.F m) K).injective h
        simp only [hαdef, hiq, hcdef] at this
        exact this.symm) (fun h ↦ absurd (Finset.mem_univ _) h),
      if_pos (by simp [hαdef, hiq, hcdef])]
    -- `mult = zc + sh ≥ 0`
    have hzc := Differential.SuperData.rat_mul_den_int (kyR n j M zN gs f i)
      (kyDen n j M zN gs cs.length f)
      (dvd_lcmL (List.mem_map.mpr ⟨i, List.mem_range.mpr i.2, rfl⟩))
    have hshq : -kyZc n j M zN gs cs.length f i ≤ kySh n j M zN gs cs.length f q := by
      simp only [kySh]
      refine foldr_max_ge _ _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, ?_⟩)
      simp only [hi]
    have hmult : (kyMult n j M zN gs cs.length f i : ℤ) =
        kyZc n j M zN gs cs.length f i + kySh n j M zN gs cs.length f q := by
      rw [kyMult, hiq, Int.toNat_of_nonneg (by omega)]
    have hzcq : (kyZc n j M zN gs cs.length f i : ℚ) =
        kyDen n j M zN gs cs.length f * kyR n j M zN gs f i := by
      rw [kyZc, hzc]
    have hkyR : kyR n j M zN gs f i = kyR n j M zN gs f (q * n + k) := rfl
    push_cast
    rw [← hkyR]
    have := congrArg (fun z : ℤ ↦ (z : ℚ)) hmult
    push_cast at this
    rw [this, hzcq, hsh]
    show _ = (N : ℚ) * (kyDen n j M zN gs cs.length f : ℚ) * _
    ring
  · have hvK : b ^ S.n = (S.p.map (algebraMap (T.F m) K)).eval a := hv
    rw [S.ordAt_mul hvK hW0ne hU0, hWord _ _ hvK, huW,
      S.ordAt_prod hvK _ _ (fun q _ ↦ zpow_ne_zero _ (S.polyX_ne_zero (X_sub_C_ne_zero _)))]
    have hg0 : Differential.SuperData.gammaPts (K := K) α β (kyMult n j M zN gs cs.length f) (a, b) = 0 := by
      rw [Differential.SuperData.gammaPts]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [if_neg]
      intro h
      exact hq _ (hin i) (by simpa [hαdef, hcdef] using (Prod.ext_iff.mp h).1)
    rw [hg0, Finset.sum_eq_zero fun q _ ↦ by
      rw [S.ordAt_zpow hvK, S.ordAt_X_sub _ a b hvK, if_neg (hq q q.2), mul_zero]]
    simp

end ZWit

end MTower

end Curves.MT
