import RischTragerBronstein.Mixed.KYMain
import RischTragerBronstein.Mixed.KYGcd
import RischTragerBronstein.Mixed.KRDecides
import RischTragerBronstein.Mixed.KQMDecides

/-!
# Radicals over an exponential level with poles: the decision answers

`kyDecideL` (local torsion certificates over `Kₘ ⊗ N`) answers for every large bound at suitable
residues, unless a component is certified non-torsion while the orders over `t = 0` cannot be
killed (a Mordell–Weil relation question, `kyDecideL_decides`).

The points over the poles are valid points of `yⁿ = A` over `Kₘ ⊗ N` (`ky_ptsM`): the field facts
are read at the root `X` of `M` in `Kₘ ⊗ N` itself (`aeval_gammaM`), and the constant facts
through the injective `ψ : Kₘ → Fₘ`. The oracle answers (`kfm_query_els`), a torsion answer gives a
witness (`witW_ne_none`) and the column computation succeeds (`ky_gcd_coprime`). With
`kyDecide_correct`: `ky_decided`.
-/

open Polynomial Differential IntermediateField CPoly CPoly.Kron Ramanujan

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

section NFMQ

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (m : ℕ) (M : CPoly ℚ)
  [Fact (Irreducible (toPoly (liftQ Fc m M)))]

lemma mk_eq_eval₂M (l : CPoly (KF Fc m)) :
    (NFK.mk _ l : NFM Fc m M) = (toPoly l).eval₂ (eM Fc m M) (gammaM Fc m M) := by
  apply NFK.toAR_injective
  have h : NFK.toARHom (liftQ Fc m M) ((toPoly l).eval₂ (eM Fc m M) (gammaM Fc m M)) =
      (toPoly l).eval₂ ((NFK.toARHom _).comp (eM Fc m M)) (NFK.toARHom _ (gammaM Fc m M)) := by
    rw [hom_eval₂]
  have e1 : (NFK.toARHom (liftQ Fc m M)).comp (eM Fc m M) = AdjoinRoot.of _ := by
    ext b
    change NFK.toAR _ (embM Fc m M b) = _
    rw [toAR_embM]; rfl
  have e2 : NFK.toARHom (liftQ Fc m M) (gammaM Fc m M) = AdjoinRoot.root _ := by
    change NFK.toAR _ (NFK.mk _ [0, 1]) = _
    rw [NFK.toAR_mk]; simp [CPoly.toPoly]
  rw [NFK.toAR_mk]
  change _ = NFK.toARHom _ _
  rw [h, e1, e2, ← AdjoinRoot.algebraMap_eq, ← aeval_def, AdjoinRoot.aeval_eq]

lemma algebraMap_NFM :
    algebraMap ℚ (NFM Fc m M) = (eM Fc m M).comp (algebraMap ℚ (KF Fc m)) :=
  RingHom.ext_rat _ _

lemma aeval_gammaM (l : CPoly ℚ) : aeval (gammaM Fc m M) (toPoly l) = ofQ Fc m M l := by
  have e : List.map (fun q : ℚ ↦ (Rat.cast q : KF Fc m)) l = l.map (algebraMap ℚ (KF Fc m)) :=
    List.map_congr_left fun q _ ↦ (eq_ratCast _ q).symm
  rw [ofQ, mk_eq_eval₂M, e, toPoly_map', eval₂_map, aeval_def, algebraMap_NFM]

lemma aeval_gammaM_M : aeval (gammaM Fc m M) (toPoly M) = 0 := by
  rw [aeval_def, algebraMap_NFM, ← eval₂_map, ← toPoly_liftQ]
  exact eval₂_gammaM Fc m M

lemma hmin_gammaM : ∀ P : ℚ[X], P ≠ 0 → P.degree < (toPoly M).degree →
    aeval (gammaM Fc m M) P ≠ 0 :=
  hmin_of_irr M _ (aeval_gammaM_M Fc m M) (K := KF Fc m) (by rw [← toPoly_liftQ]; exact Fact.out)

lemma ofQ_powQ (a : CPoly ℚ) (k : ℕ) : ofQ Fc m M (powQ M a k) = ofQ Fc m M a ^ k := by
  rw [← aeval_gammaM, aeval_powQ M _ (aeval_gammaM_M Fc m M), aeval_gammaM]

lemma ofQ_normC (q : ℚ) : ofQ Fc m M (NFK.norm M [q]) = (q : NFM Fc m M) := by
  rw [← aeval_gammaM, aeval_normQ M _ (aeval_gammaM_M Fc m M)]; simp [CPoly.toPoly]

lemma eM_ratCast (q : ℚ) : eM Fc m M (q : KF Fc m) = (q : NFM Fc m M) := map_ratCast _ q

/-- The checked `ζ` is a primitive `n`-th root of unity of `Kₘ ⊗ N`. -/
lemma zetaM_prim (htrim : CPoly.trim M = M) (hlen : 1 < M.length) (n : ℕ) (hn : 0 < n)
    (zN : CPoly ℚ) (h1 : powQ M zN n = NFK.norm M [1])
    (h2 : ∀ k, 0 < k → k < n → powQ M zN k ≠ NFK.norm M [1]) :
    IsPrimitiveRoot (ofQ Fc m M zN) n := by
  have hM0 : toPoly M ≠ 0 := by
    intro h0
    have := (trim_eq_nil_iff M).mpr h0
    rw [htrim] at this; rw [this] at hlen; simp at hlen
  rw [← aeval_gammaM]
  exact zeta_prim M _ (aeval_gammaM_M Fc m M) (hmin_gammaM Fc m M) hM0 n hn zN h1 h2

lemma toPoly_kyFA (A' : GPoly (LC m)) :
    toPoly (kyFA Fc m M A') = (toPoly (A'.map (trC Fc m))).map (eM Fc m M) := by
  rw [kyFA, CPoly.toPoly_trim, ← toPoly_map']; rfl

include Fc m in
/-- The integral data of `M` for `kfm_query_els`. -/
lemma M_clear (htrim : CPoly.trim M = M) (hlen : 1 < M.length) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ mZ : ℤ[X], mZ.map (Int.castRingHom ℚ) = C (D : ℚ) * toPoly M ∧
      (mZ.map (Int.castRingHom ℚ)).Separable ∧ 0 < mZ.natDegree := by
  obtain ⟨D, hD, mZ, hmZ⟩ := exists_clear_int (toPoly M)
  have hirr : Irreducible ((toPoly M).map (algebraMap ℚ (KF Fc m))) := by
    rw [← toPoly_liftQ]; exact Fact.out
  have hsep : (toPoly M).Separable := (separable_map _).mp hirr.separable
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hsq : Squarefree (C (D : ℚ) * toPoly M) :=
    (Associated.squarefree_iff (associated_unit_mul_left _ (C (D : ℚ))
      (isUnit_C.mpr (Ne.isUnit hD')))).mpr hsep.squarefree
  refine ⟨D, hD, mZ, hmZ, hmZ ▸ PerfectField.separable_iff_squarefree.mpr hsq, ?_⟩
  have hMdeg : 0 < (toPoly M).natDegree := by
    have hMne : M ≠ [] := fun h ↦ by rw [h] at hlen; simp at hlen
    have := CPoly.length_trim (p := M) (by rw [htrim]; exact hMne)
    rw [htrim] at this; omega
  rw [← natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)), hmZ,
    natDegree_C_mul hD']
  exact hMdeg

end NFMQ

section ZeroQ

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)

/-- `κ = zⁿ A(0)` as a rational. -/
def kyKap (m n : ℕ) (A : GPoly (LC m)) (z : LC m) : ℚ :=
  (ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n) (A.getD 0 (MO Fc ks m).zero))).getD 0

/-- The torsion answer for the point `(0, ζᵏ)` of the twist (one query of `kyZeroTorsC`). -/
def kyZeroQ (m n : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    (A : GPoly (LC m)) (zN : CPoly ℚ) (z : LC m) (κ : ℚ)
    (cpf : CPoly (NFM Fc m M) → CertProv (NFM Fc m M)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (k : ℕ) : Option (Option ℕ) :=
  torsOracleC (redAtNFM Fc m M rs) (cpf (kyFA Fc m M (krAh Fc ks m n A z κ))) ps bound
    (kyFA Fc m M (krAh Fc ks m n A z κ)) n
    (gammaL ![(0 : NFM Fc m M)] ![ofQ Fc m M zN ^ k] ![1] 1)

end ZeroQ

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

section Pts

variable (m : ℕ) (hm : T.Tr m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]

lemma eM_trC_eq_zero {x : LC m} (h : eM Fc m M (trC Fc m x) = 0) : (T.MP m hm).sem x = 0 := by
  rw [← T.psiF_trC m hm, (map_eq_zero_iff _ (eM Fc m M).injective).mp h, map_zero]

include T hm in
lemma trC_evalGC (A' : GPoly (LC m)) (c : LC m) :
    trC Fc m (evalGC Fc ks m A' c) = (toPoly (A'.map (trC Fc m))).eval (trC Fc m c) := by
  apply (T.psiF m hm).injective
  rw [T.psiF_trC m hm, T.sem_evalGC m hm, ← eval₂_at_apply, ← eval_map, T.toPoly_trC_map m hm,
    T.psiF_trC m hm]

include T hm in
lemma eval_kyFA (A' : GPoly (LC m)) (c : LC m) :
    (toPoly (kyFA Fc m M A')).eval (eM Fc m M (trC Fc m c)) =
      eM Fc m M (trC Fc m (evalGC Fc ks m A' c)) := by
  rw [toPoly_kyFA, eval_map, eval₂_at_apply, T.trC_evalGC m hm]

set_option maxHeartbeats 1600000 in
/-- **The points over the poles** are points of `yⁿ = A` over `Kₘ ⊗ N`, pairwise distinct. -/
theorem ky_ptsM (n j : ℕ) (hn : 0 < n) (hjc : Nat.Coprime j n) (g : LC m) (A B : GPoly (LC m))
    (kt l : ℕ) (cs : List (LC m)) (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (hok : kxOK Fc ks m A B kt l cs = true)
    (hc : kyConst Fc ks m n j g A B kt l cs = true)
    (hF : kyFieldOK Fc ks m n j g A B kt l cs M zN gs = true)
    (hD0 : ∀ q < cs.length, (T.MP m hm).sem (kxD Fc ks m g cs q) ≠ 0) :
    IsPrimitiveRoot (ofQ Fc m M zN) n ∧
    (∀ i, kyBe Fc ks m n j M g A B kt l cs zN gs i ≠ 0 ∧
      kyBe Fc ks m n j M g A B kt l cs zN gs i ^ n =
        (toPoly (kyFA Fc m M A)).eval (kyAl Fc ks m n M cs i)) ∧
    Function.Injective fun i ↦
      (kyAl Fc ks m n M cs i, kyBe Fc ks m n j M g A B kt l cs zN gs i) := by
  obtain ⟨htrim, hlen, hz1, hz2, -, hgn⟩ := kyFieldOK_spec hF
  have hζ := zetaM_prim Fc m M htrim hlen n hn zN hz1 hz2
  have hok' := T.kxOK_spec m hm A B kt l cs hok
  have hε0 : ∀ x, (T.MP m hm).sem x ≠ 0 → eM Fc m M (trC Fc m x) ≠ 0 :=
    fun x hx h0 ↦ hx (T.eM_trC_eq_zero m hm M h0)
  -- the roots `β_q`
  have hβ : ∀ q < cs.length, kyBeta Fc ks m n j M g A B kt l cs gs q ≠ 0 ∧
      kyBeta Fc ks m n j M g A B kt l cs gs q ^ n =
        eM Fc m M (trC Fc m (evalGC Fc ks m A (kqC Fc ks m cs q))) := by
    intro q hq
    have hAc := (hok'.2 q hq).2.2.1
    have hBc := (hok'.2 q hq).2.2.2
    have hR0 := (hok'.2 q hq).2.1
    have hAε : eM Fc m M (trC Fc m (evalGC Fc ks m A (kqC Fc ks m cs q))) ≠ 0 :=
      hε0 _ (by rw [T.sem_evalGC m hm]; exact hAc)
    have hρε : eM Fc m M (trC Fc m (kyRho Fc ks m g A B kt l cs q)) ≠ 0 :=
      hε0 _ (by
        rw [T.sem_kyRho m hm]; exact div_ne_zero hBc (mul_ne_zero (hD0 q hq) hR0))
    have hQ : trC Fc m (kyQ Fc ks m n j g A B kt l cs q) =
        trC Fc m (kyRho Fc ks m g A B kt l cs q) ^ n *
          trC Fc m (evalGC Fc ks m A (kqC Fc ks m cs q)) ^ j := by
      apply (T.psiF m hm).injective
      rw [map_mul, map_pow, map_pow, T.psiF_trC m hm, T.psiF_trC m hm, T.psiF_trC m hm,
        T.sem_kyQ m hm, T.sem_evalGC m hm]
    have hκ : trC Fc m (kyQ Fc ks m n j g A B kt l cs q) =
        ((kyK Fc ks m n j g A B kt l cs q : ℚ) : KF Fc m) := by
      apply (T.psiF m hm).injective
      rw [T.psiF_trC m hm, T.kyConst_spec m hm n j g A B kt l cs hc q hq, map_ratCast]
    have hγn : ofQ Fc m M (gs.getD q []) ^ n =
        eM Fc m M (trC Fc m (kyRho Fc ks m g A B kt l cs q)) ^ n *
          eM Fc m M (trC Fc m (evalGC Fc ks m A (kqC Fc ks m cs q))) ^ j := by
      rw [← ofQ_powQ, hgn q hq, ofQ_normC, ← eM_ratCast, ← hκ, hQ, map_mul, map_pow, map_pow]
    have hγ0 : ofQ Fc m M (gs.getD q []) ≠ 0 := fun h0 ↦ by
      rw [h0, zero_pow hn.ne'] at hγn
      exact mul_ne_zero (pow_ne_zero _ hρε) (pow_ne_zero _ hAε) hγn.symm
    have hu0 : ofQ Fc m M (gs.getD q []) * (eM Fc m M (trC Fc m (kyRho Fc ks m g A B kt l cs q)))⁻¹
        ≠ 0 := mul_ne_zero hγ0 (inv_ne_zero hρε)
    have hun : (ofQ Fc m M (gs.getD q []) *
        (eM Fc m M (trC Fc m (kyRho Fc ks m g A B kt l cs q)))⁻¹) ^ n =
        eM Fc m M (trC Fc m (evalGC Fc ks m A (kqC Fc ks m cs q))) ^ j := by
      rw [mul_pow, hγn, inv_pow]; field_simp
    have hab : (Nat.gcdA j n : ℤ) * j + Nat.gcdB j n * n = 1 := by
      have := Nat.gcd_eq_gcd_ab j n
      rw [hjc] at this; push_cast at this; linarith
    obtain ⟨hβn, -⟩ := kummer_root _ _ hu0 hAε n j _ _ hab hun
    have hβe : kyBeta Fc ks m n j M g A B kt l cs gs q =
        (ofQ Fc m M (gs.getD q []) *
          (eM Fc m M (trC Fc m (kyRho Fc ks m g A B kt l cs q)))⁻¹) ^ (Nat.gcdA j n) *
        eM Fc m M (trC Fc m (evalGC Fc ks m A (kqC Fc ks m cs q))) ^ (Nat.gcdB j n) := rfl
    rw [hβe]
    exact ⟨fun h0 ↦ hAε (by rw [← hβn, h0, zero_pow hn.ne']), hβn⟩
  have hin : ∀ i : Fin (cs.length * n), (i : ℕ) / n < cs.length :=
    fun i ↦ (Nat.div_lt_iff_lt_mul hn).mpr i.2
  have hcinj := T.kx_cinj m hm A B kt l cs hok
  refine ⟨hζ, fun i ↦ ⟨?_, ?_⟩, fun i i' h ↦ ?_⟩
  · exact mul_ne_zero (pow_ne_zero _ (hζ.ne_zero hn.ne')) (hβ _ (hin i)).1
  · rw [kyBe, mul_pow, ← pow_mul, mul_comm _ n, pow_mul, hζ.pow_eq_one, one_pow, one_mul,
      (hβ _ (hin i)).2]
    exact (T.eval_kyFA m hm M A _).symm
  · simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : (i : ℕ) / n = i' / n := by
      have : (T.MP m hm).sem (kqC Fc ks m cs (i / n)) = (T.MP m hm).sem (kqC Fc ks m cs (i' / n)) := by
        rw [← T.psiF_trC m hm, ← T.psiF_trC m hm, (eM Fc m M).injective h1]
      exact congrArg Fin.val (hcinj (a₁ := ⟨_, hin i⟩) (a₂ := ⟨_, hin i'⟩) this)
    simp only [kyBe, h1'] at h2
    have h3 := mul_right_cancel₀ (hβ _ (hin i')).1 h2
    have h4 := hζ.pow_inj (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) h3
    apply Fin.ext
    rw [← Nat.div_add_mod i n, ← Nat.div_add_mod i' n, h1', h4]

/-- **The curve over `Kₘ ⊗ N`** of a scaled `A`. -/
theorem kyFA_facts (A' A : GPoly (LC m)) (cF : T.F m) (hc0 : cF ≠ 0)
    (hpf : (toPoly (A'.map (trC Fc m))).map (T.psiF m hm) = C cF * GPoly.toPoly (T.MP m hm) A)
    (hsq : Squarefree (GPoly.toPoly (T.MP m hm) A)) (n : ℕ)
    (hcop : Nat.Coprime n (GPoly.toPoly (T.MP m hm) A).natDegree)
    (hdpos : 0 < (GPoly.toPoly (T.MP m hm) A).natDegree) :
    let fK := kyFA Fc m M A'
    let P0 := (toPoly (A'.map (trC Fc m))).map (eM Fc m M)
    0 < fK.length - 1 ∧ fK.getD (fK.length - 1) 0 ≠ 0 ∧ Squarefree (toPoly fK) ∧
      Nat.Coprime n (fK.length - 1) ∧ Squarefree P0 ∧ 0 < P0.natDegree := by
  intro fK P0
  set P := toPoly (A'.map (trC Fc m)) with hP
  have hsqI : Squarefree (C cF * GPoly.toPoly (T.MP m hm) A) :=
    (Associated.squarefree_iff (associated_unit_mul_left _ (C cF)
      (isUnit_C.mpr (Ne.isUnit hc0)))).mpr hsq
  have hPsq : Squarefree P := squarefree_of_map (T.psiF m hm) P (by rw [hpf]; exact hsqI)
  have hPdeg : P.natDegree = (GPoly.toPoly (T.MP m hm) A).natDegree := by
    rw [← natDegree_map_eq_of_injective (T.psiF m hm).injective, hpf, natDegree_C_mul hc0]
  have hfK : toPoly fK = P0 := toPoly_kyFA Fc m M A'
  have hsep : P0.Separable := (PerfectField.separable_iff_squarefree.mpr hPsq).map
  have hne : toPoly fK ≠ 0 := by rw [hfK]; exact hsep.squarefree.ne_zero
  have hnd : (toPoly fK).natDegree = P.natDegree := by
    rw [hfK, natDegree_map_eq_of_injective (eM Fc m M).injective]
  have htrim : CPoly.trim fK = fK := by simp only [fK, kyFA, CPoly.trim_trim]
  have htne : CPoly.trim fK ≠ [] := fun h0 ↦ hne ((CPoly.trim_eq_nil_iff fK).mp h0)
  have hlen := CPoly.length_trim htne
  rw [htrim] at hlen
  have hl1 : fK.length - 1 = P.natDegree := by omega
  refine ⟨by omega, ?_, hfK ▸ hsep.squarefree, by rw [hl1, hPdeg]; exact hcop, hsep.squarefree,
    by rw [← hfK, hnd, hPdeg]; exact hdpos⟩
  rw [← coeff_toPoly, show fK.length - 1 = (toPoly fK).natDegree by omega]
  exact leadingCoeff_ne_zero.mpr hne

/-- **The twist over `Kₘ ⊗ N`.** -/
theorem kyPsi_facts (n : ℕ) (A : GPoly (LC m)) (hsq : Squarefree (GPoly.toPoly (T.MP m hm) A))
    (hcop : Nat.Coprime n (GPoly.toPoly (T.MP m hm) A).natDegree)
    (hdpos : 0 < (GPoly.toPoly (T.MP m hm) A).natDegree)
    (z : LC m) (κ : ℚ) (hκ0 : κ ≠ 0) (hz0 : (T.MP m hm).sem z ≠ 0)
    (hzκ : (T.MP m hm).sem z ^ n * (T.MP m hm).sem (A.getD 0 (MO Fc ks m).zero) = (κ : T.F m)) :
    let fK := kyFA Fc m M (krAh Fc ks m n A z κ)
    let P0 := (toPoly ((krAh Fc ks m n A z κ).map (trC Fc m))).map (eM Fc m M)
    0 < fK.length - 1 ∧ fK.getD (fK.length - 1) 0 ≠ 0 ∧ Squarefree (toPoly fK) ∧
      Nat.Coprime n (fK.length - 1) ∧ Squarefree P0 ∧ 0 < P0.natDegree ∧
      (toPoly fK).eval 0 = 1 := by
  intro fK P0
  set cF : T.F m := (T.MP m hm).sem ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
    (mcst Fc ks m κ⁻¹)) with hcFdef
  have hcF : cF = (T.MP m hm).sem z ^ n * ((κ⁻¹ : ℚ) : T.F m) := by
    rw [hcFdef, (T.MP m hm).sem_mul, sem_powC, T.sem_mcst]
  have hκF : ((κ : ℚ) : T.F m) ≠ 0 := by exact_mod_cast hκ0
  have hc0 : cF ≠ 0 := by
    rw [hcF]; exact mul_ne_zero (pow_ne_zero _ hz0) (by push_cast; exact inv_ne_zero hκF)
  have hpf : (toPoly ((krAh Fc ks m n A z κ).map (trC Fc m))).map (T.psiF m hm) =
      C cF * GPoly.toPoly (T.MP m hm) A := by
    rw [T.toPoly_trC_map m hm]
    have e : krAh Fc ks m n A z κ = GPoly.smul (MO Fc ks m) ((MO Fc ks m).mul
        (powC (MO Fc ks m) z n) (mcst Fc ks m κ⁻¹)) A := rfl
    rw [e, GPoly.toPoly_smul]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := T.kyFA_facts m hm M _ A cF hc0 hpf hsq n hcop hdpos
  refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
  have hP0e : (toPoly ((krAh Fc ks m n A z κ).map (trC Fc m))).eval 0 = 1 := by
    apply (T.psiF m hm).injective
    rw [map_one, ← eval₂_at_apply, map_zero, ← eval_map, hpf, eval_mul, eval_C,
      T.toPoly_eval_zero m hm, hcF, mul_assoc, mul_comm (((κ⁻¹ : ℚ) : T.F m)), ← mul_assoc, hzκ]
    push_cast; exact mul_inv_cancel₀ hκF
  change (toPoly (kyFA Fc m M (krAh Fc ks m n A z κ))).eval 0 = 1
  rw [toPoly_kyFA, eval_map, ← map_zero (eM Fc m M), eval₂_at_apply, hP0e, map_one]

end Pts

section Solve

variable (m : ℕ) (hm : T.Tr m) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
  [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))]

include T in
/-- `kyColM` answers on a non-zero witness of `Y`-degree `< n`. -/
lemma kyColM_isSome (n : ℕ) (hn : 1 < n) (hm : T.Tr m) (htrim : CPoly.trim M = M)
    (W : BPoly (NFM Fc m M)) (hW0 : toB W ≠ 0) (hWd : (toB W).natDegree < n) (Ah : GPoly (LC m))
    (hAsq : Squarefree ((toPoly (Ah.map (trC Fc m))).map (eM Fc m M)))
    (hAd : 0 < ((toPoly (Ah.map (trC Fc m))).map (eM Fc m M)).natDegree) (z : LC m) (j : ℕ) :
    (kyColM Fc ks m n M Ah z j W).isSome := by
  have hcop := T.ky_gcd_coprime m n hn hm M htrim W hW0 hWd Ah hAsq hAd
  unfold kyColM
  simp only
  rw [if_pos (trim_egcd_length _ _ hcop)]
  simp

lemma mem_of_allSome {α : Type*} {l : List (Option α)} {l' : List α} (h : l.allSome = some l')
    {y : α} (hy : y ∈ l') : some y ∈ l := by
  obtain ⟨h1, h2⟩ := allSome_spec l l' h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  rw [← h2 i (by omega) hi]
  exact List.getElem_mem _

set_option maxHeartbeats 1600000 in
open Classical in
/-- `kySolveC` answers when every component is torsion. -/
lemma kySolveC_isSome (n j : ℕ) (hn1 : 1 < n) (hjc : Nat.Coprime j n) (g : LC m)
    (htrim : CPoly.trim M = M) (zN : CPoly ℚ) (gs : List (CPoly ℚ)) (A B : GPoly (LC m))
    (kt l : ℕ) (cs : List (LC m))
    (hok : kxOK Fc ks m A B kt l cs = true)
    (hc : kyConst Fc ks m n j g A B kt l cs = true)
    (hF : kyFieldOK Fc ks m n j g A B kt l cs M zN gs = true)
    (hD0 : ∀ q < cs.length, (T.MP m hm).sem (kxD Fc ks m g cs q) ≠ 0)
    (hsq : Squarefree (GPoly.toPoly (T.MP m hm) A))
    (hcop : Nat.Coprime n (GPoly.toPoly (T.MP m hm) A).natDegree)
    (hdpos : 0 < (GPoly.toPoly (T.MP m hm) A).natDegree)
    (rs : ℕ → ℕ) (Bd : ℕ) (extra : List (LC (m + 1)))
    (hall : ∀ f ∈ (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length), ∃ N,
      kyTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n) (primesBelow Bd) Bd rs f =
        some (some N)) :
    (kySolveC Fc ks lv m n j g M zN gs A B kt l cs (fun fK ↦ localCert fK n) (primesBelow Bd) Bd
      rs extra).isSome := by
  have hn0 : 0 < n := by omega
  obtain ⟨hζ, hvK, hinjK⟩ := T.ky_ptsM m hm M n j hn0 hjc g A B kt l cs zN gs hok hc hF hD0
  obtain ⟨hd, hlc, hsqK, hcop2, hP0sq, hP0deg⟩ := T.kyFA_facts m hm M A A 1 one_ne_zero
    (by rw [map_one, one_mul]; exact T.toPoly_trC_map m hm A) hsq n hcop hdpos
  have hspec := torsOracleC_spec (redAtNFM Fc m M rs) (localCert (kyFA Fc m M A) n)
    (fun p _ R h ↦ redAtNFM_valid Fc m M rs p R h) (primesBelow Bd) Bd hsqK hcop2
  have hΓ : ∀ i, ((n : ℕ) : NFM Fc m M) * kyBe Fc ks m n j M g A B kt l cs zN gs i ^ (n - 1) ≠ 0 ∧
      kyBe Fc ks m n j M g A B kt l cs zN gs i ^ n =
        (toPoly (kyFA Fc m M A)).eval (kyAl Fc ks m n M cs i) :=
    fun i ↦ ⟨mul_ne_zero (by exact_mod_cast hn0.ne') (pow_ne_zero _ (hvK i).1), (hvK i).2⟩
  unfold kySolveC
  dsimp only
  set comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length) with hcomps
  set tors := comps.map (kyTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n)
    (primesBelow Bd) Bd rs) with htorsdef
  have hwit : ∀ f N, kyTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n)
      (primesBelow Bd) Bd rs f = some (some N) →
      kyWit Fc ks m n j M g A B kt l cs zN gs f N ≠ none := by
    intro f N hN
    have hP := ((hspec _ _ _ (kyMult n j M zN gs cs.length f) hvK hinjK).1 N hN).2
    exact witW_ne_none _ n hn0 _ _ _ _ N hΓ hP
  have hws : ∀ p ∈ List.zip comps tors,
      kyWit Fc ks m n j M g A B kt l cs zN gs p.1 ((p.2.getD none).getD 0) ≠ none := by
    intro p hp
    have hp1 : p.1 ∈ comps := (List.of_mem_zip hp).1
    have hp2 : p.2 = kyTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n)
        (primesBelow Bd) Bd rs p.1 := by
      obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
      rw [← hpi]
      simp [htorsdef]
    obtain ⟨N, hN⟩ := hall p.1 hp1
    rw [hp2, hN]
    exact hwit p.1 N hN
  rcases hW : ((List.zip comps tors).map fun p ↦
      kyWit Fc ks m n j M g A B kt l cs zN gs p.1 ((p.2.getD none).getD 0)).allSome with _ | Wbs
  · exfalso
    refine allSome_ne_none _ (fun y hy h0 ↦ ?_) hW
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    exact hws p hp h0
  · rcases hC : (Wbs.map (kyColM Fc ks m n M A (MO Fc ks m).one j)).allSome with _ | colss
    · exfalso
      refine allSome_ne_none _ (fun y hy h0 ↦ ?_) hC
      obtain ⟨Wb, hWb, rfl⟩ := List.mem_map.mp hy
      obtain ⟨p, -, hpw⟩ := List.mem_map.mp (mem_of_allSome hW hWb)
      obtain ⟨hWb0, hWbd, -⟩ := witW_spec (kyFA Fc m M A) n hn0 _ _ _ _ _ hΓ hpw
      have := T.kyColM_isSome m M n hn1 hm htrim Wb hWb0
        (natDegree_lt_of_witW hWb0 fun i a h ↦ (hWbd i a h).1) A hP0sq hP0deg (MO Fc ks m).one j
      rw [h0] at this; exact absurd this (by simp)
    · simp only [hW, hC, Option.isSome_some]

end Solve

set_option maxHeartbeats 8000000 in
open Classical in
/-- **`kyDecideL` answers** for every large bound, at suitable residues (accepted data), unless a
component is certified non-torsion while the orders over `t = 0` cannot be killed: either some
`ℓ`-th root (`ℓ ∣ n` prime) of `A(0)` exists while no `n`-th root does, or some point `(0, ζᵏ)` of
the twist is certified non-torsion (the Mordell–Weil case). -/
theorem kyDecideL_decides (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (n j : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime n (degG (MO Fc ks m) A))
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (hn1 : 1 < n) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n) (hr0 : cs.length ≠ 0)
    (hok : kxOK Fc ks m A B kt l cs = true)
    (hF : kyConst Fc ks m n j g A B kt l cs = true →
      kyFieldOK Fc ks m n j g A B kt l cs M zN gs = true) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd →
      (kyDecideL Fc ks lv m n j g M zN gs A B kt l cs (primesBelow Bd) Bd rs).isSome ∨
      ((((List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length)).map
          (kyTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n) (primesBelow Bd) Bd
            rs)).any (· == some none) = true ∧
        ((krZ Fc ks lv m n A = none ∧ ∃ ℓ, ℓ.Prime ∧ ℓ ∣ n ∧ (krZ Fc ks lv m ℓ A).isSome) ∨
          ∃ z, krZ Fc ks lv m n A = some z ∧ ∃ k < n,
            kyZeroQ Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
              (primesBelow Bd) Bd rs k = some none)) := by
  have hn0 : 0 < n := by omega
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hTm : T.Tr m := hTr.of_succ
  have hsq := GPoly.squarefreeCheck_sound (T.MP m hTm) hsqc
  have hdeg1 : (GPoly.toPoly (T.MP m hTm) A).natDegree = degG (MO Fc ks m) A :=
    (degG_eq (T.MP m hTm) A).symm
  have hdegA : 0 < (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hdegpos
  have hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m hTm) A).natDegree := by rw [hdeg1]; exact hcop
  have hok' := T.kxOK_spec m hTm A B kt l cs hok
  have ha0 : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero) = false := by
    cases h : (MO Fc ks m).isZero (A.getD 0 (MO Fc ks m).zero)
    · rfl
    · exact absurd (((T.MP m hTm).isZero_iff _).mp h) hok'.1
  have hD0 : ∀ q < cs.length, (T.MP m hTm).sem (kxD Fc ks m g cs q) ≠ 0 :=
    fun q hq ↦ T.kxD_ne m MS.hyp hk cs q (hok'.2 q hq).1
  have hacc : (!(decide (1 < n) && decide (0 < j) && decide (j < n) &&
      decide (Nat.Coprime j n))) = false := by
    simp only [decide_eq_true hn1, decide_eq_true hj0, decide_eq_true hjn, decide_eq_true hjc]
    rfl
  by_cases hcst : kyConst Fc ks m n j g A B kt l cs = true
  swap
  · refine ⟨fun _ ↦ 0, 0, fun _ _ ↦ Or.inl ?_⟩
    unfold kyDecideL kyDecideC
    dsimp only
    rw [if_neg (by rw [hacc]; decide), if_neg hr0, if_neg (by simp [hok]),
      if_pos (by simpa using hcst)]
    rfl
  have hFt := hF hcst
  obtain ⟨htrim, hlen, -, -, -, -⟩ := kyFieldOK_spec hFt
  obtain ⟨hζ, hvK, hinjK⟩ := T.ky_ptsM m hTm M n j hn0 hjc g A B kt l cs zN gs hok hcst hFt hD0
  obtain ⟨hd, hlc, hsqK, hcop2, -, -⟩ := T.kyFA_facts m hTm M A A 1 one_ne_zero
    (by rw [map_one, one_mul]; exact T.toPoly_trC_map m hTm A) hsq n hcopA hdegA
  obtain ⟨D, hD, mZ, hmZ, hsepM, hdegM⟩ := M_clear Fc m M htrim hlen
  set comps := (List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length) with hcomps
  -- the twist, for an `n`-th root `z` of `A(0)`
  have hPsi : ∀ z, krZ Fc ks lv m n A = some z →
      kyKap Fc ks m n A z ≠ 0 ∧
      let fK := kyFA Fc m M (krAh Fc ks m n A z (kyKap Fc ks m n A z))
      let P0 := (toPoly ((krAh Fc ks m n A z (kyKap Fc ks m n A z)).map (trC Fc m))).map
        (eM Fc m M)
      0 < fK.length - 1 ∧ fK.getD (fK.length - 1) 0 ≠ 0 ∧ Squarefree (toPoly fK) ∧
        Nat.Coprime n (fK.length - 1) ∧ Squarefree P0 ∧ 0 < P0.natDegree ∧
        (toPoly fK).eval 0 = 1 := by
    intro z hz
    obtain ⟨-, -, hκ0⟩ := T.kr_z_facts hmon hdeg m n hn0 hn hc A ha0 z hz
    obtain ⟨hz0, hzκ⟩ := T.kr_zsem hmon hdeg m n hn0 hn hc hTm A ha0 z hz
    exact ⟨hκ0, T.kyPsi_facts m hTm M n A hsq hcopA hdegA z _ hκ0 hz0 hzκ⟩
  have hζk : ∀ k : ℕ, ofQ Fc m M zN ^ k ≠ 0 := fun k ↦ pow_ne_zero _ (hζ.ne_zero hn0.ne')
  have hζn : ∀ k : ℕ, (ofQ Fc m M zN ^ k) ^ n = 1 := fun k ↦ by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  -- the queries
  set Q : (ℕ ⊕ Option ℕ) → (ℕ → ℕ) → Prop := fun o rs ↦ match o with
    | Sum.inl f => ∃ B0, ∀ Bb, B0 ≤ Bb →
        (kyTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n) (primesBelow Bb) Bb
          rs f).isSome
    | Sum.inr none => ∀ z, krZ Fc ks lv m n A = some z → ∃ B0, ∀ Bb, B0 ≤ Bb →
        (kyTorsPsiC Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
          (primesBelow Bb) Bb rs).isSome
    | Sum.inr (some k) => ∀ z, krZ Fc ks lv m n A = some z → ∃ B0, ∀ Bb, B0 ≤ Bb →
        (kyZeroQ Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
          (primesBelow Bb) Bb rs k).isSome with hQdef
  obtain ⟨rs, hrs⟩ := exists_rs_many Fc m
    (comps.map Sum.inl ++ (Sum.inr none :: (List.range n).map (Sum.inr ∘ some))) Q
    (fun o _ ↦ by
      rcases o with f | _ | k
      · exact kfm_query_els Fc m M n (by omega) _ hζ D hD mZ hmZ hsepM hdegM hd hlc hsqK hcop2
          _ _ (kyMult n j M zN gs cs.length f) hvK hinjK
      · rcases hz : krZ Fc ks lv m n A with _ | z
        · exact ⟨[], fun rs _ _ z' hz' ↦ absurd (hz.symm.trans hz') (by simp)⟩
        · obtain ⟨-, hd', hlc', hsq', hcop', -, -, hf0⟩ := hPsi z hz
          obtain ⟨Els, hEls⟩ := kfm_query_els Fc m M n (by omega) _ hζ D hD mZ hmZ hsepM hdegM
            hd' hlc' hsq' hcop' (fun _ : Fin n ↦ (0 : NFM Fc m M))
            (fun k ↦ ofQ Fc m M zN ^ (k : ℕ)) (ramMult n)
            (fun k ↦ ⟨hζk k, by rw [hζn, hf0]⟩)
            (fun k k' h ↦ Fin.ext (hζ.pow_inj k.2 k'.2 (congrArg Prod.snd h)))
          refine ⟨Els, fun rs h0 hE z' hz' ↦ ?_⟩
          obtain rfl := Option.some.inj (hz.symm.trans hz')
          exact hEls rs h0 hE
      · rcases hz : krZ Fc ks lv m n A with _ | z
        · exact ⟨[], fun rs _ _ z' hz' ↦ absurd (hz.symm.trans hz') (by simp)⟩
        · obtain ⟨-, hd', hlc', hsq', hcop', -, -, hf0⟩ := hPsi z hz
          obtain ⟨Els, hEls⟩ := kfm_query_els Fc m M n (by omega) _ hζ D hD mZ hmZ hsepM hdegM
            hd' hlc' hsq' hcop' ![(0 : NFM Fc m M)] ![ofQ Fc m M zN ^ k] ![1]
            (fun i ↦ by fin_cases i; exact ⟨hζk k, by simp only [Matrix.cons_val_fin_one]; rw [hζn, hf0]⟩)
            (fun a b _ ↦ Subsingleton.elim a b)
          refine ⟨Els, fun rs h0 hE z' hz' ↦ ?_⟩
          obtain rfl := Option.some.inj (hz.symm.trans hz')
          exact hEls rs h0 hE)
  -- uniform bounds
  obtain ⟨B1, hB1⟩ := eventually_list comps (fun f Bb ↦
    (kyTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n) (primesBelow Bb) Bb
      rs f).isSome) fun f hf ↦ hrs (Sum.inl f) (by simp [hf])
  obtain ⟨B2, hB2⟩ : ∃ B2, ∀ Bb, B2 ≤ Bb → ∀ z, krZ Fc ks lv m n A = some z →
      (kyTorsPsiC Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
        (primesBelow Bb) Bb rs).isSome := by
    rcases hz : krZ Fc ks lv m n A with _ | z
    · exact ⟨0, fun _ _ z' hz' ↦ absurd hz' (by simp)⟩
    · obtain ⟨B2, h2⟩ := hrs (Sum.inr none) (by simp) z hz
      exact ⟨B2, fun Bb hBb z' hz' ↦ by obtain rfl := Option.some.inj hz'; exact h2 Bb hBb⟩
  obtain ⟨B3, hB3⟩ : ∃ B3, ∀ Bb, B3 ≤ Bb → ∀ z, krZ Fc ks lv m n A = some z → ∀ k < n,
      (kyZeroQ Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
        (primesBelow Bb) Bb rs k).isSome := by
    rcases hz : krZ Fc ks lv m n A with _ | z
    · exact ⟨0, fun _ _ z' hz' ↦ absurd hz' (by simp)⟩
    · obtain ⟨B3, h3⟩ := eventually_list (List.range n) (fun k Bb ↦
        (kyZeroQ Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
          (primesBelow Bb) Bb rs k).isSome)
        fun k hk ↦ hrs (Sum.inr (some k)) (by simp [List.mem_range.mp hk]) z hz
      exact ⟨B3, fun Bb hBb z' hz' k hk ↦ by
        obtain rfl := Option.some.inj hz'; exact h3 Bb hBb k (List.mem_range.mpr hk)⟩
  refine ⟨rs, max B1 (max B2 B3), fun Bd hBd ↦ ?_⟩
  have hB1' := hB1 Bd (le_of_max_le_left hBd)
  have hB2' := hB2 Bd (le_of_max_le_left (le_of_max_le_right hBd))
  have hB3' := hB3 Bd (le_of_max_le_right (le_of_max_le_right hBd))
  set tors := comps.map (kyTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n)
    (primesBelow Bd) Bd rs) with htorsdef
  have hnone : ¬ tors.any (· == none) = true := by
    intro h
    obtain ⟨x, hx, hx0⟩ := List.any_eq_true.mp h
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
    have := hB1' f hf
    simp only [beq_iff_eq] at hx0
    rw [hx0] at this; exact absurd this (by simp)
  have hallT : ¬ tors.any (· == some none) = true → ∀ f ∈ comps, ∃ N,
      kyTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n) (primesBelow Bd) Bd rs f =
        some (some N) := by
    intro hsn f hf
    rcases h : kyTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n) (primesBelow Bd)
      Bd rs f with _ | _ | N
    · have := hB1' f hf; rw [h] at this; exact absurd this (by simp)
    · exfalso; apply hsn
      exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨_, hf, h⟩, by simp⟩
    · exact ⟨N, rfl⟩
  have hsolve := fun extra hsn ↦ T.kySolveC_isSome (lv := lv) m hTm M n j hn1 hjc g htrim zN gs A
    B kt l cs hok hcst hFt hD0 hsq hcopA hdegA rs Bd extra (hallT hsn)
  -- the zero queries
  have hzero : ∀ z, krZ Fc ks lv m n A = some z →
      ¬ kyZeroTorsC Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
        (primesBelow Bd) Bd rs = true →
      ∃ k < n, kyZeroQ Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
        (primesBelow Bd) Bd rs k = some none := by
    intro z hz hzt
    by_contra hcon
    push Not at hcon
    apply hzt
    refine List.all_eq_true.mpr fun k hk ↦ ?_
    have hk' := List.mem_range.mp hk
    have hs := hB3' z hz k hk'
    rcases hq : kyZeroQ Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
      (primesBelow Bd) Bd rs k with _ | _ | N
    · rw [hq] at hs; exact absurd hs (by simp)
    · exact absurd hq (hcon k hk')
    · change (match kyZeroQ Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
        (primesBelow Bd) Bd rs k with
        | some (some _) => true
        | _ => false) = true
      rw [hq]
  unfold kyDecideL kyDecideC
  dsimp only
  rw [if_neg (by rw [hacc]; decide), if_neg hr0, if_neg (by simp [hok]), if_neg (by simp [hcst]),
    if_neg (by simp [hFt])]
  rw [← hcomps, ← htorsdef, if_neg hnone]
  rcases hz : krZ Fc ks lv m n A with _ | z
  · by_cases hsn : tors.any (· == some none) = true
    · by_cases hpr : (List.range (n + 1)).all (fun ℓ ↦ !(decide (Nat.Prime ℓ ∧ ℓ ∣ n)) ||
          (krZ Fc ks lv m ℓ A).isNone) = true
      · left; rw [if_neg (by simp [hsn]), if_pos hpr]; rfl
      · right
        refine ⟨hsn, Or.inl ⟨rfl, ?_⟩⟩
        by_contra hcon
        push Not at hcon
        apply hpr
        refine List.all_eq_true.mpr fun ℓ _ ↦ ?_
        by_cases hℓ : Nat.Prime ℓ ∧ ℓ ∣ n
        · have := hcon ℓ hℓ.1 hℓ.2
          simp only [Bool.not_eq_true, Option.isSome_eq_false_iff] at this
          simp [this]
        · simp [hℓ]
    · left; rw [if_pos (by simp [hsn])]; exact hsolve [] hsn
  · obtain ⟨hκ0, -, -, -, -, hP0sq, hP0deg, hf0⟩ := hPsi z hz
    have hkap : (ratValC Fc ks m ((MO Fc ks m).mul (powC (MO Fc ks m) z n)
        (A.getD 0 (MO Fc ks m).zero))).getD 0 = kyKap Fc ks m n A z := rfl
    dsimp only
    rw [hkap, if_neg hκ0]
    have hPsiq : (kyTorsPsiC Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
        (primesBelow Bd) Bd rs).isSome := hB2' z hz
    rcases ht : kyTorsPsiC Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
      (primesBelow Bd) Bd rs with _ | _ | N0
    · rw [ht] at hPsiq; exact absurd hPsiq (by simp)
    · dsimp only
      by_cases hsn : tors.any (· == some none) = true
      · by_cases hzt : kyZeroTorsC Fc ks m n M A zN z (kyKap Fc ks m n A z)
            (fun fK ↦ localCert fK n) (primesBelow Bd) Bd rs = true
        · left; rw [if_neg (by simp [hsn]), if_pos hzt]; rfl
        · right; exact ⟨hsn, Or.inr ⟨z, rfl, hzero z hz hzt⟩⟩
      · left; rw [if_pos (by simp [hsn])]; exact hsolve [] hsn
    · dsimp only
      by_cases hsn : tors.any (· == some none) = true
      · by_cases hzt : kyZeroTorsC Fc ks m n M A zN z (kyKap Fc ks m n A z)
            (fun fK ↦ localCert fK n) (primesBelow Bd) Bd rs = true
        · left; rw [if_neg (by simp [hsn]), if_pos hzt]; rfl
        · right; exact ⟨hsn, Or.inr ⟨z, rfl, hzero z hz hzt⟩⟩
      · left
        rw [if_pos (by simp [hsn])]
        obtain ⟨-, hd', hlc', hsq', hcop', -, -, -⟩ := hPsi z hz
        have hspec := torsOracleC_spec (redAtNFM Fc m M rs)
          (localCert (kyFA Fc m M (krAh Fc ks m n A z (kyKap Fc ks m n A z))) n)
          (fun p _ R h ↦ redAtNFM_valid Fc m M rs p R h) (primesBelow Bd) Bd hsq' hcop'
        have hv : ∀ k : Fin n, ofQ Fc m M zN ^ (k : ℕ) ≠ 0 ∧
            (ofQ Fc m M zN ^ (k : ℕ)) ^ n = (toPoly (kyFA Fc m M (krAh Fc ks m n A z
              (kyKap Fc ks m n A z)))).eval ((fun _ : Fin n ↦ (0 : NFM Fc m M)) k) :=
          fun k ↦ ⟨hζk k, by rw [hζn, hf0]⟩
        have hinj : Function.Injective fun k : Fin n ↦
            ((fun _ : Fin n ↦ (0 : NFM Fc m M)) k, ofQ Fc m M zN ^ (k : ℕ)) :=
          fun k k' h ↦ Fin.ext (hζ.pow_inj k.2 k'.2 (congrArg Prod.snd h))
        have hP := ((hspec n _ _ (ramMult n) hv hinj).1 N0 ht).2
        have hΓ : ∀ k : Fin n, ((n : ℕ) : NFM Fc m M) * (ofQ Fc m M zN ^ (k : ℕ)) ^ (n - 1) ≠ 0 ∧
            (ofQ Fc m M zN ^ (k : ℕ)) ^ n = (toPoly (kyFA Fc m M (krAh Fc ks m n A z
              (kyKap Fc ks m n A z)))).eval ((fun _ : Fin n ↦ (0 : NFM Fc m M)) k) :=
          fun k ↦ ⟨mul_ne_zero (by exact_mod_cast hn0.ne') (pow_ne_zero _ (hv k).1), (hv k).2⟩
        have hw := witW_ne_none _ n hn0 _ _ _ (ramMult n) N0 hΓ hP
        rcases hwit : kyWitPsi Fc ks m n M A zN z (kyKap Fc ks m n A z) N0 with _ | W0b
        · exact absurd hwit hw
        obtain ⟨hWb0, hWbd, -⟩ := witW_spec _ n hn0 _ _ _ (ramMult n) N0 hΓ hwit
        have hcol := T.kyColM_isSome m M n hn1 hTm htrim W0b hWb0
          (natDegree_lt_of_witW hWb0 fun i a h ↦ (hWbd i a h).1) _ hP0sq hP0deg z j
        obtain ⟨cols0, hcols0⟩ := Option.isSome_iff_exists.mp hcol
        dsimp only
        rw [hcols0]
        exact hsolve cols0 hsn

open Classical in
/-- **Radicals over an exponential level with poles are decided** (accepted data), outside the
Mordell–Weil case: at suitable residues, for every large bound, either `kyDecideL` answers
correctly, or some component is certified non-torsion while the orders over `t = 0` cannot be
killed. -/
theorem ky_decided (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {g : LC m} (hk : ks m = .exp g)
    (n j : ℕ) (M : CPoly ℚ) [Fact (Irreducible (toPoly (liftQ Fc m M)))]
    [Fact (Irreducible (toPoly (liftQ Fc (m + 1) M)))] (zN : CPoly ℚ) (gs : List (CPoly ℚ))
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO Fc ks m) A = true)
    (hdegpos : 0 < degG (MO Fc ks m) A) (hcop : Nat.Coprime n (degG (MO Fc ks m) A))
    (θ : L) (hθ : θ ^ n = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (hn1 : 1 < n) (hj0 : 0 < j) (hjn : j < n) (hjc : Nat.Coprime j n) (hr0 : cs.length ≠ 0)
    (hok : kxOK Fc ks m A B kt l cs = true)
    (hF : kyConst Fc ks m n j g A B kt l cs = true →
      kyFieldOK Fc ks m n j g A B kt l cs M zN gs = true) :
    ∃ rs : ℕ → ℕ, ∃ B0, ∀ Bd, B0 ≤ Bd →
      (∃ b, kyDecideL Fc ks lv m n j g M zN gs A B kt l cs (primesBelow Bd) Bd rs = some b ∧
        (HasElementaryIntegral (T.ev (m + 1) ((B, kxDen Fc ks m A kt l cs) : LC (m + 1)) * θ ^ j) ↔
          b = true)) ∨
      ((((List.range (M.length - 1)).filter (kyNZ n j M zN gs cs.length)).map
          (kyTorsC Fc ks m n j M g A B kt l cs zN gs (fun fK ↦ localCert fK n) (primesBelow Bd) Bd
            rs)).any (· == some none) = true ∧
        ((krZ Fc ks lv m n A = none ∧ ∃ ℓ, ℓ.Prime ∧ ℓ ∣ n ∧ (krZ Fc ks lv m ℓ A).isSome) ∨
          ∃ z, krZ Fc ks lv m n A = some z ∧ ∃ k < n,
            kyZeroQ Fc ks m n M A zN z (kyKap Fc ks m n A z) (fun fK ↦ localCert fK n)
              (primesBelow Bd) Bd rs k = some none)) := by
  obtain ⟨rs, B0, h⟩ := T.kyDecideL_decides hmon hdeg m hn hc hk n j M zN gs A hsqc hdegpos hcop
    B kt l cs hn1 hj0 hjn hjc hr0 hok hF
  refine ⟨rs, B0, fun Bd hBd ↦ ?_⟩
  rcases h Bd hBd with h1 | h1
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h1
    exact Or.inl ⟨b, hb, T.kyDecide_correct hmon hdeg m hn hc hk n j M zN gs A hsqc hdegpos hcop θ
      hθ hgen B kt l cs _ _ rs b hb⟩
  · exact Or.inr h1

end MTower

end Curves.MT
