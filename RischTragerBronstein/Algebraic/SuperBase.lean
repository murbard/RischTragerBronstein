import RischTragerBronstein.Algebraic.SuperDegree
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Base change of a superelliptic curve to an algebraically closed field

For `S : SuperData C L` and an algebraically closed `K ⊇ C`, `S.base K` is the same curve over
`K` (inside `AlgebraicClosure (RatFunc K)`), and `S.tau K : C⟮x⟯⟮y⟯ →+* K⟮x⟯⟮y⟯` is the natural
map. Every expansion of `S` factors through `tau` (`embXY_tau`, `embB_tau`, `embI_tau`), so
orders can be computed on the base change, where the roots of unity needed for the norm live.
-/

open Polynomial IntermediateField HahnSeries

namespace Differential

namespace SuperData

variable {C L : Type*} [Field C] [PerfectField C] [Field L] [Algebra C L]
variable (K : Type*) [Field K] [Algebra C K] [IsAlgClosed K]

variable (S : SuperData C L)

/-- The function field of the base change. -/
abbrev BaseL := AlgebraicClosure (RatFunc K)

lemma map_map_id (P : C[X]) : (P.map (algebraMap C K)).map (algebraMap K K) = P.map (algebraMap C K) := by
  rw [Algebra.algebraMap_self, Polynomial.map_id]

/-- The abscissa `x` of the base change. -/
noncomputable def baseX : BaseL K := algebraMap (RatFunc K) (BaseL K) RatFunc.X

lemma baseX_transcendental : Transcendental K (baseX K) :=
  (transcendental_algebraMap_iff (algebraMap (RatFunc K) (BaseL K)).injective).mpr
    RatFunc.transcendental_X

/-- The ordinate `y` of the base change. -/
noncomputable def baseY : BaseL K :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (aeval (baseX K) (S.p.map (algebraMap C K))) S.hn)

lemma baseY_pow : S.baseY K ^ S.n = aeval (baseX K) (S.p.map (algebraMap C K)) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (aeval (baseX K) (S.p.map (algebraMap C K)))
    S.hn)

/-- **The base change** of `S` to `K`. -/
noncomputable def base : SuperData K (BaseL K) where
  x := baseX K
  y := S.baseY K
  n := S.n
  p := S.p.map (algebraMap C K)
  htr := baseX_transcendental K
  hn := S.hn
  hsq := ((PerfectField.separable_iff_squarefree.mpr S.hsq).map).squarefree
  hp := by rw [natDegree_map_eq_of_injective (algebraMap C K).injective]; exact S.hp
  hy := S.baseY_pow K
  hnC := S.hnK K

@[simp] lemma base_n : (S.base K).n = S.n := rfl
@[simp] lemma base_p : (S.base K).p = S.p.map (algebraMap C K) := rfl
@[simp] lemma base_x : (S.base K).x = baseX K := rfl

/-- The map `C[x] → K⟮x⟯`. -/
noncomputable def tauPoly : C[X] →+* K⟮(S.base K).x⟯ :=
  letI := algebraAdjoinSimple (F := K) (S.base K).x
  (algebraMap K[X] K⟮(S.base K).x⟯).comp (Polynomial.mapRingHom (algebraMap C K))

lemma tauPoly_injective : Function.Injective (S.tauPoly K) := by
  letI := algebraAdjoinSimple (F := K) (S.base K).x
  haveI := isFractionRing_adjoin_simple (S.base K).x (S.base K).htr
  exact (IsFractionRing.injective K[X] K⟮(S.base K).x⟯).comp
    (Polynomial.map_injective _ (algebraMap C K).injective)

/-- The map `C⟮x⟯ → K⟮x⟯`. -/
noncomputable def tauX : C⟮S.x⟯ →+* K⟮(S.base K).x⟯ :=
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  IsFractionRing.lift (S.tauPoly_injective K)

lemma tauX_algebraMap (P : C[X]) :
    letI := algebraAdjoinSimple (F := C) S.x
    S.tauX K (algebraMap C[X] C⟮S.x⟯ P) = S.tauPoly K P := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  rw [tauX, IsFractionRing.lift_algebraMap]

lemma tau_root :
    (minpoly C⟮S.x⟯ S.y).eval₂ ((algebraMap K⟮(S.base K).x⟯ K⟮(S.base K).x⟯⟮(S.base K).y⟯).comp
      (S.tauX K)) (AdjoinSimple.gen K⟮(S.base K).x⟯ (S.base K).y) = 0 := by
  letI := algebraAdjoinSimple (F := C) S.x
  letI := algebraAdjoinSimple (F := K) (S.base K).x
  rw [S.minpoly_eq, eval₂_sub, eval₂_X_pow, eval₂_C, RingHom.comp_apply, S.tauX_algebraMap K]
  have hg : AdjoinSimple.gen K⟮(S.base K).x⟯ (S.base K).y ^ S.n =
      algebraMap K⟮(S.base K).x⟯ K⟮(S.base K).x⟯⟮(S.base K).y⟯
        (algebraMap K[X] K⟮(S.base K).x⟯ (S.base K).p) :=
    Subtype.ext (by
      simp only [SubmonoidClass.coe_pow, AdjoinSimple.coe_gen]
      exact (S.base K).hy.trans (algebraMap_adjoinSimple _ _).symm)
  rw [hg, sub_eq_zero]
  rfl

/-- **The base-change map** `C⟮x⟯⟮y⟯ → K⟮x⟯⟮y⟯`. -/
noncomputable def tau : C⟮S.x⟯⟮S.y⟯ →+* K⟮(S.base K).x⟯⟮(S.base K).y⟯ :=
  (AdjoinRoot.lift ((algebraMap K⟮(S.base K).x⟯ K⟮(S.base K).x⟯⟮(S.base K).y⟯).comp (S.tauX K))
    _ (S.tau_root K)).comp
    (adjoinRootEquivAdjoin C⟮S.x⟯ S.isIntegral).symm.toRingEquiv.toRingHom

lemma tau_gen : S.tau K (AdjoinSimple.gen C⟮S.x⟯ S.y) =
    AdjoinSimple.gen K⟮(S.base K).x⟯ (S.base K).y := by
  simp only [tau, RingHom.comp_apply, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, AlgEquiv.coe_ringEquiv, adjoinRootEquivAdjoin_symm_apply_gen,
    AdjoinRoot.lift_root]

lemma tau_algebraMap (a : C⟮S.x⟯) :
    S.tau K (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a) =
      algebraMap K⟮(S.base K).x⟯ K⟮(S.base K).x⟯⟮(S.base K).y⟯ (S.tauX K a) := by
  simp only [tau, RingHom.comp_apply, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  exact AdjoinRoot.lift_of _

/-! ### Expansions factor through `tau` -/

/-- Graded substitutions factor. -/
lemma embXG_tau (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (g' : K[X] →+* LaurentSeries K) (hg' : Function.Injective g')
    (hgg : ∀ P : C[X], g' (P.map (algebraMap C K)) = g P) :
    ((S.base K).embXG g' hg').comp (S.tauX K) = S.embXG g hg := by
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  refine IsLocalization.ringHom_ext (nonZeroDivisors C[X]) (RingHom.ext fun P ↦ ?_)
  simp only [RingHom.comp_apply]
  rw [S.tauX_algebraMap K, S.embXG_algebraMap, tauPoly, RingHom.comp_apply, coe_mapRingHom,
    (S.base K).embXG_algebraMap, hgg]

lemma embG_tau (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g)
    (g' : K[X] →+* LaurentSeries K) (hg' : Function.Injective g')
    (hgg : ∀ P : C[X], g' (P.map (algebraMap C K)) = g P) (Y : LaurentSeries K)
    (hY : Y ^ S.n = g S.p) (hY' : Y ^ (S.base K).n = g' (S.base K).p) :
    ((S.base K).embG g' hg' Y hY').comp (S.tau K) = S.embG g hg Y hY := by
  refine S.ringHom_ext_XY _ _ (fun a ↦ ?_) ?_
  · rw [RingHom.comp_apply, S.tau_algebraMap K, (S.base K).embG_algebraMap, S.embG_algebraMap,
      ← RingHom.comp_apply, S.embXG_tau K g hg g' hg' hgg]
  · rw [RingHom.comp_apply, S.tau_gen K, (S.base K).embG_gen, S.embG_gen]

lemma shiftHom_map (α : K) (P : C[X]) :
    shiftHom (C := K) α (P.map (algebraMap C K)) = shiftHom α P := by
  rw [shiftHom_apply, shiftHom_apply, map_map_id]

lemma branchSub_map (m : ℕ) (e : K) (P : C[X]) :
    branchSub (C := K) m e (P.map (algebraMap C K)) = branchSub m e P := by
  rw [branchSub_apply, branchSub_apply, map_map_id]

lemma infSub_map (m : ℕ) (P : C[X]) :
    infSub (C := K) (K := K) m (P.map (algebraMap C K)) = infSub m P := by
  simp only [infSub, coe_eval₂RingHom, eval₂_map]
  rfl

lemma embXY_eq_embG (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    S.embXY α β hβ hβp = S.embG (shiftHom α) (shiftHom_injective α)
      (ofPowerSeries ℤ K (branchY S.n S.hn (S.hnK K) S.p α β hβ hβp))
      (by rw [← map_pow, branchY_pow]; rfl) := rfl

/-- **Non-branch expansions factor through `tau`.** -/
theorem embXY_tau (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    ((S.base K).embXY α β hβ (by simp [hβp])).comp (S.tau K) = S.embXY α β hβ hβp := by
  have hB : branchY (S.base K).n (S.base K).hn ((S.base K).hnK K) (S.base K).p α β hβ (by simp [hβp]) =
      branchY S.n S.hn (S.hnK K) S.p α β hβ hβp := by
    refine LaurentSeries.pow_eq_pow_unique S.n S.hn (S.hnK K) ?_ ?_ ?_
    · have h1 := branchY_pow (S.base K).n (S.base K).hn ((S.base K).hnK K) (S.base K).p α β hβ (by simp [hβp])
      have h2 := branchY_pow S.n S.hn (S.hnK K) S.p α β hβ hβp
      refine h1.trans ?_
      rw [h2]
      simp only [pShift, base_p, map_map_id]
    · rw [branchY_const, branchY_const]
    · rw [branchY_const]; exact hβ
  rw [embXY_eq_embG, embXY_eq_embG]
  have := S.embG_tau K (shiftHom α) (shiftHom_injective α) (shiftHom α) (shiftHom_injective α)
    (shiftHom_map K α) (ofPowerSeries ℤ K (branchY S.n S.hn (S.hnK K) S.p α β hβ hβp))
    (by rw [← map_pow, branchY_pow]; rfl) (by
      rw [← hB, ← map_pow, branchY_pow]; rfl)
  convert this using 3
  exact congrArg _ hB

lemma base_eval (α : K) : ((S.base K).p.map (algebraMap K K)).eval α =
    (S.p.map (algebraMap C K)).eval α := by
  rw [base_p, map_map_id]

lemma base_deriv_eval (e : K) :
    (Polynomial.derivative ((S.base K).p.map (algebraMap K K))).eval e =
      (Polynomial.derivative (S.p.map (algebraMap C K))).eval e := by
  rw [base_p, map_map_id]

/-- **Branch expansions factor through `tau`.** -/
theorem embB_tau (e γ : K) (he : (S.p.map (algebraMap C K)).eval e = 0) (hγ : γ ≠ 0)
    (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e) :
    ((S.base K).embB e γ (by rw [base_eval]; exact he) hγ (by rw [base_deriv_eval]; exact hγp)).comp
      (S.tau K) = S.embB e γ he hγ hγp := by
  have hU : (S.base K).branchU e γ hγ (by rw [base_deriv_eval]; exact hγp) = S.branchU e γ hγ hγp := by
    refine LaurentSeries.pow_eq_pow_unique S.n S.hn (S.hnK K) ?_ ?_ ?_
    · refine ((S.base K).branchU_spec e γ hγ (by rw [base_deriv_eval]; exact hγp)).1.trans ?_
      rw [(S.branchU_spec e γ hγ hγp).1]
      simp only [pBranch, base_p, map_map_id, base_n]
    · rw [((S.base K).branchU_spec e γ hγ _).2, (S.branchU_spec e γ hγ hγp).2]
    · rw [(S.branchU_spec e γ hγ hγp).2]; exact hγ
  have hY : (S.base K).branchYe e γ hγ (by rw [base_deriv_eval]; exact hγp) =
      S.branchYe e γ hγ hγp := by
    rw [branchYe, branchYe, hU]
  unfold embB
  have := S.embG_tau K (branchSub S.n e) (branchSub_injective S.n S.hn e) (branchSub S.n e)
    (branchSub_injective S.n S.hn e) (branchSub_map K S.n e) (S.branchYe e γ hγ hγp)
    (S.branchYe_pow e γ he hγ hγp) (by
      rw [← hY]; exact (S.base K).branchYe_pow e γ (by rw [base_eval]; exact he) hγ _)
  convert this using 3
  all_goals first | rfl | exact hY

lemma base_leadingCoeff : (S.base K).p.leadingCoeff = algebraMap C K S.p.leadingCoeff := by
  rw [base_p, leadingCoeff_map_of_injective (algebraMap C K).injective]

lemma base_hlp (lam : K) (hlp : lam ^ S.n = algebraMap C K S.p.leadingCoeff) :
    lam ^ (S.base K).n = algebraMap K K (S.base K).p.leadingCoeff := by
  rw [base_leadingCoeff, Algebra.algebraMap_self, RingHom.id_apply]; exact hlp

/-- **Expansions at infinity factor through `tau`.** -/
theorem embI_tau (lam : K) (hlam : lam ≠ 0) (hlp : lam ^ S.n = algebraMap C K S.p.leadingCoeff) :
    ((S.base K).embI lam hlam (S.base_hlp K lam hlp)).comp (S.tau K) = S.embI lam hlam hlp := by
  have hrev : Polynomial.map (algebraMap K K) (S.base K).p.reverse =
      S.p.reverse.map (algebraMap C K) := by
    rw [Algebra.algebraMap_self, Polynomial.map_id, base_p, reverse, reverse,
      natDegree_map_eq_of_injective (algebraMap C K).injective, reflect_map]
  have hW : (S.base K).infW lam hlam (S.base_hlp K lam hlp) = S.infW lam hlam hlp := by
    refine LaurentSeries.pow_eq_pow_unique S.n S.hn (S.hnK K) ?_ ?_ ?_
    · refine ((S.base K).infW_spec lam hlam _).1.trans ?_
      rw [(S.infW_spec lam hlam hlp).1, hrev]
      rfl
    · rw [((S.base K).infW_spec lam hlam _).2, (S.infW_spec lam hlam hlp).2]
    · rw [(S.infW_spec lam hlam hlp).2]; exact hlam
  have hdeg : (S.base K).p.natDegree = S.p.natDegree := by
    rw [base_p, natDegree_map_eq_of_injective (algebraMap C K).injective]
  have hY : (S.base K).infY lam hlam (S.base_hlp K lam hlp) = S.infY lam hlam hlp := by
    rw [infY, infY, hW, hdeg]
  unfold embI
  have := S.embG_tau K (infSub S.n) (infSub_injective S.n S.hn) (infSub S.n)
    (infSub_injective S.n S.hn) (infSub_map K S.n) (S.infY lam hlam hlp)
    (S.infY_pow lam hlam hlp) (by rw [← hY]; exact (S.base K).infY_pow lam hlam _)
  convert this using 3
  all_goals first | rfl | exact hY

/-! ### Orders on the base change -/

lemma ordAt_tau (w : C⟮S.x⟯⟮S.y⟯) (α β : K) (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    (S.base K).ordAt K (S.tau K w) α β = S.ordAt K w α β := by
  by_cases hβ : β = 0
  · subst hβ
    have he : (S.p.map (algebraMap C K)).eval α = 0 := by rw [← hv, zero_pow S.hn.ne']
    obtain ⟨γ, hγ, hγp⟩ := S.exists_gamma α he
    rw [S.ordAt_br w α γ he hγ hγp, (S.base K).ordAt_br _ α γ (by rw [base_eval]; exact he) hγ
      (by rw [base_deriv_eval]; exact hγp), ← RingHom.comp_apply, embB_tau]
  · rw [S.ordAt_nb w α β hβ hv, (S.base K).ordAt_nb _ α β hβ (by rw [base_eval]; exact hv),
      ← RingHom.comp_apply, embXY_tau]

lemma ordInf_tau (hcop : Nat.Coprime S.n S.p.natDegree) (w : C⟮S.x⟯⟮S.y⟯) :
    (S.base K).ordInf K (S.tau K w) = S.ordInf K w := by
  obtain ⟨lam, hlam, hlp⟩ := S.exists_lam (K := K)
  have hcop' : Nat.Coprime (S.base K).n (S.base K).p.natDegree := by
    rw [base_n, base_p, natDegree_map_eq_of_injective (algebraMap C K).injective]; exact hcop
  rw [S.ordInf_eq hcop w lam hlam hlp, (S.base K).ordInf_eq hcop' _ lam hlam (S.base_hlp K lam hlp),
    ← RingHom.comp_apply, embI_tau]

lemma tau_ne_zero {w : C⟮S.x⟯⟮S.y⟯} (hw : w ≠ 0) : S.tau K w ≠ 0 :=
  (map_ne_zero_iff _ (RingHom.injective _)).mpr hw

lemma isIntegralS_tau {w : C⟮S.x⟯⟮S.y⟯} (hint : S.IsIntegralS K w) :
    (S.base K).IsIntegralS K (S.tau K w) := fun α β hv ↦ by
  have hv' : β ^ S.n = (S.p.map (algebraMap C K)).eval α := by rw [← base_eval]; exact hv
  rw [S.ordAt_tau K w α β hv']
  exact hint α β hv'

lemma exists_primitive (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) : ∃ ζ : K, IsPrimitiveRoot ζ n := by
  have : NeZero (n : K) := ⟨hnK⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (cyclotomic n K)
    (degree_cyclotomic_pos n K hn).ne'
  exact ⟨z, (isRoot_cyclotomic_iff).mp hz⟩

/-- **The degree theorem for `S`** (no roots of unity needed in `C`). -/
theorem degree_le' (hcop : Nat.Coprime S.n S.p.natDegree) (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0)
    (hint : S.IsIntegralS K w) (T : Finset (K × K))
    (hT : ∀ Q ∈ T, Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1) :
    ∑ Q ∈ T, S.ordAt K w Q.1 Q.2 ≤ -S.ordInf K w := by
  obtain ⟨ζ, hζ⟩ := exists_primitive K S.n S.hn (S.hnK K)
  have hcop' : Nat.Coprime (S.base K).n (S.base K).p.natDegree := by
    rw [base_n, base_p, natDegree_map_eq_of_injective (algebraMap C K).injective]; exact hcop
  have h := (S.base K).degree_le hcop' ζ hζ (S.tau K w) (S.tau_ne_zero K hw)
    (S.isIntegralS_tau K hint) T (fun Q hQ ↦ by rw [base_eval]; exact hT Q hQ)
  rw [S.ordInf_tau K hcop, Finset.sum_congr rfl fun Q hQ ↦ S.ordAt_tau K w Q.1 Q.2 (hT Q hQ)] at h
  exact h

theorem degree_eq' (hcop : Nat.Coprime S.n S.p.natDegree) (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0)
    (hint : S.IsIntegralS K w) (T : Finset (K × K))
    (hT : ∀ Q ∈ T, Q.2 ^ S.n = (S.p.map (algebraMap C K)).eval Q.1)
    (hsupp : ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α → (α, β) ∉ T →
      S.ordAt K w α β = 0) :
    ∑ Q ∈ T, S.ordAt K w Q.1 Q.2 = -S.ordInf K w := by
  obtain ⟨ζ, hζ⟩ := exists_primitive K S.n S.hn (S.hnK K)
  have hcop' : Nat.Coprime (S.base K).n (S.base K).p.natDegree := by
    rw [base_n, base_p, natDegree_map_eq_of_injective (algebraMap C K).injective]; exact hcop
  have h := (S.base K).degree_eq hcop' ζ hζ (S.tau K w) (S.tau_ne_zero K hw)
    (S.isIntegralS_tau K hint) T (fun Q hQ ↦ by rw [base_eval]; exact hT Q hQ) (fun α β hv hn ↦ by
      have hv' : β ^ S.n = (S.p.map (algebraMap C K)).eval α := by rw [← base_eval]; exact hv
      rw [S.ordAt_tau K w α β hv']; exact hsupp α β hv' hn)
  rw [S.ordInf_tau K hcop, Finset.sum_congr rfl fun Q hQ ↦ S.ordAt_tau K w Q.1 Q.2 (hT Q hQ)] at h
  exact h

lemma tau_sum (a : Fin S.n → C⟮S.x⟯) :
    S.tau K (∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ)) =
      ∑ i : Fin (S.base K).n, algebraMap K⟮(S.base K).x⟯ K⟮(S.base K).x⟯⟮(S.base K).y⟯
        (S.tauX K (a i)) * AdjoinSimple.gen K⟮(S.base K).x⟯ (S.base K).y ^ (i : ℕ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_pow, S.tau_algebraMap K, S.tau_gen K]

lemma embX_tauX (α : K) (a : C⟮S.x⟯) :
    embX (S.base K).x (S.base K).htr α (S.tauX K a) = embX S.x S.htr α a := by
  have := S.embXG_tau K (shiftHom α) (shiftHom_injective α) (shiftHom α) (shiftHom_injective α)
    (shiftHom_map K α)
  exact congrArg (fun φ : C⟮S.x⟯ →+* LaurentSeries K ↦ φ a) this

lemma orderTop_nonneg_of_ordAt {f : LaurentSeries K} (h : 0 ≤ f.order) : 0 ≤ f.orderTop := by
  by_cases hf : f = 0
  · rw [hf, HahnSeries.orderTop_zero]; exact le_top
  · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hf]; exact_mod_cast h

/-- **Integrality from regularity** for `S` itself (no roots of unity needed in `C`). -/
theorem integral_of_regular' (w : C⟮S.x⟯⟮S.y⟯) (hint : S.IsIntegralS K w) :
    ∃ a : Fin S.n → C⟮S.x⟯, w = ∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ) ∧ ∀ i, ∃ P : C[X], (a i : L) = aeval S.x P := by
  obtain ⟨ζ, hζ⟩ := exists_primitive K S.n S.hn (S.hnK K)
  obtain ⟨a, ha⟩ := S.power_repr w
  refine ⟨a, ha, fun i ↦ exists_poly_of_regular (K := K) S.x S.htr (a i) fun α hi ↦ ?_⟩
  have hτ := S.tau_sum K a
  rw [← ha] at hτ
  have hti : S.tauX K (a i) ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hi
  rw [← S.embX_tauX K α (a i)]
  by_cases hα : (S.p.map (algebraMap C K)).eval α = 0
  · obtain ⟨γ, hγ, hγp⟩ := S.exists_gamma α hα
    refine (S.base K).branch_regular α γ (by rw [base_eval]; exact hα) hγ
      (by rw [base_deriv_eval]; exact hγp) (fun k ↦ S.tauX K (a k)) ?_ i hti
    rw [← hτ, ← RingHom.comp_apply, embB_tau K S α γ hα hγ hγp]
    refine orderTop_nonneg_of_ordAt K ?_
    rw [← S.ordAt_br w α γ hα hγ hγp]
    exact hint α 0 (by rw [hα, zero_pow S.hn.ne'])
  · obtain ⟨β, hβ⟩ := S.exists_beta (K := K) α
    have hβ0 : β ≠ 0 := fun h0 ↦ hα (by rw [← hβ, h0, zero_pow S.hn.ne'])
    refine (S.base K).nonbranch_regular ζ hζ α β hβ0 (by rw [base_eval]; exact hβ)
      (fun k ↦ S.tauX K (a k)) (fun β' hβ' hβp' ↦ ?_) i hti
    have hβp'' : β' ^ S.n = (S.p.map (algebraMap C K)).eval α := by rw [← base_eval]; exact hβp'
    rw [← hτ, ← RingHom.comp_apply, embXY_tau K S α β' hβ' hβp'']
    refine orderTop_nonneg_of_ordAt K ?_
    rw [← S.ordAt_nb w α β' hβ' hβp'']
    exact hint α β' hβp''

end SuperData

end Differential
