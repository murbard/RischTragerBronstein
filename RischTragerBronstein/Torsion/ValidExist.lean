import RischTragerBronstein.Torsion.ValidBase
import RischTragerBronstein.Torsion.CertExistPt
import RischTragerBronstein.Algebraic.NFExists

/-!
# Valid branch data exist

**`exists_valid`**: for an integration problem over `ℚ` with valid shape (`shapeOK`), separable
at the finite fibres and at infinity (Bézout identities for `F` and for its inversion), there is a
certified number field `ℚ[γ]/(M)` and branch data `pts`, `inf` over it with
`(P0.baseChange _ _ pts inf).valid = true`.

The data: the roots `z` of `D · disc` in `ℚ̄`, Newton–Puiseux expansions there and at infinity
(`exists_branchCert`) at a precision above the orders of `R0` and `D` along the branches, and a
number field containing all the points and coefficients (`NFC.exists_nf`).
-/

open Polynomial

namespace Curves

open CPoly Sup NFC

section Inv

variable {F : Type*} [Field F] [DecidableEq F] {F' : Type*} [Field F'] [DecidableEq F']
  (φ : F →+* F') (P0 : CurveProb F) (pts : List (F' × BranchCert F')) (inf : BranchCert F')

lemma DA_baseChange : (P0.baseChange φ P0.k pts inf).DA = P0.DA := by
  simp only [CurveProb.DA, CurveProb.baseChange, List.length_map, getD_mapL, degT_map]

lemma degBC_baseChange : (P0.baseChange φ P0.k pts inf).degBC = P0.degBC := by
  simp only [CurveProb.degBC, CurveProb.baseChange, getD_mapL, degT_map]

lemma DWb_baseChange : (P0.baseChange φ P0.k pts inf).DWb = P0.DWb := by
  simp only [CurveProb.DWb, CurveProb.E, CurveProb.Binf, DA_baseChange, degBC_baseChange]
  simp only [CurveProb.baseChange, degT_map]

end Inv

lemma natTrailingDegree_map_inj {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : Function.Injective f) (p : R[X]) : (p.map f).natTrailingDegree = p.natTrailingDegree := by
  by_cases hp : p = 0
  · simp [hp]
  have hpm : p.map f ≠ 0 := (Polynomial.map_ne_zero_iff hf).mpr hp
  apply le_antisymm
  · refine natTrailingDegree_le_of_ne_zero ?_
    rw [coeff_map]
    exact (map_ne_zero_iff f hf).mpr (trailingCoeff_nonzero_iff_nonzero.mpr hp)
  · refine le_natTrailingDegree hpm fun m hm ↦ ?_
    rw [coeff_map, coeff_eq_zero_of_lt_natTrailingDegree hm, map_zero]

lemma comp_shift_ne_zero {K : Type*} [Field K] (p : K[X]) (hp : p ≠ 0) (a : K) {N : ℕ}
    (hN : 0 < N) : p.comp (Polynomial.C a + X ^ N) ≠ 0 := by
  rw [Ne, comp_eq_zero_iff]
  rintro (h | ⟨-, h⟩)
  · exact hp h
  · have := congrArg natDegree h
    rw [natDegree_C, natDegree_add_eq_right_of_natDegree_lt (by simp; omega), natDegree_X_pow] at this
    omega

section Orders

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] {F' : Type*} [Field F'] [DecidableEq F']
  [CharZero F'] {K : Type*} [Field K] (φ : F →+* F') (ψ : F' →+* K)

/-- The order of a polynomial along `a + Tᴺ`, computed after a further embedding. -/
lemma ordC_compC_map (R : CPoly F) (hR : toPoly R ≠ 0) (R' : CPoly F')
    (hR' : toPoly R' = (toPoly R).map φ) (a' : F') {N : ℕ} (hN : 0 < N) :
    ordC (compC R' (shiftC a' N)) =
        (((toPoly R).map (ψ.comp φ)).comp (Polynomial.C (ψ a') + X ^ N)).natTrailingDegree ∧
      ordC (compC R' (shiftC a' N)) < (compC R' (shiftC a' N)).length := by
  have hne : toPoly (compC R' (shiftC a' N)) ≠ 0 := by
    rw [toPoly_compC_shiftC, hR']
    exact comp_shift_ne_zero _ ((Polynomial.map_ne_zero_iff φ.injective).mpr hR) _ hN
  refine ⟨?_, ordC_lt_length _ hne⟩
  rw [ordC_eq_natTrailingDegree _ hne, toPoly_compC_shiftC, hR',
    ← natTrailingDegree_map_inj ψ ψ.injective, Polynomial.map_comp, Polynomial.map_map]
  simp

/-- `μ` and `μ_f` of the base-changed problem, read in `K`. -/
lemma mu_baseChange (P0 : CurveProb F) (hS : P0.shapeOK = true)
    (pts : List (F' × BranchCert F')) (inf : BranchCert F') (a' : F') {N : ℕ} (hN : 0 < N) :
    (P0.baseChange φ P0.k pts inf).muFin a' N =
        (((toPoly P0.R0).map (ψ.comp φ)).comp (Polynomial.C (ψ a') + X ^ N)).natTrailingDegree ∧
      (P0.baseChange φ P0.k pts inf).muFin a' N < ((P0.baseChange φ P0.k pts inf).QFin a' N).length ∧
      (P0.baseChange φ P0.k pts inf).mufFin a' N =
        (((toPoly P0.D).map (ψ.comp φ)).comp (Polynomial.C (ψ a') + X ^ N)).natTrailingDegree ∧
      (P0.baseChange φ P0.k pts inf).mufFin a' N < ((P0.baseChange φ P0.k pts inf).QfFin a' N).length := by
  have hS' := hS
  simp only [CurveProb.shapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true'] at hS'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, h9⟩, h10⟩, -⟩ := hS'
  have hR0 : toPoly P0.R0 ≠ 0 := fun h0 ↦ by
    rw [← trim_eq_nil_iff] at h0; rw [h0] at h9; simp at h9
  have hD0 : toPoly P0.D ≠ 0 := fun h0 ↦ by
    rw [← trim_eq_nil_iff] at h0; rw [h0] at h10; simp at h10
  obtain ⟨e1, l1⟩ := ordC_compC_map φ ψ P0.R0 hR0 _ (toPoly_R0_baseChange φ P0 hS pts inf) a' hN
  obtain ⟨e2, l2⟩ := ordC_compC_map φ ψ P0.D hD0 (P0.D.map φ) (toPoly_mapHom φ P0.D) a' hN
  exact ⟨e1, l1, e2, l2⟩

end Orders

section Exist

/-- The monic shape of `F` (without the coefficient bound). -/
lemma monic_of_shape {F : Type*} [Field F] (Fc : BPoly F) (n : ℕ) (hl : Fc.length = n + 1)
    (hlead : Fc.getD n [] = [1]) : (toB Fc).Monic ∧ (toB Fc).natDegree = n := by
  have hcn : (toB Fc).coeff n = 1 := by rw [coeff_toB, hlead]; simp
  have hdeg : (toB Fc).natDegree = n := by
    refine natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [hcn]; exact one_ne_zero)
    refine natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ ?_
    rw [coeff_toB, List.getD_eq_default _ _ (by have : n < i := (by exact_mod_cast hi); omega)]
    simp
  exact ⟨by rw [Monic, leadingCoeff, hdeg, hcn], hdeg⟩

/-- `exists_branchCert` for coefficient fields in `Type`. -/
lemma exists_branchCert0 {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (G : K[X][X]) (n : ℕ)
    (hmon : G.Monic) (hdeg : G.natDegree = n) (R : K[X]) (hR : R ≠ 0) (A B : K[X][X])
    (hAB : Polynomial.C R = A * G + B * derivative G) (a : K) :
    ∃ N prec₀ : ℕ, 0 < N ∧ ∀ prec, prec₀ ≤ prec → ∃ ys : List (CPoly K), ys.length = n ∧
      ∀ {F : Type} [Field F] [DecidableEq F] (ψ : F →+* K) (Fc : BPoly F) (a' : F)
        (ys' : List (CPoly F)), (toB Fc).map (mapRingHom ψ) = G → ψ a' = a →
        ys'.map (·.map ψ) = ys → certCheck Fc n a' ⟨N, ys', prec⟩ = true :=
  exists_branchCert G n hmon hdeg R hR A B hAB a

lemma bezout_map {K : Type} [Field K] (ι : ℚ →+* K) (W : ℚ[X][X]) (R : ℚ[X]) (A B : ℚ[X][X])
    (hAB : Polynomial.C R = A * W + B * derivative W) :
    Polynomial.C (R.map ι) = A.map (mapRingHom ι) * W.map (mapRingHom ι) +
      B.map (mapRingHom ι) * derivative (W.map (mapRingHom ι)) := by
  have := congrArg (Polynomial.map (mapRingHom ι)) hAB
  rwa [Polynomial.map_C, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
    ← Polynomial.derivative_map, coe_mapRingHom] at this

/-- Preimages of all the coefficients. -/
lemma map_pre {F K : Type*} [Semiring F] [Semiring K] (ψ : F →+* K) (pre : K → F) (S : Finset K)
    (hpre : ∀ x ∈ S, ψ (pre x) = x) (ys : List (CPoly K)) (hys : ∀ x ∈ ys.flatten, x ∈ S) :
    (ys.map (·.map pre)).map (·.map ψ) = ys := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id ys]
  refine List.map_congr_left fun l hl ↦ ?_
  simp only [Function.comp_apply, List.map_map, id]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun x hx ↦ hpre x (hys x (List.mem_flatten.mpr ⟨l, hl, hx⟩))

/-- **Valid branch data exist** over some certified number field. -/
theorem exists_valid (P0 : CurveProb ℚ) (hS : P0.shapeOK = true)
    (hsep : ∃ (R : ℚ[X]) (A B : ℚ[X][X]), R ≠ 0 ∧
      Polynomial.C R = A * toB P0.Fc + B * derivative (toB P0.Fc))
    (hsepI : ∃ (R : ℚ[X]) (A B : ℚ[X][X]), R ≠ 0 ∧ Polynomial.C R =
      A * toB (invB P0.Fc P0.k (P0.k * P0.n)) +
        B * derivative (toB (invB P0.Fc P0.k (P0.k * P0.n)))) :
    ∃ M : CPoly ℚ, ∃ hM : Kron.irredQ M = true,
      haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      ∃ (pts : List (NF M × BranchCert (NF M))) (inf : BranchCert (NF M)),
        (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).valid = true := by
  classical
  have hS' := hS
  simp only [CurveProb.shapeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.not_eq_true'] at hS'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := hS'
  set ι : ℚ →+* QB := algebraMap ℚ QB with hι
  obtain ⟨hmon, hn⟩ := monic_of_shape P0.Fc P0.n h2 h3
  obtain ⟨hmonI, hnI⟩ := monic_of_shape (invB P0.Fc P0.k (P0.k * P0.n)) P0.n h4 h5
  obtain ⟨R, A, B, hR, hAB⟩ := hsep
  obtain ⟨RI, AI, BI, hRI, hABI⟩ := hsepI
  -- the branch data at every point of `ℚ̄` and at infinity
  have hG := fun z : QB ↦ exists_branchCert0 ((toB P0.Fc).map (mapRingHom ι)) P0.n (hmon.map _)
    (by rw [hmon.natDegree_map, hn]) (R.map ι) ((Polynomial.map_ne_zero_iff ι.injective).mpr hR)
    _ _ (bezout_map ι _ R A B hAB) z
  choose N p0 hN hys using hG
  choose ys hyslen hyscert using hys
  obtain ⟨NI, p0I, hNI, hysI⟩ := exists_branchCert0
    ((toB (invB P0.Fc P0.k (P0.k * P0.n))).map (mapRingHom ι)) P0.n (hmonI.map _)
    (by rw [hmonI.natDegree_map, hnI]) (RI.map ι) ((Polynomial.map_ne_zero_iff ι.injective).mpr hRI)
    _ _ (bezout_map ι _ RI AI BI hABI) 0
  -- the precisions
  set μ : QB → ℕ := fun z ↦
    (((toPoly P0.R0).map ι).comp (Polynomial.C z + X ^ N z)).natTrailingDegree with hμ
  set μf : QB → ℕ := fun z ↦
    (((toPoly P0.D).map ι).comp (Polynomial.C z + X ^ N z)).natTrailingDegree with hμf
  set pr : QB → ℕ := fun z ↦ p0 z + μ z + μf z + 1 with hpr
  have hpr0 : ∀ z, p0 z ≤ pr z := fun z ↦ by simp only [hpr]; omega
  set prI := p0I + NI * (P0.DWb + P0.DA + 1) + 1 with hprI
  obtain ⟨ysI, hysIlen, hysIcert⟩ := hysI prI (by omega)
  -- the points: the roots of `D · disc`
  set Q := (toPoly (mul P0.D (discRC P0.Fc P0.n P0.k))).map ι with hQ
  set Z := Q.roots.toFinset with hZ
  -- the algebraic numbers involved
  set S : Finset QB := Z ∪ Z.biUnion (fun z ↦ ((ys z (pr z) (hpr0 z)).flatten).toFinset) ∪
    ysI.flatten.toFinset with hSdef
  obtain ⟨M, hM, θ, hθ, hSM⟩ := exists_nf S
  have : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
  set ψ := rho M hθ with hψ
  set φ := algebraMap ℚ (NF M) with hφ
  have hψφ : ψ.comp φ = ι := Subsingleton.elim _ _
  set pre : QB → NF M := fun x ↦ if h : ∃ c, ψ c = x then h.choose else 0 with hpredef
  have hpre : ∀ x ∈ S, ψ (pre x) = x := fun x hx ↦ by
    have h : ∃ c, ψ c = x := hSM x hx
    simp only [hpredef, dif_pos h]
    exact h.choose_spec
  -- the data over `NF M`
  set cert : QB → BranchCert (NF M) := fun z ↦
    ⟨N z, (ys z (pr z) (hpr0 z)).map (·.map pre), pr z⟩ with hcert
  set pts : List (NF M × BranchCert (NF M)) := Z.toList.map fun z ↦ (pre z, cert z) with hpts
  set inf : BranchCert (NF M) := ⟨NI, ysI.map (·.map pre), prI⟩ with hinf
  refine ⟨M, hM, pts, inf, ?_⟩
  have hFc : (toB (P0.Fc.map (·.map φ))).map (mapRingHom ψ) = (toB P0.Fc).map (mapRingHom ι) := by
    rw [toB_mapL, Polynomial.map_map, mapRingHom_comp, hψφ]
  have hFcI : (toB (invB (P0.Fc.map (·.map φ)) P0.k (P0.k * P0.n))).map (mapRingHom ψ) =
      (toB (invB P0.Fc P0.k (P0.k * P0.n))).map (mapRingHom ι) := by
    rw [invB_map, toB_mapL, Polynomial.map_map, mapRingHom_comp, hψφ]
  have hZS : ∀ z ∈ Z, z ∈ S := fun z hz ↦ by
    rw [hSdef]; exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)
  have hysS : ∀ z ∈ Z, ∀ x ∈ (ys z (pr z) (hpr0 z)).flatten, x ∈ S := fun z hz x hx ↦ by
    rw [hSdef]
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨z, hz, List.mem_toFinset.mpr hx⟩))
  have hysIS : ∀ x ∈ ysI.flatten, x ∈ S := fun x hx ↦ by
    rw [hSdef]; exact Finset.mem_union_right _ (List.mem_toFinset.mpr hx)
  obtain ⟨hmon', hn', hk'⟩ := shape_monic P0.Fc P0.n P0.k h2 h3 h7
  have hQφ : toPoly (mul (P0.D.map φ) (discRC (P0.Fc.map (·.map φ)) P0.n P0.k)) =
      (toPoly (mul P0.D (discRC P0.Fc P0.n P0.k))).map φ := by
    rw [CPoly.toPoly_mul, CPoly.toPoly_mul, Polynomial.map_mul, toPoly_mapHom,
      toPoly_discRC_map φ P0.Fc P0.n P0.k hmon' hn' hk']
  have hR0 : toPoly P0.R0 ≠ 0 := fun h0 ↦ by
    rw [← trim_eq_nil_iff] at h0; rw [h0] at h9; simp at h9
  have hQ0 : toPoly (mul P0.D (discRC P0.Fc P0.n P0.k)) ≠ 0 := by
    rw [CPoly.toPoly_mul, mul_comm, ← CPoly.toPoly_mul, ← toPoly_trim]
    exact hR0
  refine valid_of_shapeOK _ (shapeOK_baseChange φ P0 hS pts inf) hNI ?_ ?_ ?_ ?_ ?_
  · -- the branch data at the points
    intro ac hac
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hac
    have hzZ : z ∈ Z := Finset.mem_toList.mp hz
    exact hyscert z (pr z) (hpr0 z) ψ _ (pre z) _ hFc (hpre z (hZS z hzZ))
      (map_pre ψ pre S hpre _ (hysS z hzZ))
  · -- the branch data at infinity
    exact hysIcert ψ _ 0 _ hFcI (map_zero ψ) (map_pre ψ pre S hpre _ hysIS)
  · -- the cover
    refine coverCheck_complete _ _ (by
      show toPoly (mul (P0.D.map φ) (discRC (P0.Fc.map (·.map φ)) P0.n P0.k)) ≠ 0
      rw [hQφ]; exact (Polynomial.map_ne_zero_iff φ.injective).mpr hQ0) ψ fun z hz ↦ ?_
    change ((toPoly (mul (P0.D.map φ) (discRC (P0.Fc.map (·.map φ)) P0.n P0.k))).map ψ).eval z = 0 at hz
    rw [hQφ, Polynomial.map_map, hψφ] at hz
    have hzZ : z ∈ Z := by
      rw [hZ, Multiset.mem_toFinset, mem_roots ((Polynomial.map_ne_zero_iff ι.injective).mpr hQ0)]
      exact hz
    refine ⟨pre z, List.mem_map.mpr ⟨(pre z, cert z), List.mem_map.mpr ⟨z, Finset.mem_toList.mpr hzZ,
      rfl⟩, rfl⟩, (hpre z (hZS z hzZ)).symm⟩
  · -- the orders along the branches
    intro ac hac
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hac
    have hzZ : z ∈ Z := Finset.mem_toList.mp hz
    obtain ⟨e1, l1, e2, l2⟩ := mu_baseChange φ ψ P0 hS pts inf (pre z) (hN z)
    rw [hψφ, hpre z (hZS z hzZ)] at e1 e2
    refine ⟨?_, ?_, l1, l2⟩
    · change _ < pr z
      rw [e1]; simp only [hpr, hμ]; omega
    · change _ < pr z + N z
      rw [e2]; simp only [hpr, hμf]; omega
  · -- the precision at infinity
    have hinfP : (P0.baseChange φ P0.k pts inf).inf = inf := rfl
    have hsb : (P0.baseChange φ P0.k pts inf).sbInf = -((NI * P0.DWb : ℕ) : ℤ) +
        ((NI * degT (P0.baseChange φ P0.k pts inf).R0 : ℕ) : ℤ) := by
      unfold CurveProb.sbInf; rw [DWb_baseChange, hinfP]
    have hsf : (P0.baseChange φ P0.k pts inf).sfInf = -((NI * P0.DA : ℕ) : ℤ) +
        ((NI * degT (P0.baseChange φ P0.k pts inf).D : ℕ) : ℤ) := by
      unfold CurveProb.sfInf; rw [DA_baseChange, hinfP]
    rw [hsb, hsf, hinfP]
    have e1 : NI * P0.DWb ≤ prI := by rw [hprI]; nlinarith
    have e2 : NI + NI * P0.DA < prI := by rw [hprI]; nlinarith
    constructor
    · show -(-((NI * P0.DWb : ℕ) : ℤ) + _) ≤ ((prI : ℕ) : ℤ)
      push_cast; omega
    · show ((NI : ℕ) : ℤ) - (-((NI * P0.DA : ℕ) : ℤ) + _) < ((prI : ℕ) : ℤ)
      push_cast; omega

end Exist

end Curves
