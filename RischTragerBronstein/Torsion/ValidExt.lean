import RischTragerBronstein.Torsion.ValidExist
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Valid branch data over an enlarged number field

**`exists_valid_ext`**: `exists_valid` with a number field `ℚ[γ]/(M)` (integral `M`) that also
contains a prescribed finite set of algebraic numbers and primitive roots of unity of all the
ramification indices; the special points are distinct and are roots of `D · disc`.
-/

open Polynomial

namespace Curves

open CPoly Sup NFC

section Exist

/-- **Valid branch data exist** over a certified number field containing prescribed algebraic
numbers and the roots of unity of the ramification indices, with distinct special points (the roots
of `D · disc`) and an integral defining polynomial. -/
theorem exists_valid_ext (P0 : CurveProb ℚ) (hS : P0.shapeOK = true)
    (hsep : ∃ (R : ℚ[X]) (A B : ℚ[X][X]), R ≠ 0 ∧
      Polynomial.C R = A * toB P0.Fc + B * derivative (toB P0.Fc))
    (hsepI : ∃ (R : ℚ[X]) (A B : ℚ[X][X]), R ≠ 0 ∧ Polynomial.C R =
      A * toB (invB P0.Fc P0.k (P0.k * P0.n)) +
        B * derivative (toB (invB P0.Fc P0.k (P0.k * P0.n)))) (extra : Finset QB) :
    ∃ M : CPoly ℚ, ∃ hM : Kron.irredQ M = true, (∀ q ∈ M, q.den = 1) ∧
      ∃ θ : QB, ∃ hθ : aeval θ (toPoly M) = 0,
      haveI : Fact (Irreducible (toPoly M)) := ⟨Kron.irredQ_sound M hM⟩
      (∀ s ∈ extra, ∃ c : NF M, rho M hθ c = s) ∧
      ∃ (pts : List (NF M × BranchCert (NF M))) (inf : BranchCert (NF M)),
        (P0.baseChange (algebraMap ℚ (NF M)) P0.k pts inf).valid = true ∧
        (pts.map Prod.fst).Nodup ∧
        (∀ ac ∈ pts, ((toPoly (mul P0.D (discRC P0.Fc P0.n P0.k))).map (algebraMap ℚ QB)).eval
          (rho M hθ ac.1) = 0) ∧
        (∀ ac ∈ pts, ∃ ζF : NF M, IsPrimitiveRoot (rho M hθ ζF) ac.2.N) := by
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
  -- the roots of unity
  have hζex : ∀ z : QB, ∃ ζ : QB, IsPrimitiveRoot ζ (N z) := fun z ↦ by
    haveI : NeZero ((N z : ℕ) : ℚ) := ⟨by exact_mod_cast (hN z).ne'⟩
    exact HasEnoughRootsOfUnity.exists_primitiveRoot QB (N z)
  choose ζq hζq using hζex
  -- the algebraic numbers involved
  set S : Finset QB := Z ∪ Z.biUnion (fun z ↦ ((ys z (pr z) (hpr0 z)).flatten).toFinset) ∪
    ysI.flatten.toFinset ∪ extra ∪ Z.image ζq with hSdef
  obtain ⟨M, hM, hMint, θ, hθ, hSM⟩ := exists_nf_int S
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
  have hSext : ∀ s ∈ extra, s ∈ S := fun s hs ↦ by
    rw [hSdef]; simp only [Finset.mem_union]; exact Or.inl (Or.inr hs)
  have hSζ : ∀ z ∈ Z, ζq z ∈ S := fun z hz ↦ by
    rw [hSdef]; simp only [Finset.mem_union]; exact Or.inr (Finset.mem_image_of_mem _ hz)
  have hZSx : ∀ z ∈ Z, z ∈ S := fun z hz ↦ by
    rw [hSdef]; simp only [Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (Or.inl hz)))
  have hpre_inj : Set.InjOn pre Z := fun z hz z' hz' h ↦ by
    have := congrArg ψ h
    rwa [hpre z (hZSx z hz), hpre z' (hZSx z' hz')] at this
  refine ⟨M, hM, hMint, θ, hθ, fun s hs ↦ hSM s (hSext s hs), pts, inf, ?_, ?_, ?_, ?_⟩
  rotate_left
  · -- distinct points
    simp only [hpts, List.map_map, Function.comp_def]
    exact (List.nodup_map_iff_inj_on (Finset.nodup_toList Z)).mpr fun z hz z' hz' h ↦
      hpre_inj (Finset.mem_toList.mp hz) (Finset.mem_toList.mp hz') h
  · -- the points are roots of `D · disc`
    intro ac hac
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hac
    have hzZ : z ∈ Z := Finset.mem_toList.mp hz
    show (Q).eval (ψ (pre z)) = 0
    rw [hpre z (hZSx z hzZ)]
    rw [hZ, Multiset.mem_toFinset] at hzZ
    exact (mem_roots'.mp hzZ).2
  · -- the roots of unity
    intro ac hac
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hac
    have hzZ : z ∈ Z := Finset.mem_toList.mp hz
    exact ⟨pre (ζq z), by rw [hpre _ (hSζ z hzZ)]; exact hζq z⟩
  have hFc : (toB (P0.Fc.map (·.map φ))).map (mapRingHom ψ) = (toB P0.Fc).map (mapRingHom ι) := by
    rw [toB_mapL, Polynomial.map_map, mapRingHom_comp, hψφ]
  have hFcI : (toB (invB (P0.Fc.map (·.map φ)) P0.k (P0.k * P0.n))).map (mapRingHom ψ) =
      (toB (invB P0.Fc P0.k (P0.k * P0.n))).map (mapRingHom ι) := by
    rw [invB_map, toB_mapL, Polynomial.map_map, mapRingHom_comp, hψφ]
  have hZS : ∀ z ∈ Z, z ∈ S := fun z hz ↦ by
    rw [hSdef]; simp only [Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (Or.inl hz)))
  have hysS : ∀ z ∈ Z, ∀ x ∈ (ys z (pr z) (hpr0 z)).flatten, x ∈ S := fun z hz x hx ↦ by
    rw [hSdef]; simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inr (Finset.mem_biUnion.mpr ⟨z, hz, List.mem_toFinset.mpr hx⟩))))
  have hysIS : ∀ x ∈ ysI.flatten, x ∈ S := fun x hx ↦ by
    rw [hSdef]; simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr (List.mem_toFinset.mpr hx)))
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
