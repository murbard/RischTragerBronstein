import RischTragerBronstein.Torsion.PrimeUnramAux

/-!
# The prime step over a base field (unramified divisors)

`prime_step_unram`: for a curve `S` over a field `C` (e.g. a number field) with an integral basis
and a divisor `Γ − c ∞ₓ` at points of `C`-split unramified fibres, and a good prime (a Henselian DVR
`O` with an embedding `φ : C → Frac O` and the reduction data), if `m_p Γ̄` is principal modulo the
prime then every principal multiple `M Γ` gives `(m_p p^v) Γ` principal over `C` for some `v`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section PrimeStepU

variable {O K₀ : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [HenselianRing O (IsLocalRing.maximalIdeal O)] [Field K₀] [Algebra O K₀] [IsFractionRing O K₀]
variable {LK KK Lk kk : Type*} [Field LK] [Algebra K₀ LK] [Field KK] [Algebra K₀ KK] [IsAlgClosed KK]
  [Field Lk] [Algebra (IsLocalRing.ResidueField O) Lk] [Field kk]
  [Algebra (IsLocalRing.ResidueField O) kk] [IsAlgClosed kk]

local notation "𝕜" => IsLocalRing.ResidueField O
local notation "ρ" => IsLocalRing.residue O
local notation "ι" => algebraMap O K₀

set_option maxHeartbeats 2000000 in
/-- **The prime step.** -/
theorem prime_step_unram {ϖ : O} (hϖ : Irreducible ϖ) (F : O[X][X]) (hF : F.Monic)
    (SK : CurveData K₀ LK) (hSK : SK.F = F.map (mapRingHom ι)) (hBrK : SK.HasBranches KK)
    (hBIK : SK.HasBranchesInf KK)
    (Sk : CurveData 𝕜 Lk) (hSk : Sk.F = F.map (mapRingHom ρ)) (hBrk : Sk.HasBranches kk)
    (hBIk : Sk.HasBranchesInf kk)
    (hnk : Sk.F.natDegree = SK.F.natDegree) (hn : 0 < SK.F.natDegree)
    -- the integral basis
    (B : Fin SK.F.natDegree → O[X][X]) (D : O[X]) (hDm : D.Monic) (δ : Fin SK.F.natDegree → ℕ)
    (hB0 : B ⟨0, hn⟩ = Polynomial.C D) (hδ0 : δ ⟨0, hn⟩ = 0)
    (hδ : ∀ j : Fin SK.F.natDegree, (j : ℕ) ≠ 0 → 1 ≤ δ j)
    (hBK : SK.IsIntBasis KK (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) δ)
    (hBk : Sk.IsIntBasis kk (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ)) (D.map ρ)
      (fun j ↦ δ (Fin.cast hnk j)))
    -- the base fibres
    {g : ℕ} (hg : ∑ j, δ j + 1 = g + SK.F.natDegree)
    (x : Fin g → O) (hx : ∀ i j, i ≠ j → IsUnit (x i - x j))
    (y : Fin g → Fin SK.F.natDegree → O)
    (hsplit : ∀ i, F.map (evalRingHom (x i)) = ∏ k, (X - Polynomial.C (y i k)))
    (hFu : ∀ i k, IsUnit (Sup.evalW (derivative F) (x i) (y i k)))
    (hdet : ∀ i, IsUnit (Matrix.det (Matrix.of fun kk j ↦ Sup.evalW (B j) (x i) (y i kk))))
    (hDx : ∀ i, IsUnit (D.eval (x i)))
    (hNS : ∀ q : Fin SK.F.natDegree → 𝕜[X], (∀ j, q j ≠ 0 → (q j).natDegree + δ j ≤ g) →
      (∀ i (k : Fin SK.F.natDegree), (k : ℕ) ≠ 0 →
        Sup.evalW (PsiC (fun j ↦ (B j).map (mapRingHom ρ)) q) (ρ (x i)) (ρ (y i k)) = 0) →
      ∀ i, Sup.evalW (PsiC (fun j ↦ (B j).map (mapRingHom ρ)) q) (ρ (x i)) (ρ (y i ⟨0, hn⟩)) = 0)
    -- the divisor `Γ` at points of unramified fibres
    {J : Type*} [Fintype J] (α : J → O) (hα : ∀ j j', j ≠ j' → IsUnit (α j - α j'))
    (hαx : ∀ j i, IsUnit (α j - x i)) (hDα : ∀ j, IsUnit (D.eval (α j)))
    (yΓ : J → Fin SK.F.natDegree → O)
    (hsplitΓ : ∀ j, F.map (evalRingHom (α j)) = ∏ k, (X - Polynomial.C (yΓ j k)))
    (hFuΓ : ∀ j k, IsUnit (Sup.evalW (derivative F) (α j) (yΓ j k)))
    (ΓC : J → Fin SK.F.natDegree → ℕ) (cΓ : ℕ) (c' : J → ℕ) (hΓle : ∀ j k, ΓC j k ≤ c' j)
    (hsumΓ : ∑ j, ∑ k, ΓC j k = cΓ * SK.F.natDegree)
    -- the base-field data
    {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K] [IsAlgClosed K]
    (S : CurveData C L) (φ : C →+* K₀) (hSKφ : SK.F = S.F.map (mapRingHom φ))
    (hnK : SK.F.natDegree = S.F.natDegree)
    (BC : Fin S.F.natDegree → C[X][X]) (DC : C[X]) (δC : Fin S.F.natDegree → ℕ)
    (hBS : S.IsIntBasis K BC DC δC)
    (hBO : ∀ i, (B i).map (mapRingHom ι) = (BC (Fin.cast hnK i)).map (mapRingHom φ))
    (hDO : D.map ι = DC.map φ) (hδO : ∀ i, δ i = δC (Fin.cast hnK i))
    (αC : J → C) (hαO : ∀ j, ι (α j) = φ (αC j)) (yC : J → Fin S.F.natDegree → C)
    (hyO : ∀ j k, ι (yΓ j k) = φ (yC j (Fin.cast hnK k)))
    (Y0 : J → Fin S.F.natDegree → PowerSeries C)
    (hY0c : ∀ j k, PowerSeries.constantCoeff (Y0 j k) = yC j k)
    (hsp : ∀ j, S.F.map (branchSub (C := C) (K := C) 1 (αC j)) =
      ∏ k, (X - Polynomial.C (ofPowerSeries ℤ C (Y0 j k))))
    (hyinj : ∀ j, Function.Injective (yC j)) (ΓC' : J → Fin S.F.natDegree → ℕ)
    (hΓO : ∀ j k, ΓC j k = ΓC' j (Fin.cast hnK k))
    -- the prime
    (p : ℕ) (hp : p.Prime) (hpu : ∀ ℓ : ℕ, Nat.Coprime ℓ p → IsUnit (ℓ : O))
    (mp : ℕ) (hmp : 1 ≤ mp) (γk : 𝕜⟮Sk.x⟯⟮Sk.y⟯) (hγk0 : γk ≠ 0)
    (hγk : Sk.DivGEU (K := kk) (fun j ↦ ρ (α j)) (fun j k ↦ ρ (yΓ j (Fin.cast hnk k)))
      (fun j k ↦ mp * ΓC j (Fin.cast hnk k)) (mp * cΓ) γk) :
    ∀ M : ℕ, 0 < M → (∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGEU (K := K) αC yC (fun j k ↦ M * ΓC' j k) (M * cΓ) γ) →
      ∃ v : ℕ, ∃ γ : C⟮S.x⟯⟮S.y⟯, γ ≠ 0 ∧
        S.DivGEU (K := K) αC yC (fun j k ↦ (mp * p ^ v) * ΓC' j k) ((mp * p ^ v) * cΓ) γ := by
  classical
  intro M hM hprin
  have hιi : Function.Injective ι := IsFractionRing.injective O K₀
  have hσC : ∀ (q : J × Fin S.F.natDegree) i,
      LowerBd (basisSer BC DC 1 (αC q.1) (ofPowerSeries ℤ C (Y0 q.1 q.2)) i) 0 :=
    fun q i ↦ S.basisSer_lowerBd_unram hBS (αC q.1) (Y0 q.1) (hsp q.1) q.2 i
  -- the Hensel branches over `K₀`
  set Y0K : J → Fin SK.F.natDegree → PowerSeries K₀ :=
    fun j k ↦ PowerSeries.map φ (Y0 j (Fin.cast hnK k)) with hY0K
  have hY0Kc : ∀ j k, PowerSeries.constantCoeff (Y0K j k) = ι (yΓ j k) := by
    intro j k
    rw [hY0K, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hY0c, hyO]
  have hspK : ∀ j, SK.F.map (branchSub (C := K₀) (K := K₀) 1 (ι (α j))) =
      ∏ k, (X - Polynomial.C (ofPowerSeries ℤ K₀ (Y0K j k))) := by
    intro j
    have e1 : SK.F.map (branchSub (C := K₀) (K := K₀) 1 (ι (α j))) =
        (S.F.map (mapRingHom φ)).map (branchSub (C := K₀) (K := K₀) 1 (φ (αC j))) := by
      rw [hSKφ, hαO]
    rw [e1, split_map φ S.F 1 (αC j) _ (hsp j),
      ← prod_cast hnK (fun k ↦ X - Polynomial.C (lmap φ (ofPowerSeries ℤ C (Y0 j k))))]
    exact Finset.prod_congr rfl fun k _ ↦ by rw [lmap_ofPS]
  have hyinjK : ∀ j, Function.Injective fun k ↦ ι (yΓ j k) := by
    intro j a b h
    simp only [hyO] at h
    exact Fin.cast_injective hnK (hyinj j (φ.injective h))
  have hδf : (fun i ↦ δC (Fin.cast hnK i)) = δ := funext fun i ↦ (hδO i).symm
  have htrans : ∀ (β : J → Fin S.F.natDegree → ℕ) (Mc : ℕ),
      princTest δC Mc (fun _ : J × Fin S.F.natDegree ↦ 1) (fun q ↦ αC q.1)
        (fun q i ↦ basisSer BC DC 1 (αC q.1) (ofPowerSeries ℤ C (Y0 q.1 q.2)) i)
        (fun q ↦ β q.1 q.2) ↔
      princTest δ Mc (fun _ : J × Fin SK.F.natDegree ↦ 1) (fun q ↦ ι (α q.1))
        (fun q i ↦ basisSer (fun i ↦ (B i).map (mapRingHom ι)) (D.map ι) 1 (ι (α q.1))
          (ofPowerSeries ℤ K₀ (Y0K q.1 q.2)) i) (fun q ↦ β q.1 (Fin.cast hnK q.2)) := by
    intro β Mc
    have := princTest_transport S SK φ hnK BC DC δC (fun i ↦ (B i).map (mapRingHom ι)) (D.map ι)
      hBO hDO αC (fun j ↦ ι (α j)) hαO Y0 Y0K (fun j k ↦ rfl) hσC β Mc
    rwa [hδf] at this
  have hΓf : ∀ t : ℕ, (fun (q : J × Fin SK.F.natDegree) ↦ t * ΓC' q.1 (Fin.cast hnK q.2)) =
      fun q ↦ t * ΓC q.1 q.2 := fun t ↦ funext fun q ↦ by rw [hΓO]
  -- `M Γ` is principal over `K₀`
  have hC := (S.principal_iff_test_unram hBS αC yC Y0 hY0c hsp hyinj
    (fun j k ↦ M * ΓC' j k) (M * cΓ)).mp hprin
  have hKt := (htrans (fun j k ↦ M * ΓC' j k) (M * cΓ)).mp hC
  rw [hΓf M] at hKt
  have hSKp := (SK.principal_iff_test_unram hBK (fun j ↦ ι (α j)) (fun j k ↦ ι (yΓ j k)) Y0K
    hY0Kc hspK hyinjK (fun j k ↦ M * ΓC j k) (M * cΓ)).mpr hKt
  -- `M = p^v ℓ` with `ℓ` prime to `p`
  set v := M.factorization p with hv
  set ℓ := M / p ^ v with hℓdef
  have hMe : p ^ v * ℓ = M := Nat.ordProj_mul_ordCompl_eq_self M p
  have hℓcop : Nat.Coprime ℓ p := (Nat.coprime_ordCompl hp hM.ne').symm
  have hℓ1 : 1 ≤ ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · rw [h, mul_zero] at hMe; omega
    · exact h
  obtain ⟨Ξ, hΞ0, hΞ⟩ := hSKp
  rw [← hMe] at hΞ
  obtain ⟨γ', hγ'0, hγ'⟩ := principal_at_prime_unram hϖ F hF SK hSK hBrK hBIK Sk hSk hBrk hBIk hnk
    hn B D hDm δ hB0 hδ0 hδ hBK hBk hg x hx y hsplit hFu hdet hDx hNS α hα hαx hDα yΓ hsplitΓ hFuΓ
    ΓC cΓ c' hΓle hsumΓ mp (p ^ v) ℓ hmp (Nat.one_le_pow _ _ hp.pos) hℓ1 (hpu ℓ hℓcop) γk hγk0 hγk
    Ξ hΞ0 hΞ
  -- back to the base field
  refine ⟨v, (S.principal_iff_test_unram hBS αC yC Y0 hY0c hsp hyinj _ _).mpr ?_⟩
  refine (htrans (fun j k ↦ (mp * p ^ v) * ΓC' j k) ((mp * p ^ v) * cΓ)).mpr ?_
  rw [hΓf (mp * p ^ v)]
  exact (SK.principal_iff_test_unram hBK (fun j ↦ ι (α j)) (fun j k ↦ ι (yΓ j k)) Y0K
    hY0Kc hspK hyinjK _ _).mp ⟨γ', hγ'0, hγ'⟩

end PrimeStepU

end Curves
