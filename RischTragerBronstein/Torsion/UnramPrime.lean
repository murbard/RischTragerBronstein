import RischTragerBronstein.Torsion.Unram

/-!
# Torsion at a prime for divisors at unramified points (general curves)

`principal_at_prime_unram`: the specialization of `principal_at_primeG` to divisors supported at
points `(α_j, y_{j,k})` of fibres that split into simple roots over `O`, stated with `DivGEU`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

lemma lmap_ofPS {C C' : Type*} [Field C] [Field C'] (φ : C →+* C') (Y : PowerSeries C) :
    lmap φ (ofPowerSeries ℤ C Y) = ofPowerSeries ℤ C' (PowerSeries.map φ Y) := by
  ext t
  rw [lmap_coeff, coeff_ofPS, coeff_ofPS]
  split_ifs
  · rw [PowerSeries.coeff_map]
  · exact map_zero φ

lemma extend_mul_left {α β : Type*} (f : α → β) (g : α → ℕ) (m : ℕ) :
    (Function.extend f (fun a ↦ m * g a) 0) = fun b ↦ m * Function.extend f g 0 b := by
  classical
  funext b
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hb
    rw [Function.extend_def, Function.extend_def, dif_pos ⟨a, rfl⟩, dif_pos ⟨a, rfl⟩]
  · rw [Function.extend_apply' _ _ _ hb, Function.extend_apply' _ _ _ hb]; simp

section UnramPrime

variable {O K₀ : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [HenselianRing O (IsLocalRing.maximalIdeal O)] [Field K₀] [Algebra O K₀] [IsFractionRing O K₀]
variable {LK KK Lk kk : Type*} [Field LK] [Algebra K₀ LK] [Field KK] [Algebra K₀ KK] [IsAlgClosed KK]
  [Field Lk] [Algebra (IsLocalRing.ResidueField O) Lk] [Field kk]
  [Algebra (IsLocalRing.ResidueField O) kk] [IsAlgClosed kk]

local notation "𝕜" => IsLocalRing.ResidueField O
local notation "ρ" => IsLocalRing.residue O
local notation "ι" => algebraMap O K₀

set_option maxHeartbeats 2000000 in
/-- **Torsion at a prime, unramified support.** -/
theorem principal_at_prime_unram {ϖ : O} (hϖ : Irreducible ϖ) (F : O[X][X]) (hF : F.Monic)
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
    -- the multiples
    (m s ℓ : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) (hℓ1 : 1 ≤ ℓ) (hℓ : IsUnit (ℓ : O))
    (γk : 𝕜⟮Sk.x⟯⟮Sk.y⟯) (hγk0 : γk ≠ 0)
    (hγk : Sk.DivGEU (K := kk) (fun j ↦ ρ (α j)) (fun j k ↦ ρ (yΓ j (Fin.cast hnk k)))
      (fun j k ↦ m * ΓC j (Fin.cast hnk k)) (m * cΓ) γk)
    (Ξ : K₀⟮SK.x⟯⟮SK.y⟯) (hΞ0 : Ξ ≠ 0)
    (hΞ : SK.DivGEU (K := KK) (fun j ↦ ι (α j)) (fun j k ↦ ι (yΓ j k))
      (fun j k ↦ (s * ℓ) * ΓC j k) ((s * ℓ) * cΓ) Ξ) :
    ∃ γ : K₀⟮SK.x⟯⟮SK.y⟯, γ ≠ 0 ∧ SK.DivGEU (K := KK) (fun j ↦ ι (α j)) (fun j k ↦ ι (yΓ j k))
      (fun j k ↦ (m * s) * ΓC j k) ((m * s) * cΓ) γ := by
  classical
  have hιi : Function.Injective ι := IsFractionRing.injective O K₀
  have hunitk : ∀ z : O, IsUnit z → ρ z ≠ 0 := fun z hz ↦ (hz.map ρ).ne_zero
  set ιK := algebraMap K₀ KK with hιK
  set φ : O →+* KK := ιK.comp ι with hφdef
  have hφ : Function.Injective φ := ιK.injective.comp hιi
  have hydiffΓ : ∀ j k l, k ≠ l → IsUnit (yΓ j k - yΓ j l) := by
    intro j k l hkl
    have h := hFuΓ j k
    rw [Sup.evalW, ← Polynomial.derivative_map, hsplitΓ j,
      Sup.derivative_prod_X_sub_C_eval (fun l ↦ yΓ j l) k] at h
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun l ↦ yΓ j k - yΓ j l)
      (Finset.mem_erase.mpr ⟨Ne.symm hkl, Finset.mem_univ l⟩)) h
  have hFΓ0 : ∀ j k, Sup.evalW F (α j) (yΓ j k) = 0 := fun j k ↦ by
    rw [Sup.evalW, hsplitΓ j, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  -- branch systems over `K₀`
  have hyinj0 : ∀ j, Function.Injective fun k ↦ ι (yΓ j k) := by
    intro j a b h
    by_contra hne
    exact (hydiffΓ j a b hne).ne_zero (by rw [sub_eq_zero]; exact hιi h)
  have hK0 : ∀ j, ∃ Y0 : Fin SK.F.natDegree → PowerSeries K₀,
      (∀ k, (fibrePS SK.F (ι (α j))).eval (Y0 k) = 0 ∧
        PowerSeries.constantCoeff (Y0 k) = ι (yΓ j k)) ∧
      SK.F.map (branchSub (C := K₀) (K := K₀) 1 (ι (α j))) =
        ∏ k, (X - Polynomial.C (ofPowerSeries ℤ K₀ (Y0 k))) := by
    intro j
    refine split_unramified SK.F SK.monic (ι (α j)) (fun k ↦ ι (yΓ j k)) (hyinj0 j) (fun k ↦ ?_)
      (fun k ↦ ?_)
    · have := fibreAt_eval_map (Kb := K₀) F ι (α j) (yΓ j k)
      rw [← hSK] at this
      simpa [hFΓ0] using this
    · have := fibreAt_eval_map (Kb := K₀) (derivative F) ι (α j) (yΓ j k)
      rw [← Polynomial.derivative_map, ← hSK] at this
      simp only [Algebra.algebraMap_self, RingHom.id_apply] at this
      rw [this]
      exact (map_ne_zero_iff _ hιi).mpr (hFuΓ j k).ne_zero
  choose Y0 hY0 hsp0 using hK0
  have hroot0 : ∀ j k, (SK.F.map (branchSub (C := K₀) (K := K₀) 1 (ι (α j)))).eval
      (ofPowerSeries ℤ K₀ (Y0 j k)) = 0 := fun j k ↦ by
    rw [hsp0 j, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  -- branch systems over `KK`
  have hyinjK : ∀ j, Function.Injective fun k ↦ ιK (ι (yΓ j k)) :=
    fun j a b h ↦ hyinj0 j (ιK.injective h)
  choose YK hYK1 hYK2 hYK3 hYK4 using fun j ↦ SK.unram_system (Kb := KK) F ι hSK (α j) (yΓ j)
    (hsplitΓ j) (fun k ↦ (map_ne_zero_iff _ ιK.injective).mpr
      ((map_ne_zero_iff _ hιi).mpr (hFuΓ j k).ne_zero)) (hyinjK j)
  have hYKprod : ∀ j, SK.F.map (branchSub 1 (ιK (ι (α j)))) =
      ∏ k, (X - Polynomial.C (ofPowerSeries ℤ KK (YK j k))) := fun j ↦ by
    rw [hYK4 j, List.map_ofFn, List.prod_ofFn]; rfl
  have hYKinj : ∀ j, Function.Injective fun k ↦ PowerSeries.constantCoeff (YK j k) := by
    intro j a b h
    simp only [hYK2] at h
    exact hyinjK j h
  have hlmapY : ∀ j k, lmap ιK (ofPowerSeries ℤ K₀ (Y0 j k)) = ofPowerSeries ℤ KK (YK j k) := by
    intro j k
    rw [lmap_ofPS]
    congr 1
    refine SK.unram_root_unique _ (YK j) (hYKprod j) (hYKinj j) k _ ?_ ?_
    · rw [← lmap_ofPS]; exact SK.lmap_root 1 (ι (α j)) _ (hroot0 j k)
    · rw [hYK2, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, (hY0 j k).2]
  -- branch systems over `kk`
  have hyinjk : ∀ j, Function.Injective fun k : Fin Sk.F.natDegree ↦
      algebraMap 𝕜 kk (ρ (yΓ j (Fin.cast hnk k))) := by
    intro j a b hab
    by_contra hne
    have hne' : Fin.cast hnk a ≠ Fin.cast hnk b := fun h ↦ hne (Fin.cast_injective hnk h)
    exact hunitk _ (hydiffΓ j _ _ hne') (by
      rw [map_sub, sub_eq_zero]; exact (algebraMap 𝕜 kk).injective hab)
  have hsplitΓk : ∀ j, F.map (evalRingHom (α j)) =
      ∏ k : Fin Sk.F.natDegree, (X - Polynomial.C (yΓ j (Fin.cast hnk k))) := fun j ↦ by
    rw [prod_cast hnk (fun k ↦ X - Polynomial.C (yΓ j k))]; exact hsplitΓ j
  choose Yk hYk1 hYk2 hYk3 hYk4 using fun j ↦ Sk.unram_system (Kb := kk) F ρ hSk (α j)
    (fun k ↦ yΓ j (Fin.cast hnk k)) (hsplitΓk j)
    (fun k ↦ (map_ne_zero_iff _ (algebraMap 𝕜 kk).injective).mpr (hunitk _ (hFuΓ j _)))
    (hyinjk j)
  have hYkprod : ∀ j, Sk.F.map (branchSub 1 (algebraMap 𝕜 kk (ρ (α j)))) =
      ∏ k, (X - Polynomial.C (ofPowerSeries ℤ kk (Yk j k))) := fun j ↦ by
    rw [hYk4 j, List.map_ofFn, List.prod_ofFn]; rfl
  have hYKinj' : ∀ j, Function.Injective fun k ↦ ofPowerSeries ℤ KK (YK j k) := fun j a b h ↦
    hYKinj j (by simp only; rw [HahnSeries.ofPowerSeries_injective h])
  have hYkinjc : ∀ j, Function.Injective fun k ↦ PowerSeries.constantCoeff (Yk j k) := by
    intro j a b h
    simp only [hYk2] at h
    exact hyinjk j h
  have hYkinj' : ∀ j, Function.Injective fun k ↦ ofPowerSeries ℤ kk (Yk j k) := fun j a b h ↦
    hYkinjc j (by simp only; rw [HahnSeries.ofPowerSeries_injective h])
  -- the data for `principal_at_primeG`
  set lK : J → List (LaurentSeries KK) := fun j ↦ List.ofFn fun k ↦ ofPowerSeries ℤ KK (YK j k)
    with hlKdef
  set ΓK : J → LaurentSeries KK → ℕ :=
    fun j ↦ Function.extend (fun k ↦ ofPowerSeries ℤ KK (YK j k)) (ΓC j) 0 with hΓKdef
  set lk : J → List (LaurentSeries kk) := fun j ↦ List.ofFn fun k ↦ ofPowerSeries ℤ kk (Yk j k)
    with hlkdef
  set Γk : J → LaurentSeries kk → ℕ := fun j ↦
    Function.extend (fun k ↦ ofPowerSeries ℤ kk (Yk j k)) (fun k ↦ ΓC j (Fin.cast hnk k)) 0
    with hΓkdef
  set dΓ : J → ℕ := fun j ↦ ∑ k, ΓC j k with hdΓdef
  have hdK : ∀ j, ((lK j).map (ΓK j)).sum = 1 * dΓ j := by
    intro j
    rw [hlKdef, List.map_ofFn, List.sum_ofFn, one_mul]
    exact Finset.sum_congr rfl fun k _ ↦ (hYKinj' j).extend_apply _ _ k
  have hdk : ∀ j, ((lk j).map (Γk j)).sum = 1 * dΓ j := by
    intro j
    rw [hlkdef, List.map_ofFn, List.sum_ofFn, one_mul, hdΓdef]
    simp only [Function.comp_apply, hΓkdef, (hYkinj' j).extend_apply]
    exact Fintype.sum_equiv (finCongr hnk) _ _ fun _ ↦ rfl
  have hle : ∀ j, dΓ j ≤ SK.F.natDegree * c' j := by
    intro j
    calc dΓ j ≤ ∑ _k : Fin SK.F.natDegree, c' j := Finset.sum_le_sum fun k _ ↦ hΓle j k
      _ = SK.F.natDegree * c' j := by simp
  -- the places: all roots, unramified
  set σK : J × Fin SK.F.natDegree → Fin SK.F.natDegree → LaurentSeries K₀ := fun q i ↦
    basisSer (fun i ↦ (B i).map (mapRingHom ι)) (D.map ι) 1 (ι (α q.1))
      (ofPowerSeries ℤ K₀ (Y0 q.1 q.2)) i with hσKdef
  have hembY : ∀ j k (f : K₀⟮SK.x⟯⟮SK.y⟯), SK.embG (branchSub 1 (ιK (ι (α j))))
      (branchSub_injective 1 one_pos _) (ofPowerSeries ℤ KK (YK j k))
      (SK.root_of_mem (hYK4 j) (List.mem_ofFn.mpr ⟨k, rfl⟩)) f =
      SK.embG (branchSub 1 (ιK (ι (α j)))) (branchSub_injective 1 one_pos _)
        (lmap ιK (ofPowerSeries ℤ K₀ (Y0 j k))) (SK.lmap_root 1 (ι (α j)) _ (hroot0 j k)) f := by
    intro j k f
    exact congrArg (fun ψ : K₀⟮SK.x⟯⟮SK.y⟯ →+* LaurentSeries KK ↦ ψ f)
      (SK.embG_congr' rfl _ _ (hlmapY j k).symm _ _)
  have hσ : ∀ q i, LowerBd (σK q i) 0 := by
    rintro ⟨j, k⟩ i
    have h1 := hBK.reg i (ιK (ι (α j))) 1 one_ne_zero _ (hYK4 j) (ofPowerSeries ℤ KK (YK j k))
      (List.mem_ofFn.mpr ⟨k, rfl⟩)
    rw [hembY, SK.embG_lmap_fnWQ 1 one_pos (ι (α j)) _ (hroot0 j k)] at h1
    exact (lowerBd_lmap_iff _ _ _).mp (lowerBd_of_le_order _ 0 h1)
  have hψne : ∀ cK : Fin SK.F.natDegree → K₀[X], cK ≠ 0 →
      SK.elt (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) cK ≠ 0 :=
    fun cK hcK h ↦ hcK (CurveData.elt_eq_zero hBK.hD hBK.deg hBK.det cK h)
  -- orders over `KK` at the roots from the base-field expansions
  have hordK0 : ∀ (cK : Fin SK.F.natDegree → K₀[X]), cK ≠ 0 → ∀ j k (u : ℕ),
      LowerBd (∑ i, branchSub (K := K₀) 1 (ι (α j)) (cK i) * σK (j, k) i) u →
      (u : ℤ) ≤ (SK.embG (branchSub 1 (ιK (ι (α j)))) (branchSub_injective 1 one_pos _)
        (ofPowerSeries ℤ KK (YK j k)) (SK.root_of_mem (hYK4 j) (List.mem_ofFn.mpr ⟨k, rfl⟩))
        (SK.elt (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) cK)).order := by
    intro cK hcK j k u hLB
    rw [hembY]
    refine le_order_of_lowerBd _ ((map_ne_zero_iff _ (SK.embG _ _ _ _).injective).mpr
      (hψne cK hcK)) _ ?_
    rw [SK.embG_elt_lmap _ _ cK 1 one_pos (ι (α j)) _ (hroot0 j k)]
    exact (lowerBd_lmap_iff _ _ _).mpr hLB
  -- orders over `kk` from those over `KK`, through jets over `O`
  have eF : (F.map (mapRingHom ι)).map (mapRingHom ιK) = F.map (mapRingHom φ) := by
    rw [Polynomial.map_map, Polynomial.mapRingHom_comp]
  have hDαK : ∀ j, (D.map ι).eval (ι (α j)) ≠ 0 := fun j ↦ by
    rw [eval_map, eval₂_hom]; exact (map_ne_zero_iff _ hιi).mpr (hDα j).ne_zero
  have hDαk : ∀ j, (D.map ρ).eval (ρ (α j)) ≠ 0 := fun j ↦ by
    rw [eval_map, eval₂_hom]; exact hunitk _ (hDα j)
  have hordk0 : ∀ (c : Fin SK.F.natDegree → O[X]), (¬ ∀ j, Polynomial.C ϖ ∣ c j) → ∀ j
      (k : Fin Sk.F.natDegree) (u : ℕ),
      LowerBd (∑ i, branchSub (K := K₀) 1 (ι (α j)) ((c i).map ι) * σK (j, Fin.cast hnk k) i) u →
      (u : ℤ) ≤ (Sk.embG (branchSub 1 (algebraMap 𝕜 kk (ρ (α j)))) (branchSub_injective 1 one_pos _)
        (ofPowerSeries ℤ kk (Yk j k)) (Sk.root_of_mem (hYk4 j) (List.mem_ofFn.mpr ⟨k, rfl⟩))
        (Sk.elt (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ)) (D.map ρ)
          (fun j ↦ (c (Fin.cast hnk j)).map ρ))).order := by
    intro c hc j k u hLB
    obtain ⟨j0, hj0⟩ : ∃ j0, ¬ Polynomial.C ϖ ∣ c j0 := by
      by_contra h; push Not at h; exact hc h
    have hcK : (fun i ↦ (c i).map ι) ≠ 0 := by
      intro h
      apply hj0
      have := congrFun h j0
      simp only [Pi.zero_apply, Polynomial.map_eq_zero_iff hιi] at this
      rw [this]; exact dvd_zero _
    have hck : (fun i ↦ (c (Fin.cast hnk i)).map ρ) ≠ 0 := by
      intro h
      apply hj0
      rw [Jac.C_dvd_iff_map hϖ]
      have := congrFun h (Fin.cast hnk.symm j0)
      simpa using this
    have h1 := hordK0 _ hcK j (Fin.cast hnk k) u hLB
    -- to the numerator over `KK`
    have hWK : PsiC (fun j ↦ (B j).map (mapRingHom ι)) (fun i ↦ (c i).map ι) =
        (PsiC B c).map (mapRingHom ι) := (PsiC_map ι B c).symm
    rw [CurveData.elt_eq_fnWQ, ← SK.order_W_eq_fnWQ _ _ _ (hDαK j) _ _
      (by rw [← CurveData.elt_eq_fnWQ]; exact hψne _ hcK), hWK,
      CurveData.eval_branchSub_ofPS] at h1
    have hlb := lowerBd_of_le_order _ u h1
    have hv := (lowerBd_iff_vanishAtG SK.F _ _ (YK j (Fin.cast hnk k)) (hYK1 j _) (hYK2 j _)
      (hYK3 j _) ((PsiC B c).map (mapRingHom ι)) u).mp (by exact_mod_cast hlb)
    have e1 : SK.F.map (mapRingHom ιK) = F.map (mapRingHom φ) := by rw [hSK, eF]
    have e2 : ((PsiC B c).map (mapRingHom ι)).map (mapRingHom ιK) = (PsiC B c).map (mapRingHom φ) := by
      rw [Polynomial.map_map, Polynomial.mapRingHom_comp]
    rw [e1, e2] at hv
    -- down to `O`
    obtain ⟨V, hV⟩ := exists_branchG (hFΓ0 j (Fin.cast hnk k)) (hFuΓ j _) u
    have hvO := vanishAtG_of_map φ hφ hV (by
      rw [Polynomial.derivative_map, evalW_mapG]; exact (hFuΓ j _).map φ) hv
    -- up to `kk`
    have hvk := (hvO.map ρ).map (algebraMap 𝕜 kk)
    have hWk : PsiC (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ))
        (fun j ↦ (c (Fin.cast hnk j)).map ρ) = (PsiC B c).map (mapRingHom ρ) := by
      rw [PsiC_cast hnk (fun j ↦ (B j).map (mapRingHom ρ)) (fun j ↦ (c j).map ρ), PsiC_map]
    have e3 : (F.map (mapRingHom ρ)).map (mapRingHom (algebraMap 𝕜 kk)) =
        Sk.F.map (mapRingHom (algebraMap 𝕜 kk)) := by rw [hSk]
    rw [e3, ← hWk] at hvk
    have hlbk := (lowerBd_iff_vanishAtG Sk.F _ _ (Yk j k) (hYk1 j k) (hYk2 j k) (hYk3 j k) _ u).mpr
      hvk
    rw [CurveData.elt_eq_fnWQ, ← Sk.order_W_eq_fnWQ _ _ _ (hDαk j) _ _
      (by rw [← CurveData.elt_eq_fnWQ]; exact fun h ↦ hck (CurveData.elt_eq_zero hBk.hD hBk.deg
        hBk.det _ h)), CurveData.eval_branchSub_ofPS]
    refine le_order_of_lowerBd _ ?_ _ (by exact_mod_cast hlbk)
    intro h0
    have hf0 : Sk.fnWQ (PsiC (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ))
        (fun j ↦ (c (Fin.cast hnk j)).map ρ)) (D.map ρ) ≠ 0 := by
      rw [← CurveData.elt_eq_fnWQ]
      exact fun h ↦ hck (CurveData.elt_eq_zero hBk.hD hBk.deg hBk.det _ h)
    have hne := (map_ne_zero_iff _ (Sk.embG (branchSub 1 (algebraMap 𝕜 kk (ρ (α j))))
      (branchSub_injective 1 one_pos _) (ofPowerSeries ℤ kk (Yk j k))
      (Sk.root_of_mem (hYk4 j) (List.mem_ofFn.mpr ⟨k, rfl⟩))).injective).mpr hf0
    rw [Sk.embG_fnWQ, CurveData.eval_branchSub_ofPS, h0, zero_mul] at hne
    exact hne rfl
  -- the place maps
  set πK : J → LaurentSeries KK → J × Fin SK.F.natDegree := fun j ↦
    Function.extend (fun k ↦ ofPowerSeries ℤ KK (YK j k)) (fun k ↦ (j, k)) (fun _ ↦ (j, ⟨0, hn⟩))
    with hπKdef
  set πk : J → LaurentSeries kk → J × Fin SK.F.natDegree := fun j ↦
    Function.extend (fun k ↦ ofPowerSeries ℤ kk (Yk j k)) (fun k ↦ (j, Fin.cast hnk k))
      (fun _ ↦ (j, ⟨0, hn⟩)) with hπkdef
  have hmP : ∑ q : J × Fin SK.F.natDegree, (c' q.1 - ΓC q.1 q.2) =
      ∑ j, (SK.F.natDegree * c' j - dΓ j) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_tsub_distrib _ (fun k _ ↦ hΓle j k), hdΓdef]
    simp
  have hsumΓ' : ∑ j, dΓ j = cΓ * SK.F.natDegree := hsumΓ
  have hΓK : ∀ j r, r ∈ lK j → ((c' j * 1 : ℕ) : ℤ) - ΓK j r =
      ((fun _ _ ↦ 1 : J → LaurentSeries KK → ℕ) j r) * ((fun q ↦ c' q.1 - ΓC q.1 q.2) (πK j r)) := by
    intro j r hr
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
    simp only [hΓKdef, hπKdef, (hYKinj' j).extend_apply]
    push_cast [hΓle j k]
    ring
  have hΓk : ∀ j r, r ∈ lk j → ((c' j * 1 : ℕ) : ℤ) - Γk j r =
      ((fun _ _ ↦ 1 : J → LaurentSeries kk → ℕ) j r) * ((fun q ↦ c' q.1 - ΓC q.1 q.2) (πk j r)) := by
    intro j r hr
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
    simp only [hΓkdef, hπkdef, (hYkinj' j).extend_apply]
    push_cast [hΓle j (Fin.cast hnk k)]
    ring
  -- the witnesses along the branch systems
  have hyk𝕜 : ∀ j, Function.Injective fun k : Fin Sk.F.natDegree ↦ ρ (yΓ j (Fin.cast hnk k)) :=
    fun j a b h ↦ hyinjk j (by simp only at h ⊢; rw [h])
  have hyK₀ : ∀ j, Function.Injective fun k ↦ ι (yΓ j k) := hyinj0
  have hγk' := (Sk.divGEU_iff (K := kk) (fun j ↦ ρ (α j)) (fun j k ↦ ρ (yΓ j (Fin.cast hnk k))) Yk
    hYkprod hYk2 hyk𝕜 _ _ γk).mp hγk
  have hmk : (fun j ↦ Function.extend (fun k ↦ ofPowerSeries ℤ kk (Yk j k))
      (fun k ↦ m * ΓC j (Fin.cast hnk k)) 0) = fun j r ↦ m * Γk j r :=
    funext fun j ↦ extend_mul_left _ _ _
  rw [hmk] at hγk'
  have hΞ' := (SK.divGEU_iff (K := KK) (fun j ↦ ι (α j)) (fun j k ↦ ι (yΓ j k)) YK
    hYKprod hYK2 hyK₀ _ _ Ξ).mp hΞ
  have hmK : (fun j ↦ Function.extend (fun k ↦ ofPowerSeries ℤ KK (YK j k))
      (fun k ↦ (s * ℓ) * ΓC j k) 0) = fun j r ↦ (s * ℓ) * ΓK j r :=
    funext fun j ↦ extend_mul_left _ _ _
  rw [hmK] at hΞ'
  obtain ⟨γ, hγ0, hγ⟩ := principal_at_primeG hϖ F hF SK hSK hBrK hBIK Sk hSk hBrk hBIk hnk hn B D hDm
    δ hB0 hδ0 hδ hBK hBk hg x hx y hsplit hFu hdet hDx hNS α hα hαx (fun _ ↦ 1) (fun _ ↦ one_pos) lK
    (fun j ↦ SK.list_split _ _ (hYKprod j)) ΓK (fun _ ↦ 1) (fun _ ↦ one_pos) lk
    (fun j ↦ Sk.list_split _ _ (hYkprod j)) Γk cΓ c' dΓ hdK hdk hsumΓ' hle Prod.fst (fun _ ↦ 1)
    (fun _ ↦ one_pos) (fun q ↦ c' q.1 - ΓC q.1 q.2) hmP σK hσ πK (fun _ _ ↦ 1) hΓK
    (fun cK hcK j r hr u hLB ↦ by
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
      have hπ : πK j (ofPowerSeries ℤ KK (YK j k)) = (j, k) := (hYKinj' j).extend_apply _ _ k
      simp only [hπ] at hLB
      simp only [one_mul]
      exact hordK0 cK hcK j k u hLB)
    πk (fun _ _ ↦ 1) hΓk
    (fun c hc j r hr u hLB ↦ by
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
      have hπ : πk j (ofPowerSeries ℤ kk (Yk j k)) = (j, Fin.cast hnk k) :=
        (hYkinj' j).extend_apply _ _ k
      simp only [hπ] at hLB
      simp only [one_mul]
      exact hordk0 c hc j k u hLB)
    m s ℓ hm hs hℓ1 hℓ γk hγk0 hγk' Ξ hΞ0 hΞ'
  refine ⟨γ, hγ0, (SK.divGEU_iff (K := KK) (fun j ↦ ι (α j)) (fun j k ↦ ι (yΓ j k)) YK
    hYKprod hYK2 hyK₀ _ _ γ).mpr ?_⟩
  have hms : (fun j ↦ Function.extend (fun k ↦ ofPowerSeries ℤ KK (YK j k))
      (fun k ↦ (m * s) * ΓC j k) 0) = fun j r ↦ (m * s) * ΓK j r :=
    funext fun j ↦ extend_mul_left _ _ _
  rw [hms]
  exact hγ

end UnramPrime

end Curves
