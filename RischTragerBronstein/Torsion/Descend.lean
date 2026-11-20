import RischTragerBronstein.Torsion.DescendHelp

/-!
# Prime-to-`p` torsion is detected modulo `p` (general curves)

`torsion_descendsG`: let `O` be a Henselian discrete valuation ring with fraction field `K₀` and
residue field `𝕜`, `F ∈ O[x][Y]` monic with curves `SK` over `K₀` and `Sk` over `𝕜` (good reduction:
an integral basis `Bⱼ/D` over `O` which is an integral basis over both fields, and `g` non-special
base fibres). Let `Γ − c ∞ₓ` be a divisor supported above points `α_j ∈ O` (distinct modulo `ϖ`),
given along branch systems over both fields with compatible place data. If the reduction of the
class is trivial (`γk`) and `ℓ` times the class is trivial over `K₀` (`Ξ`, `ℓ` a unit of `O`), then
the class is trivial over `K₀`.
-/

open Polynomial HahnSeries IntermediateField

namespace Curves

open Differential LaurentSeries GTors

section Descend

variable {O K₀ : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [HenselianRing O (IsLocalRing.maximalIdeal O)] [Field K₀] [Algebra O K₀] [IsFractionRing O K₀]
variable {LK KK Lk kk : Type*} [Field LK] [Algebra K₀ LK] [Field KK] [Algebra K₀ KK] [IsAlgClosed KK]
  [Field Lk] [Algebra (IsLocalRing.ResidueField O) Lk] [Field kk]
  [Algebra (IsLocalRing.ResidueField O) kk] [IsAlgClosed kk]

local notation "𝕜" => IsLocalRing.ResidueField O
local notation "ρ" => IsLocalRing.residue O
local notation "ι" => algebraMap O K₀

set_option maxHeartbeats 2000000 in
/-- **Prime-to-`p` torsion descends** (general curves). -/
theorem torsion_descendsG {ϖ : O} (hϖ : Irreducible ϖ) (F : O[X][X]) (hF : F.Monic)
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
    -- the divisor `Γ`
    {J : Type*} [Fintype J] (α : J → O) (hα : ∀ j j', j ≠ j' → IsUnit (α j - α j'))
    (hαx : ∀ j i, IsUnit (α j - x i))
    (NK : J → ℕ) (hNK : ∀ j, 0 < NK j) (lK : J → List (LaurentSeries KK))
    (hlK : ∀ j, SK.F.map (branchSub (NK j) (algebraMap K₀ KK (ι (α j)))) =
      ((lK j).map fun r ↦ X - Polynomial.C r).prod)
    (ΓK : J → LaurentSeries KK → ℕ)
    (Nk : J → ℕ) (hNk : ∀ j, 0 < Nk j) (lk : J → List (LaurentSeries kk))
    (hlk : ∀ j, Sk.F.map (branchSub (Nk j) (algebraMap 𝕜 kk (ρ (α j)))) =
      ((lk j).map fun r ↦ X - Polynomial.C r).prod)
    (Γk : J → LaurentSeries kk → ℕ)
    (cΓ : ℕ) (c' dΓ : J → ℕ) (hdK : ∀ j, ((lK j).map (ΓK j)).sum = NK j * dΓ j)
    (hdk : ∀ j, ((lk j).map (Γk j)).sum = Nk j * dΓ j)
    (hsumΓ : ∑ j, dΓ j = cΓ * SK.F.natDegree) (hle : ∀ j, dΓ j ≤ SK.F.natDegree * c' j)
    -- place representatives over `K₀`
    {P : Type*} [Fintype P] (pj : P → J) (e : P → ℕ) (he : ∀ π, 0 < e π)
    (mP : P → ℕ) (hmP : ∑ π, mP π = ∑ j, (SK.F.natDegree * c' j - dΓ j))
    (σK : P → Fin SK.F.natDegree → LaurentSeries K₀) (hσ : ∀ π j, LowerBd (σK π j) 0)
    (hrepK : ∀ cK : Fin SK.F.natDegree → K₀[X], cK ≠ 0 →
      (∀ π, LowerBd (∑ j, branchSub (K := K₀) (e π) (ι (α (pj π))) (cK j) * σK π j) (mP π)) →
      ∀ j r (hr : r ∈ lK j), ((c' j * NK j : ℕ) : ℤ) - ΓK j r ≤
        (SK.embG (branchSub (NK j) (algebraMap K₀ KK (ι (α j)))) (branchSub_injective _ (hNK j) _)
          r (SK.root_of_mem (hlK j) hr) (SK.elt (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) cK)).order)
    (hredk : ∀ c : Fin SK.F.natDegree → O[X], (¬ ∀ j, Polynomial.C ϖ ∣ c j) →
      (∀ π, LowerBd (∑ j, branchSub (K := K₀) (e π) (ι (α (pj π))) ((c j).map ι) * σK π j) (mP π)) →
      ∀ j r (hr : r ∈ lk j), ((c' j * Nk j : ℕ) : ℤ) - Γk j r ≤
        (Sk.embG (branchSub (Nk j) (algebraMap 𝕜 kk (ρ (α j)))) (branchSub_injective _ (hNk j) _)
          r (Sk.root_of_mem (hlk j) hr) (Sk.elt (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ))
            (D.map ρ) (fun j ↦ (c (Fin.cast hnk j)).map ρ))).order)
    -- the reduction of the class is trivial
    (γk : 𝕜⟮Sk.x⟯⟮Sk.y⟯) (hγk0 : γk ≠ 0)
    (hγk : Sk.DivGE (fun j ↦ ρ (α j)) Nk hNk lk hlk Γk cΓ γk)
    -- `ℓ` times the class is trivial
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ : IsUnit (ℓ : O)) (Ξ : K₀⟮SK.x⟯⟮SK.y⟯) (hΞ0 : Ξ ≠ 0)
    (hΞ : SK.DivGE (fun j ↦ ι (α j)) NK hNK lK hlK (fun j r ↦ ℓ * ΓK j r) (ℓ * cΓ) Ξ) :
    ∃ γ : K₀⟮SK.x⟯⟮SK.y⟯, γ ≠ 0 ∧ SK.DivGE (fun j ↦ ι (α j)) NK hNK lK hlK ΓK cΓ γ := by
  classical
  -- basic facts
  have hιi : Function.Injective ι := IsFractionRing.injective O K₀
  have hFn : F.natDegree = SK.F.natDegree := by rw [hSK, hF.natDegree_map]
  have hunitk : ∀ z : O, IsUnit z → ρ z ≠ 0 := fun z hz ↦ (hz.map ρ).ne_zero
  have hcΓ : cΓ ≤ ∑ j, c' j := by
    have h1 : cΓ * SK.F.natDegree ≤ (∑ j, c' j) * SK.F.natDegree := by
      rw [← hsumΓ, Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ ↦ by rw [mul_comm]; exact hle j
    exact Nat.le_of_mul_le_mul_right h1 hn
  set M := ∑ j, c' j + g - cΓ with hM_def
  have hM : M + cΓ = ∑ j, c' j + g := by omega
  have hcount := count_ineq c' dΓ δ hn hδ0 hδ hg hle hsumΓ hM
  -- differences of the fibre roots are units
  have hydiff : ∀ i k l, k ≠ l → IsUnit (y i k - y i l) := by
    intro i k l hkl
    have h := hFu i k
    rw [Sup.evalW, ← Polynomial.derivative_map, hsplit i,
      Sup.derivative_prod_X_sub_C_eval (fun l ↦ y i l) k] at h
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j ↦ y i k - y i j)
      (Finset.mem_erase.mpr ⟨Ne.symm hkl, Finset.mem_univ l⟩)) h
  -- S1: the auxiliary function over `K₀`
  obtain ⟨cK, hcK0, hcKdeg, hcKrep, hcKpt⟩ := exists_psi (C := K₀) hn
    (fun j ↦ (B j).map (mapRingHom ι)) δ M e (fun π ↦ ι (α (pj π))) σK hσ mP
    (fun i ↦ ι (x i)) (fun i k ↦ ι (y i k)) (by rw [hmP]; exact hcount)
  -- S2: primitive coordinates over `O`
  obtain ⟨cO, μ, hμ, hcOmap, hprim⟩ := descend_coords hϖ cK hcK0
  set cOK : Fin SK.F.natDegree → K₀[X] := fun j ↦ (cO j).map ι with hcOK
  have hcOKeq : cOK = fun j ↦ Polynomial.C μ * cK j := funext hcOmap
  have hbsC : ∀ (N : ℕ) (a : K₀), branchSub (K := K₀) N a (Polynomial.C μ) = HahnSeries.C μ := by
    intro N a; rw [bs_C]; rfl
  have hcOKrep : ∀ π, LowerBd (∑ j, branchSub (K := K₀) (e π) (ι (α (pj π))) (cOK j) * σK π j)
      (mP π) := by
    intro π
    have : (∑ j, branchSub (K := K₀) (e π) (ι (α (pj π))) (cOK j) * σK π j) =
        HahnSeries.C μ * ∑ j, branchSub (K := K₀) (e π) (ι (α (pj π))) (cK j) * σK π j := by
      rw [hcOKeq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [map_mul, hbsC, mul_assoc]
    rw [this]
    simpa using (lowerBd_C μ).mul (hcKrep π)
  have hcOK0 : cOK ≠ 0 := by
    rw [hcOKeq]; intro h; apply hcK0; funext j
    have := congrFun h j
    simp only [Pi.zero_apply, mul_eq_zero, Polynomial.C_eq_zero] at this
    exact this.resolve_left hμ
  have hcOKdeg : ∀ j, cOK j ≠ 0 → (cOK j).natDegree + δ j ≤ M := by
    intro j hj
    rw [hcOKeq] at hj ⊢
    have hj' : cK j ≠ 0 := fun h ↦ hj (by simp [h])
    simp only
    rw [natDegree_C_mul hμ]
    exact hcKdeg j hj'
  set W : O[X][X] := PsiC B cO with hW
  have hWK : PsiC (fun j ↦ (B j).map (mapRingHom ι)) cOK = W.map (mapRingHom ι) := by
    rw [hW, PsiC_map]
  have hvxO : ∀ i (k : Fin SK.F.natDegree), (k : ℕ) ≠ 0 → Sup.evalW W (x i) (y i k) = 0 := by
    intro i k hk
    apply hιi
    rw [map_zero, ← evalW_mapG, ← hWK, hcOKeq, evalW_PsiC]
    have := hcKpt i k hk
    rw [evalW_PsiC] at this
    simp only [eval_mul, eval_C, mul_assoc, ← Finset.mul_sum, this, mul_zero]
  -- S3 (over `K₀`): vanishing on the complementary divisor
  have hvTK := hrepK cOK hcOK0 hcOKrep
  -- the reduction modulo `ϖ`
  have hnS : 0 < Sk.F.natDegree := by rw [hnk]; exact hn
  set ck : Fin Sk.F.natDegree → 𝕜[X] := fun j ↦ (cO (Fin.cast hnk j)).map ρ with hck
  have hWk : PsiC (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ)) ck = W.map (mapRingHom ρ) := by
    rw [hck, PsiC_cast hnk (fun j ↦ (B j).map (mapRingHom ρ)) (fun j ↦ (cO j).map ρ), hW, PsiC_map]
  have hck0 : ck ≠ 0 := by
    intro h
    apply hprim
    intro j
    rw [Jac.C_dvd_iff_map hϖ]
    have := congrFun h (Fin.cast hnk.symm j)
    simpa [hck] using this
  have hckdeg : ∀ j, ck j ≠ 0 → (ck j).natDegree + δ (Fin.cast hnk j) ≤ M := by
    intro j hj
    have hcO : cO (Fin.cast hnk j) ≠ 0 := fun h ↦ hj (by simp [hck, h])
    have h1 : cOK (Fin.cast hnk j) ≠ 0 := by
      simp only [hcOK]; exact (Polynomial.map_ne_zero_iff hιi).mpr hcO
    have h2 := hcOKdeg _ h1
    have h3 : (ck j).natDegree ≤ (cOK (Fin.cast hnk j)).natDegree := by
      simp only [hck, hcOK]; rw [natDegree_map_eq_of_injective hιi]; exact natDegree_map_le
    omega
  have hαk : Function.Injective fun j ↦ ρ (α j) := by
    intro a b hab
    by_contra hne
    exact hunitk _ (hα a b hne) (by rw [map_sub, sub_eq_zero]; exact hab)
  have hxk : Function.Injective fun i ↦ ρ (x i) := by
    intro a b hab
    by_contra hne
    exact hunitk _ (hx a b hne) (by rw [map_sub, sub_eq_zero]; exact hab)
  have hxαk : ∀ i j, ρ (x i) ≠ ρ (α j) := fun i j h ↦
    hunitk _ (hαx j i) (by rw [map_sub, sub_eq_zero]; exact h.symm)
  have hykinj : ∀ i, Function.Injective fun k : Fin Sk.F.natDegree ↦
      algebraMap 𝕜 kk (ρ (y i (Fin.cast hnk k))) := by
    intro i a b hab
    by_contra hne
    have hne' : Fin.cast hnk a ≠ Fin.cast hnk b := fun h ↦ hne (Fin.cast_injective hnk h)
    exact hunitk _ (hydiff i _ _ hne') (by
      rw [map_sub, sub_eq_zero]; exact (algebraMap 𝕜 kk).injective hab)
  have hsplitk : ∀ i, F.map (evalRingHom (x i)) =
      ∏ k : Fin Sk.F.natDegree, (X - Polynomial.C (y i (Fin.cast hnk k))) := fun i ↦ by
    rw [prod_cast hnk (fun k ↦ X - Polynomial.C (y i k))]; exact hsplit i
  choose Yk hYk1 hYk2 hYk3 hYk4 using fun i ↦ Sk.unram_system (Kb := kk) F ρ hSk (x i)
    (fun k ↦ y i (Fin.cast hnk k)) (hsplitk i)
    (fun k ↦ (map_ne_zero_iff _ (algebraMap 𝕜 kk).injective).mpr (hunitk _ (hFu i _)))
    (hykinj i)
  have hvTk := hredk cO hprim hcOKrep
  have hvxk : ∀ i (k : Fin Sk.F.natDegree), (k : ℕ) ≠ 0 →
      Sup.evalW (PsiC (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ)) ck) (ρ (x i))
        (ρ (y i (Fin.cast hnk k))) = 0 := by
    intro i k hk
    rw [hWk, ← residue_evalW, hvxO i _ hk, map_zero]
  have hNSk : ∀ q : Fin Sk.F.natDegree → 𝕜[X], (∀ j, q j ≠ 0 → (q j).natDegree +
      δ (Fin.cast hnk j) ≤ g) →
      (∀ i (k : Fin Sk.F.natDegree), (k : ℕ) ≠ 0 → Sup.evalW (PsiC (fun j ↦ (B (Fin.cast hnk j)).map
        (mapRingHom ρ)) q) (ρ (x i)) (ρ (y i (Fin.cast hnk k))) = 0) →
      ∀ i, Sup.evalW (PsiC (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ)) q) (ρ (x i))
        (ρ (y i (Fin.cast hnk ⟨0, hnS⟩))) = 0 := by
    intro q hq hv i
    set q' : Fin SK.F.natDegree → 𝕜[X] := fun j ↦ q (Fin.cast hnk.symm j) with hq'
    have hPq : PsiC (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ)) q =
        PsiC (fun j ↦ (B j).map (mapRingHom ρ)) q' := by
      rw [← PsiC_cast hnk (fun j ↦ (B j).map (mapRingHom ρ)) q']
      simp [hq']
    have h0 : Fin.cast hnk (⟨0, hnS⟩ : Fin Sk.F.natDegree) = ⟨0, hn⟩ := Fin.ext rfl
    rw [hPq, h0]
    refine hNS q' (fun j hj ↦ ?_) (fun i' k hk ↦ ?_) i
    · have := hq (Fin.cast hnk.symm j) hj
      simpa [hq'] using this
    · have := hv i' (Fin.cast hnk.symm k) hk
      rw [hPq] at this
      simpa using this
  have hDxk : ∀ i, (D.map ρ).eval (ρ (x i)) ≠ 0 := fun i ↦ by
    rw [eval_map, eval₂_hom]; exact hunitk _ (hDx i)
  have hsumΓk : ∑ j, dΓ j = cΓ * Sk.F.natDegree := by rw [hnk]; exact hsumΓ
  have hmk : (PsiC (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ)) ck).natDegree ≤ W.natDegree := by
    rw [hWk]; exact natDegree_map_le
  obtain ⟨hred1, hred2, hred3⟩ := Sk.reduced_sideG hBrk hBIk hBk ck hck0 M hckdeg
    (fun j ↦ ρ (α j)) hαk Nk hNk lk hlk Γk cΓ c' dΓ hdk hsumΓk (fun i ↦ ρ (x i)) hxk hxαk
    (fun i k ↦ ρ (y i (Fin.cast hnk k))) Yk hYk1 hYk2 hYk4 hYk3 hDxk hnS hM hvTk hvxk γk hγk0 hγk
    hNSk W.natDegree hmk
  -- S4 (over `K₀`): the norm is divisible by the expected factor
  have hαK : Function.Injective fun j ↦ ι (α j) := fun a b h ↦ hαk (by
    show ρ (α a) = ρ (α b); rw [hιi h])
  have hxK : Function.Injective fun i ↦ ι (x i) := fun a b h ↦ hxk (by
    show ρ (x a) = ρ (x b); rw [hιi h])
  have hxαK : ∀ i j, ι (x i) ≠ ι (α j) := fun i j h ↦ hxαk i j (by rw [hιi h])
  have hykK : ∀ i, Function.Injective fun k : Fin SK.F.natDegree ↦ algebraMap K₀ KK (ι (y i k)) := by
    intro i a b hab
    by_contra hne
    exact hunitk _ (hydiff i _ _ hne) (by
      rw [map_sub, sub_eq_zero, hιi ((algebraMap K₀ KK).injective hab)])
  choose YK hYK1 hYK2 hYK3 hYK4 using fun i ↦ SK.unram_system (Kb := KK) F ι hSK (x i) (y i)
    (hsplit i) (fun k ↦ (map_ne_zero_iff _ (algebraMap K₀ KK).injective).mpr
      ((map_ne_zero_iff _ hιi).mpr (hFu i k).ne_zero)) (hykK i)
  have hDxK : ∀ i, (D.map ι).eval (ι (x i)) ≠ 0 := fun i ↦ by
    rw [eval_map, eval₂_hom]; exact (map_ne_zero_iff _ hιi).mpr (hDx i).ne_zero
  have hvxK : ∀ i (k : Fin SK.F.natDegree), (k : ℕ) ≠ 0 →
      Sup.evalW (PsiC (fun j ↦ (B j).map (mapRingHom ι)) cOK) (ι (x i)) (ι (y i k)) = 0 := by
    intro i k hk
    rw [hWK, evalW_mapG, hvxO i k hk, map_zero]
  have hmK : (PsiC (fun j ↦ (B j).map (mapRingHom ι)) cOK).natDegree ≤ W.natDegree := by
    rw [hWK]; exact natDegree_map_le
  obtain ⟨hdvdK, hdegK⟩ := SK.norm_dvd_sideG hBrK hBIK hBK (hDm.map ι) cOK hcOK0 M hcOKdeg
    (fun j ↦ ι (α j)) hαK NK hNK lK hlK ΓK c' dΓ hdK hle (fun i ↦ ι (x i)) hxK hxαK
    (fun i k ↦ ι (y i k)) YK hYK1 hYK2 hYK4 hDxK hn hvTK hvxK W.natDegree hmK
  set N0 := resultant F W F.natDegree W.natDegree with hN0
  have hnormK : SK.normW (PsiC (fun j ↦ (B j).map (mapRingHom ι)) cOK) W.natDegree = N0.map ι := by
    rw [hWK]; exact SK.normW_map ι F W hF hSK _
  have hnormk : Sk.normW (PsiC (fun j ↦ (B (Fin.cast hnk j)).map (mapRingHom ρ)) ck) W.natDegree =
      N0.map ρ := by
    rw [hWk]; exact Sk.normW_map ρ F W hF hSk _
  set E : O[X] := D ^ SK.F.natDegree *
    ∏ j, (X - Polynomial.C (α j)) ^ (SK.F.natDegree * c' j - dΓ j) with hE
  set P2 : O[X] := ∏ i, (X - Polynomial.C (x i)) ^ (SK.F.natDegree - 1) with hP2
  have hEm : E.Monic := (hDm.pow _).mul (monic_prod_of_monic _ _ fun j _ ↦ (monic_X_sub_C _).pow _)
  have hP2m : P2.Monic := monic_prod_of_monic _ _ fun j _ ↦ (monic_X_sub_C _).pow _
  have hEP : (E * P2).map ι = (D.map ι) ^ SK.F.natDegree * (∏ j, (X - Polynomial.C (ι (α j))) ^
      (SK.F.natDegree * c' j - dΓ j)) * ∏ i, (X - Polynomial.C (ι (x i))) ^ (SK.F.natDegree - 1) := by
    simp only [hE, hP2, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_prod,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hdvdO : E * P2 ∣ N0 := by
    rw [← Polynomial.map_dvd_map ι hιi (hEm.mul hP2m), hEP, ← hnormK]; exact hdvdK
  obtain ⟨R, hR⟩ := hdvdO
  -- the reduced norm has multiplicity `n` at the base abscissae
  have hmultk : ∀ i, (N0.map ρ).rootMultiplicity (ρ (x i)) = SK.F.natDegree := by
    intro i
    rw [eq_rootMultiplicity_map (algebraMap 𝕜 kk).injective, ← hnormk, hred2 i, hnk]
  have hNk0 : N0.map ρ ≠ 0 ∨ g = 0 := by
    rcases Nat.eq_zero_or_pos g with hg0 | hgpos
    · exact Or.inr hg0
    · left
      intro h
      have := hmultk ⟨0, hgpos⟩
      rw [h, rootMultiplicity_zero] at this
      omega
  -- the norm is non-zero and `deg R ≤ g`
  have hψK0 : SK.elt (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) cOK ≠ 0 :=
    fun h ↦ hcOK0 (CurveData.elt_eq_zero hBK.hD hBK.deg hBK.det cOK h)
  have hWKne : SK.evXY (PsiC (fun j ↦ (B j).map (mapRingHom ι)) cOK) ≠ 0 := by
    have := SK.fnWQ_mul (PsiC (fun j ↦ (B j).map (mapRingHom ι)) cOK) (D.map ι) hBK.hD
    intro h0
    rw [h0, ← CurveData.elt_eq_fnWQ] at this
    exact hψK0 (Subtype.ext ((mul_eq_zero.mp this).resolve_right (fun h ↦ hBK.hD
      (transcendental_iff.mp SK.htr _ h))))
  have hN00 : N0 ≠ 0 := by
    obtain ⟨Nz, hNz, lz, -, hlz⟩ := hBrK 0
    have hlz' : SK.F.map (branchSub Nz (0 : KK)) =
        ((lz.map (ofPowerSeries ℤ KK)).map fun r ↦ X - Polynomial.C r).prod := by
      rw [hlz, List.map_map]; rfl
    have := SK.normW_ne_zero _ W.natDegree hmK hWKne _
      (branchSub_injective Nz (Nat.pos_of_ne_zero hNz) 0) _ hlz'
    rw [hnormK] at this
    exact fun h ↦ this (by rw [h, Polynomial.map_zero])
  have hR0 : R ≠ 0 := by rintro rfl; rw [mul_zero] at hR; exact hN00 hR
  have hRdeg : R.natDegree ≤ g := by
    have h1 : N0.natDegree ≤ SK.F.natDegree * (M + D.natDegree) := by
      rw [← natDegree_map_eq_of_injective hιi, ← hnormK]
      have := hdegK
      rwa [hDm.natDegree_map] at this
    have h2 : (E * P2).natDegree = SK.F.natDegree * D.natDegree +
        ∑ j, (SK.F.natDegree * c' j - dΓ j) + g * (SK.F.natDegree - 1) := by
      rw [← natDegree_map_eq_of_injective hιi, hEP, natDegree_mul, natDegree_mul, natDegree_pow,
        hDm.natDegree_map, natDegree_prodPow, natDegree_prodPow]
      · simp [mul_comm]
      · exact pow_ne_zero _ (hDm.map ι).ne_zero
      · exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
      · exact mul_ne_zero (pow_ne_zero _ (hDm.map ι).ne_zero)
          (Finset.prod_ne_zero_iff.mpr fun j _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _))
      · exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
    have h3 : N0.natDegree = (E * P2).natDegree + R.natDegree := by
      rw [hR, natDegree_mul (hEm.mul hP2m).ne_zero hR0]
    have h4 : ∑ j, (SK.F.natDegree * c' j - dΓ j) = SK.F.natDegree * ∑ j, c' j -
        cΓ * SK.F.natDegree := by
      rw [Finset.sum_tsub_distrib _ fun j _ ↦ hle j, ← Finset.mul_sum, hsumΓ]
    have h5 : cΓ * SK.F.natDegree ≤ SK.F.natDegree * ∑ j, c' j := by
      rw [mul_comm]; exact Nat.mul_le_mul_left _ hcΓ
    rw [h3, h2, h4] at h1
    have hM' : M + cΓ = ∑ j, c' j + g := hM
    have hn1 : 1 ≤ SK.F.natDegree := hn
    zify [h5, hn1] at h1
    have hM'' : (M : ℤ) + cΓ = ∑ j, (c' j : ℤ) + g := by exact_mod_cast hM'
    push_cast at h1
    have h6 : (SK.F.natDegree : ℤ) * M + SK.F.natDegree * cΓ =
        SK.F.natDegree * ∑ j, (c' j : ℤ) + SK.F.natDegree * g := by
      rw [← mul_add, hM'', mul_add]
    linarith [h6]
  -- the reduction of `R` has simple roots at the base abscissae
  have hRk : ∀ i, (R.map ρ).IsRoot (ρ (x i)) ∧ ¬ (derivative (R.map ρ)).IsRoot (ρ (x i)) := by
    intro i
    have hNk0' : N0.map ρ ≠ 0 := hNk0.resolve_right (fun h ↦ by subst h; exact i.elim0)
    have hEPk0 : (E * P2).map ρ ≠ 0 := ((hEm.mul hP2m).map ρ).ne_zero
    have hsplitN : N0.map ρ = (E * P2).map ρ * R.map ρ := by rw [hR, Polynomial.map_mul]
    have h1 := hmultk i
    rw [hsplitN, rootMultiplicity_mul (hsplitN ▸ hNk0')] at h1
    have h2 : ((E * P2).map ρ).rootMultiplicity (ρ (x i)) = SK.F.natDegree - 1 := by
      have hEPk : (E * P2).map ρ = (D.map ρ) ^ SK.F.natDegree * (∏ j, (X - Polynomial.C (ρ (α j))) ^
          (SK.F.natDegree * c' j - dΓ j)) * ∏ i, (X - Polynomial.C (ρ (x i))) ^
            (SK.F.natDegree - 1) := by
        simp only [hE, hP2, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_prod,
          Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      have hD0 : (D.map ρ).rootMultiplicity (ρ (x i)) = 0 := by
        rw [rootMultiplicity_eq_zero]; exact hDxk i
      rw [hEPk, rootMultiplicity_mul (hEPk ▸ hEPk0), rootMultiplicity_mul, rootMultiplicity_pow' _
        (hDm.map ρ).ne_zero, hD0, rootMultiplicity_prodPow_off _ _ _ (by
          rintro ⟨j, hj⟩; exact hxαk i j hj.symm),
        rootMultiplicity_prodPow_pt _ hxk _ i]
      · simp
      · exact mul_ne_zero (pow_ne_zero _ (hDm.map ρ).ne_zero)
          (Finset.prod_ne_zero_iff.mpr fun j _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _))
    rw [h2] at h1
    exact root_simple_of_mult_one (by omega)
  -- simple zeros modulo `ϖ` at the complementary base points
  have hsimple : ∀ i (k : Fin SK.F.natDegree), (k : ℕ) ≠ 0 →
      ¬ VanishAtG (F.map (mapRingHom ρ)) (W.map (mapRingHom ρ)) (ρ (x i)) (ρ (y i k)) 2 := by
    intro i k _ hv
    have h1 := hred1 i (Fin.cast hnk.symm k)
    apply h1
    have hc : Fin.cast hnk (Fin.cast hnk.symm k) = k := Fin.ext rfl
    simp only [hc]
    have e1 : Sk.F.map (mapRingHom (algebraMap 𝕜 kk)) =
        (F.map (mapRingHom ρ)).map (mapRingHom (algebraMap 𝕜 kk)) := by rw [hSk]
    rw [e1, hWk]
    exact hv.map (algebraMap 𝕜 kk)
  have hFx0 : ∀ i k, Sup.evalW F (x i) (y i k) = 0 := fun i k ↦ by
    rw [Sup.evalW, hsplit i, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  have hNR : resultant F W SK.F.natDegree W.natDegree =
      E * (∏ i, (X - Polynomial.C (x i)) ^ (SK.F.natDegree - 1)) * R := by
    rw [show resultant F W SK.F.natDegree W.natDegree = N0 by rw [hN0, hFn], hR]
  have hres := residual_zerosG hϖ F hF SK.F.natDegree hFn hn W W.natDegree le_rfl x hx y hsplit hFu
    E R hNR hRdeg hRk hvxO hsimple
  set φ : O →+* KK := (algebraMap K₀ KK).comp ι with hφdef
  have hφ : Function.Injective φ := (algebraMap K₀ KK).injective.comp hιi
  have eF : (F.map (mapRingHom ι)).map (mapRingHom (algebraMap K₀ KK)) = F.map (mapRingHom φ) := by
    rw [Polynomial.map_map, Polynomial.mapRingHom_comp]
  have hφu : ∀ a b, IsUnit (Sup.evalW (derivative F) a b) →
      IsUnit (Sup.evalW (derivative (F.map (mapRingHom φ))) (φ a) (φ b)) := by
    intro a b h
    rw [Polynomial.derivative_map, evalW_mapG]
    exact h.map φ
  -- the zeros `Qᵢ ≡ Pᵢ`
  have hQ : ∀ i, ∃ (z : O) (Yv : Fin SK.F.natDegree → O), ϖ ∣ z - x i ∧ (∀ k, ϖ ∣ Yv k - y i k) ∧
      F.map (evalRingHom z) = ∏ k, (X - Polynomial.C (Yv k)) ∧ Sup.evalW W z (Yv ⟨0, hn⟩) = 0 := by
    intro i
    rcases hres i with h | hRx
    · exact h
    refine ⟨x i, y i, by simp, fun k ↦ by simp, hsplit i, ?_⟩
    have hdvd : (X - Polynomial.C (x i)) ^ SK.F.natDegree ∣ N0 := by
      rw [hR, hP2]
      have h1 : (X - Polynomial.C (x i)) ^ (SK.F.natDegree - 1) ∣
          ∏ i, (X - Polynomial.C (x i)) ^ (SK.F.natDegree - 1) :=
        Finset.dvd_prod_of_mem (fun i ↦ (X - Polynomial.C (x i)) ^ (SK.F.natDegree - 1))
          (Finset.mem_univ i)
      calc (X - Polynomial.C (x i)) ^ SK.F.natDegree =
          (X - Polynomial.C (x i)) ^ (SK.F.natDegree - 1) * (X - Polynomial.C (x i)) := by
            rw [← pow_succ, Nat.sub_add_cancel hn]
        _ ∣ E * (∏ i, (X - Polynomial.C (x i)) ^ (SK.F.natDegree - 1)) * R :=
            mul_dvd_mul (dvd_mul_of_dvd_right h1 E) (dvd_iff_isRoot.mpr hRx)
    have hmult : SK.F.natDegree ≤ ((SK.normW (PsiC (fun j ↦ (B j).map (mapRingHom ι)) cOK)
        W.natDegree).map (algebraMap K₀ KK)).rootMultiplicity (algebraMap K₀ KK (ι (x i))) := by
      have hne : (N0.map ι).map (algebraMap K₀ KK) ≠ 0 := by
        rw [Polynomial.map_map]; exact (Polynomial.map_ne_zero_iff hφ).mpr hN00
      rw [hnormK, le_rootMultiplicity_iff hne, Polynomial.map_map]
      have := Polynomial.map_dvd φ hdvd
      rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at this
      exact this
    have hsimK : ∀ k, k ≠ (⟨0, hn⟩ : Fin SK.F.natDegree) → ¬ VanishAtG
        (SK.F.map (mapRingHom (algebraMap K₀ KK)))
        ((PsiC (fun j ↦ (B j).map (mapRingHom ι)) cOK).map (mapRingHom (algebraMap K₀ KK)))
        (algebraMap K₀ KK (ι (x i))) (algebraMap K₀ KK (ι (y i k))) 2 := by
      intro k hk hv
      have hk' : (k : ℕ) ≠ 0 := fun h ↦ hk (Fin.ext h)
      obtain ⟨V, hV⟩ := exists_branchG (hFx0 i k) (hFu i k) 2
      have h1 := jet_coeff_one_unit F W hV (hvxO i k hk') (hsimple i k hk')
      apply not_vanish2_of_unit hV (hFu i k) h1
      refine vanishAtG_of_map φ hφ hV (hφu _ _ (hFu i k)) ?_
      have eW : (W.map (mapRingHom ι)).map (mapRingHom (algebraMap K₀ KK)) =
          W.map (mapRingHom φ) := by
        rw [Polynomial.map_map, Polynomial.mapRingHom_comp]
      have e1 : SK.F.map (mapRingHom (algebraMap K₀ KK)) = F.map (mapRingHom φ) := by
        rw [hSK, eF]
      have e2 : (PsiC (fun j ↦ (B j).map (mapRingHom ι)) cOK).map (mapRingHom (algebraMap K₀ KK)) =
          W.map (mapRingHom φ) := by rw [hWK, eW]
      rw [e1, e2] at hv
      exact hv
    have hbv := SK.base_vanishG (PsiC (fun j ↦ (B j).map (mapRingHom ι)) cOK) W.natDegree hmK hWKne
      (ι (x i)) (fun k ↦ ι (y i k)) (YK i) (hYK1 i) (hYK2 i)
      (by rw [hYK4 i, List.map_ofFn, List.prod_ofFn]; rfl) (hYK3 i) hmult ⟨0, hn⟩ hsimK
    rw [hWK, evalW_mapG] at hbv
    exact (map_eq_zero_iff _ hιi).mp hbv
  choose z Yv hzx hYvy hzsplit hzW using hQ
  have hmax : ∀ w : O, ϖ ∣ w → w ∈ IsLocalRing.maximalIdeal O := fun w h ↦
    (mem_max_iff_dvdG hϖ w).mpr h
  -- the fibres above the `zᵢ`
  have hFz0 : ∀ i k, Sup.evalW F (z i) (Yv i k) = 0 := fun i k ↦ by
    rw [Sup.evalW, hzsplit i, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  have hFzu : ∀ i k, IsUnit (Sup.evalW (derivative F) (z i) (Yv i k)) := by
    intro i k
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, residue_evalW,
      Sup.residue_eq_of_sub_mem (hmax _ (hzx i)), Sup.residue_eq_of_sub_mem (hmax _ (hYvy i k)),
      ← residue_evalW]
    exact hunitk _ (hFu i k)
  have hYvdiff : ∀ i k l, k ≠ l → IsUnit (Yv i k - Yv i l) := by
    intro i k l hkl
    have h1 := Sup.unit_add_mem (hydiff i k l hkl) (Ideal.sub_mem _ (hmax _ (hYvy i k))
      (hmax _ (hYvy i l)))
    rwa [show y i k - y i l + ((Yv i k - y i k) - (Yv i l - y i l)) = Yv i k - Yv i l by ring] at h1
  have hYvK : ∀ i, Function.Injective fun k : Fin SK.F.natDegree ↦ algebraMap K₀ KK (ι (Yv i k)) := by
    intro i a b hab
    by_contra hne
    exact (hYvdiff i _ _ hne).ne_zero (by
      rw [sub_eq_zero, hιi ((algebraMap K₀ KK).injective hab)])
  choose YZ hYZ1 hYZ2 hYZ3 hYZ4 using fun i ↦ SK.unram_system (Kb := KK) F ι hSK (z i) (Yv i)
    (hzsplit i) (fun k ↦ (map_ne_zero_iff _ (algebraMap K₀ KK).injective).mpr
      ((map_ne_zero_iff _ hιi).mpr (hFzu i k).ne_zero)) (hYvK i)
  have hDzK : ∀ i, (D.map ι).eval (ι (z i)) ≠ 0 := by
    intro i
    rw [eval_map, eval₂_hom]
    refine (map_ne_zero_iff _ hιi).mpr (IsUnit.ne_zero ?_)
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← eval₂_hom, ← eval_map,
      Sup.residue_eq_of_sub_mem (hmax _ (hzx i)), eval_map, eval₂_hom]
    exact hunitk _ (hDx i)
  have hzα : ∀ i, algebraMap K₀ KK (ι (z i)) ∉ Set.range fun j ↦ algebraMap K₀ KK (ι (α j)) := by
    rintro i ⟨j, hj⟩
    have h1 : α j = z i := hιi ((algebraMap K₀ KK).injective hj)
    have h2 := Sup.unit_add_mem (hαx j i) ((IsLocalRing.maximalIdeal O).neg_mem (hmax _ (hzx i)))
    rw [show α j - x i + -(z i - x i) = α j - z i by ring, h1, sub_self] at h2
    exact not_isUnit_zero h2
  have hxα' : ∀ i, algebraMap K₀ KK (ι (x i)) ∉ Set.range fun j ↦ algebraMap K₀ KK (ι (α j)) := by
    rintro i ⟨j, hj⟩
    exact hxαK i j ((algebraMap K₀ KK).injective hj.symm)
  -- `ψ` vanishes at the `Qᵢ` and at the complementary base points
  have hψQ : ∀ i, 1 ≤ (SK.embG (branchSub 1 (algebraMap K₀ KK (ι (z i))))
      (branchSub_injective 1 one_pos _) (ofPowerSeries ℤ KK (YZ i ⟨0, hn⟩))
      (SK.root_of_fibrePS _ _ (hYZ1 i _))
      (SK.elt (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) cOK)).order := by
    intro i
    rw [CurveData.elt_eq_fnWQ]
    refine (SK.one_le_order_iff_evalW _ (D.map ι) (ι (z i)) (ι (Yv i ⟨0, hn⟩)) (hDzK i) _ _
      (hYZ2 i _) (by rw [← CurveData.elt_eq_fnWQ]; exact hψK0)).mpr ?_
    rw [hWK, evalW_mapG, hzW i, map_zero]
  have hψP : ∀ i (k : Fin SK.F.natDegree), (k : ℕ) ≠ 0 →
      1 ≤ (SK.embG (branchSub 1 (algebraMap K₀ KK (ι (x i))))
      (branchSub_injective 1 one_pos _) (ofPowerSeries ℤ KK (YK i k))
      (SK.root_of_fibrePS _ _ (hYK1 i _))
      (SK.elt (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) cOK)).order := by
    intro i k hk
    rw [CurveData.elt_eq_fnWQ]
    refine (SK.one_le_order_iff_evalW _ (D.map ι) (ι (x i)) (ι (y i k)) (hDxK i) _ _
      (hYK2 i _) (by rw [← CurveData.elt_eq_fnWQ]; exact hψK0)).mpr ?_
    exact hvxK i k hk
  -- S5: the `ℓ`-th power function, with primitive coordinates
  obtain ⟨q, hq0, hqdeg, hqord⟩ := SK.ell_powerG hBK cOK hcOK0 M hcOKdeg (fun j ↦ ι (α j)) hαK NK hNK
    lK hlK ΓK cΓ c' hM hvTK ℓ Ξ hΞ0 hΞ
  obtain ⟨qO, ν, hν, hqOmap, hqprim⟩ := descend_coords hϖ q hq0
  set W2 : O[X][X] := PsiC B qO with hW2
  have hW2K : W2.map (mapRingHom ι) = Polynomial.C (Polynomial.C ν) *
      PsiC (fun j ↦ (B j).map (mapRingHom ι)) q := by
    rw [hW2, PsiC_map, ← PsiC_C_mul]
    congr 1; funext j; exact hqOmap j
  have hqelt0 : SK.elt (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) q ≠ 0 :=
    fun h ↦ hq0 (CurveData.elt_eq_zero hBK.hD hBK.deg hBK.det q h)
  have hvanO : ∀ (a b : O) (Yp : PowerSeries KK)
      (hYp : (fibrePS SK.F (algebraMap K₀ KK (ι a))).eval Yp = 0)
      (hYc : PowerSeries.constantCoeff Yp = algebraMap K₀ KK (ι b))
      (hFY : (fibreAt (derivative SK.F) (algebraMap K₀ KK (ι a))).eval
        (algebraMap K₀ KK (ι b)) ≠ 0)
      (hDa : (D.map ι).eval (ι a) ≠ 0) (hFa : Sup.evalW F a b = 0)
      (hFua : IsUnit (Sup.evalW (derivative F) a b))
      (hl : (ℓ : ℤ) ≤ (SK.embG (branchSub 1 (algebraMap K₀ KK (ι a)))
        (branchSub_injective 1 one_pos _) (ofPowerSeries ℤ KK Yp) (SK.root_of_fibrePS _ _ hYp)
        (SK.elt (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) q)).order),
      VanishAtG F W2 a b ℓ := by
    intro a b Yp hYp hYc hFY hDa hFa hFua hl
    have hq0' : SK.fnWQ (PsiC (fun j ↦ (B j).map (mapRingHom ι)) q) (D.map ι) ≠ 0 := by
      rw [← CurveData.elt_eq_fnWQ]; exact hqelt0
    rw [CurveData.elt_eq_fnWQ, ← SK.order_W_eq_fnWQ _ _ _ hDa _ _ hq0',
      CurveData.eval_branchSub_ofPS] at hl
    have hne : ofPowerSeries ℤ KK (((PsiC (fun j ↦ (B j).map (mapRingHom ι)) q).map
        (psSub 1 (algebraMap K₀ KK (ι a)))).eval Yp) ≠ 0 := by
      intro h0
      rw [h0, HahnSeries.order_zero] at hl
      have : (1 : ℤ) ≤ ℓ := by exact_mod_cast hℓ1
      linarith
    have hlb := lowerBd_of_le_order _ ℓ hl
    have hv := (lowerBd_iff_vanishAtG SK.F _ _ Yp hYp hYc hFY
      (PsiC (fun j ↦ (B j).map (mapRingHom ι)) q) ℓ).mp (by exact_mod_cast hlb)
    have hv2 := hv.C_mul (algebraMap K₀ KK ν)
    obtain ⟨V, hV⟩ := exists_branchG hFa hFua ℓ
    refine vanishAtG_of_map φ hφ hV (hφu a b hFua) ?_
    have e1 : SK.F.map (mapRingHom (algebraMap K₀ KK)) = F.map (mapRingHom φ) := by rw [hSK, eF]
    have e2 : Polynomial.C (Polynomial.C (algebraMap K₀ KK ν)) *
        (PsiC (fun j ↦ (B j).map (mapRingHom ι)) q).map (mapRingHom (algebraMap K₀ KK)) =
        W2.map (mapRingHom φ) := by
      rw [← Polynomial.mapRingHom_comp, ← Polynomial.map_map, hW2K, Polynomial.map_mul,
        Polynomial.map_C, coe_mapRingHom, Polynomial.map_C]
    rw [e1, e2] at hv2
    exact hv2
  -- S6: the kernel lemma forces `Qᵢ = Pᵢ`
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  have ht := kernel_no_torsionG hϖ hn F B D hB0 δ hδ0 hδ hℓ x hx y hFx0 hFu hdet hDx
    (fun i ↦ z i - x i) (fun i ↦ Yv i ⟨0, hn⟩) hzx (fun i ↦ hYvy i _) qO
    (fun j hj ↦ by
      have hqj : q j ≠ 0 := by
        intro h; apply hj
        apply Polynomial.map_injective _ hιi
        rw [hqOmap, h, mul_zero, Polynomial.map_zero]
      have := hqdeg j hqj
      rw [← natDegree_map_eq_of_injective hιi, hqOmap, natDegree_C_mul hν]
      exact this)
    hqprim
    (fun i ↦ by
      rw [add_sub_cancel]
      refine hvanO (z i) (Yv i ⟨0, hn⟩) (YZ i ⟨0, hn⟩) (hYZ1 i _) (hYZ2 i _) (hYZ3 i _) (hDzK i)
        (hFz0 i _) (hFzu i _) ?_
      have h1 := hqord (algebraMap K₀ KK (ι (z i))) (hzα i) 1 one_ne_zero _ (hYZ4 i)
        (ofPowerSeries ℤ KK (YZ i ⟨0, hn⟩)) (List.mem_ofFn.mpr ⟨_, rfl⟩)
      have h2 := hψQ i
      have h3 : (0 : ℤ) ≤ (m + 1 : ℕ) := by positivity
      nlinarith)
    (fun i k hk ↦ by
      refine hvanO (x i) (y i k) (YK i k) (hYK1 i _) (hYK2 i _) (hYK3 i _) (hDxK i)
        (hFx0 i _) (hFu i _) ?_
      have h1 := hqord (algebraMap K₀ KK (ι (x i))) (hxα' i) 1 one_ne_zero _ (hYK4 i)
        (ofPowerSeries ℤ KK (YK i k)) (List.mem_ofFn.mpr ⟨_, rfl⟩)
      have h2 := hψP i k hk
      have h3 : (0 : ℤ) ≤ (m + 1 : ℕ) := by positivity
      nlinarith)
    hNS
  -- S7: `ψ` vanishes on the full base fibres, hence the class is trivial
  have hzx' : ∀ i, z i = x i := fun i ↦ sub_eq_zero.mp (ht i)
  have hYv0 : ∀ i, Yv i ⟨0, hn⟩ = y i ⟨0, hn⟩ := by
    intro i
    have hr : (F.map (evalRingHom (x i))).eval (Yv i ⟨0, hn⟩) = 0 := by
      rw [← hzx' i]; exact hFz0 i _
    rw [hsplit i, eval_prod, Finset.prod_eq_zero_iff] at hr
    obtain ⟨k, -, hk⟩ := hr
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hk
    by_cases hk0 : k = ⟨0, hn⟩
    · rw [hk, hk0]
    · exfalso
      have := hYvy i ⟨0, hn⟩
      rw [hk] at this
      exact hϖ.not_isUnit (isUnit_of_dvd_unit this (hydiff i k _ hk0))
  have hW0 : ∀ i, Sup.evalW W (x i) (y i ⟨0, hn⟩) = 0 := fun i ↦ by
    rw [← hzx' i, ← hYv0 i]; exact hzW i
  have hvall : ∀ i r (hr : r ∈ List.ofFn fun k ↦ ofPowerSeries ℤ KK (YK i k)),
      1 ≤ (SK.embG (branchSub 1 (algebraMap K₀ KK (ι (x i)))) (branchSub_injective _ one_pos _) r
        (SK.root_of_mem (hYK4 i) hr)
        (SK.elt (fun j ↦ (B j).map (mapRingHom ι)) (D.map ι) cOK)).order := by
    intro i r hr
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hr
    by_cases hk : (k : ℕ) = 0
    · have e : k = ⟨0, hn⟩ := Fin.ext hk
      subst e
      rw [CurveData.elt_eq_fnWQ]
      refine (SK.one_le_order_iff_evalW _ (D.map ι) (ι (x i)) (ι (y i ⟨0, hn⟩)) (hDxK i) _ _
        (hYK2 i _) (by rw [← CurveData.elt_eq_fnWQ]; exact hψK0)).mpr ?_
      rw [hWK, evalW_mapG, hW0 i, map_zero]
    · exact hψP i k hk
  exact SK.principal_of_vanishG hBrK hBIK hBK.hD hBK.deg hBK.det hBK.reg hBK.inf cOK hcOK0 M
    hcOKdeg (fun j ↦ ι (α j)) hαK NK hNK lK hlK ΓK cΓ c' dΓ hdK hsumΓ (fun i ↦ ι (x i)) hxK hxαK
    (fun i ↦ List.ofFn fun k ↦ ofPowerSeries ℤ KK (YK i k)) hYK4 hM hvTK hvall

end Descend

end Curves
