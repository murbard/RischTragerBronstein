import RischTragerBronstein.Mixed.NKRamAlg

/-!
# The gauge at ramified places at infinity

For a curve with a single slope `s'/e` at infinity and `r` rational places (residual polynomial
`∏ₖ (Zᵉ − γₖ)`, `γₖ` distinct non-zero), an integral basis normal at infinity has a limit matrix
`Λ` that a constant gauge makes level-triangular: `A′ = Λ A − A T` with `A ∈ GLₙ(C)`, `T`
block upper triangular in the levels with diagonal `(t_R/e) γₖ′/γₖ` (`ram_gauge`). The proof
expands the basis in the monomials `θʲ/x^{⌈j s'/e⌉}` (`NKRamExpand`), takes the jets
`[T^{N' h}]` along one root per place, and applies `tri_of_TZ`.
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section Levels

lemma gR_add_mul (e sR t l : ℕ) (he : 0 < e) : gR e sR (t + e * l) = gR e sR t + l * sR := by
  unfold gR
  have : (t + e * l) * sR + e - 1 = (t * sR + e - 1) + e * (l * sR) := by
    have h1 : 1 ≤ e := he
    rw [add_mul]
    have : t * sR + e - 1 + e * (l * sR) = t * sR + e * l * sR + e - 1 := by
      rw [show e * (l * sR) = e * l * sR by ring]; omega
    rw [this]
  rw [this, Nat.add_mul_div_left _ _ he]

lemma levR_add_mul (e sR t l : ℕ) (he : 0 < e) : levR e sR (t + e * l) = levR e sR t := by
  unfold levR
  rw [gR_add_mul e sR t l he]
  have h := (gR_spec e sR t he).1
  unfold levR at h
  have : e * (gR e sR t + l * sR) = e * gR e sR t + e * l * sR := by ring
  rw [this, add_mul, show e * l * sR = e * l * sR from rfl]
  have h2 : t * sR ≤ e * gR e sR t := by unfold levR at *; omega
  omega

lemma levR_mod (e sR j : ℕ) (he : 0 < e) : levR e sR j = levR e sR (j % e) := by
  conv_lhs => rw [← Nat.mod_add_div j e]
  exact levR_add_mul e sR _ _ he

lemma levR_inj (e sR t₁ t₂ : ℕ) (he : 0 < e) (hcop : Nat.Coprime sR e) (h₁ : t₁ < e) (h₂ : t₂ < e)
    (h : levR e sR t₁ = levR e sR t₂) : t₁ = t₂ := by
  have s₁ := (gR_spec e sR t₁ he).1
  have s₂ := (gR_spec e sR t₂ he).1
  -- `t₁ sR ≡ t₂ sR (mod e)`
  have hm : t₁ * sR ≡ t₂ * sR [MOD e] := by
    have : t₁ * sR + levR e sR t₁ ≡ t₂ * sR + levR e sR t₂ [MOD e] := by
      rw [← s₁, ← s₂]; simp [Nat.ModEq, Nat.mul_mod_right]
    rw [h] at this
    exact Nat.ModEq.add_right_cancel' _ this
  have := Nat.ModEq.cancel_right_of_coprime (Nat.Coprime.symm hcop) (by
    simpa [mul_comm] using hm)
  unfold Nat.ModEq at this
  rwa [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at this

lemma exists_levR (e sR : ℕ) (he : 0 < e) (hcop : Nat.Coprime sR e) (R : ℕ) (hR : R < e) :
    ∃ t < e, levR e sR t = R := by
  have hinj : Function.Injective (fun t : Fin e ↦ (⟨levR e sR t, (gR_spec e sR t he).2⟩ : Fin e)) :=
    fun a b hab ↦ Fin.ext (levR_inj e sR a b he hcop a.2 b.2 (by simpa using congrArg Fin.val hab))
  obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨R, hR⟩
  exact ⟨t, t.2, by simpa using congrArg Fin.val ht⟩


/-- **Summing over the monomials of level `R`**: `j = t_R + e l`, `l < r`. -/
lemma sum_lev {M : Type*} [AddCommMonoid M] (e sR r : ℕ) (he : 0 < e) (hcop : Nat.Coprime sR e)
    (R : ℕ) (hR : R < e) (F : ℕ → M) :
    ∑ j ∈ Finset.range (e * r), (if levR e sR j = R then F (j / e) else 0) =
      ∑ l ∈ Finset.range r, F l := by
  obtain ⟨t0, ht0, hlt0⟩ := exists_levR e sR he hcop R hR
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show e * (r + 1) = e * r + e by ring, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    rw [Finset.sum_eq_single t0]
    · rw [show e * r + t0 = t0 + e * r by ring, levR_add_mul e sR t0 r he, if_pos hlt0,
        Nat.add_mul_div_left _ _ he, Nat.div_eq_of_lt ht0, zero_add]
    · intro t ht htt0
      rw [show e * r + t = t + e * r by ring, levR_add_mul e sR t r he, if_neg]
      intro h
      exact htt0 (levR_inj e sR t t0 he hcop (Finset.mem_range.mp ht) ht0 (h.trans hlt0.symm))
    · intro h; exact absurd (Finset.mem_range.mpr ht0) h

end Levels

section Coeffs

variable {K : Type*} [Field K]

lemma coeff_add_mul_of_lowerBd (c : K) (E F : LaurentSeries K) (N : ℤ) (hE : LowerBd E N)
    (hF : LowerBd F 0) (k : ℤ) (hk : k < N) :
    ((HahnSeries.C c + E) * F).coeff k = c * F.coeff k := by
  rw [add_mul, HahnSeries.coeff_add, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  have := hE.mul hF
  rw [add_zero] at this
  rw [this k hk, add_zero]

end Coeffs

namespace CurveData

section RamGauge

variable {C L K : Type*} [Field C] [CharZero C] [DecidableEq C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

variable (S : CurveData C L)

/-- **The leading data of a single slope `s'/e` along a reparametrized branch system**: the scaled
roots are power series with distinct leading values, each an `e`-th root of some `γₖ`, and each
`γₖ` has such a root. -/
theorem ram_lead_data (e sR : ℕ) (he : 0 < e) {r' : ℕ} (γ : Fin (r' + 1) → C)
    (hγinj : Function.Injective γ) (hγ0 : ∀ k, γ k ≠ 0)
    (hdegF : ∀ i < S.F.natDegree, e * (S.F.coeff i).natDegree ≤ sR * (S.F.natDegree - i))
    (hlead : leadPolyR e sR S.F = ∏ k, (X ^ e - Polynomial.C (γ k)))
    (N : ℕ) (hN : 0 < N) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub (N * e)) = (l.map fun r ↦ X - Polynomial.C r).prod) :
    (∀ r ∈ l, LowerBd (r * single ((N * sR : ℕ) : ℤ) 1) 0) ∧
    (l.map fun r ↦ (r * single ((N * sR : ℕ) : ℤ) 1).coeff 0).Nodup ∧
    (∀ r ∈ l, ∃ k, ((r * single ((N * sR : ℕ) : ℤ) 1).coeff 0) ^ e = algebraMap C K (γ k)) ∧
    (∀ k, ∃ r ∈ l, ((r * single ((N * sR : ℕ) : ℤ) 1).coeff 0) ^ e = algebraMap C K (γ k)) := by
  classical
  have hNe : 0 < N * e := Nat.mul_pos hN he
  set c : LaurentSeries K → K := fun r ↦ (r * single ((N * sR : ℕ) : ℤ) 1).coeff 0 with hc
  have hdeg' : ∀ i < S.F.natDegree, N * e * (S.F.coeff i).natDegree ≤ N * sR * (S.F.natDegree - i) :=
    fun i hi ↦ by
      have := Nat.mul_le_mul_left N (hdegF i hi)
      calc N * e * (S.F.coeff i).natDegree = N * (e * (S.F.coeff i).natDegree) := by ring
        _ ≤ N * (sR * (S.F.natDegree - i)) := this
        _ = N * sR * (S.F.natDegree - i) := by ring
  obtain ⟨hLB, hprod⟩ := leadPolyR_eq_prod (K := K) (N * e) (N * sR) hNe S.F S.monic hdeg' l hl
  rw [leadPolyR_scale S.F N e sR hN, hlead, Polynomial.map_prod] at hprod
  set ι := algebraMap C K
  have hP : ∀ k, (X ^ e - Polynomial.C (γ k)).map ι = X ^ e - Polynomial.C (ι (γ k)) := fun k ↦ by
    simp
  simp only [hP] at hprod
  have hsep : (∏ k, (X ^ e - Polynomial.C (ι (γ k)))).Separable := by
    refine Polynomial.separable_prod' (fun a _ b _ hab ↦ ?_) (fun a _ ↦ ?_)
    · have hne : ι (γ b) - ι (γ a) ≠ 0 := sub_ne_zero.mpr fun h ↦ hab (hγinj (ι.injective h).symm)
      refine ⟨Polynomial.C (ι (γ b) - ι (γ a))⁻¹, -Polynomial.C (ι (γ b) - ι (γ a))⁻¹, ?_⟩
      rw [neg_mul, ← sub_eq_add_neg, ← mul_sub]
      rw [show (X ^ e - Polynomial.C (ι (γ a))) - (X ^ e - Polynomial.C (ι (γ b))) =
        Polynomial.C (ι (γ b) - ι (γ a)) by rw [map_sub]; ring]
      rw [← C_mul, inv_mul_cancel₀ hne, C_1]
    · exact Polynomial.separable_X_pow_sub_C _ (by exact_mod_cast he.ne')
        ((map_ne_zero_iff _ ι.injective).mpr (hγ0 a))
  have hnd : (l.map c).Nodup := by
    have h1 := Polynomial.nodup_roots hsep
    rw [hprod] at h1
    have e2 : (l.map fun r ↦ X - Polynomial.C (c r)) = ((l.map c).map fun a ↦ X - Polynomial.C a) := by
      rw [List.map_map]; rfl
    rw [e2, ← Multiset.prod_coe, ← Multiset.map_coe, roots_multiset_prod_X_sub_C] at h1
    exact Multiset.coe_nodup.mp h1
  refine ⟨hLB, hnd, fun r hr ↦ ?_, fun k ↦ ?_⟩
  · have h0 : (∏ k, (X ^ e - Polynomial.C (ι (γ k)))).eval (c r) = 0 := by
      rw [hprod, eval_list_prod]
      exact List.prod_eq_zero (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, by
        simp only [eval_sub, eval_X, eval_C]; exact sub_eq_zero.mpr rfl⟩)
    rw [eval_prod] at h0
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp h0
    refine ⟨k, ?_⟩
    have : c r ^ e = ι (γ k) := by simpa [sub_eq_zero] using hk
    exact this
  · obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (ι (γ k)) he
    have h0 : (∏ k, (X ^ e - Polynomial.C (ι (γ k)))).eval a = 0 := by
      rw [eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [ha])
    rw [hprod, eval_list_prod] at h0
    obtain ⟨v, hv, hv0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h0)
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hv0
    refine ⟨r, hr, ?_⟩
    have hca : c r = a := hv0.symm
    show c r ^ e = _
    rw [hca, ha]

/-- **The coefficients of the rescaled basis in the monomials are bounded, and their values at
infinity form an invertible matrix** (normality at infinity, `Reduced`). -/
theorem ram_binf (e sR : ℕ) (he : 0 < e) {r' : ℕ} (γ : Fin (r' + 1) → C)
    (hγinj : Function.Injective γ) (hγ0 : ∀ k, γ k ≠ 0)
    (hdegF : ∀ i < S.F.natDegree, e * (S.F.coeff i).natDegree ≤ sR * (S.F.natDegree - i))
    (hlead : leadPolyR e sR S.F = ∏ k, (X ^ e - Polynomial.C (γ k)))
    (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (r : Fin S.F.natDegree → ℕ)
    (hrw : ∀ j, S.InfOrd K (w j) (r j)) (hred : S.Reduced K w r)
    (W : Fin S.F.natDegree → C[X][X]) (Q : Fin S.F.natDegree → C[X]) (hQ : ∀ i, Q i ≠ 0)
    (hWQ : ∀ i, (S.wTil w r i : L) * aeval S.x (Q i) = S.evXY (W i))
    (hWn : ∀ i, (W i).natDegree < S.F.natDegree) :
    (∀ i (j : ℕ), j < S.F.natDegree →
      ((W i).coeff j * X ^ gR e sR j).natDegree ≤ (Q i).natDegree) ∧
    ∀ v : Fin S.F.natDegree → C, (∀ j : Fin S.F.natDegree,
      ∑ i, v i * (((W i).coeff j * X ^ gR e sR j).coeff (Q i).natDegree / (Q i).leadingCoeff) = 0) →
      v = 0 := by
  classical
  have hsys : ∀ (N : ℕ) (hN : 0 < N) (l : List (LaurentSeries K))
      (hl : S.F.map (infSub (N * e)) = (l.map fun r ↦ X - Polynomial.C r).prod),
      (∀ ρ ∈ l, LowerBd (ρ * single ((N * sR : ℕ) : ℤ) 1) 0) ∧
      ∀ i (j : ℕ), j < S.F.natDegree → ((W i).coeff j * X ^ gR e sR j).natDegree ≤ (Q i).natDegree := by
    intro N hN l hl
    obtain ⟨hLB, hnd, -, -⟩ := S.ram_lead_data e sR he γ hγinj hγ0 hdegF hlead N hN l hl
    refine ⟨hLB, fun i j hj ↦ S.bounded_ram e sR N he hN l hl hLB hnd (S.wTil w r i) (W i) (Q i)
      (hQ i) (hWQ i) (hWn i) (fun ρ hρ ↦ ?_) j hj⟩
    have := S.infOrd_wTil w r i (hrw i) (N * e) (Nat.mul_pos hN he).ne' l hl ρ hρ
    simpa using this
  obtain ⟨Ni, hNi, li, -, hli⟩ := S.hasBranchesInf (K := K)
  have hNi' := Nat.pos_of_ne_zero hNi
  have hdegB := (hsys Ni hNi' (li.map (lsub e he)) (branchSys_lsub S.F Ni e he li hli)).2
  refine ⟨hdegB, fun v hv ↦ ?_⟩
  funext i0
  refine hred v (fun N'' hN'' l'' hl'' ρ'' hρ'' ↦ ?_) i0
  have hN''p := Nat.pos_of_ne_zero hN''
  set f : C⟮S.x⟯⟮S.y⟯ := ∑ j, S.polyE (Polynomial.C (v j)) * ((S.polyE (X ^ r j))⁻¹ * w j) with hf
  -- the reparametrized system
  have hl2 := branchSys_lsub S.F N'' e he l'' hl''
  have hmem : lsub e he ρ'' ∈ l''.map (lsub e he) := List.mem_map.mpr ⟨ρ'', hρ'', rfl⟩
  obtain ⟨hLB2, hdeg2⟩ := hsys N'' hN''p _ hl2
  have hNe := Nat.mul_pos hN''p he
  -- the expansion of `f` along `lsub ρ''`
  have hexp : S.embG (infSub (N'' * e)) (infSub_injective (N'' * e) hNe) (lsub e he ρ'')
      (S.root_of_mem hl2 hmem) f = ∑ t ∈ Finset.range S.F.natDegree,
        (∑ i, HahnSeries.C (algebraMap C K (v i)) * (infSub (K := K) (N'' * e) ((W i).coeff t * X ^ gR e sR t) *
          (infSub (K := K) (N'' * e) (Q i))⁻¹)) * single ((N'' * levR e sR t : ℕ) : ℤ) 1 *
          (lsub e he ρ'' * single ((N'' * sR : ℕ) : ℤ) 1) ^ t := by
    have hC : ∀ i, S.embG (infSub (N'' * e)) (infSub_injective (N'' * e) hNe) (lsub e he ρ'')
        (S.root_of_mem hl2 hmem) (S.polyE (Polynomial.C (v i))) = HahnSeries.C (algebraMap C K (v i)) :=
      fun i ↦ by
        rw [show S.polyE (Polynomial.C (v i)) = ⟨aeval S.x (Polynomial.C (v i)), S.aeval_mem _⟩
          from rfl, S.embG_polyX, is_C]
    have hf' : f = ∑ j, S.polyE (Polynomial.C (v j)) * S.wTil w r j := rfl
    rw [hf', map_sum]
    have hterm : ∀ i, S.embG (infSub (N'' * e)) (infSub_injective (N'' * e) hNe) (lsub e he ρ'')
        (S.root_of_mem hl2 hmem) (S.polyE (Polynomial.C (v i)) * S.wTil w r i) =
        ∑ t ∈ Finset.range S.F.natDegree, HahnSeries.C (algebraMap C K (v i)) *
          (infSub (K := K) (N'' * e) ((W i).coeff t * X ^ gR e sR t) *
            (infSub (K := K) (N'' * e) (Q i))⁻¹) * single ((N'' * levR e sR t : ℕ) : ℤ) 1 *
            (lsub e he ρ'' * single ((N'' * sR : ℕ) : ℤ) 1) ^ t := fun i ↦ by
      rw [map_mul, hC i, S.expand_ram e sR N'' he hN''p (lsub e he ρ'') (S.root_of_mem hl2 hmem) _
        (W i) (Q i) (hQ i) (hWQ i) (hWn i), Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ ↦ by ring
    simp only [hterm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    simp only [Finset.sum_mul]
  -- each coefficient vanishes to order `N'' e`
  have hcoef : ∀ t ∈ Finset.range S.F.natDegree, LowerBd ((∑ i, HahnSeries.C (algebraMap C K (v i)) *
      (infSub (K := K) (N'' * e) ((W i).coeff t * X ^ gR e sR t) *
        (infSub (K := K) (N'' * e) (Q i))⁻¹)) * single ((N'' * levR e sR t : ℕ) : ℤ) 1 *
        (lsub e he ρ'' * single ((N'' * sR : ℕ) : ℤ) 1) ^ t) ((N'' * e : ℕ) : ℤ) := by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    have hE : ∀ i, LowerBd (infSub (K := K) (N'' * e) ((W i).coeff t * X ^ gR e sR t) *
        (infSub (K := K) (N'' * e) (Q i))⁻¹ - HahnSeries.C (algebraMap C K
          (((W i).coeff t * X ^ gR e sR t).coeff (Q i).natDegree / (Q i).leadingCoeff)))
        ((N'' * e : ℕ) : ℤ) := fun i ↦
      lowerBd_infSub_div (N'' * e) hNe _ _ (hQ i) (hdeg2 i t ht')
    have hsum : (∑ i, HahnSeries.C (algebraMap C K (v i)) * (infSub (K := K) (N'' * e) ((W i).coeff t * X ^ gR e sR t) *
        (infSub (K := K) (N'' * e) (Q i))⁻¹)) = ∑ i, HahnSeries.C (algebraMap C K (v i)) *
          (infSub (K := K) (N'' * e) ((W i).coeff t * X ^ gR e sR t) *
            (infSub (K := K) (N'' * e) (Q i))⁻¹ - HahnSeries.C (algebraMap C K
              (((W i).coeff t * X ^ gR e sR t).coeff (Q i).natDegree / (Q i).leadingCoeff))) := by
      have h0 := hv ⟨t, ht'⟩
      have h1 : ∑ i, HahnSeries.C (algebraMap C K (v i)) * HahnSeries.C (algebraMap C K
          (((W i).coeff t * X ^ gR e sR t).coeff (Q i).natDegree / (Q i).leadingCoeff)) =
          (0 : LaurentSeries K) := by
        simp only [← map_mul, ← map_sum]
        rw [h0]; simp
      simp only [mul_sub, Finset.sum_sub_distrib, h1, sub_zero]
    rw [hsum]
    have h1 : LowerBd (∑ i, HahnSeries.C (algebraMap C K (v i)) *
        (infSub (K := K) (N'' * e) ((W i).coeff t * X ^ gR e sR t) *
          (infSub (K := K) (N'' * e) (Q i))⁻¹ - HahnSeries.C (algebraMap C K
            (((W i).coeff t * X ^ gR e sR t).coeff (Q i).natDegree / (Q i).leadingCoeff))))
        ((N'' * e : ℕ) : ℤ) :=
      lowerBd_sum _ _ fun i _ ↦ ((lowerBd_C _).mul (hE i)).mono (by simp)
    have h2 := (h1.mul (lowerBd_single ((N'' * levR e sR t : ℕ) : ℤ) (1 : K))).mul
      (lowerBd_pow0 (hLB2 _ hmem) t)
    exact h2.mono (by push_cast; nlinarith)
  have h3 : LowerBd (S.embG (infSub (N'' * e)) (infSub_injective (N'' * e) hNe) (lsub e he ρ'')
      (S.root_of_mem hl2 hmem) f) ((N'' * e : ℕ) : ℤ) := by
    rw [hexp]; exact lowerBd_sum _ _ hcoef
  have hρ2 : (S.F.map (infSub (e * N''))).eval (lsub e he ρ'') = 0 := by
    rw [mul_comm]; exact S.root_of_mem hl2 hmem
  have h4 := S.embG_lsub_inf e he N'' hN''p ρ'' (S.root_of_mem hl'' hρ'') hρ2 f
  have h5 : S.embG (infSub (N'' * e)) (infSub_injective (N'' * e) hNe) (lsub e he ρ'')
      (S.root_of_mem hl2 hmem) f = S.embG (infSub (e * N''))
        (infSub_injective (e * N'') (Nat.mul_pos he hN''p)) (lsub e he ρ'') hρ2 f := by
    have := S.embG_congr' (K := K) (show infSub (C := C) (K := K) (N'' * e) = infSub (e * N'') by
      rw [mul_comm]) (infSub_injective (N'' * e) hNe) (infSub_injective (e * N'')
        (Nat.mul_pos he hN''p)) rfl (S.root_of_mem hl2 hmem) hρ2
    exact congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K ↦ φ f) this
  rw [h5, h4] at h3
  have h6 : ((N'' * e : ℕ) : ℤ) = (e : ℤ) * (N'' : ℤ) := by push_cast; ring
  rw [h6] at h3
  have h7 := (lowerBd_lsub_iff e he _ (N'' : ℤ)).mp h3
  simpa using h7


set_option maxHeartbeats 16000000 in
/-- **The gauge at ramified places at infinity** (logarithmic level): a constant gauge `A` makes the
limit matrix `Λ` level-triangular, `A′ = Λ A − A T`, with diagonal `(t/e) γₖ′/γₖ` (`t` the residue
of level `R`); and the jets along one root per place make `Λ` gauge-trivial over `K`. -/
theorem ram_gauge (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η))
    (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
    (e sR : ℕ) (he : 0 < e) (hcop : Nat.Coprime sR e) {r' : ℕ} (γ : Fin (r' + 1) → C)
    (hγinj : Function.Injective γ) (hγ0 : ∀ k, γ k ≠ 0)
    (hdegF : ∀ i < S.F.natDegree, e * (S.F.coeff i).natDegree ≤ sR * (S.F.natDegree - i))
    (hlead : leadPolyR e sR S.F = ∏ k, (X ^ e - Polynomial.C (γ k)))
    (w : Fin S.F.natDegree → C⟮S.x⟯⟮S.y⟯) (r : Fin S.F.natDegree → ℕ)
    (hrw : ∀ j, S.InfOrd K (w j) (r j)) (hred : S.Reduced K w r) (S0 : C[X]) (hS00 : S0 ≠ 0)
    (P : Fin S.F.natDegree → Fin S.F.natDegree → C[X])
    (hP : ∀ i, (⟨(w i : L)′, S.derivClosedXYW' (Polynomial.C η) hx _ (w i).2⟩ : C⟮S.x⟯⟮S.y⟯) *
      S.polyE S0 = ∑ j, S.polyE (P i j) * w j)
    (hdeg : ∀ i j, (pqV η r P S0 i j).natDegree ≤ (X ^ (r i + 1) * S0).natDegree) :
    ∃ (A : Matrix (Fin S.F.natDegree) (Fin e × Fin (r' + 1)) C)
      (Ai : Matrix (Fin e × Fin (r' + 1)) (Fin S.F.natDegree) C)
      (T : Matrix (Fin e × Fin (r' + 1)) (Fin e × Fin (r' + 1)) C),
      A * Ai = 1 ∧ Ai * A = 1 ∧
      (∀ i a, (A i a)′ = ∑ j, (pqV η r P S0 i j).coeff (X ^ (r i + 1) * S0).natDegree /
        (X ^ (r i + 1) * S0).leadingCoeff * A j a - ∑ b, A i b * T b a) ∧
      (∀ a b, b.1 < a.1 → T a b = 0) ∧
      (∀ (R : Fin e) (k k' : Fin (r' + 1)) (t : ℕ), t < e → levR e sR t = R →
        T (R, k) (R, k') = if k = k' then ((t : C) / e) * ((γ k)′ / γ k) else 0) ∧
      ∃ Jt : Fin S.F.natDegree → (Fin e × Fin (r' + 1)) → K,
        (∀ c : Fin S.F.natDegree → K, (∀ b, ∑ i, c i * Jt i b = 0) → c = 0) ∧
        ∀ i b, (Jt i b)′ = ∑ j, algebraMap C K ((pqV η r P S0 i j).coeff
          (X ^ (r i + 1) * S0).natDegree / (X ^ (r i + 1) * S0).leadingCoeff) * Jt j b := by
  classical
  set ι := algebraMap C K with hι
  -- `n = e r`
  have hne : S.F.natDegree = e * (r' + 1) := by
    have h1 := (leadPolyR_monic e sR S.F S.monic).2
    rw [hlead, natDegree_prod_of_monic _ _ (fun k _ ↦ monic_X_pow_sub_C _ he.ne')] at h1
    simp only [natDegree_X_pow_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h1
    rw [← h1]; ring
  -- a reparametrized branch system and the leading data
  obtain ⟨Ni, hNi, li, -, hli⟩ := S.hasBranchesInf (K := K)
  have hNi' := Nat.pos_of_ne_zero hNi
  have hNe : 0 < Ni * e := Nat.mul_pos hNi' he
  have hl := branchSys_lsub S.F Ni e he li hli
  obtain ⟨hLB, hnd, -, hex⟩ := S.ram_lead_data e sR he γ hγinj hγ0 hdegF hlead Ni hNi'
    (li.map (lsub e he)) hl
  choose ρk hρkl hρk using hex
  set z : Fin (r' + 1) → LaurentSeries K := fun k ↦ ρk k * single ((Ni * sR : ℕ) : ℤ) 1 with hz
  have hzLB : ∀ k, LowerBd (z k) 0 := fun k ↦ hLB _ (hρkl k)
  set cc : Fin (r' + 1) → K := fun k ↦ (z k).coeff 0 with hcc
  have hcce : ∀ k, cc k ^ e = ι (γ k) := hρk
  have hcc0 : ∀ k, cc k ≠ 0 := fun k h ↦ by
    have := hcce k
    rw [h, zero_pow he.ne'] at this
    exact hγ0 k (ι.injective (by rw [← this, map_zero]))
  -- the expansions of the rescaled basis in the monomials
  have hF1 : S.F ≠ 1 := fun h ↦ S.natDegree_F_ne_zero (by rw [h, natDegree_one])
  choose W Q hQ hWQ hWn using fun i ↦ S.exists_repr_lt (S.wTil w r i) hF1
  obtain ⟨hdegB, hBinv⟩ := S.ram_binf e sR he γ hγinj hγ0 hdegF hlead w r hrw hred W Q hQ hWQ hWn
  set Bm : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C := fun i j ↦
    ((W i).coeff j * X ^ gR e sR j).coeff (Q i).natDegree / (Q i).leadingCoeff with hBm
  have hBdet : Bm.det ≠ 0 := by
    intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
    exact hv0 (hBinv v fun j ↦ by
      have := congrFun hv j
      simpa [Matrix.vecMul, dotProduct, hBm] using this)
  have hBu : IsUnit Bm.det := isUnit_iff_ne_zero.mpr hBdet
  -- the Vandermonde matrix of the `γₖ`
  set Wv : Matrix (Fin (r' + 1)) (Fin (r' + 1)) C := fun l k ↦ γ k ^ (l : ℕ) with hWv
  have hWdet : Wv.det ≠ 0 := by
    have : Wv = (Matrix.vandermonde γ).transpose := by ext l k; simp [hWv, Matrix.vandermonde]
    rw [this, Matrix.det_transpose]; exact Matrix.det_vandermonde_ne_zero_iff.mpr hγinj
  have hWu : IsUnit Wv.det := isUnit_iff_ne_zero.mpr hWdet
  set Wi := Wv⁻¹ with hWi
  have hWWi : Wv * Wi = 1 := Matrix.mul_nonsing_inv _ hWu
  have hWiW : Wi * Wv = 1 := Matrix.nonsing_inv_mul _ hWu
  set Wi' : Fin (r' + 1) → ℕ → C := fun k l ↦ if h : l < r' + 1 then Wi k ⟨l, h⟩ else 0 with hWi'
  -- the level-graded Vandermonde matrices
  set Qm : Matrix (Fin S.F.natDegree) (Fin e × Fin (r' + 1)) C := fun j a ↦
    if levR e sR j = a.1 then γ a.2 ^ ((j : ℕ) / e) else 0 with hQm
  set Qmi : Matrix (Fin e × Fin (r' + 1)) (Fin S.F.natDegree) C := fun a j ↦
    if levR e sR j = a.1 then Wi' a.2 ((j : ℕ) / e) else 0 with hQmi
  have hjlt : ∀ j : Fin S.F.natDegree, (j : ℕ) / e < r' + 1 := fun j ↦ by
    have h1 : (j : ℕ) < e * (r' + 1) := hne ▸ j.2
    exact Nat.div_lt_of_lt_mul h1
  have hlevlt : ∀ j : ℕ, levR e sR j < e := fun j ↦ (gR_spec e sR j he).2
  have hjeq : ∀ j j' : Fin S.F.natDegree, levR e sR j = levR e sR j' → (j : ℕ) / e = (j' : ℕ) / e →
      j = j' := by
    intro j j' h1 h2
    rw [levR_mod e sR j he, levR_mod e sR j' he] at h1
    have h3 := levR_inj e sR _ _ he hcop (Nat.mod_lt _ he) (Nat.mod_lt _ he) h1
    apply Fin.ext
    rw [← Nat.mod_add_div (j : ℕ) e, ← Nat.mod_add_div (j' : ℕ) e, h3, h2]
  have hWW : ∀ l l' : Fin (r' + 1), ∑ k, γ k ^ (l : ℕ) * Wi k l' = if l = l' then 1 else 0 := by
    intro l l'
    have := congrFun (congrFun hWWi l) l'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  have hWW' : ∀ k k' : Fin (r' + 1), ∑ l : Fin (r' + 1), Wi k l * γ k' ^ (l : ℕ) =
      if k = k' then 1 else 0 := by
    intro k k'
    have := congrFun (congrFun hWiW k) k'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  have hQQ : Qm * Qmi = 1 := by
    ext j j'
    rw [Matrix.one_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Finset.sum_eq_single (⟨levR e sR j, hlevlt j⟩ : Fin e)]
    · have e1 : ∀ k : Fin (r' + 1), Qm j (⟨levR e sR j, hlevlt j⟩, k) *
          Qmi (⟨levR e sR j, hlevlt j⟩, k) j' =
          if levR e sR j' = levR e sR j then γ k ^ ((j : ℕ) / e) * Wi k ⟨(j' : ℕ) / e, hjlt j'⟩
          else 0 := by
        intro k
        simp only [hQm, hQmi, ↓reduceIte]
        by_cases h : levR e sR (j' : ℕ) = levR e sR j
        · rw [if_pos h, if_pos h]; simp only [hWi', dif_pos (hjlt j')]
        · rw [if_neg h, if_neg h, mul_zero]
      simp only [e1]
      split_ifs with hl hjj hjj
      · rw [hWW ⟨(j : ℕ) / e, hjlt j⟩ ⟨(j' : ℕ) / e, hjlt j'⟩, if_pos (by rw [hjj])]
      · rw [hWW ⟨(j : ℕ) / e, hjlt j⟩ ⟨(j' : ℕ) / e, hjlt j'⟩, if_neg]
        intro h
        exact hjj (hjeq j j' hl.symm (by simpa using congrArg Fin.val h))
      · exact absurd (by rw [hjj]) hl
      · simp
    · intro R _ hR
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      simp only [hQm]
      rw [if_neg (fun h ↦ hR (Fin.ext h.symm)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hQQ' : Qmi * Qm = 1 := by
    ext a b
    rw [Matrix.one_apply, Matrix.mul_apply]
    by_cases hab1 : (a.1 : ℕ) = b.1
    · have e1 : ∀ j : Fin S.F.natDegree, Qmi a j * Qm j b =
          if levR e sR j = a.1 then Wi' a.2 ((j : ℕ) / e) * γ b.2 ^ ((j : ℕ) / e) else 0 := by
        intro j
        simp only [hQm, hQmi]
        by_cases h : levR e sR (j : ℕ) = a.1
        · rw [if_pos h, if_pos h, if_pos (h.trans hab1)]
        · rw [if_neg h, zero_mul, if_neg h]
      rw [Finset.sum_congr rfl fun j _ ↦ e1 j]
      rw [Fin.sum_univ_eq_sum_range (fun j ↦ if levR e sR j = a.1 then Wi' a.2 (j / e) *
        γ b.2 ^ (j / e) else 0), hne, sum_lev e sR (r' + 1) he hcop a.1 a.1.2
        (fun l ↦ Wi' a.2 l * γ b.2 ^ l), ← Fin.sum_univ_eq_sum_range (fun l ↦ Wi' a.2 l * γ b.2 ^ l)]
      have e2 : ∀ l : Fin (r' + 1), Wi' a.2 l * γ b.2 ^ (l : ℕ) = Wi a.2 l * γ b.2 ^ (l : ℕ) :=
        fun l ↦ by simp only [hWi', dif_pos l.2]
      simp only [e2]
      rw [hWW' a.2 b.2]
      have hab : a = b ↔ a.2 = b.2 :=
        ⟨fun h ↦ by rw [h], fun h ↦ Prod.ext (Fin.ext hab1) h⟩
      by_cases h2 : a.2 = b.2
      · rw [if_pos h2, if_pos (hab.mpr h2)]
      · rw [if_neg h2, if_neg (fun h ↦ h2 (hab.mp h))]
    · have e1 : ∀ j : Fin S.F.natDegree, Qmi a j * Qm j b = 0 := by
        intro j
        simp only [hQm, hQmi]
        by_cases h : levR e sR (j : ℕ) = a.1
        · rw [if_neg (fun h' ↦ hab1 (h.symm.trans h')), mul_zero]
        · rw [if_neg h, zero_mul]
      rw [Finset.sum_congr rfl fun j _ ↦ e1 j, Finset.sum_const_zero,
        if_neg (fun h ↦ hab1 (by rw [h]))]
  -- the gauge `A = B∞ Q` and `T`
  set Bmi := Bm⁻¹ with hBmi
  have hBB : Bm * Bmi = 1 := Matrix.mul_nonsing_inv _ hBu
  have hBB' : Bmi * Bm = 1 := Matrix.nonsing_inv_mul _ hBu
  set A := Bm * Qm with hA
  set Ai := Qmi * Bmi with hAi
  have hAAi : A * Ai = 1 := by
    rw [hA, hAi, Matrix.mul_assoc, ← Matrix.mul_assoc Qm, hQQ, Matrix.one_mul, hBB]
  have hAiA : Ai * A = 1 := by
    rw [hA, hAi, Matrix.mul_assoc, ← Matrix.mul_assoc Bmi, hBB', Matrix.one_mul, hQQ']
  set Λm : Matrix (Fin S.F.natDegree) (Fin S.F.natDegree) C := fun i j ↦
    (pqV η r P S0 i j).coeff (X ^ (r i + 1) * S0).natDegree / (X ^ (r i + 1) * S0).leadingCoeff
    with hΛm
  set T := Ai * (Λm * A - A.map fun z ↦ z′) with hT
  have hAT : A * T = Λm * A - A.map fun z ↦ z′ := by
    rw [hT, ← Matrix.mul_assoc, hAAi, Matrix.one_mul]
  have hderA : ∀ i a, (A i a)′ = ∑ j, Λm i j * A j a - ∑ b, A i b * T b a := by
    intro i a
    have := congrFun (congrFun hAT i) a
    rw [Matrix.mul_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply] at this
    rw [this]; ring
  -- the jets along one root per place
  have hroot : ∀ k, (S.F.map (infSub (Ni * e))).eval (ρk k) = 0 := fun k ↦ S.root_of_mem hl (hρkl k)
  set φ : Fin (r' + 1) → (C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K) := fun k ↦
    S.embG (infSub (Ni * e)) (infSub_injective (Ni * e) hNe) (ρk k) (hroot k) with hφ
  have hwLB : ∀ i k, LowerBd (φ k (S.wTil w r i)) 0 := fun i k ↦ by
    have := S.infOrd_wTil w r i (hrw i) (Ni * e) hNe.ne' _ hl (ρk k) (hρkl k)
    simpa using this
  set Jt : Fin S.F.natDegree → (Fin e × Fin (r' + 1)) → K := fun i b ↦
    (φ b.2 (S.wTil w r i)).coeff ((Ni * b.1 : ℕ) : ℤ) with hJt
  set Jμ : Fin S.F.natDegree → (Fin e × Fin (r' + 1)) → K := fun j b ↦
    ((z b.2) ^ (j : ℕ)).coeff (((Ni * b.1 : ℕ) : ℤ) - ((Ni * levR e sR j : ℕ) : ℤ)) with hJμ
  have hkN : ∀ b : Fin e × Fin (r' + 1), ((Ni * b.1 : ℕ) : ℤ) < ((Ni * e : ℕ) : ℤ) := fun b ↦ by
    have : Ni * b.1 < Ni * e := Nat.mul_lt_mul_of_pos_left b.1.2 hNi'
    exact_mod_cast this
  have hJexp : ∀ i b, Jt i b = ∑ j, ι (Bm i j) * Jμ j b := by
    intro i b
    have h1 := S.expand_ram e sR Ni he hNi' (ρk b.2) (hroot b.2) (S.wTil w r i) (W i) (Q i) (hQ i)
      (hWQ i) (hWn i)
    simp only [hJt]
    change (φ b.2 (S.wTil w r i)).coeff _ = _
    rw [show φ b.2 (S.wTil w r i) = _ from h1, HahnSeries.coeff_sum, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    have hE := lowerBd_infSub_div (K := K) (Ni * e) hNe ((W i).coeff t * X ^ gR e sR t) (Q i) (hQ i)
      (hdegB i t t.2)
    set E := infSub (K := K) (Ni * e) ((W i).coeff t * X ^ gR e sR t) *
      (infSub (K := K) (Ni * e) (Q i))⁻¹ - HahnSeries.C (ι (Bm i t)) with hEdef
    have hsplit : infSub (K := K) (Ni * e) ((W i).coeff t * X ^ gR e sR t) *
        (infSub (K := K) (Ni * e) (Q i))⁻¹ = HahnSeries.C (ι (Bm i t)) + E := by
      rw [hEdef]; ring
    have hF : LowerBd (single ((Ni * levR e sR t : ℕ) : ℤ) (1 : K) * z b.2 ^ (t : ℕ)) 0 := by
      have := (lowerBd_single ((Ni * levR e sR t : ℕ) : ℤ) (1 : K)).mul (lowerBd_pow0 (hzLB b.2) t)
      exact this.mono (by positivity)
    rw [hsplit, mul_assoc, coeff_add_mul_of_lowerBd _ E _ _ hE hF _ (hkN b), coeff_single_mul',
      one_mul]
  have hJder : ∀ i b, (Jt i b)′ = ∑ j, ι (Λm i j) * Jt j b := by
    intro i b
    set q : C[X] := X ^ (r i + 1) * S0 with hq
    have hq0 : q ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hS00
    have hqK := infSub_ne_zero (K := K) (Ni * e) hNe q hq0
    have hmem := S.derivClosedXYW' (Polynomial.C η) hx (S.wTil w r i) (S.wTil w r i).2
    have hdw := S.deriv_wTil η hx w r S0 P hP i
    have hid : (⟨(S.wTil w r i : L)′, hmem⟩ : C⟮S.x⟯⟮S.y⟯) * S.polyE q =
        ∑ j, S.polyE (pqV η r P S0 i j) * S.wTil w r j := Subtype.ext (by
      push_cast
      exact hdw)
    have hemb := congrArg (φ b.2) hid
    rw [map_mul, map_sum] at hemb
    simp only [map_mul] at hemb
    rw [show φ b.2 (S.polyE q) = infSub (Ni * e) q from S.embG_polyX _ _ _ _ _ _] at hemb
    have hpoly : ∀ j, φ b.2 (S.polyE (pqV η r P S0 i j)) = infSub (Ni * e) (pqV η r P S0 i j) :=
      fun j ↦ S.embG_polyX _ _ _ _ _ _
    simp only [hpoly] at hemb
    have hder : φ b.2 ⟨(S.wTil w r i : L)′, hmem⟩ =
        ∑ j, (infSub (K := K) (Ni * e) (pqV η r P S0 i j) * (infSub (K := K) (Ni * e) q)⁻¹) *
          φ b.2 (S.wTil w r j) := by
      have : φ b.2 ⟨(S.wTil w r i : L)′, hmem⟩ =
          (∑ j, infSub (K := K) (Ni * e) (pqV η r P S0 i j) * φ b.2 (S.wTil w r j)) *
            (infSub (K := K) (Ni * e) q)⁻¹ := by
        rw [← hemb, mul_assoc, mul_inv_cancel₀ hqK, mul_one]
      rw [this, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have hL := S.coeff_embG_deriv_inf η hx hK (Ni * e) hNe (ρk b.2) (hroot b.2) (S.wTil w r i)
      (hwLB i b.2) _ (hkN b)
    simp only [hJt]
    rw [← hL]
    change (φ b.2 ⟨(S.wTil w r i : L)′, hmem⟩).coeff _ = _
    rw [hder, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hlim := lowerBd_infSub_div (K := K) (Ni * e) hNe (pqV η r P S0 i j) q hq0 (hdeg i j)
    rw [show infSub (K := K) (Ni * e) (pqV η r P S0 i j) * (infSub (K := K) (Ni * e) q)⁻¹ =
      HahnSeries.C (ι (Λm i j)) + (infSub (K := K) (Ni * e) (pqV η r P S0 i j) *
        (infSub (K := K) (Ni * e) q)⁻¹ - HahnSeries.C (ι (Λm i j))) by ring,
      coeff_add_mul_of_lowerBd _ _ _ _ hlim (hwLB j b.2) _ (hkN b)]
  -- the jets through the gauge: `Jt = A Z`
  set AK : Matrix (Fin S.F.natDegree) (Fin e × Fin (r' + 1)) K := A.map ι with hAK
  set AiK : Matrix (Fin e × Fin (r' + 1)) (Fin S.F.natDegree) K := Ai.map ι with hAiK
  set TK : Matrix (Fin e × Fin (r' + 1)) (Fin e × Fin (r' + 1)) K := T.map ι with hTK
  set Z : Matrix (Fin e × Fin (r' + 1)) (Fin e × Fin (r' + 1)) K := fun a b ↦
    ∑ j, ι (Qmi a j) * Jμ j b with hZ
  have hAKi : AK * AiK = 1 := by
    rw [hAK, hAiK, ← Matrix.map_mul, hAAi, Matrix.map_one _ (map_zero _) (map_one _)]
  have hAQ : A * Qmi = Bm := by rw [hA, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hJAZ : ∀ i b, Jt i b = ∑ a, AK i a * Z a b := by
    intro i b
    rw [hJexp]
    simp only [hZ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [← mul_assoc]
    rw [← Finset.sum_mul]
    congr 1
    rw [← hAQ, Matrix.mul_apply, map_sum]
    simp only [hAK, Matrix.map_apply, map_mul]
  -- `T Z = Z′`
  have hkey : ∀ i b, ∑ c, AK i c * (∑ a, TK c a * Z a b - (Z c b)′) = 0 := by
    intro i b
    have h1 := hJder i b
    simp only [hJAZ] at h1
    rw [map_sum] at h1
    simp only [Derivation.leibniz, smul_eq_mul] at h1
    have hAd : ∀ a, (AK i a)′ = ∑ j, ι (Λm i j) * AK j a - ∑ c, AK i c * TK c a := by
      intro a
      simp only [hAK, hTK, Matrix.map_apply]
      rw [hK, hderA i a, map_sub, map_sum, map_sum]
      simp only [map_mul]
    simp only [hAd] at h1
    have e1 : ∑ a, (AK i a * (Z a b)′ + Z a b * (∑ j, ι (Λm i j) * AK j a -
        ∑ c, AK i c * TK c a)) = ∑ j, ι (Λm i j) * ∑ a, AK j a * Z a b -
          ∑ c, AK i c * ∑ a, TK c a * Z a b + ∑ c, AK i c * (Z c b)′ := by
      simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [add_comm]
      congr 1
      congr 1
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring
    rw [e1] at h1
    simp only [mul_sub, Finset.sum_sub_distrib]
    linear_combination -h1
  have hTZ : ∀ a b, ∑ c, TK a c * Z c b = (Z a b)′ - Z a b * 0 := by
    intro a b
    rw [mul_zero, sub_zero]
    have h2 : ∑ i, AiK a i * ∑ c, AK i c * (∑ a', TK c a' * Z a' b - (Z c b)′) = 0 := by
      simp only [hkey, mul_zero, Finset.sum_const_zero]
    simp only [Finset.mul_sum] at h2
    rw [Finset.sum_comm] at h2
    have h3 : ∀ c, ∑ i, AiK a i * (AK i c * (∑ a', TK c a' * Z a' b - (Z c b)′)) =
        (AiK * AK) a c * (∑ a', TK c a' * Z a' b - (Z c b)′) := fun c ↦ by
      rw [Matrix.mul_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    have hAiAK : AiK * AK = 1 := by
      rw [hAK, hAiK, ← Matrix.map_mul, hAiA, Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [h3, hAiAK, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at h2
    exact sub_eq_zero.mp h2
  -- the level structure of `Z`
  choose t0 ht0 hlt0 using fun R : Fin e ↦ exists_levR e sR he hcop R R.2
  have hZlow : ∀ (R h : Fin e) (k k' : Fin (r' + 1)), h < R → Z (R, k) (h, k') = 0 := by
    intro R h k k' hhR
    simp only [hZ]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    by_cases hj : levR e sR (j : ℕ) = R
    · have hneg : ((Ni * (h : ℕ) : ℕ) : ℤ) - ((Ni * levR e sR j : ℕ) : ℤ) < 0 := by
        rw [hj]
        have : Ni * (h : ℕ) < Ni * (R : ℕ) := Nat.mul_lt_mul_of_pos_left hhR hNi'
        push_cast at this ⊢; linarith
      simp only [hJμ]
      rw [lowerBd_pow0 (hzLB k') _ _ hneg, mul_zero]
    · simp only [hQmi, if_neg hj, map_zero, zero_mul]
  have hcpow : ∀ (k' : Fin (r' + 1)) (j : ℕ) (R : Fin e), levR e sR j = R →
      cc k' ^ j = cc k' ^ t0 R * ι (γ k') ^ (j / e) := by
    intro k' j R hj
    have hmod : j % e = t0 R := levR_inj e sR _ _ he hcop (Nat.mod_lt _ he) (ht0 R)
      (by rw [← levR_mod e sR j he, hj, hlt0])
    conv_lhs => rw [← Nat.mod_add_div j e, hmod, pow_add, pow_mul, hcce]
  have hZdiag : ∀ (R : Fin e) (k k' : Fin (r' + 1)),
      Z (R, k) (R, k') = if k = k' then cc k ^ t0 R else 0 := by
    intro R k k'
    have hterm : ∀ j : Fin S.F.natDegree, ι (Qmi (R, k) j) * Jμ j (R, k') =
        cc k' ^ t0 R * ι (if levR e sR j = R then Wi' k ((j : ℕ) / e) * γ k' ^ ((j : ℕ) / e)
          else 0) := by
      intro j
      by_cases hj : levR e sR (j : ℕ) = R
      · simp only [hQmi, hJμ, hj, sub_self, ↓reduceIte]
        rw [coeff_zero_pow_of_lowerBd (hzLB k'), hcpow k' j R hj, map_mul, map_pow]
        ring
      · simp only [hQmi, if_neg hj, map_zero, zero_mul, mul_zero]
    simp only [hZ, hterm, ← Finset.mul_sum, ← map_sum]
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ if levR e sR j = R then Wi' k (j / e) *
      γ k' ^ (j / e) else 0), hne, sum_lev e sR (r' + 1) he hcop R R.2
      (fun l ↦ Wi' k l * γ k' ^ l), ← Fin.sum_univ_eq_sum_range (fun l ↦ Wi' k l * γ k' ^ l)]
    have e2 : ∀ l : Fin (r' + 1), Wi' k l * γ k' ^ (l : ℕ) = Wi k l * γ k' ^ (l : ℕ) :=
      fun l ↦ by simp only [hWi', dif_pos l.2]
    simp only [e2]
    rw [hWW' k k']
    split_ifs with hkk
    · subst hkk; simp
    · simp
  have hd0 : ∀ (R : Fin e) (k : Fin (r' + 1)), cc k ^ t0 R ≠ 0 := fun R k ↦ pow_ne_zero _ (hcc0 k)
  obtain ⟨hlowK, hdiagK⟩ := tri_of_TZ TK Z (fun _ ↦ 0) (fun R k ↦ cc k ^ t0 R) hd0 hZlow hZdiag hTZ
  -- back to `C`
  have hlow : ∀ a b, b.1 < a.1 → T a b = 0 := fun a b hab ↦
    ι.injective (by have := hlowK a b hab; simpa [hTK] using this)
  have hlog : ∀ (k : Fin (r' + 1)) (t : ℕ), (cc k ^ t)′ / cc k ^ t =
      ι (((t : C) / e) * ((γ k)′ / γ k)) := by
    intro k t
    have hde : (e : K) * cc k ^ (e - 1) * (cc k)′ = ι ((γ k)′) := by
      have := congrArg (fun x : K ↦ x′) (hcce k)
      simp only [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, hK] at this
      rw [← this]; ring
    have hc := hcc0 k
    have he' : (e : K) ≠ 0 := by exact_mod_cast he.ne'
    have hγk : ι (γ k) = cc k ^ e := (hcce k).symm
    simp only [map_mul, map_div₀, map_natCast, hγk, ← hde, Derivation.leibniz_pow, nsmul_eq_mul,
      smul_eq_mul]
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht; simp
    have h1 : cc k ^ t = cc k ^ (t - 1) * cc k := by rw [← pow_succ]; congr 1; omega
    have h2 : cc k ^ e = cc k ^ (e - 1) * cc k := by rw [← pow_succ]; congr 1; omega
    rw [h1, h2]
    field_simp
  have hdiag : ∀ (R : Fin e) (k k' : Fin (r' + 1)) (t : ℕ), t < e → levR e sR t = R →
      T (R, k) (R, k') = if k = k' then ((t : C) / e) * ((γ k)′ / γ k) else 0 := by
    intro R k k' t ht htR
    have htt : t = t0 R := levR_inj e sR _ _ he hcop ht (ht0 R) (by rw [htR, hlt0])
    have h1 := hdiagK R k k'
    apply ι.injective
    rw [show ι (T (R, k) (R, k')) = TK (R, k) (R, k') from rfl, h1]
    split_ifs with hkk
    · rw [sub_zero, hlog k (t0 R), htt]
    · simp
  -- the jets separate
  have hind : ∀ c : Fin S.F.natDegree → K, (∀ b, ∑ i, c i * Jt i b = 0) → c = 0 := by
    intro c hc
    set y : Fin e × Fin (r' + 1) → K := fun a ↦ ∑ i, c i * AK i a with hy
    have hy0 : y = 0 := inj_of_Z Z (fun R k ↦ cc k ^ t0 R) hd0 hZlow hZdiag y fun b ↦ by
      have hyZ : ∑ a, y a * Z a b = ∑ i, c i * Jt i b := by
        simp only [hy, hJAZ, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring
      rw [hyZ]; exact hc b
    funext i
    have h1 : c i = ∑ a, y a * AiK a i := by
      simp only [hy, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc, ← Finset.mul_sum]
      have h2 : ∀ i', ∑ a, AK i' a * AiK a i = (AK * AiK) i' i := fun i' ↦ (Matrix.mul_apply).symm
      simp only [h2, hAKi, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
    rw [h1, hy0]; simp
  exact ⟨A, Ai, T, hAAi, hAiA, hderA, hlow, hdiag, Jt, hind, hJder⟩


end RamGauge

end CurveData

end Curves
