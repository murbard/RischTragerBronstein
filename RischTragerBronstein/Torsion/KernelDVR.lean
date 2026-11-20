import RischTragerBronstein.Torsion.KernelField

/-!
# Prime-to-`p` torsion in the kernel of reduction (general curves)

Over a discrete valuation ring `O`: let `Qᵢ = (xᵢ + tᵢ, Yᵢ)` be points of `F = 0` reducing to the
base points `Pᵢ = (xᵢ, yᵢ₀)` (`ϖ ∣ tᵢ`). If a function `ψ` (basis coordinates `c`, pole order
`≤ (m+1) g`, primitive) vanishes to order `m + 1` at the `Qᵢ` and at the other points of the base
fibres, `m + 1` is a unit and the reduced base divisor is non-special (`hNS`), then `tᵢ = 0`
(`kernel_no_torsionG`), by peeling off `ψ = a uᵐ⁺¹ D + ϖʳ α` layer by layer.

The basis numerators are `B`, with `B₀ = D` (the denominator of the basis, a unit at the base
points).
-/

open Polynomial Sup

namespace GTors

section Comp

variable {R : Type*} [CommRing R]

/-- Expansion of `uᵐ⁺¹ D` at `xᵢ + t`. -/
lemma uD_pow_comp {g : ℕ} (x : Fin g → R) (i : Fin g) (t : R) (m : ℕ) (D : R[X]) :
    ∃ R₁ R₂ : R[X], ((∏ j, (X - C (x j))) ^ (m + 1) * D).comp (X + C (x i + t)) =
      X ^ (m + 1) * R₁ +
        C ((m + 1 : R) * t * (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1) * D.eval (x i)) *
          X ^ m + C (t ^ 2) * R₂ := by
  obtain ⟨R₁, R₂, hu⟩ := Jac.u_pow_comp x i t m
  -- `D(xᵢ + t + X) = D(xᵢ) + t e + X E`
  obtain ⟨e, he⟩ : ∃ e : R, D.eval (x i + t) = D.eval (x i) + t * e := by
    obtain ⟨e, he⟩ := D.sub_dvd_eval_sub (x i + t) (x i)
    exact ⟨e, by rw [add_sub_cancel_left] at he; linear_combination he⟩
  obtain ⟨E, hE⟩ : ∃ E : R[X], D.comp (X + C (x i + t)) = C (D.eval (x i + t)) + X * E := by
    refine ⟨(D.comp (X + C (x i + t))).divX, ?_⟩
    conv_lhs => rw [← X_mul_divX_add (D.comp (X + C (x i + t)))]
    rw [coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C, zero_add]
    ring
  set κ := (m + 1 : R) * (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1) with hκ
  refine ⟨R₁ * (C (D.eval (x i + t)) + X * E) + C (κ * t) * E,
    C (κ * e) * X ^ m + R₂ * (C (D.eval (x i + t)) + X * E), ?_⟩
  rw [mul_comp, hu, hE, he]
  simp only [hκ, map_add, map_mul, map_pow, map_natCast, map_one]
  ring

end Comp

section Main

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

local notation "ρ" => IsLocalRing.residue O

/-- Coordinates reducing to zero are `ϖ` times coordinates of no larger degree. -/
lemma coord_div {ϖ : O} (hϖ : Irreducible ϖ) (P : O[X]) (h : P.map ρ = 0) :
    ∃ P' : O[X], P = C ϖ * P' ∧ (P' = 0 ∨ P'.natDegree = P.natDegree) := by
  obtain ⟨P', hP'⟩ := (Jac.C_dvd_iff_map hϖ P).mpr h
  refine ⟨P', hP', ?_⟩
  by_cases h0 : P' = 0
  · exact Or.inl h0
  · right
    rw [hP', natDegree_C_mul hϖ.ne_zero]

lemma evalW_mapG {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (W : R[X][X]) (a b : R) :
    evalW (W.map (mapRingHom φ)) (φ a) (φ b) = φ (evalW W a b) := by
  simp only [evalW, Polynomial.map_map]
  rw [eval_map, eval_map, Polynomial.hom_eval₂]
  congr 1
  refine RingHom.ext fun P ↦ ?_
  simp only [RingHom.comp_apply, coe_mapRingHom, coe_evalRingHom]
  rw [eval_map, Polynomial.eval₂_at_apply]

lemma IsBranchG.mapR {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {F : R[X][X]}
    {α β : R} {ℓ : ℕ} {V : R[X]} (h : IsBranchG F α β ℓ V) :
    IsBranchG (F.map (mapRingHom φ)) (φ α) (φ β) ℓ (V.map φ) := by
  refine ⟨by rw [coeff_map, h.1], ?_⟩
  have := Polynomial.map_dvd φ h.2
  rwa [Polynomial.map_pow, Polynomial.map_X, jetN_map] at this

/-- **No prime-to-`p` torsion in the kernel of reduction** (general curves). -/
theorem kernel_no_torsionG {ϖ : O} (hϖ : Irreducible ϖ) {n g m : ℕ} (hn : 0 < n)
    (F : O[X][X]) (B : Fin n → O[X][X]) (D : O[X]) (hB0 : B ⟨0, hn⟩ = Polynomial.C D)
    (δ : Fin n → ℕ) (hδ0 : δ ⟨0, hn⟩ = 0) (hδ : ∀ j : Fin n, (j : ℕ) ≠ 0 → 1 ≤ δ j)
    (hℓ : IsUnit ((m + 1 : ℕ) : O))
    (x : Fin g → O) (hx : ∀ i j, i ≠ j → IsUnit (x i - x j)) (y : Fin g → Fin n → O)
    (hFy : ∀ i kk, evalW F (x i) (y i kk) = 0)
    (hFu : ∀ i kk, IsUnit (evalW (derivative F) (x i) (y i kk)))
    (hdet : ∀ i, IsUnit (Matrix.det (Matrix.of fun kk j ↦ evalW (B j) (x i) (y i kk))))
    (hDx : ∀ i, IsUnit (D.eval (x i)))
    (t Y : Fin g → O) (ht : ∀ i, ϖ ∣ t i) (hYy : ∀ i, ϖ ∣ Y i - y i ⟨0, hn⟩)
    (c : Fin n → O[X]) (hdeg : ∀ j, c j ≠ 0 → (c j).natDegree + δ j ≤ (m + 1) * g)
    (hprim : ¬ ∀ j, C ϖ ∣ c j)
    (hQ : ∀ i, VanishAtG F (PsiC B c) (x i + t i) (Y i) (m + 1))
    (hS : ∀ i (kk : Fin n), (kk : ℕ) ≠ 0 → VanishAtG F (PsiC B c) (x i) (y i kk) (m + 1))
    (hNS : ∀ q : Fin n → (IsLocalRing.ResidueField O)[X],
      (∀ j, q j ≠ 0 → (q j).natDegree + δ j ≤ g) →
      (∀ i (kk : Fin n), (kk : ℕ) ≠ 0 →
        evalW (PsiC (fun j ↦ (B j).map (mapRingHom ρ)) q) (ρ (x i)) (ρ (y i kk)) = 0) →
      ∀ i, evalW (PsiC (fun j ↦ (B j).map (mapRingHom ρ)) q) (ρ (x i)) (ρ (y i ⟨0, hn⟩)) = 0) :
    ∀ i, t i = 0 := by
  classical
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  by_contra hne
  push_neg at hne
  obtain ⟨j0, hj0⟩ := hne
  have hex : ∃ N, ¬ ∀ i, ϖ ^ (N + 1) ∣ t i := by
    obtain ⟨N, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hj0 hϖ
    refine ⟨N, fun h ↦ ?_⟩
    have h1 := h j0
    rw [hv, pow_succ, mul_comm (ϖ ^ N)] at h1
    have h3 : ϖ ∣ (v : O) := (mul_dvd_mul_iff_right (pow_ne_zero N hϖ0)).mp h1
    exact hϖ.not_isUnit (isUnit_of_dvd_unit h3 v.isUnit)
  set N := Nat.find hex with hNdef
  have hN1 : ¬ ∀ i, ϖ ^ (N + 1) ∣ t i := Nat.find_spec hex
  have hN : ∀ i, ϖ ^ N ∣ t i := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · intro i; rw [h0, pow_zero]; exact one_dvd _
    · have := Nat.find_min hex (show N - 1 < N by omega)
      push_neg at this
      rwa [Nat.sub_add_cancel hpos] at this
  have hN0 : 1 ≤ N := by
    by_contra h0
    push_neg at h0
    apply hN1
    rw [Nat.lt_one_iff.mp h0, zero_add, pow_one]; exact ht
  choose τ hτ using hN
  choose VQ hVQ hjQ using hQ
  set u : O[X] := ∏ j, (X - C (x j)) with hu
  have hmap_u : u.map ρ = ∏ j, (X - C (ρ (x j))) := by simp [hu, Polynomial.map_prod]
  have hxk : Function.Injective fun i ↦ ρ (x i) := by
    intro i j hij
    by_contra hne
    have := (hx i j hne).map ρ
    rw [map_sub, show ρ (x i) = ρ (x j) from hij, sub_self] at this
    exact not_isUnit_zero this
  have hρt : ∀ i, ρ (t i) = 0 := fun i ↦ (Jac.res_eq_zero_iff hϖ _).mpr (ht i)
  have hρY : ∀ i, ρ (Y i) = ρ (y i ⟨0, hn⟩) := fun i ↦ by
    rw [← sub_eq_zero, ← map_sub]; exact (Jac.res_eq_zero_iff hϖ _).mpr (hYy i)
  set Bk : Fin n → (IsLocalRing.ResidueField O)[X][X] := fun j ↦ (B j).map (mapRingHom ρ) with hBk
  -- coordinates of the `j = 0` part
  set e0 : O[X] → Fin n → O[X] := fun P j ↦ if (j : ℕ) = 0 then P else 0 with he0
  have hPsi_e0 : ∀ P : O[X], PsiC B (e0 P) = Polynomial.C (P * D) := by
    intro P
    rw [PsiC, Finset.sum_eq_single ⟨0, hn⟩]
    · simp only [he0, if_pos rfl, hB0, map_mul]
    · intro j _ hj
      simp only [he0]
      rw [if_neg (fun h ↦ hj (Fin.ext h)), map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsplit : ∀ (a : O) (α : Fin n → O[X]) (r : ℕ) (z : O) (V : O[X]),
      jetN (PsiC B fun j ↦ e0 (C a * u ^ (m + 1)) j + C (ϖ ^ r) * α j) z V =
        C a * (u ^ (m + 1) * D).comp (X + C z) + C (ϖ ^ r) * jetN (PsiC B α) z V := by
    intro a α r z V
    rw [PsiC_add, jetN_add, hPsi_e0, PsiC_C_mul, jetN_C_poly_mul, jetN_const, C_comp, mul_assoc,
      mul_comp, C_comp]
  have hU0 : ∀ i, X ^ (m + 1) ∣ (u ^ (m + 1) * D).comp (X + C (x i)) := fun i ↦ by
    obtain ⟨R₁, R₂, h⟩ := uD_pow_comp x i 0 m D
    rw [add_zero] at h
    rw [h]; simp
  have hdegU : (u ^ (m + 1)).natDegree = g * (m + 1) := by
    rw [(monic_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)).natDegree_pow,
      natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_sub_C (x i)]
    simp [mul_comm]
  have hρϖ : ∀ e, 1 ≤ e → ρ (ϖ ^ e) = 0 := fun e he ↦ by
    rw [Jac.res_eq_zero_iff hϖ]; exact dvd_pow_self ϖ (by omega)
  have hdetk : ∀ i (V : Fin n → (IsLocalRing.ResidueField O)[X]),
      (∀ kk, (V kk).coeff 0 = ρ (y i kk)) →
      IsUnit (Matrix.det (Matrix.of fun kk j ↦ evalW (Bk j) (ρ (x i)) ((V kk).coeff 0))) := by
    intro i V hV
    have e : (Matrix.of fun kk j ↦ evalW (Bk j) (ρ (x i)) ((V kk).coeff 0)) =
        (Matrix.of fun kk j ↦ evalW (B j) (x i) (y i kk)).map ρ := by
      ext kk j
      simp only [Matrix.of_apply, Matrix.map_apply, hV, hBk, evalW_mapG]
    rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hdet i).map ρ
  -- reduced jets and vanishing of a layer at all fibre points
  have hlayer : ∀ (a : O) (α : Fin n → O[X]) (r : ℕ), r < N →
      c = (fun j ↦ e0 (C a * u ^ (m + 1)) j + C (ϖ ^ r) * α j) →
      ∃ V : Fin g → Fin n → (IsLocalRing.ResidueField O)[X],
        (∀ i kk, (V i kk).coeff 0 = ρ (y i kk)) ∧
        ∀ i kk, X ^ (m + 1) ∣ jetN (PsiC Bk fun j ↦ (α j).map ρ) (ρ (x i)) (V i kk) := by
    intro a α r hr hae
    have hjets : ∀ i (kk : Fin n), ∃ V : (IsLocalRing.ResidueField O)[X],
        V.coeff 0 = ρ (y i kk) ∧
        X ^ (m + 1) ∣ jetN (PsiC Bk fun j ↦ (α j).map ρ) (ρ (x i)) V := by
      intro i kk
      by_cases hkk : (kk : ℕ) = 0
      · have e : kk = ⟨0, hn⟩ := Fin.ext hkk
        subst e
        have hj := hjQ i
        obtain ⟨R₁, R₂, hUi⟩ := uD_pow_comp x i (t i) m D
        rw [hae, hsplit, hUi, hτ i] at hj
        set κ := (m + 1 : O) * (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1) * D.eval (x i)
        have e : C a * (X ^ (m + 1) * R₁ + C ((m + 1 : O) * (ϖ ^ N * τ i) *
            (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1) * D.eval (x i)) * X ^ m +
            C ((ϖ ^ N * τ i) ^ 2) * R₂) + C (ϖ ^ r) * jetN (PsiC B α) (x i + ϖ ^ N * τ i) (VQ i) =
            X ^ (m + 1) * (C a * R₁) + C (ϖ ^ r) * (jetN (PsiC B α) (x i + ϖ ^ N * τ i) (VQ i) +
              C (ϖ ^ (N - r)) * (C (a * κ * τ i) * X ^ m + C (a * ϖ ^ N * τ i ^ 2) * R₂)) := by
          have hpow : (ϖ : O) ^ N = ϖ ^ r * ϖ ^ (N - r) := by
            rw [← pow_add]; congr 1; omega
          rw [hpow]; simp only [κ, map_mul, map_pow, map_add]; ring
        rw [e] at hj
        have hj2 := Jac.X_pow_dvd_of_C_mul (pow_ne_zero r hϖ0)
          ((dvd_add_right (dvd_mul_right _ _)).mp hj)
        have hj3 := Polynomial.map_dvd ρ hj2
        simp only [Polynomial.map_add, Polynomial.map_mul, map_C, hρϖ (N - r) (by omega), map_zero,
          zero_mul, add_zero, Polynomial.map_pow, Polynomial.map_X] at hj3
        rw [jetN_map, PsiC_map, map_add, map_mul, hρϖ N hN0, zero_mul, add_zero] at hj3
        refine ⟨(VQ i).map ρ, ?_, hj3⟩
        rw [coeff_map, (hVQ i).1, hρY]
      · obtain ⟨W, hW, hj⟩ := hS i kk hkk
        rw [hae, hsplit] at hj
        have hj2 := Jac.X_pow_dvd_of_C_mul (pow_ne_zero r hϖ0)
          ((dvd_add_right (Dvd.dvd.mul_left (hU0 i) _)).mp hj)
        have hj3 := Polynomial.map_dvd ρ hj2
        rw [Polynomial.map_pow, Polynomial.map_X, jetN_map, PsiC_map] at hj3
        exact ⟨W.map ρ, by rw [coeff_map, hW.1], hj3⟩
    choose V hV0 hVj using hjets
    exact ⟨V, hV0, hVj⟩
  have hαdegk : ∀ α : Fin n → O[X], (∀ j, α j ≠ 0 → (α j).natDegree + δ j ≤ (m + 1) * g) →
      ∀ j, (α j).map ρ ≠ 0 → ((α j).map ρ).natDegree + δ j ≤ (m + 1) * g := by
    intro α hα j hj
    have hαj : α j ≠ 0 := fun h0 ↦ hj (by rw [h0, Polynomial.map_zero])
    exact le_trans (Nat.add_le_add_right natDegree_map_le _) (hα j hαj)
  -- peeling off the layers
  have layers : ∀ r ≤ N, ∃ (a : O) (α : Fin n → O[X]),
      c = (fun j ↦ e0 (C a * u ^ (m + 1)) j + C (ϖ ^ r) * α j) ∧
      ∀ j, α j ≠ 0 → (α j).natDegree + δ j ≤ (m + 1) * g := by
    intro r
    induction r with
    | zero =>
      intro _
      refine ⟨0, c, ?_, hdeg⟩
      funext j
      simp only [he0, map_zero, zero_mul, ite_self, pow_zero, map_one, one_mul, zero_add]
    | succ r ih =>
      intro hr
      obtain ⟨a, α, hae, hαbd⟩ := ih (by omega)
      obtain ⟨V, hV0, hVj⟩ := hlayer a α r (by omega) hae
      obtain ⟨hj1, a', ha'⟩ := structure_modG Bk δ hn hδ (fun i ↦ ρ (x i)) hxk V
        (fun i ↦ hdetk i (V i) (hV0 i)) (fun j ↦ (α j).map ρ) (hαdegk α hαbd) hVj
      obtain ⟨a'', ha''⟩ := IsLocalRing.residue_surjective a'
      have hred : ∀ j, (α j - e0 (C a'' * u ^ (m + 1)) j).map ρ = 0 := by
        intro j
        rw [Polynomial.map_sub]
        by_cases hj : (j : ℕ) = 0
        · have e : j = ⟨0, hn⟩ := Fin.ext hj
          subst e
          simp only [he0, if_pos rfl, Polynomial.map_mul, map_C, ha'', Polynomial.map_pow, hmap_u]
          rw [ha']; ring
        · simp only [he0, if_neg hj, Polynomial.map_zero, sub_zero]
          exact hj1 j hj
      choose α' hα' hα'd using fun j ↦ coord_div hϖ _ (hred j)
      refine ⟨a + ϖ ^ r * a'', α', ?_, fun j hj ↦ ?_⟩
      · funext j
        have h1 := hα' j
        have hαj : α j = e0 (C a'' * u ^ (m + 1)) j + C ϖ * α' j := by rw [← h1]; ring
        rw [congrFun hae j, hαj]
        by_cases hj : (j : ℕ) = 0
        · simp only [he0, if_pos hj, map_add, map_mul, map_pow]; ring
        · simp only [he0, if_neg hj, map_pow, map_mul]; ring
      · rcases hα'd j with h0 | h0
        · exact absurd h0 hj
        rw [h0]
        by_cases hj0 : (j : ℕ) = 0
        · have e : j = ⟨0, hn⟩ := Fin.ext hj0
          subst e
          simp only [he0, if_pos rfl]
          have h1 : (α ⟨0, hn⟩ - C a'' * u ^ (m + 1)).natDegree ≤
              max (α ⟨0, hn⟩).natDegree (g * (m + 1)) :=
            (natDegree_sub_le _ _).trans (max_le_max le_rfl
              ((natDegree_C_mul_le _ _).trans hdegU.le))
          rw [hδ0, add_zero]
          refine h1.trans (max_le ?_ (by rw [mul_comm]))
          by_cases hα0 : α ⟨0, hn⟩ = 0
          · rw [hα0, natDegree_zero]; exact Nat.zero_le _
          · have := hαbd _ hα0; rw [hδ0, add_zero] at this; exact this
        · simp only [he0, if_neg hj0, sub_zero]
          have hαj : α j ≠ 0 := by
            intro h0'
            have h1 := hα' j
            simp only [he0, if_neg hj0, sub_zero, h0'] at h1
            exact hj ((mul_eq_zero.mp h1.symm).resolve_left (C_ne_zero.mpr hϖ0))
          exact hαbd j hαj
  obtain ⟨a, α, hae, hαbd⟩ := layers N le_rfl
  -- `a` is a unit
  have hc : ρ a ≠ 0 := by
    intro hc0
    apply hprim
    intro j
    rw [congrFun hae j]
    refine dvd_add ?_ ((_root_.map_dvd C (dvd_pow_self ϖ (by omega))).mul_right _)
    by_cases hj : (j : ℕ) = 0
    · simp only [he0, if_pos hj]
      exact (_root_.map_dvd C ((Jac.res_eq_zero_iff hϖ _).mp hc0)).mul_right _
    · simp only [he0, if_neg hj]; exact dvd_zero _
  -- the jets at level `N`
  set W : Fin g → Fin n → O[X] := fun i kk ↦
    if h : (kk : ℕ) ≠ 0 then Classical.choose (hS i kk h) else VQ i with hW
  set V : Fin g → Fin n → (IsLocalRing.ResidueField O)[X] := fun i kk ↦ (W i kk).map ρ with hV
  have hV0 : ∀ i kk, (V i kk).coeff 0 = ρ (y i kk) := by
    intro i kk
    simp only [hV, hW, coeff_map]
    split_ifs with h
    · rw [(Classical.choose_spec (hS i kk h)).1.1]
    · have e : kk = ⟨0, hn⟩ := Fin.ext (by push_neg at h; exact h)
      subst e
      rw [(hVQ i).1, hρY]
  set κ : Fin g → O := fun i ↦ a * ((m + 1 : O) * τ i *
    (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1) * D.eval (x i)) with hκ
  have h0 : ∀ i, X ^ (m + 1) ∣ jetN (PsiC Bk fun j ↦ (α j).map ρ) (ρ (x i)) (V i ⟨0, hn⟩) -
      C (ρ (-κ i)) * X ^ m := by
    intro i
    have hj := hjQ i
    obtain ⟨R₁, R₂, hUi⟩ := uD_pow_comp x i (t i) m D
    rw [hae, hsplit, hUi, hτ i] at hj
    have e : C a * (X ^ (m + 1) * R₁ + C ((m + 1 : O) * (ϖ ^ N * τ i) *
        (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1) * D.eval (x i)) * X ^ m +
        C ((ϖ ^ N * τ i) ^ 2) * R₂) + C (ϖ ^ N) * jetN (PsiC B α) (x i + ϖ ^ N * τ i) (VQ i) =
        X ^ (m + 1) * (C a * R₁) + C (ϖ ^ N) * (jetN (PsiC B α) (x i + ϖ ^ N * τ i) (VQ i) -
          C (-κ i) * X ^ m + C (a * ϖ ^ N * τ i ^ 2) * R₂) := by
      simp only [hκ, map_mul, map_pow, map_add, map_neg]; ring
    rw [e] at hj
    have hj2 := Jac.X_pow_dvd_of_C_mul (pow_ne_zero N hϖ0)
      ((dvd_add_right (dvd_mul_right _ _)).mp hj)
    have hj3 := Polynomial.map_dvd ρ hj2
    have hz2 : ρ (a * ϖ ^ N * τ i ^ 2) = 0 := by
      rw [map_mul, map_mul, hρϖ N hN0, mul_zero, zero_mul]
    rw [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, map_C,
      map_C, hz2, map_zero, zero_mul, add_zero, Polynomial.map_pow, Polynomial.map_X, jetN_map,
      PsiC_map, map_add, map_mul, hρϖ N hN0, zero_mul, add_zero, Polynomial.map_pow,
      Polynomial.map_X] at hj3
    have hVi : V i ⟨0, hn⟩ = (VQ i).map ρ := by
      simp only [hV, hW, dif_neg (show ¬ ((⟨0, hn⟩ : Fin n) : ℕ) ≠ 0 from fun h ↦ h rfl)]
    rw [hVi]
    exact hj3
  have hk : ∀ i (kk : Fin n), (kk : ℕ) ≠ 0 →
      X ^ (m + 1) ∣ jetN (PsiC Bk fun j ↦ (α j).map ρ) (ρ (x i)) (V i kk) := by
    intro i kk hkk
    have hspec := Classical.choose_spec (hS i kk hkk)
    obtain ⟨Wj, hWj⟩ : ∃ Wj, Wj = Classical.choose (hS i kk hkk) := ⟨_, rfl⟩
    have hj : X ^ (m + 1) ∣ jetN (PsiC B c) (x i) Wj := by rw [hWj]; exact hspec.2
    rw [hae, hsplit] at hj
    have hj2 := Jac.X_pow_dvd_of_C_mul (pow_ne_zero N hϖ0)
      ((dvd_add_right (Dvd.dvd.mul_left (hU0 i) _)).mp hj)
    have hj3 := Polynomial.map_dvd ρ hj2
    rw [Polynomial.map_pow, Polynomial.map_X, jetN_map, PsiC_map] at hj3
    have hVi : V i kk = Wj.map ρ := by
      simp only [hV, hW, dif_pos hkk, hWj]
    rw [hVi]
    exact hj3
  have hlam := tangentG Bk δ hn (fun i ↦ ρ (x i)) hxk V (fun i ↦ hdetk i (V i) (hV0 i))
    (fun j ↦ (α j).map ρ) (hαdegk α hαbd) (fun i ↦ ρ (-κ i)) h0 hk (by
      intro q hq hq0 i
      have := hNS q hq (fun i kk hkk ↦ by rw [← hV0 i kk]; exact hq0 i kk hkk) i
      rw [hV0]; exact this)
  apply hN1
  intro i
  have h1 := hlam i
  rw [map_neg, neg_eq_zero] at h1
  have hℓk : ρ ((m + 1 : ℕ) : O) ≠ 0 := (hℓ.map ρ).ne_zero
  have hck : ρ (∏ j ∈ Finset.univ.erase i, (x i - x j)) ^ (m + 1) ≠ 0 := by
    refine pow_ne_zero _ (IsUnit.ne_zero ?_)
    refine IsUnit.map ρ ?_
    exact (IsUnit.prod_iff.mpr fun j hj ↦ hx i j (Finset.ne_of_mem_erase hj).symm)
  have hDk : ρ (D.eval (x i)) ≠ 0 := ((hDx i).map ρ).ne_zero
  push_cast at hℓk
  simp only [hκ, map_mul, map_pow] at h1
  have hτ0 : ρ (τ i) = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hc
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact absurd h hℓk
          · exact h
        · exact absurd h (by rw [← map_pow]; exact hck)
      · exact absurd h hDk
  rw [hτ i, pow_succ]
  exact mul_dvd_mul_left _ ((Jac.res_eq_zero_iff hϖ _).mp hτ0)

end Main

end GTors
