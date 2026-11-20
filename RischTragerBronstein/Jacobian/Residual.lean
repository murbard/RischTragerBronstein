import RischTragerBronstein.Jacobian.Descend

/-!
# The residual zeros of the auxiliary function

Let `ψ = a + b y` over a Henselian discrete valuation ring `O` have pole order `≤ 2g + deg Γ`
and vanish on `σ(Γ + E₀)` (`E₀ = ∑ Pᵢ`), and suppose its reduction is `c · ub · σγ̄` where `γ̄`
vanishes exactly on `Γ̄` (its norm is `c₁ · wpoly Γ̄`). Then (`residual_zeros`) for every `i`
there is a point `Qᵢ = (zᵢ, Yᵢ) ≡ Pᵢ` with `ψ(Qᵢ) = 0`: the norm of `ψ` is `wpoly(Γ + E₀) · R`
with `R̄ = κ ub`, `R` has a Hensel root `zᵢ ≡ xᵢ`, and the zero over `zᵢ` lies on the `Pᵢ`-branch
(`sigma_disc_unique`, and a double-root argument when `zᵢ = xᵢ`).
-/

open Polynomial

namespace Jac

section General

variable {R : Type*} [CommRing R]

lemma VanishAt.eval_eq_zero {f a b : R[X]} {x₀ Y₀ : R} {k : ℕ} (h : VanishAt f a b x₀ Y₀ k)
    (hk : 1 ≤ k) : a.eval x₀ + b.eval x₀ * Y₀ = 0 := by
  obtain ⟨V, hV, hj⟩ := h
  have h1 := (pow_dvd_pow X hk).trans hj
  rw [pow_one, X_dvd_iff] at h1
  simp only [jet, coeff_add, coeff_zero_eq_eval_zero, eval_mul, eval_comp, eval_add, eval_X,
    eval_C, zero_add] at h1
  rwa [← coeff_zero_eq_eval_zero, hV.1] at h1

lemma natDegree_hnorm_le {g : ℕ} {f : R[X]} (hf : f.natDegree ≤ 2 * g + 1) {ψ : R[X] × R[X]}
    {N : ℕ} (h : PoleLE g ψ N) : (hnorm f ψ).natDegree ≤ N := by
  obtain ⟨ha, hb⟩ := h
  unfold hnorm
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact natDegree_pow_le.trans (by omega)
  · rcases hb with hb | hb
    · simp [hb]
    · refine natDegree_mul_le.trans ?_
      have := natDegree_pow_le (p := ψ.2) (n := 2)
      omega

lemma hnorm_hsmul (f w : R[X]) (ψ : R[X] × R[X]) :
    hnorm f (hsmul w ψ) = w ^ 2 * hnorm f ψ := by
  simp only [hnorm, hsmul]; ring

lemma hnorm_hconj (f : R[X]) (ψ : R[X] × R[X]) : hnorm f (hconj ψ) = hnorm f ψ := by
  simp only [hnorm, hconj]; ring

lemma hnorm_map {S : Type*} [CommRing S] (φ : R →+* S) (f : R[X]) (ψ : R[X] × R[X]) :
    (hnorm f ψ).map φ = hnorm (f.map φ) (ψ.1.map φ, ψ.2.map φ) := by
  simp [hnorm, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow]

end General

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [HenselianRing O (IsLocalRing.maximalIdeal O)]

local notation "k" => IsLocalRing.ResidueField O
local notation "ρ" => IsLocalRing.residue O

lemma mem_max_iff (z : O) : z ∈ IsLocalRing.maximalIdeal O ↔ ρ z = 0 :=
  (IsLocalRing.residue_eq_zero_iff z).symm

lemma isUnit_of_res_ne_zero {z : O} (h : ρ z ≠ 0) : IsUnit z := by
  by_contra hu
  exact h ((mem_max_iff z).mp ((IsLocalRing.mem_maximalIdeal z).mpr hu))

/-- The derivative of `∏ (x − xⱼ)` at `xᵢ`. -/
lemma derivative_prod_eval {F : Type*} [Field F] {g : ℕ} (x : Fin g → F) (i : Fin g) :
    (∏ j, (X - C (x j))).derivative.eval (x i) = ∏ j ∈ Finset.univ.erase i, (x i - x j) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), derivative_mul,
    derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul,
    eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, eval_prod]
  simp

/-- **The residual zeros.** -/
theorem residual_zeros {ϖ : O} (hϖ : Irreducible ϖ) (h2 : IsUnit (2 : O)) {g : ℕ} (f : O[X])
    (hf : f.natDegree ≤ 2 * g + 1) (x y : Fin g → O) (hyu : ∀ i, IsUnit (y i))
    (hyf : ∀ i, y i ^ 2 = f.eval (x i)) (hx : ∀ i j, i ≠ j → IsUnit (x i - x j))
    (Γ : EDiv O) (hon : OnCurve f Γ) (hΓx : Γ.Pairwise fun q q' ↦ IsUnit (q.1 - q'.1))
    (hΓE : ∀ q ∈ Γ, ∀ i, IsUnit (q.1 - x i))
    (ψ : O[X] × O[X]) (hψp : PoleLE g ψ (2 * g + edeg Γ))
    (hψv : Vanishes f ψ (econj (Γ ++ E0L x y)))
    (γ : k[X] × k[X]) (c c₁ : k) (hc : c ≠ 0) (hc₁ : c₁ ≠ 0)
    (hγn : hnorm (f.map ρ) γ = C c₁ * wpoly (emap ρ Γ))
    (hstr : (ψ.1.map ρ, ψ.2.map ρ) = hsmul (C c * ∏ i, (X - C (ρ (x i)))) (hconj γ)) :
    ∀ i, ∃ z Y : O, z - x i ∈ IsLocalRing.maximalIdeal O ∧ Y - y i ∈ IsLocalRing.maximalIdeal O ∧
      Y ^ 2 = f.eval z ∧ ψ.1.eval z + ψ.2.eval z * Y = 0 := by
  classical
  intro i
  set d := edeg Γ
  set u : O[X] := ∏ j, (X - C (x j))
  set ub : k[X] := ∏ j, (X - C (ρ (x j)))
  have hmapu : u.map ρ = ub := by simp [u, ub, Polynomial.map_prod]
  have hxk : Function.Injective fun j ↦ ρ (x j) := by
    intro a b hab
    by_contra hne
    have := (hx a b hne).map ρ
    rw [map_sub, show ρ (x a) = ρ (x b) from hab, sub_self] at this
    exact not_isUnit_zero this
  -- the norm factorisation over `O`
  set N := hnorm f ψ
  set W := wpoly (Γ ++ E0L x y)
  have hpair : (Γ ++ E0L x y).Pairwise fun q q' ↦ IsUnit (q.1 - q'.1) := by
    rw [List.pairwise_append]
    refine ⟨hΓx, ?_, ?_⟩
    · simp only [E0L, List.pairwise_ofFn]
      intro a b hab; exact hx a b (Fin.ne_of_lt hab)
    · intro q hq e he
      simp only [E0L, List.mem_ofFn] at he
      obtain ⟨j, rfl⟩ := he
      exact hΓE q hq j
  have hWN : W ∣ N := by
    refine wpoly_dvd' hpair fun q hq ↦ ?_
    have := hψv (q.1, -q.2.1, q.2.2) (List.mem_map_of_mem hq)
    exact this.dvd_hnorm
  obtain ⟨Rp, hRp⟩ := hWN
  have hWm : W.Monic := wpoly_monic _
  have hWd : W.natDegree = d + g := by
    rw [natDegree_wpoly, edeg_append, edeg_E0L]
  have hNd : N.natDegree ≤ 2 * g + d := natDegree_hnorm_le hf hψp
  have hRd : Rp.natDegree ≤ g := by
    by_cases hR0 : Rp = 0
    · simp [hR0]
    have := congrArg natDegree hRp
    rw [natDegree_mul hWm.ne_zero hR0, hWd] at this
    omega
  -- reduction: `R̄ = κ ub`
  have hWmap : W.map ρ = wpoly (emap ρ Γ) * ub := by
    rw [← wpoly_emap, show emap ρ (Γ ++ E0L x y) = emap ρ Γ ++ emap ρ (E0L x y) by
      simp [emap], wpoly_append]
    congr 1
    simp [wpoly, emap, E0L, List.prod_ofFn, ub]
  have hNmap : N.map ρ = C (c ^ 2 * c₁) * ub ^ 2 * wpoly (emap ρ Γ) := by
    rw [hnorm_map, hstr, hnorm_hsmul, hnorm_hconj, hγn]
    simp only [map_mul, map_pow]; ring
  have hRbar : Rp.map ρ = C (c ^ 2 * c₁) * ub := by
    have e := congrArg (Polynomial.map ρ) hRp
    rw [hNmap, Polynomial.map_mul, hWmap] at e
    have hne : wpoly (emap ρ Γ) * ub ≠ 0 :=
      mul_ne_zero (wpoly_monic _).ne_zero
        (monic_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C _).ne_zero
    apply mul_left_cancel₀ hne
    rw [← e]; ring
  have hκ : c ^ 2 * c₁ ≠ 0 := mul_ne_zero (pow_ne_zero 2 hc) hc₁
  have hubd : ub.natDegree = g := by
    have := natDegree_prod_pow (fun j ↦ ρ (x j)) 1
    simpa [ub] using this
  have hubm : ub.Monic := monic_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C _
  have hRg : ρ (Rp.coeff g) = c ^ 2 * c₁ := by
    rw [← coeff_map, hRbar, coeff_C_mul, ← hubd, hubm.coeff_natDegree, mul_one]
  have hRu : IsUnit (Rp.coeff g) := isUnit_of_res_ne_zero (by rw [hRg]; exact hκ)
  -- the monic normalisation `R'`
  set R' := C (↑hRu.unit⁻¹ : O) * Rp
  have hR'map : R'.map ρ = ub := by
    have hinv : ρ (↑hRu.unit⁻¹ : O) * (c ^ 2 * c₁) = 1 := by
      rw [← hRg, ← map_mul]; simp
    rw [Polynomial.map_mul, map_C, hRbar, ← mul_assoc, ← C_mul, hinv, C_1, one_mul]
  have hR'm : R'.Monic := by
    have hRnd : Rp.natDegree = g := le_antisymm hRd (le_natDegree_of_ne_zero hRu.ne_zero)
    rw [Monic, leadingCoeff, natDegree_C_mul (Units.ne_zero _), hRnd, coeff_C_mul]
    simp
  -- Hensel: a root `z ≡ xᵢ`
  have hH1 : R'.eval (x i) ∈ IsLocalRing.maximalIdeal O := by
    rw [mem_max_iff, ← eval_map_apply, hR'map, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hH2 : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)
      (R'.derivative.eval (x i))) := by
    show IsUnit (ρ (R'.derivative.eval (x i)))
    rw [← eval_map_apply, ← derivative_map, hR'map]
    have := derivative_prod_eval (fun j ↦ ρ (x j)) i
    rw [this]
    refine (Finset.prod_ne_zero_iff.mpr fun j hj ↦ ?_).isUnit
    exact sub_ne_zero.mpr fun he ↦ (Finset.ne_of_mem_erase hj) (hxk he).symm
  obtain ⟨z, hzr, hzx⟩ := HenselianRing.is_henselian R' hR'm (x i) hH1 hH2
  have hRz : Rp.eval z = 0 := by
    have : R'.eval z = 0 := hzr
    rw [eval_mul, eval_C] at this
    exact (mul_eq_zero.mp this).resolve_left (Units.ne_zero _)
  -- Hensel again: `Y² = f(z)`, `Y ≡ yᵢ`
  have hfz : f.eval z - f.eval (x i) ∈ IsLocalRing.maximalIdeal O :=
    Ideal.mem_of_dvd _ (sub_dvd_eval_sub z (x i) f) hzx
  set P2 : O[X] := X ^ 2 - C (f.eval z)
  have hP2m : P2.Monic := by
    unfold P2; exact monic_X_pow_sub_C _ (by norm_num)
  have hP21 : P2.eval (y i) ∈ IsLocalRing.maximalIdeal O := by
    simp only [P2, eval_sub, eval_pow, eval_X, eval_C, hyf i]
    have := (IsLocalRing.maximalIdeal O).neg_mem hfz
    rwa [neg_sub] at this
  have hP22 : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)
      (P2.derivative.eval (y i))) := by
    have e : P2.derivative.eval (y i) = 2 * y i := by
      simp only [P2, derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C,
        eval_pow, eval_X]
      norm_num
    rw [e]; exact (h2.mul (hyu i)).map _
  obtain ⟨Y, hYr, hYy⟩ := HenselianRing.is_henselian P2 hP2m (y i) hP21 hP22
  have hY2 : Y ^ 2 = f.eval z := by
    have : P2.eval Y = 0 := hYr
    simp only [P2, eval_sub, eval_pow, eval_X, eval_C] at this
    exact sub_eq_zero.mp this
  refine ⟨z, Y, hzx, hYy, hY2, ?_⟩
  -- the zero is on the `Pᵢ`-branch
  have hNz : N.eval z = 0 := by rw [hRp, eval_mul, hRz, mul_zero]
  have hfac : (ψ.1.eval z + ψ.2.eval z * Y) * (ψ.1.eval z - ψ.2.eval z * Y) = 0 := by
    have : N.eval z = ψ.1.eval z ^ 2 - ψ.2.eval z ^ 2 * f.eval z := by
      simp [N, hnorm]
    rw [← hNz, this, ← hY2]; ring
  rcases mul_eq_zero.mp hfac with h | hσ
  · exact h
  -- otherwise both `σQ` and `σPᵢ` are zeros: the disc argument
  have h2y : IsUnit (2 * y i) := h2.mul (hyu i)
  set w : O := ↑h2y.unit⁻¹
  have hw : w * (2 * y i) = 1 := by simp [w]
  have hσP : ψ.1.eval (x i) - ψ.2.eval (x i) * y i = 0 := by
    have hv := hψv (x i, -y i, 1) (by
      simp only [econj, List.map_append, List.mem_append, E0L, List.map_ofFn, List.mem_ofFn]
      right; exact ⟨i, rfl⟩)
    have := hv.eval_eq_zero le_rfl
    linear_combination this
  -- the first-order coefficient is a unit
  have hΛ : IsUnit (ψ.1.derivative.eval (x i) - ψ.2.derivative.eval (x i) * y i -
      ψ.2.eval (x i) * f.derivative.eval (x i) * w) := by
    apply isUnit_of_res_ne_zero
    have ha : ψ.1.map ρ = C c * ub * γ.1 := congrArg Prod.fst hstr
    have hb : ψ.2.map ρ = C c * ub * -γ.2 := congrArg Prod.snd hstr
    have hux : ub.eval (ρ (x i)) = 0 := by
      simp only [ub, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    set v : k := ∏ j ∈ Finset.univ.erase i, (ρ (x i) - ρ (x j))
    have hu' : ub.derivative.eval (ρ (x i)) = v := derivative_prod_eval (fun j ↦ ρ (x j)) i
    have hv0 : v ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj ↦
      sub_ne_zero.mpr fun he ↦ (Finset.ne_of_mem_erase hj) (hxk he).symm
    have e1 : ρ (ψ.1.derivative.eval (x i)) = c * v * γ.1.eval (ρ (x i)) := by
      rw [← eval_map_apply, ← derivative_map, ha]
      simp only [derivative_mul, derivative_C, zero_mul, zero_add, eval_add, eval_mul, eval_C,
        hux, hu', v]
      ring
    have e2 : ρ (ψ.2.derivative.eval (x i)) = -(c * v * γ.2.eval (ρ (x i))) := by
      rw [← eval_map_apply, ← derivative_map, hb]
      simp only [derivative_mul, derivative_C, zero_mul, zero_add, eval_add, eval_mul, eval_C,
        hux, hu', derivative_neg, eval_neg, v]
      ring
    have e3 : ρ (ψ.2.eval (x i)) = 0 := by
      rw [← eval_map_apply, hb]; simp [hux]
    rw [map_sub, map_sub, map_mul, map_mul, map_mul, e1, e2, e3]
    have hγP : γ.1.eval (ρ (x i)) + γ.2.eval (ρ (x i)) * ρ (y i) ≠ 0 := by
      intro h0
      have hN := congrArg (eval (ρ (x i))) hγn
      have hyk : ρ (y i) ^ 2 = (f.map ρ).eval (ρ (x i)) := by
        rw [eval_map_apply, ← hyf i, map_pow]
      rw [eval_mul, eval_C] at hN
      have hwn : (wpoly (emap ρ Γ)).eval (ρ (x i)) ≠ 0 := by
        apply eval_wpoly_ne_zero
        intro q hq he
        obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
        have := (hΓE q' hq' i).map ρ
        rw [map_sub] at this
        exact not_isUnit_zero (by rwa [show ρ q'.1 = ρ (x i) from he, sub_self] at this)
      apply mul_ne_zero hc₁ hwn
      rw [← hN]
      simp only [hnorm, eval_sub, eval_pow, eval_mul, ← hyk]
      linear_combination (γ.1.eval (ρ (x i)) - γ.2.eval (ρ (x i)) * ρ (y i)) * h0
    have : c * v * γ.1.eval (ρ (x i)) - -(c * v * γ.2.eval (ρ (x i))) * ρ (y i) -
        0 * ρ (f.derivative.eval (x i)) * ρ w =
        c * v * (γ.1.eval (ρ (x i)) + γ.2.eval (ρ (x i)) * ρ (y i)) := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero hc hv0) hγP
  have hzx' : z = x i := sigma_disc_unique hw (hyf i) hY2 hzx hYy hσP hσ hΛ
  -- hence `Y = yᵢ` and the double root argument
  have hYe : Y = y i := by
    have hsum : IsUnit (Y + y i) := by
      have : Y + y i = 2 * y i + (Y - y i) := by ring
      rw [this]; exact isUnit_add_mem h2y hYy
    have : (Y - y i) * (Y + y i) = 0 := by
      rw [show (Y - y i) * (Y + y i) = Y ^ 2 - y i ^ 2 by ring, hY2, hzx', hyf i, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hsum.ne_zero)
  rw [hzx', hYe]
  -- `(x − xᵢ)² ∣ N`
  have hsq : (X - C (x i)) ^ 2 ∣ N := by
    rw [hRp, pow_two]
    refine mul_dvd_mul ?_ ?_
    · have : (X - C (x i)) ∣ wpoly (E0L x y) := by
        rw [wpoly_E0L]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      exact this.trans (by
        rw [show W = wpoly Γ * wpoly (E0L x y) from wpoly_append _ _]; exact dvd_mul_left _ _)
    · rw [dvd_iff_isRoot, IsRoot, ← hzx']; exact hRz
  obtain ⟨Q, hQ⟩ := hsq
  have hN' : N.derivative.eval (x i) = 0 := by
    rw [hQ]; simp [derivative_mul, derivative_pow]
  have hN'e : N.derivative.eval (x i) = 2 * y i * ψ.2.eval (x i) *
      (ψ.1.derivative.eval (x i) - ψ.2.derivative.eval (x i) * y i -
        ψ.2.eval (x i) * f.derivative.eval (x i) * w) := by
    have hα : ψ.1.eval (x i) = ψ.2.eval (x i) * y i := by linear_combination hσP
    simp only [N, hnorm, pow_two, derivative_sub, derivative_mul, eval_sub, eval_add, eval_mul]
    rw [hα, ← hyf i]
    linear_combination (ψ.2.eval (x i) * ψ.2.eval (x i) * f.derivative.eval (x i)) * hw
  rw [hN'e] at hN'
  have hβ : ψ.2.eval (x i) = 0 := by
    rcases mul_eq_zero.mp hN' with h | h
    · exact (mul_eq_zero.mp h).resolve_left h2y.ne_zero
    · exact absurd h hΛ.ne_zero
  rw [hβ, zero_mul, add_zero]
  linear_combination hσP + y i * hβ

end Jac
