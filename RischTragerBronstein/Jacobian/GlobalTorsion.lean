import RischTragerBronstein.Jacobian.Residual

/-!
# Prime-to-`p` torsion is detected modulo `p`

`torsion_descends`: let `O` be a Henselian discrete valuation ring with `2 ∈ Oˣ` and fraction
field `K`, `y² = f(x)` with `deg f = 2g + 1` (leading coefficient a unit), `E₀ = ∑ Pᵢ` as in
`kernel_no_torsion`, and `Γ` an effective divisor over `O` whose points have pairwise distinct
abscissae modulo `ϖ`, also distinct from the `xᵢ`. If

* modulo `ϖ` some non-zero `γ̄` of pole order `≤ deg Γ` vanishes on `Γ̄` (the reduced divisor
  class is trivial), and
* over `K` some non-zero `Ξ` of pole order `≤ ℓ deg Γ` vanishes on `ℓ Γ`, `ℓ` a unit of `O`
  (the class has order dividing `ℓ`),

then over `K` some non-zero `γ` of pole order `≤ deg Γ` vanishes on `Γ` (the class is trivial).

In divisor language (with `Γ = D⁺ + σ D⁻` for a degree-zero divisor `D`): a class of order prime
to the residue characteristic which is trivial modulo `ϖ` is trivial.
-/

open Polynomial

namespace Jac

section Aux

variable {R : Type*} [CommRing R]

lemma vanishAt_one_of_eval {f a b : R[X]} {x₀ Y₀ : R} (hY : Y₀ ^ 2 = f.eval x₀)
    (hv : a.eval x₀ + b.eval x₀ * Y₀ = 0) : VanishAt f a b x₀ Y₀ 1 := by
  refine ⟨C Y₀, ⟨by simp, ?_⟩, ?_⟩
  · rw [pow_one, X_dvd_iff, coeff_sub, ← C_pow, coeff_C_zero, coeff_zero_eq_eval_zero,
      eval_comp, eval_add, eval_X, eval_C, zero_add, hY, sub_self]
  · rw [pow_one, X_dvd_iff, jet, coeff_add, mul_coeff_zero, coeff_C_zero,
      coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero, eval_comp, eval_comp]
    simpa using hv

lemma nodup_map_of_pairwise_unit {S : Type*} [CommRing S] [Nontrivial S] (φ : R →+* S)
    (Γ : EDiv R) (hΓ : Γ.Pairwise fun q q' ↦ IsUnit (q.1 - q'.1)) :
    (Γ.map fun q ↦ φ q.1).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  exact hΓ.imp fun {q q'} h he ↦ by
    have := h.map φ; rw [map_sub, he, sub_self] at this; exact not_isUnit_zero this

lemma econj_econj (Γ : EDiv R) : econj (econj Γ) = Γ := by
  simp [econj, Function.comp_def]

lemma edeg_econj' (Γ : EDiv R) : edeg (econj Γ) = edeg Γ := edeg_econj Γ

end Aux

variable {O K : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [HenselianRing O (IsLocalRing.maximalIdeal O)] [Field K] [Algebra O K] [IsFractionRing O K]

local notation "𝕜" => IsLocalRing.ResidueField O
local notation "ρ" => IsLocalRing.residue O
local notation "ι" => algebraMap O K

omit [HenselianRing O (IsLocalRing.maximalIdeal O)] in
lemma mem_max_iff_dvd {ϖ : O} (hϖ : Irreducible ϖ) (z : O) :
    z ∈ IsLocalRing.maximalIdeal O ↔ ϖ ∣ z := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton]

/-- **Torsion prime to the residue characteristic, trivial modulo `ϖ`, is trivial.** -/
theorem torsion_descends {ϖ : O} (hϖ : Irreducible ϖ) (h2 : IsUnit (2 : O)) {g : ℕ} (f : O[X])
    (hf : f.natDegree = 2 * g + 1) (hlc : IsUnit f.leadingCoeff)
    (x y : Fin g → O) (hyu : ∀ i, IsUnit (y i)) (hyf : ∀ i, y i ^ 2 = f.eval (x i))
    (hx : ∀ i j, i ≠ j → IsUnit (x i - x j))
    (Γ : EDiv O) (hon : OnCurve f Γ) (hΓx : Γ.Pairwise fun q q' ↦ IsUnit (q.1 - q'.1))
    (hΓE : ∀ q ∈ Γ, ∀ i, IsUnit (q.1 - x i))
    (γb : 𝕜[X] × 𝕜[X]) (hγ0 : γb ≠ (0, 0)) (hγp : PoleLE g γb (edeg Γ))
    (hγv : Vanishes (f.map ρ) γb (emap ρ Γ))
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ : IsUnit (ℓ : O))
    (Ξ : K[X] × K[X]) (hΞ0 : Ξ ≠ (0, 0)) (hΞp : PoleLE g Ξ (ℓ * edeg Γ))
    (hΞv : Vanishes (f.map ι) Ξ (escale ℓ (emap ι Γ))) :
    ∃ γ : K[X] × K[X], γ ≠ (0, 0) ∧ PoleLE g γ (edeg Γ) ∧ Vanishes (f.map ι) γ (emap ι Γ) := by
  classical
  set d := edeg Γ
  set ΓE := Γ ++ E0L x y
  have hι : Function.Injective ι := IsFractionRing.injective O K
  have hfK : (f.map ι).natDegree = 2 * g + 1 := by rw [natDegree_map_eq_of_injective hι, hf]
  have hfk : (f.map ρ).natDegree = 2 * g + 1 := by
    rw [natDegree_map_of_leadingCoeff_ne_zero _ ((hlc.map ρ).ne_zero), hf]
  have hfK' : (f.map ι).natDegree ≤ 2 * g + 1 := hfK.le
  have honE : OnCurve f (E0L x y) := by
    intro q hq
    simp only [E0L, List.mem_ofFn] at hq
    obtain ⟨i, rfl⟩ := hq
    exact ⟨h2.mul (hyu i), hyf i⟩
  have honΓE : OnCurve f ΓE := OnCurve.append.mpr ⟨hon, honE⟩
  have hedegE : edeg ΓE = d + g := by rw [edeg_append, edeg_E0L]
  -- S1: a function vanishing on `σ(Γ + E₀)` over `K`
  obtain ⟨ψK, hψK0, hψKp, hψKv⟩ := exists_vanishing (f.map ι) g (2 * g + d)
    (econj (emap ι ΓE)) (OnCurve.map honΓE).econj (g + d / 2 + 1)
    (if d = 0 then 0 else (d - 1) / 2 + 1) (by omega)
    (by split_ifs with h; exacts [Or.inl rfl, Or.inr (by omega)])
    (by rw [edeg_econj, edeg_emap, hedegE]; split_ifs with h <;> omega)
  -- S2: a primitive function over `O`
  obtain ⟨ψ, hprim, hψp, hψv, κ, hκ, hκ1, hκ2⟩ := descend hϖ (honΓE.econj)
    (g := g) hψK0 hψKp (by rw [emap_econj]; exact hψKv)
  -- S3: its reduction has the shape `c · ū · σγ̄`
  set ψb : 𝕜[X] × 𝕜[X] := (ψ.1.map ρ, ψ.2.map ρ)
  have hψb0 : ψb ≠ (0, 0) := by
    intro h
    apply hprim
    have h1 := congrArg Prod.fst h
    have h2' := congrArg Prod.snd h
    exact ⟨(C_dvd_iff_map hϖ _).mpr h1, (C_dvd_iff_map hϖ _).mpr h2'⟩
  have hxk : Function.Injective fun j ↦ ρ (x j) := by
    intro a b hab
    by_contra hne
    have := (hx a b hne).map ρ
    rw [map_sub, show ρ (x a) = ρ (x b) from hab, sub_self] at this
    exact not_isUnit_zero this
  have hΓk : ((econj (emap ρ Γ)).map Prod.fst).Nodup := by
    have := nodup_map_of_pairwise_unit ρ Γ hΓx
    simpa [econj, emap, Function.comp_def] using this
  have hψbv : Vanishes (f.map ρ) ψb (emap ρ (econj ΓE)) := hψv.map
  rw [emap_econj, show emap ρ ΓE = emap ρ Γ ++ emap ρ (E0L x y) by simp [ΓE, emap],
    econj_append, Vanishes.append] at hψbv
  have hψbp : PoleLE g ψb (2 * g + edeg (econj (emap ρ Γ))) := by
    rw [edeg_econj, edeg_emap]
    refine ⟨(Nat.mul_le_mul_left 2 natDegree_map_le).trans hψp.1, ?_⟩
    rcases hψp.2 with h | h
    · left; simp [ψb, h]
    · right
      exact (Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.mul_le_mul_left 2 natDegree_map_le) _) _).trans h
  obtain ⟨c, hc⟩ := structure_lemma hfk hΓk (OnCurve.map hon).econj hxk
    (fun i q hq he ↦ by
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
      obtain ⟨q'', hq'', rfl⟩ := List.mem_map.mp hq'
      have := (hΓE q'' hq'' i).map ρ
      simp only [map_sub] at this he
      rw [he, sub_self] at this
      exact not_isUnit_zero this)
    (fun i ↦ by have := (h2.mul (hyu i)).map ρ; rwa [map_mul, map_ofNat] at this)
    (fun i ↦ by rw [eval_map_apply, ← hyf i, map_pow])
    (γ := hconj γb) (χ := ψb)
    (by intro h; apply hγ0; simp only [hconj, Prod.mk.injEq, neg_eq_zero] at h;
        exact Prod.ext h.1 h.2)
    (by rw [edeg_econj, edeg_emap]; exact hγp.hconj) hγv.hconj hψbp hψbv.1
    (fun i ↦ hψbv.2 _ (by
      simp only [econj, emap, E0L, List.map_ofFn, List.mem_ofFn]
      exact ⟨i, rfl⟩))
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hψb0; rw [hc]; simp [hsmul]
  have hΓnd : ((emap ρ Γ).map Prod.fst).Nodup := by
    have := hΓk; simpa [econj, Function.comp_def] using this
  obtain ⟨c₁, hc₁, hγn⟩ := hnorm_eq_C_mul_wpoly hfk hΓnd hγ0 (by rw [edeg_emap]; exact hγp) hγv
  -- S4–S7: the residual zeros `Qᵢ ≡ Pᵢ`
  have hres := residual_zeros hϖ h2 f hf.le x y hyu hyf hx Γ hon hΓx hΓE ψ hψp hψv γb c c₁ hc0
    hc₁ hγn hc
  choose z Y hzx hYy hY2 hzero using hres
  -- S8: the `ℓ`-th power argument over `K`
  set ψK' : K[X] × K[X] := (ψ.1.map ι, ψ.2.map ι)
  have hψK'0 : ψK' ≠ (0, 0) := by
    intro h; apply hψb0
    have h1 : ψ.1 = 0 := Polynomial.map_injective ι hι (by simpa using congrArg Prod.fst h)
    have h2' : ψ.2 = 0 := Polynomial.map_injective ι hι (by simpa using congrArg Prod.snd h)
    simp [ψb, h1, h2']
  have hψK'p : PoleLE g ψK' (2 * g + d) :=
    ⟨by simp only [ψK', natDegree_map_frac]; exact hψp.1,
     hψp.2.imp (fun h ↦ by simp [ψK', h]) fun h ↦ by simp only [ψK', natDegree_map_frac]; exact h⟩
  have hψK'v : Vanishes (f.map ι) ψK' (econj (emap ι ΓE)) := by
    rw [← emap_econj]; exact hψv.map
  set Γℓ := escale ℓ (emap ι Γ)
  have honK : OnCurve (f.map ι) (emap ι Γ) := OnCurve.map hon
  have honℓ : OnCurve (f.map ι) Γℓ := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact honK q' hq'
  set Φ := hmul (f.map ι) (hpow (f.map ι) ψK' ℓ) Ξ
  have hΦ1 : Vanishes (f.map ι) Φ Γℓ := by
    intro q hq
    have := VanishAt.hmul (ψ := hpow (f.map ι) ψK' ℓ) (φ := Ξ) (k := 0) (honℓ q hq).1
      (honℓ q hq).2 (VanishAt.zero (honℓ q hq).1 (honℓ q hq).2) (hΞv q hq)
    simpa using this
  have hΦ2 : Vanishes (f.map ι) Φ (econj Γℓ) := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    obtain ⟨q'', hq'', rfl⟩ := List.mem_map.mp hq'
    obtain ⟨q3, hq3, rfl⟩ := List.mem_map.mp hq''
    have hon3 := (honK.econj) _ (List.mem_map_of_mem (List.mem_map_of_mem hq3))
    have hv3 : VanishAt (f.map ι) ψK'.1 ψK'.2 (ι q3.1) (-ι q3.2.1) q3.2.2 :=
      hψK'v _ (by
        rw [emap, econj, List.map_map, List.mem_map]
        exact ⟨q3, List.mem_append_left _ hq3, rfl⟩)
    have := VanishAt.hmul (ψ := hpow (f.map ι) ψK' ℓ) (φ := Ξ) (k' := 0) hon3.1 hon3.2
      (VanishAt.hpow hon3.1 hon3.2 hv3 ℓ) (VanishAt.zero hon3.1 hon3.2)
    simpa using this
  have hΓℓnd : (Γℓ.map Prod.fst).Nodup := by
    have := nodup_map_of_pairwise_unit ι Γ hΓx
    simpa [Γℓ, escale, emap, Function.comp_def] using this
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ := wpoly_dvd_of_vanish_both hΓℓnd honℓ hΦ1 hΦ2
  set Ψ : K[X] × K[X] := (A, B)
  have hΦΨ : Φ = hsmul (wpoly Γℓ) Ψ := Prod.ext hA hB
  have hwℓ : wpoly Γℓ ≠ 0 := (wpoly_monic _).ne_zero
  have hodd : Odd (f.map ι).natDegree := ⟨g, by omega⟩
  have hΦ0 : Φ ≠ (0, 0) := hmul_ne_zero hodd (hpow_ne_zero hodd hψK'0 ℓ) hΞ0
  have hΨ0 : Ψ ≠ (0, 0) := by
    intro h; apply hΦ0; rw [hΦΨ, h]; simp [hsmul]
  have hΦp : PoleLE g Φ (ℓ * (2 * g + d) + ℓ * d) :=
    PoleLE.hmul hfK' (PoleLE.hpow hfK' hψK'p ℓ) hΞp
  have hΨp : PoleLE g Ψ (2 * g * ℓ) := by
    have := PoleLE.of_hsmul hwℓ (hΦΨ ▸ hΦp)
    rw [natDegree_wpoly, show edeg Γℓ = ℓ * d by simp [Γℓ, edeg_escale, edeg_emap, d]] at this
    have e : ℓ * (2 * g + d) + ℓ * d = 2 * g * ℓ + 2 * (ℓ * d) := by ring
    rw [e, Nat.add_sub_cancel] at this
    exact this
  -- the zeros of `Ψ` at `Qᵢ` and `σPᵢ`
  have hwu : ∀ z₀ : O, ∀ i, z₀ - x i ∈ IsLocalRing.maximalIdeal O →
      IsUnit ((wpoly Γℓ).eval (ι z₀)) := by
    intro z₀ i hz
    refine (eval_wpoly_ne_zero fun q hq he ↦ ?_).isUnit
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    obtain ⟨q'', hq'', rfl⟩ := List.mem_map.mp hq'
    have hu := hΓE q'' hq'' i
    rw [hι he] at hu
    exact (IsLocalRing.mem_maximalIdeal _).mp hz hu
  have hmemE : ∀ i, (ι (x i), -ι (y i), 1) ∈ econj (emap ι ΓE) := fun i ↦ by
    simp only [econj, emap, ΓE, List.map_append, List.mem_append, List.map_map]
    right
    exact List.mem_map.mpr ⟨(x i, y i, 1), List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩
  have hΨQ : ∀ i, VanishAt (f.map ι) Ψ.1 Ψ.2 (ι (z i)) (ι (Y i)) ℓ := by
    intro i
    have hY2' : IsUnit (2 * Y i) := by
      have : 2 * Y i = 2 * y i + 2 * (Y i - y i) := by ring
      rw [this]
      exact isUnit_add_mem (h2.mul (hyu i)) (Ideal.mul_mem_left _ _ (hYy i))
    have hYK : IsUnit (2 * ι (Y i)) := by
      have := hY2'.map ι; rwa [map_mul, map_ofNat] at this
    have hYK2 : ι (Y i) ^ 2 = (f.map ι).eval (ι (z i)) := by
      rw [eval_map_apply, ← hY2 i, map_pow]
    have hv1 : VanishAt (f.map ι) ψK'.1 ψK'.2 (ι (z i)) (ι (Y i)) 1 :=
      (vanishAt_one_of_eval (hY2 i) (hzero i)).map ι
    have hv := VanishAt.hmul (ψ := hpow (f.map ι) ψK' ℓ) (φ := Ξ) (k' := 0) hYK hYK2
      (VanishAt.hpow hYK hYK2 hv1 ℓ) (VanishAt.zero hYK hYK2)
    rw [mul_one, add_zero] at hv
    refine VanishAt.of_hsmul_unit (w := wpoly Γℓ) (hwu (z i) i (hzx i)) ?_
    rw [← hΦΨ]; exact hv
  have hΨS : ∀ i, VanishAt (f.map ι) Ψ.1 Ψ.2 (ι (x i)) (-ι (y i)) ℓ := by
    intro i
    have hyK : IsUnit (2 * -ι (y i)) := by
      have := ((h2.mul (hyu i)).map ι).neg; rwa [map_mul, map_ofNat, ← mul_neg] at this
    have hyK2 : (-ι (y i)) ^ 2 = (f.map ι).eval (ι (x i)) := by
      rw [neg_sq, eval_map_apply, ← hyf i, map_pow]
    have hv1 : VanishAt (f.map ι) ψK'.1 ψK'.2 (ι (x i)) (-ι (y i)) 1 := hψK'v _ (hmemE i)
    have hv := VanishAt.hmul (ψ := hpow (f.map ι) ψK' ℓ) (φ := Ξ) (k' := 0) hyK hyK2
      (VanishAt.hpow hyK hyK2 hv1 ℓ) (VanishAt.zero hyK hyK2)
    rw [mul_one, add_zero] at hv
    refine VanishAt.of_hsmul_unit (w := wpoly Γℓ)
      (hwu (x i) i (by rw [sub_self]; exact Ideal.zero_mem _)) ?_
    rw [← hΦΨ]; exact hv
  -- S9: descend `Ψ` to `O` and apply `kernel_no_torsion`
  set Δ : EDiv O := List.ofFn (fun i ↦ (z i, Y i, ℓ)) ++ List.ofFn (fun i ↦ (x i, -y i, ℓ))
  have honΔ : OnCurve f Δ := by
    rw [OnCurve.append]
    constructor
    · intro q hq
      simp only [List.mem_ofFn] at hq
      obtain ⟨i, rfl⟩ := hq
      refine ⟨?_, hY2 i⟩
      have : 2 * Y i = 2 * y i + 2 * (Y i - y i) := by ring
      rw [this]
      exact isUnit_add_mem (h2.mul (hyu i)) (Ideal.mul_mem_left _ _ (hYy i))
    · intro q hq
      simp only [List.mem_ofFn] at hq
      obtain ⟨i, rfl⟩ := hq
      exact ⟨by rw [mul_neg]; exact (h2.mul (hyu i)).neg, by rw [neg_sq]; exact hyf i⟩
  obtain ⟨Ψ₁, hprim₁, hΨ₁p, hΨ₁v, -⟩ := descend hϖ honΔ (g := g) hΨ0 hΨp (by
    intro q hq
    simp only [emap, Δ, List.map_append, List.map_ofFn, List.mem_append, List.mem_ofFn] at hq
    rcases hq with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact hΨQ i
    · simpa using hΨS i)
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  have ht := kernel_no_torsion hϖ h2 f (m := m) (by exact_mod_cast hℓ) x y (fun i ↦ z i - x i) Y
    hyu hx (fun i ↦ (mem_max_iff_dvd hϖ _).mp (hzx i))
    (fun i ↦ (mem_max_iff_dvd hϖ _).mp (hYy i)) Ψ₁.1 Ψ₁.2 hprim₁
    (by have := hΨ₁p.1; nlinarith)
    (by
      rcases hΨ₁p.2 with h | h
      · rw [h, degree_zero]; exact WithBot.bot_lt_coe _
      · by_cases h0 : Ψ₁.2 = 0
        · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
        rw [degree_eq_natDegree h0]
        exact_mod_cast (show Ψ₁.2.natDegree < g * m by nlinarith))
    (fun i ↦ by
      have := hΨ₁v (z i, Y i, m + 1) (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
      simpa using this)
    (fun i ↦ hΨ₁v (x i, -y i, m + 1) (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩)))
  have hzx' : ∀ i, z i = x i := fun i ↦ sub_eq_zero.mp (ht i)
  -- S10: `ψ` vanishes on `E₀ + σE₀`, so `ū ∣ ψ`
  have hψP : ∀ i, VanishAt (f.map ι) ψK'.1 ψK'.2 (ι (x i)) (ι (y i)) 1 := by
    intro i
    have hYe : Y i = y i := by
      have hsum : IsUnit (Y i + y i) := by
        have : Y i + y i = 2 * y i + (Y i - y i) := by ring
        rw [this]; exact isUnit_add_mem (h2.mul (hyu i)) (hYy i)
      have : (Y i - y i) * (Y i + y i) = 0 := by
        rw [show (Y i - y i) * (Y i + y i) = Y i ^ 2 - y i ^ 2 by ring, hY2 i, hzx' i, hyf i,
          sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hsum.ne_zero)
    have := (vanishAt_one_of_eval (hY2 i) (hzero i)).map ι
    rwa [hzx' i, hYe] at this
  have hψσ : ∀ i, VanishAt (f.map ι) ψK'.1 ψK'.2 (ι (x i)) (-ι (y i)) 1 := fun i ↦
    hψK'v _ (hmemE i)
  have hxK : Function.Injective fun j ↦ ι (x j) := fun a b hab ↦ by
    by_contra hne
    have := (hx a b hne).map ι
    rw [map_sub, show ι (x a) = ι (x b) from hab, sub_self] at this
    exact not_isUnit_zero this
  have hdd : ∀ i, (X - C (ι (x i))) ^ 1 ∣ ψK'.1 ∧ (X - C (ι (x i))) ^ 1 ∣ ψK'.2 := fun i ↦ by
    have h2K : IsUnit (2 * ι (y i)) := by
      have := (h2.mul (hyu i)).map ι; rwa [map_mul, map_ofNat] at this
    exact dvd_of_vanish_both h2K (hψP i) (hψσ i)
  obtain ⟨a'', ha''⟩ := prod_pow_dvd hxK 1 fun i ↦ (hdd i).1
  obtain ⟨b'', hb''⟩ := prod_pow_dvd hxK 1 fun i ↦ (hdd i).2
  set uK : K[X] := ∏ i, (X - C (ι (x i)))
  have huK0 : uK ≠ 0 := (monic_prod_of_monic _ _ fun j _ ↦ monic_X_sub_C _).ne_zero
  have huKd : uK.natDegree = g := by
    have := natDegree_prod_pow (fun j ↦ ι (x j)) 1; simpa [uK] using this
  rw [pow_one] at ha'' hb''
  have hψe : ψK' = hsmul uK (a'', b'') := Prod.ext ha'' hb''
  refine ⟨hconj (a'', b''), ?_, ?_, ?_⟩
  · intro h
    simp only [hconj, Prod.mk.injEq, neg_eq_zero] at h
    apply hψK'0; rw [hψe, h.1, h.2]; simp [hsmul]
  · have := PoleLE.of_hsmul huK0 (hψe ▸ hψK'p)
    rw [huKd, show 2 * g + d - 2 * g = d by omega] at this
    exact this.hconj
  · have hv : Vanishes (f.map ι) (a'', b'') (econj (emap ι Γ)) := by
      intro q hq
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
      obtain ⟨q'', hq'', rfl⟩ := List.mem_map.mp hq'
      have h1 := hψK'v (ι q''.1, -ι q''.2.1, q''.2.2) (by
        simp only [econj, emap, ΓE, List.map_append, List.mem_append, List.map_map]
        left; exact List.mem_map.mpr ⟨q'', hq'', rfl⟩)
      rw [hψe] at h1
      refine VanishAt.of_hsmul_unit ?_ h1
      refine IsUnit.mk0 _ ?_
      simp only [uK, eval_prod, eval_sub, eval_X, eval_C]
      refine Finset.prod_ne_zero_iff.mpr fun j _ ↦ sub_ne_zero.mpr fun he ↦ ?_
      have := (hΓE q'' hq'' j).map ι
      rw [map_sub, he, sub_self] at this
      exact not_isUnit_zero this
    have := hv.hconj
    rwa [econj_econj] at this

end Jac
