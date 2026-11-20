import RischTragerBronstein.Mixed.NKExactCodes
import RischTragerBronstein.Curves.Branch
import RischTragerBronstein.Mixed.SysExpT

/-!
# The exact part over an algebraic extension of a primitive level: correctness

`exactC_true`: `some true` gives `v = ∑ Yᵢ θⁱ` (`Yᵢ ∈ Fₘ₊₁`) with `v′ = f`; `exactC_false`:
`some false` proves that no such `v` exists (given that `1, θ, …, θ^{N−1}` are linearly
independent over `Fₘ₊₁`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

section Generic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Differential K] [Differential L]
  (hcomm : ∀ z : K, (algebraMap K L z)′ = algebraMap K L z′) (θ : L)

include hcomm in
/-- **Differentiating `p(θ)`** with a coefficient derivation. -/
lemma deriv_aeval_coeff (p : K[X]) :
    (aeval θ p)′ = aeval θ (mapCoeffs p) + aeval θ (derivative p) * θ′ := by
  have h : ((p.map (algebraMap K L)).eval θ)′ = (∑ i ∈ Finset.range (p.natDegree + 1),
      ((p.map (algebraMap K L)).coeff i)′ * θ ^ i) +
      (derivative (p.map (algebraMap K L))).eval θ * θ′ :=
    derivation_eval (Differential.deriv (R := L)).toLinearMap.toAddMonoidHom
      (isLeibniz_derivation _) (p.map (algebraMap K L)) θ (p.natDegree + 1)
      (natDegree_map_le.trans_lt (Nat.lt_succ_self _))
  rw [aeval_def, eval₂_eq_eval_map, h, aeval_def, aeval_def, eval₂_eq_eval_map, eval₂_eq_eval_map,
    derivative_map]
  congr 1
  rw [eval_eq_sum_range' (n := p.natDegree + 1)]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [coeff_map, coeff_map, coeff_mapCoeffs, hcomm]
  · refine natDegree_map_le.trans_lt (Nat.lt_succ_of_le ?_)
    exact natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ by
      rw [coeff_mapCoeffs, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hi), map_zero]

end Generic

/-- The operations of level `m` with reduced codes. -/
abbrev MOr (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (m : ℕ) : COps (LC m) :=
  (MO Fc ks m).normalizeBy (redL Fc ks m)

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {Cc L : Type u} [Field Cc] [Field L]
  [Algebra Cc L] [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc]
  [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- The model of level `m` with reduced codes. -/
noncomputable def MPr (m : ℕ) (h : T.Tr m) :
    CField (LC m) (T.F m) ((MO Fc ks m).normalizeBy (redL Fc ks m)) :=
  (T.MP m h).normalizeBy (redL Fc ks m) (fun q ↦ Subtype.ext (by
    rw [T.sem_MP, T.sem_MP, T.ev_redL m h]))

lemma MPr_sem (m : ℕ) (h : T.Tr m) (q : LC m) : (T.MPr m h).sem q = (T.MP m h).sem q := rfl

variable (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L)

/-- A polynomial in `θ` with coefficients of level `m + 1`. -/
noncomputable def evθ (p : GPoly (LC (m + 1))) : L := aeval θ (GPoly.toPoly (T.MPr (m + 1) h1) p)

lemma hcommF : ∀ z : T.F (m + 1), (algebraMap (T.F (m + 1)) L z)′ = algebraMap (T.F (m + 1)) L z′ :=
  fun _ ↦ rfl

/-- `(p(θ))′ = p^δ(θ) + p_Y(θ) θ′`. -/
lemma deriv_evθ (p : GPoly (LC (m + 1))) :
    (T.evθ m h1 θ p)′ = T.evθ m h1 θ (GPoly.mapD (MOr Fc ks (m + 1)) p) +
      T.evθ m h1 θ (GPoly.derivX (MOr Fc ks (m + 1)) p) * θ′ := by
  rw [evθ, deriv_aeval_coeff (T.hcommF m) θ, evθ, evθ, GPoly.toPoly_mapD, GPoly.toPoly_derivX]

variable (P : GPoly (LC (m + 1))) (hP : T.evθ m h1 θ P = 0)

include hP in
lemma evθ_remP (p : GPoly (LC (m + 1))) :
    T.evθ m h1 θ (remP (MOr Fc ks (m + 1)) P p) = T.evθ m h1 θ p := by
  have hs := GPoly.divMod_spec (T.MPr (m + 1) h1) p P
  unfold evθ at hP ⊢
  rw [remP, hs, map_add, map_mul, hP, mul_zero, zero_add]

include hP in
/-- **`θ′` from the Bezout identity.** -/
lemma deriv_θ (dθ : GPoly (LC (m + 1)))
    (hd : dThetaC (MOr Fc ks (m + 1)) P = some dθ) :
    θ′ = T.evθ m h1 θ dθ := by
  set O1 := (MO Fc ks (m + 1)).normalizeBy (redL Fc ks (m + 1)) with hO1
  set M1 := T.MPr (m + 1) h1
  unfold dThetaC at hd
  simp only at hd
  split_ifs at hd with hg
  obtain rfl := Option.some.inj hd
  set e := GPoly.egcd O1 (GPoly.derivX O1 P) P with he
  obtain ⟨a, ha⟩ : ∃ a, GPoly.trim O1 e.1 = [a] := by
    match hx : GPoly.trim O1 e.1, hg with
    | [a], _ => exact ⟨a, rfl⟩
  have hga : (GPoly.trim O1 e.1).getD 0 O1.zero = a := by rw [ha]; rfl
  rw [hga]
  have hne : GPoly.trim O1 e.1 ≠ [] := by rw [ha]; simp
  have hlc0 := (GPoly.natDegree_toPoly_of_trim_ne_nil M1 hne).2.2
  rw [ha] at hlc0
  change M1.sem a ≠ 0 at hlc0
  have hgC : GPoly.toPoly M1 e.1 = C (M1.sem a) := by
    rw [← GPoly.toPoly_trim, ha]; simp
  have hbez := GPoly.egcd_spec M1 (GPoly.derivX O1 P) P
  rw [← he, hgC] at hbez
  have hbezθ := congrArg (aeval θ) hbez
  simp only [map_add, map_mul, aeval_C] at hbezθ
  have hPθ : aeval θ (GPoly.toPoly M1 P) = 0 := hP
  rw [hPθ, mul_zero, add_zero] at hbezθ
  have hdP := T.deriv_evθ m h1 θ P
  rw [hP, Derivation.map_zero] at hdP
  rw [T.evθ_remP m h1 θ P hP]
  unfold evθ at hdP ⊢
  rw [GPoly.toPoly_smul, GPoly.toPoly_mul, map_mul, map_mul, aeval_C, M1.sem_neg, M1.sem_inv]
  have hg0L : algebraMap (T.F (m + 1)) L (M1.sem a) ≠ 0 :=
    (algebraMap (T.F (m + 1)) L).injective.ne (by simpa using hlc0)
  rw [map_neg, map_inv₀]
  field_simp
  linear_combination (-(aeval θ (GPoly.toPoly M1 e.2.1))) * hdP - θ′ * hbezθ

include hP in
/-- `(θⁱ)′ = (dPowC i)(θ)`. -/
lemma deriv_θ_pow (dθ : GPoly (LC (m + 1)))
    (hd : dThetaC (MOr Fc ks (m + 1)) P = some dθ) (i : ℕ) :
    (θ ^ i)′ = T.evθ m h1 θ (dPowC (MOr Fc ks (m + 1)) P dθ i) := by
  unfold dPowC
  split_ifs with hi
  · subst hi; simp [evθ]
  · rw [T.evθ_remP m h1 θ P hP]
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [Derivation.leibniz_pow, T.deriv_θ m h1 θ P hP dθ hd]
    simp only [evθ, GPoly.toPoly_mul, GPoly.toPoly_monomial, map_mul, map_pow, aeval_C, aeval_X,
      (T.MPr (m + 1) h1).sem_natCast, nsmul_eq_mul, smul_eq_mul, Nat.add_sub_cancel]
    rw [map_natCast]
    ring

/-- The coefficients of `(θⁱ)′`. -/
noncomputable def Mθ (dθ : GPoly (LC (m + 1))) (i j : ℕ) : T.F (m + 1) :=
  (T.MPr (m + 1) h1).sem ((dPowC (MOr Fc ks (m + 1)) P dθ i).getD j (MOr Fc ks (m + 1)).zero)

lemma natDegree_dPowC (hPm : (GPoly.toPoly (T.MPr (m + 1) h1) P).Monic) (dθ : GPoly (LC (m + 1)))
    (i : ℕ) : (GPoly.toPoly (T.MPr (m + 1) h1) (dPowC (MOr Fc ks (m + 1)) P dθ i)).natDegree <
      (GPoly.toPoly (T.MPr (m + 1) h1) P).natDegree ∨
      GPoly.toPoly (T.MPr (m + 1) h1) (dPowC (MOr Fc ks (m + 1)) P dθ i) = 0 := by
  unfold dPowC
  split_ifs
  · right; simp
  · by_cases h0 : GPoly.toPoly (T.MPr (m + 1) h1) (remP (MOr Fc ks (m + 1)) P
        (GPoly.mul (MOr Fc ks (m + 1)) (GPoly.monomial (MOr Fc ks (m + 1)) (i - 1)
          ((MOr Fc ks (m + 1)).natCast i)) dθ)) = 0
    · right; exact h0
    · left
      have := GPoly.divMod_degree_lt (T.MPr (m + 1) h1) (GPoly.mul (MOr Fc ks (m + 1))
        (GPoly.monomial (MOr Fc ks (m + 1)) (i - 1) ((MOr Fc ks (m + 1)).natCast i)) dθ) P
        hPm.ne_zero
      exact natDegree_lt_natDegree h0 this

include hP in
/-- `(θⁱ)′ = ∑_{j < N} Mᵢⱼ θʲ`. -/
lemma deriv_θ_pow_sum (hPm : (GPoly.toPoly (T.MPr (m + 1) h1) P).Monic)
    (dθ : GPoly (LC (m + 1))) (hd : dThetaC (MOr Fc ks (m + 1)) P = some dθ) (i : ℕ) :
    (θ ^ i)′ = ∑ j ∈ Finset.range (GPoly.toPoly (T.MPr (m + 1) h1) P).natDegree,
      (T.Mθ m h1 P dθ i j : L) * θ ^ j := by
  rw [T.deriv_θ_pow m h1 θ P hP dθ hd i, evθ]
  rcases T.natDegree_dPowC m h1 P hPm dθ i with hlt | h0
  · rw [aeval_eq_sum_range' hlt]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [coeff_toPoly_sem, Mθ, Algebra.smul_def]
    rfl
  · rw [h0, map_zero]
    symm
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have : (GPoly.toPoly (T.MPr (m + 1) h1) (dPowC (MOr Fc ks (m + 1)) P dθ i)).coeff j = 0 := by
      rw [h0, coeff_zero]
    rw [coeff_toPoly_sem] at this
    rw [Mθ, this]; simp

include hP in
/-- **The derivative in coordinates**: `(∑ Yᵢ θⁱ)′ = ∑ⱼ (Yⱼ′ + ∑ᵢ Mᵢⱼ Yᵢ) θʲ`. -/
lemma deriv_coords (hPm : (GPoly.toPoly (T.MPr (m + 1) h1) P).Monic)
    (dθ : GPoly (LC (m + 1))) (hd : dThetaC (MOr Fc ks (m + 1)) P = some dθ) (Y : ℕ → T.F (m + 1)) :
    (∑ i ∈ Finset.range (GPoly.toPoly (T.MPr (m + 1) h1) P).natDegree, (Y i : L) * θ ^ i)′ =
      ∑ j ∈ Finset.range (GPoly.toPoly (T.MPr (m + 1) h1) P).natDegree,
        (((Y j)′ + ∑ i ∈ Finset.range (GPoly.toPoly (T.MPr (m + 1) h1) P).natDegree,
          T.Mθ m h1 P dθ i j * Y i : T.F (m + 1)) : L) * θ ^ j := by
  set N := (GPoly.toPoly (T.MPr (m + 1) h1) P).natDegree
  rw [map_sum]
  have e : ∀ i ∈ Finset.range N, ((Y i : L) * θ ^ i)′ = ((Y i)′ : T.F (m + 1)) * θ ^ i +
      ∑ j ∈ Finset.range N, ((T.Mθ m h1 P dθ i j * Y i : T.F (m + 1)) : L) * θ ^ j := fun i _ ↦ by
    rw [Derivation.leibniz, T.deriv_θ_pow_sum m h1 θ P hP hPm dθ hd i, smul_eq_mul, smul_eq_mul,
      Finset.mul_sum]
    have hY : ((Y i : L))′ = (((Y i)′ : T.F (m + 1)) : L) := rfl
    rw [hY]
    simp only [IntermediateField.coe_mul]
    rw [add_comm]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  push_cast
  rw [add_mul, Finset.sum_mul]

/-- Every element of `Fₘ₊₁` is `phi r / phi s`, `s ≠ 0`. -/
lemma exists_frac (htr : Transcendental (T.F m) (T.ts m)) (y : T.F (m + 1)) :
    ∃ r s : (T.F m)[X], s ≠ 0 ∧ y * T.phi m s = T.phi m r := by
  have hy : (y : L) ∈ IntermediateField.adjoin (T.F m) {T.ts m} := y.2
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff _ _).mp hy
  by_cases hs : s = 0
  · have : (y : L) = 0 := by rw [hrs, hs, map_zero, div_zero]
    refine ⟨0, 1, one_ne_zero, ?_⟩
    rw [map_zero, map_one, mul_one]
    exact Subtype.ext this
  · refine ⟨r, s, hs, Subtype.ext ?_⟩
    have hs' : aeval (T.ts m) s ≠ 0 := fun h0 ↦ hs (transcendental_iff_injective.mp htr
      (by rw [h0, map_zero]))
    push_cast
    rw [T.coe_phi, T.coe_phi, hrs, div_mul_cancel₀ _ hs']

/-- **A common denominator.** -/
lemma exists_common_den (htr : Transcendental (T.F m) (T.ts m)) {n : ℕ} (Y : Fin n → T.F (m + 1)) :
    ∃ (Z : Fin n → (T.F m)[X]) (d : (T.F m)[X]), d ≠ 0 ∧ ∀ i, Y i * T.phi m d = T.phi m (Z i) := by
  classical
  choose r s hs hrs using fun i ↦ T.exists_frac m htr (Y i)
  refine ⟨fun i ↦ r i * ∏ k ∈ Finset.univ.erase i, s k, ∏ k, s k,
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ hs k, fun i ↦ ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i), map_mul, map_mul, ← mul_assoc,
    hrs i]

/-- A successful `primSysC` has monic `q`, `h`. -/
lemma primSysC_monic {m : ℕ} {η : LC m} {lim : List (LC m) → List (List ℚ × LC m)} {n : ℕ}
    {A0 : Fin n → Fin n → GPoly (LC m)} {q hq : GPoly (LC m)} {G0 : List (Fin n → GPoly (LC m))}
    {r : GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))}
    (hres : primSysC Fc ks m η lim n A0 q hq G0 = some r) :
    isMonicC (MO Fc ks m) q = true ∧ isMonicC (MO Fc ks m) hq = true := by
  unfold primSysC at hres
  simp only at hres
  split_ifs at hres with hmon
  have : (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hq) = true := by
    revert hmon; cases (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hq) <;> simp
  exact Bool.and_eq_true_iff.mp this

/-- A successful `primSysC` returns the `W`-system denominator. -/
lemma primSysC_den {m : ℕ} {η : LC m} {lim : List (LC m) → List (List ℚ × LC m)} {n : ℕ}
    {A0 : Fin n → Fin n → GPoly (LC m)} {q hq : GPoly (LC m)} {G0 : List (Fin n → GPoly (LC m))}
    {r : GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))}
    (hres : primSysC Fc ks m η lim n A0 q hq G0 = some r) :
    ∃ B, r.1 = (wSys Fc ks m η n A0 q hq G0 B).Den := by
  unfold primSysC at hres
  simp only at hres
  split_ifs at hres
  split at hres
  · exact absurd hres (by simp)
  rename_i B _
  split_ifs at hres
  split at hres
  · exact absurd hres (by simp)
  rw [← Option.some.inj hres]
  exact ⟨B, rfl⟩

/-- A successful `expSysC` has monic `q`, `h`. -/
lemma expSysC_monic {m : ℕ} {a : LC m} {rdeD : LC m → List (LC m) → List (List ℚ × LC m)} {n : ℕ}
    {A0 : Fin n → Fin n → GPoly (LC m)} {q hq : GPoly (LC m)} {G0 : List (Fin n → GPoly (LC m))}
    {r : GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))}
    (hres : expSysC Fc ks m a rdeD n A0 q hq G0 = some r) :
    isMonicC (MO Fc ks m) q = true ∧ isMonicC (MO Fc ks m) hq = true := by
  unfold expSysC at hres
  simp only at hres
  split_ifs at hres with hmon
  have : (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hq) = true := by
    revert hmon; cases (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hq) <;> simp
  exact Bool.and_eq_true_iff.mp this

/-- A successful `expSysC` returns the `W`-system denominator. -/
lemma expSysC_den {m : ℕ} {a : LC m} {rdeD : LC m → List (LC m) → List (List ℚ × LC m)} {n : ℕ}
    {A0 : Fin n → Fin n → GPoly (LC m)} {q hq : GPoly (LC m)} {G0 : List (Fin n → GPoly (LC m))}
    {r : GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))}
    (hres : expSysC Fc ks m a rdeD n A0 q hq G0 = some r) :
    ∃ B, r.1 = (wSysE Fc ks m ((MO Fc ks m).deriv a) n A0 q hq G0 B).Den := by
  unfold expSysC at hres
  simp only at hres
  split_ifs at hres
  split at hres
  · exact absurd hres (by simp)
  rename_i B _
  split_ifs at hres
  rw [← Option.some.inj hres]
  exact ⟨B, rfl⟩

/-- A successful `expSysT` has monic `q`, `h`. -/
lemma expSysT_monic {m : ℕ} {a : LC m} {rdeD : LC m → List (LC m) → List (List ℚ × LC m)} {n : ℕ}
    {A0 : Fin n → Fin n → GPoly (LC m)} {q hq : GPoly (LC m)} {G0 : List (Fin n → GPoly (LC m))}
    {r : GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))}
    (hres : expSysT Fc ks m a rdeD n A0 q hq G0 = some r) :
    isMonicC (MO Fc ks m) q = true ∧ isMonicC (MO Fc ks m) hq = true := by
  unfold expSysT at hres
  simp only at hres
  split_ifs at hres with hmon
  have : (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hq) = true := by
    revert hmon; cases (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hq) <;> simp
  exact Bool.and_eq_true_iff.mp this

/-- A successful `expSysT` returns the `W`-system denominator. -/
lemma expSysT_den {m : ℕ} {a : LC m} {rdeD : LC m → List (LC m) → List (List ℚ × LC m)} {n : ℕ}
    {A0 : Fin n → Fin n → GPoly (LC m)} {q hq : GPoly (LC m)} {G0 : List (Fin n → GPoly (LC m))}
    {r : GPoly (LC m) × List (List ℚ × (Fin n → GPoly (LC m)))}
    (hres : expSysT Fc ks m a rdeD n A0 q hq G0 = some r) :
    ∃ B, r.1 = (wSysE Fc ks m ((MO Fc ks m).deriv a) n A0 q hq G0 B).Den := by
  unfold expSysT at hres
  simp only at hres
  split_ifs at hres
  split at hres
  · exact absurd hres (by simp)
  rename_i B _
  split_ifs at hres
  rw [← Option.some.inj hres]
  exact ⟨B, rfl⟩

/-- The value of a level-`m + 1` code over a common denominator `q = cof · den`. -/
lemma sem_cof (h1 : T.Tr (m + 1)) (htr : Transcendental (T.F m) (T.ts m)) (q : GPoly (LC m))
    (hq : GPoly.toPoly (T.MP m h1.of_succ) q ≠ 0) (c : LC (m + 1))
    (hc : (cofC (MO Fc ks m) q c.2).1 = true) :
    (T.MPr (m + 1) h1).sem c = T.phi m (GPoly.toPoly (T.MP m h1.of_succ)
      (GPoly.mul (MO Fc ks m) c.1 (cofC (MO Fc ks m) q c.2).2)) /
        T.phi m (GPoly.toPoly (T.MP m h1.of_succ) q) := by
  set M := T.MP m h1.of_succ
  have hs := GPoly.divMod_spec M q c.2
  have hr := (GPoly.isZero_iff M _).mp hc
  simp only [cofC] at hr ⊢
  rw [hr, add_zero] at hs
  rw [MPr_sem, T.sem_MP_succ, GPoly.toPoly_mul, hs, map_mul, map_mul]
  have hq' : T.phi m (GPoly.toPoly M q) ≠ 0 := fun h0 ↦ hq (T.phi_injective htr (by rw [h0, map_zero]))
  rw [hs, map_mul] at hq'
  have ha := left_ne_zero_of_mul hq'
  have hb := right_ne_zero_of_mul hq'
  field_simp
  exact mul_div_cancel_right₀ _ hb

section BridgeG

variable {n : ℕ}

/-- The cleared system as an identity of values (any `D` intertwined by `phi`). -/
lemma sysSol_phiG (w b : T.F m) (hD : ∀ P, T.phi m (DzL w b P) = (T.phi m P)′)
    (q hq : (T.F m)[X]) (A0 : Matrix (Fin n) (Fin n) (T.F m)[X]) (G : Fin n → (T.F m)[X])
    (Z : Fin n → (T.F m)[X]) (d : (T.F m)[X]) (j : Fin n) (hs : SysSol w b q hq A0 G Z d) :
    T.phi m q * T.phi m hq * (T.phi m d * (T.phi m (Z j))′ - (T.phi m d)′ * T.phi m (Z j)) +
      T.phi m hq * T.phi m d * ∑ i, T.phi m (A0 j i) * T.phi m (Z i) =
      T.phi m q * T.phi m d ^ 2 * T.phi m (G j) := by
  have := congrArg (T.phi m) (hs j)
  simp only [map_add, map_mul, map_sub, map_pow, map_sum, hD] at this
  exact this

lemma sysSol_of_phiG (htr : Transcendental (T.F m) (T.ts m)) (w b : T.F m)
    (hD : ∀ P, T.phi m (DzL w b P) = (T.phi m P)′)
    (q hq : (T.F m)[X]) (A0 : Matrix (Fin n) (Fin n) (T.F m)[X]) (G : Fin n → (T.F m)[X])
    (Z : Fin n → (T.F m)[X]) (d : (T.F m)[X])
    (h : ∀ j, T.phi m q * T.phi m hq * (T.phi m d * (T.phi m (Z j))′ - (T.phi m d)′ * T.phi m (Z j)) +
      T.phi m hq * T.phi m d * ∑ i, T.phi m (A0 j i) * T.phi m (Z i) =
      T.phi m q * T.phi m d ^ 2 * T.phi m (G j)) :
    SysSol w b q hq A0 G Z d := by
  intro j
  apply T.phi_injective htr
  simp only [map_add, map_mul, map_sub, map_pow, map_sum, hD]
  exact h j

/-- `phi` intertwines `DzL 0 a′` with the derivation at an exponential level. -/
lemma phi_DzL_exp (hm : m < T.n) {a : LC m} (hk : ks m = .exp a) (h0 : T.Tr m) (P : (T.F m)[X]) :
    T.phi m (DzL 0 ((T.MP m h0).sem ((MO Fc ks m).deriv a)) P) = (T.phi m P)′ := by
  rw [T.deriv_phi, T.wPoly_exp hm hk, (T.MP m h0).sem_deriv, T.sem_MP_F m h0]
  simp [DzL]

end BridgeG

section Bridge

variable {n : ℕ}

/-- `phi` intertwines `DzL η 0` with the derivation at a primitive level. -/
lemma phi_DzL (hm : m < T.n) {η : LC m} (hk : ks m = .prim η) (h0 : T.Tr m) (P : (T.F m)[X]) :
    T.phi m (DzL ((T.MP m h0).sem η) 0 P) = (T.phi m P)′ := by
  rw [T.deriv_phi, T.wPoly_prim hm hk, ← T.sem_MP_F m h0, T.DzL_zero_b m]

/-- **The cleared system as an identity of values.** -/
lemma sysSol_phi (hm : m < T.n) {η : LC m} (hk : ks m = .prim η) (h0 : T.Tr m)
    (q hq : (T.F m)[X]) (A0 : Matrix (Fin n) (Fin n) (T.F m)[X]) (G : Fin n → (T.F m)[X])
    (Z : Fin n → (T.F m)[X]) (d : (T.F m)[X]) (j : Fin n)
    (hs : SysSol ((T.MP m h0).sem η) 0 q hq A0 G Z d) :
    T.phi m q * T.phi m hq * (T.phi m d * (T.phi m (Z j))′ - (T.phi m d)′ * T.phi m (Z j)) +
      T.phi m hq * T.phi m d * ∑ i, T.phi m (A0 j i) * T.phi m (Z i) =
      T.phi m q * T.phi m d ^ 2 * T.phi m (G j) := by
  have := congrArg (T.phi m) (hs j)
  simp only [map_add, map_mul, map_sub, map_pow, map_sum, T.phi_DzL m hm hk h0] at this
  exact this

lemma sysSol_of_phi (hm : m < T.n) {η : LC m} (hk : ks m = .prim η) (h0 : T.Tr m)
    (htr : Transcendental (T.F m) (T.ts m))
    (q hq : (T.F m)[X]) (A0 : Matrix (Fin n) (Fin n) (T.F m)[X]) (G : Fin n → (T.F m)[X])
    (Z : Fin n → (T.F m)[X]) (d : (T.F m)[X])
    (h : ∀ j, T.phi m q * T.phi m hq * (T.phi m d * (T.phi m (Z j))′ - (T.phi m d)′ * T.phi m (Z j)) +
      T.phi m hq * T.phi m d * ∑ i, T.phi m (A0 j i) * T.phi m (Z i) =
      T.phi m q * T.phi m d ^ 2 * T.phi m (G j)) :
    SysSol ((T.MP m h0).sem η) 0 q hq A0 G Z d := by
  intro j
  apply T.phi_injective htr
  simp only [map_add, map_mul, map_sub, map_pow, map_sum, T.phi_DzL m hm hk h0]
  exact h j

end Bridge

/-- **Correctness of the exact-part test.** With `θ` a root of `P` (monic, `N = deg P`) whose powers
`1, …, θ^{N−1}` are linearly independent over `Fₘ₊₁`: `exactC` answers `true` exactly when
`f = ∑ fⱼ θʲ` has an antiderivative `∑ Yᵢ θⁱ` with `Yᵢ ∈ Fₘ₊₁`. -/
theorem exactC_correct (hm : m < T.n) (h1 : T.Tr (m + 1)) (htr : Transcendental (T.F m) (T.ts m))
    {η : LC m} (hk : ks m = .prim η) (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h1.of_succ) lim)
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range (P.length - 1), (a j : L) * θ ^ j = 0 →
      ∀ j < P.length - 1, a j = 0)
    (res : Bool) (hres : exactC Fc ks m η lim P f = some res) :
    res = true ↔ ∃ Y : ℕ → T.F (m + 1),
      (∑ i ∈ Finset.range (P.length - 1), (Y i : L) * θ ^ i)′ =
        ∑ j ∈ Finset.range (P.length - 1),
          ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j := by
  classical
  unfold exactC at hres
  simp only at hres
  split_ifs at hres with hPc
  split at hres
  · exact absurd hres (by simp)
  rename_i dθ hd
  split_ifs at hres with hcof
  split at hres
  · exact absurd hres (by simp)
  rename_i r hr
  obtain rfl := Option.some.inj hres
  set O1 := MOr Fc ks (m + 1) with hO1
  set O := MO Fc ks m with hO
  set M1 := T.MPr (m + 1) h1 with hM1
  set h0 := h1.of_succ with hh0
  set M := T.MP m h0 with hM
  -- `P` is monic of degree `(P.length - 1)`
  have hPc' : O1.isZero (O1.add (P.getD (P.length - 1) O1.zero) (O1.neg O1.one)) = true ∧ (P.length - 1) ≠ 0 := by
    revert hPc
    cases O1.isZero (O1.add (P.getD (P.length - 1) O1.zero) (O1.neg O1.one)) <;> simp
  have hlead : M1.sem (P.getD (P.length - 1) O1.zero) = 1 := by
    have := (M1.isZero_iff _).mp hPc'.1
    rw [M1.sem_add, M1.sem_neg, M1.sem_one, add_neg_eq_zero] at this
    exact this
  have hPlen : P.length = (P.length - 1) + 1 := by
    have : P ≠ [] := fun h0' ↦ by rw [h0'] at hPc'; exact hPc'.2 rfl
    have := List.length_pos_of_ne_nil this
    omega
  have hPdeg : (GPoly.toPoly M1 P).natDegree = (P.length - 1) := by
    apply le_antisymm
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [coeff_toPoly_sem, List.getD_eq_default _ _ (by
        have : (P.length - 1) < k := by exact_mod_cast hk
        omega), M1.sem_zero]
    · exact le_natDegree_of_ne_zero (by rw [coeff_toPoly_sem, hlead]; exact one_ne_zero)
  have hPm : (GPoly.toPoly M1 P).Monic := by
    rw [Monic, leadingCoeff, hPdeg, coeff_toPoly_sem, hlead]
  set Ml : List (List (LC (m + 1))) := (List.range (P.length - 1)).map fun i ↦
    (List.range (P.length - 1)).map fun j ↦ (dPowC O1 P dθ i).getD j O1.zero with hMl
  set ent : List (LC (m + 1)) := Ml.flatten ++ f with hent
  set q := lcmGL O (ent.map Prod.snd) with hq
  set num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2 with hnum
  have hqmon := isMonicC_spec M q (primSysC_monic hr).1
  set qs := GPoly.toPoly M q with hqs
  have hqs0 : qs ≠ 0 := hqmon.ne_zero
  have hcofs : ∀ c ∈ ent, (cofC O q c.2).1 = true := by
    have hall : (ent.map fun c ↦ cofC O q c.2).all Prod.fst = true := by
      revert hcof; cases (ent.map fun c ↦ cofC O q c.2).all Prod.fst <;> simp
    intro c hc
    exact List.all_eq_true.mp hall _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hval : ∀ c ∈ ent, (M1.sem c : T.F (m + 1)) = T.phi m (GPoly.toPoly M (num c)) / T.phi m qs :=
    fun c hc ↦ T.sem_cof m h1 htr q hqs0 c (hcofs c hc)
  have hMe : ∀ i < (P.length - 1), ∀ j < (P.length - 1), (Ml.getD i []).getD j O1.zero ∈ ent := fun i hi j hj ↦ by
    rw [hent]
    apply List.mem_append_left
    rw [List.mem_flatten]
    refine ⟨Ml.getD i [], ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by simpa [hMl] using hi)]; exact List.getElem_mem _
    · have hlen : j < (Ml.getD i []).length := by
        rw [hMl, NestTower.getD_range_map _ _ hi]; simpa using hj
      rw [List.getD_eq_getElem (Ml.getD i []) _ hlen]; exact List.getElem_mem _
  have hMθ : ∀ i < (P.length - 1), ∀ j < (P.length - 1), T.Mθ m h1 P dθ i j =
      T.phi m (GPoly.toPoly M (num ((Ml.getD i []).getD j O1.zero))) / T.phi m qs := by
    intro i hi j hj
    rw [← hval _ (hMe i hi j hj), Mθ, hMl, NestTower.getD_range_map _ _ hi,
      NestTower.getD_range_map _ _ hj]
  have hfv : ∀ j, (M1.sem (f.getD j O1.zero) : T.F (m + 1)) =
      T.phi m (GPoly.toPoly M (num (f.getD j O1.zero))) / T.phi m qs := by
    intro j
    by_cases hj : j < f.length
    · refine hval _ ?_
      rw [hent]
      apply List.mem_append_right
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
    · rw [List.getD_eq_default _ _ (by omega)]
      have hz : O1.zero.1 = [] := rfl
      rw [M1.sem_zero, hnum]
      simp only [hz, GPoly.mul, GPoly.toPoly_nil, map_zero, zero_div]
  set A0f : Fin (P.length - 1) → Fin (P.length - 1) → GPoly (LC m) := fun j i ↦ num ((Ml.getD i []).getD j O1.zero) with hA0f
  set Gf : Fin (P.length - 1) → GPoly (LC m) := fun j ↦ num (f.getD j O1.zero) with hGf
  -- the coordinate equations
  have hcoord : ∀ Y : ℕ → T.F (m + 1),
      ((∑ i ∈ Finset.range (P.length - 1), (Y i : L) * θ ^ i)′ = ∑ j ∈ Finset.range (P.length - 1),
        ((M1.sem (f.getD j O1.zero) : T.F (m + 1)) : L) * θ ^ j) ↔
      ∀ j < (P.length - 1), (Y j)′ + ∑ i ∈ Finset.range (P.length - 1), T.Mθ m h1 P dθ i j * Y i =
        M1.sem (f.getD j O1.zero) := by
    intro Y
    have hdc := T.deriv_coords m h1 θ P hP hPm dθ hd Y
    rw [hPdeg] at hdc
    rw [hdc]
    constructor
    · intro hE j hj
      have h0 := hind (fun j ↦ (Y j)′ + ∑ i ∈ Finset.range (P.length - 1), T.Mθ m h1 P dθ i j * Y i -
        M1.sem (f.getD j O1.zero)) (by
          push_cast
          simp only [sub_mul, Finset.sum_sub_distrib]
          rw [← hE]
          push_cast
          simp only [add_mul, Finset.sum_mul]
          ring) j hj
      exact sub_eq_zero.mp h0
    · intro hE
      exact Finset.sum_congr rfl fun j hj ↦ by rw [hE j (Finset.mem_range.mp hj)]
  constructor
  · intro hany
    obtain ⟨b, hb, he⟩ := List.any_eq_true.mp hany
    simp only [bne_iff_ne, ne_eq] at he
    set e0 : ℚ := b.1.getD 0 0 with he0
    have hs := T.primSysC_sound m h0 η (P.length - 1) A0f q q [Gf] lim r.1 r.2 (by simpa using hr) b hb
    obtain ⟨B, hB⟩ := primSysC_den hr
    have hDs : GPoly.toPoly M r.1 ≠ 0 := by
      rw [hB, T.wSys_Den m h0 η (P.length - 1) A0f q q [Gf] B]
      exact mul_ne_zero hqs0 (pow_ne_zero _ hqs0)
    have hphiD : T.phi m (GPoly.toPoly M r.1) ≠ 0 := fun h0' ↦ hDs (T.phi_injective htr
      (by rw [h0', map_zero]))
    have hphiq : T.phi m qs ≠ 0 := fun h0' ↦ hqs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hE : ((e0 : ℚ) : T.F (m + 1)) ≠ 0 := by exact_mod_cast he
    set Y : ℕ → T.F (m + 1) := fun i ↦ if hi : i < P.length - 1 then
      T.phi m (semV M b.2 ⟨i, hi⟩) / (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1))) else 0
      with hY
    refine ⟨Y, (hcoord Y).mpr fun j hj ↦ ?_⟩
    have hphi := T.sysSol_phi m hm hk h0 qs qs (semMat M A0f) _ (semV M b.2) (GPoly.toPoly M r.1)
      ⟨j, hj⟩ hs
    simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton, List.getD_cons_zero,
      map_mul, semMat, Matrix.of_apply] at hphi
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦ T.Mθ m h1 P dθ i j * Y i)]
    have hMθ' : ∀ i : Fin (P.length - 1),
        T.Mθ m h1 P dθ i j = T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ i)) / T.phi m qs :=
      fun i ↦ hMθ i i.2 j hj
    have hYi : ∀ i : Fin (P.length - 1), Y i = T.phi m (semV M b.2 i) /
        (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1))) := fun i ↦ by
      rw [hY]; simp only [dif_pos i.2]
    simp only [hMθ', hYi]
    have hYj : Y j = T.phi m (semV M b.2 ⟨j, hj⟩) /
        (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1))) := by
      rw [hY]; simp only [dif_pos hj]
    rw [hYj, hfv]
    have hG' : GPoly.toPoly M (Gf ⟨j, hj⟩) = GPoly.toPoly M (num (f.getD j O1.zero)) := rfl
    rw [hG'] at hphi
    rw [Derivation.leibniz_div, Derivation.leibniz, T.deriv_ratCast, smul_zero, zero_add,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    rw [T.phi_C_ratCast] at hphi
    have hsum : ∑ x : Fin (P.length - 1), T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ x)) / T.phi m qs *
        (T.phi m (semV M b.2 x) / (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1)))) =
        (∑ x, T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ x)) * T.phi m (semV M b.2 x)) /
          (T.phi m qs * (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1)))) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun x _ ↦ by field_simp
    rw [hsum, smul_eq_mul]
    have hG'' : GPoly.toPoly (T.MP m h0) (Gf ⟨j, hj⟩) = GPoly.toPoly M (num (f.getD j O1.zero)) := rfl
    rw [hG''] at hphi
    field_simp
    apply mul_left_cancel₀ hphiq
    linear_combination hphi
  · rintro ⟨Y, hY⟩
    have heq := (hcoord Y).mp hY
    obtain ⟨Z, d, hd0, hZ⟩ := T.exists_common_den m htr (fun i : Fin (P.length - 1) ↦ Y i)
    have hphid : T.phi m d ≠ 0 := fun h0' ↦ hd0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hphiq : T.phi m qs ≠ 0 := fun h0' ↦ hqs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hYi : ∀ i : Fin (P.length - 1), Y i = T.phi m (Z i) / T.phi m d := fun i ↦ by
      rw [← hZ i, mul_div_cancel_right₀ _ hphid]
    have hsol : SysSol (M.sem η) 0 qs qs (semMat M A0f)
        (fun j ↦ ∑ l ∈ Finset.range [Gf].length, C (algebraMap Cc (T.F m) (([1] : List Cc).getD l 0)) *
          GPoly.toPoly M (([Gf].getD l fun _ ↦ []) j)) Z d := by
      refine T.sysSol_of_phi m hm hk h0 htr qs qs (semMat M A0f) _ Z d fun j ↦ ?_
      have hj := heq j j.2
      simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton, List.getD_cons_zero,
        map_one, one_mul]
      rw [← Fin.sum_univ_eq_sum_range (fun i ↦ T.Mθ m h1 P dθ i j * Y i)] at hj
      have hMθ' : ∀ i : Fin (P.length - 1), T.Mθ m h1 P dθ i j = T.phi m (GPoly.toPoly M (A0f j i)) / T.phi m qs :=
        fun i ↦ hMθ i i.2 j j.2
      simp only [hMθ', hYi, hfv] at hj
      rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul] at hj
      simp only [semMat, Matrix.of_apply]
      have hsum : ∑ x, T.phi m (GPoly.toPoly M (A0f j x)) / T.phi m qs *
          (T.phi m (Z x) / T.phi m d) =
          (∑ x, T.phi m (GPoly.toPoly M (A0f j x)) * T.phi m (Z x)) / (T.phi m qs * T.phi m d) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun x _ ↦ by field_simp
      rw [hsum, smul_eq_mul] at hj
      have hG' : GPoly.toPoly M (Gf j) = GPoly.toPoly M (num (f.getD (↑j) O1.zero)) := rfl
      rw [hG']
      field_simp at hj
      linear_combination (T.phi m qs) * hj
    obtain ⟨β, hβc, -⟩ := T.primSysC_complete m h0 η (P.length - 1) A0f q q [Gf] hm htr hk lim hlim r.1 r.2
      (by simpa using hr) [1] (fun l hl ↦ by
        simp only [List.length_singleton] at hl
        exact List.getD_eq_default _ _ (by simpa using hl)) Z d hd0 hsol
    have h1' := hβc 0
    simp only [List.getD_cons_zero] at h1'
    by_contra hcon
    rw [Bool.not_eq_true, List.any_eq_false] at hcon
    have hz : ∀ k ∈ Finset.range r.2.length,
        β.getD k 0 * algebraMap ℚ Cc (((r.2.getD k ([], fun _ ↦ [])).1).getD 0 0) = 0 := by
      intro k hk
      have hmem : r.2.getD k ([], fun _ ↦ []) ∈ r.2 := by
        rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]; exact List.getElem_mem _
      have := hcon _ hmem
      simp only [bne_iff_ne, ne_eq, not_not] at this
      rw [this, map_zero, mul_zero]
    rw [Finset.sum_eq_zero hz] at h1'
    exact one_ne_zero h1'

/-- **Correctness of the exact-part test at an exponential level** `t = exp a`. With `θ` a root of `P` (monic, `N = deg P`) whose powers
`1, …, θ^{N−1}` are linearly independent over `Fₘ₊₁`: `exactC` answers `true` exactly when
`f = ∑ fⱼ θʲ` has an antiderivative `∑ Yᵢ θⁱ` with `Yᵢ ∈ Fₘ₊₁`. -/
theorem exactCE_correct (hm : m < T.n) (h1 : T.Tr (m + 1)) (htr : Transcendental (T.F m) (T.ts m))
    {a : LC m} (hk : ks m = .exp a) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hrdeD : ∀ c : LC m, RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
      ((T.MP m h1.of_succ).sem c)′ (rdeD c))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range (P.length - 1), (a j : L) * θ ^ j = 0 →
      ∀ j < P.length - 1, a j = 0)
    (res : Bool) (hres : exactCE Fc ks m a rdeD P f = some res) :
    res = true ↔ ∃ Y : ℕ → T.F (m + 1),
      (∑ i ∈ Finset.range (P.length - 1), (Y i : L) * θ ^ i)′ =
        ∑ j ∈ Finset.range (P.length - 1),
          ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j := by
  classical
  unfold exactCE at hres
  simp only at hres
  split_ifs at hres with hPc
  split at hres
  · exact absurd hres (by simp)
  rename_i dθ hd
  split_ifs at hres with hcof
  split at hres
  · exact absurd hres (by simp)
  rename_i r hr
  obtain rfl := Option.some.inj hres
  set O1 := MOr Fc ks (m + 1) with hO1
  set O := MO Fc ks m with hO
  set M1 := T.MPr (m + 1) h1 with hM1
  set h0 := h1.of_succ with hh0
  set M := T.MP m h0 with hM
  -- `P` is monic of degree `(P.length - 1)`
  have hPc' : O1.isZero (O1.add (P.getD (P.length - 1) O1.zero) (O1.neg O1.one)) = true ∧ (P.length - 1) ≠ 0 := by
    revert hPc
    cases O1.isZero (O1.add (P.getD (P.length - 1) O1.zero) (O1.neg O1.one)) <;> simp
  have hlead : M1.sem (P.getD (P.length - 1) O1.zero) = 1 := by
    have := (M1.isZero_iff _).mp hPc'.1
    rw [M1.sem_add, M1.sem_neg, M1.sem_one, add_neg_eq_zero] at this
    exact this
  have hPlen : P.length = (P.length - 1) + 1 := by
    have : P ≠ [] := fun h0' ↦ by rw [h0'] at hPc'; exact hPc'.2 rfl
    have := List.length_pos_of_ne_nil this
    omega
  have hPdeg : (GPoly.toPoly M1 P).natDegree = (P.length - 1) := by
    apply le_antisymm
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [coeff_toPoly_sem, List.getD_eq_default _ _ (by
        have : (P.length - 1) < k := by exact_mod_cast hk
        omega), M1.sem_zero]
    · exact le_natDegree_of_ne_zero (by rw [coeff_toPoly_sem, hlead]; exact one_ne_zero)
  have hPm : (GPoly.toPoly M1 P).Monic := by
    rw [Monic, leadingCoeff, hPdeg, coeff_toPoly_sem, hlead]
  set Ml : List (List (LC (m + 1))) := (List.range (P.length - 1)).map fun i ↦
    (List.range (P.length - 1)).map fun j ↦ (dPowC O1 P dθ i).getD j O1.zero with hMl
  set ent : List (LC (m + 1)) := Ml.flatten ++ f with hent
  set q := lcmGL O (ent.map Prod.snd) with hq
  set num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2 with hnum
  have hqmon := isMonicC_spec M q (expSysC_monic hr).1
  set qs := GPoly.toPoly M q with hqs
  have hqs0 : qs ≠ 0 := hqmon.ne_zero
  have hcofs : ∀ c ∈ ent, (cofC O q c.2).1 = true := by
    have hall : (ent.map fun c ↦ cofC O q c.2).all Prod.fst = true := by
      revert hcof; cases (ent.map fun c ↦ cofC O q c.2).all Prod.fst <;> simp
    intro c hc
    exact List.all_eq_true.mp hall _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hval : ∀ c ∈ ent, (M1.sem c : T.F (m + 1)) = T.phi m (GPoly.toPoly M (num c)) / T.phi m qs :=
    fun c hc ↦ T.sem_cof m h1 htr q hqs0 c (hcofs c hc)
  have hMe : ∀ i < (P.length - 1), ∀ j < (P.length - 1), (Ml.getD i []).getD j O1.zero ∈ ent := fun i hi j hj ↦ by
    rw [hent]
    apply List.mem_append_left
    rw [List.mem_flatten]
    refine ⟨Ml.getD i [], ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by simpa [hMl] using hi)]; exact List.getElem_mem _
    · have hlen : j < (Ml.getD i []).length := by
        rw [hMl, NestTower.getD_range_map _ _ hi]; simpa using hj
      rw [List.getD_eq_getElem (Ml.getD i []) _ hlen]; exact List.getElem_mem _
  have hMθ : ∀ i < (P.length - 1), ∀ j < (P.length - 1), T.Mθ m h1 P dθ i j =
      T.phi m (GPoly.toPoly M (num ((Ml.getD i []).getD j O1.zero))) / T.phi m qs := by
    intro i hi j hj
    rw [← hval _ (hMe i hi j hj), Mθ, hMl, NestTower.getD_range_map _ _ hi,
      NestTower.getD_range_map _ _ hj]
  have hfv : ∀ j, (M1.sem (f.getD j O1.zero) : T.F (m + 1)) =
      T.phi m (GPoly.toPoly M (num (f.getD j O1.zero))) / T.phi m qs := by
    intro j
    by_cases hj : j < f.length
    · refine hval _ ?_
      rw [hent]
      apply List.mem_append_right
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
    · rw [List.getD_eq_default _ _ (by omega)]
      have hz : O1.zero.1 = [] := rfl
      rw [M1.sem_zero, hnum]
      simp only [hz, GPoly.mul, GPoly.toPoly_nil, map_zero, zero_div]
  set A0f : Fin (P.length - 1) → Fin (P.length - 1) → GPoly (LC m) := fun j i ↦ num ((Ml.getD i []).getD j O1.zero) with hA0f
  set Gf : Fin (P.length - 1) → GPoly (LC m) := fun j ↦ num (f.getD j O1.zero) with hGf
  -- the coordinate equations
  have hcoord : ∀ Y : ℕ → T.F (m + 1),
      ((∑ i ∈ Finset.range (P.length - 1), (Y i : L) * θ ^ i)′ = ∑ j ∈ Finset.range (P.length - 1),
        ((M1.sem (f.getD j O1.zero) : T.F (m + 1)) : L) * θ ^ j) ↔
      ∀ j < (P.length - 1), (Y j)′ + ∑ i ∈ Finset.range (P.length - 1), T.Mθ m h1 P dθ i j * Y i =
        M1.sem (f.getD j O1.zero) := by
    intro Y
    have hdc := T.deriv_coords m h1 θ P hP hPm dθ hd Y
    rw [hPdeg] at hdc
    rw [hdc]
    constructor
    · intro hE j hj
      have h0 := hind (fun j ↦ (Y j)′ + ∑ i ∈ Finset.range (P.length - 1), T.Mθ m h1 P dθ i j * Y i -
        M1.sem (f.getD j O1.zero)) (by
          push_cast
          simp only [sub_mul, Finset.sum_sub_distrib]
          rw [← hE]
          push_cast
          simp only [add_mul, Finset.sum_mul]
          ring) j hj
      exact sub_eq_zero.mp h0
    · intro hE
      exact Finset.sum_congr rfl fun j hj ↦ by rw [hE j (Finset.mem_range.mp hj)]
  constructor
  · intro hany
    obtain ⟨b, hb, he⟩ := List.any_eq_true.mp hany
    simp only [bne_iff_ne, ne_eq] at he
    set e0 : ℚ := b.1.getD 0 0 with he0
    have hs := T.expSysC_sound m h0 (P.length - 1) A0f q q [Gf] a rdeD r.1 r.2 (by simpa using hr) b hb
    obtain ⟨B, hB⟩ := expSysC_den hr
    have hDs : GPoly.toPoly M r.1 ≠ 0 := by
      rw [hB, T.wSysE_Den m h0 ((MO Fc ks m).deriv a) (P.length - 1) A0f q q [Gf] B]
      exact mul_ne_zero hqs0 (pow_ne_zero _ hqs0)
    have hphiD : T.phi m (GPoly.toPoly M r.1) ≠ 0 := fun h0' ↦ hDs (T.phi_injective htr
      (by rw [h0', map_zero]))
    have hphiq : T.phi m qs ≠ 0 := fun h0' ↦ hqs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hE : ((e0 : ℚ) : T.F (m + 1)) ≠ 0 := by exact_mod_cast he
    set Y : ℕ → T.F (m + 1) := fun i ↦ if hi : i < P.length - 1 then
      T.phi m (semV M b.2 ⟨i, hi⟩) / (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1))) else 0
      with hY
    refine ⟨Y, (hcoord Y).mpr fun j hj ↦ ?_⟩
    have hphi := T.sysSol_phiG m 0 (M.sem ((MO Fc ks m).deriv a)) (T.phi_DzL_exp m hm hk h0) qs qs (semMat M A0f) _ (semV M b.2) (GPoly.toPoly M r.1)
      ⟨j, hj⟩ hs
    simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton, List.getD_cons_zero,
      map_mul, semMat, Matrix.of_apply] at hphi
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦ T.Mθ m h1 P dθ i j * Y i)]
    have hMθ' : ∀ i : Fin (P.length - 1),
        T.Mθ m h1 P dθ i j = T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ i)) / T.phi m qs :=
      fun i ↦ hMθ i i.2 j hj
    have hYi : ∀ i : Fin (P.length - 1), Y i = T.phi m (semV M b.2 i) /
        (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1))) := fun i ↦ by
      rw [hY]; simp only [dif_pos i.2]
    simp only [hMθ', hYi]
    have hYj : Y j = T.phi m (semV M b.2 ⟨j, hj⟩) /
        (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1))) := by
      rw [hY]; simp only [dif_pos hj]
    rw [hYj, hfv]
    have hG' : GPoly.toPoly M (Gf ⟨j, hj⟩) = GPoly.toPoly M (num (f.getD j O1.zero)) := rfl
    rw [hG'] at hphi
    rw [Derivation.leibniz_div, Derivation.leibniz, T.deriv_ratCast, smul_zero, zero_add,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    rw [T.phi_C_ratCast] at hphi
    have hsum : ∑ x : Fin (P.length - 1), T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ x)) / T.phi m qs *
        (T.phi m (semV M b.2 x) / (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1)))) =
        (∑ x, T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ x)) * T.phi m (semV M b.2 x)) /
          (T.phi m qs * (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1)))) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun x _ ↦ by field_simp
    rw [hsum, smul_eq_mul]
    have hG'' : GPoly.toPoly (T.MP m h0) (Gf ⟨j, hj⟩) = GPoly.toPoly M (num (f.getD j O1.zero)) := rfl
    rw [hG''] at hphi
    field_simp
    apply mul_left_cancel₀ hphiq
    linear_combination hphi
  · rintro ⟨Y, hY⟩
    have heq := (hcoord Y).mp hY
    obtain ⟨Z, d, hd0, hZ⟩ := T.exists_common_den m htr (fun i : Fin (P.length - 1) ↦ Y i)
    have hphid : T.phi m d ≠ 0 := fun h0' ↦ hd0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hphiq : T.phi m qs ≠ 0 := fun h0' ↦ hqs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hYi : ∀ i : Fin (P.length - 1), Y i = T.phi m (Z i) / T.phi m d := fun i ↦ by
      rw [← hZ i, mul_div_cancel_right₀ _ hphid]
    have hsol : SysSol 0 (M.sem ((MO Fc ks m).deriv a)) qs qs (semMat M A0f)
        (fun j ↦ ∑ l ∈ Finset.range [Gf].length, C (algebraMap Cc (T.F m) (([1] : List Cc).getD l 0)) *
          GPoly.toPoly M (([Gf].getD l fun _ ↦ []) j)) Z d := by
      refine T.sysSol_of_phiG m htr 0 (M.sem ((MO Fc ks m).deriv a)) (T.phi_DzL_exp m hm hk h0) qs qs (semMat M A0f) _ Z d fun j ↦ ?_
      have hj := heq j j.2
      simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton, List.getD_cons_zero,
        map_one, one_mul]
      rw [← Fin.sum_univ_eq_sum_range (fun i ↦ T.Mθ m h1 P dθ i j * Y i)] at hj
      have hMθ' : ∀ i : Fin (P.length - 1), T.Mθ m h1 P dθ i j = T.phi m (GPoly.toPoly M (A0f j i)) / T.phi m qs :=
        fun i ↦ hMθ i i.2 j j.2
      simp only [hMθ', hYi, hfv] at hj
      rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul] at hj
      simp only [semMat, Matrix.of_apply]
      have hsum : ∑ x, T.phi m (GPoly.toPoly M (A0f j x)) / T.phi m qs *
          (T.phi m (Z x) / T.phi m d) =
          (∑ x, T.phi m (GPoly.toPoly M (A0f j x)) * T.phi m (Z x)) / (T.phi m qs * T.phi m d) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun x _ ↦ by field_simp
      rw [hsum, smul_eq_mul] at hj
      have hG' : GPoly.toPoly M (Gf j) = GPoly.toPoly M (num (f.getD (↑j) O1.zero)) := rfl
      rw [hG']
      field_simp at hj
      linear_combination (T.phi m qs) * hj
    obtain ⟨β, hβc, -⟩ := T.expSysC_complete m h0 (P.length - 1) A0f q q [Gf] hm htr a hk rdeD hrdeD hom r.1 r.2
      (by simpa using hr) [1] (fun l hl ↦ by
        simp only [List.length_singleton] at hl
        exact List.getD_eq_default _ _ (by simpa using hl)) Z d hd0 hsol
    have h1' := hβc 0
    simp only [List.getD_cons_zero] at h1'
    by_contra hcon
    rw [Bool.not_eq_true, List.any_eq_false] at hcon
    have hz : ∀ k ∈ Finset.range r.2.length,
        β.getD k 0 * algebraMap ℚ Cc (((r.2.getD k ([], fun _ ↦ [])).1).getD 0 0) = 0 := by
      intro k hk
      have hmem : r.2.getD k ([], fun _ ↦ []) ∈ r.2 := by
        rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]; exact List.getElem_mem _
      have := hcon _ hmem
      simp only [bne_iff_ne, ne_eq, not_not] at this
      rw [this, map_zero, mul_zero]
    rw [Finset.sum_eq_zero hz] at h1'
    exact one_ne_zero h1'

/-- **Correctness of the exact-part test at an exponential level with a triangular limit.** With `θ` a root of `P` (monic, `N = deg P`) whose powers
`1, …, θ^{N−1}` are linearly independent over `Fₘ₊₁`: `exactC` answers `true` exactly when
`f = ∑ fⱼ θʲ` has an antiderivative `∑ Yᵢ θⁱ` with `Yᵢ ∈ Fₘ₊₁`. -/
theorem exactCT_correct (hm : m < T.n) (h1 : T.Tr (m + 1)) (htr : Transcendental (T.F m) (T.ts m))
    {a : LC m} (hk : ks m = .exp a) (rdeD : LC m → List (LC m) → List (List ℚ × LC m))
    (hrdeD : ∀ c : LC m, RdeSpecK (algebraMap Cc (T.F m)) (T.MP m h1.of_succ)
      ((T.MP m h1.of_succ).sem c)′ (rdeD c))
    (hom : ∀ z : T.F m, z ≠ 0 → ∀ j : ℤ, j ≠ 0 →
      z′ + (j : T.F m) * (T.MP m h1.of_succ).sem ((MO Fc ks m).deriv a) * z ≠ 0)
    (P : GPoly (LC (m + 1))) (f : List (LC (m + 1))) (θ : L) (hP : T.evθ m h1 θ P = 0)
    (hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range (P.length - 1), (a j : L) * θ ^ j = 0 →
      ∀ j < P.length - 1, a j = 0)
    (res : Bool) (hres : exactCT Fc ks m a rdeD P f = some res) :
    res = true ↔ ∃ Y : ℕ → T.F (m + 1),
      (∑ i ∈ Finset.range (P.length - 1), (Y i : L) * θ ^ i)′ =
        ∑ j ∈ Finset.range (P.length - 1),
          ((T.MPr (m + 1) h1).sem (f.getD j (MOr Fc ks (m + 1)).zero) : L) * θ ^ j := by
  classical
  unfold exactCT at hres
  simp only at hres
  split_ifs at hres with hPc
  split at hres
  · exact absurd hres (by simp)
  rename_i dθ hd
  split_ifs at hres with hcof
  split at hres
  · exact absurd hres (by simp)
  rename_i r hr
  obtain rfl := Option.some.inj hres
  set O1 := MOr Fc ks (m + 1) with hO1
  set O := MO Fc ks m with hO
  set M1 := T.MPr (m + 1) h1 with hM1
  set h0 := h1.of_succ with hh0
  set M := T.MP m h0 with hM
  -- `P` is monic of degree `(P.length - 1)`
  have hPc' : O1.isZero (O1.add (P.getD (P.length - 1) O1.zero) (O1.neg O1.one)) = true ∧ (P.length - 1) ≠ 0 := by
    revert hPc
    cases O1.isZero (O1.add (P.getD (P.length - 1) O1.zero) (O1.neg O1.one)) <;> simp
  have hlead : M1.sem (P.getD (P.length - 1) O1.zero) = 1 := by
    have := (M1.isZero_iff _).mp hPc'.1
    rw [M1.sem_add, M1.sem_neg, M1.sem_one, add_neg_eq_zero] at this
    exact this
  have hPlen : P.length = (P.length - 1) + 1 := by
    have : P ≠ [] := fun h0' ↦ by rw [h0'] at hPc'; exact hPc'.2 rfl
    have := List.length_pos_of_ne_nil this
    omega
  have hPdeg : (GPoly.toPoly M1 P).natDegree = (P.length - 1) := by
    apply le_antisymm
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [coeff_toPoly_sem, List.getD_eq_default _ _ (by
        have : (P.length - 1) < k := by exact_mod_cast hk
        omega), M1.sem_zero]
    · exact le_natDegree_of_ne_zero (by rw [coeff_toPoly_sem, hlead]; exact one_ne_zero)
  have hPm : (GPoly.toPoly M1 P).Monic := by
    rw [Monic, leadingCoeff, hPdeg, coeff_toPoly_sem, hlead]
  set Ml : List (List (LC (m + 1))) := (List.range (P.length - 1)).map fun i ↦
    (List.range (P.length - 1)).map fun j ↦ (dPowC O1 P dθ i).getD j O1.zero with hMl
  set ent : List (LC (m + 1)) := Ml.flatten ++ f with hent
  set q := lcmGL O (ent.map Prod.snd) with hq
  set num : LC (m + 1) → GPoly (LC m) := fun c ↦ GPoly.mul O c.1 (cofC O q c.2).2 with hnum
  have hqmon := isMonicC_spec M q (expSysT_monic hr).1
  set qs := GPoly.toPoly M q with hqs
  have hqs0 : qs ≠ 0 := hqmon.ne_zero
  have hcofs : ∀ c ∈ ent, (cofC O q c.2).1 = true := by
    have hall : (ent.map fun c ↦ cofC O q c.2).all Prod.fst = true := by
      revert hcof; cases (ent.map fun c ↦ cofC O q c.2).all Prod.fst <;> simp
    intro c hc
    exact List.all_eq_true.mp hall _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hval : ∀ c ∈ ent, (M1.sem c : T.F (m + 1)) = T.phi m (GPoly.toPoly M (num c)) / T.phi m qs :=
    fun c hc ↦ T.sem_cof m h1 htr q hqs0 c (hcofs c hc)
  have hMe : ∀ i < (P.length - 1), ∀ j < (P.length - 1), (Ml.getD i []).getD j O1.zero ∈ ent := fun i hi j hj ↦ by
    rw [hent]
    apply List.mem_append_left
    rw [List.mem_flatten]
    refine ⟨Ml.getD i [], ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by simpa [hMl] using hi)]; exact List.getElem_mem _
    · have hlen : j < (Ml.getD i []).length := by
        rw [hMl, NestTower.getD_range_map _ _ hi]; simpa using hj
      rw [List.getD_eq_getElem (Ml.getD i []) _ hlen]; exact List.getElem_mem _
  have hMθ : ∀ i < (P.length - 1), ∀ j < (P.length - 1), T.Mθ m h1 P dθ i j =
      T.phi m (GPoly.toPoly M (num ((Ml.getD i []).getD j O1.zero))) / T.phi m qs := by
    intro i hi j hj
    rw [← hval _ (hMe i hi j hj), Mθ, hMl, NestTower.getD_range_map _ _ hi,
      NestTower.getD_range_map _ _ hj]
  have hfv : ∀ j, (M1.sem (f.getD j O1.zero) : T.F (m + 1)) =
      T.phi m (GPoly.toPoly M (num (f.getD j O1.zero))) / T.phi m qs := by
    intro j
    by_cases hj : j < f.length
    · refine hval _ ?_
      rw [hent]
      apply List.mem_append_right
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
    · rw [List.getD_eq_default _ _ (by omega)]
      have hz : O1.zero.1 = [] := rfl
      rw [M1.sem_zero, hnum]
      simp only [hz, GPoly.mul, GPoly.toPoly_nil, map_zero, zero_div]
  set A0f : Fin (P.length - 1) → Fin (P.length - 1) → GPoly (LC m) := fun j i ↦ num ((Ml.getD i []).getD j O1.zero) with hA0f
  set Gf : Fin (P.length - 1) → GPoly (LC m) := fun j ↦ num (f.getD j O1.zero) with hGf
  -- the coordinate equations
  have hcoord : ∀ Y : ℕ → T.F (m + 1),
      ((∑ i ∈ Finset.range (P.length - 1), (Y i : L) * θ ^ i)′ = ∑ j ∈ Finset.range (P.length - 1),
        ((M1.sem (f.getD j O1.zero) : T.F (m + 1)) : L) * θ ^ j) ↔
      ∀ j < (P.length - 1), (Y j)′ + ∑ i ∈ Finset.range (P.length - 1), T.Mθ m h1 P dθ i j * Y i =
        M1.sem (f.getD j O1.zero) := by
    intro Y
    have hdc := T.deriv_coords m h1 θ P hP hPm dθ hd Y
    rw [hPdeg] at hdc
    rw [hdc]
    constructor
    · intro hE j hj
      have h0 := hind (fun j ↦ (Y j)′ + ∑ i ∈ Finset.range (P.length - 1), T.Mθ m h1 P dθ i j * Y i -
        M1.sem (f.getD j O1.zero)) (by
          push_cast
          simp only [sub_mul, Finset.sum_sub_distrib]
          rw [← hE]
          push_cast
          simp only [add_mul, Finset.sum_mul]
          ring) j hj
      exact sub_eq_zero.mp h0
    · intro hE
      exact Finset.sum_congr rfl fun j hj ↦ by rw [hE j (Finset.mem_range.mp hj)]
  constructor
  · intro hany
    obtain ⟨b, hb, he⟩ := List.any_eq_true.mp hany
    simp only [bne_iff_ne, ne_eq] at he
    set e0 : ℚ := b.1.getD 0 0 with he0
    have hs := T.expSysT_sound m h0 (P.length - 1) A0f q q [Gf] a rdeD r.1 r.2 (by simpa using hr) b hb
    obtain ⟨B, hB⟩ := expSysT_den hr
    have hDs : GPoly.toPoly M r.1 ≠ 0 := by
      rw [hB, T.wSysE_Den m h0 ((MO Fc ks m).deriv a) (P.length - 1) A0f q q [Gf] B]
      exact mul_ne_zero hqs0 (pow_ne_zero _ hqs0)
    have hphiD : T.phi m (GPoly.toPoly M r.1) ≠ 0 := fun h0' ↦ hDs (T.phi_injective htr
      (by rw [h0', map_zero]))
    have hphiq : T.phi m qs ≠ 0 := fun h0' ↦ hqs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hE : ((e0 : ℚ) : T.F (m + 1)) ≠ 0 := by exact_mod_cast he
    set Y : ℕ → T.F (m + 1) := fun i ↦ if hi : i < P.length - 1 then
      T.phi m (semV M b.2 ⟨i, hi⟩) / (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1))) else 0
      with hY
    refine ⟨Y, (hcoord Y).mpr fun j hj ↦ ?_⟩
    have hphi := T.sysSol_phiG m 0 (M.sem ((MO Fc ks m).deriv a)) (T.phi_DzL_exp m hm hk h0) qs qs (semMat M A0f) _ (semV M b.2) (GPoly.toPoly M r.1)
      ⟨j, hj⟩ hs
    simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton, List.getD_cons_zero,
      map_mul, semMat, Matrix.of_apply] at hphi
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦ T.Mθ m h1 P dθ i j * Y i)]
    have hMθ' : ∀ i : Fin (P.length - 1),
        T.Mθ m h1 P dθ i j = T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ i)) / T.phi m qs :=
      fun i ↦ hMθ i i.2 j hj
    have hYi : ∀ i : Fin (P.length - 1), Y i = T.phi m (semV M b.2 i) /
        (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1))) := fun i ↦ by
      rw [hY]; simp only [dif_pos i.2]
    simp only [hMθ', hYi]
    have hYj : Y j = T.phi m (semV M b.2 ⟨j, hj⟩) /
        (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1))) := by
      rw [hY]; simp only [dif_pos hj]
    rw [hYj, hfv]
    have hG' : GPoly.toPoly M (Gf ⟨j, hj⟩) = GPoly.toPoly M (num (f.getD j O1.zero)) := rfl
    rw [hG'] at hphi
    rw [Derivation.leibniz_div, Derivation.leibniz, T.deriv_ratCast, smul_zero, zero_add,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    rw [T.phi_C_ratCast] at hphi
    have hsum : ∑ x : Fin (P.length - 1), T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ x)) / T.phi m qs *
        (T.phi m (semV M b.2 x) / (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1)))) =
        (∑ x, T.phi m (GPoly.toPoly M (A0f ⟨j, hj⟩ x)) * T.phi m (semV M b.2 x)) /
          (T.phi m qs * (T.phi m (GPoly.toPoly M r.1) * (e0 : T.F (m + 1)))) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun x _ ↦ by field_simp
    rw [hsum, smul_eq_mul]
    have hG'' : GPoly.toPoly (T.MP m h0) (Gf ⟨j, hj⟩) = GPoly.toPoly M (num (f.getD j O1.zero)) := rfl
    rw [hG''] at hphi
    field_simp
    apply mul_left_cancel₀ hphiq
    linear_combination hphi
  · rintro ⟨Y, hY⟩
    have heq := (hcoord Y).mp hY
    obtain ⟨Z, d, hd0, hZ⟩ := T.exists_common_den m htr (fun i : Fin (P.length - 1) ↦ Y i)
    have hphid : T.phi m d ≠ 0 := fun h0' ↦ hd0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hphiq : T.phi m qs ≠ 0 := fun h0' ↦ hqs0 (T.phi_injective htr (by rw [h0', map_zero]))
    have hYi : ∀ i : Fin (P.length - 1), Y i = T.phi m (Z i) / T.phi m d := fun i ↦ by
      rw [← hZ i, mul_div_cancel_right₀ _ hphid]
    have hsol : SysSol 0 (M.sem ((MO Fc ks m).deriv a)) qs qs (semMat M A0f)
        (fun j ↦ ∑ l ∈ Finset.range [Gf].length, C (algebraMap Cc (T.F m) (([1] : List Cc).getD l 0)) *
          GPoly.toPoly M (([Gf].getD l fun _ ↦ []) j)) Z d := by
      refine T.sysSol_of_phiG m htr 0 (M.sem ((MO Fc ks m).deriv a)) (T.phi_DzL_exp m hm hk h0) qs qs (semMat M A0f) _ Z d fun j ↦ ?_
      have hj := heq j j.2
      simp only [List.length_singleton, Finset.range_one, Finset.sum_singleton, List.getD_cons_zero,
        map_one, one_mul]
      rw [← Fin.sum_univ_eq_sum_range (fun i ↦ T.Mθ m h1 P dθ i j * Y i)] at hj
      have hMθ' : ∀ i : Fin (P.length - 1), T.Mθ m h1 P dθ i j = T.phi m (GPoly.toPoly M (A0f j i)) / T.phi m qs :=
        fun i ↦ hMθ i i.2 j j.2
      simp only [hMθ', hYi, hfv] at hj
      rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul] at hj
      simp only [semMat, Matrix.of_apply]
      have hsum : ∑ x, T.phi m (GPoly.toPoly M (A0f j x)) / T.phi m qs *
          (T.phi m (Z x) / T.phi m d) =
          (∑ x, T.phi m (GPoly.toPoly M (A0f j x)) * T.phi m (Z x)) / (T.phi m qs * T.phi m d) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun x _ ↦ by field_simp
      rw [hsum, smul_eq_mul] at hj
      have hG' : GPoly.toPoly M (Gf j) = GPoly.toPoly M (num (f.getD (↑j) O1.zero)) := rfl
      rw [hG']
      field_simp at hj
      linear_combination (T.phi m qs) * hj
    obtain ⟨β, hβc, -⟩ := T.expSysT_complete m h0 (P.length - 1) A0f q q [Gf] hm htr a hk rdeD hrdeD hom r.1 r.2
      (by simpa using hr) [1] (fun l hl ↦ by
        simp only [List.length_singleton] at hl
        exact List.getD_eq_default _ _ (by simpa using hl)) Z d hd0 hsol
    have h1' := hβc 0
    simp only [List.getD_cons_zero] at h1'
    by_contra hcon
    rw [Bool.not_eq_true, List.any_eq_false] at hcon
    have hz : ∀ k ∈ Finset.range r.2.length,
        β.getD k 0 * algebraMap ℚ Cc (((r.2.getD k ([], fun _ ↦ [])).1).getD 0 0) = 0 := by
      intro k hk
      have hmem : r.2.getD k ([], fun _ ↦ []) ∈ r.2 := by
        rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]; exact List.getElem_mem _
      have := hcon _ hmem
      simp only [bne_iff_ne, ne_eq, not_not] at this
      rw [this, map_zero, mul_zero]
    rw [Finset.sum_eq_zero hz] at h1'
    exact one_ne_zero h1'

end MTower

end Curves.MT
