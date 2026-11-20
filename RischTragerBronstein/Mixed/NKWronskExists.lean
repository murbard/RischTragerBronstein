import RischTragerBronstein.Mixed.NKUnits0Decide
import RischTragerBronstein.Mixed.NKCodeField

/-!
# Existence of generalized Wronskian certificates

`exists_wronsk`: over a differential field `L`, let `S ⊆ L` be a subfield closed under the
derivation and `gᵢⱼ ∈ S` (`i < k`, positions `j ≥ 1`). If no nonzero family of constants of `S`
kills all the rows `(gᵢⱼ)_{j ≥ 1}`, there are positions `Jₚ ≥ 1`, derivative orders `Dₚ` and a
right inverse `H` (entries in `S`) of the matrix `(gᵢ_{Jₚ})^{(Dₚ)}`.

Proof: the columns `((gᵢⱼ)^{(d)})ᵢ ∈ Sᵏ` span `Sᵏ`; otherwise a nonzero linear form kills them,
and one with minimal support, normalized at one index, has derivative killing them with smaller
support, so it is constant — excluded. A basis of `Sᵏ` among the columns gives `H`.
-/

open Differential

namespace Curves.MT

section Abstract

variable {L : Type*} [Field L] [Differential L]

lemma iterate_deriv_mem (S : Subfield L) (hS : ∀ z ∈ S, z′ ∈ S) (d : ℕ) {z : L} (hz : z ∈ S) :
    (Differential.deriv)^[d] z ∈ S := by
  induction d with
  | zero => exact hz
  | succ d ih => rw [Function.iterate_succ_apply']; exact hS _ ih

/-- **Minimal support**: a nonzero `S`-family killing all derivatives of all rows yields a
nonzero constant family killing the rows. -/
lemma exists_const_kill (S : Subfield L) (hS : ∀ z ∈ S, z′ ∈ S) (k : ℕ) (g : Fin k → ℕ → L)
    (a : Fin k → L) (haS : ∀ i, a i ∈ S) (ha0 : a ≠ 0)
    (ha : ∀ j, 1 ≤ j → ∀ d, ∑ i, a i * (Differential.deriv)^[d] (g i j) = 0) :
    ∃ c : Fin k → L, (∀ i, c i ∈ S) ∧ (∀ i, (c i)′ = 0) ∧ c ≠ 0 ∧
      ∀ j, 1 ≤ j → ∑ i, c i * g i j = 0 := by
  classical
  let Good : (Fin k → L) → Prop := fun a ↦ (∀ i, a i ∈ S) ∧ a ≠ 0 ∧
    ∀ j, 1 ≤ j → ∀ d, ∑ i, a i * (Differential.deriv)^[d] (g i j) = 0
  have hex : ∃ s, ∃ a, Good a ∧ (Finset.univ.filter fun i ↦ a i ≠ 0).card = s :=
    ⟨_, a, ⟨haS, ha0, ha⟩, rfl⟩
  obtain ⟨b, ⟨hbS, hb0, hb⟩, hbs⟩ := Nat.find_spec hex
  have hmin : ∀ a, Good a → Nat.find hex ≤ (Finset.univ.filter fun i ↦ a i ≠ 0).card :=
    fun a ha ↦ Nat.find_min' hex ⟨a, ha, rfl⟩
  obtain ⟨i0, hi0⟩ : ∃ i0, b i0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hb0 (funext h)
  set c : Fin k → L := fun i ↦ (b i0)⁻¹ * b i with hc
  have hcS : ∀ i, c i ∈ S := fun i ↦ mul_mem (inv_mem (hbS i0)) (hbS i)
  have hc1 : c i0 = 1 := by simp [hc, hi0]
  have hcsupp : ∀ i, c i ≠ 0 ↔ b i ≠ 0 := fun i ↦ by simp [hc, hi0]
  have hc : ∀ j, 1 ≤ j → ∀ d, ∑ i, c i * (Differential.deriv)^[d] (g i j) = 0 := by
    intro j hj d
    simp only [hc, mul_assoc, ← Finset.mul_sum, hb j hj d, mul_zero]
  have hcd : ∀ j, 1 ≤ j → ∀ d, ∑ i, (c i)′ * (Differential.deriv)^[d] (g i j) = 0 := by
    intro j hj d
    have h1 := congrArg Differential.deriv (hc j hj d)
    rw [map_sum, Derivation.map_zero] at h1
    have h2 := hc j hj (d + 1)
    simp only [Function.iterate_succ_apply'] at h2
    have hl : ∀ i, (c i * (Differential.deriv)^[d] (g i j))′ =
        c i * ((Differential.deriv)^[d] (g i j))′ + (c i)′ * (Differential.deriv)^[d] (g i j) :=
      fun i ↦ by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
    rw [Finset.sum_congr rfl (fun i _ ↦ hl i), Finset.sum_add_distrib, h2, zero_add] at h1
    exact h1
  have hcd0 : (fun i ↦ (c i)′) = 0 := by
    by_contra hne
    have hgood : Good fun i ↦ (c i)′ := ⟨fun i ↦ hS _ (hcS i), hne, hcd⟩
    have hle := hmin _ hgood
    have hsub : (Finset.univ.filter fun i ↦ (c i)′ ≠ 0) ⊂
        (Finset.univ.filter fun i ↦ b i ≠ 0) := by
      refine Finset.ssubset_iff_of_subset (fun i hi ↦ ?_) |>.mpr ⟨i0, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        rw [← hcsupp]
        intro h0
        exact hi (by rw [h0, Derivation.map_zero])
      · simp [hi0]
      · simp [hc1]
    have := Finset.card_lt_card hsub
    omega
  refine ⟨c, hcS, fun i ↦ congrFun hcd0 i, fun h ↦ ?_, fun j hj ↦ hc j hj 0⟩
  have := congrFun h i0
  rw [hc1] at this
  exact one_ne_zero this

/-- **Generalized Wronskian certificates exist** when the rows are independent over the constants
of `S`. -/
theorem exists_wronsk (S : Subfield L) (hS : ∀ z ∈ S, z′ ∈ S) (k : ℕ) (g : Fin k → ℕ → L)
    (hg : ∀ i j, g i j ∈ S)
    (hind : ∀ c : Fin k → L, (∀ i, c i ∈ S) → (∀ i, (c i)′ = 0) →
      (∀ j, 1 ≤ j → ∑ i, c i * g i j = 0) → c = 0) :
    ∃ (J D : Fin k → ℕ) (H : Fin k → Fin k → L), (∀ p, 1 ≤ J p) ∧ (∀ p l, H p l ∈ S) ∧
      ∀ i l, ∑ p, (Differential.deriv)^[D p] (g i (J p)) * H p l = if i = l then 1 else 0 := by
  classical
  -- the columns, as vectors over `S`
  let col : {j : ℕ // 1 ≤ j} × ℕ → (Fin k → S) := fun c i ↦
    ⟨(Differential.deriv)^[c.2] (g i c.1), iterate_deriv_mem S hS _ (hg i c.1)⟩
  have hspan : Submodule.span S (Set.range col) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    set a : Fin k → S := fun i ↦ f fun j ↦ if i = j then 1 else 0 with ha
    have hfa : ∀ v : Fin k → S, f v = ∑ i, v i * a i := fun v ↦ by
      rw [LinearMap.pi_apply_eq_sum_univ f v]; rfl
    have ha0 : (fun i ↦ (a i : L)) ≠ 0 := by
      intro h
      apply hf0
      apply LinearMap.ext
      intro v
      rw [hfa]
      simp only [LinearMap.zero_apply]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      have : (a i : L) = 0 := congrFun h i
      rw [show a i = 0 from Subtype.ext this, mul_zero]
    have hkill : ∀ j, 1 ≤ j → ∀ d, ∑ i, (a i : L) * (Differential.deriv)^[d] (g i j) = 0 := by
      intro j hj d
      have h0 : f (col (⟨j, hj⟩, d)) = 0 := hker (Submodule.subset_span ⟨_, rfl⟩)
      rw [hfa] at h0
      have h1 := congrArg (fun z : S ↦ (z : L)) h0
      simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, col, ZeroMemClass.coe_zero] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    obtain ⟨c, hcS, hcc, hc0, hcg⟩ :=
      exists_const_kill S hS k g (fun i ↦ (a i : L)) (fun i ↦ (a i).2) ha0 hkill
    exact hc0 (hind c hcS hcc hcg)
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent S (Set.range col)
  have hbsp : ⊤ ≤ Submodule.span S (Set.range ((↑) : b → Fin k → S)) := by
    rw [Subtype.range_coe, hbspan, hspan]
  let B := Module.Basis.mk hbli hbsp
  have : Fintype b := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card b = k := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e : Fin k ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hpre : ∀ p : Fin k, ∃ c, col c = (e p : Fin k → S) := fun p ↦ hbsub (e p).2
  choose cp hcp using hpre
  refine ⟨fun p ↦ (cp p).1.1, fun p ↦ (cp p).2,
    fun p l ↦ (B.repr (fun j ↦ if l = j then 1 else 0) (e p) : L),
    fun p ↦ (cp p).1.2, fun p l ↦ (B.repr _ (e p)).2, fun i l ↦ ?_⟩
  have hsum := B.sum_repr (fun j ↦ if l = j then (1 : S) else 0)
  have hi := congrArg (fun v : Fin k → S ↦ ((v i : S) : L)) hsum
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, AddSubmonoidClass.coe_finsetSum,
    MulMemClass.coe_mul] at hi
  rw [← e.sum_comp] at hi
  have hr : (((if l = i then (1 : S) else 0 : S)) : L) = if i = l then 1 else 0 := by
    by_cases h : i = l
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [hr] at hi
  rw [← hi]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Module.Basis.mk_apply, ← hcp p, mul_comm]

end Abstract

open Polynomial IntermediateField Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

omit [Field Cc] [Field L] [Algebra Cc L] [Differential Cc] [Differential L]
  [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L] in
lemma getD_ofFn_fin {α : Type*} {n : ℕ} (f : Fin n → α) (p : Fin n) (d : α) :
    (List.ofFn f).getD p d = f p := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

omit [Field Cc] [Field L] [Algebra Cc L] [Differential Cc] [Differential L]
  [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L] in
lemma getD_ofFn_lt {α : Type*} {n i : ℕ} (f : Fin n → α) (hi : i < n) (d : α) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

lemma coe_iterate_deriv (m : ℕ) (z : T.F m) (d : ℕ) :
    (((Differential.deriv)^[d] z : T.F m) : L) = (Differential.deriv)^[d] (z : L) := by
  induction d with
  | zero => rfl
  | succ d ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', T.coe_deriv, ih]

/-- **The Wronskian certificate `indepWC` exists** as soon as the coefficient rows `(gᵢⱼ)_{j ≥ 1}` of
the codes `gls` are linearly independent over the constants of the code field. -/
theorem indepWC_exists (m : ℕ) (h1 : T.Tr (m + 1)) (gls : List (GPoly (LC (m + 1))))
    (hind : ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) → (∀ i, (c i)′ = 0) →
      (∀ j, 1 ≤ j → ∑ i, c i * (((T.MP (m + 1) h1).sem ((gls.getD i []).getD j
        (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) = 0) → c = 0) :
    ∃ J D H, indepWC Fc ks m gls J D H = true ∧ indepC Fc ks m gls (J ++ D) H = true := by
  classical
  set M := T.MP (m + 1) h1 with hM
  set z := (MOr Fc ks (m + 1)).zero with hz
  set g : Fin gls.length → ℕ → L := fun i j ↦ ((M.sem ((gls.getD i []).getD j z) : T.F (m + 1)) : L)
    with hg
  have hS : ∀ w ∈ (T.codeVals (m + 1) h1).toSubfield, w′ ∈ (T.codeVals (m + 1) h1).toSubfield := by
    rintro _ ⟨c, rfl⟩
    exact ⟨(MO Fc ks (m + 1)).deriv c, by rw [M.sem_deriv, T.coe_deriv]⟩
  obtain ⟨J, D, H, hJ, hHS, hH⟩ := exists_wronsk _ hS gls.length g
    (fun i j ↦ T.sem_mem_codeVals (m + 1) h1 _) hind
  choose Hc hHc using fun p l ↦ (T.mem_codeVals (m := m + 1) (h := h1)).mp (hHS p l)
  have key : ∀ Jl Dl : List ℕ, (∀ p : Fin gls.length, Jl.getD p 0 = J p) →
      (∀ p : Fin gls.length, Dl.getD p 0 = D p) →
      indepWC Fc ks m gls Jl Dl (List.ofFn fun p ↦ List.ofFn (Hc p)) = true := by
    intro Jl Dl hJl hDl
    simp only [indepWC, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
    refine ⟨fun p hp ↦ ?_, fun i hi l hl ↦ ?_⟩
    · rw [hJl ⟨p, hp⟩]
      exact hJ _
    · rw [M.isZero_iff, M.sem_add, M.sem_neg, sem_lsumC, List.map_map,
        ← List.sum_toFinset _ List.nodup_range, List.toFinset_range, add_neg_eq_zero,
        Finset.sum_range]
      apply Subtype.val_injective
      have e2 : M.sem (if i = l then (MO Fc ks (m + 1)).one else (MO Fc ks (m + 1)).zero) =
          if i = l then 1 else 0 := by
        split_ifs
        · exact M.sem_one
        · exact M.sem_zero
      rw [e2]
      have hH' := hH ⟨i, hi⟩ ⟨l, hl⟩
      have e3 : ((if (⟨i, hi⟩ : Fin gls.length) = ⟨l, hl⟩ then 1 else 0 : L)) =
          (((if i = l then 1 else 0 : T.F (m + 1))) : L) := by
        split_ifs with h h' h' <;> simp_all [Fin.ext_iff]
      rw [e3] at hH'
      rw [← hH', IntermediateField.coe_sum]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      simp only [Function.comp_apply, M.sem_mul, IntermediateField.coe_mul,
        hJl, hDl, getD_ofFn_fin, getD_ofFn_lt _ hl]
      rw [hM, T.sem_iterDC m h1, T.coe_iterate_deriv, ← hHc]
  refine ⟨List.ofFn J, List.ofFn D, _, key _ _ (fun p ↦ getD_ofFn_fin J p 0) (fun p ↦ getD_ofFn_fin D p 0), ?_⟩
  unfold indepC
  rw [List.drop_left' (by simp)]
  refine key _ _ (fun p ↦ ?_) (fun p ↦ getD_ofFn_fin D p 0)
  rw [List.getD_append _ _ _ _ (by simp), getD_ofFn_fin]

/-- **`indepWC` exists for logarithmic derivatives independent modulo `Fₘ₊₁`**: if no nonzero
family of constants of the code field makes `∑ cᵢ gᵢ(θ)` fall into `Fₘ₊₁`, a Wronskian certificate
exists. -/
theorem indepWC_exists_of_logs (m : ℕ) (h1 : T.Tr (m + 1)) (θ : L) (n : ℕ)
    (gls : List (GPoly (LC (m + 1)))) (hlen : ∀ i < gls.length, (gls.getD i []).length ≤ n)
    (hli : ∀ c : Fin gls.length → L, (∀ i, c i ∈ T.codeVals (m + 1) h1) → (∀ i, (c i)′ = 0) →
      (∃ f : T.F (m + 1), ∑ i, c i * T.evθ m h1 θ (gls.getD i []) = f) → c = 0) :
    ∃ J D H, indepWC Fc ks m gls J D H = true ∧ indepC Fc ks m gls (J ++ D) H = true := by
  classical
  refine T.indepWC_exists m h1 gls fun c hcS hcc hrow ↦ hli c hcS hcc ?_
  set G : Fin gls.length → ℕ → L := fun i j ↦ (((T.MP (m + 1) h1).sem ((gls.getD i []).getD j
    (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) with hG
  have hcF : ∀ i, c i ∈ T.F (m + 1) := fun i ↦ T.codeVals_le (m + 1) h1 _ (hcS i)
  refine ⟨⟨∑ i, c i * G i 0, sum_mem fun i _ ↦ mul_mem (hcF i) (SetLike.coe_mem _)⟩, ?_⟩
  change _ = ∑ i, c i * G i 0
  have e1 : ∀ i : Fin gls.length, T.evθ m h1 θ (gls.getD i []) =
      ∑ j ∈ Finset.range (n + 1), G i j * θ ^ j :=
    fun i ↦ by rw [T.evθ_list_le m h1 θ _ (n + 1) (by have := hlen i i.2; omega)]; rfl
  simp only [e1, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_range_succ', Finset.sum_eq_zero, zero_add]
  · simp only [pow_zero, mul_one]
  · intro j _
    have := hrow (j + 1) (by omega)
    rw [show ∑ i, c i * (G i (j + 1) * θ ^ (j + 1)) = (∑ i, c i * G i (j + 1)) * θ ^ (j + 1) by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ ↦ by ring]
    rw [show (∑ i, c i * G i (j + 1)) = 0 from this, zero_mul]

end MTower

end Curves.MT
