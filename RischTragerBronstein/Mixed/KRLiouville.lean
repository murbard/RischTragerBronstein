import RischTragerBronstein.Mixed.KRLogs

/-!
# `b(x) yʲ`, `yⁿ = p(x)`, over an exponential `x′ = η x`: the Liouville theorems

`ζ ∈ C` a primitive `n`-th root of unity, `β₀ⁿ = p(0) ≠ 0`, `0 < j < n`, `gcd(j, n) = 1`,
`b yʲ` without poles at the ordinary places over `x ≠ 0`. The logarithms of a Liouville form have no
zeros or poles over `x ≠ 0` (`kr_prep`), so their `yʲ`-projections are governed by `KRLogs`:

* `kr_liouville_exact`: if every such logarithm has zero projection (`β₀ ∉ C`, `galois_shift`; or
  `Ψ = ∑ c_n(k) P_k` not torsion, `four_dl_nontors`), then `b yʲ = (a yʲ)′`;
* `kr_liouville_tors`: with a witness `W` of `N Ψ`, `b yʲ = (a yʲ)′ + e Eⱼ yʲ` where
  `W′/W = ∑ Eᵢ yⁱ`.
-/

open Polynomial IntermediateField Ramanujan

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L)

/-- **The Liouville data for `b yʲ`**: logarithms without zeros or poles over `x ≠ 0`. -/
theorem kr_prep (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η * X))
    (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
    (hgood : ∀ α : K, α ≠ 0 → α′ ≠ algebraMap C K η * α)
    (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (jj : ℕ) (hj0 : 0 < jj) (hjn : jj < S.n) (f : L) (hf : f ∈ C⟮S.x⟯⟮S.y⟯) (b : L)
    (hb : b ∈ C⟮S.x⟯) (hfb : f = b * S.y ^ jj)
    (hreg : ∀ α β : K, β ≠ 0 → β ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 →
      0 ≤ S.ordAt K ⟨f, hf⟩ α β)
    {ι : Type*} (s : Finset ι) (c u : ι → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ (k : ℕ) (d : ℕ → C) (w : ℕ → L) (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0),
      f = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * logDeriv (w j) ∧
      (∀ j < k, (d j)′ = 0) ∧
      ∀ j (hj : j < k), ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 →
        S.ordAt K ⟨w j, (hw j hj).1⟩ α β = 0 := by
  classical
  obtain ⟨k, d, w, ⟨hd, hw, hind⟩, hsum⟩ :=
    logSum_qindep (C⟮S.x⟯⟮S.y⟯).toSubfield s c u hc (fun i hi ↦ hu i hi)
  set d' : ℕ → C := fun jj ↦ if h : jj < k then Classical.choose (hconstC (d jj) (hd jj h)) else 0
    with hd'def
  have hdd : ∀ jj < k, algebraMap C L (d' jj) = d jj := fun jj hjj ↦ by
    simp only [hd'def, dif_pos hjj]
    exact Classical.choose_spec (hconstC (d jj) (hd jj hjj))
  have hind' : ∀ q : ℕ → ℚ, ∑ jj ∈ Finset.range k, (q jj : C) * d' jj = 0 →
      ∀ jj < k, q jj = 0 := by
    intro q hq
    apply hind q
    rw [← map_zero (algebraMap C L), ← hq, map_sum]
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [map_mul, map_ratCast, hdd jj (Finset.mem_range.mp hjj)]
  have hw' : ∀ jj < k, w jj ∈ C⟮S.x⟯⟮S.y⟯ ∧ w jj ≠ 0 := fun jj hjj ↦ ⟨(hw jj hjj).2, (hw jj hjj).1⟩
  have heq' : f = v′ + ∑ jj ∈ Finset.range k, algebraMap C L (d' jj) * logDeriv (w jj) := by
    rw [heq, hsum]
    congr 1
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [hdd jj (Finset.mem_range.mp hjj)]
  have hd'c : ∀ j < k, (d' j)′ = 0 := fun j hj ↦ by
    have := hd j hj
    rw [← hdd j hj, deriv_algebraMap] at this
    exact (algebraMap C L).injective (by rw [this, map_zero])
  refine ⟨k, d', w, hw', heq', hd'c, fun j hj α β hvβ hα ↦ ?_⟩
  have heq'' : f = v′ + ∑ jj ∈ Finset.range k, algebraMap C L (d' jj) * ((w jj)′ / w jj) := by
    rw [heq']; rfl
  have hgα : α′ ≠ ((Polynomial.C η * X).map (algebraMap C K)).eval α := by
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_mul, eval_C, eval_X]
    exact hgood α hα
  by_cases hβ : β = 0
  · subst hβ
    have he : (S.p.map (algebraMap C K)).eval α = 0 := by rw [← hvβ, zero_pow S.hn.ne']
    exact S.ordAt_logs_zero_classW (Polynomial.C η * X) hx hK k d' w hw' hind' v f hv hf heq'' b hb
      jj hj0 hjn hfb α he hgα j hj
  · exact S.ordAt_logs_zeroW (Polynomial.C η * X) hx hK k d' w hw' hind' v f hv hf heq'' α β hvβ
      hgα (hreg α β hβ hvβ hα) j hj

section Main

variable (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η * X))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
  (hgood : ∀ α : K, α ≠ 0 → α′ ≠ algebraMap C K η * α)
  (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
  (ζ : C) (hζ : IsPrimitiveRoot ζ S.n) (j : Fin S.n) (hj0 : 0 < (j : ℕ))
  (b : L) (hb : b ∈ C⟮S.x⟯) (hbm : b * S.y ^ (j : ℕ) ∈ C⟮S.x⟯⟮S.y⟯)
  (hreg : ∀ α β : K, β ≠ 0 → β ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 →
      0 ≤ S.ordAt K ⟨b * S.y ^ (j : ℕ), hbm⟩ α β)

include hx hK hgood hconstC hζ hj0 hb hreg in
/-- **The projected Liouville form**: `n b yʲ = (n aⱼ yʲ)′ + ∑ dᵢ four j (wᵢ′/wᵢ)`. -/
theorem kr_project {ι : Type*} (s : Finset ι) (c u : ι → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y ^ (j : ℕ) = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ (k : ℕ) (d : ℕ → C) (W : ℕ → C⟮S.x⟯⟮S.y⟯) (a : C⟮S.x⟯),
      (∀ i < k, W i ≠ 0 ∧ S.Supp (K := K) (W i)) ∧ (∀ i < k, (d i)′ = 0) ∧
      (S.n : C⟮S.x⟯⟮S.y⟯) * (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨b, hb⟩ *
          AdjoinSimple.gen C⟮S.x⟯ S.y ^ (j : ℕ)) =
        S.dTW (Polynomial.C η * X) hx ((S.n : C⟮S.x⟯⟮S.y⟯) *
          (algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (j : ℕ))) +
        ∑ i ∈ Finset.range k, S.cst (d i) *
          S.four ζ hζ j (S.dl (Polynomial.C η * X) hx (W i)) := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  obtain ⟨k, d, w, hw, heq', hdc, hord⟩ := S.kr_prep (K := K) η hx hK hgood hconstC j hj0 j.2 _ hbm
    b hb rfl hreg s c u hc hu v hv heq
  set W : ℕ → C⟮S.x⟯⟮S.y⟯ := fun i ↦ if h : i < k then ⟨w i, (hw i h).1⟩ else 1 with hW
  have hWi : ∀ i < k, (W i : L) = w i := fun i hi ↦ by simp [hW, dif_pos hi]
  have hW0 : ∀ i < k, W i ≠ 0 := fun i hi h ↦ (hw i hi).2 (by rw [← hWi i hi, h]; rfl)
  have hWs : ∀ i < k, S.Supp (K := K) (W i) := fun i hi α β hv hα ↦ by
    have e : W i = ⟨w i, (hw i hi).1⟩ := by simp [hW, dif_pos hi]
    rw [e]; exact hord i hi α β hv hα
  obtain ⟨aV, haV⟩ := S.power_repr ⟨v, hv⟩
  refine ⟨k, d, W, aV j, fun i hi ↦ ⟨hW0 i hi, hWs i hi⟩, hdc, ?_⟩
  -- the Liouville form on `C(x, y)`
  have hF : (⟨b * S.y ^ (j : ℕ), hbm⟩ : C⟮S.x⟯⟮S.y⟯) =
      S.dTW (Polynomial.C η * X) hx ⟨v, hv⟩ + ∑ i ∈ Finset.range k, S.cst (d i) *
        S.dl (Polynomial.C η * X) hx (W i) := by
    apply Subtype.ext
    rw [IntermediateField.coe_add, coe_dTW,
      show ((∑ i ∈ Finset.range k, S.cst (d i) * S.dl (Polynomial.C η * X) hx (W i) :
        C⟮S.x⟯⟮S.y⟯) : L) = ∑ i ∈ Finset.range k, ((S.cst (d i) *
          S.dl (Polynomial.C η * X) hx (W i) : C⟮S.x⟯⟮S.y⟯) : L) from map_sum (C⟮S.x⟯⟮S.y⟯).val _ _]
    change b * S.y ^ (j : ℕ) = _
    rw [heq']
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [IntermediateField.coe_mul, coe_dl, hWi i (Finset.mem_range.mp hi)]
    rfl
  have hFrepr : (⟨b * S.y ^ (j : ℕ), hbm⟩ : C⟮S.x⟯⟮S.y⟯) =
      ∑ i : Fin S.n, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (if i = j then ⟨b, hb⟩ else 0) *
        AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ) := by
    rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [if_neg hij, map_zero, zero_mul])
      (fun h ↦ absurd (Finset.mem_univ j) h), if_pos rfl]
    rfl
  have h4 := congrArg (S.four ζ hζ j) hF
  rw [S.four_add, S.four_dTW (Polynomial.C η * X) hx ζ hζ, S.four_sum] at h4
  simp_rw [S.four_cst_mul] at h4
  rw [hFrepr, S.four_repr, if_pos rfl, haV, S.four_repr] at h4
  exact h4

include hx hK hgood hconstC hζ hj0 hb hreg in
/-- **Exactness**: if every logarithm without zeros or poles over `x ≠ 0` has no
`yʲ`-projection, a Liouville form for `b yʲ` forces `b yʲ = (a yʲ)′`. -/
theorem kr_liouville_exact
    (hproj : ∀ W : C⟮S.x⟯⟮S.y⟯, W ≠ 0 → S.Supp (K := K) W →
      S.four ζ hζ j (S.dl (Polynomial.C η * X) hx W) = 0)
    {ι : Type*} (s : Finset ι) (c u : ι → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y ^ (j : ℕ) = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ a ∈ C⟮S.x⟯, b * S.y ^ (j : ℕ) = (a * S.y ^ (j : ℕ))′ := by
  obtain ⟨k, d, W, a, hW, -, h4⟩ := S.kr_project η hx hK hgood hconstC ζ hζ j hj0 b hb hbm hreg
    s c u hc hu v hv heq
  rw [Finset.sum_eq_zero fun i hi ↦ by rw [hproj (W i) (hW i (Finset.mem_range.mp hi)).1
    (hW i (Finset.mem_range.mp hi)).2, mul_zero], add_zero] at h4
  refine ⟨a, a.2, ?_⟩
  have hL := congrArg Subtype.val h4
  simp only [IntermediateField.coe_mul, coe_dTW, IntermediateField.coe_pow] at hL
  have hn0 : ((S.n : C⟮S.x⟯⟮S.y⟯) : L) = (S.n : L) := by simp
  rw [hn0] at hL
  have hnL : (S.n : L) ≠ 0 := by exact_mod_cast S.hn.ne'
  rw [Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero, smul_eq_mul] at hL
  have hy : ((AdjoinSimple.gen C⟮S.x⟯ S.y : C⟮S.x⟯⟮S.y⟯) : L) = S.y := rfl
  simp only [IntermediateField.algebraMap_apply, hy] at hL
  exact mul_left_cancel₀ hnL hL

include hx hK hgood hconstC hζ hj0 hb hreg in
/-- **With a witness `W` of `N Ψ`**: `b yʲ = (a yʲ)′ + e Eⱼ yʲ`, `W′/W = ∑ Eᵢ yⁱ`. -/
theorem kr_liouville_tors (β₀ : K) (hβ₀ : β₀ ≠ 0) (hv0 : β₀ ^ S.n = (S.p.map (algebraMap C K)).eval 0)
    (hcop : Nat.Coprime S.n S.p.natDegree) (hjc : Nat.Coprime (j : ℕ) S.n) (hn1 : 1 < S.n)
    (N : ℕ) (hN : 0 < N) (W₀ : C⟮S.x⟯⟮S.y⟯) (hW₀ : W₀ ≠ 0) (hsW : S.Supp (K := K) W₀)
    (hWr : ∀ m, S.rv ζ β₀ W₀ m = N * ramC S.n m)
    (E : Fin S.n → C⟮S.x⟯) (hE : S.dl (Polynomial.C η * X) hx W₀ =
      ∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (E i) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ))
    {ι : Type*} (s : Finset ι) (c u : ι → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y ^ (j : ℕ) = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ a ∈ C⟮S.x⟯, ∃ e : C, e′ = 0 ∧
      b * S.y ^ (j : ℕ) = (a * S.y ^ (j : ℕ))′ + algebraMap C L e * ((E j : L) * S.y ^ (j : ℕ)) := by
  classical
  obtain ⟨k, d, W, a, hW, hdc, h4⟩ := S.kr_project η hx hK hgood hconstC ζ hζ j hj0 b hb hbm hreg
    s c u hc hu v hv heq
  have hl := fun i (hi : i < k) ↦ S.four_dl_tors (Polynomial.C η * X) hx ζ hζ β₀ hβ₀ hv0 hcop j
    hjc hn1 N hN W₀ hW₀ hsW hWr (W i) (hW i hi).1 (hW i hi).2
  choose! e he hel using hl
  set es : C := ∑ i ∈ Finset.range k, d i * e i
  have hsum : ∑ i ∈ Finset.range k, S.cst (d i) * S.four ζ hζ j (S.dl (Polynomial.C η * X) hx (W i)) =
      S.cst es * S.four ζ hζ j (S.dl (Polynomial.C η * X) hx W₀) := by
    rw [S.cst_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hel i (Finset.mem_range.mp hi), S.cst_mul]; ring
  rw [hsum, hE, S.four_repr] at h4
  refine ⟨a, a.2, es, ?_, ?_⟩
  · simp only [es, map_sum]
    exact Finset.sum_eq_zero fun i hi ↦ by
      rw [Derivation.leibniz, hdc i (Finset.mem_range.mp hi), he i (Finset.mem_range.mp hi)]
      simp
  have hL := congrArg Subtype.val h4
  simp only [IntermediateField.coe_mul, IntermediateField.coe_add, coe_dTW,
    IntermediateField.coe_pow] at hL
  have hn0 : ((S.n : C⟮S.x⟯⟮S.y⟯) : L) = (S.n : L) := by simp
  rw [hn0] at hL
  have hnL : (S.n : L) ≠ 0 := by exact_mod_cast S.hn.ne'
  rw [Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero, smul_eq_mul] at hL
  have hy : ((AdjoinSimple.gen C⟮S.x⟯ S.y : C⟮S.x⟯⟮S.y⟯) : L) = S.y := rfl
  simp only [IntermediateField.algebraMap_apply, hy] at hL
  apply mul_left_cancel₀ hnL
  have e1 : ((algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨b, hb⟩ : C⟮S.x⟯⟮S.y⟯) : L) = b := rfl
  have e2 : ((algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a : C⟮S.x⟯⟮S.y⟯) : L) = (a : L) := rfl
  have e3 : ((algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (E j) : C⟮S.x⟯⟮S.y⟯) : L) = (E j : L) := rfl
  have e4 : ((S.cst es : C⟮S.x⟯⟮S.y⟯) : L) = algebraMap C L es := rfl
  rw [e1, e2, e3, e4] at hL
  linear_combination hL

end Main

end SuperData

end Differential
