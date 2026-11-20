import RischTragerBronstein.Mixed.NKLog
import RischTragerBronstein.Mixed.KLDecide

/-!
# The logarithmic part over a general curve with a single place at infinity

**`nk_liouville`**: `S : CurveData C L` with `x′ = ω(x)`, every finite place good, a single place at
infinity (weighted-degree shape), `C` containing all the constants of `L`. If
`f = v′ + ∑ cᵢ uᵢ′/uᵢ` with `f` regular at every finite place and everything in `C(x, y)`, then
`f = v′ + ℓ` with `ℓ ∈ C`.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

namespace Curves

section Reg

variable {K : Type*} [Field K]

lemma lowerBd_of_order_nk {z : LaurentSeries K} (h : 0 ≤ z.order) : LowerBd z 0 :=
  fun k hk ↦ HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hk h)

lemma order_nonneg_of_lowerBd_nk (z : LaurentSeries K) (hz : LowerBd z 0) : 0 ≤ z.order := by
  by_cases h0 : z = 0
  · rw [h0, HahnSeries.order_zero]
  by_contra hneg
  push Not at hneg
  exact HahnSeries.coeff_order_eq_zero.not.mpr h0 (hz _ hneg)

/-- **Roots of monic polynomials with power-series coefficients are power series.** -/
lemma lowerBd_root (P : (LaurentSeries K)[X]) (hP : P.Monic) (hc : ∀ i, LowerBd (P.coeff i) 0)
    (Y : LaurentSeries K) (hY : P.eval Y = 0) : LowerBd Y 0 := by
  classical
  by_contra hne
  have hY0 : Y ≠ 0 := fun h ↦ hne (h ▸ lowerBd_zero 0)
  have hv : Y.order < 0 := by
    by_contra h
    exact hne (lowerBd_of_order_nk (not_lt.mp h))
  set n := P.natDegree with hn
  rw [eval_eq_sum_range] at hY
  have hlead : P.coeff n = 1 := hP.leadingCoeff
  refine sum_ne_zero_of_unique_min (Finset.range (n + 1)) (fun i ↦ P.coeff i * Y ^ i) n
    (by simp) (by simp only [hlead, one_mul]; exact pow_ne_zero _ hY0) (fun i hi hin ↦ ?_) hY
  have hi' : i < n := by have := Finset.mem_range.mp hi; omega
  by_cases hci : P.coeff i = 0
  · left; simp only [hci, zero_mul]
  · right
    simp only [hlead, one_mul]
    rw [HahnSeries.order_mul hci (pow_ne_zero _ hY0), HahnSeries.order_pow, HahnSeries.order_pow,
      nsmul_eq_mul, nsmul_eq_mul]
    have h1 := order_nonneg_of_lowerBd_nk (P.coeff i) (hc i)
    have h2 : (i : ℤ) < n := by exact_mod_cast hi'
    nlinarith

end Reg

section PolyF

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- `Yⁿ + ∑_{i<n} pᵢ Yⁱ`. -/
noncomputable def polyF (p : ℕ → R) (n : ℕ) : R[X] :=
  X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (p i) * X ^ i

lemma polyF_degree_lt (p : ℕ → R) (n : ℕ) :
    (∑ i ∈ Finset.range n, Polynomial.C (p i) * X ^ i).degree < (n : WithBot ℕ) := by
  refine (degree_sum_le _ _).trans_lt ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun i hi ↦ ?_
  exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast Finset.mem_range.mp hi)

lemma polyF_monic (p : ℕ → R) (n : ℕ) : (polyF p n).Monic :=
  monic_X_pow_add (polyF_degree_lt p n)

lemma polyF_natDegree (p : ℕ → R) (n : ℕ) : (polyF p n).natDegree = n := by
  unfold polyF
  rw [natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact polyF_degree_lt p n),
    natDegree_X_pow]

lemma polyF_coeff (p : ℕ → R) (n i : ℕ) (hi : i < n) : (polyF p n).coeff i = p i := by
  classical
  unfold polyF
  rw [Polynomial.coeff_add, coeff_X_pow, if_neg hi.ne, zero_add, finsetSum_coeff,
    Finset.sum_eq_single i (fun b _ hb ↦ by rw [coeff_C_mul_X_pow, if_neg (Ne.symm hb)])
      (fun h ↦ absurd (Finset.mem_range.mpr hi) h), coeff_C_mul_X_pow, if_pos rfl]

lemma polyF_eval_map {S : Type*} [CommRing S] (φ : R →+* S) (p : ℕ → R) (n : ℕ) (y : S) :
    ((polyF p n).map φ).eval y = y ^ n + ∑ i ∈ Finset.range n, φ (p i) * y ^ i := by
  simp [polyF, Polynomial.map_add, Polynomial.map_sum, eval_finsetSum]

end PolyF

section Coords

open Differential

variable {C L K : Type*} [Field C] [Field L] [Algebra C L] [Field K] [Algebra C K]

namespace CurveData

variable (S : CurveData C L)

/-- **The curve of a single place at infinity** (irreducibility from the weights). -/
noncomputable def ofWeights [CharZero C] (x y : L) (htr : Transcendental C x) (F : C[X][X])
    (hF : F.Monic) (n d : ℕ) (hn : F.natDegree = n) (hn0 : 0 < n) (ha0 : F.coeff 0 ≠ 0)
    (hd : (F.coeff 0).natDegree = d)
    (hw : ∀ i, 0 < i → i < n → F.coeff i = 0 ∨ n * (F.coeff i).natDegree < d * (n - i))
    (hcop : Nat.Coprime n d) (hroot : (F.map (aeval x).toRingHom).eval y = 0) : CurveData C L :=
  ⟨x, y, F, htr, hF, fun G hG hGy ↦ irr_of_weights x y htr F hF n d hn hn0 ha0 hd hw hcop hroot G
    (hn ▸ hG) hGy, hroot⟩

/-- **Polynomial functions are regular at every finite place.** -/
lemma regularFinite_evT (Q : C[X][X]) : S.RegularFinite K (S.evT Q) := by
  intro a N hN l hl r hr
  rw [S.embG_evT]
  have hbs : ∀ P : C[X], LowerBd (branchSub (K := K) N a P) 0 := fun P ↦ by
    by_cases hP : P = 0
    · rw [hP, map_zero]; exact lowerBd_zero 0
    · refine lowerBd_of_order_nk ?_
      rw [order_branchSub N (Nat.pos_of_ne_zero hN) a P hP]; positivity
  have hY : LowerBd r 0 := lowerBd_root _ (S.monic.map _) (fun i ↦ by rw [coeff_map]; exact hbs _) r
    (S.root_of_mem hl hr)
  apply order_nonneg_of_lowerBd_nk
  rw [eval_eq_sum_range]
  refine lowerBd_sum _ _ fun i _ ↦ ?_
  rw [coeff_map]
  simpa using (hbs _).mul (hY.pow i)

/-- **Coordinates over `C(x)` are unique.** -/
theorem coords_uniqueG (c : ℕ → L) (hc : ∀ i < S.F.natDegree, c i ∈ C⟮S.x⟯)
    (h : ∑ i ∈ Finset.range S.F.natDegree, c i * S.y ^ i = 0) :
    ∀ i < S.F.natDegree, c i = 0 := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  set n := S.F.natDegree with hn
  set Q : C⟮S.x⟯[X] := ∑ i : Fin n, monomial (i : ℕ) (⟨c i, hc i i.2⟩ : C⟮S.x⟯) with hQdef
  have hQ : aeval S.y Q = 0 := by
    rw [← h, hQdef, map_sum, ← Fin.sum_univ_eq_sum_range (fun i ↦ c i * S.y ^ i)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [aeval_monomial, IntermediateField.algebraMap_apply]
  have hcoeff : ∀ i : Fin n, Q.coeff i = ⟨c i, hc i i.2⟩ := fun i ↦ by
    rw [hQdef, finsetSum_coeff, Finset.sum_eq_single i (fun b _ hb ↦ by
      rw [coeff_monomial, if_neg (fun h ↦ hb (Fin.ext h))]) (fun h ↦ absurd (Finset.mem_univ i) h),
      coeff_monomial, if_pos rfl]
  have hQ0 : Q = 0 := by
    by_contra hQ0
    have h1 := minpoly.degree_le_of_ne_zero C⟮S.x⟯ S.y hQ0 hQ
    rw [degree_eq_natDegree (minpoly.ne_zero S.isIntegral), S.natDegree_minpoly] at h1
    have h2 : Q.degree < n := by
      refine (degree_sum_le _ _).trans_lt ?_
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun i _ ↦ ?_
      exact (degree_monomial_le _ _).trans_lt (by exact_mod_cast i.2)
    exact absurd (h1.trans_lt h2) (lt_irrefl _)
  intro i hi
  have := hcoeff ⟨i, hi⟩
  rw [hQ0, Polynomial.coeff_zero] at this
  exact (congrArg Subtype.val this).symm

/-- **Coordinates exist** in the basis `1, y, …, yⁿ⁻¹` over `C(x)`. -/
lemma exists_coords (z : L) (hz : z ∈ C⟮S.x⟯⟮S.y⟯) :
    ∃ V : ℕ → L, (∀ i, V i ∈ C⟮S.x⟯) ∧ z = ∑ i ∈ Finset.range S.F.natDegree, V i * S.y ^ i := by
  classical
  set n := S.F.natDegree with hn
  set V : ℕ → L := fun i ↦ if h : i < n then ((S.coords ⟨z, hz⟩ ⟨i, h⟩ : C⟮S.x⟯) : L) else 0
    with hVdef
  refine ⟨V, fun i ↦ ?_, ?_⟩
  · simp only [hVdef]; split_ifs
    · exact SetLike.coe_mem _
    · exact zero_mem _
  · have h := congrArg Subtype.val (S.coords_spec ⟨z, hz⟩)
    rw [AddSubmonoidClass.coe_finsetSum] at h
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦ V i * S.y ^ i)]
    refine h.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    simp only [hVdef, IntermediateField.coe_mul, IntermediateField.coe_pow,
      AdjoinSimple.coe_gen]
    rw [dif_pos i.2]
    rfl

/-- **The trace functional** `τ(∑ Vᵢ yⁱ) = ∑ Vᵢ sᵢ`, `s₀ = n`, commuting with the derivation
(`(yⁱ)′ = ∑ⱼ cᵢⱼ yʲ` with `∑ⱼ cᵢⱼ sⱼ = sᵢ′`): if `f = v′ + ℓ` with `ℓ ∈ C(x)`, then
`τ(f)/n = w′ + ℓ` for some `w ∈ C(x)`. -/
theorem trace_split [Differential L] [CharZero L] (s : ℕ → L)
    (hs : ∀ i, s i ∈ C⟮S.x⟯) (hs0 : s 0 = S.F.natDegree)
    (hτ : ∀ i < S.F.natDegree, ∃ c : ℕ → L, (∀ j, c j ∈ C⟮S.x⟯) ∧
      (S.y ^ i)′ = ∑ j ∈ Finset.range S.F.natDegree, c j * S.y ^ j ∧
      ∑ j ∈ Finset.range S.F.natDegree, c j * s j = (s i)′)
    (hdx : ∀ z ∈ C⟮S.x⟯, z′ ∈ C⟮S.x⟯)
    (fc : ℕ → L) (hfc : ∀ j, fc j ∈ C⟮S.x⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯) (ℓ : L)
    (hℓ : ℓ ∈ C⟮S.x⟯)
    (heq : ∑ j ∈ Finset.range S.F.natDegree, fc j * S.y ^ j = v′ + ℓ) :
    ∃ w ∈ C⟮S.x⟯, (∑ j ∈ Finset.range S.F.natDegree, fc j * s j) / S.F.natDegree = w′ + ℓ := by
  classical
  set n := S.F.natDegree with hn
  choose! c hcm hcd hcs using hτ
  -- the coordinates of `v`
  set V : ℕ → L := fun i ↦ if h : i < n then ((S.coords ⟨v, hv⟩ ⟨i, h⟩ : C⟮S.x⟯) : L) else 0
    with hVdef
  have hVm : ∀ i, V i ∈ C⟮S.x⟯ := fun i ↦ by
    simp only [hVdef]; split_ifs
    · exact SetLike.coe_mem _
    · exact zero_mem _
  have hvV : v = ∑ i ∈ Finset.range n, V i * S.y ^ i := by
    have h := congrArg Subtype.val (S.coords_spec ⟨v, hv⟩)
    rw [AddSubmonoidClass.coe_finsetSum] at h
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦ V i * S.y ^ i)]
    refine h.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    simp only [hVdef, IntermediateField.coe_mul, IntermediateField.coe_pow,
      AdjoinSimple.coe_gen]
    rw [dif_pos i.2]
    rfl
  -- `v′` in coordinates
  have hv' : v′ = ∑ j ∈ Finset.range n, ((V j)′ + ∑ i ∈ Finset.range n, V i * c i j) * S.y ^ j := by
    rw [hvV, map_sum]
    simp only [Derivation.leibniz, smul_eq_mul, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    · rw [Finset.sum_congr rfl fun i hi ↦ by rw [hcd i (Finset.mem_range.mp hi), Finset.mul_sum],
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
  -- comparing coordinates
  have hn0 : 0 < n := Nat.pos_of_ne_zero S.natDegree_F_ne_zero
  have hcoef : ∀ j < n, fc j = (V j)′ + ∑ i ∈ Finset.range n, V i * c i j + if j = 0 then ℓ else 0 := by
    have hz : ∑ j ∈ Finset.range n, (fc j - ((V j)′ + ∑ i ∈ Finset.range n, V i * c i j +
        if j = 0 then ℓ else 0)) * S.y ^ j = 0 := by
      simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_range, hn0, if_true, pow_zero, mul_one]
      rw [heq, hv']
      simp only [add_mul, Finset.sum_add_distrib]
      ring
    have := S.coords_uniqueG _ (fun i _ ↦ sub_mem (hfc i) (add_mem (add_mem (hdx _ (hVm i))
      (sum_mem fun k hk ↦ mul_mem (hVm k) (hcm k (Finset.mem_range.mp hk) i))) (by split_ifs; exacts [hℓ, zero_mem _]))) hz
    exact fun j hj ↦ sub_eq_zero.mp (this j hj)
  -- the trace
  have hnL : (n : L) ≠ 0 := by exact_mod_cast hn0.ne'
  refine ⟨(∑ j ∈ Finset.range n, V j * s j) / n, div_mem (sum_mem fun j _ ↦ mul_mem (hVm j) (hs j))
    (IntermediateField.natCast_mem _ _), ?_⟩
  have htr : ∑ j ∈ Finset.range n, fc j * s j = (∑ j ∈ Finset.range n, V j * s j)′ + n * ℓ := by
    rw [Finset.sum_congr rfl fun j hj ↦ by rw [hcoef j (Finset.mem_range.mp hj)]]
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_range, hn0, if_true, hs0, map_sum, Derivation.leibniz, smul_eq_mul]
    have h2 : ∑ j ∈ Finset.range n, (∑ i ∈ Finset.range n, V i * c i j) * s j =
        ∑ i ∈ Finset.range n, V i * (s i)′ := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [← hcs i (Finset.mem_range.mp hi), Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [h2]
    have h3 : ∑ j ∈ Finset.range n, (V j)′ * s j = ∑ j ∈ Finset.range n, s j * (V j)′ :=
      Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    rw [h3]
    ring
  rw [htr, add_div, mul_div_cancel_left₀ _ hnL]
  congr 1
  rw [div_eq_mul_inv, div_eq_mul_inv, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have : ((n : L)⁻¹)′ = 0 := by
    have h := congrArg (fun z : L ↦ z′) (mul_inv_cancel₀ hnL)
    simp only [Derivation.leibniz, smul_eq_mul, Derivation.map_natCast, mul_zero, add_zero,
      Derivation.map_one_eq_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hnL
  rw [this, mul_zero, zero_add, mul_comm]

end CurveData

end Coords

namespace CurveData

open Differential

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : CurveData C L) (ω : C[X]) (hx : S.x′ = aeval S.x ω)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)

include hx hK in
/-- **A Liouville form has its logarithmic part in the base.** -/
theorem nk_liouville (hnd : ∀ a : K, a′ ≠ (ω.map (algebraMap C K)).eval a)
    (n dd : ℕ) (hn : S.F.natDegree = n) (hn0 : 0 < n)
    (ha0 : S.F.coeff 0 ≠ 0) (hd : (S.F.coeff 0).natDegree = dd)
    (hw' : ∀ i, 0 < i → i < n → S.F.coeff i = 0 ∨ n * (S.F.coeff i).natDegree < dd * (n - i))
    (hcop : Nat.Coprime n dd)
    (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (f : L) (hf : f ∈ C⟮S.x⟯⟮S.y⟯) (hreg : S.RegularFinite K ⟨f, hf⟩)
    {ι : Type*} (s : Finset ι) (c u : ι → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ ℓ : C, f = v′ + algebraMap C L ℓ := by
  classical
  obtain ⟨k, d, w, ⟨hd', hw, hind⟩, hsum⟩ :=
    logSum_qindep (C⟮S.x⟯⟮S.y⟯).toSubfield s c u hc (fun i hi ↦ hu i hi)
  set d' : ℕ → C := fun jj ↦ if h : jj < k then Classical.choose (hconstC (d jj) (hd' jj h)) else 0
    with hd'def
  have hdd : ∀ jj < k, algebraMap C L (d' jj) = d jj := fun jj hjj ↦ by
    simp only [hd'def, dif_pos hjj]
    exact Classical.choose_spec (hconstC (d jj) (hd' jj hjj))
  have hind' : ∀ q : ℕ → ℚ, ∑ jj ∈ Finset.range k, (q jj : C) * d' jj = 0 →
      ∀ jj < k, q jj = 0 := by
    intro q hq
    apply hind q
    rw [← map_zero (algebraMap C L), ← hq, map_sum]
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [map_mul, map_ratCast, hdd jj (Finset.mem_range.mp hjj)]
  have hww : ∀ jj < k, w jj ∈ C⟮S.x⟯⟮S.y⟯ ∧ w jj ≠ 0 := fun jj hjj ↦ ⟨(hw jj hjj).2, (hw jj hjj).1⟩
  have heq' : f = v′ + ∑ jj ∈ Finset.range k, algebraMap C L (d' jj) * ((w jj)′ / w jj) := by
    rw [heq, hsum]
    congr 1
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [hdd jj (Finset.mem_range.mp hjj), logDeriv]
  have hbase := S.logs_in_base_inf ω hx hK hnd n dd hn hn0 ha0 hd hw' hcop k d' w hww hind' v f
    hv hf heq' hreg
  choose! e he using hbase
  refine ⟨∑ jj ∈ Finset.range k, d' jj * logDeriv (e jj), ?_⟩
  rw [heq', map_sum]
  congr 1
  refine Finset.sum_congr rfl fun jj hjj ↦ ?_
  rw [he jj (Finset.mem_range.mp hjj), map_mul, ← logDeriv, logDeriv_algebraMap]

end CurveData

end Curves

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Differential

section Codes

variable {α : Type} (O : COps α)

/-- The sum of a list of codes. -/
def lsumC (l : List α) : α := l.foldr O.add O.zero

lemma sem_lsumC {K : Type*} [Field K] [Differential K] (M : CField α K O) (l : List α) :
    M.sem (lsumC O l) = (l.map M.sem).sum := by
  induction l with
  | nil => exact M.sem_zero
  | cons a l ih => simp only [lsumC, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢; rw [M.sem_add, ih]

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m)

/-- The code `(a, 1)` of a polynomial at level `m + 1`. -/
def polyCode (m : ℕ) (a : GPoly (LC m)) : LC (m + 1) := (a, [(MO Fc ks m).one])

/-- The code of `Yⁿ + ∑_{i<n} aᵢ(t) Yⁱ` at level `m + 1` (`n` = the length of the list). -/
def nkPC (m : ℕ) (Pp : List (GPoly (LC m))) : GPoly (LC (m + 1)) :=
  Pp.map (polyCode Fc ks m) ++ [(MOr Fc ks (m + 1)).one]

/-- **The shape of a single place at infinity**: `deg a₀ = d > 0`, `gcd(n, d) = 1`,
`n deg aᵢ < d (n − i)`. -/
def nkShape (m : ℕ) (Pp : List (GPoly (LC m))) : Bool :=
  let n := Pp.length
  let d := degG (MO Fc ks m) (Pp.getD 0 [])
  decide (0 < n) && decide (0 < d) && Nat.gcd n d == 1 &&
    (List.range n).all fun i ↦ i == 0 || decide (n * degG (MO Fc ks m) (Pp.getD i []) < d * (n - i))

/-- **The trace check**: `s₀ = n` and `∑ⱼ Mᵢⱼ sⱼ = sᵢ′` (`(θⁱ)′ = ∑ⱼ Mᵢⱼ θʲ`). -/
def traceC (m : ℕ) (P : GPoly (LC (m + 1))) (s : List (LC (m + 1))) : Bool :=
  let O1 := MOr Fc ks (m + 1)
  let N := P.length - 1
  match dThetaC O1 P with
  | none => false
  | some dθ =>
    O1.isZero (O1.add (s.getD 0 O1.zero) (O1.neg (O1.natCast N))) &&
    (List.range N).all fun i ↦ O1.isZero (O1.add (lsumC O1 ((List.range N).map fun j ↦
      O1.mul ((dPowC O1 P dθ i).getD j O1.zero) (s.getD j O1.zero)))
      (O1.neg (O1.deriv (s.getD i O1.zero))))

/-- The polynomial codes `(bⱼ, 1)` of the coordinates. -/
def nkFl (m : ℕ) (fp : List (GPoly (LC m))) : List (LC (m + 1)) :=
  fp.map (polyCode Fc ks m)

/-- `τ(f)/n = (∑ⱼ fⱼ sⱼ)/n`. -/
def nkTau (m n : ℕ) (fl s : List (LC (m + 1))) : LC (m + 1) :=
  let O1 := MOr Fc ks (m + 1)
  O1.mul (lsumC O1 ((List.range n).map fun j ↦ O1.mul (fl.getD j O1.zero) (s.getD j O1.zero)))
    (O1.inv (O1.natCast n))

/-- The coordinates of `f − τ(f)/n`. -/
def nkRest (m : ℕ) (fl : List (LC (m + 1))) (q : LC (m + 1)) : List (LC (m + 1)) :=
  let O1 := MOr Fc ks (m + 1)
  O1.add (fl.getD 0 O1.zero) (O1.neg q) :: fl.tail

end Codes

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

lemma evP_nil (m : ℕ) : T.evP m [] = 0 := by simp [evP, evPL]

/-- The coordinates `(bⱼ, 1)`. -/
lemma sem_nkFl (m : ℕ) (h1 : T.Tr (m + 1)) (fp : List (GPoly (LC m))) (j : ℕ) :
    (((T.MPr (m + 1) h1).sem ((nkFl Fc ks m fp).getD j (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) :
      L) = T.evP m (fp.getD j []) := by
  rw [MPr_sem]
  have hl : (nkFl Fc ks m fp).length = fp.length := List.length_map _
  by_cases hj : j < fp.length
  · rw [List.getD_eq_getElem _ _ (by rw [hl]; exact hj)]
    simp only [nkFl, List.getElem_map]
    rw [List.getD_eq_getElem _ _ hj]
    exact T.sem_poly_code m h1 _
  · rw [List.getD_eq_default _ _ (by rw [hl]; omega), List.getD_eq_default _ _ (by omega),
      evP_nil]
    have := (T.MPr (m + 1) h1).sem_zero
    rw [MPr_sem] at this
    rw [this]; rfl

lemma sem_nkTau (m n : ℕ) (h1 : T.Tr (m + 1)) (fl s : List (LC (m + 1))) :
    (T.MPr (m + 1) h1).sem (nkTau Fc ks m n fl s) =
      (∑ j ∈ Finset.range n, (T.MPr (m + 1) h1).sem (fl.getD j (MOr Fc ks (m + 1)).zero) *
        (T.MPr (m + 1) h1).sem (s.getD j (MOr Fc ks (m + 1)).zero)) * (n : T.F (m + 1))⁻¹ := by
  set M := T.MPr (m + 1) h1
  simp only [nkTau]
  rw [M.sem_mul, sem_lsumC, M.sem_inv, M.sem_natCast, List.map_map]
  congr 1
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  · exact Finset.sum_congr rfl fun j _ ↦ M.sem_mul _ _

lemma sem_nkRest (m : ℕ) (h1 : T.Tr (m + 1)) (fl : List (LC (m + 1))) (q : LC (m + 1)) (j : ℕ) :
    (T.MPr (m + 1) h1).sem ((nkRest Fc ks m fl q).getD j (MOr Fc ks (m + 1)).zero) =
      (T.MPr (m + 1) h1).sem (fl.getD j (MOr Fc ks (m + 1)).zero) -
        if j = 0 then (T.MPr (m + 1) h1).sem q else 0 := by
  set M := T.MPr (m + 1) h1
  rcases j with _ | j
  · rw [if_pos rfl]
    simp only [nkRest, List.getD_cons_zero]
    rw [M.sem_add, M.sem_neg, sub_eq_add_neg]
  · simp only [nkRest, List.getD_cons_succ, if_neg (Nat.succ_ne_zero j), sub_zero]
    congr 1
    rcases fl with _ | ⟨a, fl⟩
    · rfl
    · rfl

/-- The polynomial of `nkPC`. -/
lemma toPoly_nkPC (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m))) :
    GPoly.toPoly (T.MPr (m + 1) h1) (nkPC Fc ks m Pp) =
      polyF (fun i ↦ (T.MPr (m + 1) h1).sem (polyCode Fc ks m (Pp.getD i []))) Pp.length := by
  set M := T.MPr (m + 1) h1
  have hl : (Pp.map (polyCode Fc ks m)).length = Pp.length := List.length_map _
  have hl2 : (nkPC Fc ks m Pp).length = Pp.length + 1 := by
    rw [nkPC, List.length_append, hl]; rfl
  refine Polynomial.ext fun i ↦ ?_
  rw [coeff_toPoly_sem]
  rcases lt_trichotomy i Pp.length with hi | rfl | hi
  · rw [polyF_coeff _ _ _ hi, nkPC, List.getD_append _ _ _ _ (by rw [hl]; exact hi),
      List.getD_eq_getElem _ _ (by rw [hl]; exact hi), List.getElem_map,
      List.getD_eq_getElem _ _ hi]
  · rw [nkPC, List.getD_append_right _ _ _ _ (by rw [hl]), hl, Nat.sub_self,
      List.getD_cons_zero, M.sem_one]
    have h := polyF_monic (fun i ↦ M.sem (polyCode Fc ks m (Pp.getD i []))) Pp.length
    rw [Monic, Polynomial.leadingCoeff, polyF_natDegree] at h
    exact h.symm
  · rw [List.getD_eq_default _ _ (by rw [hl2]; omega), M.sem_zero,
      coeff_eq_zero_of_natDegree_lt (by rw [polyF_natDegree]; exact hi)]

lemma length_nkPC (m : ℕ) (Pp : List (GPoly (LC m))) :
    (nkPC Fc ks m Pp).length - 1 = Pp.length := by
  have hl : (Pp.map (polyCode Fc ks m)).length = Pp.length := List.length_map _
  rw [nkPC, List.length_append, hl]; rfl

/-- **The trace check is sound**: `s₀ = n` and `∑ⱼ Mᵢⱼ sⱼ = sᵢ′` for the coefficients of
`(θⁱ)′ = ∑ⱼ Mᵢⱼ θʲ`. -/
lemma traceC_sound (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m))) (θ : L)
    (hP : T.evθ m h1 θ (nkPC Fc ks m Pp) = 0) (s : List (LC (m + 1)))
    (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true) :
    (T.MPr (m + 1) h1).sem (s.getD 0 (MOr Fc ks (m + 1)).zero) = (Pp.length : T.F (m + 1)) ∧
    ∀ i < Pp.length, ∃ c : ℕ → T.F (m + 1),
      (θ ^ i)′ = ∑ j ∈ Finset.range Pp.length, (c j : L) * θ ^ j ∧
      ∑ j ∈ Finset.range Pp.length, c j * (T.MPr (m + 1) h1).sem (s.getD j (MOr Fc ks (m + 1)).zero) =
        ((T.MPr (m + 1) h1).sem (s.getD i (MOr Fc ks (m + 1)).zero))′ := by
  set M := T.MPr (m + 1) h1 with hM
  set O1 := MOr Fc ks (m + 1) with hO1
  have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
  have hPm : (GPoly.toPoly M (nkPC Fc ks m Pp)).Monic := by
    rw [T.toPoly_nkPC m h1 Pp]; exact polyF_monic _ _
  have hPd : (GPoly.toPoly M (nkPC Fc ks m Pp)).natDegree = Pp.length := by
    rw [T.toPoly_nkPC m h1 Pp]; exact polyF_natDegree _ _
  unfold traceC at hs
  simp only at hs
  split at hs
  · exact absurd hs (by simp)
  rename_i dθ hd
  rw [Bool.and_eq_true, List.all_eq_true] at hs
  obtain ⟨h0, hall⟩ := hs
  rw [hlen] at h0 hall
  refine ⟨?_, fun i hi ↦ ⟨T.Mθ m h1 (nkPC Fc ks m Pp) dθ i, ?_, ?_⟩⟩
  · have := (M.isZero_iff _).mp h0
    rw [M.sem_add, M.sem_neg, M.sem_natCast, add_neg_eq_zero] at this
    exact this
  · rw [T.deriv_θ_pow_sum m h1 θ (nkPC Fc ks m Pp) hP hPm dθ hd i, hPd]
  · have := (M.isZero_iff _).mp (hall i (List.mem_range.mpr hi))
    rw [M.sem_add, M.sem_neg, M.sem_deriv, sem_lsumC, List.map_map, add_neg_eq_zero,
      ← List.sum_toFinset _ List.nodup_range, List.toFinset_range] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [Function.comp_apply, M.sem_mul]; rfl

/-- **The shape facts** for `F = Yⁿ + ∑ aᵢ(t) Yⁱ` over `Fₘ`. -/
lemma nkShape_spec (m : ℕ) (h0 : T.Tr m) (Pp : List (GPoly (LC m)))
    (hsh : nkShape Fc ks m Pp = true) :
    let F := polyF (fun i ↦ GPoly.toPoly (T.MP m h0) (Pp.getD i [])) Pp.length
    let d := degG (MO Fc ks m) (Pp.getD 0 [])
    0 < Pp.length ∧ F.coeff 0 ≠ 0 ∧ (F.coeff 0).natDegree = d ∧
      (∀ i, 0 < i → i < Pp.length → F.coeff i = 0 ∨
        Pp.length * (F.coeff i).natDegree < d * (Pp.length - i)) ∧ Nat.Coprime Pp.length d := by
  intro F d
  unfold nkShape at hsh
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at hsh
  obtain ⟨⟨⟨hn0, hd0⟩, hcop⟩, hw⟩ := hsh
  have hdeg : ∀ i, degG (MO Fc ks m) (Pp.getD i []) =
      (GPoly.toPoly (T.MP m h0) (Pp.getD i [])).natDegree := fun i ↦ degG_eq (T.MP m h0) _
  have hc0 : F.coeff 0 = GPoly.toPoly (T.MP m h0) (Pp.getD 0 []) := polyF_coeff _ _ _ hn0
  refine ⟨hn0, ?_, ?_, fun i hi hin ↦ Or.inr ?_, hcop⟩
  · rw [hc0]
    intro h
    have := hdeg 0
    rw [h, natDegree_zero] at this
    exact absurd this (by omega)
  · rw [hc0, ← hdeg 0]
  · rw [polyF_coeff _ _ _ hin, ← hdeg i]
    rcases hw i hin with h | h
    · omega
    · exact h

/-- `P(θ)` for the code `nkPC`. -/
lemma evθ_nkPC (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m))) (θ : L) :
    T.evθ m h1 θ (nkPC Fc ks m Pp) =
      θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i := by
  rw [evθ, T.toPoly_nkPC m h1 Pp, aeval_def, ← eval_map, polyF_eval_map]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  exact T.sem_poly_code m h1 _

/-- The polynomial `F = Yⁿ + ∑ aᵢ(x) Yⁱ` over `Fₘ`. -/
noncomputable def nkF (m : ℕ) (h0 : T.Tr m) (Pp : List (GPoly (LC m))) : (T.F m)[X][X] :=
  polyF (fun i ↦ GPoly.toPoly (T.MP m h0) (Pp.getD i [])) Pp.length

lemma nkF_root (m : ℕ) (h0 : T.Tr m) (Pp : List (GPoly (LC m))) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0) :
    ((T.nkF m h0 Pp).map (aeval (T.ts m)).toRingHom).eval θ = 0 := by
  rw [nkF, polyF_eval_map, ← hθ]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  exact T.aeval_toPoly (T.MP m h0) (T.sem_MP m h0) _

/-- **The curve** `F(tₘ, θ) = 0` over `Fₘ` (single place at infinity). -/
noncomputable def nkCurve (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m)))
    (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0) :
    CurveData (T.F m) L :=
  have hsp := T.nkShape_spec m h1.of_succ Pp hsh
  CurveData.ofWeights (T.ts m) θ (h1 m (by omega)) (T.nkF m h1.of_succ Pp) (polyF_monic _ _)
    Pp.length _ (polyF_natDegree _ _) hsp.1 hsp.2.1 hsp.2.2.1 hsp.2.2.2.1 hsp.2.2.2.2
    (T.nkF_root m h1.of_succ Pp θ hθ)

/-- **The powers `1, θ, …, θⁿ⁻¹` are independent over `Fₘ₊₁`.** -/
lemma nkCurve_ind (m : ℕ) (h1 : T.Tr (m + 1)) (Pp : List (GPoly (LC m)))
    (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (a : ℕ → T.F (m + 1)) (ha : ∑ j ∈ Finset.range Pp.length, (a j : L) * θ ^ j = 0) :
    ∀ j < Pp.length, a j = 0 := by
  set S := T.nkCurve m h1 Pp hsh θ hθ
  have hdeg : S.F.natDegree = Pp.length := polyF_natDegree _ _
  intro j hj
  have := S.coords_uniqueG (fun j ↦ (a j : L)) (fun i _ ↦ (T.mem_F_succ).mp (a i).2)
    (by rw [hdeg]; exact ha) j (by rw [hdeg]; exact hj)
  exact Subtype.ext this

/-- `(τ(f)/n)` as an element of `L`. -/
lemma coe_sem_MPr (m : ℕ) (h1 : T.Tr m) (q : LC m) :
    (((T.MPr m h1).sem q : T.F m) : L) = T.ev m q := by
  rw [MPr_sem, T.sem_MP]

/-- The coordinates of `f − τ(f)/n`. -/
lemma sum_nkRest (m : ℕ) (h1 : T.Tr (m + 1)) (n : ℕ) (hn : 0 < n) (fp : List (GPoly (LC m)))
    (q : LC (m + 1)) (θ : L) :
    ∑ j ∈ Finset.range n, (((T.MPr (m + 1) h1).sem ((nkRest Fc ks m (nkFl Fc ks m fp) q).getD j
      (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ j =
      ∑ j ∈ Finset.range n, T.evP m (fp.getD j []) * θ ^ j - T.ev (m + 1) q := by
  classical
  have e1 : ∀ j, (((T.MPr (m + 1) h1).sem ((nkRest Fc ks m (nkFl Fc ks m fp) q).getD j
      (MOr Fc ks (m + 1)).zero) : T.F (m + 1)) : L) * θ ^ j =
      T.evP m (fp.getD j []) * θ ^ j - (if j = 0 then T.ev (m + 1) q else 0) := fun j ↦ by
    rw [T.sem_nkRest, AddSubgroupClass.coe_sub, T.sem_nkFl]
    split_ifs with hj
    · subst hj; rw [T.coe_sem_MPr]; ring
    · simp
  rw [Finset.sum_congr rfl fun j _ ↦ e1 j, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_range.mpr hn)]

set_option maxHeartbeats 4000000 in
/-- **`⇐`**: an exact `f − τ(f)/n` and an elementary `τ(f)/n` give an elementary `f`. -/
theorem nk_sufficient (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (s : List (LC (m + 1))) (fp : List (GPoly (LC m))) (res : Bool)
    (hres : exactC Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res)
    (hr : res = true)
    (hq : HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s))) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  have MSm := T.mspecs hmon hdeg lv m (by omega) hcm
  have hn0 := (T.nkShape_spec m hTr.of_succ Pp hsh).1
  have hP : T.evθ m hTr θ (nkPC Fc ks m Pp) = 0 := by rw [T.evθ_nkPC]; exact hθ
  have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
  have hind : ∀ a : ℕ → T.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
      (a j : L) * θ ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
    rw [hlen]; exact T.nkCurve_ind m hTr Pp hsh θ hθ
  have hiff := T.exactC_correct m (by omega) hTr (hTr m (by omega)) hk (paramLimC Fc ks lv m)
    MSm.lim (nkPC Fc ks m Pp) _ θ hP hind res hres
  obtain ⟨Y, hY⟩ := hiff.mp hr
  rw [hlen, T.sum_nkRest m hTr Pp.length hn0] at hY
  rw [show ∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j =
      T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) +
        (∑ i ∈ Finset.range Pp.length, (Y i : L) * θ ^ i)′ by rw [hY]; ring]
  exact hq.add_in (hasElementaryIntegralIn_deriv _)

set_option maxHeartbeats 16000000 in
/-- **`⇒`**: an elementary `f` has an exact `f − τ(f)/n` and an elementary `τ(f)/n` (the
logarithmic part of a Liouville form lies in `Fₘ`, and `τ` is `n` on `Fₘ`). -/
theorem nk_necessary (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (res : Bool)
    (hres : exactC Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res)
    (hf : HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j)) :
    res = true ∧
      HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) := by
  classical
  set n := Pp.length with hnn
  set f := ∑ j ∈ Finset.range n, T.evP m (fp.getD j []) * θ ^ j with hfdef
  set q := nkTau Fc ks m n (nkFl Fc ks m fp) s with hq
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  obtain ⟨E₁, _, _, _, _, hE₁, g, hg⟩ := hf
  haveI : CharZero E₁ := charZero_of_injective_algebraMap (algebraMap L E₁).injective
  obtain ⟨ι, s', c, u, v, hdata, hv, heqL⟩ := liouville_strong hE₁ _ g hg
  -- the tower in `E₁`
  obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E₁
  set ψ := algebraMap L E₁ with hψ
  have MSE := TE.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTE : TE.Tr (m + 1) := MSE.hyp.tr
  have hTEm : TE.Tr m := hTE.of_succ
  have MSEm := TE.mspecs hmon hdeg lv m (by omega) hcm
  have hPE : ∀ P : GPoly (LC m), TE.evP m P = ψ (T.evP m P) := fun P ↦ by
    rw [← TE.sem_poly_code m hTE, ← T.sem_poly_code m hTr]
    exact (TE.sem_MP (m + 1) hTE _).trans ((hTEev (m + 1) _).trans
      (congrArg ψ (T.sem_MP (m + 1) hTr _).symm))
  have hθE : (ψ θ) ^ n + ∑ i ∈ Finset.range n, TE.evP m (Pp.getD i []) * (ψ θ) ^ i = 0 := by
    simp only [hPE, ← map_pow, ← map_mul, ← map_sum, ← map_add, hθ, map_zero]
  -- the curve over `C₁ = Fₘ` of the lifted tower
  set S₁ := TE.nkCurve m hTE Pp hsh (ψ θ) hθE with hS₁
  have hsp := TE.nkShape_spec m hTEm Pp hsh
  have hS₁F : S₁.F.natDegree = n := polyF_natDegree _ _
  set η₁ : TE.F m := TE.val m η with hη₁
  have hx : S₁.x′ = aeval S₁.x (Polynomial.C η₁) := by
    rw [aeval_C]
    change (TE.ts m)′ = _
    rw [TE.ht m (by omega), hk]
    rfl
  have hnd : ∀ α : AlgebraicClosure (TE.F m),
      α′ ≠ ((Polynomial.C η₁).map (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)))).eval α :=
    fun α ↦ by
      rw [Polynomial.map_C, eval_C]
      exact not_deriv_of_integral η₁ (fun z hz ↦ MSE.hyp.nd m (by omega) η hk z hz) α
        (Algebra.IsIntegral.isIntegral α)
  have hK : ∀ c : TE.F m, (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c)′ =
      algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c′ := fun c ↦ deriv_algebraMap c
  have hconstC : ∀ z : E₁, z′ = 0 → z ∈ Set.range (algebraMap (TE.F m) E₁) := fun z hz ↦ by
    obtain ⟨c0, hc0⟩ := TE.hconst z hz
    exact ⟨⟨z, hc0 ▸ TE.const_mem m c0⟩, rfl⟩
  set T₁ := (TE.F m)⟮S₁.x⟯⟮S₁.y⟯ with hT₁
  have hxT : ∀ w ∈ TE.F (m + 1), w ∈ T₁ := fun w hw ↦
    IntermediateField.algebraMap_mem T₁ (⟨w, (TE.mem_F_succ).mp hw⟩ : (TE.F m)⟮S₁.x⟯)
  have hLT : ∀ z : L, ψ z ∈ T₁ := by
    intro z
    have hz := hgen z
    induction hz using IntermediateField.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact mem_adjoin_simple_self _ _
    | algebraMap w => exact hxT _ (hTEmem (m + 1) _ w.2)
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => rw [map_mul]; exact mul_mem h₁ h₂
    | inv w _ h₁ => rw [map_inv₀]; exact inv_mem h₁
  have hCT : ∀ w ∈ Differential.constField L E₁, w ∈ T₁ := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem w hw =>
      obtain ⟨c0, hc0⟩ := hconstC w hw
      rw [← hc0]
      exact S₁.const_mem c0
    | algebraMap z => exact hLT z
    | add w₁ w₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂
    | inv w _ h₁ => exact inv_mem h₁
  -- the integrand is a polynomial in `x, y`
  have hψf : ψ f = ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) * (ψ θ) ^ j := by
    simp only [hfdef, map_sum, map_mul, map_pow, hPE]
  set Q : (TE.F m)[X][X] := ∑ j ∈ Finset.range n,
    Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (fp.getD j [])) * X ^ j with hQ
  have hQv : S₁.evXY Q = ψ f := by
    rw [hψf, CurveData.evXY, hQ, Polynomial.map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eval_mul, eval_C,
      eval_pow, eval_X]
    congr 1
    exact TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm) _
  have hfT : ψ f ∈ T₁ := hLT f
  have hfQ : (⟨ψ f, hfT⟩ : T₁) = S₁.evT Q := Subtype.ext (by rw [S₁.coe_evT, hQv])
  have hreg : S₁.RegularFinite (AlgebraicClosure (TE.F m)) ⟨ψ f, hfT⟩ := by
    rw [hfQ]; exact S₁.regularFinite_evT Q
  -- the logarithmic part lies in `Fₘ`
  have heq₁ : ψ f = v′ + ∑ i ∈ s', c i * logDeriv (u i) := by rw [heqL, add_comm]
  obtain ⟨ℓ₀, hℓ₀⟩ := S₁.nk_liouville (K := AlgebraicClosure (TE.F m)) (Polynomial.C η₁) hx hK hnd
    n _ hS₁F hsp.1 hsp.2.1 hsp.2.2.1 hsp.2.2.2.1 hsp.2.2.2.2 hconstC (ψ f) hfT hreg s' c u
    (fun i hi ↦ (hdata i hi).1) (fun i hi ↦ ⟨(hdata i hi).2.2, hCT _ (hdata i hi).2.1⟩) v
    (hCT v hv) heq₁
  -- the trace
  have hPθE : TE.evθ m hTE (ψ θ) (nkPC Fc ks m Pp) = 0 := by rw [TE.evθ_nkPC]; exact hθE
  obtain ⟨hs0, hτ⟩ := TE.traceC_sound m hTE Pp (ψ θ) hPθE s hs
  set M1 := TE.MPr (m + 1) hTE with hM1
  set O1 := MOr Fc ks (m + 1) with hO1
  have hdx : ∀ z ∈ (TE.F m)⟮S₁.x⟯, z′ ∈ (TE.F m)⟮S₁.x⟯ := fun z hz ↦ by
    have := ((⟨z, (TE.mem_F_succ).mpr hz⟩ : TE.F (m + 1))′ : TE.F (m + 1)).2
    rw [MTower.coe_deriv] at this
    exact (TE.mem_F_succ).mp this
  obtain ⟨w, hw, hwe⟩ := S₁.trace_split (fun j ↦ ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁))
    (fun j ↦ (TE.mem_F_succ).mp (M1.sem (s.getD j O1.zero)).2)
    (by rw [hS₁F, hs0]; push_cast; rfl)
    (fun i hi ↦ by
      rw [hS₁F] at hi ⊢
      obtain ⟨c', hc'd, hc's⟩ := hτ i hi
      refine ⟨fun j ↦ (c' j : E₁), fun j ↦ (TE.mem_F_succ).mp (c' j).2, hc'd, ?_⟩
      have := congrArg (fun z : TE.F (m + 1) ↦ (z : E₁)) hc's
      simp only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_mul,
        MTower.coe_deriv] at this
      exact this)
    hdx (fun j ↦ TE.evP m (fp.getD j [])) (fun j ↦ (TE.mem_F_succ).mp (TE.evP_mem m (TE.ev_mem m) _))
    v (hCT v hv) (algebraMap (TE.F m) E₁ ℓ₀) (IntermediateField.algebraMap_mem _ ℓ₀)
    (by
      rw [hS₁F]
      change ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) * (ψ θ) ^ j = _
      rw [← hψf]; exact hℓ₀)
  rw [hS₁F] at hwe
  -- `ψ (τ(f)/n)`
  have hqv : ψ (T.ev (m + 1) q) = (∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) *
      ((M1.sem (s.getD j O1.zero) : TE.F (m + 1)) : E₁)) / n := by
    rw [← hTEev (m + 1) q, ← TE.coe_sem_MPr (m + 1) hTE q, hq, TE.sem_nkTau m n hTE]
    push_cast
    rw [div_eq_mul_inv]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [TE.sem_nkFl m hTE fp j]
  have hlog : algebraMap (TE.F m) E₁ ℓ₀ = ∑ i ∈ s', c i * logDeriv (u i) := by
    have := hℓ₀.symm.trans heq₁
    exact add_left_cancel this
  refine ⟨?_, ?_⟩
  · ----------------------------------------------------------------------------------------------
    -- the exact part in the lifted tower
    have hvw : v - w ∈ T₁ := sub_mem (hCT v hv) (IntermediateField.algebraMap_mem T₁
      (⟨w, hw⟩ : (TE.F m)⟮S₁.x⟯))
    obtain ⟨Y', hY'm, hY'⟩ := S₁.exists_coords (v - w) hvw
    rw [hS₁F] at hY'
    have hlen := length_nkPC (Fc := Fc) (ks := ks) m Pp
    have hind : ∀ a : ℕ → TE.F (m + 1), ∑ j ∈ Finset.range ((nkPC Fc ks m Pp).length - 1),
        (a j : E₁) * (ψ θ) ^ j = 0 → ∀ j < (nkPC Fc ks m Pp).length - 1, a j = 0 := by
      rw [hlen]; exact TE.nkCurve_ind m hTE Pp hsh (ψ θ) hθE
    have hiff := TE.exactC_correct m (by omega) hTE (hTE m (by omega)) hk (paramLimC Fc ks lv m)
      MSEm.lim (nkPC Fc ks m Pp) _ (ψ θ) hPθE hind res hres
    refine hiff.mpr ⟨fun i ↦ ⟨Y' i, (TE.mem_F_succ).mpr (hY'm i)⟩, ?_⟩
    rw [hlen, TE.sum_nkRest m hTE n hsp.1, hTEev (m + 1) q]
    change (∑ i ∈ Finset.range n, Y' i * S₁.y ^ i)′ = _
    rw [← hY', ← hψf, hqv, hwe, map_sub, hℓ₀]
    ring
  · ----------------------------------------------------------------------------------------------
    -- `τ(f)/n` has a Liouville form in `E₁`
    set l : List (E₁ × E₁) := s'.toList.map fun i ↦ (c i, u i) with hl0
    have hl : ∀ p ∈ l, p.1′ = 0 ∧ p.2 ≠ 0 := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      rw [Finset.mem_toList] at hi
      exact ⟨(hdata i hi).1, (hdata i hi).2.2⟩
    have hform := hasElementaryIntegral_of_liouville_form w l hl
    have hsumeq : w′ + (l.map fun p ↦ p.1 * logDeriv p.2).sum = ψ (T.ev (m + 1) q) := by
      rw [hqv, hwe, hlog, hl0, List.map_map, Finset.sum_map_toList]
      rfl
    rw [hsumeq] at hform
    exact HasElementaryIntegral.of_extension hE₁ hform

/-- **The logarithmic part over a non-Kummer extension of a logarithmic level**: for
`θⁿ + ∑ aᵢ(t) θⁱ = 0` with a single place at infinity and `f = ∑ bⱼ(t) θʲ`, `f` has an elementary
integral iff `f − τ(f)/n` is exact (`exactC`) and `τ(f)/n ∈ Fₘ₊₁` has one. -/
theorem nk_iff (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (res : Bool)
    (hres : exactC Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res) :
    HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
      res = true ∧
        HasElementaryIntegral (T.ev (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) :=
  ⟨T.nk_necessary hmon hdeg m hn hc hk Pp hsh θ hθ hgen s hs fp res hres,
    fun h ↦ T.nk_sufficient hmon hdeg m hn hc hk Pp hsh θ hθ s fp res hres h.1 h.2⟩

set_option maxHeartbeats 4000000 in
/-- **The decision**: `elM` decides `τ(f)/n` (at every large search bound), `exactC` the rest. -/
theorem nk_decides (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hshF : curveShape Fc = true) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (hsh : nkShape Fc ks m Pp = true) (θ : L)
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (s : List (LC (m + 1))) (hs : traceC Fc ks m (nkPC Fc ks m Pp) s = true)
    (fp : List (GPoly (LC m))) (res : Bool)
    (hres : exactC Fc ks m η (paramLimC Fc ks lv m) (nkPC Fc ks m Pp)
      (nkRest Fc ks m (nkFl Fc ks m fp) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s)) = some res) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b,
      elM Fc ks lv (m + 1) (nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s) N = some b ∧
      (HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) ↔
        res = true ∧ b = true) := by
  classical
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  set q := nkTau Fc ks m Pp.length (nkFl Fc ks m fp) s
  obtain ⟨T', hT'n, hT'ev, hT'gen, -⟩ := T.exists_sub (m + 1) (by omega)
  obtain ⟨N₀, hN₀⟩ := elM_decides_any hmon hdeg hshF T' (m + 1) hT'n hc hT'gen q
  -- `L` is algebraic over `F (m + 1)`
  have hmem : ∀ i, T.evP m (Pp.getD i []) ∈ T.F (m + 1) := fun i ↦ T.evP_mem m (T.ev_mem m) _
  have hθi : IsIntegral (T.F (m + 1)) θ := by
    refine ⟨polyF (fun i ↦ (⟨T.evP m (Pp.getD i []), hmem i⟩ : T.F (m + 1))) Pp.length,
      polyF_monic _ _, ?_⟩
    rw [← eval_map, polyF_eval_map]
    exact hθ
  have halg : Algebra.IsAlgebraic (T.F (m + 1)) L := ⟨fun z ↦ by
    have := IntermediateField.isAlgebraic_adjoin_simple hθi
    exact (IntermediateField.isAlgebraic_iff (x := (⟨z, hgen z⟩ :
      IntermediateField.adjoin (T.F (m + 1)) {θ}))).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩
  have h0 : HasElementaryIntegral (T.ev (m + 1) q) ↔ HasElementaryIntegral (T'.ev (m + 1) q) := by
    rw [← hasElementaryIntegral_isAlgebraic_iff halg]
    rw [show algebraMap (T.F (m + 1)) L (T'.ev (m + 1) q) = T.ev (m + 1) q from
      hT'ev (m + 1) le_rfl q]
  refine ⟨N₀, fun N hN ↦ ?_⟩
  obtain ⟨b, hb, hiff, -⟩ := hN₀ N hN
  refine ⟨b, hb, ?_⟩
  rw [T.nk_iff hmon hdeg m hn hc hk Pp hsh θ hθ hgen s hs fp res hres, h0, hiff]

end MTower

end Curves.MT
