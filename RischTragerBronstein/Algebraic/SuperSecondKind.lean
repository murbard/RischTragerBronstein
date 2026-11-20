import RischTragerBronstein.Algebraic.SuperDerivG
import RischTragerBronstein.Algebraic.QIndep

/-!
# Residue-free Liouville forms on a superelliptic curve are exact

* `const_of_ordAt_zero`: an element with order `0` at every finite point is a constant
  (degree theorem + the pole bound at infinity);
* `super_second_kind`: if `f = v′ + ∑ cᵢ uᵢ′/uᵢ` on `C⟮x⟯⟮y⟯` (`C` all the constants) and `f dx` has
  no residue at any finite point, then `f = v′`.
-/

open Polynomial IntermediateField HahnSeries

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]

variable (S : SuperData C L)

omit [CharZero C] [CharZero L] in
/-- **No zeros and poles at the finite points ⇒ constant.** -/
theorem const_of_ordAt_zero [PerfectField C] (K : Type*) [Field K] [Algebra C K] [IsAlgClosed K]
    (hcop : Nat.Coprime S.n S.p.natDegree) (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0)
    (h0 : ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α → S.ordAt K w α β = 0) :
    ∃ c : C, (w : L) = algebraMap C L c := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  have hint : S.IsIntegralS K w := fun α β hv ↦ (h0 α β hv).symm ▸ le_rfl
  have hdeg := S.degree_eq' K hcop w hw hint ∅ (by simp) (fun α β hv _ ↦ h0 α β hv)
  rw [Finset.sum_empty, eq_comm, neg_eq_zero] at hdeg
  obtain ⟨a, ha, hpoly⟩ := S.integral_of_regular' K w hint
  obtain ⟨lam, hlam, hlp⟩ := S.exists_lam (K := K)
  have hinf : ((0 : ℤ) : WithTop ℤ) ≤ (S.embI lam hlam hlp (∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯
      (a i) * AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ))).orderTop := by
    rw [← ha, ← HahnSeries.order_eq_orderTop_of_ne_zero ((map_ne_zero_iff _ (RingHom.injective _)).mpr
      hw), ← S.ordInf_eq hcop w lam hlam hlp, hdeg]
  have hb := S.inf_bound hcop lam hlam hlp a 0 hinf
  -- every coefficient but the constant term vanishes, and that one is a constant
  have hdp : 0 < S.p.natDegree := S.hp
  have hai : ∀ i : Fin S.n, a i ≠ 0 → (i : ℕ) = 0 ∧ ∃ c : C, (a i : L) = algebraMap C L c := by
    intro i hi
    obtain ⟨P, hP⟩ := hpoly i
    have haP : a i = algebraMap C[X] C⟮S.x⟯ P := Subtype.ext (by rw [hP, algebraMap_adjoinSimple])
    have hP0 : P ≠ 0 := fun h ↦ hi (by rw [haP, h, map_zero])
    have := hb i hi
    rw [haP, S.embXG_inf_poly P hP0] at this
    have hn := S.hn
    have h1 : (S.n : ℤ) * P.natDegree + S.p.natDegree * (i : ℕ) ≤ 0 := by linarith
    have h2 : P.natDegree = 0 := by
      by_contra h
      have : 0 < (S.n : ℤ) * P.natDegree := by positivity
      have : (0 : ℤ) ≤ S.p.natDegree * (i : ℕ) := by positivity
      linarith
    have h3 : (i : ℕ) = 0 := by
      by_contra h
      have : 0 < (S.p.natDegree : ℤ) * (i : ℕ) := by positivity
      have : (0 : ℤ) ≤ S.n * P.natDegree := by positivity
      linarith
    refine ⟨h3, P.coeff 0, ?_⟩
    rw [hP, eq_C_of_natDegree_eq_zero h2, aeval_C, coeff_C_zero]
  refine ⟨if h : a ⟨0, S.hn⟩ = 0 then 0 else Classical.choose (hai _ h).2, ?_⟩
  rw [ha, Finset.sum_eq_single ⟨0, S.hn⟩ (fun i _ hi ↦ by
      by_cases hai0 : a i = 0
      · rw [hai0, map_zero, zero_mul]
      · exact absurd (Fin.ext (hai i hai0).1) hi)
    (fun h ↦ absurd (Finset.mem_univ _) h)]
  split_ifs with h
  · simp [h]
  · simp only [pow_zero, mul_one]
    exact Classical.choose_spec (hai _ h).2

variable [Differential C] [Differential L] [DifferentialAlgebra C L]

/-- **Residue-free Liouville forms are exact.** -/
theorem super_second_kind (K : Type*) [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]
    (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1)
    (hconst : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (hcop : Nat.Coprime S.n S.p.natDegree) (f v : L) (hf : f ∈ C⟮S.x⟯⟮S.y⟯)
    (hv : v ∈ C⟮S.x⟯⟮S.y⟯) {ι : Type*} [DecidableEq ι] (s : Finset ι) (c u : ι → L)
    (hc : ∀ i ∈ s, (c i)′ = 0) (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, c i * logDeriv (u i))
    (hnb : ∀ (α β : K) (hβ : β ≠ 0) (hβp : β ^ S.n = (S.p.map (algebraMap C K)).eval α),
      LaurentSeries.res (S.embXY α β hβ hβp ⟨f, hf⟩) = 0)
    (hbr : ∀ (e γ : K) (he : (S.p.map (algebraMap C K)).eval e = 0) (hγ : γ ≠ 0)
      (hγp : γ ^ S.n = (Polynomial.derivative (S.p.map (algebraMap C K))).eval e),
      LaurentSeries.res (S.embB e γ he hγ hγp ⟨f, hf⟩ * single ((S.n : ℤ) - 1) (S.n : K)) = 0) :
    f = v′ := by
  obtain ⟨k, d, w, ⟨hd, hw, hind⟩, hsum⟩ := logSum_qindep (C⟮S.x⟯⟮S.y⟯).toSubfield s c u hc
    (fun i hi ↦ ⟨(hu i hi).1, (hu i hi).2⟩)
  have hdC : ∀ j, ∃ dc : C, j < k → d j = algebraMap C L dc := fun j ↦ by
    by_cases hj : j < k
    · obtain ⟨dc, hdc⟩ := hconst (d j) (hd j hj)
      exact ⟨dc, fun _ ↦ hdc.symm⟩
    · exact ⟨0, fun h ↦ absurd h hj⟩
  choose dc hdc using hdC
  set w' : ℕ → L := fun j ↦ if j < k then w j else 1
  have hw' : ∀ j, w' j ≠ 0 ∧ w' j ∈ C⟮S.x⟯⟮S.y⟯ := fun j ↦ by
    by_cases hj : j < k
    · simp only [w', if_pos hj]; exact hw j hj
    · simp only [w', if_neg hj]; exact ⟨one_ne_zero, one_mem _⟩
  have heq' : f = v′ + ∑ j ∈ Finset.range k, algebraMap C L (dc j) * ((w' j)′ / w' j) := by
    rw [heq, hsum]
    congr 1
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' := Finset.mem_range.mp hj
    simp only [w', if_pos hj', hdc j hj']
    rfl
  -- every `wⱼ` has order `0` at every finite point
  have hzero : ∀ j < k, ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K ⟨w' j, (hw' j).2⟩ α β = 0 := by
    have key : ∀ (ordj : ℕ → ℤ), ∑ j ∈ Finset.range k, algebraMap C K (dc j) * (ordj j : K) = 0 →
        ∀ j < k, ordj j = 0 := by
      intro ordj h j hj
      have h1 : algebraMap C K (∑ j ∈ Finset.range k, dc j * (ordj j : C)) = 0 := by
        rw [map_sum]; simpa using h
      have h2 : ∑ j ∈ Finset.range k, ((ordj j : ℚ) : L) * d j = 0 := by
        have h3 := congrArg (algebraMap C L)
          ((map_eq_zero_iff _ (algebraMap C K).injective).mp h1)
        rw [map_sum, map_zero] at h3
        rw [← h3]
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [hdc j (Finset.mem_range.mp hj), map_mul, map_intCast]
        push_cast; ring
      exact_mod_cast hind (fun j ↦ (ordj j : ℚ)) h2 j hj
    intro j hj α β hvp
    by_cases hβ : β = 0
    · subst hβ
      have he : (S.p.map (algebraMap C K)).eval α = 0 := by rw [← hvp, zero_pow S.hn.ne']
      obtain ⟨γ, hγ, hγp⟩ := S.exists_gamma α he
      have hr := S.res_liouville_branch hC hx α γ he hγ hγp (Finset.range k) dc w'
        (fun j ↦ (hw' j).2) (fun j ↦ (hw' j).1) v f hv hf heq'
      rw [hbr α γ he hγ hγp, eq_comm] at hr
      rw [S.ordAt_br _ α γ he hγ hγp]
      exact key _ hr j hj
    · have hr := S.res_liouville hC hx α β hβ hvp (Finset.range k) dc w'
        (fun j ↦ (hw' j).2) (fun j ↦ (hw' j).1) v f hv hf heq'
      rw [hnb α β hβ hvp, eq_comm] at hr
      rw [S.ordAt_nb _ α β hβ hvp]
      exact key _ hr j hj
  -- hence every `wⱼ` is a constant and the logarithmic part vanishes
  rw [heq', add_eq_left]
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  have hj' := Finset.mem_range.mp hj
  obtain ⟨cj, hcj⟩ := S.const_of_ordAt_zero K hcop ⟨w' j, (hw' j).2⟩
    (fun h ↦ (hw' j).1 (congrArg Subtype.val h)) (hzero j hj')
  rw [show w' j = algebraMap C L cj from hcj, deriv_algebraMap, hC, map_zero, zero_div, mul_zero]

end SuperData

end Differential
