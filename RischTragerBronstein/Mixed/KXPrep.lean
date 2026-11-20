import RischTragerBronstein.Mixed.KQLiouville

/-!
# Liouville forms with poles at ordinary places, for `x′ = ω(x)` with bad places

`kx_prep0`: the generalization of `kq_prep0` to a derivation `x′ = ω(x)` whose good places are
those outside a set `bad` (for an exponential `x′ = ηx`, the places over `x = 0`): the logarithms
have no zeros or poles at the good places away from the poles `c_q`, and at the poles the raw
residue identity holds with `ω(c_q) − c_q′`.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries Classical

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L)

section GenLog

variable (ω : C[X]) (hx : S.x′ = aeval S.x ω)
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
  (bad : K → Prop) (hgood : ∀ α : K, ¬ bad α → α′ ≠ (ω.map (algebraMap C K)).eval α)
  (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
  {r : ℕ} (c : Fin r → C) (hbadc : ∀ q, ¬ bad (algebraMap C K (c q)))
  (P : C[X]) (l : ℕ) (b : L) (hb : b ∈ C⟮S.x⟯)
  (D : C[X]) (R : Fin r → C[X]) (hDR : ∀ q, D = (X - Polynomial.C (c q)) * R q)
  (hRne : ∀ q, (R q).eval (c q) ≠ 0)
  (hDoff : ∀ α : K, ¬ bad α → (∀ q, α ≠ algebraMap C K (c q)) → (D.map (algebraMap C K)).eval α ≠ 0)
  (hbP : b * aeval S.x (D * S.p ^ l) = aeval S.x P)
  (hpc : ∀ q, S.p.eval (c q) ≠ 0)

include hx hK hgood hbadc hconstC hb hDR hRne hDoff hbP hpc in
/-- **The Liouville data, normalized**, with the raw residues at the poles. -/
theorem kx_prep0 (hn1 : 1 < S.n) (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) :
    ∃ (k : ℕ) (d : ℕ → C) (w : ℕ → L) (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0),
      (∀ t : ℕ → ℚ, ∑ j ∈ Finset.range k, (t j : C) * d j = 0 → ∀ j < k, t j = 0) ∧
      b * S.y = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * logDeriv (w j) ∧
      (∀ j < k, (algebraMap C L (d j))′ = 0) ∧
      (∀ j (hj : j < k), ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
        ¬ bad α → (∀ q, α ≠ algebraMap C K (c q)) → S.ordAt K ⟨w j, (hw j hj).1⟩ α β' = 0) ∧
      ∀ q (β' : K), β' ^ S.n = (S.p.map (algebraMap C K)).eval (algebraMap C K (c q)) →
        (∑ j ∈ Finset.range k, algebraMap C K (d j) *
          (if h : j < k then (S.ordAt K ⟨w j, (hw j h).1⟩ (algebraMap C K (c q)) β' : K) else 0)) *
            algebraMap C K ((ω.eval (c q) - (c q)′) * (R q * S.p ^ l).eval (c q)) =
              algebraMap C K (P.eval (c q)) * β' := by
  classical
  obtain ⟨k, d, w, ⟨hd, hw, hind⟩, hsum⟩ :=
    logSum_qindep (C⟮S.x⟯⟮S.y⟯).toSubfield s cs u hcs (fun i hi ↦ hu i hi)
  set d' : ℕ → C := fun jj ↦ if h : jj < k then Classical.choose (hconstC (d jj) (hd jj h)) else 0
    with hd'def
  have hdd : ∀ jj < k, algebraMap C L (d' jj) = d jj := fun jj hjj ↦ by
    simp only [hd'def, dif_pos hjj]
    exact Classical.choose_spec (hconstC (d jj) (hd jj hjj))
  have hind' : ∀ t : ℕ → ℚ, ∑ jj ∈ Finset.range k, (t jj : C) * d' jj = 0 →
      ∀ jj < k, t jj = 0 := by
    intro t ht
    apply hind t
    rw [← map_zero (algebraMap C L), ← ht, map_sum]
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [map_mul, map_ratCast, hdd jj (Finset.mem_range.mp hjj)]
  have hw' : ∀ jj < k, w jj ∈ C⟮S.x⟯⟮S.y⟯ ∧ w jj ≠ 0 := fun jj hjj ↦ ⟨(hw jj hjj).2, (hw jj hjj).1⟩
  have heq' : b * S.y = v′ + ∑ jj ∈ Finset.range k, algebraMap C L (d' jj) * logDeriv (w jj) := by
    rw [heq, hsum]
    congr 1
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [hdd jj (Finset.mem_range.mp hjj)]
  have heq'' : b * S.y = v′ + ∑ jj ∈ Finset.range k, algebraMap C L (d' jj) * ((w jj)′ / w jj) := by
    rw [heq']; rfl
  have hQ := S.kq_mulQ P l b D hbP hbm
  refine ⟨k, d', w, hw', hind', heq', fun j hj ↦ by rw [hdd j hj]; exact hd j hj, ?_, ?_⟩
  · intro j hj α β' hvβ hbα hα
    by_cases hβ0 : β' = 0
    · subst hβ0
      have he : (S.p.map (algebraMap C K)).eval α = 0 := by rw [← hvβ, zero_pow S.hn.ne']
      exact S.ordAt_logs_zero_classW ω hx hK k d' w hw' hind' v _ hv hbm heq'' b hb
        1 one_pos hn1 (by rw [pow_one]) α he (hgood α hbα) j hj
    · -- `b y` is regular at `(α, β')`
      have hreg : 0 ≤ S.ordAt K ⟨b * S.y, hbm⟩ α β' := by
        have hR : ((D * S.p ^ l).map (algebraMap C K)).comp (X + Polynomial.C α) =
            X ^ 0 * ((D * S.p ^ l).map (algebraMap C K)).comp (X + Polynomial.C α) := by
          rw [pow_zero, one_mul]
        have hR0 : (((D * S.p ^ l).map (algebraMap C K)).comp (X + Polynomial.C α)).eval 0 ≠ 0 := by
          rw [eval_comp, eval_add, eval_X, eval_C, zero_add, Polynomial.map_mul, eval_mul,
            Polynomial.map_pow, eval_pow]
          exact mul_ne_zero (hDoff α hbα hα) (pow_ne_zero _ (S.p_eval_ne α β' hβ0 hvβ))
        obtain ⟨h1, -⟩ := S.expand_pole _ P _ hQ α β' hβ0 hvβ 0 _ hR hR0
        rw [S.ordAt_nb _ α β' hβ0 hvβ]
        by_cases h0 : S.embXY α β' hβ0 hvβ ⟨b * S.y, hbm⟩ = 0
        · rw [h0, HahnSeries.order_zero]
        · by_contra hlt
          push Not at hlt
          exact (not_congr HahnSeries.coeff_order_eq_zero).mpr h0 (h1 _ (by simpa using hlt))
      exact S.ordAt_logs_zeroW ω hx hK k d' w hw' hind' v _ hv hbm heq'' α β' hvβ
        (hgood α hbα) hreg j hj
  · intro q β' hvβ
    set α := algebraMap C K (c q) with hαdef
    have hpcK : (S.p.map (algebraMap C K)).eval α = algebraMap C K (S.p.eval (c q)) := by
      rw [hαdef, eval_map, eval₂_at_apply]
    have hβ0 : β' ≠ 0 := by
      intro h0
      rw [h0, zero_pow S.hn.ne', hpcK] at hvβ
      exact hpc q ((algebraMap C K).injective (by rw [← hvβ, map_zero]))
    have hα' : α′ = algebraMap C K (c q)′ := hK _
    have hRc : ((R q * S.p ^ l).map (algebraMap C K)).eval α =
        algebraMap C K ((R q * S.p ^ l).eval (c q)) := by
      rw [hαdef, eval_map, eval₂_at_apply]
    have hR : ((D * S.p ^ l).map (algebraMap C K)).comp (X + Polynomial.C α) =
        X ^ 1 * ((R q * S.p ^ l).map (algebraMap C K)).comp (X + Polynomial.C α) := by
      rw [hDR q, mul_assoc, Polynomial.map_mul (p := X - Polynomial.C (c q)), mul_comp,
        Polynomial.map_sub, map_X, Polynomial.map_C, sub_comp, X_comp, C_comp, pow_one, ← hαdef,
        add_sub_cancel_right]
    have hR0 : (((R q * S.p ^ l).map (algebraMap C K)).comp (X + Polynomial.C α)).eval 0 ≠ 0 := by
      rw [eval_comp, eval_add, eval_X, eval_C, zero_add, Polynomial.map_mul, eval_mul,
        Polynomial.map_pow, eval_pow]
      exact mul_ne_zero (by rw [eval_map, eval₂_at_apply]; exact (_root_.map_ne_zero _).mpr (hRne q)) (pow_ne_zero _ (S.p_eval_ne α β' hβ0 hvβ))
    obtain ⟨h1, h2⟩ := S.expand_pole _ P _ hQ α β' hβ0 hvβ 1 _ hR hR0
    have h3 := S.ordAt_logs_resW ω hx hK k d' w hw' v _ hv hbm heq'' α β' hβ0 hvβ
      (hgood α (hbadc q)) (fun kk hkk ↦ h1 kk (by push_cast; omega))
    have hωc : (ω.map (algebraMap C K)).eval α = algebraMap C K (ω.eval (c q)) := by
      rw [hαdef, eval_map, eval₂_at_apply]
    rw [hα', hωc] at h3
    rw [eval_comp, eval_add, eval_X, eval_C, zero_add, hRc] at h2
    have hPc : (P.map (algebraMap C K)).eval α = algebraMap C K (P.eval (c q)) := by
      rw [hαdef, eval_map, eval₂_at_apply]
    rw [hPc, show (-((1 : ℕ) : ℤ)) = -1 by norm_num, ← h3] at h2
    rw [map_mul, map_sub]
    linear_combination h2

include hx hK hgood hbadc hconstC hb hDR hRne hDoff hbP hpc in
/-- **The residues are constant**: if `b y` has an elementary integral, then at each pole,
`P(c)² p(c) = ζ ((ω(c) − c′) (R pˡ)(c))²` with `ζ′ = 0`. -/
theorem kx_resid_const (hn2 : S.n = 2) (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) (q : Fin r) :
    ∃ ζ : C, ζ′ = 0 ∧ (P.eval (c q)) ^ 2 * S.p.eval (c q) =
      ζ * ((ω.eval (c q) - (c q)′) * (R q * S.p ^ l).eval (c q)) ^ 2 := by
  classical
  obtain ⟨k, d, w, hw, -, -, hdc, -, hraw⟩ :=
    S.kx_prep0 (K := K) ω hx hK bad hgood hconstC c hbadc P l b hb D R hDR hRne hDoff hbP hpc
      (by omega) hbm s cs u hcs hu v hv heq
  obtain ⟨β', hβ'⟩ := IsAlgClosed.exists_pow_nat_eq
    ((S.p.map (algebraMap C K)).eval (algebraMap C K (c q))) S.hn
  have h := hraw q β' hβ'
  set o : ℕ → ℤ := fun j ↦ if hj : j < k then
    S.ordAt K ⟨w j, (hw j hj).1⟩ (algebraMap C K (c q)) β' else 0 with ho
  set σ : C := ∑ j ∈ Finset.range k, d j * (o j : C) with hσ
  have hSm : (∑ j ∈ Finset.range k, algebraMap C K (d j) *
      (if h : j < k then (S.ordAt K ⟨w j, (hw j h).1⟩ (algebraMap C K (c q)) β' : K) else 0)) =
      algebraMap C K σ := by
    rw [hσ, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, map_intCast]
    by_cases hj : j < k <;> simp [ho, hj]
  rw [hSm] at h
  have hd0 : ∀ j < k, (d j)′ = 0 := fun j hj ↦ by
    have := hdc j hj
    rw [deriv_algebraMap] at this
    exact (algebraMap C L).injective (by rw [this, map_zero])
  refine ⟨σ ^ 2, ?_, ?_⟩
  · have : σ′ = 0 := by
      rw [hσ, map_sum]
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      rw [Derivation.leibniz, hd0 j (Finset.mem_range.mp hj), Derivation.map_intCast]
      simp
    rw [Derivation.leibniz_pow, this, smul_zero, smul_zero]
  · apply (algebraMap C K).injective
    have h2 := congrArg (· ^ 2) h
    have hβ2 : β' ^ 2 = (S.p.map (algebraMap C K)).eval (algebraMap C K (c q)) := by
      rw [← hn2]; exact hβ'
    rw [mul_pow, mul_pow, hβ2, eval_map, eval₂_at_apply] at h2
    simp only [map_mul, map_pow]
    rw [← map_pow, ← map_pow] at h2
    simp only [map_mul, map_pow] at h2 ⊢
    linear_combination -h2

end GenLog

end SuperData

end Differential
