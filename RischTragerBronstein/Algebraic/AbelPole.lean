import RischTragerBronstein.Algebraic.AbelLine

/-!
# No function with a single simple pole (Abel bridge, step B4)

On `y² = p(x)` with `deg p = 3` there is no `w ≠ 0` whose divisor is `(R) − (∞)`: such a `w` is
integral (`integral_of_regular'`: `w = a₀(x) + a₁(x) y`), has a simple pole at infinity
(`degree_eq'`), and the pole bound at infinity (`inf_bound`: orders `−2 deg a₀` and
`−2 deg a₁ − 3`) forces `a₁ = 0` and `a₀` constant — but a constant has no zero (`no_simple_pole`).
-/

open Polynomial IntermediateField HahnSeries

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [PerfectField C] [Field L] [Algebra C L] [Field K] [Algebra C K]
  [IsAlgClosed K]
variable (S : SuperData C L)

open Classical in
/-- **B4: no function has divisor `(R) − (∞)`.** -/
theorem no_simple_pole (hn2 : S.n = 2) (hd3 : S.p.natDegree = 3) (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0)
    (α₀ β₀ : K) (hR : β₀ ^ S.n = (S.p.map (algebraMap C K)).eval α₀)
    (hdiv : ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K w α β = if α = α₀ ∧ β = β₀ then 1 else 0) : False := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  have hcop : Nat.Coprime S.n S.p.natDegree := by rw [hn2, hd3]; norm_num
  have hint : S.IsIntegralS K w := fun α β hv ↦ by rw [hdiv α β hv]; split_ifs <;> norm_num
  -- a simple pole at infinity
  have hdeg := S.degree_eq' (K := K) hcop w hw hint {(α₀, β₀)} (by simpa using hR)
    (fun α β hv hn ↦ by
      rw [hdiv α β hv, if_neg]; rintro ⟨rfl, rfl⟩; exact hn (Finset.mem_singleton_self _))
  rw [Finset.sum_singleton, hdiv α₀ β₀ hR, if_pos ⟨rfl, rfl⟩] at hdeg
  -- `w = a₀ + a₁ y` with polynomial coefficients
  obtain ⟨a, ha, hpoly⟩ := S.integral_of_regular' (K := K) w hint
  obtain ⟨lam, hlam, hlp⟩ := S.exists_lam (K := K)
  have hinf : S.ordInf K w = -1 := by linarith
  rw [S.ordInf_eq hcop w lam hlam hlp] at hinf
  have hne : S.embI lam hlam hlp w ≠ 0 := (map_ne_zero_iff _ (RingHom.injective _)).mpr hw
  have hc : ((-1 : ℤ) : WithTop ℤ) ≤ (S.embI lam hlam hlp (∑ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ (i : ℕ))).orderTop := by
    rw [← ha, orderTop_eq_order hne, hinf]
  have hb := S.inf_bound hcop lam hlam hlp a (-1) hc
  -- the coefficients as polynomials
  have hP : ∀ i, ∃ P : C[X], a i = algebraMap C[X] C⟮S.x⟯ P := fun i ↦ by
    obtain ⟨P, hP⟩ := hpoly i
    exact ⟨P, Subtype.ext (by rw [hP, algebraMap_adjoinSimple])⟩
  have hi1 : (1 : ℕ) < S.n := by rw [hn2]; norm_num
  have hi0 : (0 : ℕ) < S.n := S.hn
  set i1 : Fin S.n := ⟨1, hi1⟩
  set i0 : Fin S.n := ⟨0, hi0⟩
  have ha1 : a i1 = 0 := by
    by_contra h
    have := hb i1 h
    obtain ⟨P, hPe⟩ := hP i1
    have hP0 : P ≠ 0 := fun h0 ↦ h (by rw [hPe, h0, map_zero])
    rw [hPe, S.embXG_inf_poly P hP0] at this
    simp only [i1] at this
    rw [hn2, hd3] at this
    push_cast at this
    omega
  obtain ⟨P0, hP0e⟩ := hP i0
  have hdeg0 : P0.natDegree = 0 := by
    by_cases hz : P0 = 0
    · rw [hz, natDegree_zero]
    have h0 : a i0 ≠ 0 := fun h ↦ hz (by
      rw [hP0e] at h; exact (map_eq_zero_iff _ (IsFractionRing.injective C[X] C⟮S.x⟯)).mp h)
    have := hb i0 h0
    rw [hP0e, S.embXG_inf_poly P0 hz] at this
    simp only [i0] at this
    rw [hn2] at this
    push_cast at this
    omega
  -- so `w = P₀(x)` with `P₀` constant, of order `0` at `R`
  have hw0 : w = S.polyX P0 := by
    rw [ha, Finset.sum_eq_single i0]
    · rw [hP0e]; simp [i0, polyX]
    · intro i _ hi
      have hi' : i = i1 := by
        apply Fin.ext
        have := i.2
        have h0 : (i : ℕ) ≠ 0 := fun h ↦ hi (Fin.ext h)
        simp only [i1]; omega
      rw [hi', ha1, map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hP00 : P0 ≠ 0 := fun h0 ↦ hw (by rw [hw0, h0]; simp [polyX])
  have hord := hdiv α₀ β₀ hR
  rw [if_pos ⟨rfl, rfl⟩, hw0, S.ordAt_polyX P0 hP00 α₀ β₀ hR] at hord
  have hm : (P0.map (algebraMap C K)).rootMultiplicity α₀ = 0 := by
    rw [rootMultiplicity_eq_zero_iff]
    intro hr
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0, Polynomial.map_C, IsRoot, eval_C] at hr
    exact absurd hr (by
      have hc : P0.coeff 0 ≠ 0 := by
        intro hc; apply hP00
        rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0, hc, map_zero]
      exact (map_ne_zero_iff _ (algebraMap C K).injective).mpr hc)
  rw [hm] at hord
  simp at hord

end SuperData

end Differential
