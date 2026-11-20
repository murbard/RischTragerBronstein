import RischTragerBronstein.Algebraic.SuperSecondKind
import RischTragerBronstein.Algebraic.SuperRed

/-!
# Exactness of `B yʲ / p` on a superelliptic curve

`super_exact_zero`: if `B(x) yʲ / p(x) = v′` with `v ∈ C⟮x⟯⟮y⟯`, `0 < j < n` and
`deg B ≤ deg p − 2`, then `B = 0`. Ingredients:

* `order_derivative`: differentiation lowers a non-zero order by one;
* orders of `v` and `v′`: `v′` has no poles at the ordinary points and order `≥ j − n` at the branch
  points, which forces `v` to be integral, hence `v = ∑ Pᵢ(x) yⁱ` (`integral_of_regular'`);
* `coords_unique`: `1, y, …, yⁿ⁻¹` are independent over `C(x)`;
* `natDegree_supOp`: `p G′ + r G p′` has degree `deg G + deg p − 1`.
-/

open Polynomial IntermediateField HahnSeries

namespace LaurentSeries

variable {K : Type*} [Field K] [CharZero K]

/-- Differentiation lowers a non-zero order by one. -/
theorem order_derivative (F : K⸨X⸩) (hF : F ≠ 0) (h0 : F.order ≠ 0) :
    (derivative K F).order = F.order - 1 := by
  have hc : (derivative K F).coeff (F.order - 1) ≠ 0 := by
    rw [derivative_coeff, sub_add_cancel]
    exact mul_ne_zero (by exact_mod_cast h0) ((not_congr HahnSeries.coeff_order_eq_zero).mpr hF)
  have hne : derivative K F ≠ 0 := fun h ↦ hc (by rw [h]; rfl)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc) (not_lt.mp fun hlt ↦ ?_)
  have := (not_congr HahnSeries.coeff_order_eq_zero).mpr hne
  rw [derivative_coeff, HahnSeries.coeff_eq_zero_of_lt_order (by omega), mul_zero] at this
  exact this rfl

end LaurentSeries

namespace Polynomial

variable {k : Type*} [Field k] [CharZero k]

/-- `p G′ + r G p′` has degree `deg G + deg p − 1` (when `m + r deg p ≠ 0` for all `m`). -/
theorem supOp_ne_zero_deg (p G : k[X]) (r : k) (hp : 1 ≤ p.natDegree) (hG : G ≠ 0)
    (hr : ∀ m : ℕ, (m : k) + p.natDegree * r ≠ 0) :
    (p * derivative G + C r * (G * derivative p)).coeff (G.natDegree + p.natDegree - 1) ≠ 0 := by
  set g := G.natDegree
  set d := p.natDegree
  have hp0 : p ≠ 0 := by rintro rfl; simp [d] at hp
  have h1 : (p * derivative G).coeff (g + d - 1) = p.leadingCoeff * (G.leadingCoeff * g) := by
    rcases Nat.eq_zero_or_pos g with hg | hg
    · rw [derivative_of_natDegree_zero hg, mul_zero, coeff_zero]; simp [g, hg]
    · rw [show g + d - 1 = d + (g - 1) by omega, coeff_mul_add_eq_of_natDegree_le le_rfl
        ((natDegree_derivative_le G).trans (by omega)), coeff_derivative,
        Nat.sub_add_cancel hg]
      simp only [leadingCoeff]
      push_cast [Nat.cast_sub hg]
      ring
  have h2 : (G * derivative p).coeff (g + d - 1) = G.leadingCoeff * (p.leadingCoeff * d) := by
    rw [show g + d - 1 = g + (d - 1) by omega, coeff_mul_add_eq_of_natDegree_le le_rfl
      ((natDegree_derivative_le p).trans (by omega)), coeff_derivative, Nat.sub_add_cancel hp]
    simp only [leadingCoeff]
    push_cast [Nat.cast_sub hp]
    ring
  rw [coeff_add, coeff_C_mul, h1, h2]
  have := hr g
  have hlG := leadingCoeff_ne_zero.mpr hG
  have hlp := leadingCoeff_ne_zero.mpr hp0
  intro h
  apply this
  have : p.leadingCoeff * G.leadingCoeff * (g + d * r) = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero hlp hlG)

end Polynomial

namespace Differential

namespace SuperData

variable {C L : Type*} [Field C] [PerfectField C] [Field L] [Algebra C L]

variable (S : SuperData C L)

/-- **`1, y, …, yⁿ⁻¹` are independent over `C(x)`.** -/
theorem coords_unique (T : Fin S.n → C[X])
    (h : ∑ i, aeval S.x (T i) * S.y ^ (i : ℕ) = 0) : ∀ i, T i = 0 := by
  classical
  letI := algebraAdjoinSimple (F := C) S.x
  haveI := isFractionRing_adjoin_simple S.x S.htr
  set Q : C⟮S.x⟯[X] := ∑ i : Fin S.n, monomial (i : ℕ) (algebraMap C[X] C⟮S.x⟯ (T i))
  have hQ : aeval S.y Q = 0 := by
    rw [← h, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [aeval_monomial, IntermediateField.algebraMap_apply, algebraMap_adjoinSimple]
  have hcoeff : ∀ i : Fin S.n, Q.coeff i = algebraMap C[X] C⟮S.x⟯ (T i) := fun i ↦ by
    rw [finsetSum_coeff, Finset.sum_eq_single i (fun b _ hb ↦ by
      rw [coeff_monomial, if_neg (fun h ↦ hb (Fin.ext h))]) (fun h ↦ absurd (Finset.mem_univ i) h),
      coeff_monomial, if_pos rfl]
  have hQ0 : Q = 0 := by
    by_contra hQ0
    have h1 := minpoly.degree_le_of_ne_zero C⟮S.x⟯ S.y hQ0 hQ
    rw [S.minpoly_eq, degree_X_pow_sub_C S.hn] at h1
    have h2 : Q.degree < S.n := by
      refine (degree_sum_le _ _).trans_lt ?_
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun i _ ↦ ?_
      exact (degree_monomial_le _ _).trans_lt (by exact_mod_cast i.2)
    exact absurd (h1.trans_lt h2) (lt_irrefl _)
  intro i
  have := hcoeff i
  rw [hQ0, Polynomial.coeff_zero, eq_comm] at this
  exact (map_eq_zero_iff _ (IsFractionRing.injective C[X] C⟮S.x⟯)).mp this


/-- `(P(x) yⁱ)′ p(x) = yⁱ (p P′ + (i/n) P p′)(x)`. -/
lemma deriv_poly_y_mul [CharZero C] [CharZero L] [Differential C] [Differential L] [DifferentialAlgebra C L] 
    (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (P : C[X]) (i : ℕ) :
    (aeval S.x P * S.y ^ i)′ * aeval S.x S.p = S.y ^ i *
      aeval S.x (S.p * derivative P + Polynomial.C ((i : C) / S.n) * (P * derivative S.p)) := by
  have hy0 := S.y_ne_zero
  have hp0 := S.p_ne_zero
  have hn0 : (S.n : L) ≠ 0 := by exact_mod_cast S.hn.ne'
  rw [Derivation.leibniz, Derivation.leibniz_pow, deriv_aeval_x S.x hC hx, S.deriv_y hC hx]
  simp only [smul_eq_mul, nsmul_eq_mul, map_add, map_mul, aeval_C, map_div₀, map_natCast]
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi; simp; ring
  · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    field_simp
    ring

section Orders

variable {K : Type*} [Field K] [Algebra C K] [IsAlgClosed K]

open Classical in
/-- `y` has order `0` off the branch points and `1` at them. -/
lemma ordAt_gen (α β : K) (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    S.ordAt K (AdjoinSimple.gen C⟮S.x⟯ S.y) α β = if β = 0 then 1 else 0 := by
  by_cases hβ : β = 0
  · subst hβ
    have he : (S.p.map (algebraMap C K)).eval α = 0 := by rw [← hv, zero_pow S.hn.ne']
    obtain ⟨γ, hγ, hγp⟩ := S.exists_gamma α he
    rw [S.ordAt_br _ α γ he hγ hγp, if_pos rfl]
    unfold embB
    rw [S.embG_gen, S.order_branchYe]
  · rw [S.ordAt_nb _ α β hβ hv, if_neg hβ, S.embXY_gen,
      order_ofPS_unit _ (by rw [branchY_const]; exact hβ)]

/-- Differentiation at an ordinary point lowers a non-zero order by one. -/
lemma ordAt_deriv_nb [CharZero C] [CharZero L] [CharZero K] [Differential C] [Differential L] [DifferentialAlgebra C L] 
    (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (α β : K) (hβ : β ≠ 0)
    (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) (w : L) (hw : w ∈ C⟮S.x⟯⟮S.y⟯)
    (hw0 : w ≠ 0) (hord : S.ordAt K ⟨w, hw⟩ α β ≠ 0) :
    S.ordAt K ⟨w′, S.derivClosedXY hC hx w hw⟩ α β = S.ordAt K ⟨w, hw⟩ α β - 1 := by
  rw [S.ordAt_nb _ α β hβ hv, S.ordAt_nb _ α β hβ hv] at *
  rw [S.embXY_deriv hC hx α β hβ hv w hw, LaurentSeries.derivation_apply,
    LaurentSeries.order_derivative _ ((map_ne_zero_iff _ (RingHom.injective _)).mpr
      (fun h ↦ hw0 (congrArg Subtype.val h))) hord]

/-- Differentiation at a branch point lowers a non-zero order by `n`. -/
lemma ordAt_deriv_br [CharZero C] [CharZero L] [CharZero K] [Differential C] [Differential L] [DifferentialAlgebra C L] 
    (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (e : K)
    (he : (S.p.map (algebraMap C K)).eval e = 0) (w : L) (hw : w ∈ C⟮S.x⟯⟮S.y⟯)
    (hw0 : w ≠ 0) (hord : S.ordAt K ⟨w, hw⟩ e 0 ≠ 0) :
    S.ordAt K ⟨w′, S.derivClosedXY hC hx w hw⟩ e 0 = S.ordAt K ⟨w, hw⟩ e 0 - S.n := by
  obtain ⟨γ, hγ, hγp⟩ := S.exists_gamma e he
  rw [S.ordAt_br _ e γ he hγ hγp, S.ordAt_br _ e γ he hγ hγp] at *
  set Xh : LaurentSeries K := HahnSeries.C e + single (S.n : ℤ) 1
  have hX : LaurentSeries.derivation Xh ≠ 0 := by
    rw [derivation_branchX S.n S.hn e]
    exact HahnSeries.single_ne_zero (by exact_mod_cast S.hn.ne')
  have hd := S.embG_derivG Xh hX (branchSub S.n e) (branchSub_injective S.n S.hn e)
    (fun P ↦ by rw [branchSub_eq_subst]) hC hx (S.branchYe e γ hγ hγp)
    (S.branchYe_pow e γ he hγ hγp) w hw
  have hF0 : S.embB e γ he hγ hγp ⟨w, hw⟩ ≠ 0 :=
    (map_ne_zero_iff _ (RingHom.injective _)).mpr (fun h ↦ hw0 (congrArg Subtype.val h))
  have hD : LaurentSeries.derivative K (S.embB e γ he hγ hγp ⟨w, hw⟩) ≠ 0 := by
    intro h
    have := LaurentSeries.order_derivative _ hF0 hord
    rw [h, HahnSeries.order_zero] at this
    have h2 : (S.embB e γ he hγ hγp ⟨w, hw⟩).order = 1 := by omega
    have := (not_congr HahnSeries.coeff_order_eq_zero).mpr hF0
    have hc := congrArg (fun F : LaurentSeries K ↦ F.coeff 0) h
    simp only [LaurentSeries.derivative_coeff, HahnSeries.coeff_zero, zero_add] at hc
    rw [h2] at this
    exact this ((mul_eq_zero.mp hc).resolve_left (by norm_num))
  unfold embB at hF0 hD ⊢
  rw [hd, deltaX_apply, HahnSeries.order_mul (inv_ne_zero hX) (by
      rw [LaurentSeries.derivation_apply]; exact hD), order_inv' _ hX,
    derivation_branchX S.n S.hn e, HahnSeries.order_single (by exact_mod_cast S.hn.ne'),
    LaurentSeries.derivation_apply, LaurentSeries.order_derivative _ hF0 hord]
  ring

open Classical in
/-- Orders of `R(x) yʲ / p(x)`: non-negative off the branch points, `≥ j − n` at them. -/
lemma ordAt_Ryp (j : ℕ) (R : C[X]) (hR0 : R ≠ 0) (α β : K)
    (hvp : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    (if β = 0 then (j : ℤ) - S.n else 0) ≤ S.ordAt K (S.polyX R *
      AdjoinSimple.gen C⟮S.x⟯ S.y ^ j * (S.polyX S.p)⁻¹) α β := by
  have hg0 : AdjoinSimple.gen C⟮S.x⟯ S.y ≠ 0 := fun h ↦ S.y_ne_zero (congrArg Subtype.val h)
  have hpX0 := S.polyX_ne_zero S.hsq.ne_zero
  have hRX0 := S.polyX_ne_zero hR0
  have hsep : (S.p.map (algebraMap C K)).Separable :=
    (PerfectField.separable_iff_squarefree.mpr S.hsq).map
  rw [S.ordAt_mul hvp (mul_ne_zero hRX0 (pow_ne_zero _ hg0)) (inv_ne_zero hpX0),
    S.ordAt_mul hvp hRX0 (pow_ne_zero _ hg0), S.ordAt_pow hvp, S.ordAt_inv hvp,
    S.ordAt_polyX _ hR0 α β hvp, S.ordAt_polyX _ S.hsq.ne_zero α β hvp, S.ordAt_gen α β hvp]
  have hm0 : (0 : ℤ) ≤ ((R.map (algebraMap C K)).rootMultiplicity α : ℤ) := by positivity
  by_cases hβ : β = 0
  · have he : (S.p.map (algebraMap C K)).eval α = 0 := by rw [← hvp, hβ, zero_pow S.hn.ne']
    have hm1 : (S.p.map (algebraMap C K)).rootMultiplicity α = 1 :=
      le_antisymm (rootMultiplicity_le_one_of_separable hsep α)
        ((rootMultiplicity_pos (hsep.ne_zero)).mpr he)
    simp only [hβ, ↓reduceIte, hm1, Nat.cast_one, mul_one]
    nlinarith
  · have hm0' : (S.p.map (algebraMap C K)).rootMultiplicity α = 0 :=
      rootMultiplicity_eq_zero (by rw [IsRoot, ← hvp]; exact pow_ne_zero _ hβ)
    simp only [hβ, ↓reduceIte, hm0', Nat.cast_zero, mul_zero, one_mul, sub_zero]
    linarith


lemma polyX_coe (P : C[X]) : ((S.polyX P : C⟮S.x⟯⟮S.y⟯) : L) = aeval S.x P := by
  letI := algebraAdjoinSimple (F := C) S.x
  show ((algebraMap C[X] C⟮S.x⟯ P : C⟮S.x⟯) : L) = _
  exact algebraMap_adjoinSimple S.x P

/-- **Exactness forces the remainder to vanish.** -/
theorem super_exact_zero [CharZero C] [CharZero L] [Differential C] [Differential L]
    [DifferentialAlgebra C L] (K : Type*) [Field K] [CharZero K] [Algebra C K] [IsAlgClosed K]
    (hC : ∀ c : C, c′ = 0) (hx : S.x′ = 1) (j : ℕ) (hj0 : 0 < j) (hjn : j < S.n) (R : C[X])
    (hR : R = 0 ∨ R.natDegree + 2 ≤ S.p.natDegree) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : aeval S.x R * S.y ^ j / aeval S.x S.p = v′) : R = 0 := by
  classical
  by_contra hR0
  have hRd : R.natDegree + 2 ≤ S.p.natDegree := hR.resolve_left hR0
  set g := AdjoinSimple.gen C⟮S.x⟯ S.y
  have hg0 : g ≠ 0 := fun h ↦ S.y_ne_zero (congrArg Subtype.val h)
  set F : C⟮S.x⟯⟮S.y⟯ := S.polyX R * g ^ j * (S.polyX S.p)⁻¹
  have hF : (F : L) = aeval S.x R * S.y ^ j / aeval S.x S.p := by
    simp only [F, g, MulMemClass.coe_mul, SubmonoidClass.coe_pow, IntermediateField.coe_inv,
      polyX_coe, AdjoinSimple.coe_gen, div_eq_mul_inv]
  have hvF : (⟨v′, S.derivClosedXY hC hx v hv⟩ : C⟮S.x⟯⟮S.y⟯) = F := Subtype.ext (by rw [hF, heq])
  have hpX0 := S.polyX_ne_zero S.hsq.ne_zero
  have hRX0 := S.polyX_ne_zero hR0
  have hsep : (S.p.map (algebraMap C K)).Separable :=
    (PerfectField.separable_iff_squarefree.mpr S.hsq).map
  have hordF : ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α →
      (if β = 0 then (j : ℤ) - S.n else 0) ≤ S.ordAt K F α β :=
    fun α β hvp ↦ S.ordAt_Ryp j R hR0 α β hvp
  -- `v` is integral
  have hint : S.IsIntegralS K ⟨v, hv⟩ := by
    intro α β hvp
    by_contra hneg
    push_neg at hneg
    have hv0 : v ≠ 0 := by
      rintro rfl
      have : (⟨0, hv⟩ : C⟮S.x⟯⟮S.y⟯) = 0 := rfl
      obtain ⟨φ, hφ⟩ := S.ordAt_hom α β hvp
      rw [this, hφ, map_zero, HahnSeries.order_zero] at hneg
      exact lt_irrefl _ hneg
    have hF' := hordF α β hvp
    rw [← hvF] at hF'
    by_cases hβ : β = 0
    · subst hβ
      have he : (S.p.map (algebraMap C K)).eval α = 0 := by rw [← hvp, zero_pow S.hn.ne']
      rw [S.ordAt_deriv_br hC hx α he v hv hv0 hneg.ne, if_pos rfl] at hF'
      linarith
    · rw [S.ordAt_deriv_nb hC hx α β hβ hvp v hv hv0 hneg.ne, if_neg hβ] at hF'
      linarith
  -- `v = ∑ Pᵢ(x) yⁱ`
  obtain ⟨a, ha, hpoly⟩ := S.integral_of_regular' K ⟨v, hv⟩ hint
  choose P hP using hpoly
  have hvsum : v = ∑ i : Fin S.n, aeval S.x (P i) * S.y ^ (i : ℕ) := by
    have := congrArg Subtype.val ha
    simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
      AdjoinSimple.coe_gen] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hP i]
    rfl
  -- compare coordinates
  set r : C := (j : C) / S.n
  set Q : Fin S.n → C[X] := fun i ↦
    S.p * derivative (P i) + Polynomial.C ((i : C) / S.n) * (P i * derivative S.p)
  have hsum : v′ * aeval S.x S.p = ∑ i : Fin S.n, aeval S.x (Q i) * S.y ^ (i : ℕ) := by
    rw [hvsum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [S.deriv_poly_y_mul hC hx, mul_comm]
  have hlhs : v′ * aeval S.x S.p = aeval S.x R * S.y ^ j := by
    rw [← heq, div_mul_cancel₀ _ S.p_ne_zero]
  have hjF : (⟨j, hjn⟩ : Fin S.n) = ⟨j, hjn⟩ := rfl
  have hcoords := S.coords_unique (fun i ↦ Q i - if (i : ℕ) = j then R else 0) (by
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    rw [← hsum, hlhs, Finset.sum_eq_single (⟨j, hjn⟩ : Fin S.n) (fun i _ hi ↦ by
        rw [if_neg (fun h ↦ hi (Fin.ext h)), map_zero, zero_mul])
      (fun h ↦ absurd (Finset.mem_univ _) h), if_pos rfl, sub_self])
    ⟨j, hjn⟩
  simp only [↓reduceIte, sub_eq_zero] at hcoords
  -- degrees
  by_cases hPj : P ⟨j, hjn⟩ = 0
  · apply hR0
    rw [← hcoords]
    simp [Q, hPj]
  · have hr : ∀ m : ℕ, (m : C) + S.p.natDegree * ((j : C) / S.n) ≠ 0 := by
      intro m
      have hn0 : (S.n : C) ≠ 0 := by exact_mod_cast S.hn.ne'
      rw [show (m : C) + S.p.natDegree * ((j : C) / S.n) =
        ((m * S.n + S.p.natDegree * j : ℕ) : C) / S.n by push_cast; field_simp]
      refine div_ne_zero ?_ hn0
      have : 0 < S.p.natDegree * j := Nat.mul_pos S.hp hj0
      exact_mod_cast (show m * S.n + S.p.natDegree * j ≠ 0 by omega)
    have hc := Polynomial.supOp_ne_zero_deg S.p (P ⟨j, hjn⟩) ((j : C) / S.n) S.hp hPj hr
    have hQj : Q ⟨j, hjn⟩ = S.p * derivative (P ⟨j, hjn⟩) +
        Polynomial.C ((j : C) / S.n) * (P ⟨j, hjn⟩ * derivative S.p) := rfl
    rw [← hQj, hcoords] at hc
    have := le_natDegree_of_ne_zero hc
    omega

end Orders

end SuperData

end Differential
