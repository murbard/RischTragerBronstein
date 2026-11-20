import RischTragerBronstein.Mixed.KXMulti

/-!
# `b(x) y` over an exponential with simple poles at ordinary places

`S : SuperData C L` with `n = 2`, `x′ = η x`; the points `P± = (0, ±β₀)` over `x = 0`
(`β₀² = p(0) ≠ 0`) are the bad places, where the residue gives no information. A logarithm `w` of a
Liouville form with divisor `∑_k L_k Δ_k` at the good places is normalized to
`z = w² x^{−(r+s)}` (`r, s` its orders at `P±`), whose divisor is `∑_k 2L_k Δ_k + (r − s) δ₀`,
`δ₀ = P₊ − P₋` (`kxe_norm`).
-/

open Polynomial IntermediateField HahnSeries LaurentSeries Classical

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L)

/-- The divisor `δ₀ = P₊ − P₋`. -/
noncomputable def dZ (β₀ : K) (Q : K × K) : ℚ :=
  if Q = (0, β₀) then 1 else if Q = (0, -β₀) then -1 else 0

section Norm

variable (hn2 : S.n = 2) (β₀ : K) (hβ₀ : β₀ ≠ 0)
  (hv0 : β₀ ^ S.n = (S.p.map (algebraMap C K)).eval 0)
  {r nk : ℕ} (c β : Fin r → C) (hc0 : ∀ q, c q ≠ 0) (m : Fin r → ℕ) (cl : Fin r → Fin nk)

include hn2 hv0 in
lemma over_zero' (β' : K) (hv : β' ^ S.n = (S.p.map (algebraMap C K)).eval 0) :
    β' = β₀ ∨ β' = -β₀ := by
  rw [← hv0, hn2] at hv
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hv

include hβ₀ in
lemma dZ_plus : dZ β₀ (0, β₀) = 1 := by simp [dZ]

include hβ₀ in
lemma dZ_minus : dZ β₀ (0, -β₀) = -1 := by
  simp [dZ, Prod.ext_iff, neg_ne_self hβ₀]

lemma dZ_off (α b : K) (hα : α ≠ 0) : dZ β₀ (α, b) = 0 := by
  simp [dZ, Prod.ext_iff, hα]

include hc0 in
lemma dK_zero (k : Fin nk) (b : K) : dK (K := K) c β m cl k (0, b) = 0 :=
  dK_off c β m cl k 0 b fun q h ↦ hc0 q ((algebraMap C K).injective (by rw [← h, map_zero]))

include hn2 hβ₀ hv0 hc0 in
/-- **The normalization of a logarithm.** -/
lemma kxe_norm (w : C⟮S.x⟯⟮S.y⟯) (hw : w ≠ 0) (Lk : Fin nk → ℚ)
    (hord : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 →
      (S.ordAt K w α β' : ℚ) = ∑ k, Lk k * dK c β m cl k (α, β')) :
    let z := w ^ 2 * S.xE ^ (-(S.ordAt K w 0 β₀ + S.ordAt K w 0 (-β₀)))
    z ≠ 0 ∧ ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      (S.ordAt K z α β' : ℚ) = ∑ k, (2 * Lk k) * dK c β m cl k (α, β') +
        ((S.ordAt K w 0 β₀ - S.ordAt K w 0 (-β₀) : ℤ) : ℚ) * dZ β₀ (α, β') := by
  intro z
  have hxp : S.xE ^ (-(S.ordAt K w 0 β₀ + S.ordAt K w 0 (-β₀))) ≠ 0 := zpow_ne_zero _ S.xE_ne
  refine ⟨mul_ne_zero (pow_ne_zero _ hw) hxp, fun α β' hv ↦ ?_⟩
  simp only [z]
  rw [S.ordAt_mul hv (pow_ne_zero _ hw) hxp, S.ordAt_pow hv, S.ordAt_zpow hv, S.ordAt_xE α β' hv]
  by_cases hα : α = 0
  · subst hα
    have hβ' : β' ≠ 0 := by
      intro h0; rw [h0, zero_pow S.hn.ne', ← hv0] at hv
      exact hβ₀ (pow_eq_zero_iff S.hn.ne' |>.mp hv.symm)
    simp only [if_true, if_neg hβ', dK_zero c β hc0 m cl, mul_zero, Finset.sum_const_zero,
      zero_add]
    rcases S.over_zero' hn2 β₀ hv0 β' hv with h | h
    · rw [h, dZ_plus β₀ hβ₀]; push_cast; ring
    · rw [h, dZ_minus β₀ hβ₀]; push_cast; ring
  · simp only [if_neg hα, mul_zero, add_zero, dZ_off β₀ α β' hα]
    push_cast
    rw [hord α β' hv hα, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ by ring

end Norm

section Tail

variable (ω : C[X]) (hx : S.x′ = aeval S.x ω)

include hx in
/-- **The common ending**: if every logarithm is a rational combination of the `log W_k` plus an
element of `C(x)`, then `b y = (a y)′ + ∑ e_k B_k y`. -/
theorem kxm_tail (hn2 : S.n = 2) {nw : ℕ} (W : Fin nw → C⟮S.x⟯⟮S.y⟯)
    (W0 W1 : Fin nw → L) (hW0 : ∀ kk, W0 kk ∈ C⟮S.x⟯) (hW1 : ∀ kk, W1 kk ∈ C⟮S.x⟯)
    (hWe : ∀ kk, (W kk : L) = W0 kk + W1 kk * S.y)
    (hNm : ∀ kk, W0 kk ^ 2 - W1 kk ^ 2 * aeval S.x S.p ≠ 0)
    (b : L) (hb : b ∈ C⟮S.x⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (k : ℕ) (d : ℕ → C) (w : ℕ → L)
    (heq' : b * S.y = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * logDeriv (w j))
    (hdc : ∀ j < k, (algebraMap C L (d j))′ = 0)
    (hlog : ∀ j < k, ∃ (e : Fin nw → ℚ) (G : L), G ∈ C⟮S.x⟯ ∧
      logDeriv (w j) = ∑ kk, (e kk : L) * logDeriv (W kk : L) + G) :
    ∃ a ∈ C⟮S.x⟯, ∃ e : Fin nw → C, (∀ kk, (algebraMap C L (e kk))′ = 0) ∧
      b * S.y = (a * S.y)′ + ∑ kk, algebraMap C L (e kk) *
        ((W0 kk * ((W1 kk)′ + W1 kk * (aeval S.x (mapCoeffs S.p + ω * derivative S.p) /
          ((S.n : L) * aeval S.x S.p))) - (W0 kk)′ * W1 kk) /
          (W0 kk ^ 2 - W1 kk ^ 2 * aeval S.x S.p) * S.y) := by
  classical
  have hcl : DerivClosed C⟮S.x⟯ := S.derivClosedXW ω hx
  have hmemx : ∀ Q : C[X], aeval S.x Q ∈ C⟮S.x⟯ := fun Q ↦ by
    letI := algebraAdjoinSimple (F := C) S.x
    rw [← algebraMap_adjoinSimple (F := C) S.x Q]; exact SetLike.coe_mem _
  choose! e G hG hlogj using hlog
  set Es : Fin nw → C := fun kk ↦ ∑ j ∈ Finset.range k, d j * (e j kk : C)
  set Gs : L := ∑ j ∈ Finset.range k, algebraMap C L (d j) * G j
  have hGs : Gs ∈ C⟮S.x⟯ := sum_mem fun j hj ↦
    mul_mem (IntermediateField.algebraMap_mem _ _) (hG j (Finset.mem_range.mp hj))
  have hsum : ∑ j ∈ Finset.range k, algebraMap C L (d j) * logDeriv (w j) =
      Gs + ∑ kk, algebraMap C L (Es kk) * logDeriv (W kk : L) := by
    rw [Finset.sum_congr rfl fun j hj ↦ by rw [hlogj j (Finset.mem_range.mp hj)]]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [add_comm, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun kk _ ↦ ?_
    simp only [Es, map_sum, map_mul, map_ratCast, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hEs : ∀ kk, (algebraMap C L (Es kk))′ = 0 := by
    intro kk
    rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [map_mul, map_ratCast, Derivation.leibniz, hdc j (Finset.mem_range.mp hj),
      Tower.NestP.deriv_ratCastK (K := L) (e j kk)]
    simp
  rw [hsum] at heq'
  set P' := aeval S.x S.p with hP
  set r := aeval S.x (mapCoeffs S.p + ω * derivative S.p) / ((S.n : L) * P') with hr
  have hy2 : S.y ^ 2 = P' := by rw [← hn2]; exact S.hy
  have hyd : S.y′ = r * S.y := by rw [S.deriv_yW (ω) hx, hr]; ring
  have hrm : r ∈ C⟮S.x⟯ := S.r_memW (ω) hx
  have hPm : P' ∈ C⟮S.x⟯ := hmemx _
  set Bk : Fin nw → L := fun kk ↦
    (W0 kk * ((W1 kk)′ + W1 kk * r) - (W0 kk)′ * W1 kk) / (W0 kk ^ 2 - W1 kk ^ 2 * P')
  set Ek : Fin nw → L := fun kk ↦
    (W0 kk * (W0 kk)′ - W1 kk * ((W1 kk)′ + W1 kk * r) * P') / (W0 kk ^ 2 - W1 kk ^ 2 * P')
  have hab : ∀ kk, logDeriv (W kk : L) = Ek kk + Bk kk * S.y := fun kk ↦ by
    rw [hWe kk]; exact logDeriv_ab (y := S.y) (W0 kk) (W1 kk) P' r hy2 hyd (hNm kk)
  have hNm' : ∀ kk, W0 kk ^ 2 - W1 kk ^ 2 * P' ∈ C⟮S.x⟯ := fun kk ↦
    sub_mem (pow_mem (hW0 kk) 2) (mul_mem (pow_mem (hW1 kk) 2) hPm)
  have hBm : ∀ kk, Bk kk ∈ C⟮S.x⟯ := fun kk ↦ div_mem (sub_mem (mul_mem (hW0 kk)
    (add_mem (hcl _ (hW1 kk)) (mul_mem (hW1 kk) hrm))) (mul_mem (hcl _ (hW0 kk)) (hW1 kk))) (hNm' kk)
  have hEm : ∀ kk, Ek kk ∈ C⟮S.x⟯ := fun kk ↦ div_mem (sub_mem (mul_mem (hW0 kk) (hcl _ (hW0 kk)))
    (mul_mem (mul_mem (hW1 kk) (add_mem (hcl _ (hW1 kk)) (mul_mem (hW1 kk) hrm))) hPm)) (hNm' kk)
  simp only [hab] at heq'
  have heq2 : (b - ∑ kk, algebraMap C L (Es kk) * Bk kk) * S.y ^ 1 =
      v′ + (Gs + ∑ kk, algebraMap C L (Es kk) * Ek kk) := by
    rw [pow_one, sub_mul, Finset.sum_mul]
    rw [heq']
    simp only [mul_add, Finset.sum_add_distrib]
    have : ∑ kk, algebraMap C L (Es kk) * (Bk kk * S.y) = ∑ kk, algebraMap C L (Es kk) * Bk kk * S.y :=
      Finset.sum_congr rfl fun kk _ ↦ by ring
    rw [this]
    ring
  obtain ⟨a, ha, hae⟩ := S.exact_of_even (ω) hx 1 one_pos (by omega) _
    (sub_mem hb (sum_mem fun kk _ ↦ mul_mem (IntermediateField.algebraMap_mem _ _) (hBm kk))) v hv _
    (add_mem hGs (sum_mem fun kk _ ↦ mul_mem (IntermediateField.algebraMap_mem _ _) (hEm kk))) heq2
  refine ⟨a, ha, Es, hEs, ?_⟩
  simp only [pow_one] at hae
  rw [show ∑ kk, algebraMap C L (Es kk) * (Bk kk * S.y) = (∑ kk, algebraMap C L (Es kk) * Bk kk) * S.y by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun kk _ ↦ by ring]
  linear_combination hae


end Tail

section Aux

variable (hn2 : S.n = 2) (β₀ : K) (hβ₀ : β₀ ≠ 0)
  (hv0 : β₀ ^ S.n = (S.p.map (algebraMap C K)).eval 0)

include hn2 hβ₀ hv0 in
/-- `Z₀ = W₀² x^{−N₀}` has divisor `N₀ δ₀` when `W₀` has divisor `N₀ P₊`. -/
lemma ordAt_Z0 (W₀ : C⟮S.x⟯⟮S.y⟯) (hW₀ : W₀ ≠ 0) (N₀ : ℕ)
    (hord : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K W₀ α β' = N₀ * gammaP β₀ (α, β')) :
    W₀ ^ 2 * S.xE ^ (-(N₀ : ℤ)) ≠ 0 ∧ ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      (S.ordAt K (W₀ ^ 2 * S.xE ^ (-(N₀ : ℤ))) α β' : ℚ) = N₀ * dZ β₀ (α, β') := by
  have hxp : S.xE ^ (-(N₀ : ℤ)) ≠ 0 := zpow_ne_zero _ S.xE_ne
  refine ⟨mul_ne_zero (pow_ne_zero _ hW₀) hxp, fun α β' hv ↦ ?_⟩
  rw [S.ordAt_mul hv (pow_ne_zero _ hW₀) hxp, S.ordAt_pow hv, S.ordAt_zpow hv, S.ordAt_xE α β' hv,
    hord α β' hv, gammaP_apply]
  by_cases hα : α = 0
  · subst hα
    have hβ' : β' ≠ 0 := by
      intro h0; rw [h0, zero_pow S.hn.ne', ← hv0] at hv
      exact hβ₀ (pow_eq_zero_iff S.hn.ne' |>.mp hv.symm)
    rcases S.over_zero' hn2 β₀ hv0 β' hv with h | h
    · rw [h, dZ_plus β₀ hβ₀]; simp [hβ₀]; ring
    · rw [h, dZ_minus β₀ hβ₀]; simp [hβ₀, neg_ne_self hβ₀]
  · rw [dZ_off β₀ α β' hα]; simp [hα]

end Aux

section LogD

variable (ω : C[X]) (hx : S.x′ = aeval S.x ω)

include hx in
lemma ld_zK {r nk : ℕ} (c : Fin r → C) (m : Fin r → ℕ) (cl : Fin r → Fin nk) (kk : Fin nk)
    (W : C⟮S.x⟯⟮S.y⟯) (hW : W ≠ 0) (N : ℕ) : ∃ G ∈ C⟮S.x⟯,
      logDeriv ((S.zK c m cl kk W N : C⟮S.x⟯⟮S.y⟯) : L) = 2 * logDeriv (W : L) + G := by
  have hcl : DerivClosed C⟮S.x⟯ := S.derivClosedXW ω hx
  have hmemx : ∀ Q : C[X], aeval S.x Q ∈ C⟮S.x⟯ := fun Q ↦ by
    letI := algebraAdjoinSimple (F := C) S.x
    rw [← algebraMap_adjoinSimple (F := C) S.x Q]; exact SetLike.coe_mem _
  have hWL : (W : L) ≠ 0 := fun h ↦ hW (Subtype.ext h)
  have hXL : ∀ q, ((S.polyX (X - Polynomial.C (c q)) : C⟮S.x⟯⟮S.y⟯) : L) ≠ 0 := fun q h ↦
    S.polyX_ne_zero (X_sub_C_ne_zero (c q)) (Subtype.ext h)
  have e1 : ((S.zK c m cl kk W N : C⟮S.x⟯⟮S.y⟯) : L) = (W : L) ^ 2 *
      ∏ q, ((S.polyX (X - Polynomial.C (c q)) : C⟮S.x⟯⟮S.y⟯) : L) ^ (-((N * mK m cl kk q : ℕ) : ℤ)) := by
    rw [zK, IntermediateField.coe_mul, IntermediateField.coe_pow]
    congr 1
    rw [show ((∏ q, S.polyX (X - Polynomial.C (c q)) ^ (-((N * mK m cl kk q : ℕ) : ℤ)) :
        C⟮S.x⟯⟮S.y⟯) : L) = ∏ q, ((S.polyX (X - Polynomial.C (c q)) ^
          (-((N * mK m cl kk q : ℕ) : ℤ)) : C⟮S.x⟯⟮S.y⟯) : L) from map_prod (C⟮S.x⟯⟮S.y⟯).val _ _]
    exact Finset.prod_congr rfl fun q _ ↦ map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val _ _
  refine ⟨∑ q, ((-((N * mK m cl kk q : ℕ) : ℤ) : ℤ) : L) *
    logDeriv ((S.polyX (X - Polynomial.C (c q)) : C⟮S.x⟯⟮S.y⟯) : L), sum_mem fun q _ ↦ ?_, ?_⟩
  · refine mul_mem (intCast_mem _ _) ?_
    rw [S.polyX_coe]
    exact div_mem (hcl _ (hmemx _)) (hmemx _)
  · rw [e1, logDeriv_mul (a := (W : L) ^ 2) (b := ∏ q, ((S.polyX (X - Polynomial.C (c q)) :
        C⟮S.x⟯⟮S.y⟯) : L) ^ (-((N * mK m cl kk q : ℕ) : ℤ))) (pow_ne_zero _ hWL)
      (Finset.prod_ne_zero_iff.mpr fun q _ ↦ zpow_ne_zero _ (hXL q)), logDeriv_pow,
      logDeriv_prod _ _ _ (fun q _ ↦ zpow_ne_zero _ (hXL q))]
    simp only [fun q ↦ logDeriv_zpow' _ (hXL q)]
    push_cast
    ring

end LogD

/-- `x′/x = η` for `x′ = η x`. -/
lemma logDeriv_xE (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η * X)) :
    logDeriv ((S.xE : C⟮S.x⟯⟮S.y⟯) : L) = algebraMap C L η := by
  rw [S.xE_val, logDeriv, hx, map_mul, aeval_C, aeval_X, mul_div_assoc, div_self S.x_ne_zero,
    mul_one]

section ExpMain

variable (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η * X))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
  (hgood : ∀ α : K, ¬ α = 0 → α′ ≠ ((Polynomial.C η * X).map (algebraMap C K)).eval α)
  (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
  {r nk : ℕ} (c β : Fin r → C) (hc : Function.Injective c) (hc0 : ∀ q, c q ≠ 0)
  (hβ : ∀ q, β q ≠ 0 ∧ β q ^ S.n = S.p.eval (c q)) (m : Fin r → ℕ) (cl : Fin r → Fin nk)
  (ρ : Fin nk → C)
  (P : C[X]) (l : ℕ) (b : L) (hb : b ∈ C⟮S.x⟯)
  (D : C[X]) (R : Fin r → C[X]) (hDR : ∀ q, D = (X - Polynomial.C (c q)) * R q)
  (hRne : ∀ q, (R q).eval (c q) ≠ 0)
  (hDoff : ∀ α : K, ¬ α = 0 → (∀ q, α ≠ algebraMap C K (c q)) → (D.map (algebraMap C K)).eval α ≠ 0)
  (hbP : b * aeval S.x (D * S.p ^ l) = aeval S.x P)
  (hres : ∀ q, P.eval (c q) * β q = m q * ρ (cl q) * ((Polynomial.C η * X).eval (c q) - (c q)′) *
    (R q * S.p ^ l).eval (c q))
  (hn2 : S.n = 2) (hcop : Nat.Coprime S.n S.p.natDegree) (β₀ : K) (hβ₀ : β₀ ≠ 0)
  (hv0 : β₀ ^ S.n = (S.p.map (algebraMap C K)).eval 0)

include hc0 in
lemma hbadc_of : ∀ q, ¬ (algebraMap C K (c q) = 0) := fun q h ↦
  hc0 q ((algebraMap C K).injective (by rw [h, map_zero]))

include hx hK hgood hconstC hc hc0 hβ hb hDR hRne hDoff hbP hres hn2 hcop hβ₀ hv0 in
/-- **With a witness of `N₀ P₊` and one for every class**, a Liouville form for `b y` forces
`b y = (a y)′ + ∑ e_i B_i y` (the `B_i` of `W₀` and of the class witnesses). -/
theorem kxe_tors_W0 (N₀ : ℕ) (hN₀ : 0 < N₀) (W₀ : C⟮S.x⟯⟮S.y⟯) (hW₀ : W₀ ≠ 0)
    (hW₀ord : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K W₀ α β' = N₀ * gammaP β₀ (α, β'))
    (N : Fin nk → ℕ) (hN : ∀ kk, 0 < N kk) (W : Fin nk → C⟮S.x⟯⟮S.y⟯) (hW : ∀ kk, W kk ≠ 0)
    (hWord : ∀ kk, ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K (W kk) α β' = N kk * gammaQ c β (mK m cl kk) (α, β'))
    (W0 W1 : Fin (nk + 1) → L) (hW0 : ∀ i, W0 i ∈ C⟮S.x⟯) (hW1 : ∀ i, W1 i ∈ C⟮S.x⟯)
    (hWe : ∀ i, ((Fin.cons W₀ W : Fin (nk + 1) → C⟮S.x⟯⟮S.y⟯) i : L) = W0 i + W1 i * S.y)
    (hNm : ∀ i, W0 i ^ 2 - W1 i ^ 2 * aeval S.x S.p ≠ 0) (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) :
    ∃ a ∈ C⟮S.x⟯, ∃ e : Fin (nk + 1) → C, (∀ i, (algebraMap C L (e i))′ = 0) ∧
      b * S.y = (a * S.y)′ + ∑ i, algebraMap C L (e i) *
        ((W0 i * ((W1 i)′ + W1 i * (aeval S.x (mapCoeffs S.p + Polynomial.C η * X * derivative S.p) /
          ((S.n : L) * aeval S.x S.p))) - (W0 i)′ * W1 i) /
          (W0 i ^ 2 - W1 i ^ 2 * aeval S.x S.p) * S.y) := by
  classical
  obtain ⟨k, d, w, hw, heq', hdc, -, lam, hord, -⟩ :=
    S.kxm_core (K := K) (Polynomial.C η * X) hx hK (fun α ↦ α = 0) hgood hconstC c β hc
      (hbadc_of c hc0) hβ m cl ρ P l b hb D R hDR hRne hDoff hbP hres hn2 hbm s cs u hcs hu v hv heq
  have hcl : DerivClosed C⟮S.x⟯ := S.derivClosedXW (Polynomial.C η * X) hx
  obtain ⟨hZ0ne, hZ0o⟩ := S.ordAt_Z0 hn2 β₀ hβ₀ hv0 W₀ hW₀ N₀ hW₀ord
  have hW₀L : (W₀ : L) ≠ 0 := fun h ↦ hW₀ (Subtype.ext h)
  have hldZ0 : logDeriv (((W₀ ^ 2 * S.xE ^ (-(N₀ : ℤ)) : C⟮S.x⟯⟮S.y⟯)) : L) =
      2 * logDeriv (W₀ : L) - (N₀ : L) * algebraMap C L η := by
    have hxL : ((S.xE : C⟮S.x⟯⟮S.y⟯) : L) ≠ 0 := by rw [S.xE_val]; exact S.x_ne_zero
    rw [IntermediateField.coe_mul, IntermediateField.coe_pow,
      show ((S.xE ^ (-(N₀ : ℤ)) : C⟮S.x⟯⟮S.y⟯) : L) = ((S.xE : C⟮S.x⟯⟮S.y⟯) : L) ^ (-(N₀ : ℤ)) from
        map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val _ _,
      logDeriv_mul _ _ (pow_ne_zero _ hW₀L) (zpow_ne_zero _ hxL), logDeriv_pow, logDeriv_zpow' _ hxL,
      S.logDeriv_xE η hx]
    push_cast; ring
  have hZ := fun kk ↦ S.ld_zK (Polynomial.C η * X) hx c m cl kk (W kk) (hW kk) (N kk)
  choose GZ hGZ hGZe using hZ
  have hlog : ∀ j < k, ∃ (e : Fin (nk + 1) → ℚ) (G : L), G ∈ C⟮S.x⟯ ∧
      logDeriv (w j) = ∑ i, (e i : L) *
        logDeriv (((Fin.cons W₀ W : Fin (nk + 1) → C⟮S.x⟯⟮S.y⟯) i : C⟮S.x⟯⟮S.y⟯) : L) + G := by
    intro j hj
    set wj : C⟮S.x⟯⟮S.y⟯ := ⟨w j, (hw j hj).1⟩
    have hwj0 : wj ≠ 0 := fun h ↦ (hw j hj).2 (congrArg Subtype.val h)
    obtain ⟨hz0, hzo⟩ := S.kxe_norm hn2 β₀ hβ₀ hv0 c β hc0 m cl wj hwj0 (fun kk ↦ lam kk j)
      (fun α β' hv hα ↦ hord j hj α β' hv hα)
    set rr := S.ordAt K wj 0 β₀
    set ss := S.ordAt K wj 0 (-β₀)
    set z := wj ^ 2 * S.xE ^ (-(rr + ss))
    obtain ⟨e', g, heg⟩ := S.kqm_log_gen (K := K) hcop z hz0
      (Fin.cons (W₀ ^ 2 * S.xE ^ (-(N₀ : ℤ))) (fun kk ↦ S.zK c m cl kk (W kk) (N kk)))
      (fun i ↦ Fin.cases hZ0ne (fun kk ↦ (S.ordAt_zK c β hc hβ m hn2 cl kk (W kk) (hW kk) (N kk)
        (hWord kk)).1) i)
      (Fin.cons N₀ N) (fun i ↦ Fin.cases hN₀ hN i)
      (Fin.cons ((rr - ss : ℤ) : ℚ) (fun kk ↦ 2 * lam kk j))
      (Fin.cons (dZ β₀) (fun kk ↦ dK c β m cl kk))
      (fun α β' hv ↦ by
        rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hzo α β' hv, add_comm])
      (fun i ↦ Fin.cases (fun α β' hv ↦ by simpa using hZ0o α β' hv)
        (fun kk α β' hv ↦ by
          simpa using (S.ordAt_zK c β hc hβ m hn2 cl kk (W kk) (hW kk) (N kk) (hWord kk)).2 α β' hv) i)
    -- `w′/w = ½ z′/z + ½ (r + s) η`
    have hwL : (w j) ≠ 0 := (hw j hj).2
    have hxL : ((S.xE : C⟮S.x⟯⟮S.y⟯) : L) ≠ 0 := by rw [S.xE_val]; exact S.x_ne_zero
    have hzL : logDeriv ((z : C⟮S.x⟯⟮S.y⟯) : L) = 2 * logDeriv (w j) -
        ((rr + ss : ℤ) : L) * algebraMap C L η := by
      simp only [z]
      rw [IntermediateField.coe_mul, IntermediateField.coe_pow,
        show ((S.xE ^ (-(rr + ss)) : C⟮S.x⟯⟮S.y⟯) : L) = ((S.xE : C⟮S.x⟯⟮S.y⟯) : L) ^ (-(rr + ss)) from
          map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val _ _,
        logDeriv_mul _ _ (pow_ne_zero _ hwL) (zpow_ne_zero _ hxL), logDeriv_pow, logDeriv_zpow' _ hxL,
        S.logDeriv_xE η hx]
      push_cast; ring
    rw [Fin.sum_univ_succ] at heg
    simp only [Fin.cons_zero, Fin.cons_succ, hldZ0] at heg
    refine ⟨fun i ↦ Fin.cases (e' 0) (fun kk ↦ e' kk.succ) i,
      (algebraMap C L g + ((rr + ss : ℤ) : L) * algebraMap C L η -
        (e' 0 : L) * ((N₀ : L) * algebraMap C L η) + ∑ kk, (e' kk.succ : L) * GZ kk) / 2, ?_, ?_⟩
    · refine div_mem (add_mem (sub_mem (add_mem (IntermediateField.algebraMap_mem _ _)
        (mul_mem (intCast_mem _ _) (IntermediateField.algebraMap_mem _ _)))
        (mul_mem (SubfieldClass.ratCast_mem _ _) (mul_mem (IntermediateField.natCast_mem _ _)
          (IntermediateField.algebraMap_mem _ _))))
        (sum_mem fun kk _ ↦ mul_mem (SubfieldClass.ratCast_mem _ _) (hGZ kk))) (ofNat_mem _ 2)
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ, Fin.cons_zero, Fin.cons_succ]
      simp only [hGZe] at heg
      have h2 : logDeriv (w j) = (logDeriv ((z : C⟮S.x⟯⟮S.y⟯) : L) +
          ((rr + ss : ℤ) : L) * algebraMap C L η) / 2 := by rw [hzL]; ring
      rw [h2, heg]
      simp only [mul_add, Finset.sum_add_distrib, mul_sub]
      field_simp
      simp only [mul_add, Finset.mul_sum, ← mul_assoc]
      ring
  obtain ⟨a, ha, e, he, hae⟩ := S.kxm_tail (Polynomial.C η * X) hx hn2 _ W0 W1 hW0 hW1 hWe hNm
    b hb v hv k d w heq' hdc hlog
  exact ⟨a, ha, e, he, hae⟩

end ExpMain

end SuperData

end Differential
