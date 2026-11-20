import RischTragerBronstein.Mixed.KXExp
import RischTragerBronstein.Mixed.KXSym

/-!
# The exponential level: the `δ₀` part of the logarithms

The divisor of a normalized logarithm is `∑_k L_k Δ_k + μ δ₀`, `δ₀ = P₊ − P₋`.

* `kx_kill_gen`: the class parts can be killed by the class witnesses, leaving `D μ δ₀`;
* `kxe_mu0_sym`: if `√p(0) ∉ C` then `μ = 0` (`ordAt_pm`);
* `kxe_mu0_nt`: if all classes are torsion and `P₊ − ∞` is not, then `μ = 0`;
* `kxe_kill_W0`: a witness of `N₀ P₊` kills `μ δ₀`;
* `kxe_tors_mu0`: with `μ = 0` forced and all classes torsion, `b y = (a y)′ + ∑ e_k B_k y`;
* `kxe_nontors`: when `δ₀` can be killed, a non-torsion class with a non-zero residue gives
  no Liouville form.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries Classical

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L)

section Kill

variable (hcop : Nat.Coprime S.n S.p.natDegree)

/-- **Killing the class parts of a divisor.** -/
theorem kx_kill_gen {n : ℕ} (z : C⟮S.x⟯⟮S.y⟯) (hz : z ≠ 0) (Z : Fin n → C⟮S.x⟯⟮S.y⟯)
    (hZ : ∀ k, Z k ≠ 0) (N : Fin n → ℕ) (hN : ∀ k, 0 < N k) (L' : Fin n → ℚ)
    (δ : Fin n → K × K → ℚ) (ε : K × K → ℚ) (μ : ℤ)
    (hzo : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      (S.ordAt K z α β' : ℚ) = ∑ k, L' k * δ k (α, β') + μ * ε (α, β'))
    (hZo : ∀ k, ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      (S.ordAt K (Z k) α β' : ℚ) = N k * δ k (α, β')) :
    ∃ Dn : ℕ, 0 < Dn ∧ ∃ y : C⟮S.x⟯⟮S.y⟯, y ≠ 0 ∧ ∀ α β' : K,
      β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      (S.ordAt K y α β' : ℚ) = (Dn * μ : ℚ) * ε (α, β') := by
  obtain ⟨D, hD0, A, hA⟩ := exists_int_mul L'
  set NN : ℕ := ∏ k, N k with hNN
  have hNN0 : 0 < NN := Finset.prod_pos fun k _ ↦ hN k
  have hdiv : ∀ k, N k ∣ NN := fun k ↦ Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
  set E : Fin n → ℤ := fun k ↦ -(A k * ((NN / N k : ℕ) : ℤ)) with hE
  set y1 := z ^ (D * NN) * ∏ k, Z k ^ E k with hy1
  have hzp : z ^ (D * NN) ≠ 0 := pow_ne_zero _ hz
  have hpr : ∏ k, Z k ^ E k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (hZ k)
  refine ⟨D * NN, Nat.mul_pos hD0 hNN0, y1, mul_ne_zero hzp hpr, fun α β' hv ↦ ?_⟩
  rw [S.ordAt_mul hv hzp hpr, S.ordAt_pow hv,
    S.ordAt_prod hv _ _ (fun k _ ↦ zpow_ne_zero _ (hZ k))]
  push_cast
  rw [hzo α β' hv]
  simp only [S.ordAt_zpow hv, Int.cast_mul, hZo _ α β' hv, hE]
  rw [mul_add, Finset.mul_sum, add_comm, ← add_assoc, ← Finset.sum_add_distrib]
  rw [Finset.sum_eq_zero fun k _ ↦ ?_]
  · ring
  have hk : ((NN / N k : ℕ) : ℚ) * N k = NN := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel (hdiv k)]
  simp only [Int.cast_neg, Int.cast_mul, Int.cast_natCast]
  rw [hA k]
  linear_combination (-(D : ℚ) * L' k * δ k (α, β')) * hk

end Kill

section Mu

variable (hn2 : S.n = 2) (β₀ : K) (hβ₀ : β₀ ≠ 0)
  (hv0 : β₀ ^ S.n = (S.p.map (algebraMap C K)).eval 0)
  {r nk : ℕ} (c β : Fin r → C) (hc : Function.Injective c) (hc0 : ∀ q, c q ≠ 0)
  (hβ : ∀ q, β q ≠ 0 ∧ β q ^ S.n = S.p.eval (c q)) (m : Fin r → ℕ) (cl : Fin r → Fin nk)

/-- The divisor of `f` is `∑_k L_k Δ_k + μ δ₀`. -/
def DivKZ (f : C⟮S.x⟯⟮S.y⟯) (L' : Fin nk → ℚ) (μ : ℤ) : Prop :=
  ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
    (S.ordAt K f α β' : ℚ) = ∑ k, L' k * dK c β m cl k (α, β') + μ * dZ β₀ (α, β')

include hn2 hβ₀ hv0 hc0 in
/-- **`μ = 0` when `√p(0) ∉ C`.** -/
theorem kxe_mu0_sym (hns : ∀ c : C, algebraMap C K c ≠ β₀) (f : C⟮S.x⟯⟮S.y⟯) (hf : f ≠ 0)
    (L' : Fin nk → ℚ) (μ : ℤ) (hfo : S.DivKZ β₀ c β m cl f L' μ) : μ = 0 := by
  have hvM : (-β₀) ^ S.n = (S.p.map (algebraMap C K)).eval 0 := by
    rw [hn2, neg_sq, ← hn2]; exact hv0
  have h1 := hfo 0 β₀ hv0
  have h2 := hfo 0 (-β₀) hvM
  simp only [dK_zero c β hc0 m cl, mul_zero, Finset.sum_const_zero, zero_add] at h1 h2
  rw [dZ_plus β₀ hβ₀] at h1
  rw [dZ_minus β₀ hβ₀] at h2
  rw [S.ordAt_pm hn2 β₀ hβ₀ hv0 hns f hf, h2] at h1
  have : (μ : ℚ) = 0 := by linarith
  exact_mod_cast this

include hn2 hβ₀ hv0 hc hc0 hβ in
/-- **`μ = 0` when every class is torsion and `P₊ − ∞` is not** (`β₀ = b₀ ∈ C`). -/
theorem kxe_mu0_nt (hcop : Nat.Coprime S.n S.p.natDegree) (b₀ : C) (hb₀ : b₀ ≠ 0 ∧ b₀ ^ S.n = S.p.eval 0)
    (hβb : algebraMap C K b₀ = β₀)
    (hnp : ∀ N : ℕ, 0 < N → ¬ S.IsPrincipalS K
      (gammaQ (fun _ : Fin 1 ↦ (0 : C)) (fun _ ↦ b₀) (fun _ ↦ 1)) N)
    (N : Fin nk → ℕ) (hN : ∀ kk, 0 < N kk) (W : Fin nk → C⟮S.x⟯⟮S.y⟯) (hW : ∀ kk, W kk ≠ 0)
    (hWord : ∀ kk, ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K (W kk) α β' = N kk * gammaQ c β (mK m cl kk) (α, β'))
    (f : C⟮S.x⟯⟮S.y⟯) (hf : f ≠ 0)
    (L' : Fin nk → ℚ) (μ : ℤ) (hfo : S.DivKZ β₀ c β m cl f L' μ) : μ = 0 := by
  by_contra hμ
  obtain ⟨Dn, hDn, y, hy, hyo⟩ := S.kx_kill_gen f hf (fun kk ↦ S.zK c m cl kk (W kk) (N kk))
    (fun kk ↦ (S.ordAt_zK c β hc hβ m hn2 cl kk (W kk) (hW kk) (N kk) (hWord kk)).1) N hN L'
    (fun kk ↦ dK c β m cl kk) (dZ β₀) μ hfo
    (fun kk ↦ (S.ordAt_zK c β hc hβ m hn2 cl kk (W kk) (hW kk) (N kk) (hWord kk)).2)
  have hlam : ((Dn * μ : ℤ) : ℚ) ≠ 0 := by
    have : (Dn : ℤ) * μ ≠ 0 := mul_ne_zero (by exact_mod_cast hDn.ne') hμ
    exact_mod_cast this
  have hform : S.OrdForm (K := K) (fun _ : Fin 1 ↦ (0 : C)) (fun _ ↦ b₀) (fun _ ↦ 1) y
      ((Dn * μ : ℤ) : ℚ) := by
    refine ⟨fun α β' hv hα ↦ ?_, fun q ↦ ⟨?_, ?_⟩⟩
    · have := hyo α β' hv
      rw [dZ_off β₀ α β' (by simpa using hα 0), mul_zero] at this
      exact_mod_cast this
    · rw [map_zero, hβb, hyo 0 β₀ hv0, dZ_plus β₀ hβ₀]; push_cast; ring
    · rw [map_zero, hβb, hyo 0 (-β₀) (by rw [hn2, neg_sq, ← hn2]; exact hv0),
        dZ_minus β₀ hβ₀]; push_cast; ring
  obtain ⟨N', hN', hP⟩ := S.kq_log_nontors (fun _ : Fin 1 ↦ (0 : C)) (fun _ ↦ b₀)
    (fun i j _ ↦ Subsingleton.elim i j) (fun _ ↦ hb₀) (fun _ ↦ 1) hn2 y hy _ hlam hform
  exact hnp N' hN' hP

include hn2 hβ₀ hv0 in
/-- **A witness of `N₀ P₊` kills `μ δ₀`.** -/
theorem kxe_kill_W0 (N₀ : ℕ) (hN₀ : 0 < N₀) (W₀ : C⟮S.x⟯⟮S.y⟯) (hW₀ : W₀ ≠ 0)
    (hW₀ord : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K W₀ α β' = N₀ * gammaP β₀ (α, β'))
    (f : C⟮S.x⟯⟮S.y⟯) (hf : f ≠ 0) (L' : Fin nk → ℚ) (μ : ℤ)
    (hfo : S.DivKZ β₀ c β m cl f L' μ) :
    ∃ M : ℕ, 0 < M ∧ ∃ g : C⟮S.x⟯⟮S.y⟯, g ≠ 0 ∧ S.DivKZ β₀ c β m cl g (fun k ↦ M * L' k) 0 := by
  obtain ⟨hZ0, hZ0o⟩ := S.ordAt_Z0 hn2 β₀ hβ₀ hv0 W₀ hW₀ N₀ hW₀ord
  have hA : f ^ N₀ ≠ 0 := pow_ne_zero _ hf
  have hB : (W₀ ^ 2 * S.xE ^ (-(N₀ : ℤ))) ^ (-μ) ≠ 0 := zpow_ne_zero _ hZ0
  refine ⟨N₀, hN₀, f ^ N₀ * (W₀ ^ 2 * S.xE ^ (-(N₀ : ℤ))) ^ (-μ), mul_ne_zero hA hB,
    fun α β' hv ↦ ?_⟩
  rw [S.ordAt_mul hv hA hB, S.ordAt_pow hv, S.ordAt_zpow hv]
  push_cast
  rw [hfo α β' hv, hZ0o α β' hv, mul_add, Finset.mul_sum]
  simp only [zero_mul, add_zero, mul_assoc]
  ring

end Mu

section ExpMain2

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

include hx hK hgood hconstC hc hc0 hβ hb hDR hRne hDoff hbP hres hn2 hcop hβ₀ hv0 in
/-- **When `μ = 0` is forced and every class is torsion**, a Liouville form for `b y` forces
`b y = (a y)′ + ∑ e_k B_k y`. -/
theorem kxe_tors_mu0
    (hmu0 : ∀ f : C⟮S.x⟯⟮S.y⟯, f ≠ 0 → ∀ (L' : Fin nk → ℚ) (μ : ℤ),
      S.DivKZ β₀ c β m cl f L' μ → μ = 0)
    (N : Fin nk → ℕ) (hN : ∀ kk, 0 < N kk) (W : Fin nk → C⟮S.x⟯⟮S.y⟯) (hW : ∀ kk, W kk ≠ 0)
    (hWord : ∀ kk, ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K (W kk) α β' = N kk * gammaQ c β (mK m cl kk) (α, β'))
    (W0 W1 : Fin nk → L) (hW0 : ∀ i, W0 i ∈ C⟮S.x⟯) (hW1 : ∀ i, W1 i ∈ C⟮S.x⟯)
    (hWe : ∀ i, (W i : L) = W0 i + W1 i * S.y)
    (hNm : ∀ i, W0 i ^ 2 - W1 i ^ 2 * aeval S.x S.p ≠ 0) (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) :
    ∃ a ∈ C⟮S.x⟯, ∃ e : Fin nk → C, (∀ i, (algebraMap C L (e i))′ = 0) ∧
      b * S.y = (a * S.y)′ + ∑ i, algebraMap C L (e i) *
        ((W0 i * ((W1 i)′ + W1 i * (aeval S.x (mapCoeffs S.p + Polynomial.C η * X * derivative S.p) /
          ((S.n : L) * aeval S.x S.p))) - (W0 i)′ * W1 i) /
          (W0 i ^ 2 - W1 i ^ 2 * aeval S.x S.p) * S.y) := by
  classical
  obtain ⟨k, d, w, hw, heq', hdc, -, lam, hord, -⟩ :=
    S.kxm_core (K := K) (Polynomial.C η * X) hx hK (fun α ↦ α = 0) hgood hconstC c β hc
      (hbadc_of c hc0) hβ m cl ρ P l b hb D R hDR hRne hDoff hbP hres hn2 hbm s cs u hcs hu v hv heq
  have hZ := fun kk ↦ S.ld_zK (Polynomial.C η * X) hx c m cl kk (W kk) (hW kk) (N kk)
  choose GZ hGZ hGZe using hZ
  have hlog : ∀ j < k, ∃ (e : Fin nk → ℚ) (G : L), G ∈ C⟮S.x⟯ ∧
      logDeriv (w j) = ∑ i, (e i : L) * logDeriv (W i : L) + G := by
    intro j hj
    set wj : C⟮S.x⟯⟮S.y⟯ := ⟨w j, (hw j hj).1⟩
    have hwj0 : wj ≠ 0 := fun h ↦ (hw j hj).2 (congrArg Subtype.val h)
    obtain ⟨hz0, hzo⟩ := S.kxe_norm hn2 β₀ hβ₀ hv0 c β hc0 m cl wj hwj0 (fun kk ↦ lam kk j)
      (fun α β' hv hα ↦ hord j hj α β' hv hα)
    set rr := S.ordAt K wj 0 β₀
    set ss := S.ordAt K wj 0 (-β₀)
    set z := wj ^ 2 * S.xE ^ (-(rr + ss))
    have hmu := hmu0 z hz0 _ _ hzo
    obtain ⟨e', g, heg⟩ := S.kqm_log_gen (K := K) hcop z hz0
      (fun kk ↦ S.zK c m cl kk (W kk) (N kk))
      (fun kk ↦ (S.ordAt_zK c β hc hβ m hn2 cl kk (W kk) (hW kk) (N kk) (hWord kk)).1)
      N hN (fun kk ↦ 2 * lam kk j) (fun kk ↦ dK c β m cl kk)
      (fun α β' hv ↦ by rw [hzo α β' hv, hmu]; simp)
      (fun kk ↦ (S.ordAt_zK c β hc hβ m hn2 cl kk (W kk) (hW kk) (N kk) (hWord kk)).2)
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
    refine ⟨e', (algebraMap C L g + ((rr + ss : ℤ) : L) * algebraMap C L η +
        ∑ kk, (e' kk : L) * GZ kk) / 2, ?_, ?_⟩
    · exact div_mem (add_mem (add_mem (IntermediateField.algebraMap_mem _ _)
        (mul_mem (intCast_mem _ _) (IntermediateField.algebraMap_mem _ _)))
        (sum_mem fun kk _ ↦ mul_mem (SubfieldClass.ratCast_mem _ _) (hGZ kk))) (ofNat_mem _ 2)
    · simp only [hGZe] at heg
      have h2 : logDeriv (w j) = (logDeriv ((z : C⟮S.x⟯⟮S.y⟯) : L) +
          ((rr + ss : ℤ) : L) * algebraMap C L η) / 2 := by rw [hzL]; ring
      rw [h2, heg]
      simp only [mul_add, Finset.sum_add_distrib]
      field_simp
      simp only [mul_add, Finset.mul_sum, ← mul_assoc]
      ring
  obtain ⟨a, ha, e, he, hae⟩ := S.kxm_tail (Polynomial.C η * X) hx hn2 W W0 W1 hW0 hW1 hWe hNm
    b hb v hv k d w heq' hdc hlog
  exact ⟨a, ha, e, he, hae⟩

include hx hK hgood hconstC hc hc0 hβ hb hDR hRne hDoff hbP hres hn2 hβ₀ hv0 in
/-- **When `δ₀` can be killed, a non-torsion class carrying a non-zero residue leaves no
Liouville form.** -/
theorem kxe_nontors (k0 : Fin nk) (hk0 : ∃ q, cl q = k0 ∧ m q ≠ 0)
    (hρ : ∀ e : Fin nk → ℚ, ∑ kk, (e kk : C) * ρ kk = 0 → ∀ kk, e kk = 0)
    (hnt : ∀ N : ℕ, 0 < N → ¬ S.IsPrincipalS K (gammaQ c β (mK m cl k0)) N)
    (hkill : ∀ f : C⟮S.x⟯⟮S.y⟯, f ≠ 0 → ∀ (L' : Fin nk → ℚ) (μ : ℤ),
      S.DivKZ β₀ c β m cl f L' μ →
      ∃ M : ℕ, 0 < M ∧ ∃ g : C⟮S.x⟯⟮S.y⟯, g ≠ 0 ∧ S.DivKZ β₀ c β m cl g (fun k ↦ M * L' k) 0)
    (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    {ι : Type*} (s : Finset ι) (cs u : ι → L) (hcs : ∀ i ∈ s, (cs i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, cs i * logDeriv (u i)) : False := by
  classical
  obtain ⟨k, d, w, hw, -, -, -, lam, hord, hsum⟩ :=
    S.kxm_core (K := K) (Polynomial.C η * X) hx hK (fun α ↦ α = 0) hgood hconstC c β hc
      (hbadc_of c hc0) hβ m cl ρ P l b hb D R hDR hRne hDoff hbP hres hn2 hbm s cs u hcs hu v hv heq
  set wj : Fin k → C⟮S.x⟯⟮S.y⟯ := fun j ↦ ⟨w j, (hw j j.2).1⟩ with hwj
  have hwj0 : ∀ j, wj j ≠ 0 := fun j h ↦ (hw j j.2).2 (congrArg Subtype.val h)
  -- the normalized, `δ₀`-free logarithms
  have hg : ∀ j : Fin k, ∃ M : ℕ, 0 < M ∧ ∃ g : C⟮S.x⟯⟮S.y⟯, g ≠ 0 ∧
      S.DivKZ β₀ c β m cl g (fun kk ↦ M * (2 * lam kk j)) 0 := fun j ↦ by
    obtain ⟨hz0, hzo⟩ := S.kxe_norm hn2 β₀ hβ₀ hv0 c β hc0 m cl (wj j) (hwj0 j)
      (fun kk ↦ lam kk j) (fun α β' hv hα ↦ hord j j.2 α β' hv hα)
    exact hkill _ hz0 _ _ hzo
  choose M hM g hg0 hgo using hg
  obtain ⟨φ, hφ⟩ := _root_.exists_sep_functional (ρ := ρ) hρ
  set t : Fin k → ℚ := fun j ↦ φ (d j) k0 with ht
  obtain ⟨Dn, hD0, A, hA⟩ := exists_int_mul (fun j ↦ t j / (2 * M j))
  set z := ∏ j, g j ^ A j with hz
  have hz0 : z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ ↦ zpow_ne_zero _ (hg0 j)
  have hcoef : ∀ kk, (∃ q, cl q = kk ∧ m q ≠ 0) →
      ∑ j : Fin k, (A j : ℚ) * (M j * (2 * lam kk j)) = if kk = k0 then (Dn : ℚ) else 0 := by
    intro kk hkk
    have hs := hsum kk hkk
    have hφs := congrArg (fun x ↦ φ x k0) hs
    simp only [map_sum, hφ kk] at hφs
    have e1 : ∑ j ∈ Finset.range k, (φ ((lam kk j : C) * d j)) k0 =
        ∑ j : Fin k, lam kk j * t j := by
      rw [← Fin.sum_univ_eq_sum_range (fun j ↦ (φ ((lam kk j : C) * d j)) k0)]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← Rat.smul_def, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_apply, e1] at hφs
    simp only [Pi.single_apply] at hφs
    have e2 : ∀ j : Fin k, (A j : ℚ) * (M j * (2 * lam kk j)) = Dn * (lam kk j * t j) := fun j ↦ by
      have hMj : (M j : ℚ) ≠ 0 := by exact_mod_cast (hM j).ne'
      rw [hA j]; field_simp
    rw [Finset.sum_congr rfl fun j _ ↦ e2 j, ← Finset.mul_sum, hφs]
    split_ifs with h1 h2 h2
    · ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · ring
  have hordz : ∀ α β' : K, β' ^ S.n = (S.p.map (algebraMap C K)).eval α →
      (S.ordAt K z α β' : ℚ) = Dn * dK c β m cl k0 (α, β') := by
    intro α β' hv
    rw [hz, S.ordAt_prod hv _ _ (fun j _ ↦ zpow_ne_zero _ (hg0 j))]
    push_cast
    simp only [S.ordAt_zpow hv, Int.cast_mul]
    have e2 : ∀ j : Fin k, (S.ordAt K (g j) α β' : ℚ) =
        ∑ kk, (M j * (2 * lam kk j)) * dK c β m cl kk (α, β') := fun j ↦ by
      rw [hgo j α β' hv]; simp
    simp only [e2, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_eq_single k0]
    · have := hcoef k0 hk0
      rw [if_pos rfl] at this
      rw [← this, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    · intro kk _ hkk
      by_cases hkk' : ∃ q, cl q = kk ∧ m q ≠ 0
      · have := hcoef kk hkk'
        rw [if_neg hkk] at this
        rw [show ∑ j : Fin k, (A j : ℚ) * ((M j * (2 * lam kk j)) * dK c β m cl kk (α, β')) =
          (∑ j : Fin k, (A j : ℚ) * (M j * (2 * lam kk j))) * dK c β m cl kk (α, β') by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ ↦ by ring, this, zero_mul]
      · push Not at hkk'
        have hd0 : dK (K := K) c β m cl kk (α, β') = 0 := Finset.sum_eq_zero fun q _ ↦ by
          by_cases hq : cl q = kk
          · simp [mK, hq, hkk' q hq]
          · simp [mK, hq]
        simp [hd0]
    · simp
  have hform : S.OrdForm (K := K) c β (mK m cl k0) z Dn := by
    refine ⟨fun α β' hv hα ↦ ?_, fun q ↦ ⟨?_, ?_⟩⟩
    · have := hordz α β' hv
      rw [dK_off c β m cl k0 α β' hα, mul_zero] at this
      exact_mod_cast this
    · rw [hordz _ _ (by rw [eval_map, eval₂_at_apply, ← (hβ q).2, map_pow]),
        dK_plus S c β hc hβ m cl k0 q]; ring
    · rw [hordz _ _ (by rw [hn2, neg_sq, ← hn2, eval_map, eval₂_at_apply, ← (hβ q).2, map_pow]),
        dK_minus S c β hc hβ m cl k0 q]; ring
  obtain ⟨N, hN, hP⟩ := S.kq_log_nontors c β hc hβ (mK m cl k0) hn2 z hz0 Dn
    (by exact_mod_cast hD0.ne') hform
  exact hnt N hN hP

/-- `μ = 0` lets `δ₀` be killed trivially. -/
lemma kill_of_mu0 (hmu0 : ∀ f : C⟮S.x⟯⟮S.y⟯, f ≠ 0 → ∀ (L' : Fin nk → ℚ) (μ : ℤ),
      S.DivKZ β₀ c β m cl f L' μ → μ = 0) :
    ∀ f : C⟮S.x⟯⟮S.y⟯, f ≠ 0 → ∀ (L' : Fin nk → ℚ) (μ : ℤ),
      S.DivKZ β₀ c β m cl f L' μ →
      ∃ M : ℕ, 0 < M ∧ ∃ g : C⟮S.x⟯⟮S.y⟯, g ≠ 0 ∧ S.DivKZ β₀ c β m cl g (fun k ↦ M * L' k) 0 := by
  intro f hf L' μ hfo
  have := hmu0 f hf L' μ hfo
  subst this
  exact ⟨1, one_pos, f, hf, fun α β' hv ↦ by rw [hfo α β' hv]; simp⟩

end ExpMain2

end SuperData

end Differential
