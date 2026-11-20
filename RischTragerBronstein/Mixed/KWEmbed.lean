import RischTragerBronstein.Mixed.KPEmbed

/-!
# Superelliptic curves over a differential base with `x′ = ω(x)`: differential local expansions

The generalization of `KPEmbed` from `x′ = η ∈ C` (logarithms) to `x′ = ω(x)`, `ω ∈ C[x]` (e.g.
`x′ = η x` for exponentials).

`S : SuperData C L` (`yⁿ = p(x)`) where now the base `C` is a differential field (not constants) and
`x′ = η ∈ C` (`x` is a primitive over `C`, e.g. `x = log u`). A local expansion substitutes
`x ↦ X̂` (a Laurent series over a differential field `K ⊇ C`); with `dS s X̂ = η`, the derivation of
`C(x, y)` becomes `dS s = δ + s d/dX` (`KPLaurent`):

* `dS_substHomW`: `dS s (P(X̂)) = (P^δ + η P′)(X̂)`;
* `derivClosedXYW`: `C(x, y)` is closed under the derivation;
* `embG_dSW`: `embG (w′) = dS s (embG w)`.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries

namespace Differential

section Subst

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential C] [Differential K]
  [CharZero K]

/-- **The substitution intertwines the derivations.** -/
lemma dS_substHomW (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′) (ω : C[X])
    (s Xh : LaurentSeries K) (hXh : dS s Xh = substHom Xh ω) (P : C[X]) :
    dS s (substHom Xh P) = substHom Xh (mapCoeffs P + ω * derivative P) := by
  have hAM : ∀ k : K, algebraMap K (LaurentSeries K) k = HahnSeries.C k := fun k ↦ by
    rw [HahnSeries.algebraMap_apply']
    exact ofPowerSeries_C _
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, ← map_add]
    congr 1
    rw [map_add, derivative_add]
    ring
  | monomial n c =>
    rw [substHom_apply, Polynomial.map_monomial, aeval_monomial, Derivation.leibniz,
      Derivation.leibniz_pow, hXh, substHom_apply]
    have hC : dS s (algebraMap K (LaurentSeries K) (algebraMap C K c)) =
        algebraMap K (LaurentSeries K) (algebraMap C K c′) := by
      rw [hAM, hAM, dS_C, hK]
    rw [hC]
    have hmc : mapCoeffs (monomial n c) = monomial n c′ := by
      ext i
      rw [coeff_mapCoeffs, coeff_monomial, coeff_monomial]
      split_ifs <;> simp
    rw [hmc, derivative_monomial, map_add, map_mul, substHom_apply, substHom_apply,
      substHom_apply, Polynomial.map_monomial, Polynomial.map_monomial, aeval_monomial,
      aeval_monomial]
    simp only [smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
    simp only [hAM]
    ring

end Subst

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K]

namespace SuperData

variable (S : SuperData C L) (ω : C[X]) (hx : S.x′ = aeval S.x ω)

omit [CharZero L] [Field K] [CharZero K] [Algebra C K] [Differential K] in
include hx in
/-- `x′ = η` as a polynomial derivation. -/
lemma deriv_aeval_xW (P : C[X]) :
    (aeval S.x P)′ = aeval S.x (mapCoeffs P + ω * derivative P) := by
  rw [deriv_aeval_eq, hx, map_add, map_mul]
  ring

omit [Field K] [CharZero K] [Algebra C K] [Differential K] in
include hx in
/-- `y′ = (p^δ + η p′)(x) y / (n p(x))`. -/
lemma deriv_yW : S.y′ = aeval S.x (mapCoeffs S.p + ω * derivative S.p) * S.y /
    ((S.n : L) * aeval S.x S.p) := by
  have hp0 : aeval S.x S.p ≠ 0 := fun h ↦ S.htr ⟨S.p, S.hsq.ne_zero, h⟩
  have hy0 : S.y ≠ 0 := fun h ↦ hp0 (by rw [← S.hy, h, zero_pow S.hn.ne'])
  have hn0 : (S.n : L) ≠ 0 := by exact_mod_cast S.hn.ne'
  have hd := congrArg (fun z ↦ z′) S.hy
  rw [Derivation.leibniz_pow, S.deriv_aeval_xW ω hx] at hd
  rw [eq_div_iff (mul_ne_zero hn0 hp0), ← hd, ← S.hy]
  obtain ⟨m, hm⟩ : ∃ m, S.n = m + 1 := ⟨S.n - 1, by have := S.hn; omega⟩
  rw [hm, Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

omit [CharZero L] [Field K] [CharZero K] [Algebra C K] [Differential K] in
include hx in
/-- `C⟮x⟯` is closed under the derivation. -/
lemma derivClosedXW : DerivClosed C⟮S.x⟯ :=
  derivClosed_adjoin_simple S.x ω hx

omit [Field K] [CharZero K] [Algebra C K] [Differential K] in
include hx in
/-- **`C⟮x⟯⟮y⟯` is closed under the derivation.** -/
lemma derivClosedXYW : ∀ w ∈ C⟮S.x⟯⟮S.y⟯, w′ ∈ C⟮S.x⟯⟮S.y⟯ := by
  have hcl : DerivClosed C⟮S.x⟯ := S.derivClosedXW ω hx
  set T := C⟮S.x⟯⟮S.y⟯
  have hF : ∀ a ∈ C⟮S.x⟯, a ∈ T := fun a ha ↦ by
    have := IntermediateField.algebraMap_mem T (⟨a, ha⟩ : C⟮S.x⟯)
    exact this
  let U : IntermediateField C⟮S.x⟯ L :=
    { carrier := {w | w ∈ T ∧ w′ ∈ T}
      mul_mem' := fun {u v} hu hv ↦ ⟨mul_mem hu.1 hv.1, by
        rw [Derivation.leibniz]
        exact add_mem (mul_mem hu.1 hv.2) (mul_mem hv.1 hu.2)⟩
      one_mem' := ⟨one_mem _, by simp⟩
      add_mem' := fun {u v} hu hv ↦ ⟨add_mem hu.1 hv.1, by
        rw [map_add]; exact add_mem hu.2 hv.2⟩
      zero_mem' := ⟨zero_mem _, by simp⟩
      algebraMap_mem' := fun a ↦ ⟨T.algebraMap_mem a, hF _ (hcl _ a.2)⟩
      inv_mem' := fun u hu ↦ ⟨inv_mem hu.1, by
        rw [Derivation.leibniz_inv]
        exact mul_mem (neg_mem (pow_mem (inv_mem hu.1) 2)) hu.2⟩ }
  have hyU : S.y ∈ U := by
    refine ⟨mem_adjoin_simple_self _ _, ?_⟩
    rw [S.deriv_yW ω hx]
    have hpx : aeval S.x S.p ∈ T := hF _ (by
      rw [← algebraMap_adjoinSimple (F := C) S.x S.p]; exact SetLike.coe_mem _)
    have hdpx : aeval S.x (mapCoeffs S.p + ω * derivative S.p) ∈ T := hF _ (by
      rw [← algebraMap_adjoinSimple (F := C) S.x _]; exact SetLike.coe_mem _)
    exact div_mem (mul_mem hdpx (mem_adjoin_simple_self _ _))
      (mul_mem (_root_.natCast_mem _ _) hpx)
  have hle : C⟮S.x⟯⟮S.y⟯ ≤ U := by
    rw [adjoin_simple_le_iff]; exact hyU
  exact fun w hw ↦ (hle hw).2

section Generic

variable (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
  (s Xh : LaurentSeries K) (hXh : dS s Xh = substHom Xh ω)
  (g : C[X] →+* LaurentSeries K) (hg : Function.Injective g) (hgX : ∀ P, g P = substHom Xh P)
include hx hK hXh hgX

omit [CharZero L] in
/-- `embXG g` intertwines the derivations. -/
theorem embXG_dSW : ∀ a (ha : a ∈ C⟮S.x⟯),
    S.embXG g hg ⟨a′, S.derivClosedXW ω hx a ha⟩ = dS s (S.embXG g hg ⟨a, ha⟩) := by
  letI := algebraAdjoinSimple (F := C) S.x
  have hcl : DerivClosed C⟮S.x⟯ := S.derivClosedXW ω hx
  have hP : ∀ P : C[X], ∃ h, S.embXG g hg ⟨(aeval S.x P)′, h⟩ =
      dS s (S.embXG g hg (algebraMap C[X] C⟮S.x⟯ P)) := fun P ↦ by
    refine ⟨hcl _ (by rw [← algebraMap_adjoinSimple (F := C) S.x P]; exact SetLike.coe_mem _), ?_⟩
    have e : (⟨(aeval S.x P)′, hcl _ (by
        rw [← algebraMap_adjoinSimple (F := C) S.x P]; exact SetLike.coe_mem _)⟩ : C⟮S.x⟯) =
        algebraMap C[X] C⟮S.x⟯ (mapCoeffs P + ω * derivative P) :=
      Subtype.ext (by
        show (aeval S.x P)′ = _
        rw [algebraMap_adjoinSimple S.x (mapCoeffs P + ω * derivative P)]
        exact S.deriv_aeval_xW ω hx P)
    rw [e, S.embXG_algebraMap, S.embXG_algebraMap, hgX, hgX, dS_substHomW hK ω s Xh hXh]
  intro a ha
  induction ha using IntermediateField.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    subst hw
    obtain ⟨h, e⟩ := hP X
    have e2 : (⟨S.x, mem_adjoin_simple_self C S.x⟩ : C⟮S.x⟯) = algebraMap C[X] C⟮S.x⟯ X :=
      Subtype.ext (by rw [algebraMap_adjoinSimple, aeval_X])
    have e3 : (⟨S.x′, hcl S.x (mem_adjoin_simple_self C S.x)⟩ : C⟮S.x⟯) =
        ⟨(aeval S.x X)′, h⟩ := Subtype.ext (by show S.x′ = (aeval S.x X)′; rw [aeval_X])
    rw [e3, e, e2]
  | algebraMap c =>
    obtain ⟨h, e⟩ := hP (Polynomial.C c)
    have e2 : (⟨algebraMap C L c, IntermediateField.algebraMap_mem _ c⟩ : C⟮S.x⟯) =
        algebraMap C[X] C⟮S.x⟯ (Polynomial.C c) :=
      Subtype.ext (by rw [algebraMap_adjoinSimple, aeval_C])
    have e3 : (⟨(algebraMap C L c)′, hcl _ (IntermediateField.algebraMap_mem _ c)⟩ : C⟮S.x⟯) =
        ⟨(aeval S.x (Polynomial.C c))′, h⟩ :=
      Subtype.ext (by show (algebraMap C L c)′ = (aeval S.x (Polynomial.C c))′; rw [aeval_C])
    rw [e3, e, e2]
  | add u v hu hv ihu ihv =>
    have e1 : (⟨(u + v)′, hcl _ (add_mem hu hv)⟩ : C⟮S.x⟯) =
        ⟨u′, hcl u hu⟩ + ⟨v′, hcl v hv⟩ := Subtype.ext (by simp)
    have e2 : (⟨u + v, add_mem hu hv⟩ : C⟮S.x⟯) = ⟨u, hu⟩ + ⟨v, hv⟩ := rfl
    rw [e1, e2, map_add, map_add, map_add, ihu, ihv]
  | mul u v hu hv ihu ihv =>
    have e1 : (⟨(u * v)′, hcl _ (mul_mem hu hv)⟩ : C⟮S.x⟯) =
        ⟨u, hu⟩ * ⟨v′, hcl v hv⟩ + ⟨v, hv⟩ * ⟨u′, hcl u hu⟩ :=
      Subtype.ext (by simp [Derivation.leibniz])
    have e2 : (⟨u * v, mul_mem hu hv⟩ : C⟮S.x⟯) = ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
    rw [e1, e2, map_add, map_mul, map_mul, ihu, ihv, map_mul, Derivation.leibniz, smul_eq_mul,
      smul_eq_mul]
  | inv u hu ihu =>
    have e1 : (⟨u⁻¹′, hcl _ (inv_mem hu)⟩ : C⟮S.x⟯) = -(⟨u, hu⟩ : C⟮S.x⟯)⁻¹ ^ 2 * ⟨u′, hcl u hu⟩ :=
      Subtype.ext (by simp [Derivation.leibniz_inv])
    have e2 : (⟨u⁻¹, inv_mem hu⟩ : C⟮S.x⟯) = (⟨u, hu⟩ : C⟮S.x⟯)⁻¹ := rfl
    rw [e1, e2, map_mul, map_neg, map_pow, map_inv₀, ihu, Derivation.leibniz_inv, smul_eq_mul]

/-- **`embG` intertwines the derivations.** -/
theorem embG_dSW (Y : LaurentSeries K) (hY : Y ^ S.n = g S.p) :
    ∀ w (hw : w ∈ C⟮S.x⟯⟮S.y⟯),
      S.embG g hg Y hY ⟨w′, S.derivClosedXYW ω hx w hw⟩ = dS s (S.embG g hg Y hY ⟨w, hw⟩) := by
  letI := algebraAdjoinSimple (F := C) S.x
  have hdc := S.derivClosedXYW ω hx
  have hcl : DerivClosed C⟮S.x⟯ := S.derivClosedXW ω hx
  set φ := S.embG g hg Y hY
  intro w hw
  induction hw using IntermediateField.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    subst hw
    set Dp := mapCoeffs S.p + ω * derivative S.p with hDp
    have hpx : aeval S.x S.p ∈ C⟮S.x⟯ := by
      rw [← algebraMap_adjoinSimple (F := C) S.x S.p]; exact SetLike.coe_mem _
    have hdpx : aeval S.x Dp ∈ C⟮S.x⟯ := by
      rw [← algebraMap_adjoinSimple (F := C) S.x _]; exact SetLike.coe_mem _
    have e : (⟨S.y′, hdc _ (mem_adjoin_simple_self _ _)⟩ : C⟮S.x⟯⟮S.y⟯) =
        algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨_, hdpx⟩ * AdjoinSimple.gen C⟮S.x⟯ S.y /
          ((S.n : C⟮S.x⟯⟮S.y⟯) * algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨_, hpx⟩) :=
      Subtype.ext (by
        show S.y′ = _
        rw [S.deriv_yW ω hx]
        simp [hDp])
    have e2 : (⟨S.y, mem_adjoin_simple_self _ _⟩ : C⟮S.x⟯⟮S.y⟯) = AdjoinSimple.gen C⟮S.x⟯ S.y := rfl
    have ep : (⟨_, hpx⟩ : C⟮S.x⟯) = algebraMap C[X] C⟮S.x⟯ S.p :=
      Subtype.ext (algebraMap_adjoinSimple S.x S.p).symm
    have edp : (⟨_, hdpx⟩ : C⟮S.x⟯) = algebraMap C[X] C⟮S.x⟯ Dp :=
      Subtype.ext (algebraMap_adjoinSimple S.x _).symm
    rw [e, e2, ep, edp, map_div₀, map_mul, map_mul, map_natCast, S.embG_algebraMap,
      S.embG_algebraMap, S.embG_gen, S.embXG_algebraMap, S.embXG_algebraMap]
    -- differentiate `Yⁿ = g p`
    have hp0 : g S.p ≠ 0 := (map_ne_zero_iff _ hg).mpr S.hsq.ne_zero
    have hn0 : (S.n : LaurentSeries K) ≠ 0 := by
      rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := K))]
      intro h0
      have := HahnSeries.C_injective (Γ := ℤ) (R := K) (h0.trans (map_zero _).symm)
      exact S.hn.ne' (by exact_mod_cast this)
    have hd := congrArg (dS s) hY
    rw [Derivation.leibniz_pow, hgX, dS_substHomW hK ω s Xh hXh, ← hgX] at hd
    rw [div_eq_iff (mul_ne_zero hn0 hp0), ← hd]
    rw [← hY]
    obtain ⟨m, hm⟩ : ∃ m, S.n = m + 1 := ⟨S.n - 1, by have := S.hn; omega⟩
    rw [hm, Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  | algebraMap a =>
    have e1 : (⟨(algebraMap C⟮S.x⟯ L a)′, hdc _ (IntermediateField.algebraMap_mem _ a)⟩ :
        C⟮S.x⟯⟮S.y⟯) = algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ ⟨(a : L)′, hcl _ a.2⟩ := rfl
    have e2 : (⟨algebraMap C⟮S.x⟯ L a, IntermediateField.algebraMap_mem _ a⟩ : C⟮S.x⟯⟮S.y⟯) =
        algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ a := rfl
    rw [e1, e2, S.embG_algebraMap, S.embG_algebraMap]
    exact S.embXG_dSW ω hx hK s Xh hXh g hg hgX (a : L) a.2
  | add u v hu hv ihu ihv =>
    have e1 : (⟨(u + v)′, hdc _ (add_mem hu hv)⟩ : C⟮S.x⟯⟮S.y⟯) =
        ⟨u′, hdc u hu⟩ + ⟨v′, hdc v hv⟩ := Subtype.ext (by simp)
    have e2 : (⟨u + v, add_mem hu hv⟩ : C⟮S.x⟯⟮S.y⟯) = ⟨u, hu⟩ + ⟨v, hv⟩ := rfl
    rw [e1, e2, map_add, map_add, map_add, ihu, ihv]
  | mul u v hu hv ihu ihv =>
    have e1 : (⟨(u * v)′, hdc _ (mul_mem hu hv)⟩ : C⟮S.x⟯⟮S.y⟯) =
        ⟨u, hu⟩ * ⟨v′, hdc v hv⟩ + ⟨v, hv⟩ * ⟨u′, hdc u hu⟩ :=
      Subtype.ext (by simp [Derivation.leibniz])
    have e2 : (⟨u * v, mul_mem hu hv⟩ : C⟮S.x⟯⟮S.y⟯) = ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
    rw [e1, e2, map_add, map_mul, map_mul, ihu, ihv, map_mul, Derivation.leibniz, smul_eq_mul,
      smul_eq_mul]
  | inv u hu ihu =>
    have e1 : (⟨u⁻¹′, hdc _ (inv_mem hu)⟩ : C⟮S.x⟯⟮S.y⟯) =
        -(⟨u, hu⟩ : C⟮S.x⟯⟮S.y⟯)⁻¹ ^ 2 * ⟨u′, hdc u hu⟩ :=
      Subtype.ext (by simp [Derivation.leibniz_inv])
    have e2 : (⟨u⁻¹, inv_mem hu⟩ : C⟮S.x⟯⟮S.y⟯) = (⟨u, hu⟩ : C⟮S.x⟯⟮S.y⟯)⁻¹ := rfl
    rw [e1, e2, map_mul, map_neg, map_pow, map_inv₀, ihu, Derivation.leibniz_inv, smul_eq_mul]

end Generic

end SuperData

end Differential
