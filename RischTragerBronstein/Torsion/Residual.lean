import RischTragerBronstein.Torsion.Reduced
import RischTragerBronstein.Algebraic.SupDisc
import RischTragerBronstein.Curves.HenselQ

/-!
# Residual zeros over a Henselian DVR (general curves)

* `jetN_eval`: `jet(W; a, V)(t) = W(a + t, V(t))`;
* `disc_uniqueG`: if `W` vanishes simply at a point `(a, b)` of `F = 0` (unit `F_Y`), then it has
  no further zero `(a + t, Y)` with `t`, `Y − b` in the maximal ideal, unless `t = 0`;
* `jet_coeff_one_unit`: a simple zero modulo `ϖ` gives a unit first-order jet coefficient;
* `residual_zerosG`: if the norm `Res_Y(F, W) = E · ∏(x − xᵢ)^{n−1} · R` with `R̄` having simple
  roots at the `x̄ᵢ` and `deg R ≤ g`, then for each `i` either `W` has a zero
  `(z, Y) ≡ (xᵢ, y_{i,0})`, or `R(xᵢ) = 0`.
-/

open Polynomial

namespace GTors

section Jet

variable {R : Type*} [CommRing R]

lemma jetN_eval (W : R[X][X]) (a : R) (V : R[X]) (t : R) :
    (Sup.jetN W a V).eval t = Sup.evalW W (a + t) (V.eval t) := by
  rw [Sup.jetN, eval_map, ← coe_evalRingHom, hom_eval₂, Sup.evalW, eval_map]
  congr 1
  refine RingHom.ext fun P ↦ ?_
  simp only [RingHom.comp_apply, coe_evalRingHom, coe_compRingHom, eval_comp, eval_add, eval_X,
    eval_C, add_comm t a]

lemma poly_expand2 (P : R[X]) (t : R) : ∃ s, P.eval t = P.coeff 0 + t * P.coeff 1 + t ^ 2 * s := by
  have hdvd : X ^ 2 ∣ P - C (P.coeff 0) - C (P.coeff 1) * X := by
    rw [X_pow_dvd_iff]
    intro d hd
    interval_cases d <;> simp [coeff_C, coeff_X]
  obtain ⟨Q, hQ⟩ := hdvd
  refine ⟨Q.eval t, ?_⟩
  have e := congrArg (eval t) hQ
  simp only [eval_sub, eval_C, eval_mul, eval_X, eval_pow] at e
  linear_combination e

end Jet

section Disc

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]

local notation "𝔪" => IsLocalRing.maximalIdeal O
local notation "ρ" => IsLocalRing.residue O

lemma residue_evalW (V : O[X][X]) (a b : O) :
    ρ (Sup.evalW V a b) = Sup.evalW (V.map (mapRingHom ρ)) (ρ a) (ρ b) :=
  (evalW_mapG ρ V a b).symm

/-- **Uniqueness of a simple zero in its residue disc** (general curves). -/
theorem disc_uniqueG (F W : O[X][X]) {a b t Y : O} {V : O[X]}
    (hV : IsBranchG F a b 2 V) (hu : IsUnit (Sup.evalW (derivative F) a b))
    (h0 : (Sup.jetN W a V).coeff 0 = 0) (h1 : IsUnit ((Sup.jetN W a V).coeff 1))
    (ht : t ∈ 𝔪) (hYb : Y - b ∈ 𝔪) (hY : Sup.evalW F (a + t) Y = 0)
    (hz : Sup.evalW W (a + t) Y = 0) : t = 0 := by
  obtain ⟨sv, hsv⟩ := poly_expand2 V t
  rw [hV.1] at hsv
  set v := V.eval t with hv_def
  have hvb : v - b ∈ 𝔪 := by
    rw [hsv, show b + t * V.coeff 1 + t ^ 2 * sv - b = t * (V.coeff 1 + t * sv) by ring]
    exact Ideal.mul_mem_right _ _ ht
  have hYv : Y - v ∈ 𝔪 := by
    rw [show Y - v = (Y - b) - (v - b) by ring]; exact Ideal.sub_mem _ hYb hvb
  obtain ⟨H, hH⟩ := hV.2
  have hFv : Sup.evalW F (a + t) v = t ^ 2 * H.eval t := by
    have := congrArg (eval t) hH
    rwa [jetN_eval, eval_mul, eval_pow, eval_X] at this
  -- `F(a + t, ·)` near `v`
  set P := F.map (evalRingHom (a + t)) with hP
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion P v (Y - v)
  rw [add_sub_cancel] at hk
  have hPY : P.eval Y = 0 := hY
  have hPv : P.eval v = t ^ 2 * H.eval t := hFv
  have hres : ∀ z : O, z - a ∈ 𝔪 → ∀ w : O, w - b ∈ 𝔪 →
      IsUnit (Sup.evalW (derivative F) z w) := by
    intro z hz w hw
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, residue_evalW,
      Sup.residue_eq_of_sub_mem hz, Sup.residue_eq_of_sub_mem hw, ← residue_evalW]
    exact (hu.map ρ).ne_zero
  have hat : (a + t) - a ∈ 𝔪 := by rw [add_sub_cancel_left]; exact ht
  have hG : IsUnit (P.derivative.eval v + k * (Y - v)) := by
    refine Sup.unit_add_mem ?_ (Ideal.mul_mem_left _ _ hYv)
    have e1 : P.derivative.eval v = Sup.evalW (derivative F) (a + t) v := by
      rw [hP, Polynomial.derivative_map]; rfl
    rw [e1]
    exact hres _ hat _ hvb
  obtain ⟨Gi, hGi⟩ : ∃ Gi, Gi * (P.derivative.eval v + k * (Y - v)) = 1 := ⟨↑hG.unit⁻¹, by simp⟩
  have hYv' : Y - v = -(t ^ 2 * H.eval t) * Gi := by
    have e : 0 = t ^ 2 * H.eval t + (Y - v) * (P.derivative.eval v + k * (Y - v)) := by
      rw [← hPY, hk, hPv]; ring
    calc Y - v = (Y - v) * ((P.derivative.eval v + k * (Y - v)) * Gi) := by rw [mul_comm _ Gi, hGi, mul_one]
      _ = -(t ^ 2 * H.eval t) * Gi := by linear_combination (-Gi) * e
  -- `W(a + t, ·)` near `v`
  set Q := W.map (evalRingHom (a + t)) with hQ
  obtain ⟨k', hk'⟩ := Polynomial.binomExpansion Q v (Y - v)
  rw [add_sub_cancel] at hk'
  have hQY : Q.eval Y = 0 := hz
  have hQv : Q.eval v = (Sup.jetN W a V).eval t := by rw [jetN_eval]; rfl
  obtain ⟨s, hs⟩ := poly_expand2 (Sup.jetN W a V) t
  rw [h0, zero_add] at hs
  set c1 := (Sup.jetN W a V).coeff 1
  have hmain : t * (c1 + t * (s + (-(H.eval t) * Gi) * (Q.derivative.eval v + k' * (Y - v)))) = 0 := by
    have e : Q.eval Y = t * c1 + t ^ 2 * s + (Y - v) * (Q.derivative.eval v + k' * (Y - v)) := by
      rw [hk', hQv, hs]; ring
    rw [hQY] at e
    linear_combination -e - (Q.derivative.eval v + k' * (Y - v)) * hYv'
  have hunit : IsUnit (c1 + t * (s + (-(H.eval t) * Gi) * (Q.derivative.eval v + k' * (Y - v)))) :=
    Sup.unit_add_mem h1 (Ideal.mul_mem_right _ _ ht)
  exact (mul_eq_zero.mp hmain).resolve_right hunit.ne_zero

/-- A simple zero modulo the maximal ideal has a unit first-order jet coefficient. -/
lemma jet_coeff_one_unit (F W : O[X][X]) {a b : O} {V : O[X]} (hV : IsBranchG F a b 2 V)
    (hW0 : Sup.evalW W a b = 0)
    (hs : ¬ VanishAtG (F.map (mapRingHom ρ)) (W.map (mapRingHom ρ)) (ρ a) (ρ b) 2) :
    IsUnit ((Sup.jetN W a V).coeff 1) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  intro hc
  apply hs
  refine ⟨V.map ρ, hV.mapR ρ, ?_⟩
  rw [← Sup.jetN_map, X_pow_dvd_iff]
  intro d hd
  interval_cases d
  · rw [coeff_map, Sup.jetN_coeff_zero, hV.1, hW0, map_zero]
  · rw [coeff_map]; exact hc

/-- A monic polynomial of degree `n` over a domain with `n` distinct roots is their product. -/
lemma eq_prod_of_distinct_roots' (p : O[X]) (hp : p.Monic) {n : ℕ} (hn : p.natDegree = n)
    (r : Fin n → O) (hr : Function.Injective r) (hroot : ∀ k, p.eval (r k) = 0) :
    p = ∏ k, (X - Polynomial.C (r k)) := by
  classical
  have hp0 : p ≠ 0 := hp.ne_zero
  set S : Multiset O := Finset.univ.val.map r with hS
  have hSnd : S.Nodup := (Finset.univ.nodup).map hr
  have hle : S ≤ p.roots := (Multiset.le_iff_subset hSnd).mpr fun z hz ↦ by
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hz
    exact (mem_roots hp0).mpr (hroot k)
  have hcard : Multiset.card S = n := by simp [hS]
  have heq : S = p.roots := Multiset.eq_of_le_of_card_le hle (by rw [hcard, ← hn]; exact card_roots' p)
  have hsplit : p = (p.roots.map fun a ↦ X - Polynomial.C a).prod := by
    refine (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp ?_).symm
    rw [← heq, hcard, hn]
  rw [hsplit, ← heq, hS, Multiset.map_map]
  rfl

end Disc

section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [HenselianRing O (IsLocalRing.maximalIdeal O)]

local notation "𝔪" => IsLocalRing.maximalIdeal O
local notation "ρ" => IsLocalRing.residue O

lemma mem_max_iff_dvdG {ϖ : O} (hϖ : Irreducible ϖ) (z : O) : z ∈ 𝔪 ↔ ϖ ∣ z := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton]

/-- **The residual zeros** (general curves). -/
theorem residual_zerosG {ϖ : O} (hϖ : Irreducible ϖ) (F : O[X][X]) (hF : F.Monic) (n : ℕ)
    (hFn : F.natDegree = n) (hn : 0 < n) (W : O[X][X]) (m : ℕ) (hWm : W.natDegree ≤ m)
    {g : ℕ} (x : Fin g → O) (hx : ∀ i j, i ≠ j → IsUnit (x i - x j))
    (y : Fin g → Fin n → O) (hsplit : ∀ i, F.map (evalRingHom (x i)) = ∏ k, (X - Polynomial.C (y i k)))
    (hFu : ∀ i k, IsUnit (Sup.evalW (derivative F) (x i) (y i k)))
    (E : O[X]) (R : O[X]) (hNR : resultant F W n m = E * (∏ i, (X - Polynomial.C (x i)) ^ (n - 1)) * R)
    (hRdeg : R.natDegree ≤ g)
    (hRk : ∀ i, (R.map ρ).IsRoot (ρ (x i)) ∧ ¬ (derivative (R.map ρ)).IsRoot (ρ (x i)))
    (hWk : ∀ i (k : Fin n), (k : ℕ) ≠ 0 → Sup.evalW W (x i) (y i k) = 0)
    (hsimple : ∀ i (k : Fin n), (k : ℕ) ≠ 0 →
      ¬ VanishAtG (F.map (mapRingHom ρ)) (W.map (mapRingHom ρ)) (ρ (x i)) (ρ (y i k)) 2) :
    ∀ i, (∃ (z : O) (Yv : Fin n → O), ϖ ∣ z - x i ∧ (∀ k, ϖ ∣ Yv k - y i k) ∧
      F.map (evalRingHom z) = ∏ k, (X - Polynomial.C (Yv k)) ∧
      Sup.evalW W z (Yv ⟨0, hn⟩) = 0) ∨ R.eval (x i) = 0 := by
  classical
  have hunitk : ∀ z : O, IsUnit z → ρ z ≠ 0 := fun z hz ↦ (hz.map ρ).ne_zero
  have hxk : Function.Injective fun i ↦ ρ (x i) := by
    intro a b hab
    by_contra hne
    have := hunitk _ (hx a b hne)
    rw [map_sub, show ρ (x a) = ρ (x b) from hab, sub_self] at this
    exact this rfl
  intro i
  have hRk0 : R.map ρ ≠ 0 := fun h ↦ (hRk i).2 (by rw [h]; simp)
  -- the reduction of `R` has degree `g`
  have hdegk : g ≤ (R.map ρ).natDegree := by
    have hsub : (Finset.univ.image fun j ↦ ρ (x j)).val ≤ (R.map ρ).roots :=
      (Multiset.le_iff_subset (Finset.nodup _)).mpr fun z hz ↦ by
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hz)
        exact (mem_roots hRk0).mpr (hRk j).1
    have := (Multiset.card_le_card hsub).trans (card_roots' _)
    rwa [Finset.card_val, Finset.card_image_of_injective _ hxk, Finset.card_univ,
      Fintype.card_fin] at this
  have hRnd : R.natDegree = g := le_antisymm hRdeg (hdegk.trans natDegree_map_le)
  have hkd : (R.map ρ).natDegree = g := le_antisymm (natDegree_map_le.trans hRdeg) hdegk
  have hlc : IsUnit (R.coeff g) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← coeff_map, ← hkd]
    exact leadingCoeff_ne_zero.mpr hRk0
  set u : O := ↑hlc.unit⁻¹ with hu
  have huu : IsUnit u := Units.isUnit _
  set R' := Polynomial.C u * R with hR'
  have hR'm : R'.Monic := by
    rw [Monic, leadingCoeff, hR', natDegree_C_mul huu.ne_zero, hRnd, coeff_C_mul, hu]
    simp
  have hmapR' : R'.map ρ = Polynomial.C (ρ u) * R.map ρ := by
    rw [hR', Polynomial.map_mul, Polynomial.map_C]
  have hρeval : ∀ (P : O[X]) (a : O), ρ (P.eval a) = (P.map ρ).eval (ρ a) := fun P a ↦ by
    rw [eval_map, eval₂_hom]
  have hH1 : R'.eval (x i) ∈ 𝔪 := by
    rw [← IsLocalRing.residue_eq_zero_iff, hρeval, hmapR', eval_mul, eval_C, (hRk i).1, mul_zero]
  have hH2 : IsUnit (Ideal.Quotient.mk 𝔪 (R'.derivative.eval (x i))) := by
    show IsUnit (ρ (R'.derivative.eval (x i)))
    rw [hρeval, ← Polynomial.derivative_map, hmapR', derivative_C_mul, eval_mul, eval_C]
    exact (mul_ne_zero (hunitk _ huu) (hRk i).2).isUnit
  obtain ⟨z, hzr, hzx⟩ := HenselianRing.is_henselian R' hR'm (x i) hH1 hH2
  have hRz : R.eval z = 0 := by
    have : R'.eval z = 0 := hzr
    rw [hR', eval_mul, eval_C] at this
    exact (mul_eq_zero.mp this).resolve_left huu.ne_zero
  have hzρ : ρ z = ρ (x i) := Sup.residue_eq_of_sub_mem hzx
  -- the fibre above `z` splits over `O`
  set Pz := F.map (evalRingHom z) with hPz
  have hPzm : Pz.Monic := hF.map _
  have hPzn : Pz.natDegree = n := by rw [hPz, hF.natDegree_map, hFn]
  have hFx0 : ∀ k, Sup.evalW F (x i) (y i k) = 0 := fun k ↦ by
    rw [Sup.evalW, hsplit i, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  have hdiff : ∀ k l, k ≠ l → IsUnit (y i k - y i l) := by
    intro k l hkl
    have h := hFu i k
    rw [Sup.evalW, ← Polynomial.derivative_map, hsplit i,
      Sup.derivative_prod_X_sub_C_eval (fun l ↦ y i l) k] at h
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j ↦ y i k - y i j)
      (Finset.mem_erase.mpr ⟨Ne.symm hkl, Finset.mem_univ l⟩)) h
  have hK1 : ∀ k, Pz.eval (y i k) ∈ 𝔪 := by
    intro k
    rw [← IsLocalRing.residue_eq_zero_iff]
    have : ρ (Pz.eval (y i k)) = ρ (Sup.evalW F z (y i k)) := rfl
    rw [this, residue_evalW, hzρ, ← residue_evalW, hFx0, map_zero]
  have hK2 : ∀ k, IsUnit (Ideal.Quotient.mk 𝔪 (Pz.derivative.eval (y i k))) := by
    intro k
    show IsUnit (ρ (Pz.derivative.eval (y i k)))
    have : Pz.derivative.eval (y i k) = Sup.evalW (derivative F) z (y i k) := by
      rw [hPz, Polynomial.derivative_map]; rfl
    rw [this, residue_evalW, hzρ, ← residue_evalW]
    exact (hFu i k).map ρ
  choose Y hY hYy using fun k ↦ HenselianRing.is_henselian Pz hPzm (y i k) (hK1 k) (hK2 k)
  have hYinj : Function.Injective Y := by
    intro k l hkl
    by_contra hne
    have h1 := Sup.unit_add_mem (hdiff k l hne) (Ideal.sub_mem _ (hYy k) (hYy l))
    rw [show y i k - y i l + ((Y k - y i k) - (Y l - y i l)) = Y k - Y l by ring, hkl,
      sub_self] at h1
    exact not_isUnit_zero h1
  have hPzsplit : Pz = ∏ k, (X - Polynomial.C (Y k)) :=
    eq_prod_of_distinct_roots' Pz hPzm hPzn Y hYinj fun k ↦ hY k
  -- a zero of `W` above `z`
  have hNz : (resultant F W n m).eval z = 0 := by
    rw [hNR, eval_mul, hRz, mul_zero]
  have hres : (resultant F W n m).eval z = resultant Pz (W.map (evalRingHom z)) n m := by
    rw [hPz, resultant_map_map]; rfl
  have hlist : Pz = ((List.ofFn Y).map fun r ↦ X - Polynomial.C r).prod := by
    rw [hPzsplit, List.map_ofFn, List.prod_ofFn]; rfl
  have hrl := Curves.resultant_list_prod (List.ofFn Y) (W.map (evalRingHom z)) m
    (natDegree_map_le.trans hWm)
  rw [List.length_ofFn] at hrl
  rw [hres, hlist, hrl, List.prod_eq_zero_iff] at hNz
  obtain ⟨w, hw, hw0⟩ := List.mem_map.mp hNz
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hw
  have hWz : Sup.evalW W z (Y k) = 0 := hw0
  by_cases hk : (k : ℕ) = 0
  · left
    have e : k = ⟨0, hn⟩ := Fin.ext hk
    subst e
    exact ⟨z, Y, (mem_max_iff_dvdG hϖ _).mp hzx, fun k ↦ (mem_max_iff_dvdG hϖ _).mp (hYy k),
      hPzsplit, hWz⟩
  · right
    obtain ⟨V, hV⟩ := exists_branchG (hFx0 k) (hFu i k) 2
    have h0 : (Sup.jetN W (x i) V).coeff 0 = 0 := by
      rw [Sup.jetN_coeff_zero, hV.1]; exact hWk i k hk
    have h1 := jet_coeff_one_unit F W hV (hWk i k hk) (hsimple i k hk)
    have ht := disc_uniqueG F W hV (hFu i k) h0 h1 (t := z - x i) (Y := Y k) hzx (hYy k)
      (by rw [add_sub_cancel]; exact hY k) (by rw [add_sub_cancel]; exact hWz)
    rw [← sub_eq_zero.mp ht]; exact hRz

end DVR

end GTors
