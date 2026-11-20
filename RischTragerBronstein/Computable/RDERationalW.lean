import RischTragerBronstein.Computable.RDERationalG
import RischTragerBronstein.Computable.ResidueAnnihilator
import RischTragerBronstein.Computable.RDENonCancelExpBound

/-!
# The Risch differential equation over `R(x)`, weakly normalised

`y′ + (Gn / Gd) y = A / D` with `Gn / Gd` in lowest terms, **any** denominator `Gd` (simple poles
allowed) and no condition at infinity. Following Bronstein (§6.1), the possible cancellations are
accounted for by

* the extra denominator `E = ∏ gcd(S, r - k)^k` over the natural candidates `k` among the rational
  roots of an annihilating polynomial `μ` of the residues of `Gn / Gd` at its simple poles
  (`RDE/RationalCoeffW.lean`, `Computable/ResidueAnnihilator.lean`), and
* the degree bound `max (deg D E) k∞`, `k∞ = deg D E - lc Gn / lc Gd` when `deg Gn + 1 = deg Gd`
  (`rde_pivot_W`).

`CPoly.rdeRationalW Gn Gd A D` then solves the polynomial equation with `odeSolveFull` and returns
`y = Y / (D E)`.

* `rdeRationalW_sound`: a returned `Y / D'` solves the equation;
* `rdeRationalW_complete`: `none` means there is no solution in `S(x)` for any extension `S` of the
  constants, provided `μ` passed `muCheck` and the homogeneous equation has only the zero solution.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

open Differential

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- Powers. -/
def powC (p : CPoly R) : ℕ → CPoly R
  | 0 => [1]
  | n + 1 => mul p (powC p n)

/-- The natural numbers `k ≥ 1` among a list of rationals. -/
def natCands (l : List ℚ) : List ℕ :=
  l.filterMap fun q ↦ if q.den = 1 ∧ 0 < q.num then some q.num.toNat else none

/-- The extra denominator `∏ gcd(S, r - k)^k`. -/
def extraDen (S r : CPoly R) (ks : List ℕ) : CPoly R :=
  (ks.map fun (k : ℕ) ↦ powC (gcd S (sub r [((k : ℕ) : R)])) k).foldr mul [1]

variable [HasRatRoots R] [HasNatTest R]

/-- The extra denominator for the coefficient `Gn / Gd`, given an annihilating polynomial `μ` of
its residues at the simple poles. -/
def extraDenW (μ Gn Gd : CPoly R) : CPoly R :=
  extraDen (simplePart Gd) (residuePolyW Gn Gd) (natCands (HasRatRoots.ratRoots μ))

/-- `μ_c(z) = c^d μ(z / c)`: an annihilating polynomial for `c · r`. -/
def scaleMu (c : R) : CPoly R → CPoly R
  | [] => []
  | a :: rest => (a * c ^ rest.length) :: scaleMu c rest

/-- The bound on the zero of the pivot: `max (deg D') k∞`. -/
def pivBoundW (Gn Gd D' : CPoly R) : ℕ :=
  let dD := (trim D').length - 1
  max dD (if (trim Gn).length + 1 = (trim Gd).length then
    (HasNatTest.natTest ((dD : R) - lead (trim Gn) / lead (trim Gd))).getD 0 else 0)

/-- **The weakly normalised rational RDE solver**: `y = Y / (D E)`. -/
def rdeRationalW (μ Gn Gd A D : CPoly R) : Option (CPoly R × CPoly R) :=
  let E := extraDenW μ Gn Gd
  let D' := mul D E
  (odeSolveFull (mul Gd D') (sub (mul Gn D') (mul Gd (deriv D'))) (mul (mul (mul A E) D') Gd)
    (pivBoundW Gn Gd D')).map fun Y ↦ (Y, D')

end Defs

section Spec

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R]

lemma toPoly_powC (p : CPoly R) (n : ℕ) : toPoly (powC p n) = toPoly p ^ n := by
  induction n with
  | zero => simp [powC]
  | succ n ih => rw [powC, toPoly_mul, ih, pow_succ, mul_comm]

lemma mem_natCands {l : List ℚ} {k : ℕ} (hk : k ≠ 0) (h : (k : ℚ) ∈ l) : k ∈ natCands l := by
  refine List.mem_filterMap.mpr ⟨(k : ℚ), h, ?_⟩
  have h1 : ((k : ℚ)).den = 1 := Rat.den_natCast k
  have h2 : ((k : ℚ)).num = k := Rat.num_natCast k
  simp [h1, h2, Nat.pos_of_ne_zero hk]

lemma toPoly_scaleMu_comp (c : R) (μ : CPoly R) :
    (toPoly (scaleMu c μ)).comp (C c * X) = C (c ^ (μ.length - 1)) * toPoly μ := by
  induction μ with
  | nil => simp [scaleMu]
  | cons a rest ih =>
    rw [scaleMu, toPoly_cons, toPoly_cons, add_comp, C_comp, mul_comp, X_comp, ih]
    cases rest with
    | nil => simp
    | cons b rest' =>
      simp only [List.length_cons, Nat.add_sub_cancel]
      rw [pow_succ]
      simp only [C_mul, C_pow]
      ring

lemma scaleMu_ne_zero {c : R} (hc : c ≠ 0) {μ : CPoly R} (hμ : toPoly μ ≠ 0) :
    toPoly (scaleMu c μ) ≠ 0 := by
  intro h0
  have := toPoly_scaleMu_comp c μ
  rw [h0, zero_comp] at this
  exact hμ ((mul_eq_zero.mp this.symm).resolve_left (C_ne_zero.mpr (pow_ne_zero _ hc)))

/-- If `S ∣ μ(r)` and `r' ≡ c r (mod S)`, then `S ∣ μ_c(r')`. -/
lemma dvd_scaleMu_comp {S r r' μ : CPoly R} {c : R} (hμ : ∃ q : R[X], (toPoly μ).comp (toPoly r) = toPoly S * q)
    (hr' : toPoly S ∣ toPoly r' - C c * toPoly r) :
    ∃ q : R[X], (toPoly (scaleMu c μ)).comp (toPoly r') = toPoly S * q := by
  obtain ⟨q, hq⟩ := hμ
  have h1 : toPoly r' - C c * toPoly r ∣
      ((toPoly (scaleMu c μ)).map C).eval (toPoly r') -
        ((toPoly (scaleMu c μ)).map C).eval (C c * toPoly r) :=
    sub_dvd_eval_sub _ _ _
  rw [eval_map, eval_map] at h1
  change _ ∣ (toPoly (scaleMu c μ)).comp (toPoly r') -
    (toPoly (scaleMu c μ)).comp (C c * toPoly r) at h1
  have h2 : (toPoly (scaleMu c μ)).comp (C c * toPoly r) =
      C (c ^ (μ.length - 1)) * (toPoly S * q) := by
    rw [← hq]
    have : C c * toPoly r = (C c * X).comp (toPoly r) := by rw [mul_comp, C_comp, X_comp]
    rw [this, ← comp_assoc, toPoly_scaleMu_comp, mul_comp, C_comp]
  obtain ⟨u, hu⟩ := hr'.trans h1
  exact ⟨u + C (c ^ (μ.length - 1)) * q, by rw [mul_add, ← hu, h2]; ring⟩

lemma toPoly_extraDen (S r : CPoly R) (ks : List ℕ) :
    toPoly (extraDen S r ks) = (ks.map fun (k : ℕ) ↦ toPoly (gcd S (sub r [((k : ℕ) : R)])) ^ k).prod := by
  unfold extraDen
  induction ks with
  | nil => simp
  | cons k ks ih =>
    simp only [List.map_cons, List.foldr_cons, toPoly_mul, List.prod_cons, toPoly_powC]
    rw [ih]

lemma pow_gcd_dvd_extraDen (S r : CPoly R) {ks : List ℕ} {k : ℕ} (hk : k ∈ ks) :
    toPoly (gcd S (sub r [(k : R)])) ^ k ∣ toPoly (extraDen S r ks) := by
  rw [toPoly_extraDen]
  exact List.dvd_prod (List.mem_map_of_mem hk)

lemma extraDen_ne_zero (S r : CPoly R) (hS0 : toPoly S ≠ 0) (ks : List ℕ) :
    toPoly (extraDen S r ks) ≠ 0 := by
  rw [toPoly_extraDen]
  refine List.prod_ne_zero fun h0 ↦ ?_
  obtain ⟨k, -, hk⟩ := List.mem_map.mp h0
  refine pow_ne_zero _ (fun hg ↦ hS0 ?_) hk
  have := (egcd_dvd S (sub r [(k : R)])).1
  rw [← toPoly_gcd, hg] at this
  exact zero_dvd_iff.mp this

variable {S K : Type*} [Field S] [CharZero S] [Differential S[X]] [Field K] [Algebra S[X] K]
variable [IsFractionRing S[X] K] [Differential K] [DifferentialAlgebra S[X] K]
variable [HasRatRoots R] [HasNatTest R]

local notation "φ" => algebraMap S[X] K

omit [HasRatRoots R] [HasNatTest R] in
/-- The simple-part properties, over `R` and over the extension `S`. -/
lemma simplePart_props_map (ι : R →+* S) (Gd : CPoly R) (hGd0 : toPoly Gd ≠ 0) :
    (toPoly (simplePart Gd) ≠ 0 ∧ IsCoprime (toPoly (simplePart Gd)) (derivative (toPoly Gd))) ∧
    ((toPoly (simplePart Gd)).map ι ≠ 0 ∧ (toPoly (simplePart Gd)).map ι ∣ (toPoly Gd).map ι ∧
      IsCoprime ((toPoly (simplePart Gd)).map ι) (derivative ((toPoly Gd).map ι)) ∧
      (∀ p : S[X], Irreducible p → p ∣ (toPoly (simplePart Gd)).map ι →
        ¬p ∣ derivative ((toPoly Gd).map ι)) ∧
      (∀ p : S[X], Irreducible p → p ∣ (toPoly Gd).map ι → ¬p ∣ derivative ((toPoly Gd).map ι) →
        p ∣ (toPoly (simplePart Gd)).map ι) ∧ Squarefree ((toPoly (simplePart Gd)).map ι)) := by
  obtain ⟨S₀, G₁, G, q₁, q₂, σ, τ, σ', τ', E1, E2, E3, E4, E5, E6⟩ := simplePart_data Gd hGd0
  obtain ⟨h1, -, h2, -, -, -⟩ := simplePart_props hGd0 E1 E2 E3 E4 E5 E6
  refine ⟨⟨h1, h2⟩, ?_⟩
  have hGdS : (toPoly Gd).map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hGd0
  have m := fun P : R[X] ↦ P.map ι
  refine simplePart_props (F := S) hGdS (S₀ := S₀.map ι) (G₁ := G₁.map ι) (G := G.map ι)
    (q₁ := q₁.map ι) (q₂ := q₂.map ι) (σ := σ.map ι) (τ := τ.map ι) (σ' := σ'.map ι)
    (τ' := τ'.map ι) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [E1, Polynomial.map_mul]
  · rw [← Polynomial.map_mul, ← E2, derivative_map]
  · rw [← E3]; simp only [Polynomial.map_add, Polynomial.map_mul, derivative_map]
  · rw [E4, Polynomial.map_mul]
  · rw [← Polynomial.map_mul, ← E5, derivative_map]
  · rw [← E6]; simp only [Polynomial.map_add, Polynomial.map_mul, derivative_map]

/-- **Soundness.** -/
theorem rdeRationalW_sound (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {μ Gn Gd A D Y D' : CPoly R} (hD0 : toPoly D ≠ 0) (hGd0 : toPoly Gd ≠ 0)
    (h : rdeRationalW μ Gn Gd A D = some (Y, D')) :
    (φ ((toPoly Y).map ι) / φ ((toPoly D').map ι))′ +
        φ ((toPoly Gn).map ι) / φ ((toPoly Gd).map ι) *
          (φ ((toPoly Y).map ι) / φ ((toPoly D').map ι)) =
      φ ((toPoly A).map ι) / φ ((toPoly D).map ι) := by
  simp only [rdeRationalW, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨Y₀, hY₀, rfl, rfl⟩ := h
  have hs := odeSolveFull_sound hY₀
  simp only [toPoly_mul, toPoly_sub, toPoly_deriv] at hs
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  have hE0 : toPoly (extraDenW μ Gn Gd) ≠ 0 :=
    extraDen_ne_zero _ _ ((simplePart_props_map ι Gd hGd0).1.1) _
  have hφD : φ ((toPoly D).map ι) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hD0)
  have hφE : φ ((toPoly (extraDenW μ Gn Gd)).map ι) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hE0)
  have hφGd : φ ((toPoly Gd).map ι) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr ((Polynomial.map_ne_zero_iff ι.injective).mpr hGd0)
  have := congrArg (fun P : R[X] ↦ φ (P.map ι)) hs
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, map_add, map_mul,
    map_sub, ← derivative_map] at this
  rw [toPoly_mul, Polynomial.map_mul, map_mul]
  rw [Derivation.leibniz_div, Derivation.leibniz, deriv_algebraMap, deriv_algebraMap,
    deriv_algebraMap, hD, hD, hD]
  simp only [smul_eq_mul, derivative_mul, map_add, map_mul] at this ⊢
  field_simp
  linear_combination this

/-- **Completeness**, over every extension of the constants, given `muCheck` and the absence of
nonzero solutions of the homogeneous equation. -/
theorem rdeRationalW_complete (ι : R →+* S) (hD : ∀ P : S[X], P′ = derivative P)
    {μ Gn Gd A D : CPoly R} (hD0 : toPoly D ≠ 0) (hGn0 : toPoly Gn ≠ 0) (hGd0 : toPoly Gd ≠ 0)
    (hcop : IsCoprime (toPoly Gn) (toPoly Gd)) (hμ0 : toPoly μ ≠ 0)
    (hμ : ∃ q : R[X], (toPoly μ).comp (toPoly (residuePolyW Gn Gd)) = toPoly (simplePart Gd) * q)
    (hhom : ∀ y : K, y′ + φ ((toPoly Gn).map ι) / φ ((toPoly Gd).map ι) * y = 0 → y = 0)
    (h : rdeRationalW μ Gn Gd A D = none) (y : K) :
    y′ + φ ((toPoly Gn).map ι) / φ ((toPoly Gd).map ι) * y ≠
      φ ((toPoly A).map ι) / φ ((toPoly D).map ι) := by
  intro hy
  have hinj : Function.Injective φ := IsFractionRing.injective S[X] K
  have hιinj : Function.Injective ι := ι.injective
  obtain ⟨⟨hS0, hcopR⟩, hS0', hSd', hcop', hScop', hS', -⟩ := simplePart_props_map ι Gd hGd0
  obtain ⟨t, ht⟩ := residuePolyW_bezout Gn Gd hS0 hcopR.symm
  obtain ⟨q, hq⟩ := hμ
  have hE0 : toPoly (extraDenW μ Gn Gd) ≠ 0 := extraDen_ne_zero _ _ hS0 _
  -- the extra denominator
  have hES' : ∀ k : ℕ, k ≠ 0 → ((toPoly μ).map ι).eval (k : S) = 0 →
      ∀ p : S[X], Irreducible p → p ∣ (toPoly (simplePart Gd)).map ι →
      p ∣ (toPoly (residuePolyW Gn Gd)).map ι - C (k : S) →
      p ^ k ∣ (toPoly (extraDenW μ Gn Gd)).map ι := by
    intro k hk hev p hp hpS hpr
    have hevR : (toPoly μ).eval ((k : ℚ) : R) = 0 := by
      rw [← map_natCast ι, eval_map, eval₂_at_apply] at hev
      rw [Rat.cast_natCast]
      exact hιinj (by rw [hev, map_zero])
    have hmem : k ∈ natCands (HasRatRoots.ratRoots μ) :=
      mem_natCands hk (HasRatRoots.ratRoots_spec _ _ hμ0 hevR)
    have hTk : (toPoly (gcd (simplePart Gd) (sub (residuePolyW Gn Gd) [(k : R)]))).map ι ^ k ∣
        (toPoly (extraDenW μ Gn Gd)).map ι := by
      rw [← Polynomial.map_pow]
      exact Polynomial.map_dvd ι (pow_gcd_dvd_extraDen _ _ hmem)
    refine (pow_dvd_pow_of_dvd ?_ k).trans hTk
    have hb := egcd_spec (simplePart Gd) (sub (residuePolyW Gn Gd) [(k : R)])
    rw [← toPoly_gcd] at hb
    have := congrArg (Polynomial.map ι) hb
    simp only [Polynomial.map_add, Polynomial.map_mul, toPoly_sub, Polynomial.map_sub,
      toPoly_cons, toPoly_nil, mul_zero, add_zero, Polynomial.map_natCast, map_natCast] at this
    rw [← this]
    have hpr' : p ∣ (toPoly (residuePolyW Gn Gd)).map ι - (k : S[X]) := by
      rwa [← C_eq_natCast]
    exact dvd_add (Dvd.dvd.mul_left hpS _) (Dvd.dvd.mul_left hpr' _)
  simp only [rdeRationalW, Option.map_eq_none_iff] at h
  -- make the data opaque
  generalize hE : extraDenW μ Gn Gd = E at h hE0 hES'
  generalize hr : residuePolyW Gn Gd = r at ht hq hES'
  generalize hSp : simplePart Gd = Sp at hS0 hcopR hS0' hSd' hcop' hScop' hS' ht hq hES'
  generalize hD' : mul D E = D' at h
  have hD'0 : toPoly D' ≠ 0 := by rw [← hD', toPoly_mul]; exact mul_ne_zero hD0 hE0
  have hDS : (toPoly D).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr hD0
  have hGdS : (toPoly Gd).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr hGd0
  have hES : (toPoly E).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hιinj).mpr hE0
  have hφD : φ ((toPoly D).map ι) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hDS
  have hφGd : φ ((toPoly Gd).map ι) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hGdS
  have hφE : φ ((toPoly E).map ι) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hES
  -- the residue polynomial and the annihilator, over `S`
  have hrS : (toPoly Sp).map ι ∣ (toPoly r).map ι * derivative ((toPoly Gd).map ι) -
      (toPoly Gn).map ι := by
    refine ⟨-(t.map ι), ?_⟩
    have := congrArg (Polynomial.map ι) ht
    simp only [Polynomial.map_add, Polynomial.map_mul, ← derivative_map] at this
    rw [← this]; ring
  have hμS : (toPoly Sp).map ι ∣ ((toPoly μ).map ι).comp ((toPoly r).map ι) :=
    ⟨q.map ι, by rw [← Polynomial.map_comp, hq, Polynomial.map_mul]⟩
  -- the denominator bound
  obtain ⟨Ys, hYs⟩ := rde_denominator_rational_W (K := K) hD _ _ _ _ _ _ _ _ hDS hGdS
    (hcop.map (mapRingHom ι)) hS' hrS hμS hES' y hy
  have hD'S : (toPoly D').map ι = (toPoly D).map ι * (toPoly E).map ι := by
    rw [← hD', toPoly_mul, Polynomial.map_mul]
  have hφD' : φ ((toPoly D').map ι) ≠ 0 := by
    rw [hD'S, map_mul]; exact mul_ne_zero hφD hφE
  have hyY : y = φ Ys / φ ((toPoly D').map ι) := by
    rw [hD'S, ← hYs]; field_simp
  -- the polynomial ODE, in the form of the solver
  generalize hP₁ : mul Gd D' = P₁ at h
  generalize hP₀ : sub (mul Gn D') (mul Gd (deriv D')) = P₀ at h
  have hP₁poly : toPoly P₁ = toPoly Gd * toPoly D' := by rw [← hP₁, toPoly_mul]
  have hP₀poly : toPoly P₀ = toPoly Gn * toPoly D' - toPoly Gd * derivative (toPoly D') := by
    rw [← hP₀, toPoly_sub, toPoly_mul, toPoly_mul, toPoly_deriv]
  have hder : ∀ Y : S[X], (φ Y / φ ((toPoly D').map ι))′ =
      (φ (derivative Y) * φ ((toPoly D').map ι) - φ Y * φ (derivative ((toPoly D').map ι))) /
        φ ((toPoly D').map ι) ^ 2 := fun Y ↦ by
    rw [Derivation.leibniz_div, deriv_algebraMap, deriv_algebraMap, hD, hD]
    simp only [smul_eq_mul]
    ring
  -- `P₀ ≠ 0`: otherwise `1 / D'` solves the homogeneous equation
  have hP₀ne : toPoly P₀ ≠ 0 := by
    intro h0
    rw [hP₀poly] at h0
    have h0S := congrArg (Polynomial.map ι) h0
    simp only [Polynomial.map_sub, Polynomial.map_mul, ← derivative_map, Polynomial.map_zero] at h0S
    have h0K := congrArg φ h0S
    simp only [map_sub, map_mul, map_zero] at h0K
    have := hhom (1 / φ ((toPoly D').map ι)) (by
      rw [← map_one φ, hder, derivative_one, map_zero, map_one]
      field_simp
      linear_combination h0K)
    exact one_ne_zero (by rwa [div_eq_zero_iff, or_iff_left hφD'] at this)
  have htP₀ : trim P₀ ≠ [] := fun h0 ↦ hP₀ne ((trim_eq_nil_iff _).mp h0)
  have hP₁ne : toPoly P₁ ≠ 0 := by rw [hP₁poly]; exact mul_ne_zero hGd0 hD'0
  have htP₁ : trim P₁ ≠ [] := fun h0 ↦ hP₁ne ((trim_eq_nil_iff _).mp h0)
  have hd₀ := (natDegree_toPoly_of_trim_ne_nil htP₀).1
  have hd₁ := (natDegree_toPoly_of_trim_ne_nil htP₁).1
  have hdgeq : odeDg P₁ P₀ = max ((toPoly P₁).natDegree - 1) (toPoly P₀).natDegree := by
    rw [odeDg, hd₀, hd₁]
    congr 1
  -- the pivot bound
  have htD' : trim D' ≠ [] := fun h0 ↦ hD'0 ((trim_eq_nil_iff _).mp h0)
  obtain ⟨hdD', -, -⟩ := natDegree_toPoly_of_trim_ne_nil htD'
  have hkb : ∀ k, odePiv P₁ P₀ k = 0 → k ≤ pivBoundW Gn Gd D' := fun k hk ↦ by
    rw [odePiv, ← coeff_toPoly, ← coeff_toPoly, hdgeq, hP₁poly, hP₀poly] at hk
    unfold pivBoundW
    rcases rde_pivot_W (toPoly Gn) (toPoly Gd) (toPoly D') hGn0 hGd0 hD'0
      (hP₀poly ▸ hP₀ne) k hk with hle | ⟨hdeg, hkeq⟩
    · exact (hle.trans hdD'.le).trans (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      have htGn : trim Gn ≠ [] := fun h0 ↦ hGn0 ((trim_eq_nil_iff _).mp h0)
      have htGd : trim Gd ≠ [] := fun h0 ↦ hGd0 ((trim_eq_nil_iff _).mp h0)
      obtain ⟨hdGn, hlGn, -⟩ := natDegree_toPoly_of_trim_ne_nil htGn
      obtain ⟨hdGd, hlGd, -⟩ := natDegree_toPoly_of_trim_ne_nil htGd
      have hlen : (trim Gn).length + 1 = (trim Gd).length := by
        have := List.length_pos_of_ne_nil htGn
        have := List.length_pos_of_ne_nil htGd
        omega
      rw [ite_eq_left hlen]
      have hkeq' : ((trim D').length - 1 : ℕ) - lead (trim Gn) / lead (trim Gd) = (k : R) := by
        rw [hkeq, ← hdD', ← hlGn, ← hlGd, ← hdGn, ← hdGd, coeff_natDegree, coeff_natDegree]
      rw [(HasNatTest.natTest_spec _ k).mpr hkeq']
      exact le_rfl
  -- the solver would have found `Ys`
  refine odeSolveFull_complete_map ι htP₀ hkb h ⟨Ys, ?_⟩
  rw [hP₁poly, hP₀poly]
  simp only [Polynomial.map_mul, Polynomial.map_sub, toPoly_mul, ← derivative_map]
  apply hinj
  simp only [map_add, map_mul, map_sub]
  have hy' := hy
  rw [hyY, hder] at hy'
  have hφD'2 : φ ((toPoly D').map ι) ^ 2 ≠ 0 := pow_ne_zero _ hφD'
  rw [hD'S, map_mul] at hy' hφD' hφD'2 ⊢
  field_simp at hy'
  field_simp
  linear_combination hy'

end Spec

end CPoly
