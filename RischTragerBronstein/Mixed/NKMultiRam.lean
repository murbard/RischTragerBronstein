import RischTragerBronstein.Mixed.NKMultiData
import RischTragerBronstein.Mixed.NKMultiShape
import RischTragerBronstein.Curves.LScale

/-!
# Ramified roots above infinity: rotations, Galois action, window jets

For a root `ρ` above infinity (branch system `x = T^{−N}`) of order `−(N/e) s'` and leading
coefficient `c`:

* the rotation `T ↦ ζT` (`ζᴺ = 1`) maps `ρ` to the root with leading coefficient `ζ^{ord ρ} c`
  (`rot_lc`), and fixes `ρ` when `ζ^{ord ρ} = 1` and the data are unique (`root_rot_fixed_gen`);
* expansions along a root fixed by a primitive `M`-th root of unity are series in `T^M`
  (`embG_coeff_eq_zero_of_rot`);
* the window coefficients of an expansion along `rot ζ ρ` are those along `ρ` times `ζᵏ`
  (`embG_rot_coeff`), and an automorphism of `K/C` maps the expansion along `ρ` to the one along
  `σ ρ` (`lmap_embG`).
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section Rot

variable {K : Type*} [Field K]

lemma rot_lc {ζ : K} (hζ0 : ζ ≠ 0) (r : LaurentSeries K) :
    (rot ζ hζ0 r).coeff (rot ζ hζ0 r).order = ζ ^ r.order * r.coeff r.order := by
  rw [rot_order, rot_coeff]

lemma rot_one' (r : LaurentSeries K) : rot (1 : K) one_ne_zero r = r := by
  ext k
  simp [rot_coeff]

/-- `e ∣ h + sp t` is solvable when `gcd(sp, e) = 1`. -/
lemma exists_twist (e : ℕ) (he : 0 < e) (sp : ℤ) (hcop : Int.gcd sp e = 1) (h : ℤ) :
    ∃ t : ℕ, (e : ℤ) ∣ h + sp * t := by
  have hb := Int.gcd_eq_gcd_ab sp e
  rw [hcop] at hb
  set a := Int.gcdA sp e
  set b := Int.gcdB sp e
  refine ⟨((-h * a) % (e : ℤ)).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
  have h1 : (-h * a) % (e : ℤ) = -h * a - e * ((-h * a) / e) := by
    rw [Int.emod_def]
  rw [h1]
  refine ⟨h * b - sp * ((-h * a) / e), ?_⟩
  have : h = h * (sp * a + e * b) := by rw [← hb]; push_cast; ring
  linear_combination this

end Rot

namespace CurveData

section RamRoots

variable {C L K : Type*} [Field C] [CharZero C] [DecidableEq C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]

variable (S : CurveData C L)

/-- **A root with unique data is fixed by a rotation `ζ` with `ζ^{ord} = 1`.** -/
lemma root_rot_fixed_gen (N : ℕ) {ζ : K} (hζ0 : ζ ≠ 0) (hζN : ζ ^ N = 1)
    (l : List (LaurentSeries K)) (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    {r : LaurentSeries K} (hr : r ∈ l) (hord : ζ ^ r.order = 1)
    (huniq : ∀ r' ∈ l, r'.order = r.order → r'.coeff r'.order = r.coeff r.order → r' = r) :
    rot ζ hζ0 r = r := by
  have hmem : rot ζ hζ0 r ∈ l := mem_of_eval_prod l _ (by
    rw [← hl]; exact rot_root_inf ζ hζ0 N hζN S.F r (S.root_of_mem hl hr))
  refine huniq _ hmem (rot_order hζ0 r) ?_
  rw [rot_lc, hord, one_mul]

/-- **The rotation of a root is a root.** -/
lemma rot_mem (N : ℕ) {ζ : K} (hζ0 : ζ ≠ 0) (hζN : ζ ^ N = 1) (l : List (LaurentSeries K))
    (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    {r : LaurentSeries K} (hr : r ∈ l) : rot ζ hζ0 r ∈ l :=
  mem_of_eval_prod l _ (by rw [← hl]; exact rot_root_inf ζ hζ0 N hζN S.F r (S.root_of_mem hl hr))

/-- **The window coefficients along a rotated root.** -/
lemma embG_rot_coeff (N : ℕ) (hN : 0 < N) {ζ : K} (hζ0 : ζ ≠ 0) (hζN : ζ ^ N = 1)
    (r : LaurentSeries K) (hr : (S.F.map (infSub N)).eval r = 0)
    (hr' : (S.F.map (infSub N)).eval (rot ζ hζ0 r) = 0) (z : C⟮S.x⟯⟮S.y⟯) (k : ℤ) :
    (S.embG (infSub N) (infSub_injective N hN) (rot ζ hζ0 r) hr' z).coeff k =
      ζ ^ k * (S.embG (infSub N) (infSub_injective N hN) r hr z).coeff k := by
  rw [S.embG_eq_of_eq _ _ rfl hr' (rot_root_inf ζ hζ0 N hζN S.F r hr) z,
    S.embG_rot_inf ζ hζ0 N hN hζN r hr z, rot_coeff]

/-- **Expansions along a root fixed by a primitive `M`-th root of unity are series in `T^M`.** -/
lemma embG_coeff_eq_zero_of_rot (N : ℕ) (hN : 0 < N) {M : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ M)
    (hζ0 : ζ ≠ 0) (hζN : ζ ^ N = 1) (r : LaurentSeries K) (hr : (S.F.map (infSub N)).eval r = 0)
    (hfix : rot ζ hζ0 r = r) (z : C⟮S.x⟯⟮S.y⟯) (k : ℤ) (hk : ¬ (M : ℤ) ∣ k) :
    (S.embG (infSub N) (infSub_injective N hN) r hr z).coeff k = 0 := by
  refine coeff_eq_zero_of_rot_fixed hζ hζ0 _ ?_ k hk
  rw [← S.embG_rot_inf ζ hζ0 N hN hζN r hr z]
  exact S.embG_eq_of_eq _ _ hfix _ _ z

/-- **Galois action on expansions.** -/
lemma lmap_embG (σ : K ≃ₐ[C] K) (N : ℕ) (hN : 0 < N) (r : LaurentSeries K)
    (hr : (S.F.map (infSub N)).eval r = 0)
    (hr' : (S.F.map (infSub N)).eval (lmap (σ : K →+* K) r) = 0) (z : C⟮S.x⟯⟮S.y⟯) :
    lmap (σ : K →+* K) (S.embG (infSub N) (infSub_injective N hN) r hr z) =
      S.embG (infSub N) (infSub_injective N hN) (lmap (σ : K →+* K) r) hr' z := by
  have h := S.embG_comp_fix (lmap (σ : K →+* K)) (infSub N) (infSub_injective N hN)
    (RingHom.ext fun P ↦ lmap_infSub σ N P) r hr hr'
  exact congrArg (fun φ : C⟮S.x⟯⟮S.y⟯ →+* LaurentSeries K ↦ φ z) h

/-- **The Galois action on a ramified root**: `σ ρ` is a rotation of `ρ`. -/
lemma galois_rot (σ : K ≃ₐ[C] K) (N : ℕ) (hN : 0 < N) {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    (l : List (LaurentSeries K)) (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    {r : LaurentSeries K} (hr : r ∈ l) (hr0 : r ≠ 0) (e : ℕ) (he : 0 < e) (hdvd : e ∣ N) (sp : ℤ)
    (hcop : Int.gcd sp e = 1) (hord : r.order = -((N / e : ℕ) * sp))
    (hce : (r.coeff r.order) ^ e ∈ Set.range (algebraMap C K))
    (huniq : ∀ r₁ ∈ l, ∀ r₂ ∈ l, r₁.order = r₂.order → r₁.coeff r₁.order = r₂.coeff r₂.order →
      r₁ = r₂) :
    ∃ j : ℕ, lmap (σ : K →+* K) r = rot (ζ ^ j) (pow_ne_zero _ (hζ.ne_zero hN.ne')) r := by
  classical
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  set c := r.coeff r.order with hc
  have hc0 : c ≠ 0 := fun h ↦ hr0 (HahnSeries.coeff_order_eq_zero.mp h)
  -- `σ c = c u`, `uᵉ = 1`
  obtain ⟨γ, hγ⟩ := hce
  have hσce : σ c ^ e = c ^ e := by rw [← map_pow, ← hγ]; exact σ.commutes γ
  set u := σ c / c with hu
  have hue : u ^ e = 1 := by rw [hu, div_pow, hσce, div_self (pow_ne_zero _ hc0)]
  -- `ω = ζ^{N/e}` and `ζ^{ord} = ω^{−sp}` is a primitive `e`-th root of unity
  obtain ⟨d, hd⟩ := hdvd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hNe : N / e = d := by rw [hd, Nat.mul_div_cancel_left _ he]
  have hω : IsPrimitiveRoot (ζ ^ d) e := hζ.pow hN (by rw [hd, mul_comm])
  have hωs : IsPrimitiveRoot ((ζ ^ d) ^ (-sp)) e :=
    hω.zpow_of_gcd_eq_one (-sp) (by rw [Int.neg_gcd]; exact hcop)
  haveI : NeZero e := ⟨he.ne'⟩
  obtain ⟨j, -, hj⟩ := hωs.eq_pow_of_pow_eq_one hue
  refine ⟨j, ?_⟩
  have hζj0 : ζ ^ j ≠ 0 := pow_ne_zero _ hζ0
  have hζjN : (ζ ^ j) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  -- both are roots with the order of `r` and leading coefficient `σ c`
  have h1 : lmap (σ : K →+* K) r ∈ l := lmap_root_mem σ S.F N l hl hr
  have h2 : rot (ζ ^ j) hζj0 r ∈ l := S.rot_mem N hζj0 hζjN l hl hr
  refine huniq _ h1 _ h2 (by rw [lmap_order, rot_order]) ?_
  rw [lmap_order, lmap_coeff, rot_lc]
  have hpow : (ζ ^ j) ^ r.order = ((ζ ^ d) ^ (-sp)) ^ j := by
    rw [hord, hNe, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
      ← zpow_mul]
    congr 1
    ring
  rw [hpow, hj, hu, div_mul_cancel₀ _ hc0]
  rfl

/-- **The window jets of a ramified root, twisted by the leading coefficient, are rational.** -/
lemma jet_eigen [IsGalois C K] (N : ℕ) (hN : 0 < N) {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    (l : List (LaurentSeries K)) (hl : S.F.map (infSub N) = (l.map fun r ↦ X - Polynomial.C r).prod)
    {r : LaurentSeries K} (hr : r ∈ l) (hr0 : r ≠ 0) (e : ℕ) (he : 0 < e) (hdvd : e ∣ N) (sp : ℤ)
    (hcop : Int.gcd sp e = 1) (hord : r.order = -((N / e : ℕ) * sp))
    (hce : (r.coeff r.order) ^ e ∈ Set.range (algebraMap C K))
    (huniq : ∀ r₁ ∈ l, ∀ r₂ ∈ l, r₁.order = r₂.order → r₁.coeff r₁.order = r₂.coeff r₂.order →
      r₁ = r₂) (z : C⟮S.x⟯⟮S.y⟯) (h t : ℕ) (ht : (e : ℤ) ∣ h + sp * t) :
    (S.embG (infSub N) (infSub_injective N hN) r (S.root_of_mem hl hr) z).coeff
      ((h * (N / e) : ℕ) : ℤ) / (r.coeff r.order) ^ t ∈ Set.range (algebraMap C K) := by
  classical
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
  intro σ
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  obtain ⟨j, hj⟩ := S.galois_rot σ N hN hζ l hl hr hr0 e he hdvd sp hcop hord hce huniq
  have hζj0 : ζ ^ j ≠ 0 := pow_ne_zero _ hζ0
  have hζjN : (ζ ^ j) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hrr : (S.F.map (infSub N)).eval r = 0 := S.root_of_mem hl hr
  have hσr : (S.F.map (infSub N)).eval (lmap (σ : K →+* K) r) = 0 :=
    S.root_of_mem hl (lmap_root_mem σ S.F N l hl hr)
  have hrot : (S.F.map (infSub N)).eval (rot (ζ ^ j) hζj0 r) = 0 :=
    rot_root_inf (ζ ^ j) hζj0 N hζjN S.F r hrr
  set k : ℤ := ((h * (N / e) : ℕ) : ℤ) with hk
  -- the jet
  have ha : σ ((S.embG (infSub N) (infSub_injective N hN) r hrr z).coeff k) =
      (ζ ^ j) ^ k * (S.embG (infSub N) (infSub_injective N hN) r hrr z).coeff k := by
    have h1 := congrArg (fun y ↦ y.coeff k) (S.lmap_embG σ N hN r hrr hσr z)
    simp only [lmap_coeff] at h1
    rw [show ((σ : K →+* K) _) = σ _ from rfl] at h1
    rw [h1, S.embG_eq_of_eq _ _ hj hσr hrot z, S.embG_rot_coeff N hN hζj0 hζjN r hrr hrot z k]
  -- the leading coefficient
  have hc : σ (r.coeff r.order) = (ζ ^ j) ^ r.order * r.coeff r.order := by
    have h1 : (lmap (σ : K →+* K) r).coeff (lmap (σ : K →+* K) r).order =
        (rot (ζ ^ j) hζj0 r).coeff (rot (ζ ^ j) hζj0 r).order := by rw [hj]
    rw [lmap_order, lmap_coeff, rot_lc] at h1
    exact h1
  -- the twist cancels the rotation
  obtain ⟨d, hd⟩ := hdvd
  have hNe : N / e = d := by rw [hd, Nat.mul_div_cancel_left _ he]
  have htw : (ζ ^ j) ^ k = ((ζ ^ j) ^ r.order) ^ t := by
    rw [← zpow_natCast ((ζ ^ j) ^ r.order) t, ← zpow_mul]
    have h2 : (ζ ^ j) ^ (k - r.order * t) = 1 := by
      rw [← zpow_natCast ζ j, ← zpow_mul, hζ.zpow_eq_one_iff_dvd]
      obtain ⟨q, hq⟩ := ht
      refine ⟨j * q, ?_⟩
      rw [hk, hord, hNe, hd]
      push_cast
      linear_combination (j * d : ℤ) * hq
    rw [← mul_one ((ζ ^ j) ^ (r.order * t)), ← h2, ← zpow_add₀ hζj0]
    congr 1
    ring
  rw [map_div₀, map_pow, ha, hc, mul_pow, htw]
  field_simp

end RamRoots

end CurveData

end Curves
