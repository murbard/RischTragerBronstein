import RischTragerBronstein.Mixed.KWExact
import RischTragerBronstein.Mixed.KWClass
import RischTragerBronstein.Computable.NestPPoly
import RischTragerBronstein.Mixed.KPLiouville
import RischTragerBronstein.Algebraic.HypGlue
import RischTragerBronstein.Algebraic.SuperSecondKind

/-!
# `b(x) y` with `y² = p(x)` over an exponential: the logarithmic part

`S : SuperData C L` with `n = 2`, `x′ = η x` (`x` an exponential over the differential field `C`),
`p(0) = 1` (so the points over `x = 0` are `P± = (0, ±1)`), `deg p` odd, and `η x` without
algebraic solutions `α′ = η α` except `α = 0`. Let `b y = v′ + ∑ cᵢ uᵢ′/uᵢ` be a Liouville form, `b y`
without poles over `x ≠ 0`.

At every place over `x ≠ 0` the logarithms have order `0` (`ordAt_logs_zeroW`), so the divisor of
`uᵢ` is `rᵢ P₊ + sᵢ P₋ − (rᵢ + sᵢ)∞`.

* `ke_liouville_nontors`: if `P₊ − ∞` is not torsion, then `rᵢ = sᵢ` (otherwise `uᵢ x^{−sᵢ}` or its
  inverse shows `|rᵢ − sᵢ| (P₊ − ∞)` principal), `uᵢ x^{−sᵢ}` is a constant of `C`, the logarithmic
  part lies in `C`, and `b y = (a y)′` (`exact_of_even`).
* `ke_liouville_tors`: if `W = W₀ + W₁ y` has divisor `N(P₊ − ∞)`, then `uᵢᴺ x^{−N sᵢ} W^{sᵢ − rᵢ}` is a
  constant, the logarithmic part is `ℓ + c′ W′/W` (`ℓ ∈ C`, `c′ ∈ C`), and with
  `W′/W = E + B y` (`logDeriv_ab`), `b y = (a y)′ + c′ B y`.
-/

open Polynomial IntermediateField HahnSeries LaurentSeries Classical

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L)

/-- The divisor `P₊ = (0, β₀)`. -/
def gammaP {K : Type*} [Field K] [DecidableEq K] (β₀ : K) : K × K → ℕ :=
  fun Q ↦ if Q = (0, β₀) then 1 else 0

/-- `x` as an element of `C(x, y)`. -/
noncomputable def xE : C⟮S.x⟯⟮S.y⟯ := S.polyX (X - Polynomial.C 0)

lemma xE_val : ((S.xE : C⟮S.x⟯⟮S.y⟯) : L) = S.x := by
  letI := algebraAdjoinSimple (F := C) S.x
  show ((algebraMap C[X] C⟮S.x⟯ (X - Polynomial.C 0) : C⟮S.x⟯) : L) = S.x
  rw [algebraMap_adjoinSimple]
  simp

lemma x_ne_zero : S.x ≠ 0 := fun h ↦ S.htr ⟨X, X_ne_zero, by rw [aeval_X, h]⟩

lemma xE_ne : S.xE ≠ 0 := fun h ↦ S.x_ne_zero (by rw [← S.xE_val, h]; rfl)

lemma ordAt_xE (α β : K) (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    S.ordAt K S.xE α β = if α = 0 then (if β = 0 then (S.n : ℤ) else 1) else 0 := by
  rw [xE, S.ordAt_X_sub 0 α β hv, map_zero]

variable {S}

/-- The points over `x = 0` are `(0, ±1)` when `n = 2`, `p(0) = 1`. -/
lemma over_zero (hn2 : S.n = 2) {β₀ : K} (hp0 : β₀ ^ 2 = algebraMap C K (S.p.eval 0)) {β : K}
    (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval 0) : β = β₀ ∨ β = -β₀ := by
  rw [eval_zero_map, ← hp0, hn2] at hv
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hv

lemma neg_ne_self {β₀ : K} (hβ₀ : β₀ ≠ 0) : -β₀ ≠ β₀ := by
  intro h
  have : (2 : K) * β₀ = 0 := by linear_combination -h
  exact hβ₀ ((mul_eq_zero.mp this).resolve_left two_ne_zero)

/-- An element with no zeros and poles over `x ≠ 0` has the orders `r` at `P₊`, `s` at `P₋`. -/
lemma ordAt_form (hn2 : S.n = 2) {β₀ : K} (hp0 : β₀ ^ 2 = algebraMap C K (S.p.eval 0))
    (hβ₀ : β₀ ≠ 0) (z : C⟮S.x⟯⟮S.y⟯)
    (hgen : ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 → S.ordAt K z α β = 0)
    (α β : K) (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    S.ordAt K z α β = if α = 0 then (if β = β₀ then S.ordAt K z 0 β₀ else S.ordAt K z 0 (-β₀)) else 0 := by
  by_cases hα : α = 0
  · subst hα
    rw [if_pos rfl]
    rcases over_zero hn2 hp0 hv with rfl | rfl
    · rw [if_pos rfl]
    · rw [if_neg (neg_ne_self hβ₀)]
  · rw [if_neg hα]
    exact hgen α β hv hα

variable (S)

/-- **The Liouville data, normalized**: `ℚ`-independent constants `d j ∈ C` and logarithms `w j`
without zeros or poles over `x ≠ 0`. -/
theorem ke_prep (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η * X))
    (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
    (hgood : ∀ α : K, α ≠ 0 → α′ ≠ algebraMap C K η * α)
    (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
    (hn1 : 1 < S.n) (f : L) (hf : f ∈ C⟮S.x⟯⟮S.y⟯) (b : L) (hb : b ∈ C⟮S.x⟯)
    (hfb : f = b * S.y)
    (hreg : ∀ α β : K, β ≠ 0 → β ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 →
      0 ≤ S.ordAt K ⟨f, hf⟩ α β)
    {ι : Type*} (s : Finset ι) (c u : ι → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : f = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ (k : ℕ) (d : ℕ → C) (w : ℕ → L) (hw : ∀ j < k, w j ∈ C⟮S.x⟯⟮S.y⟯ ∧ w j ≠ 0),
      (∀ q : ℕ → ℚ, ∑ j ∈ Finset.range k, (q j : C) * d j = 0 → ∀ j < k, q j = 0) ∧
      f = v′ + ∑ j ∈ Finset.range k, algebraMap C L (d j) * logDeriv (w j) ∧
      (∀ j < k, (algebraMap C L (d j))′ = 0) ∧
      ∀ j (hj : j < k), ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 →
        S.ordAt K ⟨w j, (hw j hj).1⟩ α β = 0 := by
  classical
  obtain ⟨k, d, w, ⟨hd, hw, hind⟩, hsum⟩ :=
    logSum_qindep (C⟮S.x⟯⟮S.y⟯).toSubfield s c u hc (fun i hi ↦ hu i hi)
  set d' : ℕ → C := fun jj ↦ if h : jj < k then Classical.choose (hconstC (d jj) (hd jj h)) else 0
    with hd'def
  have hdd : ∀ jj < k, algebraMap C L (d' jj) = d jj := fun jj hjj ↦ by
    simp only [hd'def, dif_pos hjj]
    exact Classical.choose_spec (hconstC (d jj) (hd jj hjj))
  have hind' : ∀ q : ℕ → ℚ, ∑ jj ∈ Finset.range k, (q jj : C) * d' jj = 0 →
      ∀ jj < k, q jj = 0 := by
    intro q hq
    apply hind q
    rw [← map_zero (algebraMap C L), ← hq, map_sum]
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [map_mul, map_ratCast, hdd jj (Finset.mem_range.mp hjj)]
  have hw' : ∀ jj < k, w jj ∈ C⟮S.x⟯⟮S.y⟯ ∧ w jj ≠ 0 := fun jj hjj ↦ ⟨(hw jj hjj).2, (hw jj hjj).1⟩
  have heq' : f = v′ + ∑ jj ∈ Finset.range k, algebraMap C L (d' jj) * logDeriv (w jj) := by
    rw [heq, hsum]
    congr 1
    refine Finset.sum_congr rfl fun jj hjj ↦ ?_
    rw [hdd jj (Finset.mem_range.mp hjj)]
  refine ⟨k, d', w, hw', hind', heq', fun j hj ↦ by rw [hdd j hj]; exact hd j hj,
    fun j hj α β hvβ hα ↦ ?_⟩
  have heq'' : f = v′ + ∑ jj ∈ Finset.range k, algebraMap C L (d' jj) * ((w jj)′ / w jj) := by
    rw [heq']; rfl
  have hgα : α′ ≠ ((Polynomial.C η * X).map (algebraMap C K)).eval α := by
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_mul, eval_C, eval_X]
    exact hgood α hα
  by_cases hβ : β = 0
  · subst hβ
    have he : (S.p.map (algebraMap C K)).eval α = 0 := by rw [← hvβ, zero_pow S.hn.ne']
    exact S.ordAt_logs_zero_classW (Polynomial.C η * X) hx hK k d' w hw' hind' v f hv hf heq'' b hb
      1 one_pos hn1 (by rw [pow_one]; exact hfb) α he hgα j hj
  · exact S.ordAt_logs_zeroW (Polynomial.C η * X) hx hK k d' w hw' hind' v f hv hf heq'' α β hvβ
      hgα (hreg α β hβ hvβ hα) j hj


omit [CharZero K] [IsAlgClosed K] in
lemma gammaP_apply (β₀ α β : K) : gammaP β₀ (α, β) = if α = 0 ∧ β = β₀ then 1 else 0 := by
  simp [gammaP, Prod.ext_iff]

omit [CharZero K] in
lemma sum_fin_two (hn2 : S.n = 2) (f : Fin S.n → K) :
    ∑ i, f i = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ := by
  rw [Fintype.sum_equiv (finCongr hn2) f (fun j ↦ f ((finCongr hn2).symm j)) (fun i ↦ by simp),
    Fin.sum_univ_two]
  rfl

/-- **`P₊ − ∞` is not torsion when `p(0)` is not a square in `C`**: an integral `w` with
`ord_{P₊} w ≥ 1`, `ord_{P₋} w = 0` has `w = P₀(x) + P₁(x) y` and `P₀(0) ± P₁(0) β₀` its constant
terms at `P±`, so `β₀ = −P₀(0)/P₁(0) ∈ C`. -/
theorem nontors_of_nonsquare (hn2 : S.n = 2) (β₀ : K) (hp0 : β₀ ^ 2 = algebraMap C K (S.p.eval 0))
    (hβ₀ : β₀ ≠ 0) (hns : ∀ c : C, algebraMap C K c ≠ β₀) :
    ∀ N : ℕ, 0 < N → ¬ S.IsPrincipalS K (gammaP β₀) N := by
  rintro N hN ⟨w, hw0, hint, hord⟩
  letI := algebraAdjoinSimple (F := C) S.x
  obtain ⟨a, hwa, hpoly⟩ := S.integral_of_regular' K w hint
  choose P hP using hpoly
  have hai : ∀ i, algebraMap C⟮S.x⟯ C⟮S.x⟯⟮S.y⟯ (a i) = S.polyX (P i) := fun i ↦ by
    have : a i = algebraMap C[X] C⟮S.x⟯ (P i) :=
      Subtype.ext (by rw [hP i, algebraMap_adjoinSimple])
    rw [this]; rfl
  -- the constant term of the expansion at `(0, β)`
  have hc : ∀ (β : K) (hβ : β ≠ 0) (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval 0),
      (S.embXY 0 β hβ hv w).coeff 0 =
        ∑ i : Fin S.n, algebraMap C K ((P i).eval 0) * β ^ (i : ℕ) := by
    intro β hβ hv
    rw [hwa, map_sum, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_pow, hai, S.embXY_polyX, S.embXY_gen, ← map_pow, ← map_mul,
      show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, coeff_coe_powerSeries, PowerSeries.coeff_zero_eq_constantCoeff,
      map_mul, map_pow, branchY_const, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      Polynomial.coeff_coe, coeff_zero_eq_eval_zero, eval_comp]
    simp only [eval_add, eval_X, eval_C, add_zero, eval_map_algebraMap]
    rw [aeval_def, eval₂_at_zero, coeff_zero_eq_eval_zero]
  have hvP : β₀ ^ S.n = (S.p.map (algebraMap C K)).eval 0 := by rw [hn2, hp0, eval_zero_map]
  have hvM : (-β₀) ^ S.n = (S.p.map (algebraMap C K)).eval 0 := by
    rw [hn2, neg_sq, hp0, eval_zero_map]
  have hnb : -β₀ ≠ 0 := neg_ne_zero.mpr hβ₀
  have hoP : S.ordAt K w 0 β₀ = N := by
    rw [hord (0, β₀) hvP, gammaP]; simp
  have hoM : S.ordAt K w 0 (-β₀) = 0 := by
    rw [hord (0, -β₀) hvM, gammaP]; simp [neg_ne_self hβ₀]
  rw [S.ordAt_nb w 0 β₀ hβ₀ hvP] at hoP
  rw [S.ordAt_nb w 0 (-β₀) hnb hvM] at hoM
  have heP : (S.embXY 0 β₀ hβ₀ hvP w).coeff 0 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_order (by rw [hoP]; exact_mod_cast hN)
  have hneM : S.embXY 0 (-β₀) hnb hvM w ≠ 0 := S.embXY_ne_zero 0 (-β₀) hnb hvM hw0
  have heM : (S.embXY 0 (-β₀) hnb hvM w).coeff 0 ≠ 0 := by
    have := (not_congr HahnSeries.coeff_order_eq_zero).mpr hneM
    rwa [hoM] at this
  rw [hc, sum_fin_two S hn2] at heP heM
  simp only [pow_zero, mul_one, pow_one] at heP heM
  set c0 := (P ⟨0, by omega⟩).eval 0
  set c1 := (P ⟨1, by omega⟩).eval 0
  have hc1 : algebraMap C K c1 ≠ 0 := by
    intro h; rw [h, zero_mul, add_zero] at heP; rw [h, zero_mul, add_zero] at heM; exact heM heP
  apply hns (-c0 / c1)
  rw [map_div₀, map_neg, div_eq_iff hc1]
  linear_combination -heP

section Logs

variable (hn2 : S.n = 2) (β₀ : K) (hp0 : β₀ ^ 2 = algebraMap C K (S.p.eval 0))
  (hβ₀ : β₀ ≠ 0) (hcop : Nat.Coprime S.n S.p.natDegree)
  (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η * X))
include hn2 hp0 hβ₀ hcop hx

lemma logDeriv_x : logDeriv S.x = algebraMap C L η := by
  rw [logDeriv, hx, map_mul, aeval_C, aeval_X, mul_div_assoc, div_self S.x_ne_zero, mul_one]

omit hcop hx in
/-- The orders of `z x^{−s}`, `s` the order of `z` at `P₋`. -/
lemma ordAt_shift (z : C⟮S.x⟯⟮S.y⟯) (hz : z ≠ 0) (e : ℤ)
    (hgen : ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 → S.ordAt K z α β = 0)
    (α β : K) (hv : β ^ S.n = (S.p.map (algebraMap C K)).eval α) :
    S.ordAt K (z * S.xE ^ e) α β = if α = 0 then
      (if β = β₀ then S.ordAt K z 0 β₀ + e else S.ordAt K z 0 (-β₀) + e) else 0 := by
  rw [S.ordAt_mul hv hz (zpow_ne_zero _ S.xE_ne), S.ordAt_zpow hv, S.ordAt_xE α β hv,
    ordAt_form hn2 hp0 hβ₀ z hgen α β hv]
  by_cases hα : α = 0
  · subst hα
    rcases over_zero hn2 hp0 hv with rfl | rfl
    · simp [hβ₀]
    · simp [neg_ne_self hβ₀, hβ₀]
  · simp [hα]

/-- **Without torsion, the logarithmic derivative of a logarithm is in `C`.** -/
lemma ke_log_nontors (hnt : ∀ N : ℕ, 0 < N → ¬ S.IsPrincipalS K (gammaP β₀) N)
    (z : C⟮S.x⟯⟮S.y⟯) (hz : z ≠ 0)
    (hgen : ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 → S.ordAt K z α β = 0) :
    ∃ ℓ : C, logDeriv (z : L) = algebraMap C L ℓ := by
  set r := S.ordAt K z 0 β₀ with hr
  set s := S.ordAt K z 0 (-β₀) with hs
  set y1 := z * S.xE ^ (-s) with hy1
  have hy10 : y1 ≠ 0 := mul_ne_zero hz (zpow_ne_zero _ S.xE_ne)
  have hord := fun (α β : K) hv ↦ S.ordAt_shift hn2 β₀ hp0 hβ₀ z hz (-s) hgen α β hv
  simp only [← hr, ← hs] at hord
  have hrs : r = s := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · apply hnt (s - r).toNat (by omega)
      refine ⟨y1⁻¹, inv_ne_zero hy10, fun α β hv ↦ ?_, fun Q hQ ↦ ?_⟩
      · rw [S.ordAt_inv hv, hord α β hv]
        split_ifs <;> omega
      · obtain ⟨α, β⟩ := Q
        rw [S.ordAt_inv hQ, hord α β hQ, gammaP_apply β₀]
        by_cases hα : α = 0
        · subst hα
          rcases over_zero hn2 hp0 hQ with rfl | rfl
          · simp [hβ₀]; omega
          · simp [neg_ne_self hβ₀, hβ₀]
        · simp [hα]
    · apply hnt (r - s).toNat (by omega)
      refine ⟨y1, hy10, fun α β hv ↦ ?_, fun Q hQ ↦ ?_⟩
      · rw [hord α β hv]
        split_ifs <;> omega
      · obtain ⟨α, β⟩ := Q
        rw [hord α β hQ, gammaP_apply β₀]
        by_cases hα : α = 0
        · subst hα
          rcases over_zero hn2 hp0 hQ with rfl | rfl
          · simp [hβ₀]; omega
          · simp [neg_ne_self hβ₀, hβ₀]
        · simp [hα]
  have h0 : ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α → S.ordAt K y1 α β = 0 := by
    intro α β hv
    rw [hord α β hv]
    split_ifs <;> omega
  obtain ⟨γ, hγ⟩ := S.const_of_ordAt_zero K hcop y1 hy10 h0
  have hγ0 : γ ≠ 0 := fun h ↦ hy10 (Subtype.ext (by rw [hγ, h, map_zero]; rfl))
  have hzL : (z : L) = algebraMap C L γ * S.x ^ s := by
    have e1 : ((y1 : C⟮S.x⟯⟮S.y⟯) : L) = (z : L) * S.x ^ (-s) := by
      rw [hy1, IntermediateField.coe_mul]
      rw [show ((S.xE ^ (-s) : C⟮S.x⟯⟮S.y⟯) : L) = ((S.xE : C⟮S.x⟯⟮S.y⟯) : L) ^ (-s) from
        map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val S.xE _, S.xE_val]
    rw [← hγ, e1, mul_assoc, ← zpow_add₀ S.x_ne_zero, neg_add_cancel, zpow_zero, mul_one]
  refine ⟨logDeriv γ + s * η, ?_⟩
  rw [hzL, logDeriv_mul (a := algebraMap C L γ) (b := S.x ^ s) ((_root_.map_ne_zero _).mpr hγ0)
    (zpow_ne_zero _ S.x_ne_zero),
    logDeriv_algebraMap, logDeriv_zpow' _ S.x_ne_zero, S.logDeriv_x hn2 β₀ hp0 hβ₀ hcop η hx, map_add,
    map_mul, map_intCast]

/-- **With a torsion witness `W`, a logarithm contributes a multiple of `W′/W`.** -/
lemma ke_log_tors (N : ℕ) (hN : 0 < N) (W : C⟮S.x⟯⟮S.y⟯) (hW : W ≠ 0)
    (hWord : ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K W α β = N * gammaP β₀ (α, β))
    (z : C⟮S.x⟯⟮S.y⟯) (hz : z ≠ 0)
    (hgen : ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 → S.ordAt K z α β = 0) :
    ∃ (ℓ : C) (e : ℚ), logDeriv (z : L) = algebraMap C L ℓ + (e : L) * logDeriv (W : L) := by
  set r := S.ordAt K z 0 β₀ with hr
  set s := S.ordAt K z 0 (-β₀) with hs
  set y1 := z ^ N * S.xE ^ (-(N * s)) * W ^ (-(r - s)) with hy1
  have hzN : z ^ N ≠ 0 := pow_ne_zero _ hz
  have hy10 : y1 ≠ 0 := mul_ne_zero (mul_ne_zero hzN (zpow_ne_zero _ S.xE_ne)) (zpow_ne_zero _ hW)
  have h0 : ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α → S.ordAt K y1 α β = 0 := by
    intro α β hv
    rw [S.ordAt_mul hv (mul_ne_zero hzN (zpow_ne_zero _ S.xE_ne)) (zpow_ne_zero _ hW),
      S.ordAt_mul hv hzN (zpow_ne_zero _ S.xE_ne), S.ordAt_pow hv, S.ordAt_zpow hv,
      S.ordAt_zpow hv, S.ordAt_xE α β hv, hWord α β hv, gammaP_apply β₀,
      ordAt_form hn2 hp0 hβ₀ z hgen α β hv, ← hr, ← hs]
    by_cases hα : α = 0
    · subst hα
      rcases over_zero hn2 hp0 hv with rfl | rfl
      · simp [hβ₀]; ring
      · simp [neg_ne_self hβ₀, hβ₀]
    · simp [hα]
  obtain ⟨γ, hγ⟩ := S.const_of_ordAt_zero K hcop y1 hy10 h0
  have hγ0 : γ ≠ 0 := fun h ↦ hy10 (Subtype.ext (by rw [hγ, h, map_zero]; rfl))
  have hWL : (W : L) ≠ 0 := fun h ↦ hW (Subtype.ext h)
  have hzL0 : (z : L) ≠ 0 := fun h ↦ hz (Subtype.ext h)
  have hx1 : ((S.xE ^ (-(N * s)) : C⟮S.x⟯⟮S.y⟯) : L) = S.x ^ (-((N : ℤ) * s)) := by
    rw [show ((S.xE ^ (-(N * s)) : C⟮S.x⟯⟮S.y⟯) : L) = ((S.xE : C⟮S.x⟯⟮S.y⟯) : L) ^ (-(N * s)) from
      map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val S.xE _, S.xE_val]
  have hW1 : ((W ^ (-(r - s)) : C⟮S.x⟯⟮S.y⟯) : L) = (W : L) ^ (-(r - s)) :=
    map_zpow₀ (C⟮S.x⟯⟮S.y⟯).val W _
  have e1 : ((y1 : C⟮S.x⟯⟮S.y⟯) : L) = (z : L) ^ N * S.x ^ (-((N : ℤ) * s)) * (W : L) ^ (-(r - s)) := by
    rw [hy1, IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_pow, hx1, hW1]
  have ha : (z : L) ^ N * S.x ^ (-((N : ℤ) * s)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hzL0) (zpow_ne_zero _ S.x_ne_zero)
  have hb : (W : L) ^ (-(r - s)) ≠ 0 := zpow_ne_zero _ hWL
  have hl := congrArg logDeriv (e1.symm.trans hγ)
  rw [logDeriv_mul (a := (z : L) ^ N * S.x ^ (-((N : ℤ) * s))) (b := (W : L) ^ (-(r - s))) ha hb,
    logDeriv_mul (a := (z : L) ^ N) (b := S.x ^ (-((N : ℤ) * s))) (pow_ne_zero _ hzL0)
      (zpow_ne_zero _ S.x_ne_zero),
    logDeriv_pow, logDeriv_zpow' _ S.x_ne_zero, logDeriv_zpow' _ hWL, S.logDeriv_x hn2 β₀ hp0 hβ₀ hcop η hx,
    logDeriv_algebraMap] at hl
  have hN0 : (N : L) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨(logDeriv γ + N * s * η) / N, ((r - s : ℤ) : ℚ) / N, ?_⟩
  simp only [map_div₀, map_add, map_mul, map_natCast, map_intCast, map_sub, Rat.cast_div,
    Rat.cast_intCast, Rat.cast_natCast, Int.cast_sub, Rat.cast_sub]
  field_simp
  push_cast at hl
  change _ = logDeriv (algebraMap C L γ) at hl
  rw [logDeriv_algebraMap] at hl
  linear_combination hl

end Logs

section Main

variable (hn2 : S.n = 2) (β₀ : K) (hp0 : β₀ ^ 2 = algebraMap C K (S.p.eval 0))
  (hβ₀ : β₀ ≠ 0) (hcop : Nat.Coprime S.n S.p.natDegree)
  (η : C) (hx : S.x′ = aeval S.x (Polynomial.C η * X))
  (hK : ∀ c : C, (algebraMap C K c)′ = algebraMap C K c′)
  (hgood : ∀ α : K, α ≠ 0 → α′ ≠ algebraMap C K η * α)
  (hconstC : ∀ z : L, z′ = 0 → z ∈ Set.range (algebraMap C L))
include hn2 hp0 hβ₀ hcop hx hK hgood hconstC

/-- **Without torsion of `P₊ − ∞`, a Liouville form for `b y` forces `b y = (a y)′`.** -/
theorem ke_liouville_nontors (hnt : ∀ N : ℕ, 0 < N → ¬ S.IsPrincipalS K (gammaP β₀) N)
    (b : L) (hb : b ∈ C⟮S.x⟯) (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    (hreg : ∀ α β : K, β ≠ 0 → β ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 →
      0 ≤ S.ordAt K ⟨b * S.y, hbm⟩ α β)
    {ι : Type*} (s : Finset ι) (c u : ι → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ a ∈ C⟮S.x⟯, b * S.y = (a * S.y)′ := by
  classical
  obtain ⟨k, d, w, hw, -, heq', hdc, hord⟩ :=
    S.ke_prep η hx hK hgood hconstC (by omega) _ hbm b hb rfl hreg s c u hc hu v hv heq
  have hl : ∀ j < k, ∃ ℓ : C, logDeriv (w j) = algebraMap C L ℓ := fun j hj ↦
    S.ke_log_nontors hn2 β₀ hp0 hβ₀ hcop η hx hnt ⟨w j, (hw j hj).1⟩
      (fun h ↦ (hw j hj).2 (congrArg Subtype.val h)) (hord j hj)
  choose! ℓ hℓ using hl
  have hsum : ∑ j ∈ Finset.range k, algebraMap C L (d j) * logDeriv (w j) =
      algebraMap C L (∑ j ∈ Finset.range k, d j * ℓ j) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j hj ↦ by rw [hℓ j (Finset.mem_range.mp hj), map_mul]
  rw [hsum] at heq'
  obtain ⟨a, ha, hae⟩ := S.exact_of_even (Polynomial.C η * X) hx 1 one_pos (by omega) b hb v hv _
    (IntermediateField.algebraMap_mem _ _) (by rw [pow_one]; exact heq')
  exact ⟨a, ha, by simpa using hae⟩

/-- **With a witness `W = W₀ + W₁ y` of `N(P₊ − ∞)`, a Liouville form for `b y` forces
`b y = (a y)′ + c B y`**, `W′/W = E + B y`. -/
theorem ke_liouville_tors (N : ℕ) (hN : 0 < N) (W : C⟮S.x⟯⟮S.y⟯) (hW : W ≠ 0)
    (hWord : ∀ α β : K, β ^ S.n = (S.p.map (algebraMap C K)).eval α →
      S.ordAt K W α β = N * gammaP β₀ (α, β))
    (W0 W1 : L) (hW0 : W0 ∈ C⟮S.x⟯) (hW1 : W1 ∈ C⟮S.x⟯) (hWe : (W : L) = W0 + W1 * S.y)
    (hNm : W0 ^ 2 - W1 ^ 2 * aeval S.x S.p ≠ 0)
    (b : L) (hb : b ∈ C⟮S.x⟯) (hbm : b * S.y ∈ C⟮S.x⟯⟮S.y⟯)
    (hreg : ∀ α β : K, β ≠ 0 → β ^ S.n = (S.p.map (algebraMap C K)).eval α → α ≠ 0 →
      0 ≤ S.ordAt K ⟨b * S.y, hbm⟩ α β)
    {ι : Type*} (s : Finset ι) (c u : ι → L) (hc : ∀ i ∈ s, (c i)′ = 0)
    (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ C⟮S.x⟯⟮S.y⟯) (v : L) (hv : v ∈ C⟮S.x⟯⟮S.y⟯)
    (heq : b * S.y = v′ + ∑ i ∈ s, c i * logDeriv (u i)) :
    ∃ a ∈ C⟮S.x⟯, ∃ e : C, (algebraMap C L e)′ = 0 ∧ b * S.y = (a * S.y)′ + algebraMap C L e *
      ((W0 * (W1′ + W1 * (aeval S.x (mapCoeffs S.p + Polynomial.C η * X * derivative S.p) /
        ((S.n : L) * aeval S.x S.p))) - W0′ * W1) / (W0 ^ 2 - W1 ^ 2 * aeval S.x S.p) * S.y) := by
  classical
  obtain ⟨k, d, w, hw, -, heq', hdc, hord⟩ :=
    S.ke_prep η hx hK hgood hconstC (by omega) _ hbm b hb rfl hreg s c u hc hu v hv heq
  have hl : ∀ j < k, ∃ (ℓ : C) (e : ℚ), logDeriv (w j) =
      algebraMap C L ℓ + (e : L) * logDeriv (W : L) := fun j hj ↦
    S.ke_log_tors hn2 β₀ hp0 hβ₀ hcop η hx N hN W hW hWord ⟨w j, (hw j hj).1⟩
      (fun h ↦ (hw j hj).2 (congrArg Subtype.val h)) (hord j hj)
  choose! ℓ e hℓ using hl
  set ℓs : C := ∑ j ∈ Finset.range k, d j * ℓ j
  set es : C := ∑ j ∈ Finset.range k, d j * (e j : C)
  have hsum : ∑ j ∈ Finset.range k, algebraMap C L (d j) * logDeriv (w j) =
      algebraMap C L ℓs + algebraMap C L es * logDeriv (W : L) := by
    rw [map_sum, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j hj ↦ by
      rw [hℓ j (Finset.mem_range.mp hj), map_mul, map_mul, map_ratCast]; ring
  have hes : (algebraMap C L es)′ = 0 := by
    rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [map_mul, map_ratCast, Derivation.leibniz, hdc j (Finset.mem_range.mp hj),
      Tower.NestP.deriv_ratCastK (K := L) (e j)]
    simp
  rw [hsum] at heq'
  -- `W′/W = E + B y`
  set P := aeval S.x S.p with hP
  set r := aeval S.x (mapCoeffs S.p + Polynomial.C η * X * derivative S.p) / ((S.n : L) * P)
    with hr
  have hy2 : S.y ^ 2 = P := by rw [← hn2]; exact S.hy
  have hyd : S.y′ = r * S.y := by
    rw [S.deriv_yW (Polynomial.C η * X) hx, hr]; ring
  have hab := logDeriv_ab (y := S.y) W0 W1 P r hy2 hyd hNm
  rw [hWe, hab] at heq'
  have hcl : DerivClosed C⟮S.x⟯ := S.derivClosedXW (Polynomial.C η * X) hx
  have hrm : r ∈ C⟮S.x⟯ := S.r_memW (Polynomial.C η * X) hx
  have hPm : P ∈ C⟮S.x⟯ := by
    letI := algebraAdjoinSimple (F := C) S.x
    rw [hP, ← algebraMap_adjoinSimple (F := C) S.x S.p]; exact SetLike.coe_mem _
  have hNm' : W0 ^ 2 - W1 ^ 2 * P ∈ C⟮S.x⟯ :=
    sub_mem (pow_mem hW0 2) (mul_mem (pow_mem hW1 2) hPm)
  set B := (W0 * (W1′ + W1 * r) - W0′ * W1) / (W0 ^ 2 - W1 ^ 2 * P) with hB
  have hBm : B ∈ C⟮S.x⟯ := div_mem (sub_mem (mul_mem hW0 (add_mem (hcl _ hW1) (mul_mem hW1 hrm)))
    (mul_mem (hcl _ hW0) hW1)) hNm'
  set E := (W0 * W0′ - W1 * (W1′ + W1 * r) * P) / (W0 ^ 2 - W1 ^ 2 * P) with hE
  have hEm : E ∈ C⟮S.x⟯ := div_mem (sub_mem (mul_mem hW0 (hcl _ hW0))
    (mul_mem (mul_mem hW1 (add_mem (hcl _ hW1) (mul_mem hW1 hrm))) hPm)) hNm'
  have heq2 : (b - algebraMap C L es * B) * S.y ^ 1 = v′ + (algebraMap C L ℓs + algebraMap C L es * E) := by
    rw [pow_one]; linear_combination heq'
  obtain ⟨a, ha, hae⟩ := S.exact_of_even (Polynomial.C η * X) hx 1 one_pos (by omega) _
    (sub_mem hb (mul_mem (IntermediateField.algebraMap_mem _ _) hBm)) v hv _
    (add_mem (IntermediateField.algebraMap_mem _ _) (mul_mem (IntermediateField.algebraMap_mem _ _) hEm))
    heq2
  refine ⟨a, ha, es, hes, ?_⟩
  simp only [pow_one] at hae
  linear_combination hae

end Main

end SuperData

end Differential
