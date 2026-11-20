import RischTragerBronstein.Mixed.KRPoints
import RischTragerBronstein.Algebraic.KRDft

/-!
# The `yʲ`-projection of logarithmic derivatives with divisors over `x = 0`

`w ∈ C(x, y)` with `Supp w` (no zeros or poles over `x ≠ 0`), `gcd(j, n) = 1`:

* `four_dl_shift`: if the orders of `w` at the `P_k` are invariant under `k ↦ k + c`, `0 < c < n`,
  then `four j (dl w) = 0`;
* `wt w = ∏_k (σ_k w)^{c_n(k)}` (Ramanujan exponents): `four j (dl (wt w)) = n · four j (dl w)`
  (`four_dl_wt`), `rv (wt w) m = ∑_k c_n(k) rv w (m + k)` (`rv_wt`);
* `four_dl_tors`: if `W` has orders `N c_n(m)` at `P_m`, then
  `four j (dl w) = e · four j (dl W)` for a constant `e ∈ C`.
-/

open Polynomial IntermediateField Ramanujan

set_option linter.unusedSectionVars false

namespace Differential

namespace SuperData

variable {C L K : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
variable [Differential C] [Differential L] [DifferentialAlgebra C L]
variable [Field K] [CharZero K] [Algebra C K] [Differential K] [IsAlgClosed K]
variable (S : SuperData C L) (ω : C[X]) (hx : S.x′ = aeval S.x ω)
variable (ζ : C) (hζ : IsPrimitiveRoot ζ S.n)
variable (β₀ : K) (hβ₀ : β₀ ≠ 0) (hv0 : β₀ ^ S.n = (S.p.map (algebraMap C K)).eval 0)
variable (hcop : Nat.Coprime S.n S.p.natDegree) (j : Fin S.n) (hj : Nat.Coprime (j : ℕ) S.n)

include hζ hj in
lemma zeta_pow_ne_one (c : ℕ) (hc0 : 0 < c) (hcn : c < S.n) : ζ ^ (c * (j : ℕ)) ≠ 1 := by
  intro h
  have := (hζ.pow_eq_one_iff_dvd _).mp h
  have h2 : S.n ∣ c := (Nat.Coprime.dvd_of_dvd_mul_right hj.symm this)
  exact absurd (Nat.le_of_dvd hc0 h2) (by omega)

include hj in
lemma j_ne_zero (hn1 : 1 < S.n) : (j : ℕ) ≠ 0 := by
  intro h
  rw [h, Nat.coprime_zero_left] at hj
  omega

include hx hζ hβ₀ hv0 hcop hj in
/-- **A shift-invariant divisor has no `yʲ`-projection.** -/
theorem four_dl_shift (hn1 : 1 < S.n) (w : C⟮S.x⟯⟮S.y⟯) (hw0 : w ≠ 0) (hw : S.Supp (K := K) w)
    (c : ℕ) (hc0 : 0 < c) (hcn : c < S.n) (hsh : ∀ k, S.rv ζ β₀ w (k + c) = S.rv ζ β₀ w k) :
    S.four ζ hζ j (S.dl ω hx w) = 0 := by
  have hcw : S.cj ζ hζ c w ≠ 0 := S.cj_ne_zero ζ hζ c w hw0
  set u := S.cj ζ hζ c w * w⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero hcw (inv_ne_zero hw0)
  have hsu : S.Supp (K := K) u := by
    refine S.supp_mul _ _ hcw (inv_ne_zero hw0) (S.supp_cj ζ hζ c w hw) ?_
    rw [← zpow_neg_one]; exact S.supp_zpow w hw (-1)
  have hru : ∀ k < S.n, S.rv ζ β₀ u k = 0 := fun k _ ↦ by
    rw [hu, S.rv_mul ζ hζ β₀ hv0 _ _ hcw (inv_ne_zero hw0), ← zpow_neg_one,
      S.rv_zpow ζ hζ β₀ hv0, S.rv_cj ζ hζ β₀ hβ₀ hv0, hsh]
    ring
  have h0 := S.four_dl_zero ω hx ζ hζ β₀ hβ₀ hv0 hcop j (S.j_ne_zero j hj hn1) u hu0 hsu hru
  rw [hu, S.dl_mul ω hx _ _ hcw (inv_ne_zero hw0), ← zpow_neg_one, S.dl_zpow ω hx _ hw0,
    S.dl_cj ω hx ζ hζ, S.four_add, S.four_cj, S.four_intCast_mul] at h0
  have hz : ζ ^ (c * (j : ℕ)) - 1 ≠ 0 := sub_ne_zero.mpr (S.zeta_pow_ne_one ζ hζ j hj c hc0 hcn)
  have h1 : S.cst (ζ ^ (c * (j : ℕ)) - 1) * S.four ζ hζ j (S.dl ω hx w) = 0 := by
    rw [show S.cst (ζ ^ (c * (j : ℕ)) - 1) = S.cst (ζ ^ (c * (j : ℕ))) - 1 from
      Subtype.ext (by simp [cst])]
    push_cast at h0
    linear_combination h0
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd ((algebraMap C L).injective (by
      have := congrArg Subtype.val h
      simpa [cst] using this)) hz
  · exact h

/-- **Swapping a correlation** (indices mod `n`, `b` even). -/
lemma corr_swap {R : Type*} [CommRing R] (n : ℕ) (hn : 0 < n) (a b : ℕ → R)
    (ha : ∀ k, a (k % n) = a k) (hb : ∀ k, b (k % n) = b k) (hbs : ∀ k ≤ n, b (n - k) = b k)
    (m : ℕ) : ∑ k ∈ Finset.range n, b k * a (m + k) = ∑ k ∈ Finset.range n, a (n - k) * b (m + k) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  set A : ZMod n → R := fun x ↦ a x.val
  set B : ZMod n → R := fun x ↦ b x.val
  have hA : ∀ k : ℕ, a k = A (k : ZMod n) := fun k ↦ by simp only [A, ZMod.val_natCast, ha]
  have hB : ∀ k : ℕ, b k = B (k : ZMod n) := fun k ↦ by simp only [B, ZMod.val_natCast, hb]
  have hBn : ∀ x : ZMod n, B (-x) = B x := fun x ↦ by
    simp only [B]
    by_cases hx : x = 0
    · rw [hx, neg_zero]
    · rw [ZMod.neg_val, if_neg hx]
      exact hbs _ (ZMod.val_lt x).le
  have hsum : ∀ f : ℕ → R, ∑ k ∈ Finset.range n, f k = ∑ x : ZMod n, f x.val := fun f ↦ by
    refine Finset.sum_bij' (fun k _ ↦ (k : ZMod n)) (fun x _ ↦ x.val) (fun _ _ ↦ Finset.mem_univ _)
      (fun x _ ↦ Finset.mem_range.mpr (ZMod.val_lt x))
      (fun k hk ↦ ZMod.val_natCast_of_lt (Finset.mem_range.mp hk)) (fun x _ ↦ ZMod.natCast_zmod_val x)
      (fun k hk ↦ by rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hk)])
  rw [hsum, hsum]
  simp only [hA, hB]
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  have h1 : ∑ x : ZMod n, B x * A ((m : ZMod n) + x) = ∑ y : ZMod n, B (y - m) * A y :=
    Fintype.sum_equiv (Equiv.addLeft (m : ZMod n)) _ _ (fun x ↦ by simp)
  have h2 : ∑ x : ZMod n, A (((n - x.val : ℕ) : ZMod n)) * B ((m : ZMod n) + x) =
      ∑ y : ZMod n, A y * B (m - y) := by
    refine Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ (fun x ↦ ?_)
    simp only [Equiv.neg_apply, sub_neg_eq_add]
    congr 2
    rw [Nat.cast_sub (ZMod.val_lt x).le, ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]
  rw [h1, h2]
  refine Fintype.sum_congr _ _ fun y ↦ ?_
  rw [show y - (m : ZMod n) = -((m : ZMod n) - y) by ring, hBn, mul_comm]

/-- The Ramanujan element `∏_k (σ_k w)^{c_n(k)}`. -/
noncomputable def wt (w : C⟮S.x⟯⟮S.y⟯) : C⟮S.x⟯⟮S.y⟯ :=
  ∏ k ∈ Finset.range S.n, (S.cj ζ hζ k w) ^ (ramC S.n k)

lemma wt_ne (w : C⟮S.x⟯⟮S.y⟯) (hw0 : w ≠ 0) : S.wt ζ hζ w ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (S.cj_ne_zero ζ hζ k w hw0)

include hζ in
lemma supp_wt (w : C⟮S.x⟯⟮S.y⟯) (hw0 : w ≠ 0) (hw : S.Supp (K := K) w) :
    S.Supp (K := K) (S.wt ζ hζ w) :=
  S.supp_prod _ _ (fun k _ ↦ zpow_ne_zero _ (S.cj_ne_zero ζ hζ k w hw0))
    (fun k _ ↦ S.supp_zpow _ (S.supp_cj ζ hζ k w hw) _)

include hζ hβ₀ hv0 in
lemma rv_wt (w : C⟮S.x⟯⟮S.y⟯) (hw0 : w ≠ 0) (m : ℕ) :
    S.rv ζ β₀ (S.wt ζ hζ w) m = ∑ k ∈ Finset.range S.n, ramC S.n k * S.rv ζ β₀ w (m + k) := by
  rw [wt, S.rv_prod ζ hζ β₀ hv0 _ _ (fun k _ ↦ zpow_ne_zero _ (S.cj_ne_zero ζ hζ k w hw0))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [S.rv_zpow ζ hζ β₀ hv0, S.rv_cj ζ hζ β₀ hβ₀ hv0]

include hx hj in
/-- **`four j (dl (wt w)) = n four j (dl w)`.** -/
lemma four_dl_wt (w : C⟮S.x⟯⟮S.y⟯) (hw0 : w ≠ 0) :
    S.four ζ hζ j (S.dl ω hx (S.wt ζ hζ w)) = (S.n : C⟮S.x⟯⟮S.y⟯) * S.four ζ hζ j (S.dl ω hx w) := by
  classical
  rw [wt, S.dl_prod ω hx _ _ (fun k _ ↦ zpow_ne_zero _ (S.cj_ne_zero ζ hζ k w hw0)), S.four_sum]
  simp_rw [S.dl_zpow ω hx _ (S.cj_ne_zero ζ hζ _ w hw0), S.four_intCast_mul, S.dl_cj ω hx ζ hζ,
    S.four_cj]
  have hprim : IsPrimitiveRoot (ζ ^ (j : ℕ)) S.n := hζ.pow_of_coprime _ hj
  have key := sum_ramC_mul_pow S.hn hζ (ω := ζ ^ (j : ℕ)) (by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
  rw [if_pos hprim] at key
  have e : ∑ k ∈ Finset.range S.n, ((ramC S.n k : ℤ) : C⟮S.x⟯⟮S.y⟯) *
      (S.cst (ζ ^ (k * (j : ℕ))) * S.four ζ hζ j (S.dl ω hx w)) =
      S.cst (∑ k ∈ Finset.range S.n, (ramC S.n k : C) * (ζ ^ (j : ℕ)) ^ k) *
        S.four ζ hζ j (S.dl ω hx w) := by
    rw [S.cst_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [S.cst_mul, ← pow_mul, mul_comm (j : ℕ) k,
      show ((ramC S.n k : ℤ) : C⟮S.x⟯⟮S.y⟯) = S.cst (ramC S.n k : C) from Subtype.ext (by simp [cst])]
    ring
  rw [e, key, S.cst_natCast]

include hx hζ hβ₀ hv0 hcop hj in
/-- **With a witness `W` of `N Ψ`, the projection of a logarithm is a multiple of that of `W`.** -/
theorem four_dl_tors (hn1 : 1 < S.n) (N : ℕ) (hN : 0 < N) (W : C⟮S.x⟯⟮S.y⟯) (hW0 : W ≠ 0)
    (hW : S.Supp (K := K) W) (hWr : ∀ m, S.rv ζ β₀ W m = N * ramC S.n m)
    (w : C⟮S.x⟯⟮S.y⟯) (hw0 : w ≠ 0) (hw : S.Supp (K := K) w) :
    ∃ e : C, e′ = 0 ∧ S.four ζ hζ j (S.dl ω hx w) = S.cst e * S.four ζ hζ j (S.dl ω hx W) := by
  set r : ℕ → ℤ := fun k ↦ S.rv ζ β₀ w k with hr
  have hwt0 := S.wt_ne ζ hζ w hw0
  have hcW : ∀ k, S.cj ζ hζ k W ≠ 0 := fun k ↦ S.cj_ne_zero ζ hζ k W hW0
  set P := ∏ k ∈ Finset.range S.n, (S.cj ζ hζ k W) ^ (-(r (S.n - k))) with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (hcW k)
  set E := (S.wt ζ hζ w) ^ (N : ℤ) * P with hE
  have hE0 : E ≠ 0 := mul_ne_zero (zpow_ne_zero _ hwt0) hP0
  have hsE : S.Supp (K := K) E := S.supp_mul _ _ (zpow_ne_zero _ hwt0) hP0
    (S.supp_zpow _ (S.supp_wt ζ hζ w hw0 hw) _)
    (S.supp_prod _ _ (fun k _ ↦ zpow_ne_zero _ (hcW k))
      (fun k _ ↦ S.supp_zpow _ (S.supp_cj ζ hζ k W hW) _))
  have hrE : ∀ m < S.n, S.rv ζ β₀ E m = 0 := fun m _ ↦ by
    rw [hE, S.rv_mul ζ hζ β₀ hv0 _ _ (zpow_ne_zero _ hwt0) hP0, S.rv_zpow ζ hζ β₀ hv0,
      S.rv_wt ζ hζ β₀ hβ₀ hv0 w hw0, hP,
      S.rv_prod ζ hζ β₀ hv0 _ _ (fun k _ ↦ zpow_ne_zero _ (hcW k))]
    simp_rw [S.rv_zpow ζ hζ β₀ hv0, S.rv_cj ζ hζ β₀ hβ₀ hv0, hWr]
    have hsw := corr_swap S.n S.hn (fun k ↦ r k) (fun k ↦ ramC S.n k)
      (fun k ↦ S.rv_mod ζ hζ β₀ w k) (fun k ↦ by rw [← ramC_gcd, Nat.gcd_comm, ← Nat.gcd_rec,
        ramC_gcd])
      (fun k hk ↦ ramC_sub S.n k hk) m
    rw [Finset.mul_sum]
    have : ∑ k ∈ Finset.range S.n, -r (S.n - k) * ((N : ℤ) * ramC S.n (m + k)) =
        -((N : ℤ) * ∑ k ∈ Finset.range S.n, r (S.n - k) * ramC S.n (m + k)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    rw [this, ← hsw, Finset.mul_sum]
    simp only [hr]
    ring
  have h0 := S.four_dl_zero ω hx ζ hζ β₀ hβ₀ hv0 hcop j (S.j_ne_zero j hj hn1) E hE0 hsE hrE
  rw [hE, S.dl_mul ω hx _ _ (zpow_ne_zero _ hwt0) hP0, S.dl_zpow ω hx _ hwt0, S.four_add,
    S.four_intCast_mul, S.four_dl_wt ω hx ζ hζ j hj w hw0, hP,
    S.dl_prod ω hx _ _ (fun k _ ↦ zpow_ne_zero _ (hcW k)), S.four_sum] at h0
  simp_rw [S.dl_zpow ω hx _ (hcW _), S.four_intCast_mul, S.dl_cj ω hx ζ hζ, S.four_cj] at h0
  have hnN : ((S.n : C) * N) ≠ 0 := mul_ne_zero (by exact_mod_cast S.hn.ne') (by exact_mod_cast hN.ne')
  refine ⟨(∑ k ∈ Finset.range S.n, (r (S.n - k) : C) * ζ ^ (k * (j : ℕ))) / ((S.n : C) * N), ?_, ?_⟩
  · have hz : ∀ k : ℕ, (ζ ^ (k * (j : ℕ)))′ = 0 := fun k ↦
      LaurentSeries.deriv_root_of_unity S.hn (by
        rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
    rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, map_sum]
    have h1 : ∑ k ∈ Finset.range S.n, ((r (S.n - k) : C) * ζ ^ (k * (j : ℕ)))′ = 0 :=
      Finset.sum_eq_zero fun k _ ↦ by rw [Derivation.leibniz, hz, Derivation.map_intCast]; simp
    have h2 : ((S.n : C) * N)′ = 0 := by
      rw [Derivation.leibniz, Derivation.map_natCast, Derivation.map_natCast]; simp
    rw [h1, h2]; simp
  have hsum : ∑ k ∈ Finset.range S.n, ((-r (S.n - k) : ℤ) : C⟮S.x⟯⟮S.y⟯) *
      (S.cst (ζ ^ (k * (j : ℕ))) * S.four ζ hζ j (S.dl ω hx W)) =
      -(S.cst (∑ k ∈ Finset.range S.n, (r (S.n - k) : C) * ζ ^ (k * (j : ℕ))) *
        S.four ζ hζ j (S.dl ω hx W)) := by
    rw [S.cst_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [S.cst_mul, show ((-r (S.n - k) : ℤ) : C⟮S.x⟯⟮S.y⟯) = -S.cst (r (S.n - k) : C) from
      Subtype.ext (by simp [cst])]
    ring
  rw [hsum] at h0
  have hc : S.cst ((S.n : C) * N) * S.four ζ hζ j (S.dl ω hx w) =
      S.cst (∑ k ∈ Finset.range S.n, (r (S.n - k) : C) * ζ ^ (k * (j : ℕ))) *
        S.four ζ hζ j (S.dl ω hx W) := by
    rw [S.cst_mul, S.cst_natCast, S.cst_natCast]
    push_cast at h0
    linear_combination h0
  have hinv : S.cst (((S.n : C) * N)⁻¹) * S.cst ((S.n : C) * N) = 1 := by
    rw [← S.cst_mul, inv_mul_cancel₀ hnN]; exact Subtype.ext (by simp [cst])
  calc S.four ζ hζ j (S.dl ω hx w)
      = S.cst (((S.n : C) * N)⁻¹) * (S.cst ((S.n : C) * N) * S.four ζ hζ j (S.dl ω hx w)) := by
        rw [← mul_assoc, hinv, one_mul]
    _ = _ := by rw [hc, ← mul_assoc, ← S.cst_mul, div_eq_mul_inv, mul_comm (∑ k ∈ _, _)]

include hx hζ hβ₀ hv0 hcop hj in
/-- **Without torsion of `Ψ`, logarithms have no `yʲ`-projection.** -/
theorem four_dl_nontors (hn1 : 1 < S.n)
    (hnt : ∀ u : C⟮S.x⟯⟮S.y⟯, u ≠ 0 → S.Supp (K := K) u → ∀ M : ℕ, 0 < M →
      (∀ m < S.n, S.rv ζ β₀ u m = M * ramC S.n m) → False)
    (w : C⟮S.x⟯⟮S.y⟯) (hw0 : w ≠ 0) (hw : S.Supp (K := K) w) :
    S.four ζ hζ j (S.dl ω hx w) = 0 := by
  classical
  set r : ℕ → ℤ := fun k ↦ S.rv ζ β₀ w k with hr
  have hrper : ∀ k, r (k + S.n) = r k := fun k ↦ by
    simp only [hr]
    rw [← S.rv_mod ζ hζ β₀ w (k + S.n), Nat.add_mod_right, S.rv_mod ζ hζ β₀ w]
  have hwt0 := S.wt_ne ζ hζ w hw0
  have hswt := S.supp_wt ζ hζ w hw0 hw
  have hrwt : ∀ m, S.rv ζ β₀ (S.wt ζ hζ w) m = KRDft.corr S.n (fun k ↦ ramC S.n k) r m := fun m ↦ by
    rw [S.rv_wt ζ hζ β₀ hβ₀ hv0 w hw0 m, KRDft.corr]
  by_cases hv : ∃ m < S.n, KRDft.corr S.n (fun k ↦ ramC S.n k) r m ≠ 0
  · exfalso
    obtain ⟨h, p, q, hp, hq, hid⟩ := KRDft.corr_core hn1 hζ r hrper hv
    have hcw : ∀ k, S.cj ζ hζ k (S.wt ζ hζ w) ≠ 0 := fun k ↦ S.cj_ne_zero ζ hζ k _ hwt0
    set G := ∏ k ∈ Finset.range S.n, (S.cj ζ hζ k (S.wt ζ hζ w)) ^ ((q : ℤ) * h k) with hG
    have hG0 : G ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (hcw k)
    have hsG : S.Supp (K := K) G := S.supp_prod _ _ (fun k _ ↦ zpow_ne_zero _ (hcw k))
      (fun k _ ↦ S.supp_zpow _ (S.supp_cj ζ hζ k _ hswt) _)
    have hrG : ∀ m < S.n, S.rv ζ β₀ G m = p * ramC S.n m := fun m hm ↦ by
      rw [hG, S.rv_prod ζ hζ β₀ hv0 _ _ (fun k _ ↦ zpow_ne_zero _ (hcw k))]
      simp_rw [S.rv_zpow ζ hζ β₀ hv0, S.rv_cj ζ hζ β₀ hβ₀ hv0, hrwt]
      rw [← hid m hm, KRDft.corr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    rcases lt_or_gt_of_ne hp with hneg | hpos
    · refine hnt G⁻¹ (inv_ne_zero hG0) (by rw [← zpow_neg_one]; exact S.supp_zpow _ hsG _)
        (-p).toNat (by omega) fun m hm ↦ ?_
      rw [← zpow_neg_one, S.rv_zpow ζ hζ β₀ hv0, hrG m hm]
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    · exact hnt G hG0 hsG p.toNat (by omega) fun m hm ↦ by
        rw [hrG m hm, Int.toNat_of_nonneg hpos.le]
  · push Not at hv
    have h0 := S.four_dl_zero ω hx ζ hζ β₀ hβ₀ hv0 hcop j (S.j_ne_zero j hj hn1) _ hwt0 hswt
      (fun m hm ↦ by rw [hrwt]; exact hv m hm)
    rw [S.four_dl_wt ω hx ζ hζ j hj w hw0] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exfalso
      have : ((S.n : C⟮S.x⟯⟮S.y⟯) : L) = 0 := by rw [h]; rfl
      have e : ((S.n : C⟮S.x⟯⟮S.y⟯) : L) = (S.n : L) := by simp
      rw [e] at this
      exact S.hn.ne' (by exact_mod_cast this)
    · exact h

include hζ hβ₀ hv0 in
/-- **If `β₀ ∉ C`, a Galois automorphism shifts the points `P_k`**, and the orders of elements of
`C(x, y)` are invariant under the shift. -/
theorem galois_shift [Algebra.IsAlgebraic C K] (hn1 : 1 < S.n)
    (hns : ∀ c : C, algebraMap C K c ≠ β₀) :
    ∃ c, 0 < c ∧ c < S.n ∧ ∀ (w : C⟮S.x⟯⟮S.y⟯) (k : ℕ), S.rv ζ β₀ w (k + c) = S.rv ζ β₀ w k := by
  classical
  haveI : IsAlgClosure C K := ⟨inferInstance, inferInstance⟩
  haveI : Normal C K := IsAlgClosure.normal C K
  have hint : IsIntegral C β₀ := Algebra.IsIntegral.isIntegral β₀
  have hirr : Irreducible (minpoly C β₀) := minpoly.irreducible hint
  have hdeg : 2 ≤ (minpoly C β₀).natDegree := by
    by_contra hlt
    push Not at hlt
    have hpos := minpoly.natDegree_pos hint
    have h1 : (minpoly C β₀).natDegree = 1 := by omega
    obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.mp h1
    exact hns c hc
  -- a second root
  have hsep : (minpoly C β₀).Separable := hirr.separable
  have hspl : ((minpoly C β₀).map (algebraMap C K)).Splits := IsAlgClosed.splits _
  have hroots : ((minpoly C β₀).aroots K).card = (minpoly C β₀).natDegree := by
    rw [← natDegree_map (f := algebraMap C K)]
    exact (splits_iff_card_roots.mp hspl)
  have hnd : ((minpoly C β₀).aroots K).Nodup := nodup_roots (hsep.map)
  obtain ⟨β', hβ'r, hβ'ne⟩ : ∃ β' ∈ (minpoly C β₀).aroots K, β' ≠ β₀ := by
    by_contra hcon
    push Not at hcon
    have hsub : ((minpoly C β₀).aroots K).toFinset ⊆ {β₀} := fun z hz ↦
      Finset.mem_singleton.mpr (hcon z (Multiset.mem_toFinset.mp hz))
    have := Finset.card_le_card hsub
    rw [Multiset.toFinset_card_of_nodup hnd, hroots, Finset.card_singleton] at this
    omega
  have hβ'0 : aeval β' (minpoly C β₀) = 0 := (mem_aroots.mp hβ'r).2
  have hp0 : (S.p.map (algebraMap C K)).eval 0 = algebraMap C K (S.p.eval 0) := by
    rw [← map_zero (algebraMap C K), eval_map, eval₂_at_apply]
  -- `β'` is one of the `P_k`
  have hβ'v : β' ^ S.n = (S.p.map (algebraMap C K)).eval 0 := by
    have hdvd : minpoly C β₀ ∣ X ^ S.n - Polynomial.C (S.p.eval 0) := minpoly.dvd C β₀ (by
      rw [map_sub, map_pow, aeval_X, aeval_C, hv0, hp0, sub_self])
    obtain ⟨Q, hQ⟩ := hdvd
    have := congrArg (aeval β') hQ
    rw [map_mul, hβ'0, zero_mul, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at this
    rw [this, hp0]
  obtain ⟨c, hcn, hcβ⟩ := S.over_zero_k ζ hζ β₀ hβ₀ hv0 β' hβ'v
  have hc0 : c ≠ 0 := fun h ↦ hβ'ne (by rw [hcβ, h, bk, pow_zero, one_mul])
  obtain ⟨τ, hτ⟩ := minpoly.exists_algEquiv_of_root' (K := C) (Algebra.IsAlgebraic.isAlgebraic β₀) hβ'0
  refine ⟨c, Nat.pos_of_ne_zero hc0, hcn, fun w k ↦ ?_⟩
  have hk : τ (bk ζ β₀ k) = bk ζ β₀ (k + c) := by
    rw [bk, map_mul, map_pow, AlgEquiv.commutes, hτ, hcβ, bk, bk, pow_add]; ring
  rw [rv, rv, ← hk, ← S.ordAt_galois τ w 0 _ (S.bk_ne ζ hζ β₀ hβ₀ k) (S.bk_v ζ hζ β₀ hv0 k),
    map_zero]

end SuperData

end Differential
