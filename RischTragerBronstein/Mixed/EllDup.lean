import RischTragerBronstein.Mixed.FFMorph
import Mathlib.Tactic.LinearCombination

/-!
# The duplication estimate for elliptic curves over `K(X)`

For `E : y² = x³ + a x + b` with `a, b ∈ K[X]` and `Δ = 4a³ + 27b² ≠ 0`, the `x`-coordinate of `2P`
is `φ(u, v) / ψ(u, v)` when `x(P) = u / v`, with
`φ = u⁴ − 2a u²v² − 8b u v³ + a² v⁴`, `ψ = 4u³v + 4a u v³ + 4b v⁴`.
**`dup_height`**: with `D = max (deg a) (deg b)`,
`4 ht x ≤ ht (φ / ψ) + 11 D` and `ht (φ / ψ) ≤ 4 ht x + 2 D`, i.e. the naive height
`h(P) = ht (x P)` satisfies `|h (2P) − 4 h P| ≤ 11 D` — the doubling hypothesis of `MWTate`.

The lower bound comes from the resultant identities (Silverman, AEC VIII.4)
`f₁ φ − g₁ ψ = 4Δ v⁷` and `f₂ φ + g₂ ψ = 4Δ u⁷`, checked by `ring`, via `FFHeight.ht_ge_of_res`.
Degree bounds use a small weighted-degree estimator on expression trees (`WE`).
-/

open Polynomial

namespace FFHeight

variable {K : Type*} [Field K]

/-- **Lowest terms**: `p = num (p / q) · h`, `q = denom (p / q) · h` with `h ≠ 0`. -/
lemma exists_common (p q : K[X]) (hq : q ≠ 0) :
    ∃ h : K[X], h ≠ 0 ∧
      p = RatFunc.num (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) * h ∧
      q = RatFunc.denom (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) * h := by
  set x := algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q with hx
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hq' : algebraMap K[X] (RatFunc K) q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq
  have hd' : algebraMap K[X] (RatFunc K) (RatFunc.denom x) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (RatFunc.denom_ne_zero x)
  have key : RatFunc.num x * q = p * RatFunc.denom x := by
    apply hinj
    have h2 : algebraMap K[X] (RatFunc K) (RatFunc.num x) =
        x * algebraMap K[X] (RatFunc K) (RatFunc.denom x) :=
      (div_eq_iff hd').mp (RatFunc.num_div_denom x)
    rw [map_mul, map_mul, h2, hx]; field_simp
  have hnd := RatFunc.isCoprime_num_denom x
  obtain ⟨h, hh⟩ : RatFunc.denom x ∣ q :=
    hnd.symm.dvd_of_dvd_mul_right ⟨p, by linear_combination key⟩
  have hh0 : h ≠ 0 := by rintro rfl; rw [mul_zero] at hh; exact hq hh
  refine ⟨h, hh0, ?_, hh⟩
  have : RatFunc.denom x * (p - RatFunc.num x * h) = 0 := by
    linear_combination (-1 : K[X]) * key + RatFunc.num x * hh
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 (RatFunc.denom_ne_zero x)
  · exact sub_eq_zero.mp h0

/-- **Upper bound**: `ht (p / q) ≤ max (deg p) (deg q)`. -/
theorem ht_div_le (p q : K[X]) (hq : q ≠ 0) :
    ht (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) ≤
      max p.natDegree q.natDegree := by
  obtain ⟨h, hh0, hp, hq'⟩ := exists_common p q hq
  unfold ht
  by_cases hp0 : p = 0
  · have : algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q = 0 := by
      rw [hp0, map_zero, zero_div]
    rw [this]; simp
  have hn0 : RatFunc.num (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hp; exact hp0 hp
  refine max_le_max ?_ ?_
  · conv_rhs => rw [hp]
    rw [natDegree_mul hn0 hh0]; omega
  · conv_rhs => rw [hq']
    rw [natDegree_mul (RatFunc.denom_ne_zero _) hh0]; omega

/-- **Lower bound from a resultant identity**: common factors of `p, q` divide `R`. -/
theorem ht_ge_of_res (p q A B A' B' R u v : K[X]) (m : ℕ) (hq : q ≠ 0) (hc : IsCoprime u v)
    (hR : R ≠ 0) (h1 : A * p + B * q = R * v ^ m) (h2 : A' * p + B' * q = R * u ^ m) :
    max p.natDegree q.natDegree ≤
      ht (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q) + R.natDegree := by
  obtain ⟨h, hh0, hp, hq'⟩ := exists_common p q hq
  set x := algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) q
  have hdv1 : h ∣ R * v ^ m := ⟨A * RatFunc.num x + B * RatFunc.denom x, by
    rw [← h1]; conv_lhs => rw [hp, hq']
    ring⟩
  have hdv2 : h ∣ R * u ^ m := ⟨A' * RatFunc.num x + B' * RatFunc.denom x, by
    rw [← h2]; conv_lhs => rw [hp, hq']
    ring⟩
  obtain ⟨α, β, hab⟩ := (hc.pow (m := m) (n := m))
  have hdR : h ∣ R := by
    have : R = α * (R * u ^ m) + β * (R * v ^ m) := by linear_combination (-R) * hab
    rw [this]; exact dvd_add (dvd_mul_of_dvd_right hdv2 _) (dvd_mul_of_dvd_right hdv1 _)
  have hhR : h.natDegree ≤ R.natDegree := natDegree_le_of_dvd hdR hR
  unfold ht
  refine max_le ?_ ?_
  · by_cases hn0 : RatFunc.num x = 0
    · rw [hn0, zero_mul] at hp; rw [hp, natDegree_zero]; exact Nat.zero_le _
    · rw [hp, natDegree_mul hn0 hh0]
      have := le_max_left (RatFunc.num x).natDegree (RatFunc.denom x).natDegree
      omega
  · rw [hq', natDegree_mul (RatFunc.denom_ne_zero x) hh0]
    have := le_max_right (RatFunc.num x).natDegree (RatFunc.denom x).natDegree
    omega

/-! ### A weighted-degree estimator -/

/-- Expressions in `a, b` (weight `(1, 0)`) and `u, v` (weight `(0, 1)`) with integer constants. -/
inductive WE
  | a | b | u | v
  | cst (c : ℤ)
  | add (e f : WE)
  | sub (e f : WE)
  | mul (e f : WE)
  | pow (e : WE) (n : ℕ)

namespace WE

/-- Evaluation. -/
noncomputable def ev (A B U V : K[X]) : WE → K[X]
  | a => A
  | b => B
  | u => U
  | v => V
  | cst c => (c : K[X])
  | add e f => ev A B U V e + ev A B U V f
  | sub e f => ev A B U V e - ev A B U V f
  | mul e f => ev A B U V e * ev A B U V f
  | pow e n => ev A B U V e ^ n

/-- The estimate `(i, k)`: degree `≤ i D + k M`. -/
def est : WE → ℕ × ℕ
  | a => (1, 0)
  | b => (1, 0)
  | u => (0, 1)
  | v => (0, 1)
  | cst _ => (0, 0)
  | add e f => (max (est e).1 (est f).1, max (est e).2 (est f).2)
  | sub e f => (max (est e).1 (est f).1, max (est e).2 (est f).2)
  | mul e f => ((est e).1 + (est f).1, (est e).2 + (est f).2)
  | pow e n => (n * (est e).1, n * (est e).2)

theorem est_sound (A B U V : K[X]) (D M : ℕ) (hA : A.natDegree ≤ D) (hB : B.natDegree ≤ D)
    (hU : U.natDegree ≤ M) (hV : V.natDegree ≤ M) :
    ∀ e : WE, (ev A B U V e).natDegree ≤ (est e).1 * D + (est e).2 * M
  | a => by simp [ev, est, hA]
  | b => by simp [ev, est, hB]
  | u => by simp [ev, est, hU]
  | v => by simp [ev, est, hV]
  | cst c => by simp [ev, est]
  | add e f => by
    have he := est_sound A B U V D M hA hB hU hV e
    have hf := est_sound A B U V D M hA hB hU hV f
    simp only [ev, est]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact he.trans (add_le_add (Nat.mul_le_mul_right _ (le_max_left _ _))
        (Nat.mul_le_mul_right _ (le_max_left _ _)))
    · exact hf.trans (add_le_add (Nat.mul_le_mul_right _ (le_max_right _ _))
        (Nat.mul_le_mul_right _ (le_max_right _ _)))
  | sub e f => by
    have he := est_sound A B U V D M hA hB hU hV e
    have hf := est_sound A B U V D M hA hB hU hV f
    simp only [ev, est]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact he.trans (add_le_add (Nat.mul_le_mul_right _ (le_max_left _ _))
        (Nat.mul_le_mul_right _ (le_max_left _ _)))
    · exact hf.trans (add_le_add (Nat.mul_le_mul_right _ (le_max_right _ _))
        (Nat.mul_le_mul_right _ (le_max_right _ _)))
  | mul e f => by
    have he := est_sound A B U V D M hA hB hU hV e
    have hf := est_sound A B U V D M hA hB hU hV f
    simp only [ev, est]
    refine natDegree_mul_le.trans ?_
    nlinarith
  | pow e n => by
    have he := est_sound A B U V D M hA hB hU hV e
    simp only [ev, est]
    refine natDegree_pow_le.trans ?_
    calc n * (ev A B U V e).natDegree ≤ n * ((est e).1 * D + (est e).2 * M) :=
          Nat.mul_le_mul_left _ he
      _ = _ := by ring

end WE

open WE in
/-- The expression trees of the duplication data. -/
def phiE : WE := .add (.sub (.sub (.pow .u 4) (.mul (.mul (.mul (.cst 2) .a) (.pow .u 2)) (.pow .v 2)))
  (.mul (.mul (.mul (.cst 8) .b) .u) (.pow .v 3))) (.mul (.pow .a 2) (.pow .v 4))

open WE in
def psiE : WE := .add (.add (.mul (.mul (.cst 4) (.pow .u 3)) .v)
  (.mul (.mul (.mul (.cst 4) .a) .u) (.pow .v 3))) (.mul (.mul (.cst 4) .b) (.pow .v 4))

open WE in
def f1E : WE := .add (.mul (.mul (.cst 12) (.pow .u 2)) .v) (.mul (.mul (.cst 16) .a) (.pow .v 3))

open WE in
def g1E : WE := .sub (.sub (.mul (.cst 3) (.pow .u 3)) (.mul (.mul (.mul (.cst 5) .a) .u) (.pow .v 2)))
  (.mul (.mul (.cst 27) .b) (.pow .v 3))

open WE in
def deltaE : WE := .add (.mul (.cst 4) (.pow .a 3)) (.mul (.cst 27) (.pow .b 2))

open WE in
def f2E : WE :=
  .add (.add (.sub (.mul (.mul (.cst 4) deltaE) (.pow .u 3))
    (.mul (.mul (.mul (.mul (.cst 4) (.pow .a 2)) .b) (.pow .u 2)) .v))
    (.mul (.mul (.mul (.mul (.cst 4) .a) (.add (.mul (.cst 3) (.pow .a 3)) (.mul (.cst 22) (.pow .b 2)))) .u)
      (.pow .v 2)))
    (.mul (.mul (.mul (.cst 12) .b) (.add (.pow .a 3) (.mul (.cst 8) (.pow .b 2)))) (.pow .v 3))

open WE in
def g2E : WE :=
  .sub (.add (.add (.mul (.mul (.pow .a 2) .b) (.pow .u 3))
    (.mul (.mul (.mul .a (.add (.mul (.cst 5) (.pow .a 3)) (.mul (.cst 32) (.pow .b 2)))) (.pow .u 2)) .v))
    (.mul (.mul (.mul (.mul (.cst 2) .b) (.add (.mul (.cst 13) (.pow .a 3)) (.mul (.cst 96) (.pow .b 2)))) .u)
      (.pow .v 2)))
    (.mul (.mul (.mul (.cst 3) (.pow .a 2)) (.add (.pow .a 3) (.mul (.cst 8) (.pow .b 2)))) (.pow .v 3))

lemma res1 (A B U V : K[X]) :
    WE.ev A B U V f1E * WE.ev A B U V phiE + (-WE.ev A B U V g1E) * WE.ev A B U V psiE =
      (4 * WE.ev A B U V deltaE) * V ^ 7 := by
  simp only [WE.ev, f1E, g1E, phiE, psiE, deltaE]; push_cast; ring

lemma res2 (A B U V : K[X]) :
    WE.ev A B U V f2E * WE.ev A B U V phiE + WE.ev A B U V g2E * WE.ev A B U V psiE =
      (4 * WE.ev A B U V deltaE) * U ^ 7 := by
  simp only [WE.ev, f2E, g2E, phiE, psiE, deltaE]; push_cast; ring

/-- **The duplication estimate.** For `x = u / v` in lowest terms on `y² = x³ + a x + b`
(`Δ ≠ 0`), with `ψ(u, v) ≠ 0` (`2P ≠ O`) and `D = max (deg a) (deg b)`:
`4 ht x ≤ ht (φ/ψ) + 11 D` and `ht (φ/ψ) ≤ 4 ht x + 2 D`. -/
theorem dup_height [CharZero K] (A B U V : K[X]) (hc : IsCoprime U V) (hV : V ≠ 0)
    (hΔ : WE.ev A B U V deltaE ≠ 0) (hψ : WE.ev A B U V psiE ≠ 0) :
    4 * ht (algebraMap K[X] (RatFunc K) U / algebraMap K[X] (RatFunc K) V) ≤
        ht (algebraMap K[X] (RatFunc K) (WE.ev A B U V phiE) /
          algebraMap K[X] (RatFunc K) (WE.ev A B U V psiE)) + 11 * max A.natDegree B.natDegree ∧
      ht (algebraMap K[X] (RatFunc K) (WE.ev A B U V phiE) /
          algebraMap K[X] (RatFunc K) (WE.ev A B U V psiE)) ≤
        4 * ht (algebraMap K[X] (RatFunc K) U / algebraMap K[X] (RatFunc K) V) +
          2 * max A.natDegree B.natDegree := by
  set D := max A.natDegree B.natDegree
  set M := max U.natDegree V.natDegree
  rw [ht_div_coprime U V hV hc]
  have hA : A.natDegree ≤ D := le_max_left _ _
  have hB : B.natDegree ≤ D := le_max_right _ _
  have hU : U.natDegree ≤ M := le_max_left _ _
  have hVd : V.natDegree ≤ M := le_max_right _ _
  have S := WE.est_sound A B U V D M hA hB hU hVd
  have hphi := S phiE
  have hpsi := S psiE
  have hf1 := S f1E
  have hg1 := S g1E
  have hf2 := S f2E
  have hg2 := S g2E
  have hdl := S deltaE
  rw [show phiE.est = (2, 4) from rfl] at hphi
  rw [show psiE.est = (1, 4) from rfl] at hpsi
  rw [show f1E.est = (1, 3) from rfl] at hf1
  rw [show g1E.est = (1, 3) from rfl] at hg1
  rw [show f2E.est = (4, 3) from rfl] at hf2
  rw [show g2E.est = (5, 3) from rfl] at hg2
  rw [show deltaE.est = (3, 0) from rfl] at hdl
  simp only [zero_mul, add_zero] at hphi hpsi hf1 hg1 hf2 hg2 hdl
  have hR0 : (4 * WE.ev A B U V deltaE) ≠ 0 := mul_ne_zero (by norm_num) hΔ
  have hR : (4 * WE.ev A B U V deltaE).natDegree ≤ 3 * D := by
    refine natDegree_mul_le.trans ?_
    have : (4 : K[X]).natDegree = 0 := natDegree_ofNat 4
    omega
  refine ⟨?_, ?_⟩
  · -- lower bound: `7M ≤ deg R + (3M + 5D) + max`, and `max ≤ ht + deg R`
    have hng1 : (-WE.ev A B U V g1E).natDegree ≤ 5 * D + 3 * M := by
      rw [natDegree_neg]; omega
    have hmax := deg_max_ge U V (WE.ev A B U V phiE) (WE.ev A B U V psiE) _ _ _ _
      (4 * WE.ev A B U V deltaE) 7 (5 * D + 3 * M) hc hR0 (res1 A B U V) (res2 A B U V)
      (by omega) hng1 (by omega) (by omega)
    have hht := ht_ge_of_res (WE.ev A B U V phiE) (WE.ev A B U V psiE) _ _ _ _
      (4 * WE.ev A B U V deltaE) U V 7 hψ hc hR0 (res1 A B U V) (res2 A B U V)
    omega
  · have := ht_div_le (WE.ev A B U V phiE) (WE.ev A B U V psiE) hψ
    omega

end FFHeight
