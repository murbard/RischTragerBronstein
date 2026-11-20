import RischTragerBronstein.Algebraic.SupRed
import RischTragerBronstein.Algebraic.PadicTransc

/-!
# Reduction of rational function fields modulo `p`

For a computable field `K` with a reduction `R : RedFns p K` induced by `φ : K → ℚ_p`, and a residue
`r ∈ 𝔽_p`, `rfFns R r` reduces `K(t)` by `t ↦ r`: on the canonical representative `P/Q`, it is
defined when the coefficients are integral and `Q̄(r) ≠ 0`, with residue `P̄(r)/Q̄(r)`.

`rfFns_valid`: it is induced by the embedding `K(t) → ℚ_p`, `t ↦ ξ`, for any `ξ ∈ ℤ_p` of residue
`r` transcendental over `φ(K)` (which exists, `exists_transc`); so `rfFns_exists` provides the
embedding required by `torsOracle_spec`.
-/

open Polynomial CPoly CPoly.Kron RFC

namespace Sup

variable (p : ℕ) [hp : Fact p.Prime]
variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]
set_option linter.unusedSectionVars false

/-- **The reduction of `K(t)` at `t ↦ r`.** -/
def rfFns (R : RedFns p K) (r : ZMod p) : RedFns p (RatFuncC K) :=
  ⟨fun x ↦ (canon x).1.all R.ok && (canon x).2.all R.ok &&
      (evalC ((canon x).2.map R.red) r != 0),
    fun x ↦ evalC ((canon x).1.map R.red) r / evalC ((canon x).2.map R.red) r⟩

variable {p}

lemma lift_list (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ) (ξ : ℤ_[p]) :
    ∀ l : CPoly K, (∀ c ∈ l, R.ok c = true) →
      ∃ w : ℤ_[p], (toPoly l).eval₂ φ (ξ : ℚ_[p]) = (w : ℚ_[p]) ∧
        PadicInt.toZMod w = evalC (l.map R.red) (PadicInt.toZMod ξ)
  | [], _ => ⟨0, by simp, by simp [evalC]⟩
  | a :: l, h => by
    obtain ⟨za, hza, hzar⟩ := hR a (h a (List.mem_cons_self))
    obtain ⟨w, hw, hwr⟩ := lift_list R φ hR ξ l fun c hc ↦ h c (List.mem_cons_of_mem a hc)
    refine ⟨za + ξ * w, ?_, ?_⟩
    · rw [toPoly_cons, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, hw, hza]
      rw [PadicInt.coe_add, PadicInt.coe_mul]; rfl
    · rw [map_add, map_mul, hzar, hwr]
      simp [evalC]

lemma evalHom_eq {E : Type*} [Field E] {φ : K →+* E} {z : E} (hz : Transc φ z) (x : RatFuncC K) :
    evalHom hz x = evalRF hz (toRF x) := rfl

/-- **`rfFns` is induced by an embedding** `t ↦ ξ` (`ξ` of residue `r`, transcendental). -/
theorem rfFns_valid (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ) (ξ : ℤ_[p])
    (hz : Transc φ (ξ : ℚ_[p])) :
    RedValid p (rfFns p R (PadicInt.toZMod ξ)) (evalHom hz) := by
  intro x hx
  simp only [rfFns, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at hx
  obtain ⟨⟨hP, hQ⟩, hQr⟩ := hx
  obtain ⟨wP, hwP, hwPr⟩ := lift_list R φ hR ξ _ hP
  obtain ⟨wQ, hwQ, hwQr⟩ := lift_list R φ hR ξ _ hQ
  have hu : IsUnit wQ := by
    by_contra hn
    have hm : wQ ∈ IsLocalRing.maximalIdeal ℤ_[p] := (IsLocalRing.mem_maximalIdeal wQ).mpr hn
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hwQr] at hm
    exact hQr hm
  obtain ⟨u, rfl⟩ := hu
  refine ⟨wP * ↑u⁻¹, ?_, ?_⟩
  · obtain ⟨-, -, -, hx⟩ := canon_spec x
    rw [evalHom_eq, hx, map_div₀, evalRF_algebraMap, evalRF_algebraMap, hwP, hwQ]
    rw [map_mul, div_eq_mul_inv]
    congr 1
    symm
    exact eq_inv_of_mul_eq_one_left (by
      show algebraMap ℤ_[p] ℚ_[p] _ * algebraMap ℤ_[p] ℚ_[p] _ = 1
      rw [← map_mul, Units.inv_mul, map_one])
  · show _ = evalC ((canon x).1.map R.red) (PadicInt.toZMod ξ) /
      evalC ((canon x).2.map R.red) (PadicInt.toZMod ξ)
    rw [map_mul, hwPr, ← hwQr, div_eq_mul_inv]
    congr 1
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

/-- **An embedding inducing `rfFns R r`**, for a countable `K`. -/
theorem rfFns_exists [Countable K] (R : RedFns p K) (φ : K →+* ℚ_[p]) (hR : RedValid p R φ)
    (r : ZMod p) : ∃ φ' : RatFuncC K →+* ℚ_[p], RedValid p (rfFns p R r) φ' := by
  obtain ⟨y, hy⟩ := exists_transc φ ((ZMod.cast r : ℤ_[p]))
  refine ⟨evalHom hy, ?_⟩
  have hr : PadicInt.toZMod ((ZMod.cast r : ℤ_[p]) + (p : ℤ_[p]) * y) = r := by
    rw [map_add, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero]
    exact ZMod.ringHom_map_cast PadicInt.toZMod r
  have := rfFns_valid R φ hR _ hy
  rwa [hr] at this

end Sup
