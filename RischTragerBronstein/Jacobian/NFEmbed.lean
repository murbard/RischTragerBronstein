import RischTragerBronstein.Algebraic.NumField
import RischTragerBronstein.Jacobian.CertCheck

/-!
# Number fields in `ℚ_p`, with integrality and reduction

For `K = ℚ[θ]/(f)` (`NF f`), `f = fZ` over `ℤ`, and `z ∈ ℤ_p` a root of `fZ`, `embedZ` is the
embedding `K → ℚ_p`, `θ ↦ z`. An element whose coefficients are `p`-integral maps into `ℤ_p`, and
its reduction is obtained by reducing the coefficients and evaluating at `z mod p`
(`exists_lift_list`, with `ratMod` and `redL`).
-/

open Polynomial CPoly CPoly.Kron

namespace Jac

variable {p : ℕ} [hp : Fact p.Prime]

/-- A rational number modulo `p`. -/
def ratMod (p : ℕ) (c : ℚ) : ZMod p := (c.num : ZMod p) * ((c.den : ℕ) : ZMod p)⁻¹

/-- The reduction of a coefficient list, evaluated at `s`. -/
def redL (p : ℕ) (s : ZMod p) (l : CPoly ℚ) : ZMod p := evalC (l.map (ratMod p)) s

/-- `p`-integrality of a coefficient list. -/
def pIntL (p : ℕ) (l : CPoly ℚ) : Bool := l.all fun c ↦ c.den % p != 0

lemma exists_lift_rat {c : ℚ} (hc : c.den % p ≠ 0) :
    ∃ w : ℤ_[p], (w : ℚ_[p]) = c ∧ PadicInt.toZMod w = ratMod p c := by
  have hu : IsUnit ((c.den : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr
      (fun h ↦ hc (Nat.mod_eq_zero_of_dvd h)))
  refine ⟨(c.num : ℤ_[p]) * ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), ?_, ?_⟩
  · have h1 : ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((c.den : ℕ) : ℤ_[p]) = 1 := hu.val_inv_mul
    have h2 : (((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * ((c.den : ℕ) : ℚ_[p]) = 1 := by
      exact_mod_cast congrArg (fun w : ℤ_[p] ↦ (w : ℚ_[p])) h1
    have hd : ((c.den : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast c.den_nz
    push_cast
    rw [show (c : ℚ_[p]) = (c.num : ℚ_[p]) / (c.den : ℚ_[p]) by
      rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]]
    field_simp
    linear_combination (c.num : ℚ_[p]) * h2
  · have h1 := hu.val_inv_mul
    have h2 := congrArg PadicInt.toZMod h1
    rw [map_mul, map_one, map_natCast] at h2
    rw [map_mul, map_intCast, ratMod]
    congr 1
    exact (eq_inv_of_mul_eq_one_left h2)

lemma exists_lift_list (z : ℤ_[p]) : ∀ l : CPoly ℚ, pIntL p l = true →
    ∃ w : ℤ_[p], (w : ℚ_[p]) = (toPoly l).eval₂ (algebraMap ℚ ℚ_[p]) (z : ℚ_[p]) ∧
      PadicInt.toZMod w = redL p (PadicInt.toZMod z) l
  | [], _ => ⟨0, by simp, by simp [redL, evalC]⟩
  | c :: l, h => by
    simp only [pIntL, List.all_cons, Bool.and_eq_true, bne_iff_ne] at h
    obtain ⟨wc, hc1, hc2⟩ := exists_lift_rat h.1
    obtain ⟨wl, hl1, hl2⟩ := exists_lift_list z l h.2
    refine ⟨wc + z * wl, ?_, ?_⟩
    · simp only [toPoly_cons, eval₂_add, eval₂_C, eval₂_mul, eval₂_X, PadicInt.coe_add,
        PadicInt.coe_mul, hc1, hl1]; rfl
    · simp only [map_add, map_mul, hc2, hl2, redL, List.map_cons, evalC, List.foldr_cons]

section Embed

variable {f : CPoly ℚ} [Fact (Irreducible (toPoly f))]

lemma root_q (fZ : ℤ[X]) (hfZ : toPoly f = fZ.map (Int.castRingHom ℚ)) (z : ℤ_[p])
    (hz : aeval z fZ = 0) : (toPoly f).eval₂ (algebraMap ℚ ℚ_[p]) (z : ℚ_[p]) = 0 := by
  have hcoe : (PadicInt.Coe.ringHom (aeval z fZ) : ℚ_[p]) = aeval (PadicInt.Coe.ringHom z) fZ := by
    rw [aeval_def, aeval_def, hom_eval₂]
    congr 1
  rw [← aeval_def, hfZ, show fZ.map (Int.castRingHom ℚ) = fZ.map (algebraMap ℤ ℚ) from rfl,
    aeval_map_algebraMap]
  rw [show (z : ℚ_[p]) = PadicInt.Coe.ringHom z from rfl, ← hcoe, hz, map_zero]

/-- The embedding `θ ↦ z` of `ℚ[θ]/(f)` into `ℚ_p`. -/
noncomputable def embedZ (fZ : ℤ[X]) (hfZ : toPoly f = fZ.map (Int.castRingHom ℚ)) (z : ℤ_[p])
    (hz : aeval z fZ = 0) : NFC.NF f →+* ℚ_[p] :=
  (AdjoinRoot.lift (algebraMap ℚ ℚ_[p]) (z : ℚ_[p]) (root_q fZ hfZ z hz)).comp (NFC.toARHom f)

lemma embedZ_apply (fZ : ℤ[X]) (hfZ : toPoly f = fZ.map (Int.castRingHom ℚ)) (z : ℤ_[p])
    (hz : aeval z fZ = 0) (x : NFC.NF f) :
    embedZ fZ hfZ z hz x = (toPoly x.1).eval₂ (algebraMap ℚ ℚ_[p]) (z : ℚ_[p]) := by
  simp only [embedZ, RingHom.comp_apply]
  exact AdjoinRoot.lift_mk _ _

/-- **Integral elements lift to `ℤ_p`, and reduce by evaluating at `z mod p`.** -/
lemma exists_lift_NF (fZ : ℤ[X]) (hfZ : toPoly f = fZ.map (Int.castRingHom ℚ)) (z : ℤ_[p])
    (hz : aeval z fZ = 0) (x : NFC.NF f) (hx : pIntL p x.1 = true) :
    ∃ w : ℤ_[p], (w : ℚ_[p]) = embedZ fZ hfZ z hz x ∧
      PadicInt.toZMod w = redL p (PadicInt.toZMod z) x.1 := by
  rw [embedZ_apply]
  exact exists_lift_list z x.1 hx

end Embed

end Jac
