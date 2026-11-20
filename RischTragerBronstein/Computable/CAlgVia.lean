import RischTragerBronstein.Computable.CFracVia
import RischTragerBronstein.Computable.GEuclidDegree

/-!
# Algebraic extensions of computable differential fields

`CField.algVia M P φ`: given a model `M` of `O` in `K`, a list `P` of codes denoting a monic
polynomial of degree `n ≥ 1`, and a ring homomorphism `φ : K[X] →+* L` into a differential field
(think `φ = aeval y`) such that

* `φ P = 0` (`y` is a root),
* `φ` kills no non-zero polynomial of codes of degree `< n` (`P` is the minimal polynomial of `y`
  over the values of the codes),
* `φ` is compatible with the derivations: `(φ Q)′ = φ Q^D + φ Q_X · (φ X)′`,

the algebraic extension `K(y)` is modelled by lists of codes (polynomials in `y`) with the
operations `COps.algExt O P`: products are reduced modulo `P`, the zero test reduces modulo `P`,
the inverse comes from the extended Euclidean algorithm against `P`, and the derivation uses
`y′ = −P^D(y)/P_Y(y)`. The value of a list `a` is `φ a`.
-/

open Polynomial Differential

namespace GPoly

variable {α : Type*} (O : COps α)

/-- Reduction modulo `P`. -/
def algRed (P a : GPoly α) : GPoly α := (divMod O a P).2

/-- The inverse modulo `P` (extended Euclid). -/
def algInv (P a : GPoly α) : GPoly α :=
  if isZero O (algRed O P a) then []
  else
    let g := egcd O (algRed O P a) P
    algRed O P (smul O (O.inv (lead O (trim O g.1))) g.2.1)

/-- The derivative of the generator: `y′ = −P^D(y) / P_Y(y)`. -/
def algYd (P : GPoly α) : GPoly α :=
  algRed O P (mul O (neg O (mapD O P)) (algInv O P (derivX O P)))

end GPoly

namespace COps

variable {α : Type*}

/-- The operations of the algebraic extension defined by `P`. -/
def algExt (O : COps α) (P : GPoly α) : COps (GPoly α) where
  zero := []
  one := [O.one]
  add := GPoly.add O
  neg := GPoly.neg O
  mul a b := GPoly.algRed O P (GPoly.mul O a b)
  inv := GPoly.algInv O P
  deriv a := GPoly.algRed O P (GPoly.derivT O (GPoly.algYd O P) a)
  isZero a := GPoly.isZero O (GPoly.algRed O P a)
  natCast n := [O.natCast n]

end COps

namespace CField

variable {α K L : Type*} [Field K] [Differential K] [Field L] [Differential L] {O : COps α}
  (M : CField α K O)

section Lemmas

variable (P : GPoly α) (φ : K[X] →+* L) (hroot : φ (GPoly.toPoly M P) = 0)
include hroot

lemma phi_algRed (a : GPoly α) :
    φ (GPoly.toPoly M (GPoly.algRed O P a)) = φ (GPoly.toPoly M a) := by
  rw [GPoly.algRed]
  conv_rhs => rw [GPoly.divMod_spec M a P]
  rw [map_add, map_mul, hroot, mul_zero, zero_add]

end Lemmas

variable (P : GPoly α) (n : ℕ) (hPm : (GPoly.toPoly M P).Monic)
  (hPn : (GPoly.toPoly M P).natDegree = n) (hn : 0 < n) (φ : K[X] →+* L)
  (hroot : φ (GPoly.toPoly M P) = 0)
  (hmin : ∀ p : GPoly α, (GPoly.toPoly M p).natDegree < n → φ (GPoly.toPoly M p) = 0 →
    GPoly.toPoly M p = 0)

include hPm hPn hn hroot hmin in
/-- The remainder modulo `P` is zero exactly when its value is. -/
lemma algRed_eq_zero_iff (a : GPoly α) :
    GPoly.toPoly M (GPoly.algRed O P a) = 0 ↔ φ (GPoly.toPoly M a) = 0 := by
  rw [← phi_algRed M P φ hroot a]
  refine ⟨fun h ↦ by rw [h, map_zero], fun h ↦ hmin _ ?_ h⟩
  have hP0 : GPoly.toPoly M P ≠ 0 := hPm.ne_zero
  have hlt : (GPoly.toPoly M (GPoly.algRed O P a)).degree < (GPoly.toPoly M P).degree :=
    GPoly.divMod_degree_lt M a P hP0
  by_cases h0 : GPoly.toPoly M (GPoly.algRed O P a) = 0
  · rw [h0, natDegree_zero]; exact hn
  · rw [degree_eq_natDegree h0, degree_eq_natDegree hP0, hPn] at hlt
    exact_mod_cast hlt

include hPm hPn hn hroot hmin in
/-- The value of the inverse. -/
lemma phi_algInv (a : GPoly α) :
    φ (GPoly.toPoly M (GPoly.algInv O P a)) = (φ (GPoly.toPoly M a))⁻¹ := by
  have hP0 : GPoly.toPoly M P ≠ 0 := hPm.ne_zero
  set r := GPoly.algRed O P a with hrdef
  unfold GPoly.algInv
  rw [← hrdef]
  split_ifs with hz
  · have hr : GPoly.toPoly M r = 0 := (GPoly.isZero_iff M r).mp hz
    rw [(algRed_eq_zero_iff M P n hPm hPn hn φ hroot hmin a).mp hr, inv_zero,
      GPoly.toPoly_nil, map_zero]
  have hr : GPoly.toPoly M r ≠ 0 := fun h ↦ hz ((GPoly.isZero_iff M r).mpr h)
  have hrdeg : (GPoly.toPoly M r).natDegree < n := by
    have hlt : (GPoly.toPoly M r).degree < (GPoly.toPoly M P).degree :=
      GPoly.divMod_degree_lt M a P hP0
    rw [degree_eq_natDegree hr, degree_eq_natDegree hP0, hPn] at hlt
    exact_mod_cast hlt
  have hφr : φ (GPoly.toPoly M r) = φ (GPoly.toPoly M a) := phi_algRed M P φ hroot a
  set g := GPoly.egcd O r P with hg
  have hspec := GPoly.egcd_spec M r P
  obtain ⟨hgr, hgP⟩ := GPoly.egcd_dvd M r P
  rw [← hg] at hspec hgr hgP
  have hg0 : GPoly.toPoly M g.1 ≠ 0 := fun h ↦ hr (by rw [h] at hgr; exact zero_dvd_iff.mp hgr)
  -- `g` is a constant
  have hgdeg : (GPoly.toPoly M g.1).natDegree = 0 := by
    set h := (GPoly.divMod O P g.1).1 with hh
    have hPgh : GPoly.toPoly M P = GPoly.toPoly M h * GPoly.toPoly M g.1 :=
      GPoly.div_mul_of_dvd M P g.1 hg0 hgP
    have hh0 : GPoly.toPoly M h ≠ 0 := fun h0 ↦ hP0 (by rw [hPgh, h0, zero_mul])
    have hsum : (GPoly.toPoly M h).natDegree + (GPoly.toPoly M g.1).natDegree = n := by
      rw [← hPn, hPgh, natDegree_mul hh0 hg0]
    have hφ : φ (GPoly.toPoly M h) * φ (GPoly.toPoly M g.1) = 0 := by
      rw [← map_mul, ← hPgh, hroot]
    rcases mul_eq_zero.mp hφ with h1 | h1
    · by_contra hne
      exact hh0 (hmin h (by omega) h1)
    · exfalso
      have hle : (GPoly.toPoly M g.1).natDegree ≤ (GPoly.toPoly M r).natDegree :=
        natDegree_le_of_dvd hgr hr
      exact hg0 (hmin g.1 (by omega) h1)
  set c := GPoly.lead O (GPoly.trim O g.1)
  have hgC : GPoly.toPoly M g.1 = C (M.sem c) := by
    rw [eq_C_of_natDegree_eq_zero hgdeg, ← GPoly.leadingCoeff_toPoly M hg0, leadingCoeff,
      hgdeg]
  have hc0 : M.sem c ≠ 0 := fun h ↦ hg0 (by rw [hgC, h, C_0])
  have hφC : ∀ x : K, x ≠ 0 → φ (C x) ≠ 0 := fun x hx h ↦ by
    have : φ (C x) * φ (C x⁻¹) = 1 := by rw [← map_mul, ← C_mul, mul_inv_cancel₀ hx, C_1, map_one]
    rw [h, zero_mul] at this; exact zero_ne_one this
  have hkey : φ (GPoly.toPoly M g.2.1) * φ (GPoly.toPoly M r) = φ (C (M.sem c)) := by
    rw [← hgC, ← hspec, map_add, map_mul, map_mul, hroot, mul_zero, add_zero]
  rw [phi_algRed M P φ hroot, GPoly.toPoly_smul, map_mul, M.sem_inv, ← hφr]
  have hne := hφC _ hc0
  have hr' : φ (GPoly.toPoly M r) ≠ 0 := fun h ↦ hne (by rw [← hkey, h, mul_zero])
  refine eq_inv_of_mul_eq_one_left ?_
  rw [mul_assoc, hkey, ← map_mul, ← C_mul, inv_mul_cancel₀ hc0, C_1,
    map_one]

variable (hder : ∀ Q : K[X], (φ Q)′ = φ (mapCoeffs Q) + φ (derivative Q) * (φ X)′)

include hPm hPn hn hroot hmin hder in
/-- The value of the derivative of the generator. -/
lemma phi_algYd [CharZero K] : φ (GPoly.toPoly M (GPoly.algYd O P)) = (φ X)′ := by
  have hd0 : GPoly.toPoly M (GPoly.derivX O P) ≠ 0 := by
    rw [GPoly.toPoly_derivX]
    intro h0
    have := congrArg (fun q : K[X] ↦ q.coeff (n - 1)) h0
    simp only [coeff_derivative, Polynomial.coeff_zero] at this
    rw [Nat.sub_add_cancel hn, ← hPn, hPm.coeff_natDegree, one_mul, hPn] at this
    have e : ((n - 1 : ℕ) : K) + 1 = ((n - 1 + 1 : ℕ) : K) := by push_cast; ring
    rw [e, Nat.sub_add_cancel hn] at this
    exact (Nat.cast_ne_zero.mpr (by omega : n ≠ 0)) this
  have hφd : φ (GPoly.toPoly M (GPoly.derivX O P)) ≠ 0 := fun h ↦ hd0 (hmin _ (by
    rw [GPoly.toPoly_derivX]
    have := natDegree_derivative_le (GPoly.toPoly M P)
    rw [hPn] at this; omega) h)
  have h0 := hder (GPoly.toPoly M P)
  rw [hroot, map_zero] at h0
  rw [GPoly.algYd, phi_algRed M P φ hroot, GPoly.toPoly_mul, map_mul,
    phi_algInv M P n hPm hPn hn φ hroot hmin, GPoly.toPoly_neg, GPoly.toPoly_mapD, map_neg,
    GPoly.toPoly_derivX]
  rw [GPoly.toPoly_derivX] at hφd
  field_simp
  linear_combination h0

/-- **The algebraic extension defined by `P`, modelled through `φ`.** -/
noncomputable def algVia [CharZero K] : CField (GPoly α) L (O.algExt P) where
  sem a := φ (GPoly.toPoly M a)
  sem_zero := by simp [COps.algExt]
  sem_one := by simp [COps.algExt, M.sem_one]
  sem_add a b := by simp [COps.algExt, GPoly.toPoly_add]
  sem_neg a := by simp [COps.algExt, GPoly.toPoly_neg]
  sem_mul a b := by
    simp only [COps.algExt]
    rw [phi_algRed M P φ hroot, GPoly.toPoly_mul, map_mul]
  sem_inv a := phi_algInv M P n hPm hPn hn φ hroot hmin a
  sem_deriv a := by
    simp only [COps.algExt]
    rw [phi_algRed M P φ hroot, hder]
    simp only [GPoly.derivT, GPoly.toPoly_add, GPoly.toPoly_mapD, GPoly.toPoly_mul,
      GPoly.toPoly_derivX, map_add, map_mul, phi_algYd M P n hPm hPn hn φ hroot hmin hder]
    ring
  sem_natCast k := by simp [COps.algExt, M.sem_natCast]
  isZero_iff a := by
    simp only [COps.algExt]
    rw [GPoly.isZero_iff M, algRed_eq_zero_iff M P n hPm hPn hn φ hroot hmin]

lemma sem_algVia [CharZero K] (a : GPoly α) :
    (M.algVia P n hPm hPn hn φ hroot hmin hder).sem a = φ (GPoly.toPoly M a) := rfl

end CField
