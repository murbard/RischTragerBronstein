import RischTragerBronstein.Computable.SquarefreePart
import RischTragerBronstein.Computable.BezoutSolve
import RischTragerBronstein.Computable.RatRoots
import RischTragerBronstein.RDE.RationalCoeffW
import RischTragerBronstein.Computable.DependencyFinder

/-!
# The residues of a rational function at its simple poles, without factorisation

For `g = Gn / Gd ∈ R(x)` in lowest terms:

* `simplePart Gd = S`: the product of the simple prime factors of `Gd`, computed as
  `S₀ / gcd (S₀, Gd′)` with `S₀ = sqfreePart Gd`;
* `residuePolyW Gn Gd = r` with `r Gd′ ≡ Gn (mod S)` (Bézout): the residue of `g` at a simple
  prime `p` is `r mod p`;
* `muCheck S r μ`: checks `μ ≠ 0` and `S ∣ μ(r)`, i.e. `μ` annihilates all the residues;
  `findMu S r` computes such a `μ` as a linear dependency among `1, r, r², … (mod S)`
  (`CPoly.depend`, verified); `muCheck_findMu`: the check always succeeds for `S ≠ 0`.

The properties of `S`, `r`, `μ` needed by `RDE/RationalCoeffW.lean` are stated in a form that is
stable under extension of the constants (`simplePart_data`: equations and Bézout identities).
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace CPoly

section Defs

variable {R : Type*} [Field R] [DecidableEq R]

/-- The product of the simple prime factors of `Gd`. -/
def simplePart (Gd : CPoly R) : CPoly R :=
  let S₀ := sqfreePart Gd
  div S₀ (gcd S₀ (deriv Gd))

/-- The residue polynomial at the simple poles: `r Gd′ ≡ Gn (mod S)`. -/
def residuePolyW (Gn Gd : CPoly R) : CPoly R := (solveBezout (deriv Gd) (simplePart Gd) Gn).1

/-- Horner composition `μ(r)`. -/
def compC (μ r : CPoly R) : CPoly R := μ.foldr (fun a acc ↦ add [a] (mul acc r)) []

/-- `μ ≠ 0` and `S ∣ μ(r)`. -/
def muCheck (S r μ : CPoly R) : Bool :=
  decide (trim μ ≠ []) && isZero (divMod (compC μ r) S).2

/-- A vector of fixed length `d`: the coefficients of `p mod S`. -/
def padTo (d : ℕ) (p : CPoly R) : List R := (p ++ List.replicate d 0).take d

/-- The vectors `P, P r, P r², … (mod S)`, `n` of them. -/
def powersModAux (S r : CPoly R) (d : ℕ) : ℕ → CPoly R → List (List R)
  | 0, _ => []
  | n + 1, P => padTo d P :: powersModAux S r d n (divMod (mul P r) S).2

/-- An annihilating polynomial of `r mod S`: a dependency among `1, r, …, r^d (mod S)`. -/
def findMu (S r : CPoly R) : CPoly R :=
  let d := (trim S).length - 1
  depend d (powersModAux S r d (d + 1) [1])

end Defs

section CompC

variable {R : Type*} [Field R] [DecidableEq R]

lemma toPoly_compC (μ r : CPoly R) : toPoly (compC μ r) = (toPoly μ).comp (toPoly r) := by
  induction μ with
  | nil => simp [compC]
  | cons a μ ih =>
    simp only [compC, List.foldr_cons, toPoly_add, toPoly_mul, toPoly_cons, add_comp, C_comp,
      mul_comp, X_comp, ← ih]
    simp
    ring

end CompC

section Spec

variable {R : Type*} [Field R] [DecidableEq R] [CharZero R]

theorem muCheck_spec {S r μ : CPoly R} (h : muCheck S r μ = true) :
    toPoly μ ≠ 0 ∧ ∃ q : R[X], (toPoly μ).comp (toPoly r) = toPoly S * q := by
  simp only [muCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun h0 ↦ h1 ((trim_eq_nil_iff μ).mpr h0), toPoly (divMod (compC μ r) S).1, ?_⟩
  have := divMod_spec (compC μ r) S
  rw [(isZero_iff _).mp h2, add_zero, toPoly_compC] at this
  rw [this, mul_comm]

lemma length_padTo (d : ℕ) (p : CPoly R) : (padTo d p).length = d := by
  simp [padTo]

lemma coord_padTo (d : ℕ) (p : CPoly R) (k : ℕ) :
    coord (padTo d p) k = if k < d then coord p k else 0 := by
  simp only [padTo, coord]
  split_ifs with hk
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_take, List.getElem_append]
    split_ifs with hp
    · rw [List.getD_eq_getElem _ _ hp]
    · rw [List.getElem_replicate, List.getD_eq_default _ _ (by omega)]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

lemma toPoly_padTo {d : ℕ} {p : CPoly R} (hp : (toPoly p).degree < d) :
    toPoly (padTo d p) = toPoly p := by
  ext k
  rw [coeff_toPoly, coeff_toPoly]
  change coord (padTo d p) k = coord p k
  rw [coord_padTo]
  split_ifs with hk
  · rfl
  · have : (toPoly p).coeff k = 0 :=
      coeff_eq_zero_of_degree_lt (hp.trans_le (by exact_mod_cast not_lt.mp hk))
    rw [coeff_toPoly] at this
    exact this.symm

lemma length_powersModAux (S r : CPoly R) (d n : ℕ) (P : CPoly R) :
    (powersModAux S r d n P).length = n := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih => simp [powersModAux, ih]

lemma mem_powersModAux_length (S r : CPoly R) (d n : ℕ) (P : CPoly R) :
    ∀ v ∈ powersModAux S r d n P, v.length = d := by
  induction n generalizing P with
  | zero => simp [powersModAux]
  | succ n ih =>
    intro v hv
    simp only [powersModAux, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact length_padTo d P
    · exact ih _ v hv

/-- `∑ᵢ C cᵢ · vᵢ`, as a polynomial. -/
noncomputable def polyComb (c : List R) (vs : List (List R)) : R[X] :=
  (List.zipWith (fun ci v ↦ C ci * toPoly v) c vs).sum

lemma coeff_polyComb (c : List R) (vs : List (List R)) (k : ℕ) :
    (polyComb c vs).coeff k = lincombAt c vs k := by
  induction c generalizing vs with
  | nil => simp [polyComb, lincombAt]
  | cons ci c ih =>
    cases vs with
    | nil => simp [polyComb, lincombAt]
    | cons v vs =>
      simp only [polyComb, List.zipWith_cons_cons, List.sum_cons, coeff_add, coeff_C_mul,
        coeff_toPoly] at ih ⊢
      rw [ih, lincombAt_cons]
      rfl

lemma polyComb_eq_zero {d : ℕ} {c : List R} {vs : List (List R)} (hv : ∀ v ∈ vs, v.length = d)
    (h : ∀ k < d, lincombAt c vs k = 0) : polyComb c vs = 0 := by
  ext k
  rw [coeff_polyComb, coeff_zero]
  by_cases hk : k < d
  · exact h k hk
  · clear h
    induction c generalizing vs with
    | nil => simp [lincombAt]
    | cons ci c ih =>
      cases vs with
      | nil => simp [lincombAt]
      | cons v vs =>
        rw [lincombAt_cons, ih fun w hw ↦ hv w (List.mem_cons_of_mem _ hw)]
        have : coord v k = 0 := by
          simp only [coord]
          rw [List.getD_eq_default _ _ (by rw [hv v List.mem_cons_self]; omega)]
        rw [this]; ring

/-- The key congruence: `μ(r) · P ≡ ∑ cᵢ vᵢ (mod S)` for the power vectors starting at `P`. -/
lemma dvd_comp_sub_polyComb (S r : CPoly R) {d : ℕ} (hd : 1 ≤ d) (hS : (toPoly S).degree = d) :
    ∀ (n : ℕ) (c : List R) (P : CPoly R), c.length ≤ n → (toPoly P).degree < d →
      toPoly S ∣ (toPoly c).comp (toPoly r) * toPoly P - polyComb c (powersModAux S r d n P) := by
  intro n
  induction n with
  | zero =>
    intro c P hc _
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hc)]
    simp [polyComb, powersModAux]
  | succ n ih =>
    intro c P hc hP
    cases c with
    | nil => simp [polyComb]
    | cons c₀ c' =>
      have hS0 : toPoly S ≠ 0 := fun h0 ↦ by rw [h0, degree_zero] at hS; exact absurd hS (by simp)
      have hdm := divMod_spec (mul P r) S
      have hlt := divMod_degree_lt (mul P r) S hS0
      rw [hS] at hlt
      obtain ⟨q, hq⟩ := ih c' (divMod (mul P r) S).2 (by simpa using hc) hlt
      refine ⟨toPoly (divMod (mul P r) S).1 * (toPoly c').comp (toPoly r) + q, ?_⟩
      simp only [powersModAux, polyComb, List.zipWith_cons_cons, List.sum_cons, toPoly_cons,
        add_comp, C_comp, mul_comp, X_comp, toPoly_padTo hP]
      simp only [polyComb] at hq
      rw [toPoly_mul] at hdm
      linear_combination hq + (toPoly c').comp (toPoly r) * hdm

/-- **`findMu` always succeeds** for `S ≠ 0`. -/
theorem muCheck_findMu (S r : CPoly R) (hS0 : toPoly S ≠ 0) :
    muCheck S r (findMu S r) = true := by
  have htS : trim S ≠ [] := fun h0 ↦ hS0 ((trim_eq_nil_iff _).mp h0)
  obtain ⟨hdS, -, -⟩ := natDegree_toPoly_of_trim_ne_nil htS
  set d := (trim S).length - 1 with hd
  have hdegS : (toPoly S).degree = d := by rw [degree_eq_natDegree hS0, hdS]
  set vs := powersModAux S r d (d + 1) [1] with hvs
  have hlen : d < vs.length := by rw [hvs, length_powersModAux]; omega
  have hvlen : ∀ v ∈ vs, v.length = d := mem_powersModAux_length S r d (d + 1) [1]
  obtain ⟨h1, ⟨i, hi⟩, h3⟩ := depend_spec d vs hlen hvlen
  have hμ0 : toPoly (depend d vs) ≠ 0 := fun h0 ↦ hi (by
    have := congrArg (fun P : R[X] ↦ P.coeff i) h0
    simpa [coeff_toPoly, coord] using this)
  have hcomb : polyComb (depend d vs) vs = 0 := polyComb_eq_zero hvlen h3
  have hdvd : toPoly S ∣ (toPoly (depend d vs)).comp (toPoly r) := by
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · -- `S` is a nonzero constant
      have hunit : IsUnit (toPoly S) :=
        Polynomial.isUnit_iff_degree_eq_zero.mpr (by rw [hdegS, hd0]; rfl)
      exact hunit.dvd
    · have := dvd_comp_sub_polyComb S r hdpos hdegS (d + 1) (depend d vs) [1]
        (by rw [h1, hvs, length_powersModAux]) (by simp [toPoly_cons]; exact_mod_cast hdpos)
      rw [← hvs, hcomb, sub_zero, toPoly_cons, toPoly_nil, mul_zero, add_zero, C_1,
        mul_one] at this
      exact this
  simp only [muCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨fun h0 ↦ hμ0 ((trim_eq_nil_iff _).mp h0), ?_⟩
  rw [isZero_iff]
  change toPoly (divMod (compC (depend d vs) r) S).2 = 0
  exact divMod_exact _ _ hS0 (by rw [toPoly_compC]; exact hdvd)

/-- The data defining `simplePart`, as equations stable under extension of the constants:
`Gd = S₀ G₁`, `Gd′ = G₁ q₁`, `σ Gd + τ Gd′ = G₁`, `S₀ = S G`, `Gd′ = G q₂`, `σ' S₀ + τ' Gd′ = G`. -/
theorem simplePart_data (Gd : CPoly R) (hGd0 : toPoly Gd ≠ 0) :
    ∃ S₀ G₁ G q₁ q₂ σ τ σ' τ' : R[X],
      toPoly Gd = S₀ * G₁ ∧ derivative (toPoly Gd) = G₁ * q₁ ∧
        σ * toPoly Gd + τ * derivative (toPoly Gd) = G₁ ∧
      S₀ = toPoly (simplePart Gd) * G ∧ derivative (toPoly Gd) = G * q₂ ∧
        σ' * S₀ + τ' * derivative (toPoly Gd) = G := by
  set S₀ := sqfreePart Gd with hS₀
  have hE1 := sqfreePart_mul Gd hGd0
  obtain ⟨-, hE2⟩ := egcd_dvd Gd (deriv Gd)
  have hE3 := egcd_spec Gd (deriv Gd)
  rw [toPoly_deriv] at hE2 hE3
  rw [toPoly_gcd] at hE1
  set G := gcd S₀ (deriv Gd) with hG
  have hGS₀ : toPoly G ∣ toPoly S₀ := by rw [hG, toPoly_gcd]; exact (egcd_dvd _ _).1
  have hS₀0 : toPoly S₀ ≠ 0 := fun h0 ↦ hGd0 (by rw [hE1, h0, zero_mul])
  have hG0 : toPoly G ≠ 0 := fun h0 ↦ hS₀0 (by simpa [h0] using hGS₀)
  have hE4 := div_mul_of_dvd S₀ G hG0 hGS₀
  obtain ⟨-, hE5⟩ := egcd_dvd S₀ (deriv Gd)
  have hE6 := egcd_spec S₀ (deriv Gd)
  rw [toPoly_deriv] at hE5 hE6
  rw [← toPoly_gcd, ← hG] at hE5 hE6
  obtain ⟨q₁, hq₁⟩ := hE2
  obtain ⟨q₂, hq₂⟩ := hE5
  exact ⟨toPoly S₀, toPoly (egcd Gd (deriv Gd)).1, toPoly G, q₁, q₂, _, _, _, _, hE1, hq₁, hE3,
    hE4, hq₂, hE6⟩

/-- The Bézout identity of `residuePolyW`: `r Gd′ + t S = Gn`, provided `S` and `Gd′` are coprime
(which `simplePart_props` guarantees). -/
theorem residuePolyW_bezout (Gn Gd : CPoly R) (hS0 : toPoly (simplePart Gd) ≠ 0)
    (hcop : IsCoprime (derivative (toPoly Gd)) (toPoly (simplePart Gd))) :
    ∃ t : R[X], toPoly (residuePolyW Gn Gd) * derivative (toPoly Gd) +
      t * toPoly (simplePart Gd) = toPoly Gn := by
  have := solveBezout_spec (deriv Gd) (simplePart Gd) Gn hS0 (by rwa [toPoly_deriv])
  rw [toPoly_deriv] at this
  exact ⟨_, this⟩

end Spec

end CPoly

namespace Differential

open Polynomial

variable {F : Type*} [Field F] [CharZero F]

/-- **Properties of the simple part**, derived from the equations of `simplePart_data` over any
field of characteristic zero: `S ≠ 0`, `S ∣ Gd`, `S` coprime to `Gd′`, no prime of `S` divides
`Gd′`, and every simple prime of `Gd` divides `S`. -/
theorem simplePart_props {Gd S₀ G₁ G S q₁ q₂ σ τ σ' τ' : F[X]} (hGd0 : Gd ≠ 0)
    (E1 : Gd = S₀ * G₁) (E2 : derivative Gd = G₁ * q₁) (E3 : σ * Gd + τ * derivative Gd = G₁)
    (E4 : S₀ = S * G) (E5 : derivative Gd = G * q₂) (E6 : σ' * S₀ + τ' * derivative Gd = G) :
    S ≠ 0 ∧ S ∣ Gd ∧ IsCoprime S (derivative Gd) ∧
      (∀ p : F[X], Irreducible p → p ∣ S → ¬p ∣ derivative Gd) ∧
      (∀ p : F[X], Irreducible p → p ∣ Gd → ¬p ∣ derivative Gd → p ∣ S) ∧ Squarefree S := by
  have hS₀0 : S₀ ≠ 0 := fun h0 ↦ hGd0 (by rw [E1, h0, zero_mul])
  have hS0 : S ≠ 0 := fun h0 ↦ hS₀0 (by rw [E4, h0, zero_mul])
  have hsq : Squarefree S₀ := squarefree_of_gcd_derivative hGd0 (by rw [E1, mul_comm]) ⟨q₁, E2⟩
      fun h h1 h2 ↦ by
    rw [← E3]; exact dvd_add (Dvd.dvd.mul_left h1 _) (Dvd.dvd.mul_left h2 _)
  have hSd : S ∣ Gd := by rw [E1, E4]; exact (dvd_mul_right S G).trans (dvd_mul_right _ _)
  have hprime : ∀ p : F[X], Irreducible p → p ∣ S → ¬p ∣ derivative Gd := fun p hp hpS hpd ↦ by
    have hpG : p ∣ G := by
      rw [← E6]
      exact dvd_add (Dvd.dvd.mul_left (E4 ▸ hpS.trans (dvd_mul_right S G)) _)
        (Dvd.dvd.mul_left hpd _)
    exact hp.not_isUnit (hsq p (by rw [E4]; exact mul_dvd_mul hpS hpG))
  refine ⟨hS0, hSd, ?_, hprime, fun p hp hpG hpd ↦ ?_, hsq.squarefree_of_dvd ⟨G, E4⟩⟩
  · refine isCoprime_of_dvd _ _ (fun h ↦ hS0 h.1) fun z hz hz0 hzS hzd ↦ ?_
    obtain ⟨p, hp, hpz⟩ := WfDvdMonoid.exists_irreducible_factor hz hz0
    exact hprime p hp (hpz.trans hzS) (hpz.trans hzd)
  · have hpS₀ : p ∣ S₀ := by
      rw [E1] at hpG
      rcases hp.prime.dvd_or_dvd hpG with h | h
      · exact h
      · exact absurd (E2 ▸ h.trans (dvd_mul_right G₁ q₁)) hpd
    rw [E4] at hpS₀
    rcases hp.prime.dvd_or_dvd hpS₀ with h | h
    · exact h
    · exact absurd (E5 ▸ h.trans (dvd_mul_right G q₂)) hpd

end Differential

-- `η = 1 / (x² + 1)` (`exp (arctan x)`): `S = x² + 1`, `r = -x/2`, `μ = 4z² + 1`
#eval CPoly.trim (CPoly.simplePart ([1, 0, 1] : CPoly ℚ))
#eval CPoly.trim (CPoly.residuePolyW ([1] : CPoly ℚ) [1, 0, 1])
#eval CPoly.findMu ([1, 0, 1] : CPoly ℚ) (CPoly.residuePolyW ([1] : CPoly ℚ) [1, 0, 1])
#eval CPoly.muCheck ([1, 0, 1] : CPoly ℚ) (CPoly.residuePolyW ([1] : CPoly ℚ) [1, 0, 1])
  (CPoly.findMu ([1, 0, 1] : CPoly ℚ) (CPoly.residuePolyW ([1] : CPoly ℚ) [1, 0, 1]))
-- `η = 3/x + 1/(x-1)²`: `Gd = x (x-1)²`, `S = x`, residue `3`
#eval CPoly.trim (CPoly.simplePart (CPoly.mul [0, 1] [1, -2, 1] : CPoly ℚ))
#eval CPoly.findMu (CPoly.simplePart (CPoly.mul [0, 1] [1, -2, 1] : CPoly ℚ))
  (CPoly.residuePolyW (CPoly.add (CPoly.smul 3 [1, -2, 1]) [0, 1]) (CPoly.mul [0, 1] [1, -2, 1]))
