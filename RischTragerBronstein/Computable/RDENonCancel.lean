import RischTragerBronstein.Computable.GEuclidDegree

/-!
# The Risch differential equation in the non-cancellation case, generically

`y′ + g y = A / D` over `K(t)` with `deg_t g ≥ 1` (e.g. `t₂ = exp a` with `a ∈ K[t]` of positive
degree: `g = n a′`). With `y = Y / D`: `D Y′ + P₀ Y = A D`, `P₀ = g D - D′`, and since
`deg (D Y′) < deg P₀ + deg Y`, the coefficients of `Y` are determined **from the top by division**
— no lower-level differential equation at all.

`GPoly.rdeNC O w g A D`: the executable solver on codes (`w` the code of `t′`);
* `rdeNC_sound`: a returned `Y` satisfies `D Y′ + (g D - D′) Y = A D`, in every model;
* `rdeNC_complete`: if a polynomial solution exists, the solver finds one.
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace GPoly

section Defs

variable {α : Type*} (O : COps α)

/-- The coefficient of `t^k`. -/
def coeffAt (p : GPoly α) (k : ℕ) : α := p.getD k O.zero

/-- The top-down loop: `fuel` remaining coefficients (`t^(fuel-1)` down to `t^0`), `m = deg P₀`. -/
def rdeNCLoop (w D P₀ : GPoly α) (lcInv : α) (m : ℕ) :
    ℕ → GPoly α → GPoly α → GPoly α × GPoly α
  | 0, Y, Rm => (Y, Rm)
  | fuel + 1, Y, Rm =>
    let c := O.mul (coeffAt O Rm (fuel + m)) lcInv
    let mono := monomial O fuel c
    rdeNCLoop w D P₀ lcInv m fuel (add O Y mono)
      (sub O Rm (add O (mul O D (derivT O w mono)) (mul O P₀ mono)))

/-- **The non-cancellation solver.** -/
def rdeNC (w g A D : GPoly α) : Option (GPoly α) :=
  let P₀ := sub O (mul O g D) (derivT O w D)
  let tP := trim O P₀
  if tP = [] then none
  else
    let m := tP.length - 1
    let AD := mul O A D
    let st := rdeNCLoop O w D P₀ (O.inv (lead O tP)) m ((trim O AD).length - m) [] AD
    if isZero O st.2 then some st.1 else none

end Defs

variable {α K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)
variable [Differential K[X]]

lemma sem_coeffAt (p : GPoly α) (k : ℕ) : M.sem (coeffAt O p k) = (toPoly M p).coeff k := by
  rw [coeff_toPoly, coeffAt]
  by_cases hk : k < p.length
  · rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ (by simpa using hk),
      List.getElem_map]
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simpa using hk),
      M.sem_zero]

/-- The loop invariant: `D Y′ + P₀ Y + Rm` is constant. -/
lemma rdeNCLoop_invariant (w D P₀ : GPoly α) (lcInv : α) (m : ℕ)
    (hD : ∀ P : K[X], P′ = implicitDeriv (toPoly M w) P) (fuel : ℕ) (Y Rm : GPoly α) :
    toPoly M D * (toPoly M (rdeNCLoop O w D P₀ lcInv m fuel Y Rm).1)′ +
        toPoly M P₀ * toPoly M (rdeNCLoop O w D P₀ lcInv m fuel Y Rm).1 +
        toPoly M (rdeNCLoop O w D P₀ lcInv m fuel Y Rm).2 =
      toPoly M D * (toPoly M Y)′ + toPoly M P₀ * toPoly M Y + toPoly M Rm := by
  induction fuel generalizing Y Rm with
  | zero => rfl
  | succ fuel ih =>
    rw [rdeNCLoop, ih]
    simp only [toPoly_add, toPoly_sub, toPoly_mul, toPoly_derivT, map_add]
    rw [← hD]
    ring

/-- **Soundness.** -/
theorem rdeNC_sound (w g A D : GPoly α) (hD : ∀ P : K[X], P′ = implicitDeriv (toPoly M w) P)
    {Y : GPoly α} (h : rdeNC O w g A D = some Y) :
    toPoly M D * (toPoly M Y)′ + (toPoly M g * toPoly M D - (toPoly M D)′) * toPoly M Y =
      toPoly M A * toPoly M D := by
  simp only [rdeNC] at h
  split_ifs at h with h1 h2
  · have hinv := rdeNCLoop_invariant M w D (sub O (mul O g D) (derivT O w D)) (O.inv (lead O (trim O
      (sub O (mul O g D) (derivT O w D))))) ((trim O (sub O (mul O g D) (derivT O w D))).length - 1)
      hD ((trim O (mul O A D)).length - ((trim O (sub O (mul O g D) (derivT O w D))).length - 1))
      [] (mul O A D)
    rw [Option.some.inj h] at hinv
    rw [(isZero_iff M _).mp h2, add_zero] at hinv
    simp only [toPoly_nil, map_zero, mul_zero, zero_add, toPoly_sub, toPoly_mul, toPoly_derivT]
      at hinv
    rw [← hD] at hinv
    exact hinv

/-- **Completeness**, in the non-cancellation case `deg (D Z′) < deg P₀ + deg Z`. -/
theorem rdeNC_complete (w g A D : GPoly α) (hD : ∀ P : K[X], P′ = implicitDeriv (toPoly M w) P)
    (hder : ∀ P : K[X], (P′).natDegree ≤ P.natDegree)
    (hg : 1 ≤ (toPoly M g).natDegree) (hg0 : toPoly M g ≠ 0) (hD0 : toPoly M D ≠ 0)
    (Z : K[X]) (hZ : toPoly M D * Z′ + (toPoly M g * toPoly M D - (toPoly M D)′) * Z =
      toPoly M A * toPoly M D) :
    ∃ Y, rdeNC O w g A D = some Y := by
  classical
  set P₀ : GPoly α := sub O (mul O g D) (derivT O w D) with hP₀
  have hP₀poly : toPoly M P₀ = toPoly M g * toPoly M D - (toPoly M D)′ := by
    rw [hP₀, toPoly_sub, toPoly_mul, toPoly_derivT, ← hD]
  -- the degree of `P₀`
  have hgD : (toPoly M g * toPoly M D).natDegree = (toPoly M g).natDegree + (toPoly M D).natDegree :=
    natDegree_mul hg0 hD0
  have hD'lt : ((toPoly M D)′).natDegree < (toPoly M g * toPoly M D).natDegree := by
    rw [hgD]; have := hder (toPoly M D); omega
  have hP₀deg : (toPoly M P₀).natDegree = (toPoly M g).natDegree + (toPoly M D).natDegree := by
    rw [hP₀poly, natDegree_sub_eq_left_of_natDegree_lt hD'lt, hgD]
  have hP₀0 : toPoly M P₀ ≠ 0 := fun h0 ↦ by
    have := hP₀deg
    rw [h0, natDegree_zero] at this
    have := hg
    have hDd : 0 ≤ (toPoly M D).natDegree := Nat.zero_le _
    omega
  have htP : trim O P₀ ≠ [] := fun h0 ↦ hP₀0 ((trim_eq_nil_iff M P₀).mp h0)
  obtain ⟨hm, hlcP, hlc0⟩ := natDegree_toPoly_of_trim_ne_nil M htP
  set m := (trim O P₀).length - 1 with hmdef
  have hlcP' : M.sem (lead O (trim O P₀)) = (toPoly M P₀).leadingCoeff := by
    rw [leadingCoeff, hm, hlcP]
  -- the key degree estimate: `deg (D Z′) < m + deg Z` for `Z ≠ 0`
  have hkey : ∀ Z : K[X], Z ≠ 0 → (toPoly M D * Z′).natDegree < m + Z.natDegree := fun Z hZ0 ↦ by
    rw [← hm, hP₀deg]
    calc (toPoly M D * Z′).natDegree ≤ (toPoly M D).natDegree + (Z′).natDegree :=
          natDegree_mul_le
      _ ≤ (toPoly M D).natDegree + Z.natDegree := by have := hder Z; omega
      _ < (toPoly M g).natDegree + (toPoly M D).natDegree + Z.natDegree := by omega
  -- the loop invariant for completeness
  have hloop : ∀ (fuel : ℕ) (Y Rm : GPoly α) (Z : K[X]),
      toPoly M D * Z′ + toPoly M P₀ * Z = toPoly M Rm → Z.degree < fuel →
      isZero O (rdeNCLoop O w D P₀ (O.inv (lead O (trim O P₀))) m fuel Y Rm).2 = true := by
    intro fuel
    induction fuel with
    | zero =>
      intro Y Rm Z hZ hdeg
      have hZ0 : Z = 0 := degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp (by exact_mod_cast hdeg))
      rw [hZ0, map_zero, mul_zero, mul_zero, add_zero] at hZ
      show isZero O Rm = true
      exact (isZero_iff M Rm).mpr hZ.symm
    | succ fuel ih =>
      intro Y Rm Z hZ hdeg
      have hZdeg : Z.natDegree ≤ fuel := by
        by_cases hZ0 : Z = 0
        · rw [hZ0, natDegree_zero]; exact Nat.zero_le _
        · have := (degree_eq_natDegree hZ0) ▸ hdeg
          exact Nat.lt_succ_iff.mp (by exact_mod_cast this)
      -- the coefficient of `t^(fuel + m)`
      have hcoeff : (toPoly M Rm).coeff (fuel + m) = (toPoly M P₀).leadingCoeff * Z.coeff fuel := by
        rw [← hZ, coeff_add, add_comm fuel m]
        have h0 : (toPoly M D * Z′).coeff (m + fuel) = 0 := by
          by_cases hZ0 : Z = 0
          · rw [hZ0, map_zero, mul_zero, coeff_zero]
          · exact coeff_eq_zero_of_natDegree_lt ((hkey Z hZ0).trans_le (by omega))
        rw [h0, zero_add]
        rcases Nat.lt_or_ge Z.natDegree fuel with hlt | hge
        · have h1 : (toPoly M P₀ * Z).coeff (m + fuel) = 0 :=
            coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt (by omega))
          rw [h1, coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
        · have hZn : Z.natDegree = fuel := le_antisymm hZdeg hge
          rw [← hZn, ← hm, coeff_mul_degree_add_degree]
          rfl
      have hc : M.sem (O.mul (coeffAt O Rm (fuel + m)) (O.inv (lead O (trim O P₀)))) =
          Z.coeff fuel := by
        rw [M.sem_mul, M.sem_inv, sem_coeffAt, hcoeff, hlcP']
        have : (toPoly M P₀).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP₀0
        field_simp
      rw [rdeNCLoop]
      refine ih _ _ (Z - C (Z.coeff fuel) * X ^ fuel) ?_ ?_
      · simp only [toPoly_sub, toPoly_add, toPoly_mul, toPoly_derivT, toPoly_monomial, hc, map_sub]
        rw [← hZ, ← hD]
        ring
      · rw [degree_lt_iff_coeff_zero]
        intro n hn
        rw [coeff_sub, coeff_C_mul, coeff_X_pow]
        rcases Nat.lt_or_ge fuel n with hlt | hge
        · rw [if_neg (by omega), mul_zero, sub_zero]
          exact coeff_eq_zero_of_natDegree_lt (by omega)
        · have : n = fuel := by omega
          subst this
          simp
  simp only [rdeNC, ← hP₀]
  rw [if_neg htP]
  refine ⟨(rdeNCLoop O w D P₀ (O.inv (lead O (trim O P₀))) m ((trim O (mul O A D)).length - m)
    [] (mul O A D)).1, ?_⟩
  rw [if_pos (hloop ((trim O (mul O A D)).length - m) [] (mul O A D) Z
    (by rw [hP₀poly, toPoly_mul]; exact hZ) ?_)]
  -- the degree bound on `Z`
  by_cases hZ0 : Z = 0
  · rw [hZ0, degree_zero]; exact WithBot.bot_lt_coe _
  have hPZ : (toPoly M P₀ * Z).natDegree = m + Z.natDegree := by rw [natDegree_mul hP₀0 hZ0, hm]
  have hADeq : toPoly M (mul O A D) = toPoly M D * Z′ + toPoly M P₀ * Z := by
    rw [toPoly_mul, ← hZ, hP₀poly]
  have hAD : (toPoly M (mul O A D)).natDegree = m + Z.natDegree := by
    rw [hADeq, natDegree_add_eq_right_of_natDegree_lt (by rw [hPZ]; exact hkey Z hZ0), hPZ]
  have hAD0 : toPoly M (mul O A D) ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hAD
    omega
  have htAD : trim O (mul O A D) ≠ [] := fun h0 ↦ hAD0 ((trim_eq_nil_iff M _).mp h0)
  obtain ⟨hlen, -, -⟩ := natDegree_toPoly_of_trim_ne_nil M htAD
  have hpos := List.length_pos_of_ne_nil htAD
  rw [degree_eq_natDegree hZ0]
  exact_mod_cast (by omega : Z.natDegree < (trim O (mul O A D)).length - m)

end GPoly
