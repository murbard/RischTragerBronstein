import RischTragerBronstein.Mixed.SysPrim
import RischTragerBronstein.Mixed.SysSpecial3

/-!
# The system solver at a primitive level always answers in its regime

**`primSysC_isSome`**: `primSysC` answers when `q`, `h` are monic, the matrix vanishes at infinity
(`deg A₀ < deg q`), no irreducible factor of `q` divides `D(q)` (squarefree normal `q`) and `η` is
not a derivative in `Fₘ`:

* the indicial bound answers (`indBound2_isSome`);
* the degree check holds: `B_W = t (h Den A₀ − q h D(Den) I)` has degree `≤ deg a − 1`, since
  `D(Den)` lowers the degree of the monic `Den` (`degree_DzL_lt`);
* the special-degree bound answers (`specBound2_isSome`).
-/

open Polynomial Differential

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM

/-- `D(P) = P^D + w P′` lowers the degree of a monic `P`. -/
lemma degree_DzL_lt {K : Type*} [Field K] [Differential K] [CharZero K] (w : K) (P : K[X]) (hP : P.Monic) :
    (DzL w 0 P).degree < P.degree := by
  rw [DzL_eq, map_zero, zero_mul, add_zero]
  by_cases hd : P.natDegree = 0
  · rw [eq_one_of_monic_natDegree_zero hP hd]
    simp
  have hlt : ∀ i, P.natDegree ≤ i → ((mapCoeffs P) + C w * derivative P).coeff i = 0 := by
    intro i hi
    rw [coeff_add, coeff_mapCoeffs, coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (natDegree_derivative_lt hd) hi), mul_zero,
      add_zero]
    rcases hi.eq_or_lt with h | h
    · rw [← h, ← leadingCoeff, hP.leadingCoeff, Derivation.map_one_eq_zero]
    · rw [coeff_eq_zero_of_natDegree_lt h, map_zero]
  rw [degree_eq_natDegree hP.ne_zero]
  exact (degree_lt_iff_coeff_zero _ _).mpr fun i hi ↦ hlt i (by exact_mod_cast hi)

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

/-- **`primSysC` answers in its regime.** -/
theorem primSysC_isSome (m : ℕ) (h : T.Tr m) (η : LC m) (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h) lim) (n : ℕ)
    (A0 : Fin n → Fin n → GPoly (LC m)) (q hh : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m)))
    (hmon : (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hh) = true)
    (hA : ∀ i j, (GPoly.toPoly (T.MP m h) (A0 i j)).degree < (GPoly.toPoly (T.MP m h) q).degree)
    (hpd : ∀ p : (T.F m)[X], Irreducible p → p ∣ GPoly.toPoly (T.MP m h) q →
      ¬ p ∣ GPoly.toPoly (T.MP m h) (DzLC (MO Fc ks m) η (MO Fc ks m).zero q))
    (hη : ∀ y : T.F m, y′ ≠ (T.MP m h).sem η) :
    (primSysC Fc ks m η lim n A0 q hh G0).isSome := by
  set O := MO Fc ks m with hO
  set M := T.MP m h with hM
  rw [Bool.and_eq_true] at hmon
  have hqM := isMonicC_spec M q hmon.1
  have hhM := isMonicC_spec M hh hmon.2
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp
    (T.indBound2_isSome m h (degG O q) n q (DzLC O η O.zero q) A0 hqM (degG_eq M q).symm hpd)
  set W := wSys Fc ks m η n A0 q hh G0 B with hW
  -- the degree check
  have hDen := T.wSys_Den m h η n A0 q hh G0 B
  have hDmon : (GPoly.toPoly M W.Den).Monic := by rw [hDen]; exact hhM.mul (hqM.pow B)
  have hokB : ((List.finRange n).all fun i ↦ (List.finRange n).all fun j ↦
      decide ((GPoly.trim O (W.BW i j)).length ≤ degG O W.a)) = true := by
    simp only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]
    intro i j
    have hBW := T.wSys_BW m h η n A0 q hh G0 B i j
    simp only [semPM] at hBW
    rw [degG_eq M, T.wSys_a m h η n A0 q hh G0 B]
    set qs := GPoly.toPoly M q
    set hs := GPoly.toPoly M hh
    set Ds := GPoly.toPoly M W.Den
    have hqhD : (qs * (hs * Ds)).Monic := hqM.mul (hhM.mul hDmon)
    -- the inner polynomial has degree below `deg (q h Den)`
    have hhD0 : (hs * Ds).degree ≠ ⊥ := by
      rw [Ne, degree_eq_bot]; exact (hhM.mul hDmon).ne_zero
    have hin : (hs * Ds * semMat M A0 i j - if i = j then qs * (hs * DzL (M.sem η) 0 Ds) else 0).degree
        < (qs * (hs * Ds)).degree := by
      refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_)
      · rw [show qs * (hs * Ds) = hs * Ds * qs by ring, degree_mul, degree_mul (p := hs * Ds)]
        exact WithBot.add_lt_add_left hhD0 (hA i j)
      · split_ifs
        · rw [degree_mul, degree_mul, degree_mul, degree_mul]
          have hq0 : qs.degree ≠ ⊥ := by rw [Ne, degree_eq_bot]; exact hqM.ne_zero
          have hh0 : hs.degree ≠ ⊥ := by rw [Ne, degree_eq_bot]; exact hhM.ne_zero
          exact WithBot.add_lt_add_left hq0 (WithBot.add_lt_add_left hh0
            (degree_DzL_lt (M.sem η) Ds hDmon))
        · rw [degree_zero]
          exact bot_lt_iff_ne_bot.mpr (by rw [Ne, degree_eq_bot]; exact hqhD.ne_zero)
    set inner := hs * Ds * semMat M A0 i j - if i = j then qs * (hs * DzL (M.sem η) 0 Ds) else 0
    by_cases hz : GPoly.toPoly M (W.BW i j) = 0
    · rw [(GPoly.trim_eq_nil_iff M _).mpr hz]
      exact Nat.zero_le _
    · have hne : GPoly.trim O (W.BW i j) ≠ [] := fun h0 ↦ hz ((GPoly.trim_eq_nil_iff M _).mp h0)
      rw [GPoly.length_trim M hne, hBW]
      have hi0 : inner ≠ 0 := fun h0 ↦ hz (by rw [hBW, h0, mul_zero])
      rw [natDegree_mul X_ne_zero hi0, natDegree_mul X_ne_zero hqhD.ne_zero, natDegree_X]
      have := natDegree_lt_natDegree hi0 hin
      omega
  -- assemble
  unfold primSysC
  dsimp only
  rw [if_neg (by simp only [hO] at hmon; simp [hmon.1, hmon.2]), hB]
  dsimp only
  rw [← hW, if_neg (by rw [hokB]; decide)]
  obtain ⟨Bs, hBs⟩ := Option.isSome_iff_exists.mp
    (T.specBound2_isSome m h lim hlim n η _ hη)
  rw [hBs]
  rfl

/-- A squarefree `q` is coprime to its derivative factor-wise at a primitive level. -/
lemma not_dvd_DzLC_of_squarefree (m : ℕ) (h : T.Tr m) (η : LC m) (hm : m < T.n)
    (htr : Transcendental (T.F m) (T.ts m)) (hk : ks m = .prim η) (q : GPoly (LC m))
    (hsq : Squarefree (GPoly.toPoly (T.MP m h) q)) :
    ∀ p : (T.F m)[X], Irreducible p → p ∣ GPoly.toPoly (T.MP m h) q →
      ¬ p ∣ GPoly.toPoly (T.MP m h) (DzLC (MO Fc ks m) η (MO Fc ks m).zero q) := by
  intro p hp hpq hdiv
  rw [toPoly_DzLC, (T.MP m h).sem_zero] at hdiv
  obtain ⟨r, hr⟩ := hpq
  rw [hr] at hdiv
  have hl : DzL ((T.MP m h).sem η) 0 (p * r) =
      p * DzL ((T.MP m h).sem η) 0 r + r * DzL ((T.MP m h).sem η) 0 p := by
    simp only [DzL, Derivation.leibniz, smul_eq_mul]
  rw [hl] at hdiv
  have h2 : p ∣ r * DzL ((T.MP m h).sem η) 0 p := (dvd_add_right (dvd_mul_right p _)).mp hdiv
  rcases hp.prime.dvd_or_dvd h2 with h3 | h3
  · obtain ⟨s, hs⟩ := h3
    have : p * p ∣ GPoly.toPoly (T.MP m h) q := ⟨s, by rw [hr, hs]; ring⟩
    exact hp.not_isUnit (hsq p this)
  · exact T.not_dvd_DzL m h η hm htr hk p hp h3

/-- **`primSysC` answers** at a certified primitive level for squarefree monic `q`, monic `h` and a
matrix vanishing at infinity. -/
theorem primSysC_isSome_sq (m : ℕ) (h : T.Tr m) (η : LC m) (hm : m < T.n)
    (htr : Transcendental (T.F m) (T.ts m)) (hk : ks m = .prim η)
    (lim : List (LC m) → List (List ℚ × LC m))
    (hlim : LimSpec (algebraMap Cc (T.F m)) (T.MP m h) lim) (n : ℕ)
    (A0 : Fin n → Fin n → GPoly (LC m)) (q hh : GPoly (LC m)) (G0 : List (Fin n → GPoly (LC m)))
    (hmon : (isMonicC (MO Fc ks m) q && isMonicC (MO Fc ks m) hh) = true)
    (hA : ∀ i j, (GPoly.toPoly (T.MP m h) (A0 i j)).degree < (GPoly.toPoly (T.MP m h) q).degree)
    (hsq : Squarefree (GPoly.toPoly (T.MP m h) q))
    (hη : ∀ y : T.F m, y′ ≠ (T.MP m h).sem η) :
    (primSysC Fc ks m η lim n A0 q hh G0).isSome :=
  T.primSysC_isSome m h η lim hlim n A0 q hh G0 hmon hA
    (T.not_dvd_DzLC_of_squarefree m h η hm htr hk q hsq) hη

end MTower

end Curves.MT
