import RischTragerBronstein.Computable.GEuclid
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Total correctness of division and gcd over a computable model

The generic counterparts of `Computable/EuclidDegree.lean`:

* `GPoly.divMod_degree_lt`: `deg (p mod d) < deg d` for `d ≠ 0`;
* `GPoly.egcd_dvd`, `GPoly.dvd_egcd`: the executable gcd is a greatest common divisor;
* `GPoly.divMod_exact`, `GPoly.div_mul_of_dvd`: exact division.

They hold at every level of a computable tower; decidable equality of coefficients is replaced by
the model's zero test (`CField.isZero_iff`).
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace GPoly

variable {α K : Type*} [Field K] [Differential K] {O : COps α} (M : CField α K O)

lemma coeff_toPoly (p : GPoly α) (n : ℕ) :
    (toPoly M p).coeff n = (p.map M.sem).getD n 0 := by
  induction p generalizing n with
  | nil => simp
  | cons a p ih =>
    cases n with
    | zero => simp
    | succ n => simp [ih, coeff_X_mul]

lemma degree_toPoly_lt (p : GPoly α) : (toPoly M p).degree < p.length := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_toPoly, List.getD_eq_default _ _ (by simpa using hm)]

lemma isZero_getLast_trim (p : GPoly α) (h : trim O p ≠ []) :
    O.isZero ((trim O p).getLast h) = false := by
  have h' : p.reverse.dropWhile O.isZero ≠ [] := fun h0 ↦ h (by rw [trim, h0]; rfl)
  have := List.head_dropWhile_not O.isZero (l := p.reverse) h'
  simp only [trim, List.getLast_reverse]
  simpa using this

lemma natDegree_toPoly_of_trim_ne_nil {g : GPoly α} (hg : trim O g ≠ []) :
    (toPoly M g).natDegree = (trim O g).length - 1 ∧
      (toPoly M g).coeff ((trim O g).length - 1) = M.sem (lead O (trim O g)) ∧
      M.sem (lead O (trim O g)) ≠ 0 := by
  have hpos := List.length_pos_of_ne_nil hg
  have hlead : lead O (trim O g) = (trim O g).getLast hg := by
    rw [lead, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hg]; rfl
  have hne : M.sem (lead O (trim O g)) ≠ 0 := by
    rw [hlead]
    intro h0
    have := isZero_getLast_trim (O := O) g hg
    rw [(M.isZero_iff _).mpr h0] at this
    exact Bool.noConfusion this
  have hcoeff : (toPoly M g).coeff ((trim O g).length - 1) = M.sem (lead O (trim O g)) := by
    rw [← toPoly_trim M, coeff_toPoly, List.getD_eq_getElem _ _ (by simpa using by omega),
      List.getElem_map, ← List.getLast_eq_getElem hg, hlead]
  refine ⟨le_antisymm ?_ (le_natDegree_of_ne_zero (hcoeff ▸ hne)), hcoeff, hne⟩
  have h1 := degree_toPoly_lt M (trim O g)
  rw [toPoly_trim] at h1
  have h2 := (natDegree_lt_iff_degree_lt (p := toPoly M g) (n := (trim O g).length)
    (fun h0 ↦ by rw [h0, coeff_zero] at hcoeff; exact hne hcoeff.symm)).mpr h1
  omega

lemma trim_eq_nil_iff (p : GPoly α) : trim O p = [] ↔ toPoly M p = 0 := by
  constructor
  · intro h; rw [← toPoly_trim M, h]; rfl
  · intro h
    by_contra hne
    obtain ⟨-, hlc, hlc0⟩ := natDegree_toPoly_of_trim_ne_nil M hne
    rw [h, coeff_zero] at hlc
    exact hlc0 hlc.symm

lemma length_trim {p : GPoly α} (h : trim O p ≠ []) :
    (trim O p).length = (toPoly M p).natDegree + 1 := by
  have := (natDegree_toPoly_of_trim_ne_nil M h).1
  have hpos := List.length_pos_of_ne_nil h
  omega

lemma length_trim_le (p : GPoly α) : (trim O p).length ≤ p.length := by
  unfold trim
  rw [List.length_reverse]
  exact ((List.dropWhile_sublist _).length_le).trans (by rw [List.length_reverse])

lemma trim_trim (p : GPoly α) : trim O (trim O p) = trim O p := by
  unfold trim
  rw [List.reverse_reverse]
  congr 1
  generalize p.reverse = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : O.isZero a = true
    · simp [List.dropWhile_cons_of_pos ha, ih]
    · simp [List.dropWhile_cons_of_neg ha]

lemma leadingCoeff_toPoly {q : GPoly α} (hq : toPoly M q ≠ 0) :
    (toPoly M q).leadingCoeff = M.sem (lead O (trim O q)) := by
  have hne : trim O q ≠ [] := fun h ↦ hq ((trim_eq_nil_iff M q).mp h)
  obtain ⟨hdeg, hlc, -⟩ := natDegree_toPoly_of_trim_ne_nil M hne
  rw [leadingCoeff, hdeg, hlc]

include M in
/-- One division step strictly lowers the trimmed length. -/
lemma length_trim_step_lt {p d : GPoly α} (hp : trim O p = p) (hd : trim O d = d) (hp0 : p ≠ [])
    (hd0 : d ≠ []) (hle : d.length ≤ p.length) :
    (trim O (sub O p (mul O (monomial O (p.length - d.length)
      (O.mul (lead O p) (O.inv (lead O d)))) d))).length < p.length := by
  have hpne : trim O p ≠ [] := hp.symm ▸ hp0
  have hdne : trim O d ≠ [] := hd.symm ▸ hd0
  obtain ⟨hpdeg, hplc, hplc0⟩ := natDegree_toPoly_of_trim_ne_nil M hpne
  obtain ⟨hddeg, hdlc, hdlc0⟩ := natDegree_toPoly_of_trim_ne_nil M hdne
  rw [hp] at hpdeg hplc hplc0
  rw [hd] at hddeg hdlc hdlc0
  set P := toPoly M p with hP
  set D := toPoly M d with hD
  set k := p.length - d.length
  set c := M.sem (lead O p) / M.sem (lead O d) with hc
  have hP0 : P ≠ 0 := fun h ↦ hp0 (hp ▸ (trim_eq_nil_iff M p).mpr h)
  have hD0 : D ≠ 0 := fun h ↦ hd0 (hd ▸ (trim_eq_nil_iff M d).mpr h)
  have hPlc : P.leadingCoeff = M.sem (lead O p) := by rw [leadingCoeff, hpdeg, hplc]
  have hDlc : D.leadingCoeff = M.sem (lead O d) := by rw [leadingCoeff, hddeg, hdlc]
  have hc0 : c ≠ 0 := div_ne_zero hplc0 hdlc0
  have hQ : toPoly M (sub O p (mul O (monomial O k (O.mul (lead O p) (O.inv (lead O d)))) d)) =
      P - C c * X ^ k * D := by
    simp [M.sem_mul, M.sem_inv, hc, hP, hD, div_eq_mul_inv]
  have hM0 : C c * X ^ k * D ≠ 0 :=
    mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hc0) (pow_ne_zero _ X_ne_zero)) hD0
  have hMdeg : (C c * X ^ k * D).natDegree = P.natDegree := by
    rw [natDegree_mul (mul_ne_zero (C_ne_zero.mpr hc0) (pow_ne_zero _ X_ne_zero)) hD0,
      natDegree_C_mul_X_pow k c hc0, hpdeg, hddeg]
    have := List.length_pos_of_ne_nil hd0
    omega
  have hMlc : (C c * X ^ k * D).leadingCoeff = P.leadingCoeff := by
    rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X_pow, mul_one, hDlc,
      hPlc, hc]
    field_simp
  have hlt : (P - C c * X ^ k * D).degree < P.degree :=
    degree_sub_lt_left (by rw [degree_eq_natDegree hP0, degree_eq_natDegree hM0, hMdeg]) hP0
      hMlc.symm
  by_cases hnil : trim O (sub O p (mul O (monomial O k (O.mul (lead O p) (O.inv (lead O d)))) d))
      = []
  · rw [hnil]; exact List.length_pos_of_ne_nil hp0
  · rw [length_trim M hnil, hQ]
    have hQ0 : P - C c * X ^ k * D ≠ 0 := fun h ↦ hnil ((trim_eq_nil_iff M _).mpr (hQ.trans h))
    have := natDegree_lt_natDegree hQ0 hlt
    have := List.length_pos_of_ne_nil hp0
    omega

include M in
lemma divModAux_remainder_lt (d : GPoly α) (hd : trim O d = d) (hd0 : d ≠ []) (fuel : ℕ)
    (acc p : GPoly α) (hfuel : (trim O p).length ≤ fuel) :
    (trim O (divModAux O d fuel acc p).2).length < d.length := by
  induction fuel generalizing acc p with
  | zero =>
    simp only [divModAux]
    have : (trim O p).length = 0 := by omega
    rw [this]; exact List.length_pos_of_ne_nil hd0
  | succ fuel ih =>
    simp only [divModAux]
    split_ifs with hstop
    · rw [trim_trim]
      rcases hstop with h | h
      · exact h
      · rw [h]; exact List.length_pos_of_ne_nil hd0
    · rw [not_or, not_lt] at hstop
      apply ih
      have hp0 : trim O p ≠ [] := fun h ↦ hstop.2 (by rw [h]; rfl)
      have := length_trim_step_lt M (trim_trim p) hd hp0 hd0 hstop.1
      omega

include M in
theorem divMod_remainder_lt (p d : GPoly α) (hd : trim O d ≠ []) :
    (trim O (divMod O p d).2).length < (trim O d).length :=
  divModAux_remainder_lt M (trim O d) (trim_trim d) hd (p.length + 1) [] p
    ((length_trim_le p).trans (Nat.le_succ _))

theorem divMod_degree_lt (p d : GPoly α) (hd : toPoly M d ≠ 0) :
    (toPoly M (divMod O p d).2).degree < (toPoly M d).degree := by
  have hdne : trim O d ≠ [] := fun h ↦ hd ((trim_eq_nil_iff M d).mp h)
  have hlt := divMod_remainder_lt M p d hdne
  by_cases hr : toPoly M (divMod O p d).2 = 0
  · rw [hr, degree_zero]; exact bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hd)
  · have hrne : trim O (divMod O p d).2 ≠ [] := fun h ↦ hr ((trim_eq_nil_iff M _).mp h)
    rw [degree_eq_natDegree hr, degree_eq_natDegree hd]
    have h1 := length_trim M hrne
    have h2 := length_trim M hdne
    exact_mod_cast (by omega : (toPoly M (divMod O p d).2).natDegree < (toPoly M d).natDegree)

lemma egcdAux_dvd (fuel : ℕ) (x y : GPoly α × GPoly α × GPoly α)
    (hfuel : (trim O y.1).length < fuel) :
    toPoly M (egcdAux O fuel x y).1 ∣ toPoly M x.1 ∧
      toPoly M (egcdAux O fuel x y).1 ∣ toPoly M y.1 := by
  induction fuel generalizing x y with
  | zero => omega
  | succ fuel ih =>
    obtain ⟨r₀, s₀, t₀⟩ := x
    obtain ⟨r₁, s₁, t₁⟩ := y
    simp only [egcdAux]
    split_ifs with hz
    · exact ⟨dvd_rfl, by rw [(isZero_iff M r₁).mp hz]; exact dvd_zero _⟩
    · have hr₁ : trim O r₁ ≠ [] := fun h ↦
        hz ((isZero_iff M r₁).mpr ((trim_eq_nil_iff M r₁).mp h))
      have hlt := divMod_remainder_lt M r₀ r₁ hr₁
      obtain ⟨h1, h2⟩ := ih (r₁, s₁, t₁)
        ((divMod O r₀ r₁).2, sub O s₀ (mul O (divMod O r₀ r₁).1 s₁),
          sub O t₀ (mul O (divMod O r₀ r₁).1 t₁))
        (by simp only at hfuel ⊢; omega)
      refine ⟨?_, h1⟩
      rw [divMod_spec M r₀ r₁]
      exact dvd_add (Dvd.dvd.mul_left h1 _) h2

theorem egcd_dvd (p q : GPoly α) :
    toPoly M (egcd O p q).1 ∣ toPoly M p ∧ toPoly M (egcd O p q).1 ∣ toPoly M q :=
  egcdAux_dvd M _ (p, [O.one], []) (q, [], [O.one]) (by
    have := length_trim_le (O := O) q
    simp only
    omega)

theorem dvd_egcd (p q : GPoly α) {h : K[X]} (hp : h ∣ toPoly M p) (hq : h ∣ toPoly M q) :
    h ∣ toPoly M (egcd O p q).1 := by
  rw [← egcd_spec M p q]
  exact dvd_add (Dvd.dvd.mul_left hp _) (Dvd.dvd.mul_left hq _)

theorem divMod_exact (p d : GPoly α) (hd : toPoly M d ≠ 0) (hdvd : toPoly M d ∣ toPoly M p) :
    toPoly M (divMod O p d).2 = 0 := by
  have hspec := divMod_spec M p d
  have hrem : toPoly M d ∣ toPoly M (divMod O p d).2 := by
    have : toPoly M (divMod O p d).2 =
        toPoly M p - toPoly M (divMod O p d).1 * toPoly M d := by rw [hspec]; ring
    rw [this]
    exact dvd_sub hdvd (Dvd.intro_left _ rfl)
  exact eq_zero_of_dvd_of_degree_lt hrem (divMod_degree_lt M p d hd)

theorem div_mul_of_dvd (p d : GPoly α) (hd : toPoly M d ≠ 0) (hdvd : toPoly M d ∣ toPoly M p) :
    toPoly M p = toPoly M (divMod O p d).1 * toPoly M d := by
  have := divMod_spec M p d
  rwa [divMod_exact M p d hd hdvd, add_zero] at this

end GPoly
