import RischTragerBronstein.Computable.DegCount
import RischTragerBronstein.Computable.EuclidDegree

/-!
# Factor degrees modulo a prime: a fast certificate that no factor of a given degree exists

Distinct-degree factorisation over a finite field `R` with `p` elements: for a squarefree `f`,
`ddf` computes `h₁, h₂, …` with `h_d = gcd(f_{d-1}, X^{p^d} − X)`, `f_d = f_{d-1}/h_d`, and returns
the degrees of the `h_d`. Every irreducible factor of `f` of degree `d` divides `h_d`
(`ddf_spec`; `Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`). With `DegCount`, the degree
of every divisor of `f` is one of the sums `∑ d c_d`, `d c_d ≤ deg h_d` (`sums`, `mem_sums`).
-/

open Polynomial

namespace CPoly

namespace DegCert

section Field

variable {R : Type*} [Field R] [DecidableEq R]

/-- `aⁿ mod f` by repeated squaring (fuel `k ≥ n`; structural, so that the kernel can run it). -/
def powModAux (f a : CPoly R) : ℕ → ℕ → CPoly R
  | 0, _ => [1]
  | k + 1, n =>
    if n = 0 then [1] else
      let h := powModAux f a k (n / 2)
      let s := (divMod (mul h h) f).2
      if n % 2 = 1 then (divMod (mul s a) f).2 else s

/-- `aⁿ mod f`. -/
def powMod (f a : CPoly R) (n : ℕ) : CPoly R := powModAux f a n n

lemma dvd_rem_sub (x f : CPoly R) : toPoly f ∣ toPoly (divMod x f).2 - toPoly x :=
  ⟨-toPoly (divMod x f).1, by
    have := divMod_spec x f
    linear_combination -this⟩

lemma powModAux_spec (f a : CPoly R) : ∀ (k n : ℕ), n ≤ k →
    toPoly f ∣ toPoly (powModAux f a k n) - toPoly a ^ n
  | 0, n, hn => by
    obtain rfl : n = 0 := by omega
    simp [powModAux, toPoly_cons]
  | k + 1, n, hn => by
    rw [powModAux]
    split_ifs with h0 h1
    · subst h0; simp [toPoly_cons]
    · have hh := powModAux_spec f a k (n / 2) (by omega)
      set h := powModAux f a k (n / 2)
      set s := (divMod (mul h h) f).2
      have hs : toPoly f ∣ toPoly s - toPoly a ^ (n / 2) * toPoly a ^ (n / 2) := by
        have h1 := dvd_rem_sub (mul h h) f
        rw [toPoly_mul] at h1
        have h2 : toPoly f ∣ toPoly h * toPoly h - toPoly a ^ (n / 2) * toPoly a ^ (n / 2) := by
          obtain ⟨c, hc⟩ := hh
          exact ⟨c * toPoly h + toPoly a ^ (n / 2) * c, by
            linear_combination toPoly h * hc + toPoly a ^ (n / 2) * hc⟩
        have := dvd_add h1 h2
        simpa using this
      have h3 := dvd_rem_sub (mul s a) f
      rw [toPoly_mul] at h3
      have e : toPoly a ^ n = toPoly a ^ (n / 2) * toPoly a ^ (n / 2) * toPoly a := by
        rw [← pow_add, ← pow_succ]; congr 1; omega
      rw [e]
      have h4 : toPoly f ∣ (toPoly s - toPoly a ^ (n / 2) * toPoly a ^ (n / 2)) * toPoly a :=
        Dvd.dvd.mul_right hs _
      have := dvd_add h3 h4
      convert this using 1; ring
    · have hh := powModAux_spec f a k (n / 2) (by omega)
      set h := powModAux f a k (n / 2)
      have h1 := dvd_rem_sub (mul h h) f
      rw [toPoly_mul] at h1
      have e : toPoly a ^ n = toPoly a ^ (n / 2) * toPoly a ^ (n / 2) := by
        rw [← pow_add]; congr 1; omega
      rw [e]
      obtain ⟨c, hc⟩ := hh
      obtain ⟨c1, hc1⟩ := h1
      refine ⟨c1 + c * toPoly h + toPoly a ^ (n / 2) * c, ?_⟩
      linear_combination hc1 + toPoly h * hc + toPoly a ^ (n / 2) * hc

lemma powMod_spec (f a : CPoly R) (n : ℕ) : toPoly f ∣ toPoly (powMod f a n) - toPoly a ^ n :=
  powModAux_spec f a n n le_rfl

/-- **Distinct-degree factorisation** (`n` rounds; `w = X^{p^j} mod f`, `cur = f_j`): the degrees
of `h_{j+1}, h_{j+2}, …`. -/
def ddf (p : ℕ) (f : CPoly R) : ℕ → CPoly R → CPoly R → Option (List ℕ)
  | 0, _, _ => some []
  | n + 1, w, cur =>
    let w' := powMod f w p
    let d := sub w' [0, 1]
    let g := (egcd cur d).1
    let q1 := divMod cur g
    let q2 := divMod d g
    if isZero g then none
    else if isZero q1.2 && isZero q2.2 then
      (ddf p f n w' q1.1).map fun l ↦ ((trim g).length - 1) :: l
    else none

/-- The sums `∑ᵢ (j + i) cᵢ` with `(j + i) cᵢ ≤ lᵢ`. -/
def sums : ℕ → List ℕ → List ℕ
  | _, [] => [0]
  | j, m :: l => ((List.range (m / j + 1)).flatMap fun c ↦ (sums (j + 1) l).map (c * j + ·)).dedup

lemma mem_sums : ∀ (l : List ℕ) (j : ℕ) (c : ℕ → ℕ), 1 ≤ j →
    (∀ i < l.length, (j + i) * c (j + i) ≤ l.getD i 0) →
    ∑ i ∈ Finset.range l.length, (j + i) * c (j + i) ∈ sums j l
  | [], _, _, _, _ => by simp [sums]
  | m :: l, j, c, hj, h => by
    rw [sums, List.mem_dedup, List.mem_flatMap]
    refine ⟨c j, ?_, ?_⟩
    · rw [List.mem_range]
      have := h 0 (by simp)
      simp only [add_zero, List.getD_cons_zero] at this
      have : c j ≤ m / j := (Nat.le_div_iff_mul_le hj).mpr (by rw [mul_comm]; exact this)
      omega
    · rw [List.mem_map]
      refine ⟨∑ i ∈ Finset.range l.length, (j + 1 + i) * c (j + 1 + i),
        mem_sums l (j + 1) c (by omega) (fun i hi ↦ ?_), ?_⟩
      · have := h (i + 1) (by simpa using hi)
        simp only [List.getD_cons_succ] at this
        rw [show j + 1 + i = j + (i + 1) by omega]
        exact this
      · rw [List.length_cons, Finset.sum_range_succ']
        simp only [add_zero]
        rw [mul_comm (c j) j, add_comm]
        congr 1
        exact Finset.sum_congr rfl fun i _ ↦ by rw [show j + 1 + i = j + (i + 1) by omega]

end Field

section Spec

variable {R : Type*} [Field R] [DecidableEq R] [Finite R]

lemma natDegree_of_not_isZero (g : CPoly R) (h : isZero g = false) :
    toPoly g ≠ 0 ∧ (toPoly g).natDegree = (trim g).length - 1 := by
  have h0 : toPoly g ≠ 0 := fun h' ↦ by rw [(isZero_iff g).mpr h'] at h; cases h
  have htr : trim g ≠ [] := fun h' ↦ h0 ((trim_eq_nil_iff g).mp h')
  exact ⟨h0, by rw [length_trim htr]; simp⟩

lemma toPoly_X : toPoly ([0, 1] : CPoly R) = X := by simp [toPoly_cons]

/-- **Correctness of `ddf`.** -/
theorem ddf_spec (p : ℕ) (hp : Nat.card R = p) (f : CPoly R) :
    ∀ (n j : ℕ) (w cur : CPoly R) (l : List ℕ),
      toPoly f ∣ toPoly w - X ^ p ^ j → toPoly cur ∣ toPoly f →
      (∀ π : R[X], Irreducible π → π ∣ toPoly f → j < π.natDegree → π ∣ toPoly cur) →
      ddf p f n w cur = some l →
      l.length = n ∧ ∀ i < n, ∃ h : R[X], h ≠ 0 ∧ h.natDegree = l.getD i 0 ∧
        ∀ π : R[X], Irreducible π → π ∣ toPoly f → π.natDegree = j + 1 + i → π ∣ h
  | 0, j, w, cur, l, _, _, _, h => by
    simp only [ddf, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
  | n + 1, j, w, cur, l, hw, hcur, hinv, h => by
    simp only [ddf] at h
    set w' := powMod f w p with hw'def
    set d := sub w' [0, 1] with hddef
    set g := (egcd cur d).1 with hgdef
    split_ifs at h with hz hc
    obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.mp h
    have hz' : isZero g = false := by simpa using hz
    obtain ⟨hg0, hgdeg⟩ := natDegree_of_not_isZero g hz'
    rw [Bool.and_eq_true] at hc
    have hq1 : toPoly cur = toPoly (divMod cur g).1 * toPoly g := by
      have := divMod_spec cur g
      rw [(isZero_iff _).mp hc.1, add_zero] at this
      exact this
    have hq2 : toPoly d = toPoly (divMod d g).1 * toPoly g := by
      have := divMod_spec d g
      rw [(isZero_iff _).mp hc.2, add_zero] at this
      exact this
    have hbez := egcd_spec cur d
    have hd : toPoly d = toPoly w' - X := by rw [hddef, toPoly_sub, toPoly_X]
    -- `w' ≡ X^{p^{j+1}}`
    have hw1 : toPoly f ∣ toPoly w' - X ^ p ^ (j + 1) := by
      have h1 := powMod_spec f w p
      have h2 : toPoly f ∣ toPoly w ^ p - (X ^ p ^ j) ^ p :=
        hw.trans (sub_dvd_pow_sub_pow _ _ p)
      have := dvd_add h1 h2
      rw [pow_succ, pow_mul]
      convert this using 1; ring
    -- for a factor `π` of `f`: `π ∣ d ↔ π ∣ X^{p^{j+1}} − X`
    have hiff : ∀ π : R[X], π ∣ toPoly f → (π ∣ toPoly d ↔ π ∣ X ^ p ^ (j + 1) - X) := by
      intro π hπ
      have h1 := hπ.trans hw1
      rw [hd]
      constructor
      · intro h2
        have := dvd_sub h2 h1
        convert this using 1; ring
      · intro h2
        have := dvd_add h2 h1
        convert this using 1; ring
    have hcard : ∀ π : R[X], Irreducible π → ∀ k : ℕ,
        π.natDegree ∣ k ↔ π ∣ X ^ p ^ k - X := fun π hπ k ↦ by
      rw [← hp]; exact hπ.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X
    obtain ⟨hlen, hrest⟩ := ddf_spec p hp f n (j + 1) w' (divMod cur g).1 l' hw1
      (Dvd.dvd.trans ⟨toPoly g, hq1⟩ hcur) (fun π hπ hπf hjπ ↦ by
        have h1 := hinv π hπ hπf (by omega)
        rw [hq1] at h1
        rcases hπ.prime.dvd_or_dvd h1 with h2 | h2
        · exact h2
        · exfalso
          have h3 : π ∣ toPoly d := h2.trans ⟨toPoly (divMod d g).1, by rw [hq2, mul_comm]⟩
          have h4 := (hcard π hπ (j + 1)).mpr ((hiff π hπf).mp h3)
          have := Nat.le_of_dvd (by omega) h4
          omega) hl'
    refine ⟨by simp [hlen], fun i hi ↦ ?_⟩
    rcases i with _ | i
    · refine ⟨toPoly g, hg0, by simpa using hgdeg, fun π hπ hπf hdeg ↦ ?_⟩
      have h1 := hinv π hπ hπf (by omega)
      have h2 : π ∣ toPoly d :=
        (hiff π hπf).mpr ((hcard π hπ (j + 1)).mp (by rw [hdeg]))
      rw [← hbez]
      exact dvd_add (Dvd.dvd.mul_left h1 _) (Dvd.dvd.mul_left h2 _)
    · obtain ⟨h', h0, hdeg', hall⟩ := hrest i (by omega)
      refine ⟨h', h0, by simpa using hdeg', fun π hπ hπf hdeg ↦ hall π hπ hπf (by omega)⟩

end Spec

/-! ### From `ℚ[x]` to `𝔽_p[x]` -/

section Rat

open Kron

/-- The possible degrees of the factors of `F` over `ℚ`, read off modulo the prime `p`
(`none` if `p` is not prime, divides the leading coefficient, or `F mod p` is not squarefree). -/
def primeSums (p : ℕ) (F : CPoly ℚ) : Option (List ℕ) :=
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    let f : CPoly (ZMod p) := (F.map Rat.num).map (Int.castRingHom (ZMod p))
    if (trim f).length = F.length ∧ 2 ≤ F.length ∧ (trim (egcd f (deriv f)).1).length = 1 then
      (ddf p f (F.length - 1) [0, 1] f).map (sums 1)
    else none
  else none

lemma toPoly_mapL {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (l : List A) :
    toPoly (l.map φ) = (toPoly l).map φ := by
  induction l with
  | nil => simp
  | cons a l ih => simp [toPoly_cons, ih]

lemma natDegree_toPoly_lt {A : Type*} [CommRing A] (l : List A) :
    (toPoly l).natDegree ≤ l.length - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_toPoly]
  exact List.getD_eq_default _ _ (by omega)

/-- A factor over `ℚ` of an integral polynomial gives an integral factor of the same degree. -/
lemma exists_int_factor {FZ : ℤ[X]} (hF : FZ ≠ 0) {g : ℚ[X]}
    (hg : g ∣ FZ.map (Int.castRingHom ℚ)) :
    ∃ G : ℤ[X], G ∣ FZ ∧ G.natDegree = g.natDegree := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hFm : FZ.map (Int.castRingHom ℚ) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hF
  have hg0 : g ≠ 0 := ne_zero_of_dvd_ne_zero hFm hg
  obtain ⟨b, hb, hG⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) g
  set G0 := IsLocalization.integerNormalization (nonZeroDivisors ℤ) g
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have eG : G0.map (Int.castRingHom ℚ) = C (b : ℚ) * g := by
    change G0.map (algebraMap ℤ ℚ) = _
    rw [hG, ← smul_eq_C_mul]; exact (Int.cast_smul_eq_zsmul ℚ b g).symm
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
  have hG00 : G0 ≠ 0 := fun h ↦ by
    rw [h, Polynomial.map_zero] at eG
    exact mul_ne_zero (C_ne_zero.mpr hbQ) hg0 eG.symm
  have hdeg0 : G0.natDegree = g.natDegree := by
    rw [← natDegree_map_eq_of_injective hinj G0, eG, natDegree_C_mul hbQ]
  refine ⟨G0.primPart, ?_, by rw [natDegree_primPart, hdeg0]⟩
  have h1 : G0.primPart ∣ FZ.primPart := by
    rw [IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ (isPrimitive_primPart G0)]
    have e1 : G0.map (Int.castRingHom ℚ) =
        C ((G0.content : ℤ) : ℚ) * G0.primPart.map (Int.castRingHom ℚ) := by
      conv_lhs => rw [G0.eq_C_content_mul_primPart]
      simp
    have e2 : FZ.map (Int.castRingHom ℚ) =
        C ((FZ.content : ℤ) : ℚ) * FZ.primPart.map (Int.castRingHom ℚ) := by
      conv_lhs => rw [FZ.eq_C_content_mul_primPart]
      simp
    have hc1 : ((G0.content : ℤ) : ℚ) ≠ 0 := by
      exact_mod_cast (content_eq_zero_iff.not.mpr hG00)
    have hc2 : ((FZ.content : ℤ) : ℚ) ≠ 0 := by
      exact_mod_cast (content_eq_zero_iff.not.mpr hF)
    have h3 : G0.primPart.map (Int.castRingHom ℚ) ∣ g :=
      ⟨C (((G0.content : ℤ) : ℚ) * (b : ℚ)⁻¹), by
        have : g = C ((b : ℚ)⁻¹) * G0.map (Int.castRingHom ℚ) := by
          rw [eG, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hbQ, C_1, one_mul]
        rw [this, e1, C_mul]; ring⟩
    have h4 : G0.primPart.map (Int.castRingHom ℚ) ∣ FZ.map (Int.castRingHom ℚ) := h3.trans hg
    rw [e2] at h4
    exact (IsUnit.dvd_mul_left (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc2))).mp h4
  exact h1.trans (primPart_dvd FZ)

/-- **Soundness of `primeSums`**: the degree of every factor of `F` over `ℚ` is in the list. -/
theorem primeSums_sound (p : ℕ) (F : CPoly ℚ) (hint : ∀ q ∈ F, q.den = 1) (S : List ℕ)
    (h : primeSums p F = some S) (g : ℚ[X]) (hg : g ∣ toPoly F) : g.natDegree ∈ S := by
  unfold primeSums at h
  by_cases hp : p.Prime
  swap
  · rw [dif_neg hp] at h; cases h
  rw [dif_pos hp] at h
  haveI : Fact p.Prime := ⟨hp⟩
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨hlen, h2, hsqc⟩ := hc
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp h
  set f : CPoly (ZMod p) := (F.map Rat.num).map (Int.castRingHom (ZMod p)) with hfdef
  have hfpoly : toPoly f = (polyZ F).map (Int.castRingHom (ZMod p)) := toPoly_mapL _ _
  have htr : trim f ≠ [] := fun h0 ↦ by rw [h0] at hlen; simp at hlen; omega
  have hf0 : toPoly f ≠ 0 := fun h0 ↦ htr ((trim_eq_nil_iff f).mpr h0)
  have hfdeg : (toPoly f).natDegree = F.length - 1 := by
    have := length_trim htr
    omega
  have hFZ0 : polyZ F ≠ 0 := fun h0 ↦ hf0 (by rw [hfpoly, h0, Polynomial.map_zero])
  -- squarefree modulo `p`
  have hsq : Squarefree (toPoly f) := by
    have hb := egcd_spec f (deriv f)
    set e := (egcd f (deriv f)).1
    have he : trim e ≠ [] := fun h0 ↦ by rw [h0] at hsqc; simp at hsqc
    have hed : (toPoly e).natDegree = 0 := by have := length_trim he; omega
    have he0 : toPoly e ≠ 0 := fun h0 ↦ he ((trim_eq_nil_iff e).mpr h0)
    have hu : IsUnit (toPoly e) := by
      rw [eq_C_of_natDegree_eq_zero hed] at he0 ⊢
      exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (C_ne_zero.mp he0))
    have hcop : IsCoprime (toPoly f) (derivative (toPoly f)) := by
      obtain ⟨u, hu'⟩ := hu.exists_left_inv
      refine ⟨u * toPoly (egcd f (deriv f)).2.1, u * toPoly (egcd f (deriv f)).2.2, ?_⟩
      rw [toPoly_deriv] at hb
      rw [mul_assoc, mul_assoc, ← mul_add, hb, hu']
    exact Separable.squarefree hcop
  -- an integral factor of the same degree, and its reduction
  rw [← polyZ_map F hint] at hg
  obtain ⟨G, ⟨H, hGH⟩, hGdeg⟩ := exists_int_factor hFZ0 hg
  set φ := Int.castRingHom (ZMod p)
  have hprod : toPoly f = G.map φ * H.map φ := by rw [hfpoly, hGH, Polynomial.map_mul]
  have hG0 : G.map φ ≠ 0 := fun h0 ↦ hf0 (by rw [hprod, h0, zero_mul])
  have hH0 : H.map φ ≠ 0 := fun h0 ↦ hf0 (by rw [hprod, h0, mul_zero])
  have hGd : (G.map φ).natDegree = G.natDegree := by
    have h1 := natDegree_map_le (f := φ) (p := G)
    have h3 := natDegree_map_le (f := φ) (p := H)
    have h4 : (toPoly f).natDegree = (G.map φ).natDegree + (H.map φ).natDegree := by
      rw [hprod, natDegree_mul hG0 hH0]
    have hG0' : G ≠ 0 := fun h0 ↦ hG0 (by rw [h0, Polynomial.map_zero])
    have hH0' : H ≠ 0 := fun h0 ↦ hH0 (by rw [h0, Polynomial.map_zero])
    have h5 : (polyZ F).natDegree = G.natDegree + H.natDegree := by
      rw [hGH, natDegree_mul hG0' hH0']
    have h6 : (polyZ F).natDegree ≤ F.length - 1 := by
      have := natDegree_toPoly_lt (F.map Rat.num)
      simpa [polyZ] using this
    omega
  have hcard : Nat.card (ZMod p) = p := by simp
  obtain ⟨hll, hall⟩ := ddf_spec p hcard f (F.length - 1) 0 [0, 1] f l
    (by rw [toPoly_X, pow_zero, pow_one, sub_self]; exact dvd_zero _) dvd_rfl
    (fun π _ hπ _ ↦ hπ) hl
  obtain ⟨c, hc1, hc2⟩ := DegCount.natDegree_of_dvd_sq hf0 hsq
    (⟨H.map φ, hprod⟩ : G.map φ ∣ toPoly f) (F.length - 1) (le_of_eq hfdeg)
    (fun d ↦ l.getD (d - 1) 0) (fun d hd1 hdn ↦ by
      obtain ⟨h', h0, hdeg, hπ⟩ := hall (d - 1) (by omega)
      exact ⟨h', h0, hdeg, fun π hπi hπf hπd ↦ hπ π hπi hπf (by omega)⟩)
  rw [← hGdeg, ← hGd, hc2]
  have hsum : ∑ d ∈ Finset.Icc 1 (F.length - 1), d * c d =
      ∑ i ∈ Finset.range l.length, (1 + i) * c (1 + i) := by
    rw [hll, Finset.range_eq_Ico, Finset.sum_Ico_add (fun d ↦ d * c d) 0 (F.length - 1) 1]
    exact Finset.sum_congr (by ext x; simp [Finset.mem_Icc, Finset.mem_Ico]) fun _ _ ↦ rfl
  rw [hsum]
  refine mem_sums l 1 c le_rfl fun i hi ↦ ?_
  have := hc1 (1 + i) (by omega) (by omega)
  simpa using this

/-- The primes tried. -/
def certPrimes : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

/-- The lists of possible factor degrees of `F`, one per usable prime. -/
def degSets (F : CPoly ℚ) : List (List ℕ) :=
  if (trim F).all (fun q ↦ q.den == 1) then certPrimes.filterMap fun p ↦ primeSums p (trim F)
  else []

/-- Some prime excludes the degree `e`. -/
def degExcluded (Ss : List (List ℕ)) (e : ℕ) : Bool := Ss.any fun S ↦ !S.contains e

/-- **No factor of an excluded degree.** -/
theorem degExcluded_sound (F : CPoly ℚ) (e : ℕ) (h : degExcluded (degSets F) e = true) (g : ℚ[X])
    (hg : g ∣ toPoly F) : g.natDegree ≠ e := by
  unfold degExcluded degSets at h
  split_ifs at h with hint
  · obtain ⟨S, hS, hne⟩ := List.any_eq_true.mp h
    obtain ⟨p, -, hp⟩ := List.mem_filterMap.mp hS
    have hint' : ∀ q ∈ trim F, q.den = 1 := fun q hq ↦ by
      simpa using (List.all_eq_true.mp hint) q hq
    have hmem := primeSums_sound p (trim F) hint' S hp g (by rw [toPoly_trim]; exact hg)
    intro he
    rw [he] at hmem
    simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hne
    exact hne hmem
  · simp at h

end Rat

end DegCert

end CPoly
