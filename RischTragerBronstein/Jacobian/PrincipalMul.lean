import RischTragerBronstein.Jacobian.GlobalTorsion

/-!
# Principal multiples of a divisor

For an effective divisor `Γ = D⁺ + σ D⁻` (distinct abscissae) of a degree-zero divisor `D`,
`PrincipalMul f g Γ n` says that `n D` is principal: some non-zero `ψ` of pole order
`≤ n deg Γ` vanishes on `n Γ`. The set of such `n` is closed under addition (`PrincipalMul.add`,
products of functions) and subtraction (`PrincipalMul.sub`, product with the conjugate and
division by `wpoly (m Γ)`), hence under `gcd` (`PrincipalMul.gcd`).
-/

open Polynomial

namespace Jac

variable {K : Type*} [Field K]

/-- `n D` is principal. -/
def PrincipalMul (f : K[X]) (g : ℕ) (Γ : EDiv K) (n : ℕ) : Prop :=
  ∃ ψ : K[X] × K[X], ψ ≠ (0, 0) ∧ PoleLE g ψ (n * edeg Γ) ∧ Vanishes f ψ (escale n Γ)

/-- Splitting off the factor of one point from `wpoly`. -/
lemma wpoly_split {Γ : EDiv K} (hnd : (Γ.map Prod.fst).Nodup) {q : K × K × ℕ} (hq : q ∈ Γ) :
    ∃ w' : K[X], wpoly Γ = (X - C q.1) ^ q.2.2 * w' ∧ w'.eval q.1 ≠ 0 := by
  induction Γ with
  | nil => simp at hq
  | cons r Γ ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    have hw : wpoly (r :: Γ) = (X - C r.1) ^ r.2.2 * wpoly Γ := by
      simp [wpoly]
    rcases List.mem_cons.mp hq with rfl | hq'
    · refine ⟨wpoly Γ, hw, eval_wpoly_ne_zero fun q' hq' he ↦ hnd.1 ?_⟩
      rw [← he]; exact List.mem_map_of_mem hq'
    · obtain ⟨w0, h1, h2⟩ := ih hnd.2 hq'
      refine ⟨(X - C r.1) ^ r.2.2 * w0, by rw [hw, h1]; ring, ?_⟩
      rw [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
      refine mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr fun he ↦ hnd.1 ?_)) h2
      rw [← he]; exact List.mem_map_of_mem hq'

lemma escale_mem {n : ℕ} {Γ : EDiv K} {q : K × K × ℕ} (hq : q ∈ escale n Γ) :
    ∃ q' ∈ Γ, q = (q'.1, q'.2.1, n * q'.2.2) := by
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
  exact ⟨q', hq', rfl⟩

lemma nodup_escale {n : ℕ} {Γ : EDiv K} (h : (Γ.map Prod.fst).Nodup) :
    ((escale n Γ).map Prod.fst).Nodup := by
  simpa [escale, Function.comp_def] using h

lemma OnCurve.escale {f : K[X]} {n : ℕ} {Γ : EDiv K} (h : OnCurve f Γ) :
    OnCurve f (escale n Γ) := by
  intro q hq
  obtain ⟨q', hq', rfl⟩ := escale_mem hq
  exact h q' hq'

variable {f : K[X]} {g : ℕ} {Γ : EDiv K}

lemma PrincipalMul.zero (hon : OnCurve f Γ) : PrincipalMul f g Γ 0 := by
  refine ⟨(1, 0), by simp, ⟨by simp, Or.inl rfl⟩, fun q hq ↦ ?_⟩
  obtain ⟨q', hq', rfl⟩ := escale_mem hq
  simpa using VanishAt.zero (a := 1) (b := 0) (hon q' hq').1 (hon q' hq').2

/-- **Sums of principal multiples.** -/
theorem PrincipalMul.add (hf : f.natDegree = 2 * g + 1) (hon : OnCurve f Γ) {n m : ℕ}
    (hn : PrincipalMul f g Γ n) (hm : PrincipalMul f g Γ m) : PrincipalMul f g Γ (n + m) := by
  obtain ⟨ψ, hψ0, hψp, hψv⟩ := hn
  obtain ⟨φ, hφ0, hφp, hφv⟩ := hm
  refine ⟨hmul f ψ φ, hmul_ne_zero ⟨g, by omega⟩ hψ0 hφ0, ?_, fun q hq ↦ ?_⟩
  · rw [add_mul]; exact PoleLE.hmul hf.le hψp hφp
  · obtain ⟨q', hq', rfl⟩ := escale_mem hq
    have h1 := hψv (q'.1, q'.2.1, n * q'.2.2) (List.mem_map_of_mem hq')
    have h2 := hφv (q'.1, q'.2.1, m * q'.2.2) (List.mem_map_of_mem hq')
    have := VanishAt.hmul (hon q' hq').1 (hon q' hq').2 h1 h2
    rwa [← add_mul] at this

/-- **Differences of principal multiples.** -/
theorem PrincipalMul.sub (hf : f.natDegree = 2 * g + 1) (hon : OnCurve f Γ)
    (hnd : (Γ.map Prod.fst).Nodup) {n m : ℕ} (hmn : m ≤ n)
    (hn : PrincipalMul f g Γ n) (hm : PrincipalMul f g Γ m) : PrincipalMul f g Γ (n - m) := by
  obtain ⟨ψ, hψ0, hψp, hψv⟩ := hn
  obtain ⟨φ, hφ0, hφp, hφv⟩ := hm
  set Φ := hmul f ψ (hconj φ)
  have hodd : Odd f.natDegree := ⟨g, by omega⟩
  have hΦ0 : Φ ≠ (0, 0) := hmul_ne_zero hodd hψ0 (by
    intro h; apply hφ0; simp only [hconj, Prod.mk.injEq, neg_eq_zero] at h; exact Prod.ext h.1 h.2)
  -- `Φ` vanishes on `m Γ` and on `σ (m Γ)`
  have hv1 : Vanishes f Φ (escale m Γ) := fun q hq ↦ by
    obtain ⟨q', hq', rfl⟩ := escale_mem hq
    have h1 := (hψv (q'.1, q'.2.1, n * q'.2.2) (List.mem_map_of_mem hq')).mono
      (Nat.mul_le_mul_right _ hmn)
    have := VanishAt.hmul (φ := hconj φ) (k' := 0) (hon q' hq').1 (hon q' hq').2 h1
      (VanishAt.zero (hon q' hq').1 (hon q' hq').2)
    simpa using this
  have hv2 : Vanishes f Φ (econj (escale m Γ)) := fun q hq ↦ by
    obtain ⟨q1, hq1, rfl⟩ := List.mem_map.mp hq
    obtain ⟨q', hq', rfl⟩ := escale_mem hq1
    have hon' : IsUnit (2 * -q'.2.1) ∧ (-q'.2.1) ^ 2 = f.eval q'.1 :=
      ⟨by rw [mul_neg]; exact (hon q' hq').1.neg, by rw [neg_sq]; exact (hon q' hq').2⟩
    have h2 := (hφv (q'.1, q'.2.1, m * q'.2.2) (List.mem_map_of_mem hq')).hconj
    have := VanishAt.hmul (ψ := ψ) (φ := hconj φ) (k := 0) hon'.1 hon'.2
      (VanishAt.zero hon'.1 hon'.2) h2
    rwa [zero_add] at this
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ := wpoly_dvd_of_vanish_both (nodup_escale hnd)
    (OnCurve.escale hon) hv1 hv2
  have hΦe : Φ = hsmul (wpoly (escale m Γ)) (A, B) := Prod.ext hA hB
  have hw0 : wpoly (escale m Γ) ≠ 0 := (wpoly_monic _).ne_zero
  refine ⟨(A, B), ?_, ?_, fun q hq ↦ ?_⟩
  · intro h; apply hΦ0; rw [hΦe, h]; simp [hsmul]
  · have hΦp : PoleLE g Φ (n * edeg Γ + m * edeg Γ) := PoleLE.hmul hf.le hψp hφp.hconj
    have := PoleLE.of_hsmul hw0 (hΦe ▸ hΦp)
    rw [natDegree_wpoly, edeg_escale] at this
    have e : n * edeg Γ + m * edeg Γ - 2 * (m * edeg Γ) = (n - m) * edeg Γ := by
      rw [Nat.sub_mul]
      have : m * edeg Γ ≤ n * edeg Γ := Nat.mul_le_mul_right _ hmn
      omega
    rwa [e] at this
  · obtain ⟨q', hq', rfl⟩ := escale_mem hq
    -- split the factor of `q'` off `wpoly (m Γ)`
    obtain ⟨w', hw', hw'0⟩ := wpoly_split (nodup_escale (n := m) hnd)
      (List.mem_map_of_mem (f := fun q ↦ (q.1, q.2.1, m * q.2.2)) hq')
    simp only at hw' hw'0
    have hΦq := (hψv (q'.1, q'.2.1, n * q'.2.2) (List.mem_map_of_mem hq'))
    have hΦq' := VanishAt.hmul (φ := hconj φ) (k' := 0) (hon q' hq').1 (hon q' hq').2 hΦq
      (VanishAt.zero (hon q' hq').1 (hon q' hq').2)
    rw [add_zero] at hΦq'
    have e1 : Φ = hsmul ((X - C q'.1) ^ (m * q'.2.2)) (hsmul w' (A, B)) := by
      rw [hΦe, hw']; simp only [hsmul]; exact Prod.ext (by ring) (by ring)
    have e2 : n * q'.2.2 = (n - m) * q'.2.2 + m * q'.2.2 := by
      rw [← add_mul, Nat.sub_add_cancel hmn]
    rw [e2] at hΦq'
    have h3 := VanishAt.of_hsmul_pow (e := m * q'.2.2) (ψ := hsmul w' (A, B)) (by
      rw [← e1]; exact hΦq')
    exact VanishAt.of_hsmul_unit (IsUnit.mk0 _ hw'0) h3

/-- **Principal multiples are closed under `gcd`.** -/
theorem PrincipalMul.gcd (hf : f.natDegree = 2 * g + 1) (hon : OnCurve f Γ)
    (hnd : (Γ.map Prod.fst).Nodup) : ∀ {n m : ℕ}, PrincipalMul f g Γ n →
      PrincipalMul f g Γ m → PrincipalMul f g Γ (Nat.gcd n m) := by
  intro n m
  induction n using Nat.strong_induction_on generalizing m with
  | _ n ih =>
    intro hn hm
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rwa [Nat.gcd_zero_left]
    · -- `gcd n m = gcd (m % n) n`
      rw [Nat.gcd_rec]
      apply ih (m % n) (Nat.mod_lt _ hpos) _ hn
      -- `m % n = m − n * (m / n)`
      have hmul : ∀ k, PrincipalMul f g Γ (n * k) := by
        intro k
        induction k with
        | zero => rw [mul_zero]; exact PrincipalMul.zero hon
        | succ k ihk => rw [Nat.mul_succ]; exact PrincipalMul.add hf hon ihk hn
      have := PrincipalMul.sub hf hon hnd (Nat.mul_div_le m n) hm (hmul (m / n))
      rwa [← Nat.mod_eq_sub_mul_div] at this

/-- Multiples of principal multiples. -/
theorem PrincipalMul.mul (hf : f.natDegree = 2 * g + 1) (hon : OnCurve f Γ) {n : ℕ}
    (hn : PrincipalMul f g Γ n) (k : ℕ) : PrincipalMul f g Γ (n * k) := by
  induction k with
  | zero => rw [mul_zero]; exact PrincipalMul.zero hon
  | succ k ihk => rw [Nat.mul_succ]; exact PrincipalMul.add hf hon ihk hn

/-- Divisibility: if `n D` is principal and `n ∣ m` then `m D` is principal. -/
theorem PrincipalMul.of_dvd (hf : f.natDegree = 2 * g + 1) (hon : OnCurve f Γ) {n m : ℕ}
    (hn : PrincipalMul f g Γ n) (hnm : n ∣ m) : PrincipalMul f g Γ m := by
  obtain ⟨k, rfl⟩ := hnm; exact hn.mul hf hon k

end Jac
