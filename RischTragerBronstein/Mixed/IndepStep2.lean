import RischTragerBronstein.Mixed.IndepStep

/-!
# Completeness of one step of the recursive independence certificate

**`stepI_complete`** / **`stepI1_complete`**: under Manin's kernel theorem over `K` and with a
complete recursive check over `K` (`RecC`, `RecC1`), independent points (a point of infinite order)
on a short model over `K(X)` pass the step for all large `kmax`. The case split is
`jConstB` (non-constant `j` ⇒ Manin), then `const_j_classify` (`IsoNT` ⇒ heights `certQ`;
constant up to scaling ⇒ `csData`, `descPt`, recursion).
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine CPoly

namespace FFHeight

section Props

variable {K' : Type*} [Field K'] [CharZero K']

open scoped Classical

/-- **Completeness of a recursive two-point check over `K`.** -/
def RecC (rec : ℕ → K' → K' → Option (K' × K') → Option (K' × K') → Bool) : Prop :=
  ∀ (a b : K') (p q : Option (K' × K')) (P Q : (shortF a b).toAffine.Point),
    4 * a ^ 3 + 27 * b ^ 2 ≠ 0 → RelC a b p P → RelC a b q Q →
    (∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) → ∃ K0, ∀ k, K0 ≤ k → rec k a b p q = true

/-- **Completeness of a recursive one-point check over `K`.** -/
def RecC1 (rec1 : ℕ → K' → K' → Option (K' × K') → Bool) : Prop :=
  ∀ (a b : K') (p : Option (K' × K')) (P : (shortF a b).toAffine.Point),
    4 * a ^ 3 + 27 * b ^ 2 ≠ 0 → RelC a b p P →
    (∀ n : ℤ, n • P = 0 → n = 0) → ∃ K0, ∀ k, K0 ≤ k → rec1 k a b p = true

lemma indep_ΦCS' {A B : K'[X]} {u : RatFunc K'} {a b : K'} (hu : u ≠ 0)
    (hA : algebraMap K'[X] (RatFunc K') A = u ^ 4 * algebraMap K' (RatFunc K') a)
    (hB : algebraMap K'[X] (RatFunc K') B = u ^ 6 * algebraMap K' (RatFunc K') b)
    (P' Q' : (shortF a b).toAffine.Point)
    (h : ∀ m n : ℤ, m • ΦCS hu hA hB P' = n • ΦCS hu hA hB Q' → m = 0 ∧ n = 0) :
    ∀ m n : ℤ, m • P' = n • Q' → m = 0 ∧ n = 0 := (indep_iff_ΦCS hu hA hB P' Q').mp h

lemma nt_ΦCS' {A B : K'[X]} {u : RatFunc K'} {a b : K'} (hu : u ≠ 0)
    (hA : algebraMap K'[X] (RatFunc K') A = u ^ 4 * algebraMap K' (RatFunc K') a)
    (hB : algebraMap K'[X] (RatFunc K') B = u ^ 6 * algebraMap K' (RatFunc K') b)
    (P' : (shortF a b).toAffine.Point) (h : ∀ n : ℤ, n • ΦCS hu hA hB P' = 0 → n = 0) :
    ∀ n : ℤ, n • P' = 0 → n = 0 := fun n hn ↦ h n (by rw [← map_zsmul, hn, map_zero])

end Props

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

open scoped Classical

/-- **Completeness of a step.** -/
theorem stepI_complete (hM : Manin.MKT K) {isRat : K → Bool}
    (hRat : ∀ x, isRat x = true ↔ ∃ q : ℚ, x = q)
    {rec : ℕ → K → K → Option (K × K) → Option (K × K) → Bool} (hrec : RecC rec)
    (Ac Bc : CPoly K) (oD oZ : PtC K) (hΔ : 4 * toPoly Ac ^ 3 + 27 * toPoly Bc ^ 2 ≠ 0)
    (P Q : (shortW (toPoly Ac) (toPoly Bc)).toAffine.Point) (hP : Rel _ _ oD P) (hQ : Rel _ _ oZ Q)
    (hind : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0) :
    ∃ K0, ∀ kmax, K0 ≤ kmax → stepI isRat rec kmax Ac Bc oD oZ = true := by
  cases hj : jConstB Ac Bc
  · have hβ := bt_ne_of_jConstB hj hΔ
    rcases Manin.manCertP_exists hM hRat Ac Bc hΔ hβ oD oZ P Q hP hQ hind with h | h
    · exact ⟨0, fun k _ ↦ by simp [stepI, h]⟩
    · exact ⟨0, fun k _ ↦ by simp [stepI, h]⟩
  rcases const_j_classify _ _ hΔ (jConstB_true hj) with hiso | hcs
  · obtain ⟨k, hk⟩ := certQ_exists_iso Ac Bc _ _ rfl rfl hΔ hiso oD oZ P Q hP hQ hind
    refine ⟨k + 1, fun kmax hkm ↦ ?_⟩
    have : (List.range kmax).any (fun k ↦ certQ Ac (max (cdeg Ac) (cdeg Bc)) k oD oZ) = true :=
      List.any_eq_true.mpr ⟨k, List.mem_range.mpr (by omega), by rw [cdeg_spec, cdeg_spec]; exact hk⟩
    simp [stepI, this]
  · obtain ⟨⟨v, a, b⟩, hcsd⟩ := Option.isSome_iff_exists.mp (csData_complete hΔ hcs)
    obtain ⟨hu, hA, hB, hv, hΔ'⟩ := cs_facts hcsd hΔ
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (descPt_complete v hv hA hB hΔ' hu oD P hP)
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (descPt_complete v hv hA hB hΔ' hu oZ Q hQ)
    obtain ⟨P', hP', rfl⟩ := descPt_sound v hv hA hB hΔ' hu oD p hp P hP
    obtain ⟨Q', hQ', rfl⟩ := descPt_sound v hv hA hB hΔ' hu oZ q hq Q hQ
    obtain ⟨K0, hK⟩ := hrec a b p q P' Q' hΔ' hP' hQ' (indep_ΦCS' hu hA hB P' Q' hind)
    refine ⟨K0, fun kmax hkm ↦ ?_⟩
    have hr := hK kmax hkm
    unfold stepI
    rw [hcsd]
    simp only [hp, hq, hr, Bool.or_true]

/-- **Completeness of a one-point step.** -/
theorem stepI1_complete (hM : Manin.MKT K)
    {rec1 : ℕ → K → K → Option (K × K) → Bool} (hrec : RecC1 rec1)
    (Ac Bc : CPoly K) (oP : PtC K) (hΔ : 4 * toPoly Ac ^ 3 + 27 * toPoly Bc ^ 2 ≠ 0)
    (P : (shortW (toPoly Ac) (toPoly Bc)).toAffine.Point) (hP : Rel _ _ oP P)
    (hnt : ∀ n : ℤ, n • P = 0 → n = 0) :
    ∃ K0, ∀ kmax, K0 ≤ kmax → stepI1 rec1 kmax Ac Bc oP = true := by
  cases hj : jConstB Ac Bc
  · have hβ := bt_ne_of_jConstB hj hΔ
    have h := Manin.manCert1P_exists hM Ac Bc hΔ hβ oP P hP hnt
    exact ⟨0, fun k _ ↦ by simp [stepI1, h]⟩
  rcases const_j_classify _ _ hΔ (jConstB_true hj) with hiso | hcs
  · obtain ⟨k, hk⟩ := certQ1_exists_iso Ac _ _ rfl hΔ hiso oP P hP hnt
    refine ⟨k + 1, fun kmax hkm ↦ ?_⟩
    have : (List.range kmax).any (fun k ↦ certQ1 Ac (max (cdeg Ac) (cdeg Bc)) k oP) = true :=
      List.any_eq_true.mpr ⟨k, List.mem_range.mpr (by omega), by rw [cdeg_spec, cdeg_spec]; exact hk⟩
    simp [stepI1, this]
  · obtain ⟨⟨v, a, b⟩, hcsd⟩ := Option.isSome_iff_exists.mp (csData_complete hΔ hcs)
    obtain ⟨hu, hA, hB, hv, hΔ'⟩ := cs_facts hcsd hΔ
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (descPt_complete v hv hA hB hΔ' hu oP P hP)
    obtain ⟨P', hP', rfl⟩ := descPt_sound v hv hA hB hΔ' hu oP p hp P hP
    obtain ⟨K0, hK⟩ := hrec a b p P' hΔ' hP' (nt_ΦCS' hu hA hB P' hnt)
    refine ⟨K0, fun kmax hkm ↦ ?_⟩
    have hr := hK kmax hkm
    unfold stepI1
    rw [hcsd]
    simp only [hp, hr, Bool.or_true]

end FFHeight
