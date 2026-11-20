import RischTragerBronstein.Mixed.IndepDesc
import RischTragerBronstein.Mixed.JTest
import RischTragerBronstein.Mixed.ManinOne
import RischTragerBronstein.Mixed.KXRepS2
import RischTragerBronstein.Mixed.EllIsoCert1

/-!
# One step of the recursive independence certificate

For a short model `y² = x³ + A x + B` over `K(X)` (`A, B ∈ K[X]` given as codes) and point codes:
`stepI` tries the Manin certificates (`manCertP`, `manCertRP`), the height certificate `certQ`
(levels `< kmax`), and finally the **descent** (curve constant up to scaling: `csData`, `descPt`)
followed by a recursive check `rec` over `K`. `stepI1` is the one-point (infinite order) variant.

* **`stepI_sound`** / **`stepI1_sound`**: given a sound `rec`, a passing step proves independence
  (resp. infinite order).
* **`stepI_complete`** / **`stepI1_complete`**: given Manin's kernel theorem over `K` and a complete
  `rec`, independent points (resp. a point of infinite order) pass for all large `kmax` — the
  three cases: `j` non-constant (Manin), `IsoNT` (heights), constant up to scaling (descent).
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine CPoly

namespace FFHeight

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]

local notation "ι" => algebraMap K[X] (RatFunc K)
local notation "κ" => algebraMap K (RatFunc K)

/-- **One step, two points.** -/
def stepI (isRat : K → Bool) (rec : ℕ → K → K → Option (K × K) → Option (K × K) → Bool)
    (kmax : ℕ) (Ac Bc : CPoly K) (oD oZ : PtC K) : Bool :=
  Differential.SuperData.manCertP Ac Bc oD oZ ||
  Differential.SuperData.manCertRP Ac Bc isRat oD oZ ||
  (List.range kmax).any (fun k ↦ certQ Ac (max (cdeg Ac) (cdeg Bc)) k oD oZ) ||
  match csData Ac Bc with
  | some (v, a, b) =>
    match descPt v oD, descPt v oZ with
    | some p, some q => rec kmax a b p q
    | _, _ => false
  | none => false

/-- **One step, one point.** -/
def stepI1 (rec1 : ℕ → K → K → Option (K × K) → Bool) (kmax : ℕ) (Ac Bc : CPoly K) (oP : PtC K) :
    Bool :=
  Manin.manCert1P Ac Bc oP ||
  (List.range kmax).any (fun k ↦ certQ1 Ac (max (cdeg Ac) (cdeg Bc)) k oP) ||
  match csData Ac Bc with
  | some (v, a, b) =>
    match descPt v oP with
    | some p => rec1 kmax a b p
    | none => false
  | none => false

section Props

variable {K' : Type*} [Field K'] [CharZero K']

open scoped Classical

/-- Independence of two constant-coded points on `E_{a,b}(K)` (classical group structure, as for
`ΦCS`). -/
def IndC (a b : K') (p q : Option (K' × K')) : Prop :=
  ∀ P Q : (shortF a b).toAffine.Point, RelC a b p P →
    RelC a b q Q → ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0

/-- Infinite order of a constant-coded point on `E_{a,b}(K)`. -/
def NTC (a b : K') (p : Option (K' × K')) : Prop :=
  ∀ P : (shortF a b).toAffine.Point, RelC a b p P →
    ∀ n : ℤ, n • P = 0 → n = 0

/-- Infinite order transfers along `ΦCS`. -/
lemma nt_ΦCS {A B : K'[X]} {u : RatFunc K'} {a b : K'} (hu : u ≠ 0)
    (hA : algebraMap K'[X] (RatFunc K') A = u ^ 4 * algebraMap K' (RatFunc K') a)
    (hB : algebraMap K'[X] (RatFunc K') B = u ^ 6 * algebraMap K' (RatFunc K') b)
    (P' : (shortF a b).toAffine.Point) (h : ∀ n : ℤ, n • P' = 0 → n = 0) :
    ∀ n : ℤ, n • ΦCS hu hA hB P' = 0 → n = 0 := fun n hn ↦
  h n (ΦCS_injective hu hA hB (by rw [map_zsmul, hn, map_zero]))

end Props

open scoped Classical

/-- Data of a passing descent. -/
lemma cs_facts {Ac Bc : CPoly K} {v : CPoly K} {a b : K} (h : csData Ac Bc = some (v, a, b))
    (hΔ : 4 * toPoly Ac ^ 3 + 27 * toPoly Bc ^ 2 ≠ 0) :
    ∃ (hu : ι (toPoly v) ≠ 0) (hA : ι (toPoly Ac) = ι (toPoly v) ^ 4 * κ a)
      (hB : ι (toPoly Bc) = ι (toPoly v) ^ 6 * κ b), toPoly v ≠ 0 ∧ 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 := by
  obtain ⟨hv, hA, hB⟩ := csData_sound h
  have hu : ι (toPoly v) ≠ 0 := Fr.ι_ne hv
  have hA' : ι (toPoly Ac) = ι (toPoly v) ^ 4 * κ a := by
    rw [hA, map_mul, ιC, map_pow]; ring
  have hB' : ι (toPoly Bc) = ι (toPoly v) ^ 6 * κ b := by
    rw [hB, map_mul, ιC, map_pow]; ring
  exact ⟨hu, hA', hB', hv, const_scale_disc hu hA' hB' hΔ⟩

/-- **Soundness of a step.** -/
theorem stepI_sound {isRat : K → Bool} (hRat : ∀ q : ℚ, isRat (q : K) = true)
    {rec : ℕ → K → K → Option (K × K) → Option (K × K) → Bool}
    (hrec : ∀ k a b p q, rec k a b p q = true → 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 → IndC a b p q)
    (kmax : ℕ) (Ac Bc : CPoly K) (oD oZ : PtC K)
    (hΔ : 4 * toPoly Ac ^ 3 + 27 * toPoly Bc ^ 2 ≠ 0)
    (P Q : (shortW (toPoly Ac) (toPoly Bc)).toAffine.Point) (hP : Rel _ _ oD P) (hQ : Rel _ _ oZ Q)
    (h : stepI isRat rec kmax Ac Bc oD oZ = true) : ∀ m n : ℤ, m • P = n • Q → m = 0 ∧ n = 0 := by
  unfold stepI at h
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range] at h
  rcases h with ((h | h) | ⟨k, -, h⟩) | h
  · exact Differential.SuperData.indep_of_manCertP Ac Bc oD oZ P Q hP hQ h
  · exact Differential.SuperData.indep_of_manCertRP Ac Bc hRat oD oZ P Q hP hQ h
  · rw [cdeg_spec, cdeg_spec] at h
    exact indep_of_certQ Ac Bc _ _ rfl hΔ k oD oZ P Q hP hQ h
  · split at h
    · rename_i v a b hcs
      obtain ⟨hu, hA, hB, hv, hΔ'⟩ := cs_facts hcs hΔ
      split at h
      · rename_i p q hp hq
        obtain ⟨P', hP', rfl⟩ := descPt_sound v hv hA hB hΔ' hu oD p hp P hP
        obtain ⟨Q', hQ', rfl⟩ := descPt_sound v hv hA hB hΔ' hu oZ q hq Q hQ
        exact (indep_iff_ΦCS hu hA hB P' Q').mpr (hrec _ a b p q h hΔ' P' Q' hP' hQ')
      · exact absurd h (by decide)
    · exact absurd h (by decide)

/-- **Soundness of a one-point step.** -/
theorem stepI1_sound {rec1 : ℕ → K → K → Option (K × K) → Bool}
    (hrec : ∀ k a b p, rec1 k a b p = true → 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 → NTC a b p)
    (kmax : ℕ) (Ac Bc : CPoly K) (oP : PtC K)
    (hΔ : 4 * toPoly Ac ^ 3 + 27 * toPoly Bc ^ 2 ≠ 0)
    (P : (shortW (toPoly Ac) (toPoly Bc)).toAffine.Point) (hP : Rel _ _ oP P)
    (h : stepI1 rec1 kmax Ac Bc oP = true) : ∀ n : ℤ, n • P = 0 → n = 0 := by
  unfold stepI1 at h
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range] at h
  rcases h with (h | ⟨k, -, h⟩) | h
  · exact Manin.nontors_of_manCert1P Ac Bc oP P hP h
  · rw [cdeg_spec, cdeg_spec] at h
    exact nontors_of_certQ1 Ac _ _ rfl hΔ k oP P hP h
  · split at h
    · rename_i v a b hcs
      obtain ⟨hu, hA, hB, hv, hΔ'⟩ := cs_facts hcs hΔ
      split at h
      · rename_i p hp
        obtain ⟨P', hP', rfl⟩ := descPt_sound v hv hA hB hΔ' hu oP p hp P hP
        exact nt_ΦCS hu hA hB P' (hrec _ a b p h hΔ' P' hP')
      · exact absurd h (by decide)
    · exact absurd h (by decide)

end FFHeight
