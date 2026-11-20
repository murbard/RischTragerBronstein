import RischTragerBronstein.Mixed.KXMWDecide
import RischTragerBronstein.Mixed.KXCertBridgeK
import RischTragerBronstein.Mixed.KXQuadLift

/-!
# The Mordell–Weil certificate search over `ℚ(√d)`

`kxDecideMWQ0`: like `kxDecideMW0`, and when the rational search fails, the search over a quadratic
field `k₀ = ℚ(√d)` (Mathlib's computable `QuadraticAlgebra ℚ d 0`): with one class generator
`kxGens = [d]` (`σ = c√d` or `σ = c`), or `kxGens = []` and `κ` not a square (`d = κ`, `σ = √d`)
(`kxQuadTry`). A passing `kxChkK` answers `some false`; correct by `kxDecideMWQ0_correct`
(`grp_of_chkK` with the embeddings `NFEmbed.qa_lift`).
-/

open Polynomial Differential IntermediateField NFEmbed

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

/-- The choice of `ℚ(√d)`, `ρs`, `σ`: `(d, has generator, c, σ radical)`. -/
def kxQuadTry (gens : List ℚ) (κ : ℚ) : Option (ℚ × Bool × ℚ × Bool) :=
  if κ = 0 then none else
  match gens with
  | [] => if Rat.sqrt κ * Rat.sqrt κ = κ then none else some (κ, false, 1, true)
  | [d] =>
    if d ≠ 0 ∧ Rat.sqrt (κ / d) * Rat.sqrt (κ / d) = κ / d then some (d, true, Rat.sqrt (κ / d), true)
    else if Rat.sqrt κ * Rat.sqrt κ = κ then some (d, true, Rat.sqrt κ, false) else none
  | _ => none

/-- `ρs` of a choice. -/
def qaRhos (d : ℚ) (hg : Bool) : List (QuadraticAlgebra ℚ d 0) := if hg then [qaW d] else []

/-- `σ` of a choice. -/
def qaSigma (d c : ℚ) (rad : Bool) : QuadraticAlgebra ℚ d 0 := if rad then ⟨0, c⟩ else ⟨c, 0⟩

lemma kxQuadTry_spec {gens : List ℚ} {κ d c : ℚ} {hg rad : Bool}
    (h : kxQuadTry gens κ = some (d, hg, c, rad)) :
    ((gens = [d] ∧ qaRhos d hg = [qaW d]) ∨ (gens = [] ∧ qaRhos d hg = [] ∧
      ∃ c', c' ≠ 0 ∧ κ = c' ^ 2 * d ∧ qaSigma d c rad = ⟨0, c'⟩)) ∧
    SigmaForm d κ (qaSigma d c rad) := by
  unfold kxQuadTry at h
  by_cases hκ : κ = 0
  · simp [hκ] at h
  rw [if_neg hκ] at h
  rcases gens with _ | ⟨d', _ | ⟨e, l'⟩⟩ <;> dsimp only at h
  · by_cases hs : Rat.sqrt κ * Rat.sqrt κ = κ
    · simp [hs] at h
    simp only [hs, if_false, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨Or.inr ⟨rfl, rfl, 1, one_ne_zero, by ring, rfl⟩, ?_⟩
    exact SigmaForm.rad 1 one_ne_zero (by ring)
  · by_cases h1 : d' ≠ 0 ∧ Rat.sqrt (κ / d') * Rat.sqrt (κ / d') = κ / d'
    · rw [if_pos h1] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      refine ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩
      have hc0 : Rat.sqrt (κ / d') ≠ 0 := fun h0 ↦ by
        have h2 := h1.2
        rw [h0, zero_mul] at h2
        exact hκ (by
          rw [eq_comm, div_eq_zero_iff] at h2
          exact h2.resolve_right h1.1)
      exact SigmaForm.rad _ hc0 (by rw [sq, h1.2]; field_simp [h1.1])
    · rw [if_neg h1] at h
      by_cases h2 : Rat.sqrt κ * Rat.sqrt κ = κ
      · simp only [h2, if_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨Or.inl ⟨rfl, rfl⟩, SigmaForm.rat _ (by rw [sq, h2])⟩
      · simp [h2] at h
  · simp at h

lemma not_isSquare_of_sqrt {d : ℚ} (h : ¬ Rat.sqrt d * Rat.sqrt d = d) : ¬ IsSquare d := by
  rintro ⟨r, hr⟩
  exact h ((Rat.exists_mul_self d).mp ⟨r, hr.symm⟩)

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m)
  (lv : (m : ℕ) → LC m)

section Search

variable (c0f : CPoly ℚ) (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (kmax : ℕ)

/-- The search over `ℚ(√d)` for given `ρs`, `σ`. -/
def kxMWSearchK (d : ℚ) [Fact (¬ IsSquare d)] (z : LC 0) (κ : ℚ)
    (ρs : List (QuadraticAlgebra ℚ d 0)) (σ : QuadraticAlgebra ℚ d 0) : Bool :=
  let uF := mwU Fc ks c0f A
  let Ac := polyOf (AFr Fc ks c0f A uF)
  let Bc := polyOf (BFr Fc ks c0f A uF)
  (List.range (kxCls Fc ks 0 g A B kt l cs).length).any fun kc ↦
    (List.range kmax).any fun kk ↦ kxChkK Fc ks c0f g A B kt l cs z κ ρs σ uF Ac Bc (kk + 1) kc

/-- **The quadratic search.** -/
def kxMWQ : Bool :=
  match kxZ Fc ks lv 0 A with
  | none => false
  | some z =>
    match kxQuadTry (kxGens Fc ks 0 g A B kt l cs) (kxKap Fc ks 0 A z) with
    | none => false
    | some (d, hg, c, rad) =>
      if hd : Rat.sqrt d * Rat.sqrt d = d then false
      else
        haveI : Fact (¬ IsSquare d) := ⟨not_isSquare_of_sqrt hd⟩
        kxMWSearchK Fc ks c0f g A B kt l cs kmax d z (kxKap Fc ks 0 A z) (qaRhos d hg)
          (qaSigma d c rad)

/-- The side conditions and the quadratic search. -/
def kxMWOKQ : Bool :=
  Fc == [c0f, [1]] && degG (MO Fc ks 0) A == 3 && kxOK Fc ks 0 A B kt l cs &&
  kxConst Fc ks 0 g A B kt l cs && kxRepOK Fc ks 0 g A B kt l cs &&
  kxMWQ Fc ks lv c0f g A B kt l cs kmax

end Search

/-- **`kxDecide` at level `0` with the rational and the quadratic certificate searches.** -/
def kxDecideMWQ0 (g : LC 0) (A B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (ps : List ℕ)
    (bound : ℕ) (rs : ℕ → ℕ) (kmax : ℕ) : Option Bool :=
  match kxDecideMW0 Fc ks lv g A B kt l cs ps bound rs kmax with
  | some b => some b
  | none => if kxMWOKQ Fc ks lv (Fc.headD []) g A B kt l cs kmax then some false else none

namespace MTower

variable {Fc ks lv}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The quadratic branch proves non-elementarity.** -/
theorem not_elementary_of_MWOKQ (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {g : LC 0} (hk : ks 0 = .exp g)
    (A : GPoly (LC 0)) (hsqc : GPoly.squarefreeCheck (MO Fc ks 0) A = true)
    (hdegpos : 0 < degG (MO Fc ks 0) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks 0) A))
    (θ : L) (hθ : θ ^ 2 = T.evP 0 A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (kmax : ℕ)
    (hok : kxMWOKQ Fc ks lv (Fc.headD []) g A B kt l cs kmax = true) :
    ¬ HasElementaryIntegral (T.ev 1 ((B, kxDen Fc ks 0 A kt l cs) : LC 1) * θ) := by
  simp only [kxMWOKQ, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨hFc, hdeg3⟩, hokx⟩, hcst⟩, hrep⟩, hq⟩ := hok
  unfold kxMWQ at hq
  split at hq
  · exact absurd hq (by decide)
  rename_i z hz
  split at hq
  · exact absurd hq (by decide)
  rename_i d hg c rad htry
  split_ifs at hq with hd
  have : Fact (¬ IsSquare d) := ⟨not_isSquare_of_sqrt hd⟩
  obtain ⟨hgc, hσc⟩ := kxQuadTry_spec htry
  unfold kxMWSearchK at hq
  simp only [List.any_eq_true, List.mem_range] at hq
  obtain ⟨kc, hkc, kk, -, hchk⟩ := hq
  exact T.kx_not_elementary_mwC hmon hdeg 0 hn hc hk A hsqc hdegpos hcop hdeg3 θ hθ hgen B kt l cs
    hokx hcst hrep ⟨kc, hkc⟩ z hz (fun E _ _ _ TE _ hTm rtsF hrl hrs b₀ hb₀ ↦ by
      intro cC xC βC hns hns0 N hN μ
      have h := TE.grp_of_chkK (Fc.headD []) g A B kt l cs z (kxKap Fc ks 0 A z) (qaRhos d hg)
        (qaSigma d c rad) _ _ _ (kk + 1) hFc hTm ⟨kc, hkc⟩ hchk
        (fun rs s hl hsq hs ↦ qa_lift d _ _ _ _ hgc hσc rs s hl hsq hs)
        rtsF hrl hrs b₀ hb₀ hns hns0 N hN μ
      convert h using 3)

set_option maxHeartbeats 2000000 in
/-- **`kxDecideMWQ0` is correct**: whenever it answers `some b`, the integral is elementary exactly
when `b = true`. -/
theorem kxDecideMWQ0_correct (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc)
    (hn : T.n = 1) (hc : certC Fc ks lv 1 = true) {g : LC 0} (hk : ks 0 = .exp g)
    (A : GPoly (LC 0)) (hsqc : GPoly.squarefreeCheck (MO Fc ks 0) A = true)
    (hdegpos : 0 < degG (MO Fc ks 0) A) (hcop : Nat.Coprime 2 (degG (MO Fc ks 0) A))
    (θ : L) (hθ : θ ^ 2 = T.evP 0 A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F 1) {θ})
    (B : GPoly (LC 0)) (kt l : ℕ) (cs : List (LC 0)) (ps : List ℕ) (bound : ℕ) (rs : ℕ → ℕ)
    (kmax : ℕ) (b : Bool) (hdec : kxDecideMWQ0 Fc ks lv g A B kt l cs ps bound rs kmax = some b) :
    HasElementaryIntegral (T.ev 1 ((B, kxDen Fc ks 0 A kt l cs) : LC 1) * θ) ↔ b = true := by
  unfold kxDecideMWQ0 at hdec
  cases hkx : kxDecideMW0 Fc ks lv g A B kt l cs ps bound rs kmax with
  | some b' =>
    rw [hkx] at hdec
    cases hdec
    exact T.kxDecideMW0_correct hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs ps bound
      rs kmax _ hkx
  | none =>
    rw [hkx] at hdec
    simp only at hdec
    split_ifs at hdec with hok
    cases hdec
    exact iff_of_false (T.not_elementary_of_MWOKQ hmon hdeg hn hc hk A hsqc hdegpos hcop θ hθ hgen
      B kt l cs kmax hok) (by decide)

end MTower

end Curves.MT
