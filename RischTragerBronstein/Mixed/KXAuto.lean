import RischTragerBronstein.Mixed.KXSearch
import RischTragerBronstein.Mixed.KXResidues
import RischTragerBronstein.Computable.NatSeq

/-!
# Automatic residue selection for the cubic decider

`kxAuto` enumerates both finite residue data and the three search bounds. Its caller supplies
only the input and one search bound. Every answer is correct, and completeness (unconditional: no
Manin kernel hypothesis) has no existential residue parameter. The finite dependence lemma is essential: this is an
enumeration of sufficient finite prefixes, not an enumeration of all infinite functions.
-/

open Polynomial Differential IntermediateField

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable (c0 : CPoly ℚ) [Fact (Irreducible (toPoly (fKc [c0, [1]])))]
  (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- Decode residue data and a bound triple, then run one decision attempt. -/
def kxAutoStage (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ)
    (cs : List (LC m)) (i : ℕ) : Option Bool :=
  let p := Nat.unpair i
  kxSearchStage c0 ks lv m g A B kt l cs (natSeq p.1) p.2

/-- Search with automatic residue data, retaining the first answer. -/
def kxAuto (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ)
    (cs : List (LC m)) (N : ℕ) : Option Bool :=
  prefixSearch (kxAutoStage c0 ks lv m g A B kt l cs) N

/-- Every answer persists unchanged as the search bound grows. -/
theorem kxAuto_mono (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ)
    (cs : List (LC m)) {N M : ℕ} {b : Bool} (hNM : N ≤ M)
    (h : kxAuto c0 ks lv m g A B kt l cs N = some b) :
    kxAuto c0 ks lv m g A B kt l cs M = some b :=
  prefixSearch_mono hNM h

namespace MTower

variable {ks lv}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
  (T : MTower [c0, [1]] ks Cc L)

/-- Automatic residue selection preserves correctness. -/
theorem kxAuto_correct (hmon : (toB [c0, [1]]).Monic)
    (hdeg : (toB [c0, [1]]).natDegree = cvN [c0, [1]]) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC [c0, [1]] ks lv (m + 1) = true)
    {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO [c0, [1]] ks m) A = true)
    (hdegpos : 0 < degG (MO [c0, [1]] ks m) A)
    (hcop : Nat.Coprime 2 (degG (MO [c0, [1]] ks m) A))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (N : ℕ) (b : Bool)
    (hdec : kxAuto c0 ks lv m g A B kt l cs N = some b) :
    HasElementaryIntegral (T.ev (m + 1)
      ((B, kxDen [c0, [1]] ks m A kt l cs) : LC (m + 1)) * θ) ↔ b = true := by
  obtain ⟨i, -, hi⟩ := prefixSearch_sound hdec
  exact T.kxDecideNC_correct c0 hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs
    _ _ _ _ _ b hi

/-- For accepted cubic data, the automatic search eventually returns the correct answer.
Only Manin's kernel theorem is assumed beyond the input conditions; no residue data is supplied. -/
theorem kxAuto_decides (hmon : (toB [c0, [1]]).Monic)
    (hdeg : (toB [c0, [1]]).natDegree = cvN [c0, [1]]) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC [c0, [1]] ks lv (m + 1) = true)
    {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO [c0, [1]] ks m) A = true)
    (hdeg3 : degG (MO [c0, [1]] ks m) A = 3)
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (hr0 : cs.length ≠ 0)
    (hok : kxOK [c0, [1]] ks m A B kt l cs = true)
    (hrep : kxConst [c0, [1]] ks m g A B kt l cs = true →
      kxRepOK [c0, [1]] ks m g A B kt l cs = true)
    (hAw : ∀ a ∈ A, kxWF c0 ks m a) (hBw : ∀ b ∈ B, kxWF c0 ks m b)
    (hcsw : ∀ c ∈ cs, kxWF c0 ks m c) (hgw : kxWF c0 ks m g) :
    ∃ N0 b, (∀ N, N0 ≤ N → kxAuto c0 ks lv m g A B kt l cs N = some b) ∧
      (HasElementaryIntegral (T.ev (m + 1)
        ((B, kxDen [c0, [1]] ks m A kt l cs) : LC (m + 1)) * θ) ↔ b = true) := by
  obtain ⟨rs, B0, hB⟩ := T.kxDecideNC_decides c0 hmon hdeg m hn hc hk A hsqc hdeg3 θ hθ
    hgen B kt l cs hr0 hok hrep hAw hBw hcsw hgw
  obtain ⟨N0, hN⟩ := hB B0 le_rfl
  obtain ⟨K0, hK⟩ := hN N0 le_rfl
  obtain ⟨b, hb, -⟩ := hK K0 le_rfl
  obtain ⟨r, hr⟩ := natSeq_complete (m + 1) rs
  have heq := kxDecideNC_congr_prefix c0 ks lv m g A B kt l cs (primesBelow B0) B0 N0 K0
    (fun j hj ↦ hr j (by omega))
  have hi : kxAutoStage c0 ks lv m g A B kt l cs
      (Nat.pair r (Nat.pair B0 (Nat.pair N0 K0))) = some b := by
    simpa only [kxAutoStage, kxSearchStage, Nat.unpair_pair] using heq.trans hb
  obtain ⟨b', hb'⟩ := prefixSearch_complete hi
  refine ⟨Nat.pair r (Nat.pair B0 (Nat.pair N0 K0)) + 1, b',
    fun N hN ↦ hb' N (by omega), ?_⟩
  exact T.kxAuto_correct c0 hmon hdeg m hn hc hk A hsqc (by rw [hdeg3]; decide)
    (by rw [hdeg3]; decide) θ hθ hgen B kt l cs _ b' (hb' _ (Nat.lt_succ_self _))

end MTower

end Curves.MT
