import RischTragerBronstein.Mixed.KXAllLevels
import RischTragerBronstein.Computable.PrefixSearch

/-!
# A persistent, single-bound search for the cubic decider

The three bounds in `kxDecideNC_decides` have nested quantifiers. Setting all three equal is
not justified by that theorem. Instead enumerate triples and retain the first answer.
`kxSearch_correct` is unconditional; `kxSearch_decides` assumes Manin's kernel theorem and
retains the existing existential choice of the residue-specialization data `rs`.
-/

open Polynomial Differential IntermediateField

namespace Curves.MT

open CPoly Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable (c0 : CPoly ℚ) [Fact (Irreducible (toPoly (fKc [c0, [1]])))]
  (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- Stage `i` tries the triple encoded by `i = pair Bd (pair nmax kmax)`. -/
def kxSearchStage (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ)
    (cs : List (LC m)) (rs : ℕ → ℕ) (i : ℕ) : Option Bool :=
  let p := Nat.unpair i
  let q := Nat.unpair p.2
  kxDecideNC c0 ks lv m g A B kt l cs (primesBelow p.1) p.1 rs q.1 q.2

/-- Try the first `N` bound triples, retaining the first answer. -/
def kxSearch (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ)
    (cs : List (LC m)) (rs : ℕ → ℕ) (N : ℕ) : Option Bool :=
  prefixSearch (kxSearchStage c0 ks lv m g A B kt l cs rs) N

/-- Increasing the search bound preserves every answer, even on unchecked inputs. -/
theorem kxSearch_mono (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ)
    (cs : List (LC m)) (rs : ℕ → ℕ) {N M : ℕ} {b : Bool} (hNM : N ≤ M)
    (h : kxSearch c0 ks lv m g A B kt l cs rs N = some b) :
    kxSearch c0 ks lv m g A B kt l cs rs M = some b :=
  prefixSearch_mono hNM h

namespace MTower

variable {ks lv}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
  (T : MTower [c0, [1]] ks Cc L)

/-- Every returned answer is correct at every bound, without Manin's kernel theorem. -/
theorem kxSearch_correct (hmon : (toB [c0, [1]]).Monic)
    (hdeg : (toB [c0, [1]]).natDegree = cvN [c0, [1]]) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC [c0, [1]] ks lv (m + 1) = true)
    {g : LC m} (hk : ks m = .exp g)
    (A : GPoly (LC m)) (hsqc : GPoly.squarefreeCheck (MO [c0, [1]] ks m) A = true)
    (hdegpos : 0 < degG (MO [c0, [1]] ks m) A)
    (hcop : Nat.Coprime 2 (degG (MO [c0, [1]] ks m) A))
    (θ : L) (hθ : θ ^ 2 = T.evP m A)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m)) (rs : ℕ → ℕ) (N : ℕ) (b : Bool)
    (hdec : kxSearch c0 ks lv m g A B kt l cs rs N = some b) :
    HasElementaryIntegral (T.ev (m + 1)
      ((B, kxDen [c0, [1]] ks m A kt l cs) : LC (m + 1)) * θ) ↔ b = true := by
  obtain ⟨i, -, hi⟩ := prefixSearch_sound hdec
  exact T.kxDecideNC_correct c0 hmon hdeg m hn hc hk A hsqc hdegpos hcop θ hθ hgen B kt l cs
    _ _ rs _ _ b hi

/-- For suitable residue data, one search bound suffices at every level. Once reached, the
correct answer persists. Completeness is unconditional. -/
theorem kxSearch_decides (hmon : (toB [c0, [1]]).Monic)
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
    ∃ rs : ℕ → ℕ, ∃ N0 b, (∀ N, N0 ≤ N → kxSearch c0 ks lv m g A B kt l cs rs N = some b) ∧
      (HasElementaryIntegral (T.ev (m + 1)
        ((B, kxDen [c0, [1]] ks m A kt l cs) : LC (m + 1)) * θ) ↔ b = true) := by
  obtain ⟨rs, B0, hB⟩ := T.kxDecideNC_decides c0 hmon hdeg m hn hc hk A hsqc hdeg3 θ hθ
    hgen B kt l cs hr0 hok hrep hAw hBw hcsw hgw
  obtain ⟨N0, hN⟩ := hB B0 le_rfl
  obtain ⟨K0, hK⟩ := hN N0 le_rfl
  obtain ⟨b, hb, -⟩ := hK K0 le_rfl
  have hi : kxSearchStage c0 ks lv m g A B kt l cs rs (Nat.pair B0 (Nat.pair N0 K0)) = some b := by
    simpa only [kxSearchStage, Nat.unpair_pair] using hb
  obtain ⟨b', hb'⟩ := prefixSearch_complete hi
  refine ⟨rs, Nat.pair B0 (Nat.pair N0 K0) + 1, b', fun N hN ↦ hb' N (by omega), ?_⟩
  exact T.kxSearch_correct c0 hmon hdeg m hn hc hk A hsqc (by rw [hdeg3]; decide)
    (by rw [hdeg3]; decide) θ hθ hgen B kt l cs rs _ b' (hb' _ (Nat.lt_succ_self _))

end MTower

end Curves.MT
