import RischTragerBronstein.Torsion.IrrExist3
import RischTragerBronstein.Algebraic.SupRedGNF

/-!
# Reduction at large primes (1): the link with `pext`, and eventual goodness

For a certified reduction `R` (`RedValid p R φ`), the partial homomorphism
`pext (intSub φ) (psiRed φ)` of the reduction library agrees with `R.red` on `R.ok` elements
(`pext_eq_red`), so the reduced lists of the checks are `pext`-images (`map_pext_eq`,
`redBL_eq_pext`). An element is *good* at `R` if it and (when non-zero) its inverse are `R.ok`;
good elements are zero-or-unit (`ZP`) in `intSub φ` (`zp_of_good`).

Over a number field `NF M`, with `R.ok = pIntL p` (the reductions of `nfRedAt`), every finite list
of elements is good at all large primes (**`ev_good`**).
-/

open Polynomial Filter

namespace Curves

open CPoly Sup

section Link

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [DecidableEq K] (R : RedFns p K) {φ : K →+* ℚ_[p]}
  (hR : RedValid p R φ)

include hR in
lemma mem_intSub_of_ok {x : K} (hx : R.ok x = true) : x ∈ intSub φ := (atom φ R hR hx).2

include hR in
lemma pext_eq_red {x : K} (hx : R.ok x = true) : pext (intSub φ) (psiRed φ) x = R.red x := by
  rw [pext_of_mem (mem_intSub_of_ok R hR hx)]
  exact psiRed_atom φ R hR hx

include hR in
lemma map_pext_eq {l : List K} (hl : ∀ c ∈ l, R.ok c = true) :
    l.map (pext (intSub φ) (psiRed φ)) = l.map R.red :=
  List.map_congr_left fun c hc ↦ pext_eq_red R hR (hl c hc)

include hR in
lemma inS_of_ok {l : List K} (hl : ∀ c ∈ l, R.ok c = true) : InS (intSub φ) l :=
  fun c hc ↦ mem_intSub_of_ok R hR (hl c hc)

include hR in
lemma inSB_of_ok {W : List (List K)} (hW : ∀ P ∈ W, ∀ c ∈ P, R.ok c = true) :
    InSB (intSub φ) W :=
  fun P hP ↦ inS_of_ok R hR (hW P hP)

include hR in
lemma redBL_eq_pext {W : List (List K)} (hW : ∀ P ∈ W, ∀ c ∈ P, R.ok c = true) :
    redBL R W = W.map (·.map (pext (intSub φ) (psiRed φ))) := by
  unfold redBL
  exact List.map_congr_left fun P hP ↦ (map_pext_eq R hR (hW P hP)).symm

/-- A good element: integral, with an integral inverse when non-zero. -/
def Good (x : K) : Prop := R.ok x = true ∧ (x ≠ 0 → R.ok x⁻¹ = true)

include hR in
lemma zp_of_good {x : K} (h : Good R x) : ZP (intSub φ) x := by
  by_cases h0 : x = 0
  · exact Or.inl h0
  · exact Or.inr ⟨mem_intSub_of_ok R hR h.1, mem_intSub_of_ok R hR (h.2 h0)⟩

include hR in
lemma red_ne_zero_of_good {x : K} (h : Good R x) (h0 : x ≠ 0) : R.red x ≠ 0 := by
  rw [← pext_eq_red R hR h.1]
  exact pext_ne_zero_of_inv (mem_intSub_of_ok R hR h.1) (mem_intSub_of_ok R hR (h.2 h0)) h0

include hR in
lemma red_ne_of_good {x y : K} (hx : R.ok x = true) (hy : R.ok y = true) (h : Good R (x - y))
    (hne : x ≠ y) : R.red x ≠ R.red y := by
  rw [← pext_eq_red R hR hx, ← pext_eq_red R hR hy]
  intro heq
  have := pext_sub (g := psiRed φ) (mem_intSub_of_ok R hR hx) (mem_intSub_of_ok R hR hy)
  rw [heq, sub_self] at this
  exact pext_ne_zero_of_inv (mem_intSub_of_ok R hR h.1) (mem_intSub_of_ok R hR (h.2 (sub_ne_zero.mpr hne)))
    (sub_ne_zero.mpr hne) this

end Link

section Ev

variable {M : CPoly ℚ} [Fact (Irreducible (toPoly M))]

/-- Reductions of `NF M` with the integrality test of `nfRedAt`. -/
def NFRed (p : ℕ) (R : RedFns p (NFC.NF M)) : Prop := ∀ x, R.ok x = Jac.pIntL p x.1

omit [Fact (Irreducible (toPoly M))] in
lemma nfRed_nfFns (p : ℕ) (s : ZMod p) : NFRed p (nfFns (M := M) p s) := fun _ ↦ rfl

/-- **Every finite list is good at all large primes.** -/
theorem ev_good (L : List (NFC.NF M)) :
    ∀ᶠ p in atTop, ∀ R : RedFns p (NFC.NF M), NFRed p R → ∀ x ∈ L, Good R x := by
  refine eventually_atTop.mpr ⟨(L.map fun x ↦ denSum x + denSum x⁻¹).sum + 1, fun p hp R hR x hx ↦ ?_⟩
  have hle : denSum x + denSum x⁻¹ ≤ (L.map fun x ↦ denSum x + denSum x⁻¹).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem hx)
  exact ⟨by rw [hR]; exact pInt_of_den (by omega), fun _ ↦ by rw [hR]; exact pInt_of_den (by omega)⟩

end Ev

end Curves
