import RischTragerBronstein.Computable.CField
import Mathlib.Data.List.GetD

/-!
# Codes over a simple algebraic extension `ℚ(α)`

An element `∑ₖ αᵏ cₖ` of `R ⊗ ℚ(α)` is coded by the list `[c₀, c₁, …]` of codes of `R`, for any
code ring `ROps β` interpreted by `sem` in a commutative ring `K ∋ α`. `nConv` multiplies, `nRed`
reduces modulo a monic `μ = Xᵈ + ∑_{i<d} μᵢ Xⁱ ∈ ℤ[X]` (`α` a root), by structural recursion only
(cheap kernel evaluation). `nVal` is the value; `nVal_nConv`, `nVal_nRed` are the specifications.
-/

namespace NCodes

/-- Ring operations on codes. -/
structure ROps (β : Type) where
  add : β → β → β
  mul : β → β → β
  neg : β → β
  zero : β
  ofInt : ℤ → β

variable {β : Type} (R : ROps β)

/-- A semantics of the ring operations. -/
structure RSem {K : Type*} [CommRing K] (sem : β → K) : Prop where
  add : ∀ a b, sem (R.add a b) = sem a + sem b
  mul : ∀ a b, sem (R.mul a b) = sem a * sem b
  neg : ∀ a, sem (R.neg a) = -sem a
  zero : sem R.zero = 0
  ofInt : ∀ z : ℤ, sem (R.ofInt z) = z

/-- Coefficientwise sum. -/
def nAdd : List β → List β → List β
  | [], q => q
  | p, [] => p
  | x :: p, y :: q => R.add x y :: nAdd p q

/-- Negation. -/
def nNeg (p : List β) : List β := p.map R.neg

/-- Product (convolution). -/
def nConv : List β → List β → List β
  | [], _ => []
  | x :: a, b => nAdd R (b.map (R.mul x)) (R.zero :: nConv a b)

/-- Multiplication by `α` of a reduced code of length `≤ d` (`μ = [μ₀, …, μ_{d−1}]`). -/
def mulα (μ : List ℤ) (r : List β) : List β :=
  let d := μ.length
  let top := r.getD (d - 1) R.zero
  (List.range d).map fun s ↦
    R.add (if s = 0 then R.zero else r.getD (s - 1) R.zero) (R.mul (R.ofInt (-μ.getD s 0)) top)

/-- Reduction modulo `μ` (Horner from the top). -/
def nRed (μ : List ℤ) : List β → List β
  | [] => []
  | x :: c => nAdd R [x] (mulα R μ (nRed μ c))

lemma length_mulα (μ : List ℤ) (r : List β) : (mulα R μ r).length = μ.length := by
  simp [mulα]

lemma length_nRed (μ : List ℤ) (hd : 0 < μ.length) : ∀ c : List β, (nRed R μ c).length ≤ μ.length
  | [] => by simp [nRed]
  | x :: c => by
    simp only [nRed]
    have h := length_mulα R μ (nRed R μ c)
    generalize mulα R μ (nRed R μ c) = r at h
    cases r with
    | nil => simp at h; omega
    | cons y r => simp only [nAdd, List.length_cons] at h ⊢; omega

section Sem

variable {K : Type*} [CommRing K] {R} {sem : β → K} (hS : RSem R sem) (α : K)

/-- The value `∑ₖ αᵏ sem cₖ`. -/
def nVal (sem : β → K) (α : K) : List β → K
  | [] => 0
  | x :: c => sem x + α * nVal sem α c

include hS

lemma nVal_nAdd : ∀ p q : List β, nVal sem α (nAdd R p q) = nVal sem α p + nVal sem α q
  | [], q => by simp [nAdd, nVal]
  | x :: p, [] => by simp [nAdd, nVal]
  | x :: p, y :: q => by
    simp only [nAdd, nVal, hS.add, nVal_nAdd p q]
    ring

lemma nVal_nNeg (p : List β) : nVal sem α (nNeg R p) = -nVal sem α p := by
  induction p with
  | nil => simp [nNeg, nVal]
  | cons x p ih =>
    simp only [nNeg, List.map_cons, nVal, hS.neg] at ih ⊢
    rw [ih]; ring

lemma nVal_map_mul (x : β) (b : List β) :
    nVal sem α (b.map (R.mul x)) = sem x * nVal sem α b := by
  induction b with
  | nil => simp [nVal]
  | cons y b ih =>
    simp only [List.map_cons, nVal, hS.mul, ih]
    ring

lemma nVal_nConv (a b : List β) : nVal sem α (nConv R a b) = nVal sem α a * nVal sem α b := by
  induction a with
  | nil => simp [nConv, nVal]
  | cons x a ih =>
    simp only [nConv, nVal_nAdd hS, nVal_map_mul hS, nVal, hS.zero, ih]
    ring

lemma nVal_eq_sum (c : List β) (N : ℕ) (hN : c.length ≤ N) :
    nVal sem α c = ∑ s ∈ Finset.range N, α ^ s * sem (c.getD s R.zero) := by
  induction c generalizing N with
  | nil => simp [nVal, hS.zero]
  | cons x c ih =>
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at hN; omega⟩
    rw [Finset.sum_range_succ', nVal, ih N (by simp at hN; omega), Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_mul, pow_succ]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun s _ ↦ by ring

lemma nVal_mulα (μ : List ℤ) (hd : 0 < μ.length)
    (hμ : α ^ μ.length + ∑ i ∈ Finset.range μ.length, (μ.getD i 0 : K) * α ^ i = 0)
    (r : List β) (hr : r.length ≤ μ.length) : nVal sem α (mulα R μ r) = α * nVal sem α r := by
  set d := μ.length with hdd
  rw [nVal_eq_sum hS α _ d (by rw [length_mulα]), nVal_eq_sum hS α r d hr]
  have e : ∀ s ∈ Finset.range d, α ^ s * sem ((mulα R μ r).getD s R.zero) =
      α ^ s * (if s = 0 then 0 else sem (r.getD (s - 1) R.zero)) -
        (μ.getD s 0 : K) * α ^ s * sem (r.getD (d - 1) R.zero) := by
    intro s hs
    have hs' := Finset.mem_range.mp hs
    rw [List.getD_eq_getElem _ _ (by rw [length_mulα]; exact hs')]
    simp only [mulα, List.getElem_map, List.getElem_range]
    rw [hS.add, hS.mul, hS.ofInt]
    split_ifs with h0
    · rw [hS.zero]; push_cast; ring
    · push_cast; ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hμ2 : ∑ i ∈ Finset.range d, (μ.getD i 0 : K) * α ^ i = -α ^ d := by linear_combination hμ
  rw [hμ2]
  obtain ⟨d', hd'⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [hd', Finset.sum_range_succ', Finset.mul_sum, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, if_true, mul_zero, add_zero, Nat.succ_ne_zero, if_false,
    ← mul_assoc, ← pow_succ']
  ring

lemma nVal_nRed (μ : List ℤ) (hd : 0 < μ.length)
    (hμ : α ^ μ.length + ∑ i ∈ Finset.range μ.length, (μ.getD i 0 : K) * α ^ i = 0) :
    ∀ c : List β, nVal sem α (nRed R μ c) = nVal sem α c
  | [] => rfl
  | x :: c => by
    simp only [nRed]
    rw [nVal_nAdd hS, nVal_mulα hS α μ hd hμ _ (length_nRed R μ hd c), nVal_nRed μ hd hμ c]
    simp [nVal]

end Sem

end NCodes
