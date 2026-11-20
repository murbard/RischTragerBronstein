import RischTragerBronstein.Mixed.KRSetup

/-!
# Radicals over an exponential level: the Liouville form on the curve `yⁿ = A(x)` over `Fₘ`

For a realization `T` whose top level `t = tₘ` is an exponential and `θⁿ = A(t)`:

* `kr_core_exact`: if the logarithms have no `θʲ`-projection, a Liouville form for
  `B/(tᵏ Aˡ) · θʲ` gives `a ∈ Fₘ₊₁` with `B/(tᵏ Aˡ) · θʲ = (a θʲ)′`;
* `kr_core_tors`: with a witness `W₀` of `N Ψ` and `W₀′/W₀ = ∑ Eᵢ θⁱ`,
  `B/(tᵏ Aˡ) · θʲ = (a θʲ)′ + e Eⱼ θʲ` with `e` constant.
-/

open Polynomial Differential IntermediateField Ramanujan

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

section Core

variable (m : ℕ) (h : T.Tr (m + 1)) (A : GPoly (LC m))
  (hsq : Squarefree (GPoly.toPoly (T.MP m h.of_succ) A))
  (hdeg : 0 < (GPoly.toPoly (T.MP m h.of_succ) A).natDegree)
  (n : ℕ) (hn : 0 < n) (θ : L) (hθ : θ ^ n = T.evP m A)

/-- The rational part `B/(tᵏ Aˡ)` lies in `C(x)`. -/
lemma krS_b (B : GPoly (LC m)) (k l : ℕ) :
    T.evP m B / (T.ts m ^ k * T.evP m A ^ l) ∈ (T.F m)⟮(T.krS m h A hsq hdeg n hn θ hθ).x⟯ := by
  letI := algebraAdjoinSimple (F := T.F m) (T.krS m h A hsq hdeg n hn θ hθ).x
  have h1 : ∀ P : GPoly (LC m), T.evP m P ∈ (T.F m)⟮(T.krS m h A hsq hdeg n hn θ hθ).x⟯ := by
    intro P
    rw [← T.aeval_toPoly (T.MP m h.of_succ) (T.sem_MP m h.of_succ),
      ← algebraMap_adjoinSimple (F := T.F m) (T.ts m)]
    exact SetLike.coe_mem _
  have h2 : T.ts m ∈ (T.F m)⟮(T.krS m h A hsq hdeg n hn θ hθ).x⟯ := mem_adjoin_simple_self _ _
  exact div_mem (h1 B) (mul_mem (pow_mem h2 k) (pow_mem (h1 A) l))

lemma krS_f (B : GPoly (LC m)) (k l j : ℕ) :
    T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ ^ j ∈
      (T.F m)⟮(T.krS m h A hsq hdeg n hn θ hθ).x⟯⟮(T.krS m h A hsq hdeg n hn θ hθ).y⟯ :=
  mul_mem (IntermediateField.algebraMap_mem _ (⟨_, T.krS_b m h A hsq hdeg n hn θ hθ B k l⟩ :
    (T.F m)⟮(T.krS m h A hsq hdeg n hn θ hθ).x⟯)) (pow_mem (mem_adjoin_simple_self _ _) j)

variable (hM : T.MixHyp (m + 1)) (hmn : m < T.n) {g : LC m} (hk : ks m = .exp g)
  (ζ : T.F m) (hζ : IsPrimitiveRoot ζ n) (j : ℕ) (hj0 : 0 < j) (hjn : j < n)
  (B : GPoly (LC m)) (k l : ℕ) {ι : Type*} (s : Finset ι) (c u : ι → L)
  (hcd : ∀ i ∈ s, (c i)′ = 0)
  (hu : ∀ i ∈ s, u i ≠ 0 ∧ u i ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
  (v : L) (hv : v ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
  (heq : T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ ^ j = v′ + ∑ i ∈ s, c i * logDeriv (u i))

include hM hj0 hcd hu hv heq in
/-- **Exactness**: without projected logarithms, `B/(tᵏ Aˡ) · θʲ = (a θʲ)′`. -/
theorem kr_core_exact
    (hproj : ∀ W : (T.F m)⟮(T.krS m h A hsq hdeg n hn θ hθ).x⟯⟮(T.krS m h A hsq hdeg n hn θ hθ).y⟯,
      W ≠ 0 → (T.krS m h A hsq hdeg n hn θ hθ).Supp (K := AlgebraicClosure (T.F m)) W →
      (T.krS m h A hsq hdeg n hn θ hθ).four ζ hζ ⟨j, hjn⟩
        ((T.krS m h A hsq hdeg n hn θ hθ).dl (Polynomial.C (T.val m g)′ * X)
          (T.krS_hx m h A hsq hdeg n hn θ hθ hmn hk) W) = 0) :
    ∃ a ∈ T.F (m + 1), T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ ^ j = (a * θ ^ j)′ := by
  classical
  have hb := T.krS_b m h A hsq hdeg n hn θ hθ B k l
  have hfm := T.krS_f m h A hsq hdeg n hn θ hθ B k l j
  have hreg := T.krS_reg m h A hsq hdeg n hn θ hθ B k l j hfm
  obtain ⟨a, ha, hae⟩ := (T.krS m h A hsq hdeg n hn θ hθ).kr_liouville_exact (K := AlgebraicClosure (T.F m)) ((T.val m g)′)
    (T.krS_hx m h A hsq hdeg n hn θ hθ hmn hk) (fun c ↦ deriv_algebraMap c) (T.keS_good m hM hk)
    (T.keS_constC m) ζ hζ ⟨j, hjn⟩ hj0 _ hb hfm hreg hproj s c u hcd
    (fun i hi ↦ ⟨(hu i hi).1, T.krS_mem m h A hsq hdeg n hn θ hθ _ (hu i hi).2⟩) v
    (T.krS_mem m h A hsq hdeg n hn θ hθ _ hv) heq
  exact ⟨a, (T.mem_F_succ).mpr ha, hae⟩

include hM hj0 hcd hu hv heq hζ in
/-- **With a torsion witness**: `B/(tᵏ Aˡ) · θʲ = (a θʲ)′ + e Eⱼ θʲ`. -/
theorem kr_core_tors (hcopA : Nat.Coprime n (GPoly.toPoly (T.MP m h.of_succ) A).natDegree)
    (hjc : Nat.Coprime j n) (hn1 : 1 < n) (β₀ : AlgebraicClosure (T.F m)) (hβ₀ : β₀ ≠ 0)
    (hv0 : β₀ ^ n = ((T.krS m h A hsq hdeg n hn θ hθ).p.map (algebraMap (T.F m) _)).eval 0)
    (N : ℕ) (hN : 0 < N)
    (W₀ : (T.F m)⟮(T.krS m h A hsq hdeg n hn θ hθ).x⟯⟮(T.krS m h A hsq hdeg n hn θ hθ).y⟯)
    (hW₀ : W₀ ≠ 0) (hsW : (T.krS m h A hsq hdeg n hn θ hθ).Supp (K := AlgebraicClosure (T.F m)) W₀)
    (hWr : ∀ i, (T.krS m h A hsq hdeg n hn θ hθ).rv ζ β₀ W₀ i = N * ramC n i)
    (E : Fin n → (T.F m)⟮(T.krS m h A hsq hdeg n hn θ hθ).x⟯)
    (hE : (T.krS m h A hsq hdeg n hn θ hθ).dl (Polynomial.C (T.val m g)′ * X)
        (T.krS_hx m h A hsq hdeg n hn θ hθ hmn hk) W₀ =
      ∑ i, algebraMap (T.F m)⟮(T.krS m h A hsq hdeg n hn θ hθ).x⟯
        (T.F m)⟮(T.krS m h A hsq hdeg n hn θ hθ).x⟯⟮(T.krS m h A hsq hdeg n hn θ hθ).y⟯ (E i) *
          AdjoinSimple.gen (T.F m)⟮(T.krS m h A hsq hdeg n hn θ hθ).x⟯
            (T.krS m h A hsq hdeg n hn θ hθ).y ^ (i : ℕ)) :
    ∃ a ∈ T.F (m + 1), ∃ e : L, e′ = 0 ∧ T.evP m B / (T.ts m ^ k * T.evP m A ^ l) * θ ^ j =
      (a * θ ^ j)′ + e * ((E ⟨j, hjn⟩ : L) * θ ^ j) := by
  classical
  have hb := T.krS_b m h A hsq hdeg n hn θ hθ B k l
  have hfm := T.krS_f m h A hsq hdeg n hn θ hθ B k l j
  have hreg := T.krS_reg m h A hsq hdeg n hn θ hθ B k l j hfm
  obtain ⟨a, ha, e, he, hae⟩ := (T.krS m h A hsq hdeg n hn θ hθ).kr_liouville_tors (K := AlgebraicClosure (T.F m))
    ((T.val m g)′) (T.krS_hx m h A hsq hdeg n hn θ hθ hmn hk) (fun c ↦ deriv_algebraMap c)
    (T.keS_good m hM hk) (T.keS_constC m) ζ hζ ⟨j, hjn⟩ hj0 _ hb hfm hreg β₀ hβ₀ hv0 hcopA hjc hn1
    N hN W₀ hW₀ hsW hWr E hE s c u hcd
    (fun i hi ↦ ⟨(hu i hi).1, T.krS_mem m h A hsq hdeg n hn θ hθ _ (hu i hi).2⟩) v
    (T.krS_mem m h A hsq hdeg n hn θ hθ _ hv) heq
  refine ⟨a, (T.mem_F_succ).mpr ha, algebraMap (T.F m) L e, ?_, hae⟩
  rw [deriv_algebraMap, he, map_zero]

end Core

end MTower

end Curves.MT
