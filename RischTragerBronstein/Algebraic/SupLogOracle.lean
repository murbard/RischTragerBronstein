import RischTragerBronstein.Algebraic.SupLogDecide

/-!
# A search oracle for torsion

`torsSearch f n bound` looks for the least `N ≤ bound` with `N Γ` principal (by `supPrincipalC`);
it never claims non-torsion, so it satisfies `TorsSpecN` (`torsSearch_spec`). With it,
`superLogDecide` decides every integrand whose residue components are torsion of order `≤ bound`.
-/

open Polynomial CPoly

namespace Sup

variable {F : Type*} [Field F] [DecidableEq F]

/-- Search for a principal multiple `N Γ`, `1 ≤ N ≤ bound`. -/
def torsSearch (f : CPoly F) (n bound : ℕ) (l : List (F × F × ℕ)) : Option (Option ℕ) :=
  ((List.range bound).find? fun N ↦ (supPrincipalC f n (f.length - 1)
    (l.map fun q ↦ (q.1, q.2.1, (N + 1) * q.2.2)) ((N + 1) * (l.map fun q ↦ q.2.2).sum)).isSome).map
    fun N ↦ some (N + 1)

lemma gammaL_scale {r : ℕ} (α β : Fin r → F) (mq : Fin r → ℕ) (N : ℕ) :
    (gammaL α β mq 1).map (fun q ↦ (q.1, q.2.1, N * q.2.2)) = gammaL α β mq N := by
  simp [gammaL, List.map_ofFn, Function.comp_def]

lemma gammaL_sum {r : ℕ} (α β : Fin r → F) (mq : Fin r → ℕ) :
    ((gammaL α β mq 1).map fun q ↦ q.2.2).sum = ∑ q, mq q := by
  simp [gammaL, List.map_ofFn, Function.comp_def, List.sum_ofFn]

/-- **The search oracle is correct.** -/
theorem torsSearch_spec [CharZero F] (f : CPoly F) {n : ℕ} (hn : 0 < n) (bound : ℕ) :
    TorsSpecN f n (torsSearch f n bound) := by
  intro r α β mq hv _
  refine ⟨fun N hN ↦ ?_, fun h ↦ ?_⟩
  · unfold torsSearch at hN
    obtain ⟨N0, hN0, hNe⟩ := Option.map_eq_some_iff.mp hN
    simp only [Option.some.injEq] at hNe
    subst hNe
    have hfind := List.find?_some hN0
    rw [gammaL_scale, gammaL_sum] at hfind
    obtain ⟨⟨jj, cs⟩, hjc⟩ := Option.isSome_iff_exists.mp hfind
    have hΓ : ∀ q ∈ gammaL α β mq (N0 + 1), (n : F) * q.2.1 ^ (n - 1) ≠ 0 ∧
        q.2.1 ^ n = (toPoly f).eval q.1 := by
      intro q hq
      obtain ⟨i, rfl⟩ := (mem_gammaL α β mq (N0 + 1) q).mp hq
      exact ⟨mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (pow_ne_zero _ (hv i).1), (hv i).2⟩
    obtain ⟨W, hW0, hWs, hWv⟩ := supPrincipalC_sound f n hn _ _ _ hΓ hjc
    refine ⟨by omega, W, hW0, hWs, fun q ↦ hWv _ ((mem_gammaL α β mq _ _).mpr ⟨q, rfl⟩)⟩
  · unfold torsSearch at h
    obtain ⟨N0, -, hNe⟩ := Option.map_eq_some_iff.mp h
    simp at hNe

end Sup
