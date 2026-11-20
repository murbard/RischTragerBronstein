import RischTragerBronstein.Torsion.PlacePrimeExist2

/-!
# Place data modulo large primes (3): the checks without the multiplier

**`primePre_of_good`**: a place certificate over `K` with its characteristic-`0` checks
(`Char0Pl`: `PlaceCert.Facts`, `D` non-zero at the fibres, fibres distinct from the base points)
passes `PlaceCert.primePre` at every certified reduction at which finitely many explicit elements
are good (`GoodPl`).
-/

open Polynomial

namespace Curves

open CPoly Sup

section Pre

variable {K : Type*} [Field K] [DecidableEq K] {p : ℕ} [Fact p.Prime] (R : RedFns p K)
  {φ : K →+* ℚ_[p]} (hR : RedValid p R φ)

local notation "Sφ" => intSub φ
local notation "gφ" => psiRed φ

/-- The characteristic-`0` facts behind the place checks at a prime. -/
structure Char0Pl (Fc : BPoly K) (n : ℕ) (Dc : CPoly K) (xs : List K) (D : PlaceCert K) : Prop where
  facts : D.Facts Fc n
  Dne : ∀ j < D.fib.length, muD Dc (D.fα j) 1 < (compC Dc (shiftC (D.fα j) 1)).length
  αx : ∀ j < D.fib.length, ∀ i < xs.length, D.fα j ≠ xs.getD i 0

/-- The elements that must be good for the place checks. -/
structure GoodPl (Fc : BPoly K) (n : ℕ) (Dc : CPoly K) (xs : List K) (D : PlaceCert K) : Prop where
  zero : Good R 0
  F : GoodLL R Fc
  Dg : ∀ c ∈ Dc, Good R c
  x : ∀ c ∈ xs, Good R c
  α : ∀ j < D.fib.length, Good R (D.fα j)
  αd : ∀ j < D.fib.length, ∀ j' < D.fib.length, Good R (D.fα j - D.fα j')
  py : ∀ π < D.pl.length, ∀ c ∈ D.py π, Good R c
  ζ : ∀ j < D.fib.length, ∀ k < n, Good R (D.rζ j k)
  μ : ∀ j < D.fib.length, Good R ((compC Dc (shiftC (D.fα j) 1)).getD (muD Dc (D.fα j) 1) 0)
  αx : ∀ j < D.fib.length, ∀ i < xs.length, Good R (D.fα j - xs.getD i 0)
  unit : ∀ π < D.pl.length, Good R (derivLead Fc (D.fα (D.pj π)) (D.pe π) (D.py π))
  sep : ∀ j < D.fib.length, ∀ k < n, ∀ l < n, ∀ i < D.tp.getD j 0,
    Good R ((D.apx j k).getD i 0 - (D.apx j l).getD i 0)

lemma pext_pow {F F' : Type*} [Field F] [Field F'] {S : Subring F} {g : S →+* F'} {x : F}
    (hx : x ∈ S) (m : ℕ) : pext S g (x ^ m) = pext S g x ^ m := by
  rw [pext_of_mem (S.pow_mem hx m), pext_of_mem hx, ← map_pow]; rfl

include hR in
/-- **The place checks without the multiplier pass at good primes.** -/
theorem primePre_of_good {Fc : BPoly K} {n : ℕ} {Dc : CPoly K} {xs : List K} {D : PlaceCert K}
    (hC : Char0Pl Fc n Dc xs D) (hG : GoodPl R Fc n Dc xs D) :
    D.primePre R Fc n Dc (xs.map R.red) = true := by
  have hF : InSB Sφ Fc := inSB_of_good R hR hG.F
  have hD : InS Sφ Dc := inS_of_good R hR hG.Dg
  have hokF := ok_of_goodLL R hG.F
  have hDp : Dc.map R.red = Dc.map (pext Sφ gφ) := (map_pext_eq R hR fun c hc ↦ (hG.Dg c hc).1).symm
  have hFp : redBL R Fc = Fc.map (·.map (pext Sφ gφ)) := redBL_eq_pext R hR hokF
  have hfαS : ∀ j < D.fib.length, D.fα j ∈ Sφ := fun j hj ↦ mem_intSub_of_ok R hR (hG.α j hj).1
  have hαs : D.αs.length = D.fib.length := by simp [PlaceCert.αs]
  have hαget : ∀ j < D.fib.length, D.αs.getD j 0 = D.fα j := fun j hj ↦ D.αs_getD j hj
  have hαok : ∀ c ∈ D.αs, R.ok c = true := fun c hc ↦ by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    rw [← List.getD_eq_getElem _ 0 hj, hαget j (by rw [← hαs]; exact hj)]
    exact (hG.α j (by rw [← hαs]; exact hj)).1
  simp only [PlaceCert.primePre, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨hαok, fun π hπ c hc ↦ (hG.py π hπ c hc).1⟩, fun j hj k hk ↦ (hG.ζ j hj k hk).1⟩,
    ?_⟩, fun j hj ↦ ⟨?_, fun i hi ↦ ?_⟩⟩, fun π hπ ↦ ?_⟩, ?_⟩
  · -- the fibres stay distinct
    have e : (D.map R.red).αs = D.αs.map (pext Sφ gφ) := by
      rw [map_pext_eq R hR hαok]; simp [PlaceCert.αs, PlaceCert.map]
    rw [e]
    refine nodup_pext (fun c hc ↦ mem_intSub_of_ok R hR (hαok c hc)) hC.facts.nd fun i hi j hj ↦ ?_
    rw [hαs] at hi hj
    rw [hαget i hi, hαget j hj]
    exact zp_of_good R hR (hG.αd i hi j hj)
  · -- `D` keeps its order at the fibres
    obtain ⟨hs, hs'⟩ := shiftC_pext (g := gφ) (hfαS j hj) 1
    obtain ⟨hc, hc'⟩ := compC_pext (g := gφ) _ hs Dc hD
    rw [hDp, ← pext_eq_red R hR (hG.α j hj).1, ← hs', ← hc', getD_pext]
    exact pext_ne_zero_of_zp (zp_of_good R hR (hG.μ j hj)) (getD_ordC _ (hC.Dne j hj))
  · -- the fibres avoid the base points
    rw [List.length_map] at hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      ← List.getD_eq_getElem _ 0 hi]
    exact red_ne_of_good R hR (hG.α j hj).1 (hG.x _ (List.getD_eq_getElem _ _ hi ▸ List.getElem_mem hi)).1 (hG.αx j hj i hi)
      (hC.αx j hj i hi)
  · -- the unit condition
    have hπj := (hC.facts.pl π hπ).1
    obtain ⟨-, hB2, -⟩ := rootCheck_spec (hC.facts.pl π hπ).2.2
    have hyS : InS Sφ (D.py π) := inS_of_good R hR (hG.py π hπ)
    obtain ⟨hs, hs'⟩ := shiftC_pext (g := gφ) (hfαS _ hπj) (D.pe π)
    have hdF := derivYB_pext (g := gφ) Fc hF
    obtain ⟨hb, hb'⟩ := bivEval_pext (g := gφ) _ _ hs hyS (derivYB Fc) hdF.1
    rw [hFp, ← hdF.2, ← pext_eq_red R hR (hG.α _ hπj).1, ← hs',
      ← map_pext_eq R hR fun c hc ↦ (hG.py π hπ c hc).1, ← hb', getD_pext]
    exact pext_ne_zero_of_zp (zp_of_good R hR (hG.unit π hπ)) (getD_ordC _ hB2)
  · -- separation
    simp only [PlaceCert.sepCheckP, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      decide_eq_true_eq, List.any_eq_true]
    intro j hj k hk l hl
    rw [PlaceCert.map_fib_length] at hj
    by_cases hkl : k = l
    · exact Or.inl hkl
    right
    obtain ⟨i, hi, hne⟩ := PlaceCert.sepCheckP_spec D hC.facts.sep j hj k l hk hl hkl
    refine ⟨i, by rw [PlaceCert.map_tp]; exact hi, ?_⟩
    have hrtl : j < D.rt.length := by rw [hC.facts.rtl]; exact hj
    obtain ⟨hlen', hrts⟩ := hC.facts.rt j hj
    have key : ∀ k < n, ((D.map R.red).apx j k).getD i 0 = pext Sφ gφ ((D.apx j k).getD i 0) := by
      intro k hk
      obtain ⟨hπk, -, hs, -, -, -⟩ := hrts k hk
      have hk' : k < (D.rt.getD j []).length := by rw [hlen']; exact hk
      have hζS : D.rζ j k ∈ Sφ := mem_intSub_of_ok R hR (hG.ζ j hj k hk).1
      have hyS : InS Sφ (D.py (D.rπ j k)) := inS_of_good R hR (hG.py _ hπk)
      rw [PlaceCert.map_apx D R.red j k hrtl hk' hπk, PlaceCert.apx, getD_conjC _ hs,
        getD_conjC _ hs]
      split_ifs with hd
      · rw [pext_mul ((intSub φ).pow_mem hζS _) (hyS.getD _), pext_pow hζS,
          ← pext_eq_red R hR (hG.ζ j hj k hk).1,
          ← map_pext_eq R hR fun c hc ↦ (hG.py _ hπk c hc).1, getD_pext]
      · exact pext_zero.symm
    rw [key k hk, key l hl]
    have hS : ∀ k < n, (D.apx j k).getD i 0 ∈ Sφ := fun k hk ↦ by
      obtain ⟨hπk, -, hs, -, -, -⟩ := hrts k hk
      have hζS : D.rζ j k ∈ Sφ := mem_intSub_of_ok R hR (hG.ζ j hj k hk).1
      have hyS : InS Sφ (D.py (D.rπ j k)) := inS_of_good R hR (hG.py _ hπk)
      rw [PlaceCert.apx, getD_conjC _ hs]
      split_ifs
      · exact (intSub φ).mul_mem ((intSub φ).pow_mem hζS _) (hyS.getD _)
      · exact (intSub φ).zero_mem
    exact pext_ne_of_zp (hS k hk) (hS l hl) (zp_of_good R hR (hG.sep j hj k hk l hl i hi)) hne

end Pre

end Curves
