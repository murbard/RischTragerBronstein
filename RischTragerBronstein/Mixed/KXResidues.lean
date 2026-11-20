import RischTragerBronstein.Mixed.KXAllLevels

/-!
# The cubic decider reads only a finite prefix of its residue data

At level `m`, entries `0, …, m` specialize `x, t₀, …, tₘ₋₁`. All higher entries are irrelevant
to `redAtKF`, hence to the torsion tests and the complete cubic decision pipeline.
-/

open Polynomial

namespace Curves.MT

open CPoly Sup Curves.LT

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))]

/-- Reductions at level `m` read only the first `m + 1` residues. -/
theorem redKF_congr_prefix (p : ℕ) [Fact p.Prime] (s0 : ZMod p) (m : ℕ)
    {rs rt : ℕ → ZMod p} (h : ∀ j ≤ m, rs j = rt j) :
    redKF Fc p s0 rs m = redKF Fc p s0 rt m := by
  induction m with
  | zero => simp only [redKF, h 0 le_rfl]
  | succ m ih =>
    simp only [redKF, ih (fun j hj ↦ h j (by omega)), h (m + 1) le_rfl]

/-- The root search and the returned reduction use the same finite residue prefix. -/
theorem redAtKF_congr_prefix (m : ℕ) {rs rt : ℕ → ℕ}
    (h : ∀ j ≤ m, rs j = rt j) : redAtKF Fc m rs = redAtKF Fc m rt := by
  funext p
  unfold redAtKF
  split_ifs with hp
  · have : Fact p.Prime := ⟨hp⟩
    simp only [h 0 (Nat.zero_le m)]
    congr 1
    funext i
    exact redKF_congr_prefix Fc p i m (fun j hj ↦ by rw [h j hj])
  · rfl

/-- All residue dependence of the relation-search decider is through `redAtKF`. -/
theorem kxDecideDL_congr_red (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)
    (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (ps : List ℕ) (bound nmax : ℕ) {rs rt : ℕ → ℕ}
    (h : redAtKF Fc m rs = redAtKF Fc m rt) :
    kxDecideDL Fc ks lv m g A B kt l cs ps bound rs nmax =
      kxDecideDL Fc ks lv m g A B kt l cs ps bound rt nmax := by
  have ht : kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) ps bound rs =
      kxTorsC Fc ks m g A B kt l cs (fun fK ↦ localCert fK 2) ps bound rt := by
    funext T
    simp only [kxTorsC, h]
  simp only [kxDecideDL, kxDecideL, kxDecideC, kxSolveC, kxDecideDepC, kxSolveDepC,
    ht, kxTors0C, h]

/-- At any exponential level, the unified decider depends only on entries `0, …, m`. -/
theorem kxDecideNC_congr_prefix (c0 : CPoly ℚ)
    [Fact (Irreducible (toPoly (fKc [c0, [1]])))]
    (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)
    (m : ℕ) (g : LC m) (A B : GPoly (LC m)) (kt l : ℕ) (cs : List (LC m))
    (ps : List ℕ) (bound nmax kmax : ℕ) {rs rt : ℕ → ℕ}
    (h : ∀ j ≤ m, rs j = rt j) :
    kxDecideNC c0 ks lv m g A B kt l cs ps bound rs nmax kmax =
      kxDecideNC c0 ks lv m g A B kt l cs ps bound rt nmax kmax := by
  have hd := kxDecideDL_congr_red [c0, [1]] ks lv m g A B kt l cs ps bound nmax
    (redAtKF_congr_prefix [c0, [1]] m h)
  cases m with
  | zero => simp only [kxDecideNC, kxDecideNC0, kxDecideDK0, hd]
  | succ m => simp only [kxDecideNC, kxDecideNCS3, kxDecideNCS2, kxDecideNCS, hd]

end Curves.MT
