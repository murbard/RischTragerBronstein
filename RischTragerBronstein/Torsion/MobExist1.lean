import RischTragerBronstein.Torsion.BasePtsAlg
import RischTragerBronstein.Torsion.DecideEnum

/-!
# Möbius transformations in the certificate search (1): base change and certificates

* list operations commute with ring homomorphisms (`compC_map`, `shiftB_map`, `stripB_map`, …),
  derived from the reduction library (`pext` for the whole field);
* **`baseChange_mobT`**: the Möbius transform commutes with base change;
* **`mobCheck_baseChange`**: the Möbius check over a number field from the conditions over `F`;
* **`certExists_of_mob`**: a certificate (without Möbius option) for the transformed problem over
  `ℚ` gives a certificate for the original problem (with the Möbius option).
-/

open Polynomial

namespace Curves

open CPoly Sup

section Maps

variable {F F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F'] (φ : F →+* F')

lemma pext_top_eq : pext (⊤ : Subring F) (φ.comp (⊤ : Subring F).subtype) = ⇑φ :=
  funext fun x ↦ by rw [pext_of_mem (Subring.mem_top x)]; rfl

lemma inS_top (l : List F) : InS (⊤ : Subring F) l := fun c _ ↦ Subring.mem_top c

lemma inSB_top (W : List (List F)) : InSB (⊤ : Subring F) W := fun P _ ↦ inS_top P

lemma compC_map (c s : List F) : (compC c s).map φ = compC (c.map φ) (s.map φ) := by
  have := (compC_pext (S := ⊤) (g := φ.comp (⊤ : Subring F).subtype) s (inS_top s) c
    (inS_top c)).2
  rwa [pext_top_eq] at this

lemma shiftC_map (a : F) (N : ℕ) : (shiftC a N).map φ = shiftC (φ a) N := by
  have := (shiftC_pext (S := ⊤) (g := φ.comp (⊤ : Subring F).subtype) (Subring.mem_top a) N).2
  rwa [pext_top_eq] at this

lemma mul_map (p q : List F) : (mul p q).map φ = mul (p.map φ) (q.map φ) := by
  have := (mul_pext (S := ⊤) (g := φ.comp (⊤ : Subring F).subtype) p q (inS_top p)
    (inS_top q)).2
  rwa [pext_top_eq] at this

lemma xPowC_map (N : ℕ) : (xPowC N : List F).map φ = xPowC N := by
  have := (xPowC_pext (S := ⊤) (g := φ.comp (⊤ : Subring F).subtype) N).2
  rwa [pext_top_eq] at this

lemma smulB_map (c : List F) (W : List (List F)) :
    (smulB c W).map (·.map φ) = smulB (c.map φ) (W.map (·.map φ)) := by
  have := (smulB_pext (S := ⊤) (g := φ.comp (⊤ : Subring F).subtype) c (inS_top c) W
    (inSB_top W)).2
  rwa [pext_top_eq] at this

lemma shiftB_map (W : BPoly F) (e : F) :
    shiftB (W.map (·.map φ)) (φ e) = (shiftB W e).map (·.map φ) := by
  simp only [shiftB, List.map_map]
  refine List.map_congr_left fun c _ ↦ ?_
  simp only [Function.comp_apply, compC_map, shiftC_map]

lemma stripB_map (W : BPoly F) : stripB (W.map (·.map φ)) = (stripB W).map (·.map φ) := by
  simp only [stripB, ← List.map_reverse, List.dropWhile_map]
  have e : ((fun P : CPoly F' ↦ isZero P) ∘ fun x ↦ List.map φ x) = fun P ↦ isZero P :=
    funext fun P ↦ by simp [isZero_map]
  rw [e]

lemma trim_map (P : CPoly F) : trim (P.map φ) = (trim P).map φ := by
  simp only [trim, ← List.map_reverse, List.dropWhile_map]
  have e : ((fun a : F' ↦ decide (a = 0)) ∘ φ) = fun a ↦ decide (a = 0) :=
    funext fun a ↦ by simp [map_eq_zero_iff φ φ.injective]
  rw [e]

lemma mobA_map (W : BPoly F) (e : F) (k DA : ℕ) :
    mobA (W.map (·.map φ)) (φ e) k DA = (mobA W e k DA).map (·.map φ) := by
  rw [mobA, mobA, shiftB_map, invB_map, ← stripB_map, List.map_map]
  congr 1
  rw [show ([-1] : CPoly F') = ([-1] : CPoly F).map φ by simp, ← smulB_map, List.map_map]
  refine List.map_congr_left fun c _ ↦ ?_
  simp only [Function.comp_apply, trim_map]

end Maps

section Mob

variable {F F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F'] (φ : F →+* F')

/-- **The Möbius transform commutes with base change.** -/
lemma baseChange_mobT (P0 : CurveProb F) (e : F) (k₀ DA k' : ℕ) (pts0 : List (F' × BranchCert F'))
    (inf0 : BranchCert F') (pts : List (F' × BranchCert F')) (inf : BranchCert F')
    (pts1 : List (F × BranchCert F)) (inf1 : BranchCert F) :
    (P0.baseChange φ P0.k pts0 inf0).mobT (φ e) k₀ DA k' pts inf =
      (P0.mobT e k₀ DA k' pts1 inf1).baseChange φ k' pts inf := by
  simp only [CurveProb.mobT, CurveProb.baseChange, CurveProb.mk.injEq, true_and, and_true]
  refine ⟨?_, ?_, ?_⟩
  · rw [shiftB_map, invB_map]
  · rw [mobA_map]
  · rw [mul_map, xPowC_map, ← reflectC_map, compC_map, shiftC_map, List.length_map]

/-- **The Möbius check after base change.** -/
lemma mobCheck_baseChange (P0 : CurveProb F) (e : F) (k₀ DA k' : ℕ)
    (pts0 : List (F' × BranchCert F')) (inf0 : BranchCert F') (pts : List (F' × BranchCert F'))
    (inf : BranchCert F') (hF : invOKb k₀ (k₀ * P0.n) (shiftB P0.Fc e) = true)
    (hA : invOKb k₀ DA (shiftB P0.A e) = true)
    (hl : (compC P0.D (shiftC e 1)).length ≤ P0.D.length - 1 + 1) (hDA : P0.D.length - 1 ≤ DA + 2) :
    mobCheck (P0.baseChange φ P0.k pts0 inf0)
      ((P0.baseChange φ P0.k pts0 inf0).mobT (φ e) k₀ DA k' pts inf) (φ e) k₀ DA = true := by
  simp only [mobCheck, CurveProb.mobT, CurveProb.baseChange, Bool.and_eq_true, decide_eq_true_eq,
    and_true, true_and]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [shiftB_map, invOKb_map]; exact hF
  · rw [shiftB_map, invOKb_map]; exact hA
  · refine decide_eq_true ?_
    rw [List.length_map, ← shiftC_map, ← compC_map, List.length_map]; exact hl
  · refine decide_eq_true ?_
    rw [List.length_map]; exact hDA

end Mob

end Curves
