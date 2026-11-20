import RischTragerBronstein.Torsion.PlaceCompleteExt

/-!
# Prime certificates exist (1): evaluations and unit conditions under `pext`

Naturality of the evaluations `Kron.evalC`, `evalB` under the partial homomorphism `pext`, and the
unit conditions of the reduction library (`OrdUnit`, `SepUnit`, `UnitAt`, nodup of reductions) from
zero-or-unit (`ZP`) hypotheses on explicit elements.
-/

open Polynomial

namespace Curves

open CPoly Sup

section Eval

variable {F F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F']
  {S : Subring F} {g : S →+* F'}

lemma evalC_pext {a : F} (ha : a ∈ S) : ∀ (c : List F), InS S c →
    Kron.evalC c a ∈ S ∧ pext S g (Kron.evalC c a) = Kron.evalC (c.map (pext S g)) (pext S g a)
  | [], _ => ⟨S.zero_mem, by simp [Kron.evalC, pext_zero]⟩
  | x :: c, hc => by
    obtain ⟨hx, hc'⟩ := hc.of_cons
    obtain ⟨h1, h2⟩ := evalC_pext ha c hc'
    have e : Kron.evalC (x :: c) a = x + a * Kron.evalC c a := rfl
    have e' : Kron.evalC ((x :: c).map (pext S g)) (pext S g a) =
        pext S g x + pext S g a * Kron.evalC (c.map (pext S g)) (pext S g a) := rfl
    refine ⟨by rw [e]; exact S.add_mem hx (S.mul_mem ha h1), ?_⟩
    rw [e, e', pext_add hx (S.mul_mem ha h1), pext_mul ha h1, h2]

lemma evalB_pext {a b : F} (ha : a ∈ S) (hb : b ∈ S) : ∀ (W : List (List F)), InSB S W →
    evalB W a b ∈ S ∧
      pext S g (evalB W a b) = evalB (W.map (·.map (pext S g))) (pext S g a) (pext S g b)
  | [], _ => ⟨S.zero_mem, by simp [evalB, pext_zero]⟩
  | c :: W, hW => by
    have hc : InS S c := hW c List.mem_cons_self
    have hW' : InSB S W := fun P hP ↦ hW P (List.mem_cons_of_mem _ hP)
    obtain ⟨h1, h2⟩ := evalB_pext ha hb W hW'
    obtain ⟨h3, h4⟩ := evalC_pext (g := g) ha c hc
    have e : evalB (c :: W) a b = Kron.evalC c a + b * evalB W a b := rfl
    have e' : evalB ((c :: W).map (·.map (pext S g))) (pext S g a) (pext S g b) =
        Kron.evalC (c.map (pext S g)) (pext S g a) +
          pext S g b * evalB (W.map (·.map (pext S g))) (pext S g a) (pext S g b) := rfl
    refine ⟨by rw [e]; exact S.add_mem h3 (S.mul_mem hb h1), ?_⟩
    rw [e, e', pext_add h3 (S.mul_mem hb h1), pext_mul hb h1, h4, h2]

end Eval

section Units

variable {F F' : Type*} [Field F] [DecidableEq F] [Field F'] [DecidableEq F']
  {S : Subring F} {g : S →+* F'}

lemma pext_ne_zero_of_zp {v : F} (hv : ZP S v) (h0 : v ≠ 0) : pext S g v ≠ 0 :=
  fun h ↦ h0 ((pext_eq_zero_iff hv).mp h)

lemma pext_ne_of_zp {v w : F} (hv : v ∈ S) (hw : w ∈ S) (hz : ZP S (v - w)) (hne : v ≠ w) :
    pext S g v ≠ pext S g w := by
  intro h
  have := pext_sub (g := g) hv hw
  rw [h, sub_self] at this
  exact pext_ne_zero_of_zp hz (sub_ne_zero.mpr hne) this

lemma ordUnit_of {P : List F} (h : ZP S (P.getD (ordC P) 0)) : OrdUnit S g P :=
  fun hlt ↦ pext_ne_zero_of_zp h (getD_ordC P hlt)

lemma sepUnit_of {ys : List (List F)} {prec : ℕ} (hys : InSB S ys) (hsep : sepCheck ys prec = true)
    (hZ : ∀ k < ys.length, ∀ l < ys.length, ∀ i < prec,
      ZP S ((ys.getD k []).getD i 0 - (ys.getD l []).getD i 0)) :
    SepUnit (S := S) (g := g) ys prec := by
  intro k l hkl hk hl
  simp only [sepCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true] at hsep
  rcases hsep k hk l hl with h | ⟨i, hi, hne⟩
  · exact absurd h hkl
  exact ⟨i, hi, pext_ne_of_zp ((hys.getD k).getD i) ((hys.getD l).getD i) (hZ k hk l hl i hi) hne⟩

lemma unitAt_of {Dc : List F} {a : F} {N : ℕ}
    (h : ((compC Dc (shiftC a N)).getD (muD Dc a N) 0)⁻¹ ∈ S) : UnitAt (S := S) Dc a N := h

lemma nodup_pext {l : List F} (hl : InS S l) (hnd : l.Nodup)
    (hZ : ∀ i < l.length, ∀ j < l.length, ZP S (l.getD i 0 - l.getD j 0)) :
    (l.map (pext S g)).Nodup := by
  rw [List.nodup_iff_injective_get] at hnd ⊢
  intro i j hij
  simp only [List.get_eq_getElem, List.getElem_map] at hij
  by_contra hne
  have hne' : l[(i : ℕ)]'(by simpa using i.2) ≠ l[(j : ℕ)]'(by simpa using j.2) := fun h ↦
    hne (Fin.ext (by
      have := hnd (a₁ := ⟨i, by simpa using i.2⟩) (a₂ := ⟨j, by simpa using j.2⟩) (by simpa using h)
      simpa using congrArg Fin.val this))
  have hz := hZ i (by simpa using i.2) j (by simpa using j.2)
  rw [List.getD_eq_getElem _ _ (by simpa using i.2), List.getD_eq_getElem _ _ (by simpa using j.2)] at hz
  exact pext_ne_of_zp (hl _ (List.getElem_mem _)) (hl _ (List.getElem_mem _)) hz hne' hij

end Units

end Curves
