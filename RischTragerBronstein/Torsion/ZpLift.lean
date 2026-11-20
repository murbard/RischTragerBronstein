import RischTragerBronstein.Torsion.TestCert
import RischTragerBronstein.Algebraic.SupRedG
import RischTragerBronstein.Jacobian.CertCheckK

/-!
# Lifting data to `ℤ_p`

* `prod_eq_of_roots`: a monic polynomial of degree `n` over a domain with `n` distinct roots is the
  product of the linear factors;
* `hensel_Zp`, `split_Zp`: simple roots modulo `p` lift (Hensel), and a fibre that splits modulo
  `p` into simple roots splits over `ℤ_p`;
* `liftL`: the lift of a list of `p`-integral elements of a field `K` with a certified reduction
  (`RedValid`), with `toPoly_liftL_map` (to `ℚ_p`) and `toPoly_liftL_red` (to `𝔽_p`).
-/

open Polynomial

namespace Curves

open CPoly Sup

section Roots

lemma prod_eq_of_roots {R : Type*} [CommRing R] [IsDomain R] (f : R[X]) (hf : f.Monic) {n : ℕ}
    (hn : f.natDegree = n) (y : Fin n → R) (hy : Function.Injective y)
    (hr : ∀ k, f.eval (y k) = 0) : f = ∏ k, (X - C (y k)) := by
  classical
  set l : Multiset R := Finset.univ.val.map y with hl
  have hnd : l.Nodup := Multiset.Nodup.map hy Finset.univ.nodup
  have hle : l ≤ f.roots := by
    rw [Multiset.le_iff_subset hnd]
    intro a ha
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp ha
    exact (mem_roots hf.ne_zero).mpr (hr k)
  have hcl : Multiset.card l = n := by simp [hl]
  have heq : l = f.roots := Multiset.eq_of_le_of_card_le hle (by
    rw [hcl, ← hn]; exact card_roots' f)
  have hcard : Multiset.card f.roots = f.natDegree := by rw [← heq, hcl, hn]
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hf hcard, ← heq, hl, Multiset.map_map]
  rfl

end Roots

section Hensel

variable {p : ℕ} [Fact p.Prime]

/-- **Hensel** over `ℤ_p` with the reduction of the root. -/
lemma hensel_Zp (f : ℤ_[p][X]) (s : ZMod p) (hs : (f.map PadicInt.toZMod).eval s = 0)
    (hs' : ((derivative f).map PadicInt.toZMod).eval s ≠ 0) :
    ∃ z : ℤ_[p], f.eval z = 0 ∧ PadicInt.toZMod z = s := by
  set a : ℤ_[p] := (s.val : ℤ_[p])
  have ha : PadicInt.toZMod a = s := by
    simp only [a, map_natCast, ZMod.natCast_zmod_val]
  have hev : ∀ G : ℤ_[p][X], PadicInt.toZMod (G.aeval a) = (G.map PadicInt.toZMod).eval s := by
    intro G
    rw [aeval_def, eval_map, ← ha, hom_eval₂]
    rfl
  have h1 : ‖(f.aeval a : ℚ_[p])‖ < 1 := by
    rw [EllDV.norm_lt_one_iff_toZMod, hev]; exact hs
  have h2 : ‖((derivative f).aeval a : ℚ_[p])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp ?_)
    rw [EllDV.norm_lt_one_iff_toZMod, hev]; exact hs'
  obtain ⟨z, hz, hza, -⟩ := hensels_lemma (F := f) (a := a) (by
    change ‖(f.aeval a : ℚ_[p])‖ < ‖((derivative f).aeval a : ℚ_[p])‖ ^ 2
    rw [h2, one_pow]; exact h1)
  refine ⟨z, by rwa [aeval_def, Algebra.algebraMap_self, eval₂_id] at hz, ?_⟩
  have hlt : ‖((z - a : ℤ_[p]) : ℚ_[p])‖ < 1 := by
    have : ‖z - a‖ < 1 := by
      calc ‖z - a‖ < ‖(derivative f).aeval a‖ := hza
        _ = 1 := h2
    exact this
  rw [EllDV.norm_lt_one_iff_toZMod, map_sub, sub_eq_zero, ha] at hlt
  exact hlt

/-- **A fibre splitting modulo `p` into simple roots splits over `ℤ_p`.** -/
lemma split_Zp (f : ℤ_[p][X]) (hf : f.Monic) {n : ℕ} (hn : f.natDegree = n) (s : Fin n → ZMod p)
    (hsi : Function.Injective s) (hs : ∀ k, (f.map PadicInt.toZMod).eval (s k) = 0)
    (hs' : ∀ k, ((derivative f).map PadicInt.toZMod).eval (s k) ≠ 0) :
    ∃ y : Fin n → ℤ_[p], (∀ k, PadicInt.toZMod (y k) = s k) ∧ f = ∏ k, (X - C (y k)) := by
  choose y hy hys using fun k ↦ hensel_Zp f (s k) (hs k) (hs' k)
  refine ⟨y, hys, prod_eq_of_roots f hf hn y (fun k k' h ↦ hsi ?_) hy⟩
  rw [← hys, ← hys, h]

end Hensel

section Lift

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K]
variable (R : Sup.RedFns p K) (φ : K →+* ℚ_[p]) (hR : Sup.RedValid p R φ)

/-- The lift of a list of `p`-integral elements. -/
noncomputable def liftL (l : CPoly K) : CPoly ℤ_[p] := l.map (Sup.zL R φ hR)

/-- The lift of a bivariate list. -/
noncomputable def liftBL (W : BPoly K) : BPoly ℤ_[p] := W.map (liftL R φ hR)

omit [Field K] in
lemma toPoly_map_of_eq' {A B : Type*} [CommRing A] [CommRing B] (h : A →+* B) (f : K → A)
    (g : K → B) (l : List K) (hfg : ∀ c ∈ l, h (f c) = g c) :
    (CPoly.toPoly (l.map f)).map h = CPoly.toPoly (l.map g) := by
  rw [← Sup.toPoly_mapHom, List.map_map]
  congr 1
  exact List.map_congr_left fun c hc ↦ hfg c hc

lemma toPoly_liftL_map (l : CPoly K) (hok : ∀ c ∈ l, R.ok c = true) :
    (CPoly.toPoly (liftL R φ hR l)).map (algebraMap ℤ_[p] ℚ_[p]) = (CPoly.toPoly l).map φ := by
  rw [liftL, toPoly_map_of_eq' _ _ φ l fun c hc ↦ (Sup.zL_spec R φ hR (hok c hc)).1.symm,
    ← Sup.toPoly_mapHom]

lemma toPoly_liftL_red (l : CPoly K) (hok : ∀ c ∈ l, R.ok c = true) :
    (CPoly.toPoly (liftL R φ hR l)).map PadicInt.toZMod = CPoly.toPoly (l.map R.red) := by
  rw [liftL, toPoly_map_of_eq' _ _ R.red l fun c hc ↦ (Sup.zL_spec R φ hR (hok c hc)).2]

omit [Field K] in
lemma toB_map_of {A B : Type*} [CommRing A] [CommRing B] (h : A →+* B) (W : BPoly A)
    (W' : BPoly B) (hl : W.length = W'.length)
    (hW : ∀ i < W.length, (CPoly.toPoly (W.getD i [])).map h = CPoly.toPoly (W'.getD i [])) :
    (Sup.toB W).map (mapRingHom h) = Sup.toB W' := by
  induction W generalizing W' with
  | nil =>
    cases W' with
    | nil => simp
    | cons _ _ => simp at hl
  | cons a W ih =>
    cases W' with
    | nil => simp at hl
    | cons b W' =>
      simp only [Sup.toB_cons, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X,
        Polynomial.map_C, coe_mapRingHom]
      have h0 := hW 0 (by simp)
      simp only [List.getD_cons_zero] at h0
      rw [h0, ih W' (by simpa using hl) fun i hi ↦ by
        have := hW (i + 1) (by simp; omega)
        simpa using this]

lemma toB_liftBL_map (W : BPoly K) (hok : ∀ P ∈ W, ∀ c ∈ P, R.ok c = true) :
    (Sup.toB (liftBL R φ hR W)).map (mapRingHom (algebraMap ℤ_[p] ℚ_[p])) =
      (Sup.toB W).map (mapRingHom φ) := by
  have e : (Sup.toB W).map (mapRingHom φ) = Sup.toB (W.map fun P ↦ P.map φ) :=
    toB_map_of φ W _ (by simp) fun i hi ↦ by
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simpa using hi),
        List.getElem_map, Sup.toPoly_mapHom]
  rw [e]
  refine toB_map_of _ _ _ (by simp [liftBL]) fun i hi ↦ ?_
  have hi' : i < W.length := by simpa [liftBL] using hi
  rw [liftBL, List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map,
    toPoly_liftL_map R φ hR _ (hok _ (List.getElem_mem hi')),
    List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, Sup.toPoly_mapHom]

lemma toB_liftBL_red (W : BPoly K) (hok : ∀ P ∈ W, ∀ c ∈ P, R.ok c = true) :
    (Sup.toB (liftBL R φ hR W)).map (mapRingHom PadicInt.toZMod) =
      Sup.toB (W.map fun P ↦ P.map R.red) := by
  refine toB_map_of _ _ _ (by simp [liftBL]) fun i hi ↦ ?_
  have hi' : i < W.length := by simpa [liftBL] using hi
  rw [liftBL, List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map,
    toPoly_liftL_red R φ hR _ (hok _ (List.getElem_mem hi')),
    List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map]

end Lift

end Curves
