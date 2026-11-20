import RischTragerBronstein.Torsion.TorsOrdExist4

/-!
# The place certificates `PcE tx` refine each other

Raising the precision slack `tx` of the place certificate `PcE` keeps the fibres, the places, the
roots and the multiplicities, and only lengthens the approximations of the place series
(**`PcE_refines`**): exactly the hypotheses of `exists_placeWit_ext`, so one multiplier `m_p`
serves all `PcE tx`.

`assemble_refines`: assembled certificates of pointwise refining local data refine each other.
-/

open Polynomial HahnSeries EllQuad.QCoords

namespace Curves

open CPoly Sup

section Gen

variable {F : Type*} [Field F] [DecidableEq F]

/-- Refinement of local place entries `(e, y, prec)`: the approximation is extended. -/
def PlsRef (a' a : ℕ × CPoly F × ℕ) : Prop :=
  a'.1 = a.1 ∧ a.2.2 ≤ a'.2.2 ∧ a.2.1 <+: a'.2.1

/-- Refinement of global place entries `(j, e, y, prec)`. -/
def PlRef (x' x : ℕ × ℕ × CPoly F × ℕ) : Prop :=
  x'.1 = x.1 ∧ PlsRef x'.2 x.2

/-- Refinement of local data. -/
def LocRef (L' L : LocPlaces F) : Prop :=
  L'.α = L.α ∧ L'.N = L.N ∧ L'.rts = L.rts ∧ L'.Γ = L.Γ ∧ List.Forall₂ PlsRef L'.pls L.pls

lemma plsRef_refl (a : ℕ × CPoly F × ℕ) : PlsRef a a := ⟨rfl, le_rfl, List.prefix_refl _⟩

lemma getD_of_prefix {l l' : List F} (h : l <+: l') {i : ℕ} (hi : i < l.length) :
    l'.getD i 0 = l.getD i 0 := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

lemma locRef_refl (L : LocPlaces F) : LocRef L L :=
  ⟨rfl, rfl, rfl, rfl, List.forall₂_same.mpr fun a _ ↦ plsRef_refl a⟩

lemma forall₂_getD {α β : Type*} {R : α → β → Prop} {l' : List α} {l : List β}
    (h : List.Forall₂ R l' l) {d' : α} {d : β} (hd : R d' d) : ∀ i, R (l'.getD i d') (l.getD i d) := by
  induction h with
  | nil => intro i; simpa using hd
  | cons hab _ ih =>
    intro i
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

lemma forall₂_map_eq {α β γ : Type*} {R : α → β → Prop} {l' : List α} {l : List β}
    (h : List.Forall₂ R l' l) (f : α → γ) (g : β → γ) (hfg : ∀ a b, R a b → f a = g b) :
    l'.map f = l.map g := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [hfg _ _ hab, ih]

lemma offF_congr {β γ : Type*} {P : List (List β)} {P' : List (List γ)}
    (h : P.map List.length = P'.map List.length) (j : ℕ) : offF P j = offF P' j := by
  unfold offF; rw [List.map_take, List.map_take, h]

/-- **Assembled refinements.** -/
theorem assemble_refines {Ls' Ls : List (LocPlaces F)} (h : List.Forall₂ LocRef Ls' Ls) (c : ℕ) :
    (assemble Ls' c).fib = (assemble Ls c).fib ∧ (assemble Ls' c).rt = (assemble Ls c).rt ∧
      (assemble Ls' c).Γp = (assemble Ls c).Γp ∧ (assemble Ls' c).cΓ = (assemble Ls c).cΓ ∧
      (assemble Ls' c).pl.length = (assemble Ls c).pl.length ∧
      ∀ π < (assemble Ls c).pl.length, (assemble Ls' c).pj π = (assemble Ls c).pj π ∧
        (assemble Ls' c).pe π = (assemble Ls c).pe π ∧ (assemble Ls c).pp π ≤ (assemble Ls' c).pp π ∧
        (assemble Ls c).py π <+: (assemble Ls' c).py π := by
  have hlen := h.length_eq
  have hj : ∀ j, LocRef (Ls'.getD j locDef) (Ls.getD j locDef) :=
    forall₂_getD h (locRef_refl locDef)
  -- the blocks of places
  have hB : List.Forall₂ (List.Forall₂ PlRef) (plBlocks Ls') (plBlocks Ls) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp [plBlocks, hlen], fun j h1 h2 ↦ ?_⟩
    simp only [plBlocks, List.get_eq_getElem, List.getElem_map, List.getElem_range,
      LocPlaces.placeList]
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact (hj j).2.2.2.2.imp fun a' a hr ↦ ⟨rfl, hr⟩
  have hBl : (plBlocks Ls').map List.length = (plBlocks Ls).map List.length :=
    forall₂_map_eq hB _ _ fun _ _ hr ↦ hr.length_eq
  have hpl : List.Forall₂ PlRef (assemble Ls' c).pl (assemble Ls c).pl := List.rel_flatten hB
  refine ⟨?_, ?_, ?_, rfl, hpl.length_eq, fun π _ ↦ ?_⟩
  · exact forall₂_map_eq h _ _ fun a b hr ↦ by rw [hr.1, hr.2.1]
  · simp only [assemble, hlen]
    refine List.map_congr_left fun j _ ↦ ?_
    rw [(hj j).2.2.1, offF_congr hBl]
  · exact congrArg List.flatten (forall₂_map_eq h _ _ fun a b hr ↦ hr.2.2.2.1)
  · have hr := forall₂_getD hpl (d' := (0, 1, [], 0)) (d := (0, 1, [], 0))
      ⟨rfl, plsRef_refl _⟩ π
    exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2⟩

end Gen

section PcE

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field L] [CharZero L] [Algebra C L]

namespace CurveData

variable (S : CurveData C L) (P : CurveProb F) {ψ : F →+* C}
  (hSF : S.F = (toB P.Fc).map (mapRingHom ψ)) (hV : P.ValidFacts)
  (hζ : ∀ ac ∈ P.pts, ∃ ζF : F, IsPrimitiveRoot (ψ ζF) ac.2.N) (j₀ : Fin (dim F))

lemma prefix_range_map {α : Type*} (f : ℕ → α) {a b : ℕ} (h : a ≤ b) :
    (List.range a).map f <+: (List.range b).map f := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.map_append]
  exact List.prefix_append _ _

lemma lpj_ref (j : Fin P.pts.length) (Γf : Fin S.F.natDegree → ℕ) {t t' : ℕ} (htt : t ≤ t') :
    LocRef (S.lpj P hSF hV hζ j Γf t') (S.lpj P hSF hV hζ j Γf t) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  simp only [lpj, SplitFibre.locPlaces]
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro π _
  refine ⟨rfl, ?_, ?_⟩
  · simp only [SplitFibre.ppF]; omega
  · simp only [SplitFibre.yF]
    exact prefix_range_map _ (by simp only [SplitFibre.ppF]; omega)

/-- **`PcE t'` refines `PcE t`** for `t ≤ t'`. -/
theorem PcE_refines {t t' : ℕ} (htt : t ≤ t') :
    let D' := S.PcE P hSF hV hζ j₀ t'
    let D := S.PcE P hSF hV hζ j₀ t
    D'.fib = D.fib ∧ D'.rt = D.rt ∧ D'.Γp = D.Γp ∧ D'.cΓ = D.cΓ ∧ D'.pl.length = D.pl.length ∧
      ∀ π < D.pl.length, D'.pj π = D.pj π ∧ D'.pe π = D.pe π ∧ D.pp π ≤ D'.pp π ∧
        D.py π <+: D'.py π := by
  refine assemble_refines ?_ _
  rw [List.forall₂_iff_get]
  refine ⟨by simp [Ls], fun j h1 h2 ↦ ?_⟩
  simp only [Ls, List.get_eq_getElem, List.getElem_ofFn]
  exact S.lpj_ref P hSF hV hζ _ _ htt

end CurveData

end PcE

end Curves
