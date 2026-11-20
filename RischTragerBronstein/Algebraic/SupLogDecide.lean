import RischTragerBronstein.Algebraic.SupLogComplete

/-!
# The superelliptic logarithmic-part decision procedure: correctness

`superLogDecide_spec`: for `∫ (B(x, y) + B₁(x, y)/f(x) + ∑ᵢ Gᵢ(x, y)/(x − aᵢ)) dx` on `yⁿ = f(x)`,
every answer of `superLogDecide` (given a correct torsion oracle) is correct:
`some true` iff the integral is elementary.
-/

open Polynomial CPoly Differential IntermediateField

namespace Sup

section Glue

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
  [Differential C] [Differential L] [DifferentialAlgebra C L]

open EllQuad.QCoords Differential.SuperData

/-- The concrete integrand in the superelliptic function field. -/
lemma hInt_coe (S : SuperData C L) (ψ : F →+* C) (f : CPoly F) {n : ℕ} (hSn : S.n = n)
    (hSp : S.p = (toPoly f).map ψ) {m : ℕ} (a : Fin m → F) (B B₁ : BPoly F)
    (G : Fin m → BPoly F) (hBn : B.length ≤ n) (hB₁n : B₁.length ≤ n)
    (hGn : ∀ i, (G i).length ≤ n) :
    ((S.hInt (mapB ψ B) (mapB ψ B₁) (fun i ↦ ψ (a i)) fun i ↦ mapB ψ (G i) :
      C⟮S.x⟯⟮S.y⟯) : L) = integrandE ψ S.x S.y f B B₁ a G := by
  have hdegB : ∀ (W : BPoly F), W.length ≤ n → ∀ i, S.n ≤ i → (toB W).coeff i = 0 :=
    fun W hW i hi ↦ toB_coeff_ge W hW i (hSn ▸ hi)
  simp only [hInt, IntermediateField.coe_add, IntermediateField.coe_mul,
    IntermediateField.coe_inv, IntermediateField.coe_sum, S.polyX_coe,
    elemW_map_coe S ψ _ (hdegB B hBn), elemW_map_coe S ψ _ (hdegB B₁ hB₁n),
    fun i ↦ elemW_map_coe S ψ _ (hdegB (G i) (hGn i)), div_eq_mul_inv, integrandE]
  rw [hSp]
  simp [exC, aeval_C]

end Glue

section Hom

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]
variable {Kc E Cc L : Type*} [Field Kc] [Field E] [Algebra Kc E] [Field Cc] [Field L] [Algebra Cc L]
  [Differential Kc] [Differential E] [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]
  [Differential Cc] [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

lemma integrandE_hom (ι : F →+* Kc) (φ : Kc →+* Cc) (jE : E →+* L)
    (hj : ∀ c : Kc, jE (algebraMap Kc E c) = algebraMap Cc L (φ c)) (x y : E) (f : CPoly F)
    {m : ℕ} (B B₁ : BPoly F) (a : Fin m → F) (G : Fin m → BPoly F) :
    jE (integrandE ι x y f B B₁ a G) = integrandE (φ.comp ι) (jE x) (jE y) f B B₁ a G := by
  have hexC : ∀ P : CPoly F, jE (exC ι x P) = exC (φ.comp ι) (jE x) P := by
    intro P
    have := evalE_hom ι φ jE hj x y (Polynomial.C (toPoly P))
    rwa [evalE_C, evalE_C] at this
  simp only [integrandE, map_add, map_div₀, map_sum, map_sub, evalE_hom ι φ jE hj, hexC, hj,
    RingHom.coe_comp, Function.comp_apply]

end Hom

section Main

universe u

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] [EllQuad.QCoords F]

open EllQuad.QCoords

lemma logJ_spec {m : ℕ} (f : CPoly F) (n : ℕ) (ζ : F) (a b : Fin m → F) (G : Fin m → BPoly F)
    (tors : List (F × F × ℕ) → Option (Option ℕ)) (j : Fin (dim F)) {NW : ℕ × BPoly F}
    (h : logJ f n ζ a b G tors j = some NW) :
    torsJ n ζ a b G tors j = some (some NW.1) ∧
      witW f n (f.length - 1) (ptA n a) (ptB n ζ b) (mqJ n ζ a b G j) NW.1 = some NW.2 := by
  unfold logJ at h
  split at h
  · rename_i N hN
    obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨hN, hW⟩
  · cases h

variable {Kc E : Type u} [Field Kc] [Field E] [Algebra Kc E] [Differential Kc] [Differential E]
  [DifferentialAlgebra Kc E] [CharZero Kc] [CharZero E]

set_option maxHeartbeats 4000000 in
/-- **Correctness of `superLogDecide`**: given a correct torsion oracle, every answer is
correct — `some true` iff `∫ (B + B₁/f + ∑ Gᵢ/(x − aᵢ)) dx` is elementary. -/
theorem superLogDecide_spec (hC : ∀ c : Kc, c′ = 0) (x y : E) (hx : x′ = 1) (ι : F →+* Kc)
    (f : CPoly F) {n : ℕ} (hn : 0 < n) (hsq : Squarefree (toPoly f))
    (hdeg : (toPoly f).natDegree = f.length - 1) (hpd : 0 < f.length - 1)
    (hcop : Nat.Coprime n (f.length - 1)) (hy : y ^ n = aeval x ((toPoly f).map ι))
    (hgen : ∀ z : E, z ∈ Kc⟮x⟯⟮y⟯) {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (tors : List (F × F × ℕ) → Option (Option ℕ)) (htors : TorsSpecN f n tors)
    (B B₁ : BPoly F) (hBn : B.length ≤ n) (hB₁n : B₁.length ≤ n) (hB₁0 : (toB B₁).coeff 0 = 0)
    {m : ℕ} (a b : Fin m → F) (G : Fin m → BPoly F) (hGn : ∀ i, (G i).length ≤ n)
    (ha : Function.Injective a) (hb : ∀ i, b i ≠ 0) (hbf : ∀ i, b i ^ n = (toPoly f).eval (a i))
    (ans : Bool) (h : superLogDecide f n ζ tors B B₁ a b G = some ans) :
    ans = true ↔ HasElementaryIntegral (integrandE ι x y f B B₁ a G) := by
  have hpd' : 0 < (toPoly f).natDegree := hdeg ▸ hpd
  have hsqK : Squarefree ((toPoly f).map ι) :=
    ((PerfectField.separable_iff_squarefree.mpr hsq).map).squarefree
  have hpK : 0 < ((toPoly f).map ι).natDegree := by
    rw [natDegree_map_eq_of_injective ι.injective]; exact hpd'
  have hvalidF : ∀ q, ptB n ζ b q ≠ 0 ∧ ptB n ζ b q ^ n = (toPoly f).eval (ptA n a q) :=
    fun q ↦ ⟨pt_ne_zero hn hζ b hb q, pt_valid _ hζ a b hbf q⟩
  have hinjF := pt_injective hζ a b ha hb
  unfold superLogDecide at h
  rw [dif_pos hn] at h
  split_ifs at h with hA hB hAll
  · -- a non-torsion component: not elementary
    simp only [Option.some.injEq] at h; subst h
    simp only [Bool.false_eq_true, false_iff]
    intro hel
    obtain ⟨j, -, hj⟩ := List.any_eq_true.mp hB
    have hj' : torsJ n ζ a b G tors j = some none := by simpa using hj
    refine super_lift hC x y hx n hn ((toPoly f).map ι) hsqK hpK hy hgen _ hel ?_
    intro Cc L _ _ _ _ _ _ _ _ φ jE SL hCc hxL hconst hSx hSy hSn hSp hjd hjc hEs v hv ιI sI d w
      hd hw heqL
    set ψ : F →+* Cc := φ.comp ι with hψ
    have hSp' : SL.p = (toPoly f).map ψ := by rw [hSp, Polynomial.map_map]
    classical
    set c : ιI → Cc := fun i ↦ if hi : (d i)′ = 0 then Classical.choose (hconst _ hi) else 0
      with hc_def
    have hc : ∀ i ∈ sI, algebraMap Cc L (c i) = d i := by
      intro i hi
      simp only [hc_def, dif_pos (hd i hi)]
      exact Classical.choose_spec (hconst _ (hd i hi))
    set u' : ιI → L := fun i ↦ if i ∈ sI then w i else 1 with hu'_def
    have hu : ∀ i, u' i ∈ Cc⟮SL.x⟯⟮SL.y⟯ := by
      intro i; simp only [hu'_def]; split_ifs with hi
      · exact (hw i hi).2
      · exact one_mem _
    have hu0 : ∀ i, u' i ≠ 0 := by
      intro i; simp only [hu'_def]; split_ifs with hi
      · exact (hw i hi).1
      · exact one_ne_zero
    have heqA : ((SL.hInt (mapB ψ B) (mapB ψ B₁) (fun i ↦ ψ (a i)) fun i ↦ mapB ψ (G i) :
        Cc⟮SL.x⟯⟮SL.y⟯) : L) = v′ + ∑ i ∈ sI, algebraMap Cc L (c i) * ((u' i)′ / u' i) := by
      rw [hInt_coe SL ψ f hSn hSp' a B B₁ G hBn hB₁n hGn, hSx, hSy, ← integrandE_hom ι φ jE hjc,
        heqL]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [hu'_def, if_pos hi, hc i hi]
      rfl
    obtain ⟨N, hN1, hP⟩ := abel_component SL hCc hxL ψ f hSn hSp' hdeg hcop hζ a b ha hb hbf B
      B₁ G hGn sI c u' hu hu0 v hv heqA j
    exact (htors _ _ _ _ hvalidF hinjF).2 hj' N hN1 hP
  · -- every component is torsion: the exactness test decides
    have hsome : ∀ j, (logJ f n ζ a b G tors j).isSome := fun j ↦ by
      simpa using List.all_eq_true.mp hAll j (List.mem_finRange j)
    set NW : Fin (dim F) → ℕ × BPoly F :=
      fun j ↦ (logJ f n ζ a b G tors j).getD (1, [[1]]) with hNW_def
    have hNWs : ∀ j, logJ f n ζ a b G tors j = some (NW j) := fun j ↦ by
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hsome j)
      simp only [hNW_def, ht, Option.getD_some]
    have hNW : ∀ j, 1 ≤ (NW j).1 ∧ toB (NW j).2 ≠ 0 ∧
        (∀ i c, ((toB (NW j).2).coeff i).coeff c ≠ 0 →
          i < n ∧ n * c + (f.length - 1) * i ≤ (NW j).1 * ∑ q, mqJ n ζ a b G j q) ∧
        ∀ q, VanishAtN (toPoly f) n (toB (NW j).2) (ptA n a q) (ptB n ζ b q)
          ((NW j).1 * mqJ n ζ a b G j q) := by
      intro j
      obtain ⟨ht, hw⟩ := logJ_spec f n ζ a b G tors j (hNWs j)
      obtain ⟨hN1, -⟩ := (htors _ _ _ _ hvalidF hinjF).1 _ ht
      obtain ⟨h0, hs, hv⟩ := witW_spec f n hn (f.length - 1) (ptA n a) (ptB n ζ b)
        (mqJ n ζ a b G j) (NW j).1 (fun q ↦ ⟨mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne')
          (pow_ne_zero _ (hvalidF q).1), (hvalidF q).2⟩) hw
      exact ⟨hN1, h0, hs, hv⟩
    have hdegW : ∀ j, toB (NW j).2 ≠ 0 ∧ ∀ i, n ≤ i → (toB (NW j).2).coeff i = 0 := by
      intro j
      refine ⟨(hNW j).2.1, fun i hi ↦ ?_⟩
      by_contra h0
      obtain ⟨c, hc⟩ : ∃ c, ((toB (NW j).2).coeff i).coeff c ≠ 0 := by
        by_contra h1; push_neg at h1; exact h0 (Polynomial.ext h1)
      have := ((hNW j).2.2.1 i c hc).1
      omega
    simp only [Option.some.injEq] at h
    subst h
    constructor
    · intro hs
      obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.mp hs
      exact superLog_sound hC x y hx ι f hn hsq hpd' hy ζ a b G B B₁ NW hdegW _ hcs
    · intro hel
      by_contra hns
      have hnone : exactTest f n hn (logMT f n ζ a b G B B₁ NW).1 (logMT f n ζ a b G B B₁ NW).2
          (basisN n (f.length - 1) (boundH f n B B₁ G + n)) = none := by
        simpa using hns
      refine super_lift hC x y hx n hn ((toPoly f).map ι) hsqK hpK hy hgen _ hel ?_
      intro Cc L _ _ _ _ _ _ _ _ φ jE SL hCc hxL hconst hSx hSy hSn hSp hjd hjc hEs v hv ιI sI d w
        hd hw heqL
      set ψ : F →+* Cc := φ.comp ι with hψ
      have hSp' : SL.p = (toPoly f).map ψ := by rw [hSp, Polynomial.map_map]
      have heqC : ((SL.hInt (mapB ψ B) (mapB ψ B₁) (fun i ↦ ψ (a i)) fun i ↦ mapB ψ (G i) :
          Cc⟮SL.x⟯⟮SL.y⟯) : L) = v′ + ∑ i ∈ sI, d i * logDeriv (w i) := by
        rw [hInt_coe SL ψ f hSn hSp' a B B₁ G hBn hB₁n hGn, hSx, hSy,
          ← integrandE_hom ι φ jE hjc, heqL]
      exact exact_complete SL hCc hxL hconst ψ f hn hSn hSp' hdeg hcop hζ a b ha hb hbf B B₁ G
        hBn hB₁n hB₁0 hGn NW hNW v hv sI d w hd hw heqC hnone

end Main

end Sup
