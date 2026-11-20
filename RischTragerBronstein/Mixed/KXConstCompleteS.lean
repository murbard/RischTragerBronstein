import RischTragerBronstein.Mixed.KXMWDecideSK
import RischTragerBronstein.Mixed.CodeWFS
import RischTragerBronstein.Mixed.KFConstTail
import RischTragerBronstein.Mixed.KXCertBridgeSRev

/-!
# The structural parts of the level-`m + 1` checks pass on constant-curve data

Constant fractions over `Kₘ` with rational values (`IsConstFrS`), closed under the operations;
the scaling `mwUS` and the model `AFrS`, `BFrS` of a curve with rational coefficients are rational
constants, read off by `polyOfS` (`polyOfS_head`). Hence `kxChkC0S` / `kxChkT0S` pass on valid
data (`kxChkC0S_true`, `kxChkT0S_true`).
-/

open Polynomial

namespace Curves.MT

open CPoly Sup Curves.LT FFHeight Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

section Gen

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- Constant fractions with a rational value. -/
def IsConstFrS (f : Fr K) (c : ℚ) : Prop := Fr.ok f ∧ Fr.val f = algebraMap ℚ (RatFunc K) c

lemma constFrS_mul {f g : Fr K} {a b : ℚ} (hf : IsConstFrS f a) (hg : IsConstFrS g b) :
    IsConstFrS (Fr.mul f g) (a * b) :=
  ⟨Fr.ok_mul hf.1 hg.1, by rw [Fr.val_mul hf.1 hg.1, hf.2, hg.2, map_mul]⟩

lemma constFrS_sub {f g : Fr K} {a b : ℚ} (hf : IsConstFrS f a) (hg : IsConstFrS g b) :
    IsConstFrS (Fr.sub f g) (a - b) :=
  ⟨Fr.ok_sub hf.1 hg.1, by rw [Fr.val_sub hf.1 hg.1, hf.2, hg.2, map_sub]⟩

lemma constFrS_add {f g : Fr K} {a b : ℚ} (hf : IsConstFrS f a) (hg : IsConstFrS g b) :
    IsConstFrS (Fr.add f g) (a + b) :=
  ⟨Fr.ok_add hf.1 hg.1, by rw [Fr.val_add hf.1 hg.1, hf.2, hg.2, map_add]⟩

lemma constFrS_smulC {f : Fr K} {a : ℚ} (c : ℚ) (hf : IsConstFrS f a) :
    IsConstFrS (Fr.smulC (c : K) f) (c * a) :=
  ⟨Fr.ok_smulC _ hf.1, by
    rw [Fr.val_smulC, hf.2, map_mul, map_ratCast, eq_ratCast (algebraMap ℚ (RatFunc K)) c]⟩

lemma constFrS_ofPoly (c : ℚ) : IsConstFrS (Fr.ofPoly [(c : K)]) c :=
  ⟨Fr.ok_ofPoly _, by
    rw [Fr.val_ofPoly]; simp [CPoly.toPoly, RatFunc.algebraMap_C, map_ratCast]⟩

lemma constFrS_one : IsConstFrS (Fr.ofPoly [(1 : K)]) 1 := by
  have := constFrS_ofPoly (K := K) 1
  simpa using this

lemma constFrS_val {f : Fr K} {c : ℚ} (hf : IsConstFrS f c) :
    Fr.val f = algebraMap K (RatFunc K) (c : K) := by
  rw [hf.2, eq_ratCast (algebraMap ℚ _), map_ratCast]

lemma dropWhile_zeros_appendK (t : List K) (ht : ∀ x ∈ t, x = 0) (l : List K) :
    (t ++ l).dropWhile (fun x ↦ decide (x = 0)) = l.dropWhile (fun x ↦ decide (x = 0)) := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    rw [List.cons_append, List.dropWhile_cons, if_pos (by simp [ht a List.mem_cons_self])]
    exact ih fun x hx ↦ ht x (List.mem_cons_of_mem _ hx)

lemma trim_of_isConstK (p : CPoly K) (h : isConstK p = true) :
    CPoly.trim p = if p.headD 0 = 0 then [] else [p.headD 0] := by
  rcases p with _ | ⟨c, t⟩
  · simp [CPoly.trim]
  · have ht : ∀ x ∈ t, x = 0 := by
      simpa [isConstK, List.all_eq_true] using h
    simp only [CPoly.trim, List.reverse_cons, List.headD_cons]
    rw [dropWhile_zeros_appendK _ (fun x hx ↦ ht x (List.mem_reverse.mp hx))]
    by_cases hc : c = 0 <;> simp [hc]

/-- The reduced denominator of a constant fraction is a non-zero rational constant. -/
lemma constFrS_den (f : Fr K) (c : K) (hf : Fr.ok f) (hv : Fr.val f = algebraMap K (RatFunc K) c) :
    ∃ d : K, d ≠ 0 ∧ Fr.ok (Fr.ofPoly (Fr.norm f).2) ∧
      Fr.val (Fr.ofPoly (Fr.norm f).2) = algebraMap K (RatFunc K) d := by
  obtain ⟨-, h2, -⟩ := isConstK_norm f hf c hv
  have hok := Fr.ok_norm hf
  have hq := toPoly_of_isConstK h2
  refine ⟨(Fr.norm f).2.headD 0, fun h0 ↦ hok (by show CPoly.toPoly _ = 0; rw [hq, h0, C_0]),
    Fr.ok_ofPoly _, ?_⟩
  rw [Fr.val_ofPoly, hq, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]

end Gen

variable (Fc : BPoly ℚ) [Fact (Irreducible (toPoly (fKc Fc)))] (ks : (m : ℕ) → KindC m) (m : ℕ)
  (A : GPoly (LC (m + 1)))

/-- **`polyOfS` reads the value of a constant fraction.** -/
lemma polyOfS_head (f : Fr (KF Fc m)) (hf : Fr.ok f) (c : KF Fc m)
    (hv : Fr.val f = algebraMap (KF Fc m) (RatFunc (KF Fc m)) c) :
    (polyOfS Fc m f).headD 0 = c := by
  obtain ⟨h1, h2, hr⟩ := isConstK_norm f hf c hv
  have hok := Fr.ok_norm hf
  have hq := toPoly_of_isConstK h2
  have hd0 : (Fr.norm f).2.headD 0 ≠ 0 := fun h0 ↦ hok (by
    show CPoly.toPoly _ = 0; rw [hq, h0, C_0])
  unfold polyOfS
  rw [trim_of_isConstK _ h1, trim_of_isConstK _ h2, if_neg hd0]
  simp only [List.headD_cons]
  split_ifs with hn
  · simp only [List.map_nil, List.headD_nil]
    rw [← hr, hn, zero_div]
  · simp only [List.map_cons, List.map_nil, List.headD_cons]
    exact hr

/-- `(1/3 : Kₘ)` is a rational cast. -/
lemma third_cast : (1 / 3 : KF Fc m) = ((1 / 3 : ℚ) : KF Fc m) := by push_cast; rfl
lemma two27_cast : (2 / 27 : KF Fc m) = ((2 / 27 : ℚ) : KF Fc m) := by push_cast; rfl

lemma mwUS_const (r : ℕ → ℚ) (hcF : ∀ i < 4, IsConstFrS (cFS Fc ks m A i) (r i)) :
    ∃ U : KF Fc m, U ≠ 0 ∧ Fr.ok (mwUS Fc ks m A) ∧
      Fr.val (mwUS Fc ks m A) = algebraMap (KF Fc m) _ U := by
  unfold mwUS
  generalize hl : (List.range 4).map (fun i ↦ Fr.ofPoly (Fr.norm (cFS Fc ks m A i)).2) = l
  have hmem : ∀ f ∈ l, ∃ d : KF Fc m, d ≠ 0 ∧ Fr.ok f ∧ Fr.val f = algebraMap (KF Fc m) _ d := by
    intro f hf
    rw [← hl] at hf
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    have hc := hcF i (List.mem_range.mp hi)
    exact constFrS_den _ _ hc.1 (constFrS_val hc)
  clear hl
  induction l with
  | nil => exact ⟨1, one_ne_zero, Fr.ok_ofPoly _, by
      rw [List.foldr_nil, Fr.val_ofPoly]; simp [CPoly.toPoly, RatFunc.algebraMap_C]⟩
  | cons f l ih =>
    obtain ⟨d, hd, hf, hfv⟩ := hmem f List.mem_cons_self
    obtain ⟨U, hU, hlo, hlv⟩ := ih fun g hg ↦ hmem g (List.mem_cons_of_mem _ hg)
    exact ⟨d * U, mul_ne_zero hd hU, Fr.ok_mul hf hlo, by
      rw [List.foldr_cons, Fr.val_mul hf hlo, hfv, hlv, map_mul]⟩

lemma AFrS_const (r : ℕ → ℚ) (hcF : ∀ i < 4, IsConstFrS (cFS Fc ks m A i) (r i)) (uF : Fr (KF Fc m))
    (u : ℚ) (hu : IsConstFrS uF u) :
    IsConstFrS (AFrS Fc ks m A uF) (u * u * (u * u) * (r 1 * r 3 - 1 / 3 * (r 2 * r 2))) := by
  unfold AFrS
  rw [third_cast]
  exact constFrS_mul (constFrS_mul (constFrS_mul hu hu) (constFrS_mul hu hu))
    (constFrS_sub (constFrS_mul (hcF 1 (by norm_num)) (hcF 3 (by norm_num)))
      (constFrS_smulC _ (constFrS_mul (hcF 2 (by norm_num)) (hcF 2 (by norm_num)))))

lemma BFrS_const (r : ℕ → ℚ) (hcF : ∀ i < 4, IsConstFrS (cFS Fc ks m A i) (r i)) (uF : Fr (KF Fc m))
    (u : ℚ) (hu : IsConstFrS uF u) :
    IsConstFrS (BFrS Fc ks m A uF) (u * u * (u * u * (u * u)) *
      (r 0 * (r 3 * r 3) - 1 / 3 * (r 2 * (r 1 * r 3)) + 2 / 27 * (r 2 * (r 2 * r 2)))) := by
  unfold BFrS
  rw [third_cast, two27_cast]
  have h0 := hcF 0 (by norm_num); have h1 := hcF 1 (by norm_num)
  have h2 := hcF 2 (by norm_num); have h3 := hcF 3 (by norm_num)
  exact constFrS_mul (constFrS_mul (constFrS_mul hu hu) (constFrS_mul (constFrS_mul hu hu)
    (constFrS_mul hu hu)))
    (constFrS_add (constFrS_sub (constFrS_mul h0 (constFrS_mul h3 h3))
      (constFrS_smulC _ (constFrS_mul h2 (constFrS_mul h1 h3))))
      (constFrS_smulC _ (constFrS_mul h2 (constFrS_mul h2 h2))))

lemma AcS_head (r : ℕ → ℚ) (hcF : ∀ i < 4, IsConstFrS (cFS Fc ks m A i) (r i)) (s : ℚ)
    (uF : Fr (KF Fc m)) (u : ℚ) (hu : IsConstFrS uF u) :
    (polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 2) : KF Fc m) (AFrS Fc ks m A uF))).headD 0 =
      ((s ^ 2 * (u * u * (u * u) * (r 1 * r 3 - 1 / 3 * (r 2 * r 2))) : ℚ) : KF Fc m) :=
  polyOfS_head Fc m _ (constFrS_smulC _ (AFrS_const Fc ks m A r hcF _ u hu)).1 _
    (constFrS_val (constFrS_smulC _ (AFrS_const Fc ks m A r hcF _ u hu)))

lemma BcS_head (r : ℕ → ℚ) (hcF : ∀ i < 4, IsConstFrS (cFS Fc ks m A i) (r i)) (s : ℚ)
    (uF : Fr (KF Fc m)) (u : ℚ) (hu : IsConstFrS uF u) :
    (polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 3) : KF Fc m) (BFrS Fc ks m A uF))).headD 0 =
      ((s ^ 3 * (u * u * (u * u * (u * u)) *
        (r 0 * (r 3 * r 3) - 1 / 3 * (r 2 * (r 1 * r 3)) + 2 / 27 * (r 2 * (r 2 * r 2)))) : ℚ) :
          KF Fc m) :=
  polyOfS_head Fc m _ (constFrS_smulC _ (BFrS_const Fc ks m A r hcF _ u hu)).1 _
    (constFrS_val (constFrS_smulC _ (BFrS_const Fc ks m A r hcF _ u hu)))

namespace MTower

universe u

variable {Fc ks}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]
variable (T : MTower Fc ks Cc L)

/-- **A code with a rational value has a rational fraction** (level `m + 1`). -/
lemma frval_of_ratS (h0 : T.Tr (m + 1)) (b : LC (m + 1)) (r : ℚ)
    (hr : T.val (m + 1) b = (r : T.F (m + 1))) :
    Fr.val (trFr (Fc := Fc) m b) = algebraMap ℚ (RatFunc (KF Fc m)) r := by
  apply (ratMap (T.psiF m h0.of_succ)).injective
  rw [← T.phiS_val m h0 b, hr, map_ratCast, eq_ratCast (algebraMap ℚ _), map_ratCast]

lemma okS_zCS (h0 : T.Tr (m + 1)) : okS (Fc := Fc) m (zCS Fc ks m) = true := by
  unfold okS trFr zCS
  simp only [List.map_cons, List.map_nil, T.trC_one_T m h0.of_succ]
  rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CPoly.isZero_iff]
  simp [CPoly.toPoly]

set_option maxHeartbeats 8000000 in
/-- **The structural part of the level-`m + 1` conjugation check passes on constant data.** -/
theorem kxChkC0S_true (h0 : T.Tr (m + 1)) (g : LC (m + 1)) (B : GPoly (LC (m + 1))) (kt l : ℕ)
    (cs : List (LC (m + 1))) (z : LC (m + 1)) (κ : ℚ) (kc : ℕ) (mm : ℚ)
    (hA4 : ∀ i < 4, okS (Fc := Fc) m (aCS Fc ks m A i) = true)
    (hBok : ∀ b ∈ B, okS (Fc := Fc) m b = true)
    (hcs : ∀ q < cs.length, okS (Fc := Fc) m (kqC Fc ks (m + 1) cs q) = true)
    (hD : ∀ q < cs.length, okS (Fc := Fc) m (kxD Fc ks (m + 1) g cs q) = true)
    (hz : okS (Fc := Fc) m z = true)
    (r : ℕ → ℚ) (hr : ∀ i < 4, T.val (m + 1) (aCS Fc ks m A i) = (r i : T.F (m + 1)))
    (hBq : ∀ q < cs.length,
      (GPoly.toPoly (T.MP (m + 1) h0) B).eval (T.val (m + 1) (kqC Fc ks (m + 1) cs q)) ≠ 0)
    (hκ : κ ≠ 0) (hs : sTS Fc ks m g A B kt l cs kc ≠ 0)
    (hzκ : T.val (m + 1) z ^ 2 * T.val (m + 1) (aCS Fc ks m A 0) = (κ : T.F (m + 1)))
    (hmG : mGS Fc ks m g A B kt l cs kc ≠ 0) (hm : mm ≠ 0)
    (hdisc : 4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
      27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2 ≠ 0) :
    kxChkC0S Fc ks m g A B kt l cs z κ (Fr.ofPoly [((mm : ℚ) : KF Fc m)])
      [(polyOfS Fc m (Fr.smulC (Rat.cast (sTS Fc ks m g A B kt l cs kc ^ 2) : KF Fc m)
        (AFrS Fc ks m A (Fr.ofPoly [((mm : ℚ) : KF Fc m)])))).headD 0]
      [(polyOfS Fc m (Fr.smulC (Rat.cast (sTS Fc ks m g A B kt l cs kc ^ 3) : KF Fc m)
        (BFrS Fc ks m A (Fr.ofPoly [((mm : ℚ) : KF Fc m)])))).headD 0] kc = true := by
  set s := sTS Fc ks m g A B kt l cs kc with hsdef
  set uF : Fr (KF Fc m) := Fr.ofPoly [((mm : ℚ) : KF Fc m)] with huF
  set φ := T.phiS m h0 with hφ
  set jQ := T.psiF m h0.of_succ with hjQ
  have hcF : ∀ i < 4, IsConstFrS (cFS Fc ks m A i) (r i) := fun i hi ↦
    ⟨okS_spec (Fc := Fc) (hA4 i hi), T.frval_of_ratS m h0 _ (r i) (hr i hi)⟩
  have hu : IsConstFrS uF mm := constFrS_ofPoly mm
  have hAc := constFrS_smulC (s ^ 2) (AFrS_const Fc ks m A r hcF uF _ hu)
  have hBc := constFrS_smulC (s ^ 3) (BFrS_const Fc ks m A r hcF uF _ hu)
  have hAh := AcS_head Fc ks m A r hcF s uF _ hu
  have hBh := BcS_head Fc ks m A r hcF s uF _ hu
  -- the conjuncts
  have h1 : (List.range 4).all (fun i ↦ okS (Fc := Fc) m (aCS Fc ks m A i)) = true :=
    List.all_eq_true.mpr fun i hi ↦ hA4 i (List.mem_range.mp hi)
  have h2 : B.all (okS (Fc := Fc) m) = true := List.all_eq_true.mpr hBok
  have h3 : (List.range cs.length).all (fun q ↦ okS (Fc := Fc) m (kqC Fc ks (m + 1) cs q) &&
      okS (Fc := Fc) m (kxD Fc ks (m + 1) g cs q) && okS (Fc := Fc) m (kxR Fc ks (m + 1) A kt l cs q) &&
      !Fr.isZ (hornerFrS (Fc := Fc) m (trFr (Fc := Fc) m (kqC Fc ks (m + 1) cs q)) B)) = true := by
    refine List.all_eq_true.mpr fun q hq ↦ ?_
    have hq' := List.mem_range.mp hq
    have oq := okS_spec (Fc := Fc) (hcs q hq')
    have oH := hornerFrS_ok (Fc := Fc) m _ oq B hBok
    have hHs := T.hornerFrS_spec m h0 _ oq (T.val (m + 1) (kqC Fc ks (m + 1) cs q))
      (T.phiS_val m h0 _) B hBok
    have hH : Fr.isZ (hornerFrS (Fc := Fc) m (trFr (Fc := Fc) m (kqC Fc ks (m + 1) cs q)) B) =
        false := by
      rw [Bool.eq_false_iff, Ne, Fr.isZ_iff oH]
      intro h0'
      apply hBq q hq'
      have := hHs; rw [h0', map_zero] at this
      exact (map_eq_zero_iff _ (T.phiS m h0).injective).mp this.symm
    have hR : okS (Fc := Fc) m (kxR Fc ks (m + 1) A kt l cs q) = true := by
      unfold kxR; exact T.okS_normC m h0.of_succ _
    simp only [hcs q hq', hD q hq', hH, hR, Bool.true_and, Bool.not_false]
  have h5 : (!CPoly.isZero uF.2) = true := by
    have := hu.1; rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CPoly.isZero_iff]; exact this
  have h6 : (!Fr.isZ uF) = true := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, Fr.isZ_iff hu.1, hu.2]
    exact (map_ne_zero_iff _ (algebraMap ℚ (RatFunc (KF Fc m))).injective).mpr hm
  have h7 : Fr.eqb (Fr.ofPoly [(polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 2) : KF Fc m)
      (AFrS Fc ks m A uF))).headD 0]) (Fr.smulC (Rat.cast (s ^ 2) : KF Fc m) (AFrS Fc ks m A uF)) =
      true := by
    rw [Fr.eqb_iff (Fr.ok_ofPoly _) hAc.1, hAh, (constFrS_ofPoly _).2, hAc.2]
  have h8 : Fr.eqb (Fr.ofPoly [(polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 3) : KF Fc m)
      (BFrS Fc ks m A uF))).headD 0]) (Fr.smulC (Rat.cast (s ^ 3) : KF Fc m) (BFrS Fc ks m A uF)) =
      true := by
    rw [Fr.eqb_iff (Fr.ok_ofPoly _) hBc.1, hBh, (constFrS_ofPoly _).2, hBc.2]
  have h9 : (!CPoly.isZero (discCS Fc m
      [(polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 2) : KF Fc m) (AFrS Fc ks m A uF))).headD 0]
      [(polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 3) : KF Fc m) (BFrS Fc ks m A uF))).headD 0])) =
      true := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CPoly.isZero_iff, hAh, hBh]
    simp only [discCS, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_mul, CPoly.toPoly,
      mul_zero, add_zero, ← C_mul, ← C_add]
    rw [C_eq_zero]
    intro h0'
    apply hdisc
    have h1' : ((s ^ 6 * mm ^ 12 * (4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
        27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2) : ℚ) : KF Fc m) = 0 := by
      push_cast at h0' ⊢
      linear_combination h0'
    have h1'' := (Rat.cast_eq_zero (α := KF Fc m)).mp h1'
    exact (mul_eq_zero.mp h1'').resolve_left (mul_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ hm))
  have h12 : Fr.eqb (Fr.mul (Fr.mul (trFr (Fc := Fc) m z) (trFr (Fc := Fc) m z)) (cFS Fc ks m A 0))
      (Fr.ofPoly [(Rat.cast κ : KF Fc m)]) = true := by
    have oz := okS_spec (Fc := Fc) hz
    rw [Fr.eqb_iff (Fr.ok_mul (Fr.ok_mul oz oz) (hcF 0 (by norm_num)).1) (Fr.ok_ofPoly _)]
    apply (ratMap jQ).injective
    rw [Fr.val_mul (Fr.ok_mul oz oz) (hcF 0 (by norm_num)).1, Fr.val_mul oz oz, map_mul, map_mul,
      show cFS Fc ks m A 0 = trFr (Fc := Fc) m (aCS Fc ks m A 0) from rfl,
      ← T.phiS_val m h0 z, ← T.phiS_val m h0, ← map_mul, ← map_mul, ← sq, hzκ,
      map_ratCast, (constFrS_ofPoly κ).2, eq_ratCast (algebraMap ℚ _), map_ratCast]
  have h13 := T.okS_zCS m h0
  unfold kxChkC0S
  simp only [← hsdef, ← huF]
  simp only [h1, h2, h3, h5, h6, h7, h8, h9, h12, h13, hz, Bool.true_and, Bool.and_true,
    bne_iff_ne, ne_eq, hκ, hs, hmG, not_false_eq_true, decide_true]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨⟨hκ, hs⟩, hmG⟩

set_option maxHeartbeats 8000000 in
/-- **The structural part of the level-`m + 1` twisted check passes on constant data.** -/
theorem kxChkT0S_true (h0 : T.Tr (m + 1)) (g : LC (m + 1)) (B : GPoly (LC (m + 1))) (kt l : ℕ)
    (cs : List (LC (m + 1))) (z : LC (m + 1)) (c : ℚ) (kc : ℕ) (mm : ℚ)
    (hA4 : ∀ i < 4, okS (Fc := Fc) m (aCS Fc ks m A i) = true)
    (hBok : ∀ b ∈ B, okS (Fc := Fc) m b = true)
    (hcs : ∀ q < cs.length, okS (Fc := Fc) m (kqC Fc ks (m + 1) cs q) = true)
    (hD : ∀ q < cs.length, okS (Fc := Fc) m (kxD Fc ks (m + 1) g cs q) = true)
    (hz : okS (Fc := Fc) m z = true)
    (r : ℕ → ℚ) (hr : ∀ i < 4, T.val (m + 1) (aCS Fc ks m A i) = (r i : T.F (m + 1)))
    (hBq : ∀ q < cs.length,
      (GPoly.toPoly (T.MP (m + 1) h0) B).eval (T.val (m + 1) (kqC Fc ks (m + 1) cs q)) ≠ 0)
    (hκ : c ≠ 0) (hs : sTS Fc ks m g A B kt l cs kc ≠ 0)
    (hzκ : T.val (m + 1) z ^ 2 * T.val (m + 1) (aCS Fc ks m A 0) =
      ((sTS Fc ks m g A B kt l cs kc * c * c : ℚ) : T.F (m + 1)))
    (hmG : mGS Fc ks m g A B kt l cs kc ≠ 0) (hm : mm ≠ 0)
    (hdisc : 4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
      27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2 ≠ 0) :
    kxChkT0S Fc ks m g A B kt l cs z c (Fr.ofPoly [((mm : ℚ) : KF Fc m)])
      [(polyOfS Fc m (Fr.smulC (Rat.cast (sTS Fc ks m g A B kt l cs kc ^ 2) : KF Fc m)
        (AFrS Fc ks m A (Fr.ofPoly [((mm : ℚ) : KF Fc m)])))).headD 0]
      [(polyOfS Fc m (Fr.smulC (Rat.cast (sTS Fc ks m g A B kt l cs kc ^ 3) : KF Fc m)
        (BFrS Fc ks m A (Fr.ofPoly [((mm : ℚ) : KF Fc m)])))).headD 0] kc = true := by
  set s := sTS Fc ks m g A B kt l cs kc with hsdef
  set uF : Fr (KF Fc m) := Fr.ofPoly [((mm : ℚ) : KF Fc m)] with huF
  set φ := T.phiS m h0 with hφ
  set jQ := T.psiF m h0.of_succ with hjQ
  have hcF : ∀ i < 4, IsConstFrS (cFS Fc ks m A i) (r i) := fun i hi ↦
    ⟨okS_spec (Fc := Fc) (hA4 i hi), T.frval_of_ratS m h0 _ (r i) (hr i hi)⟩
  have hu : IsConstFrS uF mm := constFrS_ofPoly mm
  have hAc := constFrS_smulC (s ^ 2) (AFrS_const Fc ks m A r hcF uF _ hu)
  have hBc := constFrS_smulC (s ^ 3) (BFrS_const Fc ks m A r hcF uF _ hu)
  have hAh := AcS_head Fc ks m A r hcF s uF _ hu
  have hBh := BcS_head Fc ks m A r hcF s uF _ hu
  -- the conjuncts
  have h1 : (List.range 4).all (fun i ↦ okS (Fc := Fc) m (aCS Fc ks m A i)) = true :=
    List.all_eq_true.mpr fun i hi ↦ hA4 i (List.mem_range.mp hi)
  have h2 : B.all (okS (Fc := Fc) m) = true := List.all_eq_true.mpr hBok
  have h3 : (List.range cs.length).all (fun q ↦ okS (Fc := Fc) m (kqC Fc ks (m + 1) cs q) &&
      okS (Fc := Fc) m (kxD Fc ks (m + 1) g cs q) && okS (Fc := Fc) m (kxR Fc ks (m + 1) A kt l cs q) &&
      !Fr.isZ (hornerFrS (Fc := Fc) m (trFr (Fc := Fc) m (kqC Fc ks (m + 1) cs q)) B)) = true := by
    refine List.all_eq_true.mpr fun q hq ↦ ?_
    have hq' := List.mem_range.mp hq
    have oq := okS_spec (Fc := Fc) (hcs q hq')
    have oH := hornerFrS_ok (Fc := Fc) m _ oq B hBok
    have hHs := T.hornerFrS_spec m h0 _ oq (T.val (m + 1) (kqC Fc ks (m + 1) cs q))
      (T.phiS_val m h0 _) B hBok
    have hH : Fr.isZ (hornerFrS (Fc := Fc) m (trFr (Fc := Fc) m (kqC Fc ks (m + 1) cs q)) B) =
        false := by
      rw [Bool.eq_false_iff, Ne, Fr.isZ_iff oH]
      intro h0'
      apply hBq q hq'
      have := hHs; rw [h0', map_zero] at this
      exact (map_eq_zero_iff _ (T.phiS m h0).injective).mp this.symm
    have hR : okS (Fc := Fc) m (kxR Fc ks (m + 1) A kt l cs q) = true := by
      unfold kxR; exact T.okS_normC m h0.of_succ _
    simp only [hcs q hq', hD q hq', hH, hR, Bool.true_and, Bool.not_false]
  have h5 : (!CPoly.isZero uF.2) = true := by
    have := hu.1; rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CPoly.isZero_iff]; exact this
  have h6 : (!Fr.isZ uF) = true := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, Fr.isZ_iff hu.1, hu.2]
    exact (map_ne_zero_iff _ (algebraMap ℚ (RatFunc (KF Fc m))).injective).mpr hm
  have h7 : Fr.eqb (Fr.ofPoly [(polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 2) : KF Fc m)
      (AFrS Fc ks m A uF))).headD 0]) (Fr.smulC (Rat.cast (s ^ 2) : KF Fc m) (AFrS Fc ks m A uF)) =
      true := by
    rw [Fr.eqb_iff (Fr.ok_ofPoly _) hAc.1, hAh, (constFrS_ofPoly _).2, hAc.2]
  have h8 : Fr.eqb (Fr.ofPoly [(polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 3) : KF Fc m)
      (BFrS Fc ks m A uF))).headD 0]) (Fr.smulC (Rat.cast (s ^ 3) : KF Fc m) (BFrS Fc ks m A uF)) =
      true := by
    rw [Fr.eqb_iff (Fr.ok_ofPoly _) hBc.1, hBh, (constFrS_ofPoly _).2, hBc.2]
  have h9 : (!CPoly.isZero (discCS Fc m
      [(polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 2) : KF Fc m) (AFrS Fc ks m A uF))).headD 0]
      [(polyOfS Fc m (Fr.smulC (Rat.cast (s ^ 3) : KF Fc m) (BFrS Fc ks m A uF))).headD 0])) =
      true := by
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CPoly.isZero_iff, hAh, hBh]
    simp only [discCS, CPoly.toPoly_add, CPoly.toPoly_smul, CPoly.toPoly_mul, CPoly.toPoly,
      mul_zero, add_zero, ← C_mul, ← C_add]
    rw [C_eq_zero]
    intro h0'
    apply hdisc
    have h1' : ((s ^ 6 * mm ^ 12 * (4 * (r 1 * r 3 - r 2 ^ 2 / 3) ^ 3 +
        27 * (r 0 * r 3 ^ 2 - r 2 * r 1 * r 3 / 3 + 2 * r 2 ^ 3 / 27) ^ 2) : ℚ) : KF Fc m) = 0 := by
      push_cast at h0' ⊢
      linear_combination h0'
    have h1'' := (Rat.cast_eq_zero (α := KF Fc m)).mp h1'
    exact (mul_eq_zero.mp h1'').resolve_left (mul_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ hm))
  have h12 : Fr.eqb (Fr.mul (Fr.mul (trFr (Fc := Fc) m z) (trFr (Fc := Fc) m z)) (cFS Fc ks m A 0))
      (Fr.ofPoly [(Rat.cast (s * c * c) : KF Fc m)]) = true := by
    have oz := okS_spec (Fc := Fc) hz
    rw [Fr.eqb_iff (Fr.ok_mul (Fr.ok_mul oz oz) (hcF 0 (by norm_num)).1) (Fr.ok_ofPoly _)]
    apply (ratMap jQ).injective
    rw [Fr.val_mul (Fr.ok_mul oz oz) (hcF 0 (by norm_num)).1, Fr.val_mul oz oz, map_mul, map_mul,
      show cFS Fc ks m A 0 = trFr (Fc := Fc) m (aCS Fc ks m A 0) from rfl,
      ← T.phiS_val m h0 z, ← T.phiS_val m h0, ← map_mul, ← map_mul, ← sq, hzκ,
      map_ratCast, (constFrS_ofPoly (s * c * c)).2, eq_ratCast (algebraMap ℚ _), map_ratCast]
  have h13 := T.okS_zCS m h0
  unfold kxChkT0S
  simp only [← hsdef, ← huF]
  simp only [h1, h2, h3, h5, h6, h7, h8, h9, h12, h13, hz, Bool.true_and, Bool.and_true,
    bne_iff_ne, ne_eq, hκ, hs, hmG, not_false_eq_true, decide_true]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨⟨hκ, hs⟩, hmG⟩


set_option maxHeartbeats 4000000 in
open Classical in
/-- **Some level makes the level-`m + 1` constant-curve conjugation check pass.** -/
theorem kxChkCKS_exists (c0f : CPoly ℚ) (hFc : Fc = [c0f, [1]]) (h0 : T.Tr (m + 1))
    (g : LC (m + 1)) (B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
    (z : LC (m + 1)) (κ : ℚ) (uF : Fr (KF Fc m)) (Ac Bc : CPoly (KF Fc m)) (a b : ℤ)
    (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length)
    [Fact (¬ IsSquare (Rat.cast (sTS Fc ks m g A B kt l cs k * κ) : KF Fc m))]
    (hchk : kxChkC0S Fc ks m g A B kt l cs z κ uF Ac Bc k = true)
    (hAc : Ac = [((a : ℚ) : KF Fc m)]) (hBc : Bc = [((b : ℚ) : KF Fc m)])
    (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (rtsF : List (T.F (m + 1))) (hrl : rtsF.length = (kxGens Fc ks (m + 1) g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks (m + 1) g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks (m + 1) g A B kt l cs)[i] : T.F (m + 1)))
    (b₀ : T.F (m + 1)) (hb₀ : b₀ ^ 2 = (T.MP (m + 1) h0).sem (A.getD 0 (MO Fc ks (m + 1)).zero))
    (hns : ∀ q : Fin cs.length, (Differential.SuperData.WG ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3)
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 2) ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 1)
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3 * (T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3 * (((kxRep Fc ks (m + 1) g A B kt l cs q).2 : T.F (m + 1)) *
          SqrtIndep.prodRoots rtsF (kxRep Fc ks (m + 1) g A B kt l cs q).1 *
          ((T.MP (m + 1) h0).sem (kxD Fc ks (m + 1) g cs q) * (T.MP (m + 1) h0).sem (kxR Fc ks (m + 1) A kt l cs q) /
            (GPoly.toPoly (T.MP (m + 1) h0) B).eval ((T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))))))
    (hns0 : (Differential.SuperData.WG ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3)
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 2) ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 1)
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3 * 0) ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3 * b₀))
    (hntF : ∀ n : ℤ, n • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks (m + 1) g A B kt l cs q)
        (kxCl (m + 1) g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) = 0 →
        n = 0) :
    ∃ kk, kxChkCKS Fc ks m g A B kt l cs z κ uF Ac Bc kk k a b = true := by
  obtain ⟨⟨PD, hRD⟩, hnt⟩ := T.indep_of_grpC0S m g A B kt l cs z uF Ac Bc κ h0 k hchk rtsF hrl
    hrs b₀ hb₀ hns hns0 hntF
  subst hAc hBc
  subst hFc
  have hA : CPoly.toPoly [((a : ℚ) : KF [c0f, [1]] m)] = Polynomial.C ((a : ℚ) : KF [c0f, [1]] m) := by
    simp [CPoly.toPoly]
  have hB : CPoly.toPoly [((b : ℚ) : KF [c0f, [1]] m)] = Polynomial.C ((b : ℚ) : KF [c0f, [1]] m) := by
    simp [CPoly.toPoly]
  obtain ⟨kk, hkk⟩ := ck_tail_existsS c0f m a b hΔ _ _ _ hA hB PD hRD (hnt PD hRD)
  refine ⟨kk, ?_⟩
  unfold kxChkCKS
  rw [hchk]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨hΔ, hkk⟩

set_option maxHeartbeats 4000000 in
open Classical in
/-- **Some level makes the level-`m + 1` constant-curve same-class check pass.** -/
theorem kxChkTKS_exists (c0f : CPoly ℚ) (hFc : Fc = [c0f, [1]]) (h0 : T.Tr (m + 1))
    (g : LC (m + 1)) (B : GPoly (LC (m + 1))) (kt l : ℕ) (cs : List (LC (m + 1)))
    (z : LC (m + 1)) (c : ℚ) (uF : Fr (KF Fc m)) (Ac Bc : CPoly (KF Fc m)) (a b : ℤ)
    (k : Fin (kxCls Fc ks (m + 1) g A B kt l cs).length)
    (hchk : kxChkT0S Fc ks m g A B kt l cs z c uF Ac Bc k = true)
    (hAc : Ac = [((a : ℚ) : KF Fc m)]) (hBc : Bc = [((b : ℚ) : KF Fc m)])
    (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (rtsF : List (T.F (m + 1))) (hrl : rtsF.length = (kxGens Fc ks (m + 1) g A B kt l cs).length)
    (hrs : ∀ i (hi : i < rtsF.length) (hi' : i < (kxGens Fc ks (m + 1) g A B kt l cs).length),
      rtsF[i] ^ 2 = ((kxGens Fc ks (m + 1) g A B kt l cs)[i] : T.F (m + 1)))
    (b₀ : T.F (m + 1)) (hb₀ : b₀ ^ 2 = (T.MP (m + 1) h0).sem (A.getD 0 (MO Fc ks (m + 1)).zero))
    (hns : ∀ q : Fin cs.length, (Differential.SuperData.WG ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3)
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 2) ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 1)
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3 * (T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3 * (((kxRep Fc ks (m + 1) g A B kt l cs q).2 : T.F (m + 1)) *
          SqrtIndep.prodRoots rtsF (kxRep Fc ks (m + 1) g A B kt l cs q).1 *
          ((T.MP (m + 1) h0).sem (kxD Fc ks (m + 1) g cs q) * (T.MP (m + 1) h0).sem (kxR Fc ks (m + 1) A kt l cs q) /
            (GPoly.toPoly (T.MP (m + 1) h0) B).eval ((T.MP (m + 1) h0).sem (kqC Fc ks (m + 1) cs q))))))
    (hns0 : (Differential.SuperData.WG ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3)
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 2) ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 1)
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 0)).Nonsingular
        ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3 * 0) ((GPoly.toPoly (T.MP (m + 1) h0) A).coeff 3 * b₀))
    (hgrp : ∀ N : ℕ, 0 < N → ∀ μ : ℤ,
        (2 * (N : ℤ)) • (∑ q, (Differential.SuperData.mK (fun q ↦ kxMNm Fc ks (m + 1) g A B kt l cs q)
          (kxCl (m + 1) g A B kt l cs) k q : ℤ) • WeierstrassCurve.Affine.Point.some _ _ (hns q)) +
          (2 * μ) • WeierstrassCurve.Affine.Point.some _ _ hns0 ≠ 0)
    (hP0 : ∀ n : ℤ, n • WeierstrassCurve.Affine.Point.some _ _ hns0 = 0 → n = 0) :
    ∃ kk, kxChkTKS Fc ks m g A B kt l cs z uF Ac Bc kk k a b c = true := by
  obtain ⟨⟨PD, hRD⟩, ⟨PZ, hRZ⟩, hind⟩ := T.indep_of_grpT0S m g A B kt l cs z c uF Ac Bc h0 k hchk
    rtsF hrl hrs b₀ hb₀ hns hns0 hgrp hP0
  subst hAc hBc
  subst hFc
  have hA : CPoly.toPoly [((a : ℚ) : KF [c0f, [1]] m)] = Polynomial.C ((a : ℚ) : KF [c0f, [1]] m) := by
    simp [CPoly.toPoly]
  have hB : CPoly.toPoly [((b : ℚ) : KF [c0f, [1]] m)] = Polynomial.C ((b : ℚ) : KF [c0f, [1]] m) := by
    simp [CPoly.toPoly]
  obtain ⟨kk, hkk⟩ := tk_tail_existsS c0f m a b hΔ _ _ _ _ hA hB PD PZ hRD hRZ (hind PD PZ hRD hRZ)
  refine ⟨kk, ?_⟩
  unfold kxChkTKS
  rw [hchk]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨hΔ, hkk⟩

end MTower

end Curves.MT
