import RischTragerBronstein.Mixed.NKResOrdC
import RischTragerBronstein.Mixed.NKInfRVMR0
import RischTragerBronstein.Mixed.KQMain

/-!
# Places at infinity without a rational residue: non-elementary integrals

`coeff_place_multi`: every place at infinity carries a root along which the coefficient at `T^N`
of `f` is the residue value of the truncation. If at some place no rational `ρ` makes
`c + ρ η` a derivative (`noResCk`: the parametric Risch equation for `[c, η]` has only solutions
with zero first coordinate), the integral is not elementary (`nk_not_elem_noRes`): the residue of
a Liouville form is a constant of `Fₘ`, and the descent from `Fₘ` to its algebraic closure keeps
antiderivatives.
-/

open Polynomial HahnSeries LaurentSeries IntermediateField

set_option linter.unusedSectionVars false

namespace Curves

open Differential

section CurvePlace

variable {C L Kb : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
  [Differential C] [Differential L] [DifferentialAlgebra C L]
  [Field Kb] [CharZero Kb] [Algebra C Kb] [Differential Kb] [IsAlgClosed Kb]

namespace CurveData

variable (S : CurveData C L)

theorem coeff_place_multi {q : ℕ} (e : Fin (q + 1) → ℕ) (he : ∀ k, 0 < e k) (s : Fin (q + 1) → ℤ)
    (hcop : ∀ k, Int.gcd (s k) (e k) = 1)
    (hdec : ∀ k : Fin q, s k.succ * e k.castSucc < s k.castSucc * e k.succ)
    (K0 : Fin (q + 1) → ℤ) (c : Fin (q + 1) → C) (hc : ∀ k, c k ≠ 0) (lo : Fin (q + 1) → ℕ)
    (Γ : Fin (q + 1) → List C) (hΓ : ∀ k, (Γ k).Nodup ∧ (0 : C) ∉ Γ k)
    (hbound : ∀ k, ∀ i ≤ S.F.natDegree, S.F.coeff i ≠ 0 →
      (e k : ℤ) * (S.F.coeff i).natDegree + i * s k ≤ K0 k)
    (hres : ∀ k, ∑ i ∈ Finset.range (S.F.natDegree + 1),
      Polynomial.C (coeffZe (S.F.coeff i) (e k) (K0 k - i * s k)) * X ^ i =
        Polynomial.C (c k) * X ^ (lo k) * ((Γ k).map fun γ ↦ X ^ (e k) - Polynomial.C γ).prod)
    (htop : lo 0 + e 0 * (Γ 0).length = S.F.natDegree)
    (hchain : ∀ k : Fin q, lo k.castSucc = lo k.succ + e k.succ * (Γ k.succ).length)
    (hlast : lo (Fin.last q) = 0)
    (β : ∀ k, Fin (Γ k).length → C) (hβ : ∀ k i, β k i ^ e k = (Γ k)[(i : ℕ)])
    (Θt : ∀ k, Fin (Γ k).length → C[X]) (hΘ0 : ∀ k i, (Θt k i).coeff 0 = β k i)
    (hu : ∀ k i, ((derivative (segPoly (e k) (s k) (K0 k) S.F)).eval (Θt k i)).coeff 0 ≠ 0)
    (M : ℕ) (hM : ∀ k i, ∀ n < M, ((segPoly (e k) (s k) (K0 k) S.F).eval (Θt k i)).coeff n = 0)
    (Q : C[X][X])
    (hMb : ∀ k, ∀ j ≤ Q.natDegree, ∀ l ≤ (Q.coeff j).natDegree,
      (e k : ℤ) + e k * l + s k * j < M)
    (hK : ∀ c : C, (algebraMap C Kb c)′ = algebraMap C Kb c′) :
    ∃ (N : ℕ) (hN : 0 < N) (li : List (LaurentSeries Kb)) (hli : S.F.map (infSub (K := Kb) N) =
      (li.map fun r ↦ X - Polynomial.C r).prod),
      ∀ k (p : Fin (Γ k).length), ∃ r, ∃ hr : r ∈ li, (S.embG (infSub N) (infSub_injective N hN) r
        (S.root_of_mem hli hr) (S.evT Q)).coeff (N : ℤ) =
          algebraMap C Kb (∑ j ∈ Finset.range (Q.natDegree + 1),
            ∑ l ∈ Finset.range ((Q.coeff j).natDegree + 1), (Q.coeff j).coeff l *
              (if 0 ≤ (e k : ℤ) + e k * l + s k * j then
                ((Θt k p) ^ j).coeff ((e k : ℤ) + e k * l + s k * j).toNat else 0)) := by
  classical
  have hF0 : S.F.coeff 0 ≠ 0 := coeff0_ne_of_resR S.F (e (Fin.last q)) (he _) (s (Fin.last q))
    (K0 (Fin.last q)) (c (Fin.last q)) (hc _) (Γ (Fin.last q)) (hΓ _).2
    (by rw [← hlast]; exact hres _)
  obtain ⟨Nb, hNb, lb, -, hlb⟩ := S.hasBranchesInf (K := Kb)
  have hNb' := Nat.pos_of_ne_zero hNb
  set E : ℕ := ∏ k, e k with hE
  have hE0 : 0 < E := Finset.prod_pos fun k _ ↦ he k
  set N : ℕ := Nb * E with hNdef
  have hN : 0 < N := Nat.mul_pos hNb' hE0
  set lr := lb.map (lsub E hE0) with hlr
  have hl : S.F.map (infSub N) = (lr.map fun r ↦ X - Polynomial.C r).prod :=
    branchSys_lsub S.F Nb E hE0 lb hlb
  have hed : ∀ k, e k ∣ N := fun k ↦
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) _
  have hsA := strictAnti_weights N hN e he hed s hdec
  obtain ⟨hord, huniq, hsurj⟩ := multi_hdataR (K := Kb) N hN S.F S.monic hF0 lr hl e he hed s
    hsA K0 c hc lo Γ hΓ hbound hres htop hchain hlast
  have hl0 : ∀ r ∈ lr, r ≠ 0 := by
    intro r hr h0
    subst h0
    have h1 : (S.F.map (infSub (K := Kb) N)).eval 0 = 0 := S.root_of_mem hl hr
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at h1
    exact hF0 ((infSub_injective N hN) (by rw [h1, map_zero]))
  have : NeZero ((N : ℕ) : Kb) := ⟨by exact_mod_cast hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Kb N
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  refine ⟨N, hN, lr, hl, fun k p ↦ ?_⟩
  obtain ⟨r, hr, hk, hγe⟩ := hsurj k _ (List.getElem_mem p.2)
  obtain ⟨i, hi⟩ := p
  set ι := algebraMap C Kb with hι
  set cr := r.coeff r.order with hcr
  have hcr0 : cr ≠ 0 := fun h ↦ hl0 r hr (HahnSeries.coeff_order_eq_zero.mp h)
  set bK := ι (β k ⟨i, hi⟩) with hbK
  set uu := bK / cr with huu
  have hue : uu ^ e k = 1 := by
    rw [huu, div_pow, hγe, hbK, ← map_pow, hβ k ⟨i, hi⟩, div_self]
    rw [← hγe]; exact pow_ne_zero _ hcr0
  obtain ⟨d, hd⟩ := hed k
  have hNe : N / e k = d := by rw [hd, Nat.mul_div_cancel_left _ (he k)]
  have hω : IsPrimitiveRoot (ζ ^ d) (e k) := hζ.pow hN (by rw [hd, mul_comm])
  have hωs : IsPrimitiveRoot ((ζ ^ d) ^ (-s k)) (e k) :=
    hω.zpow_of_gcd_eq_one (-s k) (by rw [Int.neg_gcd]; exact hcop k)
  haveI : NeZero (e k) := ⟨(he k).ne'⟩
  obtain ⟨j, -, hj⟩ := hωs.eq_pow_of_pow_eq_one hue
  have hζj0 : ζ ^ j ≠ 0 := pow_ne_zero _ hζ0
  have hζjN : (ζ ^ j) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  set r' := rot (ζ ^ j) hζj0 r with hr'
  have hr'mem : r' ∈ lr := S.rot_mem N hζj0 hζjN lr hl hr
  have hr'o : r'.order = -((d : ℤ) * s k) := by rw [hr', rot_order, hk, hNe]
  have hr'c : r'.coeff r'.order = bK := by
    rw [hr', rot_lc]
    have hpow' : (ζ ^ j) ^ r.order = ((ζ ^ d) ^ (-s k)) ^ j := by
      rw [hk, hNe, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
        ← zpow_mul]
      congr 1
      ring
    rw [hpow', hj, huu, div_mul_cancel₀ _ hcr0]
  -- the residue along `r` is the one along `r'`
  have hrr := S.root_of_mem hl hr
  have hrr' := S.root_of_mem hl hr'mem
  have hrot := S.embG_rot_coeff N hN hζj0 hζjN r hrr hrr' (S.evT Q) (N : ℤ)
  rw [show (ζ ^ j) ^ (N : ℤ) = 1 by rw [zpow_natCast, hζjN], one_mul] at hrot
  -- the power series of `r'`
  set Θ := r'.powerSeriesPart with hΘ
  have hr'eq : r' = single (-((d : ℤ) * s k)) 1 * ofPowerSeries ℤ Kb Θ := by
    rw [← hr'o]; exact (single_order_mul_powerSeriesPart r').symm
  have hΘc : PowerSeries.constantCoeff Θ = ι ((Θt k ⟨i, hi⟩).coeff 0) := by
    rw [hΘ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, powerSeriesPart_coeff, Nat.cast_zero,
      add_zero, hr'c, hΘ0]
  have hNde : N = d * e k := by rw [hd, mul_comm]
  have hroot : ((segPoly (e k) (s k) (K0 k) S.F).map (phiD (K := Kb) d)).eval Θ = 0 :=
    segPoly_root N d (e k) hNde (s k) (K0 k) S.F (hbound k) Θ (by rw [← hr'eq]; exact hrr')
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hd; omega)
  have hagree := seg_trunc d hd0 _ Θ hroot (Θt k ⟨i, hi⟩) hΘc (hu k ⟨i, hi⟩) M (hM k ⟨i, hi⟩)
  refine ⟨r', hr'mem, ?_⟩
  rw [S.embG_evT, hr'eq]
  rw [coeff_eval_seg Q N d (s k) Θ (phiD d (Θt k ⟨i, hi⟩)) (d * M) hagree (fun j' hj' l hl' ↦ by
    have := hMb k j' hj' l hl'
    have h2 : (N : ℤ) + N * l + d * s k * j' = d * ((e k : ℤ) + e k * l + s k * j') := by
      rw [hNde]; push_cast; ring
    rw [h2]; push_cast
    exact mul_lt_mul_of_pos_left this (by exact_mod_cast hd0))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j' _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  have h2 : (N : ℤ) + N * l + d * s k * j' = d * ((e k : ℤ) + e k * l + s k * j') := by
    rw [hNde]; push_cast; ring
  rw [h2, coeff_ofPS_phiD_pow d hd0, map_mul]
  split_ifs
  · rfl
  · rw [map_zero, mul_zero]

end CurveData

end CurvePlace

end Curves

namespace Curves.MT

open CPoly Sup Curves.LT Tower.Sys Tower.NestP Tower.NestM Tower.NestX Tower.PrimN GTors Differential

section Codes

variable (Fc : BPoly ℚ) (ks : (m : ℕ) → KindC m) (lv : (m : ℕ) → LC m)

/-- The place data checks of `multiResCk` (without the residue tests). -/
def placesCk (m : ℕ) (Pp : List (GPoly (LC m))) (segs : List (SegRC m))
    (βs : List (List (LC m))) (Θs : List (List (GPoly (LC m)))) (M : ℕ)
    (fp : List (GPoly (LC m))) : Bool :=
  let O := MO Fc ks m
  let n := Pp.length
  (List.range segs.length).all fun k ↦
    let sg := segs.getD k (segRD Fc ks m)
    decide ((βs.getD k []).length = sg.2.2.2.2.length) &&
    (List.range sg.2.2.2.2.length).all (fun i ↦
      let β := (βs.getD k []).getD i O.zero
      let Θ := (Θs.getD k []).getD i []
      O.isZero (O.add (powC O β sg.1) (O.neg (sg.2.2.2.2.getD i O.zero))) &&
      O.isZero (O.add (Θ.getD 0 O.zero) (O.neg β)) &&
      truncOKC Fc ks m M (segEvalC Fc ks m sg.1 sg.2.1 sg.2.2.1 Pp Θ) &&
      !O.isZero (evalLC Fc ks m (GPoly.derivX O (segResidC Fc ks m sg.1 sg.2.1 sg.2.2.1 Pp)) β)) &&
    (List.range n).all fun j ↦ (List.range (max 1 (fp.getD j []).length)).all fun l ↦
      decide ((sg.1 : ℤ) + sg.1 * l + sg.2.1 * j < M)

/-- **No rational residue at the place `(k, p)`**: every solution of `y′ = q₁ c + q₂ η` has
`q₁ = 0`. -/
def noResAt (m : ℕ) (η : LC m) (Pp : List (GPoly (LC m))) (segs : List (SegRC m))
    (Θs : List (List (GPoly (LC m)))) (fp : List (GPoly (LC m))) (k p : ℕ) : Bool :=
  (prdeC Fc ks lv m ⟨(MO Fc ks m).one, []⟩
    [segResC Fc ks m (segs.getD k (segRD Fc ks m)).1 (segs.getD k (segRD Fc ks m)).2.1 Pp.length fp
      ((Θs.getD k []).getD p []), η]).all fun r ↦ r.1.getD 0 0 == 0

/-- **The certificate**: the place data, and a place without rational residue. -/
def noResCk (m : ℕ) (η : LC m) (Pp : List (GPoly (LC m))) (segs : List (SegRC m))
    (βs : List (List (LC m))) (Θs : List (List (GPoly (LC m)))) (M : ℕ)
    (fp : List (GPoly (LC m))) (k p : ℕ) : Bool :=
  placesCk Fc ks m Pp segs βs Θs M fp && decide (k < segs.length) &&
    decide (p < (segs.getD k (segRD Fc ks m)).2.2.2.2.length) &&
    noResAt Fc ks lv m η Pp segs Θs fp k p

end Codes

universe u

section Tower

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L)

set_option maxHeartbeats 1000000 in
/-- **Place data**: every place carries a root along which the coefficient at `T^N` of `f` is the
residue value of the truncation. -/
theorem coeff_place_multiC (m : ℕ) (h : T.Tr m) {L' : Type*} [Field L'] [CharZero L']
    [Algebra (T.F m) L'] [Differential L'] [DifferentialAlgebra (T.F m) L']
    (S : CurveData (T.F m) L') (Pp : List (GPoly (LC m))) (hSF : S.F = T.nkF m h Pp)
    (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true)
    (βs : List (List (LC m))) (Θs : List (List (GPoly (LC m)))) (M : ℕ) (fp : List (GPoly (LC m)))
    (hck : placesCk Fc ks m Pp segs βs Θs M fp = true)
    {Kb : Type*} [Field Kb] [CharZero Kb] [Algebra (T.F m) Kb] [Differential Kb] [IsAlgClosed Kb]
    (hK : ∀ c : T.F m, (algebraMap (T.F m) Kb c)′ = algebraMap (T.F m) Kb c′) :
    ∃ (N : ℕ) (hN : 0 < N) (li : List (LaurentSeries Kb)) (hli : S.F.map (infSub (K := Kb) N) =
      (li.map fun r ↦ X - Polynomial.C r).prod),
      ∀ k < segs.length, ∀ p < (segs.getD k (segRD Fc ks m)).2.2.2.2.length, ∃ r, ∃ hr : r ∈ li,
        (S.embG (infSub N) (infSub_injective N hN) r
        (S.root_of_mem hli hr) (S.evT (∑ j ∈ Finset.range Pp.length,
          Polynomial.C (GPoly.toPoly (T.MP m h) (fp.getD j [])) * X ^ j))).coeff (N : ℤ) =
          algebraMap (T.F m) Kb ((T.MP m h).sem (segResC Fc ks m (segs.getD k (segRD Fc ks m)).1
            (segs.getD k (segRD Fc ks m)).2.1 Pp.length fp ((Θs.getD k []).getD p []))) := by
  classical
  obtain ⟨q, hq, hn0, hePos, hgcd, hdecS, hcne, hΓ, hbd, hres, htop, hchain, hlast⟩ :=
    T.multiShapeR_spec m h Pp segs hms
  simp only [placesCk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true'] at hck
  set sg : Fin (q + 1) → SegRC m := fun k ↦ segs.getD k (segRD Fc ks m) with hsg
  set n := Pp.length with hn
  set Q : (T.F m)[X][X] := ∑ j ∈ Finset.range n,
    Polynomial.C (GPoly.toPoly (T.MP m h) (fp.getD j [])) * X ^ j with hQ
  have hQc : ∀ j, Q.coeff j = if j < n then GPoly.toPoly (T.MP m h) (fp.getD j []) else 0 := by
    intro j
    rw [hQ, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  have hQd : Q.natDegree < n := by
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := n - 1) fun j hj ↦ ?_)
      (by omega)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_X_pow]; have := Finset.mem_range.mp hj; omega
  have hk : ∀ k : Fin (q + 1), (k : ℕ) < segs.length := fun k ↦ by rw [hq]; exact k.2
  -- the data per place
  set Γ : Fin (q + 1) → List (T.F m) := fun k ↦ (sg k).2.2.2.2.map (T.MP m h).sem with hΓdef
  have hΓlen : ∀ k, (Γ k).length = (sg k).2.2.2.2.length := fun k ↦ List.length_map _
  set β : ∀ k, Fin (Γ k).length → T.F m := fun k i ↦ (T.MP m h).sem ((βs.getD k []).getD i (MO Fc ks m).zero) with hβ
  set Θt : ∀ k, Fin (Γ k).length → (T.F m)[X] := fun k i ↦
    GPoly.toPoly (T.MP m h) ((Θs.getD k []).getD i []) with hΘt
  have hplace : ∀ k (i : Fin (Γ k).length), _ := fun k i ↦
    (hck k (hk k)).1.2 i (by rw [← hΓlen]; exact i.2)
  have hβe : ∀ k (i : Fin (Γ k).length), β k i ^ (sg k).1 = (Γ k)[(i : ℕ)] := by
    intro k i
    have A := (hplace k i).1.1.1
    rw [(T.MP m h).isZero_iff, (T.MP m h).sem_add, (T.MP m h).sem_neg, sem_powC, add_neg_eq_zero] at A
    simp only [hβ, hΓdef]
    rw [A, List.getElem_map, List.getD_eq_getElem]
  have hΘ0s : ∀ k (i : Fin (Γ k).length),
      (T.MP m h).sem (((Θs.getD k []).getD i []).getD 0 (MO Fc ks m).zero) = β k i := by
    intro k i
    have B := (hplace k i).1.1.2
    rw [(T.MP m h).isZero_iff, (T.MP m h).sem_add, (T.MP m h).sem_neg, add_neg_eq_zero] at B
    exact B
  have hΘ0 : ∀ k (i : Fin (Γ k).length), (Θt k i).coeff 0 = β k i := fun k i ↦ by
    rw [hΘt, coeff_toPoly_sem]; exact hΘ0s k i
  have hu : ∀ k (i : Fin (Γ k).length),
      ((derivative (segPoly (sg k).1 (sg k).2.1 (sg k).2.2.1 S.F)).eval (Θt k i)).coeff 0 ≠ 0 := by
    intro k i
    have D := (hplace k i).2
    rw [hSF, hΘt]
    beta_reduce
    rw [T.deriv_segPoly_nkF m h Pp, sem_evalLC, hΘ0s k i, hβ]
    rw [← sem_evalLC]
    intro h0
    rw [← (T.MP m h).isZero_iff] at h0
    rw [h0] at D
    exact absurd D (by simp)
  have hM : ∀ k (i : Fin (Γ k).length), ∀ n' < M,
      ((segPoly (sg k).1 (sg k).2.1 (sg k).2.2.1 S.F).eval (Θt k i)).coeff n' = 0 := by
    intro k i n' hn'
    have C := (hplace k i).1.2
    rw [hSF, hΘt]
    beta_reduce
    rw [T.eval_segPoly_nkF m h Pp, coeff_toPoly_sem]
    exact ((T.MP m h).isZero_iff _).mp (List.all_eq_true.mp C n' (List.mem_range.mpr hn'))
  have hMb : ∀ k, ∀ j ≤ Q.natDegree, ∀ l ≤ (Q.coeff j).natDegree,
      ((sg k).1 : ℤ) + (sg k).1 * l + (sg k).2.1 * j < M := by
    intro k j hj l hl
    have hjn : j < n := lt_of_le_of_lt hj hQd
    rw [hQc, if_pos hjn] at hl
    have h1 := natDegree_toPoly_le (T.MP m h) (fp.getD j [])
    exact (hck k (hk k)).2 j hjn l (by omega)
  have hbd' : ∀ k : Fin (q + 1), ∀ i ≤ S.F.natDegree, S.F.coeff i ≠ 0 →
      ((sg k).1 : ℤ) * (S.F.coeff i).natDegree + i * (sg k).2.1 ≤ (sg k).2.2.1 := by
    rw [hSF]; exact hbd
  have hres' : ∀ k : Fin (q + 1), ∑ i ∈ Finset.range (S.F.natDegree + 1),
      Polynomial.C (coeffZe (S.F.coeff i) (sg k).1 ((sg k).2.2.1 - i * (sg k).2.1)) * X ^ i =
        Polynomial.C ((T.MP m h).sem (sg k).2.2.2.1) * X ^ (loRC segs k) *
          ((Γ k).map fun γ ↦ X ^ (sg k).1 - Polynomial.C γ).prod := by
    rw [hSF]; exact hres
  have htop' : loRC segs ((0 : Fin (q + 1)) : ℕ) + (sg 0).1 * (Γ 0).length = S.F.natDegree := by
    rw [hSF]; exact htop
  obtain ⟨N, hN, li, hli, hzr⟩ := S.coeff_place_multi (Kb := Kb) (fun k ↦ (sg k).1) hePos
    (fun k ↦ (sg k).2.1) hgcd hdecS (fun k ↦ (sg k).2.2.1) (fun k ↦ (T.MP m h).sem (sg k).2.2.2.1) hcne
    (fun k ↦ loRC segs k) Γ hΓ hbd' hres' htop' hchain hlast β hβe Θt hΘ0 hu M hM Q hMb hK
  refine ⟨N, hN, li, hli, fun k hk' p hp ↦ ?_⟩
  obtain ⟨r, hr, hcoef⟩ := hzr ⟨k, by omega⟩ ⟨p, by rw [hΓlen]; exact hp⟩
  refine ⟨r, hr, ?_⟩
  rw [hcoef, sem_segResC]
  congr 1
  have hstep : ∀ j ∈ Finset.range n,
      ∑ l ∈ Finset.range (fp.getD j []).length, (T.MP m h).sem ((fp.getD j []).getD l (MO Fc ks m).zero) *
        (if 0 ≤ ((segs.getD k (segRD Fc ks m)).1 : ℤ) + (segs.getD k (segRD Fc ks m)).1 * l +
            (segs.getD k (segRD Fc ks m)).2.1 * j then
          ((GPoly.toPoly (T.MP m h) ((Θs.getD k []).getD p [])) ^ j).coeff
            (((segs.getD k (segRD Fc ks m)).1 : ℤ) + (segs.getD k (segRD Fc ks m)).1 * l +
              (segs.getD k (segRD Fc ks m)).2.1 * j).toNat else 0) =
      ∑ l ∈ Finset.range ((Q.coeff j).natDegree + 1), (Q.coeff j).coeff l *
        (if 0 ≤ ((segs.getD k (segRD Fc ks m)).1 : ℤ) + (segs.getD k (segRD Fc ks m)).1 * l +
            (segs.getD k (segRD Fc ks m)).2.1 * j then
          ((GPoly.toPoly (T.MP m h) ((Θs.getD k []).getD p [])) ^ j).coeff
            (((segs.getD k (segRD Fc ks m)).1 : ℤ) + (segs.getD k (segRD Fc ks m)).1 * l +
              (segs.getD k (segRD Fc ks m)).2.1 * j).toNat else 0) := by
    intro j hj
    rw [hQc, if_pos (Finset.mem_range.mp hj)]
    exact sum_toPoly_coeff (T.MP m h) _ _
  rw [Finset.sum_congr rfl hstep]
  refine Finset.sum_subset (Finset.range_subset_range.mpr (show Q.natDegree + 1 ≤ n by omega))
    fun j _ hnj ↦ ?_
  rw [coeff_eq_zero_of_natDegree_lt (by simpa using hnj)]
  simp

set_option maxHeartbeats 4000000 in
/-- **No rational residue at a place at infinity: not elementary** (logarithmic level, several
Newton segments). If the parametric Risch equation `y′ = q₁ c + q₂ η` for the residue value `c` of
the place `(k, p)` has only solutions with `q₁ = 0`, then `∫ f` is not elementary. -/
theorem nk_not_elem_noRes (hmon : (toB Fc).Monic) (hdeg : (toB Fc).natDegree = cvN Fc) (m : ℕ)
    (hn : T.n = m + 1) (hc : certC Fc ks lv (m + 1) = true) {η : LC m} (hk : ks m = .prim η)
    (Pp : List (GPoly (LC m))) (qE : GPoly (LC m)) (csE : List (GPoly (LC m)))
    (sE tE s2E t2E : GPoly (LC m)) (hck : eisCk Fc ks m Pp qE csE sE tE s2E t2E = true) (θ : L)
    (hn0 : 0 < Pp.length) (dθ wθ : GPoly (LC (m + 1))) (s : List (LC (m + 1)))
    (hθ : θ ^ Pp.length + ∑ i ∈ Finset.range Pp.length, T.evP m (Pp.getD i []) * θ ^ i = 0)
    (hgen : ∀ z : L, z ∈ IntermediateField.adjoin (T.F (m + 1)) {θ})
    (hs : traceW Fc ks m Pp dθ wθ s = true)
    (fp : List (GPoly (LC m))) (segs : List (SegRC m)) (hms : multiShapeRC Fc ks m Pp segs = true)
    (βs : List (List (LC m))) (Θs : List (List (GPoly (LC m)))) (MR : ℕ) (k p : ℕ)
    (hcert : noResCk Fc ks lv m η Pp segs βs Θs MR fp k p = true) :
    ¬ HasElementaryIntegral (∑ j ∈ Finset.range Pp.length, T.evP m (fp.getD j []) * θ ^ j) := by
  classical
  intro hf
  set n := Pp.length with hnn
  set f := ∑ j ∈ Finset.range n, T.evP m (fp.getD j []) * θ ^ j with hfdef
  set q := nkTau Fc ks m n (nkFl Fc ks m fp) s with hq
  have MS := T.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTr : T.Tr (m + 1) := MS.hyp.tr
  have hcm : certC Fc ks lv m = true := by
    rw [certX_succ, Bool.and_eq_true] at hc; exact hc.1
  obtain ⟨E₁, _, _, _, _, hE₁, g, hg⟩ := hf
  haveI : CharZero E₁ := charZero_of_injective_algebraMap (algebraMap L E₁).injective
  obtain ⟨ι, s', c, u, v, hdata, hv, heqL⟩ := liouville_strong hE₁ _ g hg
  -- the tower in `E₁`
  obtain ⟨TE, hTEn, hTEts, hTEev, hTEmem⟩ := T.exists_lift E₁
  set ψ := algebraMap L E₁ with hψ
  have MSE := TE.mspecs hmon hdeg lv (m + 1) (by omega) hc
  have hTE : TE.Tr (m + 1) := MSE.hyp.tr
  have hTEm : TE.Tr m := hTE.of_succ
  have MSEm := TE.mspecs hmon hdeg lv m (by omega) hcm
  have hPE : ∀ P : GPoly (LC m), TE.evP m P = ψ (T.evP m P) := fun P ↦ by
    rw [← TE.sem_poly_code m hTE, ← T.sem_poly_code m hTr]
    exact (TE.sem_MP (m + 1) hTE _).trans ((hTEev (m + 1) _).trans
      (congrArg ψ (T.sem_MP (m + 1) hTr _).symm))
  have hθE : (ψ θ) ^ n + ∑ i ∈ Finset.range n, TE.evP m (Pp.getD i []) * (ψ θ) ^ i = 0 := by
    simp only [hPE, ← map_pow, ← map_mul, ← map_sum, ← map_add, hθ, map_zero]
  -- the curve over `C₁ = Fₘ` of the lifted tower
  set S₁ := TE.nkCurveE m hTE Pp qE csE sE tE s2E t2E hck (ψ θ) hθE with hS₁
  have hS₁F : S₁.F.natDegree = n := polyF_natDegree _ _
  set η₁ : TE.F m := TE.val m η with hη₁
  have hx : S₁.x′ = aeval S₁.x (Polynomial.C η₁) := by
    rw [aeval_C]
    change (TE.ts m)′ = _
    rw [TE.ht m (by omega), hk]
    rfl
  have hnd : ∀ α : AlgebraicClosure (TE.F m),
      α′ ≠ ((Polynomial.C η₁).map (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)))).eval α :=
    fun α ↦ by
      rw [Polynomial.map_C, eval_C]
      exact not_deriv_of_integral η₁ (fun z hz ↦ MSE.hyp.nd m (by omega) η hk z hz) α
        (Algebra.IsIntegral.isIntegral α)
  have hK : ∀ c : TE.F m, (algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c)′ =
      algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) c′ := fun c ↦ deriv_algebraMap c
  have hconstC : ∀ z : E₁, z′ = 0 → z ∈ Set.range (algebraMap (TE.F m) E₁) := fun z hz ↦ by
    obtain ⟨c0, hc0⟩ := TE.hconst z hz
    exact ⟨⟨z, hc0 ▸ TE.const_mem m c0⟩, rfl⟩
  set T₁ := (TE.F m)⟮S₁.x⟯⟮S₁.y⟯ with hT₁
  have hxT : ∀ w ∈ TE.F (m + 1), w ∈ T₁ := fun w hw ↦
    IntermediateField.algebraMap_mem T₁ (⟨w, (TE.mem_F_succ).mp hw⟩ : (TE.F m)⟮S₁.x⟯)
  have hLT : ∀ z : L, ψ z ∈ T₁ := by
    intro z
    have hz := hgen z
    induction hz using IntermediateField.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact mem_adjoin_simple_self _ _
    | algebraMap w => exact hxT _ (hTEmem (m + 1) _ w.2)
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => rw [map_mul]; exact mul_mem h₁ h₂
    | inv w _ h₁ => rw [map_inv₀]; exact inv_mem h₁
  have hCT : ∀ w ∈ Differential.constField L E₁, w ∈ T₁ := by
    intro w hw
    induction hw using IntermediateField.adjoin_induction with
    | mem w hw =>
      obtain ⟨c0, hc0⟩ := hconstC w hw
      rw [← hc0]
      exact S₁.const_mem c0
    | algebraMap z => exact hLT z
    | add w₁ w₂ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | mul w₁ w₂ _ _ h₁ h₂ => exact mul_mem h₁ h₂
    | inv w _ h₁ => exact inv_mem h₁
  -- the integrand is a polynomial in `x, y`
  have hψf : ψ f = ∑ j ∈ Finset.range n, TE.evP m (fp.getD j []) * (ψ θ) ^ j := by
    simp only [hfdef, map_sum, map_mul, map_pow, hPE]
  set Q : (TE.F m)[X][X] := ∑ j ∈ Finset.range n,
    Polynomial.C (GPoly.toPoly (TE.MP m hTEm) (fp.getD j [])) * X ^ j with hQ
  have hQv : S₁.evXY Q = ψ f := by
    rw [hψf, CurveData.evXY, hQ, Polynomial.map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eval_mul, eval_C,
      eval_pow, eval_X]
    congr 1
    exact TE.aeval_toPoly (TE.MP m hTEm) (TE.sem_MP m hTEm) _
  have hfT : ψ f ∈ T₁ := hLT f
  have hfQ : (⟨ψ f, hfT⟩ : T₁) = S₁.evT Q := Subtype.ext (by rw [S₁.coe_evT, hQv])
  have hreg : S₁.RegularFinite (AlgebraicClosure (TE.F m)) ⟨ψ f, hfT⟩ := by
    rw [hfQ]; exact S₁.regularFinite_evT Q
  -- the logarithmic part lies in `Fₘ`
  have heq₁ : ψ f = v′ + ∑ i ∈ s', c i * logDeriv (u i) := by rw [heqL, add_comm]
  -- geometric irreducibility and a branch system above infinity
  have hgeo' : Irreducible (S₁.F.map (mapRingHom (algebraMap (TE.F m)
      (AlgebraicClosure (TE.F m))))) := TE.nkF_geo_of_eisCk m hTEm Pp qE csE sE tE s2E t2E hck _
  -- zero residues along the split branch system above infinity
  have hrde0 := MSEm.rde ⟨(MO Fc ks m).one, []⟩ (fun cw hcw ↦ by simp at hcw)
  simp only [noResCk, Bool.and_eq_true, decide_eq_true_eq] at hcert
  obtain ⟨⟨⟨hplaces, hkk⟩, hpp⟩, hnr⟩ := hcert
  obtain ⟨Ni, hNi, li, hli, hpl⟩ := TE.coeff_place_multiC (Kb := AlgebraicClosure (TE.F m)) m hTEm
    S₁ Pp rfl segs hms βs Θs MR fp hplaces hK
  obtain ⟨r, hr, hcoef⟩ := hpl k hkk p hpp
  set cP : LC m := segResC Fc ks m (segs.getD k (segRD Fc ks m)).1 (segs.getD k (segRD Fc ks m)).2.1
    Pp.length fp ((Θs.getD k []).getD p []) with hcP
  -- the Liouville form with constants of `Fₘ`
  have hcF : ∀ i ∈ s', ∃ ci : TE.F m, algebraMap (TE.F m) E₁ ci = c i := fun i hi ↦ by
    obtain ⟨c0, hc0⟩ := hconstC (c i) (hdata i hi).1
    exact ⟨c0, hc0⟩
  choose! c' hc' using hcF
  have hc'd : ∀ i ∈ s', (c' i)′ = 0 := fun i hi ↦ by
    apply (algebraMap (TE.F m) E₁).injective
    rw [← deriv_algebraMap, hc' i hi, (hdata i hi).1, map_zero]
  set u' : _ → T₁ := fun i ↦ if hi : i ∈ s' then ⟨u i, hCT _ (hdata i hi).2.1⟩ else 1 with hu'
  have hu'0 : ∀ i ∈ s', u' i ≠ 0 := fun i hi h0 ↦ by
    have := congrArg Subtype.val h0
    simp only [hu', dif_pos hi] at this
    exact (hdata i hi).2.2 this
  obtain ⟨β, hβ⟩ := S₁.coeff_liouville_top η₁ hx hK Ni hNi r (S₁.root_of_mem hli hr) s' c'
    hc'd u' hu'0 ⟨v, hCT v hv⟩ ⟨ψ f, hfT⟩ (by
      show ψ f = _
      rw [heq₁]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [hu', dif_pos hi, hc' i hi, logDeriv])
  rw [hfQ, hcoef] at hβ
  -- the residue is a constant of `Fₘ`
  set ρF : TE.F m := (∑ i ∈ s', c' i * ((S₁.embG (infSub Ni) (infSub_injective Ni hNi) r
    (S₁.root_of_mem hli hr) (u' i)).order : TE.F m)) / Ni with hρF
  have hρ : algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) ρF =
      (∑ i ∈ s', algebraMap (TE.F m) (AlgebraicClosure (TE.F m)) (c' i) *
        ((S₁.embG (infSub Ni) (infSub_injective Ni hNi) r (S₁.root_of_mem hli hr)
          (u' i)).order : AlgebraicClosure (TE.F m))) / Ni := by
    rw [hρF, map_div₀, map_sum, map_natCast]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_intCast]
  rw [← hρ, ← map_mul, ← map_add] at hβ
  have hρd : ρF′ = 0 := by
    rw [hρF, Derivation.leibniz_div, map_sum]
    have h1 : ∀ i ∈ s', (c' i * ((S₁.embG (infSub Ni) (infSub_injective Ni hNi) r
        (S₁.root_of_mem hli hr) (u' i)).order : TE.F m))′ = 0 := fun i hi ↦ by
      rw [Derivation.leibniz, hc'd i hi, Derivation.map_intCast]; simp
    rw [Finset.sum_eq_zero h1, Derivation.map_natCast]
    simp
  -- descent of the antiderivative to `Fₘ`
  have hz : ∃ z : TE.F m, z′ = (TE.MP m hTEm).sem cP + ρF * η₁ := by
    by_contra hne
    push_neg at hne
    exact not_deriv_of_integral _ hne β (Algebra.IsIntegral.isIntegral β) hβ.symm
  obtain ⟨z, hz⟩ := hz
  -- the residue is the image of a constant of `Cc`
  obtain ⟨ρc, hρc⟩ := TE.hconst (ρF : E₁) (by rw [← MTower.coe_deriv, hρd]; rfl)
  have hρc' : algebraMap _ (TE.F m) ρc = ρF := Subtype.ext hρc
  -- the parametric Risch equation has a solution with first coordinate `1`
  have hsC : z′ + (TE.MP m hTEm).sem (fCode (MO Fc ks m) ⟨(MO Fc ks m).one, []⟩) * z =
      sC (algebraMap _ (TE.F m)) (TE.MP m hTEm) [1, ρc] [cP, η] := by
    have hf0 : (TE.MP m hTEm).sem (fCode (MO Fc ks m) ⟨(MO Fc ks m).one, []⟩) = 0 := by
      rw [sem_fCode]
      simp [logSumV, (TE.MP m hTEm).sem_one]
    rw [hf0, zero_mul, add_zero, hz, sC]
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, List.getD_cons_zero, List.getD_cons_succ, map_one, one_mul]
    rw [hρc', hη₁, TE.sem_eq_val m hTEm η]
  obtain ⟨βs', hβs', -⟩ := hrde0.complete [cP, η] [1, ρc] (fun i hi ↦ by
    simp only [List.length_cons, List.length_nil] at hi
    rw [List.getD_eq_default _ _ (by simpa using hi)]) z hsC
  have h0 := hβs' 0
  simp only [List.getD_cons_zero] at h0
  have hall := List.all_eq_true.mp hnr
  rw [Finset.sum_eq_zero (fun kk hkk ↦ by
    have hmem : (prdeC Fc ks lv m ⟨(MO Fc ks m).one, []⟩ [cP, η]).getD kk ([], (MO Fc ks m).zero) ∈
        prdeC Fc ks lv m ⟨(MO Fc ks m).one, []⟩ [cP, η] := by
      rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hkk)]
      exact List.getElem_mem _
    have := hall _ hmem
    simp only [beq_iff_eq] at this
    rw [this, map_zero, mul_zero])] at h0
  exact one_ne_zero h0

end MTower

end Tower

end Curves.MT
