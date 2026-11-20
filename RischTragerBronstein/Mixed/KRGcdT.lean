import RischTragerBronstein.Mixed.KRGcd

/-!
# The column computation of `krDecide`: the tower facts

`kr_gcd_coprime`: the descended norm `W₀` of a witness and `Yⁿ − Â` are coprime over `K_{m+1}`
(`coprime_norm_abstract` after reading the codes in `Kₘ[t]`: `trC (unTr y) = y`, `trC 1 = 1`).
-/

open Polynomial CPoly CPoly.Kron

set_option linter.unusedSectionVars false

namespace Curves.MT

open Sup Curves.LT Tower.PrimN Tower.NestP Tower.NestM Tower.NestX

universe u

variable {Fc : BPoly ℚ} {ks : (m : ℕ) → KindC m} {lv : (m : ℕ) → LC m}
variable {Cc L : Type u} [Field Cc] [Field L] [Algebra Cc L] [Differential Cc]
  [Differential L] [DifferentialAlgebra Cc L] [CharZero Cc] [CharZero L]

namespace MTower

variable (T : MTower Fc ks Cc L) [Fact (Irreducible (toPoly (fKc Fc)))]

lemma trC_one_T (m : ℕ) (hm : T.Tr m) : trC Fc m (MO Fc ks m).one = 1 :=
  (T.psiF m hm).injective (by rw [T.psiF_trC, (T.MP m hm).sem_one, map_one])

lemma trC_unTr_T (m : ℕ) (hm : T.Tr m) (y : KF Fc m) : trC Fc m (unTr Fc m y) = y :=
  (T.psiF m hm).injective (by rw [T.psiF_trC, T.sem_unTr])

lemma toRF_trC_pcP_unTr (m : ℕ) (hm : T.Tr m) (c : CPoly (KF Fc m)) :
    RFC.toRF (show RFC.RatFuncC (KF Fc m) from trC Fc (m + 1) (pcP Fc ks m (c.map (unTr Fc m)))) =
      algebraMap (KF Fc m)[X] (RatFunc (KF Fc m)) (toPoly c) := by
  show RFC.toRF (RFC.mk ((c.map (unTr Fc m)).map (trC Fc m)) ([(MO Fc ks m).one].map (trC Fc m))) = _
  rw [List.map_map, List.map_singleton, T.trC_one_T m hm, RFC.toRF_mk]
  have : (trC Fc m ∘ unTr Fc m) = id := funext fun y ↦ T.trC_unTr_T m hm y
  rw [this, List.map_id]
  simp [CPoly.toPoly]

lemma toRF_trC_pcP (m : ℕ) (hm : T.Tr m) (P : GPoly (LC m)) :
    RFC.toRF (show RFC.RatFuncC (KF Fc m) from trC Fc (m + 1) (pcP Fc ks m P)) =
      algebraMap (KF Fc m)[X] (RatFunc (KF Fc m)) (toPoly (P.map (trC Fc m))) := by
  show RFC.toRF (RFC.mk (P.map (trC Fc m)) ([(MO Fc ks m).one].map (trC Fc m))) = _
  rw [List.map_singleton, T.trC_one_T m hm, RFC.toRF_mk]
  simp [CPoly.toPoly]

/-- **The descended norm of a witness is coprime to `Yⁿ − Â`.** -/
theorem kr_gcd_coprime (m n : ℕ) [Fact (Irreducible (toPoly (cycK Fc m n)))] (hn : 1 < n) (hm : T.Tr m) (Wb : BPoly (NFz Fc m n)) (hWb0 : toB Wb ≠ 0)
    (hWbd : (toB Wb).natDegree < n) (W0 : BPoly (KF Fc m))
    (hdesc : descendNF Fc m n (normNF Fc m n Wb) = some W0) (Ah : GPoly (LC m))
    (hAsq : Squarefree (toPoly (Ah.map (trC Fc m))))
    (hAd : 0 < (toPoly (Ah.map (trC Fc m))).natDegree) :
    IsCoprime (toPoly ((W0.map fun c ↦ pcP Fc ks m (c.map (unTr Fc m))).map (trC Fc (m + 1))))
      (toPoly ((-(trC Fc (m + 1) (pcP Fc ks m Ah))) :: (List.replicate (n - 1) 0 ++ [1]))) := by
  have hn0 : 0 < n := by omega
  rw [← isCoprime_map (RFC.toRFHom (K := KF Fc m))]
  have hW : (toPoly ((W0.map fun c ↦ pcP Fc ks m (c.map (unTr Fc m))).map (trC Fc (m + 1)))).map
      (RFC.toRFHom (K := KF Fc m)) = (toB W0).map (algebraMap (KF Fc m)[X] (RatFunc (KF Fc m))) := by
    rw [← toPoly_map', List.map_map, List.map_map, ← toPoly_map_toB]
    congr 1
    refine List.map_congr_left fun c _ ↦ ?_
    exact T.toRF_trC_pcP_unTr m hm c
  have hM : (toPoly ((-(trC Fc (m + 1) (pcP Fc ks m Ah))) :: (List.replicate (n - 1) 0 ++ [1]))).map
      (RFC.toRFHom (K := KF Fc m)) = (X ^ n - C (toPoly (Ah.map (trC Fc m))) : (KF Fc m)[X][X]).map
        (algebraMap (KF Fc m)[X] (RatFunc (KF Fc m))) := by
    rw [toPoly_xnSubC _ n hn0, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_pow, map_X, map_X, map_C, map_C]
    congr 2
    exact T.toRF_trC_pcP m hm Ah
  rw [hW, hM]
  refine coprime_norm_abstract (eNF Fc m n) n hn0 _ hAsq hAd (toB W0)
    ((unitsN n).map fun u ↦ toB (Wb.map (·.map (tauN Fc m n u)))) ?_ ?_
  · rw [← toB_mapL', show (eNF Fc m n : KF Fc m → NFz Fc m n) = embNF Fc m n from rfl,
      ← descendNF_spec Fc m n _ W0 hdesc, normNF_eq, toB_foldr_mulB, List.map_map]
    rfl
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    have huc : Nat.Coprime u n := by simpa using (List.mem_filter.mp hu).2
    have hu0 : 0 < u := by
      rcases Nat.eq_zero_or_pos u with h | h
      · rw [h, Nat.coprime_zero_left] at huc; omega
      · exact h
    have e : toB (Wb.map (·.map (tauN Fc m n u))) =
        (toB Wb).map (mapRingHom (tauHom Fc m n hn0 u huc hu0)) := by
      rw [← toB_mapL']; rfl
    rw [e]
    have hinj : Function.Injective (mapRingHom (tauHom Fc m n hn0 u huc hu0)) := fun a b h ↦
      Polynomial.map_injective _ (tauN_injective Fc m n hn0 u huc hu0) h
    have hinj2 : Function.Injective
        (Polynomial.map (mapRingHom (tauHom Fc m n hn0 u huc hu0)) : (NFz Fc m n)[X][X] → _) :=
      Polynomial.map_injective _ hinj
    refine ⟨fun h0 ↦ hWb0 (hinj2 (h0.trans (Polynomial.map_zero _).symm)), ?_⟩
    exact lt_of_le_of_lt (natDegree_map_le) hWbd

end MTower

end Curves.MT
