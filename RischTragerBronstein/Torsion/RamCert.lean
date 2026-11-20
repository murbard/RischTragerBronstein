import RischTragerBronstein.Torsion.RamRoots

/-!
# Certificates for divisors supported on arbitrary places

`PlaceCert`: fibres `x = α_j` with branch parameters `x = α_j + Tᴺʲ`, places `π` with a certified
approximate representative `y_π` of a root of `F(α + T^{e_π}, Y)`, and for each root above `α_j`
its place, the reparametrization `s` (`N_j = s e_π`) and the rotation `ζ` (`ζ^{N_j} = 1`): the root
is `ρ_π(ζ T)ˢ`-reparametrized, `conjPS ζ s ρ_π`. `Γp` gives the multiplicities of the places.

`PlaceCert.check`: the global checks; `PlaceCert.primeCheck`: the checks at a prime, including a
principal witness for `m_p Γ` modulo `p`.

`split_K`: the certified roots split `F(α_j + T^{N_j}, Y)` over `K((T))`.
-/

open Polynomial HahnSeries

namespace Curves

open Differential LaurentSeries CPoly Sup GTors

/-- The certificate of a divisor supported on places above finitely many fibres. -/
structure PlaceCert (F : Type*) where
  /-- the fibres `(α_j, N_j)` -/
  fib : List (F × ℕ)
  /-- the places `(j, e, y, prec)` -/
  pl : List (ℕ × ℕ × CPoly F × ℕ)
  /-- the roots above `α_j`: `(place, s, ζ)` -/
  rt : List (List (ℕ × ℕ × F))
  /-- the multiplicities of the places -/
  Γp : List ℕ
  /-- a bound `c'_j` per fibre -/
  cf : List ℕ
  /-- the degree of `Γ` on each fibre -/
  dΓ : List ℕ
  /-- the degree of `Γ` divided by `n` -/
  cΓ : ℕ
  /-- the test precisions per fibre -/
  tp : List ℕ

namespace PlaceCert

section Defs

variable {F : Type*} [Field F] [DecidableEq F] (D : PlaceCert F)

def fα (j : ℕ) : F := (D.fib.getD j (0, 1)).1
def fN (j : ℕ) : ℕ := (D.fib.getD j (0, 1)).2
def pj (π : ℕ) : ℕ := (D.pl.getD π (0, 1, [], 0)).1
def pe (π : ℕ) : ℕ := (D.pl.getD π (0, 1, [], 0)).2.1
def py (π : ℕ) : CPoly F := (D.pl.getD π (0, 1, [], 0)).2.2.1
def pp (π : ℕ) : ℕ := (D.pl.getD π (0, 1, [], 0)).2.2.2
def rπ (j k : ℕ) : ℕ := ((D.rt.getD j []).getD k (0, 1, 1)).1
def rs (j k : ℕ) : ℕ := ((D.rt.getD j []).getD k (0, 1, 1)).2.1
def rζ (j k : ℕ) : F := ((D.rt.getD j []).getD k (0, 1, 1)).2.2

/-- The approximation of the root `k` above `α_j`. -/
def apx (j k : ℕ) : CPoly F := conjC (D.rζ j k) (D.rs j k) (D.py (D.rπ j k))

/-- The fibre certificates. -/
def fcerts (n : ℕ) : List (BranchCert F) :=
  (List.range D.fib.length).map fun j ↦ ⟨D.fN j, (List.range n).map (D.apx j), D.tp.getD j 0⟩

/-- The multiplicities `m s Γ_π` of the roots. -/
def bL (n m : ℕ) : List (List ℕ) :=
  (List.range D.fib.length).map fun j ↦
    (List.range n).map fun k ↦ m * (D.rs j k * D.Γp.getD (D.rπ j k) 0)

/-- The fibres. -/
def αs : List F := D.fib.map Prod.fst

/-- The coefficient map. -/
def map {F' : Type*} (f : F → F') : PlaceCert F' :=
  ⟨D.fib.map fun q ↦ (f q.1, q.2), D.pl.map fun q ↦ (q.1, q.2.1, q.2.2.1.map f, q.2.2.2),
    D.rt.map (·.map fun q ↦ (q.1, q.2.1, f q.2.2)), D.Γp, D.cf, D.dΓ, D.cΓ, D.tp⟩

/-- Separation of the approximations below the test precision. -/
def sepCheckP (n : ℕ) : Bool :=
  (List.range D.fib.length).all fun j ↦ (List.range n).all fun k ↦ (List.range n).all fun l ↦
    decide (k = l) || (List.range (D.tp.getD j 0)).any fun i ↦
      decide ((D.apx j k).getD i 0 ≠ (D.apx j l).getD i 0)

/-- **The global checks.** -/
def check (Fc : BPoly F) (n : ℕ) : Bool :=
  decide D.αs.Nodup &&
  (List.range D.pl.length).all (fun π ↦ decide (D.pj π < D.fib.length) && decide (0 < D.pe π) &&
    rootCheck Fc (D.fα (D.pj π)) (D.pe π) (D.pp π) (D.py π)) &&
  decide (D.rt.length = D.fib.length) &&
  (List.range D.fib.length).all (fun j ↦ decide ((D.rt.getD j []).length = n) &&
    (List.range n).all fun k ↦ decide (D.rπ j k < D.pl.length) && decide (D.pj (D.rπ j k) = j) &&
      decide (0 < D.rs j k) && decide (D.fN j = D.rs j k * D.pe (D.rπ j k)) &&
      decide (D.rζ j k ^ D.fN j = 1) && decide (D.tp.getD j 0 ≤ D.rs j k * D.pp (D.rπ j k))) &&
  D.sepCheckP n &&
  (List.range D.pl.length).all (fun π ↦ decide (D.Γp.getD π 0 ≤ D.cf.getD (D.pj π) 0 * D.pe π)) &&
  (List.range D.fib.length).all (fun j ↦
    decide ((∑ k ∈ Finset.range n, D.rs j k * D.Γp.getD (D.rπ j k) 0) = D.fN j * D.dΓ.getD j 0) &&
    decide (D.dΓ.getD j 0 ≤ n * D.cf.getD j 0)) &&
  decide ((∑ j ∈ Finset.range D.fib.length, D.dΓ.getD j 0) = D.cΓ * n) &&
  decide ((∑ π ∈ Finset.range D.pl.length, (D.cf.getD (D.pj π) 0 * D.pe π - D.Γp.getD π 0)) =
    ∑ j ∈ Finset.range D.fib.length, (n * D.cf.getD j 0 - D.dΓ.getD j 0)) &&
  -- completeness of the place data (used only for the existence of `m_p`)
  decide ((∑ π ∈ Finset.range D.pl.length, D.Γp.getD π 0) = D.cΓ * n) &&
  (List.range D.pl.length).all fun π ↦ (List.range D.fib.length).any fun j ↦
    (List.range n).any fun k ↦ decide (D.rπ j k = π)

end Defs

/-- The data at a prime: the multiplier `m_p` and a principal witness for `m_p Γ` modulo `p`. -/
structure PrimeData (p : ℕ) where
  mp : ℕ
  Gw : List (List (ZMod p))

section PrimeDefs

variable {K : Type*} [Field K] [DecidableEq K] {p : ℕ} [Fact p.Prime] (R : RedFns p K)

/-- **The checks at a prime.** -/
def primeCheck (Fc : BPoly K) (n : ℕ) (δL : List ℕ) (Bc : List (BPoly K)) (Dc : CPoly K)
    (xs : List (ZMod p)) (D : PlaceCert K) (Q : PrimeData p) : Bool :=
  D.αs.all R.ok && (List.range D.pl.length).all (fun π ↦ (D.py π).all R.ok) &&
  (List.range D.fib.length).all (fun j ↦ (List.range n).all fun k ↦ R.ok (D.rζ j k)) &&
  decide (D.map R.red).αs.Nodup &&
  (List.range D.fib.length).all (fun j ↦
    decide ((compC (Dc.map R.red) (shiftC (R.red (D.fα j)) 1)).getD (muD Dc (D.fα j) 1) 0 ≠ 0) &&
    (List.range xs.length).all fun i ↦ decide (R.red (D.fα j) ≠ xs.getD i 0)) &&
  (List.range D.pl.length).all (fun π ↦
    decide ((bivEval (derivYB (redBL R Fc)) (shiftC (R.red (D.fα (D.pj π))) (D.pe π))
      ((D.py π).map R.red)).getD
        (ordC (bivEval (derivYB Fc) (shiftC (D.fα (D.pj π)) (D.pe π)) (D.py π))) 0 ≠ 0)) &&
  (D.map R.red).sepCheckP n &&
  decide (1 ≤ Q.mp) &&
  princWitCheckN n (Q.mp * D.cΓ) δL (Bc.map (redBL R)) (Dc.map R.red) (D.map R.red).αs
    ((D.map R.red).fcerts n) ((D.map R.red).bL n Q.mp) Q.Gw

end PrimeDefs

section Facts

variable {F : Type*} [Field F] [DecidableEq F] (D : PlaceCert F)

/-- The content of `check`. -/
structure Facts (Fc : BPoly F) (n : ℕ) : Prop where
  nd : D.αs.Nodup
  pl : ∀ π < D.pl.length, D.pj π < D.fib.length ∧ 0 < D.pe π ∧
    rootCheck Fc (D.fα (D.pj π)) (D.pe π) (D.pp π) (D.py π) = true
  rtl : D.rt.length = D.fib.length
  rt : ∀ j < D.fib.length, (D.rt.getD j []).length = n ∧ ∀ k < n, D.rπ j k < D.pl.length ∧
    D.pj (D.rπ j k) = j ∧ 0 < D.rs j k ∧ D.fN j = D.rs j k * D.pe (D.rπ j k) ∧
    D.rζ j k ^ D.fN j = 1 ∧ D.tp.getD j 0 ≤ D.rs j k * D.pp (D.rπ j k)
  sep : D.sepCheckP n = true
  Γle : ∀ π < D.pl.length, D.Γp.getD π 0 ≤ D.cf.getD (D.pj π) 0 * D.pe π
  dΓ : ∀ j < D.fib.length,
    (∑ k ∈ Finset.range n, D.rs j k * D.Γp.getD (D.rπ j k) 0) = D.fN j * D.dΓ.getD j 0 ∧
    D.dΓ.getD j 0 ≤ n * D.cf.getD j 0
  sum : (∑ j ∈ Finset.range D.fib.length, D.dΓ.getD j 0) = D.cΓ * n
  mP : (∑ π ∈ Finset.range D.pl.length, (D.cf.getD (D.pj π) 0 * D.pe π - D.Γp.getD π 0)) =
    ∑ j ∈ Finset.range D.fib.length, (n * D.cf.getD j 0 - D.dΓ.getD j 0)
  places : (∑ π ∈ Finset.range D.pl.length, D.Γp.getD π 0) = D.cΓ * n
  surj : ∀ π < D.pl.length, ∃ j < D.fib.length, ∃ k < n, D.rπ j k = π

lemma check_spec {Fc : BPoly F} {n : ℕ} (h : D.check Fc n = true) : D.Facts Fc n := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    List.mem_range, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

lemma sepCheckP_spec {n : ℕ} (h : D.sepCheckP n = true) (j : ℕ) (hj : j < D.fib.length) (k l : ℕ)
    (hk : k < n) (hl : l < n) (hkl : k ≠ l) :
    ∃ i < D.tp.getD j 0, (D.apx j k).getD i 0 ≠ (D.apx j l).getD i 0 := by
  simp only [sepCheckP, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true] at h
  rcases h j hj k hk l hl with h1 | h1
  · exact absurd h1 hkl
  · exact h1

lemma fcerts_getD (n : ℕ) (j : ℕ) (hj : j < D.fib.length) :
    (D.fcerts n).getD j ⟨1, [], 0⟩ = ⟨D.fN j, (List.range n).map (D.apx j), D.tp.getD j 0⟩ := by
  rw [fcerts, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]

lemma bL_getD (n m j k : ℕ) (hj : j < D.fib.length) (hk : k < n) :
    ((D.bL n m).getD j []).getD k 0 = m * (D.rs j k * D.Γp.getD (D.rπ j k) 0) := by
  have e1 : (D.bL n m).getD j [] =
      (List.range n).map fun k ↦ m * (D.rs j k * D.Γp.getD (D.rπ j k) 0) := by
    rw [bL, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
  rw [e1, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range]

lemma αs_getD (j : ℕ) (hj : j < D.fib.length) : D.αs.getD j 0 = D.fα j := by
  rw [αs, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, fα,
    List.getD_eq_getElem _ _ hj]

variable {F' : Type*} (f : F → F')

@[simp] lemma map_fib_length : (D.map f).fib.length = D.fib.length := by simp [map]
@[simp] lemma map_pl_length : (D.map f).pl.length = D.pl.length := by simp [map]
@[simp] lemma map_cΓ : (D.map f).cΓ = D.cΓ := rfl
@[simp] lemma map_Γp : (D.map f).Γp = D.Γp := rfl
@[simp] lemma map_tp : (D.map f).tp = D.tp := rfl

lemma map_fα [Field F'] (j : ℕ) (hj : j < D.fib.length) : (D.map f).fα j = f (D.fα j) := by
  simp only [fα, map]
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getD_eq_getElem _ _ hj]

lemma map_fN [Field F'] (j : ℕ) (hj : j < D.fib.length) : (D.map f).fN j = D.fN j := by
  simp only [fN, map]
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getD_eq_getElem _ _ hj]

lemma map_pj [Field F'] (π : ℕ) (hπ : π < D.pl.length) : (D.map f).pj π = D.pj π := by
  simp only [pj, map]
  rw [List.getD_eq_getElem _ _ (by simpa using hπ), List.getElem_map, List.getD_eq_getElem _ _ hπ]

lemma map_pe [Field F'] (π : ℕ) (hπ : π < D.pl.length) : (D.map f).pe π = D.pe π := by
  simp only [pe, map]
  rw [List.getD_eq_getElem _ _ (by simpa using hπ), List.getElem_map, List.getD_eq_getElem _ _ hπ]

lemma map_pp [Field F'] (π : ℕ) (hπ : π < D.pl.length) : (D.map f).pp π = D.pp π := by
  simp only [pp, map]
  rw [List.getD_eq_getElem _ _ (by simpa using hπ), List.getElem_map, List.getD_eq_getElem _ _ hπ]

lemma map_py [Field F'] (π : ℕ) (hπ : π < D.pl.length) : (D.map f).py π = (D.py π).map f := by
  simp only [py, map]
  rw [List.getD_eq_getElem _ _ (by simpa using hπ), List.getElem_map, List.getD_eq_getElem _ _ hπ]

lemma map_rt_getD (j : ℕ) (hj : j < D.rt.length) :
    (D.map f).rt.getD j [] = (D.rt.getD j []).map fun q ↦ (q.1, q.2.1, f q.2.2) := by
  simp only [map]
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getD_eq_getElem _ _ hj]

lemma map_rπ [Field F'] (j k : ℕ) (hj : j < D.rt.length) (hk : k < (D.rt.getD j []).length) :
    (D.map f).rπ j k = D.rπ j k := by
  simp only [rπ]
  rw [map_rt_getD D f j hj, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
    List.getD_eq_getElem _ _ hk]

lemma map_rs [Field F'] (j k : ℕ) (hj : j < D.rt.length) (hk : k < (D.rt.getD j []).length) :
    (D.map f).rs j k = D.rs j k := by
  simp only [rs]
  rw [map_rt_getD D f j hj, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
    List.getD_eq_getElem _ _ hk]

lemma map_rζ [Field F'] (j k : ℕ) (hj : j < D.rt.length) (hk : k < (D.rt.getD j []).length) :
    (D.map f).rζ j k = f (D.rζ j k) := by
  simp only [rζ]
  rw [map_rt_getD D f j hj, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
    List.getD_eq_getElem _ _ hk]

end Facts

end PlaceCert

section Gen

variable {L : Type*} [Field L]

lemma root_ofPS (G : L[X][X]) (e : ℕ) (α : L) (ρ : PowerSeries L)
    (h : (G.map (psSubR e α)).eval ρ = 0) :
    (G.map (branchSub (C := L) (K := L) e α)).eval (ofPowerSeries ℤ L ρ) = 0 := by
  have := eval_psSubR_map (RingHom.id L) e α G ρ
  simp only [PowerSeries.map_id, RingHom.id_apply, Polynomial.mapRingHom_id,
    Polynomial.map_id, id] at this
  rw [← this, h, map_zero]

/-- **Conjugates of a representative are roots.** -/
lemma conj_root (G : L[X][X]) (e s N : ℕ) (hs : 0 < s) (hN : N = s * e) (ζ : L) (hζ : ζ ≠ 0)
    (hζN : ζ ^ N = 1) (α : L) (ρ : PowerSeries L) (h : (G.map (psSubR e α)).eval ρ = 0) :
    (G.map (branchSub (C := L) (K := L) N α)).eval (ofPowerSeries ℤ L (conjPS ζ s ρ)) = 0 := by
  rw [ofPS_conjPS ζ hζ s hs]
  refine rot_root ζ hζ N hζN α G _ ?_
  have hc : (lsub s hs).comp (branchSub (C := L) (K := L) e α) = branchSub N α := by
    rw [lsub_comp_branchSub, hN, mul_comm]
  rw [← hc, ← Polynomial.map_map, eval_map, eval₂_at_apply, root_ofPS G e α ρ h, map_zero]

lemma conj_approx {F : Type*} [Field F] [DecidableEq F] (ψ : F →+* L) (ζ : F) {s : ℕ} (hs : 0 < s)
    (ρ : PowerSeries L) (y : CPoly F) {P tp : ℕ}
    (hP : (PowerSeries.X : PowerSeries L) ^ P ∣ ρ - thetaT ψ (toPoly y)) (htp : tp ≤ s * P) :
    (PowerSeries.X : PowerSeries L) ^ tp ∣ conjPS (ψ ζ) s ρ - thetaT ψ (toPoly (conjC ζ s y)) := by
  rw [thetaT_conjC ψ ζ hs, ← conjPS_sub]
  exact (pow_dvd_pow _ htp).trans (X_pow_dvd_conjPS _ hs hP)

/-- **Separated approximations give distinct roots.** -/
lemma conj_inj {F : Type*} [Field F] [DecidableEq F] (ψ : F →+* L) {n tp : ℕ}
    (Y : Fin n → PowerSeries L) (y : Fin n → CPoly F)
    (hY : ∀ k, (PowerSeries.X : PowerSeries L) ^ tp ∣ Y k - thetaT ψ (toPoly (y k)))
    (hsep : ∀ k l, k ≠ l → ∃ i < tp, (y k).getD i 0 ≠ (y l).getD i 0) :
    Function.Injective fun k ↦ ofPowerSeries ℤ L (Y k) := by
  intro k l hkl
  have hY' : Y k = Y l := HahnSeries.ofPowerSeries_injective hkl
  by_contra hne
  obtain ⟨i, hi, hd⟩ := hsep k l hne
  have h1 := (PowerSeries.X_pow_dvd_iff.mp (hY k)) i hi
  have h2 := (PowerSeries.X_pow_dvd_iff.mp (hY l)) i hi
  rw [map_sub, coeff_thetaT, sub_eq_zero] at h1 h2
  rw [hY', h2] at h1
  exact hd (ψ.injective h1.symm)

lemma split_of_roots (G : L[X][X]) (hG : G.Monic) {n : ℕ} (hn : G.natDegree = n) (N : ℕ) (α : L)
    (r : Fin n → LaurentSeries L) (hr : ∀ k, (G.map (branchSub (C := L) (K := L) N α)).eval (r k) = 0)
    (hinj : Function.Injective r) :
    G.map (branchSub (C := L) (K := L) N α) = ∏ k, (X - Polynomial.C (r k)) := by
  classical
  exact eq_prod_of_distinct_roots _ (hG.map _) (by rw [hG.natDegree_map, hn]) r hinj hr

end Gen

section RepK

variable {K : Type*} [Field K] [DecidableEq K]

/-- The representative of the place `π` over `K`. -/
noncomputable def repK (Fc : BPoly K) (D : PlaceCert K) (π : ℕ) : PowerSeries K :=
  if h : rootCheck Fc (D.fα (D.pj π)) (D.pe π) (D.pp π) (D.py π) = true then
    Classical.choose (rep_root_field (RingHom.id K) h) else 0

lemma repK_spec (Fc : BPoly K) (D : PlaceCert K) (π : ℕ)
    (h : rootCheck Fc (D.fα (D.pj π)) (D.pe π) (D.pp π) (D.py π) = true) :
    ((toB Fc).map (psSubR (D.pe π) (D.fα (D.pj π)))).eval (repK Fc D π) = 0 ∧
      (PowerSeries.X : PowerSeries K) ^ D.pp π ∣
        repK Fc D π - thetaT (RingHom.id K) (toPoly (D.py π)) := by
  rw [repK, dif_pos h]
  obtain ⟨h1, h2⟩ := Classical.choose_spec (rep_root_field (RingHom.id K) h)
  generalize Classical.choose (rep_root_field (RingHom.id K) h) = c at h1 h2 ⊢
  simp only [repEq, Polynomial.mapRingHom_id, Polynomial.map_id, RingHom.id_apply] at h1
  exact ⟨h1, h2⟩

/-- The roots above `α_j` over `K`. -/
noncomputable def rCK (Fc : BPoly K) (D : PlaceCert K) (j k : ℕ) : LaurentSeries K :=
  ofPowerSeries ℤ K (conjPS (D.rζ j k) (D.rs j k) (repK Fc D (D.rπ j k)))

lemma ne_zero_of_pow_eq_one {M : Type*} [MonoidWithZero M] [Nontrivial M] {ζ : M} {N : ℕ}
    (hN : 0 < N) (h : ζ ^ N = 1) : ζ ≠ 0 := by
  rintro rfl
  rw [zero_pow hN.ne'] at h
  exact zero_ne_one h

/-- **The certified roots split the fibres over `K`.** -/
theorem split_K {L : Type*} [Field L] [Algebra K L] (S : CurveData K L) (Fc : BPoly K)
    (hSF : S.F = toB Fc) (hmon : (toB Fc).Monic) (D : PlaceCert K) (hD : D.Facts Fc S.F.natDegree)
    (j : ℕ) (hj : j < D.fib.length) :
    S.F.map (branchSub (C := K) (K := K) (D.fN j) (D.fα j)) =
        ∏ k : Fin S.F.natDegree, (X - Polynomial.C (rCK Fc D j k)) ∧
      Function.Injective fun k : Fin S.F.natDegree ↦ rCK Fc D j k := by
  obtain ⟨-, hrt⟩ := hD.rt j hj
  have hroot' : ∀ k < S.F.natDegree,
      (S.F.map (branchSub (C := K) (K := K) (D.fN j) (D.fα j))).eval (rCK Fc D j k) = 0 := by
    intro k hk
    obtain ⟨hπ, hpj, hs, hN, hζ, -⟩ := hrt k hk
    have hN0 : 0 < D.fN j := by rw [hN]; exact Nat.mul_pos hs (hD.pl _ hπ).2.1
    obtain ⟨hr, -⟩ := repK_spec Fc D (D.rπ j k) (hD.pl _ hπ).2.2
    rw [hpj] at hr
    rw [rCK, hSF]
    exact conj_root _ _ _ _ hs hN _ (ne_zero_of_pow_eq_one hN0 hζ) hζ _ _ hr
  have hroot : ∀ k : Fin S.F.natDegree,
      (S.F.map (branchSub (C := K) (K := K) (D.fN j) (D.fα j))).eval (rCK Fc D j k) = 0 :=
    fun k ↦ hroot' k k.2
  have hinj : Function.Injective fun k : Fin S.F.natDegree ↦ rCK Fc D j k := by
    refine conj_inj (RingHom.id K) (tp := D.tp.getD j 0)
      (fun k : Fin S.F.natDegree ↦ conjPS (D.rζ j k) (D.rs j k) (repK Fc D (D.rπ j k)))
      (fun k ↦ D.apx j k) (fun k ↦ ?_) (fun k l hkl ↦ ?_)
    · obtain ⟨hπ, -, hs, -, -, htp⟩ := hrt k k.2
      obtain ⟨-, hd⟩ := repK_spec Fc D (D.rπ j k) (hD.pl _ hπ).2.2
      exact conj_approx (RingHom.id K) (D.rζ j k) hs _ _ hd htp
    · exact PlaceCert.sepCheckP_spec D hD.sep j hj k l k.2 l.2 (Fin.val_ne_of_ne hkl)
  exact ⟨split_of_roots S.F S.monic rfl _ _ _ hroot hinj, hinj⟩

end RepK

end Curves
