import RischTragerBronstein.Algebraic.EllSolve

/-!
# Every non-zero solution of the linear system is a valid certificate

For `A + B y` vanishing to order `mᵢ` at `(αᵢ, yᵢ)` with `deg A ≤ M₀/2`, `deg B ≤ (M₀−3)/2`:

* the norm `N = A² − B² p` is `λ ∏ (x − αᵢ)^{mᵢ}`, `λ ≠ 0`;
* at each `αᵢ` (`mᵢ ≥ 1`), `M ≡ mᵢ yᵢ (x − αᵢ)^{mᵢ − 1} N₁ (mod (x − αᵢ)^{mᵢ})`, `N = (x − αᵢ)^{mᵢ} N₁`
  (`local_residue`): `M/N` has a simple pole with residue `mᵢ yᵢ`;
* hence `Gd N ∣ Gn N − Gd c M` and `certCheck` succeeds.
-/

open Polynomial

namespace EllAlgo

variable {K : Type*} [Field K] [CharZero K]

/-- **The local residue congruence** (shifted coordinates, abstract derivatives). -/
lemma local_residue (a b da db P dP Y dY V dV F dF Z : K[X]) (y₀ : K) (k : ℕ)
    (hV : a + b * Y = X ^ (k + 1) * V)
    (hdV : da + db * Y + b * dY = C ((k : K) + 1) * X ^ k * V + X ^ (k + 1) * dV)
    (hE : P - Y ^ 2 = X ^ (k + 2) * F)
    (hdE : dP - 2 * Y * dY = C ((k : K) + 2) * X ^ (k + 1) * F + X ^ (k + 2) * dF)
    (hZ : Y - C y₀ = X * Z) :
    (2 * P * (a * db - da * b) + a * b * dP) -
      C ((k : K) + 1) * C y₀ * X ^ k * ((V * (a - b * Y)) - X * b ^ 2 * F) =
      X ^ (k + 1) * (2 * X * F * (a * db - da * b) + a * b * (C ((k : K) + 2) * F + X * dF) +
        C ((k : K) + 1) * Z * V * (a - b * Y) + Y * (dV * (a - b * Y) - V * (da - db * Y - b * dY)) +
        C ((k : K) + 1) * C y₀ * b ^ 2 * F) := by
  linear_combination (2 * (a * db - da * b)) * hE + (a * b) * hdE +
    (Y * (a - b * Y)) * hdV - (Y * (da - db * Y - b * dY)) * hV +
    (C ((k : K) + 1) * X ^ k * V * (a - b * Y)) * hZ

lemma comp_shift_back (f : K[X]) (α : K) : (f.comp (X + C α)).comp (X - C α) = f := by
  rw [comp_assoc]; simp

lemma derivative_comp_shift (f : K[X]) (α : K) :
    derivative (f.comp (X + C α)) = (derivative f).comp (X + C α) := by
  rw [derivative_comp]; simp

/-- **Residue of `M/N` at a point where `A + B y` vanishes to order `m ≥ 1`.** -/
theorem residue_at [DecidableEq K] (pC : CPoly K) (A B : K[X]) (α y₀ : K) (m : ℕ) (hm : 1 ≤ m) (hy₀ : y₀ ≠ 0)
    (hpα : (CPoly.toPoly pC).eval α = y₀ ^ 2)
    (hloc : X ^ m ∣ locVal pC A B (α, y₀, m)) :
    ∃ N₁ : K[X], A ^ 2 - B ^ 2 * CPoly.toPoly pC = (X - C α) ^ m * N₁ ∧
      (X - C α) ^ m ∣ (2 * CPoly.toPoly pC * (A * derivative B - derivative A * B) +
        A * B * derivative (CPoly.toPoly pC)) - C ((m : K) * y₀) * (X - C α) ^ (m - 1) * N₁ := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  set p := CPoly.toPoly pC
  set pt := shiftPoly pC α
  have hpt : CPoly.toPoly pt = p.comp (X + C α) := toPoly_shiftPoly α pC
  have hpt0 : (CPoly.toPoly pt).coeff 0 = y₀ ^ 2 := by
    rw [hpt, coeff_zero_eq_eval_zero, eval_comp]; simpa using hpα
  set Y := CPoly.toPoly (sqrtSeries pt y₀ (k + 1))
  set Y' := CPoly.toPoly (sqrtSeries pt y₀ (k + 2))
  set a := A.comp (X + C α)
  set b := B.comp (X + C α)
  set P := p.comp (X + C α)
  -- the data of `local_residue`
  simp only [locVal, Yq] at hloc
  obtain ⟨F, hF⟩ := sqrtSeries_dvd pt y₀ hy₀ hpt0 (k + 2) (by omega)
  rw [hpt] at hF
  obtain ⟨G, hG⟩ := sqrtSeries_succ_sub pt y₀ (k + 1) (by omega)
  have hloc' : X ^ (k + 1) ∣ a + b * Y' := by
    have : a + b * Y' = (a + b * Y) + b * (Y' - Y) := by ring
    rw [this]
    exact dvd_add hloc (dvd_mul_of_dvd_right ⟨G, hG⟩ _)
  obtain ⟨V, hV⟩ := hloc'
  obtain ⟨Z, hZ⟩ : X ∣ Y' - C y₀ := by
    rw [X_dvd_iff, coeff_sub, coeff_C_zero, coeff_zero_sqrtSeries, sub_self]
  have hdV := congrArg derivative hV
  simp only [derivative_add, derivative_mul, derivative_X_pow] at hdV
  push_cast at hdV
  have hdE := congrArg derivative hF
  simp only [derivative_sub, derivative_mul, derivative_X_pow, derivative_pow, derivative_X,
    mul_one] at hdE
  rw [show k + 2 - 1 = k + 1 by omega, show (2 : ℕ) - 1 = 1 by rfl, pow_one] at hdE
  push_cast at hdE
  rw [map_ofNat] at hdE
  have key := local_residue a b (derivative a) (derivative b) P (derivative P) Y' (derivative Y')
    V (derivative V) F (derivative F) Z y₀ k hV (by
      linear_combination hdV) hF (by
      linear_combination hdE) hZ
  -- unshift
  refine ⟨((V * (a - b * Y')) - X * b ^ 2 * F).comp (X - C α), ?_, ?_⟩
  · have e : a ^ 2 - b ^ 2 * P = X ^ (k + 1) * ((V * (a - b * Y')) - X * b ^ 2 * F) := by
      linear_combination (a - b * Y') * hV - b ^ 2 * hF
    have := congrArg (fun f ↦ f.comp (X - C α)) e
    simp only [sub_comp, pow_comp, mul_comp, X_comp, a, b, P, comp_shift_back] at this ⊢
    exact this
  · have hda : derivative a = (derivative A).comp (X + C α) := derivative_comp_shift A α
    have hdb : derivative b = (derivative B).comp (X + C α) := derivative_comp_shift B α
    have hdP : derivative P = (derivative p).comp (X + C α) := derivative_comp_shift p α
    rw [hda, hdb, hdP] at key
    have hdvd : (X - C α) ^ (k + 1) ∣ (2 * P * (a * (derivative B).comp (X + C α) -
        (derivative A).comp (X + C α) * b) + a * b * (derivative p).comp (X + C α) -
        C ((k : K) + 1) * C y₀ * X ^ k * (V * (a - b * Y') - X * b ^ 2 * F)).comp (X - C α) := by
      rw [key, mul_comp, pow_comp, X_comp]
      exact dvd_mul_right _ _
    rw [show ((k + 1 : ℕ) : K) * y₀ = ((k : K) + 1) * y₀ by push_cast; ring, C_mul,
      Nat.add_sub_cancel]
    convert hdvd using 1
    simp only [sub_comp, add_comp, pow_comp, mul_comp, X_comp, C_comp, a, b, P,
      comp_shift_back, ofNat_comp, Nat.cast_ofNat]

/-! ### The norm -/

lemma norm_ne_zero (p A B : K[X]) (hp : p.natDegree = 3) (h : A ≠ 0 ∨ B ≠ 0) :
    A ^ 2 - B ^ 2 * p ≠ 0 := by
  intro h0
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  by_cases hB : B = 0
  · subst hB
    have : A ^ 2 = 0 := by linear_combination h0
    exact h.elim (fun hA ↦ hA (pow_eq_zero_iff two_ne_zero |>.mp this)) (fun h ↦ h rfl)
  · have hA : A ≠ 0 := by
      rintro rfl
      have : B ^ 2 * p = 0 := by linear_combination -h0
      exact mul_ne_zero (pow_ne_zero 2 hB) hp0 this
    have e : A ^ 2 = B ^ 2 * p := by linear_combination h0
    have := congrArg natDegree e
    rw [natDegree_pow, natDegree_mul (pow_ne_zero 2 hB) hp0, natDegree_pow, hp] at this
    omega

lemma norm_natDegree_le (p A B : K[X]) (hp : p.natDegree = 3) (M₀ : ℕ)
    (hA : 2 * A.natDegree ≤ M₀) (hB : B = 0 ∨ 2 * B.natDegree + 3 ≤ M₀) :
    (A ^ 2 - B ^ 2 * p).natDegree ≤ M₀ := by
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_pow_le).trans (by omega)) ?_)
  rcases hB with rfl | hB
  · simp
  · refine (natDegree_mul_le).trans ?_
    rw [hp]
    exact Nat.add_le_of_le_sub (by omega) ((natDegree_pow_le).trans (by omega))

/-- **The shape of the norm**: divisible by `∏ (X − αᵢ)^{mᵢ}` and of degree at most `∑ mᵢ`. -/
lemma norm_shape' {ι' : Type*} (s : Finset ι') (α : ι' → K) (hinj : Set.InjOn α s) (m : ι' → ℕ)
    (N : K[X]) (hN0 : N ≠ 0) (hdvd : ∀ i ∈ s, (X - C (α i)) ^ m i ∣ N)
    (hdeg : N.natDegree ≤ ∑ i ∈ s, m i) :
    ∃ lam : K, lam ≠ 0 ∧ N = C lam * ∏ i ∈ s, (X - C (α i)) ^ m i := by
  have hcop : (s : Set ι').Pairwise (Function.onFun IsCoprime fun i ↦ (X - C (α i)) ^ m i) := by
    intro i hi j hj hij
    exact ((isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr fun h ↦ hij (hinj hi hj h)).isUnit)).pow
  obtain ⟨Kq, hK⟩ := Finset.prod_dvd_of_coprime hcop hdvd
  have hmon : (∏ i ∈ s, (X - C (α i)) ^ m i).Monic :=
    monic_prod_of_monic _ _ fun i _ ↦ (monic_X_sub_C _).pow _
  have hPdeg : (∏ i ∈ s, (X - C (α i)) ^ m i).natDegree = ∑ i ∈ s, m i := by
    rw [natDegree_prod_of_monic _ _ fun i _ ↦ (monic_X_sub_C _).pow _]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  have hK0 : Kq ≠ 0 := by rintro rfl; rw [mul_zero] at hK; exact hN0 hK
  have hKdeg : Kq.natDegree = 0 := by
    have := congrArg natDegree hK
    rw [natDegree_mul hmon.ne_zero hK0, hPdeg] at this
    omega
  refine ⟨Kq.coeff 0, fun h ↦ hK0 ?_, ?_⟩
  · rw [eq_C_of_natDegree_eq_zero hKdeg, h, map_zero]
  · rw [hK, mul_comm, ← eq_C_of_natDegree_eq_zero hKdeg]

/-! ### The denominator of `G` -/

lemma fracG_local [DecidableEq K] (B : CPoly K) (D : ℕ) : ∀ (pts : List (K × K × ℤ)), ∀ q ∈ pts,
    ∃ Gq H : K[X], CPoly.toPoly (fracG B D pts).2 = (X - C q.1) * Gq ∧
      CPoly.toPoly (fracG B D pts).1 = C ((q.2.2 : K) / D * q.2.1) * Gq + (X - C q.1) * H
  | [], q, hq => by simp at hq
  | q' :: t, q, hq => by
    simp only [fracG, CPoly.toPoly_mul, CPoly.toPoly_add, CPoly.toPoly_smul, toPoly_lin]
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨CPoly.toPoly (fracG B D t).2, CPoly.toPoly (fracG B D t).1, by ring, by ring⟩
    · obtain ⟨Gq, H, h1, h2⟩ := fracG_local B D t q hq
      refine ⟨Gq * (X - C q'.1), H * (X - C q'.1) + C ((q'.2.2 : K) / D * q'.2.1) * Gq, ?_, ?_⟩
      · rw [h1]; ring
      · rw [h1, h2]; ring

lemma fracG_den [DecidableEq K] (B : CPoly K) (D : ℕ) : ∀ (pts : List (K × K × ℤ)),
    CPoly.toPoly (fracG B D pts).2 = (pts.map fun q ↦ X - C q.1).prod
  | [] => by simp [fracG]
  | q :: t => by
    simp only [fracG, CPoly.toPoly_mul, toPoly_lin, fracG_den B D t, List.map_cons,
      List.prod_cons]
    ring

lemma divMod_exact [DecidableEq K] (p d : CPoly K) (hd : CPoly.toPoly d ≠ 0)
    (hdvd : CPoly.toPoly d ∣ CPoly.toPoly p) :
    CPoly.toPoly p = CPoly.toPoly (CPoly.divMod p d).1 * CPoly.toPoly d := by
  have hspec := CPoly.divMod_spec p d
  have hrem : CPoly.toPoly d ∣ CPoly.toPoly (CPoly.divMod p d).2 := by
    have : CPoly.toPoly (CPoly.divMod p d).2 =
        CPoly.toPoly p - CPoly.toPoly (CPoly.divMod p d).1 * CPoly.toPoly d := by
      rw [hspec]; ring
    rw [this]
    exact dvd_sub hdvd (Dvd.intro_left _ rfl)
  have h0 := eq_zero_of_dvd_of_degree_lt hrem (CPoly.divMod_degree_lt p d hd)
  rw [hspec, h0, add_zero]

lemma prod_map_eq_fin {M : Type*} [CommMonoid M] {β : Type*} (g : β → M) :
    ∀ l : List β, (l.map g).prod = ∏ i : Fin l.length, g l[i]
  | [] => by simp
  | q :: t => by
    rw [List.map_cons, List.prod_cons, prod_map_eq_fin g t]
    show _ = ∏ i : Fin (t.length + 1), g (q :: t)[i]
    rw [Fin.prod_univ_succ]
    simp

/-- The per-point divisibility `(X − α)^{m+1} ∣ Gn N − Gd c M`. -/
lemma point_dvd (Gd Gn N M Gq H N₁ T : K[X]) (α cc rβ y₀ : K) (k : ℕ)
    (hGd : Gd = (X - C α) * Gq) (hGn : Gn = C rβ * Gq + (X - C α) * H)
    (hN : N = (X - C α) ^ (k + 1) * N₁)
    (hT : M - C (((k + 1 : ℕ) : K) * y₀) * (X - C α) ^ k * N₁ = (X - C α) ^ (k + 1) * T)
    (hc : cc * (((k + 1 : ℕ) : K) * y₀) = rβ) :
    (X - C α) ^ (k + 1 + 1) ∣ Gn * N - Gd * (C cc * M) := by
  refine ⟨H * N₁ - Gq * C cc * T, ?_⟩
  have hc' : C cc * C (((k + 1 : ℕ) : K) * y₀) = C rβ := by rw [← C_mul, hc]
  rw [hGd, hGn, hN]
  linear_combination (-(X - C α) * Gq * C cc) * hT - ((X - C α) ^ (k + 1) * Gq * N₁) * hc'

/-- **Every non-zero relation is a valid certificate** (any cubic `pC`). -/
theorem certCheck_ok_gen [DecidableEq K] (pC : CPoly K) (hp3 : (CPoly.toPoly pC).natDegree = 3)
    (pts : List (K × K × ℤ))
    (hon : ∀ q ∈ pts, (CPoly.toPoly pC).eval q.1 = q.2.1 ^ 2 ∧ q.2.1 ≠ 0)
    (hnd : (pts.map Prod.fst).Nodup) (D : ℕ) (hD : D ≠ 0) (n : ℕ) (hn : 1 ≤ n) (w : List K)
    (hw : CPoly.lcomb w (ellCols (pC) (ptsQ pts n) (ellNa (ptsQ pts n))
      (ellNb (ptsQ pts n))) = 0)
    (hw0 : CPoly.toPoly (w.take (ellNa (ptsQ pts n) + ellNb (ptsQ pts n))) ≠ 0) (B : CPoly K) :
    certCheck (pC) (w.take (ellNa (ptsQ pts n)),
      (w.drop (ellNa (ptsQ pts n))).take (ellNb (ptsQ pts n))) (fracG B D pts)
      (1 / ((n : K) * D)) = true := by
  set na := ellNa (ptsQ pts n)
  set nb := ellNb (ptsQ pts n)
  set p := CPoly.toPoly (pC) with hpdef
  set A := CPoly.toPoly (w.take na) with hAdef
  set Bp := CPoly.toPoly ((w.drop na).take nb) with hBdef
  have hAB : A ≠ 0 ∨ Bp ≠ 0 := by
    by_contra h
    push_neg at h
    apply hw0
    rw [List.take_add, CPoly.toPoly_append, ← hAdef, ← hBdef, h.1, h.2]; ring
  set N := A ^ 2 - Bp ^ 2 * p with hNdef
  have hN0 : N ≠ 0 := norm_ne_zero p A Bp hp3 hAB
  have hloc := (lcomb_ellCols (pC) na nb w (ptsQ pts n)).mp hw
  set M₀ := ((ptsQ pts n).map fun q ↦ q.2.2).sum with hM₀
  -- degrees
  have hna : na = M₀ / 2 + 1 := rfl
  have hnb : nb = (M₀ - 1) / 2 := rfl
  have hA : 2 * A.natDegree ≤ M₀ := by
    have := CPoly.natDegree_toPoly_le_length (w.take na)
    rw [← hAdef] at this
    have hl : (w.take na).length ≤ na := by simp
    omega
  have hB : Bp = 0 ∨ 2 * Bp.natDegree + 3 ≤ M₀ := by
    rcases Nat.eq_zero_or_pos nb with h0 | h0
    · left; rw [hBdef, h0, List.take_zero, CPoly.toPoly_nil]
    · right
      have := CPoly.natDegree_toPoly_le_length ((w.drop na).take nb)
      rw [← hBdef] at this
      have hl : ((w.drop na).take nb).length ≤ nb := by simp
      omega
  have hdeg : N.natDegree ≤ M₀ := norm_natDegree_le p A Bp hp3 M₀ hA hB
  -- per-point data
  set L := pts.length
  let α : Fin L → K := fun i ↦ pts[i].1
  let z : Fin L → ℤ := fun i ↦ pts[i].2.2
  let m : Fin L → ℕ := fun i ↦ n * (z i).natAbs
  let y : Fin L → K := fun i ↦ ((z i).sign : K) * pts[i].2.1
  have hqi : ∀ i : Fin L, (α i, y i, m i) ∈ ptsQ pts n := fun i ↦ by
    simp only [ptsQ, List.mem_map]
    exact ⟨pts[i], List.getElem_mem _, rfl⟩
  have hinj : Set.InjOn α (Finset.univ : Finset (Fin L)) := by
    intro i _ j _ hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd (hi := by rw [List.length_map]; exact i.2)
      (hj := by rw [List.length_map]; exact j.2)).mp
      (by simp only [List.getElem_map]; exact hij))
  have hres : ∀ i : Fin L, 1 ≤ m i → ∃ N₁ : K[X], N = (X - C (α i)) ^ m i * N₁ ∧
      (X - C (α i)) ^ m i ∣ (2 * p * (A * derivative Bp - derivative A * Bp) +
        A * Bp * derivative p) - C ((m i : K) * y i) * (X - C (α i)) ^ (m i - 1) * N₁ := by
    intro i hm
    have hz : z i ≠ 0 := by
      intro h0; simp only [m, h0, Int.natAbs_zero, mul_zero] at hm; omega
    have hβ := (hon _ (List.getElem_mem i.2)).2
    have hs : ((z i).sign : K) ^ 2 = 1 := by
      rcases lt_trichotomy (z i) 0 with h | h | h
      · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
      · exact absurd h hz
      · rw [Int.sign_eq_one_of_pos h]; norm_num
    have hy0 : y i ≠ 0 := by
      simp only [y]
      refine mul_ne_zero (fun h0 ↦ ?_) hβ
      rw [h0] at hs; norm_num at hs
    have hpα : p.eval (α i) = y i ^ 2 := by
      have hc := (hon _ (List.getElem_mem i.2)).1
      simp only [y, α, z] at hs ⊢
      rw [mul_pow, hs, one_mul]
      exact hc
    obtain ⟨N₁, h1, h2⟩ := residue_at (pC) A Bp (α i) (y i) (m i) hm hy0 hpα
      (hloc _ (hqi i))
    exact ⟨N₁, h1, h2⟩
  have hdvdN : ∀ i ∈ (Finset.univ : Finset (Fin L)), (X - C (α i)) ^ m i ∣ N := by
    intro i _
    rcases Nat.eq_zero_or_pos (m i) with h0 | h0
    · rw [h0, pow_zero]; exact one_dvd _
    · obtain ⟨N₁, h1, -⟩ := hres i h0
      exact ⟨N₁, h1⟩
  have hM₀' : M₀ = ∑ i : Fin L, m i := by
    rw [hM₀, ptsQ, List.map_map, sum_map_eq_fin]
    rfl
  obtain ⟨lam, hlam, hNeq⟩ := norm_shape' Finset.univ α hinj m N hN0 hdvdN (hM₀' ▸ hdeg)
  -- the denominator of `G`
  have hGd : CPoly.toPoly (fracG B D pts).2 = ∏ i : Fin L, (X - C (α i)) := by
    rw [fracG_den, prod_map_eq_fin]
  have hGd0 : CPoly.toPoly (fracG B D pts).2 ≠ 0 := by
    rw [hGd]; exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ X_sub_C_ne_zero _
  -- the global divisibility
  set cc : K := 1 / ((n : K) * D)
  set Mp := 2 * p * (A * derivative Bp - derivative A * Bp) + A * Bp * derivative p
  set Q := CPoly.toPoly (fracG B D pts).1 * N - CPoly.toPoly (fracG B D pts).2 * (C cc * Mp)
  have hcop : ((Finset.univ : Finset (Fin L)) : Set (Fin L)).Pairwise
      (Function.onFun IsCoprime fun i ↦ (X - C (α i)) ^ (m i + 1)) := by
    intro i hi j hj hij
    exact ((isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr fun h ↦ hij (hinj hi hj h)).isUnit)).pow
  have hpt : ∀ i ∈ (Finset.univ : Finset (Fin L)), (X - C (α i)) ^ (m i + 1) ∣ Q := by
    intro i _
    obtain ⟨Gq, H, hG1, hG2⟩ := fracG_local B D pts pts[i] (List.getElem_mem i.2)
    rcases Nat.eq_zero_or_pos (m i) with h0 | h0
    · have hz : z i = 0 := by
        simp only [m] at h0
        rcases Nat.mul_eq_zero.mp h0 with h | h
        · omega
        · exact Int.natAbs_eq_zero.mp h
      rw [h0, zero_add, pow_one]
      refine ⟨H * N - Gq * (C cc * Mp), ?_⟩
      simp only [Q, hG1, hG2]
      simp only [z] at hz
      rw [hz]; simp only [Int.cast_zero, zero_div, zero_mul, map_zero]
      ring
    · obtain ⟨N₁, h1, T, hT⟩ := hres i h0
      obtain ⟨k, hk⟩ : ∃ k, m i = k + 1 := ⟨m i - 1, by omega⟩
      rw [hk] at h1 hT ⊢
      rw [Nat.add_sub_cancel] at hT
      refine point_dvd _ _ N Mp Gq H N₁ T (α i) cc _ (y i) k hG1 hG2 h1 (by
        linear_combination hT) ?_
      rw [← hk]
      simp only [cc, m, y, z]
      have hDq : (D : K) ≠ 0 := by exact_mod_cast hD
      have hnq : (n : K) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hs : ((pts[i].2.2.sign : ℤ) : K) * (pts[i].2.2.natAbs : K) = (pts[i].2.2 : K) := by
        have h' := congrArg (fun t : ℤ ↦ (t : K)) (Int.sign_mul_natAbs pts[i].2.2)
        simp only [Int.cast_mul, Int.cast_natCast] at h'
        exact h'
      push_cast
      field_simp
      linear_combination pts[i].2.1 * hs
  have hprod := Finset.prod_dvd_of_coprime hcop hpt
  have hGN : CPoly.toPoly (fracG B D pts).2 * N =
      C lam * ∏ i : Fin L, (X - C (α i)) ^ (m i + 1) := by
    rw [hGd, hNeq]
    simp only [pow_succ, Finset.prod_mul_distrib]
    ring
  have hdvdQ : CPoly.toPoly (fracG B D pts).2 * N ∣ Q := by
    rw [hGN]
    exact (C_mul_dvd (by exact hlam)).mpr hprod
  -- the check
  unfold certCheck certR
  have hNpoly : CPoly.toPoly (certN (pC) (w.take na, (w.drop na).take nb)) = N := by
    simp only [certN, CPoly.toPoly_sub, CPoly.toPoly_mul]; ring
  have hMpoly : CPoly.toPoly (certM (pC) (w.take na, (w.drop na).take nb)) = Mp := by
    have h2 : CPoly.toPoly ([2] : CPoly K) = 2 := by
      rw [CPoly.toPoly_cons, CPoly.toPoly_nil, mul_zero, add_zero]; exact map_ofNat C 2
    simp only [certM, CPoly.toPoly_add, CPoly.toPoly_sub, CPoly.toPoly_mul, CPoly.toPoly_deriv, h2]
    ring
  have hex := divMod_exact (CPoly.sub (CPoly.mul (fracG B D pts).1
      (certN (pC) (w.take na, (w.drop na).take nb)))
      (CPoly.mul (fracG B D pts).2 (CPoly.smul cc (certM (pC) (w.take na, (w.drop na).take nb)))))
    (CPoly.mul (fracG B D pts).2 (certN (pC) (w.take na, (w.drop na).take nb)))
    (by rw [CPoly.toPoly_mul, hNpoly]; exact mul_ne_zero hGd0 hN0)
    (by
      simp only [CPoly.toPoly_mul, CPoly.toPoly_sub, CPoly.toPoly_smul, hNpoly, hMpoly]
      exact hdvdQ)
  simp only [CPoly.toPoly_mul, CPoly.toPoly_sub, CPoly.toPoly_smul, hNpoly, hMpoly] at hex
  simp only [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, CPoly.isZero_iff, hNpoly]
  refine ⟨⟨hN0, hGd0⟩, (CPoly.beq_iff _ _).mpr ?_⟩
  simp only [CPoly.toPoly_mul, CPoly.toPoly_add, CPoly.toPoly_smul, hNpoly, hMpoly]
  linear_combination hex

/-- **Every non-zero relation is a valid certificate.** -/
theorem certCheck_ok (a b c : ℤ) (_hsq : Squarefree (CPoly.toPoly (pOf a b c)))
    (pts : List (ℚ × ℚ × ℤ))
    (hon : ∀ q ∈ pts, q.2.1 ^ 2 = q.1 ^ 3 + a * q.1 ^ 2 + b * q.1 + c ∧ q.2.1 ≠ 0)
    (hnd : (pts.map Prod.fst).Nodup) (D : ℕ) (hD : D ≠ 0) (n : ℕ) (hn : 1 ≤ n) (w : List ℚ)
    (hw : CPoly.lcomb w (ellCols (pOf a b c) (ptsQ pts n) (ellNa (ptsQ pts n))
      (ellNb (ptsQ pts n))) = 0)
    (hw0 : CPoly.toPoly (w.take (ellNa (ptsQ pts n) + ellNb (ptsQ pts n))) ≠ 0) (B : CPoly ℚ) :
    certCheck (pOf a b c) (w.take (ellNa (ptsQ pts n)),
      (w.drop (ellNa (ptsQ pts n))).take (ellNb (ptsQ pts n))) (fracG B D pts)
      (1 / ((n : ℚ) * D)) = true :=
  certCheck_ok_gen (pOf a b c) (by rw [toPoly_pOf]; compute_degree!) pts
    (fun q hq ↦ ⟨by rw [toPoly_pOf, (hon q hq).1]; simp, (hon q hq).2⟩) hnd D hD n hn w hw hw0 B

end EllAlgo
